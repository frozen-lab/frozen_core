//! Custom implementation of `memmap`

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::{
    error::{FrozenErr, FrozenRes},
    ffile::FrozenFile,
};
use std::{
    cell, fmt, mem,
    sync::{self, atomic},
    thread, time,
};

/// Domain Id for [`FrozenMMap`] is **18**
const ERRDOMAIN: u8 = 0x12;

/// default auto flush state for [`FMCfg`]
const AUTO_FLUSH: bool = false;

/// default flush duration for [`FMCfg`]
const FLUSH_DURATION: time::Duration = time::Duration::from_millis(250);

#[cfg(any(target_os = "linux", target_os = "macos"))]
type TMap = posix::POSIXMMap;

/// module id used for [`FrozenErr`]
static MID: atomic::AtomicU8 = atomic::AtomicU8::new(0);

#[inline]
pub(in crate::fmmap) fn mid() -> u8 {
    MID.load(atomic::Ordering::Relaxed)
}

/// Error codes for [`FrozenFile`]
#[repr(u16)]
pub enum FMMapErrRes {
    /// (512) internal fuck up (hault and catch fire)
    Hcf = 0x200,

    /// (513) unknown error (fallback)
    Unk = 0x201,

    /// (514) no more memory available
    Nmm = 0x202,

    /// (515) syncing error
    Syn = 0x203,

    /// (516) thread error or panic inside thread
    Txe = 0x204,

    /// (517) lock error (failed or poisoned)
    Lpn = 0x205,

    /// (518) perm error (read or write)
    Prm = 0x208,
}

impl FMMapErrRes {
    #[inline]
    fn default_message(&self) -> &'static [u8] {
        match self {
            Self::Lpn => b"lock poisoned",
            Self::Unk => b"unknown error type",
            Self::Nmm => b"no more memory left",
            Self::Hcf => b"hault and catch fire",
            Self::Prm => b"no perm to read or write",
            Self::Txe => b"thread failed or paniced",
            Self::Syn => b"failed to sync/flush data to storage device",
        }
    }
}

#[inline]
pub(in crate::fmmap) fn new_err<R>(res: FMMapErrRes, message: Vec<u8>) -> FrozenRes<R> {
    let detail = res.default_message();
    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, message);
    Err(err)
}

/// Config for [`FrozenMMap`]
#[derive(Debug, Clone)]
pub struct FMCfg {
    /// module id for [`FrozenMMap`]
    ///
    /// This id is used for error codes
    ///
    /// ## Why
    ///
    /// It enables for easier identification of error boundries when multiple [`FrozenMMap`]
    /// modules are present in the codebase
    pub module_id: u8,

    /// when true, all dirty pages would be synced by background thread
    pub auto_flush: bool,

    /// time interval for sync to flush dirty pages
    pub flush_duration: time::Duration,
}

impl FMCfg {
    /// Create a new instance of [`FMCfg`] w/ specified `module_id`
    pub const fn new(module_id: u8) -> Self {
        Self {
            module_id,
            auto_flush: AUTO_FLUSH,
            flush_duration: FLUSH_DURATION,
        }
    }

    /// Enable `auto_flush` for intervaled background sync for [`FrozenMMap`]
    pub const fn enable_auto_flush(mut self) -> Self {
        self.auto_flush = true;
        self
    }

    /// Set the interval for sync in [`FrozenMMap`]
    pub const fn flush_duration(mut self, interval: time::Duration) -> Self {
        self.flush_duration = interval;
        self
    }
}

/// Custom implementation of MemMap
#[derive(Debug)]
pub struct FrozenMMap(sync::Arc<Core>);

unsafe impl Send for FrozenMMap {}
unsafe impl Sync for FrozenMMap {}

impl FrozenMMap {
    /// Read current length of [`FrozenMMap`]
    #[inline]
    pub fn length(&self) -> usize {
        self.0.length
    }

    /// Create a new [`FrozenMMap`] for given `fd` w/ read & write permissions
    pub fn new(file: FrozenFile, length: usize, cfg: FMCfg) -> FrozenRes<Self> {
        MID.store(cfg.module_id, atomic::Ordering::Relaxed);

        let mmap = unsafe { posix::POSIXMMap::new(file.fd(), length) }?;
        let core = sync::Arc::new(Core::new(mmap, cfg.clone(), length, file));

        if cfg.auto_flush {
            Core::spawn_tx(core.clone())?;
        }

        Ok(Self(core))
    }

    /// Syncs in-mem data on the storage device
    ///
    /// ## `F_FULLFSYNC` vs `msync`
    ///
    /// On mac (the supposed best os),`msync()` does not guarantee that the dirty pages are flushed
    /// by the storage device, and it may not physically write the data to the platters for
    /// quite some time
    ///
    /// More info [here](https://developer.apple.com/library/archive/documentation/System/Conceptual/ManPages_iPhoneOS/man2/msync.2.html)
    ///
    /// To achieve true crash durability (including protection against power loss),
    /// we must use `fcntl(fd, F_FULLFSYNC)` which provides strict durability guarantees
    ///
    /// If `F_FULLFSYNC` is not supported by the underlying filesystem or device
    /// (e.g., returns `EINVAL`, `ENOTSUP`, or `EOPNOTSUPP`), we fall back to
    /// `fsync()` as a best-effort persistence mechanism
    #[inline]
    pub fn sync(&self) -> FrozenRes<()> {
        self.0.sync()
    }

    /// Returns the [`FrozenErr`] representing the last error occurred in [`FrozenMMap`]
    #[inline]
    pub fn last_error(&self) -> Option<&FrozenErr> {
        self.0.error.get()
    }

    /// Get's a read only typed pointer for `T`
    #[inline]
    pub fn with_read<T, R>(&self, offset: usize, f: impl FnOnce(&T) -> R) -> R {
        let guard = self.acquire_guard();

        let ptr = unsafe { self.get_mmap().get(offset) };
        let res = unsafe { f(&*ptr) };

        drop(guard);
        res
    }

    /// Get's a mutable typed pointer for `T`
    #[inline]
    pub fn with_write<T, R>(&self, offset: usize, f: impl FnOnce(&mut T) -> R) -> R {
        let guard = self.acquire_guard();

        let ptr = unsafe { self.get_mmap().get_mut(offset) };
        let res = unsafe { f(&mut *ptr) };

        drop(guard);
        res
    }

    /// Get a [`FMReader`] object for `T` at given `offset`
    ///
    /// **NOTE**: `offset` must be 8 bytes aligned
    #[inline]
    pub fn reader<T>(&self, offset: usize) -> FMReader<T> {
        let guard = self.acquire_guard();
        let reader = FMReader {
            ptr: unsafe { self.get_mmap().get(offset) },
            _guard: guard,
        };

        reader
    }

    /// Get a [`FMWriter`] object for `T` at given `offset`
    ///
    /// **NOTE**: `offset` must be 8 bytes aligned
    #[inline]
    pub fn writer<'a, T>(&'a self, offset: usize) -> FMWriter<'a, T> {
        let guard = self.acquire_guard();
        let writer = FMWriter {
            map: self,
            ptr: unsafe { self.get_mmap().get_mut(offset) },
            _guard: guard,
        };

        writer
    }

    #[inline]
    fn munmap(&self) -> FrozenRes<()> {
        unsafe { self.get_mmap().unmap(self.length()) }
    }

    #[inline]
    fn get_mmap(&self) -> &mem::ManuallyDrop<TMap> {
        unsafe { &*self.0.mmap.get() }
    }

    #[inline]
    fn acquire_guard(&self) -> ActiveGuard<'_> {
        let _ = self.0.active.fetch_add(1, atomic::Ordering::AcqRel);
        ActiveGuard { core: &self.0 }
    }
}

impl Drop for FrozenMMap {
    fn drop(&mut self) {
        // close flusher thread
        if self.0.cfg.auto_flush {
            self.0.cv.notify_one();
        }

        // sync if dirty
        if self.0.dirty.swap(false, atomic::Ordering::AcqRel) {
            let _ = self.sync();
        }

        let mut guard = match self.0.lock.lock() {
            Ok(g) => g,
            Err(_) => return,
        };

        while self.0.active.load(atomic::Ordering::Acquire) != 0 {
            guard = match self.0.shutdown_cv.wait(guard) {
                Ok(g) => g,
                Err(_) => return,
            }
        }

        let _ = self.munmap();
    }
}

impl fmt::Display for FrozenMMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FrozenMMap{{len: {}, id: {}, mode: {}}}",
            self.length(),
            self.0.cfg.module_id,
            self.0.cfg.auto_flush,
        )
    }
}

#[derive(Debug)]
struct Core {
    cfg: FMCfg,
    length: usize,
    cv: sync::Condvar,
    _ffile: FrozenFile,
    lock: sync::Mutex<()>,
    dirty: atomic::AtomicBool,
    shutdown_cv: sync::Condvar,
    active: atomic::AtomicUsize,
    error: sync::OnceLock<FrozenErr>,
    mmap: cell::UnsafeCell<mem::ManuallyDrop<TMap>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(mmap: TMap, cfg: FMCfg, length: usize, ffile: FrozenFile) -> Self {
        Self {
            cfg,
            length,
            _ffile: ffile,
            cv: sync::Condvar::new(),
            lock: sync::Mutex::new(()),
            error: sync::OnceLock::new(),
            shutdown_cv: sync::Condvar::new(),
            active: atomic::AtomicUsize::new(0),
            dirty: atomic::AtomicBool::new(false),
            mmap: cell::UnsafeCell::new(mem::ManuallyDrop::new(mmap)),
        }
    }

    #[inline]
    fn sync(&self) -> FrozenRes<()> {
        #[cfg(target_os = "linux")]
        unsafe {
            let mmap = &*self.mmap.get();
            return mmap.sync(self.length);
        }

        #[cfg(target_os = "macos")]
        return self._ffile.sync();
    }

    fn spawn_tx(core: sync::Arc<Self>) -> FrozenRes<()> {
        let (tx, rx) = sync::mpsc::sync_channel::<FrozenRes<()>>(1);

        if let Err(error) = thread::Builder::new()
            .name("fm-flush-tx".into())
            .spawn(move || Self::tx_thread(core, tx))
        {
            let mut error = error.to_string().as_bytes().to_vec();
            error.extend_from_slice(b"Failed to spawn flush thread for FrozenMMap");
            return new_err(FMMapErrRes::Hcf, error);
        }

        if let Err(error) = rx.recv() {
            let mut error = error.to_string().as_bytes().to_vec();
            error.extend_from_slice(b"Flush thread died before init could be completed for FrozenMMap");
            return new_err(FMMapErrRes::Hcf, error);
        }

        Ok(())
    }

    fn tx_thread(core: sync::Arc<Self>, init: sync::mpsc::SyncSender<FrozenRes<()>>) {
        // init phase (acquiring locks)
        let mut guard = match core.lock.lock() {
            Ok(g) => {
                // NOTE: We can supress the error here, as this may never panic, unless the receiver
                // is shut, which is preveneted by design
                let _ = init.send(Ok(()));
                g
            }
            Err(error) => {
                if let Err(err) = init.send(new_err(FMMapErrRes::Unk, error.to_string().as_bytes().to_vec())) {
                    let res = FMMapErrRes::Lpn;
                    let detail = res.default_message();

                    let mut err_msg = err.to_string().as_bytes().to_vec();
                    err_msg.extend_from_slice(b"Flush thread died before init could be completed for FrozenMMap");

                    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, err_msg);
                    let _ = core.error.set(err);
                }
                return;
            }
        };

        // init done, now is detached from thread
        drop(init);

        // sync loop w/ non-busy waiting
        loop {
            guard = match core.cv.wait_timeout(guard, core.cfg.flush_duration) {
                Ok((g, _)) => g,
                Err(e) => {
                    let res = FMMapErrRes::Txe;
                    let detail = res.default_message();

                    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, e.to_string().as_bytes().to_vec());
                    let _ = core.error.set(err);
                    return;
                }
            };

            if core.dirty.swap(false, atomic::Ordering::AcqRel) {
                drop(guard);

                if let Err(error) = core.sync() {
                    let _ = core.error.set(error);
                    return;
                }

                guard = match core.lock.lock() {
                    Ok(g) => g,
                    Err(e) => {
                        let res = FMMapErrRes::Lpn;
                        let detail = res.default_message();

                        let err =
                            FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, e.to_string().as_bytes().to_vec());
                        let _ = core.error.set(err);
                        return;
                    }
                };
            }
        }
    }
}

#[derive(Debug)]
struct ActiveGuard<'a> {
    core: &'a Core,
}

impl Drop for ActiveGuard<'_> {
    fn drop(&mut self) {
        if self.core.active.fetch_sub(1, atomic::Ordering::Release) == 1 {
            // last user
            if let Ok(_g) = self.core.lock.lock() {
                self.core.shutdown_cv.notify_one();
            }
        }
    }
}

/// Reader object for [`FrozenMMap`]
#[derive(Debug)]
pub struct FMReader<'a, T> {
    ptr: *const T,
    _guard: ActiveGuard<'a>,
}

impl<'a, T> FMReader<'a, T> {
    /// Get's an immutable (read only) typed pointer for `T`
    #[inline]
    pub fn read<R>(&self, f: impl FnOnce(&T) -> R) -> R {
        unsafe { f(&*self.ptr) }
    }
}

/// Writer object for [`FrozenMMap`]
#[derive(Debug)]
pub struct FMWriter<'a, T> {
    ptr: *mut T,
    map: &'a FrozenMMap,
    _guard: ActiveGuard<'a>,
}

impl<'a, T> FMWriter<'a, T> {
    /// Get's a mutable (read & write) typed pointer for `T`
    #[inline]
    pub fn write<R>(&self, f: impl FnOnce(&mut T) -> R) -> FrozenRes<R> {
        let res = unsafe { f(&mut *self.ptr) };
        match self.map.0.cfg.auto_flush {
            false => self.map.sync()?,
            true => {
                self.map.0.dirty.store(true, atomic::Ordering::Release);
                self.map.0.cv.notify_one();
            }
        }
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{error::TEST_MID, ffile::FrozenFile};
    use std::{path::PathBuf, sync::Arc, thread};
    use tempfile::{tempdir, TempDir};

    const LEN: usize = 0x80;

    fn new_tmp() -> (TempDir, PathBuf, FrozenMMap) {
        let dir = tempdir().expect("tmp dir");
        let path = dir.path().join("ids");

        let file = FrozenFile::new(path.clone(), LEN, TEST_MID).expect("new FrozenFile");
        let cfg = FMCfg::new(TEST_MID);
        let mmap = FrozenMMap::new(file, LEN, cfg).expect("new FrozenMMap");

        (dir, path, mmap)
    }

    mod fm_lifetime {
        use super::*;

        #[test]
        fn drop_without_dirty_is_safe() {
            let (_dir, _path, mmap) = new_tmp();
            drop(mmap);
        }

        #[test]
        fn last_error_initially_none() {
            let (_dir, _path, mmap) = new_tmp();
            assert!(mmap.last_error().is_none());
        }
    }

    mod fm_sync {
        use super::*;

        #[test]
        fn sync_works() {
            let (_dir, _path, mmap) = new_tmp();
            mmap.sync().expect("sync");
        }

        #[test]
        fn sync_persists_without_rewrite() {
            let (_dir, path, mmap) = new_tmp();

            let _ = mmap.writer::<u64>(0x10).write(|v| *v = 0xABCD);

            mmap.sync().expect("sync");
            drop(mmap);

            let file2 = FrozenFile::new(path, LEN, TEST_MID).expect("open existing");
            let mmap = FrozenMMap::new(file2, LEN, FMCfg::new(TEST_MID)).unwrap();

            let v = mmap.reader::<u64>(0x10).read(|v| *v);
            assert_eq!(v, 0xABCD);
        }

        #[test]
        fn repeated_sync_is_stable() {
            let (_dir, _path, mmap) = new_tmp();

            mmap.writer::<u64>(0).write(|v| *v = 7).expect("write");

            for _ in 0..0x20 {
                mmap.sync().expect("sync");
            }
        }
    }

    mod fm_reader_writer {
        use super::*;

        #[test]
        fn reader_fails_after_real_drop() {
            let (_dir, _path, mmap) = new_tmp();

            let reader = mmap.reader::<u64>(0);
            drop(reader);

            // Move into thread and drop the only instance
            let handle = std::thread::spawn(move || {
                drop(mmap);
            });

            handle.join().unwrap();
        }

        #[test]
        fn active_counter_tracks_readers() {
            let (_dir, _path, mmap) = new_tmp();

            let r1 = mmap.reader::<u64>(0);
            let r2 = mmap.reader::<u64>(0);

            assert!(mmap.0.active.load(std::sync::atomic::Ordering::Acquire) >= 2);

            drop(r1);
            drop(r2);
        }
    }

    mod fm_auto_flush {
        use super::*;

        #[test]
        fn auto_flush_persists() {
            let dir = tempdir().expect("tmp dir");
            let path = dir.path().join("ids");

            let file = FrozenFile::new(path.clone(), LEN, TEST_MID).unwrap();

            let cfg = FMCfg::new(TEST_MID)
                .enable_auto_flush()
                .flush_duration(std::time::Duration::from_millis(50));

            let mmap = FrozenMMap::new(file, LEN, cfg).unwrap();

            let _ = mmap.writer::<u64>(0).write(|v| *v = 123);

            thread::sleep(std::time::Duration::from_millis(150));

            drop(mmap);

            let file = FrozenFile::new(path, LEN, TEST_MID).unwrap();
            let mmap = FrozenMMap::new(file, LEN, FMCfg::new(TEST_MID)).unwrap();

            let v = mmap.reader::<u64>(0).read(|v| *v);
            assert_eq!(v, 123);
        }

        #[test]
        fn dirty_flag_resets_after_flush() {
            let (_dir, _path, mmap) = new_tmp();

            mmap.writer::<u64>(0).write(|v| *v = 1).unwrap();
            assert!(!mmap.0.dirty.load(std::sync::atomic::Ordering::Acquire));
        }
    }

    mod fm_with_api {
        use super::*;

        #[test]
        fn with_write_then_read() {
            let (_dir, _path, mmap) = new_tmp();

            mmap.with_write::<u64, _>(0, |v| *v = 99);

            let v = mmap.with_read::<u64, _>(0, |v| *v);
            assert_eq!(v, 99);
        }

        #[test]
        fn with_write_multiple_offsets() {
            let (_dir, _path, mmap) = new_tmp();

            for i in 0..8u64 {
                mmap.with_write::<u64, _>((i as usize) * 8, |v| *v = i);
            }

            for i in 0..8u64 {
                let v = mmap.with_read::<u64, _>((i as usize) * 8, |v| *v);
                assert_eq!(v, i);
            }
        }
    }

    mod fm_active_drain {
        use super::*;

        #[test]
        fn drop_waits_for_reader() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            let m = mmap.clone();
            let handle = thread::spawn(move || {
                let r = m.reader::<u64>(0);
                thread::sleep(std::time::Duration::from_millis(50));
                drop(r);
            });

            thread::sleep(std::time::Duration::from_millis(10));
            drop(mmap); // must wait for reader

            handle.join().expect("join");
        }
    }

    mod fm_write_read {
        use super::*;

        #[test]
        fn write_read_cycle() {
            let (_dir, _path, mmap) = new_tmp();

            mmap.writer::<u64>(0)
                .write(|v| *v = 0xDEAD_C0DE_DEAD_C0DE)
                .expect("write");

            let v = mmap.reader::<u64>(0).read(|v| *v);
            assert_eq!(v, 0xDEAD_C0DE_DEAD_C0DE);
        }

        #[test]
        fn write_read_across_sessions() {
            let (_dir, path, mmap) = new_tmp();

            mmap.writer::<u64>(0)
                .write(|v| *v = 0xDEAD_C0DE_DEAD_C0DE)
                .expect("write");

            drop(mmap);

            let file = FrozenFile::new(path, LEN, TEST_MID).expect("open existing");
            let mmap = FrozenMMap::new(file, LEN, FMCfg::new(TEST_MID)).expect("new frozeMMap");

            let v = mmap.reader::<u64>(0).read(|v| *v);
            assert_eq!(v, 0xDEAD_C0DE_DEAD_C0DE);
        }

        #[test]
        fn multiple_writes_single_sync() {
            let (_dir, _path, mmap) = new_tmp();

            for i in 0..16u64 {
                mmap.writer::<u64>((i as usize) * 8).write(|v| *v = i).expect("write");
            }

            for i in 0..16u64 {
                let v = mmap.reader::<u64>((i as usize) * 8).read(|v| *v);
                assert_eq!(v, i);
            }
        }
    }

    mod fm_concurrency {
        use super::*;

        #[test]
        fn concurrent_sync_is_safe() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            mmap.writer::<u64>(0).write(|v| *v = 42).expect("write");

            let handles: Vec<_> = (0..8)
                .map(|_| {
                    let m = mmap.clone();
                    thread::spawn(move || {
                        m.sync().expect("sync");
                    })
                })
                .collect();

            for h in handles {
                h.join().expect("thread join");
            }

            let v = mmap.reader::<u64>(0).read(|v| *v);
            assert_eq!(v, 42);
        }

        #[test]
        fn concurrent_writes_distinct_offsets() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            let handles: Vec<_> = (0..8u64)
                .map(|i| {
                    let m = mmap.clone();
                    thread::spawn(move || {
                        m.writer::<u64>((i as usize) * 8).write(|v| *v = i).unwrap();
                    })
                })
                .collect();

            for h in handles {
                h.join().expect("thread join");
            }

            for i in 0..8u64 {
                let v = mmap.reader::<u64>((i as usize) * 8).read(|v| *v);
                assert_eq!(v, i);
            }
        }

        #[test]
        fn concurrent_with_write() {
            let (_dir, _path, mmap) = new_tmp();
            let mmap = Arc::new(mmap);

            let handles: Vec<_> = (0..8u64)
                .map(|i| {
                    let m = mmap.clone();
                    thread::spawn(move || {
                        m.with_write::<u64, _>((i as usize) * 8, |v| *v = i);
                    })
                })
                .collect();

            for h in handles {
                h.join().expect("join");
            }

            for i in 0..8u64 {
                let v = mmap.with_read::<u64, _>((i as usize) * 8, |v| *v);
                assert_eq!(v, i);
            }
        }
    }
}
