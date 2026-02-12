//! Custom implementation of MemMap

#[cfg(target_os = "linux")]
mod linux;

use crate::{
    fe::{FErr, FRes},
    hints::unlikely,
};
use std::{
    cell, fmt, io, mem,
    sync::{self, atomic},
    thread, time,
};

/// Domain Id for [`FM`] is **18**
const ERRDOMAIN: u8 = 0x12;

/// default auto flush state for [`FMCfg`]
const AUTO_FLUSH: bool = false;

/// default flush duration for [`FMCfg`]
const FLUSH_DURATION: time::Duration = time::Duration::from_millis(250);

/// Error codes for [`FM`]
#[repr(u16)]
pub enum FMErr {
    /// (512) internal fuck up
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
}

/// Config for [`FM`]
#[derive(Clone)]
pub struct FMCfg {
    /// module id for [`FM`]
    ///
    /// This id is used for error codes
    ///
    /// ## Why
    ///
    /// It enables for easier identification of error boundries when multiple [`FM`]
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

    /// Enable `auto_flush` for intervaled background sync for [`FM`]
    pub const fn enable_auto_flush(mut self) -> Self {
        self.auto_flush = true;
        self
    }

    /// Set the interval for sync in [`FM`]
    pub const fn flush_duration(mut self, interval: time::Duration) -> Self {
        self.flush_duration = interval;
        self
    }
}

/// Custom implementation of MemMap
pub struct FM(sync::Arc<Core>);

unsafe impl Send for FM {}
unsafe impl Sync for FM {}

impl FM {
    /// Create a new [`FM`] for given `fd` w/ read & write permissions
    #[cfg(target_os = "linux")]
    pub fn new(fd: i32, length: usize, cfg: FMCfg) -> FRes<Self> {
        let mmap = unsafe { linux::MMap::new(fd, length, cfg.module_id) }?;
        let core = sync::Arc::new(Core::new(mmap, cfg.clone(), length));

        if cfg.auto_flush {
            Core::spawn_tx(core.clone())?;
        }

        Ok(Self(core))
    }

    /// Get current length of [`FM`]
    #[inline]
    pub fn length(&self) -> usize {
        self.0.length
    }

    /// Returns the [`FErr`] representing the last error occurred in [`FM`]
    #[inline]
    #[cfg(target_os = "linux")]
    pub fn last_error(&self) -> Option<&FErr> {
        self.0.error.get()
    }

    /// Syncs in-mem data on the storage device
    #[inline]
    pub fn sync(&self) -> FRes<()> {
        // sanity check
        self.ensure_sanity()?;
        self.0.sync()
    }

    /// Get a [`FMReader`] object for `T` at given `offset`
    ///
    /// **NOTE**: `offset` must be 8 bytes aligned
    #[inline]
    pub fn reader<'a, T>(&'a self, offset: usize) -> FRes<FMReader<'a, T>> {
        self.0.acquire_instance()?;
        let reader = FMReader {
            ptr: unsafe { self.get_mmap().get(offset) },
            _guard: ActiveGuard { core: &self.0 },
        };

        Ok(reader)
    }

    /// Get a [`FMWriter`] object for `T` at given `offset`
    ///
    /// **NOTE**: `offset` must be 8 bytes aligned
    #[inline]
    pub fn writer<'a, T>(&'a self, offset: usize) -> FRes<FMWriter<'a, T>> {
        self.0.acquire_instance()?;
        let writer = FMWriter {
            map: self,
            ptr: unsafe { self.get_mmap().get_mut(offset) },
            _guard: ActiveGuard { core: &self.0 },
        };

        Ok(writer)
    }

    fn munmap(&self) -> FRes<()> {
        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        unsafe {
            self.get_mmap().unmap(self.length(), self.0.cfg.module_id)?;
        }

        Ok(())
    }

    #[inline(always)]
    fn ensure_sanity(&self) -> FRes<()> {
        if let Some(err) = self.0.error.get() {
            return Err(err.clone());
        }

        let closed = self.0.dropped.load(atomic::Ordering::Acquire);
        if unlikely(closed) {
            let error = io::Error::new(io::ErrorKind::BrokenPipe, "Trying to access closed FM");
            return new_error(self.0.cfg.module_id, FMErr::Hcf, error);
        }

        Ok(())
    }

    #[inline]
    fn get_mmap(&self) -> &mem::ManuallyDrop<FMMap> {
        unsafe { &*self.0.mmap.get() }
    }
}

impl Drop for FM {
    fn drop(&mut self) {
        if self.0.dropped.swap(true, atomic::Ordering::AcqRel) {
            return;
        }

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

impl fmt::Display for FM {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        write!(
            f,
            "FM {{len: {}, id: {}, mode: {}, has_error: {}}}",
            self.length(),
            self.0.cfg.module_id,
            self.0.cfg.auto_flush,
            self.0.error.get().is_some(),
        )
    }
}

#[cfg(target_os = "linux")]
type FMMap = linux::MMap;

#[cfg(not(target_os = "linux"))]
type FMMap = ();

struct Core {
    cfg: FMCfg,
    length: usize,
    cv: sync::Condvar,
    lock: sync::Mutex<()>,
    dirty: atomic::AtomicBool,
    shutdown_cv: sync::Condvar,
    dropped: atomic::AtomicBool,
    active: atomic::AtomicUsize,
    error: sync::OnceLock<FErr>,
    mmap: cell::UnsafeCell<mem::ManuallyDrop<FMMap>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(mmap: FMMap, cfg: FMCfg, length: usize) -> Self {
        Self {
            cfg,
            length,
            cv: sync::Condvar::new(),
            lock: sync::Mutex::new(()),
            error: sync::OnceLock::new(),
            shutdown_cv: sync::Condvar::new(),
            active: atomic::AtomicUsize::new(0),
            dirty: atomic::AtomicBool::new(false),
            dropped: atomic::AtomicBool::new(false),
            mmap: cell::UnsafeCell::new(mem::ManuallyDrop::new(mmap)),
        }
    }

    #[inline]
    fn sync(&self) -> FRes<()> {
        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        unsafe {
            (&*self.mmap.get()).sync(self.length, self.cfg.module_id)
        }
    }

    #[inline]
    fn acquire_instance(&self) -> FRes<()> {
        let mut cur = self.active.load(atomic::Ordering::Acquire);
        loop {
            if self.dropped.load(atomic::Ordering::Acquire) {
                let error = io::Error::new(io::ErrorKind::BrokenPipe, "Trying to access unmapped FM");
                return new_error(self.cfg.module_id, FMErr::Hcf, error);
            }

            if let Err(v) =
                self.active
                    .compare_exchange_weak(cur, cur + 1, atomic::Ordering::AcqRel, atomic::Ordering::Acquire)
            {
                cur = v;
                continue;
            }

            return Ok(());
        }
    }

    fn spawn_tx(core: sync::Arc<Self>) -> FRes<()> {
        let mid = core.cfg.module_id;
        let (tx, rx) = sync::mpsc::sync_channel::<FRes<()>>(1);

        if let Err(error) = thread::Builder::new()
            .name("fm-flush-tx".into())
            .spawn(move || Self::tx_thread(core, tx))
        {
            return Err(raw_err_with_msg(
                mid,
                error,
                FMErr::Hcf,
                "Failed to spawn flush thread for FM",
            ));
        }

        if let Err(error) = rx.recv() {
            return Err(raw_err_with_msg(
                mid,
                error,
                FMErr::Hcf,
                "Flush thread died before init could be completed for FM",
            ));
        }

        Ok(())
    }

    fn tx_thread(core: sync::Arc<Self>, init: sync::mpsc::SyncSender<FRes<()>>) {
        // init phase (acquiring locks)
        let mut guard = match core.lock.lock() {
            Ok(g) => {
                // NOTE: We can supress the error here, as this may never panic, unless the receiver
                // is shut, which is preveneted by design
                let _ = init.send(Ok(()));
                g
            }
            Err(error) => {
                if let Err(err) = init.send(new_error(core.cfg.module_id, FMErr::Unk, error)) {
                    let error = raw_err_with_msg(
                        core.cfg.module_id,
                        err,
                        FMErr::Lpn,
                        "Flush thread died before init could be completed for FM",
                    );
                    let _ = core.error.set(error);
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
                    let error = raw_error(core.cfg.module_id, FMErr::Txe, e);
                    let _ = core.error.set(error);
                    return;
                }
            };

            if core.dropped.load(atomic::Ordering::Acquire) {
                return;
            }

            if core.dirty.swap(false, atomic::Ordering::AcqRel) {
                drop(guard);

                if let Err(error) = core.sync() {
                    let _ = core.error.set(error);
                    return;
                }

                guard = match core.lock.lock() {
                    Ok(g) => g,
                    Err(e) => {
                        let error = raw_error(core.cfg.module_id, FMErr::Lpn, e);
                        let _ = core.error.set(error);
                        return;
                    }
                };
            }
        }
    }
}

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

/// Reader object for [`FM`]
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

/// Writer object for [`FM`]
pub struct FMWriter<'a, T> {
    ptr: *mut T,
    map: &'a FM,
    _guard: ActiveGuard<'a>,
}

impl<'a, T> FMWriter<'a, T> {
    /// Get's a mutable (read & write) typed pointer for `T`
    #[inline]
    pub fn write<R>(&self, f: impl FnOnce(&mut T) -> R) -> FRes<R> {
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

#[inline]
pub(in crate::fm) fn new_error<E, R>(mid: u8, reason: FMErr, error: E) -> FRes<R>
where
    E: fmt::Display,
{
    let code = crate::fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    let err = FErr::with_err(code, error);
    Err(err)
}

#[inline]
pub(in crate::fm) fn raw_error<E>(mid: u8, reason: FMErr, error: E) -> FErr
where
    E: fmt::Display,
{
    let code = crate::fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    FErr::with_err(code, error)
}

#[inline]
pub(in crate::fm) fn raw_err_with_msg<E>(mid: u8, error: E, reason: FMErr, msg: &'static str) -> FErr
where
    E: fmt::Display,
{
    let code = crate::fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    FErr::with_msg(code, format!("{msg} due to error =>\n{error}"))
}

mod fm_tests {
    use super::*;
    use crate::fe::{FECheckOk, MID};
    use crate::ff::{FFCfg, FF};
    use std::path::PathBuf;
    use tempfile::{tempdir, TempDir};

    const LEN: usize = 0x20;
    const CFG: FMCfg = FMCfg::new(MID);

    fn get_ff_cfg(path: PathBuf) -> FFCfg {
        FFCfg::new(path, MID)
    }

    fn new_tmp() -> (TempDir, PathBuf, FF, FM) {
        let dir = tempdir().expect("temp dir");
        let tmp = dir.path().join("tmp_file");

        let file = FF::new(get_ff_cfg(tmp.clone()), LEN as u64).expect("new FF");
        let mmap = FM::new(file.fd(), LEN, CFG).expect("new MMap");

        (dir, tmp, file, mmap)
    }

    mod map_unmap {
        use super::*;

        #[test]
        fn map_unmap_cycle() {
            let (_dir, _tmp, _file, map) = new_tmp();

            assert_eq!(map.length(), LEN);
            assert!(map.munmap().check_ok());
        }

        #[test]
        fn unmap_after_unmap_does_not_fails() {
            let (_dir, _tmp, _file, map) = new_tmp();

            assert!(map.munmap().check_ok());
            assert!(map.munmap().check_ok());
            assert!(map.munmap().check_ok());
        }
    }

    mod write_read {
        use super::*;

        #[test]
        fn write_read_cycle() {
            let (_dir, _tmp, _file, mmap) = new_tmp();

            {
                let w = mmap.writer::<u64>(0).expect("writer");
                assert!(w.write(|v| *v = 0xDEAD_C0DE_DEAD_C0DE).check_ok());
            }

            assert!(mmap.sync().check_ok());

            {
                let r = mmap.reader::<u64>(0).expect("reader");
                let val = r.read(|v| *v);
                assert_eq!(val, 0xDEAD_C0DE_DEAD_C0DE);
            }
        }

        #[test]
        fn write_read_across_sessions() {
            let dir = tempdir().expect("tmp dir");
            let path = dir.path().join("persist");

            {
                let file = FF::new(get_ff_cfg(path.clone()), LEN as u64).expect("new");
                let mmap = FM::new(file.fd(), LEN, CFG).expect("mmap");

                mmap.writer::<u64>(0)
                    .expect("writer")
                    .write(|v| *v = 0xAABBCCDDEEFF0011)
                    .expect("write");

                mmap.sync().expect("sync");
            }

            {
                let file = FF::open(get_ff_cfg(path.clone())).expect("new");
                let mmap = FM::new(file.fd(), LEN, CFG).expect("mmap");

                let r = mmap.reader::<u64>(0).expect("reader");
                assert_eq!(r.read(|v| *v), 0xAABBCCDDEEFF0011);
            }
        }

        #[test]
        fn mmap_write_visible_to_file_read() {
            let (_dir, _tmp, file, mmap) = new_tmp();

            mmap.writer::<u64>(0)
                .expect("writer")
                .write(|v| *v = 0xCAFEBABECAFEBABE)
                .expect("write");

            mmap.sync().expect("sync");

            let mut buf = [0u8; 8];
            file.read(buf.as_mut_ptr(), 0, 8).expect("pread");

            assert_eq!(u64::from_le_bytes(buf), 0xCAFEBABECAFEBABE);
        }
    }

    mod concurrency {
        use super::*;

        #[test]
        fn concurrent_readers() {
            let (_dir, _tmp, _file, mmap) = new_tmp();
            let mmap = sync::Arc::new(mmap);

            mmap.writer::<u64>(0)
                .expect("writer")
                .write(|v| *v = 42)
                .expect("write");

            mmap.sync().expect("sync");

            let mut handles = Vec::new();
            for _ in 0..8 {
                let m = mmap.clone();
                handles.push(thread::spawn(move || {
                    let r = m.reader::<u64>(0).expect("reader");
                    assert_eq!(r.read(|v| *v), 42);
                }));
            }

            for h in handles {
                // assert!(h.join().check_ok());

                assert!(h
                    .join()
                    .map_err(|e| {
                        eprintln!("\n{:?}\n", e);
                    })
                    .is_ok());
            }
        }

        #[test]
        fn concurrent_writes_disjoint_offsets() {
            const N: usize = 8;
            let dir = tempdir().expect("tmp dir");
            let path = dir.path().join("multi");

            let file = FF::new(get_ff_cfg(path), (LEN * N) as u64).expect("new");
            let mmap = sync::Arc::new(FM::new(file.fd(), LEN * N, CFG).expect("mmap"));

            let mut handles = Vec::new();
            for i in 0..N {
                let m = mmap.clone();
                handles.push(thread::spawn(move || {
                    let off = i * LEN;
                    m.writer::<u64>(off)
                        .expect("writer")
                        .write(|v| *v = i as u64)
                        .expect("write");
                }));
            }

            for h in handles {
                assert!(h
                    .join()
                    .map_err(|e| {
                        eprintln!("\n{:?}\n", e);
                    })
                    .is_ok());
            }

            mmap.sync().expect("sync");

            for i in 0..N {
                let r = mmap.reader::<u64>(i * LEN).expect("reader");
                assert_eq!(r.read(|v| *v), i as u64);
            }
        }

        #[test]
        fn concurrent_writes_same_offset_then_sync() {
            let (_dir, _tmp, _file, mmap) = new_tmp();
            let mmap = sync::Arc::new(mmap);

            let mut handles = Vec::new();
            for i in 0..8u64 {
                let m = mmap.clone();
                handles.push(thread::spawn(move || {
                    m.writer::<u64>(0).expect("writer").write(|v| *v = i).expect("write");
                }));
            }

            for h in handles {
                assert!(h
                    .join()
                    .map_err(|e| {
                        eprintln!("\n{:?}\n", e);
                    })
                    .is_ok());
            }

            mmap.sync().expect("sync");

            let r = mmap.reader::<u64>(0).expect("reader");
            let _ = r.read(|v| *v); // value nondeterministic but must not crash
        }

        #[test]
        fn drop_waits_for_active_readers() {
            let (_dir, _tmp, _file, mmap) = new_tmp();
            let mmap = sync::Arc::new(mmap);

            let r = mmap.reader::<u64>(0).expect("reader");

            let m = mmap.clone();
            let h = thread::spawn(move || {
                // must block until reader is dropped
                drop(m);
            });

            thread::sleep(time::Duration::from_millis(50));
            drop(r);

            assert!(h
                .join()
                .map_err(|e| {
                    eprintln!("\n{:?}\n", e);
                })
                .is_ok());
        }
    }
}
