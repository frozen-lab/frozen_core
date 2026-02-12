//! Custom implementation of File

#[cfg(target_os = "linux")]
mod linux;

use crate::fe::{FErr, FRes};
use crate::hints::unlikely;
use std::{
    cell, fmt, io, mem, path,
    sync::{self, atomic},
    thread, time,
};

/// Domain Id for [`FF`] is **17**
const ERRDOMAIN: u8 = 0x11;

/// default auto flush state for [`FFCfg`]
const AUTO_FLUSH: bool = false;

/// default flush duration for [`FFCfg`]
const FLUSH_DURATION: time::Duration = time::Duration::from_millis(250);

#[cfg(target_os = "linux")]
type FFile = linux::File;

#[cfg(not(target_os = "linux"))]
type FFile = ();

/// Error codes for [`FF`]
#[repr(u16)]
pub enum FFErr {
    /// (256) internal fuck up
    Hcf = 0x100,

    /// (257) unknown error (fallback)
    Unk = 0x101,

    /// (258) no more space available
    Nsp = 0x102,

    /// (259) unexpected eof
    Eof = 0x103,

    /// (260) syncing error
    Syn = 0x104,

    /// (261) no write perm
    Wrt = 0x105,

    /// (262) no read perm
    Red = 0x106,

    /// (263) invalid path
    Inv = 0x107,

    /// (264) thread error or panic inside thread
    Txe = 0x108,

    /// (265) lock error (failed or poisoned)
    Lpn = 0x109,
}

/// Config for [`FF`]
#[derive(Clone)]
pub struct FFCfg {
    /// module id for [`FF`]
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

    /// Path of the file
    pub path: path::PathBuf,

    /// time interval for sync to flush dirty pages
    pub flush_duration: time::Duration,
}

impl FFCfg {
    /// Create a new instance of [`FFCfg`] w/ specified `module_id`
    pub const fn new(path: path::PathBuf, module_id: u8) -> Self {
        Self {
            path,
            module_id,
            auto_flush: AUTO_FLUSH,
            flush_duration: FLUSH_DURATION,
        }
    }

    /// Enable `auto_flush` for intervaled background sync for [`FF`]
    pub const fn enable_auto_flush(mut self) -> Self {
        self.auto_flush = true;
        self
    }

    /// Set the interval for sync in [`FF`]
    pub const fn flush_duration(mut self, interval: time::Duration) -> Self {
        self.flush_duration = interval;
        self
    }
}

/// Custom implementation of File
pub struct FF(sync::Arc<Core>);

unsafe impl Send for FF {}
unsafe impl Sync for FF {}

impl FF {
    /// Create new [`FF`] w/ specified length
    pub fn new(cfg: FFCfg, length: u64) -> FRes<Self> {
        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        let file = unsafe { linux::File::new(&cfg.path, true, cfg.module_id) }?;
        let init_res = unsafe { file.resize(length, cfg.module_id) };

        let core = sync::Arc::new(Core::new(file, cfg.clone(), length));
        let ff = Self(core.clone());

        if let Err(e) = init_res {
            // NOTE: we delete the file so new init could work w/o any errors
            // HACK: we ignore the delete error, cause we already in errored state
            let _ = ff.delete();
            return Err(e);
        }

        if cfg.auto_flush {
            Core::spawn_tx(core)?;
        }

        Ok(ff)
    }

    /// Open an existing `[FF]`
    pub fn open(cfg: FFCfg) -> FRes<Self> {
        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        let file = unsafe { linux::File::new(&cfg.path, false, cfg.module_id) }?;
        let length = unsafe { file.length(cfg.module_id) }?;

        let core = sync::Arc::new(Core::new(file, cfg.clone(), length));
        let ff = Self(core.clone());

        if cfg.auto_flush {
            Core::spawn_tx(core)?;
        }

        Ok(ff)
    }

    /// Resize [`FF`] w/ `new_len`
    pub fn resize(&self, new_len: u64) -> FRes<()> {
        // sanity checks
        self.ensure_sanity()?;
        debug_assert!(new_len > self.length());

        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        unsafe { self.get_file().resize(new_len, self.0.cfg.module_id) }?;

        self.0.length.store(new_len, atomic::Ordering::Release);
        Ok(())
    }

    /// Current length of [`FF`]
    #[inline]
    pub fn length(&self) -> u64 {
        self.0.length.load(atomic::Ordering::Acquire)
    }

    /// Get file descriptor for [`FF`]
    #[inline]
    #[cfg(target_os = "linux")]
    pub fn fd(&self) -> i32 {
        self.get_file().fd()
    }

    /// Returns the [`FErr`] representing the last error occurred in [`FF`]
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

    /// Delete [`FF`] from filesystem
    ///
    /// _NOTE:_ Closing [`FF`] beforehand is not required
    pub fn delete(&self) -> FRes<()> {
        let file = self.get_file();

        // NOTE: sanity check is invalid here, cause we are deleting the file, hence we don't
        // actually care if the state is sane or not ;)

        // mark file as close
        self.0.closed.store(true, atomic::Ordering::Release);

        // close flusher thread
        if self.0.cfg.auto_flush {
            self.0.cv.notify_one();
        }

        // NOTE: we must wait for sync thread to exit to avoid use of operations using
        // invalid fd (which is after close, i.e. fd = -1)
        if let Err(error) = self.0.lock.lock() {
            return new_error(self.0.cfg.module_id, FFErr::Lpn, error);
        }

        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        unsafe {
            match file.close(self.0.cfg.module_id) {
                Ok(_) => file.unlink(&self.0.cfg.path, self.0.cfg.module_id),
                Err(e) => Err(e),
            }
        }
    }

    /// Read at given `offset` from [`FF`]
    #[inline]
    pub fn read(&self, buf_ptr: *mut u8, offset: usize, len_to_read: usize) -> FRes<()> {
        // sanity check
        self.ensure_sanity()?;

        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        unsafe {
            self.get_file()
                .pread(buf_ptr, offset, len_to_read, self.0.cfg.module_id)
        }
    }

    /// Read (multiple vectors) at given `offset` from [`FF`]
    #[inline]
    pub fn readv(&self, buf_ptrs: &[*mut u8], offset: usize, len_to_read: usize) -> FRes<()> {
        // sanity checks
        self.ensure_sanity()?;
        debug_assert!(buf_ptrs.len() <= self.0.max_iovecs);

        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        unsafe {
            self.get_file()
                .preadv(buf_ptrs, offset, len_to_read, self.0.cfg.module_id)
        }
    }

    /// Write at given `offset` to [`FF`]
    #[inline]
    pub fn write(&self, buf_ptr: *const u8, offset: usize, len_to_write: usize) -> FRes<()> {
        // sanity check
        self.ensure_sanity()?;
        debug_assert!(offset + len_to_write <= self.length() as usize);

        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        unsafe {
            self.get_file()
                .pwrite(buf_ptr, offset, len_to_write, self.0.cfg.module_id)
        }?;

        self.0.dirty.store(true, atomic::Ordering::Release);
        self.0.cv.notify_one();
        Ok(())
    }

    /// Write (multiple vectors) at given `offset` to [`FF`]
    #[inline]
    pub fn writev(&self, buf_ptrs: &[*const u8], offset: usize, buffer_size: usize) -> FRes<()> {
        // sanity check
        self.ensure_sanity()?;
        debug_assert!(buf_ptrs.len() <= self.0.max_iovecs);
        debug_assert!(offset + (buf_ptrs.len() * buffer_size) <= self.length() as usize);

        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        unsafe {
            self.get_file()
                .pwritev(buf_ptrs, offset, buffer_size, self.0.cfg.module_id)
        }?;

        self.0.dirty.store(true, atomic::Ordering::Release);
        self.0.cv.notify_one();
        Ok(())
    }

    #[inline(always)]
    fn ensure_sanity(&self) -> FRes<()> {
        if let Some(err) = self.0.error.get() {
            return Err(err.clone());
        }

        let closed = self.0.closed.load(atomic::Ordering::Acquire);
        if unlikely(closed) {
            let error = io::Error::new(io::ErrorKind::BrokenPipe, "Trying to access closed FF");
            return new_error(self.0.cfg.module_id, FFErr::Hcf, error);
        }

        Ok(())
    }

    #[inline]
    fn get_file(&self) -> &mem::ManuallyDrop<FFile> {
        unsafe { &*self.0.file.get() }
    }
}

impl Drop for FF {
    fn drop(&mut self) {
        if self.0.closed.swap(true, atomic::Ordering::AcqRel) {
            return;
        }

        // close flusher thread
        if self.0.cfg.auto_flush {
            self.0.cv.notify_one();
        }

        // sync if dirty & close
        let _ = self.0.sync();
        let _ = unsafe { self.get_file().close(self.0.cfg.module_id) };
    }
}

impl fmt::Display for FF {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        write!(
            f,
            "FF {{fd: {}, len: {}, id: {}, mode: {}, has_error: {}}}",
            self.fd(),
            self.length(),
            self.0.cfg.module_id,
            self.0.cfg.auto_flush,
            self.0.error.get().is_some(),
        )
    }
}

struct Core {
    cfg: FFCfg,
    cv: sync::Condvar,
    lock: sync::Mutex<()>,
    max_iovecs: usize,
    error: sync::OnceLock<FErr>,
    dirty: atomic::AtomicBool,
    closed: atomic::AtomicBool,
    length: atomic::AtomicU64,
    file: cell::UnsafeCell<mem::ManuallyDrop<FFile>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(file: FFile, cfg: FFCfg, length: u64) -> Self {
        Self {
            cfg,
            cv: sync::Condvar::new(),
            lock: sync::Mutex::new(()),
            error: sync::OnceLock::new(),
            max_iovecs: get_max_iovecs(),
            dirty: atomic::AtomicBool::new(false),
            closed: atomic::AtomicBool::new(false),
            length: atomic::AtomicU64::new(length),
            file: cell::UnsafeCell::new(mem::ManuallyDrop::new(file)),
        }
    }

    #[inline]
    fn sync(&self) -> FRes<()> {
        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        unsafe {
            (&*self.file.get()).sync(self.cfg.module_id)
        }
    }

    fn spawn_tx(core: sync::Arc<Self>) -> FRes<()> {
        let mid = core.cfg.module_id;
        let (tx, rx) = sync::mpsc::sync_channel::<FRes<()>>(1);

        if let Err(error) = thread::Builder::new()
            .name("ff-flush-tx".into())
            .spawn(move || Self::tx_thread(core, tx))
        {
            return Err(raw_err_with_msg(
                mid,
                error,
                FFErr::Hcf,
                "Failed to spawn flush thread for FF",
            ));
        }

        if let Err(error) = rx.recv() {
            return Err(raw_err_with_msg(
                mid,
                error,
                FFErr::Hcf,
                "Flush thread died before init could be completed for FF",
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
                if let Err(err) = init.send(new_error(core.cfg.module_id, FFErr::Unk, error)) {
                    let error = raw_err_with_msg(
                        core.cfg.module_id,
                        err,
                        FFErr::Lpn,
                        "Flush thread died before init could be completed for FF",
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
                    let error = raw_error(core.cfg.module_id, FFErr::Txe, e);
                    let _ = core.error.set(error);
                    return;
                }
            };

            if core.closed.load(atomic::Ordering::Acquire) {
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
                        let error = raw_error(core.cfg.module_id, FFErr::Lpn, e);
                        let _ = core.error.set(error);
                        return;
                    }
                };
            }
        }
    }
}

/// max iovecs allowed for single readv/writev calls
const MAX_IOVECS: usize = 512;

fn get_max_iovecs() -> usize {
    #[cfg(target_os = "linux")]
    unsafe {
        let res = libc::sysconf(libc::_SC_IOV_MAX);
        if res <= 0 {
            return MAX_IOVECS;
        }

        return res as usize;
    }

    #[cfg(not(target_os = "linux"))]
    MAX_IOVECS
}

#[inline]
pub(in crate::ff) fn new_error<E, R>(mid: u8, reason: FFErr, error: E) -> FRes<R>
where
    E: fmt::Display,
{
    let code = crate::fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    let err = FErr::with_err(code, error);
    Err(err)
}

#[inline]
pub(in crate::ff) fn raw_error<E>(mid: u8, reason: FFErr, error: E) -> FErr
where
    E: fmt::Display,
{
    let code = crate::fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    FErr::with_err(code, error)
}

#[inline]
pub(in crate::ff) fn raw_err_with_msg<E>(mid: u8, error: E, reason: FFErr, msg: &'static str) -> FErr
where
    E: fmt::Display,
{
    let code = crate::fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    FErr::with_msg(code, format!("{msg} due to error =>\n{error}"))
}

#[cfg(test)]
mod ff_tests {
    use super::*;
    use crate::fe::{FECheckOk, MID};
    use tempfile::{tempdir, TempDir};

    const LEN: usize = 0x20;

    fn new_cfg(path: path::PathBuf) -> FFCfg {
        FFCfg::new(path, MID)
    }

    fn new_tmp(auto_flush: bool) -> (TempDir, path::PathBuf, FF) {
        let dir = tempdir().expect("temp dir");
        let path = dir.path().join("tmp_file");

        let mut cfg = new_cfg(path.clone());

        if auto_flush {
            cfg = cfg.enable_auto_flush();
        }

        let ff = FF::new(cfg, LEN as u64).expect("new FF");
        (dir, path, ff)
    }

    mod new_open {
        use super::*;

        #[test]
        fn new_works() {
            let (_dir, path, ff) = new_tmp(false);

            assert!(ff.fd() >= 0);
            assert_eq!(ff.length(), LEN as u64);
            assert!(path.exists());
        }

        #[test]
        fn open_works() {
            let (_dir, path, ff) = new_tmp(false);
            drop(ff);

            let cfg = new_cfg(path);

            let ff = FF::open(cfg).expect("open FF");
            assert!(ff.fd() >= 0);
        }

        #[test]
        fn open_fails_when_deleted() {
            let (_dir, path, ff) = new_tmp(false);
            assert!(ff.delete().check_ok());

            let cfg = new_cfg(path);
            assert!(FF::open(cfg).is_err());
        }
    }

    mod resize {
        use super::*;
        use std::fs;

        #[test]
        fn resize_zero_extends() {
            let (_dir, path, ff) = new_tmp(false);
            const NEW_LEN: u64 = 0x80;

            assert!(ff.resize(NEW_LEN).check_ok());
            assert_eq!(ff.length(), NEW_LEN);

            let data = fs::read(&path).expect("read file");
            assert_eq!(data.len(), NEW_LEN as usize);
            assert!(data.iter().all(|b| *b == 0));
        }

        #[test]
        fn open_preserves_length() {
            let (_dir, path, ff) = new_tmp(true);
            const NEW_LEN: u64 = 0x80;

            assert!(ff.resize(NEW_LEN).check_ok());
            thread::sleep(FLUSH_DURATION * 2);
            drop(ff);

            let cfg = new_cfg(path);
            let ff = FF::open(cfg).expect("open FF");
            assert_eq!(ff.length(), NEW_LEN);
        }
    }

    mod write_read {
        use super::*;

        #[test]
        fn write_read_cycle() {
            let (_dir, _path, ff) = new_tmp(false);
            let data = [0x1Au8; LEN];

            assert!(ff.write(data.as_ptr(), 0, LEN).check_ok());

            let mut buf = vec![0u8; LEN];
            assert!(ff.read(buf.as_mut_ptr(), 0, LEN).check_ok());
            assert_eq!(buf, data);
        }

        #[test]
        fn writev_read_cycle() {
            let (_dir, _path, ff) = new_tmp(false);
            let data = [0x1Au8; LEN];
            let ptrs = vec![data.as_ptr(); 8];

            let total = ptrs.len() * LEN;
            assert!(ff.resize(total as u64).check_ok());
            assert!(ff.writev(&ptrs, 0, LEN).check_ok());

            let mut buf = vec![0u8; total];
            assert!(ff.read(buf.as_mut_ptr(), 0, total).check_ok());

            for chunk in buf.chunks_exact(LEN) {
                assert_eq!(chunk, data);
            }
        }

        #[test]
        fn write_persist_across_sessions() {
            let (_dir, path, ff) = new_tmp(true);
            let data = [0xABu8; LEN];

            assert!(ff.write(data.as_ptr(), 0, LEN).check_ok());
            thread::sleep(FLUSH_DURATION * 2);
            drop(ff);

            let cfg = new_cfg(path);
            let ff = FF::open(cfg).expect("open FF");
            let mut buf = vec![0u8; LEN];

            assert!(ff.read(buf.as_mut_ptr(), 0, LEN).check_ok());
            assert_eq!(buf, data);
        }
    }

    mod concurrency {
        use super::*;

        #[test]
        fn concurrent_writes_then_read() {
            const THREADS: usize = 8;
            const CHUNK: usize = 0x100;

            let (_dir, _path, ff) = new_tmp(false);
            let ff = sync::Arc::new(ff);

            assert!(ff.resize((THREADS * CHUNK) as u64).check_ok());

            let mut handles = Vec::new();
            for i in 0..THREADS {
                let f = ff.clone();
                handles.push(thread::spawn(move || {
                    let data = vec![i as u8; CHUNK];
                    f.write(data.as_ptr(), i * CHUNK, CHUNK).expect("write");
                }));
            }

            for h in handles {
                assert!(h.join().is_ok());
            }

            let mut buf = vec![0u8; THREADS * CHUNK];
            assert!(ff.read(buf.as_mut_ptr(), 0, buf.len()).check_ok());

            for i in 0..THREADS {
                let chunk = &buf[i * CHUNK..(i + 1) * CHUNK];
                assert!(chunk.iter().all(|b| *b == i as u8));
            }
        }
    }

    mod delete {
        use super::*;

        #[test]
        fn delete_works() {
            let (_dir, path, ff) = new_tmp(false);
            assert!(ff.delete().check_ok());
            assert!(!path.exists());
        }

        #[test]
        fn delete_twice_fails() {
            let (_dir, _path, ff) = new_tmp(false);
            assert!(ff.delete().check_ok());
            assert!(ff.delete().is_err());
        }
    }
}
