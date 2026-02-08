//! Custom implementation of MemMap

#![deny(missing_docs)]
#![allow(unsafe_op_in_unsafe_fn)]

#[cfg(target_os = "linux")]
mod linux;

mod error;
pub use error::FMErr;

use error::{new_error, raw_err_with_msg, raw_error};
use fe::{FErr, FRes};
use hints::unlikely;
use std::{cell, mem, sync, sync::atomic, thread};

/// Config for [`FM`]
#[derive(Clone)]
pub struct FMCfg {
    /// module id (used for error codes)
    pub module_id: u8,

    /// when true, all dirty pages would be automatically be synced by a
    /// background thread
    pub auto_flush: bool,

    /// time interval for sync to flush dirty pages
    pub flush_duration: std::time::Duration,
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
            let error = std::io::Error::new(std::io::ErrorKind::BrokenPipe, "Trying to access closed FM");
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

impl std::fmt::Display for FM {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
                let error = std::io::Error::new(std::io::ErrorKind::BrokenPipe, "Trying to access unmapped FM");
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
