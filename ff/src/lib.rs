#![deny(missing_docs)]
#![allow(unsafe_op_in_unsafe_fn)]

//! Custom implementation of File

#[cfg(target_os = "linux")]
mod linux;

mod error;
pub use error::FFErr;

use fe::FRes;
use std::{
    cell::UnsafeCell,
    mem::ManuallyDrop,
    path::PathBuf,
    sync::{atomic, mpsc, Arc, Condvar, Mutex},
};

#[cfg(target_os = "linux")]
type FFile = linux::File;

#[cfg(not(target_os = "linux"))]
type FFile = ();

/// Custom implementation of File
pub struct FF(Arc<Core>);

unsafe impl Send for FF {}
unsafe impl Sync for FF {}

impl FF {
    /// Create new [`FF`] w/ specified length
    pub fn new(path: &PathBuf, length: u64, auto_flush: bool, module_id: u8) -> FRes<Self> {
        #[cfg(not(target_os = "linux"))]
        unimplemented!();

        #[cfg(target_os = "linux")]
        let file = unsafe { linux::File::new(path, true, module_id) }?;
        let init_res = unsafe { file.resize(length, module_id) };

        let core = Arc::new(Core::new(file, length, auto_flush));
        let ff = Self(core.clone());

        if let Err(e) = init_res {
            // NOTE: we delete the file so new init could work w/o any errors
            // HACK: we ignore the delete error, cause we already in errored state
            let _ = ff.delete();
            return Err(e);
        }

        Ok(ff)
    }

    /// Delete [`FF`] from filesystem
    ///
    /// _NOTE:_ Closing [`FF`] beforehand is not required
    pub fn delete(&self) -> FRes<()> {
        todo!()
    }
}

struct Core {
    cv: Condvar,
    lock: Mutex<()>,
    auto_flush: bool,
    length: atomic::AtomicU64,
    version: atomic::AtomicU8,
    dirty: atomic::AtomicBool,
    closed: atomic::AtomicBool,
    errored: atomic::AtomicBool,
    err_code: atomic::AtomicU16,
    file: UnsafeCell<ManuallyDrop<FFile>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(file: FFile, length: u64, auto_flush: bool) -> Self {
        Self {
            auto_flush,
            cv: Condvar::new(),
            lock: Mutex::new(()),
            version: atomic::AtomicU8::new(0),
            err_code: atomic::AtomicU16::new(0),
            dirty: atomic::AtomicBool::new(false),
            closed: atomic::AtomicBool::new(false),
            length: atomic::AtomicU64::new(length),
            errored: atomic::AtomicBool::new(false),
            file: UnsafeCell::new(ManuallyDrop::new(file)),
        }
    }
}
