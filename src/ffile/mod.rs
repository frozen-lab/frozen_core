//! Custom implementation of `std::fs::File`

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::error::{FrozenErr, FrozenRes};
use alloc::{sync::Arc, vec::Vec};
use core::{cell, fmt, mem, sync::atomic};

#[cfg(any(target_os = "linux", target_os = "macos"))]
type TFile = posix::POSIXFile;

/// Domain Id for [`FrozenFile`] is **17**
const ERRDOMAIN: u8 = 0x11;

/// module id used for [`FrozenErr`]
static MID: atomic::AtomicU8 = atomic::AtomicU8::new(0);

#[inline]
pub(in crate::ffile) fn mid() -> u8 {
    MID.load(atomic::Ordering::Relaxed)
}

/// Error codes for [`FrozenFile`]
#[repr(u16)]
pub enum FFileErrRes {
    /// (256) internal fuck up (hault and catch fire)
    Hcf = 0x100,

    /// (257) unknown error (fallback)
    Unk = 0x101,

    /// (258) no more space available
    Nsp = 0x102,

    /// (259) syncing error
    Syn = 0x103,

    /// (260) no write perm
    Wrt = 0x104,

    /// (261) no read perm
    Red = 0x105,

    /// (262) invalid path
    Inv = 0x106,

    /// (263) corrupted file
    Cpt = 0x107,

    /// (264) unexpected eof
    Eof = 0x108,
}

impl FFileErrRes {
    #[inline]
    fn default_message(&self) -> &'static [u8] {
        match self {
            Self::Inv => b"invalid file path",
            Self::Unk => b"unknown error type",
            Self::Hcf => b"hault and catch fire",
            Self::Red => b"read permission denied",
            Self::Wrt => b"write permission denied",
            Self::Eof => b"unxpected eof while io op",
            Self::Nsp => b"no space left on storage device",
            Self::Cpt => b"file is either invalid or corrupted",
            Self::Syn => b"failed to sync/flush data to storage device",
        }
    }
}

#[inline]
pub(in crate::ffile) fn new_err<R>(res: FFileErrRes, message: alloc::vec::Vec<u8>) -> FrozenRes<R> {
    let detail = res.default_message();
    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, message);
    Err(err)
}

#[inline]
pub(in crate::ffile) fn new_err_default<R>(res: FFileErrRes) -> FrozenRes<R> {
    let detail = res.default_message();
    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, alloc::vec::Vec::with_capacity(0));
    Err(err)
}

/// Custom implementation of `std::fs::File`
#[derive(Debug)]
pub struct FrozenFile(Arc<Core>);

unsafe impl Send for FrozenFile {}
unsafe impl Sync for FrozenFile {}

impl FrozenFile {
    /// Read current length of [`FrozenFile`]
    #[inline]
    pub fn length(&self) -> u64 {
        self.0.length.load(atomic::Ordering::Acquire)
    }

    /// Get file descriptor for [`FrozenFile`]
    #[inline]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn fd(&self) -> i32 {
        self.get_file().fd()
    }

    /// check if [`FrozenFile`] exists on storage device or not
    #[inline]
    pub fn exists(&self) -> FrozenRes<bool> {
        unsafe { TFile::exists(&self.0.path) }
    }

    /// create a new or open an existing [`FrozenFile`]
    pub fn new(path: Vec<u8>, init_len: u64, mid: u8) -> FrozenRes<Self> {
        MID.store(mid, atomic::Ordering::Relaxed);

        let file = unsafe { posix::POSIXFile::new(&path) }?;
        let curr_len = unsafe { file.length()? };

        // TODO: (in future) improve corruption handling for file

        match curr_len {
            0 => unsafe { file.grow(0, init_len)? },
            _ => {
                if curr_len < init_len {
                    return new_err_default(FFileErrRes::Cpt);
                }
            }
        }

        let core = Arc::new(Core::new(file, curr_len.max(init_len), path));
        Ok(Self(core))
    }

    /// Grow [`FrozenFile`] w/ given `len_to_add`
    #[inline(always)]
    pub fn grow(&self, len_to_add: u64) -> FrozenRes<()> {
        unsafe { self.get_file().grow(self.length(), len_to_add) }.inspect(|_| {
            let _ = self.0.length.fetch_add(len_to_add, atomic::Ordering::Release);
        })
    }

    /// Syncs in-mem data on the storage device
    #[inline]
    pub fn sync(&self) -> FrozenRes<()> {
        self.0.sync()
    }

    /// Delete [`FrozenFile`] from filesystem
    pub fn delete(&self) -> FrozenRes<()> {
        let file = self.get_file();

        // NOTE: sanity check is invalid here, cause we are deleting the file, hence we don't
        // actually care if the state is sane or not ;)

        unsafe { file.unlink(&self.0.path) }
    }

    /// Read at given `offset` from [`FrozenFile`]
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn read(&self, buf_ptr: *mut u8, offset: usize, len_to_read: usize) -> FrozenRes<()> {
        unsafe { self.get_file().pread(buf_ptr, offset, len_to_read) }
    }

    /// Write at given `offset` into [`FrozenFile`]
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn write(&self, buf_ptr: *const u8, offset: usize, len_to_write: usize) -> FrozenRes<()> {
        unsafe { self.get_file().pwrite(buf_ptr, offset, len_to_write) }
    }

    #[inline]
    fn get_file(&self) -> &mem::ManuallyDrop<TFile> {
        unsafe { &*self.0.file.get() }
    }
}

impl Drop for FrozenFile {
    fn drop(&mut self) {
        // sync if dirty & close
        let _ = self.0.sync();
        let _ = unsafe { self.get_file().close() };
    }
}

impl fmt::Display for FrozenFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FrozenFile {{fd: {}, len: {}, id: {}}}",
            self.fd(),
            self.length(),
            mid()
        )
    }
}

#[derive(Debug)]
struct Core {
    path: Vec<u8>,
    length: atomic::AtomicU64,
    file: cell::UnsafeCell<mem::ManuallyDrop<TFile>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(file: TFile, length: u64, path: Vec<u8>) -> Self {
        Self {
            path,
            length: atomic::AtomicU64::new(length),
            file: cell::UnsafeCell::new(mem::ManuallyDrop::new(file)),
        }
    }

    #[inline]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn sync(&self) -> FrozenRes<()> {
        unsafe { (&*self.file.get()).sync() }
    }
}
