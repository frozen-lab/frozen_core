//! Custom implementation of `std::fs::File`

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::error::{FrozenErr, FrozenRes};
use alloc::{sync::Arc, vec::Vec};
use core::{cell, fmt, mem, sync::atomic};

#[cfg(any(target_os = "linux", target_os = "macos"))]
type FFile = posix::POSIXFile;

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
pub enum FFileErrCtx {
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
}

#[inline]
pub(in crate::ffile) fn new_err<R>(ctx: FFileErrCtx, message: alloc::vec::Vec<u8>) -> FrozenRes<R> {
    let err = FrozenErr::new(mid(), ERRDOMAIN, ctx as u16, message);
    Err(err)
}

/// Custom implementation of `std::fs::File`
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

    /// Create/open new instance of [`FrozenFile`]
    pub fn new(path: Vec<u8>, init_len: u64, mid: u8) -> FrozenRes<Self> {
        MID.store(mid, atomic::Ordering::Relaxed);

        let file = unsafe { posix::POSIXFile::new(&path) }?;
        let curr_len = unsafe { file.length()? };

        // TODO: (in future) improve corruption handling for file

        match curr_len {
            0 => unsafe { file.grow(0, init_len)? },
            _ => {
                if curr_len < init_len {
                    return new_err(
                        FFileErrCtx::Cpt,
                        b"underlying file is either corrupted or tampered with".to_vec(),
                    );
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

    #[inline]
    fn get_file(&self) -> &mem::ManuallyDrop<FFile> {
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

struct Core {
    path: Vec<u8>,
    length: atomic::AtomicU64,
    file: cell::UnsafeCell<mem::ManuallyDrop<FFile>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(file: FFile, length: u64, path: Vec<u8>) -> Self {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::TEST_MID;
    use std::os::unix::ffi::OsStrExt;
    use std::path::PathBuf;
    use tempfile::tempdir;

    fn tmp_path() -> (tempfile::TempDir, PathBuf) {
        let dir = tempdir().expect("temp dir");
        let path = dir.path().join("db_file");
        (dir, path)
    }

    mod ffile_new {
        use super::*;

        #[test]
        fn new_creates_and_initializes_length() {
            let (_dir, path) = tmp_path();

            let ff = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 0x800, TEST_MID).expect("create db");

            assert_eq!(ff.length(), 0x800);
            assert!(path.exists());
        }

        #[test]
        fn reopen_existing_preserves_length() {
            let (_dir, path) = tmp_path();

            let ff1 = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 0x400, TEST_MID).expect("create db");

            assert_eq!(ff1.length(), 0x400);
            drop(ff1);

            let ff2 = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 0x400, TEST_MID).expect("reopen db");
            assert_eq!(ff2.length(), 0x400);
        }

        #[test]
        fn reopening_with_smaller_init_len_is_ok() {
            let (_dir, path) = tmp_path();

            let ff1 = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 0x1000, TEST_MID).expect("create db");
            drop(ff1);

            let ff2 = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 0x200, TEST_MID).expect("reopen db");
            assert_eq!(ff2.length(), 0x1000);
        }

        #[test]
        fn reopening_with_larger_init_len_detects_corruption() {
            let (_dir, path) = tmp_path();

            let ff1 = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 0x400, TEST_MID).expect("create db");
            drop(ff1);

            let res = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 0x800, TEST_MID);
            assert!(res.is_err());

            let err = res.err().expect("must fail");
            assert!(err.cmp(FFileErrCtx::Cpt as u16));
        }

        #[test]
        fn new_fails_on_missing_parent_directory() {
            let dir = tempdir().expect("temp dir");
            let path = dir.path().join("missing").join("db_file");
            let res = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 0x200, TEST_MID);

            assert!(res.is_err());
        }
    }

    mod ffile_grow {
        use super::*;

        #[test]
        fn grow_updates_length_correctly() {
            let (_dir, path) = tmp_path();

            let ff = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 0x200, TEST_MID).expect("create db");
            ff.grow(0x300).expect("grow");

            assert_eq!(ff.length(), 0x500);
        }
    }

    mod ffile_delete {
        use super::*;

        #[test]
        fn delete_removes_file() {
            let (_dir, path) = tmp_path();

            let ff = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 0x200, TEST_MID).expect("create db");
            ff.delete().expect("delete");

            assert!(!path.exists());
        }

        #[test]
        fn drop_sync_and_close_is_safe() {
            let (_dir, path) = tmp_path();

            {
                let ff = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 0x300, TEST_MID).expect("create db");
                assert_eq!(ff.length(), 0x300);
            }

            assert!(path.exists());
        }
    }
}
