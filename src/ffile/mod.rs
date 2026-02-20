//! Custom implementation of `std::fs::File`

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::error::{FrozenErr, FrozenRes};
use core::{cell, fmt, mem, sync::atomic};
use std::{os::unix::ffi::OsStrExt, sync::Arc};

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
pub(in crate::ffile) fn new_err<R>(res: FFileErrRes, message: Vec<u8>) -> FrozenRes<R> {
    let detail = res.default_message();
    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, message);
    Err(err)
}

#[inline]
pub(in crate::ffile) fn new_err_default<R>(res: FFileErrRes) -> FrozenRes<R> {
    let detail = res.default_message();
    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, Vec::with_capacity(0));
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
    pub fn length(&self) -> usize {
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
    pub fn exists(path: &std::path::PathBuf) -> FrozenRes<bool> {
        unsafe { TFile::exists(path.as_os_str().as_bytes()) }
    }

    /// create a new or open an existing [`FrozenFile`]
    pub fn new(path: std::path::PathBuf, init_len: usize, mid: u8) -> FrozenRes<Self> {
        MID.store(mid, atomic::Ordering::Relaxed);
        let path = path.as_os_str().as_bytes().to_vec();

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
    pub fn grow(&self, len_to_add: usize) -> FrozenRes<()> {
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
    length: atomic::AtomicUsize,
    file: cell::UnsafeCell<mem::ManuallyDrop<TFile>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(file: TFile, length: usize, path: Vec<u8>) -> Self {
        Self {
            path,
            length: atomic::AtomicUsize::new(length),
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
    use std::path::PathBuf;
    use tempfile::{tempdir, TempDir};

    const INIT_LEN: usize = 0;

    fn new_tmp() -> (TempDir, PathBuf, FrozenFile) {
        let dir = tempdir().expect("tempdir");
        let path = dir.path().join("ids");

        let file = FrozenFile::new(path.clone(), INIT_LEN, TEST_MID).expect("new POSIXFile");
        (dir, path, file)
    }

    mod ff_new {
        use super::*;

        #[test]
        fn new_create_a_file() {
            let (_dir, _path, file) = new_tmp();

            #[cfg(any(target_os = "linux", target_os = "macos"))]
            assert!(file.fd() >= 0);
        }

        #[test]
        fn new_opens_existing_file() {
            let (_dir, path, file) = new_tmp();

            #[cfg(any(target_os = "linux", target_os = "macos"))]
            assert!(file.fd() >= 0);

            drop(file);

            match FrozenFile::new(path, INIT_LEN, TEST_MID) {
                Ok(file) => {
                    assert!(file.fd() >= 0);
                }
                Err(e) => panic!("failed to open file due to E: {:?}", e),
            }
        }

        #[test]
        fn new_creates_file_with_init_len() {
            let (_dir, _path, file) = new_tmp();

            #[cfg(any(target_os = "linux", target_os = "macos"))]
            assert!(file.fd() >= 0);

            assert_eq!(file.length(), INIT_LEN);
        }

        #[test]
        fn new_preserves_existing_len() {
            const LEN: usize = 0x100;
            let (_dir, path, file) = new_tmp();

            file.grow(LEN).expect("grow");

            let file2 = { FrozenFile::new(path, INIT_LEN, TEST_MID) }.expect("open existing");
            let len = file2.length();
            assert_eq!(len, LEN);
        }

        #[test]
        fn new_fails_on_dirpath() {
            let (dir, _path, _file) = new_tmp();
            FrozenFile::new(dir.path().to_path_buf(), INIT_LEN, TEST_MID).expect_err("must fail");
        }

        #[test]
        fn new_fails_if_existing_file_is_smaller_than_init_len() {
            let (_dir, path, file) = new_tmp();

            file.grow(16).expect("grow");
            drop(file);

            let err = FrozenFile::new(path, 32, TEST_MID).expect_err("must fail");
            assert!(err.cmp(FFileErrRes::Cpt as u16));
        }
    }

    mod ff_exists {
        use super::*;

        #[test]
        fn exists_false_for_missing() {
            let dir = tempdir().expect("tempdir");
            let path = dir.path().join("missing");

            let exists = FrozenFile::exists(&path).expect("exists");
            assert!(!exists);
        }
    }

    mod ff_delete {
        use super::*;

        #[test]
        fn delete_works() {
            let (_dir, path, file) = new_tmp();

            file.delete().expect("delete file");

            let exists = FrozenFile::exists(&path).expect("check exists");
            assert!(!exists);
        }
    }

    mod ff_grow {
        use super::*;

        #[test]
        fn grow_works() {
            let (_dir, _path, file) = new_tmp();
            file.grow(0x80).expect("grow");
        }

        #[test]
        fn grow_updates_length() {
            let (_dir, _path, file) = new_tmp();

            file.grow(0x80).expect("grow");
            assert_eq!(file.length(), 0x80);
        }

        #[test]
        fn grow_after_grow() {
            let (_dir, _path, file) = new_tmp();

            let mut total = 0;
            for _ in 0..4 {
                file.grow(0x100).expect("grow step");
                total += 0x100;
            }

            assert_eq!(file.length(), total);
        }
    }

    mod ff_write_read {
        use super::*;

        #[test]
        fn write_read_cycle() {
            let (_dir, _path, file) = new_tmp();

            const LEN: usize = 0x20;
            const DATA: [u8; LEN] = [0x1A; LEN];

            let mut buf = vec![0u8; LEN];

            file.grow(LEN).expect("resize file");
            file.write(DATA.as_ptr(), 0, LEN).expect("write");

            file.read(buf.as_mut_ptr(), 0, LEN).expect("read");
            assert_eq!(DATA.to_vec(), buf, "mismatch between read and write");
        }

        #[test]
        fn write_read_across_sessions() {
            let (_dir, path, file) = new_tmp();

            const LEN: usize = 0x20;
            const DATA: [u8; LEN] = [0x1A; LEN];

            {
                file.grow(LEN).expect("resize file");
                file.write(DATA.as_ptr(), 0, LEN).expect("write");
                file.sync().expect("sync");
                drop(file);
            }

            {
                let mut buf = vec![0u8; LEN];
                let file2 = FrozenFile::new(path, INIT_LEN, TEST_MID).expect("open existing");

                file2.read(buf.as_mut_ptr(), 0, LEN).expect("read");
                assert_eq!(DATA.to_vec(), buf, "mismatch between read and write");
            }
        }

        #[test]
        fn read_fails_on_eof() {
            let (_dir, _path, file) = new_tmp();

            file.grow(8).expect("grow");

            let mut buf = [0u8; 16];
            let err = file.read(buf.as_mut_ptr(), 0, 16).expect_err("must eof");
            assert!(err.cmp(FFileErrRes::Eof as u16));
        }

        #[test]
        fn write_fails_after_delete() {
            let (_dir, _path, file) = new_tmp();

            file.delete().expect("delete");

            let buf = [1u8; 8];
            let err = file.write(buf.as_ptr(), 0, buf.len()).expect_err("must fail");

            assert!(err.cmp(FFileErrRes::Hcf as u16));
        }

        #[test]
        fn write_with_offset() {
            let (_dir, _path, file) = new_tmp();

            file.grow(64).expect("grow");

            let a = [0xAAu8; 16];
            let b = [0xBBu8; 16];

            file.write(a.as_ptr(), 0, 16).expect("write a");
            file.write(b.as_ptr(), 32, 16).expect("write b");

            let mut buf = [0u8; 64];
            file.read(buf.as_mut_ptr(), 0, 64).expect("read");

            assert_eq!(&buf[0..16], &a);
            assert_eq!(&buf[32..48], &b);

            file.delete().expect("delete");
        }
    }

    mod ff_sync {
        use super::*;

        #[test]
        fn sync_works() {
            let (_dir, _path, file) = new_tmp();

            file.grow(32).expect("grow");
            file.sync().expect("sync");

            file.delete().expect("delete");
        }
    }

    mod ff_drop {
        use super::*;

        #[test]
        fn drop_persists_data() {
            let (_dir, path, file) = new_tmp();

            const LEN: usize = 16;
            let data = [7u8; LEN];

            file.grow(LEN).expect("grow");
            file.write(data.as_ptr(), 0, LEN).expect("write");
            drop(file);

            let file2 = FrozenFile::new(path, INIT_LEN, TEST_MID).expect("reopen");

            let mut buf = [0u8; LEN];
            file2.read(buf.as_mut_ptr(), 0, LEN).expect("read");

            assert_eq!(buf, data);

            file2.delete().expect("delete");
        }
    }
}
