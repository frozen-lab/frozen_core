use super::{new_error, FFErr};
use crate::{fe::FRes, hints};
use core::sync::atomic;
use libc::{
    c_int, c_uint, close, fstat, ftruncate, off_t, open, stat, unlink, EACCES, EBADF, EFAULT, EINTR, EINVAL, EIO,
    EISDIR, ENOENT, ENOSPC, ENOTDIR, EPERM, EROFS, O_CLOEXEC, O_CREAT, O_RDONLY, O_RDWR, O_TRUNC, S_IRUSR, S_IWUSR,
};
use std::{ffi, io, os::unix::ffi::OsStrExt, path};

/// type for file descriptor on POSIX systems
type FD = c_int;

const CLOSED_FD: FD = -1;
const MAX_RETRIES: usize = 6; // max allowed retries for `EINTR` errors

/// Raw implementation of Posix (linux & macos) file for [`FrozenFile`]
pub(super) struct POSIXFile(atomic::AtomicI32);

unsafe impl Send for POSIXFile {}
unsafe impl Sync for POSIXFile {}

impl POSIXFile {
    /// Get the file descriptor of [`POSIXFile`]
    #[inline]
    pub(super) fn fd(&self) -> FD {
        self.0.load(atomic::Ordering::Acquire)
    }

    /// create a new [`POSIXFile`]
    pub(super) unsafe fn new(path: &path::PathBuf, mid: u8) -> FRes<Self> {
        let fd = open_raw(path, prep_flags(true), mid)?;

        // NOTE: On POSIX, `open(O_CREATE)` only creates the directory entry in memory,
        // it may be visible immediately, but it's existence is not crash durable, for
        // crash safe durability, we must do `fsync(file)` & `fsync(dir)`

        #[cfg(target_os = "linux")]
        fsync_raw(fd, mid)?;

        #[cfg(target_os = "macos")]
        fullsync_raw(fd, mid)?;

        sync_parent_dir(path, mid)?;

        Ok(Self(atomic::AtomicI32::new(fd)))
    }

    /// open an existing [`POSIXFile`]
    pub(super) unsafe fn open(path: &path::PathBuf, mid: u8) -> FRes<Self> {
        let fd = open_raw(path, prep_flags(false), mid)?;
        Ok(Self(atomic::AtomicI32::new(fd)))
    }

    /// Close [`POSIXFile`] to give up file descriptor
    ///
    /// ## Multiple Calls
    ///
    /// This function is idempotent, hence it prevents close-on-close errors
    ///
    /// ## Sync Error (`FFErr::Syn`)
    ///
    /// In POSIX systems, kernal may report delayed write/sync failures when closing, this are
    /// durability errors, fatel in nature
    ///
    /// when these errors are detected, error w/ `FFErr::Syn` is thrown, this must be handled by
    /// the storage engine to keep durability intact
    #[inline(always)]
    pub(super) unsafe fn close(&self, mid: u8) -> FRes<()> {
        let fd = self.0.swap(CLOSED_FD, atomic::Ordering::AcqRel);
        if fd == CLOSED_FD {
            return Ok(());
        }

        close_raw(fd, mid)
    }

    /// Unlinks (possibly deletes) the [`POSIXFile`]
    #[inline]
    pub(super) unsafe fn unlink(&self, path: &path::PathBuf, mid: u8) -> FRes<()> {
        let cpath = path_to_cstring(path, mid)?;

        // NOTE: POSIX systems requires fd to be closed before attempting to unlink the file
        self.close(mid)?;

        if unlink(cpath.as_ptr()) != 0 {
            let error = last_os_error();

            match error.raw_os_error() {
                // missing file or invalid path
                Some(ENOENT) | Some(ENOTDIR) => return new_error(mid, FFErr::Inv, error),

                // lack of permission
                Some(EACCES) | Some(EPERM) => return new_error(mid, FFErr::Red, error),

                // read only fs
                Some(EROFS) => return new_error(mid, FFErr::Wrt, error),

                // IO error (durability failure)
                Some(EIO) => return new_error(mid, FFErr::Syn, error),

                _ => return new_error(mid, FFErr::Unk, error),
            }
        }

        // NOTE: For crash durability, we must `fsync(dir)` for the given `path`
        sync_parent_dir(path, mid)
    }

    /// Read current length of [`POSIXFile`] using file metadata (w/ `fstat` syscall)
    #[inline(always)]
    pub(super) unsafe fn length(&self, mid: u8) -> FRes<u64> {
        let mut st = std::mem::zeroed::<stat>();
        let res = fstat(self.fd(), &mut st);

        if res != 0 {
            let error = last_os_error();
            let error_raw = error.raw_os_error();

            // bad or invalid fd
            if error_raw == Some(EBADF) || error_raw == Some(EFAULT) {
                return new_error(mid, FFErr::Hcf, error);
            }

            return new_error(mid, FFErr::Unk, error);
        }

        Ok(st.st_size as u64)
    }

    /// Grow (zero extend) [`POSIXFile`] w/ given `len_to_add`
    ///
    /// ## `ftruncate()` vs `fallocate()` (Linux only)
    ///
    /// `ftruncate()` only adjusts the logical file size, blocks are lazily on writes,
    /// and does not guarantees physical block allocations
    ///
    /// On the contrary, `fallocate` preallocates immediately, and reduces fragmentation
    /// for write ops
    ///
    /// On Linux, we use `fallocate` by default, and use `ftruncate` as a fallback
    #[inline(always)]
    pub(super) unsafe fn grow(&self, curr_len: u64, len_to_add: u64, mid: u8) -> FRes<()> {
        let fd = self.fd();
        let new_len = (curr_len + len_to_add) as off_t;

        #[cfg(target_os = "linux")]
        {
            let mut retries = 0;
            loop {
                if hints::likely(libc::fallocate(fd, 0, curr_len as off_t, len_to_add as off_t) == 0) {
                    return Ok(());
                }

                let error = last_os_error();
                let error_raw = error.raw_os_error();

                match error_raw {
                    // IO interrupt
                    Some(EINTR) => {
                        if retries < MAX_RETRIES {
                            retries += 1;
                            continue;
                        }

                        break;
                    }

                    // invalid fd
                    Some(libc::EBADF) => return new_error(mid, FFErr::Hcf, error),

                    // read-only fs (can also be caused by TOCTOU)
                    Some(libc::EROFS) => return new_error(mid, FFErr::Wrt, error),

                    // no space available on disk
                    Some(libc::ENOSPC) => return new_error(mid, FFErr::Nsp, error),

                    // lack of support for `fallocate` (fall through to ftruncate)
                    Some(libc::EINVAL) | Some(libc::EOPNOTSUPP) | Some(libc::ENOSYS) => break,

                    _ => return new_error(mid, FFErr::Unk, error),
                }
            }
        }

        let res = ftruncate(fd, new_len);
        if hints::unlikely(res != 0) {
            let error = last_os_error();
            match error.raw_os_error() {
                // invalid fd or lack of support for sync
                Some(EINVAL) | Some(EBADF) => return new_error(mid, FFErr::Hcf, error),

                // read-only fs (can also be caused by TOCTOU)
                Some(EROFS) => return new_error(mid, FFErr::Wrt, error),

                // no space available on disk
                Some(ENOSPC) => return new_error(mid, FFErr::Nsp, error),

                _ => return new_error(mid, FFErr::Unk, error),
            }
        }

        Ok(())
    }

    /// Syncs in-mem data on the storage device
    ///
    /// **NOTE:** This function is `macos` only
    ///
    /// ## `F_FULLFSYNC` vs `fsync`
    ///
    /// On mac (the supposed best os),`fsync()` does not guarantee that the dirty pages are flushed
    /// by the storage device, and it may not physically write the data to the platters for
    /// quite some time
    ///
    /// More info [here](https://developer.apple.com/library/archive/documentation/System/Conceptual/ManPages_iPhoneOS/man2/fsync.2.html)
    ///
    /// To achieve true crash durability (including protection against power loss),
    /// we must use `fcntl(fd, F_FULLFSYNC)` which provides strict durability guarantees
    ///
    /// If `F_FULLFSYNC` is not supported by the underlying filesystem or device
    /// (e.g., returns `EINVAL`, `ENOTSUP`, or `EOPNOTSUPP`), we fall back to
    /// `fsync()` as a best-effort persistence mechanism
    #[inline(always)]
    #[cfg(target_os = "macos")]
    pub(super) unsafe fn sync(&self, mid: u8) -> FRes<()> {
        fullsync_raw(self.fd() as c_int, mid)
    }

    /// Syncs in-mem data on the storage device
    ///
    /// **NOTE:** This function is `linux` only
    ///
    /// ## `fsync` vs `fdatasync`
    ///
    /// We use `fdatasync()` instead of `fsync()` for persistence, as `fdatasync()` guarantees,
    /// all modified file data and any metadata required to retrieve that data, like file size
    /// changes are flushed to stable storage
    ///
    /// This way we avoid non-essential metadata updates, such as access time (`atime`),
    /// mod time (`mtime`), and other inode bookkeeping info
    #[inline(always)]
    #[cfg(target_os = "linux")]
    pub(super) unsafe fn sync(&self, mid: u8) -> FRes<()> {
        fdatasync_raw(self.fd(), mid)
    }
}

/// create/open a new file w/ `open` syscall
///
/// ## Caveats of `O_NOATIME` (`EPERM` Error)
///
/// `open()` with `O_NOATIME` may fail with `EPERM` instead of silently ignoring the flag
///
/// `EPERM` indicates a kernel level permission violation, as the kernel rejects the
/// request outright, even though the flag only affects metadata behavior
///
/// To remain sane across ownership models, containers, and shared filesystems,
/// we explicitly retry the `open()` w/o `O_NOATIME` when `EPERM` is encountered
unsafe fn open_raw(path: &path::PathBuf, flags: FD, mid: u8) -> FRes<FD> {
    let cpath = path_to_cstring(path, mid)?;

    #[cfg(target_os = "linux")]
    let mut flags = flags;

    #[cfg(target_os = "linux")]
    let mut tried_noatime = false;

    loop {
        let fd = if flags & O_CREAT != 0 {
            open(
                cpath.as_ptr(),
                flags,
                (S_IRUSR | S_IWUSR) as c_uint, // write + read permissions
            )
        } else {
            open(cpath.as_ptr(), flags)
        };

        if hints::unlikely(fd < 0) {
            let error = last_os_error();
            let error_raw = error.raw_os_error();

            // NOTE: Fallback for `EPERM` error, when `O_NOATIME` is not supported by current FS
            #[cfg(target_os = "linux")]
            {
                if error_raw == Some(EPERM) && (flags & libc::O_NOATIME) != 0 && !tried_noatime {
                    flags &= !libc::O_NOATIME;
                    tried_noatime = true;
                    continue;
                }
            }

            match error_raw {
                // NOTE: We must retry on interuption errors (EINTR retry)
                Some(EINTR) => continue,

                // no space available on disk
                Some(ENOSPC) => return new_error(mid, FFErr::Nsp, error),

                // path is a dir (hcf)
                Some(EISDIR) => return new_error(mid, FFErr::Hcf, error),

                // invalid path (missing sub dir's)
                Some(ENOENT) | Some(ENOTDIR) => return new_error(mid, FFErr::Inv, error),

                // permission denied
                Some(EACCES) | Some(EPERM) => return new_error(mid, FFErr::Red, error),

                // read-only fs
                Some(EROFS) => return new_error(mid, FFErr::Wrt, error),

                _ => return new_error(mid, FFErr::Unk, error),
            }
        }

        return Ok(fd);
    }
}

/// close a file or dir via given `fd`
unsafe fn close_raw(fd: FD, mid: u8) -> FRes<()> {
    if close(fd) != 0 {
        let error = last_os_error();
        let error_raw = error.raw_os_error();

        // NOTE: In POSIX systems, kernal may report delayed writeback failures on `close`,
        // this are fatel errors, and can not be retried! Hence, all the writes in the sync
        // window were not persisted.
        //
        // So we treat this error as **sync** error, to notify above layer as the recent batch
        // failed to persist!
        if error_raw == Some(EIO) {
            return new_error(mid, FFErr::Syn, error);
        }

        return new_error(mid, FFErr::Unk, error);
    }

    Ok(())
}

/// perform `fsync` on given `FD` (can be File or Directory)
///
/// ## Why do we retry?
///
/// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases,
/// no progress is guaranteed, so the syscall must be retried
///
/// For reliability, we retry on `EINTR` w/o busy waiting to avoid strain on resources
unsafe fn fsync_raw(fd: FD, mid: u8) -> FRes<()> {
    // only for EINTR errors
    let mut retries = 0;
    loop {
        if hints::unlikely(libc::fsync(fd) != 0) {
            let error = last_os_error();
            match error.raw_os_error() {
                // IO interrupt
                Some(EINTR) => {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // NOTE: sync error indicates that retries exhausted and durability is broken
                    // in the current/last window/batch
                    return new_error(mid, FFErr::Syn, error);
                }

                // invalid fd or lack of support for sync
                Some(libc::EBADF) | Some(libc::EINVAL) => return new_error(mid, FFErr::Hcf, error),

                // read-only file (can also be caused by TOCTOU)
                Some(libc::EROFS) => return new_error(mid, FFErr::Wrt, error),

                // fatel error, i.e. no sync for writes in recent window/batch
                Some(libc::EIO) => return new_error(mid, FFErr::Syn, error),

                _ => return new_error(mid, FFErr::Unk, error),
            }
        }

        return Ok(());
    }
}

/// perform `F_FULLSYNC` on given file `FD`
///
/// **NOTE:** This function is `macos` only
///
/// ## Why do we retry?
///
/// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases,
/// no progress is guaranteed, so the syscall must be retried
///
/// For reliability, we retry on `EINTR` w/o busy waiting to avoid strain on resources
///
/// ## Durability Guaranty
///
/// `fsync()` does not provide instant durability on mac. So, we use `fcntl(F_FULLFSYNC)` as it
/// forces data to stable storage
///
/// `fcntl(F_FULLSYNC)` may result in `EINVAL` or `ENOTSUP` on fs which does not support full flush,
/// such as _network filesystems, FUSE mounts, FAT32 volumes, or some external devices_
///
/// To guard this, we fallback to `fsync()`, which does not guaranty durability for sudden crash or
/// power loss, which is acceptable when _strong durability is not available or allowed_
#[inline(always)]
#[cfg(target_os = "macos")]
unsafe fn fullsync_raw(fd: c_int, mid: u8) -> FRes<()> {
    // only for EINTR errors
    let mut retries = 0;

    loop {
        if hints::unlikely(libc::fcntl(fd, libc::F_FULLFSYNC) != 0) {
            let error = last_os_error();

            match error.raw_os_error() {
                // IO interrupt
                Some(EINTR) => {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // NOTE: sync error indicates that retries exhausted and durability is broken
                    // in the current/last window/batch
                    return new_error(mid, FFErr::Syn, error);
                }

                // lack of support for `F_FULLSYNC` (must fallback to fsync)
                Some(libc::EINVAL) | Some(libc::ENOTSUP) | Some(libc::EOPNOTSUPP) => break,

                // invalid fd
                Some(EBADF) => return new_error(mid, FFErr::Hcf, error),

                // read-only file (can also be caused by TOCTOU)
                Some(EROFS) => return new_error(mid, FFErr::Wrt, error),

                // fatel error, i.e. no sync for writes in recent window/batch
                Some(EIO) => return new_error(mid, FFErr::Syn, error),

                _ => return new_error(mid, FFErr::Unk, error),
            }
        }

        return Ok(());
    }

    // NOTE: As a fallback to `F_FULLFSYNC` we use `fsync`
    //
    // HACK: On mac, fsync does NOT mean "data is on disk". The drive is still free to cache,
    // reorder, and generally do whatever it wants with your supposedly "synced" data. But for us,
    // this is the least-bad fallback when `F_FULLFSYNC` isn’t supported or working
    fsync_raw(fd, mid)
}

/// perform `fdatasync` on given `FD` (can be File or Directory)
///
/// **NOTE:** This function is `linux` only
///
/// ## Why do we retry?
///
/// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases,
/// no progress is guaranteed, so the syscall must be retried
///
/// For reliability, we retry on `EINTR` w/o busy waiting to avoid strain on resources
///
/// ## Combination of `O_NOATIME` and `fdatasync()`
///
/// On linux, we can use combination of `O_NOATIME` and `fdatasync()` for persistence, while
/// avoiding non-essential metadata updates, such as access time (`atime`), modification time (`mtime`),
/// and other bookkeeping info
///
/// But, not all systems support use of `O_NOATIME` (including macos), in such caces we use `fsync` as fallback
#[cfg(target_os = "linux")]
unsafe fn fdatasync_raw(fd: FD, mid: u8) -> FRes<()> {
    // only for EIO & EINTR errors
    let mut retries = 0;
    loop {
        if hints::unlikely(libc::fdatasync(fd) != 0) {
            let error = last_os_error();
            match error.raw_os_error() {
                // IO interrupt (must retry)
                Some(EINTR) => {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // NOTE: sync error indicates that retries exhausted and durability is broken
                    // in the current/last window/batch
                    return new_error(mid, FFErr::Syn, error);
                }

                // invalid fd or lack of support for sync
                Some(EINVAL) | Some(EBADF) => return new_error(mid, FFErr::Hcf, error),

                // read-only file (can also be caused by TOCTOU)
                Some(EROFS) => return new_error(mid, FFErr::Wrt, error),

                // fatel error, i.e. no sync for writes in recent window/batch
                //
                // NOTE: this must be handled seperately, cuase, if this error occurs,
                // the storage system must act, mark recent writes as failed or notify users,
                // etc. to keep the system robust and fault tolerent!
                Some(EIO) => {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // NOTE: sync error indicates that retries exhausted and durability is broken
                    // in the current/last window/batch
                    return new_error(mid, FFErr::Syn, error);
                }

                _ => return new_error(mid, FFErr::Unk, error),
            }
        }

        return Ok(());
    }
}

/// perform `fsync` for parent directory of file at given `path`
///
/// ## Why
///
/// On POSIX, `open(O_CREATE)` only creates the directory entry in memory, it may be visible
/// immediately, but it's existence is not crash durable
///
/// Therefore, `fsync(parent_dir)` is required to make file creation durable
///
/// On Linux, journaling fs (ext4, xfs, etc) often replay their journal on mount after a crash,
/// which usually restores recent directory updates, as a result newly created file often survives
/// the crash
///
/// But for strong guaranty and reliability, we perform `fsync(parent_dir)`
unsafe fn sync_parent_dir(path: &path::PathBuf, mid: u8) -> FRes<()> {
    let parent = match path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => path::Path::new("."),
    };

    let fd = open_raw(&parent.to_path_buf(), O_RDONLY | O_CLOEXEC, mid)?;
    let res = fsync_raw(fd, mid);
    close_raw(fd, mid)?;

    res
}

/// prep flags for `open` syscall
///
/// ## Access Time Updates (O_NOATIME)
///
/// We use the `O_NOATIME` flag (**Linux Only**) to disable access time updates on the [`POSIXFile`]
/// Normally every I/O operation triggers an `atime` update/write to disk
///
/// This is counter productive and increases latency for I/O ops in our case!
///
/// ## Limitations of `O_NOATIME`
///
/// Macos does not support this flag
///
/// On Linux, not all filesystems support this flag on Linux either, on many it is silently ignored,
/// but some rejects it with `EPERM` error
///
/// The flag only works when the UID's are matched for calling processe and file owner
const fn prep_flags(is_new: bool) -> FD {
    const NEW: FD = O_CREAT | O_TRUNC;

    // NOTE: `O_NOATIME` is not supported on `macos`

    #[cfg(target_os = "macos")]
    const BASE: FD = O_RDWR | O_CLOEXEC;

    #[cfg(target_os = "linux")]
    const BASE: FD = O_RDWR | O_CLOEXEC | libc::O_NOATIME;

    BASE | ((is_new as FD) * NEW)
}

fn path_to_cstring(path: &path::PathBuf, mid: u8) -> FRes<ffi::CString> {
    match ffi::CString::new(path.as_os_str().as_bytes()) {
        Ok(cs) => Ok(cs),
        Err(e) => {
            let error = io::Error::new(io::ErrorKind::Other, e.to_string());
            new_error(mid, FFErr::Inv, error)
        }
    }
}

#[inline]
fn last_os_error() -> std::io::Error {
    io::Error::last_os_error()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fe::{from_err_code, FECheckOk, MID};
    use std::fs;
    use std::os::unix::fs::PermissionsExt;
    use tempfile::{tempdir, TempDir};

    fn new_tmp() -> (TempDir, path::PathBuf, POSIXFile) {
        let dir = tempdir().expect("temp dir");
        let tmp = dir.path().join("tmp_file");
        let file = unsafe { POSIXFile::new(&tmp, MID) }.expect("new POSIXFile");

        (dir, tmp, file)
    }

    mod file_new_and_open {
        use super::*;

        #[test]
        fn new_works() {
            let (_dir, tmp, file) = new_tmp();
            assert!(file.fd() >= 0);

            // sanity check
            assert!(tmp.exists());
            assert!(unsafe { file.close(MID).check_ok() });
        }

        #[test]
        fn open_works() {
            let (_dir, tmp, file) = new_tmp();
            unsafe {
                assert!(file.fd() >= 0);
                assert!(file.close(MID).check_ok());

                match POSIXFile::open(&tmp, MID) {
                    Ok(file) => {
                        assert!(file.fd() >= 0);
                        assert!(file.close(MID).check_ok());
                    }
                    Err(e) => panic!("failed to open file due to E: {:?}", e),
                }
            }
        }

        #[test]
        fn open_fails_when_file_is_unlinked() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.fd() >= 0);
                assert!(file.close(MID).check_ok());
                assert!(file.unlink(&tmp, MID).check_ok());

                let file = POSIXFile::open(&tmp, MID);
                assert!(file.is_err());
            }
        }

        #[test]
        fn open_fails_when_no_permissions() {
            // NOTE: When running as root (UID 0), perm (read & write) checks are bypassed
            if unsafe { libc::geteuid() } == 0 {
                panic!("Tests must not run as root (UID 0); root bypasses Unix file permission checks");
            }

            let (_dir, tmp, file) = new_tmp();

            // remove all permissions
            unsafe { assert!(file.close(MID).check_ok()) };
            fs::set_permissions(&tmp, fs::Permissions::from_mode(0o000)).expect("chmod");

            // re-open
            let res = unsafe { POSIXFile::open(&tmp, MID) };

            assert!(res.is_err());
            let err = res.err().expect("must fail");

            let (_, _, code) = from_err_code(err.code);
            assert_eq!(code, FFErr::Red as u16);
        }

        #[test]
        fn open_fails_when_read_only_file() {
            // NOTE: When running as root (UID 0), perm (read & write) checks are bypassed
            if unsafe { libc::geteuid() } == 0 {
                panic!("Tests must not run as root (UID 0); root bypasses Unix file permission checks");
            }

            let (_dir, tmp, file) = new_tmp();

            // read-only permission
            unsafe { assert!(file.close(MID).check_ok()) };
            fs::set_permissions(&tmp, fs::Permissions::from_mode(0o400)).expect("chmod");

            // re-open
            let res = unsafe { POSIXFile::open(&tmp, MID) };

            assert!(res.is_err());
            let err = res.err().expect("must fail");

            let (_, _, code) = from_err_code(err.code);
            assert_eq!(code, FFErr::Red as u16);
        }

        #[test]
        fn open_fails_on_directory() {
            let dir = tempdir().expect("temp dir");
            let path = dir.path().to_path_buf();

            let res = unsafe { POSIXFile::open(&path, MID) };
            assert!(res.is_err());

            let err = res.err().expect("must fail");
            let (_, _, code) = from_err_code(err.code);

            // opening directory with O_RDWR (EISDIR)
            assert_eq!(code, FFErr::Hcf as u16);
        }

        #[test]
        fn new_works_on_existing_file() {
            let (dir, tmp, file) = new_tmp();

            unsafe {
                file.grow(0, 0x800, MID).expect("grow");
                assert!(file.close(MID).check_ok());
            }

            let file2 = unsafe { POSIXFile::new(&tmp, MID) }.expect("recreate");

            unsafe {
                let len = file2.length(MID).expect("length");

                assert_eq!(len, 0);
                assert!(file2.close(MID).check_ok());
            }

            drop(dir);
        }

        #[test]
        fn new_fails_on_missing_parent_directory() {
            let dir = tempdir().expect("temp dir");
            let path = dir.path().join("missing").join("file");

            let res = unsafe { POSIXFile::new(&path, MID) };
            assert!(res.is_err());

            let err = res.err().expect("must fail");
            let (_, _, code) = from_err_code(err.code);
            assert_eq!(code, FFErr::Inv as u16);
        }
    }

    mod file_close {
        use super::*;

        #[test]
        fn close_works() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.close(MID).check_ok());

                // sanity check
                assert!(tmp.exists());
            }
        }

        #[test]
        fn close_after_close_does_not_fail() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                // should never fail
                assert!(file.close(MID).check_ok());
                assert!(file.close(MID).check_ok());
                assert!(file.close(MID).check_ok());

                // sanity check
                assert!(tmp.exists());
            }

            // NOTE: We need this protection, cause in multithreaded env's, more then one thread
            // could try to close the file at same time, hence the system should not panic in these cases
        }
    }

    mod length_and_grow {
        use super::*;

        #[test]
        fn length_initially_zero() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                let len = file.length(MID).expect("length must work");

                assert_eq!(len, 0);
                assert!(file.close(MID).check_ok());
            }
        }

        #[test]
        fn grow_increases_length() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                let curr = file.length(MID).expect("length must work");
                file.grow(curr, 0x400, MID).expect("grow must work");

                let new_len = file.length(MID).expect("length after grow");
                assert_eq!(new_len, curr + 0x400);

                assert!(file.close(MID).check_ok());
            }
        }

        #[test]
        fn grow_multiple_times() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                let mut total = 0;
                for _ in 0..4 {
                    file.grow(total, 0x100, MID).expect("grow step");
                    total += 0x100;
                }

                let len = file.length(MID).expect("length after grows");
                assert_eq!(len, total);

                assert!(file.close(MID).check_ok());
            }
        }
    }

    mod file_sync {
        use super::*;

        #[test]
        fn sync_works() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                assert!(file.sync(MID).check_ok());
                assert!(file.close(MID).check_ok());
            }
        }

        #[test]
        fn file_sync_for_file_at_current_dir() {
            let dir = tempdir().expect("temp dir");

            let old = std::env::current_dir().expect("cwd");
            std::env::set_current_dir(dir.path()).expect("set cwd");

            let rel = path::PathBuf::from("rel_file");
            let file = unsafe { POSIXFile::new(&rel, MID) }.expect("create relative file");

            unsafe {
                assert!(file.sync(MID).check_ok());
                assert!(file.close(MID).check_ok());
            }

            assert!(rel.exists());
            std::env::set_current_dir(old).expect("restore cwd");
        }
    }

    mod file_unlink {
        use super::*;

        #[test]
        fn unlink_removes_file() {
            let (_dir, tmp, file) = new_tmp();

            unsafe { assert!(file.unlink(&tmp, MID).check_ok()) };
            assert!(!tmp.exists());
        }

        #[test]
        fn unlink_twice_is_error() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.unlink(&tmp, MID).check_ok());
                assert!(file.unlink(&tmp, MID).is_err());
            }
        }

        #[test]
        fn unlink_after_close_is_safe() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.close(MID).check_ok());
                assert!(file.unlink(&tmp, MID).check_ok());
            }

            assert!(!tmp.exists());
        }
    }

    mod file_access_after_close {
        use super::*;

        #[test]
        fn length_after_close_fails() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                assert!(file.close(MID).check_ok());

                let res = file.length(MID);
                assert!(res.is_err());

                let err = res.err().expect("must fail");
                let (_, _, code) = from_err_code(err.code);

                // closed fd (EBADF)
                assert_eq!(code, FFErr::Hcf as u16);
            }
        }

        #[test]
        fn grow_after_close_fails() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                assert!(file.close(MID).check_ok());

                let res = file.grow(0, 0x1000, MID);
                assert!(res.is_err());

                let err = res.err().expect("must fail");
                let (_, _, code) = from_err_code(err.code);

                assert_eq!(code, FFErr::Hcf as u16);
            }
        }

        #[test]
        fn sync_after_close_fails() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                assert!(file.close(MID).check_ok());

                let res = file.sync(MID);
                assert!(res.is_err());

                let err = res.err().expect("must fail");
                let (_, _, code) = from_err_code(err.code);

                assert_eq!(code, FFErr::Hcf as u16);
            }
        }
    }
}
