use super::{new_err, FFileErrCtx};
use crate::{error::FrozenRes, hints};
use alloc::{ffi::CString, vec::Vec};
use core::{ffi::CStr, sync::atomic};
use libc::{
    c_int, c_uint, close, fstat, ftruncate, off_t, open, stat, unlink, EACCES, EBADF, EFAULT, EINTR, EINVAL, EIO,
    EISDIR, ENOENT, ENOSPC, ENOTDIR, EPERM, EROFS, O_CLOEXEC, O_CREAT, O_RDWR, S_IRUSR, S_IWUSR,
};

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
    pub(super) unsafe fn new(path: &[u8]) -> FrozenRes<Self> {
        let fd = open_raw(path, prep_flags())?;

        // NOTE: On POSIX, `open(O_CREATE)` only creates the directory entry in memory,
        // it may be visible immediately, but it's existence is not crash durable, for
        // crash safe durability, we must do `fsync(file)` or `fcntl(F_FULLSYNC)`

        #[cfg(target_os = "linux")]
        fsync_raw(fd)?;

        #[cfg(target_os = "macos")]
        fullsync_raw(fd)?;

        Ok(Self(atomic::AtomicI32::new(fd)))
    }

    /// Close [`POSIXFile`] to give up file descriptor
    ///
    /// ## Multiple Calls
    ///
    /// This function is idempotent, hence it prevents close-on-close errors
    ///
    /// ## Sync Error (`FFileErrCtx::Syn`)
    ///
    /// In POSIX systems, kernal may report delayed write/sync failures when closing, this are
    /// durability errors, fatel in nature
    ///
    /// when these errors are detected, error w/ `FFileErrCtx::Syn` is thrown, this must be handled by
    /// the storage engine to keep durability intact
    #[inline(always)]
    pub(super) unsafe fn close(&self) -> FrozenRes<()> {
        let fd = self.0.swap(CLOSED_FD, atomic::Ordering::AcqRel);
        if fd == CLOSED_FD {
            return Ok(());
        }

        close_raw(fd)
    }

    /// Unlinks (possibly deletes) the [`POSIXFile`]
    #[inline]
    pub(super) unsafe fn unlink(&self, path: &[u8]) -> FrozenRes<()> {
        let cpath = path_to_cstring(path)?;

        // NOTE: POSIX systems requires fd to be closed before attempting to unlink the file
        self.close()?;

        if unlink(cpath.as_ptr()) == 0 {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // missing file or invalid path
            ENOENT | ENOTDIR => return new_err(FFileErrCtx::Inv, err_msg),

            // lack of permission
            EACCES | EPERM => return new_err(FFileErrCtx::Red, err_msg),

            // read only fs
            EROFS => return new_err(FFileErrCtx::Wrt, err_msg),

            // IO error (durability failure)
            EIO => return new_err(FFileErrCtx::Syn, err_msg),

            _ => return new_err(FFileErrCtx::Unk, err_msg),
        }
    }

    /// Read current length of [`POSIXFile`] using file metadata (w/ `fstat` syscall)
    #[inline(always)]
    pub(super) unsafe fn length(&self) -> FrozenRes<u64> {
        let mut st = core::mem::zeroed::<stat>();
        let res = fstat(self.fd(), &mut st);

        if res != 0 {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            // bad or invalid fd
            if errno == EBADF || errno == EFAULT {
                return new_err(FFileErrCtx::Hcf, err_msg);
            }

            return new_err(FFileErrCtx::Unk, err_msg);
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
    pub(super) unsafe fn grow(&self, curr_len: u64, len_to_add: u64) -> FrozenRes<()> {
        let fd = self.fd();
        let new_len = (curr_len + len_to_add) as off_t;

        #[cfg(target_os = "linux")]
        {
            let mut retries = 0;
            loop {
                if hints::likely(libc::fallocate(fd, 0, curr_len as off_t, len_to_add as off_t) == 0) {
                    return Ok(());
                }

                let errno = last_errno();
                let err_msg = err_msg(errno);

                match errno {
                    // IO interrupt
                    EINTR => {
                        if retries < MAX_RETRIES {
                            retries += 1;
                            continue;
                        }

                        break;
                    }

                    // invalid fd
                    libc::EBADF => return new_err(FFileErrCtx::Hcf, err_msg),

                    // read-only fs (can also be caused by TOCTOU)
                    libc::EROFS => return new_err(FFileErrCtx::Wrt, err_msg),

                    // no space available on disk
                    libc::ENOSPC => return new_err(FFileErrCtx::Nsp, err_msg),

                    // lack of support for `fallocate` (fall through to ftruncate)
                    libc::EINVAL | libc::EOPNOTSUPP | libc::ENOSYS => break,

                    _ => return new_err(FFileErrCtx::Unk, err_msg),
                }
            }
        }

        let res = ftruncate(fd, new_len);
        if res == 0 {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // invalid fd or lack of support for sync
            EINVAL | EBADF => return new_err(FFileErrCtx::Hcf, err_msg),

            // read-only fs (can also be caused by TOCTOU)
            EROFS => return new_err(FFileErrCtx::Wrt, err_msg),

            // no space available on disk
            ENOSPC => return new_err(FFileErrCtx::Nsp, err_msg),

            _ => return new_err(FFileErrCtx::Unk, err_msg),
        }
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
    pub(super) unsafe fn sync(&self) -> FrozenRes<()> {
        fullsync_raw(self.fd() as c_int)
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
    pub(super) unsafe fn sync(&self) -> FrozenRes<()> {
        fdatasync_raw(self.fd())
    }
}

/// create/open a new file w/ `open` syscall
///
/// ## Caveats of `O_NOATIME` (`EPERM` err_msg)
///
/// `open()` with `O_NOATIME` may fail with `EPERM` instead of silently ignoring the flag
///
/// `EPERM` indicates a kernel level permission violation, as the kernel rejects the
/// request outright, even though the flag only affects metadata behavior
///
/// To remain sane across ownership models, containers, and shared filesystems,
/// we explicitly retry the `open()` w/o `O_NOATIME` when `EPERM` is encountered
unsafe fn open_raw(path: &[u8], flags: FD) -> FrozenRes<FD> {
    let cpath = path_to_cstring(path)?;

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
            let errno = last_errno();
            let err_msg = err_msg(errno);

            // NOTE: Fallback for `EPERM` error, when `O_NOATIME` is not supported by current FS
            #[cfg(target_os = "linux")]
            {
                if errno == EPERM && (flags & libc::O_NOATIME) != 0 && !tried_noatime {
                    flags &= !libc::O_NOATIME;
                    tried_noatime = true;
                    continue;
                }
            }

            match errno {
                // NOTE: We must retry on interuption errors (EINTR retry)
                EINTR => continue,

                // no space available on disk
                ENOSPC => return new_err(FFileErrCtx::Nsp, err_msg),

                // path is a dir (hcf)
                EISDIR => return new_err(FFileErrCtx::Hcf, err_msg),

                // invalid path (missing sub dir's)
                ENOENT | ENOTDIR => return new_err(FFileErrCtx::Inv, err_msg),

                // permission denied
                EACCES | EPERM => return new_err(FFileErrCtx::Red, err_msg),

                // read-only fs
                EROFS => return new_err(FFileErrCtx::Wrt, err_msg),

                _ => return new_err(FFileErrCtx::Unk, err_msg),
            }
        }

        return Ok(fd);
    }
}

/// close a file or dir via given `fd`
unsafe fn close_raw(fd: FD) -> FrozenRes<()> {
    if close(fd) != 0 {
        let errno = last_errno();
        let err_msg = err_msg(errno);

        // NOTE: In POSIX systems, kernal may report delayed writeback failures on `close`,
        // this are fatel errors, and can not be retried! Hence, all the writes in the sync
        // window were not persisted.
        //
        // So we treat this error as **sync** error, to notify above layer as the recent batch
        // failed to persist!
        if errno == EIO {
            return new_err(FFileErrCtx::Syn, err_msg);
        }

        return new_err(FFileErrCtx::Unk, err_msg);
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
unsafe fn fsync_raw(fd: FD) -> FrozenRes<()> {
    // only for EINTR errors
    let mut retries = 0;
    loop {
        if hints::unlikely(libc::fsync(fd) != 0) {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            match errno {
                // IO interrupt
                EINTR => {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // NOTE: sync error indicates that retries exhausted and durability is broken
                    // in the current/last window/batch
                    return new_err(FFileErrCtx::Syn, err_msg);
                }

                // invalid fd or lack of support for sync
                libc::EBADF | libc::EINVAL => return new_err(FFileErrCtx::Hcf, err_msg),

                // read-only file (can also be caused by TOCTOU)
                libc::EROFS => return new_err(FFileErrCtx::Wrt, err_msg),

                // fatel error, i.e. no sync for writes in recent window/batch
                libc::EIO => return new_err(FFileErrCtx::Syn, err_msg),

                _ => return new_err(FFileErrCtx::Unk, err_msg),
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
unsafe fn fullsync_raw(fd: c_int) -> FrozenRes<()> {
    // only for EINTR errors
    let mut retries = 0;

    loop {
        if hints::unlikely(libc::fcntl(fd, libc::F_FULLFSYNC) != 0) {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            match errno {
                // IO interrupt
                EINTR => {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // NOTE: sync error indicates that retries exhausted and durability is broken
                    // in the current/last window/batch
                    return new_err(FFileErrCtx::Syn, err_msg);
                }

                // lack of support for `F_FULLSYNC` (must fallback to fsync)
                libc::EINVAL | libc::ENOTSUP | libc::EOPNOTSUPP => break,

                // invalid fd
                EBADF => return new_err(FFileErrCtx::Hcf, err_msg),

                // read-only file (can also be caused by TOCTOU)
                EROFS => return new_err(FFileErrCtx::Wrt, err_msg),

                // fatel error, i.e. no sync for writes in recent window/batch
                EIO => return new_err(FFileErrCtx::Syn, err_msg),

                _ => return new_err(FFileErrCtx::Unk, err_msg),
            }
        }

        return Ok(());
    }

    // NOTE: As a fallback to `F_FULLFSYNC` we use `fsync`
    //
    // HACK: On mac, fsync does NOT mean "data is on disk". The drive is still free to cache,
    // reorder, and generally do whatever it wants with your supposedly "synced" data. But for us,
    // this is the least-bad fallback when `F_FULLFSYNC` isn’t supported or working
    fsync_raw(fd)
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
unsafe fn fdatasync_raw(fd: FD) -> FrozenRes<()> {
    // only for EIO & EINTR errors
    let mut retries = 0;
    loop {
        if hints::unlikely(libc::fdatasync(fd) != 0) {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            match errno {
                // IO interrupt (must retry)
                EINTR => {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // NOTE: sync error indicates that retries exhausted and durability is broken
                    // in the current/last window/batch
                    return new_err(FFileErrCtx::Syn, err_msg);
                }

                // invalid fd or lack of support for sync
                EINVAL | EBADF => return new_err(FFileErrCtx::Hcf, err_msg),

                // read-only file (can also be caused by TOCTOU)
                EROFS => return new_err(FFileErrCtx::Wrt, err_msg),

                // fatel error, i.e. no sync for writes in recent window/batch
                //
                // NOTE: this must be handled seperately, cuase, if this error occurs,
                // the storage system must act, mark recent writes as failed or notify users,
                // etc. to keep the system robust and fault tolerent!
                EIO => {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // NOTE: sync error indicates that retries exhausted and durability is broken
                    // in the current/last window/batch
                    return new_err(FFileErrCtx::Syn, err_msg);
                }

                _ => return new_err(FFileErrCtx::Unk, err_msg),
            }
        }

        return Ok(());
    }
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
const fn prep_flags() -> FD {
    #[cfg(target_os = "linux")]
    return O_RDWR | O_CLOEXEC | libc::O_NOATIME | O_CREAT;

    // NOTE: `O_NOATIME` is not supported on `macos`

    #[cfg(target_os = "macos")]
    return O_RDWR | O_CLOEXEC | O_CREAT;
}

fn path_to_cstring(path: &[u8]) -> FrozenRes<CString> {
    match CString::new(path) {
        Ok(cs) => Ok(cs),
        Err(e) => new_err(FFileErrCtx::Inv, e.into_vec()),
    }
}

#[inline]
fn last_errno() -> i32 {
    #[cfg(target_os = "linux")]
    unsafe {
        *libc::__errno_location()
    }

    #[cfg(target_os = "macos")]
    unsafe {
        *libc::__error()
    }
}

#[inline]
unsafe fn err_msg(errno: i32) -> Vec<u8> {
    const BUF_LEN: usize = 0x100;
    let mut buf = [0i8; BUF_LEN];

    if libc::strerror_r(errno, buf.as_mut_ptr(), BUF_LEN) != 0 {
        return Vec::new();
    }

    let cstr = CStr::from_ptr(buf.as_ptr());
    return cstr.to_bytes().to_vec();
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;
    use std::{fs, os::unix::ffi::OsStrExt, path::PathBuf};
    use tempfile::{tempdir, TempDir};

    fn new_tmp() -> (TempDir, PathBuf, POSIXFile) {
        let dir = tempdir().expect("temp dir");
        let tmp = dir.path().join("tmp_file");

        let file = unsafe { POSIXFile::new(tmp.as_os_str().as_bytes()) }.expect("new POSIXFile");

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
            assert!(unsafe { file.close().is_ok() });
        }

        #[test]
        fn open_works() {
            let (_dir, tmp, file) = new_tmp();
            unsafe {
                assert!(file.fd() >= 0);
                assert!(file.close().is_ok());

                match POSIXFile::new(tmp.as_os_str().as_bytes()) {
                    Ok(file) => {
                        assert!(file.fd() >= 0);
                        assert!(file.close().is_ok());
                    }
                    Err(e) => panic!("failed to open file due to E: {:?}", e),
                }
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
            unsafe { assert!(file.close().is_ok()) };
            fs::set_permissions(&tmp, fs::Permissions::from_mode(0o000)).expect("chmod");

            // re-open
            let res = unsafe { POSIXFile::new(tmp.as_os_str().as_bytes()) };

            let err = res.err().expect("must fail");
            assert!(err.cmp(FFileErrCtx::Red as u16));
        }

        #[test]
        fn open_fails_when_read_only_file() {
            // NOTE: When running as root (UID 0), perm (read & write) checks are bypassed
            if unsafe { libc::geteuid() } == 0 {
                panic!("Tests must not run as root (UID 0); root bypasses Unix file permission checks");
            }

            let (_dir, tmp, file) = new_tmp();

            // read-only permission
            unsafe { assert!(file.close().is_ok()) };
            fs::set_permissions(&tmp, fs::Permissions::from_mode(0o400)).expect("chmod");

            // re-open
            let res = unsafe { POSIXFile::new(tmp.as_os_str().as_bytes()) };

            let err = res.err().expect("must fail");
            assert!(err.cmp(FFileErrCtx::Red as u16));
        }

        #[test]
        fn open_fails_on_directory() {
            let dir = tempdir().expect("temp dir");
            let path = dir.path().to_path_buf();

            let res = unsafe { POSIXFile::new(path.as_os_str().as_bytes()) };
            assert!(res.is_err());

            // opening directory with O_RDWR (EISDIR)
            let err = res.err().expect("must fail");
            assert!(err.cmp(FFileErrCtx::Hcf as u16));
        }

        #[test]
        fn open_does_not_truncates_file() {
            let (dir, tmp, file) = new_tmp();

            unsafe {
                file.grow(0, 0x800).expect("grow");
                assert!(file.close().is_ok());
            }

            let file2 = unsafe { POSIXFile::new(tmp.as_os_str().as_bytes()) }.expect("recreate");

            unsafe {
                let len = file2.length().expect("length");
                assert_eq!(len, 0x800);
                assert!(file2.close().is_ok());
            }

            drop(dir);
        }

        #[test]
        fn new_fails_on_missing_parent_directory() {
            let dir = tempdir().expect("temp dir");
            let path = dir.path().join("missing").join("file");

            let res = unsafe { POSIXFile::new(&path.as_os_str().as_bytes()) };
            let err = res.err().expect("must fail");
            assert!(err.cmp(FFileErrCtx::Inv as u16));
        }
    }

    mod file_close {
        use super::*;

        #[test]
        fn close_works() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.close().is_ok());

                // sanity check
                assert!(tmp.exists());
            }
        }

        #[test]
        fn close_after_close_does_not_fail() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                // should never fail
                assert!(file.close().is_ok());
                assert!(file.close().is_ok());
                assert!(file.close().is_ok());

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
                let len = file.length().expect("length must work");

                assert_eq!(len, 0);
                assert!(file.close().is_ok());
            }
        }

        #[test]
        fn grow_increases_length() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                let curr = file.length().expect("length must work");
                file.grow(curr, 0x400).expect("grow must work");

                let new_len = file.length().expect("length after grow");
                assert_eq!(new_len, curr + 0x400);

                assert!(file.close().is_ok());
            }
        }

        #[test]
        fn grow_multiple_times() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                let mut total = 0;
                for _ in 0..4 {
                    file.grow(total, 0x100).expect("grow step");
                    total += 0x100;
                }

                let len = file.length().expect("length after grows");
                assert_eq!(len, total);

                assert!(file.close().is_ok());
            }
        }
    }

    mod file_sync {
        use super::*;

        #[test]
        fn sync_works() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                assert!(file.sync().is_ok());
                assert!(file.close().is_ok());
            }
        }

        #[test]
        fn file_sync_for_file_at_current_dir() {
            let dir = tempdir().expect("temp dir");

            let old = std::env::current_dir().expect("cwd");
            std::env::set_current_dir(dir.path()).expect("set cwd");

            let rel = PathBuf::from("rel_file");
            let file = unsafe { POSIXFile::new(rel.as_os_str().as_bytes()) }.expect("create relative file");

            unsafe {
                assert!(file.sync().is_ok());
                assert!(file.close().is_ok());
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

            unsafe { assert!(file.unlink(tmp.as_os_str().as_bytes(),).is_ok()) };
            assert!(!tmp.exists());
        }

        #[test]
        fn unlink_twice_is_error() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.unlink(tmp.as_os_str().as_bytes(),).is_ok());
                assert!(file.unlink(tmp.as_os_str().as_bytes(),).is_err());
            }
        }

        #[test]
        fn unlink_after_close_is_safe() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.close().is_ok());
                assert!(file.unlink(tmp.as_os_str().as_bytes(),).is_ok());
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
                assert!(file.close().is_ok());

                let res = file.length();
                assert!(res.is_err());

                // closed fd (EBADF)
                let err = res.err().expect("must fail");
                assert!(err.cmp(FFileErrCtx::Hcf as u16));
            }
        }

        #[test]
        fn grow_after_close_fails() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                assert!(file.close().is_ok());

                let res = file.grow(0, 0x1000);
                let err = res.err().expect("must fail");
                assert!(err.cmp(FFileErrCtx::Hcf as u16));
            }
        }

        #[test]
        fn sync_after_close_fails() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                assert!(file.close().is_ok());

                let res = file.sync();
                let err = res.err().expect("must fail");
                assert!(err.cmp(FFileErrCtx::Hcf as u16));
            }
        }
    }
}
