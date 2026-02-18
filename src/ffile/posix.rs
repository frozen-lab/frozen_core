use super::{new_err, FFileErrRes};
use crate::{error::FrozenRes, hints};
use alloc::{ffi::CString, vec::Vec};
use core::{ffi::CStr, sync::atomic};
use libc::{
    access, c_char, c_int, c_uint, c_void, close, fstat, ftruncate, off_t, open, pread, pwrite, size_t, stat, unlink,
    EACCES, EBADF, EFAULT, EINTR, EINVAL, EIO, EISDIR, ENOENT, ENOSPC, ENOTDIR, EPERM, EROFS, ESPIPE, F_OK, O_CLOEXEC,
    O_CREAT, O_RDWR, S_IRUSR, S_IWUSR,
};

/// type for file descriptor on POSIX systems
type FD = c_int;

const CLOSED_FD: FD = -1;
const MAX_RETRIES: usize = 6; // max allowed retries for `EINTR` errors

/// Raw implementation of Posix (linux & macos) file for [`FrozenFile`]
#[derive(Debug)]
pub(super) struct POSIXFile(atomic::AtomicI32);

unsafe impl Send for POSIXFile {}
unsafe impl Sync for POSIXFile {}

impl POSIXFile {
    /// Get the file descriptor of [`POSIXFile`]
    #[inline]
    pub(super) fn fd(&self) -> FD {
        self.0.load(atomic::Ordering::Acquire)
    }

    /// check if [`POSIXFile`] exists on storage device or not
    ///
    /// ## Working
    ///
    /// This performs a POSIX `access(2)` syscall with `F_OK`, which checks whether the
    /// calling process can resolve the path in the filesystem
    #[inline]
    pub(super) unsafe fn exists(path: &[u8]) -> FrozenRes<bool> {
        let cpath = path_to_cstring(path)?;
        Ok(access(cpath.as_ptr(), F_OK) == 0)
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
    /// ## Sync Error (`FFileErrRes::Syn`)
    ///
    /// In POSIX systems, kernal may report delayed write/sync failures when closing, this are
    /// durability errors, fatel in nature
    ///
    /// when these errors are detected, error w/ `FFileErrRes::Syn` is thrown, this must be handled by
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
            ENOENT | ENOTDIR => return new_err(FFileErrRes::Inv, err_msg),

            // lack of permission
            EACCES | EPERM => return new_err(FFileErrRes::Red, err_msg),

            // read only fs
            EROFS => return new_err(FFileErrRes::Wrt, err_msg),

            // IO error (durability failure)
            EIO => return new_err(FFileErrRes::Syn, err_msg),

            _ => return new_err(FFileErrRes::Unk, err_msg),
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
                return new_err(FFileErrRes::Hcf, err_msg);
            }

            return new_err(FFileErrRes::Unk, err_msg);
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
                    libc::EBADF => return new_err(FFileErrRes::Hcf, err_msg),

                    // read-only fs (can also be caused by TOCTOU)
                    libc::EROFS => return new_err(FFileErrRes::Wrt, err_msg),

                    // no space available on disk
                    libc::ENOSPC => return new_err(FFileErrRes::Nsp, err_msg),

                    // lack of support for `fallocate` (fall through to ftruncate)
                    libc::EINVAL | libc::EOPNOTSUPP | libc::ENOSYS => break,

                    _ => return new_err(FFileErrRes::Unk, err_msg),
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
            EINVAL | EBADF => return new_err(FFileErrRes::Hcf, err_msg),

            // read-only fs (can also be caused by TOCTOU)
            EROFS => return new_err(FFileErrRes::Wrt, err_msg),

            // no space available on disk
            ENOSPC => return new_err(FFileErrRes::Nsp, err_msg),

            _ => return new_err(FFileErrRes::Unk, err_msg),
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

    /// Read at given `offset` w/ `pread` syscall from [`POSIXFile`]
    #[inline(always)]
    pub(super) unsafe fn pread(&self, buf_ptr: *mut u8, offset: usize, len_to_read: usize) -> FrozenRes<()> {
        let mut read = 0usize;
        while read < len_to_read {
            let res = pread(
                self.fd(),
                buf_ptr.add(read) as *mut c_void,
                (len_to_read - read) as libc::size_t,
                (offset + read) as i64,
            );

            if hints::unlikely(res <= 0) {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                match errno {
                    // unexpected EOF
                    0 => return new_err(FFileErrRes::Eof, err_msg),

                    // io interrupt
                    EINTR => continue,

                    EACCES | EPERM => return new_err(FFileErrRes::Red, err_msg),

                    // invalid fd, invalid fd type, bad pointer, etc.
                    EINVAL | EBADF | EFAULT | ESPIPE => return new_err(FFileErrRes::Hcf, err_msg),

                    _ => return new_err(FFileErrRes::Unk, err_msg),
                }
            }

            read += res as usize;
        }

        Ok(())
    }

    /// Write at given `offset` w/ `pwrite` syscall to [`POSIXFile`]
    #[inline(always)]
    pub(super) unsafe fn pwrite(&self, buf_ptr: *const u8, offset: usize, len_to_write: usize) -> FrozenRes<()> {
        let mut written = 0usize;
        while written < len_to_write {
            let res = pwrite(
                self.fd(),
                buf_ptr.add(written) as *const c_void,
                (len_to_write - written) as size_t,
                (offset + written) as i64,
            );

            if hints::unlikely(res <= 0) {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                match errno {
                    // unexpected EOF
                    0 => return new_err(FFileErrRes::Eof, err_msg),

                    // io interrupt
                    EINTR => continue,

                    EACCES | EPERM => return new_err(FFileErrRes::Red, err_msg),

                    // invalid fd, invalid fd type, bad pointer, etc.
                    EINVAL | EBADF | EFAULT | ESPIPE => return new_err(FFileErrRes::Hcf, err_msg),

                    _ => return new_err(FFileErrRes::Unk, err_msg),
                }
            }

            written += res as usize;
        }

        Ok(())
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
                ENOSPC => return new_err(FFileErrRes::Nsp, err_msg),

                // path is a dir (hcf)
                EISDIR => return new_err(FFileErrRes::Hcf, err_msg),

                // invalid path (missing sub dir's)
                ENOENT | ENOTDIR => return new_err(FFileErrRes::Inv, err_msg),

                // permission denied
                EACCES | EPERM => return new_err(FFileErrRes::Red, err_msg),

                // read-only fs
                EROFS => return new_err(FFileErrRes::Wrt, err_msg),

                _ => return new_err(FFileErrRes::Unk, err_msg),
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
            return new_err(FFileErrRes::Syn, err_msg);
        }

        return new_err(FFileErrRes::Unk, err_msg);
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
                    return new_err(FFileErrRes::Syn, err_msg);
                }

                // invalid fd or lack of support for sync
                libc::EBADF | libc::EINVAL => return new_err(FFileErrRes::Hcf, err_msg),

                // read-only file (can also be caused by TOCTOU)
                libc::EROFS => return new_err(FFileErrRes::Wrt, err_msg),

                // fatel error, i.e. no sync for writes in recent window/batch
                libc::EIO => return new_err(FFileErrRes::Syn, err_msg),

                _ => return new_err(FFileErrRes::Unk, err_msg),
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
                    return new_err(FFileErrRes::Syn, err_msg);
                }

                // lack of support for `F_FULLSYNC` (must fallback to fsync)
                libc::EINVAL | libc::ENOTSUP | libc::EOPNOTSUPP => break,

                // invalid fd
                EBADF => return new_err(FFileErrRes::Hcf, err_msg),

                // read-only file (can also be caused by TOCTOU)
                EROFS => return new_err(FFileErrRes::Wrt, err_msg),

                // fatel error, i.e. no sync for writes in recent window/batch
                EIO => return new_err(FFileErrRes::Syn, err_msg),

                _ => return new_err(FFileErrRes::Unk, err_msg),
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
                    return new_err(FFileErrRes::Syn, err_msg);
                }

                // invalid fd or lack of support for sync
                EINVAL | EBADF => return new_err(FFileErrRes::Hcf, err_msg),

                // read-only file (can also be caused by TOCTOU)
                EROFS => return new_err(FFileErrRes::Wrt, err_msg),

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
                    return new_err(FFileErrRes::Syn, err_msg);
                }

                _ => return new_err(FFileErrRes::Unk, err_msg),
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
        Err(e) => new_err(FFileErrRes::Inv, e.into_vec()),
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
    let mut buf = [c_char::default(); BUF_LEN];

    if libc::strerror_r(errno, buf.as_mut_ptr(), BUF_LEN) != 0 {
        return Vec::new();
    }

    let cstr = CStr::from_ptr(buf.as_ptr());
    return cstr.to_bytes().to_vec();
}

#[cfg(test)]
mod tests {
    use super::*;

    fn new_tmp(id: &'static [u8]) -> (Vec<u8>, POSIXFile) {
        let mut path = Vec::with_capacity(b"./target/".len() + id.len());
        path.extend_from_slice(b"./target/");
        path.extend_from_slice(id);

        let file = unsafe { POSIXFile::new(&path).expect("new POSIXFile") };

        (path, file)
    }

    mod posix_new {
        use super::*;

        #[test]
        fn new_create_a_file() {
            let (path, file) = new_tmp(b"ffile_new");
            assert!(file.fd() >= 0);

            unsafe { file.unlink(&path) }.expect("unlink file");
        }

        #[test]
        fn new_opens_existing_file() {
            let (path, file) = new_tmp(b"ffile_open");

            assert!(file.fd() >= 0);
            unsafe { file.close() }.expect("close file");

            unsafe {
                match POSIXFile::new(&path) {
                    Ok(file) => {
                        assert!(file.fd() >= 0);
                        file.unlink(&path).expect("unlink file");
                    }
                    Err(e) => panic!("failed to open file due to E: {:?}", e),
                }
            }
        }

        #[test]
        fn new_creates_file_with_len_zero() {
            let (path, file) = new_tmp(b"ffile_new_len");
            assert!(file.fd() >= 0);

            unsafe {
                assert_eq!(file.length().expect("read len"), 0);
                file.unlink(&path).expect("unlink file");
            }
        }

        #[test]
        fn new_preserves_existing_len() {
            const LEN: u64 = 0x100;
            let (path, file) = new_tmp(b"ffile_open_len");

            unsafe {
                file.grow(0, LEN).expect("grow");
                file.close().expect("close file");
            }

            let file2 = unsafe { POSIXFile::new(&path) }.expect("open existing");
            unsafe {
                let len = file2.length().expect("length");
                assert_eq!(len, LEN);
                file2.unlink(&path).expect("unlink file");
            }
        }

        #[test]
        fn new_fails_on_dirpath() {
            unsafe { POSIXFile::new(b"./target/") }.expect_err("must fail");
        }
    }

    mod posix_close_unlink {
        use super::*;

        #[test]
        fn close_works() {
            let (path, file) = new_tmp(b"ffile_close_works");

            unsafe {
                file.close().expect("close file");
                assert_eq!(file.fd(), CLOSED_FD);
                file.unlink(&path).expect("unlink file");
            }
        }

        #[test]
        fn unlink_works() {
            let (path, file) = new_tmp(b"ffile_unlink_works");

            unsafe {
                file.unlink(&path).expect("unlink file");
                assert_eq!(file.fd(), CLOSED_FD);

                let exists = POSIXFile::exists(&path).expect("check exists");
                assert!(!exists);
            }
        }
    }

    mod posix_length_grow {
        use super::*;

        #[test]
        fn grow_works() {
            let (path, file) = new_tmp(b"ffile_grow_works");

            unsafe {
                file.grow(0, 0x80).expect("grow");
                file.unlink(&path).expect("unlink file");
            }
        }

        #[test]
        fn grow_updates_length() {
            let (path, file) = new_tmp(b"ffile_grow_length");

            unsafe {
                file.grow(0, 0x80).expect("grow");
                assert_eq!(file.length().expect("read len"), 0x80);
                file.unlink(&path).expect("unlink file");
            }
        }

        #[test]
        fn grow_after_grow() {
            let (path, file) = new_tmp(b"ffile_grow_after_grow");

            unsafe {
                let mut total = 0;
                for _ in 0..4 {
                    file.grow(total, 0x100).expect("grow step");
                    total += 0x100;
                }

                assert_eq!(file.length().expect("read len"), total);
                file.unlink(&path).expect("unlink file");
            }
        }
    }
}
