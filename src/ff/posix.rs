use super::{new_error, FFErr};
use crate::fe::FRes;
use libc::{
    c_int, c_uint, c_void, close, fstat, ftruncate, iovec, off_t, open, preadv, pwritev, stat, sysconf, unlink, EACCES,
    EBADF, EDQUOT, EFAULT, EINTR, EINVAL, EIO, EISDIR, EMSGSIZE, ENOENT, ENOSPC, ENOTDIR, EPERM, EROFS, ESPIPE,
    O_CLOEXEC, O_CREAT, O_RDONLY, O_RDWR, O_TRUNC, S_IRUSR, S_IWUSR, _SC_IOV_MAX,
};
use std::{
    ffi, io,
    os::unix::ffi::OsStrExt,
    path,
    sync::{self, atomic},
};

/// type for file descriptor on POSIX systems
type FD = c_int;

const CLOSED_FD: FD = -1;
const MAX_RETRIES: usize = 6; // max allowed retries for `EINTR` errors
const MAX_IOVECS: usize = 512; // max iovecs allowed for single readv/writev calls

static IOV_MAX_CACHE: sync::OnceLock<usize> = sync::OnceLock::new();

/// Linux implementation of `POSIXFile`
pub(super) struct POSIXFile(atomic::AtomicI32);

unsafe impl Send for POSIXFile {}
unsafe impl Sync for POSIXFile {}

impl POSIXFile {
    /// creates/opens a new instance of [`POSIXFile`]
    ///
    /// ## Errors
    ///
    /// - `FFErr::Inv` is thrown when the given `path` is either invalid or missing sub-dir's
    pub(super) unsafe fn new(path: &path::PathBuf, is_new: bool, mid: u8) -> FRes<Self> {
        let fd = open_raw(path, prep_flags(is_new), mid)?;

        if is_new {
            #[cfg(target_os = "macos")]
            fullsync_raw(fd, mid)?;

            #[cfg(target_os = "linux")]
            fsync_raw(fd, mid)?;

            sync_parent_dir(path, mid)?;
        }

        Ok(Self(atomic::AtomicI32::new(fd)))
    }

    /// Get file descriptor for [`POSIXFile`]
    #[inline]
    pub(super) fn fd(&self) -> FD {
        self.0.load(atomic::Ordering::Acquire)
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
        // sanity check
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxPOSIXFile");
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
        // sanity check
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxPOSIXFile");

        let fd = self.fd() as c_int;
        fdatasync_raw(fd, mid)
    }

    /// Closes file handle for [`POSIXFile`]
    ///
    /// This function is _idempotent_ and prevents close-on-close errors!
    #[inline(always)]
    pub(super) unsafe fn close(&self, mid: u8) -> FRes<()> {
        // prevent multiple close syscalls
        let fd = self.0.swap(CLOSED_FD, atomic::Ordering::AcqRel);
        if fd == CLOSED_FD {
            return Ok(());
        }

        close_raw(fd, mid)
    }

    /// Unlinks (possibly deletes) the [`POSIXFile`]
    ///
    /// **WARN**: POSIXFile must be closed beforehand, to avoid I/O errors
    #[inline]
    pub(super) unsafe fn unlink(&self, path: &path::PathBuf, mid: u8) -> FRes<()> {
        let cpath = path_to_cstring(path, mid)?;
        if unlink(cpath.as_ptr()) != 0 {
            let error = last_os_error();
            return new_error(mid, FFErr::Unk, error);
        }

        Ok(())
    }

    /// Fetches current length of [`POSIXFile`] using `fstat` syscall
    #[inline(always)]
    pub(super) unsafe fn length(&self, mid: u8) -> FRes<u64> {
        // sanity check
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxPOSIXFile");

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

    /// Resize [`POSIXFile`] w/ `new_len`
    #[inline(always)]
    pub(super) unsafe fn resize(&self, new_len: u64, mid: u8) -> FRes<()> {
        // sanity check
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxPOSIXFile");

        if ftruncate(self.fd(), new_len as off_t) != 0 {
            let error = last_os_error();
            let error_raw = error.raw_os_error();

            // invalid fd or lack of support for sync
            if error_raw == Some(EINVAL) || error_raw == Some(EBADF) {
                return new_error(mid, FFErr::Hcf, error);
            }

            // read-only fs (can also be caused by TOCTOU)
            if error_raw == Some(EROFS) {
                return new_error(mid, FFErr::Wrt, error);
            }

            // no space available on disk
            if error_raw == Some(ENOSPC) {
                return new_error(mid, FFErr::Nsp, error);
            }

            return new_error(mid, FFErr::Unk, error);
        }

        Ok(())
    }

    /// Read (multiple vectors) at given `offset` w/ `preadv` syscall from [`POSIXFile`]
    #[inline(always)]
    pub(super) unsafe fn preadv(&self, iovecs: &mut [iovec], offset: usize, mid: u8) -> FRes<()> {
        // sanity checks
        #[cfg(debug_assertions)]
        {
            debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxPOSIXFile");
            debug_assert_ne!(iovecs.len(), 0, "iovecs must not be empty");

            let iov_len = iovecs[0].iov_len;
            debug_assert_ne!(iov_len, 0, "invalid iov length");

            for iov in iovecs.iter() {
                debug_assert_eq!(iov_len, iov.iov_len, "all iov's must be of same length");
            }
        }

        let fd = self.fd();
        let max_iovs = max_iovecs();
        let iovecs_len = iovecs.len();
        let iov_size = iovecs[0].iov_len;

        let mut head = 0usize;
        let mut consumed = 0usize;

        while head < iovecs_len {
            let remaining_iov = iovecs_len - head;
            let cnt = remaining_iov.min(max_iovs) as c_int;
            let ptr = iovecs.as_ptr().add(head);

            let res = preadv(fd, ptr, cnt, offset as off_t + consumed as off_t);
            if res <= 0 {
                let error = io::Error::last_os_error();
                let error_raw = error.raw_os_error();

                // interrupted syscall
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }

                // unexpected EOF
                if res == 0 {
                    return new_error(mid, FFErr::Eof, error);
                }

                // permission denied
                if error_raw == Some(EACCES) || error_raw == Some(EPERM) {
                    return new_error(mid, FFErr::Red, error);
                }

                // invalid fd, bad pointer, illegal seek, etc.
                if error_raw == Some(EINVAL)
                    || error_raw == Some(EBADF)
                    || error_raw == Some(EFAULT)
                    || error_raw == Some(ESPIPE)
                    || error_raw == Some(EMSGSIZE)
                {
                    return new_error(mid, FFErr::Hcf, error);
                }

                return new_error(mid, FFErr::Unk, error);
            }

            // NOTE: In POSIX systems, preadv may -
            //
            // - read fewer bytes than requested
            // - stop in-between iovec's
            // - stop mid iovec
            //
            // Even though this behavior is situation or filesystem dependent (according to my short research),
            // we opt to handle it for correctness across different systems

            let written = res as usize;
            let full_pages = written / iov_size;
            let partial = written % iov_size;

            // fully written pages
            head += full_pages;
            consumed += full_pages * iov_size;

            // partially written page (rare)
            if partial > 0 {
                let iov = &mut iovecs[head];
                iov.iov_base = (iov.iov_base as *mut u8).add(partial) as *mut c_void;
                iov.iov_len -= partial;
                consumed += partial;
            }
        }

        Ok(())
    }

    /// Write (multiple vectors) at given `offset` w/ `pwritev` syscall to [`POSIXFile`]
    #[inline(always)]
    pub(super) unsafe fn pwritev(&self, iovecs: &mut [iovec], offset: usize, mid: u8) -> FRes<()> {
        // sanity checks
        #[cfg(debug_assertions)]
        {
            debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxPOSIXFile");
            debug_assert_ne!(iovecs.len(), 0, "iovecs must not be empty");

            let iov_len = iovecs[0].iov_len;
            debug_assert_ne!(iov_len, 0, "invalid iov length");

            for iov in iovecs.iter() {
                debug_assert_eq!(iov_len, iov.iov_len, "all iov's must be of same length");
            }
        }

        let fd = self.fd();
        let max_iovs = max_iovecs();
        let iovecs_len = iovecs.len();
        let iov_size = iovecs[0].iov_len;

        let mut head = 0usize;
        let mut consumed = 0usize;

        while head < iovecs_len {
            let remaining_iov = iovecs_len - head;
            let cnt = remaining_iov.min(max_iovs) as c_int;
            let ptr = iovecs.as_ptr().add(head);

            let res = pwritev(fd, ptr, cnt, offset as off_t + consumed as off_t);
            if res <= 0 {
                let error = std::io::Error::last_os_error();
                let error_raw = error.raw_os_error();

                // io interrupt
                if error.kind() == std::io::ErrorKind::Interrupted {
                    continue;
                }

                // unexpected EOF
                if res == 0 {
                    return new_error(mid, FFErr::Eof, error);
                }

                // read-only file (can also be caused by TOCTOU)
                if error_raw == Some(EROFS) {
                    return new_error(mid, FFErr::Wrt, error);
                }

                // no space available on disk
                if error_raw == Some(ENOSPC) || error_raw == Some(EDQUOT) {
                    return new_error(mid, FFErr::Nsp, error);
                }

                // invalid fd, invalid fd type, bad pointer, etc.
                if error_raw == Some(EINVAL)
                    || error_raw == Some(EBADF)
                    || error_raw == Some(EFAULT)
                    || error_raw == Some(ESPIPE)
                    || error_raw == Some(EMSGSIZE)
                {
                    return new_error(mid, FFErr::Hcf, error);
                }

                return new_error(mid, FFErr::Unk, error);
            }

            // NOTE: In POSIX systems, pwritev may -
            //
            // - write fewer bytes than requested
            // - stop in-between iovec's
            // - stop mid iovec
            //
            // Even though this behavior is situation or filesystem dependent (according to my short research),
            // we opt to handle it for correctness across different systems

            let written = res as usize;
            let full_pages = written / iov_size;
            let partial = written % iov_size;

            // fully written pages
            head += full_pages;
            consumed += full_pages * iov_size;

            // partially written page (rare)
            if partial > 0 {
                let iov = &mut iovecs[head];
                iov.iov_base = (iov.iov_base as *mut u8).add(partial) as *mut c_void;
                iov.iov_len -= partial;
                consumed += partial;
            }
        }

        Ok(())
    }

    /// Read at given `offset` w/ `pread` syscall from [`POSIXFile`]
    #[cfg(test)]
    #[inline(always)]
    unsafe fn pread(&self, buf_ptr: *mut u8, offset: usize, len_to_read: usize, mid: u8) -> FRes<()> {
        // sanity checks
        debug_assert_ne!(len_to_read, 0, "invalid length");
        debug_assert!(!buf_ptr.is_null(), "invalid buffer pointer");
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxPOSIXFile");

        let mut read = 0usize;
        while read < len_to_read {
            let res = libc::pread(
                self.fd(),
                buf_ptr.add(read) as *mut c_void,
                (len_to_read - read) as libc::size_t,
                (offset + read) as i64,
            );

            if res <= 0 {
                let error = std::io::Error::last_os_error();
                let error_raw = error.raw_os_error();

                // io interrupt
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }

                // unexpected EOF
                if res == 0 {
                    return new_error(mid, FFErr::Eof, error);
                }

                // permission denied
                if error_raw == Some(EACCES) || error_raw == Some(EPERM) {
                    return new_error(mid, FFErr::Red, error);
                }

                // invalid fd, invalid fd type, bad pointer, etc.
                if error_raw == Some(EINVAL)
                    || error_raw == Some(EBADF)
                    || error_raw == Some(EFAULT)
                    || error_raw == Some(ESPIPE)
                {
                    return new_error(mid, FFErr::Hcf, error);
                }

                return new_error(mid, FFErr::Unk, error);
            }

            read += res as usize;
        }

        Ok(())
    }

    /// Write at given `offset` w/ `pwrite` syscall to [`POSIXFile`]
    #[cfg(test)]
    #[inline(always)]
    unsafe fn pwrite(&self, buf_ptr: *const u8, offset: usize, len_to_write: usize, mid: u8) -> FRes<()> {
        // sanity checks
        debug_assert_ne!(len_to_write, 0, "invalid length");
        debug_assert!(!buf_ptr.is_null(), "invalid buffer pointer");
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxPOSIXFile");

        let mut written = 0usize;
        while written < len_to_write {
            let res = libc::pwrite(
                self.fd(),
                buf_ptr.add(written) as *const c_void,
                (len_to_write - written) as libc::size_t,
                (offset + written) as i64,
            );

            if res <= 0 {
                let error = std::io::Error::last_os_error();
                let error_raw = error.raw_os_error();

                // io interrupt
                if error.kind() == std::io::ErrorKind::Interrupted {
                    continue;
                }

                // unexpected EOF
                if res == 0 {
                    return new_error(mid, FFErr::Eof, error);
                }

                // read-only file (can also be caused by TOCTOU)
                if error_raw == Some(EROFS) {
                    return new_error(mid, FFErr::Wrt, error);
                }

                // invalid fd, invalid fd type, bad pointer, etc.
                if error_raw == Some(EINVAL)
                    || error_raw == Some(EBADF)
                    || error_raw == Some(EFAULT)
                    || error_raw == Some(ESPIPE)
                {
                    return new_error(mid, FFErr::Hcf, error);
                }

                return new_error(mid, FFErr::Unk, error);
            }

            written += res as usize;
        }

        Ok(())
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

        if fd < 0 {
            let error = last_os_error();
            let err_raw = error.raw_os_error();

            // NOTE: We must retry on interuption errors (EINTR retry)
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }

            // NOTE: Fallback for `EPERM` error, when `O_NOATIME` is not supported by current FS
            #[cfg(target_os = "linux")]
            {
                if err_raw == Some(EPERM) && (flags & libc::O_NOATIME) != 0 && !tried_noatime {
                    flags &= !libc::O_NOATIME;
                    tried_noatime = true;
                    continue;
                }
            }

            // no space available on disk
            if err_raw == Some(ENOSPC) {
                return new_error(mid, FFErr::Nsp, error);
            }

            // path is a dir (hcf)
            if err_raw == Some(EISDIR) {
                return new_error(mid, FFErr::Hcf, error);
            }

            // invalid path (missing sub dir's)
            if err_raw == Some(ENOENT) || err_raw == Some(ENOTDIR) {
                return new_error(mid, FFErr::Inv, error);
            }

            // permission denied
            if err_raw == Some(EACCES) || err_raw == Some(EPERM) {
                return new_error(mid, FFErr::Red, error);
            }

            // read-only fs
            if err_raw == Some(EROFS) {
                return new_error(mid, FFErr::Wrt, error);
            }

            return new_error(mid, FFErr::Unk, error);
        }

        return Ok(fd);
    }
}

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
        if libc::fsync(fd) != 0 {
            let error = last_os_error();
            let error_raw = error.raw_os_error();

            // IO interrupt
            if error_raw == Some(EINTR) {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_error(mid, FFErr::Syn, error);
            }

            // invalid fd or lack of support for sync
            if error_raw == Some(libc::EBADF) || error_raw == Some(libc::EINVAL) {
                return new_error(mid, FFErr::Hcf, error);
            }

            // read-only file (can also be caused by TOCTOU)
            if error_raw == Some(libc::EROFS) {
                return new_error(mid, FFErr::Wrt, error);
            }

            // fatel error, i.e. no sync for writes in recent window/batch
            if error_raw == Some(libc::EIO) {
                return new_error(mid, FFErr::Syn, error);
            }

            return new_error(mid, FFErr::Unk, error);
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
        if libc::fcntl(fd, libc::F_FULLFSYNC) != 0 {
            let error = last_os_error();
            let error_raw = error.raw_os_error();

            // IO interrupt
            if error_raw == Some(EINTR) {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_error(mid, FFErr::Syn, error);
            }

            // lack of support for `F_FULLSYNC` (must fallback to fsync)
            if error_raw == Some(libc::EINVAL)
                || error_raw == Some(libc::ENOTSUP)
                || error_raw == Some(libc::EOPNOTSUPP)
            {
                break;
            }

            // invalid fd
            if error_raw == Some(EBADF) {
                return new_error(mid, FFErr::Hcf, error);
            }

            // read-only file (can also be caused by TOCTOU)
            if error_raw == Some(EROFS) {
                return new_error(mid, FFErr::Wrt, error);
            }

            // fatel error, i.e. no sync for writes in recent window/batch
            if error_raw == Some(EIO) {
                return new_error(mid, FFErr::Syn, error);
            }

            return new_error(mid, FFErr::Unk, error);
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

/// perform `fsync` on given `FD` (can be File or Directory)
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
/// But, not all systems support
///
/// We use `fdatasync()` instead of `fsync()` for persistence, as `fdatasync()` guarantees,
/// all modified file data and any metadata required to retrieve that data, like file size
/// changes are flushed to stable storage
///
/// This way we avoid non-essential metadata updates, such as access time (`atime`),
/// mod time (`mtime`), and other inode bookkeeping info
#[cfg(target_os = "linux")]
unsafe fn fdatasync_raw(fd: FD, mid: u8) -> FRes<()> {
    // only for EIO & EINTR errors

    use libc::EINTR;
    let mut retries = 0;
    loop {
        if libc::fdatasync(fd) != 0 {
            let error = last_os_error();
            let error_raw = error.raw_os_error();

            // IO interrupt (must retry)
            if error_raw == Some(EINTR) {
                continue;
            }

            // invalid fd or lack of support for sync
            if error_raw == Some(EINVAL) || error_raw == Some(EBADF) {
                return new_error(mid, FFErr::Hcf, error);
            }

            // read-only file (can also be caused by TOCTOU)
            if error_raw == Some(EROFS) {
                return new_error(mid, FFErr::Wrt, error);
            }

            // fatel error, i.e. no sync for writes in recent window/batch
            //
            // NOTE: this must be handled seperately, cuase, if this error occurs,
            // the storage system must act, mark recent writes as failed or notify users,
            // etc. to keep the system robust and fault tolerent!
            if error_raw == Some(EIO) {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_error(mid, FFErr::Syn, error);
            }

            return new_error(mid, FFErr::Unk, error);
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

/// fetch max allowed `iovecs` per `preadv` & `pwritev` syscalls
fn max_iovecs() -> usize {
    *IOV_MAX_CACHE.get_or_init(|| unsafe {
        let res = sysconf(_SC_IOV_MAX);
        if res <= 0 {
            MAX_IOVECS
        } else {
            res as usize
        }
    })
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
    use crate::fe::{FECheckOk, MID};
    use std::fs;
    use std::os::unix::fs::PermissionsExt;
    use tempfile::{tempdir, TempDir};

    fn new_tmp() -> (TempDir, path::PathBuf, POSIXFile) {
        let dir = tempdir().expect("temp dir");
        let tmp = dir.path().join("tmp_file");
        let file = unsafe { POSIXFile::new(&tmp, true, MID) }.expect("new LinuxPOSIXFile");

        (dir, tmp, file)
    }

    mod new_open {
        use super::*;
        use crate::fe::from_err_code;

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

                match POSIXFile::new(&tmp, false, MID) {
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

                let file = POSIXFile::new(&tmp, false, MID);
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
            let res = unsafe { POSIXFile::new(&tmp, false, MID) };

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
            let res = unsafe { POSIXFile::new(&tmp, false, MID) };

            assert!(res.is_err());
            let err = res.err().expect("must fail");

            let (_, _, code) = from_err_code(err.code);
            assert_eq!(code, FFErr::Red as u16);
        }
    }

    mod close {
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

    mod sync {
        use super::*;

        #[test]
        fn sync_works() {
            let (_dir, _tmp, file) = new_tmp();

            unsafe {
                assert!(file.sync(MID).check_ok());
                assert!(file.close(MID).check_ok());
            }
        }
    }

    mod unlink {
        use super::*;

        #[test]
        fn unlink_correctly_deletes_file() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.close(MID).check_ok());
                assert!(file.unlink(&tmp, MID).check_ok());
                assert!(!tmp.exists());
            }
        }

        #[test]
        fn unlink_fails_on_unlinked_file() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.close(MID).check_ok());
                assert!(file.unlink(&tmp, MID).check_ok());
                assert!(!tmp.exists());

                // should fail on missing
                assert!(file.unlink(&tmp, MID).is_err());
            }
        }
    }

    mod resize {
        use super::*;

        #[test]
        fn extend_zero_extends_file() {
            const NEW_LEN: u64 = 0x80;
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.resize(NEW_LEN, MID).check_ok());

                let curr_len = file.length(MID).expect("fetch metadata");
                assert_eq!(curr_len, NEW_LEN);
                assert!(file.close(MID).check_ok());
            }

            // strict sanity check to ensure file is zero byte extended
            let file_contents = std::fs::read(&tmp).expect("read from file");
            assert_eq!(file_contents.len(), NEW_LEN as usize, "len mismatch for file");
            assert!(
                file_contents.iter().all(|b| *b == 0u8),
                "file must be zero byte extended"
            );
        }

        #[test]
        fn open_preserves_existing_length() {
            const NEW_LEN: u64 = 0x80;
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.resize(NEW_LEN, MID).check_ok());

                let curr_len = file.length(MID).expect("fetch metadata");
                assert_eq!(curr_len, NEW_LEN);

                assert!(file.sync(MID).check_ok());
                assert!(file.close(MID).check_ok());

                match POSIXFile::new(&tmp, false, MID) {
                    Err(e) => panic!("{:?}", e),
                    Ok(file) => {
                        let curr_len = file.length(MID).expect("fetch metadata");
                        assert_eq!(curr_len, NEW_LEN);
                    }
                }
            }
        }
    }

    mod write_read {
        use super::*;

        #[test]
        fn pwrite_pread_cycle() {
            let (_dir, _tmp, file) = new_tmp();

            const LEN: usize = 0x20;
            const DATA: [u8; LEN] = [0x1A; LEN];

            unsafe {
                file.resize(LEN as u64, MID).expect("resize file");
                assert!(file.pwrite(DATA.as_ptr(), 0, LEN, MID).check_ok());

                let mut buf = vec![0u8; LEN];
                assert!(file.pread(buf.as_mut_ptr(), 0, LEN, MID).check_ok());
                assert_eq!(DATA.to_vec(), buf, "mismatch between read and write");
                assert!(file.close(MID).check_ok());
            }
        }

        #[test]
        fn pwritev_pread_cycle() {
            let (_dir, _tmp, file) = new_tmp();

            const LEN: usize = 0x20;
            const DATA: [u8; LEN] = [0x1A; LEN];

            let ptrs = vec![DATA.as_ptr(); LEN];
            let mut iovecs: Vec<iovec> = ptrs
                .iter()
                .map(|ptr| iovec {
                    iov_base: *ptr as *mut c_void,
                    iov_len: LEN,
                })
                .collect();

            let total_len = ptrs.len() * LEN;

            unsafe {
                file.resize(total_len as u64, MID).expect("resize file");
                assert!(file.pwritev(&mut iovecs, 0, MID).check_ok());

                let mut buf = vec![0u8; total_len];
                assert!(
                    file.pread(buf.as_mut_ptr(), 0, total_len, MID).check_ok(),
                    "pread failed"
                );
                assert_eq!(buf.len(), total_len, "mismatch between read and write");

                for chunk in buf.chunks_exact(LEN) {
                    assert_eq!(chunk, DATA, "data mismatch in pwritev readback");
                }

                assert!(file.close(MID).check_ok());
            }
        }

        #[test]
        fn pwritev_preadv_cycle() {
            let (_dir, _tmp, file) = new_tmp();

            const LEN: usize = 0x20;
            const DATA: [u8; LEN] = [0x1A; LEN];

            let ptrs = vec![DATA.as_ptr(); LEN];
            let mut iovecs: Vec<iovec> = ptrs
                .iter()
                .map(|ptr| iovec {
                    iov_base: *ptr as *mut c_void,
                    iov_len: LEN,
                })
                .collect();
            let total_len = ptrs.len() * LEN;

            unsafe {
                file.resize(total_len as u64, MID).expect("resize file");
                assert!(file.pwritev(&mut iovecs, 0, MID).check_ok());

                let mut read_bufs: Vec<Vec<u8>> = (0..LEN).map(|_| vec![0u8; LEN]).collect();
                let mut read_iovecs: Vec<iovec> = read_bufs
                    .iter_mut()
                    .map(|buf| iovec {
                        iov_base: buf.as_mut_ptr() as *mut c_void,
                        iov_len: LEN,
                    })
                    .collect();

                assert!(file.preadv(&mut read_iovecs, 0, MID).check_ok(), "preadv failed");

                // verify each buffer
                for buf in read_bufs.iter() {
                    assert_eq!(buf.as_slice(), &DATA, "data mismatch in pwritev/preadv cycle");
                }

                assert!(file.close(MID).check_ok());
            }
        }

        #[test]
        fn pwrite_pread_cycle_across_sessions() {
            let (_dir, tmp, file) = new_tmp();

            const LEN: usize = 0x20;
            const DATA: [u8; LEN] = [0x1A; LEN];

            // create + write + sync + close
            unsafe {
                assert!(file.resize(LEN as u64, MID).check_ok());
                assert!(file.pwrite(DATA.as_ptr(), 0, LEN, MID).check_ok());

                assert!(file.sync(MID).check_ok());
                assert!(file.close(MID).check_ok());
            }

            // open + read + verify
            unsafe {
                let mut buf = vec![0u8; LEN];
                let file = POSIXFile::new(&tmp, false, MID).expect("open file");

                assert!(file.pread(buf.as_mut_ptr(), 0, LEN, MID).check_ok());
                assert_eq!(DATA.to_vec(), buf, "mismatch between read and write");
                assert!(file.close(MID).check_ok());
            }
        }
    }

    mod concurrency {
        use super::*;

        #[test]
        fn concurrent_writes_then_read() {
            const THREADS: usize = 8;
            const CHUNK: usize = 0x100;

            let (_dir, _tmp, file) = new_tmp();
            let file = std::sync::Arc::new(file);

            // required len
            unsafe { file.resize((THREADS * CHUNK) as u64, MID).expect("extend") };

            let mut handles = Vec::new();
            for i in 0..THREADS {
                let f = file.clone();
                handles.push(std::thread::spawn(move || {
                    let data = vec![i as u8; CHUNK];
                    unsafe { f.pwrite(data.as_ptr(), i * CHUNK, CHUNK, MID).expect("write") };
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

            //
            // read back (sanity check)
            //

            let mut read_buf = vec![0u8; THREADS * CHUNK];
            unsafe { assert!(file.pread(read_buf.as_mut_ptr(), 0, read_buf.len(), MID).check_ok()) };

            for i in 0..THREADS {
                let chunk = &read_buf[i * CHUNK..(i + 1) * CHUNK];
                assert!(chunk.iter().all(|b| *b == i as u8));
            }
        }
    }
}
