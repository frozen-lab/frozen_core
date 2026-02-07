use crate::error::{new_error, FFErr};
use fe::{FErr, FRes};
use libc::{
    c_int, c_short, c_void, close, fcntl, fdatasync, flock, fstat, ftruncate, iovec, off_t, open, pread, preadv,
    pwrite, pwritev, size_t, stat, sysconf, unlink, EACCES, EBADF, EDQUOT, EFAULT, EINVAL, EIO, EISDIR, EMSGSIZE,
    ENOSPC, EPERM, EROFS, ESPIPE, F_SETLKW, F_UNLCK, F_WRLCK, O_CLOEXEC, O_CREAT, O_NOATIME, O_RDWR, O_TRUNC, SEEK_SET,
    S_IRUSR, S_IWUSR, _SC_IOV_MAX,
};
use std::{
    ffi::CString,
    io,
    os::unix::ffi::OsStrExt,
    path::PathBuf,
    sync::atomic::{AtomicI32, Ordering},
};

const CLOSED_FD: i32 = -1;
const MAX_IOVECS: usize = 512;

/// Linux implementation of `File`
pub(crate) struct File(AtomicI32);

unsafe impl Send for File {}
unsafe impl Sync for File {}

impl File {
    /// creates/opens a new instance of [`File`]
    pub(crate) unsafe fn new(path: &PathBuf, is_new: bool, mid: u8) -> FRes<Self> {
        let fd = open_with_flags(path, prep_flags(is_new), mid)?;
        Ok(Self(AtomicI32::new(fd)))
    }

    /// Get file descriptor for [`File`]
    #[inline]
    pub(crate) fn fd(&self) -> i32 {
        self.0.load(Ordering::Acquire)
    }

    /// fetch value of maximum iovecs allowed in preadv/pwritev syscalls
    ///
    /// **NOTE:** On some systems, `_SC_IOV_MAX` is not set, hence it can return `-1`
    pub(crate) unsafe fn max_iovecs(&self) -> usize {
        let res = sysconf(_SC_IOV_MAX);
        if res <= 0 {
            return MAX_IOVECS;
        }

        res as usize
    }

    /// Syncs in-mem data on the storage device
    ///
    /// ## `fsync` vs `fdatasync`
    ///
    /// We use `fdatasync()` instead of `fsync()` for persistence. As, `fdatasync()` guarantees,
    /// all modified file data and any metadata required to retrieve that data, like file size
    /// changes are flushed to stable storage.
    ///
    /// This way we avoid non-essential metadata updates, such as access time (`atime`),
    /// mod time (`mtime`), and other inode bookkeeping info!
    #[inline]
    pub(super) unsafe fn sync(&self, mid: u8) -> FRes<()> {
        // sanity check
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxFile");

        // only for EIO errors
        const MAX_RETRIES: usize = 4;
        let mut retries = 0;

        loop {
            if fdatasync(self.fd() as c_int) != 0 {
                let error = last_os_error();
                let error_raw = error.raw_os_error();

                // IO interrupt (must retry)
                if error.kind() == io::ErrorKind::Interrupted {
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
                        std::hint::spin_loop();
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

    /// Closes file handle for [`File`]
    ///
    /// This function is _idempotent_ and prevents close-on-close errors!
    #[inline(always)]
    pub(crate) unsafe fn close(&self, mid: u8) -> FRes<()> {
        // prevent multiple close syscalls
        let fd = self.fd();
        if fd == CLOSED_FD {
            return Ok(());
        }

        if close(fd) != 0 {
            let error = last_os_error();
            let error_raw = error.raw_os_error();

            // NOTE: In posix systems, kernal may report delayed writeback failures on `close`,
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

        self.close_fd();
        Ok(())
    }

    /// Unlinks (possibly deletes) the [`File`]
    ///
    /// **WARN**: File must be closed beforehand, to avoid I/O errors
    #[inline]
    pub(super) unsafe fn unlink(&self, path: &PathBuf, mid: u8) -> FRes<()> {
        let cpath = path_to_cstring(path, mid)?;
        if unlink(cpath.as_ptr()) != 0 {
            let error = last_os_error();
            return new_error(mid, FFErr::Unk, error);
        }

        Ok(())
    }

    /// Fetches matadata for [`File`] using `fstat` syscall
    #[inline]
    pub(crate) unsafe fn metadata(&self, mid: u8) -> FRes<stat> {
        // sanity check
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxFile");

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

        Ok(st)
    }

    pub(crate) unsafe fn resize(&self, new_len: u64, mid: u8) -> FRes<()> {
        // sanity check
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxFile");

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

    /// Read at given `offset` w/ `pread` syscall from [`File`]
    #[inline(always)]
    pub(super) unsafe fn pread(&self, buf_ptr: *mut u8, offset: usize, len_to_read: usize, mid: u8) -> FRes<()> {
        // sanity checks
        debug_assert_ne!(len_to_read, 0, "invalid length");
        debug_assert!(!buf_ptr.is_null(), "invalid buffer pointer");
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxFile");

        let mut read = 0usize;
        while read < len_to_read {
            let res = pread(
                self.fd(),
                buf_ptr.add(read) as *mut c_void,
                (len_to_read - read) as size_t,
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

    /// Read (multiple vectors) at given `offset` w/ `preadv` syscall from [`File`]
    #[inline(always)]
    pub(super) unsafe fn preadv(&self, buf_ptrs: &[*mut u8], offset: usize, buffer_size: usize, mid: u8) -> FRes<()> {
        // sanity checks
        #[cfg(debug_assertions)]
        {
            debug_assert_ne!(buffer_size, 0, "invalid buffer length");
            debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxFile");
            debug_assert!(buf_ptrs.len() <= self.max_iovecs(), "Buffer overflow beyound IOV_MAX");
        }

        let nptrs = buf_ptrs.len();
        let total_len = nptrs * buffer_size;
        let mut iovecs: Vec<iovec> = buf_ptrs
            .iter()
            .map(|ptr| iovec {
                iov_base: *ptr as *mut c_void,
                iov_len: buffer_size,
            })
            .collect();

        let mut read = 0usize;
        while read < total_len {
            let res = preadv(
                self.fd(),
                iovecs.as_ptr(),
                iovecs.len() as c_int,
                (offset + read) as off_t,
            );

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

            // NOTE: In posix systems, preadv may -
            //
            // - read fewer bytes than requested
            // - stop in-between iovec's
            // - stop mid iovec
            //
            // Even though this behavior is situation or filesystem dependent (according to my short research),
            // we opt to handle it for correctness across different systems

            let mut idx = 0;
            let mut remaining = res as usize;

            while remaining > 0 {
                let current_iov = &mut iovecs[idx];
                if remaining >= current_iov.iov_len {
                    read += current_iov.iov_len;
                    remaining -= current_iov.iov_len;
                    idx += 1;
                } else {
                    current_iov.iov_base = (current_iov.iov_base as *mut u8).add(remaining) as *mut c_void;
                    current_iov.iov_len -= remaining;
                    read += remaining;
                    remaining = 0;
                }
            }

            if idx > 0 {
                iovecs.drain(0..idx);
            }
        }

        Ok(())
    }

    /// Write at given `offset` w/ `pwrite` syscall to [`File`]
    #[inline(always)]
    pub(super) unsafe fn pwrite(&self, buf_ptr: *const u8, offset: usize, len_to_write: usize, mid: u8) -> FRes<()> {
        // sanity checks
        debug_assert_ne!(len_to_write, 0, "invalid length");
        debug_assert!(!buf_ptr.is_null(), "invalid buffer pointer");
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxFile");

        let mut written = 0usize;
        while written < len_to_write {
            let res = pwrite(
                self.fd(),
                buf_ptr.add(written) as *const c_void,
                (len_to_write - written) as size_t,
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

    /// Write (multiple vectors) at given `offset` w/ `pwritev` syscall to [`File`]
    #[inline(always)]
    pub(super) unsafe fn pwritev(
        &self,
        buf_ptrs: &[*const u8],
        offset: usize,
        buffer_size: usize,
        mid: u8,
    ) -> FRes<()> {
        // sanity checks
        #[cfg(debug_assertions)]
        {
            debug_assert_ne!(buffer_size, 0, "invalid buffer length");
            debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxFile");
            debug_assert!(buf_ptrs.len() <= self.max_iovecs(), "Buffer overflow beyound IOV_MAX");
        }

        let nptrs = buf_ptrs.len();
        let total_len = nptrs * buffer_size;
        let mut iovecs: Vec<iovec> = buf_ptrs
            .iter()
            .map(|ptr| iovec {
                iov_base: *ptr as *mut c_void,
                iov_len: buffer_size,
            })
            .collect();

        let mut written = 0usize;
        while written < total_len {
            let res = pwritev(
                self.fd(),
                iovecs.as_ptr(),
                iovecs.len() as c_int,
                (offset + written) as off_t,
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

            // NOTE: In posix systems, pwritev may -
            //
            // - write fewer bytes than requested
            // - stop in-between iovec's
            // - stop mid iovec
            //
            // Even though this behavior is situation or filesystem dependent (according to my short research),
            // we opt to handle it for correctness across different systems

            let mut idx = 0;
            let mut remaining = res as usize;

            while remaining > 0 {
                let current_iov = &mut iovecs[idx];
                if remaining >= current_iov.iov_len {
                    idx += 1;
                    written += current_iov.iov_len;
                    remaining -= current_iov.iov_len;
                } else {
                    current_iov.iov_base = (current_iov.iov_base as *mut u8).add(remaining) as *mut c_void;
                    current_iov.iov_len -= remaining;
                    written += remaining;
                    remaining = 0;
                }
            }

            if idx > 0 {
                iovecs.drain(0..idx);
            }
        }

        Ok(())
    }

    /// Acquire an exclusive write lock to [`File`]
    #[inline]
    pub(super) unsafe fn lock(&self, mid: u8) -> FRes<()> {
        // sanity check
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxFile");
        self.flock_impl(F_WRLCK, mid)
    }

    /// Release the acquired lock (shared/exclusive) for [`File`]
    #[inline]
    pub(super) unsafe fn unlock(&self, mid: u8) -> FRes<()> {
        // sanity check
        debug_assert!(self.fd() != CLOSED_FD, "Invalid fd for LinuxFile");
        self.flock_impl(F_UNLCK, mid)
    }

    #[inline]
    unsafe fn flock_impl(&self, lock_type: c_int, mid: u8) -> FRes<()> {
        let mut fl = flock {
            l_type: lock_type as c_short,
            l_whence: SEEK_SET as c_short,
            l_start: 0,
            l_len: 0, // whole file
            l_pid: 0,
        };

        loop {
            if fcntl(self.fd(), F_SETLKW, &mut fl) != 0 {
                let error = io::Error::last_os_error();

                // We must retry on interuption errors, e.g. EINTR
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }

                return new_error(mid, FFErr::Lck, error);
            }

            return Ok(());
        }
    }

    #[inline]
    fn close_fd(&self) {
        self.0.store(CLOSED_FD, Ordering::Release);
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
unsafe fn open_with_flags(path: &PathBuf, mut flags: i32, mid: u8) -> FRes<i32> {
    let cpath = path_to_cstring(path, mid)?;
    let mut tried_noatime = false;

    loop {
        let fd = if flags & O_CREAT != 0 {
            open(
                cpath.as_ptr(),
                flags,
                S_IRUSR | S_IWUSR, // write + read permissions
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
            if err_raw == Some(EPERM) && (flags & O_NOATIME) != 0 && !tried_noatime {
                flags &= !O_NOATIME;
                tried_noatime = true;
                continue;
            }

            // no space available on disk
            if err_raw == Some(ENOSPC) {
                return new_error(mid, FFErr::Nsp, error);
            }

            // path is a dir (hcf)
            if err_raw == Some(EISDIR) {
                return new_error(mid, FFErr::Hcf, error);
            }

            return new_error(mid, FFErr::Unk, error);
        }

        return Ok(fd);
    }
}

/// prep flags for `open` syscall
///
/// ## Access Time Updates (O_NOATIME)
///
/// We use the `O_NOATIME` flag to disable access time updates on the [`File`]
/// Normally every I/O operation triggers an `atime` update/write to disk
///
/// This is counter productive and increases latency for I/O ops in our case!
///
/// ## Limitations of `O_NOATIME`
///
/// Not all filesystems support this flag, on many it is silently ignored, but some rejects
/// it with `EPERM` error
///
/// Also, this flag only works when UID's match for calling processe and file owner
const fn prep_flags(is_new: bool) -> i32 {
    const BASE: i32 = O_RDWR | O_NOATIME | O_CLOEXEC;
    const NEW: i32 = O_CREAT | O_TRUNC;
    BASE | ((is_new as i32) * NEW)
}

fn path_to_cstring(path: &std::path::PathBuf, mid: u8) -> FRes<CString> {
    match CString::new(path.as_os_str().as_bytes()) {
        Ok(cs) => Ok(cs),
        Err(e) => {
            let error = io::Error::new(io::ErrorKind::Other, e.to_string());
            new_error(mid, FFErr::Inv, e.into())
        }
    }
}

#[inline]
fn last_os_error() -> std::io::Error {
    io::Error::last_os_error()
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;
    use fe::FEAsOk;
    use std::path::PathBuf;
    use tempfile::{tempdir, TempDir};

    // module id (test)
    const MID: u8 = 0x00;

    fn new_tmp() -> (TempDir, PathBuf, File) {
        let dir = tempdir().expect("temp dir");
        let tmp = dir.path().join("tmp_file");
        let file = unsafe { File::new(&tmp, true, MID) }.expect("new LinuxFile");

        (dir, tmp, file)
    }

    mod new_open {
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

                match File::new(&tmp, false, MID) {
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

                let file = File::new(&tmp, false, MID);
                assert!(file.is_err());
            }
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
            let (_dir, tmp, file) = new_tmp();

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

                let curr_len = file.metadata(MID).expect("fetch metadata").st_size;
                assert_eq!(curr_len, NEW_LEN as i64);
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

                let curr_len = file.metadata(MID).expect("fetch metadata").st_size;
                assert_eq!(curr_len, NEW_LEN as i64);

                assert!(file.sync(MID).check_ok());
                assert!(file.close(MID).check_ok());

                match File::new(&tmp, false, MID) {
                    Err(e) => panic!("{:?}", e),
                    Ok(file) => {
                        let curr_len = file.metadata(MID).expect("fetch metadata").st_size;
                        assert_eq!(curr_len, NEW_LEN as i64);
                    }
                }
            }
        }
    }

    mod lock_unlock {
        use super::*;

        #[test]
        fn lock_unlock_cycle() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.lock(MID).check_ok());
                assert!(file.unlock(MID).check_ok());

                assert!(file.lock(MID).check_ok());
                assert!(file.unlock(MID).check_ok());

                assert!(file.close(MID).check_ok());
            }
        }

        #[test]
        fn lock_survives_io_operation() {
            let (_dir, tmp, file) = new_tmp();

            unsafe {
                assert!(file.lock(MID).check_ok());

                let data = vec![1u8; 0x20];
                file.resize(data.len() as u64, MID).expect("resize file");
                file.pwrite(data.as_ptr(), 0, data.len(), MID).expect("write to file");

                assert!(file.unlock(MID).check_ok());
                assert!(file.close(MID).check_ok());
            }
        }
    }

    mod write_read {
        use super::*;

        #[test]
        fn pwrite_pread_cycle() {
            let (_dir, tmp, file) = new_tmp();

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
            let (_dir, tmp, file) = new_tmp();

            const LEN: usize = 0x20;
            const DATA: [u8; LEN] = [0x1A; LEN];

            let ptrs = vec![DATA.as_ptr(); 0x10];
            let total_len = ptrs.len() * LEN;

            unsafe {
                file.resize(total_len as u64, MID).expect("resize file");
                assert!(file.pwritev(&ptrs, 0, LEN, MID).check_ok());

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
            let (_dir, tmp, file) = new_tmp();

            const LEN: usize = 0x20;
            const DATA: [u8; LEN] = [0x1A; LEN];

            let ptrs = vec![DATA.as_ptr(); 0x10];
            let total_len = ptrs.len() * LEN;

            unsafe {
                file.resize(total_len as u64, MID).expect("resize file");
                assert!(file.pwritev(&ptrs, 0, LEN, MID).check_ok());

                // prepare read buffers
                let mut bufs: Vec<Vec<u8>> = (0..ptrs.len()).map(|_| vec![0u8; LEN]).collect();
                let mut buf_ptrs: Vec<*mut u8> = bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();

                assert!(file.preadv(&buf_ptrs, 0, LEN, MID).check_ok(), "preadv failed");

                // verify each buffer
                for buf in bufs {
                    assert_eq!(buf, DATA, "data mismatch in pwritev/preadv cycle");
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
                let file = File::new(&tmp, false, MID).expect("open file");

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

        #[test]
        fn concurrent_writes_with_lock() {
            const THREADS: usize = 4;
            const LEN: usize = 0x80;

            let (_dir, _tmp, file) = new_tmp();
            let file = std::sync::Arc::new(file);

            unsafe { file.resize(LEN as u64, MID).expect("extend") };

            let mut handles = Vec::new();
            for _ in 0..THREADS {
                let f = file.clone();
                handles.push(std::thread::spawn(move || unsafe {
                    let _guard = f.lock(MID).expect("lock");
                    let data = vec![0xAB; LEN];
                    assert!(f.pwrite(data.as_ptr(), 0, LEN, MID).check_ok());
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
        }
    }
}
