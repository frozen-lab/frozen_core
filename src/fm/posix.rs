use super::{new_error, FMErr, FRes};
use crate::hints;
use core::{ptr, sync::atomic};
use libc::{
    c_void, mmap, msync, munmap, off_t, size_t, EACCES, EBADF, EBUSY, EINTR, EINVAL, EIO, ENOMEM, MAP_FAILED,
    MAP_SHARED, MS_SYNC, PROT_READ, PROT_WRITE,
};

const MAX_RETRIES: usize = 6; // max allowed retries for `EINTR` errors

/// Raw implementation of Posix (linux & macos) `memmap` for [`FrozenMMap`]
pub(super) struct POSIXMMap {
    ptr: *mut c_void,
    unmapped: atomic::AtomicBool,
}

unsafe impl Send for POSIXMMap {}
unsafe impl Sync for POSIXMMap {}

impl POSIXMMap {
    /// Create a new [`POSIXMMap`] instance for given `fd` w/ read & write permissions
    pub(super) unsafe fn new(fd: i32, length: size_t, mid: u8) -> FRes<Self> {
        let ptr = mmap(
            ptr::null_mut(),
            length,
            PROT_WRITE | PROT_READ,
            MAP_SHARED,
            fd,
            0 as off_t,
        );

        if ptr == MAP_FAILED {
            let error = last_os_error();
            let err_raw = error.raw_os_error();

            // invalid fd, invalid fd type, invalid length, etc.
            if err_raw == Some(EINVAL) || err_raw == Some(EBADF) || err_raw == Some(EACCES) {
                return new_error(mid, FMErr::Hcf, error);
            }

            // no more memory space available
            if err_raw == Some(ENOMEM) {
                return new_error(mid, FMErr::Nmm, error);
            }

            // unknown (unsupported, etc.)
            return new_error(mid, FMErr::Unk, error);
        }

        return Ok(Self {
            ptr,
            unmapped: atomic::AtomicBool::new(false),
        });
    }

    /// Unmap (free/drop) the mmaped instance of [`POSIXMMap`]
    pub(super) unsafe fn unmap(&self, length: usize, mid: u8) -> FRes<()> {
        // NOTE: To avoid another thread/process from executing munmap, we mark unmapped before even
        // trying to unmap, this kind of wroks like mutex, as we reassign to false on failure
        if self
            .unmapped
            .compare_exchange(false, true, atomic::Ordering::AcqRel, atomic::Ordering::Acquire)
            .is_err()
        {
            return Ok(());
        }

        if munmap(self.ptr, length) != 0 {
            let error = last_os_error();
            let err_raw = error.raw_os_error();

            // invalid or unaligned pointer
            if err_raw == Some(EINVAL) || err_raw == Some(ENOMEM) {
                return new_error(mid, FMErr::Hcf, error);
            }

            // unknown
            return new_error(mid, FMErr::Unk, error);
        }

        Ok(())
    }

    /// Syncs in-mem data on the storage device
    pub(super) unsafe fn sync(&self, length: usize, mid: u8) -> FRes<()> {
        // only for EIO and EBUSY errors
        let mut retries = 0;

        loop {
            let res = msync(self.ptr, length, MS_SYNC);
            if hints::unlikely(res != 0) {
                let error = last_os_error();
                let error_raw = error.raw_os_error();

                // IO interrupt (must retry)
                if error_raw == Some(EINTR) {
                    continue;
                }

                // invalid fd or lack of support for sync
                if error_raw == Some(ENOMEM) || error_raw == Some(EINVAL) {
                    return new_error(mid, FMErr::Hcf, error);
                }

                // locked file or fatel error, i.e. unable to sync
                //
                // NOTE: this is handled seperately, as if this error occurs, we must
                // notify users that the sync failed, hence the data is not persisted
                if error_raw == Some(EIO) || error_raw == Some(EBUSY) {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // retries exhausted and durability is broken in the current window
                    return new_error(mid, FMErr::Syn, error);
                }

                return new_error(mid, FMErr::Unk, error);
            }

            return Ok(());
        }
    }

    /// Syncs in-mem data on the storage device
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
    pub(super) unsafe fn full_sync(&self, length: usize, fd: i32, mid: u8) -> FRes<()> {
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
                        return new_error(mid, FMErr::Syn, error);
                    }

                    // lack of support for `F_FULLSYNC` (must fallback to fsync)
                    Some(libc::EINVAL) | Some(libc::ENOTSUP) | Some(libc::EOPNOTSUPP) => break,

                    // invalid fd
                    Some(EBADF) => return new_error(mid, FMErr::Hcf, error),

                    // read-only file (can also be caused by TOCTOU)
                    Some(libc::EROFS) => return new_error(mid, FMErr::Prm, error),

                    // fatel error, i.e. no sync for writes in recent window/batch
                    Some(EIO) => return new_error(mid, FMErr::Syn, error),

                    _ => return new_error(mid, FMErr::Unk, error),
                }
            }

            return Ok(());
        }

        // NOTE: As a fallback to `F_FULLFSYNC` we use `fsync`
        //
        // HACK: On mac, fsync does NOT mean "data is on disk". The drive is still free to cache,
        // reorder, and generally do whatever it wants with your supposedly "synced" data. But for us,
        // this is the least-bad fallback when `F_FULLFSYNC` isn’t supported or working
        self.sync(length, mid)
    }

    /// Get an immutable typed pointer to `T` at given `offset`
    #[inline]
    pub(super) unsafe fn get<T>(&self, offset: usize) -> *const T {
        self.ptr.add(offset) as *const T
    }

    /// Get a mutable (read/write) typed pointer to `T` at given `offset`
    #[inline]
    pub(super) unsafe fn get_mut<T>(&self, offset: usize) -> *mut T {
        self.ptr.add(offset) as *mut T
    }
}

// TODO: In future, make it `#![no_std]`
#[inline]
fn last_os_error() -> std::io::Error {
    std::io::Error::last_os_error()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fe::{FECheckOk, MID};
    use crate::ff::{FFCfg, FrozenFile};
    use std::path::PathBuf;
    use tempfile::{tempdir, TempDir};

    const LEN: usize = 0x80;

    fn get_ff_cfg(path: PathBuf) -> FFCfg {
        FFCfg::new(path, MID)
    }

    fn new_tmp() -> (TempDir, PathBuf, FrozenFile, POSIXMMap) {
        let dir = tempdir().expect("temp dir");
        let tmp = dir.path().join("tmp_file");

        unsafe {
            let file = FrozenFile::new(get_ff_cfg(tmp.clone()), LEN as u64).expect("new FrozenFile");
            let mmap = POSIXMMap::new(file.fd(), LEN, MID).expect("new POSIXMMap");

            (dir, tmp, file, mmap)
        }
    }

    unsafe fn perf_sync(mmap: &POSIXMMap, _fd: i32, length: usize, mid: u8) -> FRes<()> {
        #[cfg(target_os = "linux")]
        return mmap.sync(length, mid);

        #[cfg(target_os = "macos")]
        return mmap.full_sync(length, _fd, mid);
    }

    mod mmap_new_and_unmap {
        use super::*;

        #[test]
        fn map_unmap_cycle() {
            let (_dir, _tmp, _file, map) = new_tmp();

            assert!(!map.ptr.is_null());
            assert!(unsafe { map.unmap(LEN, MID) }.check_ok());
        }

        #[test]
        fn map_fails_on_invalid_fd() {
            unsafe { assert!(POSIXMMap::new(-1, LEN, MID).is_err()) };
        }

        #[test]
        fn unmap_after_unmap_does_not_fails() {
            let (_dir, _tmp, _file, map) = new_tmp();

            unsafe {
                assert!(map.unmap(LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }
    }

    mod mmap_sync {
        use super::*;

        #[test]
        fn msync_works() {
            let (_dir, _tmp, file, map) = new_tmp();

            unsafe {
                assert!(perf_sync(&map, file.fd(), LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn sync_persists_without_rewrite() {
            let (_dir, tmp, file, map) = new_tmp();

            unsafe {
                *map.get_mut::<u64>(16) = 0xABCD;

                assert!(perf_sync(&map, file.fd(), LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());

                drop(file);
            }

            unsafe {
                let file = FrozenFile::open(get_ff_cfg(tmp)).expect("open existing");
                let map = POSIXMMap::new(file.fd(), LEN, MID).expect("new mmap");

                assert_eq!(*map.get::<u64>(16), 0xABCD);
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn repeated_sync_is_stable() {
            let (_dir, _tmp, file, map) = new_tmp();

            unsafe {
                *map.get_mut::<u64>(0) = 7;

                for _ in 0..0x20 {
                    assert!(perf_sync(&map, file.fd(), LEN, MID).check_ok());
                }

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        /// this is linux only test, as on macos, the `fnctl` does not care about mapping, we use
        /// the files `fd` to perform the sync
        #[test]
        #[cfg(target_os = "linux")]
        fn sync_after_unmap_should_fail() {
            let (_dir, _tmp, file, map) = new_tmp();

            unsafe {
                assert!(map.unmap(LEN, MID).check_ok());
                assert!(perf_sync(&map, file.fd(), LEN, MID).is_err());
            }
        }
    }

    mod mmap_write_read {
        use super::*;

        #[test]
        fn write_read_cycle() {
            let (_dir, _tmp, file, map) = new_tmp();

            unsafe {
                // write + sync
                let ptr = map.get_mut::<u64>(0);
                *ptr = 0xDEAD_C0DE_DEAD_C0DE;
                assert!(perf_sync(&map, file.fd(), LEN, MID).check_ok());

                // read + validate
                let val = *map.get::<u64>(0);
                assert_eq!(val, 0xDEAD_C0DE_DEAD_C0DE);

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn write_read_across_sessions() {
            let (_dir, tmp, file, map) = new_tmp();

            // write + sync + unmap + close
            unsafe {
                let ptr = map.get_mut::<u64>(0);
                *ptr = 0xDEAD_C0DE_DEAD_C0DE;
                assert!(perf_sync(&map, file.fd(), LEN, MID).check_ok());

                assert!(map.unmap(LEN, MID).check_ok());
                drop(file);
            }

            // open + map + read + validate
            unsafe {
                let file = FrozenFile::open(get_ff_cfg(tmp)).expect("open existing");
                let map = POSIXMMap::new(file.fd(), LEN, MID).expect("new mmap");

                // read + validate
                let val = *map.get::<u64>(0);
                assert_eq!(val, 0xDEAD_C0DE_DEAD_C0DE);

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn mmap_write_is_in_synced_with_file_read() {
            let (_dir, tmp, file, map) = new_tmp();

            unsafe {
                // write + sync
                let ptr = map.get_mut::<u64>(0);
                *ptr = 0xDEAD_C0DE_DEAD_C0DE;
                assert!(perf_sync(&map, file.fd(), LEN, MID).check_ok());

                let buf = std::fs::read(&tmp).expect("read from file");
                let bytes: [u8; 8] = buf[0..8].try_into().expect("Slice with incorrect length");
                assert_eq!(u64::from_le_bytes(bytes), 0xDEAD_C0DE_DEAD_C0DE);

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn multiple_writes_single_sync() {
            let (_dir, _tmp, file, map) = new_tmp();

            unsafe {
                for i in 0..16u64 {
                    *map.get_mut::<u64>((i as usize) * 8) = i;
                }

                assert!(perf_sync(&map, file.fd(), LEN, MID).check_ok());

                for i in 0..16u64 {
                    assert_eq!(*map.get::<u64>((i as usize) * 8), i);
                }

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }
    }

    mod mmap_concurrency {
        use super::*;
        use std::{sync, thread};

        #[test]
        fn munmap_is_thread_safe() {
            let (_dir, _tmp, _file, map) = new_tmp();

            let mut handles = Vec::new();
            let map = sync::Arc::new(map);

            for _ in 0..8 {
                let m = map.clone();
                handles.push(thread::spawn(move || unsafe {
                    assert!(m.unmap(LEN, MID).check_ok());
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

        #[test]
        fn msync_is_thread_safe() {
            let (_dir, _tmp, file, map) = new_tmp();

            let mut handles = Vec::new();
            let fd = file.fd();
            let map = sync::Arc::new(map);

            unsafe {
                *map.get_mut::<u64>(0) = 42;
            }

            for _ in 0..8 {
                let m = map.clone();
                handles.push(thread::spawn(move || unsafe {
                    assert!(perf_sync(&m, fd, LEN, MID).check_ok());
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

            unsafe {
                assert_eq!(*map.get::<u64>(0), 42);
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn concurrent_writes_then_sync() {
            let (_dir, _tmp, file, map) = new_tmp();

            let mut handles = Vec::new();
            let map = sync::Arc::new(map);

            for i in 0..8u64 {
                let m = map.clone();
                handles.push(thread::spawn(move || unsafe {
                    let ptr = m.get_mut::<u64>(0);
                    *ptr = i;
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

            unsafe {
                assert!(perf_sync(&map, file.fd(), LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn concurrent_writes_distinct_offsets() {
            let (_dir, _tmp, file, map) = new_tmp();

            let mut handles = Vec::new();
            let map = std::sync::Arc::new(map);

            for i in 0..8u64 {
                let m = map.clone();
                handles.push(std::thread::spawn(move || unsafe {
                    *m.get_mut::<u64>((i as usize) * 8) = i;
                }));
            }

            for h in handles {
                h.join().expect("thread join failed");
            }

            unsafe {
                assert!(perf_sync(&map, file.fd(), LEN, MID).check_ok());

                for i in 0..8u64 {
                    assert_eq!(*map.get::<u64>((i as usize) * 8), i);
                }

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }
    }
}
