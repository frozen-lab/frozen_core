use super::{new_err, FMMapErrRes};
use crate::error::FrozenRes;
use core::{ffi::CStr, ptr, sync::atomic};
use libc::{
    c_char, c_void, mmap, munmap, off_t, size_t, EACCES, EBADF, EINVAL, ENOMEM, MAP_FAILED, MAP_SHARED, PROT_READ,
    PROT_WRITE,
};

#[cfg(target_os = "linux")]
const MAX_RETRIES: usize = 6; // max allowed retries for `EINTR` errors

/// Raw implementation of Posix (linux & macos) `memmap` for [`FrozenMMap`]
#[derive(Debug)]
pub(super) struct POSIXMMap {
    ptr: *mut c_void,
    unmapped: atomic::AtomicBool,
}

unsafe impl Send for POSIXMMap {}
unsafe impl Sync for POSIXMMap {}

impl POSIXMMap {
    /// Create a new [`POSIXMMap`] instance for given `fd` w/ read & write permissions
    pub(super) unsafe fn new(fd: i32, length: size_t) -> FrozenRes<Self> {
        let ptr = mmap(
            ptr::null_mut(),
            length,
            PROT_WRITE | PROT_READ,
            MAP_SHARED,
            fd,
            0 as off_t,
        );

        if ptr == MAP_FAILED {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            // invalid fd, invalid fd type, invalid length, etc.
            if errno == EINVAL || errno == EBADF || errno == EACCES {
                return new_err(FMMapErrRes::Hcf, err_msg);
            }

            // no more memory space available
            if errno == ENOMEM {
                return new_err(FMMapErrRes::Nmm, err_msg);
            }

            // unknown (unsupported, etc.)
            return new_err(FMMapErrRes::Unk, err_msg);
        }

        return Ok(Self {
            ptr,
            unmapped: atomic::AtomicBool::new(false),
        });
    }

    /// Unmap (free/drop) the mmaped instance of [`POSIXMMap`]
    pub(super) unsafe fn unmap(&self, length: usize) -> FrozenRes<()> {
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
            let errno = last_errno();
            let err_msg = err_msg(errno);

            // invalid or unaligned pointer
            if errno == EINVAL || errno == ENOMEM {
                return new_err(FMMapErrRes::Hcf, err_msg);
            }

            // unknown (fallback)
            return new_err(FMMapErrRes::Unk, err_msg);
        }

        Ok(())
    }

    /// Syncs in-mem data on the storage device
    #[cfg(target_os = "linux")]
    pub(super) unsafe fn sync(&self, length: usize) -> FrozenRes<()> {
        // only for EIO and EBUSY errors
        let mut retries = 0;

        loop {
            let res = libc::msync(self.ptr, length, libc::MS_SYNC);
            if crate::hints::unlikely(res != 0) {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                // IO interrupt (must retry)
                if errno == libc::EINTR {
                    continue;
                }

                // no-more memory available
                if errno == ENOMEM {
                    return new_err(FMMapErrRes::Nmm, err_msg);
                }

                // invalid fd or lack of support for sync
                if errno == EINVAL {
                    return new_err(FMMapErrRes::Hcf, err_msg);
                }

                // locked file or fatel error, i.e. unable to sync
                //
                // NOTE: this is handled seperately, as if this error occurs, we must
                // notify users that the sync failed, hence the data is not persisted
                if errno == libc::EIO || errno == libc::EBUSY {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // retries exhausted and durability is broken in the current window
                    return new_err(FMMapErrRes::Syn, err_msg);
                }

                return new_err(FMMapErrRes::Unk, err_msg);
            }

            return Ok(());
        }
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
    use crate::{error::TEST_MID, ffile::FrozenFile};
    use std::path::PathBuf;
    use tempfile::{tempdir, TempDir};

    const LEN: usize = 0x80;

    fn new_tmp() -> (TempDir, PathBuf, FrozenFile, POSIXMMap) {
        let dir = tempdir().expect("tmp dir");
        let path = dir.path().join("tmp_file");

        let file = FrozenFile::new(path.clone(), LEN, TEST_MID).expect("new FrozenFile");
        let mmap = unsafe { POSIXMMap::new(file.fd(), LEN) }.expect("new POSIXMMap");

        (dir, path, file, mmap)
    }

    fn perf_sync(_file: &FrozenFile, _mmap: &POSIXMMap, _length: usize) {
        #[cfg(target_os = "linux")]
        unsafe { _mmap.sync(_length) }.expect("per sync");

        #[cfg(target_os = "macos")]
        _file.sync().expect("perf sync");
    }

    mod posix_map_unmap {
        use super::*;

        #[test]
        fn map_unmap_works() {
            let (_dir, _path, _file, map) = new_tmp();

            assert!(!map.ptr.is_null());
            unsafe { map.unmap(LEN) }.expect("unmap");
        }

        #[test]
        fn map_fails_on_invalid_fd() {
            unsafe { POSIXMMap::new(-1, LEN) }.expect_err("must fail");
        }

        #[test]
        fn unmap_is_idempotent() {
            let (_dir, _path, _file, map) = new_tmp();

            unsafe { map.unmap(LEN) }.expect("unmap");
            unsafe { map.unmap(LEN) }.expect("unmap");
            unsafe { map.unmap(LEN) }.expect("unmap");
        }

        #[test]
        fn map_fails_on_zero_length() {
            let (_dir, _path, file, _) = new_tmp();
            unsafe { POSIXMMap::new(file.fd(), 0) }.expect_err("zero len must fail");
        }

        #[test]
        #[cfg(target_os = "linux")]
        fn sync_after_full_unmap_fails() {
            let (_dir, _path, _file, map) = new_tmp();

            unsafe {
                map.unmap(LEN).unwrap();
                map.sync(LEN).expect_err("sync must fail after unmap");
            }
        }

        #[test]
        fn unmap_zero_length_fails() {
            let (_dir, _path, _file, map) = new_tmp();

            unsafe {
                let err = map.unmap(0).expect_err("zero length must fail");
                assert!(err.cmp(FMMapErrRes::Hcf as u16));
            }
        }

        #[test]
        fn map_fails_after_file_delete() {
            let (_dir, _path, file, _map) = new_tmp();

            file.delete().expect("delete");
            unsafe { POSIXMMap::new(file.fd(), LEN) }.expect_err("must fail");
        }
    }

    mod posix_sync {
        use super::*;

        #[test]
        fn sync_works() {
            let (_dir, _path, file, map) = new_tmp();
            perf_sync(&file, &map, LEN);
        }

        #[test]
        fn sync_persists_without_rewrite() {
            let (_dir, path, file, map) = new_tmp();

            unsafe {
                *map.get_mut::<u64>(16) = 0xABCD;

                perf_sync(&file, &map, LEN);
                map.unmap(LEN).expect("unmap");
            }

            unsafe {
                let file = FrozenFile::new(path, LEN, TEST_MID).expect("open existing");
                let map = POSIXMMap::new(file.fd(), LEN).expect("new mmap");

                assert_eq!(*map.get::<u64>(16), 0xABCD);
                map.unmap(LEN).expect("unmap");
            }
        }

        #[test]
        fn repeated_sync_is_stable() {
            let (_dir, _path, file, map) = new_tmp();

            unsafe {
                *map.get_mut::<u64>(0) = 7;

                for _ in 0..0x20 {
                    perf_sync(&file, &map, LEN);
                }

                map.unmap(LEN).expect("unmap");
            }
        }

        #[test]
        fn sync_without_write_is_ok() {
            let (_dir, _path, file, map) = new_tmp();

            unsafe {
                perf_sync(&file, &map, LEN);
                map.unmap(LEN).expect("unmap");
            }
        }
    }

    mod posix_write_read {
        use super::*;

        #[test]
        fn write_read_cycle() {
            let (_dir, _path, file, map) = new_tmp();

            unsafe {
                *map.get_mut::<u64>(0) = 0xDEAD_C0DE_DEAD_C0DE;
                perf_sync(&file, &map, LEN);

                let val = *map.get::<u64>(0);
                assert_eq!(val, 0xDEAD_C0DE_DEAD_C0DE);

                map.unmap(LEN).expect("unmap");
            }
        }

        #[test]
        fn write_read_across_sessions() {
            let (_dir, path, file, map) = new_tmp();

            unsafe {
                *map.get_mut::<u64>(0) = 0xDEAD_C0DE_DEAD_C0DE;
                perf_sync(&file, &map, LEN);
                map.unmap(LEN).expect("unmap");
            }

            drop(file);

            unsafe {
                let file = FrozenFile::new(path.clone(), LEN, TEST_MID).expect("open existing");
                let map = POSIXMMap::new(file.fd(), LEN).expect("new mmap");

                assert_eq!(*map.get::<u64>(0), 0xDEAD_C0DE_DEAD_C0DE);
                map.unmap(LEN).expect("unmap");
            }
        }

        #[test]
        fn mmap_write_is_synced_with_file_read() {
            let (_dir, path, file, map) = new_tmp();

            unsafe {
                *map.get_mut::<u64>(0) = 0xDEAD_C0DE_DEAD_C0DE;
                perf_sync(&file, &map, LEN);

                let buf = std::fs::read(&path).expect("read file");
                let bytes: [u8; 8] = buf[0..8].try_into().expect("slice len");
                assert_eq!(u64::from_le_bytes(bytes), 0xDEAD_C0DE_DEAD_C0DE);

                map.unmap(LEN).expect("unmap");
            }
        }

        #[test]
        fn multiple_writes_single_sync() {
            let (_dir, _path, file, map) = new_tmp();

            unsafe {
                for i in 0..16u64 {
                    *map.get_mut::<u64>((i as usize) * 8) = i;
                }

                perf_sync(&file, &map, LEN);

                for i in 0..16u64 {
                    assert_eq!(*map.get::<u64>((i as usize) * 8), i);
                }

                map.unmap(LEN).expect("unmap");
            }
        }

        #[test]
        fn write_at_boundary() {
            let (_dir, _path, file, map) = new_tmp();

            unsafe {
                *map.get_mut::<u8>(LEN - 1) = 0xAA;
                perf_sync(&file, &map, LEN);

                assert_eq!(*map.get::<u8>(LEN - 1), 0xAA);
                map.unmap(LEN).expect("unmap");
            }
        }
    }

    mod posix_concurrency {
        use super::*;
        use std::{sync::Arc, thread};

        #[test]
        fn munmap_is_thread_safe() {
            let (_dir, _path, _file, map) = new_tmp();
            let map = Arc::new(map);

            let handles: Vec<_> = (0..8)
                .map(|_| {
                    let m = map.clone();
                    thread::spawn(move || unsafe {
                        m.unmap(LEN).expect("unmap");
                    })
                })
                .collect();

            for h in handles {
                h.join().expect("thread join");
            }
        }

        #[test]
        fn msync_is_thread_safe() {
            let (_dir, _path, file, map) = new_tmp();

            let file = Arc::new(file);
            let map = Arc::new(map);

            unsafe {
                *map.get_mut::<u64>(0) = 42;
            }

            let handles: Vec<_> = (0..8)
                .map(|_| {
                    let m = map.clone();
                    let f = file.clone();
                    thread::spawn(move || {
                        perf_sync(&f, &m, LEN);
                    })
                })
                .collect();

            for h in handles {
                h.join().expect("thread join");
            }

            unsafe {
                assert_eq!(*map.get::<u64>(0), 42);
                map.unmap(LEN).expect("unmap");
            }
        }

        #[test]
        fn concurrent_writes_then_sync() {
            let (_dir, _path, file, map) = new_tmp();
            let map = Arc::new(map);

            let handles: Vec<_> = (0..8u64)
                .map(|i| {
                    let m = map.clone();
                    thread::spawn(move || unsafe {
                        *m.get_mut::<u64>(0) = i;
                    })
                })
                .collect();

            for h in handles {
                h.join().expect("thread join");
            }

            unsafe {
                perf_sync(&file, &map, LEN);
                map.unmap(LEN).expect("unmap");
            }
        }

        #[test]
        fn concurrent_writes_distinct_offsets() {
            let (_dir, _path, file, map) = new_tmp();
            let map = Arc::new(map);

            let handles: Vec<_> = (0..8u64)
                .map(|i| {
                    let m = map.clone();
                    thread::spawn(move || unsafe {
                        *m.get_mut::<u64>((i as usize) * 8) = i;
                    })
                })
                .collect();

            for h in handles {
                h.join().expect("thread join");
            }

            unsafe {
                perf_sync(&file, &map, LEN);

                for i in 0..8u64 {
                    assert_eq!(*map.get::<u64>((i as usize) * 8), i);
                }

                map.unmap(LEN).expect("unmap");
            }
        }
    }
}
