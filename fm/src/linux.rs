use crate::{error::new_error, FMErr};
use fe::FRes;
use libc::{
    c_void, mmap, msync, munmap, off_t, size_t, EACCES, EBADF, EBUSY, EINVAL, EIO, ENOMEM, EOVERFLOW, MAP_FAILED,
    MAP_SHARED, MS_SYNC, PROT_READ, PROT_WRITE,
};
use std::sync::atomic;

/// Linux implementation of `MemMap`
pub(crate) struct MMap {
    ptr: *mut c_void,
    unmapped: atomic::AtomicBool,
}

unsafe impl Send for MMap {}
unsafe impl Sync for MMap {}

impl MMap {
    /// Create a new [`MMap`] instance for given `fd` w/ read & write permissions
    pub(crate) unsafe fn new(fd: i32, length: size_t, mid: u8) -> FRes<Self> {
        let ptr = mmap(
            std::ptr::null_mut(),
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
            if err_raw == Some(EINVAL)
                || err_raw == Some(EBADF)
                || err_raw == Some(EACCES)
                || err_raw == Some(EOVERFLOW)
            {
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

    /// Unmap (free/drop) the mmaped instance of [`MMap`]
    pub(crate) unsafe fn unmap(&self, length: usize, mid: u8) -> FRes<()> {
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
    pub(crate) unsafe fn sync(&self, length: usize, mid: u8) -> FRes<()> {
        // only for EIO and EBUSY errors
        const MAX_RETRIES: usize = 4;
        let mut retries = 0;

        loop {
            if msync(self.ptr, length, MS_SYNC) != 0 {
                let error = last_os_error();
                let error_raw = error.raw_os_error();

                // IO interrupt (must retry)
                if error.kind() == std::io::ErrorKind::Interrupted {
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
                        std::thread::yield_now();
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

    /// Get an immutable typed pointer at given `offset`
    #[inline]
    pub(crate) unsafe fn get<T>(&self, offset: usize) -> *const T {
        // sanity check
        debug_assert!(offset % 8 == 0, "Offset must be 8 bytes aligned");
        debug_assert!(
            !self.unmapped.load(atomic::Ordering::Acquire),
            "Trying to access dropped mmap"
        );

        self.ptr.add(offset) as *const T
    }

    /// Get a mutable (read/write) typed pointer at given `offset`
    #[inline]
    pub(crate) unsafe fn get_mut<T>(&self, offset: usize) -> *mut T {
        // sanity check
        debug_assert!(offset % 0x8 == 0, "Offset must be 8 bytes aligned");
        debug_assert!(
            !self.unmapped.load(atomic::Ordering::Acquire),
            "Trying to access dropped mmap"
        );

        self.ptr.add(offset) as *mut T
    }
}

#[inline]
fn last_os_error() -> std::io::Error {
    std::io::Error::last_os_error()
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;
    use fe::FECheckOk;
    use ff::{FFCfg, FF};
    use std::path::PathBuf;
    use tempfile::{tempdir, TempDir};

    const MID: u8 = 0x00; // module id (test)
    const LEN: usize = 0x80;

    fn get_ff_cfg(path: PathBuf) -> FFCfg {
        FFCfg {
            path,
            module_id: MID,
            auto_flush: false,
            flush_duration: std::time::Duration::from_secs(1),
        }
    }

    fn new_tmp() -> (TempDir, PathBuf, FF, MMap) {
        let dir = tempdir().expect("temp dir");
        let tmp = dir.path().join("tmp_file");

        unsafe {
            let file = FF::new(get_ff_cfg(tmp.clone()), LEN as u64).expect("new FF");
            let mmap = MMap::new(file.fd(), LEN, MID).expect("new MMap");

            (dir, tmp, file, mmap)
        }
    }

    mod map_unmap {
        use super::*;

        #[test]
        fn map_unmap_cycle() {
            let (_dir, _tmp, _file, map) = new_tmp();

            assert!(!map.ptr.is_null());
            assert!(unsafe { map.unmap(LEN, MID) }.check_ok());
        }

        #[test]
        fn map_fails_on_invalid_fd() {
            unsafe { assert!(MMap::new(-1, LEN, MID).is_err()) };
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

    mod sync {
        use super::*;

        #[test]
        fn msync_works() {
            let (_dir, _tmp, _file, map) = new_tmp();

            unsafe {
                assert!(map.sync(LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }
    }

    mod write_read {
        use super::*;

        #[test]
        fn write_read_cycle() {
            let (_dir, _tmp, _file, map) = new_tmp();

            unsafe {
                // write + sync
                let ptr = map.get_mut::<u64>(0);
                *ptr = 0xDEAD_C0DE_DEAD_C0DE;
                assert!(map.sync(LEN, MID).check_ok());

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
                assert!(map.sync(LEN, MID).check_ok());

                assert!(map.unmap(LEN, MID).check_ok());
                drop(file);
            }

            // open + map + read + validate
            unsafe {
                let file = FF::open(get_ff_cfg(tmp)).expect("open existing");
                let map = MMap::new(file.fd(), LEN, MID).expect("new mmap");

                // read + validate
                let val = *map.get::<u64>(0);
                assert_eq!(val, 0xDEAD_C0DE_DEAD_C0DE);

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn mmap_write_is_in_synced_with_file_read() {
            let (_dir, _tmp, file, map) = new_tmp();

            unsafe {
                // write + sync
                let ptr = map.get_mut::<u64>(0);
                *ptr = 0xDEAD_C0DE_DEAD_C0DE;
                assert!(map.sync(LEN, MID).check_ok());

                // pread
                let mut buf = [0u8; 8];
                file.read(buf.as_mut_ptr(), 0, 8).expect("failed to read");
                assert_eq!(u64::from_le_bytes(buf), 0xDEAD_C0DE_DEAD_C0DE);

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }
    }

    mod concurrency {
        use super::*;

        #[test]
        fn munmap_is_thread_safe() {
            let (_dir, _tmp, _file, map) = new_tmp();

            let mut handles = Vec::new();
            let map = std::sync::Arc::new(map);

            for _ in 0..8 {
                let m = map.clone();
                handles.push(std::thread::spawn(move || unsafe {
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
            let (_dir, _tmp, _file, map) = new_tmp();

            let mut handles = Vec::new();
            let map = std::sync::Arc::new(map);

            unsafe {
                *map.get_mut::<u64>(0) = 42;
            }

            for _ in 0..8 {
                let m = map.clone();
                handles.push(std::thread::spawn(move || unsafe {
                    assert!(m.sync(LEN, MID).check_ok());
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
            let (_dir, _tmp, _file, map) = new_tmp();

            let mut handles = Vec::new();
            let map = std::sync::Arc::new(map);

            for i in 0..8u64 {
                let m = map.clone();
                handles.push(std::thread::spawn(move || unsafe {
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
                assert!(map.sync(LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }
    }
}
