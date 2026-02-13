use frozen_core::{
    fe::FECheckOk,
    ff::{FFCfg, FF},
};

const MODULE_ID: u8 = 0;

fn main() {
    let dir = std::path::PathBuf::from("/tmp/frozen-core/examples");
    std::fs::create_dir_all(&dir).expect("create missing dir");

    let path = dir.join("ff_example.bin");
    if path.exists() {
        std::fs::remove_file(&path).expect("del existing file");
    }

    let ff = FF::new(FFCfg::new(path, MODULE_ID), 16).expect("create");

    let mut buf = [0u8; 8];
    let data = 42u64.to_le_bytes();

    let mut write_iov = libc::iovec {
        iov_base: data.as_ptr() as *mut _,
        iov_len: data.len(),
    };
    let mut read_iov = libc::iovec {
        iov_base: buf.as_mut_ptr() as *mut _,
        iov_len: buf.len(),
    };

    // write
    assert!(ff.writev(std::slice::from_mut(&mut write_iov), 0).check_ok());
    assert!(ff.sync().check_ok());

    // read
    assert!(ff.readv(std::slice::from_mut(&mut read_iov), 0).check_ok());
    assert_eq!(u64::from_le_bytes(buf), 42);
}
