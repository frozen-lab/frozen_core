use frozen_core::ffile::FrozenFile;
use std::os::unix::ffi::OsStrExt;

const MODULE_ID: u8 = 0;

fn main() {
    let dir = std::path::PathBuf::from("/tmp/frozen-core/examples");
    let path = dir.join("ff_example.bin");
    std::fs::create_dir_all(&dir).expect("create example dir");

    let ff = FrozenFile::new(path.as_os_str().as_bytes().to_vec(), 16, MODULE_ID).expect("create");
    assert!(ff.fd() >= 0);
}
