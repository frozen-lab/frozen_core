use frozen_core::ff::{FFCfg, FF};

const MODULE_ID: u8 = 0;

fn main() {
    let dir = std::path::PathBuf::from("/tmp/frozen-core/examples");
    let path = dir.join("ff_example.bin");
    std::fs::create_dir_all(&dir).expect("create example dir");

    let mut buf = [0u8; 8];
    let data = 42u64.to_le_bytes();

    let ff = FF::new(FFCfg::new(path, MODULE_ID), 16).expect("create");

    ff.write(data.as_ptr(), 0, data.len()).expect("write");
    ff.sync().expect("sync");

    ff.read(buf.as_mut_ptr(), 0, buf.len()).expect("read");
    assert_eq!(u64::from_le_bytes(buf), 42);
}
