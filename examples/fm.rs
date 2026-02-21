use frozen_core::{ffile, fmmap};

fn main() {
    let module_id = 0u8;
    let len = 0x10;

    let dir = std::path::PathBuf::from("./target/examples");
    let path = dir.join("ff_example.bin");
    std::fs::create_dir_all(&dir).expect("create example dir");

    let ff = ffile::FrozenFile::new(path, len, module_id).expect("new FFile");
    assert!(ff.fd() >= 0);

    let fm = fmmap::FrozenMMap::new(ff, fmmap::FMCfg::new(module_id)).expect("mmap");

    fm.with_write::<u64, _>(0, |v| *v = 0xDEADC0DE).unwrap();
    fm.sync().expect("sync");

    let value = fm.with_read::<u64, u64>(0, |v| *v).unwrap();
    assert_eq!(value, 0xDEADC0DE);
}
