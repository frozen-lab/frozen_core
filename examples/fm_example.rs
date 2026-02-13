use frozen_core::{
    fe::FECheckOk,
    ff::{FFCfg, FF},
    fm::{FMCfg, FM},
};

const MODULE_ID: u8 = 0;

fn main() {
    let dir = std::path::PathBuf::from("/tmp/frozen-core/examples");
    std::fs::create_dir_all(&dir).expect("create missing dir");

    let path = dir.join("fm_example.bin");
    if path.exists() {
        std::fs::remove_file(&path).expect("del existing file");
    }

    let ff = FF::new(FFCfg::new(path, MODULE_ID), 8).expect("create file");
    let fm = FM::new(ff.fd(), 8, FMCfg::new(MODULE_ID)).expect("mmap");

    // write
    {
        let w = fm.writer::<u64>(0).expect("writer");
        assert!(w.write(|v| *v = 0xDEADBEEF).check_ok());
        assert!(fm.sync().check_ok());
    }

    // read
    let r = fm.reader::<u64>(0).expect("reader");
    let value = r.read(|v| *v);
    assert_eq!(value, 0xDEADBEEF);
}
