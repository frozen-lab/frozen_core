use frozen_core::{
    ff::{FFCfg, FF},
    fm::{FMCfg, FM},
};

const MODULE_ID: u8 = 0;

fn main() {
    let dir = std::path::PathBuf::from("/tmp/frozen-core/examples");
    let path = dir.join("ff_example.bin");
    std::fs::create_dir_all(&dir).expect("create example dir");

    let ff = FF::new(FFCfg::new(path, MODULE_ID), 8).expect("file");
    let fm = FM::new(ff.fd(), 8, FMCfg::new(MODULE_ID)).expect("mmap");

    {
        let w = fm.writer::<u64>(0).expect("writer");
        w.write(|v| *v = 0xDEADBEEF).expect("write");
    }

    fm.sync().expect("sync");

    let r = fm.reader::<u64>(0).expect("reader");
    let value = r.read(|v| *v);

    assert_eq!(value, 0xDEADBEEF);
}
