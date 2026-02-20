use frozen_core::{error, ffile, fmmap};

fn main() -> error::FrozenRes<()> {
    let module_id = 0u8;
    let len = 0x10;

    let dir = std::path::PathBuf::from("./target/examples");
    let path = dir.join("ff_example.bin");
    std::fs::create_dir_all(&dir).expect("create example dir");

    let ff = ffile::FrozenFile::new(path, len, module_id)?;
    assert!(ff.fd() >= 0);

    let fm = fmmap::FrozenMMap::new(ff, len as usize, fmmap::FMCfg::new(module_id)).expect("mmap");

    {
        let w = fm.writer::<u64>(0).expect("writer");
        w.write(|v| *v = 0xDEADBEEF).expect("write");
    }

    fm.sync().expect("sync");

    let r = fm.reader::<u64>(0).expect("reader");
    let value = r.read(|v| *v);

    assert_eq!(value, 0xDEADBEEF);
    Ok(())
}
