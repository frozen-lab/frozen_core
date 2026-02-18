fn main() -> frozen_core::error::FrozenRes<()> {
    let module_id = 0u8;

    let dir = std::path::PathBuf::from("./target/examples");
    let path = dir.join("ff_example.bin");
    std::fs::create_dir_all(&dir).expect("create example dir");

    let ff = frozen_core::ffile::FrozenFile::new(path.as_os_str().as_encoded_bytes().to_vec(), 16, module_id)?;
    assert!(ff.fd() >= 0);

    Ok(())
}
