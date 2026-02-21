fn main() {
    let module_id = 0u8;
    let init_len = 0x10;

    let dir = std::path::PathBuf::from("./target/examples");
    let path = dir.join("ff_example.bin");
    std::fs::create_dir_all(&dir).expect("create example dir");

    let ff = frozen_core::ffile::FrozenFile::new(path, init_len, module_id).expect("new FFile");
    assert_eq!(ff.length(), init_len);

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    assert!(ff.fd() >= 0);
}
