use std::process::Command;

#[test]
fn test_rdis_help_command() {
    let rdis_bin = env!("CARGO_BIN_EXE_rdis");
    let output = Command::new(rdis_bin)
        .arg(rdis_bin)
        .arg("help")
        .output()
        .expect("failed to execute rdis");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("commands"));
    assert!(stdout.contains("walk"));
    assert!(stdout.contains("dis"));
}

#[test]
fn test_rdis_info_command() {
    let rdis_bin = env!("CARGO_BIN_EXE_rdis");
    let output = Command::new(rdis_bin)
        .arg(rdis_bin)
        .arg("info")
        .output()
        .expect("failed to execute rdis");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("image_base"));
    assert!(stdout.contains("functions_pdata"));
}

#[test]
fn test_rdis_sec_command() {
    let rdis_bin = env!("CARGO_BIN_EXE_rdis");
    let output = Command::new(rdis_bin)
        .arg(rdis_bin)
        .arg("sec")
        .output()
        .expect("failed to execute rdis");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains(".text"));
    assert!(stdout.contains(".pdata"));
}

#[test]
fn test_rdis_mksig_command_help() {
    let rdis_bin = env!("CARGO_BIN_EXE_rdis");
    let output = Command::new(rdis_bin)
        .arg(rdis_bin)
        .arg("mksig")
        .output()
        .expect("failed to execute rdis");

    // Missing address argument produces error json or failure
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stdout.contains("missing address") || stderr.contains("missing address") || stdout.contains("error"));
}
