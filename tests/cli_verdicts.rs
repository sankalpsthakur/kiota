use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

fn run(input: &[u8], max_decl: Option<&str>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_kiota"));
    command
        .arg("--use-stdin")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    // Keep the requested evaluator, but never inherit diagnostic cutoffs.
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KIOTA_") && key != "KIOTA_NBE" {
            command.env_remove(key);
        }
    }
    if let Some(limit) = max_decl {
        command.env("KIOTA_MAX_DECL", limit);
    }
    let mut child = command.spawn().expect("spawn checker");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input)
        .expect("write test input");
    child.wait_with_output().expect("read checker result")
}

#[test]
fn parse_error_is_not_a_proof_rejection() {
    let output = run(b"{\n", None);
    assert_eq!(output.status.code(), Some(3));
    assert!(String::from_utf8_lossy(&output.stderr).contains("ERROR: json parse:"));
}

#[test]
fn missing_input_reports_path_without_panicking() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/does-not-exist.ndjson");
    assert!(!path.exists(), "missing-input fixture unexpectedly exists");
    let output = Command::new(env!("CARGO_BIN_EXE_kiota"))
        .arg(&path)
        .output()
        .expect("run checker");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(3), "{output:?}");
    assert!(
        stderr.contains(&format!("ERROR: open input `{}`:", path.display())),
        "{output:?}"
    );
    assert!(!stderr.contains("panicked at"), "{output:?}");
    assert!(!stderr.contains("panic during checking"), "{output:?}");
}

#[test]
fn valid_proof_still_accepts() {
    let output = run(include_bytes!("fixtures/067_eqRec.accept.ndjson"), None);
    assert_eq!(output.status.code(), Some(0), "{:?}", output);
}

#[test]
fn invalid_proof_still_rejects() {
    let output = run(include_bytes!("fixtures/002_badDef.reject.ndjson"), None);
    assert_eq!(output.status.code(), Some(1), "{:?}", output);
    assert!(String::from_utf8_lossy(&output.stderr).contains("REJECT:"));
}

#[test]
fn diagnostic_cutoff_is_not_an_accept_or_reject() {
    let output = run(include_bytes!("fixtures/067_eqRec.accept.ndjson"), Some("0"));
    assert_eq!(output.status.code(), Some(2), "{:?}", output);
    assert!(String::from_utf8_lossy(&output.stderr).contains("DECLINE:"));
}
