//! Exercise both streaming CLI entry points, including data after a valid proof.
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
}

fn stdin_verdict(bytes: &[u8]) -> i32 {
    let mut child = Command::new(env!("CARGO_BIN_EXE_kiota"))
        .arg("--use-stdin")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn checker");
    child.stdin.take().unwrap().write_all(bytes).unwrap();
    child.wait_with_output().unwrap().status.code().unwrap()
}

#[test]
fn streaming_file_and_stdin_agree() {
    for (name, expected) in [
        ("proof-irrel.accept.ndjson", 0),
        ("002_badDef.reject.ndjson", 1),
    ] {
        let path = fixture(name);
        let output = Command::new(env!("CARGO_BIN_EXE_kiota"))
            .arg(&path)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(expected), "{name}: file");
        assert_eq!(stdin_verdict(&std::fs::read(path).unwrap()), expected,
                   "{name}: stdin");
    }
}

#[test]
fn streaming_stdin_checks_the_suffix() {
    let mut bytes = std::fs::read(fixture("proof-irrel.accept.ndjson")).unwrap();
    bytes.extend_from_slice(b"\ninvalid JSON\n");
    assert_eq!(stdin_verdict(&bytes), 3,
               "a valid prefix must not conceal malformed trailing input");
}
