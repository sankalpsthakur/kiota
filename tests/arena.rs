//! Optional full-arena integration. Skipped unless `LEAN_ARENA_TESTS` points
//! at an unpacked `lean-arena-tests` tree (`good/` + `bad/`).

use kiota::parser::Parser;
use kiota::tc::TcError;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

fn arena_root() -> Option<PathBuf> {
    std::env::var_os("LEAN_ARENA_TESTS").map(PathBuf::from)
}

fn check_file(path: &Path) -> Result<(), TcError> {
    let bytes = fs::read(path).expect("read export");
    let mut p = Parser::new();
    p.run(Cursor::new(bytes))
}

fn walk_ndjson(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            walk_ndjson(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("ndjson") {
            out.push(path);
        }
    }
}

#[test]
fn tutorial_good_accepts_when_arena_present() {
    let Some(root) = arena_root() else {
        return;
    };
    let mut files = Vec::new();
    walk_ndjson(&root.join("good/tutorial"), &mut files);
    files.sort();
    assert!(!files.is_empty(), "no tutorial goods under {}", root.display());
    let mut fails = Vec::new();
    for f in &files {
        if let Err(e) = check_file(f) {
            fails.push(format!("{}: {e:?}", f.file_name().unwrap().to_string_lossy()));
        }
    }
    assert!(fails.is_empty(), "tutorial goods failed:\n{}", fails.join("\n"));
}

#[test]
fn tutorial_bad_rejects_when_arena_present() {
    let Some(root) = arena_root() else {
        return;
    };
    let mut files = Vec::new();
    walk_ndjson(&root.join("bad/tutorial"), &mut files);
    files.sort();
    assert!(!files.is_empty(), "no tutorial bads under {}", root.display());
    let mut fails = Vec::new();
    for f in &files {
        match check_file(f) {
            Err(TcError::Reject(_)) => {}
            other => fails.push(format!(
                "{}: {other:?}",
                f.file_name().unwrap().to_string_lossy()
            )),
        }
    }
    assert!(fails.is_empty(), "tutorial bads not rejected:\n{}", fails.join("\n"));
}
