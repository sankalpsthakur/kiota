//! The cross-declaration caches (`KIOTA_XCACHE`, `KIOTA_XMEMO`) must not
//! change a verdict. Every export here is checked by the built binary four
//! times (neither flag, each one, both) and the four exit codes must be the
//! same one, and the expected one where the file name or its directory
//! says what that is.
//!
//! `KIOTA_ARENA_SUITE=<dir>` adds the arena's small suite (`<dir>/good/**`
//! accept, `<dir>/bad/**` reject); without it that test says so and passes.

use std::path::{Path, PathBuf};
use std::process::Command;

const ACCEPT: i32 = 0;
const REJECT: i32 = 1;

const MODES: [(&str, &[&str]); 4] = [
    ("neither", &[]),
    ("KIOTA_XCACHE", &["KIOTA_XCACHE"]),
    ("KIOTA_XMEMO", &["KIOTA_XMEMO"]),
    ("both", &["KIOTA_XCACHE", "KIOTA_XMEMO"]),
];

struct Run {
    code: i32,
    stderr: String,
}

fn check(path: &Path, flags: &[&str], stats: bool) -> Run {
    let mut command = Command::new(env!("CARGO_BIN_EXE_kiota"));
    command.arg(path);
    // Whatever the test process inherited, each run sets exactly its flags.
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KIOTA_") {
            command.env_remove(key);
        }
    }
    for flag in flags {
        command.env(flag, "1");
    }
    if stats {
        command.env("KIOTA_STATS", "1");
    }
    let out = command.output().expect("run the checker");
    Run {
        code: out.status.code().unwrap_or(-1),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

/// One counter off the `STATS3` line of a `KIOTA_STATS=1` run.
fn stat(run: &Run, name: &str) -> u64 {
    let line = run
        .stderr
        .lines()
        .find(|l| l.starts_with("STATS3 "))
        .unwrap_or_else(|| panic!("no STATS3 line in:\n{}", run.stderr));
    line.split_whitespace()
        .find_map(|field| field.strip_prefix(name)?.strip_prefix('='))
        .unwrap_or_else(|| panic!("no `{name}` in `{line}`"))
        .parse()
        .unwrap()
}

/// The four exit codes of `path`, which must agree, and equal `expected`
/// when there is one. Returns a description of the disagreement, if any.
fn disagreement(path: &Path, expected: Option<i32>) -> Option<String> {
    let codes: Vec<i32> = MODES.iter().map(|(_, flags)| check(path, flags, false).code).collect();
    let same = codes.iter().all(|c| *c == codes[0]);
    let as_expected = expected.map_or(true, |e| codes[0] == e);
    if same && as_expected {
        return None;
    }
    let shown: Vec<String> = MODES.iter().zip(&codes).map(|((m, _), c)| format!("{m}={c}")).collect();
    Some(format!(
        "{}: {}{}",
        path.display(),
        shown.join(" "),
        expected.map_or(String::new(), |e| format!(" (expected {e})"))
    ))
}

fn ndjson_under(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            ndjson_under(&p, out);
        } else if p.extension().is_some_and(|x| x == "ndjson") {
            out.push(p);
        }
    }
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

#[test]
fn every_fixture_has_one_verdict_under_all_cache_flags() {
    let mut files = Vec::new();
    ndjson_under(&fixtures_dir(), &mut files);
    assert!(files.len() > 50, "fixtures not found");
    let mut bad = Vec::new();
    for path in &files {
        let name = path.file_name().unwrap().to_string_lossy();
        let expected = if name.ends_with(".accept.ndjson") {
            Some(ACCEPT)
        } else if name.ends_with(".reject.ndjson") {
            Some(REJECT)
        } else {
            None
        };
        bad.extend(disagreement(path, expected));
    }
    assert!(bad.is_empty(), "verdicts differ:\n{}", bad.join("\n"));
}

#[test]
fn the_arena_small_suite_has_one_verdict_under_all_cache_flags() {
    let Some(root) = std::env::var_os("KIOTA_ARENA_SUITE").map(PathBuf::from) else {
        eprintln!("SKIPPED: set KIOTA_ARENA_SUITE to the arena suite directory (good/, bad/) to run this");
        return;
    };
    let mut bad = Vec::new();
    let mut seen = 0;
    for (sub, expected) in [("good", ACCEPT), ("bad", REJECT)] {
        let mut files = Vec::new();
        ndjson_under(&root.join(sub), &mut files);
        for path in &files {
            let name = path.file_name().unwrap().to_string_lossy();
            // Too heavy for a developer machine; they run in the arena.
            if name.contains("magma-") || name.contains("gf3") {
                continue;
            }
            seen += 1;
            bad.extend(disagreement(path, Some(expected)));
        }
    }
    assert!(seen > 100, "suite not found under {}", root.display());
    assert!(bad.is_empty(), "verdicts differ:\n{}", bad.join("\n"));
}
