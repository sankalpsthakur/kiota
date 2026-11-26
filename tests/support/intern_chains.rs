//! The hash-cons table twins, written at test time instead of being checked
//! in (each is 1.9 MB of one-line records).
//!
//! Axioms `T U : Type`, `s : T → T`, `w : U`, and 230 definitions
//! `d_i : T := s (s (... (s z_i)))` of 200 applications each over its own
//! axiom `z_i : T`: 46,000 distinct application nodes are filed, so the
//! default table doubles on the way (at 40,961 nodes). The reject twin
//! differs in one line: the innermost argument of the last chain is `w`
//! where the accept twin has `z230`.

use std::path::PathBuf;
use std::sync::OnceLock;

pub const ACCEPT: &str = "intern-table-chains.accept.ndjson";
pub const REJECT: &str = "intern-table-chains.reject.ndjson";

const DEFS: usize = 230;
const CHAIN: usize = 200;

/// The export text; `wrong_leaf` gives the reject twin.
pub fn text(wrong_leaf: bool) -> String {
    let mut out = String::with_capacity(1 << 21);
    let mut line = |s: String| {
        out.push_str(&s);
        out.push('\n');
    };
    line(format!(
        r#"{{"meta":{{"exporter":{{"name":"lean4export","version":"3.1.0"}},"format":{{"version":"3.1.0"}},"lean":{{"githash":"{}","version":"4.34.1"}}}}}}"#,
        "0".repeat(40)
    ));
    for fixed in [
        r#"{"il":1,"succ":0}"#,
        r#"{"sort":1,"ie":0}"#,
        r#"{"in":1,"str":{"pre":0,"str":"T"}}"#,
        r#"{"in":2,"str":{"pre":0,"str":"U"}}"#,
        r#"{"in":3,"str":{"pre":0,"str":"s"}}"#,
        r#"{"in":4,"str":{"pre":0,"str":"w"}}"#,
        r#"{"in":5,"str":{"pre":0,"str":"x"}}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":2,"type":0}}"#,
        r#"{"const":{"name":1,"us":[]},"ie":1}"#,
        r#"{"const":{"name":2,"us":[]},"ie":2}"#,
        r#"{"forallE":{"binderInfo":"default","body":1,"name":5,"type":1},"ie":3}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":3,"type":3}}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":4,"type":2}}"#,
        r#"{"const":{"name":3,"us":[]},"ie":4}"#,
        r#"{"const":{"name":4,"us":[]},"ie":5}"#,
    ] {
        line(fixed.to_string());
    }
    // Expression 4 is `s`, 5 is `w`, 1 is `T`.
    let mut next_expr = 6usize;
    for i in 1..=DEFS {
        let z_name = 2 * i + 4;
        let d_name = 2 * i + 5;
        line(format!(r#"{{"in":{z_name},"str":{{"pre":0,"str":"z{i}"}}}}"#));
        line(format!(
            r#"{{"axiom":{{"isUnsafe":false,"levelParams":[],"name":{z_name},"type":1}}}}"#
        ));
        let z = next_expr;
        line(format!(r#"{{"const":{{"name":{z_name},"us":[]}},"ie":{z}}}"#));
        next_expr += 1;
        let mut arg = if wrong_leaf && i == DEFS { 5 } else { z };
        for _ in 0..CHAIN {
            line(format!(r#"{{"app":{{"arg":{arg},"fn":4}},"ie":{next_expr}}}"#));
            arg = next_expr;
            next_expr += 1;
        }
        line(format!(r#"{{"in":{d_name},"str":{{"pre":0,"str":"d{i}"}}}}"#));
        line(format!(
            r#"{{"def":{{"all":[{d_name}],"hints":"opaque","levelParams":[],"name":{d_name},"safety":"safe","type":1,"value":{arg}}}}}"#
        ));
    }
    out
}

/// The path of a twin: `name` is `ACCEPT` or `REJECT`. The text is fixed,
/// so every test process writes the same two files under
/// `CARGO_TARGET_TMPDIR`: each is written to a name of its own process and
/// then renamed into place, so a test running side by side never reads a
/// partial file, and runs no longer leave one pair of 1.9 MB files behind
/// each. The per-process files earlier versions left there are removed.
pub fn path(name: &str) -> PathBuf {
    static PATHS: OnceLock<(PathBuf, PathBuf)> = OnceLock::new();
    let (accept, reject) = PATHS.get_or_init(|| {
        let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
        std::fs::create_dir_all(&dir).expect("create the test tmp dir");
        sweep_per_process_twins(&dir);
        let pid = std::process::id();
        let write = |file: &str, wrong_leaf: bool| {
            let dest = dir.join(file);
            let tmp = dir.join(format!("{file}.{pid}.partial"));
            std::fs::write(&tmp, text(wrong_leaf)).expect("write a chain twin");
            std::fs::rename(&tmp, &dest).expect("move a chain twin into place");
            dest
        };
        (write(ACCEPT, false), write(REJECT, true))
    });
    match name {
        ACCEPT => accept.clone(),
        REJECT => reject.clone(),
        other => panic!("not a chain twin: {other}"),
    }
}

/// `intern-table-chains.{accept,reject}-<pid>.ndjson`, the names each test
/// process used to write. Nothing writes them any more, so removing them
/// cannot pull a file from under a running test.
fn sweep_per_process_twins(dir: &std::path::Path) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        let legacy = ["intern-table-chains.accept-", "intern-table-chains.reject-"]
            .iter()
            .filter_map(|stem| name.strip_prefix(stem))
            .filter_map(|rest| rest.strip_suffix(".ndjson"))
            .any(|pid| !pid.is_empty() && pid.bytes().all(|b| b.is_ascii_digit()));
        if legacy {
            let _ = std::fs::remove_file(entry.path());
        }
    }
}
