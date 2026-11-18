//! The hash-cons table is emptied between declarations once it holds more
//! than a threshold of nodes (4,000,000, which no fixture reaches). From
//! then on a term kept from before the reset and the same term built after
//! it are two nodes. These tests put the threshold at a few hundred nodes
//! (`KIOTA_INTERN_RESET_AT`) so that fixtures cross it many times, and ask
//! for the same verdict with the one-walk inference of `KIOTA_SPINE` as
//! without it.

use std::process::{Command, Output};

/// (fixture, exit code). Accepts and rejects, small and large; the two
/// largest fixtures are the ones the counters are compared on.
const FIXTURES: &[(&str, i32)] = &[
    ("067_eqRec.accept.ndjson", 0),
    ("002_badDef.reject.ndjson", 1),
    ("loose-bvar-value.reject.ndjson", 1),
    ("forged-quot-ind.reject.ndjson", 1),
    ("std-iterm-allm-pure.accept.ndjson", 0),
    ("cedar-value-sizeOf3-nested-map.accept.ndjson", 0),
    ("lean-compiler-lcnf-code-ctorelim.accept.ndjson", 0),
    ("freegroup-unit-equiv-int-multiplicative.accept.ndjson", 0),
    ("rat-instEncodable-and-rec-theorem-major.accept.ndjson", 0),
];

const ARMS: &[(&str, &[&str])] = &[
    ("off", &[]),
    ("KIOTA_SPINE", &["KIOTA_SPINE"]),
    ("KIOTA_SPINE + KIOTA_SPINE_VERIFY", &["KIOTA_SPINE", "KIOTA_SPINE_VERIFY"]),
];

fn run(fixture: &str, reset_at: Option<&str>, flags: &[&str]) -> Output {
    let path = format!("{}/tests/fixtures/{fixture}", env!("CARGO_MANIFEST_DIR"));
    let mut command = Command::new(env!("CARGO_BIN_EXE_kiota"));
    command.arg(&path);
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KIOTA_") {
            command.env_remove(key);
        }
    }
    if let Some(at) = reset_at {
        command.env("KIOTA_INTERN_RESET_AT", at).env("KIOTA_INTERN_RESET_LOG", "1");
    }
    for flag in flags {
        command.env(flag, "1");
    }
    command.output().expect("run the checker")
}

fn resets(output: &Output) -> usize {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .filter(|line| line.starts_with("INTERN_RESET "))
        .count()
}

#[test]
fn verdicts_agree_across_interner_resets_with_and_without_the_spine_walk() {
    let mut total_resets = 0;
    for &(fixture, expected) in FIXTURES {
        let mut codes = Vec::new();
        for &(arm, flags) in ARMS {
            let output = run(fixture, Some("300"), flags);
            let code = output.status.code();
            assert_eq!(
                code,
                Some(expected),
                "{fixture} [{arm}, reset at 300 nodes]: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            total_resets += resets(&output);
            codes.push(code);
        }
        assert!(codes.windows(2).all(|w| w[0] == w[1]), "{fixture}: arms disagree: {codes:?}");
    }
    assert!(total_resets > 0, "no arm ever reset the table");
}

/// The comparison above means something only if the table really is reset
/// between the declarations of these fixtures, in every arm.
#[test]
fn the_small_threshold_resets_the_table_in_every_arm() {
    for fixture in [
        "std-iterm-allm-pure.accept.ndjson",
        "freegroup-unit-equiv-int-multiplicative.accept.ndjson",
        "rat-instEncodable-and-rec-theorem-major.accept.ndjson",
    ] {
        for &(arm, flags) in ARMS {
            let output = run(fixture, Some("300"), flags);
            assert!(resets(&output) >= 2, "{fixture} [{arm}]: {} resets", resets(&output));
        }
    }
}

/// Unset, the threshold is the 4,000,000 it always was: no fixture resets.
#[test]
fn the_default_threshold_is_not_reached_by_a_fixture() {
    let mut command = Command::new(env!("CARGO_BIN_EXE_kiota"));
    command.arg(format!(
        "{}/tests/fixtures/rat-instEncodable-and-rec-theorem-major.accept.ndjson",
        env!("CARGO_MANIFEST_DIR")
    ));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KIOTA_") {
            command.env_remove(key);
        }
    }
    let output = command.env("KIOTA_INTERN_RESET_LOG", "1").output().expect("run the checker");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(resets(&output), 0);
    // A value that is not a number leaves the default in place.
    let output = run("067_eqRec.accept.ndjson", Some("soon"), &[]);
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(resets(&output), 0);
}
