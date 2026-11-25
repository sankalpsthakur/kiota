//! The hash-cons table doubles when it is 5/8 full while it is small and
//! when it is 7/8 full from 2^25 slots (half a gigabyte) on, and a reset
//! replaces a slot array of more than 2^24 slots by one of that size. No
//! fixture builds a table that large, so by default these rules are only
//! met by the heaviest arena cases and the large corpora.
//!
//! `KIOTA_INTERN_TABLE=3,3,6` starts the table at 8 slots, makes it dense
//! from there, and lets a reset keep 64 slots. The fixtures then run
//! through the dense rule at every size up to the one they need, and, with
//! the reset threshold at 300 nodes, through the replacement of an outsized
//! array many times. Verdict, message and every counter must be the ones the
//! default table gives.

use std::process::{Command, Output};

#[path = "support/intern_chains.rs"]
mod intern_chains;

const SMALL_DENSE: &str = "3,3,6";

/// (fixture, exit code): the fixtures of `tests/intern_reset.rs` and the
/// twins written for the table (generated at test time, see
/// `tests/support/intern_chains.rs`).
const FIXTURES: &[(&str, i32)] = &[
    ("intern-table-chains.accept.ndjson", 0),
    ("intern-table-chains.reject.ndjson", 1),
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

fn run(fixture: &str, vars: &[(&str, &str)]) -> Output {
    let path = if fixture == intern_chains::ACCEPT || fixture == intern_chains::REJECT {
        intern_chains::path(fixture).display().to_string()
    } else {
        format!("{}/tests/fixtures/{fixture}", env!("CARGO_MANIFEST_DIR"))
    };
    let mut command = Command::new(env!("CARGO_BIN_EXE_kiota"));
    command.arg(&path);
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KIOTA_") {
            command.env_remove(key);
        }
    }
    for (key, value) in vars {
        command.env(key, value);
    }
    command.output().expect("run the checker")
}

/// What a run reports besides progress: the verdict line, every counter
/// line of `KIOTA_STATS`, and the table resets.
fn report(output: &Output) -> Vec<String> {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .filter(|line| {
            ["STATS", "REJECT", "DECLINE", "ERROR", "INTERN_RESET "]
                .iter()
                .any(|prefix| line.starts_with(prefix))
        })
        .map(str::to_string)
        .collect()
}

/// `INTERN_TABLE <what> nodes=<n> slots=2^<a>→2^<b>` lines as `(n, a, b)`.
fn table_lines(output: &Output, what: &str) -> Vec<(usize, u32, u32)> {
    let prefix = format!("INTERN_TABLE {what} nodes=");
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .filter_map(|line| {
            let rest = line.strip_prefix(&prefix)?;
            let (nodes, slots) = rest.split_once(" slots=2^")?;
            let (from, to) = slots.split_once("→2^")?;
            Some((nodes.parse().ok()?, from.parse().ok()?, to.parse().ok()?))
        })
        .collect()
}

#[test]
fn verdicts_and_counters_do_not_depend_on_the_table_policy() {
    for &(fixture, expected) in FIXTURES {
        for reset in [None, Some("300")] {
            let mut vars = vec![("KIOTA_STATS", "1")];
            if let Some(at) = reset {
                vars.push(("KIOTA_INTERN_RESET_AT", at));
                vars.push(("KIOTA_INTERN_RESET_LOG", "1"));
            }
            let default = run(fixture, &vars);
            vars.push(("KIOTA_INTERN_TABLE", SMALL_DENSE));
            let dense = run(fixture, &vars);
            for (arm, output) in [("default table", &default), ("small dense table", &dense)] {
                assert_eq!(
                    output.status.code(),
                    Some(expected),
                    "{fixture} [{arm}, reset {reset:?}]: {}",
                    String::from_utf8_lossy(&output.stderr)
                );
            }
            let (a, b) = (report(&default), report(&dense));
            assert!(
                a.iter().any(|line| line.starts_with("STATS ")),
                "{fixture}: no counters reported"
            );
            assert_eq!(a, b, "{fixture} [reset {reset:?}]: the table policy changed a report");
        }
    }
}

/// The comparison above means something only if the small policy really
/// takes the table through the dense rule. Under it every doubling of the
/// chain fixture happens one node past 7/8 of the slots; by default the one
/// doubling the fixture needs is one node past 5/8 of 2^16.
#[test]
fn the_small_dense_policy_fills_every_size_to_seven_eighths() {
    let log = ("KIOTA_INTERN_TABLE_LOG", "1");
    for fixture in ["intern-table-chains.accept.ndjson", "intern-table-chains.reject.ndjson"] {
        let default = table_lines(&run(fixture, &[log]), "grow");
        assert_eq!(default, [(40_961, 16, 17)], "{fixture}: default table");

        let dense = table_lines(&run(fixture, &[log, ("KIOTA_INTERN_TABLE", SMALL_DENSE)]), "grow");
        let expected: Vec<(usize, u32, u32)> =
            (3..16).map(|log2| ((1usize << log2) / 8 * 7 + 1, log2, log2 + 1)).collect();
        assert_eq!(dense, expected, "{fixture}: small dense table");
    }
}

/// With the reset threshold at 300 nodes the table is emptied between
/// declarations while it holds far more slots than the 64 the small policy
/// retains: the outsized array is replaced, again and again, and checking
/// carries on in the replacement.
#[test]
fn the_small_policy_replaces_an_outsized_table_at_a_reset() {
    for fixture in [
        "std-iterm-allm-pure.accept.ndjson",
        "freegroup-unit-equiv-int-multiplicative.accept.ndjson",
        "intern-table-chains.reject.ndjson",
    ] {
        let output = run(
            fixture,
            &[
                ("KIOTA_INTERN_TABLE_LOG", "1"),
                ("KIOTA_INTERN_TABLE", SMALL_DENSE),
                ("KIOTA_INTERN_RESET_AT", "300"),
            ],
        );
        let resets = table_lines(&output, "reset");
        let shrunk = resets.iter().filter(|&&(_, from, to)| from > 6 && to == 6).count();
        assert!(shrunk >= 2, "{fixture}: {shrunk} outsized resets of {}", resets.len());
        assert!(resets.iter().all(|&(nodes, _, to)| nodes > 300 && to <= 6), "{fixture}: {resets:?}");
        // And the default keeps what these fixtures build.
        let output = run(
            fixture,
            &[("KIOTA_INTERN_TABLE_LOG", "1"), ("KIOTA_INTERN_RESET_AT", "300")],
        );
        let resets = table_lines(&output, "reset");
        assert!(resets.len() >= 2, "{fixture}: default table never reset");
        assert!(resets.iter().all(|&(_, from, to)| from == to), "{fixture}: {resets:?}");
    }
}

/// The twins are one line apart, and the verdict on the reject twin names
/// the definition with the wrong leaf under either policy.
#[test]
fn the_chain_twins_differ_in_one_leaf_and_only_the_wrong_leaf_rejects() {
    let (accept, reject) = (intern_chains::text(false), intern_chains::text(true));
    let differing: Vec<(&str, &str)> =
        accept.lines().zip(reject.lines()).filter(|(a, b)| a != b).collect();
    assert_eq!(accept.lines().count(), reject.lines().count());
    assert_eq!(
        differing,
        [(
            r#"{"app":{"arg":46035,"fn":4},"ie":46036}"#,
            r#"{"app":{"arg":5,"fn":4},"ie":46036}"#
        )]
    );
    for policy in [None, Some(SMALL_DENSE)] {
        let vars: Vec<(&str, &str)> = policy.map(|p| ("KIOTA_INTERN_TABLE", p)).into_iter().collect();
        let output = run("intern-table-chains.accept.ndjson", &vars);
        assert_eq!(output.status.code(), Some(0), "accept twin [{policy:?}]");
        let output = run("intern-table-chains.reject.ndjson", &vars);
        assert_eq!(output.status.code(), Some(1), "reject twin [{policy:?}]");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.lines().any(|l| l == "REJECT: [d230] application argument type mismatch"),
            "reject twin [{policy:?}]: {stderr}"
        );
    }
}
