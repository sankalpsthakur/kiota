//! The profile-guided build line, as text. What it does on a runner is
//! tested by the `remote-build-flags` workflow; these tests hold the two
//! properties that broke silently before:
//!
//! - the instrumented build and the profile-use build must give cargo the
//!   same inputs apart from RUSTFLAGS. A cargo feature on one of them
//!   changes the crate hash in every mangled name, and rustc then applies
//!   the profile to no function of this crate without saying so;
//! - the block in this repository's `checker.yaml` and the one proposed for
//!   the arena must be the same block.

use std::path::Path;

fn read(relative: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The lines of the `build: |` block scalar, without their indentation.
fn build_block(yaml: &str) -> Vec<String> {
    let mut lines = yaml.lines().skip_while(|l| *l != "build: |");
    assert_eq!(lines.next(), Some("build: |"), "no `build: |` block");
    lines
        .take_while(|l| l.starts_with("  ") || l.is_empty())
        .map(|l| l.strip_prefix("  ").unwrap_or(l).to_string())
        .collect()
}

/// Shell lines joined across `\` continuations, comments dropped.
fn commands(block: &[String]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut open = false;
    for line in block {
        let line = line.trim();
        if line.starts_with('#') || line.is_empty() {
            continue;
        }
        let (text, continues) = match line.strip_suffix('\\') {
            Some(t) => (t.trim_end(), true),
            None => (line, false),
        };
        if open {
            let last = out.last_mut().unwrap();
            last.push(' ');
            last.push_str(text);
        } else {
            out.push(text.to_string());
        }
        open = continues;
    }
    out
}

#[test]
fn repository_and_arena_build_blocks_are_the_same() {
    let ours = build_block(&read("checker.yaml"));
    let proposed = build_block(&read("docs/arena-build-proposal.yaml"));
    assert!(ours.len() > 5, "checker.yaml build block is too short to be the profile-guided one");
    assert_eq!(ours, proposed);
}

#[test]
fn instrumented_and_profile_use_builds_differ_only_in_rustflags() {
    let block = build_block(&read("docs/arena-build-proposal.yaml"));
    let cargo: Vec<String> = commands(&block)
        .into_iter()
        .filter(|c| c.contains("cargo build"))
        .collect();
    let generate: Vec<&String> = cargo.iter().filter(|c| c.contains("profile-generate")).collect();
    let apply: Vec<&String> = cargo.iter().filter(|c| c.contains("profile-use")).collect();
    assert_eq!(generate.len(), 1, "one instrumented build: {cargo:?}");
    assert_eq!(apply.len(), 1, "one profile-use build: {cargo:?}");
    for command in &cargo {
        for word in ["--features", "--all-features", "--no-default-features", "--profile ", "-p ", "--package"] {
            assert!(!command.contains(word), "`{word}` changes what cargo hashes into symbol names: {command}");
        }
    }
    assert!(generate[0].contains("--cfg kiota_pgo_gen"), "the training run would write no profile: {}", generate[0]);
    assert!(!apply[0].contains("kiota_pgo_gen"), "the shipped binary must not carry the profile writer: {}", apply[0]);
    // Whatever follows `cargo build` (apart from the instrumented build's own
    // target directory) is the same in both.
    let args = |c: &str| -> Vec<String> {
        let after = c.split("cargo build").nth(1).unwrap();
        let after = after.split("||").next().unwrap();
        let mut words: Vec<String> = after.split_whitespace().map(str::to_string).collect();
        if let Some(i) = words.iter().position(|w| w == "--target-dir") {
            words.drain(i..i + 2);
        }
        words
    };
    assert_eq!(args(generate[0]), args(apply[0]));
}

#[test]
fn the_profile_switch_is_not_a_cargo_feature() {
    let manifest = read("Cargo.toml");
    assert!(
        !manifest.lines().any(|l| l.trim() == "[features]"),
        "a feature for the instrumented build changes the crate hash; use --cfg kiota_pgo_gen"
    );
    assert!(manifest.contains("cfg(kiota_pgo_gen)"), "the cfg must be declared to the unexpected_cfgs lint");
    let main = read("src/main.rs");
    assert!(main.contains("#[cfg(kiota_pgo_gen)]"));
    assert!(!main.contains("feature = \"pgo"));
}
