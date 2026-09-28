# Strict offline corpus verification

Stdlib Python 3.10+ and POSIX. This runner uses already-mounted exports and an
already-present local Git repository/toolchain. The harness never submits jobs,
downloads, installs, builds corpora, or removes files; Cargo is offline and rustup
auto-install is disabled. This is not a network sandbox for Cargo build scripts
or provided binaries. No shell execution. All artifacts use
exclusive creation inside a new `kiota-remote-*` scratch directory.

Copy `manifest.example.json` and replace **every null** with verified values.
The template intentionally cannot run: missing hashes/versions are not evidence.
`repo_sha` is exactly 40 hex characters; each input requires a unique name,
path (relative to the manifest or absolute), SHA-256 (64 hex), exact positive
bytes, exact first-line `meta` object, and positive timeout <=3600 seconds.
`header` contains Lean `version`/`githash`, exporter `name`/`version`, and format
`version`; copy it from the actual export. All listed corpora are expected valid
and must exit **0**. The only modes are `default` (omission also means default)
and `reclaim` (`KIOTA_RECLAIM=1`). All inherited `KIOTA_*` and `GIT_*` are cleared.

```sh
python3 scripts/remote/runner.py /path/to/verified-manifest.json \
  --repo /path/to/local/repository --output-parent /existing/scratch-parent \
  --total-timeout 14400 --build-timeout 1800
```

Normal execution clones locally without hardlinks into fresh scratch, checks out
the exact detached SHA, verifies actual `rev-parse HEAD` and clean status, then
runs checked `cargo build --offline --locked --release --bin kiota` with a unique
target directory. Dependencies must already be cached. A missing commit/cache or
failed/timed-out build fails the run. No remote fetch fallback exists.
`--existing-checkout /path` explicitly bypasses the clone, still verifies SHA,
and requires clean status for a build; **existing checkout runs always leave
source/build association and public candidate gate false**, since status cannot
prove ignored contents or immutability. For fake-binary local tests only, add
`--binary /path/to/executable`; dirty status is recorded, and binary/source
association is explicitly unverified (`source_build_association_verified: false`,
`public_candidate_gate: false` even when `success: true`). A provided binary's success is test
evidence, never exact-source build evidence.

Every report explicitly limits its scope to the listed manifest inputs.
`public_candidate_gate` means complete manifest acceptance from a fresh source
build, not full Arena coverage, deployment readiness, or verified rank; those
remain separate gates. The hardware probe records its event/scope explicitly,
including user-only events, and is never an Arena instruction measurement.

All inputs are verified before any checker invocation with 1 MiB streaming
hashes and a <=64 KiB first-line header. Verified regular-file descriptors stay
open; each serial checker receives `--use-stdin`. Identity/size/timestamps are
checked before/after execution and at completion; the binary is hashed before
and after. Inputs and checkouts must remain externally immutable during the
run: metadata checks are not a security boundary against a hostile writer.
Body syntax and semantic validity remain the checker's responsibility.

Per-case and total monotonic watchdogs kill POSIX process groups, including
descendants that remain in the original group (a child creating a new session
can escape). The leader remains unreaped through signalling (`waitid`/`WNOWAIT`
is required) to prevent PID/PGID reuse. Reaping is bounded to 2 seconds; cleanup
failure in any command/probe aborts the run before another case can start.
Total budget includes preflight, clone, build and checks. Optional
`--memory-mib N` samples Linux `/proc` group RSS and fails if `/proc` is unavailable;
shared pages can count multiple times. `--log-bytes N` samples each command log,
default **8 MiB** (positive limit required).
Sampling (~20 ms) permits short overshoot and is not a hard cgroup/disk quota;
external resource limits are appropriate for real large-corpus runs.

`provenance.json` records the manifest, checkout, mode, binary hash, host and
limits before checking, including bounded Rust/Cargo version probes, free disk,
CPU count/affinity, Linux meminfo and cgroup v2 limits (unavailable elsewhere).
Inherited compiler wrapper/RUSTFLAGS overrides are cleared and recorded.
Versions are probed in the checkout's toolchain context. Rustup auto-install/update
checks are disabled. `public_candidate_gate` requires a fresh clone, verified
fresh build and complete acceptance; it is not publication authority
or PMU/ranking evidence. `report.json` is written once on completion/failure,
with every completed case and its log. Outcomes preserve `accept` (0), `reject`
(1), `decline` (2), `error` (3), `crash` (negative signal exit), unexpected positive
exit, per-case/total timeout, log/memory limit, changed input, and a leader exiting
while descendants remain (`incomplete_process_group`). Harness exit 0
means complete acceptance; exit 1 means failed validation/build/check or an
incomplete run; CLI misuse exits 2. Missing/malformed inputs, declines, crashes
and timeouts can never pass the aggregate. Supervisor SIGKILL or host loss may
leave no final report; a missing report, `complete != true`, missing cases or
`success != true` is failure, never completion. Scratch/logs are retained.

Optional `--probe-perf` runs bounded `perf stat -x ';' -e instructions` on a tiny
Python process, separately from correctness, within the total time budget. Missing/denied/unsupported PMU or
no positive count at **100% running coverage** records `unavailable` and
`instructions: null`, never zero. `running_percent` records reported coverage;
`coverage_status` distinguishes full, partial, invalid and unavailable;
partial/missing/invalid coverage cannot pass the probe.
An available probe is **not** a corpus instruction count or ranking result.
Actual Linux corpus measurement requires a separate authorized run, for example
`perf stat -x ';' -e instructions -- /verified/kiota /verified/export.ndjson`,
using the same recorded hashes/mode. Acceptance and a meaningful positive
hardware count must both be checked; wall time cannot replace instructions.

Lightweight tests (fake binaries; no Rust build/network jobs):

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s scripts/remote/tests -v
```

Tests intentionally retain small temporary artifacts. Real locked builds,
large-corpus acceptance, Linux RSS behavior and hardware counters require the
main agent's review/Linux gate. No evidence from this harness deploys a checker.
