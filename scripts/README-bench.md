# scripts/bench.sh — A/B instruction counts without `perf`

A small measurement harness for comparing two builds (or two runs of the
*same* build) of kiota, without relying on Linux `perf`. It reports
instruction counts (via `valgrind --tool=callgrind`, when available), wall
time, and peak RSS as a single JSON object.

## Usage

```
scripts/bench.sh <sha-or-bin> <corpus> [--prefix N]
```

- `<sha-or-bin>` — a git commit/tag/branch to build `--release`, or a path
  to an already-built `kiota` binary. Builds are cached per-SHA under
  `.bench-cache/<sha>/` (a `git worktree`), so re-running against the same
  SHA does not rebuild.
- `<corpus>` — path to a single export file (e.g. one of the
  `tests/fixtures/*.ndjson` files) to feed the binary.
- `--prefix N` — optional. Sets `KIOTA_MAX_DECL=N` before running, so the
  checker declines once it has processed `N` declarations. Use this to A/B
  a fixed-size prefix of a large corpus instead of paying for the whole
  thing on every run. (`KIOTA_MAX_DECL` is an existing env var read in
  `src/parser.rs`; this script does not add new kernel behavior, it just
  sets the variable.)

Output is one line of JSON on stdout:

```json
{"instructions": 123456789, "wall_ms": 842, "peak_rss_kb": 51200, "sha": "<sha>", "prefix": null}
```

- `instructions` is callgrind **Ir** (instructions retired). It is `null`
  if `valgrind` is not on `PATH` (a clear skip notice is printed to stderr
  in that case). It is never invented from wall time, RSS, or the arena's
  ⏱️ column.
- `wall_ms` is elapsed real time for a separate, plain (no-valgrind) run,
  measured with bash `$EPOCHREALTIME` (bash 5+) or `date +%s%N`. It does
  not require GNU `time`.
- `peak_rss_kb` is that same plain run's peak RSS from
  `/proc/<pid>/status` `VmHWM` (kB), sampled while the child is alive.
  It does not require GNU `time`. `/usr/bin/time -v` is an optional
  cross-check and is used only if `/proc` sampling produced nothing.
- Valgrind's own wall time and RSS are ignored: they include instrumentation
  overhead and are not comparable.

## How this relates to the arena sort key

The Lean Kernel Arena's ⏱️ column is **not** wall-clock time. It is virtual
CPU time derived from instruction counts at a fixed **6.0 Ginstr/s**. Field
3 of the arena sort key is the **raw mathlib instruction count** (Ir), not
that derived ⏱️ value.

So `instructions` (callgrind Ir) is the number this harness exists to
produce. Do not treat `wall_ms` as ⏱️, and do not compute a fake Ir as
`wall_ms * 6.0e6`. If valgrind is missing, `instructions` stays `null`.

`wall_ms` and `peak_rss_kb` are diagnostics for local A/B runs.

## Comparing two runs of the same SHA

Run it twice against the same SHA and diff the JSON to sanity-check
noise/variance before trusting a cross-SHA comparison:

```
scripts/bench.sh HEAD tests/fixtures/067_eqRec.accept.ndjson > /tmp/run1.json
scripts/bench.sh HEAD tests/fixtures/067_eqRec.accept.ndjson > /tmp/run2.json
diff <(cat /tmp/run1.json) <(cat /tmp/run2.json)
```

`instructions` should be identical (or very close) run-to-run for the same
binary and input, since it's a deterministic count rather than a timing.
`wall_ms` and `peak_rss_kb` can vary with machine load; run a few times and
look at the spread before drawing conclusions from a single sample.

## Comparing two SHAs (A/B)

```
scripts/bench.sh <sha-A> tests/fixtures/big-corpus.ndjson --prefix 5000 > /tmp/a.json
scripts/bench.sh <sha-B> tests/fixtures/big-corpus.ndjson --prefix 5000 > /tmp/b.json
cat /tmp/a.json /tmp/b.json
```

Compare the `instructions` field between the two JSON objects — that's the
primary signal this harness exists to produce, since it does not depend on
`perf` (which may be unavailable or require elevated privileges) and is
less noisy than wall-clock time.

## Requirements

- `cargo` (for building from a SHA; not needed if you pass an
  already-built binary path).
- `valgrind` (optional, for instruction counts). If missing, the script
  still runs and reports `wall_ms`/`peak_rss_kb`, with `instructions: null`
  and a skip notice on stderr.
- `/proc` (Linux) for `peak_rss_kb`. `/usr/bin/time` is optional: wall
  time is always measured by the script, and `peak_rss_kb` comes from
  `VmHWM` when `/proc` is available.

## Cache

Per-SHA builds live under `.bench-cache/<sha>/` (a `git worktree` checked
out from the SHA, plus its own `target/release/kiota`). This directory is
git-ignored. Delete it (or set `KIOTA_BENCH_CACHE=/some/other/dir`) to
force a clean rebuild.
