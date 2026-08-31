#!/usr/bin/env bash
# bench.sh — eager vs NbE (KIOTA_NBE=1) instruction-count comparison on a
# KIOTA_MAX_DECL-bounded prefix of an ndjson export.
#
# Primary signal: valgrind --tool=callgrind (deterministic instruction
# count, not wall-clock — safe to compare across runs/hosts). Secondary,
# best-effort signal: `perf stat -e instructions` (some hosts forbid
# performance counters entirely; this script degrades gracefully rather
# than failing when that happens).
#
# Usage:
#   ./bench.sh --input path/to/export.ndjson [--max-decl N] [--repeat N] [--release|--debug]
#
# Prints one JSON object to stdout. Determinism: `repeat` (default 2) runs
# of the *same* flag on the *same* binary should report identical Ir counts;
# the JSON records whether they did (`deterministic`).
#
# This does not require or fabricate arena-scale numbers: with no --input,
# or on a host with no giant corpus available, run it against whatever
# ndjson prefix you have (e.g. a `tests/fixtures/*.ndjson` file) — the
# script reports exactly what it measured, nothing more.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"

INPUT=""
MAX_DECL=""
REPEAT=2
PROFILE="release"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --input) INPUT="$2"; shift 2 ;;
    --max-decl) MAX_DECL="$2"; shift 2 ;;
    --repeat) REPEAT="$2"; shift 2 ;;
    --release) PROFILE="release"; shift ;;
    --debug) PROFILE="debug"; shift ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

if [[ -z "$INPUT" ]]; then
  echo "usage: $0 --input path/to/export.ndjson [--max-decl N] [--repeat N] [--release|--debug]" >&2
  exit 2
fi
if [[ ! -f "$INPUT" ]]; then
  echo "input not found: $INPUT" >&2
  exit 2
fi

json_escape() {
  local s="$1"
  s="${s//\\/\\\\}"
  s="${s//\"/\\\"}"
  printf '%s' "$s"
}

SHA="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
DIRTY="false"
if ! git diff --quiet 2>/dev/null; then DIRTY="true"; fi

echo "building ($PROFILE)..." >&2
if [[ "$PROFILE" == "release" ]]; then
  cargo build --release --quiet
  BIN="./target/release/kiota"
else
  cargo build --quiet
  BIN="./target/debug/kiota"
fi

HAVE_VALGRIND=0
command -v valgrind >/dev/null 2>&1 && HAVE_VALGRIND=1
HAVE_PERF=0
if command -v perf >/dev/null 2>&1; then
  if perf stat -e instructions -- true >/tmp/bench_perf_probe.$$ 2>&1; then
    HAVE_PERF=1
  fi
  rm -f /tmp/bench_perf_probe.$$
fi

echo "valgrind: $HAVE_VALGRIND  perf: $HAVE_PERF" >&2

# Run one (flag, iteration) under callgrind; echoes the Ir count, or empty
# on decline/failure (we still want the instruction count for a Decline —
# only a crash is a real failure).
run_callgrind() {
  local flag_env="$1"
  local outfile="$2"
  rm -f "$outfile"
  local -a envs=()
  [[ -n "$MAX_DECL" ]] && envs+=("KIOTA_MAX_DECL=$MAX_DECL")
  [[ -n "$flag_env" ]] && envs+=("$flag_env")
  if ! env "${envs[@]}" valgrind --tool=callgrind --callgrind-out-file="$outfile" -- "$BIN" "$INPUT" >/tmp/bench_stdout.$$ 2>/tmp/bench_stderr.$$; then
    # kiota itself exits nonzero for Reject/Decline; that's not a bench
    # failure. Only a missing callgrind output file is.
    :
  fi
  local verdict_line
  verdict_line="$(tail -n1 /tmp/bench_stdout.$$ 2>/dev/null || true)"
  rm -f /tmp/bench_stdout.$$ /tmp/bench_stderr.$$
  if [[ ! -f "$outfile" ]]; then
    echo ""
    return
  fi
  # callgrind writes both a running `summary:` and a final `totals:` line;
  # `totals:` is the grand total across every part callgrind recorded.
  grep -E '^totals: ' "$outfile" | tail -n1 | awk '{print $2}'
}

run_perf() {
  local flag_env="$1"
  local -a envs=()
  [[ -n "$MAX_DECL" ]] && envs+=("KIOTA_MAX_DECL=$MAX_DECL")
  [[ -n "$flag_env" ]] && envs+=("$flag_env")
  local out
  out="$(env "${envs[@]}" perf stat -e instructions -- "$BIN" "$INPUT" 2>&1 >/dev/null || true)"
  echo "$out" | grep -E 'instructions' | head -n1 | sed -E 's/^\s*([0-9,]+).*/\1/' | tr -d ','
}

bench_flag() {
  local name="$1"
  local flag_env="$2"
  local cg_counts=()
  local i
  for ((i = 0; i < REPEAT; i++)); do
    if [[ "$HAVE_VALGRIND" == "1" ]]; then
      local c
      c="$(run_callgrind "$flag_env" "/tmp/bench_cg_${name}_${i}.out")"
      cg_counts+=("$c")
      echo "  $name run $i: Ir=$c" >&2
    fi
  done
  local perf_count=""
  if [[ "$HAVE_PERF" == "1" ]]; then
    perf_count="$(run_perf "$flag_env")"
    echo "  $name perf instructions=$perf_count" >&2
  fi
  local deterministic="null"
  if [[ "${#cg_counts[@]}" -ge 2 ]]; then
    deterministic="true"
    local first="${cg_counts[0]}"
    for c in "${cg_counts[@]}"; do
      if [[ "$c" != "$first" ]]; then
        deterministic="false"
      fi
    done
  fi
  local counts_json="["
  for c in "${cg_counts[@]:-}"; do
    [[ -z "$c" ]] && continue
    counts_json+="${c},"
  done
  counts_json="${counts_json%,}]"
  local perf_json="null"
  [[ -n "$perf_count" ]] && perf_json="$perf_count"
  printf '{"name":"%s","callgrind_ir":%s,"deterministic":%s,"perf_instructions":%s}' \
    "$(json_escape "$name")" "$counts_json" "$deterministic" "$perf_json"
}

EAGER_JSON="$(bench_flag "eager" "")"
NBE_JSON="$(bench_flag "nbe" "KIOTA_NBE=1")"

cat <<EOF
{
  "sha": "$(json_escape "$SHA")",
  "dirty": $DIRTY,
  "input": "$(json_escape "$INPUT")",
  "max_decl": $( [[ -n "$MAX_DECL" ]] && echo "$MAX_DECL" || echo null ),
  "repeat": $REPEAT,
  "profile": "$PROFILE",
  "have_valgrind": $( [[ "$HAVE_VALGRIND" == "1" ]] && echo true || echo false ),
  "have_perf": $( [[ "$HAVE_PERF" == "1" ]] && echo true || echo false ),
  "eager": $EAGER_JSON,
  "nbe": $NBE_JSON
}
EOF
