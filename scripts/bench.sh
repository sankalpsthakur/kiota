#!/usr/bin/env bash
# scripts/bench.sh — measurement harness for A/B'ing instruction counts, wall
# time, and peak RSS across kiota builds, without requiring Linux `perf`.
#
# Usage:
#   scripts/bench.sh <sha-or-bin> <corpus> [--prefix N]
#
#   <sha-or-bin>  A git commit/tag/branch to build --release, or a path to an
#                 already-built kiota binary.
#   <corpus>      Path to a single export file (ndjson) to feed the binary.
#   --prefix N    Optional. Sets KIOTA_MAX_DECL=N so the checker declines
#                 after N declarations, letting you A/B a fixed-size prefix
#                 of a large corpus instead of the whole thing.
#
# Output: one JSON object on stdout:
#   {"instructions": <int|null>, "wall_ms": <int|null>,
#    "peak_rss_kb": <int|null>, "sha": "<string>", "prefix": <int|null>}
#
# Instruction counts come from `valgrind --tool=callgrind` when valgrind is
# on PATH (callgrind Ir). That field is never derived from wall time or from
# the arena's ⏱️ column (virtual CPU at a fixed 6.0 Ginstr/s). If valgrind is
# missing, instructions is null and a clear skip notice is printed to stderr.
#
# Wall time and peak RSS come from a separate, unaltered (no valgrind) run,
# since valgrind's own overhead makes its wall time and RSS meaningless for
# comparison. wall_ms is elapsed real time via $EPOCHREALTIME (bash 5+) or
# date +%s%N; peak_rss_kb is /proc/<pid>/status VmHWM (kB). Neither field
# requires GNU time or valgrind. /usr/bin/time, if present, is an optional
# cross-check / last-resort RSS fallback only.
#
# See scripts/README-bench.md for how to compare two runs of the same SHA.

set -euo pipefail

die() {
    echo "bench.sh: $*" >&2
    exit 1
}

usage() {
    echo "usage: $0 <sha-or-bin> <corpus> [--prefix N]" >&2
    exit 1
}

[ "$#" -ge 2 ] || usage

SHA_OR_BIN="$1"
CORPUS="$2"
shift 2

PREFIX=""
while [ "$#" -gt 0 ]; do
    case "$1" in
        --prefix)
            [ "$#" -ge 2 ] || die "--prefix requires a value"
            PREFIX="$2"
            shift 2
            ;;
        *)
            die "unknown argument: $1"
            ;;
    esac
done

[ -f "$CORPUS" ] || die "corpus not found: $CORPUS"

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CACHE_DIR="${KIOTA_BENCH_CACHE:-$REPO_ROOT/.bench-cache}"

SHA=""
BIN=""

if [ -f "$SHA_OR_BIN" ] && [ -x "$SHA_OR_BIN" ]; then
    # Already-built binary: use it as-is, no build step.
    BIN="$(cd "$(dirname "$SHA_OR_BIN")" && pwd)/$(basename "$SHA_OR_BIN")"
    SHA="$SHA_OR_BIN"
else
    ( cd "$REPO_ROOT" && git rev-parse --verify "${SHA_OR_BIN}^{commit}" >/dev/null 2>&1 ) \
        || die "not an executable file and not a valid git commit: $SHA_OR_BIN"
    SHA="$(cd "$REPO_ROOT" && git rev-parse "${SHA_OR_BIN}^{commit}")"

    WORKTREE="$CACHE_DIR/$SHA"
    BIN="$WORKTREE/target/release/kiota"

    if [ ! -x "$BIN" ]; then
        echo "bench.sh: building $SHA --release (first run for this sha)..." >&2
        mkdir -p "$CACHE_DIR"
        if [ ! -d "$WORKTREE" ]; then
            ( cd "$REPO_ROOT" && git worktree add --detach "$WORKTREE" "$SHA" >&2 )
        fi
        ( cd "$WORKTREE" && cargo build --release --quiet )
        [ -x "$BIN" ] || die "build did not produce $BIN"
    else
        echo "bench.sh: reusing cached build for $SHA" >&2
    fi
fi

RUN_COMMAND=(env)
if [ -n "$PREFIX" ]; then
    RUN_COMMAND+=("KIOTA_MAX_DECL=$PREFIX")
fi

# --- Plain run: wall_ms + peak_rss_kb (no valgrind overhead) ---------------
# Wall and RSS are measured directly. /usr/bin/time is never required.

# Integer microseconds from $EPOCHREALTIME (sec.usec) or date +%s%N.
realtime_to_us() {
    local t="$1" sec frac
    sec="${t%%.*}"
    frac="${t#*.}"
    if [ "$sec" = "$t" ]; then
        frac="0"
    fi
    frac="${frac}000000"
    frac="${frac:0:6}"
    printf '%s' "$((10#$sec * 1000000 + 10#$frac))"
}

now_us() {
    if [ -n "${EPOCHREALTIME:-}" ]; then
        realtime_to_us "$EPOCHREALTIME"
    else
        local ns
        ns="$(date +%s%N 2>/dev/null || true)"
        case "$ns" in
            ''|*[!0-9]*)
                ns="$(date +%s)000000000"
                ;;
        esac
        printf '%s' "$((10#$ns / 1000))"
    fi
}

# VmHWM is kB. Empty output if /proc is missing or the pid is already gone.
# Parse with bash builtins so we can poll without forking awk on every sample.
read_proc_vmhwm_state() {
    # Sets PROC_VMHWM and PROC_STATE. Both empty if /proc/<pid>/status
    # cannot be read (process already reaped).
    PROC_VMHWM=""
    PROC_STATE=""
    local status="/proc/${1}/status" key rest
    [ -r "$status" ] || return 0
    while IFS=$' \t' read -r key rest; do
        case "$key" in
            State:)
                PROC_STATE="${rest#"${rest%%[![:space:]]*}"}"
                PROC_STATE="${PROC_STATE%%[[:space:]]*}"
                ;;
            VmHWM:)
                PROC_VMHWM="${rest#"${rest%%[![:space:]]*}"}"
                PROC_VMHWM="${PROC_VMHWM%%[[:space:]]*}"
                ;;
        esac
    done < "$status" 2>/dev/null || true
}

# Sample the child's VmHWM until it exits. Bash may reap background children
# on SIGCHLD, so a post-wait /proc/<pid> read is unreliable; stop on zombie
# (State Z), a failed read, or once /proc/<pid>/status is gone. VmHWM is a
# kernel high-water mark, so the last successful read is the peak up to
# that point. Busy-poll at first so tiny fixtures are not missed, then
# back off so a long run does not pin a core.
# Sets PEAK_RSS_KB in this shell (not via command substitution).
sample_peak_rss_kb() {
    local pid="$1" last="" polls=0
    while :; do
        read_proc_vmhwm_state "$pid"
        if [ -n "$PROC_VMHWM" ]; then
            last="$PROC_VMHWM"
        fi
        case "$PROC_STATE" in
            Z*) break ;;
        esac
        if [ -z "$PROC_VMHWM" ] && [ -z "$PROC_STATE" ]; then
            break
        fi
        polls=$((polls + 1))
        if [ "$polls" -gt 200 ]; then
            sleep 0.01 2>/dev/null || true
        fi
    done
    PEAK_RSS_KB="$last"
}

parse_gnu_time_rss_kb() {
    awk -F ': ' '/Maximum resident set size/ { print $NF; exit }' "$1"
}

WALL_MS=""
PEAK_RSS_KB=""

if [ -n "${EPOCHREALTIME:-}" ]; then
    START_US="$(realtime_to_us "$EPOCHREALTIME")"
else
    START_US="$(now_us)"
fi
"${RUN_COMMAND[@]}" "$BIN" "$CORPUS" >/dev/null 2>&1 &
CHILD_PID=$!
# Sample in this shell (not a command substitution) so the first /proc
# read is not delayed by an extra fork.
sample_peak_rss_kb "$CHILD_PID"
# Child may already be a zombie; one more /proc/<pid> read before wait.
read_proc_vmhwm_state "$CHILD_PID"
if [ -n "$PROC_VMHWM" ]; then
    PEAK_RSS_KB="$PROC_VMHWM"
fi
wait "$CHILD_PID" || true
if [ -n "${EPOCHREALTIME:-}" ]; then
    END_US="$(realtime_to_us "$EPOCHREALTIME")"
else
    END_US="$(now_us)"
fi
WALL_MS=$(( (END_US - START_US) / 1000 ))

# After wait, bash has reaped the child so /proc/<pid> is gone.
# /proc/self/status would be this shell, not kiota — do not substitute it.

# Optional GNU time cross-check: fill peak_rss_kb only if /proc sampling
# produced nothing (no /proc, or the child exited before the first read).
if [ -z "${PEAK_RSS_KB:-}" ] && [ -x /usr/bin/time ]; then
    TIME_OUT="$(mktemp)"
    TIME_PROBE="$(mktemp)"
    if /usr/bin/time -v true >/dev/null 2>"$TIME_PROBE" \
        && grep -q 'Elapsed (wall clock) time' "$TIME_PROBE"; then
        echo "bench.sh: /proc VmHWM unavailable; GNU time -v fallback for peak_rss_kb" >&2
        if "${RUN_COMMAND[@]}" /usr/bin/time -v "$BIN" "$CORPUS" \
            >/dev/null 2>"$TIME_OUT"; then :; else :; fi
        PEAK_RSS_KB="$(parse_gnu_time_rss_kb "$TIME_OUT")"
    else
        echo "bench.sh: /proc VmHWM unavailable and GNU time -v missing; peak_rss_kb will be null" >&2
    fi
    rm -f "$TIME_OUT" "$TIME_PROBE"
elif [ -z "${PEAK_RSS_KB:-}" ]; then
    echo "bench.sh: /proc VmHWM unavailable; peak_rss_kb will be null" >&2
fi

# --- Valgrind/callgrind run: instructions -----------------------------------

INSTRUCTIONS=""

if command -v valgrind >/dev/null 2>&1; then
    CALLGRIND_OUT="$(mktemp)"
    if "${RUN_COMMAND[@]}" valgrind --tool=callgrind --callgrind-out-file="$CALLGRIND_OUT" \
        --quiet -- "$BIN" "$CORPUS" >/dev/null 2>&1; then :; else :; fi
    # The callgrind output file's "summary:" line is the total cost for the
    # collected events; with default settings the sole event is Ir
    # (instructions retired).
    INSTRUCTIONS="$(grep -m1 '^summary:' "$CALLGRIND_OUT" | awk '{print $2}')"
    rm -f "$CALLGRIND_OUT"
else
    echo "bench.sh: SKIP — valgrind not found on PATH; instructions will be null. Install valgrind to get instruction counts (apt-get install valgrind / brew install valgrind)." >&2
fi

# --- Emit JSON ---------------------------------------------------------------

json_num_or_null() {
    if [ -n "${1:-}" ]; then printf '%s' "$1"; else printf 'null'; fi
}

printf '{"instructions": %s, "wall_ms": %s, "peak_rss_kb": %s, "sha": "%s", "prefix": %s}\n' \
    "$(json_num_or_null "${INSTRUCTIONS:-}")" \
    "$(json_num_or_null "${WALL_MS:-}")" \
    "$(json_num_or_null "${PEAK_RSS_KB:-}")" \
    "$SHA" \
    "$(json_num_or_null "${PREFIX:-}")"
