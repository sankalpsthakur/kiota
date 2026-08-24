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
# on PATH. Wall time and peak RSS come from a separate, unaltered (no
# valgrind) run, since valgrind's own overhead makes its wall time and RSS
# meaningless for comparison. If valgrind is missing, instructions is null
# and a clear skip notice is printed to stderr; wall_ms/peak_rss_kb are
# still measured.
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

RUN_ENV=()
if [ -n "$PREFIX" ]; then
    RUN_ENV+=("KIOTA_MAX_DECL=$PREFIX")
fi

# --- Plain run: wall_ms + peak_rss_kb (no valgrind overhead) ---------------

WALL_MS=""
PEAK_RSS_KB=""

if command -v /usr/bin/time >/dev/null 2>&1; then
    TIME_OUT="$(mktemp)"
    trap 'rm -f "$TIME_OUT"' RETURN 2>/dev/null || true
    if env "${RUN_ENV[@]}" /usr/bin/time -v "$BIN" "$CORPUS" >/dev/null 2>"$TIME_OUT"; then :; else :; fi
    WALL_CLOCK="$(grep -E 'Elapsed \(wall clock\) time' "$TIME_OUT" | sed -E 's/.*: *//')"
    if [ -n "${WALL_CLOCK:-}" ]; then
        # Formats: [h:]mm:ss.ss or m:ss.ss
        IFS=: read -ra PARTS <<<"$WALL_CLOCK"
        if [ "${#PARTS[@]}" -eq 3 ]; then
            WALL_MS=$(awk -v h="${PARTS[0]}" -v m="${PARTS[1]}" -v s="${PARTS[2]}" \
                'BEGIN { printf "%d", (h*3600 + m*60 + s) * 1000 }')
        else
            WALL_MS=$(awk -v m="${PARTS[0]}" -v s="${PARTS[1]}" \
                'BEGIN { printf "%d", (m*60 + s) * 1000 }')
        fi
    fi
    PEAK_RSS_KB="$(grep -E 'Maximum resident set size' "$TIME_OUT" | sed -E 's/.*: *//')"
    rm -f "$TIME_OUT"
else
    echo "bench.sh: /usr/bin/time not found; timing wall clock manually, peak_rss_kb will be null" >&2
    START_NS=$(date +%s%N)
    env "${RUN_ENV[@]}" "$BIN" "$CORPUS" >/dev/null 2>&1 || true
    END_NS=$(date +%s%N)
    WALL_MS=$(( (END_NS - START_NS) / 1000000 ))
fi

# --- Valgrind/callgrind run: instructions -----------------------------------

INSTRUCTIONS=""

if command -v valgrind >/dev/null 2>&1; then
    CALLGRIND_OUT="$(mktemp)"
    if env "${RUN_ENV[@]}" valgrind --tool=callgrind --callgrind-out-file="$CALLGRIND_OUT" \
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
