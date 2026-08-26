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

RUN_COMMAND=(env)
if [ -n "$PREFIX" ]; then
    RUN_COMMAND+=("KIOTA_MAX_DECL=$PREFIX")
fi

# --- Plain run: wall_ms + peak_rss_kb (no valgrind overhead) ---------------

WALL_MS=""
PEAK_RSS_KB=""

if [ -x /usr/bin/time ]; then
    TIME_OUT="$(mktemp)"
    TIME_PROBE="$(mktemp)"
    if /usr/bin/time -v true >/dev/null 2>"$TIME_PROBE" \
        && grep -q 'Elapsed (wall clock) time' "$TIME_PROBE"; then
        if "${RUN_COMMAND[@]}" /usr/bin/time -v "$BIN" "$CORPUS" \
            >/dev/null 2>"$TIME_OUT"; then :; else :; fi
        # Split on the label/value separator (`: `), not the colons inside
        # GNU time's `[h:]mm:ss` value.
        WALL_CLOCK="$(awk -F ': ' '/Elapsed \(wall clock\) time/ { print $NF; exit }' "$TIME_OUT")"
        if [ -n "${WALL_CLOCK:-}" ]; then
            IFS=: read -ra PARTS <<<"$WALL_CLOCK"
            if [ "${#PARTS[@]}" -eq 3 ]; then
                WALL_MS=$(awk -v h="${PARTS[0]}" -v m="${PARTS[1]}" -v s="${PARTS[2]}" \
                    'BEGIN { printf "%d", (h*3600 + m*60 + s) * 1000 }')
            elif [ "${#PARTS[@]}" -eq 2 ]; then
                WALL_MS=$(awk -v m="${PARTS[0]}" -v s="${PARTS[1]}" \
                    'BEGIN { printf "%d", (m*60 + s) * 1000 }')
            fi
        fi
        PEAK_RSS_KB="$(awk -F ': ' '/Maximum resident set size/ { print $NF; exit }' "$TIME_OUT")"
    else
        # POSIX `-p` works with GNU, macOS, and BSD time. It reports wall time
        # but not peak RSS in a portable unit.
        if "${RUN_COMMAND[@]}" /usr/bin/time -p "$BIN" "$CORPUS" \
            >/dev/null 2>"$TIME_OUT"; then :; else :; fi
        WALL_SECONDS="$(awk '$1 == "real" { print $2; exit }' "$TIME_OUT")"
        if [ -n "${WALL_SECONDS:-}" ]; then
            WALL_MS=$(awk -v s="$WALL_SECONDS" 'BEGIN { printf "%d", s * 1000 }')
        fi
        echo "bench.sh: GNU time -v unavailable; peak_rss_kb will be null" >&2
    fi
    rm -f "$TIME_OUT" "$TIME_PROBE"
else
    echo "bench.sh: /usr/bin/time not found; wall_ms and peak_rss_kb will be null" >&2
    "${RUN_COMMAND[@]}" "$BIN" "$CORPUS" >/dev/null 2>&1 || true
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
