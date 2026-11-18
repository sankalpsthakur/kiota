#!/usr/bin/env bash
# Does a merged profile name the functions of the binary built from it?
#   profile_match.sh <label> <merged.profdata> <binary> [llvm-profdata]
# Prints one PROFILE_MATCH line and fails when no function of this crate
# named in the profile exists in the binary. rustc applies a profile whose
# names match nothing without a word, and that is what a profile recorded
# under other cargo inputs is: features, unlike RUSTFLAGS, are part of the
# crate hash in every mangled name.
set -euo pipefail
label=$1; profdata=$2; binary=$3
tool=${4:-$(ls "$(rustc --print sysroot)"/lib/rustlib/*/bin/llvm-profdata 2>/dev/null | head -n 1)}
[ -n "$tool" ] || tool=$(command -v llvm-profdata)
# Mangled names of this crate's functions, v0 (`_R..5kiota..`) or legacy.
kiota_names() { { grep -oE '_R[A-Za-z0-9_]*5kiota[A-Za-z0-9_]*|_ZN[0-9A-Za-z_$.]*5kiota[0-9A-Za-z_$.]*' || true; } | LC_ALL=C sort -u; }
tmp=$(mktemp -d)
"$tool" show --all-functions "$profdata" | kiota_names > "$tmp/profile"
nm "$binary" | awk '{print $NF}' | kiota_names > "$tmp/binary"
profiled=$(wc -l < "$tmp/profile")
found=$(LC_ALL=C comm -12 "$tmp/profile" "$tmp/binary" | wc -l)
hashes() { { grep -oE 'Cs[A-Za-z0-9]+_5kiota' "$1" || true; } | LC_ALL=C sort -u | tr '\n' ',' ; }
echo "PROFILE_MATCH label=$label kiota_functions_in_profile=$profiled of_those_in_binary=$found binary_kiota_functions=$(wc -l < "$tmp/binary") profile_crate_hashes=$(hashes "$tmp/profile") binary_crate_hashes=$(hashes "$tmp/binary")"
rm -rf "$tmp"
[ "$found" -gt 0 ] || { echo "the profile names no function of the binary" >&2; exit 1; }
