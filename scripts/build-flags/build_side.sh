#!/usr/bin/env bash
# Build one variant of the release binary for the build-flags comparison.
#   build_side.sh <plain|native|pgo|nativepgo|stalepgo> <training export> <output binary>
# The profile-guided variants are trained on the given export with the
# `pgo-gen` feature, which is what makes the training run write a profile.
# `stalepgo` is the recipe as it was before that feature existed (native,
# no feature, profiles left by the build scripts merged in): kept only to
# show what an earlier comparison had measured under the name "pgo".
set -euo pipefail
side=$1; train=$2; out=$3
case "$side" in
  plain|pgo) cpu="" ;;
  native|nativepgo|stalepgo) cpu="-C target-cpu=native" ;;
  *) echo "unknown side $side" >&2; exit 2 ;;
esac
case "$side" in
  pgo|nativepgo)
    prof="$PWD/pgo-$side"
    profdata=$(ls "$(rustc --print sysroot)"/lib/rustlib/*/bin/llvm-profdata | head -n 1)
    RUSTFLAGS="$cpu -C profile-generate=$prof" cargo build --release --locked \
      --features pgo-gen --target-dir "t-gen-$side" 2>&1 | tail -n 1
    echo "PROFILES side=$side written_by_build_scripts=$(find "$prof" -name '*.profraw' 2>/dev/null | wc -l)"
    rm -rf "$prof"
    /usr/bin/time -f "TRAIN side=$side user=%U maxrss_kb=%M" "t-gen-$side/release/kiota" "$train" >/dev/null 2>train.err \
      || { tail -n 5 train.err; echo "training run failed" >&2; exit 1; }
    tail -n 1 train.err
    echo "PROFILES side=$side written_by_training=$(find "$prof" -name '*.profraw' | wc -l) bytes=$(du -sb "$prof" | cut -f1)"
    "$profdata" merge -o "$prof.profdata" "$prof"
    "$profdata" show "$prof.profdata" | sed -n '2,7p' | tr '\n' ';'; echo
    RUSTFLAGS="$cpu -C profile-use=$prof.profdata" cargo build --release --locked --target-dir "t-$side" 2>&1 | tail -n 1
    ;;
  stalepgo)
    prof="$PWD/pgo-$side"
    profdata=$(ls "$(rustc --print sysroot)"/lib/rustlib/*/bin/llvm-profdata | head -n 1)
    RUSTFLAGS="$cpu -C profile-generate=$prof" cargo build --release --locked --target-dir "t-gen-$side" 2>&1 | tail -n 1
    before=$(find "$prof" -name '*.profraw' | wc -l)
    "t-gen-$side/release/kiota" "$train" >/dev/null 2>&1 || true
    echo "PROFILES side=$side written_by_build_scripts=$before after_training=$(find "$prof" -name '*.profraw' | wc -l)"
    "$profdata" merge -o "$prof.profdata" "$prof"
    "$profdata" show "$prof.profdata" | sed -n '2,7p' | tr '\n' ';'; echo
    RUSTFLAGS="$cpu -C profile-use=$prof.profdata" cargo build --release --locked --target-dir "t-$side" 2>&1 | tail -n 1
    ;;
  *)
    RUSTFLAGS="$cpu" cargo build --release --locked --target-dir "t-$side" 2>&1 | tail -n 1
    ;;
esac
cp "t-$side/release/kiota" "$out"
echo "BUILT side=$side bytes=$(stat -c %s "$out") sha=$(sha256sum "$out" | cut -c1-12) cpu=$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs)"
