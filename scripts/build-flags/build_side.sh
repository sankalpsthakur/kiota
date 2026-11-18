#!/usr/bin/env bash
# Build one variant of the release binary for the build-flags comparison.
#   build_side.sh <side> <training export> <output binary>
# A side is `plain` or a `+`-joined set of
#   native      -C target-cpu=native
#   v3          -C target-cpu=x86-64-v3 (what valgrind can still run; the
#               GitHub runners' native CPUs have AVX-512, which it cannot)
#   inlineN     -C llvm-args=-inline-threshold=N
#   pgo         profile-guided, trained on the given export with the `pgo-gen`
#               feature, which is what makes the training run write a profile
#   stale       the profile-guided recipe as it was before that feature
#               existed (no feature, the build scripts' profiles merged in):
#               kept only to show what an earlier comparison had measured
#               under the name "pgo"
# Output file name: kiota-<side> with `+` kept, e.g. kiota-pgo+inline2000.
set -euo pipefail
side=$1; train=$2; out=$3
flags=""; pgo=""; stale=""
IFS='+' read -r -a parts <<< "$side"
for part in "${parts[@]}"; do
  case "$part" in
    plain) ;;
    native) flags="$flags -C target-cpu=native" ;;
    v3) flags="$flags -C target-cpu=x86-64-v3" ;;
    inline[0-9]*) flags="$flags -C llvm-args=-inline-threshold=${part#inline}" ;;
    pgo) pgo=1 ;;
    stale) stale=1 ;;
    *) echo "unknown part $part of side $side" >&2; exit 2 ;;
  esac
done
prof="$PWD/prof-$side"
profdata_tool() { ls "$(rustc --print sysroot)"/lib/rustlib/*/bin/llvm-profdata | head -n 1; }
if [ -n "$pgo" ]; then
  RUSTFLAGS="$flags -C profile-generate=$prof" cargo build --release --locked \
    --features pgo-gen --target-dir "t-gen-$side" 2>&1 | tail -n 1
  echo "PROFILES side=$side written_by_build_scripts=$(find "$prof" -name '*.profraw' 2>/dev/null | wc -l)"
  rm -rf "$prof"
  /usr/bin/time -f "TRAIN side=$side user=%U maxrss_kb=%M" "t-gen-$side/release/kiota" "$train" >/dev/null 2>train.err \
    || { tail -n 5 train.err; echo "training run failed" >&2; exit 1; }
  tail -n 1 train.err
  echo "PROFILES side=$side written_by_training=$(find "$prof" -name '*.profraw' | wc -l) bytes=$(du -sb "$prof" | cut -f1)"
  "$(profdata_tool)" merge -o "$prof.profdata" "$prof"
  "$(profdata_tool)" show "$prof.profdata" | sed -n '2,7p' | tr '\n' ';'; echo
  flags="$flags -C profile-use=$prof.profdata"
elif [ -n "$stale" ]; then
  RUSTFLAGS="$flags -C profile-generate=$prof" cargo build --release --locked --target-dir "t-gen-$side" 2>&1 | tail -n 1
  before=$(find "$prof" -name '*.profraw' | wc -l)
  "t-gen-$side/release/kiota" "$train" >/dev/null 2>&1 || true
  echo "PROFILES side=$side written_by_build_scripts=$before after_training=$(find "$prof" -name '*.profraw' | wc -l)"
  "$(profdata_tool)" merge -o "$prof.profdata" "$prof"
  "$(profdata_tool)" show "$prof.profdata" | sed -n '2,7p' | tr '\n' ';'; echo
  flags="$flags -C profile-use=$prof.profdata"
fi
RUSTFLAGS="$flags" cargo build --release --locked --target-dir "t-$side" 2>&1 | tail -n 1
cp "t-$side/release/kiota" "$out"
echo "$flags" > "$out.rustflags"
echo "BUILT side=$side bytes=$(stat -c %s "$out") sha=$(sha256sum "$out" | cut -c1-12) cpu=$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs)"
