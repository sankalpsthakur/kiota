#!/bin/sh
# Export the prelude-free Lean files beside this script, and the variants of
# Genuine.lean in which exactly one definition is wrong, to *.base.ndjson in
# the current directory. Needs `lean` (4.33.0) and `lean4export` on PATH.
#
#   sh make_bases.sh && python3 forged_fixtures.py . ../..
set -e
src=$(cd "$(dirname "$0")" && pwd)
export_one() { # <module>
  lean -o "$1.olean" "$1.lean"
  LEAN_PATH=$PWD lean4export "$1" > "$1.base.ndjson"
}
for m in Forged ForgedCtors ForgedBitwise ForgedLarge ForgedString Genuine; do
  [ -f "$m.lean" ] || cp "$src/$m.lean" .
  export_one "$m"
done
# One wrong definition each; every other one stays genuine, so the wrong one
# fails on its own equations and not for want of a validated neighbour.
variant() { # <name> <python: s.replace(old, new)>
  python3 - "$src/Genuine.lean" "GenuineBut$1.lean" "$2" "$3" <<'PY'
import sys
src, dst, old, new = sys.argv[1:5]
s = open(src).read()
assert s.count(old) == 1, (dst, old)
open(dst, "w").write(s.replace(old, new))
PY
  export_one "GenuineBut$1"
}
# mul x 0 = x
variant Mul 'Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ ih => Nat.add ih a) b' \
            'Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.add ih a) b'
# pow x 0 = 0
variant Pow 'Nat.rec (motive := fun _ => Nat) (Nat.succ Nat.zero) (fun _ ih => Nat.mul ih a) b' \
            'Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ ih => Nat.mul ih a) b'
# pred (succ n) = succ n
variant Pred 'Nat.rec (motive := fun _ => Nat) Nat.zero (fun n _ => n) a' \
             'Nat.rec (motive := fun _ => Nat) Nat.zero (fun n _ => Nat.succ n) a'
# sub x (succ y) = pred (pred (sub x y))
variant Sub 'Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.pred ih) b' \
            'Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.pred (Nat.pred ih)) b'
# beq 0 (succ x) = true: this is ble
variant Beq '(fun b => Nat.rec (motive := fun _ => Bool) Bool.true (fun _ _ => Bool.false) b)' \
            '(fun b => Nat.rec (motive := fun _ => Bool) Bool.true (fun _ _ => Bool.true) b)'
# ble 0 (succ x) = false: this is beq
variant Ble '    (fun _ => Bool.true)
    (fun _ ih b => Nat.rec (motive := fun _ => Bool) Bool.false (fun m _ => ih m) b) a b
noncomputable def Nat.shiftLeft' \
            '    (fun b => Nat.rec (motive := fun _ => Bool) Bool.true (fun _ _ => Bool.false) b)
    (fun _ ih b => Nat.rec (motive := fun _ => Bool) Bool.false (fun m _ => ih m) b) a b
noncomputable def Nat.shiftLeft'
# shiftLeft x (succ y) = shiftLeft x y
variant ShiftLeft '(fun _ ih a => ih (Nat.mul (Nat.succ (Nat.succ Nat.zero)) a)) b a' \
                  '(fun _ ih a => ih a) b a'
# add x (succ y) = succ (succ (add x y))
variant Add 'Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.succ ih) b' \
            'Nat.rec (motive := fun _ => Nat) a (fun _ ih => Nat.succ (Nat.succ ih)) b'
