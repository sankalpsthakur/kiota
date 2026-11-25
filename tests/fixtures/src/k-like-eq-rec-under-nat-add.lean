/-
Source of `k-like-eq-rec-under-nat-add.{accept,reject}` (Lean 4.36.0; exported
with `leanexport Adv2 -- Adv2.k_nat_ok` / `Adv2.k_nat_bad`). The K-like
`Eq.rec` whose proof is `Std.Time.Nanosecond.Offset.ofHours._proof_1` sits
under `Nat.add`, so the closed-`Nat` driver evaluates it; the comparison that
reduces it must keep its own depth cap (a deeper one counts a literal of 2^29
or more down until the peel budget declines).
-/
import Lean
import Std.Time
open Lean Elab Command Meta

def findProof : CoreM Name := do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if n.toString.endsWith "Std.Time.Nanosecond.Offset.ofHours._proof_1" then return n
  throwError "not found"

/-- Build `lhs = 7` where lhs is `Eq.rec (motive := fun _ _ => Nat) 7 P` (+ 0 when `wrap`). -/
def mk (thm : Name) (wrap : Bool) (rhs : Nat) : CommandElabM Unit := liftTermElabM do
  let p ← findProof
  let ci ← getConstInfo p
  let some (α, a, b) := ci.type.eq? | throwError "not eq {ci.type}"
  let nat := mkConst ``Nat
  let motive := mkLambda `x .default α (mkLambda `h .default (← mkEq a (.bvar 0)) nat)
  let seven := mkNatLit 7
  let er := mkAppN (mkConst ``Eq.rec [1, 1]) #[α, a, motive, seven, b, mkConst p]
  let lhs := if wrap then mkApp2 (mkConst ``Nat.add) er (mkNatLit 0) else er
  let ty ← mkEq lhs (mkNatLit rhs)
  addDecl (.thmDecl { name := thm, levelParams := [], type := ty, value := ← mkEqRefl lhs })
  logInfo m!"{p} : {ci.type}"

set_option debug.skipKernelTC true
run_cmd mk `Adv2.k_nat_ok true 7
run_cmd mk `Adv2.k_nat_bad true 8
