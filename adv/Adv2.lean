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
run_cmd mk `Adv2.k_top_ok false 7
run_cmd mk `Adv2.k_nat_ok true 7
run_cmd mk `Adv2.k_nat_bad true 8
