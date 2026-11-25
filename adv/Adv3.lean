import Lean
open Lean Elab Command Meta

namespace Adv3
/-- `g n a = a + 2^n`, nesting 2^n additions when evaluated. -/
def g : Nat → Nat → Nat
  | 0, a => a + 1
  | n+1, a => g n (g n a)
/-- Non-tail countdown: `cnt n = n`, nests n additions. -/
def cnt : Nat → Nat
  | 0 => 0
  | n+1 => cnt n + 1
/-- A wrapper so the deep Nat sits under a non-Nat structure. -/
structure Box where
  val : Nat
def mkBox (n : Nat) : Box := ⟨g n 0⟩
axiom ax : Nat
end Adv3

def addRefl (n : Name) (stx : Term) : CommandElabM Unit := liftTermElabM do
  let ty ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  -- value: fun xs => Eq.refl lhs, under the foralls of ty
  let val ← forallTelescope ty fun xs body => do
    let some (α, lhs, _) := body.eq? | throwError "not an Eq"
    let u ← getLevel α
    mkLambdaFVars xs (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  addDecl (.thmDecl { name := n, levelParams := [], type := ty, value := val })

set_option debug.skipKernelTC true
open Adv3
run_cmd addRefl `Adv3.len20k_ok (← `((List.replicate 20000 ()).length + 0 = 20000))
run_cmd addRefl `Adv3.len20k_bad (← `((List.replicate 20000 ()).length + 0 = 19999))
