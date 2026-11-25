import R2
open Lean Elab Command Meta
open R2

def addRefl3 (n : Name) (stx : Term) : CommandElabM Unit := liftTermElabM do
  let ty ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let val ← forallTelescope ty fun xs body => do
    let some (α, lhs, _) := body.eq? | throwError "not an Eq"
    let u ← getLevel α
    mkLambdaFVars xs (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  addDecl (.thmDecl { name := n, levelParams := [], type := ty, value := val })

set_option debug.skipKernelTC true
-- open twins of the R2 spines (x free: not driven, cut at the depth cap)
run_cmd addRefl3 `R3.ogp_ok (← `(∀ x : Nat, gp 14 x = x + 16384))
run_cmd addRefl3 `R3.ogi_ok (← `(∀ x : Nat, gi 13 x = x + 8192))
run_cmd addRefl3 `R3.ogk_ok (← `(∀ x : Nat, gk 14 x = x + 16384))
run_cmd addRefl3 `R3.ogm_ok (← `(∀ x : Nat, gm 14 x = x + 16384))
run_cmd addRefl3 `R3.olen_ok (← `(∀ u : Unit, (List.replicate 20000 u).length = 20000))
run_cmd addRefl3 `R3.olen2_ok (← `(∀ u : Unit, (List.replicate 20000 u).length * 1 = 20000))
-- open, both sides deep and structurally different
run_cmd addRefl3 `R3.oshift_ok (← `(∀ x : Nat, g 14 (x + 1) = g 14 x + 1))
-- closed deep value against open deep value
run_cmd addRefl3 `R3.omix_ok (← `(∀ x : Nat, g 14 0 + x = x + g 14 0))
-- cntR straddling the pending cap (~1200 * 1024)
run_cmd addRefl3 `R3.cap_lo_ok (← `(cntR 1150000 = 1150000))
run_cmd addRefl3 `R3.cap_hi_ok (← `(cntR 1300000 = 1300000))
run_cmd addRefl3 `R3.cap_lo_bad (← `(cntR 1150000 = 1150001))
