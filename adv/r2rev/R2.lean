import Lean
open Lean Elab Command Meta

namespace R2
/-- `g n a = a + 2^n` with 2^n nested additions (the arena's shape). -/
def g (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a + 1) (fun _ ih a => ih (ih a)) n
/-- Same, but each level goes through a structure projection. -/
structure Box where
  val : Nat
def gp (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => (Box.mk (a + 1)).val)
    (fun _ ih a => (Box.mk (ih (ih a))).val) n
/-- Same, but each level decides `a < 0` (Decidable / Nat.ble on the deep value). -/
def gi (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a + 1)
    (fun _ ih a => if a < 0 then 0 else ih (ih a)) n
/-- Countdown by Nat.rec on a literal: each step is an iota peel of the literal. -/
def cntR (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) n
/-- Each level is a K-like cast `Eq.rec (motive := fun _ _ => Nat) x (rfl-like proof)`. -/
theorem e0 : (0 : Nat) + 0 = 0 := rfl
def gk (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a + 1)
    (fun _ ih a => @Eq.rec Nat (0 + 0) (fun _ _ => Nat) (ih (ih a)) 0 e0) n
/-- Each level multiplies by 1 and subtracts 0 (Nat.mul / Nat.sub on the spine). -/
def gm (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a * 1 + 1)
    (fun _ ih a => ih (ih a) - 0) n
axiom ax : Nat
end R2

def addRefl (n : Name) (stx : Term) : CommandElabM Unit := liftTermElabM do
  let ty ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let val ← forallTelescope ty fun xs body => do
    let some (α, lhs, _) := body.eq? | throwError "not an Eq"
    let u ← getLevel α
    mkLambdaFVars xs (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  addDecl (.thmDecl { name := n, levelParams := [], type := ty, value := val })

set_option debug.skipKernelTC true
open R2
-- N1 projection at every level of the spine
run_cmd addRefl `R2.gp_ok (← `(gp 16 0 = 65536))
run_cmd addRefl `R2.gp_bad (← `(gp 16 0 = 65537))
-- N2 a Decidable test on the deep value at every level
run_cmd addRefl `R2.gi_ok (← `(gi 15 0 = 32768))
run_cmd addRefl `R2.gi_bad (← `(gi 15 0 = 32769))
-- N3 Nat.rec countdown on a literal (iota peels build the chain)
run_cmd addRefl `R2.cnt_ok (← `(cntR 100000 = 100000))
run_cmd addRefl `R2.cnt_bad (← `(cntR 100000 = 100001))
-- N4 K-like Eq.rec cast at every level
run_cmd addRefl `R2.gk_ok (← `(gk 15 0 = 32768))
run_cmd addRefl `R2.gk_bad (← `(gk 15 0 = 32769))
-- N5 mul/sub on the spine
run_cmd addRefl `R2.gm_ok (← `(gm 15 0 = 32768))
run_cmd addRefl `R2.gm_bad (← `(gm 15 0 = 32769))
-- N6 two deep values compared (lockstep unfolding), off by one
run_cmd addRefl `R2.two_bad (← `(g 16 0 = g 16 1))
run_cmd addRefl `R2.two_ok (← `(g 16 1 = g 16 0 + 1))
-- N7 deep value in a type: Fin bound
run_cmd addRefl `R2.fin_ok (← `((Fin.mk (n := g 15 0 + 1) (g 15 0) (Nat.lt_add_one (g 15 0))).val = 32768))
run_cmd addRefl `R2.fin_bad (← `((Fin.mk (n := g 15 0 + 1) (g 15 0) (Nat.lt_add_one (g 15 0))).val = 32767))
-- N8 deep value beside an axiom inside the chain bottom, compared to itself shifted
run_cmd addRefl `R2.axs_ok (← `(g 15 ax + 0 = g 15 ax))
-- N9 Nat.div / Nat.mod / Nat.gcd on deep values
run_cmd addRefl `R2.div_ok (← `(g 16 0 / 3 + g 16 0 % 3 + Nat.gcd (g 16 0) 6 = 21845 + 1 + 2))
run_cmd addRefl `R2.div_bad (← `(g 16 0 / 3 + g 16 0 % 3 + Nat.gcd (g 16 0) 6 = 21845 + 1 + 3))
-- N10 just past the pending cap: 1200*1024 ≈ 1.23M; g 21 = 2.1M nested (must decline, not crash)
run_cmd addRefl `R2.over_ok (← `(g 21 0 = 2097152))
