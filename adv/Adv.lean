import Lean
open Lean Elab Command Meta

namespace Adv
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
end Adv

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
open Adv
-- 1/2: deeper than the arena's 2^19, below the 1.2M cap
run_cmd addRefl `Adv.d20_ok (← `(g 20 0 = 1048576))
run_cmd addRefl `Adv.d20_bad (← `(g 20 0 = 1048577))
-- 3: 2^21 nested additions, above the cap: must decline, not crash
run_cmd addRefl `Adv.d21_ok (← `(g 21 0 = 2097152))
-- 4: Nat.beq on a deep value, wrong claim
run_cmd addRefl `Adv.beq_bad (← `(Nat.beq (g 20 0) 1048577 = true))
-- 5: decide through Nat.decEq, wrong and right
run_cmd addRefl `Adv.dec_bad (← `(decide (g 19 0 = 524287) = true))
run_cmd addRefl `Adv.dec_ok (← `(decide (g 19 0 = 524288) = true))
-- 6: non-Nat data (List) under the raised cap
run_cmd addRefl `Adv.len_ok (← `((List.replicate 1000000 ()).length + 0 = 1000000))
run_cmd addRefl `Adv.len_bad (← `((List.replicate 1000000 ()).length + 0 = 999999))
-- 7: open term: x free, so the raised cap must not apply
run_cmd addRefl `Adv.open_ok (← `(∀ x : Nat, g 19 x + 0 = x + 524288))
run_cmd addRefl `Adv.open_bad (← `(∀ x : Nat, g 19 x + 0 = x + 524289))
-- 8: countdown near and above the cap
run_cmd addRefl `Adv.cnt_near_ok (← `(cnt 1100000 + 0 = 1100000))
run_cmd addRefl `Adv.cnt_over_ok (← `(cnt 3000000 + 0 = 3000000))
run_cmd addRefl `Adv.cnt_near_bad (← `(cnt 1100000 + 0 = 1100001))
-- 9: deep value inside a structure projection, wrong claim
run_cmd addRefl `Adv.box_bad (← `((mkBox 19).val + 0 = 524289))
run_cmd addRefl `Adv.box_ok (← `((mkBox 19).val + 0 = 524288))
-- 10: closed deep arg beside an opaque axiom (Nat.add stuck on ax)
run_cmd addRefl `Adv.ax_ok (← `(g 19 0 + ax = 524288 + ax))
run_cmd addRefl `Adv.ax_bad (← `(g 19 0 + ax = 524289 + ax))
-- 11: Nat.sub / Nat.mul / pow on deep values
run_cmd addRefl `Adv.sub_bad (← `(g 19 0 - g 18 0 = 262145))
run_cmd addRefl `Adv.mul_ok (← `(g 19 0 * 2 = 1048576))
run_cmd addRefl `Adv.ble_bad (← `(Nat.ble (g 19 0) 524287 = true))
