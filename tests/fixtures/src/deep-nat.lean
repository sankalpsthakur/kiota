/-
Sources of the `deep-nat-*` and `deep-list-length*` fixtures (Lean 4.36.0,
`lean -o DeepNat.olean deep-nat.lean`, then
`LEAN_PATH=.:$LEAN/lib/lean leanexport DeepNat -- DeepNat.<case>`):

  sum_ok      deep-nat-sum.accept                 sum_bad   deep-nat-sum-wrong.reject
  box_ok      deep-nat-box-projection.accept      box_bad   deep-nat-box-projection-wrong.reject
  ax_ok       deep-nat-beside-axiom.accept        ax_bad    deep-nat-beside-axiom-wrong.reject
  ble_ok      deep-nat-ble.accept                 sub_bad   deep-nat-sub-wrong.reject
  dec_bad     deep-nat-decide-wrong.reject
  len_ok      deep-list-length.accept             len_bad   deep-list-length-wrong.reject
  len_open_ok deep-list-length-open.accept

`leanchecker --from-export` gives the verdict in each name. The theorems are
added with `skipKernelTC`, so the wrong ones can be exported at all.
-/
import Lean
open Lean Elab Command Meta

namespace DeepNat
/-- `g n a = a + 2^n`: `g (n+1) a = g n (g n a)`, so `g n 0` nests 2^n
additions, each waiting for the value of the next (the arena's `slowA` is
`g 19 0`). -/
def g (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a + 1) (fun _ ih a => ih (ih a)) n
/-- 2^14 = 16384 nested additions: twice the checker's native depth cap. -/
def slow : Nat := g 14 0
structure Box where
  val : Nat
def mkBox (n : Nat) : Box := ⟨g n 0⟩
axiom ax : Nat
end DeepNat

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
open DeepNat
-- the arena's unfold-before-literal-fallback / -bad shapes at 2^14
run_cmd addRefl `DeepNat.sum_ok (← `([slow + 1, 1].sum = slow + (2 + 0)))
run_cmd addRefl `DeepNat.sum_bad (← `([slow, 1].sum = slow + (2 + 0)))
-- a structure projection over the deep value, and an axiom beside it
run_cmd addRefl `DeepNat.box_ok (← `((mkBox 14).val + 0 = 16384))
run_cmd addRefl `DeepNat.box_bad (← `((mkBox 14).val + 0 = 16385))
run_cmd addRefl `DeepNat.ax_ok (← `(g 14 0 + ax = 16384 + ax))
run_cmd addRefl `DeepNat.ax_bad (← `(g 14 0 + ax = 16385 + ax))
-- Nat.sub / Nat.ble / decide over deep values
run_cmd addRefl `DeepNat.sub_bad (← `(g 14 0 - g 13 0 = 8193))
run_cmd addRefl `DeepNat.ble_ok (← `(Nat.ble (g 14 0) 16384 = true))
run_cmd addRefl `DeepNat.dec_bad (← `(decide (g 14 0 = 16383) = true))
-- a long list's length: closed (evaluated) and open (cut at the depth cap)
run_cmd addRefl `DeepNat.len_ok (← `((List.replicate 20000 ()).length + 0 = 20000))
run_cmd addRefl `DeepNat.len_bad (← `((List.replicate 20000 ()).length + 0 = 19999))
run_cmd addRefl `DeepNat.len_open_ok (← `(∀ u : Unit, (List.replicate 20000 u).length + 0 = 20000))
