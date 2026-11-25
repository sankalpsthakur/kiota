-- `tests/fixtures/abbrev-coe-of-comp.accept.ndjson`, exported with
-- lean4export (Lean 4.33.0) for `coe_coe_comp`. `CoeF.coe` is a class
-- projection, an abbrev. The two sides apply it to `f` and to `f.comp f`,
-- which are not equal; unfolding `CoeF.coe` on both sides meets them at
-- `g 24 (CoeF.coe f q)` against `g 24 (f.toFun q)`. Normalizing `g 24` builds
-- a 2^24-leaf tree of `ite`s. The shape of Mathlib
-- `Polynomial.Bivariate.swap._proof_1`, without the cost of refuting the
-- argument pair that made that declaration spin.
structure Hom where
  toFun : Nat → Nat

class CoeF (F : Type) where
  coe : F → Nat → Nat

instance : CoeF Hom := ⟨Hom.toFun⟩

def Hom.comp (f g : Hom) : Hom := ⟨fun x => f.toFun (g.toFun x)⟩

open Classical in
@[irreducible] noncomputable def g : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => if x = n then g n (x + 1) else g n (x + 2)

noncomputable def f : Hom := ⟨g 24⟩

theorem coe_coe_comp (q : Nat) : CoeF.coe f (CoeF.coe f q) = CoeF.coe (f.comp f) q := rfl
