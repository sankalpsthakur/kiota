-- Sources of tests/fixtures/name-*.ndjson (lean4export of Lean 4.36.0, via the
-- toolchain's `leanexport`). Lean compares names by components: the single
-- component «Nat.add», the components "", "Nat" (printed «».Nat here) and the
-- numeric component a.1 are not Nat.add, Nat or a.«1». Each section was a
-- separate file (NC.lean, NC2.lean).
--
-- * name-quoted-beside-dotted.accept: `c1_both`.
-- * name-quoted-nat-{add,beq}.accept, name-quoted-nat-succ.accept,
--   name-quoted-decide.accept: `cN_true cN_false`. The -false.reject twins (none
--   for succ, whose twin the duplicate check used to hide)
--   append `theorem bad_cN_false : cN_false := <proof of cN_true>` and drop
--   `cN_true` itself, so the bad theorem is the first declaration Lean's
--   kernel refuses.
-- * name-empty-component-nat.accept: `Nat c5_true c5_false`. The
--   -nat-literal.reject twin is the export of `c5_true c5_false` (no Nat) plus
--   `theorem c5_lit : @Eq «».Nat 5 () := <proof of c5_true>`;
--   -nat-literal-beside-nat.reject adds the same theorem to the export with Nat.
--   leanchecker: "unknown constant 'Nat'" and an argument type mismatch.
-- * name-num-beside-digit-string.accept: `c11_both`.
-- * name-empty-component-ite.accept and its -false twin: `c12_true c12_false`.
-- * name-duplicate-index-bool-true.accept: `c13_beq`, given a second index
--   (106) with Bool.true's components, bound right after the original (17);
--   every reference to 17 is moved to 106, so 17 is bound and never declared.
-- * name-index-bound-twice.reject: name-quoted-nat-add.accept with the line
--   `{"in":23,"str":{"pre":0,"str":"other"}}` inserted right after index 23's
--   own line; leanchecker: "Name index 23 bound twice".

-- ===== NC =====
import Lean
open Lean Elab Command Meta

set_option Elab.async false

-- c1: the one component «a.b» and the two components a.b are distinct constants.
def «a.b» : Nat := 1
def a.b : Nat := 2
theorem c1_both : «a.b» + a.b = 3 := rfl

-- c2: a single-component «Nat.add» is not Nat.add; no Nat extension applies.
def «Nat.add» (x _y : Nat) : Nat := x
theorem c2_true : «Nat.add» 2 3 = 2 := rfl
def c2_false : Prop := «Nat.add» 2 3 = 5

-- c3: «Nat.succ» likewise.
def «Nat.succ» (x : Nat) : Nat := x
theorem c3_true : «Nat.succ» 4 = 4 := rfl
def c3_false : Prop := «Nat.succ» 4 = 5

-- c4: «Nat.beq» likewise.
def «Nat.beq» (_x _y : Nat) : Bool := false
theorem c4_true : «Nat.beq» 3 3 = false := rfl
def c4_false : Prop := «Nat.beq» 3 3 = true

-- c13: the native Nat.beq returns the declared Bool.true.
theorem c13_beq : Nat.beq 3 3 = true := rfl

-- ===== NC2 =====
import Lean
open Lean Meta Elab

set_option Elab.async false

def addDef (n : Name) (lps : List Name) (ty v : Expr) (h := ReducibilityHints.abbrev) : MetaM Unit :=
  addDecl (Declaration.defnDecl (mkDefinitionValEx n lps ty v h .safe [n]))
def addThm (n : Name) (ty v : Expr) : MetaM Unit :=
  addDecl (Declaration.thmDecl ⟨⟨n, [], ty⟩, v, [n]⟩)

-- c5: the name with components "", "Nat" is not Nat.
def fakeNat : Name := .str (.str .anonymous "") "Nat"
run_meta addDef fakeNat [] (mkSort Level.one) (mkConst ``Unit)
run_meta do
  let u := mkConst ``Unit.unit
  let ty := mkApp3 (mkConst ``Eq [Level.one]) (mkConst fakeNat) u u
  addDef `c5_false [] (mkSort Level.zero) ty
  addThm `c5_true ty (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst fakeNat) u)

-- c10: a single component «Decidable.decide» is not Decidable.decide.
def «Decidable.decide» (p : Prop) (_h : Decidable p) : Bool := false
theorem c10_true : «Decidable.decide» True inferInstance = false := rfl
def c10_false : Prop := «Decidable.decide» True inferInstance = true

-- c11: the numeric component a.1 and the string component a.«1» are distinct.
def a.«1» : Nat := 10
run_meta addDef (.num `a 1) [] (mkConst ``Nat) (mkNatLit 20)
run_meta do
  let ty := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat)
    (mkApp2 (mkConst ``Nat.add) (mkConst (.str `a "1")) (mkConst (.num `a 1))) (mkNatLit 30)
  addThm `c11_both ty (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) (mkNatLit 30))

-- c12: the name with components "", "ite" is not ite: it always takes the else branch.
def fakeIte : Name := .str (.str .anonymous "") "ite"
run_meta do
  let c ← mkConstWithLevelParams ``ite
  let ty ← inferType c
  let v ← forallTelescope ty fun xs _ => mkLambdaFVars xs xs[4]!
  addDef fakeIte [`u] ty v (.regular 1)
run_meta do
  -- «».ite Nat True instDecidableTrue 1 2 = 2
  let lhs := mkAppN (mkConst fakeIte [Level.one]) #[mkConst ``Nat, mkConst ``True, mkConst ``instDecidableTrue, mkNatLit 1, mkNatLit 2]
  let mk (r : Expr) := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) lhs r
  addThm `c12_true (mk (mkNatLit 2)) (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) lhs)
  addDef `c12_false [] (mkSort Level.zero) (mk (mkNatLit 1))
