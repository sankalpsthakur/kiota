import Lean
open Lean Elab Command

/-
A nested inductive whose two nested occurrences differ only by a redex:

    inductive NestedRedex
    | leaf : NestedRedex
    | a : List ((fun _ : Bool => NestedRedex) true) → NestedRedex
    | b : List NestedRedex → NestedRedex

The kernel finds nested occurrences syntactically, so `List ((fun _ => NestedRedex) true)`
and `List NestedRedex` become two auxiliary types and `NestedRedex.rec` has three
motives. The elaborator never writes such a field, so the block is built
programmatically and added with `addDecl`; the official kernel accepts it.
-/

run_cmd liftTermElabM do
  let T := mkConst `NestedRedex
  let list (e : Expr) := mkApp (mkConst ``List [0]) e
  let redex := mkApp (.lam `h (mkConst ``Bool) T .default) (mkConst ``Bool.true)
  addDecl <| .inductDecl [] 0 [{
    name := `NestedRedex, type := mkSort 1, ctors := [
      { name := `NestedRedex.leaf, type := T },
      { name := `NestedRedex.a, type := .forallE `x (list redex) T .default },
      { name := `NestedRedex.b, type := .forallE `x (list T) T .default }] }] false


run_cmd liftTermElabM do
  let T := mkConst `NestedRedex
  let nat := mkConst ``Nat
  let listT := mkApp (mkConst ``List [0]) T
  let lam (n : Name) (ty body : Expr) := Expr.lam n ty body .default
  let add (a b : Expr) := mkApp2 (mkConst ``Nat.add) a b
  let motive (ty : Expr) := lam `t ty nat
  let sum := lam `h T (lam `t listT (lam `i nat (lam `j nat (add (.bvar 1) (.bvar 0)))))
  -- the two auxiliary groups differ in their `nil` minor: 0 for `List (redex)`, 100 for `List NestedRedex`
  let args := #[motive T, motive listT, motive listT,
    mkRawNatLit 0,
    lam `x listT (lam `ih nat (add (.bvar 0) (mkRawNatLit 1))),
    lam `x listT (lam `ih nat (add (.bvar 0) (mkRawNatLit 10))),
    mkRawNatLit 0, sum, mkRawNatLit 100, sum]
  let nil := mkApp (mkConst ``List.nil [0]) T
  let mk (major : Expr) := mkAppN (mkConst `NestedRedex.rec [1]) (args.push major)
  let viaB := mk (mkApp (mkConst `NestedRedex.b) nil)
  let viaA := mk (mkApp (mkConst `NestedRedex.a) nil)
  let eq (l : Expr) (n : Nat) := mkApp3 (mkConst ``Eq [1]) nat l (mkRawNatLit n)
  let refl (l : Expr) := mkApp2 (mkConst ``Eq.refl [1]) nat l
  -- true: b's field is a `List NestedRedex`, eliminated by the third motive's group
  addDecl <| .thmDecl { name := `viaB_true, levelParams := [], type := eq viaB 110, value := refl viaB }
  addDecl <| .thmDecl { name := `viaA_true, levelParams := [], type := eq viaA 1, value := refl viaA }
  -- carriers for the false statements
  addDecl <| .defnDecl { name := `viaB_falseTy, levelParams := [], type := mkSort 0, value := eq viaB 10, hints := .abbrev, safety := .safe }
  addDecl <| .thmDecl { name := `ten, levelParams := [], type := eq (mkRawNatLit 10) 10, value := refl (mkRawNatLit 10) }
  addDecl <| .defnDecl { name := `viaA_falseTy, levelParams := [], type := mkSort 0, value := eq viaA 101, hints := .abbrev, safety := .safe }
  addDecl <| .thmDecl { name := `hundredOne, levelParams := [], type := eq (mkRawNatLit 101) 101, value := refl (mkRawNatLit 101) }
