import Lean
open Lean Elab Command

run_cmd liftTermElabM do
  let T := mkConst `NR
  let list (e : Expr) := mkApp (mkConst ``List [0]) e
  let redex := mkApp (.lam `h (mkConst ``Bool) T .default) (mkConst ``Bool.true)
  addDecl <| .inductDecl [] 0 [{
    name := `NR, type := mkSort 1, ctors := [
      { name := `NR.leaf, type := T },
      { name := `NR.a, type := .forallE `x (list redex) T .default },
      { name := `NR.b, type := .forallE `x (list T) T .default }] }] false

run_cmd liftTermElabM do
  let T := mkConst `NR
  let nat := mkConst ``Nat
  let listT := mkApp (mkConst ``List [0]) T
  let redex := mkApp (.lam `h (mkConst ``Bool) T .default) (mkConst ``Bool.true)
  let listR := mkApp (mkConst ``List [0]) redex
  let lam (n : Name) (ty body : Expr) := Expr.lam n ty body .default
  let add (a b : Expr) := mkApp2 (mkConst ``Nat.add) a b
  let motive (ty : Expr) := lam `t ty nat
  let sum := lam `h T (lam `t listT (lam `i nat (lam `j nat (add (.bvar 1) (.bvar 0)))))
  let args := #[motive T, motive listT, motive listT,
    mkRawNatLit 0,
    lam `x listT (lam `ih nat (add (.bvar 0) (mkRawNatLit 1))),
    lam `x listT (lam `ih nat (add (.bvar 0) (mkRawNatLit 10))),
    mkRawNatLit 0, sum, mkRawNatLit 100, sum]
  let leaf := mkConst `NR.leaf
  -- a's field written at `List NR` instead of `List ((fun _ => NR) true)`
  let consT := mkApp3 (mkConst ``List.cons [0]) T leaf (mkApp (mkConst ``List.nil [0]) T)
  -- b's field written at the redex
  let consR := mkApp3 (mkConst ``List.cons [0]) redex leaf (mkApp (mkConst ``List.nil [0]) redex)
  let mk (major : Expr) := mkAppN (mkConst `NR.rec [1]) (args.push major)
  let mk1 (major : Expr) := mkAppN (mkConst `NR.rec_1 [1]) (args.push major)
  let mk2 (major : Expr) := mkAppN (mkConst `NR.rec_2 [1]) (args.push major)
  let eq (l : Expr) (n : Nat) := mkApp3 (mkConst ``Eq [1]) nat l (mkRawNatLit n)
  let refl (l : Expr) := mkApp2 (mkConst ``Eq.refl [1]) nat l
  let defn (n : Name) (ty v : Expr) := addDecl <| .defnDecl { name := n, levelParams := [], type := ty, value := v, hints := .abbrev, safety := .safe }
  let thm (n : Name) (ty v : Expr) := addDecl <| .thmDecl { name := n, levelParams := [], type := ty, value := v }
  -- 1. NR.a with its field at List NR
  let x1 := mk (mkApp (mkConst `NR.a) consT)
  thm `x1_true (eq x1 1) (refl x1)
  defn `x1_false101 (mkSort 0) (eq x1 101)
  -- 2. NR.b with its field at List redex
  let x2 := mk (mkApp (mkConst `NR.b) consR)
  thm `x2_true (eq x2 110) (refl x2)
  defn `x2_false10 (mkSort 0) (eq x2 10)
  -- 3. rec_1 directly at a List NR major
  let x3 := mk1 consT
  thm `x3_true (eq x3 0) (refl x3)
  defn `x3_false100 (mkSort 0) (eq x3 100)
  -- 4. rec_2 directly at a List redex major
  let x4 := mk2 consR
  thm `x4_true (eq x4 100) (refl x4)
  defn `x4_false0 (mkSort 0) (eq x4 0)
  -- the canonical writings, as controls
  let x5 := mk1 (mkApp3 (mkConst ``List.cons [0]) redex leaf (mkApp (mkConst ``List.nil [0]) redex))
  thm `x5_true (eq x5 0) (refl x5)
  let x6 := mk2 (mkApp3 (mkConst ``List.cons [0]) T leaf (mkApp (mkConst ``List.nil [0]) T))
  thm `x6_true (eq x6 100) (refl x6)
