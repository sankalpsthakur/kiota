/-
Source of `conleche-ite-open-hash-condition.accept.ndjson` (Lean 4.33.0,
lean4export df81913):

  lean -o Repro.olean Repro.lean
  LEAN_PATH=$PWD lean4export Repro -- R.wscopedBP.eq_1 > conleche-ite-open-hash-condition.accept.ndjson

A cut-down copy of leanprover/con-leche (rev 78ded4b6) `ConLeche.Expr.wscopedBP`:
an inductive whose computed field packs a hash and two ranges into one
`UInt64`, and a structural recursion guarded by a read of that word.
`R.wscopedBP.eq_1 : wscopedBP (.bvar i) d = if ((E.bvar i).fvarB == 0) = true then true else true`
is `fun d i => Eq.refl _`: both sides are `ite c inst true _` over the same
condition, and the condition cannot be evaluated (`mixHash` is opaque, `i`
is a variable; `x * 4294967296` on an open `x` counts the literal down).
-/
namespace R
def satRange : Nat := 32767
@[inline] def packData (h b f : UInt64) (lp : Bool) : UInt64 :=
  h * 4294967296 + b * 65536 + f * 2 + (if lp then 1 else 0)
@[inline] def hashOfData (w : UInt64) : UInt64 := w / 4294967296
@[inline] def fvarOfData (w : UInt64) : UInt64 := w / 2 % 32768
@[inline] def hash32 (w : UInt64) : UInt64 := w % 4294967296
@[inline] def satSucc (n : Nat) : UInt64 := UInt64.ofNat (min (n + 1) satRange)

inductive E where
  | bvar (i : Nat)
  | fvar (idx : Nat) (ty : E)
  | app (f a : E)
with
  @[computed_field] data : E → UInt64
   | .bvar i => packData (hash32 (mixHash 3 (Hashable.hash i))) (satSucc i) 0 false
   | .fvar idx ty => packData (hash32 (mixHash 5 (mixHash (Hashable.hash idx) (hashOfData ty.data)))) 0 (satSucc idx) false
   | .app f a => packData (hash32 (mixHash 17 (mixHash (hashOfData f.data) (hashOfData a.data)))) 0 (max (fvarOfData f.data) (fvarOfData a.data)) false

def E.fvarBRaw (e : E) : Nat := (fvarOfData e.data).toNat
def fvarRange : E → Nat
  | .bvar _ => 0
  | .fvar idx _ => idx + 1
  | .app f a => max (fvarRange f) (fvarRange a)
@[inline] def E.fvarB (e : E) : Nat :=
  let r := e.fvarBRaw
  if r == satRange then fvarRange e else r

def wscopedBP (e : E) (d : Nat) : Bool :=
  if e.fvarB == 0 then true else
  match e with
  | .bvar .. => true
  | .fvar idx ty .. => idx < d && wscopedBP ty idx
  | .app f a => wscopedBP f d && wscopedBP a d

-- Naming the equation lemma in a declaration keeps it in the `.olean`.
theorem t1 : ∀ (d i : Nat), wscopedBP (E.bvar i) d =
    if ((E.bvar i).fvarB == 0) = true then true else true := @wscopedBP.eq_1
end R
