/-
Source of `conleche-decide-open-uint64-argument.accept.ndjson` (Lean 4.33.0,
lean4export df81913):

  lean -o Dec.olean Dec.lean
  LEAN_PATH=$PWD lean4export Dec -- D.lp_unfold > conleche-decide-open-uint64-argument.accept.ndjson

The comparison inside leanprover/con-leche (rev 78ded4b6)
`ConLeche.lpOfData_pack`, on its own: `lpOfData w` against `w % 2 == 1`, the
body it unfolds to, for the packed word `w = h * 4294967296 + …` of variables.
Both sides become `decide (_ = _)` over the same open `UInt64` terms; Lean's
lazy delta compares the two `decide` applications argument by argument and
never evaluates the instance (which would count `x * 4294967296` down).
-/
namespace D
@[inline] def packData (h b f : UInt64) (lp : Bool) : UInt64 :=
  h * 4294967296 + b * 65536 + f * 2 + (if lp then 1 else 0)
@[inline] def lpOfData (w : UInt64) : Bool := w % 2 == 1

theorem lp_unfold (h b f : UInt64) :
    lpOfData (packData h b f false) = (packData h b f false % 2 == 1) := rfl
end D
