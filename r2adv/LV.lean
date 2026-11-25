import Lean
open Lean
def tryAdd (label : String) (decl : Declaration) : CoreM Unit := do
  match (← getEnv).addDeclCore 0 2048 decl none with
  | .ok env => setEnv env; IO.println s!"LEAN OK   {label}"
  | .error ex => IO.println s!"LEAN ERR  {label}: {← (ex.toMessageData {}).toString}"
def u : Level := .param `u
def mkT (n : Name) (occ concl : Level) : Declaration :=
  .inductDecl [`u] 0 [{name := n, type := .sort (.succ u), ctors := [
    {name := n ++ `mk, type := .forallE `x (.const n [occ]) (.const n [concl]) .default}]}] false
#eval show CoreM Unit from do
  tryAdd "max0u" (mkT `L1 (.max .zero u) u)
  tryAdd "maxu0" (mkT `L2 (.max u .zero) u)
  tryAdd "imax0u" (mkT `L3 (.imax .zero u) u)
  tryAdd "maxuu_nested" (mkT `L4 (.max (.max u u) u) u)
  tryAdd "concl_max0u" (mkT `L5 u (.max .zero u))
  tryAdd "control" (mkT `L6 u u)
