-- Source of the tests/fixtures/ind-nested-aux-*.accept.ndjson fixtures.
-- Each block hands its declarations to the Lean 4.36 kernel with
-- `addDeclCore`; the environment the `#eval`s leave is the module's, so the
-- accepted declarations are exported from the compiled module:
--
--   lean -o NestedAuxTyping.olean nested-aux-typing.lean   (as NestedAuxTyping.lean)
--   LEAN_PATH=.:$TOOLCHAIN/lib/lean leanexport NestedAuxTyping -- Zq<k>.T > <name>.ndjson
--
-- where block k is the k-th fixture below. leanchecker 4.36 accepts each
-- export. The specs are in scripts/inductive-audit/fixtures.py.
import Lean
set_option Elab.async false
open Lean

def tryAdd (label : String) (decl : Declaration) : CoreM Unit := do
  match (← getEnv).addDeclCore 0 2048 decl none with
  | .ok env =>
    setEnv env
    let mut info := ""
    match decl with
    | .inductDecl lps _ types _ =>
      for t in types do
        if let some (.inductInfo iv) := env.find? t.name then
          info := info ++ s!" [{t.name}: isRec={iv.isRec} isReflexive={iv.isReflexive} numNested={iv.numNested} nidx={iv.numIndices}"
          if let some (.recInfo rv) := env.find? (t.name ++ `rec) then
            info := info ++ s!" largeElim={rv.levelParams.length != lps.length} k={rv.k} motives={rv.numMotives} minors={rv.numMinors} rules={rv.rules.map (·.ctor)}"
          info := info ++ "]"
    | _ => pure ()
    IO.println s!"LEAN OK   {label}{info}"
  | .error ex => IO.println s!"LEAN ERR  {label}: {← (ex.toMessageData {}).toString}"

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-proj-unnested.accept#0" (.inductDecl [] 0 [{name := `Zq0.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq0.N.z, type := (.const `Zq0.N [])}, {name := `Zq0.N.s, type := (.forallE `a (.const `Zq0.N []) (.const `Zq0.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-unnested.accept#1" (.inductDecl [] 1 [{name := `Zq0.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq0.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq0.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-unnested.accept#2" (.inductDecl [] 0 [{name := `Zq0.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq0.T.mk, type := (.forallE `a (.app (.const `Zq0.P []) (.const `Zq0.N [])) (.forallE `a (.app (.lam `a (.const `Zq0.N []) (.const `Zq0.N []) .default) (.proj `Zq0.P 0 (.bvar 0))) (.const `Zq0.T []) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-proj-ctor-value.accept#0" (.inductDecl [] 0 [{name := `Zq1.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq1.N.z, type := (.const `Zq1.N [])}, {name := `Zq1.N.s, type := (.forallE `a (.const `Zq1.N []) (.const `Zq1.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-ctor-value.accept#1" (.inductDecl [] 1 [{name := `Zq1.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq1.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq1.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-ctor-value.accept#2" (.inductDecl [] 0 [{name := `Zq1.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq1.T.mk, type := (.forallE `a (.app (.const `Zq1.P []) (.const `Zq1.T [])) (.forallE `a (.forallE `a (.const `Zq1.N []) (.const `Zq1.T []) .default) (.forallE `a (.app (.lam `a (.const `Zq1.T []) (.const `Zq1.N []) .default) (.proj `Zq1.P 0 (.app (.app (.const `Zq1.P.mk []) (.const `Zq1.T [])) (.app (.bvar 0) (.const `Zq1.N.z []))))) (.const `Zq1.T []) .default) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-app-ctor-value.accept#0" (.inductDecl [] 0 [{name := `Zq2.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq2.N.z, type := (.const `Zq2.N [])}, {name := `Zq2.N.s, type := (.forallE `a (.const `Zq2.N []) (.const `Zq2.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-app-ctor-value.accept#1" (.inductDecl [] 1 [{name := `Zq2.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq2.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq2.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-app-ctor-value.accept#2" (.axiomDecl {name := `Zq2.ax, levelParams := [], type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq2.P []) (.bvar 0)) (.const `Zq2.N []) .default) .default), isUnsafe := false})
  tryAdd "ind-nested-aux-app-ctor-value.accept#3" (.inductDecl [] 0 [{name := `Zq2.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq2.T.mk, type := (.forallE `a (.app (.const `Zq2.P []) (.const `Zq2.T [])) (.forallE `a (.forallE `a (.const `Zq2.N []) (.const `Zq2.T []) .default) (.forallE `a (.app (.lam `a (.const `Zq2.N []) (.const `Zq2.N []) .default) (.app (.app (.const `Zq2.ax []) (.const `Zq2.T [])) (.app (.app (.const `Zq2.P.mk []) (.const `Zq2.T [])) (.app (.bvar 0) (.const `Zq2.N.z []))))) (.const `Zq2.T []) .default) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-container-unnested.accept#0" (.inductDecl [] 0 [{name := `Zq3.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq3.N.z, type := (.const `Zq3.N [])}, {name := `Zq3.N.s, type := (.forallE `a (.const `Zq3.N []) (.const `Zq3.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-container-unnested.accept#1" (.inductDecl [] 1 [{name := `Zq3.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq3.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq3.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-container-unnested.accept#2" (.inductDecl [] 1 [{name := `Zq3.Q, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq3.Q.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq3.P []) (.bvar 0)) (.forallE `a (.app (.lam `a (.bvar 1) (.const `Zq3.N []) .default) (.proj `Zq3.P 0 (.bvar 0))) (.app (.const `Zq3.Q []) (.bvar 2)) .default) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-container-unnested.accept#3" (.inductDecl [] 0 [{name := `Zq3.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq3.T.mk, type := (.forallE `a (.app (.const `Zq3.Q []) (.const `Zq3.N [])) (.const `Zq3.T []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-let-var.accept#0" (.inductDecl [] 0 [{name := `Zq4.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq4.N.z, type := (.const `Zq4.N [])}, {name := `Zq4.N.s, type := (.forallE `a (.const `Zq4.N []) (.const `Zq4.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-let-var.accept#1" (.inductDecl [] 1 [{name := `Zq4.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq4.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq4.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-let-var.accept#2" (.inductDecl [] 0 [{name := `Zq4.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq4.T.mk, type := (.forallE `a (.app (.const `Zq4.P []) (.const `Zq4.T [])) (.forallE `a (.letE `a (.app (.const `Zq4.P []) (.const `Zq4.T [])) (.bvar 0) (.const `Zq4.N []) false) (.const `Zq4.T []) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-index-closed.accept#0" (.inductDecl [] 0 [{name := `Zq5.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq5.N.z, type := (.const `Zq5.N [])}, {name := `Zq5.N.s, type := (.forallE `a (.const `Zq5.N []) (.const `Zq5.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-index-closed.accept#1" (.inductDecl [] 1 [{name := `Zq5.W, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.const `Zq5.N []) (.sort (.succ .zero)) .default) .default), ctors := [{name := `Zq5.W.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.app (.const `Zq5.W []) (.bvar 1)) (.const `Zq5.N.z [])) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-index-closed.accept#2" (.inductDecl [] 0 [{name := `Zq5.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq5.T.mk, type := (.forallE `a (.app (.app (.const `Zq5.W []) (.const `Zq5.T [])) (.const `Zq5.N.z [])) (.const `Zq5.T []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-prop-in-prop.accept#0" (.inductDecl [] 1 [{name := `Zq6.PR, type := (.forallE `a (.sort .zero) (.sort .zero) .default), ctors := [{name := `Zq6.PR.mk, type := (.forallE `a (.sort .zero) (.forallE `a (.bvar 0) (.app (.const `Zq6.PR []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-prop-in-prop.accept#1" (.inductDecl [] 0 [{name := `Zq6.T, type := (.sort .zero), ctors := [{name := `Zq6.T.mk, type := (.forallE `a (.app (.const `Zq6.PR []) (.const `Zq6.T [])) (.const `Zq6.T []) .default)}]}] false)
