import Lean
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
  tryAdd "ind-field-univ-other-param.reject#0" (.inductDecl [`u, `v] 0 [{name := `Zq0.T, type := (.sort (.succ (.param `u))), ctors := [{name := `Zq0.T.mk, type := (.forallE `a (.sort (.succ (.param `v))) (.const `Zq0.T [(.param `u), (.param `v)]) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-field-univ-same-param.reject#0" (.inductDecl [`u] 0 [{name := `Zq1.T, type := (.sort (.succ (.param `u))), ctors := [{name := `Zq1.T.mk, type := (.forallE `a (.sort (.succ (.param `u))) (.const `Zq1.T [(.param `u)]) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-field-univ-sort-param.reject#0" (.inductDecl [`u] 0 [{name := `Zq2.T, type := (.sort (.param `u)), ctors := [{name := `Zq2.T.mk, type := (.forallE `a (.sort (.succ .zero)) (.const `Zq2.T [(.param `u)]) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-field-univ-max.accept#0" (.inductDecl [`u, `v] 0 [{name := `Zq3.T, type := (.sort (.succ (.max (.param `u) (.param `v)))), ctors := [{name := `Zq3.T.mk, type := (.forallE `a (.sort (.param `u)) (.const `Zq3.T [(.param `u), (.param `v)]) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-field-univ-max-one-param.accept#0" (.axiomDecl {name := `Zq4.Ax, levelParams := [`v], type := (.sort (.param `v)), isUnsafe := false})
  tryAdd "ind-field-univ-max-one-param.accept#1" (.inductDecl [`u] 0 [{name := `Zq4.T, type := (.sort (.max (.succ .zero) (.param `u))), ctors := [{name := `Zq4.T.mk, type := (.forallE `a (.const `Zq4.Ax [(.param `u)]) (.const `Zq4.T [(.param `u)]) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-occ-erased-nonuniform.reject#0" (.inductDecl [] 0 [{name := `Zq5.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq5.N.z, type := (.const `Zq5.N [])}, {name := `Zq5.N.s, type := (.forallE `a (.const `Zq5.N []) (.const `Zq5.N []) .default)}]}] false)
  tryAdd "ind-occ-erased-nonuniform.reject#1" (.inductDecl [] 1 [{name := `Zq5.T, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq5.T.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.lam `a (.sort (.succ .zero)) (.const `Zq5.N []) .default) (.app (.const `Zq5.T []) (.const `Zq5.N []))) (.app (.const `Zq5.T []) (.bvar 1)) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-occ-erased-uniform.accept#0" (.inductDecl [] 0 [{name := `Zq6.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq6.N.z, type := (.const `Zq6.N [])}, {name := `Zq6.N.s, type := (.forallE `a (.const `Zq6.N []) (.const `Zq6.N []) .default)}]}] false)
  tryAdd "ind-occ-erased-uniform.accept#1" (.inductDecl [] 1 [{name := `Zq6.T, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq6.T.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.lam `a (.sort (.succ .zero)) (.const `Zq6.N []) .default) (.app (.const `Zq6.T []) (.bvar 0))) (.app (.const `Zq6.T []) (.bvar 1)) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-occ-beta-param.reject#0" (.inductDecl [] 1 [{name := `Zq7.T, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq7.T.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq7.T []) (.app (.lam `a (.sort (.succ .zero)) (.bvar 0) .default) (.bvar 0))) (.app (.const `Zq7.T []) (.bvar 1)) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-occ-unit-eta-param.reject#0" (.inductDecl [] 0 [{name := `Zq8.U, type := (.sort (.succ .zero)), ctors := [{name := `Zq8.U.mk, type := (.const `Zq8.U [])}]}] false)
  tryAdd "ind-occ-unit-eta-param.reject#1" (.inductDecl [] 1 [{name := `Zq8.T, type := (.forallE `a (.const `Zq8.U []) (.sort (.succ .zero)) .default), ctors := [{name := `Zq8.T.mk, type := (.forallE `a (.const `Zq8.U []) (.forallE `a (.const `Zq8.U []) (.forallE `a (.app (.const `Zq8.T []) (.bvar 0)) (.app (.const `Zq8.T []) (.bvar 2)) .default) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-occ-nested-wrong-levels.reject#0" (.inductDecl [`w] 1 [{name := `Zq9.Lu, type := (.forallE `a (.sort (.succ (.param `w))) (.sort (.succ (.param `w))) .default), ctors := [{name := `Zq9.Lu.nil, type := (.forallE `a (.sort (.succ (.param `w))) (.app (.const `Zq9.Lu [(.param `w)]) (.bvar 0)) .default)}]}] false)
  tryAdd "ind-occ-nested-wrong-levels.reject#1" (.inductDecl [`u, `v] 0 [{name := `Zq9.T, type := (.sort (.succ (.max (.param `u) (.param `v)))), ctors := [{name := `Zq9.T.mk, type := (.forallE `a (.app (.const `Zq9.Lu [(.max (.param `u) (.param `v))]) (.const `Zq9.T [(.param `v), (.param `u)])) (.const `Zq9.T [(.param `u), (.param `v)]) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-ctor-type-redex.reject#0" (.inductDecl [] 1 [{name := `Zq10.T, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq10.T.mk, type := (.app (.lam `a (.sort (.succ (.succ .zero))) (.forallE `a (.sort (.succ .zero)) (.app (.const `Zq10.T []) (.bvar 0)) .default) .default) (.sort (.succ .zero)))}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-type-names-sibling.reject#0" (.inductDecl [] 0 [{name := `Zq11.A, type := (.sort (.succ .zero)), ctors := [{name := `Zq11.A.a, type := (.const `Zq11.A [])}]}, {name := `Zq11.Bx, type := (.forallE `a (.const `Zq11.A []) (.sort (.succ .zero)) .default), ctors := [{name := `Zq11.Bx.b, type := (.forallE `a (.const `Zq11.A []) (.app (.const `Zq11.Bx []) (.bvar 0)) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-mutual-params.accept#0" (.inductDecl [] 1 [{name := `Zq12.A, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq12.A.a, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq12.Bt []) (.bvar 0)) (.app (.const `Zq12.A []) (.bvar 1)) .default) .default)}]}, {name := `Zq12.Bt, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq12.Bt.b, type := (.forallE `a (.sort (.succ .zero)) (.app (.const `Zq12.Bt []) (.bvar 0)) .default)}, {name := `Zq12.Bt.c, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq12.A []) (.bvar 0)) (.app (.const `Zq12.Bt []) (.bvar 1)) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-ctor-names-own-ctor.reject#0" (.inductDecl [] 0 [{name := `Zq13.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq13.N.z, type := (.const `Zq13.N [])}, {name := `Zq13.N.s, type := (.forallE `a (.const `Zq13.N []) (.const `Zq13.N []) .default)}]}] false)
  tryAdd "ind-ctor-names-own-ctor.reject#1" (.axiomDecl {name := `Zq13.g, levelParams := [], type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.const `Zq13.N []) .default) .default), isUnsafe := false})
  tryAdd "ind-ctor-names-own-ctor.reject#2" (.inductDecl [] 0 [{name := `Zq13.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq13.T.a, type := (.const `Zq13.T [])}, {name := `Zq13.T.b, type := (.forallE `a (.app (.lam `a (.const `Zq13.N []) (.const `Zq13.N []) .default) (.app (.app (.const `Zq13.g []) (.const `Zq13.T [])) (.const `Zq13.T.a []))) (.const `Zq13.T []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-ctor-numfields-zero.reject#0" (.inductDecl [] 2 [{name := `Zq14.Eq', type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default) .default), ctors := [{name := `Zq14.Eq'.refl, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.app (.app (.const `Zq14.Eq' []) (.bvar 1)) (.bvar 0)) (.bvar 0)) .default) .default)}]}] false)
  tryAdd "ind-ctor-numfields-zero.reject#1" (.inductDecl [] 0 [{name := `Zq14.B2, type := (.sort (.succ .zero)), ctors := [{name := `Zq14.B2.t, type := (.const `Zq14.B2 [])}, {name := `Zq14.B2.f, type := (.const `Zq14.B2 [])}]}] false)
  tryAdd "ind-ctor-numfields-zero.reject#2" (.inductDecl [] 0 [{name := `Zq14.S, type := (.sort (.succ .zero)), ctors := [{name := `Zq14.S.mk, type := (.forallE `a (.const `Zq14.B2 []) (.const `Zq14.S []) .default)}]}] false)
  tryAdd "ind-ctor-numfields-zero.reject#3" (.thmDecl {name := `Zq14.allEq, levelParams := [], type := (.forallE `a (.const `Zq14.S []) (.forallE `a (.const `Zq14.S []) (.app (.app (.app (.const `Zq14.Eq' []) (.const `Zq14.S [])) (.bvar 1)) (.bvar 0)) .default) .default), value := (.lam `a (.const `Zq14.S []) (.lam `a (.const `Zq14.S []) (.app (.app (.const `Zq14.Eq'.refl []) (.const `Zq14.S [])) (.bvar 1)) .default) .default)})

#eval show CoreM Unit from do
  tryAdd "ind-struct-eta.accept#0" (.inductDecl [] 2 [{name := `Zq15.Eq', type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default) .default), ctors := [{name := `Zq15.Eq'.refl, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.app (.app (.const `Zq15.Eq' []) (.bvar 1)) (.bvar 0)) (.bvar 0)) .default) .default)}]}] false)
  tryAdd "ind-struct-eta.accept#1" (.inductDecl [] 0 [{name := `Zq15.B2, type := (.sort (.succ .zero)), ctors := [{name := `Zq15.B2.t, type := (.const `Zq15.B2 [])}, {name := `Zq15.B2.f, type := (.const `Zq15.B2 [])}]}] false)
  tryAdd "ind-struct-eta.accept#2" (.inductDecl [] 0 [{name := `Zq15.S, type := (.sort (.succ .zero)), ctors := [{name := `Zq15.S.mk, type := (.forallE `a (.const `Zq15.B2 []) (.const `Zq15.S []) .default)}]}] false)
  tryAdd "ind-struct-eta.accept#3" (.thmDecl {name := `Zq15.eta, levelParams := [], type := (.forallE `a (.const `Zq15.S []) (.app (.app (.app (.const `Zq15.Eq' []) (.const `Zq15.S [])) (.bvar 0)) (.app (.const `Zq15.S.mk []) (.proj `Zq15.S 0 (.bvar 0)))) .default), value := (.lam `a (.const `Zq15.S []) (.app (.app (.const `Zq15.Eq'.refl []) (.const `Zq15.S [])) (.bvar 0)) .default)})

#eval show CoreM Unit from do
  tryAdd "ind-isrec-false-struct-eta.reject#0" (.inductDecl [] 2 [{name := `Zq16.Eq', type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default) .default), ctors := [{name := `Zq16.Eq'.refl, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.app (.app (.const `Zq16.Eq' []) (.bvar 1)) (.bvar 0)) (.bvar 0)) .default) .default)}]}] false)
  tryAdd "ind-isrec-false-struct-eta.reject#1" (.inductDecl [] 0 [{name := `Zq16.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq16.T.mk, type := (.forallE `a (.const `Zq16.T []) (.const `Zq16.T []) .default)}]}] false)
  tryAdd "ind-isrec-false-struct-eta.reject#2" (.thmDecl {name := `Zq16.eta, levelParams := [], type := (.forallE `a (.const `Zq16.T []) (.app (.app (.app (.const `Zq16.Eq' []) (.const `Zq16.T [])) (.bvar 0)) (.app (.const `Zq16.T.mk []) (.proj `Zq16.T 0 (.bvar 0)))) .default), value := (.lam `a (.const `Zq16.T []) (.app (.app (.const `Zq16.Eq'.refl []) (.const `Zq16.T [])) (.bvar 0)) .default)})

#eval show CoreM Unit from do
  tryAdd "ind-isrec-true-lie.reject#0" (.inductDecl [] 0 [{name := `Zq17.B2, type := (.sort (.succ .zero)), ctors := [{name := `Zq17.B2.t, type := (.const `Zq17.B2 [])}, {name := `Zq17.B2.f, type := (.const `Zq17.B2 [])}]}] false)
  tryAdd "ind-isrec-true-lie.reject#1" (.inductDecl [] 0 [{name := `Zq17.S, type := (.sort (.succ .zero)), ctors := [{name := `Zq17.S.mk, type := (.forallE `a (.const `Zq17.B2 []) (.const `Zq17.S []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-isrec-erased-occurrence.accept#0" (.inductDecl [] 0 [{name := `Zq18.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq18.N.z, type := (.const `Zq18.N [])}, {name := `Zq18.N.s, type := (.forallE `a (.const `Zq18.N []) (.const `Zq18.N []) .default)}]}] false)
  tryAdd "ind-isrec-erased-occurrence.accept#1" (.inductDecl [] 0 [{name := `Zq18.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq18.T.mk, type := (.forallE `a (.app (.lam `a (.sort (.succ .zero)) (.const `Zq18.N []) .default) (.forallE `a (.const `Zq18.T []) (.const `Zq18.N []) .default)) (.const `Zq18.T []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "rec-rules.accept#0" (.inductDecl [] 2 [{name := `Zq20.Eq', type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default) .default), ctors := [{name := `Zq20.Eq'.refl, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.app (.app (.const `Zq20.Eq' []) (.bvar 1)) (.bvar 0)) (.bvar 0)) .default) .default)}]}] false)
  tryAdd "rec-rules.accept#1" (.inductDecl [] 0 [{name := `Zq20.B2, type := (.sort (.succ .zero)), ctors := [{name := `Zq20.B2.t, type := (.const `Zq20.B2 [])}, {name := `Zq20.B2.f, type := (.const `Zq20.B2 [])}]}] false)
  tryAdd "rec-rules.accept#2" (.thmDecl {name := `Zq20.iota, levelParams := [], type := (.app (.app (.app (.const `Zq20.Eq' []) (.const `Zq20.B2 [])) (.app (.app (.app (.app (.const `Zq20.B2.rec [(.succ .zero)]) (.lam `a (.const `Zq20.B2 []) (.const `Zq20.B2 []) .default)) (.const `Zq20.B2.t [])) (.const `Zq20.B2.f [])) (.const `Zq20.B2.t []))) (.const `Zq20.B2.t [])), value := (.app (.app (.const `Zq20.Eq'.refl []) (.const `Zq20.B2 [])) (.const `Zq20.B2.t []))})

#eval show CoreM Unit from do
  tryAdd "rec-rules-swapped.reject#0" (.inductDecl [] 2 [{name := `Zq21.Eq', type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default) .default), ctors := [{name := `Zq21.Eq'.refl, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.app (.app (.const `Zq21.Eq' []) (.bvar 1)) (.bvar 0)) (.bvar 0)) .default) .default)}]}] false)
  tryAdd "rec-rules-swapped.reject#1" (.inductDecl [] 0 [{name := `Zq21.B2, type := (.sort (.succ .zero)), ctors := [{name := `Zq21.B2.t, type := (.const `Zq21.B2 [])}, {name := `Zq21.B2.f, type := (.const `Zq21.B2 [])}]}] false)
  tryAdd "rec-rules-swapped.reject#2" (.thmDecl {name := `Zq21.swapped, levelParams := [], type := (.app (.app (.app (.const `Zq21.Eq' []) (.const `Zq21.B2 [])) (.app (.app (.app (.app (.const `Zq21.B2.rec [(.succ .zero)]) (.lam `a (.const `Zq21.B2 []) (.const `Zq21.B2 []) .default)) (.const `Zq21.B2.t [])) (.const `Zq21.B2.f [])) (.const `Zq21.B2.t []))) (.const `Zq21.B2.f [])), value := (.app (.app (.const `Zq21.Eq'.refl []) (.const `Zq21.B2 [])) (.const `Zq21.B2.f []))})

#eval show CoreM Unit from do
  tryAdd "rec-rules-dropped.reject#0" (.inductDecl [] 0 [{name := `Zq22.B2, type := (.sort (.succ .zero)), ctors := [{name := `Zq22.B2.t, type := (.const `Zq22.B2 [])}, {name := `Zq22.B2.f, type := (.const `Zq22.B2 [])}]}] false)

#eval show CoreM Unit from do
  tryAdd "rec-rules-nfields.reject#0" (.inductDecl [] 0 [{name := `Zq23.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq23.N.z, type := (.const `Zq23.N [])}, {name := `Zq23.N.s, type := (.forallE `a (.const `Zq23.N []) (.const `Zq23.N []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "rec-rules-mutual.accept#0" (.inductDecl [] 0 [{name := `Zq24.A, type := (.sort (.succ .zero)), ctors := [{name := `Zq24.A.a, type := (.forallE `a (.const `Zq24.Bt []) (.const `Zq24.A []) .default)}]}, {name := `Zq24.Bt, type := (.sort (.succ .zero)), ctors := [{name := `Zq24.Bt.b, type := (.const `Zq24.Bt [])}]}] false)

#eval show CoreM Unit from do
  tryAdd "rec-rules-nested.accept#0" (.inductDecl [] 1 [{name := `Zq26.L, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq26.L.nil, type := (.forallE `a (.sort (.succ .zero)) (.app (.const `Zq26.L []) (.bvar 0)) .default)}, {name := `Zq26.L.cons, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.forallE `a (.app (.const `Zq26.L []) (.bvar 1)) (.app (.const `Zq26.L []) (.bvar 2)) .default) .default) .default)}]}] false)
  tryAdd "rec-rules-nested.accept#1" (.inductDecl [] 0 [{name := `Zq26.Tree, type := (.sort (.succ .zero)), ctors := [{name := `Zq26.Tree.node, type := (.forallE `a (.app (.const `Zq26.L []) (.const `Zq26.Tree [])) (.const `Zq26.Tree []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "rec-rules-nested-order.reject#0" (.inductDecl [] 1 [{name := `Zq27.L, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq27.L.nil, type := (.forallE `a (.sort (.succ .zero)) (.app (.const `Zq27.L []) (.bvar 0)) .default)}, {name := `Zq27.L.cons, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.forallE `a (.app (.const `Zq27.L []) (.bvar 1)) (.app (.const `Zq27.L []) (.bvar 2)) .default) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-ctor-type-identity-redex.reject#0" (.inductDecl [] 1 [{name := `Zq28.T, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq28.T.mk, type := (.app (.lam `a (.sort (.succ (.succ .zero))) (.bvar 0) .default) (.forallE `a (.sort (.succ .zero)) (.app (.const `Zq28.T []) (.bvar 0)) .default))}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-first-sig-identity-redex.reject#0" (.inductDecl [] 1 [{name := `Zq29.T, type := (.app (.lam `a (.sort (.succ (.succ (.succ .zero)))) (.bvar 0) .default) (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default)), ctors := [{name := `Zq29.T.mk, type := (.forallE `a (.sort (.succ .zero)) (.app (.const `Zq29.T []) (.bvar 0)) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-first-sig-via-def.reject#0" (.defnDecl {name := `Zq30.BSig, levelParams := [], type := (.sort (.succ (.succ .zero))), value := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), hints := .abbrev, safety := .safe})
  tryAdd "ind-first-sig-via-def.reject#1" (.inductDecl [] 1 [{name := `Zq30.Bt, type := (.const `Zq30.BSig []), ctors := [{name := `Zq30.Bt.b, type := (.forallE `a (.sort (.succ .zero)) (.app (.const `Zq30.Bt []) (.bvar 0)) .default)}]}, {name := `Zq30.A, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq30.A.a, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq30.Bt []) (.bvar 0)) (.app (.const `Zq30.A []) (.bvar 1)) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-later-sig-via-def.accept#0" (.defnDecl {name := `Zq31.BSig, levelParams := [], type := (.sort (.succ (.succ .zero))), value := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), hints := .abbrev, safety := .safe})
  tryAdd "ind-later-sig-via-def.accept#1" (.inductDecl [] 1 [{name := `Zq31.A, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq31.A.a, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq31.Bt []) (.bvar 0)) (.app (.const `Zq31.A []) (.bvar 1)) .default) .default)}]}, {name := `Zq31.Bt, type := (.const `Zq31.BSig []), ctors := [{name := `Zq31.Bt.b, type := (.forallE `a (.sort (.succ .zero)) (.app (.const `Zq31.Bt []) (.bvar 0)) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-index-sig-via-def.accept#0" (.inductDecl [] 0 [{name := `Zq32.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq32.N.z, type := (.const `Zq32.N [])}, {name := `Zq32.N.s, type := (.forallE `a (.const `Zq32.N []) (.const `Zq32.N []) .default)}]}] false)
  tryAdd "ind-index-sig-via-def.accept#1" (.defnDecl {name := `Zq32.G, levelParams := [], type := (.sort (.succ (.succ .zero))), value := (.forallE `a (.const `Zq32.N []) (.sort (.succ .zero)) .default), hints := .abbrev, safety := .safe})
  tryAdd "ind-index-sig-via-def.accept#2" (.inductDecl [] 1 [{name := `Zq32.T, type := (.forallE `a (.sort (.succ .zero)) (.const `Zq32.G []) .default), ctors := [{name := `Zq32.T.mk, type := (.forallE `a (.sort (.succ .zero)) (.app (.app (.const `Zq32.T []) (.bvar 0)) (.const `Zq32.N.z [])) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-identity-redex.accept#0" (.inductDecl [] 1 [{name := `Zq33.L, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq33.L.nil, type := (.forallE `a (.sort (.succ .zero)) (.app (.const `Zq33.L []) (.bvar 0)) .default)}, {name := `Zq33.L.cons, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.forallE `a (.app (.const `Zq33.L []) (.bvar 1)) (.app (.const `Zq33.L []) (.bvar 2)) .default) .default) .default)}]}] false)
  tryAdd "ind-nested-identity-redex.accept#1" (.inductDecl [] 0 [{name := `Zq33.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq33.T.mk, type := (.forallE `a (.app (.lam `a (.sort (.succ .zero)) (.bvar 0) .default) (.app (.const `Zq33.L []) (.const `Zq33.T []))) (.const `Zq33.T []) .default)}]}] false)

