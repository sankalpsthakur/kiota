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

#eval show CoreM Unit from do
  tryAdd "ind-field-unknown-const.reject#0" (.inductDecl [] 0 [{name := `Zq34.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq34.T.mk, type := (.forallE `a (.const `Zq34.nope []) (.const `Zq34.T []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-sig-unknown-const.reject#0" (.inductDecl [] 0 [{name := `Zq35.T, type := (.forallE `a (.const `Zq35.nope []) (.sort (.succ .zero)) .default), ctors := []}] false)

#eval show CoreM Unit from do
  tryAdd "def-unknown-const.reject#0" (.inductDecl [] 0 [{name := `Zq36.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq36.N.z, type := (.const `Zq36.N [])}, {name := `Zq36.N.s, type := (.forallE `a (.const `Zq36.N []) (.const `Zq36.N []) .default)}]}] false)
  tryAdd "def-unknown-const.reject#1" (.defnDecl {name := `Zq36.d, levelParams := [], type := (.const `Zq36.N []), value := (.const `Zq36.nope []), hints := .abbrev, safety := .safe})

#eval show CoreM Unit from do
  tryAdd "ind-occ-lam-offset-nonuniform.reject#0" (.inductDecl [] 1 [{name := `Zq37.T, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq37.T.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.lam `a (.sort (.succ .zero)) (.app (.const `Zq37.T []) (.bvar 0)) .default) (.bvar 0)) (.app (.const `Zq37.T []) (.bvar 1)) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-occ-let-body-nonuniform.reject#0" (.inductDecl [] 1 [{name := `Zq38.T, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq38.T.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.letE `a (.sort (.succ .zero)) (.bvar 0) (.app (.const `Zq38.T []) (.bvar 0)) false) (.app (.const `Zq38.T []) (.bvar 1)) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-occ-level-max-uu.reject#0" (.inductDecl [`u] 0 [{name := `Zq39.T, type := (.sort (.succ (.param `u))), ctors := [{name := `Zq39.T.mk, type := (.forallE `a (.const `Zq39.T [(.max (.param `u) (.param `u))]) (.const `Zq39.T [(.param `u)]) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-occ-level-imax-uu.reject#0" (.inductDecl [`u] 0 [{name := `Zq40.T, type := (.sort (.succ (.param `u))), ctors := [{name := `Zq40.T.mk, type := (.forallE `a (.const `Zq40.T [(.imax (.param `u) (.param `u))]) (.const `Zq40.T [(.param `u)]) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-result-level-max-uu.reject#0" (.inductDecl [`u] 0 [{name := `Zq41.T, type := (.sort (.succ (.param `u))), ctors := [{name := `Zq41.T.mk, type := (.const `Zq41.T [(.max (.param `u) (.param `u))])}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-occ-level-max-other-const.accept#0" (.axiomDecl {name := `Zq42.Ax, levelParams := [`v], type := (.sort (.succ (.param `v))), isUnsafe := false})
  tryAdd "ind-occ-level-max-other-const.accept#1" (.inductDecl [`u] 0 [{name := `Zq42.T, type := (.sort (.succ (.param `u))), ctors := [{name := `Zq42.T.mk, type := (.forallE `a (.const `Zq42.Ax [(.max (.param `u) (.param `u))]) (.const `Zq42.T [(.param `u)]) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-level-max-uu-after-block.accept#0" (.inductDecl [`u] 0 [{name := `Zq43.T, type := (.sort (.succ (.param `u))), ctors := [{name := `Zq43.T.mk, type := (.forallE `a (.const `Zq43.T [(.param `u)]) (.const `Zq43.T [(.param `u)]) .default)}]}] false)
  tryAdd "ind-level-max-uu-after-block.accept#1" (.defnDecl {name := `Zq43.back, levelParams := [`u], type := (.forallE `a (.const `Zq43.T [(.max (.param `u) (.param `u))]) (.const `Zq43.T [(.param `u)]) .default), value := (.lam `a (.const `Zq43.T [(.max (.param `u) (.param `u))]) (.bvar 0) .default), hints := .abbrev, safety := .safe})

#eval show CoreM Unit from do
  tryAdd "ind-ctor-field-proj-own-type.reject#0" (.inductDecl [] 0 [{name := `Zq44.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq44.N.z, type := (.const `Zq44.N [])}, {name := `Zq44.N.s, type := (.forallE `a (.const `Zq44.N []) (.const `Zq44.N []) .default)}]}] false)
  tryAdd "ind-ctor-field-proj-own-type.reject#1" (.inductDecl [] 2 [{name := `Zq44.Eq', type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default) .default), ctors := [{name := `Zq44.Eq'.refl, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.app (.app (.const `Zq44.Eq' []) (.bvar 1)) (.bvar 0)) (.bvar 0)) .default) .default)}]}] false)
  tryAdd "ind-ctor-field-proj-own-type.reject#2" (.inductDecl [] 0 [{name := `Zq44.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq44.T.mk, type := (.forallE `a (.const `Zq44.N []) (.forallE `a (.const `Zq44.T []) (.forallE `a (.app (.app (.app (.const `Zq44.Eq' []) (.const `Zq44.N [])) (.proj `Zq44.T 0 (.bvar 0))) (.bvar 1)) (.const `Zq44.T []) .default) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-ctor-field-proj-erased.reject#0" (.inductDecl [] 0 [{name := `Zq45.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq45.N.z, type := (.const `Zq45.N [])}, {name := `Zq45.N.s, type := (.forallE `a (.const `Zq45.N []) (.const `Zq45.N []) .default)}]}] false)
  tryAdd "ind-ctor-field-proj-erased.reject#1" (.inductDecl [] 0 [{name := `Zq45.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq45.T.mk, type := (.forallE `a (.const `Zq45.N []) (.forallE `a (.const `Zq45.T []) (.forallE `a (.app (.lam `a (.const `Zq45.N []) (.const `Zq45.N []) .default) (.proj `Zq45.T 0 (.bvar 0))) (.const `Zq45.T []) .default) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-ctor-field-proj-other.accept#0" (.inductDecl [] 0 [{name := `Zq46.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq46.N.z, type := (.const `Zq46.N [])}, {name := `Zq46.N.s, type := (.forallE `a (.const `Zq46.N []) (.const `Zq46.N []) .default)}]}] false)
  tryAdd "ind-ctor-field-proj-other.accept#1" (.inductDecl [] 0 [{name := `Zq46.P, type := (.sort (.succ .zero)), ctors := [{name := `Zq46.P.mk, type := (.forallE `a (.const `Zq46.N []) (.const `Zq46.P []) .default)}]}] false)
  tryAdd "ind-ctor-field-proj-other.accept#2" (.inductDecl [] 0 [{name := `Zq46.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq46.T.mk, type := (.forallE `a (.const `Zq46.P []) (.forallE `a (.app (.lam `a (.const `Zq46.N []) (.const `Zq46.N []) .default) (.proj `Zq46.P 0 (.bvar 0))) (.const `Zq46.T []) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-reserved-nested-prefix.reject#0" (.axiomDecl {name := `Zq47._nested.Foo, levelParams := [], type := (.sort (.succ .zero)), isUnsafe := false})
  tryAdd "ind-reserved-nested-prefix.reject#1" (.inductDecl [] 0 [{name := `Zq47.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq47.T.mk, type := (.forallE `a (.const `Zq47._nested.Foo []) (.const `Zq47.T []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-sig-reserved-nested-prefix.reject#0" (.axiomDecl {name := `Zq48._nested.Foo, levelParams := [], type := (.sort (.succ .zero)), isUnsafe := false})
  tryAdd "ind-sig-reserved-nested-prefix.reject#1" (.inductDecl [] 0 [{name := `Zq48.T, type := (.forallE `a (.const `Zq48._nested.Foo []) (.sort (.succ .zero)) .default), ctors := []}] false)

#eval show CoreM Unit from do
  tryAdd "ind-reserved-nested-prefix-elsewhere.accept#0" (.axiomDecl {name := `Zq49._nested.Foo, levelParams := [], type := (.sort (.succ .zero)), isUnsafe := false})
  tryAdd "ind-reserved-nested-prefix-elsewhere.accept#1" (.axiomDecl {name := `Zq49.g, levelParams := [], type := (.forallE `a (.const `Zq49._nested.Foo []) (.const `Zq49._nested.Foo []) .default), isUnsafe := false})
  tryAdd "ind-reserved-nested-prefix-elsewhere.accept#2" (.axiomDecl {name := `Zq49._nestedFoo, levelParams := [], type := (.sort (.succ .zero)), isUnsafe := false})
  tryAdd "ind-reserved-nested-prefix-elsewhere.accept#3" (.axiomDecl {name := `Zq49.Foo._nested, levelParams := [], type := (.sort (.succ .zero)), isUnsafe := false})
  tryAdd "ind-reserved-nested-prefix-elsewhere.accept#4" (.inductDecl [] 0 [{name := `Zq49.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq49.T.mk, type := (.forallE `a (.const `Zq49._nestedFoo []) (.forallE `a (.const `Zq49.Foo._nested []) (.const `Zq49.T []) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-proj-field.reject#0" (.inductDecl [] 0 [{name := `Zq50.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq50.N.z, type := (.const `Zq50.N [])}, {name := `Zq50.N.s, type := (.forallE `a (.const `Zq50.N []) (.const `Zq50.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-field.reject#1" (.inductDecl [] 1 [{name := `Zq50.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq50.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq50.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-field.reject#2" (.inductDecl [] 0 [{name := `Zq50.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq50.T.mk, type := (.forallE `a (.app (.const `Zq50.P []) (.const `Zq50.T [])) (.forallE `a (.app (.lam `a (.const `Zq50.T []) (.const `Zq50.N []) .default) (.proj `Zq50.P 0 (.bvar 0))) (.const `Zq50.T []) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-app-field.reject#0" (.inductDecl [] 0 [{name := `Zq51.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq51.N.z, type := (.const `Zq51.N [])}, {name := `Zq51.N.s, type := (.forallE `a (.const `Zq51.N []) (.const `Zq51.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-app-field.reject#1" (.inductDecl [] 1 [{name := `Zq51.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq51.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq51.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-app-field.reject#2" (.axiomDecl {name := `Zq51.ax, levelParams := [], type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq51.P []) (.bvar 0)) (.const `Zq51.N []) .default) .default), isUnsafe := false})
  tryAdd "ind-nested-aux-app-field.reject#3" (.inductDecl [] 0 [{name := `Zq51.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq51.T.mk, type := (.forallE `a (.app (.const `Zq51.P []) (.const `Zq51.T [])) (.forallE `a (.app (.lam `a (.const `Zq51.N []) (.const `Zq51.N []) .default) (.app (.app (.const `Zq51.ax []) (.const `Zq51.T [])) (.bvar 0))) (.const `Zq51.T []) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-container-ctor-proj.reject#0" (.inductDecl [] 0 [{name := `Zq52.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq52.N.z, type := (.const `Zq52.N [])}, {name := `Zq52.N.s, type := (.forallE `a (.const `Zq52.N []) (.const `Zq52.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-container-ctor-proj.reject#1" (.inductDecl [] 1 [{name := `Zq52.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq52.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq52.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-container-ctor-proj.reject#2" (.inductDecl [] 1 [{name := `Zq52.Q, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq52.Q.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq52.P []) (.bvar 0)) (.forallE `a (.app (.lam `a (.bvar 1) (.const `Zq52.N []) .default) (.proj `Zq52.P 0 (.bvar 0))) (.app (.const `Zq52.Q []) (.bvar 2)) .default) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-container-ctor-proj.reject#3" (.inductDecl [] 0 [{name := `Zq52.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq52.T.mk, type := (.forallE `a (.app (.const `Zq52.Q []) (.const `Zq52.T [])) (.const `Zq52.T []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-let-proj.reject#0" (.inductDecl [] 0 [{name := `Zq53.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq53.N.z, type := (.const `Zq53.N [])}, {name := `Zq53.N.s, type := (.forallE `a (.const `Zq53.N []) (.const `Zq53.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-let-proj.reject#1" (.inductDecl [] 1 [{name := `Zq53.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq53.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq53.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-let-proj.reject#2" (.inductDecl [] 0 [{name := `Zq53.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq53.T.mk, type := (.forallE `a (.app (.const `Zq53.P []) (.const `Zq53.T [])) (.forallE `a (.letE `a (.app (.const `Zq53.P []) (.const `Zq53.T [])) (.bvar 0) (.app (.lam `a (.const `Zq53.T []) (.const `Zq53.N []) .default) (.proj `Zq53.P 0 (.bvar 0))) false) (.const `Zq53.T []) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-let-value-type.reject#0" (.inductDecl [] 0 [{name := `Zq54.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq54.N.z, type := (.const `Zq54.N [])}, {name := `Zq54.N.s, type := (.forallE `a (.const `Zq54.N []) (.const `Zq54.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-let-value-type.reject#1" (.inductDecl [] 1 [{name := `Zq54.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq54.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq54.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-let-value-type.reject#2" (.inductDecl [] 0 [{name := `Zq54.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq54.T.mk, type := (.forallE `a (.app (.const `Zq54.P []) (.const `Zq54.T [])) (.forallE `a (.forallE `a (.const `Zq54.N []) (.const `Zq54.T []) .default) (.forallE `a (.letE `a (.app (.const `Zq54.P []) (.const `Zq54.T [])) (.app (.app (.const `Zq54.P.mk []) (.const `Zq54.T [])) (.app (.bvar 0) (.const `Zq54.N.z []))) (.const `Zq54.N []) false) (.const `Zq54.T []) .default) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-index-sig.reject#0" (.inductDecl [] 1 [{name := `Zq55.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq55.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq55.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-index-sig.reject#1" (.inductDecl [] 1 [{name := `Zq55.V, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq55.P []) (.bvar 0)) (.sort (.succ .zero)) .default) .default), ctors := [{name := `Zq55.V.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq55.P []) (.bvar 0)) (.app (.app (.const `Zq55.V []) (.bvar 1)) (.bvar 0)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-index-sig.reject#2" (.inductDecl [] 0 [{name := `Zq55.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq55.T.mk, type := (.forallE `a (.app (.const `Zq55.P []) (.const `Zq55.T [])) (.forallE `a (.app (.app (.const `Zq55.V []) (.const `Zq55.T [])) (.bvar 0)) (.const `Zq55.T []) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-proj-reserved-name.reject#0" (.inductDecl [] 0 [{name := `Zq56.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq56.N.z, type := (.const `Zq56.N [])}, {name := `Zq56.N.s, type := (.forallE `a (.const `Zq56.N []) (.const `Zq56.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-reserved-name.reject#1" (.inductDecl [] 1 [{name := `Zq56.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq56.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq56.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-reserved-name.reject#2" (.inductDecl [] 0 [{name := `Zq56.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq56.T.mk, type := (.forallE `a (.app (.const `Zq56.P []) (.const `Zq56.T [])) (.forallE `a (.app (.lam `a (.const `Zq56.T []) (.const `Zq56.N []) .default) (.proj `Zq56._nested.P_1 0 (.bvar 0))) (.const `Zq56.T []) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-proj-unnested.accept#0" (.inductDecl [] 0 [{name := `Zq57.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq57.N.z, type := (.const `Zq57.N [])}, {name := `Zq57.N.s, type := (.forallE `a (.const `Zq57.N []) (.const `Zq57.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-unnested.accept#1" (.inductDecl [] 1 [{name := `Zq57.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq57.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq57.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-unnested.accept#2" (.inductDecl [] 0 [{name := `Zq57.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq57.T.mk, type := (.forallE `a (.app (.const `Zq57.P []) (.const `Zq57.N [])) (.forallE `a (.app (.lam `a (.const `Zq57.N []) (.const `Zq57.N []) .default) (.proj `Zq57.P 0 (.bvar 0))) (.const `Zq57.T []) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-proj-ctor-value.accept#0" (.inductDecl [] 0 [{name := `Zq58.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq58.N.z, type := (.const `Zq58.N [])}, {name := `Zq58.N.s, type := (.forallE `a (.const `Zq58.N []) (.const `Zq58.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-ctor-value.accept#1" (.inductDecl [] 1 [{name := `Zq58.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq58.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq58.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-proj-ctor-value.accept#2" (.inductDecl [] 0 [{name := `Zq58.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq58.T.mk, type := (.forallE `a (.app (.const `Zq58.P []) (.const `Zq58.T [])) (.forallE `a (.forallE `a (.const `Zq58.N []) (.const `Zq58.T []) .default) (.forallE `a (.app (.lam `a (.const `Zq58.T []) (.const `Zq58.N []) .default) (.proj `Zq58.P 0 (.app (.app (.const `Zq58.P.mk []) (.const `Zq58.T [])) (.app (.bvar 0) (.const `Zq58.N.z []))))) (.const `Zq58.T []) .default) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-app-ctor-value.accept#0" (.inductDecl [] 0 [{name := `Zq59.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq59.N.z, type := (.const `Zq59.N [])}, {name := `Zq59.N.s, type := (.forallE `a (.const `Zq59.N []) (.const `Zq59.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-app-ctor-value.accept#1" (.inductDecl [] 1 [{name := `Zq59.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq59.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq59.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-app-ctor-value.accept#2" (.axiomDecl {name := `Zq59.ax, levelParams := [], type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq59.P []) (.bvar 0)) (.const `Zq59.N []) .default) .default), isUnsafe := false})
  tryAdd "ind-nested-aux-app-ctor-value.accept#3" (.inductDecl [] 0 [{name := `Zq59.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq59.T.mk, type := (.forallE `a (.app (.const `Zq59.P []) (.const `Zq59.T [])) (.forallE `a (.forallE `a (.const `Zq59.N []) (.const `Zq59.T []) .default) (.forallE `a (.app (.lam `a (.const `Zq59.N []) (.const `Zq59.N []) .default) (.app (.app (.const `Zq59.ax []) (.const `Zq59.T [])) (.app (.app (.const `Zq59.P.mk []) (.const `Zq59.T [])) (.app (.bvar 0) (.const `Zq59.N.z []))))) (.const `Zq59.T []) .default) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-container-unnested.accept#0" (.inductDecl [] 0 [{name := `Zq60.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq60.N.z, type := (.const `Zq60.N [])}, {name := `Zq60.N.s, type := (.forallE `a (.const `Zq60.N []) (.const `Zq60.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-container-unnested.accept#1" (.inductDecl [] 1 [{name := `Zq60.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq60.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq60.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-container-unnested.accept#2" (.inductDecl [] 1 [{name := `Zq60.Q, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq60.Q.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.app (.const `Zq60.P []) (.bvar 0)) (.forallE `a (.app (.lam `a (.bvar 1) (.const `Zq60.N []) .default) (.proj `Zq60.P 0 (.bvar 0))) (.app (.const `Zq60.Q []) (.bvar 2)) .default) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-container-unnested.accept#3" (.inductDecl [] 0 [{name := `Zq60.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq60.T.mk, type := (.forallE `a (.app (.const `Zq60.Q []) (.const `Zq60.N [])) (.const `Zq60.T []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-let-var.accept#0" (.inductDecl [] 0 [{name := `Zq61.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq61.N.z, type := (.const `Zq61.N [])}, {name := `Zq61.N.s, type := (.forallE `a (.const `Zq61.N []) (.const `Zq61.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-let-var.accept#1" (.inductDecl [] 1 [{name := `Zq61.P, type := (.forallE `a (.sort (.succ .zero)) (.sort (.succ .zero)) .default), ctors := [{name := `Zq61.P.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.const `Zq61.P []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-let-var.accept#2" (.inductDecl [] 0 [{name := `Zq61.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq61.T.mk, type := (.forallE `a (.app (.const `Zq61.P []) (.const `Zq61.T [])) (.forallE `a (.letE `a (.app (.const `Zq61.P []) (.const `Zq61.T [])) (.bvar 0) (.const `Zq61.N []) false) (.const `Zq61.T []) .default) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-index-closed.accept#0" (.inductDecl [] 0 [{name := `Zq62.N, type := (.sort (.succ .zero)), ctors := [{name := `Zq62.N.z, type := (.const `Zq62.N [])}, {name := `Zq62.N.s, type := (.forallE `a (.const `Zq62.N []) (.const `Zq62.N []) .default)}]}] false)
  tryAdd "ind-nested-aux-index-closed.accept#1" (.inductDecl [] 1 [{name := `Zq62.W, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.const `Zq62.N []) (.sort (.succ .zero)) .default) .default), ctors := [{name := `Zq62.W.mk, type := (.forallE `a (.sort (.succ .zero)) (.forallE `a (.bvar 0) (.app (.app (.const `Zq62.W []) (.bvar 1)) (.const `Zq62.N.z [])) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-index-closed.accept#2" (.inductDecl [] 0 [{name := `Zq62.T, type := (.sort (.succ .zero)), ctors := [{name := `Zq62.T.mk, type := (.forallE `a (.app (.app (.const `Zq62.W []) (.const `Zq62.T [])) (.const `Zq62.N.z [])) (.const `Zq62.T []) .default)}]}] false)

#eval show CoreM Unit from do
  tryAdd "ind-nested-aux-prop-in-prop.accept#0" (.inductDecl [] 1 [{name := `Zq63.PR, type := (.forallE `a (.sort .zero) (.sort .zero) .default), ctors := [{name := `Zq63.PR.mk, type := (.forallE `a (.sort .zero) (.forallE `a (.bvar 0) (.app (.const `Zq63.PR []) (.bvar 1)) .default) .default)}]}] false)
  tryAdd "ind-nested-aux-prop-in-prop.accept#1" (.inductDecl [] 0 [{name := `Zq63.T, type := (.sort .zero), ctors := [{name := `Zq63.T.mk, type := (.forallE `a (.app (.const `Zq63.PR []) (.const `Zq63.T [])) (.const `Zq63.T []) .default)}]}] false)

