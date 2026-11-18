"""Differential probes for inductive admission: each spec is checked by the official kernel (Lean addDecl) and by kiota."""
from lib import *
import copy, sys, os
T = C('T'); L = C('L'); Sx = C('S')
idT = Lam(Type, B(0))

# ---------------- batch b0 ----------------
def sanity_N(x): decl_N(x)
def sanity_L(x): decl_L(x)
def sanity_tree(x):
    decl_L(x)
    x.inductive([], 0, [Ty('Tree', Type, [('Tree.node', Pi(A(C('L'), C('Tree')), C('Tree')))])], isRec=True, numNested=1)
def sanity_neg(x):
    decl_N(x)
    x.inductive([], 0, [Ty('Bad', Type, [('Bad.mk', Pi(Pi(C('Bad'), N), C('Bad')))])])
# ---------------- batch b1 ----------------
# ---------- B: field universes ----------
def B1_field_other_param(x):   # T.{u,v} : Type u | mk : Type v -> T
    x.inductive(['u','v'], 0, [Ty('T', S(('S','u')), [('T.mk', Pi(S(('S','v')), C('T','u','v')))])])
def B2_field_succ(x):          # T.{u} : Type u | mk : Type u -> T
    x.inductive(['u'], 0, [Ty('T', S(('S','u')), [('T.mk', Pi(S(('S','u')), C('T','u')))])])
def B3_field_param_in_closed(x):  # T.{u} : Type | mk : Sort u -> T
    x.inductive(['u'], 0, [Ty('T', Type, [('T.mk', Pi(S('u'), C('T','u')))])])
def B4_ok_max(x):              # T.{u,v} : Sort (max u v + 1) | mk : Sort u -> T   (ok)
    x.inductive(['u','v'], 0, [Ty('T', S(('S',('m','u','v'))), [('T.mk', Pi(S('u'), C('T','u','v')))])])
def B5_field_axiom_sort_v(x):  # Ax.{v} : Sort v ; T.{u,v} : Type u | mk : Ax.{v} -> T
    x.axiom('Ax', ['v'], S('v'))
    x.inductive(['u','v'], 0, [Ty('T', S(('S','u')), [('T.mk', Pi(C('Ax','v'), C('T','u','v')))])])
def B6_field_plus2(x):         # T.{u} : Type u | mk : Type (u+1) -> T
    x.inductive(['u'], 0, [Ty('T', S(('S','u')), [('T.mk', Pi(S(('S',('S','u'))), C('T','u')))])])
def B7_field_max(x):           # T.{u,v} : Type u | mk : Sort (max u v) -> T   (field level max u v + 1 > u+1)
    x.inductive(['u','v'], 0, [Ty('T', S(('S','u')), [('T.mk', Pi(S(('m','u','v')), C('T','u','v')))])])
def B8_prop_any_field(x):      # P.{u} : Prop | mk : Sort u -> P  (ok: Prop)
    x.inductive(['u'], 0, [Ty('T', Prop, [('T.mk', Pi(S('u'), C('T','u')))])])
def B9_sort_u_field_type(x):   # T.{u} : Sort u | mk : Type -> T   (is_geq(u, 2) false, not normalizes to zero -> reject)
    x.inductive(['u'], 0, [Ty('T', S('u'), [('T.mk', Pi(Type, C('T','u')))])])
def B10_imax(x):               # T.{u} : Sort (imax 1 u) | mk : Type -> T  (field 2 vs imax 1 u -> reject)
    x.inductive(['u'], 0, [Ty('T', S(('i',1,'u')), [('T.mk', Pi(Type, C('T','u')))])])
def B11_ok_same(x):            # T.{u} : Sort (max 1 u) | mk : Sort u -> ... field level u+1 > max 1 u -> reject
    x.inductive(['u'], 0, [Ty('T', S(('m',1,'u')), [('T.mk', Pi(S('u'), C('T','u')))])])
def B12_ok_axfield(x):         # T.{u} : Sort (max 1 u) | mk : Ax.{u} -> T   ok
    x.axiom('Ax', ['v'], S('v'))
    x.inductive(['u'], 0, [Ty('T', S(('m',1,'u')), [('T.mk', Pi(C('Ax','u'), C('T','u')))])])
# ---------- C: mutual universes ----------
def C1_mutual_prop_type(x):
    x.inductive([], 0, [Ty('A', Prop, [('A.a', C('A'))]), Ty('Bt', Type, [('Bt.b', Pi(C('A'), C('Bt')))])])
def C2_mutual_type_prop(x):
    x.inductive([], 0, [Ty('Bt', Type, [('Bt.b', Pi(C('A'), C('Bt')))]), Ty('A', Prop, [('A.a', C('A')), ('A.a2', Pi(C('Bt'), C('A')))])])
def C3_mutual_type_type1(x):
    x.inductive([], 0, [Ty('A', Type, [('A.a', C('A'))]), Ty('Bt', S(2), [('Bt.b', Pi(C('A'), C('Bt'))), ('Bt.c', Pi(Type, C('Bt')))])])
# ---------- D: syntactic vs defeq params ----------
def D1_concl_beta_param(x):    # T (α : Type) : Type | mk : T ((fun x => x) α)
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, A(T, A(idT, B(0)))))])])
def D2_rec_beta_param(x):      # T α | mk : T ((fun x => x) α) -> T α
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, Pi(A(T, A(idT, B(0))), A(T, B(1)))))])], isRec=True)
def D3_unit_eta_swap(x):       # U unit ; T (a b : U) : Type | mk : T b a
    decl_U(x)
    x.inductive([], 2, [Ty('T', Pi(C('U'), Pi(C('U'), Type)), [('T.mk', Pi(C('U'), Pi(C('U'), A(T, B(0), B(1)))))])])
def D4_unit_eta_rec(x):        # T (a : U) | mk : (b : U) -> T b -> T a
    decl_U(x)
    x.inductive([], 1, [Ty('T', Pi(C('U'), Type), [('T.mk', Pi(C('U'), Pi(C('U'), Pi(A(T, B(0)), A(T, B(2))))))])], isRec=True)
def D5_rec_wrong_levels(x):    # T.{u} : Type u | mk : T.{u+1}... can't typecheck; use T.{u,v} | mk : T.{v,u} -> T.{u,v}
    x.inductive(['u','v'], 0, [Ty('T', S(('S',('m','u','v'))), [('T.mk', Pi(C('T','v','u'), C('T','u','v')))])], isRec=True)
def D6_nonuniform_param(x):    # T (α : Type) | mk : T N -> T α
    decl_N(x)
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, Pi(A(T, N), A(T, B(1)))))])], isRec=True)
def D7_erased_nonuniform(x):   # T (α : Type) | mk : (fun _ : Type => N) (T N) -> T α
    decl_N(x)
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, Pi(A(Lam(Type, N), A(T, N)), A(T, B(1)))))])])
def D8_erased_uniform(x):      # T (α : Type) | mk : (fun _ : Type => N) (T α) -> T α   (ok in Lean)
    decl_N(x)
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, Pi(A(Lam(Type, N), A(T, B(0))), A(T, B(1)))))])])
def D9_erased_neg(x):          # T | mk : (fun _ : Type => N) (T -> N) -> T   (ok in Lean: occurrence erased by whnf)
    decl_N(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(Lam(Type, N), Pi(T, N)), T))])])
def D10_underapplied(x):       # T (α : Type) | mk : ((fun (f : Type -> Type) => N) T) -> T α   (bare T under-applied)
    decl_N(x)
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, Pi(A(Lam(Pi(Type, Type), N), T), A(T, B(1)))))])])
# ---------- E: nested vs whnf ----------
def E1_nested_via_def(x):      # def Lst α := L α ; Tree | node : Lst Tree -> Tree
    decl_L(x)
    x.defn('Lst', [], Pi(Type, Type), Lam(Type, A(C('L'), B(0))))
    x.inductive([], 0, [Ty('Tree', Type, [('Tree.node', Pi(A(C('Lst'), C('Tree')), C('Tree')))])], isRec=True)
def E2_nested_local_var(x):    # Pr (α β : Type) ; T | mk : (β : Type) -> L (Pr T β) -> T
    decl_L(x)
    x.inductive([], 2, [Ty('Pr', Pi(Type, Pi(Type, Type)), [('Pr.mk', Pi(Type, Pi(Type, Pi(B(1), Pi(B(1), A(C('Pr'), B(3), B(2)))))))])])
    x.inductive([], 0, [Ty('T', S(2), [('T.mk', Pi(Type, Pi(A(C('L'), A(C('Pr'), T, B(0))), T)))])], isRec=True)
def E3_nested_index(x):        # Idx : Type -> Type | mk : Idx N ; T | mk : Idx T -> T
    decl_N(x)
    x.inductive([], 0, [Ty('Idx', Pi(Type, Type), [('Idx.mk', A(C('Idx'), N))], nindices=1)])
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(C('Idx'), T), T))])], isRec=True)
def E4_nested_beta_container(x):  # T | mk : (fun a => L a) T -> T
    decl_L(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(Lam(Type, A(C('L'), B(0))), T), T))])], isRec=True)
def E5_nested_param_beta(x):   # T | mk : L ((fun a => a) T) -> T   (official: nested with param (fun a=>a) T; aux type; ok?)
    decl_L(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(C('L'), A(idT, T)), T))])], isRec=True)
def E6_nested_neg_param(x):    # Neg α | mk : (α -> N) -> Neg α ; T | mk : Neg T -> T
    decl_N(x)
    x.inductive([], 1, [Ty('Neg', Pi(Type, Type), [('Neg.mk', Pi(Type, Pi(Pi(B(0), N), A(C('Neg'), B(1)))))])])
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(C('Neg'), T), T))])], isRec=True)
def E7_nested_in_fn_dom_of_container(x):  # T | mk : L (T -> N) -> T
    decl_N(x); decl_L(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(C('L'), Pi(T, N)), T))])], isRec=True)
def E8_nested_wrong_levels(x): # Lu.{w} (α : Type w) : Type w ; T.{u,v} | mk : Lu (T.{v,u}) -> T.{u,v}
    x.inductive(['w'], 1, [Ty('Lu', Pi(S(('S','w')), S(('S','w'))), [('Lu.nil', Pi(S(('S','w')), A(C('Lu','w'), B(0))))])])
    x.inductive(['u','v'], 0, [Ty('T', S(('S',('m','u','v'))), [('T.mk', Pi(A(C('Lu',('m','u','v')), C('T','v','u')), C('T','u','v')))])], isRec=True)
# ---------------- batch b2 ----------------
# ---------- F: elimination level ----------
def F1_prop_data_field(x):     # P : Prop | mk : N -> P   (propOnly expected)
    decl_N(x); x.inductive([], 0, [Ty('P', Prop, [('P.mk', Pi(N, C('P')))])])
def F2_prop_two_ctors(x):
    x.inductive([], 0, [Ty('P', Prop, [('P.a', C('P')), ('P.b', C('P'))])])
def F3_prop_field_in_index(x): # P : N -> Prop | mk : (n : N) -> P n   (large elim)
    decl_N(x); x.inductive([], 0, [Ty('P', Pi(N, Prop), [('P.mk', Pi(N, A(C('P'), B(0))))], nindices=1)])
def F4_sort_u_two_ctors(x):    # T.{u} : Sort u | a | b   (prop only)
    x.inductive(['u'], 0, [Ty('T', S('u'), [('T.a', C('T','u')), ('T.b', C('T','u'))])])
def F5_sort_max1u(x):          # T.{u} : Sort (max 1 u) | a | b  (large)
    x.inductive(['u'], 0, [Ty('T', S(('m',1,'u')), [('T.a', C('T','u')), ('T.b', C('T','u'))])])
def F6_sort_imax1u(x):         # T.{u} : Sort (imax 1 u) | a | b  (prop only)
    x.inductive(['u'], 0, [Ty('T', S(('i',1,'u')), [('T.a', C('T','u')), ('T.b', C('T','u'))])])
def F7_sort_u_field_sort_u(x): # Ax.{v} : Sort v; T.{u} : Sort u | mk : Ax.{u} -> T  (prop only)
    x.axiom('Ax', ['v'], S('v'))
    x.inductive(['u'], 0, [Ty('T', S('u'), [('T.mk', Pi(C('Ax','u'), C('T','u')))])])
def F8_prop_field_in_index_app(x):  # P : N -> Prop | mk : (n : N) -> P (N.s n)   (field not itself an index arg -> prop only)
    decl_N(x); x.inductive([], 0, [Ty('P', Pi(N, Prop), [('P.mk', Pi(N, A(C('P'), A(C('N.s'), B(0)))))], nindices=1)])
def F9_prop_nested(x):         # P : Prop | mk : L P -> P   hmm L P needs P : Type; skip -> use mutual Prop
    x.inductive([], 0, [Ty('P', Prop, [('P.a', C('P'))]), Ty('Q', Prop, [('Q.b', Pi(C('P'), C('Q')))])])
def F10_prop_field_imax_zero(x): # P.{u} : Prop | mk : (Ax.{imax u 0}) -> P : field level imax u 0 == 0 -> large elim?? Lean: normalizes_to_zero?
    x.axiom('Ax', ['v'], S('v'))
    x.inductive(['u'], 0, [Ty('P', Prop, [('P.mk', Pi(C('Ax',('i','u',0)), C('P','u')))])])
def F11_sort_imax_u_zero(x):   # T.{u} : Sort (imax u 0) | mk : N -> T    (result level semantically 0)
    decl_N(x); x.inductive(['u'], 0, [Ty('T', S(('i','u',0)), [('T.mk', Pi(N, C('T','u')))])])
def F12_prop_param_dep_field(x): # P (n : N) : Prop | mk : (m : N) -> P n  (prop only)
    decl_N(x); x.inductive([], 1, [Ty('P', Pi(N, Prop), [('P.mk', Pi(N, Pi(N, A(C('P'), B(1)))))])])
def F13_prop_let_field(x): # P : N -> Prop | mk : (n : N) -> let m := n; P m   -- conclusion under let
    decl_N(x); x.inductive([], 0, [Ty('P', Pi(N, Prop), [('P.mk', Pi(N, Let(N, B(0), A(C('P'), B(0)))))], nindices=1)])
# ---------- H: well-typedness / self reference ----------
def H1_illtyped_index(x):      # Idx : N -> Type | mk : Idx Prop
    decl_N(x); x.inductive([], 0, [Ty('Idx', Pi(N, Type), [('Idx.mk', A(C('Idx'), Prop))], nindices=1)])
def H2_param_not_type(x):      # T (a : N.z) : Type
    decl_N(x); x.inductive([], 1, [Ty('T', Pi(C('N.z'), Type), [('T.mk', Pi(C('N.z'), A(T, B(0))))])])
def H3_field_not_type(x):      # T | mk : N.z -> T
    decl_N(x); x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(C('N.z'), T))])])
def H4_type_mentions_self(x):  # T : (T -> Type)?? ill: T : Pi (x : T), Type
    x.inductive([], 0, [Ty('T', Pi(T, Type), [], nindices=1)])
def H5_ctor_mentions_ctor(x):  # Eq-free: Q : T -> Prop axiom can't precede. Use: T | mk : (f : T -> T) ... skip; ctor type mentions own ctor via index family
    decl_N(x)
    # W : N -> Type ; T : Type | mk : W N.z -> T   fine.  Self-ref: T | a : T | b : Fam a -> T  where Fam : T -> Type can't precede T.
    # Mutual trick: A : Type | a : A ; Bx : A -> Type | b : Bx A.a      (index mentions ctor of sibling type in same block)
    x.inductive([], 0, [Ty('A', Type, [('A.a', C('A'))]), Ty('Bx', Pi(C('A'), Type), [('Bx.b', A(C('Bx'), C('A.a')))], nindices=1)])
def H6_type_mentions_sibling(x): # A : Type ; Bx : A -> Type  (index type mentions sibling type)  -- official rejects: unknown constant
    x.inductive([], 0, [Ty('A', Type, [('A.a', C('A'))]), Ty('Bx', Pi(C('A'), Type), [('Bx.b', Pi(C('A'), A(C('Bx'), B(0))))], nindices=1)])
def H7_ctor_type_redex(x):     # T (α : Type) | mk : (fun (_ : Type) => ∀ α : Type, T α) Type    (ctor type not syntactically a Pi)
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', A(Lam(S(2), Pi(Type, A(T, B(0)))), Type), 0)])])
def H8_ctor_field_redex(x):    # T | mk : (fun (_ : Type) => N -> T) Type   (fields hidden behind a redex), numFields claims 1
    decl_N(x); x.inductive([], 0, [Ty('T', Type, [('T.mk', A(Lam(S(2), Pi(N, T)), Type), 1)])])
def H9_type_via_def(x):        # def F := N -> Type ; inductive T : F | mk : T N.z   (type whnf's to Pi; official counts 1 index)
    decl_N(x); x.defn('F', [], S(2), Pi(N, Type))
    x.inductive([], 0, [Ty('T', C('F'), [('T.mk', A(T, C('N.z')))], nindices=1)])
def H10_result_not_sort(x):    # T : N
    decl_N(x); x.inductive([], 0, [Ty('T', N, [])])
def H11_numindices_lie(x):     # T : N -> Type declared with numIndices 0, numParams 0 ; mk : T N.z
    decl_N(x); x.inductive([], 0, [Ty('T', Pi(N, Type), [('T.mk', A(T, C('N.z')))], nindices=0)], lean=False)
def H12_nparams_too_many(x):   # T : Type -> Type with nparams 2
    x.inductive([], 2, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, A(T, B(0))), 0)])])
def H13_ctor_extra_univ(x):    # ctor conclusion T.{u} applied... T.{u} : Type u | mk : T.{max u u}
    x.inductive(['u'], 0, [Ty('T', S(('S','u')), [('T.mk', C('T',('m','u',('S',0))))])])
def H14_index_field_dep(x):    # ok twin: Vec : N -> Type | cons : (n : N) -> Vec n -> Vec (N.s n)
    decl_N(x); x.inductive([], 0, [Ty('V', Pi(N, Type), [('V.nil', A(C('V'), C('N.z'))), ('V.cons', Pi(N, Pi(A(C('V'), B(0)), A(C('V'), A(C('N.s'), B(1))))))], nindices=1)], isRec=True)
def H15_reflexive_index(x):    # T : N -> Type | mk : (N -> T N.z) -> T N.z   ok reflexive
    decl_N(x); x.inductive([], 0, [Ty('T', Pi(N, Type), [('T.mk', Pi(Pi(N, A(T, C('N.z'))), A(T, C('N.z'))))], nindices=1)], isRec=True, isReflexive=True)
def H16_refl_occ_in_index_of_rec(x):  # Ix : Type -> Type ax-like inductive; T : Type -> Type | mk : T (T N) -> T N  hmm index contains T
    decl_N(x); x.inductive([], 0, [Ty('T', Pi(Type, Type), [('T.mk', Pi(A(T, A(T, N)), A(T, N)))], nindices=1)], isRec=True)
def H17_ctor_ret_sibling(x):   # A | a : Bt ; Bt | b : Bt
    x.inductive([], 0, [Ty('A', Type, [('A.a', C('Bt'))]), Ty('Bt', Type, [('Bt.b', C('Bt'))])])
def H18_param_mentions_T(x):   # T (a : T) hmm: T : (a : N) -> Type, ctor param domain mentions T?  mk : (a : N) -> T a ok.  Instead: param type differs between type and ctor
    decl_N(x); x.inductive([], 1, [Ty('T', Pi(N, Type), [('T.mk', Pi(Type, A(T, C('N.z'))))])])
# ---------------- batch b3 ----------------
def setk(path_fn):
    return path_fn
# ---------- G: flags ----------
def G1_isRec_false_lie(x):     # T | mk : T -> T, exported isRec=false
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(T, T))])], isRec=False)
def G2_isRec_true_lie(x):      # S | mk : B2 -> S, exported isRec=true
    decl_B2(x); x.inductive([], 0, [Ty('S', Type, [('S.mk', Pi(B2, C('S')))])], isRec=True)
def G3_isRec_erased(x):        # T | mk : (fun _ : Type => N) (T -> N) -> T  -- official isRec=true (syntactic), export false
    decl_N(x); x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(Lam(Type, N), Pi(T, N)), T))])], isRec=False)
def G4_numNested_lie(x):
    decl_N(x); x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(N, T))])], numNested=3)
def G5_isReflexive_lie(x):
    decl_N(x); x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(N, T))])], isReflexive=True)
def G6_nested_isRec_false(x):  # Tree | node : L Tree -> Tree with isRec false
    decl_L(x); x.inductive([], 0, [Ty('Tree', Type, [('Tree.node', Pi(A(C('L'), C('Tree')), C('Tree')))])], isRec=False, numNested=1)
def G7_mutual_isRec(x):        # A | a : Bt -> A ; Bt | b : Bt   official: rec = true for both (one flag for the block)
    x.inductive([], 0, [Ty('A', Type, [('A.a', Pi(C('Bt'), C('A')))]), Ty('Bt', Type, [('Bt.b', C('Bt'))])], isRec=True)
# ---------- K: ctor list / numFields / cidx lies ----------
def K1_numFields_zero_lie(x):  # S | mk : B2 -> S, ctor numFields=0
    decl_B2(x); x.inductive([], 0, [Ty('S', Type, [('S.mk', Pi(B2, C('S')), 0)])], lean=False)
def K2_numFields_big_lie(x):
    decl_B2(x); x.inductive([], 0, [Ty('S', Type, [('S.mk', Pi(B2, C('S')), 5)])], lean=False)
def K3_dup_ctor_in_list(x):    # T.ctors = [mk, mk]
    def m(blk, nd):
        blk['types'][0]['ctors'] = blk['types'][0]['ctors'] * 2
    x.inductive([], 0, [Ty('T', Type, [('T.mk', T)])], mut=m, lean=False)
def K4_ctor_missing_from_list(x):  # two ctor objects, type lists only one
    def m(blk, nd):
        blk['types'][0]['ctors'] = blk['types'][0]['ctors'][:1]
    x.inductive([], 0, [Ty('T', Type, [('T.a', T), ('T.b', T)])], mut=m, lean=False)
def K5_ctor_numParams_lie(x):
    def m(blk, nd): blk['ctors'][0]['numParams'] = 0
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, A(T, B(0))))])], mut=m, lean=False)
def K6_all_lie_extra(x):       # T.all = [T, N]
    decl_N(x)
    def m(blk, nd): blk['types'][0]['all'] = blk['types'][0]['all'] + [nd.name('N')]
    x.inductive([], 0, [Ty('T', Type, [('T.mk', T)])], mut=m, lean=False)
def K7_all_lie_missing(x):     # mutual A,B but A.all=[A]
    def m(blk, nd): blk['types'][0]['all'] = blk['types'][0]['all'][:1]
    x.inductive([], 0, [Ty('A', Type, [('A.a', Pi(C('Bt'), C('A')))]), Ty('Bt', Type, [('Bt.b', C('Bt'))])], mut=m, lean=False, isRec=True)
def K8_ctor_listed_from_other_type(x):  # T.ctors = [T.mk, B2.t]
    decl_B2(x)
    def m(blk, nd): blk['types'][0]['ctors'].append(nd.name('B2.t'))
    x.inductive([], 0, [Ty('T', Type, [('T.mk', T)])], mut=m, lean=False)
def K9_ctor_cross_claim(x):    # mutual: A.a declared with induct=Bt
    def m(blk, nd):
        blk['ctors'][0]['induct'] = blk['types'][1]['name']
    x.inductive([], 0, [Ty('A', Type, [('A.a', C('A'))]), Ty('Bt', Type, [('Bt.b', C('Bt'))])], mut=m, lean=False)
def K10_ctor_name_foreign(x):  # ctor named N2.zero belongs to T (name prefix mismatch) - official allows any ctor name? addDecl allows
    x.inductive([], 0, [Ty('T', Type, [('Other.mk', T)])])
def K11_rec_levelparam_clash(x):  # T.{uElim} : Type ... rec fresh name must differ; our generator names elim 'uElim' -> duplicates
    x.inductive(['uElim'], 0, [Ty('T', S(('S','uElim')), [('T.mk', C('T','uElim'))])], lean=False)
# ---------- J: recursor rules ----------
def J0_two_ctor_ok(x): decl_B2(x)
def mk_rules_mut(f):
    def m(blk, nd):
        f(blk['recs'], nd)
    return m
def J1_rules_swapped(x):
    x.inductive([], 0, [Ty('B2', Type, [('B2.t', B2), ('B2.f', B2)])], mut=mk_rules_mut(lambda recs, nd: recs[0]['rules'].reverse()), lean=False)
def J2_rules_dropped(x):
    x.inductive([], 0, [Ty('B2', Type, [('B2.t', B2), ('B2.f', B2)])], mut=mk_rules_mut(lambda recs, nd: recs[0]['rules'].pop()), lean=False)
def J3_rules_dup(x):
    x.inductive([], 0, [Ty('B2', Type, [('B2.t', B2), ('B2.f', B2)])], mut=mk_rules_mut(lambda recs, nd: recs[0]['rules'].append(copy.deepcopy(recs[0]['rules'][0]))), lean=False)
def J4_rules_cross_mutual(x):
    def f(recs, nd):
        recs[0]['rules'], recs[1]['rules'] = recs[1]['rules'], recs[0]['rules']
    x.inductive([], 0, [Ty('A', Type, [('A.a', Pi(C('Bt'), C('A')))]), Ty('Bt', Type, [('Bt.b', C('Bt'))])], mut=mk_rules_mut(f), lean=False, isRec=True)
def J5_rules_nfields_lie(x):
    decl_N(x)
    def f(recs, nd): recs[0]['rules'][0]['nfields'] = 3
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(N, T))])], mut=mk_rules_mut(f), lean=False)
def J6_rules_empty(x):
    x.inductive([], 0, [Ty('B2', Type, [('B2.t', B2), ('B2.f', B2)])], mut=mk_rules_mut(lambda recs, nd: recs[0]['rules'].clear()), lean=False)
def J7_rules_foreign_ctor(x):  # T.rec rules name B2's constructors
    decl_B2(x)
    def f(recs, nd):
        recs[0]['rules'][0]['ctor'] = nd.name('B2.t')
    x.inductive([], 0, [Ty('T', Type, [('T.mk', T)])], mut=mk_rules_mut(f), lean=False)
def J8_k_lie(x):
    def f(recs, nd): recs[0]['k'] = True
    x.inductive([], 0, [Ty('B2', Type, [('B2.t', B2), ('B2.f', B2)])], mut=mk_rules_mut(f), lean=False)
def J9_rules_nested_swap(x):   # Tree.rec / Tree.rec_1 rule lists swapped
    decl_L(x)
    def f(recs, nd):
        recs[0]['rules'], recs[1]['rules'] = recs[1]['rules'], recs[0]['rules']
    x.inductive([], 0, [Ty('Tree', Type, [('Tree.node', Pi(A(C('L'), C('Tree')), C('Tree')))])], mut=mk_rules_mut(f), isRec=True, numNested=1, lean=False)
def J10_rules_nested_order(x):  # Tree.rec_1 rules [cons, nil]
    decl_L(x)
    def f(recs, nd): recs[1]['rules'].reverse()
    x.inductive([], 0, [Ty('Tree', Type, [('Tree.node', Pi(A(C('L'), C('Tree')), C('Tree')))])], mut=mk_rules_mut(f), isRec=True, numNested=1, lean=False)
# ---------------- batch b4 ----------------
def X1_numFields_zero_unit_eta(x):
    decl_Eq(x); decl_B2(x)
    x.inductive([], 0, [Ty('S', Type, [('S.mk', Pi(B2, Sx), 0)])])
    x.thm('allEq', [], Pi(Sx, Pi(Sx, Eq(Sx, B(1), B(0)))), Lam(Sx, Lam(Sx, Refl(Sx, B(1)))))
def X2_isRec_false_struct_eta(x):
    decl_Eq(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(T, T))])], isRec=False)
    x.thm('eta', [], Pi(T, Eq(T, B(0), A(C('T.mk'), Proj('T', 0, B(0))))), Lam(T, Refl(T, B(0))))
def X3_rules_swapped_iota(x):
    decl_Eq(x)
    def m(blk, nd): blk['recs'][0]['rules'].reverse()
    decl_B2(x, mut=m)
    lhs = A(C('B2.rec', 1), Lam(B2, B2), C('B2.t'), C('B2.f'), C('B2.t'))
    x.thm('swapped', [], Eq(B2, lhs, C('B2.f')), Refl(B2, C('B2.f')))
def X4_rules_dropped_iota(x):   # rules = [t] only; rec .. f ?
    decl_Eq(x)
    def m(blk, nd): blk['recs'][0]['rules'].pop(0)
    decl_B2(x, mut=m)
    lhs = A(C('B2.rec', 1), Lam(B2, B2), C('B2.t'), C('B2.f'), C('B2.f'))
    x.thm('dropped', [], Eq(B2, lhs, C('B2.t')), Refl(B2, C('B2.t')))
def X5_honest_iota(x):
    decl_Eq(x); decl_B2(x)
    lhs = A(C('B2.rec', 1), Lam(B2, B2), C('B2.t'), C('B2.f'), C('B2.t'))
    x.thm('honest', [], Eq(B2, lhs, C('B2.t')), Refl(B2, C('B2.t')))
def X6_numFields_big_proj(x):   # S | mk : B2 -> S with numFields=2 ; proj idx 1
    decl_Eq(x); decl_B2(x)
    x.inductive([], 0, [Ty('S', Type, [('S.mk', Pi(B2, Sx), 2)])])
    x.defn('p1', [], Pi(Sx, B2), Lam(Sx, Proj('S', 1, B(0))))
def X7_isRec_true_blocks_eta(x):  # honest struct but isRec=true: eta theorem should hold in Lean
    decl_Eq(x); decl_B2(x)
    x.inductive([], 0, [Ty('S', Type, [('S.mk', Pi(B2, Sx))])], isRec=True)
    x.thm('eta', [], Pi(Sx, Eq(Sx, B(0), A(C('S.mk'), Proj('S', 0, B(0))))), Lam(Sx, Refl(Sx, B(0))))
# ---------------- batch b5 ----------------
def E2b_nested_local_var(x):   # Pn (α : Type) (n : N) : Type ; T | mk : (n : N) -> L (Pn T n) -> T
    decl_N(x); decl_L(x)
    x.inductive([], 2, [Ty('Pn', Pi(Type, Pi(N, Type)), [('Pn.mk', Pi(Type, Pi(N, A(C('Pn'), B(1), B(0)))))])])
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(N, Pi(A(L, A(C('Pn'), T, B(0))), T)))])])
def E9_nested_under_redex(x):  # T | mk : (fun _ : Type => N) (L T) -> T
    decl_N(x); decl_L(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(Lam(Type, N), A(L, T)), T))])])
def E10_nested_redex_two(x):
    decl_N(x); decl_L(x)
    x.inductive([], 0, [Ty('T', Type, [('T.leaf', T), ('T.a', Pi(A(L, A(Lam(N, T), C('N.z'))), T)), ('T.b', Pi(A(L, T), T))])])
def E12_nested_two_containers(x):  # Pr (α β : Type) ; T | mk : Pr T (L T) -> T
    decl_L(x)
    x.inductive([], 2, [Ty('Pr', Pi(Type, Pi(Type, Type)), [('Pr.mk', Pi(Type, Pi(Type, Pi(B(1), Pi(B(1), A(C('Pr'), B(3), B(2)))))))])])
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(C('Pr'), T, A(L, T)), T))])])
def E15_nested_prop(x):        # And' (a b : Prop) : Prop | intro : a -> b -> And' a b ; P : Prop | base : P | mk : And' P P -> P
    x.inductive([], 2, [Ty("And'", Pi(Prop, Pi(Prop, Prop)), [("And'.intro", Pi(Prop, Pi(Prop, Pi(B(1), Pi(B(1), A(C("And'"), B(3), B(2)))))))])])
    x.inductive([], 0, [Ty('P', Prop, [('P.base', C('P')), ('P.mk', Pi(A(C("And'"), C('P'), C('P')), C('P')))])])
def E15b_nested_prop_single(x):  # P : Prop | mk : And' P P -> P   (single ctor; nested makes aux group -> prop only)
    x.inductive([], 2, [Ty("And'", Pi(Prop, Pi(Prop, Prop)), [("And'.intro", Pi(Prop, Pi(Prop, Pi(B(1), Pi(B(1), A(C("And'"), B(3), B(2)))))))])])
    x.inductive([], 0, [Ty('P', Prop, [('P.mk', Pi(A(C("And'"), C('P'), C('P')), C('P')))])])
def E16_nested_univ(x):        # Lu.{w} (α : Sort w) : Sort (max 1 w) | nil | cons ; T.{u} : Type u | mk : Lu.{u+1} T -> T
    Lu = lambda w, a: A(C('Lu', w), a)
    x.inductive(['w'], 1, [Ty('Lu', Pi(S('w'), S(('m',1,'w'))), [('Lu.nil', Pi(S('w'), Lu('w', B(0)))), ('Lu.cons', Pi(S('w'), Pi(B(0), Pi(Lu('w', B(1)), Lu('w', B(2))))))])])
    x.inductive(['u'], 0, [Ty('T', S(('S','u')), [('T.mk', Pi(Lu(('S','u'), C('T','u')), C('T','u')))])])
def E17_nested_container_index_occ(x):  # Vx (α : Type) : Type -> Type | mk : Vx α α ; T | mk : Vx N T -> T  (T in index of container, param N has no occ)
    decl_N(x)
    x.inductive([], 1, [Ty('Vx', Pi(Type, Pi(Type, Type)), [('Vx.mk', Pi(Type, A(C('Vx'), B(0), B(0))))], nindices=1)])
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(C('Vx'), N, T), T))])])
def E18_nested_container_index_occ2(x):  # T | mk : Vx T T -> T   (nested param T and index T)
    decl_N(x)
    x.inductive([], 1, [Ty('Vx', Pi(Type, Pi(Type, Type)), [('Vx.mk', Pi(Type, A(C('Vx'), B(0), B(0))))], nindices=1)])
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(C('Vx'), T, T), T))])])
def E19_nested_mutual_container(x):  # mutual Ev/Od containers with param ; T | mk : Ev T -> T
    Ev = lambda a: A(C('Ev'), a); Od = lambda a: A(C('Od'), a)
    x.inductive([], 1, [Ty('Ev', Pi(Type, Type), [('Ev.nil', Pi(Type, Ev(B(0)))), ('Ev.cons', Pi(Type, Pi(B(0), Pi(Od(B(1)), Ev(B(2))))))]),
                        Ty('Od', Pi(Type, Type), [('Od.cons', Pi(Type, Pi(B(0), Pi(Ev(B(1)), Od(B(2))))))])])
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(Ev(T), T))])])
def E20_nested_refl(x):        # T | mk : (N -> L T) -> T
    decl_N(x); decl_L(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(Pi(N, A(L, T)), T))])])
def E21_nested_param_T_applied(x):  # T (α : Type) | mk : L (T α) -> T α
    decl_L(x)
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, Pi(A(L, A(T, B(0))), A(T, B(1)))))])])
def E22_nested_param_T_nonuniform(x):  # T (α : Type) | mk : L (T N) -> T α     (official 4.34 rejects)
    decl_N(x); decl_L(x)
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, Pi(A(L, A(T, N)), A(T, B(1)))))])])
# ---- K-like ----
def rec_app(name, lv, motive, minors, major_args):
    return A(C(name + '.rec', lv), motive, *minors, *major_args)
def KL1_prop_unit_K(x):
    decl_Eq(x); decl_B2(x)
    x.inductive([], 0, [Ty('P', Prop, [('P.mk', C('P'))])])
    x.thm('k', [], Pi(C('P'), Eq(B2, A(C('P.rec', 1), Lam(C('P'), B2), C('B2.t'), B(0)), C('B2.t'))), Lam(C('P'), Refl(B2, C('B2.t'))))
def KL2_sort_u_not_K(x):
    decl_Eq(x); decl_B2(x)
    x.inductive(['u'], 0, [Ty('P', S('u'), [('P.mk', C('P','u'))])])
    x.thm('k', ['u'], Pi(C('P','u'), Eq(B2, A(C('P.rec', 1, 'u'), Lam(C('P','u'), B2), C('B2.t'), B(0)), C('B2.t'))), Lam(C('P','u'), Refl(B2, C('B2.t'))))
def KL4_index_K(x):            # Ix : N -> Prop | mk : Ix N.z ; ∀ h : Ix N.z, rec t N.z h = t  (ok) ; ∀ n (h : Ix n), rec t n h = t (bad)
    decl_Eq(x); decl_B2(x); decl_N(x)
    Ix = lambda n: A(C('Ix'), n)
    x.inductive([], 0, [Ty('Ix', Pi(N, Prop), [('Ix.mk', Ix(C('N.z')))], nindices=1)])
    mot = Lam(N, Lam(Ix(B(0)), B2))
    x.thm('kOk', [], Pi(Ix(C('N.z')), Eq(B2, A(C('Ix.rec', 1), mot, C('B2.t'), C('N.z'), B(0)), C('B2.t'))), Lam(Ix(C('N.z')), Refl(B2, C('B2.t'))))
def KL4b_index_K_bad(x):
    decl_Eq(x); decl_B2(x); decl_N(x)
    Ix = lambda n: A(C('Ix'), n)
    x.inductive([], 0, [Ty('Ix', Pi(N, Prop), [('Ix.mk', Ix(C('N.z')))], nindices=1)])
    mot = Lam(N, Lam(Ix(B(0)), B2))
    x.thm('kBad', [], Pi(N, Pi(Ix(B(0)), Eq(B2, A(C('Ix.rec', 1), mot, C('B2.t'), B(1), B(0)), C('B2.t')))), Lam(N, Lam(Ix(B(0)), Refl(B2, C('B2.t')))))
def KL5_proof_field_not_K(x):  # Tr : Prop | i ; Pf : Prop | mk : Tr -> Pf ; ∀ h : Pf, rec (fun _ => t) h = t  (not K: Lean rejects)
    decl_Eq(x); decl_B2(x)
    x.inductive([], 0, [Ty('Tr', Prop, [('Tr.i', C('Tr'))])])
    x.inductive([], 0, [Ty('Pf', Prop, [('Pf.mk', Pi(C('Tr'), C('Pf')))])])
    x.thm('k', [], Pi(C('Pf'), Eq(B2, A(C('Pf.rec', 1), Lam(C('Pf'), B2), Lam(C('Tr'), C('B2.t')), B(0)), C('B2.t'))), Lam(C('Pf'), Refl(B2, C('B2.t'))))
def KL6_param_K(x):            # Eq'-style K with param: Pq (n : N) : Prop | mk : Pq n
    decl_Eq(x); decl_B2(x); decl_N(x)
    Pq = lambda n: A(C('Pq'), n)
    x.inductive([], 1, [Ty('Pq', Pi(N, Prop), [('Pq.mk', Pi(N, Pq(B(0))))])])
    x.thm('k', [], Pi(N, Pi(Pq(B(0)), Eq(B2, A(C('Pq.rec', 1), B(1), Lam(Pq(B(1)), B2), C('B2.t'), B(0)), C('B2.t')))), Lam(N, Lam(Pq(B(0)), Refl(B2, C('B2.t')))))
def KL7_two_ctor_prop_not_K(x):
    decl_Eq(x); decl_B2(x)
    x.inductive([], 0, [Ty('P', Prop, [('P.a', C('P')), ('P.b', C('P'))])])
    x.thm('k', [], Pi(C('P'), Eq(C('P'), A(C('P.rec'), Lam(C('P'), C('P')), C('P.a'), C('P.a'), B(0)), C('P.a'))), Lam(C('P'), Refl(C('P'), C('P.a'))))
# ---------------- batch b6 ----------------
def H19_ctor_mentions_own_ctor_erased(x):  # g : (α : Type) -> α -> N ; T | a : T | b : (fun _ : N => N) (g T T.a) -> T
    decl_N(x)
    x.axiom('g', [], Pi(Type, Pi(B(0), N)))
    x.inductive([], 0, [Ty('T', Type, [('T.a', T), ('T.b', Pi(A(Lam(N, N), A(C('g'), T, C('T.a'))), T))])])
def H20_ctor_mentions_rec(x):   # field type mentions T.rec (erased)
    decl_N(x)
    x.axiom('g', ['v'], Pi(S('v'), N))
    x.inductive([], 0, [Ty('T', Type, [('T.a', T), ('T.b', Pi(A(Lam(N, N), A(C('g', 3), Pi(Pi(T, Type), Type))), T))])])
def L1_field_loose_bvar(x):
    decl_N(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(B(3), T))])])
def L2_type_loose_bvar(x):
    x.inductive([], 0, [Ty('T', Pi(B(2), Type), [], nindices=1)])
def L3_levelparam_dup(x):
    x.inductive(['u','u'], 0, [Ty('T', S(('S','u')), [('T.mk', C('T','u','u'))])])
def M1_mutual_param_mismatch(x):  # A (α : Type) ; Bt (n : N)
    decl_N(x)
    x.inductive([], 1, [Ty('A', Pi(Type, Type), [('A.a', Pi(Type, A(C('A'), B(0))))]), Ty('Bt', Pi(N, Type), [('Bt.b', Pi(N, A(C('Bt'), B(0))))])])
def M2_mutual_ok(x):
    decl_N(x)
    x.inductive([], 1, [Ty('A', Pi(Type, Type), [('A.a', Pi(Type, Pi(A(C('Bt'), B(0)), A(C('A'), B(1)))))]), Ty('Bt', Pi(Type, Type), [('Bt.b', Pi(Type, A(C('Bt'), B(0)))), ('Bt.c', Pi(Type, Pi(A(C('A'), B(0)), A(C('Bt'), B(1)))))])])
def M3_mutual_cross_param_swap(x):  # A (α β) ; ctor of A mentions Bt β α
    x.inductive([], 2, [Ty('A', Pi(Type, Pi(Type, Type)), [('A.a', Pi(Type, Pi(Type, Pi(A(C('Bt'), B(0), B(1)), A(C('A'), B(2), B(1))))))]),
                        Ty('Bt', Pi(Type, Pi(Type, Type)), [('Bt.b', Pi(Type, Pi(Type, A(C('Bt'), B(1), B(0)))))])])
# ---------------- batch b7 ----------------
def P1_mutual_second_sig_via_def(x):   # def BSig := Type -> Type ; mutual A (α : Type) : Type, B : BSig  (nparams = 1)
    x.defn('BSig', [], S(2), Pi(Type, Type))
    x.inductive([], 1, [Ty('A', Pi(Type, Type), [('A.a', Pi(Type, Pi(A(C('Bt'), B(0)), A(C('A'), B(1)))))]),
                        Ty('Bt', C('BSig'), [('Bt.b', Pi(Type, A(C('Bt'), B(0))))])])
def P1b_first_sig_via_def(x):          # the same with the def-typed member first
    x.defn('BSig', [], S(2), Pi(Type, Type))
    x.inductive([], 1, [Ty('Bt', C('BSig'), [('Bt.b', Pi(Type, A(C('Bt'), B(0))))]),
                        Ty('A', Pi(Type, Type), [('A.a', Pi(Type, Pi(A(C('Bt'), B(0)), A(C('A'), B(1)))))])])
def P2_ctor_type_identity_redex(x):    # T (α : Type) | mk : (fun (F : Type 1) => F) (∀ α : Type, T α)
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', A(Lam(S(2), B(0)), Pi(Type, A(T, B(0)))), 0)])])
def P3_first_sig_identity_redex(x):    # T : (fun (F : Type 2) => F) (Type -> Type), nparams = 1
    x.inductive([], 1, [Ty('T', A(Lam(S(3), B(0)), Pi(Type, Type)), [('T.mk', Pi(Type, A(T, B(0))))])])
def P4_index_sig_via_def(x):           # def F := N -> Type ; T : F (nparams 0, one index) | mk : T N.z
    decl_N(x); x.defn('F', [], S(2), Pi(N, Type))
    x.inductive([], 0, [Ty('T', C('F'), [('T.mk', A(T, C('N.z')))], nindices=1)])
def P5_param_then_index_via_def(x):    # def G := N -> Type ; T (α : Type) : G | mk : T α N.z    (index binder behind a def, after a manifest parameter)
    decl_N(x); x.defn('G', [], S(2), Pi(N, Type))
    x.inductive([], 1, [Ty('T', Pi(Type, C('G')), [('T.mk', Pi(Type, A(T, B(0), C('N.z'))))], nindices=1)])
def H20b_ctor_names_rec(x):            # h : N -> N ; T | a : T | b : (fun _ : N => N) (h T.rec) -> T   (cannot be well typed)
    decl_N(x); x.axiom('h', [], Pi(N, N))
    x.inductive([], 0, [Ty('T', Type, [('T.a', T), ('T.b', Pi(A(Lam(N, N), A(C('h'), C('T.rec', 1))), T))])])
def E23_nested_identity_redex(x):      # T | mk : (fun x : Type => x) (L T) -> T
    decl_L(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(Lam(Type, B(0)), A(C('L'), T)), T))])])
# ---------------- batch b8 ----------------
def U1_def_unknown_const(x):
    decl_N(x); x.defn('d', [], N, C('nope'))
def U2_ind_field_unknown_const(x):
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(C('nope'), T))])])
def U3_ind_sig_unknown_const(x):
    x.inductive([], 0, [Ty('T', Pi(C('nope'), Type), [], nindices=1)])
def U4_axiom_unknown_const(x):
    x.axiom('ax', [], C('nope'))

ALL = [sanity_N, sanity_L, sanity_tree, sanity_neg, B1_field_other_param, B2_field_succ, B3_field_param_in_closed, B4_ok_max, B5_field_axiom_sort_v, B6_field_plus2, B7_field_max, B8_prop_any_field, B9_sort_u_field_type, B10_imax, B11_ok_same, B12_ok_axfield, C1_mutual_prop_type, C2_mutual_type_prop, C3_mutual_type_type1, D1_concl_beta_param, D2_rec_beta_param, D3_unit_eta_swap, D4_unit_eta_rec, D5_rec_wrong_levels, D6_nonuniform_param, D7_erased_nonuniform, D8_erased_uniform, D9_erased_neg, D10_underapplied, E1_nested_via_def, E2_nested_local_var, E3_nested_index, E4_nested_beta_container, E5_nested_param_beta, E6_nested_neg_param, E7_nested_in_fn_dom_of_container, E8_nested_wrong_levels, F1_prop_data_field, F2_prop_two_ctors, F3_prop_field_in_index, F4_sort_u_two_ctors, F5_sort_max1u, F6_sort_imax1u, F7_sort_u_field_sort_u, F8_prop_field_in_index_app, F9_prop_nested, F10_prop_field_imax_zero, F11_sort_imax_u_zero, F12_prop_param_dep_field, F13_prop_let_field, H1_illtyped_index, H2_param_not_type, H3_field_not_type, H4_type_mentions_self, H5_ctor_mentions_ctor, H6_type_mentions_sibling, H7_ctor_type_redex, H8_ctor_field_redex, H9_type_via_def, H10_result_not_sort, H11_numindices_lie, H12_nparams_too_many, H13_ctor_extra_univ, H14_index_field_dep, H15_reflexive_index, H16_refl_occ_in_index_of_rec, H17_ctor_ret_sibling, H18_param_mentions_T, G1_isRec_false_lie, G2_isRec_true_lie, G3_isRec_erased, G4_numNested_lie, G5_isReflexive_lie, G6_nested_isRec_false, G7_mutual_isRec, K1_numFields_zero_lie, K2_numFields_big_lie, K3_dup_ctor_in_list, K4_ctor_missing_from_list, K5_ctor_numParams_lie, K6_all_lie_extra, K7_all_lie_missing, K8_ctor_listed_from_other_type, K9_ctor_cross_claim, K10_ctor_name_foreign, K11_rec_levelparam_clash, J0_two_ctor_ok, J1_rules_swapped, J2_rules_dropped, J3_rules_dup, J4_rules_cross_mutual, J5_rules_nfields_lie, J6_rules_empty, J7_rules_foreign_ctor, J8_k_lie, J9_rules_nested_swap, J10_rules_nested_order, X1_numFields_zero_unit_eta, X2_isRec_false_struct_eta, X3_rules_swapped_iota, X4_rules_dropped_iota, X5_honest_iota, X6_numFields_big_proj, X7_isRec_true_blocks_eta, E2b_nested_local_var, E9_nested_under_redex, E10_nested_redex_two, E12_nested_two_containers, E15_nested_prop, E15b_nested_prop_single, E16_nested_univ, E17_nested_container_index_occ, E18_nested_container_index_occ2, E19_nested_mutual_container, E20_nested_refl, E21_nested_param_T_applied, E22_nested_param_T_nonuniform, KL1_prop_unit_K, KL2_sort_u_not_K, KL4_index_K, KL4b_index_K_bad, KL5_proof_field_not_K, KL6_param_K, KL7_two_ctor_prop_not_K, H19_ctor_mentions_own_ctor_erased, H20_ctor_mentions_rec, L1_field_loose_bvar, L2_type_loose_bvar, L3_levelparam_dup, M1_mutual_param_mismatch, M2_mutual_ok, M3_mutual_cross_param_swap, P1_mutual_second_sig_via_def, P1b_first_sig_via_def, P2_ctor_type_identity_redex, P3_first_sig_identity_redex, P4_index_sig_via_def, P5_param_then_index_via_def, H20b_ctor_names_rec, E23_nested_identity_redex, U1_def_unknown_const, U2_ind_field_unknown_const, U3_ind_sig_unknown_const, U4_axiom_unknown_const]

if __name__ == '__main__':
    only = sys.argv[2:] 
    run([f for f in ALL if not only or any(f.__name__.startswith(p) for p in only)], sys.argv[1])
