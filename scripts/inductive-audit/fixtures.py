"""Fixture specs for the inductive admission audit: tests/fixtures/ind-*.ndjson,
rec-rules-*.ndjson and src/inductive-audit.lean (usage in mk.py)."""
from lib import *
import copy, sys
T = C('T'); L = C('L'); Sx = C('S')
idT = Lam(Type, B(0))
F = {}
def fx(name):
    def d(f):
        F[name] = f; f.__name__ = name.replace('.', '_').replace('-', '_'); return f
    return d

# ---- field universes ----
@fx('ind-field-univ-other-param.reject')
def _(x):   # T.{u,v} : Type u | mk : Type v -> T
    x.inductive(['u','v'], 0, [Ty('T', S(('S','u')), [('T.mk', Pi(S(('S','v')), C('T','u','v')))])])
@fx('ind-field-univ-same-param.reject')
def _(x):   # T.{u} : Type u | mk : Type u -> T
    x.inductive(['u'], 0, [Ty('T', S(('S','u')), [('T.mk', Pi(S(('S','u')), C('T','u')))])])
@fx('ind-field-univ-sort-param.reject')
def _(x):   # T.{u} : Sort u | mk : Type -> T
    x.inductive(['u'], 0, [Ty('T', S('u'), [('T.mk', Pi(Type, C('T','u')))])])
@fx('ind-field-univ-max.accept')
def _(x):   # T.{u,v} : Sort (max u v + 1) | mk : Sort u -> T
    x.inductive(['u','v'], 0, [Ty('T', S(('S',('m','u','v'))), [('T.mk', Pi(S('u'), C('T','u','v')))])])
@fx('ind-field-univ-max-one-param.accept')
def _(x):   # Ax.{v} : Sort v ; T.{u} : Sort (max 1 u) | mk : Ax.{u} -> T
    x.axiom('Ax', ['v'], S('v'))
    x.inductive(['u'], 0, [Ty('T', S(('m',1,'u')), [('T.mk', Pi(C('Ax','u'), C('T','u')))])])
# ---- uniform occurrences ----
@fx('ind-occ-erased-nonuniform.reject')
def _(x):   # T (α : Type) | mk : (fun _ : Type => N) (T N) -> T α
    decl_N(x)
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, Pi(A(Lam(Type, N), A(T, N)), A(T, B(1)))))])])
@fx('ind-occ-erased-uniform.accept')
def _(x):   # T (α : Type) | mk : (fun _ : Type => N) (T α) -> T α
    decl_N(x)
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, Pi(A(Lam(Type, N), A(T, B(0))), A(T, B(1)))))])])
@fx('ind-occ-beta-param.reject')
def _(x):   # T (α : Type) | mk : T ((fun x => x) α) -> T α
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', Pi(Type, Pi(A(T, A(idT, B(0))), A(T, B(1)))))])])
@fx('ind-occ-unit-eta-param.reject')
def _(x):   # U unit ; T (a : U) | mk : (b : U) -> T b -> T a
    decl_U(x)
    x.inductive([], 1, [Ty('T', Pi(C('U'), Type), [('T.mk', Pi(C('U'), Pi(C('U'), Pi(A(T, B(0)), A(T, B(2))))))])])
@fx('ind-occ-nested-wrong-levels.reject')
def _(x):   # Lu.{w} (α : Type w) : Type w ; T.{u,v} | mk : Lu T.{v,u} -> T.{u,v}
    x.inductive(['w'], 1, [Ty('Lu', Pi(S(('S','w')), S(('S','w'))), [('Lu.nil', Pi(S(('S','w')), A(C('Lu','w'), B(0))))])])
    x.inductive(['u','v'], 0, [Ty('T', S(('S',('m','u','v'))), [('T.mk', Pi(A(C('Lu',('m','u','v')), C('T','v','u')), C('T','u','v')))])])
@fx('ind-ctor-type-redex.reject')
def _(x):   # T (α : Type) | mk : (fun (_ : Type 1) => ∀ α : Type, T α) Type
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', A(Lam(S(2), Pi(Type, A(T, B(0)))), Type), 0)])])
# ---- self reference ----
@fx('ind-type-names-sibling.reject')
def _(x):   # A : Type | a ; Bx : A -> Type | b : (x : A) -> Bx x     (one block)
    x.inductive([], 0, [Ty('A', Type, [('A.a', C('A'))]), Ty('Bx', Pi(C('A'), Type), [('Bx.b', Pi(C('A'), A(C('Bx'), B(0))))], nindices=1)])
@fx('ind-mutual-params.accept')
def _(x):
    x.inductive([], 1, [Ty('A', Pi(Type, Type), [('A.a', Pi(Type, Pi(A(C('Bt'), B(0)), A(C('A'), B(1)))))]), Ty('Bt', Pi(Type, Type), [('Bt.b', Pi(Type, A(C('Bt'), B(0)))), ('Bt.c', Pi(Type, Pi(A(C('A'), B(0)), A(C('Bt'), B(1)))))])])
@fx('ind-ctor-names-own-ctor.reject')
def _(x):   # g : (α : Type) -> α -> N ; T | a : T | b : (fun _ : N => N) (g T T.a) -> T
    decl_N(x)
    x.axiom('g', [], Pi(Type, Pi(B(0), N)))
    x.inductive([], 0, [Ty('T', Type, [('T.a', T), ('T.b', Pi(A(Lam(N, N), A(C('g'), T, C('T.a'))), T))])])
# ---- numFields / isRec ----
@fx('ind-ctor-numfields-zero.reject')
def _(x):   # S | mk : B2 -> S exported with numFields = 0 ; allEq : ∀ x y : S, x = y := fun x _ => rfl
    decl_Eq(x); decl_B2(x)
    x.inductive([], 0, [Ty('S', Type, [('S.mk', Pi(B2, Sx), 0)])])
    x.thm('allEq', [], Pi(Sx, Pi(Sx, Eq(Sx, B(1), B(0)))), Lam(Sx, Lam(Sx, Refl(Sx, B(1)))))
@fx('ind-struct-eta.accept')
def _(x):   # the same S, honest ; eta : ∀ x : S, x = S.mk x.1 := fun x => rfl
    decl_Eq(x); decl_B2(x)
    x.inductive([], 0, [Ty('S', Type, [('S.mk', Pi(B2, Sx))])])
    x.thm('eta', [], Pi(Sx, Eq(Sx, B(0), A(C('S.mk'), Proj('S', 0, B(0))))), Lam(Sx, Refl(Sx, B(0))))
@fx('ind-isrec-false-struct-eta.reject')
def _(x):   # T | mk : T -> T exported with isRec = false ; eta : ∀ x : T, x = T.mk x.1 := fun x => rfl
    decl_Eq(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(T, T))])], isRec=False)
    x.thm('eta', [], Pi(T, Eq(T, B(0), A(C('T.mk'), Proj('T', 0, B(0))))), Lam(T, Refl(T, B(0))))
@fx('ind-isrec-true-lie.reject')
def _(x):   # S | mk : B2 -> S exported with isRec = true
    decl_B2(x); x.inductive([], 0, [Ty('S', Type, [('S.mk', Pi(B2, Sx))])], isRec=True)
@fx('ind-isrec-erased-occurrence.accept')
def _(x):   # T | mk : (fun _ : Type => N) (T -> N) -> T : the kernel's isRec is true, by the written occurrence
    decl_N(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(Lam(Type, N), Pi(T, N)), T))])])
# ---- constructor list ----
@fx('ind-dup-ctor-in-list.reject')
def _(x):
    def m(blk, nd): blk['types'][0]['ctors'] = blk['types'][0]['ctors'] * 2
    x.inductive([], 0, [Ty('T', Type, [('T.mk', T)])], mut=m, lean=False)
# ---- recursor rules ----
def b2_iota(x, mut, thm_name, major, rhs):
    decl_Eq(x); decl_B2(x, mut=mut)
    lhs = A(C('B2.rec', 1), Lam(B2, B2), C('B2.t'), C('B2.f'), major)
    x.thm(thm_name, [], Eq(B2, lhs, rhs), Refl(B2, rhs))
@fx('rec-rules.accept')
def _(x): b2_iota(x, None, 'iota', C('B2.t'), C('B2.t'))
@fx('rec-rules-swapped.reject')
def _(x):   # B2.rec rules listed [f, t] ; swapped : B2.rec t f t = f := rfl
    def m(blk, nd): blk['recs'][0]['rules'].reverse()
    b2_iota(x, m, 'swapped', C('B2.t'), C('B2.f'))
@fx('rec-rules-dropped.reject')
def _(x):
    def m(blk, nd): blk['recs'][0]['rules'].pop()
    decl_B2(x, mut=m)
@fx('rec-rules-nfields.reject')
def _(x):
    decl_N(x)
    def m(blk, nd): blk['recs'][0]['rules'][0]['nfields'] = 3
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(N, T))])], mut=m, lean=False)
def mutual_AB(x, mut):
    x.inductive([], 0, [Ty('A', Type, [('A.a', Pi(C('Bt'), C('A')))]), Ty('Bt', Type, [('Bt.b', C('Bt'))])], mut=mut, lean=(mut is None))
@fx('rec-rules-mutual.accept')
def _(x): mutual_AB(x, None)
@fx('rec-rules-mutual-crossed.reject')
def _(x):   # A.rec lists Bt's constructor and Bt.rec lists A's
    def m(blk, nd):
        r = blk['recs']; r[0]['rules'], r[1]['rules'] = r[1]['rules'], r[0]['rules']
    mutual_AB(x, m)
def tree(x, mut):
    decl_L(x)
    x.inductive([], 0, [Ty('Tree', Type, [('Tree.node', Pi(A(L, C('Tree')), C('Tree')))])], mut=mut, numNested=1, lean=(mut is None))
@fx('rec-rules-nested.accept')
def _(x): tree(x, None)
@fx('rec-rules-nested-order.reject')
def _(x):   # Tree.rec_1 (the copied L) lists [cons, nil]
    def m(blk, nd): blk['recs'][1]['rules'].reverse()
    tree(x, m)

# ---- parameters as binders ----
@fx('ind-ctor-type-identity-redex.reject')
def _(x):   # T (α : Type) | mk : (fun (F : Type 1) => F) (∀ α : Type, T α)   -- the occurrence is uniform as written
    x.inductive([], 1, [Ty('T', Pi(Type, Type), [('T.mk', A(Lam(S(2), B(0)), Pi(Type, A(T, B(0)))), 0)])])
@fx('ind-first-sig-identity-redex.reject')
def _(x):   # T : (fun (F : Type 2) => F) (Type -> Type), one parameter
    x.inductive([], 1, [Ty('T', A(Lam(S(3), B(0)), Pi(Type, Type)), [('T.mk', Pi(Type, A(T, B(0))))])])
def sig_via_def(x, def_first):
    x.defn('BSig', [], S(2), Pi(Type, Type))
    a = Ty('A', Pi(Type, Type), [('A.a', Pi(Type, Pi(A(C('Bt'), B(0)), A(C('A'), B(1)))))])
    b = Ty('Bt', C('BSig'), [('Bt.b', Pi(Type, A(C('Bt'), B(0))))])
    x.inductive([], 1, [b, a] if def_first else [a, b])
@fx('ind-first-sig-via-def.reject')
def _(x): sig_via_def(x, True)     # def BSig := Type -> Type ; mutual Bt : BSig, A (α : Type) : Type
@fx('ind-later-sig-via-def.accept')
def _(x): sig_via_def(x, False)    # the same two types with A first
@fx('ind-index-sig-via-def.accept')
def _(x):   # def G := N -> Type ; T (α : Type) : G | mk : T α N.z
    decl_N(x); x.defn('G', [], S(2), Pi(N, Type))
    x.inductive([], 1, [Ty('T', Pi(Type, C('G')), [('T.mk', Pi(Type, A(T, B(0), C('N.z'))))], nindices=1)])
@fx('ind-nested-identity-redex.accept')
def _(x):   # T | mk : (fun x : Type => x) (L T) -> T : nested occurrences are found as written; two motives
    decl_L(x)
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(A(Lam(Type, B(0)), A(L, T)), T))])], numNested=1)

# ---- undeclared constants ----
@fx('ind-field-unknown-const.reject')
def _(x):   # T | mk : nope -> T, where nothing declares `nope`
    x.inductive([], 0, [Ty('T', Type, [('T.mk', Pi(C('nope'), T))])])
@fx('ind-sig-unknown-const.reject')
def _(x):   # T : nope -> Type
    x.inductive([], 0, [Ty('T', Pi(C('nope'), Type), [], nindices=1)])
@fx('def-unknown-const.reject')
def _(x):   # def d : N := nope
    decl_N(x); x.defn('d', [], N, C('nope'))

if __name__ == '__main__':
    outdir = sys.argv[1]
    xs = []
    for name, f in F.items():
        x = X(name); f(x); xs.append(x)
        notes = render_nd(x, '%s/%s.ndjson' % (outdir, name))
    open(outdir + '/src/inductive-audit.lean', 'w').write(render_lean(xs) + '\n')
    print(len(xs), 'fixtures')
