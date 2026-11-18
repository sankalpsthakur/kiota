from mk import *
N = C('N')
def decl_N(x):
    x.inductive([], 0, [Ty('N', Type, [('N.z', N), ('N.s', Pi(N, N))])], isRec=True)
def decl_L(x):  # L (α : Type) : Type
    La = A(C('L'), B(0))
    x.inductive([], 1, [Ty('L', Pi(Type, Type), [('L.nil', Pi(Type, La)), ('L.cons', Pi(Type, Pi(B(0), Pi(A(C('L'), B(1)), A(C('L'), B(2))))))])], isRec=True)
def decl_U(x):  # unit structure
    x.inductive([], 0, [Ty('U', Type, [('U.mk', C('U'))])])
def decl_False(x):
    x.inductive([], 0, [Ty('Fa', Prop, [])])
def decl_Eq(x):  # Eq' (α : Type) (a : α) : α -> Prop | refl : Eq' α a a
    x.inductive([], 2, [Ty("Eq'", Pi(Type, Pi(B(0), Pi(B(1), Prop))), [("Eq'.refl", Pi(Type, Pi(B(0), A(C("Eq'"), B(1), B(0), B(0)))))], nindices=1)])
def Eq(al, a, b): return A(C("Eq'"), al, a, b)
def Refl(al, a): return A(C("Eq'.refl"), al, a)
B2 = C('B2')
def decl_B2(x, mut=None): x.inductive([], 0, [Ty('B2', Type, [('B2.t', B2), ('B2.f', B2)])], mut=mut)
