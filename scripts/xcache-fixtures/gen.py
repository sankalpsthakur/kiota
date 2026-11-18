"""Writes the hand-built exports that pin the cross-declaration cache holes.

    python3 scripts/xcache-fixtures/gen.py tests/fixtures

Each fixture is named for what it must do with and without KIOTA_XCACHE /
KIOTA_XMEMO; tests/xcache_parity.rs runs them under all four settings.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lk import Export


def nat_axioms(x):
    """axiom Nat : Type, P : Nat -> Prop, p5 : P 5."""
    type1 = x.sort(x.lsucc(0))
    nat = x.axiom("Nat", type1)
    P = x.axiom("P", x.pi(x.const(nat), x.sort(0), "n"))
    p5 = x.axiom("p5", x.app(x.const(P), x.nat(5)))
    return nat, P, p5


def name_respelled_into_nat_succ():
    """An axiom F : Nat -> Nat whose name index is respelled `Nat.succ`.

    `P (F 4)` is not `P 5`. Respelled, the literal extension computed
    `F 4 = 5` and the theorem was accepted with no cache flag at all.
    """
    x = Export()
    nat, P, p5 = nat_axioms(x)
    Nat = x.const(nat)
    F = x.axiom("F", x.pi(Nat, Nat, "n"))
    goal = x.app(x.const(P), x.app(x.const(F), x.nat(4)))
    x.emit({"in": F, "str": {"pre": nat, "str": "succ"}})
    x.thm("t", goal, x.const(p5))
    return x


def name_respelled_after_cached_equality():
    """`Nat.succ` (an axiom here) respelled `S` between two theorems.

    t1 : P (Nat.succ 4) := p5 holds by the literal extension and leaves
    `P 5 = P (Nat.succ 4)` in the equality cache. t2 states the same about
    the same nodes after the constant has stopped being `Nat.succ`: without
    the cache it was rejected, with KIOTA_XCACHE it was accepted.
    """
    x = Export()
    nat, P, p5 = nat_axioms(x)
    Nat = x.const(nat)
    succ = x.axiom("Nat.succ", x.pi(Nat, Nat, "n"))
    goal = x.app(x.const(P), x.app(x.const(succ), x.nat(4)))
    x.thm("t1", goal, x.const(p5))
    x.emit({"in": succ, "str": {"pre": 0, "str": "S"}})
    x.thm("t2", goal, x.const(p5))
    return x


def nat_literal_under_duplicate_nat_spelling(warm):
    """A second, never declared name index also spelled `Nat`.

    `inductive T | mk : P 5 -> T` is well typed: 5 : Nat. The inductive
    check typed literals by the last index spelled `Nat` (the undeclared
    one) while every other check used the declared one, so the block was
    rejected without the cache and accepted with it, where an earlier
    checker had left `5 : Nat` behind (`warm`: a definition; otherwise the
    block's own recursor reconstruction).
    """
    x = Export()
    type1 = x.sort(x.lsucc(0))
    nat = x.name("Nat")
    x.name("Nat", fresh=True)
    x.axiom(nat, type1)
    Nat = x.const(nat)
    P = x.axiom("P", x.pi(Nat, type1, "n"))
    five = x.nat(5)
    if warm:
        x.defn("five", Nat, five)
    x.struct1("T", x.app(x.const(P), five))
    return x


def whnf_depth_cap_then_shallow(n=8300):
    """A reduction that runs out of depth in one declaration and not the next.

    c_0 = B.t, c_{k+1} = B.rec (fun _ => B) B.f B.t c_k, and PV projects a
    structure picked by c_n. Typing `r : R PV` and checking d1 reduce the
    chain from inside other reductions and hit the depth cap; the weak head
    normal forms left stuck there are still what the term is equal to, but
    not what a fresh reduction gives. d2 needs PV reduced and has the depth
    for it: accepted without the cache, rejected with KIOTA_XCACHE when the
    stuck forms were read back.
    """
    x = Export()
    B, Bt, Bf, Brec, _ = x.enum2("B", "t", "f")
    one = x.lsucc(0)
    type1 = x.sort(one)
    Bc = x.const(B)
    S, Smk, _, _ = x.struct1("S", Bc)
    Sc = x.const(S)
    two = x.lsucc(one)
    const_b = x.defn(
        "ConstB",
        x.pi(Bc, type1, "t"),
        x.app(x.const(Brec, [two]), x.lam(Bc, type1, "t"), Bc, Bc),
        hints="abbrev",
    )
    c = x.const(Bt)
    for _ in range(n):
        c = x.app(x.const(Brec, [one]), x.const(const_b), x.const(Bf), x.const(Bt), c)
    V = x.app(
        x.const(Brec, [one]),
        x.lam(Bc, Sc, "t"),
        x.app(x.const(Smk), x.const(Bt)),
        x.app(x.const(Smk), x.const(Bf)),
        c,
    )
    PV = x.proj(S, 0, V)
    R = x.axiom("R", x.pi(Bc, x.sort(0), "b"))
    Rc = x.const(R)
    r = x.axiom("r", x.app(Rc, PV))
    x.thm("d1", x.app(Rc, x.app(x.lam(Bc, x.bvar(0), "x"), PV)), x.const(r))
    value = x.const(Bt) if n % 2 == 0 else x.const(Bf)
    q = x.axiom("q", x.app(Rc, value))
    x.thm("d2", x.app(Rc, PV), x.const(q))
    return x


def literal_typed_by_a_respelled_unused_index():
    """A name index spelled `Nat` while unused, respelled `T`, then declared.

    axiom T : Type sits under an index the parser's spelling table still
    filed under `Nat`, so a literal was typed `T` and `def bad : T := 5`
    was accepted, with or without the cache flags, although no `Nat`
    exists.
    """
    x = Export()
    type1 = x.sort(x.lsucc(0))
    t = x.name("Nat")
    x.emit({"in": t, "str": {"pre": 0, "str": "T"}})
    x.axiom(t, type1)
    x.defn("bad", x.const(t), x.nat(5))
    return x


FIXTURES = {
    "name-index-respelled-into-nat-succ.reject.ndjson": name_respelled_into_nat_succ,
    "name-index-respelled-after-cached-equality.reject.ndjson": name_respelled_after_cached_equality,
    "name-index-respelled-before-declaration.reject.ndjson": literal_typed_by_a_respelled_unused_index,
    "nat-literal-under-duplicate-nat-spelling.accept.ndjson": lambda: nat_literal_under_duplicate_nat_spelling(True),
    "nat-literal-under-duplicate-nat-spelling-inductive-only.accept.ndjson": lambda: nat_literal_under_duplicate_nat_spelling(False),
    "whnf-depth-cap-then-shallow.accept.ndjson": whnf_depth_cap_then_shallow,
}



def ctor_type_mentions_own_ctor():
    """Not a cache case and not a fixture: an open finding about the checker.

    inductive S | mk : ((fun (k : B -> S) => B) S.mk) -> S. The field type
    mentions S.mk, the constructor being declared. The checker accepts it
    with or without the cache flags (exit 0 on main 07367f0). What the
    official kernel does with it has not been run; it checks constructor
    types before the constructors are in the environment.
    """
    x = Export()
    B, _, _, _, _ = x.enum2("B", "t", "f")
    Bc = x.const(B)
    x.name("S")
    mk = x.name("S.mk")
    x.name("S.rec")
    Sc = x.const("S")
    field = x.app(x.lam(x.pi(Bc, Sc, "b"), Bc, "k"), x.const(mk))
    x.struct1("S", field)
    return x


# Written only when named on the command line.
OPEN_FINDINGS = {
    "open-finding-ctor-type-mentions-own-ctor.ndjson": ctor_type_mentions_own_ctor,
}

if __name__ == "__main__":
    out = sys.argv[1]
    only = sys.argv[2:]
    for name, build in FIXTURES.items():
        if only and name not in only:
            continue
        build().write(os.path.join(out, name))
        print(name)
    for name, build in OPEN_FINDINGS.items():
        if name in only:
            build().write(os.path.join(out, name))
            print(name)
