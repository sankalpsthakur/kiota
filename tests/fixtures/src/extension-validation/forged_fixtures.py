#!/usr/bin/env python3
"""Build the extension-validation fixtures.

    forged_fixtures.py <dir with *.base.ndjson> <output dir>

Each `*.base.ndjson` is the lean4export of the prelude-free Lean file of the
same name beside this script (Lean 4.33.0, lean4export df81913):

    lean -o Forged.olean Forged.lean
    LEAN_PATH=$PWD lean4export Forged > Forged.base.ndjson

A fixture is one base plus one theorem appended here. The theorems cannot
come from Lean: the false ones Lean refuses to add, and the accept twins use
raw literals that a prelude-free file has no notation for.
"""
import json
import sys


class Export:
    def __init__(self, path):
        self.lines = [l.rstrip("\n") for l in open(path)]
        self.names = {"": 0}
        self.max_in = self.max_il = self.max_ie = 0
        byid = {0: ""}
        for line in self.lines:
            o = json.loads(line)
            if "in" in o:
                key = "str" if "str" in o else "num"
                pre = byid[o[key]["pre"]]
                seg = str(o[key]["str"] if key == "str" else o[key]["i"])
                full = pre + "." + seg if pre else seg
                byid[o["in"]] = full
                self.names[full] = o["in"]
                self.max_in = max(self.max_in, o["in"])
            elif "il" in o:
                self.max_il = max(self.max_il, o["il"])
            elif "ie" in o:
                self.max_ie = max(self.max_ie, o["ie"])
        self.out = []
        self.one = None

    def emit(self, o):
        self.out.append(json.dumps(o, separators=(",", ":"), sort_keys=True))

    def name(self, full):
        if full in self.names:
            return self.names[full]
        pre, _, seg = full.rpartition(".")
        p = self.name(pre) if pre else 0
        self.max_in += 1
        self.emit({"in": self.max_in, "str": {"pre": p, "str": seg}})
        self.names[full] = self.max_in
        return self.max_in

    def level_one(self):
        if self.one is None:
            self.max_il += 1
            self.emit({"il": self.max_il, "succ": 0})
            self.one = self.max_il
        return self.one

    def expr(self, o):
        self.max_ie += 1
        o["ie"] = self.max_ie
        self.emit(o)
        return self.max_ie

    def const(self, name, us=()):
        assert name in self.names, name
        return self.expr({"const": {"name": self.names[name], "us": list(us)}})

    def app(self, f, *args):
        for a in args:
            f = self.expr({"app": {"fn": f, "arg": a}})
        return f

    def nat(self, v):
        return self.expr({"natVal": str(v)})

    def lam(self, binder, ty, body):
        return self.expr({"lam": {"binderInfo": "default", "name": self.name(binder), "type": ty, "body": body}})

    def bvar(self, i):
        return self.expr({"bvar": i})

    def eq_refl_theorem(self, name, ty, lhs, rhs):
        """`theorem name : @Eq.{1} ty lhs rhs := @Eq.refl.{1} ty rhs`"""
        one = self.level_one()
        statement = self.app(self.const("Eq", [one]), ty, lhs, rhs)
        proof = self.app(self.const("Eq.refl", [one]), ty, rhs)
        n = self.name(name)
        self.emit({"thm": {"all": [n], "levelParams": [], "name": n, "type": statement, "value": proof}})

    def write(self, path):
        with open(path, "w") as f:
            for l in self.lines + self.out:
                f.write(l + "\n")


def nat_op(base, out, thm, op, a, b, result, ty="Nat"):
    """`op a b = result` by `rfl`, on raw literals."""
    x = Export(base)
    lhs = x.app(x.const(op), x.nat(a), x.nat(b))
    rhs = x.nat(result) if ty == "Nat" else x.const(result)
    x.eq_refl_theorem(thm, x.const(ty), lhs, rhs)
    x.write(out)


def true_instance(x, ctor):
    """`ctor True True.intro : Decidable True`"""
    return x.app(x.const(ctor), x.const("True"), x.const("True.intro"))


def ite_true(base, out, thm, ctor="Decidable.isTrue"):
    """`ite True (isTrue True.intro) true false = true`"""
    x = Export(base)
    one = x.level_one()
    b, t, f = x.const("Bool"), x.const("Bool.true"), x.const("Bool.false")
    lhs = x.app(x.const("ite", [one]), b, x.const("True"), true_instance(x, ctor), t, f)
    x.eq_refl_theorem(thm, b, lhs, t)
    x.write(out)


def dite_true(base, out, thm, ctor="Decidable.isTrue"):
    """`dite True (isTrue True.intro) (fun _ => true) (fun _ => false) = true`"""
    x = Export(base)
    one = x.level_one()
    b, t, f = x.const("Bool"), x.const("Bool.true"), x.const("Bool.false")
    then_ = x.lam("h", x.const("True"), t)
    else_ = x.lam("h", x.app(x.const("Not"), x.const("True")), f)
    lhs = x.app(x.const("dite", [one]), b, x.const("True"), true_instance(x, ctor), then_, else_)
    x.eq_refl_theorem(thm, b, lhs, t)
    x.write(out)


def decide_true(base, out, thm, ctor="Decidable.isTrue"):
    """`decide True (isTrue True.intro) = true`"""
    x = Export(base)
    lhs = x.app(x.const("Decidable.decide"), x.const("True"), true_instance(x, ctor))
    x.eq_refl_theorem(thm, x.const("Bool"), lhs, x.const("Bool.true"))
    x.write(out)


def literal_is_zero(base, out, thm):
    """`Nat.isZero 1 = true` over a `Nat` whose constructors are out of order."""
    x = Export(base)
    lhs = x.app(x.const("Nat.isZero"), x.nat(1))
    x.eq_refl_theorem(thm, x.const("Bool"), lhs, x.const("Bool.true"))
    x.write(out)


def main():
    src, dst = sys.argv[1], sys.argv[2]
    forged, ctors, genuine, bitwise, large = (
        f"{src}/{m}.base.ndjson" for m in ("Forged", "ForgedCtors", "Genuine", "ForgedBitwise", "ForgedLarge")
    )
    big = 2**200

    # Every theorem below is false for the definitions in Forged.lean.
    for op, a, b, r in [
        ("add", 2, 2, 4), ("mul", 2, 3, 6), ("pow", 2, 3, 8), ("sub", 5, 2, 3),
        ("shiftLeft", 1, 4, 16), ("shiftRight", 16, 4, 1), ("div", 6, 2, 3),
        ("mod", 7, 4, 3), ("gcd", 4, 6, 2), ("land", 6, 3, 2), ("lor", 4, 1, 5), ("xor", 6, 3, 5),
    ]:
        nat_op(forged, f"{dst}/forged-nat-{op.lower()}.reject.ndjson", "Forged.bad", f"Nat.{op}", a, b, r)
    nat_op(forged, f"{dst}/forged-nat-beq.reject.ndjson", "Forged.bad", "Nat.beq", 2, 3, "Bool.false", ty="Bool")
    nat_op(forged, f"{dst}/forged-nat-ble.reject.ndjson", "Forged.bad", "Nat.ble", 2, 3, "Bool.true", ty="Bool")
    ite_true(forged, f"{dst}/forged-ite-swapped.reject.ndjson", "Forged.bad")
    dite_true(forged, f"{dst}/forged-dite-axiom.reject.ndjson", "Forged.bad")
    decide_true(forged, f"{dst}/forged-decide-swapped.reject.ndjson", "Forged.bad")

    # ForgedBitwise.lean: `Nat.lor` is `Nat.bitwise and`, the wrong table.
    # `Nat.land` has the right table over a `Nat.bitwise` that returns its
    # first number, and is wrong at `1, 0`.
    nat_op(bitwise, f"{dst}/forged-nat-lor-wrong-table.reject.ndjson", "Forged.bad", "Nat.lor", 4, 1, 5)
    nat_op(bitwise, f"{dst}/forged-nat-bitwise.reject.ndjson", "Forged.bad", "Nat.land", 6, 3, 2)
    nat_op(bitwise, f"{dst}/forged-nat-modcore.reject.ndjson", "Forged.bad", "Nat.modCore", 7, 4, 3)

    # ForgedLarge.lean: a `Nat.div` that is division up to 16. It agrees with
    # the native rule wherever the validation looks, so this false theorem
    # is still accepted: the hole that remains.
    nat_op(large, f"{dst}/forged-nat-div-beyond-the-grid.hole.ndjson", "Forged.bad", "Nat.div", 1000, 10, 100)

    # Decidable.isTrue is an axiom in ForgedCtors.lean; nothing reduces at it.
    ite_true(ctors, f"{dst}/forged-decidable-istrue-axiom-ite.reject.ndjson", "Forged.bad")
    dite_true(ctors, f"{dst}/forged-decidable-istrue-axiom-dite.reject.ndjson", "Forged.bad")
    decide_true(ctors, f"{dst}/forged-decidable-istrue-axiom-decide.reject.ndjson", "Forged.bad")
    literal_is_zero(ctors, f"{dst}/forged-nat-ctor-order.reject.ndjson", "Forged.bad")

    # The same statements over the genuine definitions; the literals are too
    # large for anything but the native reductions.
    for op, a, b, r in [
        ("add", big, big, 2 * big), ("mul", big, big, big * big), ("pow", 2, 4000, 2**4000),
        ("sub", big * big, big, big * big - big), ("shiftLeft", 1, 4000, 2**4000),
    ]:
        nat_op(genuine, f"{dst}/validated-nat-{op.lower()}.accept.ndjson", "Genuine.good", f"Nat.{op}", a, b, r)
    nat_op(genuine, f"{dst}/validated-nat-beq.accept.ndjson", "Genuine.good", "Nat.beq", big, big + 1, "Bool.false", ty="Bool")
    nat_op(genuine, f"{dst}/validated-nat-ble.accept.ndjson", "Genuine.good", "Nat.ble", big, big + 1, "Bool.true", ty="Bool")
    ite_true(genuine, f"{dst}/validated-ite.accept.ndjson", "Genuine.good")
    dite_true(genuine, f"{dst}/validated-dite.accept.ndjson", "Genuine.good")
    decide_true(genuine, f"{dst}/validated-decide.accept.ndjson", "Genuine.good")


if __name__ == "__main__":
    main()
