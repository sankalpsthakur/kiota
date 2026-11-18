#!/usr/bin/env python3
"""Writes the hand-made export fixtures for the name table, the index
tables and the recursor records (tests/fixtures/*.ndjson, see the tests at
the end of tests/exports.rs).

Three fixtures are lean4export output and are not written here
(tests/fixtures/src/<name>.lean, Lean 4.33.0, lean4export 3.1.0):
  mutual-with-empty-member.accept     lean4export MutEmpty
  recursor-rules-nested.accept        lean4export NestRules -- Snd.good Snd.badTy Snd.badVal
  recursor-k-flag.accept              lean4export IdxRules
The recursor rejects below are those exports with one field changed;
recursor-rules-nested-base.ndjson is `lean4export NestRules -- Snd.badTy
Snd.badVal`, i.e. the same export without the theorem `good`.

usage: python3 scripts/snd-fixtures/gen.py   (from the repository root)
"""
import json, os

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "..", "tests", "fixtures")
META = {"meta": {"exporter": {"name": "handcrafted", "version": "0.1.0"}, "format": {"version": "3.1.0"},
                 "lean": {"githash": "5045d0056413266e57c625dcd7c365b10e377c52", "version": "4.34.1"}}}


class Ex:
    """An export under construction: next free indices and name lookup."""

    def __init__(self, base=None):
        self.lines, self.names, self.rev = [], {"": 0}, {0: ""}
        self.nmax, self.lmax, self.emax = 0, 0, -1
        if base is None:
            self.raw(META)
            return
        with open(base) as f:
            for ln in f:
                ln = ln.rstrip("\n")
                if not ln:
                    continue
                self.lines.append(ln)
                v = json.loads(ln)
                if "in" in v:
                    i = v["in"]
                    self.nmax = max(self.nmax, i)
                    p, s = (v["str"]["pre"], v["str"]["str"]) if "str" in v else (v["num"]["pre"], str(v["num"]["i"]))
                    full = s if not self.rev[p] else self.rev[p] + "." + s
                    self.rev[i] = full
                    self.names[full] = i
                elif "il" in v:
                    self.lmax = max(self.lmax, v["il"])
                elif "ie" in v:
                    self.emax = max(self.emax, v["ie"])

    def raw(self, obj):
        self.lines.append(obj if isinstance(obj, str) else json.dumps(obj, separators=(",", ":")))

    def name_line(self, idx, pre, seg):
        self.raw({"in": idx, "str": {"pre": pre, "str": seg}})
        self.nmax = max(self.nmax, idx)

    def name(self, full):
        if full in self.names:
            return self.names[full]
        pre, _, seg = full.rpartition(".")
        p = self.name(pre) if pre else 0
        self.nmax += 1
        self.name_line(self.nmax, p, seg)
        self.names[full] = self.nmax
        self.rev[self.nmax] = full
        return self.nmax

    def lvl(self, obj):
        self.lmax += 1
        self.raw({**obj, "il": self.lmax})
        return self.lmax

    def e(self, obj):
        self.emax += 1
        self.raw({**obj, "ie": self.emax})
        return self.emax

    def sort(self, l): return self.e({"sort": l})
    def bvar(self, i): return self.e({"bvar": i})
    def nat(self, n): return self.e({"natVal": str(n)})

    def const(self, n, us=()):
        return self.e({"const": {"name": self.name(n) if isinstance(n, str) else n, "us": list(us)}})

    def app(self, f, *args):
        for a in args:
            f = self.e({"app": {"fn": f, "arg": a}})
        return f

    def pi(self, ty, body, bn="x"):
        return self.e({"forallE": {"binderInfo": "default", "name": self.name(bn), "type": ty, "body": body}})

    def lam(self, ty, body, bn="x"):
        return self.e({"lam": {"binderInfo": "default", "name": self.name(bn), "type": ty, "body": body}})

    def axiom(self, n, ty):
        n = self.name(n) if isinstance(n, str) else n
        self.raw({"axiom": {"isUnsafe": False, "levelParams": [], "name": n, "type": ty}})
        return n

    def thm(self, n, ty, val):
        n = self.name(n) if isinstance(n, str) else n
        self.raw({"thm": {"all": [n], "levelParams": [], "name": n, "type": ty, "value": val}})
        return n

    def defn(self, n, ty, val):
        n = self.name(n) if isinstance(n, str) else n
        self.raw({"def": {"all": [n], "hints": "opaque", "levelParams": [], "name": n, "safety": "safe",
                          "type": ty, "value": val}})
        return n

    def type1(self):
        return self.sort(self.lvl({"succ": 0}))

    def write(self, name):
        with open(os.path.join(OUT, name + ".ndjson"), "w") as f:
            f.write("\n".join(self.lines) + "\n")


def nat_world(x):
    """axiom Nat : Type, P : Nat -> Prop, p5 : P 5. Returns (Nat, P) as expression indices."""
    x.axiom("Nat", x.type1())
    nat = x.const("Nat")
    x.axiom("P", x.pi(nat, x.sort(0), "n"))
    p = x.const("P")
    x.axiom("p5", x.app(p, x.nat(5)))
    return nat, p


# ---------------------------------------------------------------- name table

# An axiom F : Nat -> Nat whose index is respelled `Nat.succ` after the
# declaration: the literal extension then computed F 4 = 5.
x = Ex()
nat, p = nat_world(x)
f = x.axiom("F", x.pi(nat, nat, "n"))
goal = x.app(p, x.app(x.const(f), x.nat(4)))
x.name_line(f, x.names["Nat"], "succ")
x.thm("t", goal, x.const("p5"))
x.write("name-index-respelled-after-declaration.reject")

# The other order: an unused index spelled `Nat`, respelled `T`, then
# `axiom T : Type` under it; `def bad : T := 5` was accepted.
x = Ex()
t1 = x.type1()
x.name_line(1, 0, "Nat")
x.name_line(1, 0, "T")
x.raw({"axiom": {"isUnsafe": False, "levelParams": [], "name": 1, "type": t1}})
x.defn("bad", x.const(1), x.nat(5))
x.write("name-index-respelled-before-declaration.reject")

# A second name line that says the same thing again is harmless.
x = Ex()
x.name_line(1, 0, "Foo")
x.name_line(1, 0, "Foo")
x.name_line(2, 1, "bar")
x.name_line(2, 1, "bar")
x.nmax = 2
x.axiom(2, x.sort(0))
x.write("name-line-repeated.accept")

# A name line whose prefix has no line yet. It used to be spelled as its
# bare last component, so index 2 (really `Foo.Nat`) was `Nat` and typed
# every literal.
x = Ex()
t1 = x.type1()
x.name_line(3, 0, "pad")
x.name_line(2, 1, "Nat")
x.name_line(1, 0, "Foo")
x.raw({"axiom": {"isUnsafe": False, "levelParams": [], "name": 2, "type": t1}})
x.defn("five", x.const(2), x.nat(5))
x.write("name-prefix-not-yet-defined.reject")

# The same export with the prefix first, and a `Nat` for the literal to
# have: `Foo.Nat` is not `Nat`.
x = Ex()
t1 = x.type1()
x.name_line(3, 0, "pad")
x.name_line(1, 0, "Foo")
x.name_line(2, 1, "Nat")
x.raw({"axiom": {"isUnsafe": False, "levelParams": [], "name": 2, "type": t1}})
x.axiom("Nat", t1)
x.defn("five", x.const(2), x.nat(5))
x.write("name-foo-nat-is-not-nat.reject")

# ... and `axiom Foo.Nat : Type` with an inhabitant by axiom is fine.
x = Ex()
t1 = x.type1()
x.name_line(3, 0, "pad")
x.name_line(1, 0, "Foo")
x.name_line(2, 1, "Nat")
x.raw({"axiom": {"isUnsafe": False, "levelParams": [], "name": 2, "type": t1}})
x.axiom("five", x.const(2))
x.write("name-prefix-defined-first.accept")

# The one-component name `«Nat.succ»` is not `Nat.succ`.
x = Ex()
nat, p = nat_world(x)
x.name_line(10, 0, "Nat.succ")
x.raw({"axiom": {"isUnsafe": False, "levelParams": [], "name": 10, "type": x.pi(nat, nat, "n")}})
x.nmax = 10
x.thm("t", x.app(p, x.app(x.const(10), x.nat(4))), x.const("p5"))
x.write("name-one-component-with-dot.reject")

# With the two-component name the kernel's literal extension applies.
x = Ex()
nat, p = nat_world(x)
s = x.axiom("Nat.succ", x.pi(nat, nat, "n"))
x.thm("t", x.app(p, x.app(x.const(s), x.nat(4))), x.const("p5"))
x.write("name-nat-succ-two-components.accept")

# A name index that never had a name line.
x = Ex()
x.name_line(5, 0, "pad")
x.raw({"axiom": {"isUnsafe": False, "levelParams": [], "name": 3, "type": x.sort(0)}})
x.write("name-index-without-name-line.reject")

# Two indices for one name are one name: declared through one, used
# through the other.
x = Ex()
x.name_line(1, 0, "Foo")
x.name_line(2, 0, "Foo")
x.nmax = 2
x.raw({"axiom": {"isUnsafe": False, "levelParams": [], "name": 1, "type": x.sort(0)}})
x.axiom("h", x.const(2))
x.write("name-second-index-is-the-same-name.accept")

# ------------------------------------------------------------- index tables

# fun (h : P) => #4294967296 was read as fun h => #0.
x = Ex()
x.axiom("P", x.sort(0))
pc = x.const("P")
x.thm("t", x.pi(pc, pc, "h"), x.lam(pc, x.bvar(4294967296), "h"))
x.write("bvar-index-beyond-u32.reject")

# #4294967295 fits a u32, and its loose range wrapped to "closed".
x = Ex()
x.axiom("P", x.sort(0))
x.thm("t", x.const("P"), x.bvar(4294967295))
x.write("bvar-index-u32-max.reject")

# A node with such an index that no declaration uses is only a node.
x = Ex()
x.axiom("P", x.sort(0))
pc = x.const("P")
x.bvar(4294967296)
x.bvar(18446744073709551615)
x.thm("t", x.pi(pc, pc, "h"), x.lam(pc, x.bvar(0), "h"))
x.write("bvar-index-beyond-u32-unused.accept")

# An expression reference 2^32 + i was read as i.
x = Ex()
x.axiom("P", x.sort(0))
pc = x.const("P")
b0 = x.bvar(0)
val = x.e({"lam": {"binderInfo": "default", "name": x.name("h"), "type": pc + 4294967296, "body": b0 + 4294967296}})
x.thm("t", x.pi(pc, pc, "h"), val)
x.write("expr-index-beyond-u32.reject")

# A level index inside the table that no level line filled read as zero:
# `axiom A : Sort #3` was `A : Prop`.
x = Ex()
x.raw({"il": 5, "succ": 0})
x.axiom("A", x.sort(3))
x.write("level-index-without-level-line.reject")

# Sparse level indices in dependency order are fine.
x = Ex()
x.raw({"il": 5, "succ": 0})
x.raw({"il": 3, "succ": 5})
x.axiom("A", x.sort(3))
x.write("level-index-sparse.accept")

# A numeral is decimal digits, with single underscores between digits
# (Lean's `String.toNat?`). `5_` and `+5` were read as 5, and anything
# unparseable as 0.
for tag, lit in (("trailing-separator", "5_"), ("signed", "+5")):
    x = Ex()
    nat, p = nat_world(x)
    x.thm("t", x.app(p, x.e({"natVal": lit})), x.const("p5"))
    x.write("nat-literal-" + tag + ".reject")
x = Ex()
nat, p = nat_world(x)
x.axiom("p0", x.app(p, x.nat(0)))
x.thm("t", x.app(p, x.e({"natVal": "zero"})), x.const("p0"))
x.write("nat-literal-not-a-numeral.reject")
x = Ex()
nat, p = nat_world(x)
x.thm("t", x.app(p, x.e({"natVal": "0_5"})), x.const("p5"))
x.write("nat-literal-separated.accept")

# A record of no known kind is not skipped: it could be a declaration.
x = Ex()
x.axiom("P", x.sort(0))
n = x.name("t")
x.raw({"theorem": {"all": [n], "levelParams": [], "name": n, "type": x.const("P"), "value": x.const("P")}})
x.write("unknown-record-kind.reject")

# One line, one record.
x = Ex()
n = x.name("P")
x.raw({"ie": 0, "sort": 0, "axiom": {"isUnsafe": False, "levelParams": [], "name": n, "type": 0}})
x.write("two-records-on-one-line.reject")

# ---------------------------------------------------------------- recursors


def decl_of(x, name):
    n = x.names[name]
    for ln in x.lines:
        v = json.loads(ln)
        for k in ("def", "thm"):
            if k in v and v[k]["name"] == n:
                return v[k]
    raise KeyError(name)


def edit_rec(x, recname, f):
    n = x.names[recname]
    for i, ln in enumerate(x.lines):
        v = json.loads(ln)
        if "inductive" in v:
            for r in v["inductive"]["recs"]:
                if r["name"] == n:
                    f(r)
                    x.lines[i] = json.dumps(v, separators=(",", ":"))
                    return
    raise KeyError(recname)


BASE = os.path.join(HERE, "recursor-rules-nested-base.ndjson")

# `Snd.Tr` nests `C` twice, so two minors of `Snd.Tr.rec_1`'s group are
# for `C.a`; with a major `@C.a (id' Tr)` the recursor's type cannot tell
# them apart and the minor was found by position in the exported rule
# list. Listing rec_1's rules as [b, a] made X reduce to N.o, and
# `bad : X = N.o := Eq.refl N.o` was accepted (X is N.z).
x = Ex(BASE)
edit_rec(x, "Snd.Tr.rec_1", lambda r: r["rules"].reverse())
x.thm("Snd.bad", decl_of(x, "Snd.badTy")["value"], decl_of(x, "Snd.badVal")["value"])
x.write("recursor-rules-permuted.reject")

# The same false theorem with the genuine rule list.
x = Ex(BASE)
x.thm("Snd.bad", decl_of(x, "Snd.badTy")["value"], decl_of(x, "Snd.badVal")["value"])
x.write("recursor-rules-genuine-false-theorem.reject")

# A rule that claims one field too many.
x = Ex(os.path.join(OUT, "recursor-rules-nested.accept.ndjson"))
def one_more_field(r): r["rules"][0]["nfields"] += 1
edit_rec(x, "Snd.Tr.rec", one_more_field)
x.write("recursor-rule-nfields-lie.reject")

# A rule list that leaves a constructor out.
x = Ex(os.path.join(OUT, "recursor-rules-nested.accept.ndjson"))
edit_rec(x, "Snd.C.rec", lambda r: r["rules"].pop())
x.write("recursor-rule-missing.reject")

# `k` is an assertion about the declaration.
x = Ex(os.path.join(OUT, "recursor-k-flag.accept.ndjson"))
def flip_k(r): r["k"] = not r["k"]
edit_rec(x, "T.rec", flip_k)
x.write("recursor-k-flag-lie.reject")
x = Ex(os.path.join(OUT, "recursor-k-flag.accept.ndjson"))
edit_rec(x, "Eq.rec", flip_k)
x.write("recursor-k-flag-denied.reject")
