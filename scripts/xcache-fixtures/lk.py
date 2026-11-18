"""Tiny lean4export ndjson writer (format 3.1.0) for hand-built fixtures."""
import json

class Export:
    def __init__(self):
        self.lines = ['{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"5045d0056413266e57c625dcd7c365b10e377c52","version":"4.34.1"}}}']
        self.names = {"": 0}
        self.nnames = 1
        self.levels = {("zero",): 0}
        self.exprs = {}
    def emit(self, obj):
        self.lines.append(json.dumps(obj, separators=(",", ":"), sort_keys=True))
    # names
    def name(self, dotted, fresh=False):
        if dotted in self.names and not fresh:
            return self.names[dotted]
        if "." in dotted:
            pre, seg = dotted.rsplit(".", 1)
            p = self.name(pre)
        else:
            p, seg = 0, dotted
        idx = self.nnames
        self.nnames += 1
        if not fresh:
            self.names[dotted] = idx
        self.emit({"in": idx, "str": {"pre": p, "str": seg}})
        return idx
    # levels
    def _lvl(self, key, obj):
        if key in self.levels:
            return self.levels[key]
        idx = len(self.levels)
        self.levels[key] = idx
        obj["il"] = idx
        self.emit(obj)
        return idx
    def lsucc(self, l): return self._lvl(("succ", l), {"succ": l})
    def lparam(self, nm): 
        n = self.name(nm)
        return self._lvl(("param", n), {"param": n})
    # exprs
    def _e(self, key, obj):
        if key in self.exprs:
            return self.exprs[key]
        idx = len(self.exprs)
        self.exprs[key] = idx
        obj["ie"] = idx
        self.emit(obj)
        return idx
    def sort(self, l): return self._e(("sort", l), {"sort": l})
    def bvar(self, i): return self._e(("bvar", i), {"bvar": i})
    def const(self, nm, us=()):
        n = nm if isinstance(nm, int) else self.name(nm)
        return self._e(("const", n, tuple(us)), {"const": {"name": n, "us": list(us)}})
    def app(self, f, *args):
        for a in args:
            f = self._e(("app", f, a), {"app": {"fn": f, "arg": a}})
        return f
    def lam(self, ty, body, nm="x", bi="default"):
        n = self.name(nm)
        return self._e(("lam", n, bi, ty, body), {"lam": {"binderInfo": bi, "body": body, "name": n, "type": ty}})
    def pi(self, ty, body, nm="x", bi="default"):
        n = self.name(nm)
        return self._e(("pi", n, bi, ty, body), {"forallE": {"binderInfo": bi, "body": body, "name": n, "type": ty}})
    def proj(self, tname, idx, s):
        n = tname if isinstance(tname, int) else self.name(tname)
        return self._e(("proj", n, idx, s), {"proj": {"idx": idx, "struct": s, "typeName": n}})
    def nat(self, v): return self._e(("nat", v), {"natVal": str(v)})
    # decls
    def axiom(self, nm, ty, lps=()):
        n = nm if isinstance(nm, int) else self.name(nm)
        self.emit({"axiom": {"isUnsafe": False, "levelParams": list(lps), "name": n, "type": ty}})
        return n
    def defn(self, nm, ty, val, lps=(), hints="opaque"):
        n = nm if isinstance(nm, int) else self.name(nm)
        self.emit({"def": {"all": [n], "hints": hints, "levelParams": list(lps), "name": n, "safety": "safe", "type": ty, "value": val}})
        return n
    def thm(self, nm, ty, val, lps=()):
        n = nm if isinstance(nm, int) else self.name(nm)
        self.emit({"thm": {"all": [n], "levelParams": list(lps), "name": n, "type": ty, "value": val}})
        return n
    def enum2(self, T, c0, c1, ty=None):
        """inductive T : Type | c0 | c1, with its recursor."""
        t = self.name(T); a = self.name(f"{T}.{c0}"); b = self.name(f"{T}.{c1}"); r = self.name(f"{T}.rec")
        u = self.name("u"); lu = self.lparam("u")
        type1 = self.sort(self.lsucc(0)) if ty is None else ty
        Tc = self.const(t)
        motive_ty = self.pi(Tc, self.sort(lu), "t")
        # {motive} -> motive c0 -> motive c1 -> (t : T) -> motive t
        rec_ty = self.pi(motive_ty,
                  self.pi(self.app(self.bvar(0), self.const(a)),
                   self.pi(self.app(self.bvar(1), self.const(b)),
                    self.pi(Tc, self.app(self.bvar(3), self.bvar(0)), "t"), c1), c0), "motive", "implicit")
        rhs0 = self.lam(motive_ty, self.lam(self.app(self.bvar(0), self.const(a)), self.lam(self.app(self.bvar(1), self.const(b)), self.bvar(1), c1), c0), "motive")
        rhs1 = self.lam(motive_ty, self.lam(self.app(self.bvar(0), self.const(a)), self.lam(self.app(self.bvar(1), self.const(b)), self.bvar(0), c1), c0), "motive")
        self.emit({"inductive": {
            "ctors": [{"cidx": 0, "induct": t, "isUnsafe": False, "levelParams": [], "name": a, "numFields": 0, "numParams": 0, "type": Tc},
                      {"cidx": 1, "induct": t, "isUnsafe": False, "levelParams": [], "name": b, "numFields": 0, "numParams": 0, "type": Tc}],
            "recs": [{"all": [t], "isUnsafe": False, "k": False, "levelParams": [u], "name": r, "numIndices": 0, "numMinors": 2, "numMotives": 1, "numParams": 0,
                      "rules": [{"ctor": a, "nfields": 0, "rhs": rhs0}, {"ctor": b, "nfields": 0, "rhs": rhs1}], "type": rec_ty}],
            "types": [{"all": [t], "ctors": [a, b], "isRec": False, "isReflexive": False, "isUnsafe": False, "levelParams": [], "name": t, "numIndices": 0, "numNested": 0, "numParams": 0, "type": type1}]}})
        return t, a, b, r, lu
    def struct1(self, S, field_ty, sort=None, fname="val"):
        """inductive S : Type | mk : field_ty -> S (field_ty closed)."""
        s = self.name(S); mk = self.name(f"{S}.mk"); r = self.name(f"{S}.rec")
        u = self.name("u"); lu = self.lparam("u")
        srt = self.sort(self.lsucc(0)) if sort is None else sort
        Sc = self.const(s)
        mk_ty = self.pi(field_ty, Sc, fname)
        motive_ty = self.pi(Sc, self.sort(lu), "t")
        minor_ty = self.pi(field_ty, self.app(self.bvar(1), self.app(self.const(mk), self.bvar(0))), fname)
        rec_ty = self.pi(motive_ty, self.pi(minor_ty, self.pi(Sc, self.app(self.bvar(2), self.bvar(0)), "t"), "mk"), "motive", "implicit")
        rhs = self.lam(motive_ty, self.lam(minor_ty, self.lam(field_ty, self.app(self.bvar(1), self.bvar(0)), fname), "mk"), "motive")
        self.emit({"inductive": {
            "ctors": [{"cidx": 0, "induct": s, "isUnsafe": False, "levelParams": [], "name": mk, "numFields": 1, "numParams": 0, "type": mk_ty}],
            "recs": [{"all": [s], "isUnsafe": False, "k": False, "levelParams": [u], "name": r, "numIndices": 0, "numMinors": 1, "numMotives": 1, "numParams": 0,
                      "rules": [{"ctor": mk, "nfields": 1, "rhs": rhs}], "type": rec_ty}],
            "types": [{"all": [s], "ctors": [mk], "isRec": False, "isReflexive": False, "isUnsafe": False, "levelParams": [], "name": s, "numIndices": 0, "numNested": 0, "numParams": 0, "type": srt}]}})
        return s, mk, r, lu
    def write(self, path):
        with open(path, "w") as f:
            f.write("\n".join(self.lines) + "\n")
