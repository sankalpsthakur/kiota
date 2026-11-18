#!/usr/bin/env python3
"""Gives four older synthetic fixtures the computation rules Lean generates.

Their recursor records were written by hand with placeholder rules
(`Nat.rec`'s `succ` rule took the induction hypothesis as a fifth argument,
`Ok.rec`'s rule was a loose `#0`). Nothing read a rule's right-hand side
then; it is now type checked and compared with iota, as the official kernel
compares it with the rule it generates. Run once; kept for the record.

usage: python3 scripts/snd-fixtures/fix_synthetic_rules.py   (from the repository root)
"""
import json, os

FX = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tests", "fixtures")


def patch(name, rec_name, build):
    path = os.path.join(FX, name)
    lines = open(path).read().split("\n")
    spaced = '": ' in lines[0]
    dump = (lambda o: json.dumps(o)) if spaced else (lambda o: json.dumps(o, separators=(",", ":")))
    names, exprs, levels = {0: ""}, {}, {}
    emax = -1
    for pos, ln in enumerate(lines):
        if not ln.strip():
            continue
        v = json.loads(ln)
        if "in" in v:
            p, s = (v["str"]["pre"], v["str"]["str"]) if "str" in v else (v["num"]["pre"], str(v["num"]["i"]))
            names[v["in"]] = (names[p] + "." if names[p] else "") + s
        elif "il" in v:
            levels[v["il"]] = v
        elif "ie" in v:
            exprs[v["ie"]] = v
            emax = max(emax, v["ie"])
        elif "inductive" in v:
            for r in v["inductive"]["recs"]:
                if names[r["name"]] == rec_name:
                    emax = max(max(exprs), emax)
                    for later in lines[pos:]:
                        if later.strip():
                            w = json.loads(later)
                            if "ie" in w:
                                emax = max(emax, w["ie"])
                    new = []

                    def e(obj):
                        nonlocal emax
                        emax += 1
                        new.append(dump({**obj, "ie": emax}))
                        return emax

                    build(r, names, exprs, levels, e)
                    lines[pos] = dump(v)
                    lines[pos:pos] = new
                    open(path, "w").write("\n".join(lines))
                    return
    raise KeyError(rec_name)


def nat_succ_rule(r, names, exprs, levels, e):
    """fun motive zero succ n => succ n (Nat.rec motive zero succ n)"""
    zero_rule, succ_rule = r["rules"]
    l1 = exprs[zero_rule["rhs"]]["lam"]
    l2 = exprs[l1["body"]]["lam"]
    l3 = exprs[l2["body"]]["lam"]
    old = exprs[exprs[exprs[exprs[succ_rule["rhs"]]["lam"]["body"]]["lam"]["body"]]["lam"]["body"]]["lam"]
    nat = old["type"]
    u = next(i for i, l in levels.items() if l.get("param") == r["levelParams"][0])
    b = [e({"bvar": i}) for i in range(4)]
    app = lambda f, *xs: [f := e({"app": {"fn": f, "arg": x}}) for x in xs][-1]
    rec = e({"const": {"name": r["name"], "us": [u]}})
    body = app(b[1], b[0], app(rec, b[3], b[2], b[1], b[0]))
    lam = lambda src, body: e({"lam": {"binderInfo": src["binderInfo"], "name": src["name"], "type": src["type"], "body": body}})
    succ_rule["rhs"] = lam(l1, lam(l2, lam(l3, e({"lam": {"binderInfo": old["binderInfo"], "name": old["name"], "type": nat, "body": body}}))))


def ok_rule(r, names, exprs, levels, e):
    """fun motive mk α => mk α, with the binder types of Ok.rec's own type"""
    p1 = exprs[r["type"]]["forallE"]
    p2 = exprs[p1["body"]]["forallE"]
    p3 = exprs[p2["body"]]["forallE"]
    body = e({"app": {"fn": e({"bvar": 1}), "arg": e({"bvar": 0})}})
    lam = lambda src, body: e({"lam": {"binderInfo": src["binderInfo"], "name": src["name"], "type": src["type"], "body": body}})
    r["rules"][0]["rhs"] = lam(p1, lam(p2, lam(p3, body)))


for fixture in ("synthetic-nat-rec-countdown", "synthetic-below-brecon-countdown", "synthetic-below-inline-unshared"):
    patch(fixture + ".accept.ndjson", "Nat.rec", nat_succ_rule)
patch("eq-shaped-index-field.accept.ndjson", "Ok.rec", ok_rule)
