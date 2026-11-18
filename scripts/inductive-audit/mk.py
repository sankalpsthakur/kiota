"""Tiny DSL for inductive admission probes: one spec renders to a lean4export
ndjson file and to a Lean script that hands the same declarations to the
official kernel (`Environment.addDeclCore`).

kiota compares a block's recursors with the ones it reconstructs, so a probe
needs the real recursor types or it only tests what fires before
reconstruction. `probe.patch` adds a `KIOTA_PROBE=<first type>` hook that
prints the reconstructed recursors of that block; `render_nd` runs it once
per block and writes them back into the export.

  git apply scripts/inductive-audit/probe.patch && cargo build --release
  cp target/release/kiota /tmp/kiota-probe && git checkout src
  PROBE_BIN=/tmp/kiota-probe KIOTA_BIN=target/release/kiota \
      python3 scripts/inductive-audit/probes.py /tmp/out [name-prefix ...]
  PROBE_BIN=/tmp/kiota-probe python3 scripts/inductive-audit/fixtures.py /tmp/fx

The hook sits after the structural checks, so a block the checker refuses
gets no recursors from a probe built on the same source. The reject fixtures
were generated with the patch applied to 606c3c0, which admitted them.
NOLEAN=1 skips the Lean run; the toolchain defaults to v4.34.0-rc2.
"""
import json, subprocess, os, sys, copy
W = os.path.dirname(os.path.abspath(__file__))
PROBE = os.environ.get('PROBE_BIN', W + '/kiota-probe')
META = {"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"5045d0056413266e57c625dcd7c365b10e377c52","version":"4.34.1"}}}

# ---- expr constructors (tuples) ----
def S(l): return ('s', l)
Prop = S(0); Type = S(1)
def C(n, *ls): return ('c', n, tuple(ls))
def B(i): return ('b', i)
def A(f, *args):
    for a in args: f = ('a', f, a)
    return f
def Pi(ty, body): return ('p', ty, body)
def Pis(tys, body):
    for t in reversed(tys): body = Pi(t, body)
    return body
def Lam(ty, body): return ('l', ty, body)
def Let(ty, v, body): return ('let', ty, v, body)
def Proj(s, i, e): return ('proj', s, i, e)
def Ty(name, type, ctors, nindices=0): return dict(name=name, type=type, ctors=ctors, nindices=nindices)

class X:
    def __init__(self, label):
        self.label = label; self.ops = []
    def axiom(self, name, lps, type): self.ops.append(('axiom', name, lps, type))
    def defn(self, name, lps, type, value, hints='abbrev'): self.ops.append(('def', name, lps, type, value, hints))
    def thm(self, name, lps, type, value): self.ops.append(('thm', name, lps, type, value))
    def inductive(self, lps, nparams, types, mut=None, lean=True, **flags):
        self.ops.append(('ind', lps, nparams, types, mut, flags, lean))

class Nd:
    def __init__(self):
        self.lines = [json.dumps(META, separators=(',',':'))]
        self.names = {'': 0}; self.levels = {('z',): 0}; self.exprs = {}
    def emit(self, o): self.lines.append(json.dumps(o, separators=(',',':'), sort_keys=True))
    def name(self, s):
        if s in self.names: return self.names[s]
        pre, _, last = s.rpartition('.')
        p = self.name(pre); i = len(self.names); self.names[s] = i
        self.emit({"in": i, "str": {"pre": p, "str": last}}); return i
    def nl(self, l):
        if isinstance(l, int): return ('z',) if l == 0 else ('S', self.nl(l-1))
        if isinstance(l, str): return ('P', l)
        if l[0] in ('m','i'): return (l[0], self.nl(l[1]), self.nl(l[2]))
        if l[0] == 'S': return ('S', self.nl(l[1]))
        return l
    def lvl(self, l):
        l = self.nl(l)
        if l in self.levels: return self.levels[l]
        if l[0] == 'S': o = {"succ": self.lvl(l[1])}
        elif l[0] == 'm': o = {"max": [self.lvl(l[1]), self.lvl(l[2])]}
        elif l[0] == 'i': o = {"imax": [self.lvl(l[1]), self.lvl(l[2])]}
        elif l[0] == 'P': o = {"param": self.name(l[1])}
        i = len(self.levels); self.levels[l] = i; o["il"] = i; self.emit(o); return i
    def expr(self, e):
        if e in self.exprs: return self.exprs[e]
        k = e[0]
        if k == 's': o = {"sort": self.lvl(e[1])}
        elif k == 'c': o = {"const": {"name": self.name(e[1]), "us": [self.lvl(l) for l in e[2]]}}
        elif k == 'b': o = {"bvar": e[1]}
        elif k == 'a': o = {"app": {"fn": self.expr(e[1]), "arg": self.expr(e[2])}}
        elif k in ('p','l'):
            o = {("forallE" if k == 'p' else "lam"): {"binderInfo": "default", "name": 0, "type": self.expr(e[1]), "body": self.expr(e[2])}}
        elif k == 'let': o = {"letE": {"name": 0, "type": self.expr(e[1]), "value": self.expr(e[2]), "body": self.expr(e[3]), "nondep": False}}
        elif k == 'proj': o = {"proj": {"typeName": self.name(e[1]), "idx": e[2], "struct": self.expr(e[3])}}
        else: raise Exception(e)
        i = len(self.exprs); self.exprs[e] = i; o["ie"] = i; self.emit(o); return i
    # probe sexpr (name ids) -> tuple expr
    def from_probe_level(self, l, rev):
        if l[0] == 'z': return 0
        if l[0] == 'S': return ('S', self.from_probe_level(l[1], rev))
        if l[0] in ('m','i'): return (l[0], self.from_probe_level(l[1], rev), self.from_probe_level(l[2], rev))
        if l[0] == 'P': return 'uElim' if l[1] == 2**32-1-7 else rev[l[1]]
    def from_probe(self, e, rev):
        k = e[0]
        if k == 'b': return B(e[1])
        if k == 's': return S(self.from_probe_level(e[1], rev))
        if k == 'c': return ('c', rev[e[1]], tuple(self.from_probe_level(l, rev) for l in e[2]))
        if k == 'a': return ('a', self.from_probe(e[1], rev), self.from_probe(e[2], rev))
        if k in ('p','l'): return (k, self.from_probe(e[1], rev), self.from_probe(e[2], rev))
        if k == 'let': return ('let',) + tuple(self.from_probe(x, rev) for x in e[1:])
        if k == 'proj': return ('proj', rev[e[1]], e[2], self.from_probe(e[3], rev))
        raise Exception(e)

def render_nd(x, path, probe_bin=None):
    probe_bin = probe_bin or PROBE
    nd = Nd(); notes = []
    for op in x.ops:
        if op[0] == 'axiom':
            _, name, lps, ty = op
            nd.emit({"axiom": {"name": nd.name(name), "levelParams": [nd.name(l) for l in lps], "type": nd.expr(ty), "isUnsafe": False}})
        elif op[0] == 'def':
            _, name, lps, ty, val, hints = op
            nd.emit({"def": {"name": nd.name(name), "levelParams": [nd.name(l) for l in lps], "type": nd.expr(ty), "value": nd.expr(val), "hints": hints, "safety": "safe", "all": [nd.name(name)]}})
        elif op[0] == 'thm':
            _, name, lps, ty, val = op
            nd.emit({"thm": {"name": nd.name(name), "levelParams": [nd.name(l) for l in lps], "type": nd.expr(ty), "value": nd.expr(val), "all": [nd.name(name)]}})
        elif op[0] == 'ind':
            _, lps, nparams, types, mut, flags, _lean = op
            lp_ids = [nd.name(l) for l in lps]
            all_ids = [nd.name(t['name']) for t in types]
            tys = []; ctors = []
            if 'isRec' not in flags:
                names = set(t['name'] for t in types)
                def occ(e):
                    if e[0] == 'c': return e[1] in names
                    return any(occ(x) for x in e[1:] if isinstance(x, tuple) and x and isinstance(x[0], str) and x[0] in ('s','c','b','a','p','l','let','proj'))
                def doms(e):
                    while e[0] == 'p':
                        yield e[1]; e = e[2]
                flags = dict(flags, isRec=any(occ(d) for t in types for c in t['ctors'] for d in doms(c[1])))
            for t in types:
                cids = [nd.name(c[0]) for c in t['ctors']]
                tys.append({"name": nd.name(t['name']), "levelParams": lp_ids, "type": nd.expr(t['type']), "numParams": nparams,
                            "numIndices": t['nindices'], "all": all_ids, "ctors": cids, "isRec": flags.get('isRec', False),
                            "isReflexive": flags.get('isReflexive', False), "isUnsafe": False, "numNested": flags.get('numNested', 0)})
                for ci, c in enumerate(t['ctors']):
                    nf = c[2] if len(c) > 2 else count_pis(c[1]) - nparams
                    ctors.append({"name": nd.name(c[0]), "levelParams": lp_ids, "type": nd.expr(c[1]), "induct": nd.name(t['name']),
                                  "cidx": ci, "numParams": nparams, "numFields": nf, "isUnsafe": False})
            first = types[0]['name']
            dummy_t = nd.expr(Prop)
            dummy = [{"name": nd.name(first + '.rec'), "levelParams": lp_ids, "type": dummy_t, "all": all_ids, "numParams": nparams,
                      "numIndices": 0, "numMotives": 1, "numMinors": 0, "k": False, "isUnsafe": False, "rules": []}]
            uel = nd.name('uElim')
            tmp = path + '.probe'
            open(tmp, 'w').write('\n'.join(nd.lines + [json.dumps({"inductive": {"types": tys, "ctors": ctors, "recs": dummy}})]) + '\n')
            r = subprocess.run([probe_bin, tmp], capture_output=True, text=True, env=dict(os.environ, KIOTA_PROBE=first))
            out = r.stdout + r.stderr
            recs = dummy
            pl = [l for l in out.splitlines() if l.startswith('PROBE recs ')]
            ml = [l for l in out.splitlines() if l.startswith('PROBE members ')]
            if pl:
                rev = {v: k for k, v in nd.names.items()}
                info = json.loads(pl[0][len('PROBE recs '):]); members = json.loads(ml[-1][len('PROBE members '):])
                recs = []
                for i, rc in enumerate(info['recs']):
                    rname = types[i]['name'] + '.rec' if i < len(types) else first + '.rec_%d' % (i - len(types) + 1)
                    rt = nd.from_probe(rc['type'], rev)
                    recs.append({"name": nd.name(rname), "levelParams": (lp_ids if info['propOnly'] else [uel] + lp_ids), "type": nd.expr(rt),
                                 "all": all_ids, "numParams": rc['numParams'], "numIndices": rc['numIndices'], "numMotives": rc['numMotives'],
                                 "numMinors": rc['numMinors'], "k": rc['k'], "isUnsafe": False,
                                 "rules": [{"ctor": c, "nfields": nf, "rhs": dummy_t} for c, nf in members[i]]})
                notes.append('struct+reconstruct ok (propOnly=%s, %d recs)' % (info['propOnly'], len(recs)))
            else:
                msg = [l for l in out.splitlines() if 'REJECT' in l or 'PROBE' in l or 'DECLINE' in l or 'rror' in l]
                notes.append('probe: ' + ' | '.join(msg)[:300])
            os.remove(tmp)
            blk = {"types": tys, "ctors": ctors, "recs": recs}
            if mut: blk = mut(blk, nd) or blk
            nd.emit({"inductive": blk})
    open(path, 'w').write('\n'.join(nd.lines) + '\n')
    return notes

def count_pis(e):
    n = 0
    while e[0] == 'p': n += 1; e = e[2]
    return n

# ---- Lean backend ----
def lean_level(l):
    if isinstance(l, int): return '.zero' if l == 0 else '(.succ %s)' % lean_level(l-1)
    if isinstance(l, str): return '(.param `%s)' % l
    if l[0] == 'S': return '(.succ %s)' % lean_level(l[1])
    if l[0] == 'm': return '(.max %s %s)' % (lean_level(l[1]), lean_level(l[2]))
    if l[0] == 'i': return '(.imax %s %s)' % (lean_level(l[1]), lean_level(l[2]))
def lean_expr(e, pfx):
    k = e[0]
    if k == 's': return '(.sort %s)' % lean_level(e[1])
    if k == 'c': return '(.const `%s.%s [%s])' % (pfx, e[1], ', '.join(lean_level(l) for l in e[2]))
    if k == 'b': return '(.bvar %d)' % e[1]
    if k == 'a': return '(.app %s %s)' % (lean_expr(e[1], pfx), lean_expr(e[2], pfx))
    if k == 'p': return '(.forallE `a %s %s .default)' % (lean_expr(e[1], pfx), lean_expr(e[2], pfx))
    if k == 'l': return '(.lam `a %s %s .default)' % (lean_expr(e[1], pfx), lean_expr(e[2], pfx))
    if k == 'let': return '(.letE `a %s %s %s false)' % tuple(lean_expr(x, pfx) for x in e[1:])
    if k == 'proj': return '(.proj `%s.%s %d %s)' % (pfx, e[1], e[2], lean_expr(e[3], pfx))
def render_lean(xs):
    out = ['import Lean', 'open Lean', '',
           'def tryAdd (label : String) (decl : Declaration) : CoreM Unit := do',
           '  match (← getEnv).addDeclCore 0 2048 decl none with',
           '  | .ok env =>',
           '    setEnv env',
           '    let mut info := ""',
           '    match decl with',
           '    | .inductDecl lps _ types _ =>',
           '      for t in types do',
           '        if let some (.inductInfo iv) := env.find? t.name then',
           '          info := info ++ s!" [{t.name}: isRec={iv.isRec} isReflexive={iv.isReflexive} numNested={iv.numNested} nidx={iv.numIndices}"',
           '          if let some (.recInfo rv) := env.find? (t.name ++ `rec) then',
           '            info := info ++ s!" largeElim={rv.levelParams.length != lps.length} k={rv.k} motives={rv.numMotives} minors={rv.numMinors} rules={rv.rules.map (·.ctor)}"',
           '          info := info ++ "]"',
           '    | _ => pure ()',
           '    IO.println s!"LEAN OK   {label}{info}"',
           '  | .error ex => IO.println s!"LEAN ERR  {label}: {← (ex.toMessageData {}).toString}"', '']
    for n, x in enumerate(xs):
        pfx = 'Zq%d' % n
        body = []
        for j, op in enumerate(x.ops):
            lab = '%s#%d' % (x.label, j)
            if op[0] == 'axiom':
                _, name, lps, ty = op
                d = '(.axiomDecl {name := `%s.%s, levelParams := [%s], type := %s, isUnsafe := false})' % (pfx, name, ', '.join('`'+l for l in lps), lean_expr(ty, pfx))
            elif op[0] == 'def':
                _, name, lps, ty, val, hints = op
                d = '(.defnDecl {name := `%s.%s, levelParams := [%s], type := %s, value := %s, hints := .abbrev, safety := .safe})' % (pfx, name, ', '.join('`'+l for l in lps), lean_expr(ty, pfx), lean_expr(val, pfx))
            elif op[0] == 'thm':
                _, name, lps, ty, val = op
                d = '(.thmDecl {name := `%s.%s, levelParams := [%s], type := %s, value := %s})' % (pfx, name, ', '.join('`'+l for l in lps), lean_expr(ty, pfx), lean_expr(val, pfx))
            elif op[0] == 'ind':
                _, lps, nparams, types, mut, flags, lean = op
                if not lean: continue
                ts = ', '.join('{name := `%s.%s, type := %s, ctors := [%s]}' % (pfx, t['name'], lean_expr(t['type'], pfx),
                      ', '.join('{name := `%s.%s, type := %s}' % (pfx, c[0], lean_expr(c[1], pfx)) for c in t['ctors'])) for t in types)
                d = '(.inductDecl [%s] %d [%s] false)' % (', '.join('`'+l for l in lps), nparams, ts)
            body.append('  tryAdd "%s" %s' % (lab, d))
        if body:
            out.append('#eval show CoreM Unit from do'); out += body; out.append('')
    return '\n'.join(out)

def run(specs, outdir, kiota=None, lean=(os.environ.get('NOLEAN') is None), toolchain='leanprover/lean4:v4.34.0-rc2'):
    kiota = kiota or os.environ.get('KIOTA_BIN') or 'target/release/kiota'
    os.makedirs(outdir, exist_ok=True)
    xs = []
    for f in specs:
        x = X(f.__name__); f(x); xs.append(x)
    leanres = {}
    if lean:
        lp = outdir + '/probes.lean'
        open(lp, 'w').write(render_lean(xs))
        r = subprocess.run([os.path.expanduser('~/.elan/bin/lean'), '+' + toolchain, lp], capture_output=True, text=True)
        for l in (r.stdout + r.stderr).splitlines():
            if l.startswith('LEAN '):
                lab = l[10:].split(':')[0].split('#')[0].strip()
                leanres.setdefault(lab, []).append(l[5:].strip())
            elif l.strip(): leanres.setdefault('_other', []).append(l)
    for x in xs:
        p = '%s/%s.ndjson' % (outdir, x.label)
        notes = render_nd(x, p)
        r = subprocess.run([kiota, p], capture_output=True, text=True)
        msg = [l for l in (r.stdout + r.stderr).splitlines() if not l.startswith('[decl')]
        print('== %s' % x.label)
        for n in notes: print('   probe : ' + n)
        print('   kiota : rc=%d %s' % (r.returncode, (msg[-1] if msg else '')[:220]))
        for l in leanres.get(x.label, []): print('   lean  : ' + l[:260])
    for l in leanres.get('_other', [])[:20]: print('   lean-other: ' + l[:300])
