#!/usr/bin/env python3
"""UNIT A0C (2026-08-28) — certification of the FIVE exact monic-cubic splitting
densities (COROLLARY HM3.D / EFF.HMENU3.17), the target list of the Lean campaign
`IFC6.CubicValueLaw` x 5  =>  `decidedSliceAt_three`.

With Phi = q^4+q^3+q^2+q+1  (so (q-1)*Phi = q^5-1):

    R_split    = R_{(1,1)^3}      = q^3 (q^2-q+1) / (6 (q+1) Phi)
    R_linInert = R_{(1,2),(1,1)}  = q^3 (q^2+q+1) / (2 (q+1) Phi)
    R_inert    = R_{(1,3)}        = q^3 (q+1)     / (3 Phi)
    R_linRam   = R_{(2,1),(1,1)}  = q (q^3+q+1)   / ((q+1) Phi)
    R_ram      = R_{(3,1)}        = (q^2+1)       / Phi

Four legs:
  A. SYMBOLIC (sympy): sum = 1; the self-similar stratum recursion (derived
     independently for this unit, see the fixed-point system below) is satisfied
     by the closed forms; E[#roots] = q/(q+1); q=2,3 anchors match the blueprint;
     transcription tie against verification/padic_types.monic_cubic_pred.
  B. EXACT F_q STRATA: brute-force factorization-shape counts of monic cubics
     over F_q for q in {2,3,5,7} match the five residue strata counts used by
     the recursion.
  C. EXACT RECURSION ORACLE, EXHAUSTIVE FINITE LEVEL: classify EVERY canonical
     lift at level N with padic_types.cubic_type_monic (exact integer Newton
     polygon / Hensel recursion) and check convergence of the level-N class
     proportions to the closed forms.
  D. DECORRELATED PARI LEG (gp binary, nfinit([f,[p]]) + idealprimedec):
     a ground-truth classifier that knows nothing of the recursion; calibrated
     first against the LEAN-PROVED n=2 values, then run on the cubics at
     p in {2,3,5,7} (wild p=2 and p=3 included). Monte Carlo, 4-sigma gates.

The recursion (fixed-point system) certified in leg A — this is the shape the
Lean lower-bound towers follow:

  full box (monic cubics, coefficients Haar on O^3), residue strata:
    s_split    = (q-1)(q-2)/(6q^2)   [3 distinct residue roots; Hensel-decided]
    s_linInert = (q-1)/(2q)          [distinct linear x irred quadratic]
    s_inert    = (q^2-1)/(3q^2)      [irreducible residue cubic]
    s_dbl      = (q-1)/q^2           [double root x distinct simple root]
    s_trp      = 1/q^2               [triple residue root]
  DBL box (recentred quadratic factor g = x^2+b1x+b0, b1,b0 in m), conditional:
    v(b0) = 1  -> ram              (measure (q-1)/q)
    v(b0) >= 2 -> full n=2 problem (measure 1/q, scale x -> pi y)
    so d_tau = [(q-1)/q]*1{tau=ram} + (1/q) R2_tau   with the LEAN-PROVED
    R2 = (q/(2(q+1)), q/(2(q+1)), 1/(q+1)).
  TRP box (recentred cubic, all coefficients in m), conditional, Newton polygon:
    v(c0) = 1                      -> (3,1)          measure (q-1)/q
    v(c0) = 2, v(c1) = 1           -> (2,1),(1,1)    measure (q-1)^2/q^3
    v(c0) = 2, v(c1) >= 2          -> (3,1)          measure (q-1)/q^3
    v(c0) >= 3, v(c1) = 1          -> (2,1),(1,1)    measure (q-1)/q^3
    v(c0) >= 3, v(c1) >= 2         -> full n=3 box   measure 1/q^3 (x -> pi y)
  assembly:
    R_split    = s_split    + s_dbl*d_split + s_trp*t_split
    R_linInert = s_linInert + s_dbl*d_inert + s_trp*t_linInert
    R_inert    = s_inert    +                s_trp*t_inert
    R_linRam   =              s_dbl*d_ram   + s_trp*t_linRam
    R_ram      =                              s_trp*t_ram
  with t_tau = (TRP conditional) = decided strata above + (1/q^3) R_tau.

Run:  uv run --with sympy python3 a0c_cubic_cert.py [--fast]
"""

import os
import subprocess
import sys
import random
import itertools
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import padic_types  # noqa: E402  (the repo's exact oracle + closed forms)

import sympy as sp  # noqa: E402

FAST = '--fast' in sys.argv

PASS = []


def chk(name, ok, extra=""):
    PASS.append((name, ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name} {extra}")


q = sp.symbols('q', positive=True)
Phi = q**4 + q**3 + q**2 + q + 1

R = {
    'split':    q**3 * (q**2 - q + 1) / (6 * (q + 1) * Phi),
    'linInert': q**3 * (q**2 + q + 1) / (2 * (q + 1) * Phi),
    'inert':    q**3 * (q + 1) / (3 * Phi),
    'linRam':   q * (q**3 + q + 1) / ((q + 1) * Phi),
    'ram':      (q**2 + 1) / Phi,
}

# padic_types type-code dictionary
CODE = {'split': '111', 'linInert': '12', 'inert': '3', 'linRam': '1r1', 'ram': '1c'}

print("=" * 72)
print("LEG A — symbolic identities (sympy, exact rational functions)")
print("=" * 72)

chk("A1: sum of the five closed forms = 1",
    sp.simplify(sum(R.values()) - 1) == 0)

# n=2 landed (LEAN-PROVED, G48) values
R2 = {'split': q / (2 * (q + 1)), 'inert': q / (2 * (q + 1)), 'ram': 1 / (q + 1)}

# DBL box conditionals
d = {'split': R2['split'] / q, 'inert': R2['inert'] / q,
     'ram': (q - 1) / q + R2['ram'] / q}
chk("A2: DBL-box conditionals sum to 1", sp.simplify(sum(d.values()) - 1) == 0)

# TRP box conditionals (decided strata + self-similar tail)
t = {
    'split':    R['split'] / q**3,
    'linInert': R['linInert'] / q**3,
    'inert':    R['inert'] / q**3,
    'linRam':   (q - 1)**2 / q**3 + (q - 1) / q**3 + R['linRam'] / q**3,
    'ram':      (q - 1) / q + (q - 1) / q**3 + R['ram'] / q**3,
}
chk("A3: TRP-box conditionals sum to 1", sp.simplify(sum(t.values()) - 1) == 0)

# residue strata
s_split = (q - 1) * (q - 2) / (6 * q**2)
s_linInert = (q - 1) / (2 * q)
s_inert = (q**2 - 1) / (3 * q**2)
s_dbl = (q - 1) / q**2
s_trp = 1 / q**2
chk("A4: residue strata sum to 1",
    sp.simplify(s_split + s_linInert + s_inert + s_dbl + s_trp - 1) == 0)

eqs = {
    'split':    R['split'] - (s_split + s_dbl * d['split'] + s_trp * t['split']),
    'linInert': R['linInert'] - (s_linInert + s_dbl * d['inert'] + s_trp * t['linInert']),
    'inert':    R['inert'] - (s_inert + s_trp * t['inert']),
    'linRam':   R['linRam'] - (s_dbl * d['ram'] + s_trp * t['linRam']),
    'ram':      R['ram'] - (s_trp * t['ram']),
}
for k, e in eqs.items():
    chk(f"A5: recursion fixed-point identity for {k}", sp.simplify(e) == 0)

chk("A6: E[#roots] = 3 R_split + R_linInert + R_linRam = q/(q+1)",
    sp.simplify(3 * R['split'] + R['linInert'] + R['linRam'] - q / (q + 1)) == 0)

anchors = {
    2: {'split': Fr(4, 93), 'linInert': Fr(28, 93), 'inert': Fr(8, 31),
        'linRam': Fr(22, 93), 'ram': Fr(5, 31)},
    3: {'split': Fr(63, 968), 'linInert': Fr(351, 968), 'inert': Fr(36, 121),
        'linRam': Fr(93, 484), 'ram': Fr(10, 121)},
}
for qq, tbl in anchors.items():
    ok = all(sp.Rational(v.numerator, v.denominator) == R[k].subs(q, qq)
             for k, v in tbl.items())
    chk(f"A7: q={qq} anchors match the blueprint tuple", ok,
        str({k: str(R[k].subs(q, qq)) for k in R}))

# transcription tie vs the repo's padic_types.monic_cubic_pred (numeric q=2..40)
ok = True
for qq in range(2, 41):
    pred = padic_types.monic_cubic_pred(qq)
    for k in R:
        mine = R[k].subs(q, qq)
        if sp.Rational(pred[CODE[k]].numerator, pred[CODE[k]].denominator) != mine:
            ok = False
chk("A8: closed forms == padic_types.monic_cubic_pred at q=2..40", ok)

# G61 lower bounds from the blueprint table stay BELOW the targets (sanity)
g61 = {2: {'split': Fr(1, 512), 'linInert': Fr(1, 4), 'inert': Fr(1, 4),
           'linRam': Fr(1, 16), 'ram': Fr(1, 16)},
       3: {'split': Fr(1, 19683), 'linInert': Fr(1, 3), 'inert': Fr(8, 27),
           'linRam': Fr(4, 81), 'ram': Fr(2, 81)}}
ok = all(sp.Rational(b.numerator, b.denominator) <= R[k].subs(q, qq)
         for qq, tbl in g61.items() for k, b in tbl.items())
chk("A9: G61's transcribed lower bounds <= targets at q=2,3", ok)

print("=" * 72)
print("LEG B — exact F_q residue-strata counts (brute force)")
print("=" * 72)


def fq_strata(p):
    """Counts of monic-cubic factorization shapes over F_p by brute force."""
    cnt = {'3distinct': 0, 'lin_x_irrquad': 0, 'irred': 0, 'dbl': 0, 'trp': 0}
    for c2, c1, c0 in itertools.product(range(p), repeat=3):
        roots = padic_types._residue_roots_mults([c2, c1, c0], p)
        mults = sorted(roots.values())
        if mults == [1, 1, 1]:
            cnt['3distinct'] += 1
        elif mults == [1]:
            cnt['lin_x_irrquad'] += 1
        elif mults == []:
            cnt['irred'] += 1
        elif mults == [1, 2]:
            cnt['dbl'] += 1
        elif mults == [3]:
            cnt['trp'] += 1
        else:
            raise AssertionError(mults)
    return cnt


for p in [2, 3, 5, 7]:
    cnt = fq_strata(p)
    expect = {'3distinct': p * (p - 1) * (p - 2) // 6,
              'lin_x_irrquad': p * p * (p - 1) // 2,
              'irred': (p**3 - p) // 3,
              'dbl': p * (p - 1),
              'trp': p}
    chk(f"B: F_{p} strata counts match", cnt == expect, str(cnt))

print("=" * 72)
print("LEG C — exhaustive level-N class proportions (exact recursion oracle)")
print("=" * 72)
print("  (canonical-lift proportion at level N -> R_tau as N -> infty;")
print("   deviation is bounded by the undecided mass ~ C q^{-N})")

levels = {2: [4, 6] if FAST else [4, 6, 8],
          3: [3, 4] if FAST else [3, 4, 5],
          5: [2, 3]}
for p, Ns in levels.items():
    target = {k: R[k].subs(q, p) for k in R}
    prev_maxdev = None
    for N in Ns:
        pN = p ** N
        tot = pN ** 3
        cnt = dict.fromkeys(CODE.values(), 0)
        und = 0
        for c2 in range(pN):
            for c1 in range(pN):
                for c0 in range(pN):
                    ty = padic_types.cubic_type_monic(c2, c1, c0, p)
                    if ty == 'UND':
                        und += 1
                    else:
                        cnt[ty] += 1
        devs = {k: abs(sp.Rational(cnt[CODE[k]], tot) - target[k]) for k in R}
        maxdev = max(devs.values())
        # loose but honest gate: undecided-mass envelope C * q^{1-N}, C = 4
        gate = sp.Rational(4 * p, p ** N)
        ok = maxdev <= gate and und <= 3 * p ** (2 * N)  # UND only on exact-root slice
        chk(f"C: p={p} N={N} max |obs - target| = {float(maxdev):.2e} <= {float(gate):.2e}",
            ok, f"(UND classes: {und})")
        if prev_maxdev is not None:
            chk(f"C: p={p} N={N} deviation shrank vs previous level",
                maxdev < prev_maxdev)
        prev_maxdev = maxdev

print("=" * 72)
print("LEG D — decorrelated PARI leg (gp: nfinit([f,[p]]) + idealprimedec)")
print("=" * 72)

GP = os.path.expanduser('~/.local/bin/gp')


def pari_types(polys, p):
    """Classify each integer monic poly (list of coeff-lists, ascending) over Q_p
    via gp: factor over Q, then idealprimedec on each factor (nfinit maximal at p
    only). Returns list of sorted (e,f) multisets."""
    lines = ["default(parisize, 256*1024*1024);"]
    for cs in polys:
        poly = "+".join(f"({c})*x^{i}" for i, c in enumerate(cs))
        lines.append(
            "my(f=%s, out=List()); my(fa=factor(f)[,1]);"
            "for(i=1, #fa, my(g=fa[i]);"
            " if(poldegree(g)==1, listput(out,[1,1]),"
            "  my(K=nfinit([g,[%d]]), dec=idealprimedec(K,%d));"
            "  for(j=1,#dec, listput(out,[dec[j].e, dec[j].f]))));"
            "print(Vec(out));" % (poly, p, p))
    script = "\n".join(lines) + "\nquit;\n"
    r = subprocess.run([GP, '-q', '-f'], input=script, capture_output=True,
                       text=True, timeout=1200)
    if r.returncode != 0:
        raise RuntimeError(r.stderr[:2000])
    outs = []
    for ln in r.stdout.strip().splitlines():
        ln = ln.strip()
        if not ln.startswith('['):
            continue
        pairs = []
        body = ln.strip('[]')
        # format: [e, f], [e, f], ...
        toks = body.replace('[', '').split(']')
        for t in toks:
            t = t.strip().strip(',').strip()
            if not t:
                continue
            e, f = [int(x) for x in t.split(',')]
            pairs.append((e, f))
        outs.append(tuple(sorted(pairs)))
    return outs


TYPE3 = {(((1, 1), (1, 1), (1, 1))): 'split',
         (((1, 1), (1, 2))): 'linInert',
         (((1, 3),)): 'inert',
         (((1, 1), (2, 1))): 'linRam',
         (((3, 1),)): 'ram'}
TYPE2 = {(((1, 1), (1, 1))): 'split', (((1, 2),)): 'inert', (((2, 1),)): 'ram'}

rng = random.Random(20260828)
M2 = 1500 if FAST else 4000   # calibration samples (n=2)
M3 = 1500 if FAST else 4000   # cubic samples per prime


def mc_leg(p, n, M, typemap, targets):
    H = p ** 10  # 10 base-p digits: decided with prob 1 - O(p^-9)
    polys = []
    for _ in range(M):
        cs = [rng.randrange(H) for _ in range(n)] + [1]
        polys.append(cs)
    res = pari_types(polys, p)
    assert len(res) == M, (len(res), M)
    freq = {}
    for r in res:
        freq[r] = freq.get(r, 0) + 1
    ok_all = True
    detail = []
    for shape, name in typemap.items():
        obs = freq.get(shape, 0) / M
        pred = float(targets[name])
        sd = (pred * (1 - pred) / M) ** 0.5
        ok = abs(obs - pred) <= 4 * sd + 1e-9
        ok_all = ok_all and ok
        detail.append(f"{name}: obs {obs:.4f} pred {pred:.4f}")
    stray = sum(v for k, v in freq.items() if k not in typemap)
    ok_all = ok_all and stray <= max(3, M // 500)  # rare undecided-tail slips
    return ok_all, "; ".join(detail) + f" | stray shapes: {stray}"


# D0: calibration on the LEAN-PROVED n=2 densities
for p in [2, 3, 5]:
    targ2 = {'split': Fr(p, 2 * (p + 1)), 'inert': Fr(p, 2 * (p + 1)),
             'ram': Fr(1, p + 1)}
    ok, detail = mc_leg(p, 2, M2, TYPE2, targ2)
    chk(f"D0: PARI calibration vs Lean-proved n=2 values, p={p} (4-sigma)", ok, detail)

# D1: the five cubic targets
for p in [2, 3, 5, 7]:
    targ3 = {k: Fr(int(sp.fraction(R[k].subs(q, p))[0]),
                   int(sp.fraction(R[k].subs(q, p))[1])) for k in R}
    ok, detail = mc_leg(p, 3, M3, TYPE3, targ3)
    chk(f"D1: PARI vs the five cubic targets, p={p} (4-sigma)", ok, detail)

print()
print("=" * 72)
nfail = sum(1 for _, ok in PASS if not ok)
print(f"{len(PASS)} checks, {nfail} failures")
if nfail:
    sys.exit(1)
