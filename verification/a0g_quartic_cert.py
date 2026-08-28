#!/usr/bin/env python3
"""A0G quartic reality check: the eleven monic degree-four genres.

This is evidence for the general-n design, not a proof for n >= 5.  It checks:

  A. the eleven proposed rational functions symbolically (partition of unity,
     expected number of Q_p-roots, and q=2,3 anchors);
  B. the complete degree-four residue-divisor census over F_p, p=2,3,5,7;
  C. an independent assembly of those eleven residue genres from the cluster
     laws in om_density_engine, tied term-by-term to alpha_full(4);
  D. a decorrelated PARI/GP Monte Carlo factorization check, including p=2.

Run from the repository root:
    python3 verification/a0g_quartic_cert.py [--fast]
"""

from collections import Counter, defaultdict
from fractions import Fraction as Fr
import itertools
import os
import random
import subprocess
import sys
import warnings

import sympy as sp
from sympy.utilities.exceptions import SymPyDeprecationWarning

warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import om_density_engine as E  # noqa: E402


FAST = "--fast" in sys.argv
PASS = []
q = E.q


def chk(name, ok, extra=""):
    PASS.append((name, bool(ok)))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name} {extra}")


TYPES = [
    ((1, 1), (1, 1), (1, 1), (1, 1)),
    ((1, 1), (1, 1), (1, 2)),
    ((1, 1), (1, 1), (2, 1)),
    ((1, 1), (1, 3)),
    ((1, 1), (3, 1)),
    ((1, 2), (1, 2)),
    ((1, 2), (2, 1)),
    ((1, 4),),
    ((2, 1), (2, 1)),
    ((2, 2),),
    ((4, 1),),
]
NAMES = ["1111", "112", "11r", "13", "1r3", "22", "2r", "4", "rr", "r2", "r4"]

P2 = q**2 + q + 1
P3 = q**6 + q**3 + 1
P5 = q**4 + q**3 + q**2 + q + 1
FORMS = [
    q**6 * (q**8 - 2*q**7 + q**6 + 2*q**5 - q**4 + 2*q**3 + q**2 - 2*q + 1)
    / (24 * (q + 1)**2 * P2 * P3 * P5),
    q**6 * (q**8 + 2*q**7 + 3*q**6 + 2*q**5 + q**4 + 2*q**3 + 3*q**2 + 2*q + 1)
    / (4 * (q + 1)**2 * P2 * P3 * P5),
    q**3 * (q**10 + q**8 + 3*q**7 + q**6 + q**5 + 3*q**4 + 2*q**3 + 2*q**2 + 2*q + 1)
    / (2 * (q + 1)**2 * P2 * P3 * P5),
    q**6 * (q + 1)**2 * (q**2 - q + 1) / (3 * P3 * P5),
    q * (q**9 + 2*q**7 + q**6 + q**5 + 2*q**4 + 2*q**3 + q**2 + q + 1)
    / (P2 * P3 * P5),
    q**6 * (q**6 + q**5 - 2*q**3 + q + 1)
    / (8 * (q + 1)**2 * (q**2 + 1) * P2 * P3),
    q**3 * (q**6 + q**5 + q**4 + q + 1)
    / (2 * (q + 1)**2 * P2 * P3),
    q**6 * P5 / (4 * (q**2 + 1) * P2 * P3),
    q**2 / (2 * (q + 1)**2 * P2),
    q**2 * (q**7 + q**6 + q**4 + q**3 + 2*q**2 + q + 1)
    / (2 * (q + 1) * (q**2 + 1) * P2 * P3),
    (q**6 + q**5 + q**3 + q + 1) / ((q + 1) * P2 * P3),
]
R = dict(zip(TYPES, FORMS))

ANCHORS = {
    2: [Fr(344, 142569), Fr(13072, 142569), Fr(7348, 142569), Fr(576, 2263),
        Fr(1838, 15841), Fr(664, 22995), Fr(460, 4599), Fr(496, 2555),
        Fr(2, 63), Fr(454, 7665), Fr(107, 1533)],
    3: [Fr(821097, 152417408), Fr(10043433, 76208704), Fr(1983555, 38104352),
        Fr(27216, 91597), Fr(75774, 1190761), Fr(336069, 6298240),
        Fr(28539, 314912), Fr(88209, 393640), Fr(9, 416),
        Fr(13707, 393640), Fr(1003, 39364)],
}


print("=" * 76)
print("LEG A — exact symbolic quartic table")
print("=" * 76)
chk("A1: eleven forms sum to one", sp.cancel(sum(FORMS) - 1) == 0)
root_mean = sum(t.count((1, 1)) * R[t] for t in TYPES)
chk("A2: expected number of Q_p-roots is q/(q+1)",
    sp.cancel(root_mean - q / (q + 1)) == 0)
for qq, vals in ANCHORS.items():
    got = [sp.cancel(f.subs(q, qq)) for f in FORMS]
    want = [sp.Rational(x.numerator, x.denominator) for x in vals]
    chk(f"A3: q={qq} anchors", got == want)
for qq in [2, 3, 5, 7, 11]:
    chk(f"A4: q={qq} all masses are positive", all(f.subs(q, qq) > 0 for f in FORMS))


# A residue genre is a multiset of (closed-point degree, multiplicity) pairs.
GENRE_COUNTS = {
    ((1, 1), (1, 1), (1, 1), (1, 1)): q*(q-1)*(q-2)*(q-3)/24,
    ((1, 1), (1, 1), (1, 2)): q*(q-1)*(q-2)/2,
    ((1, 1), (1, 1), (2, 1)): q**2*(q-1)**2/4,
    ((1, 1), (1, 3)): q*(q-1),
    ((1, 1), (3, 1)): q**2*(q-1)*(q+1)/3,
    ((1, 2), (1, 2)): q*(q-1)/2,
    ((1, 2), (2, 1)): q**2*(q-1)/2,
    ((1, 4),): q,
    ((2, 1), (2, 1)): q*(q-1)*(q-2)*(q+1)/8,
    ((2, 2),): q*(q-1)/2,
    ((4, 1),): q**2*(q-1)*(q+1)/4,
}


def residue_shape(coeffs, p):
    """Factorization shape of a monic polynomial over F_p."""
    x = sp.symbols("x")
    poly = x**4 + sum((coeffs[i] % p) * x**i for i in range(4))
    factors = sp.factor_list(sp.Poly(poly, x, modulus=p), modulus=p)[1]
    return tuple(sorted((fac.degree(), exponent) for fac, exponent in factors))


print("=" * 76)
print("LEG B — complete F_p residue-genre census")
print("=" * 76)
chk("B0: the eleven symbolic genre counts sum to q^4",
    sp.cancel(sum(GENRE_COUNTS.values()) - q**4) == 0)
for p in [2, 3, 5, 7]:
    counts = Counter(residue_shape(cs, p) for cs in itertools.product(range(p), repeat=4))
    expected = {t: int(sp.cancel(c.subs(q, p))) for t, c in GENRE_COUNTS.items()}
    chk(f"B1: all {p**4} monic quartics over F_{p} hit the exact table",
        counts == Counter(expected), str(dict(sorted(counts.items()))))


def union_types(a, b):
    return tuple(sorted(a + b))


def assemble_one_pattern(pattern):
    dist = {(): sp.Integer(1)}
    for delta, multiplicity in pattern:
        if multiplicity == 1:
            child = {((1, delta),): sp.Integer(1)}
        else:
            child = E.beta_scaled(multiplicity, delta)
        nxt = defaultdict(lambda: sp.Integer(0))
        for t0, p0 in dist.items():
            for t1, p1 in child.items():
                nxt[union_types(t0, t1)] += p0 * p1
        dist = dict(nxt)
    return dist


print("=" * 76)
print("LEG C — eleven-genre cluster assembly")
print("=" * 76)
assembled = defaultdict(lambda: sp.Integer(0))
for pattern, count in GENRE_COUNTS.items():
    dist = assemble_one_pattern(pattern)
    chk(f"C1: conditional law for residue genre {pattern} sums to one",
        sp.cancel(sum(dist.values()) - 1) == 0)
    for typ, prob in dist.items():
        assembled[typ] += count * prob / q**4
assembled = {t: sp.cancel(v) for t, v in assembled.items()}
engine = E.alpha_full(4)
chk("C2: independent eleven-row assembly has exactly eleven output types",
    set(assembled) == set(TYPES))
chk("C3: independent assembly equals the displayed table term-by-term",
    all(sp.cancel(assembled[t] - R[t]) == 0 for t in TYPES))
chk("C4: independent assembly equals om_density_engine.alpha_full(4)",
    set(engine) == set(TYPES) and all(sp.cancel(engine[t] - R[t]) == 0 for t in TYPES))


print("=" * 76)
print("LEG D — decorrelated PARI/GP factorization check")
print("=" * 76)
GP = os.path.expanduser("~/.local/bin/gp")


def pari_types(polys, p):
    lines = ["default(parisize, 256*1024*1024);"]
    for coeffs in polys:
        poly = "+".join(f"({c})*x^{i}" for i, c in enumerate(coeffs))
        lines.append(
            "my(f=%s,out=List(),fa=factor(f)[,1]);"
            "for(i=1,#fa,my(g=fa[i]);"
            "if(poldegree(g)==1,listput(out,[1,1]),"
            "my(K=nfinit([g,[%d]]),dec=idealprimedec(K,%d));"
            "for(j=1,#dec,listput(out,[dec[j].e,dec[j].f]))));"
            "print(Vec(out));" % (poly, p, p))
    run = subprocess.run([GP, "-q", "-f"], input="\n".join(lines) + "\nquit;\n",
                         capture_output=True, text=True, timeout=1200)
    if run.returncode != 0:
        raise RuntimeError(run.stderr[:2000])
    out = []
    for line in run.stdout.splitlines():
        line = line.strip()
        if not line.startswith("["):
            continue
        pairs = []
        for token in line.strip("[]").replace("[", "").split("]"):
            token = token.strip().strip(",").strip()
            if token:
                pairs.append(tuple(int(x) for x in token.split(",")))
        out.append(tuple(sorted(pairs)))
    return out


rng = random.Random(20260828)
M = 800 if FAST else 2400
for p in [2, 3, 5, 7]:
    height = p**10
    polys = [[rng.randrange(height) for _ in range(4)] + [1] for _ in range(M)]
    observed = Counter(pari_types(polys, p))
    ok = True
    detail = []
    for typ in TYPES:
        pred = float(R[typ].subs(q, p))
        obs = observed[typ] / M
        sd = (pred * (1 - pred) / M) ** 0.5
        ok = ok and abs(obs - pred) <= 4 * sd + 3 / M
        detail.append(f"{NAMES[TYPES.index(typ)]}:{obs:.3f}/{pred:.3f}")
    stray = sum(v for typ, v in observed.items() if typ not in R)
    ok = ok and stray <= max(3, M // 500)
    chk(f"D1: PARI quartics at p={p}, every row within 4 sigma", ok,
        " ".join(detail) + f" stray={stray}")


print()
failures = sum(not ok for _, ok in PASS)
print(f"{len(PASS)} checks, {failures} failures")
if failures:
    sys.exit(1)
