#!/usr/bin/env python3
"""O12 REV 4 falsifier checks: L6e (a.e. exhaustion) + the O2 allocation datum.

V13 findings being repaired:
  (3) The polygon-cell exhaustion of C_e \\ R_e is only valid up to a null
      set: a coefficient can be 0 (valuation +infinity), and if a_e = 0 the
      finite Newton polygon does not begin at column 0, so the polynomial
      lies in NO admissible L6 cell.  New Lemma L6e states the EXACT
      partition:  (C_e \\ R_e) \\ Z_e = disjoint union of the admissible
      cells, with Z_e := (C_e \\ R_e) & {a_e = 0} Haar-null (and Z_2 empty).
  (1) The (O2) booking's kappa_1 mass is now distributed by a fully
      displayed ALLOCATION DATUM alpha_e : verdicts -> Q[q] with
      sum_sigma alpha_e(sigma) = q - 1; each verdict row gains
      alpha_e(sigma) * q^{-E}.  The degree-2 concrete table is the member
      alpha_2 = (0, q-1).

Checks (exact; a single mismatch REFUTES L6e resp. the datum's grammar):
  F: over exact integer lifts of (Z/p^M)^e -- genuine polynomials over Z_p
     -- the FULL trichotomy: every tuple in C\\R with a_e != 0 has an
     admissible hull (starts at column 0, integral vertex heights, strictly
     decreasing positive slopes, min slope in (0,1), b_k >= 2, b_j | L_j)
     and satisfies its own cell's conditions; every tuple with a_e = 0 (and
     every tuple outside C\\R) lies in NO cell; for e <= 3 the membership
     count over an INDEPENDENTLY enumerated admissible-P list is exactly
     1 on (C\\R) & {a_e != 0} and 0 elsewhere; #Z_e matches the exact
     volume identity p^{(e-1)M} * (p^{-(e-1)} - p^{-e(e-1)/2}); Z_2 = 0.
  G: allocation-datum algebra at e = 2 (E = 3), symbolic: alpha = (0, q-1)
     reproduces the section-7 machine-checked table EXACTLY; a battery of
     other Q[q] allocations (including q-2 weights, rational-coefficient
     and high-degree weights) keeps every adjusted row t_sigma and solved
     entry x_sigma with reduced denominator dividing q^5 (q^3-1)^2 (an
     R-shape), and the mass identity sum x = 1 holds whenever
     sum alpha = q - 1.
"""
import json
import math
import os
import sys
from fractions import Fraction
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
_USER_SITE = os.path.expanduser("~/.local/lib/python3.10/site-packages")
if os.path.isdir(_USER_SITE) and _USER_SITE not in sys.path:
    sys.path.append(_USER_SITE)
import sympy as sp

RESULTS = {}
FAILS = []
INF = None  # valuation of 0


def chk(name, ok, detail=""):
    print(("PASS  " if ok else "FAIL  ") + name + (" " + detail if detail else ""))
    if not ok:
        FAILS.append(name)


def vp(x, p):
    if x == 0:
        return INF
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def geq(v, t):
    return True if v is INF else v >= t


def lower_hull(pts):
    """Lower convex hull (monotone chain) of points sorted by x, one per x."""
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # drop hull[-1] if it is above or on segment hull[-2]->pt
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull


def heights(hull, e):
    """H(i) for i = 0..e as Fractions; None left of the first hull vertex."""
    hs = [None] * (e + 1)
    for (xa, ya), (xb, yb) in zip(hull, hull[1:]):
        for i in range(xa, xb + 1):
            hs[i] = Fraction(ya) + Fraction(yb - ya, xb - xa) * (i - xa)
    if len(hull) == 1:
        hs[hull[0][0]] = Fraction(hull[0][1])
    return hs


def faces_of(hull):
    """[(L_j, s_j)] with s_j = -slope, left to right."""
    return [(xb - xa, Fraction(ya - yb, xb - xa))
            for (xa, ya), (xb, yb) in zip(hull, hull[1:])]


def admissible(faces, e):
    """L6 admissibility of a face list; returns (ok, why)."""
    if sum(L for L, _ in faces) != e:
        return False, "sum L != e"
    prev = None
    for L, s in faces:
        if s <= 0:
            return False, "slope <= 0"
        if prev is not None and not s < prev:
            return False, "slopes not strictly decreasing"
        if L % s.denominator != 0:
            return False, "b does not divide L"
        prev = s
    sk = faces[-1][1]
    if not (0 < sk < 1):
        return False, "min slope not in (0,1)"
    if sk.denominator < 2:
        return False, "b_k < 2"
    return True, ""


def cell_of_P(faces, e):
    """From an admissible face list, the cell data:
    (ceil heights h*_i for i=0..e-1, vertex column set, integral check)."""
    hs = [Fraction(0)] * (e + 1)
    x = e
    for L, s in reversed(faces):
        for t in range(1, L + 1):
            hs[x - t] = hs[x] + s * t
        x -= L
    assert x == 0
    verts = set()
    c = 0
    for L, _ in faces:
        verts.add(c)
        c += L
    ok_int = all(hs[i].denominator == 1 for i in verts)
    return hs, verts, ok_int


def in_cell(vv, hs, verts, e):
    """vv[i] = valuation at column i (v(a_{e-i})), i = 0..e-1."""
    for i in range(e):
        hce = -(-hs[i].numerator // hs[i].denominator)  # ceil
        if i in verts:
            if vv[i] is INF or vv[i] != hs[i]:
                return False
        elif not geq(vv[i], hce):
            return False
    return True


def enumerate_P(e, hmax):
    """All admissible P (face lists [(L, s)]) with h_0 <= hmax."""
    def compositions(n):
        if n == 0:
            yield []
            return
        for first in range(1, n + 1):
            for rest in compositions(n - first):
                yield [first] + rest
    out = []
    for Ls in compositions(e):
        k = len(Ls)
        bchoices = []
        for j, L in enumerate(Ls):
            divs = [b for b in range(1, L + 1) if L % b == 0]
            if j == k - 1:
                divs = [b for b in divs if b >= 2]
            bchoices.append(divs)
        for bs in product(*bchoices):
            # slope tuples right-to-left: s_k in (0,1), then s_j > s_{j+1}
            def slopes(j, lo):
                if j < 0:
                    yield []
                    return
                b = bs[j]
                a = lo.numerator * b // lo.denominator + 1
                while Fraction(a, b) <= lo:
                    a += 1
                while Fraction(a, b) * (Ls[j] // b) <= hmax:
                    if math.gcd(a, b) == 1:
                        if j == k - 1 and not Fraction(a, b) < 1:
                            break
                        for pre in slopes(j - 1, Fraction(a, b)):
                            yield pre + [Fraction(a, b)]
                    a += 1
            for ss in slopes(k - 1, Fraction(0)):
                faces = list(zip(Ls, ss))
                h0 = sum(s * L for L, s in faces)
                if h0 <= hmax and admissible(faces, e)[0]:
                    out.append(faces)
    return out


def check_F():
    cases = []
    for (e, p, M) in [(2, 2, 7), (2, 3, 5), (3, 2, 6), (3, 3, 4), (4, 2, 4)]:
        E = e * (e + 1) // 2
        Plist = enumerate_P(e, M - 1) if e <= 3 else None
        Pcells = ([cell_of_P(f, e) for f in Plist] if Plist is not None
                  else None)
        if Pcells is not None and not all(okI for _, _, okI in Pcells):
            chk(f"F(e={e},p={p},M={M}) integral vertex heights", False)
            continue
        nC = nR = nZ = 0
        bad = 0
        for a in product(range(p ** M), repeat=e):
            va = [vp(x, p) for x in a]           # v(a_1), ..., v(a_e)
            if not all(geq(v, 1) for v in va):
                inC = False
            else:
                inC = True
            inR = inC and all(geq(v, i + 1) for i, v in enumerate(va))
            if inC:
                nC += 1
            if inR:
                nR += 1
            inCR = inC and not inR
            # vv[i] = valuation at diagram column i, which carries a_{e-i}
            vv = [va[e - 1 - i] for i in range(e)]
            expect = 0
            if inCR and a[e - 1] != 0:
                expect = 1
                pts = [(i, vv[i]) for i in range(e) if vv[i] is not INF]
                pts.append((e, 0))
                hull = lower_hull(pts)
                faces = faces_of(hull)
                okA, why = admissible(faces, e)
                if not (okA and hull[0][0] == 0):
                    bad += 1
                    continue
                hs, verts, okI = cell_of_P(faces, e)
                if not (okI and in_cell(vv, hs, verts, e)
                        and hs[0] == vv[0] and geq(vv[0], 1)):
                    bad += 1
                    continue
            if inCR and a[e - 1] == 0:
                nZ += 1
            if Pcells is not None and inC:
                nmatch = sum(1 for hs, verts, _ in Pcells
                             if in_cell(vv, hs, verts, e))
                if nmatch != expect:
                    bad += 1
        Zpred = (p ** ((e - 1) * M) * (Fraction(1, p ** (e - 1))
                 - Fraction(1, p ** (e * (e - 1) // 2))))
        okZ = Fraction(nZ) == Zpred and (e != 2 or nZ == 0)
        okC = nC == p ** (e * (M - 1)) and nR == p ** (e * M - E)
        chk(f"F(e={e},p={p},M={M})", bad == 0 and okZ and okC,
            f"C\\R trichotomy exact; #Z={nZ} (predicted {Zpred}); "
            f"{'membership counts vs ' + str(len(Plist)) + ' enumerated P; ' if Plist is not None else 'own-hull checks only; '}"
            f"#C={nC} #R={nR}")
        cases.append(dict(e=e, p=p, M=M, nC=nC, nR=nR, nZ=nZ,
                          Zpred=str(Zpred), bad=bad,
                          nP=(len(Plist) if Plist is not None else None)))
    return cases


def check_G():
    q = sp.symbols('q')
    E = 3
    kappa0 = q ** -E
    s_base = [1 - 1 / q, 1 / q - 1 / q ** 2]
    battery = [
        ("(0, q-1)  [the concrete degree-2 member]", [sp.Integer(0), q - 1]),
        ("(q-1, 0)", [q - 1, sp.Integer(0)]),
        ("(1, q-2)", [sp.Integer(1), q - 2]),
        ("(q-2, 1)", [q - 2, sp.Integer(1)]),
        ("((q-1)/2, (q-1)/2)", [(q - 1) / 2, (q - 1) / 2]),
        ("(q, -1)", [q, sp.Integer(-1)]),
        ("(q^3, q-1-q^3)", [q ** 3, q - 1 - q ** 3]),
    ]
    Rtest = q ** 5 * (q ** 3 - 1) ** 2
    allok = True
    details = []
    for name, alpha in battery:
        ok = sp.simplify(sum(alpha) - (q - 1)) == 0
        t = [sp.cancel(s + al * q ** -E) for s, al in zip(s_base, alpha)]
        x = [sp.cancel(ti / (1 - kappa0)) for ti in t]
        for f in t + x:
            den = sp.fraction(sp.cancel(f))[1]
            _, rem = sp.div(Rtest, den, q)
            ok = ok and rem == 0
        ok = ok and sp.simplify(sum(x) - 1) == 0
        if name.startswith("(0, q-1)"):
            ok = ok and sp.simplify(t[0] - (1 - 1 / q)) == 0
            ok = ok and sp.simplify(t[1] - (1 / q - q ** -3)) == 0
            ok = ok and sp.simplify(x[0] - q ** 2 / (q ** 2 + q + 1)) == 0
            ok = ok and sp.simplify(x[1] - (q + 1) / (q ** 2 + q + 1)) == 0
        chk(f"G alpha={name}", ok,
            "adjusted rows + solve R-shaped, mass 1"
            + ("; matches section-7 table exactly"
               if name.startswith("(0, q-1)") else ""))
        allok = allok and ok
        details.append(dict(alpha=name, ok=bool(ok)))
    return dict(ok=allok, battery=details)


def main():
    print("=" * 72)
    print("O12 REV 4 falsifier checks: L6e exhaustion + O2 allocation datum")
    print("=" * 72)
    RESULTS["F"] = check_F()
    RESULTS["G"] = check_G()
    RESULTS["fails"] = FAILS
    with open(os.path.join(HERE, "O12_rev4_results.json"), "w") as fh:
        json.dump(RESULTS, fh, indent=1, default=str)
    print("=" * 72)
    print("ALL PASS -- zero findings" if not FAILS
          else "FAILURES: " + ", ".join(FAILS))
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
