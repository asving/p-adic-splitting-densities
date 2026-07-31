#!/usr/bin/env python3
"""O12 REV 3 falsifier checks: the joint count-rationality lemma L6d.

The V9 finding: L6c gives independent column residues (vertices uniform on
F^x, interiors uniform on F, anchor = 1), but adjacent faces SHARE their
vertex coefficients, so the claim that every JOINT residual-shape event has
a probability that is one fixed element of Q(q) -- a ratio of standard
point-count polynomials, uniform over residue characteristics -- was not
proved.  L6d proves it via the fibered product over the shared vertex torus:

  (T1)  for every c in F^x:  #{R : deg R = d, R(0) = c, pattern(R) = rho}
        = P_{d,rho}(q)  (the monic nonzero-constant pattern count),
        INDEPENDENT of c;
  joint count over the anchored chain = prod_j P_{d_j, rho_j}(q).

Checks (all exact, exhaustive; a single mismatch REFUTES L6d):
  A: P_{d,rho}(q) necklace formula vs brute-force monic counts (+ total).
  B: (T1) at EVERY c in F^x, honest enumeration over all leading coeffs.
  C: joint law over anchored chains with SHARED vertices: every joint count
     equals the product formula; empirical shape independence.
  D: nontriviality hook: pointwise conditional counts n(rho; lam, c) VARY
     with (lam, c) in odd characteristic (double-root shape) -- only the
     torus-summed counts are universal.
  E: N_pi(q) (all-monic pattern counts, z allowed) vs brute force
     (feeds row family (ii) of the explicit E(e) table).
"""
import itertools
import json
import math
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = {}
FAILS = []


def chk(name, ok, detail=""):
    print(("PASS  " if ok else "FAIL  ") + name + (" " + detail if detail else ""))
    if not ok:
        FAILS.append(name)


# ---------------------------------------------------------------- GF(p)[z]
# polynomial = tuple of coeffs, ascending powers, last entry nonzero (or ()).

def pmul(a, b, p):
    if not a or not b:
        return ()
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % p
    while out and out[-1] == 0:
        out.pop()
    return tuple(out)


def pdivmod(a, b, p):
    # b monic
    a = list(a)
    db, da = len(b) - 1, len(a) - 1
    if da < db:
        return (), tuple(a)
    q = [0] * (da - db + 1)
    for i in range(da, db - 1, -1):
        c = a[i] % p
        if c:
            q[i - db] = c
            for j in range(db + 1):
                a[i - db + j] = (a[i - db + j] - c * b[j]) % p
    while a and a[-1] == 0:
        a.pop()
    while q and q[-1] == 0:
        q.pop()
    return tuple(q), tuple(a)


def monics(d, p):
    for lows in itertools.product(range(p), repeat=d):
        yield tuple(lows) + (1,)


def irreducibles(p, dmax):
    irr = {D: [] for D in range(1, dmax + 1)}
    for D in range(1, dmax + 1):
        for f in monics(D, p):
            if all(pdivmod(f, g, p)[1] for dd in range(1, D // 2 + 1)
                   for g in irr[dd]):
                irr[D].append(f)
    return irr


def pattern(f, p, irr):
    """factorization pattern of monic f: sorted tuple of (deg, mult)."""
    d = len(f) - 1
    pat = []
    for D in range(1, d + 1):
        for g in irr[D]:
            m = 0
            while True:
                q, r = pdivmod(f, g, p)
                if r:
                    break
                f, m = q, m + 1
            if m:
                pat.append((D, m))
            if len(f) == 1:
                break
        if len(f) == 1:
            break
    assert len(f) == 1, "incomplete factorization"
    return tuple(sorted(pat))


# ------------------------------------------------- the universal polynomials

def mobius(n):
    m, res = n, 1
    for q in range(2, n + 1):
        if q * q > m:
            break
        if m % q == 0:
            m //= q
            if m % q == 0:
                return 0
            res = -res
    if m > 1:
        res = -res
    return res


def necklace(D, q):
    tot = sum(mobius(dd) * q ** (D // dd) for dd in range(1, D + 1) if D % dd == 0)
    assert tot % D == 0
    return tot // D


def falling(M, r):
    out = 1
    for i in range(r):
        out *= (M - i)
    return out


def pattern_count(rho, q, zfree):
    """#{monic with pattern rho}, constant term nonzero iff zfree."""
    byD = {}
    for (D, m) in rho:
        byD.setdefault(D, []).append(m)
    out = Fraction(1)
    for D, ms in byD.items():
        M = necklace(D, q)
        if D == 1 and zfree:
            M -= 1
        r = len(ms)
        sym = 1
        for m in set(ms):
            sym *= math.factorial(ms.count(m))
        out *= Fraction(falling(M, r), sym)
    assert out.denominator == 1
    return int(out)


def P_drho(d, rho, q):
    return pattern_count(rho, q, zfree=True)


# ------------------------------------------------------------------ CHECK A

def check_A():
    ok = True
    cases = []
    for p in (2, 3, 5, 7, 11, 13):
        for d in (1, 2, 3, 4):
            if d == 4 and p > 7:
                continue
            irr = IRR[p]
            counts = {}
            for f in monics(d, p):
                if f[0] == 0:
                    continue
                counts[pattern(f, p, irr)] = counts.get(pattern(f, p, irr), 0) + 1
            good = all(P_drho(d, rho, p) == c for rho, c in counts.items())
            # every z-free pattern predicted nonzero must occur
            tot = sum(counts.values())
            good = good and tot == p ** d - p ** (d - 1)
            ok = ok and good
            cases.append(dict(p=p, d=d, npat=len(counts), ok=good))
    chk("CHECK A: P_{d,rho} necklace formula = brute-force monic z-free "
        "pattern counts, p in {2..13}, d <= 4, incl. totals", ok)
    return dict(ok=ok, cases=cases)


# ------------------------------------------------------------------ CHECK B

def check_B():
    ok = True
    cases = []
    for p in (2, 3, 5, 7):
        for d in (1, 2, 3):
            irr = IRR[p]
            # counts[(c)][rho] over ALL R with deg=d (lead in F^x), R(0)=c
            counts = {c: {} for c in range(1, p)}
            for lead in range(1, p):
                for mid in itertools.product(range(p), repeat=d - 1):
                    for c in range(1, p):
                        R = (c,) + mid + (lead,)
                        # monic normalization for pattern
                        linv = pow(lead, p - 2, p) if p > 2 else 1
                        S = tuple(x * linv % p for x in R)
                        rho = pattern(S, p, irr)
                        counts[c][rho] = counts[c].get(rho, 0) + 1
            good = all(cnt == P_drho(d, rho, p)
                       for c in counts for rho, cnt in counts[c].items())
            ok = ok and good
            cases.append(dict(p=p, d=d, ok=good))
    chk("CHECK B: (T1) fixed constant c, lead summed over F^x = P_{d,rho}"
        " for EVERY c (incl. the anchor c=1), p <= 7, d <= 3", ok)
    return dict(ok=ok, cases=cases)


# ------------------------------------------------------------------ CHECK C

def check_C():
    ok = True
    cases = []
    plans = [((2, 2), (2, 3, 5, 7, 11, 13)),
             ((2, 1), (2, 3, 5, 7)),
             ((1, 2), (2, 3, 5, 7)),
             ((2, 3), (2, 3, 5, 7)),
             ((3, 2), (2, 3, 5, 7)),
             ((2, 2, 2), (2, 3, 5, 7))]
    for degs, ps in plans:
        k = len(degs)
        for p in ps:
            irr = IRR[p]
            joint = {}
            marg = [dict() for _ in range(k)]
            tot = 0
            ivars = sum(d - 1 for d in degs)
            for V in itertools.product(range(1, p), repeat=k):
                Vfull = list(V) + [1]  # anchor
                for w in itertools.product(range(p), repeat=ivars):
                    pos = 0
                    rhos = []
                    for j, d in enumerate(degs):
                        mid = w[pos:pos + d - 1]
                        pos += d - 1
                        R = (Vfull[j + 1],) + tuple(mid) + (Vfull[j],)
                        lead = R[-1]
                        linv = pow(lead, p - 2, p) if p > 2 else 1
                        S = tuple(x * linv % p for x in R)
                        rhos.append(pattern(S, p, irr))
                    key = tuple(rhos)
                    joint[key] = joint.get(key, 0) + 1
                    for j in range(k):
                        marg[j][rhos[j]] = marg[j].get(rhos[j], 0) + 1
                    tot += 1
            # (1) every joint count = product formula
            good = all(cnt == math.prod(P_drho(degs[j], key[j], p)
                                        for j in range(k))
                       for key, cnt in joint.items())
            # completeness: the formula predicts the same support size
            pred = 1
            for j in range(k):
                pred *= (p ** degs[j] - p ** (degs[j] - 1))
            good = good and sum(joint.values()) == tot == pred
            # (2) independence: joint prob = product of empirical marginals
            good = good and all(
                Fraction(cnt, tot) == math.prod(
                    Fraction(marg[j][key[j]], tot) for j in range(k))
                for key, cnt in joint.items())
            ok = ok and good
            cases.append(dict(degs=list(degs), p=p, njoint=len(joint), ok=good))
    chk("CHECK C: joint shape law over anchored shared-vertex chains = "
        "prod_j P_{d_j,rho_j}(q), and shape events independent "
        "(chains up to (2,2,2), p up to 13)", ok)
    return dict(ok=ok, cases=cases)


# ------------------------------------------------------------------ CHECK D

def check_D():
    ok = True
    details = []
    rho_dbl = ((1, 2),)
    for p in (2, 3, 5, 7):
        irr = IRR[p]
        vals = set()
        for lead in range(1, p):
            for c in range(1, p):
                n = 0
                for b in range(p):
                    R = (c, b, lead)
                    linv = pow(lead, p - 2, p) if p > 2 else 1
                    S = tuple(x * linv % p for x in R)
                    if pattern(S, p, irr) == rho_dbl:
                        n += 1
                vals.add(n)
        if p == 2:
            good = vals == {1}          # char 2: squaring bijective
        else:
            good = vals == {0, 2}       # 1 + chi(c/lead) in {0, 2}
        ok = ok and good
        details.append(dict(p=p, vals=sorted(vals), ok=good))
    chk("CHECK D: pointwise conditional double-root counts VARY with the "
        "shared vertex pair in odd char ({0,2}), constant in char 2 ({1}) "
        "-- the torus sum is doing real work", ok)
    return dict(ok=ok, details=details)


# ------------------------------------------------------------------ CHECK E

def check_E():
    ok = True
    cases = []
    for p in (2, 3, 5, 7):
        for d in (2, 3, 4):
            if d == 4 and p > 5:
                continue
            irr = IRR[p]
            counts = {}
            for f in monics(d, p):
                counts[pattern(f, p, irr)] = counts.get(pattern(f, p, irr), 0) + 1
            good = all(pattern_count(rho, p, zfree=False) == c
                       for rho, c in counts.items())
            good = good and sum(counts.values()) == p ** d
            ok = ok and good
            cases.append(dict(p=p, d=d, ok=good))
    chk("CHECK E: N_pi all-monic pattern counts (z allowed) match the "
        "necklace formula (feeds E(e) row family (ii))", ok)
    return dict(ok=ok, cases=cases)


# ---------------------------------------------------------------------------

IRR = {}

def main():
    print("=" * 72)
    print("O12 REV 3 falsifier checks: L6d joint count-rationality")
    print("=" * 72)
    for p in (2, 3, 5, 7, 11, 13):
        IRR[p] = irreducibles(p, 4)
    RESULTS["A"] = check_A()
    RESULTS["B"] = check_B()
    RESULTS["C"] = check_C()
    RESULTS["D"] = check_D()
    RESULTS["E"] = check_E()
    RESULTS["fails"] = FAILS
    with open(os.path.join(HERE, "O12_rev3_results.json"), "w") as fh:
        json.dump(RESULTS, fh, indent=1, default=str)
    print("=" * 72)
    print("ALL PASS -- zero findings" if not FAILS
          else "FAILURES: " + ", ".join(FAILS))
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
