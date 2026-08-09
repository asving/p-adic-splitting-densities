#!/usr/bin/env python3
"""TAMEK post-seal leg (disclosed; written AFTER the sealed scoring run, in response to
the P5/P4b refutation of CONJ-MEAN): EXACT finite-n mean E[X_K](n) for UNRAMIFIED K,
via the S5 Euler-product mean telescope (BCFGTIE Lemma A/B/C generalized over the
divisor tower), pure Fractions. Predictions compared to the sealed MC records at every
measured n, and the n -> infinity limit = the CORRECTED law
      E[X_K^unram]_inf = sum over residue points abar of F_{q^f} of 1/(q^deg(abar)+1).
"""
import json, math, sys, os
from fractions import Fraction
from functools import lru_cache

def P_mj(q, m, j):
    """BCFGTIE Lemma C deep-count law P_m(j), exact."""
    if m == 0: return Fraction(1) if j == 0 else Fraction(0)
    if m == 1: return Fraction(1) if j == 1 else Fraction(0)
    if j == m: return Fraction(1, q**(m*(m-1)//2))
    if j > m or j < 0 or j == m-1: return Fraction(0)
    tot = Fraction(0)
    for mu in range(j+1, m):
        E = (mu-j-1) + j*(mu-1) - j*(j-1)//2 + (mu-1-j)*(mu-j)//2
        tot += Fraction(q-1, q) * Fraction(1, q**E)
    return tot

def n_points(q, d):
    """# closed points of degree d on A^1_{F_q} = # monic irreducibles of degree d."""
    tot = q**d
    for dd in range(1, d):
        if d % dd == 0:
            tot -= dd * n_points(q, dd)
    return tot // d

@lru_cache(maxsize=None)
def E_mean(q, f, n):
    """E[X_K](n) for K unramified of degree f over F with residue size q, monic model.
    The deep self-loop (rational point of full multiplicity n, all-deep re-entry) is
    solved as the linear fixed point: E(n) = S/(1 - q^{1-n} q^{-n(n-1)/2})."""
    if n <= 0: return Fraction(0)
    if n == 1: return Fraction(1)          # linear polynomial: one root, in F <= K
    S = Fraction(0)
    for d in [dd for dd in range(1, f+1) if f % dd == 0]:
        Nd = n_points(q, d)
        block = Fraction(0)
        for m in range(1, n//d + 1):
            if d*(m+1) <= n:
                w = Fraction(1, q**(d*m)) * (1 - Fraction(1, q**d))
            else:
                w = Fraction(1, q**(d*m))
            top = m if not (d == 1 and m == n) else m - 1   # exclude self term j=m=n
            qp, fpp = q**d, f//d
            block += w * d * sum(P_mj(qp, m, j) * E_mean(qp, fpp, j)
                                 for j in range(0, top+1))
        S += Nd * block
    selfcoef = Fraction(q, q**n) * Fraction(1, q**(n*(n-1)//2))
    return S / (1 - selfcoef)

def limit_law(q, f):
    return sum(Fraction(dd * n_points(q, dd), q**dd + 1)
               for dd in range(1, f+1) if f % dd == 0)

if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    R = json.load(open(os.path.join(here, "tamek_results.json")))
    def mean_se(r):
        N = r["nsamp"]; mu = sum(int(k)*v for k, v in r["hist"].items())/N
        var = sum((int(k)-mu)**2*v for k, v in r["hist"].items())/(N-1)
        return mu, math.sqrt(var/N)
    fails = 0
    for r in R["mc"]:
        p, e, f, c = r["cell"]
        if e != 1 or f == 1: continue
        m, se = mean_se(r)
        ex = E_mean(p, f, r["n"])
        dev = (m - float(ex))/se
        okk = abs(dev) <= 5
        fails += 0 if okk else 1
        print("%s cell(%d,1,%d) n=%d mc=%.4f exact=%.6f (%s) dev=%+.1f sigma"
              % ("PASS" if okk else "FAIL", p, f, r["n"], m, float(ex), ex, dev))
    for (q, f) in [(3,2),(3,3),(5,2),(7,2)]:
        lim = limit_law(q, f)
        seq = [float(E_mean(q, f, n)) for n in range(2, 13)]
        print("q=%d f=%d: E(n) n=2..12 -> %s ; limit = %s = %.6f"
              % (q, f, " ".join("%.4f" % x for x in seq), lim, float(lim)))
    print("FAILS:", fails)
    sys.exit(0 if fails == 0 else 1)
