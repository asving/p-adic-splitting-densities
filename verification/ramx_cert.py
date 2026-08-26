#!/usr/bin/env python3
"""ramx_cert.py — unit MRAMX examples-first certificate (2026-08-26).

Certifies the completion-free RAMIFIED LEVEL-1 NORM EXACTNESS formula at a frame key
(the B53b analogue one level up; BLOCKERS_PLAN_2026-08-26.md F2.3-F2.6):

    v( N_{O[x]/(K)} (A0 mod K) )  =  f1 * stageHeight(A0)      (*)

for K a KeyFrame key over a DVR O = Z_(p): K monic of degree D' = e1*f1, x-polygon
one-sided of slope h/e1 (gcd(h,e1)=1, both endpoints ON the side = IsPure), residual
polynomial psi irreducible of degree f1 over F_p, and A0 != 0 with deg A0 < D'.

    stageHeight(A0) = min_j ( e1*v_p(a_j) + h*j )        (C.02 / suppVal X A0 h e1)

The norm is computed two independent ways: Res(K, A0) (monic K: Res(K,A0) = prod A0(beta_i)
= Norm) and det of the multiplication-by-A0 matrix on the power basis of Z[x]/(K).

Batteries (positive): (p,e1,h,f1) = (2,2,1,1), (2,2,1,2), (2,3,2,1), (3,2,1,2), (5,1,1,2),
plus the degenerate (2,1,0,2) unramified sanity row (= landed B53c regime).
NEGATIVE control: (3,1,1,2) with RESIDUAL psi = y^2+2 = (y-1)(y+1) REDUCIBLE over F_3
(K = x^2+18: irreducible over Q, pure, coprime — ONLY hresirr fails): the formula must
FAIL for some A0, certifying that residual irreducibility is the load-bearing hypothesis.

Exit 0 iff every positive check passes AND the negative control exhibits a violation.
"""

import sys
from itertools import product
from sympy import Poly, symbols, resultant, Matrix, ZZ, rem

x = symbols('x')

def vp(n, p):
    """p-adic valuation of a nonzero integer; None for 0 (= +infinity)."""
    n = int(n)
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def stage_height(coeffs, p, e1, h):
    """min_j (e1*v_p(a_j) + h*j) over nonzero coefficients; coeffs[j] = a_j. None if A0=0."""
    best = None
    for j, a in enumerate(coeffs):
        v = vp(a, p)
        if v is None:
            continue
        w = e1 * v + h * j
        if best is None or w < best:
            best = w
    return best

def norm_via_det(Kc, A0c):
    """det of multiplication-by-A0 on the power basis of Z[x]/(K), K monic (coeff lists,
    ascending). Independent cross-check of the resultant route."""
    D = len(Kc) - 1
    K = Poly(list(reversed(Kc)), x)
    cols = []
    for j in range(D):
        # A0 * x^j mod K
        pj = Poly([c for c in reversed(A0c)], x) * Poly([1] + [0]*j, x)
        r = pj.rem(K)
        rc = list(reversed(r.all_coeffs())) if r.all_coeffs() != [0] else [0]
        rc = rc + [0]*(D - len(rc))
        cols.append(rc[:D])
    M = Matrix(D, D, lambda i, j: cols[j][i])
    return M.det()

def check_battery(name, p, e1, h, f1, Kc, coeff_grid, expect_violation=False):
    """Kc: ascending coefficient list of K.  Enumerates A0 over coeff_grid^(D') minus 0.
    Returns (n_checked, n_holds, n_fails, example_fail)."""
    D = e1 * f1
    assert len(Kc) == D + 1 and Kc[-1] == 1, "K must be monic of degree D'"
    # purity audit of K itself: every weight >= h*D', endpoints exact
    wts = []
    for a, c in enumerate(Kc):
        v = vp(c, p)
        if v is not None:
            wts.append((a, e1 * v + h * a))
    wmin = min(w for _, w in wts)
    assert wmin == h * D, f"{name}: key not of slope h/e1 (min weight {wmin} != {h*D})"
    assert dict(wts).get(0) == h * D, f"{name}: left endpoint off the side (v(c0) != h*f1)"
    Kpoly = Poly(list(reversed(Kc)), x)
    n_checked = n_holds = n_fails = 0
    example_fail = None
    for tup in product(coeff_grid, repeat=D):
        if all(c == 0 for c in tup):
            continue
        s = stage_height(tup, p, e1, h)
        A0 = Poly(list(reversed(tup)), x)
        R = resultant(Kpoly, A0)
        vR = vp(R, p)
        assert vR is not None, f"{name}: resultant vanished at {tup} (K reducible or A0 mult.)"
        # independent determinant cross-check (norm = Res(K, A0) for monic K)
        Ndet = norm_via_det(Kc, list(tup))
        assert abs(int(Ndet)) == abs(int(R)), f"{name}: det/resultant mismatch at {tup}"
        n_checked += 1
        if vR == f1 * s:
            n_holds += 1
        else:
            n_fails += 1
            if example_fail is None:
                example_fail = (tup, vR, f1 * s)
    tag = "NEGATIVE-CONTROL" if expect_violation else "POSITIVE"
    ok = (n_fails == 0) if not expect_violation else (n_fails > 0)
    print(f"[{tag}] {name}: p={p} (e1,h,f1)=({e1},{h},{f1}) K={Kc} | "
          f"checked={n_checked} holds={n_holds} fails={n_fails} "
          f"{'OK' if ok else '*** FAIL ***'}")
    if example_fail:
        t, vR, rhs = example_fail
        print(f"    first violation: A0 coeffs (asc) {t}: v(N)={vR} vs f1*s={rhs}")
    return ok

def main():
    grids = {
        2: [0, 1, 2, 3, 4, 6, 8, 12],
        3: [0, 1, 2, 3, 6, 9, 18, 27],
        5: [0, 1, 2, 5, 10, 25, 50],
    }
    small2 = [0, 1, 2, 3, 4, 6, 8]           # deg-3 enum at p=2: 7^4 - 1 cases
    ok = True
    # 1. Eisenstein, totally ramified: K = x^2 - 2, psi = y - 1 (f1=1)
    ok &= check_battery("eisenstein-x2-2", 2, 2, 1, 1, [-2, 0, 1], grids[2])
    # 1b. Eisenstein variant with off-side middle coefficient: K = x^2 + 2x + 2? weight
    #     of a=1 term: 2*1+1=3 >= 2 OK (above side): pure, psi = y+1
    ok &= check_battery("eisenstein-x2+2x+2", 2, 2, 1, 1, [2, 2, 1], grids[2])
    # 2. Ramified WITH residue: K = x^4 + 2x^2 + 4, psi = y^2+y+1 irreducible /F_2
    ok &= check_battery("ram-res-x4+2x2+4", 2, 2, 1, 2, [4, 0, 2, 0, 1], small2)
    # 3. Slope 2/3: K = x^3 - 4, psi = y - 1 (f1=1)
    ok &= check_battery("slope23-x3-4", 2, 3, 2, 1, [-4, 0, 0, 1], grids[2])
    # 4. p=3 ramified with residue: K = x^4 + 3x^2 + 18, psi = y^2+y+2 irreducible /F_3
    ok &= check_battery("p3-x4+3x2+18", 3, 2, 1, 2, [18, 0, 3, 0, 1], [0, 1, 2, 3, 6, 9])
    # 5. Unramified-with-slope sanity e1=1, h=1: K = x^2 + 5x + 10?? need psi irr /F_5:
    #    weights (e1=1,h=1): a=0: v(10)=1+0=1... h*D'=2. Use K = x^2+5x+50: a=0: v=2+0=2,
    #    a=1: 1+1=2, a=2: 0+2=2; psi = y^2 + y + 2 over F_5 (disc 1-8=-7=3 nonsquare /F_5)
    ok &= check_battery("p5-e1-h1-f2", 5, 1, 1, 2, [50, 5, 1], grids[5])
    # 6. Degenerate h=0 (unramified, landed B53c regime): K = x^2+x+1 over Z_(2)
    ok &= check_battery("degenerate-h0", 2, 1, 0, 2, [1, 1, 1], grids[2])
    # NEGATIVE control: psi reducible (only hresirr fails): K = x^2 + 18 over Z_(3),
    # psi = y^2 + 2 = (y-1)(y+1) /F_3.  K irreducible over Q, pure of slope 1/1, coprime.
    ok &= check_battery("NEG-reducible-psi", 3, 1, 1, 2, [18, 0, 1], grids[3],
                        expect_violation=True)
    print()
    if ok:
        print("ALL CERT CHECKS PASS (positive batteries exact; negative control violated).")
        return 0
    print("CERT FAILURE — see rows above.")
    return 1

if __name__ == "__main__":
    sys.exit(main())
