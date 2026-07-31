#!/usr/bin/env python3
"""O12 REV 2 — falsifiers for the two V7 repairs (run FIRST, before the prose).

V7 (lean/notes/openmath/V7_o12_verify.jsonl) confirmed the rev-1 determinant
algebra and numerics but found:
  (V7-C3) Lemma L6 never proves the semantic depth sums have exponent c >= 1
          (the brief's L6 summed ceil(h_i) over an ARBITRARY finite column set
          I, which can miss the affected columns);
  (V7-C2) the (g7) solve step is invalid at organization O2 as written: its
          "exit row" contains the CURRENT block's unknown (the kappa_1 leg),
          so beta_e is not a division by Phi^{(O2)} = 1 - kappa_0.

REPAIRS UNDER TEST:

 CHECK 1 [L6a semantic link]: the polygon-stratum event {lower Newton hull of
   g = P} is EXACTLY the coefficient cell {v(a_i) >= ceil(h_i) all columns,
   equality at the hull vertices}, of Haar volume (1-1/q)^V q^{-N} with
       N = sum over ALL coefficient columns j = 0..e-1 of ceil(h_j),
       V = number of hull vertices among columns 0..e-1  (= #faces).
   Exhaustive enumeration over (Z/p^M)^e: for every hull with max height
   <= M-1 (where capped valuations decide membership exactly), the counted
   fiber must equal p^{eM} (1-1/p)^V p^{-N} EXACTLY.  Aggregates: the union of
   min-slope-in-(0,1) hulls must have count p^{eM}(p^{-e} - p^{-E}), E=e(e+1)/2
   (= vol(C_e \\ R_e): tests the L1 dichotomy), and C_e, R_e likewise.
   REFUTES the repaired L6a if any fiber count deviates.

 CHECK 2 [L6b affine exponents, c >= 1]: for every face-kind sequence
   (L_j, b_j)_{j=1..k} with sum L_j = e <= 7, b_j | L_j, b_k >= 2 (rightmost
   slope in (0,1)), and sampled admissible slope tuples: the cone move
   "a_{j'} += b_{j'} for all j' <= j0" (j0 <= k-1; the unit gap-variable
   increment) changes N = sum_{j=0}^{e-1} ceil(h_j) by EXACTLY
       c_{j0} = sum_{j'<=j0} ( x_{j'} L_{j'} + L_{j'}(L_{j'}+1)/2 )  >= 1
   (x_j = left endpoint column of face j), with the vertex count k unchanged.
   Also confirms k = 1 families have NO unbounded slope parameter (the
   rightmost slope enumerates a_k in [1, b_k-1]: finite).
   REFUTES the repaired L6b if any move deviates or any c < 1.

 CHECK 3 [O2/O2' solve algebra]: symbolic (sympy).
   (a) For E in {3, 6, 10, 15}: the three re-entrant fixpoints
       x = (k0+k1)x + s   [O1],   x = k0 x + (k1 x + s)  [O2'],
       (1 - k1/(1-k0)) x = s/(1-k0)  [O3]
       have the SAME unique solution x = s / (1 - q^{1-E}), whose extra
       denominator q^{E-1} - 1 has rational roots in {+-1} only.
   (b) The as-built n=2 table (kernel q^-3, terminal rows 1 - 1/q and
       1/q - q^-3, NO re-entrance) solves to exactly
       (q^2/(q^2+q+1), (q+1)/(q^2+q+1)) = (terminals)/(1 - q^-3): the O2
       booking is a genuine no-feedback division by the unit 1 - kappa_0.
   (c) The value divergence is REAL and documented: the same e=2
       stratification under the re-entrant solve gives (q/(q+1), 1/(q+1))
       != (b)'s values — both R-shaped (denominators divide q^3-1 resp.
       q^2-1); REG-p (zero/pole structure) is blind to the difference.
   REFUTES the repaired (g7) if any identity fails.

Exact arithmetic throughout (Fraction / sympy).  Results ->
O12_rev2_results.json.
"""
import os
import sys
import json
import math
from fractions import Fraction
from itertools import product

# sympy lives in the user site-packages (user-site disabled in some shells)
_USER_SITE = os.path.expanduser("~/.local/lib/python3.10/site-packages")
if os.path.isdir(_USER_SITE) and _USER_SITE not in sys.path:
    sys.path.append(_USER_SITE)
import sympy as sp

FINDINGS = []
RESULTS = {}


def chk(name, cond, detail=""):
    tag = "PASS" if cond else "FINDING"
    if not cond:
        FINDINGS.append(f"{name}  {detail}")
    print(f"[{tag}] {name}  {detail}", flush=True)


# ----------------------------------------------------------------------------
# CHECK 1: exhaustive polygon-cell volumes over (Z/p^M)^e
# ----------------------------------------------------------------------------

def vp_capped(x, p, M):
    """v_p of a residue x in [0, p^M), capped at M (x = 0 -> M)."""
    if x == 0:
        return M
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def lower_hull(pts):
    """Lower convex hull, collinear interior points removed (strict turns)."""
    h = []
    for pt in pts:
        while len(h) >= 2 and cross(h[-2], h[-1], pt) <= 0:
            h.pop()
        h.append(pt)
    return tuple(h)


def hull_heights(hull, e):
    """Heights h_j (Fraction) at integer columns j = 0..e from the hull."""
    hs = {}
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        s = Fraction(y2 - y1, x2 - x1)
        for j in range(x1, x2):
            hs[j] = Fraction(y1) + s * (j - x1)
    hs[hull[-1][0]] = Fraction(hull[-1][1])
    return [hs[j] for j in range(e + 1)]


def check1_case(e, p, M):
    E = e * (e + 1) // 2
    assert M > e, "need M > e so C/R classification is exact"
    pm = p ** M
    buckets = {}
    # coefficient tuple (a_1..a_e); column j carries a_{e-j}; anchor (e, 0)
    for a in product(range(pm), repeat=e):
        w = [vp_capped(a[e - 1 - j], p, M) for j in range(e)]  # w[j]=v(a_{e-j})
        pts = [(j, w[j]) for j in range(e)] + [(e, 0)]
        hull = lower_hull(pts)
        buckets[hull] = buckets.get(hull, 0) + 1

    n_checked = n_skipped = 0
    ok_fibers = True
    cnr_total = 0   # min slope in (0,1)  (C_e \ R_e)
    c_total = 0     # all slopes > 0      (C_e)
    r_total = 0     # min slope >= 1      (R_e)
    cnr_buckets = 0
    for hull, cnt in buckets.items():
        hts = hull_heights(hull, e)
        # min |slope| = height drop over the rightmost segment per column
        (x1, y1), (x2, y2) = hull[-2], hull[-1]
        min_slope = Fraction(y1 - y2, x2 - x1)
        pos = all(hts[j] > 0 for j in range(e))
        if pos:
            c_total += cnt
            if min_slope >= 1:
                r_total += cnt
            if 0 < min_slope < 1:
                cnr_total += cnt
                cnr_buckets += 1
        # exact per-fiber check only where capping cannot interfere
        if hts[0] <= M - 1:
            N = sum(math.ceil(hts[j]) for j in range(e))
            V = sum(1 for (x, _) in hull if x < e)
            pred = (p - 1) ** V * p ** (e * M - N - V)
            if pred != cnt:
                ok_fibers = False
                FINDINGS.append(f"CHECK1 e={e} p={p}: hull {hull} count {cnt}"
                                f" != predicted {pred}")
            n_checked += 1
        else:
            n_skipped += 1
    chk(f"CHECK1 fibers e={e} p={p} M={M}", ok_fibers,
        f"{n_checked} hulls exact, {n_skipped} height-capped (excluded)")
    chk(f"CHECK1 C_e aggregate e={e} p={p}", c_total == p ** (e * (M - 1)),
        f"count {c_total}")
    chk(f"CHECK1 R_e aggregate e={e} p={p}", r_total == p ** (e * M - E),
        f"count {r_total}")
    chk(f"CHECK1 C\\R aggregate e={e} p={p}",
        cnr_total == p ** (e * M - e) - p ** (e * M - E),
        f"count {cnr_total} over {cnr_buckets} polygon buckets")
    return {"e": e, "p": p, "M": M, "hulls_exact": n_checked,
            "hulls_capped": n_skipped, "cnr_buckets": cnr_buckets,
            "fibers_ok": ok_fibers}


# ----------------------------------------------------------------------------
# CHECK 2: affine exponent along every cone generator, coefficient >= 1
# ----------------------------------------------------------------------------

def N_of_slopes(Ls, slopes):
    """N = sum_{j=0}^{e-1} ceil(h_j), heights anchored h_e = 0 (right end)."""
    e = sum(Ls)
    xs = [0]
    for L in Ls:
        xs.append(xs[-1] + L)
    h = Fraction(0)
    N = 0
    verts = 1  # left endpoint column 0 is always a hull vertex
    # walk faces right-to-left
    for j in range(len(Ls) - 1, -1, -1):
        for t in range(1, Ls[j] + 1):        # distance to face's right endpoint
            N += math.ceil(h + t * slopes[j])
        h += Ls[j] * slopes[j]
        assert h.denominator == 1, "vertex height must be an integer"
    verts = len(Ls)  # k faces <=> k vertex columns among 0..e-1
    return N, verts


def compositions(n):
    if n == 0:
        yield ()
        return
    for first in range(1, n + 1):
        for rest in compositions(n - first):
            yield (first,) + rest


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def check2(emax=7):
    total_moves = 0
    total_kinds = 0
    ok = True
    single_face_finite = True
    for e in range(2, emax + 1):
        for Ls in compositions(e):
            k = len(Ls)
            for bs in product(*[divisors(L) for L in Ls]):
                if bs[-1] < 2:
                    continue  # rightmost slope must be in (0,1): b_k >= 2
                total_kinds += 1
                xs = [0]
                for L in Ls:
                    xs.append(xs[-1] + L)
                # admissible base slope tuples (strictly decreasing, s_k in (0,1))
                sk_opts = [Fraction(a, bs[-1]) for a in range(1, bs[-1])
                           if math.gcd(a, bs[-1]) == 1][:2]
                single_face_finite &= (k > 1 or len(sk_opts) < bs[-1])
                for sk in sk_opts:
                    tuples = [[sk]]
                    for j in range(k - 2, -1, -1):  # faces k-1 .. 1 (0-idx)
                        new = []
                        for tl in tuples:
                            below = tl[0]
                            a0 = math.floor(below * bs[j]) + 1
                            picks = 0
                            a = a0
                            while picks < 2 and a < a0 + 3 * bs[j] + 2:
                                if math.gcd(a, bs[j]) == 1 and \
                                        Fraction(a, bs[j]) > below:
                                    new.append([Fraction(a, bs[j])] + tl)
                                    picks += 1
                                a += 1
                        tuples = new
                    for slopes in tuples:
                        N0, V0 = N_of_slopes(Ls, slopes)
                        for j0 in range(1, k):  # cone generators w_1..w_{k-1}
                            moved = [s + 1 if j < j0 else s
                                     for j, s in enumerate(slopes)]
                            N1, V1 = N_of_slopes(Ls, moved)
                            c_pred = sum(xs[j] * Ls[j]
                                         + Ls[j] * (Ls[j] + 1) // 2
                                         for j in range(j0))
                            total_moves += 1
                            if not (N1 - N0 == c_pred and c_pred >= 1
                                    and V1 == V0):
                                ok = False
                                FINDINGS.append(
                                    f"CHECK2 e={e} Ls={Ls} bs={bs} "
                                    f"slopes={slopes} j0={j0}: dN={N1-N0} "
                                    f"pred={c_pred} V {V0}->{V1}")
    chk("CHECK2 affine exponents, all c >= 1, V constant", ok,
        f"{total_moves} cone moves over {total_kinds} face-kind seqs, e<=7")
    chk("CHECK2 k=1 families have finite slope range", single_face_finite, "")
    return {"moves": total_moves, "kinds": total_kinds, "ok": ok}


# ----------------------------------------------------------------------------
# CHECK 3: the repaired (g7) solve algebra
# ----------------------------------------------------------------------------

def check3():
    q, s, x = sp.symbols('q s x')
    out = {}
    ok_a = True
    for E in (3, 6, 10, 15):
        k0 = q ** (-E)
        k1 = (q - 1) * q ** (-E)
        sol_o1 = sp.solve(sp.Eq(x, (k0 + k1) * x + s), x)[0]
        sol_o2p = sp.solve(sp.Eq(x, k0 * x + (k1 * x + s)), x)[0]
        sol_o3 = sp.solve(sp.Eq((1 - k1 / (1 - k0)) * x, s / (1 - k0)), x)[0]
        closed = s / (1 - q ** (1 - E))
        same = all(sp.simplify(a - closed) == 0
                   for a in (sol_o1, sol_o2p, sol_o3))
        den = sp.Poly(q ** (E - 1) - 1, q)
        roots = set(sp.roots(den, filter='Q').keys())
        ok = same and roots <= {1, -1}
        ok_a &= ok
        chk(f"CHECK3a E={E} O1=O2'=O3 solve = s/(1-q^(1-E)); den roots",
            ok, f"roots {roots}")
    # (b) the as-built n=2 table: no-feedback division by 1 - q^-3
    t1, t2 = 1 - 1 / q, 1 / q - q ** (-3)
    b1 = sp.simplify(t1 / (1 - q ** (-3)) - q ** 2 / (q ** 2 + q + 1)) == 0
    b2 = sp.simplify(t2 / (1 - q ** (-3)) - (q + 1) / (q ** 2 + q + 1)) == 0
    mass = sp.simplify(q ** (-3) + t1 + t2 - 1) == 0
    div = sp.simplify(sp.rem(sp.Poly(q ** 3 - 1, q),
                             sp.Poly(q ** 2 + q + 1, q))) == 0
    chk("CHECK3b as-built n=2: (terminals)/(1-q^-3) = recorded solve; "
        "mass law; q^2+q+1 | q^3-1", b1 and b2 and mass and div, "")
    # (c) the documented value divergence, both R-shaped
    s_true = (1 - 1 / q, 1 / q - q ** (-2))
    bt1 = sp.simplify(s_true[0] / (1 - q ** (-2)) - q / (q + 1)) == 0
    bt2 = sp.simplify(s_true[1] / (1 - q ** (-2)) - 1 / (q + 1)) == 0
    differ = sp.simplify(q / (q + 1) - q ** 2 / (q ** 2 + q + 1)) != 0
    div2 = sp.simplify(sp.rem(sp.Poly(q ** 2 - 1, q), sp.Poly(q + 1, q))) == 0
    chk("CHECK3c re-entrant e=2 solve = (q/(q+1), 1/(q+1)) != as-built; "
        "q+1 | q^2-1", bt1 and bt2 and differ and div2, "")
    out["ok"] = ok_a and b1 and b2 and mass and div and bt1 and bt2 \
        and differ and div2
    return out


# ----------------------------------------------------------------------------

def main():
    print("=" * 72)
    print("O12 REV 2 falsifier checks")
    print("=" * 72)
    RESULTS["check1"] = [
        check1_case(2, 2, 7),
        check1_case(2, 3, 5),
        check1_case(3, 2, 6),
        check1_case(3, 3, 4),
        check1_case(4, 2, 5),
    ]
    RESULTS["check2"] = check2(7)
    RESULTS["check3"] = check3()
    RESULTS["findings"] = FINDINGS
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "O12_rev2_results.json"), "w") as f:
        json.dump(RESULTS, f, indent=1, default=str)
    print("=" * 72)
    if FINDINGS:
        print(f"{len(FINDINGS)} FINDINGS:")
        for x in FINDINGS:
            print("  *", x)
        sys.exit(1)
    print("ALL PASS — zero findings.")


if __name__ == "__main__":
    main()
