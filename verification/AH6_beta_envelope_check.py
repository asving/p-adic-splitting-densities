#!/usr/bin/env python3
"""AH6 — the beta-cell envelope certification (unit A-H.6, repair of FINDING F-H17.2).

FINDING F-H17.2 (leanfinal/notes/RESCHEDULE_H121c_H122_2026-08-16.md) refuted the ROUTE of
blueprint node H.122 at the constants signed in node H.121 clause (iii):

    signed clause (iii):   #(beta & undec)(N) <= N^m * Q^{m(N-1)} * Q^{-(N-2)}
    normalized:            betahat(N)         <= N^m * Q^{-(N-2)} = Q * N^m * Q^{-(N-1)}
    H.122's target:        uhat(N)            <= N * Q^{-(N-1)}          [(K,B,c) = (1,1,1)]

and `Q * N^m > N` for every Q >= 2, m >= 2, N >= 1, so clause (iii) can never certify H.122.
The finding proposed the repair candidate

    CANDIDATE-0:           betahat(N) <= (m - 1) * Q^{-(N-1)}       (NO polynomial factor)

This script decides CANDIDATE-0 and, if it fails, certifies the sharpest true form.  Exact
arithmetic throughout (`Fraction`); every count exhaustive or from a validated closed form.

LEG A (brute force).  Exhaustive enumeration of every cluster state (m, d = 1, window N) with
the corpus reader (imported verbatim from verification/openmath/OM2_genindb_battery.py, the
same transcription H.119/H.121a/H.121b gate).  Emits the exact beta-undecided count.

LEG B (structural, m = 3).  The beta cell at m = 3 has EXACTLY ONE child, of degree mu = 2
(2 <= mu < m = 3 forces mu = 2, and 2 + 2 > 3 forces uniqueness).  Per-genre the child map is
uniform onto the full child-state space (battery check P1(f)), so

    #(beta & undec)(N) = sum_M nbeta(N, M) * u2hat(M)

with nbeta(N, M) = #(beta states at window N whose child window is M) and u2hat the m = 2
normalized complement (H.26 closed form).  nbeta is a pure Newton-polygon count: it depends
only on the valuation vector (v_0, v_1, v_2) (capped at N) and the unit residues, so it is
computed by a WEIGHTED enumeration over ~N^3 * (Q-1)^3 classes instead of Q^{3(N-1)} states.
LEG B is cross-validated against LEG A on every overlapping cell before it is used to extend.

LEG C.  The envelope verdicts on the LEG-B extension, up to large N: CANDIDATE-0, the signed
clause (iii), the sharpest true constant, and the H.122 (1,1,1) target on uhat itself.

Run:  python3 AH6_beta_envelope_check.py [--fast] [--nmax K]
Exit 0 iff every check passes.
"""

import sys, os, itertools
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "openmath"))
import OM2_genindb_battery as B

FAST = "--fast" in sys.argv
NMAX = 60
if "--nmax" in sys.argv:
    NMAX = int(sys.argv[sys.argv.index("--nmax") + 1])

CHECKS = []
def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok), detail))
    print(("  ok  " if ok else "  FAIL") + f"  {name}" + (f"  [{detail}]" if detail else ""))

def fmt(x):
    return f"{float(x):.6g}"

# ----------------------------------------------------------------------------------
# the m = 2 normalized complement, from the H.26 closed form (battery-verified tie
# "P3 m=2 closed-form tie" and node H.26's `uTwo_closed`)
# ----------------------------------------------------------------------------------
def u2(q, M):
    """uTwo q M = #(undecided degree-2 cluster states at window M)."""
    if M <= 0: return 0
    if M == 1: return 1
    return q ** (M - 1) + ((M - 1) // 2) * (q - 1) * q ** (M - 2)

def u2hat(q, M):
    """normalized: u2 / Q^{2(M-1)}."""
    if M <= 0: return Fraction(0)
    return Fraction(u2(q, M), q ** (2 * (M - 1)))

# ----------------------------------------------------------------------------------
# LEG A — brute force with the corpus reader
# ----------------------------------------------------------------------------------
def brute_cell(q, m, N):
    """exhaustive: returns dict with total, u, drain, alpha_undec, beta_undec, beta_by_M."""
    prec = N * (m + 1) + 4
    RB = B.Ring('Zq', q, prec)
    tot = q ** (m * (N - 1))
    u = drain = a_undec = b_undec = 0
    beta_by_M = {}
    for st in B.cluster_states(RB, m, N):
        d0 = B.depth0_data(RB, st, m, N, q)
        v = B.read_cluster('Zq', q, st, m, N)
        undec = (v[0] == 'U')
        if undec: u += 1
        bk = d0['bucket']
        if bk == 'DRAIN': drain += 1
        elif bk == 'ALPHA' and undec: a_undec += 1
        elif bk == 'BETA':
            # child windows of this state
            for (mu, k, z) in d0['children']:
                c, D, Dp = B.extract_child(RB, st, m, N, k, z, q)
                assert D == Dp
                M = N - D
                beta_by_M[(mu, M)] = beta_by_M.get((mu, M), 0) + 1
            if undec: b_undec += 1
        elif bk == 'CS':
            assert m >= 4, "CS bucket must be empty at m <= 3 (H.117)"
    return {'total': tot, 'u': u, 'drain': drain, 'alpha_undec': a_undec,
            'beta_undec': b_undec, 'beta_by_M': beta_by_M}

# ----------------------------------------------------------------------------------
# LEG B — the structural beta count at m = 3
# ----------------------------------------------------------------------------------
def lower_hull(pts):
    return B.lower_hull(pts)

def beta_classes_m3(q, N):
    """WEIGHTED enumeration of degree-3 cluster states by (valuation vector, unit residues).

    Returns dict M -> nbeta(N, M): the number of window-N degree-3 cluster states in the BETA
    bucket whose (unique, mu = 2) child sits at window M.  A state is (a0, a1, a2), each with
    v >= 1, canonical mod pi^N; the class of a_j is (v_j, r_j) with v_j in {1..N-1} and
    r_j in F_q^x  (weight (q-1)^0 * q^{N-1-v_j} classes... see `weight`), or v_j >= N (the
    zero rep, weight 1).  The Newton polygon, the residual factorizations, the child slope k
    and the content D = min_j(min(v_j, N) + j k) all depend only on this data.
    """
    INF = N  # "invisible at window N"
    def weight(v):
        # number of canonical reps mod pi^N with valuation exactly v and a PRESCRIBED unit
        # residue r = res(a / pi^v):  q^{N-1-v}  (the higher digits are free)
        return 1 if v >= INF else q ** (N - 1 - v)

    out = {}
    vals_range = list(range(1, N)) + [INF]
    units = list(range(1, q))
    for v0 in vals_range:
        for v1 in vals_range:
            for v2 in vals_range:
                if v0 >= INF:
                    continue                     # DRAIN
                r0s = units if v0 < INF else [None]
                r1s = units if v1 < INF else [None]
                r2s = units if v2 < INF else [None]
                for r0 in r0s:
                    for r1 in r1s:
                        for r2 in r2s:
                            vals = [v0, v1, v2, 0]
                            res = [r0, r1, r2, 1]
                            info = polygon_read_m3(q, N, vals, res)
                            if info is None:
                                continue
                            M = info
                            w = weight(v0) * weight(v1) * weight(v2)
                            out[M] = out.get(M, 0) + w
    return out

def polygon_read_m3(q, N, vals, res):
    """depth-0 polygon read of a degree-3 state given valuations (capped, N = invisible) and
    unit residues.  Returns the child window M if the state is in the BETA bucket, else None.
    Mirrors OM2_genindb_battery.depth0_data exactly (same hull, same residual convention)."""
    m = 3
    pts = [(j, vals[j]) for j in range(m + 1) if vals[j] < N or j == m]
    hull = B.lower_hull(pts)
    children, pieces, csblocks = [], [], []
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        ln, drop = x2 - x1, y1 - y2
        import math
        gg = math.gcd(drop, ln)
        h_, e_ = drop // gg, ln // gg
        deg_r = ln // e_
        rc = []
        for i in range(deg_r + 1):
            j = x1 + i * e_
            vline = y1 - i * h_
            if j <= m and vals[j] < N and vals[j] == vline:
                rc.append(res[j] % q)
            elif j == m and vline == 0:
                rc.append(1)
            else:
                rc.append(0)
        assert rc[0] != 0 and rc[-1] != 0
        for (psi, mult) in B.fq_factor(list(rc), q):
            gpsi = len(psi) - 1
            if mult == 1:
                pieces.append((e_, gpsi))
            elif e_ == 1 and gpsi == 1:
                z = (q - psi[0]) % q
                assert z != 0
                children.append((mult, h_, z))
            else:
                csblocks.append((e_, mult, gpsi))
    if csblocks:
        raise AssertionError("CS bucket must be empty at m = 3 (H.117)")
    if not children:
        return None                                   # DEC
    if len(hull) - 1 == 1 and len(children) == 1 and not pieces and children[0][0] == m:
        return None                                   # ALPHA
    # BETA: at m = 3 exactly one child, of degree 2
    assert len(children) == 1 and children[0][0] == 2, f"unexpected beta children {children}"
    mu, k, z = children[0]
    D = min([min(vals[j], N) + j * k for j in range(m)] + [m * k])
    return N - D

# ----------------------------------------------------------------------------------
def main():
    print("AH6 — beta-cell envelope certification (unit A-H.6; FINDING F-H17.2 repair)")
    print("exact arithmetic; reader imported from verification/openmath/OM2_genindb_battery.py\n")

    # ---------------- LEG A ----------------
    print("LEG A — exhaustive brute force (corpus reader)")
    plan = [(2, 2, 6), (3, 2, 5), (2, 3, 6), (3, 3, 4)]
    if FAST: plan = [(2, 2, 4), (2, 3, 5), (3, 3, 4)]
    brute = {}
    for (q, m, Nmax) in plan:
        for N in range(1, Nmax + 1):
            r = brute_cell(q, m, N)
            brute[(q, m, N)] = r
            bhat = Fraction(r['beta_undec'], r['total'])
            print(f"    q={q} m={m} N={N}: total={r['total']:>8}  u={r['u']:>8}"
                  f"  beta&undec={r['beta_undec']:>6}  betahat={fmt(bhat)}")
    # m = 2: the beta bucket is EMPTY (finding sec.1; H.118 betaChild_mult_lt + H.109)
    ok = all(brute[(q, 2, N)]['beta_undec'] == 0
             for (q, m, Nmax) in plan if m == 2 for N in range(1, Nmax + 1))
    check("A1  m=2: beta&undecided count is 0 at every tested cell", ok)

    # ---------------- LEG B validation ----------------
    print("\nLEG B — structural beta count at m = 3, validated against LEG A")
    for (q, m, Nmax) in plan:
        if m != 3: continue
        for N in range(1, Nmax + 1):
            nb = beta_classes_m3(q, N)
            got = sum(nb.values())
            want_states = sum(c for (mu, M), c in brute[(q, 3, N)]['beta_by_M'].items())
            ok = (got == want_states)
            check(f"B1  q={q} m=3 N={N}: structural beta-state count = brute force"
                  f" ({got})", ok, "" if ok else f"{got} vs {want_states}")
            # the composed undecided count
            comp = sum(cnt * u2hat(q, M) for M, cnt in nb.items())
            ok2 = (comp == Fraction(brute[(q, 3, N)]['beta_undec']))
            check(f"B2  q={q} m=3 N={N}: sum_M nbeta(N,M)*u2hat(M) = #(beta&undec)"
                  f" ({brute[(q,3,N)]['beta_undec']})", ok2,
                  "" if ok2 else f"{comp} vs {brute[(q,3,N)]['beta_undec']}")

    # ---------------- LEG C ----------------
    print("\nLEG C — the envelope verdicts on the structural extension")
    NM = 12 if FAST else NMAX
    for q in ([2] if FAST else [2, 3]):
        m = 3
        Q = q
        rows = []
        for N in range(1, NM + 1):
            nb = beta_classes_m3(q, N)
            tot = Fraction(q ** (m * (N - 1)))
            bhat = sum(Fraction(cnt) * u2hat(q, M) for M, cnt in nb.items()) / tot
            cand0 = Fraction(m - 1, 1) * Fraction(1, Q ** (N - 1))
            signed = Fraction(N ** m, 1) * Fraction(1, Q ** max(N - 2, 0))
            ratio = bhat * Q ** (N - 1)                      # betahat / Q^{-(N-1)}
            rows.append((N, bhat, cand0, signed, ratio))
        print(f"\n  q={q}, m=3   [betahat exact; ratio := betahat * Q^(N-1)]")
        print(f"  {'N':>3} {'betahat':>14} {'CAND-0 2Q^-(N-1)':>18} {'ratio':>10}"
              f" {'ratio/N':>10}")
        for (N, bhat, cand0, signed, ratio) in rows:
            if N <= 12 or N % 5 == 0 or N == NM:
                print(f"  {N:>3} {fmt(bhat):>14} {fmt(cand0):>18} {fmt(ratio):>10}"
                      f" {fmt(Fraction(ratio, N)):>10}")
        # CANDIDATE-0 verdict
        bad0 = [(N, ratio) for (N, bhat, cand0, signed, ratio) in rows if bhat > cand0]
        if bad0:
            N0, r0 = bad0[0]
            check(f"C1  q={q}: CANDIDATE-0 betahat <= (m-1)Q^-(N-1) is FALSE"
                  f" — first failure at N={N0} (ratio {fmt(r0)} > {m-1})", True,
                  f"{len(bad0)} failures in N<={NM}")
        else:
            check(f"C1  q={q}: CANDIDATE-0 holds on N<={NM}"
                  f" (sup ratio {fmt(max(r for *_ , r in rows))})", True)
        # the sharpest LINEAR form: betahat <= K * N * Q^{-(N-1)}
        Kstar = max(Fraction(ratio, N) for (N, _, _, _, ratio) in rows)
        Nstar = max(rows, key=lambda t: Fraction(t[4], t[0]))[0]
        print(f"    sup_N betahat*Q^(N-1)/N = {Kstar} = {fmt(Kstar)}   (attained N={Nstar})")
        for K, lab in [(Fraction(1, 1), "1"), (Fraction(m - 1, 1), f"{m-1}")]:
            ok = all(bhat <= K * Fraction(N, Q ** (N - 1))
                     for (N, bhat, _, _, _) in rows)
            check(f"C2  q={q}: betahat(N) <= {lab} * N * Q^-(N-1) on 1<=N<={NM}", ok)
        # the signed clause (iii) — true but useless (the finding's tooth)
        ok = all(bhat <= signed for (N, bhat, _, signed, _) in rows)
        check(f"C3  q={q}: the SIGNED clause (iii) envelope holds (it is TRUE, just weak)", ok)
        teeth = [(N, signed) for (N, bhat, cand0, signed, ratio) in rows
                 if N >= 2 and signed > Fraction(N, Q ** (N - 1))]
        check(f"C4  q={q}: TOOTH — the signed envelope exceeds H.122's TOTAL budget"
              f" N*Q^-(N-1) at every tested N>=2", len(teeth) == NM - 1,
              f"{len(teeth)}/{NM-1}")
        teeth2 = [N for (N, bhat, cand0, signed, ratio) in rows
                  if N >= 2 and signed > Fraction(N, Q ** (N - 1))
                  and bhat <= Fraction(N, Q ** (N - 1))]
        check(f"C5  q={q}: TOOTH — at those N the TRUE betahat is inside the budget"
              f" (the envelope, not the cell, is the defect)", len(teeth2) == NM - 1)

    bad = [c for c in CHECKS if not c[1]]
    print(f"\n==== {len(CHECKS)} checks, {len(CHECKS) - len(bad)} passed, {len(bad)} failed ====")
    if bad:
        for name, _, det in bad:
            print(f"  FAILED: {name}  {det}")
        sys.exit(1)
    print("ALL CHECKS PASSED")

if __name__ == "__main__":
    main()
