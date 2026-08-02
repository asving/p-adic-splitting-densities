#!/usr/bin/env python3
"""tr4_check.py — the TR-4 preregistered falsifier family (2026-08-08).

UNIT UNDER TEST: the GRB order-2 leaf's TR-4 row (GRB_ORDER2_2026-08-05.md
S4 + the R11.5/R13.4 residue displays): the ARGUMENT-TYPE FACTORIZATION of
the residual operator — the printed FGMN corollaries, retargeted through
Lemma RESCALE to integer weights, asserted of the order-2 operator
R_{2,gamma} (Def 3.16, corrected Def 3.15, reading C — the operator of
record, pinned by N-1's T0/P3/P12):

  (Cor 4.4(1))  vanishing detects exactly the coset:  for 0 != f with
                w2(f) >= gamma:  R_{2,gamma}(f) = 0  iff  w2(f) > gamma
                (i.e. f in P_gamma^+).
  (Cor 4.5)     the operator factors through the initial form H_mu(f):
                for nonzero g, h with w2(g) = w2(h) = gamma,
                g ~_mu h (i.e. w2(g - h) > gamma)  <=>  R_{2,gamma}(g) =
                R_{2,gamma}(h).  Both directions.
  (Cor 4.11)    the induced map R^gr: P_gamma(mu)/P_gamma^+(mu) -> K1[y]
                is BIJECTIVE (total, injective, onto).

WHY THIS FAMILY EXISTS (the leaf's displayed empirical debt): the N-1
family ledger (GRB REV-12/REV-13, GAP 1 + GAP 4) records "TR-4's
Cor-4.5/4.11 factorization/bijectivity content <-> NO listed family
(paper-secured only)" — T2 checks two-form/support, not factorization or
bijectivity.  Chartered as SYNTHESIS_PASS4 item 8 / PASS5 F6 (the TR-4
harness family).  This script is that family.

STATE-KEY CONVENTION (the ORD-INV law of record, TR3-S2 arc): TR-4's
statement is CONVENTION-INTERNAL — one tower, one state key Phi_2, one
operator; no cross-convention (FGMN-normalized vs GMN-lawful key)
comparison occurs anywhere below, so every check is automatically in the
matched-key form.  Likewise the twist reading: a per-slot UNIT rescaling
eps_1(gamma_j) preserves factorization/bijectivity, so this family does
NOT discriminate reading C vs P (that discrimination is N-1's T0/P3/
P11/P12); it tests the factorization/bijectivity CONTENT of the operator
of record, which no prior family covered.

MACHINERY: grb_order2_check's exact Tower objects are reused (base rings,
developments, w1/w2, R1w_at_z1, eps1, R2w, realize1).  NEW and
independent here: R2gamma(f, gamma) — Def 3.16 transcribed at a FIXED
weight gamma (the harness's Tower.R2w only evaluates at gamma = w2(f));
the class-realization builder realize_target (targets any q in K1[y]);
and the pairwise-difference class tests, which consume only w2 (no
residual-operator reuse — a non-circular injectivity leg).

================ PREREGISTERED PREDICTIONS (exact arithmetic) =============
Towers: the FULL N-1 roster A-J (grb_order2_check.ROSTER — no stratum
restriction; TR-4 has none), over all four base rings
{Z_2, Z_3, F_2[[t]], F_3[[t]]} = 40 towers.  Reading: C only.
seed: 20260817 (fresh; N-1 used 20260808, TS1 20260812, strata 20260815,
TS2 20260816).  All predictions are VIOLATION counts; sample counts are
printed at run time.

TR4a  fixed-weight transcription tie + nonvanishing at own weight
      (Cor 4.4(1), "only if" half): for nonzero f of every genre (random,
      structured, Phi1^a*g improper corners, pi^k constants, Phi2^mu*Q,
      f = Phi2): R2gamma(f, w2(f)) == fp_norm(Tower.R2w(f)) as raw K1
      lists, and != [].
      PREDICTED: 0 violations.  A violation falsifies the Def-3.16
      transcription tie or the "R_{2,gamma}(g) != 0 on P_gamma \\ P_gamma^+"
      half of Cor 4.4(1).
TR4b  coset vanishing (Cor 4.4(1), "if" half): for f with w2(f) > gamma
      (gamma in {w2(f)-1, w2(f)-E2, w2(f)-1-rand}, floored at 0):
      R2gamma(f, gamma) == [].
      PREDICTED: 0 violations.  A violation falsifies "R_{i,alpha}(g) = 0
      iff g in P_alpha^+" (fgmn.txt:1516).
TR4c  factorization / well-definedness (Cor 4.5, (1) => (2)): for
      nonzero g, gamma = w2(g), and noise n with w2(n) > gamma:
      w2(g + n) == gamma and R2w(g + n) == R2w(g) EXACTLY.
      PREDICTED: 0 violations.  A violation falsifies "R_{r,alpha}(g)
      depends on g only through H_mu(g)" — the S4 lemma-shaped fact.
TR4d  the Cor 4.5 equivalence on same-weight pairs, BOTH branches: for
      pairs g, h with w2(g) == w2(h) == gamma (random rejection-sampled
      pairs + constructed same-class pairs (g, g+n)):
        if R2w(g) == R2w(h):  w2(g - h) > gamma   [(2) => (1), injectivity]
        else:                 w2(g - h) == gamma  [(1) => (2), contrapositive]
      (g == h identically counts to the first branch, w2(0) = INF.)
      PREDICTED: 0 violations on both branches; branch counts reported
      (the eq-branch is guaranteed nonvacuous by the constructed pairs).
      A violation falsifies Cor 4.5 (1)<=>(2) (fgmn.txt:1527).
TR4e  surjectivity / totality (Cor 4.11 onto): for random targets
      q in K1[y], deg q <= 4, arbitrary support (including q_0 = 0 and
      deg 0), at a random abscissa class s(gamma) = s2r in [0, e1):
      realize_target builds g with w2(g) == gamma and
      R2gamma(g, gamma) == fp_norm(q) == fp_norm(Tower.R2w(g)); in half
      the samples g is additionally perturbed by above-line noise first.
      PREDICTED: 0 violations.  A violation falsifies the ONTO half of
      Cor 4.11 (fgmn.txt:1616) at the realized class.
TR4f  finite-window BIJECTIVITY certificate (Cor 4.11, exhaustive): on
      every roster tower with |K1| <= 4 (26 of the 40): enumerate ALL
      nonzero targets q with deg q <= 2 (N = |K1|^3 - 1 in {7, 26, 63}),
      realize each at the same gamma (s2r = 0); check (i) every read-back
      R2gamma(g_q, gamma) == q  [onto the window], and (ii) for every
      pair q != q': w2(g_q - g_q') == gamma  [distinct targets sit in
      DISTINCT graded classes — the injectivity leg, consuming only w2].
      PREDICTED: 0 violations.  A violation falsifies bijectivity of the
      induced map on the window.
==========================================================================
RED PROTOCOL (the D-ITER precedent): if any family is RED, the measured
violation shape (first instances, tower pattern) is the deliverable;
no prediction is edited post hoc.
"""
import random, sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pneg, pmul, ppow, pscal,
                              fp_norm, eq12, INF, Tower)

VIOL = []
COUNTS = {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

# ================= the fixed-weight operator (independent leg) ==============
def R2gamma(T, f, gamma):
    """Def 3.16 R_{2,gamma}(f) at a FIXED integer weight gamma (reading C),
    transcribed independently of Tower.R2w (which only evaluates at
    gamma = w2(f)).  Requires 0 != f in P_gamma (w2(f) >= gamma).  Returns
    the fp_norm'd K1-coefficient list indexed from j = 0 at abscissa
    s(gamma); [] is the zero read."""
    d1, vals, gw = T.w2_data(f)
    assert gw < INF and gw >= gamma, "R2gamma: f = 0 or f below P_gamma"
    s2, u2 = eq12(gamma, T.e1, T.h1)
    jmax = (len(d1) - 1 - s2)//T.e1 if len(d1) - 1 >= s2 else -1
    coeffs = []
    for j in range(jmax + 1):
        sj = s2 + j*T.e1
        a = d1[sj]
        num = gamma - sj*T.gamma2
        assert num % T.e1 == 0, "slot weight not integral"
        gj = num // T.e1
        if a and gj >= 0 and vals[sj] == gj:
            c = T.K1["mul"](T.eps1(gj), T.R1w_at_z1(a, gj))
        else:
            assert not (a and vals[sj] < gj), "digit below the gamma-line"
            c = T.K1["zero"]
        coeffs.append(c)
    return fp_norm(T.K1, coeffs)

# ========================== sample builders =================================
def rand_any(T, allow_big=True):
    """nonzero O[x] sample: random / structured / Phi1-shifted mixtures."""
    R = T.R
    for _ in range(30):
        pick = random.random()
        if pick < 0.45:
            f = T.rand_opoly(random.randrange(0, T.degPhi2 + (4 if allow_big else 1)))
        elif pick < 0.8:
            f = T.rand_structured(random.choice([1, 2, 3]))
        else:
            a = random.randrange(0, 2*T.e1 + 1)
            g = T.rand_opoly(random.randrange(0, T.degPhi1 + 2), pimax=3)
            f = pmul(R, ppow(R, T.Phi1, a), g) if g else []
        if f: return f
    return [R["one"]]

def perturb_above(T, gamma):
    """nonzero n with w2(n) > gamma (w2 shifts by E2 per pi-power)."""
    R = T.R
    while True:
        r = T.rand_opoly(random.randrange(0, T.degPhi2 + 3))
        if r: break
    wr = T.w2(r)
    m = 0
    if wr <= gamma:
        m = (gamma + 1 - wr + T.E2 - 1)//T.E2
    n = pscal(R, R["pi_pow"](m), r)
    assert T.w2(n) > gamma
    return n

def realize_target(T, q, s2r):
    """Build g with w2(g) = gamma, s(gamma) = s2r, R_{2,gamma}(g) == q:
    per nonzero slot j, the anchor digit realize1(eps1(gamma_j)^{-1} q_j,
    gamma_j) * Phi1^{s2r + j e1} (the build_Phi2 recipe, arbitrary target).
    Returns (g, gamma)."""
    K1 = T.K1
    D = len(q) - 1
    slack = (T.g0 + 2)*T.h0*T.e0 + 5*T.e0 + 7
    u2r = s2r*T.w1Phi1 + D*T.gamma2 + slack
    gamma = s2r*T.h1 + T.e1*u2r
    assert eq12(gamma, T.e1, T.h1) == (s2r, u2r)
    g = []
    for j, qj in enumerate(q):
        if K1["isz"](qj): continue
        gj = u2r - s2r*T.w1Phi1 - j*T.gamma2
        assert gj >= slack   # gj = (D-j)*gamma2 + slack
        tau = K1["mul"](K1["inv"](T.eps1(gj)), qj)
        Cj = T.realize1(tau, gj)
        g = padd(T.R, g, pmul(T.R, Cj, ppow(T.R, T.Phi1, s2r + j*T.e1)))
    return g, gamma

def rand_target(T, maxdeg=4, force_deg=None, force_c0_zero=False):
    """nonzero K1[y] target with arbitrary support pattern."""
    K1 = T.K1
    d = force_deg if force_deg is not None else random.randrange(0, maxdeg + 1)
    if force_c0_zero and d == 0:
        d = 1
    while True:
        q = []
        for j in range(d + 1):
            if (j == 0 and force_c0_zero) or (j < d and random.random() < 0.3):
                q.append(K1["zero"])
            else:
                q.append(T.rand_K1(nonzero=(j == d)))
        if fp_norm(K1, q):
            return q

def w2_diff(T, g, h):
    d = padd(T.R, g, pneg(T.R, h))
    return T.w2(d) if d else INF

# ============================ test families =================================
def TR4a(T, nf=10):
    R = T.R
    samples = [rand_any(T) for _ in range(nf)]
    samples += [pmul(R, ppow(R, T.Phi1, T.e1 + 1),
                     T.rand_opoly(T.degPhi1, pimax=2) or [R["one"]])]
    samples += [[R["pi_pow"](random.randrange(0, 3))]]
    samples += [pmul(R, T.Phi2, T.rand_structured(2))]
    samples += [T.Phi2]
    for f in samples:
        if not f: continue
        note("TR4a")
        mine = R2gamma(T, f, T.w2(f))
        theirs = fp_norm(T.K1, T.R2w(f))
        if mine != theirs:
            viol("TR4a", T.tag, "fixed-gamma transcription != Tower.R2w")
        if not mine:
            viol("TR4a", T.tag, "R_{2,gamma}(f) == 0 at gamma = w2(f)")

def TR4b(T, nf=10):
    R = T.R
    for _ in range(nf):
        f = rand_any(T)
        gw = T.w2(f)
        if gw == 0:
            f = pscal(R, R["pi_pow"](1), f); gw += T.E2
        cands = {gw - 1, gw - T.E2, gw - 1 - random.randrange(0, 2*T.E2 + 1)}
        for gamma in sorted(c for c in cands if 0 <= c < gw):
            note("TR4b")
            if R2gamma(T, f, gamma):
                viol("TR4b", T.tag,
                     f"R_(2,{gamma})(f) != 0 though w2(f) = {gw} > {gamma}")

def TR4c(T, nf=14):
    R = T.R
    for _ in range(nf):
        g = rand_any(T)
        gamma = T.w2(g)
        n = perturb_above(T, gamma)
        gp = padd(R, g, n)
        note("TR4c")
        if T.w2(gp) != gamma:
            viol("TR4c", T.tag, "w2(g + above-line noise) != w2(g)")
            continue
        if fp_norm(T.K1, T.R2w(gp)) != fp_norm(T.K1, T.R2w(g)):
            viol("TR4c", T.tag, "R2w(g + n) != R2w(g), w2(n) > w2(g)")

def TR4d(T, npairs=14, nsame=6):
    R = T.R
    branches = [0, 0]
    pairs = []
    tries = 0
    while len(pairs) < npairs and tries < 40*npairs:
        tries += 1
        g, h = rand_any(T), rand_any(T)
        d = T.w2(g) - T.w2(h)
        if d % T.E2 != 0: continue
        if d > 0: h = pscal(R, R["pi_pow"](d//T.E2), h)
        elif d < 0: g = pscal(R, R["pi_pow"]((-d)//T.E2), g)
        pairs.append((g, h))
    for _ in range(nsame):
        g = rand_any(T)
        pairs.append((g, padd(R, g, perturb_above(T, T.w2(g)))))
    for g, h in pairs:
        gamma = T.w2(g)
        assert T.w2(h) == gamma
        note("TR4d")
        Rg = fp_norm(T.K1, T.R2w(g))
        Rh = fp_norm(T.K1, T.R2w(h))
        wd = w2_diff(T, g, h)
        if Rg == Rh:
            branches[0] += 1
            if not (wd > gamma):
                viol("TR4d", T.tag,
                     f"R equal but w2(g-h) = {wd} == gamma = {gamma}")
        else:
            branches[1] += 1
            if wd != gamma:
                viol("TR4d", T.tag,
                     f"R unequal but w2(g-h) = {wd} != gamma = {gamma}")
    return branches

def TR4e(T, nf=12):
    R = T.R
    for i in range(nf):
        force0 = (i % 4 == 1)
        q = rand_target(T, maxdeg=4, force_deg=(0 if i % 4 == 2 else None),
                        force_c0_zero=force0 and not (i % 4 == 2))
        s2r = random.randrange(T.e1)
        g, gamma = realize_target(T, q, s2r)
        if i % 2 == 0:
            g = padd(R, g, perturb_above(T, gamma))
        note("TR4e")
        if T.w2(g) != gamma:
            viol("TR4e", T.tag, "realized g: w2(g) != gamma"); continue
        qn = fp_norm(T.K1, q)
        if R2gamma(T, g, gamma) != qn:
            viol("TR4e", T.tag, "read-back R2gamma(g) != target q")
        if fp_norm(T.K1, T.R2w(g)) != qn:
            viol("TR4e", T.tag, "Tower.R2w(g) != target q")

def TR4f(T, maxdeg=2):
    K1 = T.K1
    elems = list(G._field_elems(K1))
    if len(elems) > 4:
        return None
    targets = []
    def rec(pref):
        if len(pref) == maxdeg + 1:
            q = fp_norm(K1, list(pref))
            if q: targets.append(list(pref))
            return
        for c in elems: rec(pref + [c])
    rec([])
    N = len(elems)**(maxdeg + 1) - 1
    assert len(targets) == N
    reps = []
    gamma0 = None
    for q in targets:
        g, gamma = realize_target(T, q, 0)
        if gamma0 is None: gamma0 = gamma
        assert gamma == gamma0
        note("TR4f")
        if T.w2(g) != gamma or R2gamma(T, g, gamma) != fp_norm(K1, q):
            viol("TR4f", T.tag, "window realization: read-back != target")
        reps.append(g)
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            note("TR4f")
            if w2_diff(T, reps[i], reps[j]) != gamma0:
                viol("TR4f", T.tag,
                     f"targets {i},{j}: w2(g_q - g_q') != gamma (class collision)")
    return N

# ================================= main =====================================
def main():
    t0 = time.time()
    random.seed(20260817)
    eq_branch = uneq_branch = 0
    tr4f_windows = []
    for kind, p in [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]:
        for tag, d0, r0, r1 in G.ROSTER:
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}", mode="C")
            TR4a(T, nf=10)
            TR4b(T, nf=10)
            TR4c(T, nf=14)
            b = TR4d(T, npairs=14, nsame=6)
            eq_branch += b[0]; uneq_branch += b[1]
            TR4e(T, nf=12)
            N = TR4f(T)
            if N is not None:
                tr4f_windows.append((T.tag, N))
        print(f"[{time.time()-t0:6.1f}s] ring ({kind}, p={p}) done: "
              f"cumulative violations = {len(VIOL)}")
    print("=" * 76)
    print("TR-4 PREREGISTERED vs OBSERVED (violation counts; samples in parens)")
    fams = [("TR4a", "fixed-gamma tie + nonvanishing at own weight", 0),
            ("TR4b", "coset vanishing on P_gamma^+ (Cor 4.4(1))",    0),
            ("TR4c", "factorization through H_mu (Cor 4.5 =>)",      0),
            ("TR4d", "Cor 4.5 equivalence, both branches",           0),
            ("TR4e", "surjectivity via realize_target (Cor 4.11)",   0),
            ("TR4f", "exhaustive window bijectivity (Cor 4.11)",     0)]
    ok = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == pred else "RED"
        if obs != pred: ok = False
        print(f"{fam:5} {desc:46} pred {pred}  obs {obs:5d} ({n:6d})  {verdict}")
    print(f"TR4d branch counts: R-equal {eq_branch} (incl. constructed "
          f"same-class), R-unequal {uneq_branch}")
    print(f"TR4f windows: {len(tr4f_windows)} towers with |K1| <= 4; "
          f"N per window: {sorted(set(n for _, n in tr4f_windows))}")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 25):")
        for v in VIOL[:25]: print("  ", v)
    print(f"TOTAL samples: {sum(COUNTS.values())}")
    print(f"VERDICT: {'ALL GREEN' if ok and not VIOL else 'RED'}")
    return 0 if (ok and not VIOL) else 1

if __name__ == "__main__":
    sys.exit(main())
