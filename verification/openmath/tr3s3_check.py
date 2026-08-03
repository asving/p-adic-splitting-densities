#!/usr/bin/env python3
"""tr3s3_check.py — the TR3-S3 preregistered falsifier family (2026-08-08).

UNIT UNDER TEST: lean/notes/openmath/TR3S3_2026-08-08.md — TR-3'-GEN at ORDER 3
on the all-e_j = 1 stratum, the COMPOSED identity: under {sigma0, sigma1,
sigma2} and the normalized-l convention, with (H-v3) displayed,

    (coeff)  sigma2( C^F3_j ) == c^G3_{s_j}   at every slot (support equal),
    (form)   sigma2( R^F_3(f) ) == R_lambda3(f)   EXACTLY (discrepancy == 1),

for every nonzero f at every order-3 all-e_j = 1 state, plus the S6.2
consequences (label tie at Phi3; matched-label ord transport).

WHY A NEW FAMILY (beyond strata3_probe, which measured (IDENT-3) 0/1,656 at
seed 20260817): this family tests the COMPOSED identity END-TO-END and the
note's four-step proof route as separate falsifiable rows, on FRESH draws
(seed 20260818) — not a re-confirmation of the probe's per-slot C1 row:
  * a FRESH FGMN level-3 pipeline (fresh_R3 below, built on a fresh
    Def-3.16-at-i=2 transcription R2w_at that reads at ARBITRARY weights):
    the probe's Tower3.R3w HARD-CODES off-line slot coefficients to zero;
    here every slot coefficient (on- AND off-line) is COMPUTED, so the
    note's Lemma Z2 (off-line vanishing) becomes a tested prediction
    instead of an implementation assumption;
  * the two-form is checked on SIDE READS as LISTS (Def 3.18 j0 law +
    length + nonzero ends + elementwise equality with the GMN
    lambda3-list), which the probe never compared as lists (its V5 row
    checked shape only, its C1 row per-slot values only);
  * the four route steps of the note's S5(ii) chain are separate rows
    (RI kernel / RII inner TR3-S1+m0 / RIII t2-absorption / RIV
    recomposition from LEVEL-2 GMN data only — non-circular vs E2A);
  * a PRESCRIBED-VALUE family (W): f is CONSTRUCTED to have slot values
    tau_j fixed a priori, and BOTH pipelines must return the tau-list —
    an end-to-end test against a prediction, not implementation vs
    implementation; half the draws add sub-line noise (tests Z2 +
    linearity end-to-end); holes force j0 > 0 corners.

INDEPENDENCE PERIMETER (stated exactly, the TR3-S1 REV-2 discipline).  This
harness IMPORTS from strata3_probe: the Tower3 object (levels 0-2 = N-1's
Tower verbatim; level-3 layer Phi3/eps2/realize2), and the GMN side
gmn1/gmn2/gmn3 (the probe's FRESH implementation of Defs 1.6/1.9,
(18)/2.19-2.21 at r = 2, 3; normalized l hard-coded — the S0 hypothesis, so
this family CANNOT falsify the normalization choice; u_i = w2 + i*w2(Phi2)
hard-codes (H-v3), so it cannot falsify that either).  FRESH here: the seed
and every draw; the FGMN pipeline fresh_R3/R2w_at (independent of Tower3.R3w
/Tower.R2w — cross-validated against them in rows XV/Z2 and used for every
E2E row); the route decomposition; the W prescription.  Shared inputs carry
their external legs: N-1's T0/T11/P11/P12 (PARI) for levels 0-2, and this
run RE-FIRES the CERT legs per tower (G.T1_T2/T5/T11 + CERT3 PARI
factorpadic/idealprimedec on Z_p rows).  sigma2 = identity of the shared
concrete K2 model (the sigma-content is the note's S2 mathematics, not
testable numerics).  The author of this script also wrote the note (no model
diversity here — that is the hostile passes' job).

DETERMINISTIC: random.seed(20260818) (fresh; 20260808/12/15/16/17 used by
the parents).  EXACT arithmetic only.  Towers: the strata3_probe ROSTER3
(rows 3A-3F, all e_j = 1, mixed g_j incl. g0 = 1, g1 = 1, g2 = 1 corners)
over {Z_2, Z_3, F_2[[t]], F_3[[t]]} = 24 instances.

================ PREREGISTERED PREDICTIONS (sealed BEFORE the run) ===========
E2A  per-abscissa composed identity, fresh FGMN pipeline vs gmn3:
     CF3_j == cG3_j at EVERY abscissa of the union range (both zero
     off-line/off-window), support == the GMN on-line set.  PREDICTED: 0.
E2B  the assembled two-form on side reads: first-nonzero index j0 == s0(f)
     (the GMN initial abscissa; e2 = 1), stripped list == the GMN
     lambda3-list elementwise, length d+1, ends nonzero.  PREDICTED: 0.
RI   kernel row (note S3 Lemma KER): every consumed eq-(12) split has
     s == 0; l0 == l1 == l2 == 0; every consumed eps1/eps2 value == 1.
     PREDICTED: 0.
RII  inner identity row (note S4 Lemma A3 = accepted TR3-S1 on the digit):
     at every on-line slot, the fresh level-2 weight-read list of the digit
     A == the gmn2 coefficient list abscissa-matched (zeros off-window),
     and its first-nonzero index == s2(A) (the m0 = s2(A) law).
     PREDICTED: 0.
RIII t2-absorption row (Def 2.19 verbatim at l1 = 0, e1 = 1):
     t2 := (s2(A) - l1*u_j)/e1 is integral and == s2(A).  PREDICTED: 0.
RIV  recomposition row (the chain's right side from LEVEL-2 GMN data only):
     CF3_j == z2^{s2(A)} * sum_k c^G2_k(A) z2^{k-s2(A)} ... i.e.
     CF3_j == z2^{s2(A)} * R_lambda2(A)(z2), with R_lambda2(A) rebuilt from
     gmn2's list (NOT via gmn3).  PREDICTED: 0.
Z2   off-line vanishing (note S4 Lemma Z2) + own-weight cross-validation:
     (z-i) for constructed nonzero A and beta = w2(A) - k (k = 1..3):
     R2w_at(A, beta) is ALL ZERO; (z-ii) R2w_at(A, w2(A)) == Tower.R2w(A)
     elementwise (fresh transcription vs the N-1-certified operator).
     PREDICTED: 0.
XV   fresh-vs-probe FGMN cross-validation: fresh_R3(f) == Tower3.R3w(f)
     elementwise on the shared slot range.  PREDICTED: 0.
W    prescribed-value end-to-end: constructed f with slot values tau_j
     (holes allowed, half the draws noise-dressed): BOTH side lists == the
     tau-prescription from the first nonzero slot; j0 == first prescribed
     index.  PREDICTED: 0 violations, 0 construction failures.
K    label ties (note S6.2): fresh side read of Phi3 == psi2 with j0 = 0;
     gmn3(Phi3): s0 = 0, d = g2, list == psi2 (both key classes coincide).
     PREDICTED: 0.
O    matched-label ord transport: ord_{psi2}(GMN list) ==
     ord_{psi2}(fresh side list) on every E2E sample; histogram REPORTED,
     must contain some ord >= 1.  PREDICTED: 0 mismatches.
CERT external/integrity legs re-fired per tower: G.T1_T2(nf=4) + G.T5 +
     G.T11(PARI) on the order-2 substate; strata3_probe.cert3_pari (order-3
     PARI leg, Z_p rows); gmn-side P0 integrity (strata3_probe.VIOL empty).
     PREDICTED: 0.
METERS (teeth; all must fire):
     m0pos: on-line slots with m0 = s2(A) > 0        — pred > 0
     j0pos: samples with j0 > 0                       — pred > 0
     noff:  off-line slots carrying a NONZERO digit
            (the honestly-computed Z2 face of E2A)    — pred > 0
     noisy: W draws that were noise-dressed           — pred > 0
     holes: W draws with interior/leading holes       — pred > 0
     ordhi: ord histogram contains ord >= 1           — pred yes
EXIT: 0 iff every row at its predicted count and all meters fire.
Output: tee to tr3s3_check_output.txt; JSON tr3s3_check_results.json.

============ REVISION 1 ADDENDUM (preregistered BEFORE the rerun) ============
Pass-1 gap 3 (TR3S3_pass1_report.md): the RI preregistration above claims
"l0 == l1 == l2 == 0" and eq-(12) splits at every level, but the run-1
implementation checked only the level-2 split + l1 (R2w_at), the level-3
split + l2 (fresh_R3), and the eps1/eps2 values — never l0, never the
level-1 eq-(12) split.  ADDED at REVISION 1 (sealed in this header BEFORE
the rerun): inside R2w_at's digit loop, for every nonzero digit, the
level-1 eq-(12) split of the slot weight beta_m at (e0, h0) — PREDICTED
s == 0 — and the l0 == 0 check (normalized bezout(e0, h0); e0 = 1 on the
stratum).  One new RI sample per nonzero level-1 digit read; NO randomness
consumed by the addition.  PREDICTED: 0 new violations; vs the run-1
record (tr3s3_check_output.txt; pre-run seal commit b4a142b, first-run
record commit 482150b) ONLY the RI sample count and the TOTAL may change
(both strictly up by the same amount), every other row/meter/histogram
value byte-identical mod timings.  ANY other deviation = STOP and report,
do not accept.  Rerun output: tr3s3_check_run2_output.txt.
"""
import random, sys, os, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal,
                              fp_norm, fp_ord, eq12, INF)
import strata3_probe as S3P
from strata3_probe import Tower3, gmn2, gmn3, ROSTER3, cert3_pari

VIOL = []
COUNTS = {}
ORD_HIST = {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

class Meters:
    def __init__(self):
        self.m0pos = 0; self.j0pos = 0; self.noff = 0
        self.noisy = 0; self.holes = 0; self.wfail = 0

# ---------------- the FRESH FGMN pipeline (Def 3.16 at i = 2, 3) --------------
def R2w_at(T, A, beta):
    """FRESH level-2 weight read of nonzero A at ARBITRARY integer weight
    beta <= w2(A), Def 3.16 at i = 2 on the stratum (e0 = e1 = 1: forced
    abscissa progression = 0,1,2,..., slot weights beta - m*gamma2).
    Unlike Tower.R2w (which reads only at beta = w2(A)), this computes the
    off-line reads honestly (Lemma Z2's face)."""
    K1 = T.K1
    d1 = dev(T.R, A, T.Phi1)
    s, u = eq12(beta, T.e1, T.h1)
    note("RI")
    if s != 0 or T.l1 != 0:
        viol("RI", T.tag, f"level-2 kernel: s(beta)={s}, l1={T.l1}")
    out = []
    for m in range(len(d1)):
        a = d1[m]
        bm = beta - m*T.gamma2
        if not a:
            out.append(K1["zero"]); continue
        # REVISION 1 leg (preregistered in the header): level-1 eq-(12)
        # split of the slot weight + the l0 check.
        s1v, _u1v = eq12(bm, T.e0, T.h0)
        note("RI")
        if s1v != 0 or T.l0 != 0:
            viol("RI", T.tag, f"level-1 kernel: s({bm})={s1v}, l0={T.l0}")
        e1v = T.eps1(bm)
        note("RI")
        if e1v != K1["one"]:
            viol("RI", T.tag, f"eps1({bm}) != 1 on the stratum")
        out.append(K1["mul"](e1v, T.R1w_at_z1(a, bm)))
    return out

def evalK2(T3, lst):
    K2, K1 = T3.K2, T3.T.K1
    v = K2["zero"]; zp = K2["one"]
    for c in lst:
        if not K1["isz"](c):
            v = K2["add"](v, K2["mul"](K2["embed"](c), zp))
        zp = K2["mul"](zp, T3.z2)
    return v

def fresh_R3(T3, f, M):
    """FRESH level-3 weight read (Def 3.16 at i = 3): every slot coefficient
    computed as eps2(gamma_j) * R_{2,gamma_j}(A_j)(z2) via R2w_at — including
    off-line slots (predicted 0 by Lemma Z2, CHECKED downstream)."""
    T, K2 = T3.T, T3.K2
    d2 = dev(T3.R, f, T.Phi2)
    vals = [T.w2(A) if A else INF for A in d2]
    assert any(v < INF for v in vals), "fresh_R3 of 0"
    g = min(T3.e2*vals[j] + j*T3.gamma3 for j in range(len(d2))
            if vals[j] < INF)
    s3, u3 = eq12(g, T3.e2, T3.h2)
    note("RI")
    if s3 != 0 or T3.l2 != 0:
        viol("RI", T3.tag, f"level-3 kernel: s(gamma)={s3}, l2={T3.l2}")
    coeffs = []
    for j in range(len(d2)):
        A = d2[j]
        gj = g - j*T3.gamma3
        if not A:
            coeffs.append(K2["zero"]); continue
        if vals[j] > gj:
            M.noff += 1
        e2v = T3.eps2(gj)
        note("RI")
        if e2v != K2["one"]:
            viol("RI", T3.tag, f"eps2({gj}) != 1 on the stratum")
        coeffs.append(K2["mul"](e2v, evalK2(T3, R2w_at(T, A, gj))))
    return coeffs, g, d2, vals

# ------------------------------- the E2E check --------------------------------
def check_sample(T3, f, shape, M):
    T, K2, K1 = T3.T, T3.K2, T3.T.K1
    coeffs, g, d2, vals = fresh_R3(T3, f, M)
    s, d, gco, on, s2map, r2map, uvec = gmn3(T3, f)
    # E2A per-abscissa composed identity + support
    jmax = max(len(coeffs) - 1, s + d)
    for j in range(jmax + 1):
        CF = coeffs[j] if j < len(coeffs) else K2["zero"]
        cG = gco[j - s] if s <= j <= s + d else K2["zero"]
        note("E2A")
        if CF != cG:
            viol("E2A", T3.tag, f"[{shape}] composed identity FAILS at "
                                f"abscissa {j}: CF={CF} cG={cG}")
            return
        if (not K2["isz"](CF)) != (j in on):
            viol("E2A", T3.tag, f"[{shape}] support mismatch at {j}")
            return
        if K2["isz"](CF):
            continue
        # route rows at on-line slots
        A = d2[j]
        gj = g - j*T3.gamma3
        innr = R2w_at(T, A, gj)
        s2G, d2G, co2G, on2G, _, _ = gmn2(T, A, tag=T3.tag)
        note("RII")
        mtop = max(len(innr) - 1, s2G + d2G)
        first_nz = None
        for m in range(mtop + 1):
            c2F = innr[m] if m < len(innr) else K1["zero"]
            c2G = co2G[m - s2G] if s2G <= m <= s2G + d2G else K1["zero"]
            if c2F != c2G:
                viol("RII", T3.tag, f"[{shape}] inner TR3-S1 identity fails "
                                    f"at digit abscissa {m} (slot {j})")
                return
            if first_nz is None and not K1["isz"](c2F):
                first_nz = m
        if first_nz != s2G:
            viol("RII", T3.tag, f"[{shape}] m0 law fails: first nonzero "
                                f"{first_nz} != s2(A) = {s2G}")
            return
        if s2G > 0: M.m0pos += 1
        note("RIII")
        num = s2G - T.l1*uvec[j]
        if num % T.e1 != 0 or num // T.e1 != s2G:
            viol("RIII", T3.tag, f"[{shape}] t2 absorption fails at slot {j}")
            return
        note("RIV")
        rl2 = evalK2(T3, [K1["zero"]]*s2G + co2G)   # z2^{s2}*R_lambda2(A)(z2)
        if rl2 != coeffs[j]:
            viol("RIV", T3.tag, f"[{shape}] recomposition (level-2 GMN data) "
                                f"fails at slot {j}")
            return
    # E2B side two-form as lists
    note("E2B")
    j0 = 0
    while j0 < len(coeffs) and K2["isz"](coeffs[j0]): j0 += 1
    side = fp_norm(K2, coeffs[j0:])
    glist = fp_norm(K2, gco)
    ok = (j0 == s and len(side) == d + 1 and side == glist
          and side and not K2["isz"](side[0]) and not K2["isz"](side[-1]))
    if not ok:
        viol("E2B", T3.tag, f"[{shape}] two-form: j0={j0} vs s0={s}, "
                            f"len={len(side)} vs d+1={d+1}, list eq: "
                            f"{side == glist}")
        return
    if j0 > 0: M.j0pos += 1
    # XV cross-validation vs the probe pipeline
    note("XV")
    pco = T3.R3w(f)
    top = max(len(coeffs), len(pco))
    for j in range(top):
        a = coeffs[j] if j < len(coeffs) else K2["zero"]
        b = pco[j] if j < len(pco) else K2["zero"]
        if a != b:
            viol("XV", T3.tag, f"[{shape}] fresh vs probe FGMN differ at "
                               f"slot {j}")
            return
    # O matched-label ord transport
    note("O")
    o1 = fp_ord(K2, glist, T3.psi2)
    o2 = fp_ord(K2, side, T3.psi2)
    ORD_HIST[o1] = ORD_HIST.get(o1, 0) + 1
    if o1 != o2:
        viol("O", T3.tag, f"[{shape}] ord: GMN {o1} != FGMN {o2}")

# ------------------------- Z2 constructed off-line row ------------------------
def z2_row(T3, ndraws=8):
    T, K1 = T3.T, T3.T.K1
    for _ in range(ndraws):
        A = T.rand_opoly(random.randrange(0, T.degPhi2), pimax=3)
        if not A: A = [T.R["pi_pow"](random.randrange(0, 3))]
        b = T.w2(A)
        note("Z2")
        # (z-ii) own-weight cross-validation vs the certified operator
        mine = R2w_at(T, A, b)
        ref = T.R2w(A)
        top = max(len(mine), len(ref))
        for m in range(top):
            x = mine[m] if m < len(mine) else K1["zero"]
            y = ref[m] if m < len(ref) else K1["zero"]
            if x != y:
                viol("Z2", T3.tag, f"own-weight cross-validation fails at "
                                   f"abscissa {m}")
                break
        # (z-i) strictly-below reads vanish identically
        for k in range(1, 4):
            note("Z2")
            lst = R2w_at(T, A, b - k)
            if any(not K1["isz"](c) for c in lst):
                viol("Z2", T3.tag, f"Lemma Z2 fails: R_(2,{b-k}) of A with "
                                   f"w2={b} is nonzero")

# ---------------------- W prescribed-value construction -----------------------
def w_row(T3, M, ndraws=6):
    T, R, K2 = T3.T, T3.R, T3.K2
    for _ in range(ndraws):
        nslots = random.choice([2, 3, 4])
        base = T3.gamma3*(nslots + 2) + T.g1*T.gamma2 + T.g0*T.h0 + 4
        taus = [None if random.random() < 0.3 else T3.rand_K2(nonzero=True)
                for _ in range(nslots)]
        if taus[-1] is None: taus[-1] = T3.rand_K2(nonzero=True)
        if all(t is None for t in taus[:-1]) and nslots > 1 \
           and random.random() < 0.5:
            taus[0] = T3.rand_K2(nonzero=True)
        has_hole = any(t is None for t in taus)
        if has_hole: M.holes += 1
        f = []
        try:
            for j, tau in enumerate(taus):
                if tau is None: continue
                f = padd(R, f, pmul(R, T3.realize2(tau, base - j*T3.gamma3),
                                    ppow(R, T.Phi2, j)))
        except AssertionError as exc:
            M.wfail += 1
            viol("W", T3.tag, f"construction failure: {exc}")
            continue
        noisy = random.random() < 0.5
        if noisy:
            M.noisy += 1
            noise = T.rand_opoly(random.randrange(0, T.degPhi2 + 3), pimax=2)
            f = padd(R, f, pscal(R, R["pi_pow"](base + 2), noise))
        jstar = next(j for j, t in enumerate(taus) if t is not None)
        pred = [K2["zero"] if t is None else t for t in taus[jstar:]]
        # both pipelines against the a-priori prescription
        note("W")
        coeffs, g, d2, vals = fresh_R3(T3, f, M)
        j0 = 0
        while j0 < len(coeffs) and K2["isz"](coeffs[j0]): j0 += 1
        side = fp_norm(K2, coeffs[j0:])
        s, d, gco, on, _, _, _ = gmn3(T3, f)
        okF = (g == base and j0 == jstar and side == fp_norm(K2, pred))
        okG = (s == jstar and fp_norm(K2, gco) == fp_norm(K2, pred))
        if not (okF and okG):
            viol("W", T3.tag, f"prescribed-value E2E fails (noisy={noisy}, "
                              f"holes={has_hole}): okF={okF} okG={okG} "
                              f"j0={j0}/{jstar} s={s}")

# ------------------------------ K label-tie row -------------------------------
def k_row(T3, M):
    T, K2 = T3.T, T3.K2
    note("K")
    coeffs, g, d2, vals = fresh_R3(T3, T3.Phi3, M)
    j0 = 0
    while j0 < len(coeffs) and K2["isz"](coeffs[j0]): j0 += 1
    side = fp_norm(K2, coeffs[j0:])
    if j0 != 0 or side != fp_norm(K2, T3.psi2):
        viol("K", T3.tag, f"fresh side read of Phi3 != psi2 (j0={j0})")
    s, d, gco, on, _, _, _ = gmn3(T3, T3.Phi3)
    if s != 0 or d != T3.g2 or fp_norm(K2, gco) != fp_norm(K2, T3.psi2):
        viol("K", T3.tag, f"gmn3(Phi3): s0={s}, d={d} vs (0, {T3.g2}), "
                          f"or list != psi2")

# ----------------------------------- main -------------------------------------
def run_tower(T3, M, pari):
    T, R = T3.T, T3.R
    # CERT legs re-fired
    gv0 = len(G.VIOL); sv0 = len(S3P.VIOL)
    G.T1_T2(T, nf=4); G.T5(T); G.T11(T, pari)
    cert3_pari(T3, pari)
    note("CERT", (len(G.VIOL) - gv0) + (len(S3P.VIOL) - sv0) + 1)
    k_row(T3, M)
    z2_row(T3, ndraws=8)
    w_row(T3, M, ndraws=6)
    for _ in range(14):
        f = T.rand_opoly(random.randrange(0, int(2.2*T3.degPhi3) + 1),
                         pimax=5)
        if not f: f = [R["pi_pow"](random.randrange(0, 4))]
        check_sample(T3, f, "rand", M)
    for _ in range(6):
        check_sample(T3, T3.rand_structured3(random.choice([2, 3, 4])),
                     "struct", M)
    for _ in range(4):
        a = random.randrange(1, 4)
        h = T.rand_opoly(random.randrange(0, T.degPhi2 + 2), pimax=3)
        if not h: h = [R["one"]]
        check_sample(T3, pmul(R, ppow(R, T.Phi2, a), h), f"Phi2^{a}*g", M)
    for _ in range(4):
        a = random.randrange(1, 4)
        h = T.rand_opoly(random.randrange(0, T.degPhi1 + 2), pimax=3)
        if not h: h = [R["one"]]
        check_sample(T3, pmul(R, ppow(R, T.Phi1, a), h), f"Phi1^{a}*g", M)
    for k in range(0, 3):
        check_sample(T3, [R["pi_pow"](k)], f"pi^{k}", M)
    for _ in range(3):
        mu = random.choice([1, 2])
        check_sample(T3, pmul(R, ppow(R, T3.Phi3, mu),
                              T3.rand_structured3(2)), f"Phi3^{mu}*Q", M)

def main():
    t0 = time.time()
    random.seed(20260818)
    sys.path.insert(0, os.path.expanduser(
        '~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari(); pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        print(f"WARNING: cypari2 unavailable ({exc}); PARI legs skipped "
              "-> CERT RED if predicted")
    M = Meters()
    configs = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]
    for kind, p in configs:
        for tag, d0, r0, r1, r2 in ROSTER3:
            full = f"{kind},p={p},{tag}"
            T3 = Tower3(kind, p, d0, r0, r1, r2, full)
            run_tower(T3, M, pari)
        print(f"[{time.time()-t0:6.1f}s] ring ({kind},p={p}) done: "
              f"viol={len(VIOL)} G={len(G.VIOL)} S3P={len(S3P.VIOL)}")
    print()
    print("=" * 78)
    print("TR3-S3 FALSIFIER — PREDICTED vs OBSERVED (violations; samples in "
          "parens)")
    print("=" * 78)
    fams = [
        ("E2A", "per-abscissa composed identity + support    ", 0),
        ("E2B", "side-read two-form as lists + j0 law        ", 0),
        ("RI",  "kernel: s==0, l==0, eps1==eps2==1           ", 0),
        ("RII", "inner TR3-S1 on the digit + m0 = s2(A)      ", 0),
        ("RIII","t2 absorption t2 == s2(A) integral          ", 0),
        ("RIV", "recomposition from level-2 GMN data         ", 0),
        ("Z2",  "off-line vanishing + own-weight cross-val   ", 0),
        ("XV",  "fresh vs probe FGMN pipeline                ", 0),
        ("W",   "prescribed-value end-to-end (noise/holes)   ", 0),
        ("K",   "label ties at Phi3 (both pipelines = psi2)  ", 0),
        ("O",   "matched-label ord transport                 ", 0),
    ]
    all_green = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == pred else "RED"
        if verdict == "RED": all_green = False
        print(f"{fam:4} {desc:46} pred {pred}  obs {obs:5d} ({n:6d})  "
              f"{verdict}")
    certv = len(G.VIOL) + len(S3P.VIOL) + \
        sum(1 for v in VIOL if v[0] == "CERT")
    cv = "GREEN" if certv == 0 else "RED"
    if certv: all_green = False
    print(f"CERT external/integrity legs (G + S3P + local)     pred 0  "
          f"obs {certv:5d} ({COUNTS.get('CERT',0):6d})  {cv}")
    mrows = [("m0pos: on-line slots with m0 = s2(A) > 0", M.m0pos > 0,
              M.m0pos),
             ("j0pos: samples with j0 > 0", M.j0pos > 0, M.j0pos),
             ("noff: off-line nonzero-digit slots computed", M.noff > 0,
              M.noff),
             ("noisy: W draws noise-dressed", M.noisy > 0, M.noisy),
             ("holes: W draws with holes", M.holes > 0, M.holes),
             ("wfail: W construction failures == 0", M.wfail == 0, M.wfail)]
    for desc, ok, val in mrows:
        tag = "MATCH" if ok else "MISMATCH"
        if not ok: all_green = False
        print(f"METER {desc}: {val}  {tag}")
    hist = " ".join(f"{k}:{v}" for k, v in sorted(ORD_HIST.items()))
    ordhi = any(k >= 1 and v > 0 for k, v in ORD_HIST.items())
    if not ordhi: all_green = False
    print(f"METER ord histogram: {hist} (pred: some ord >= 1)  "
          f"{'MATCH' if ordhi else 'MISMATCH'}")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 30):")
        for v in VIOL[:30]: print("  ", v)
    if G.VIOL:
        print(f"{len(G.VIOL)} G VIOLATIONS (first 10):")
        for v in G.VIOL[:10]: print("  ", v)
    if S3P.VIOL:
        print(f"{len(S3P.VIOL)} S3P VIOLATIONS (first 10):")
        for v in S3P.VIOL[:10]: print("  ", v)
    total = sum(COUNTS.values())
    print(f"TOTAL samples: {total}   elapsed {time.time()-t0:.1f}s")
    verdict = all_green and not VIOL and not G.VIOL and not S3P.VIOL
    print(f"VERDICT (preregistered rows): "
          f"{'ALL GREEN' if verdict else 'RED — see above'}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "tr3s3_check_results.json"), "w") as fh:
        json.dump(dict(seed=20260818,
                       violations=[list(v) for v in VIOL],
                       g_violations=[list(v) for v in G.VIOL],
                       s3p_violations=[list(v) for v in S3P.VIOL],
                       counts=COUNTS,
                       meters=dict(m0pos=M.m0pos, j0pos=M.j0pos,
                                   noff=M.noff, noisy=M.noisy,
                                   holes=M.holes, wfail=M.wfail),
                       ord_hist=ORD_HIST), fh, indent=1, default=str)
    return 0 if verdict else 1

if __name__ == "__main__":
    sys.exit(main())
