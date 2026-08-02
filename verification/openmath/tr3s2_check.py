#!/usr/bin/env python3
"""tr3s2_check.py — the TR3-S2 preregistered falsifier family (2026-08-08).

UNIT UNDER TEST: lean/notes/openmath/TR3S2_2026-08-08.md — the COMPOSE argument
closing stratum (ii) of TR-3'-GEN at order 2 (all e0): sigma-coefficientwise,
with theta := l0*g0*h0,

    (coeff)  C^F_j              == z1^(theta*s_j) * c^G_{s_j}    (every slot),
    (form)   sigma(R^F_2(f))(y) == z1^(theta*s0(f)) * R_lambda(f)(z1^(theta*e1)*y),

and the TR-3-ORD-X-on-(ii) consequence (matched-label ord transport; see the
AMENDMENT below for the exact form).

WHY A NEW FAMILY (beyond strata_probe FAMILY A, which confirmed the closed form
0/3,640 at seed 20260815): this family tests the COMPOSE CHAIN itself — each
link of the note's S5(ii) computation separately AND the assembled two-form /
ord / label-tie consequences end-to-end, on FRESH parameter draws (seed
20260816) and fresh sample shapes. Specifically new vs strata_probe:
  * the kernel (EXP) is checked as an identity of INTEGERS per slot
    (strata_probe only checked the resulting group element);
  * the two-form is checked on SIDE READS (Def 3.18 normalization + j0 law +
    variable rescaling assembled), which strata_probe never touched;
  * the label ties at both state-key conventions and the matched-label ord
    transport (TR-3-ORD-X-on-(ii) minus its FGMN-internal Cor-5.15 leg) are
    checked, which strata_probe never touched.

INDEPENDENCE PERIMETER (stated exactly, the TR3-S1 REV-2 discipline): the GMN
side below is implemented FRESH from the printed Defs (1.6/1.9 order 1;
(18)/2.19-2.21 order 2; normalized l0 hard-coded — the note's S0 hypothesis, so
this family CANNOT falsify the normalization choice), with its own polygon /
on-line / s1 / t1 / coefficient assembly; it SHARES with the FGMN side the
Tower object (base-ring arithmetic, Phi0/Phi1/Phi2, residue fields) and w0/w1
consumed as v1/v2 (the pinned Def-2.5 identity). Those shared inputs carry
N-1's external legs (T11/P11/P12 PARI + T0) and, for the designed rows K/L/M/N,
strata_probe's CERT leg (0 violations, incl. PARI on Z_p). sigma_1 = identity
of the shared concrete K1 model (the sigma-content is the note's S2
mathematics, not testable numerics). The author of this script also wrote the
note (no model diversity here — that is the hostile passes' job).

=============================================================================
AMENDMENT (RUN 1 -> RUN 2, 2026-08-08; the run-1 log is
tr3s2_check_run1_output.txt and is part of the unit's record).

RUN 1 (v1 predictions): TS2a 0/3,536 GREEN, TS2b 0/3,536 GREEN, TS2e 0/1,088
GREEN — the THEOREM rows (compose chain, integer kernel, two-form, controls)
all green on first contact. TS2c 20/52 RED, TS2d 214/3,536 RED. Diagnosis
(traced, all 20 towers): v1 preregistered the label tie
R_lambda(Phi2) == z1^(-theta*e1*g1)*psi1 for THE HARNESS'S Phi2 — but
build_Phi2 constructs the FGMN-NORMALIZED key (side read == psi1 exactly;
N-1's T5 row), and at e0 >= 2 that key is NOT GMN-lawful: measured on all 20
divergent towers, side(Phi2) == psi1 and R_lambda(Phi2) == T_{1/c}psi1
(coefficients psi1_k * z1^(-theta*e1*k)), exactly as the note's two-form
dictates for this key. v1's TS2d then paired MISMATCHED labels (psi1 on both
sides), which the note's own S6.2 transport says must FAIL at e0 >= 2 — the
214 mismatches are that failure, measured. THE THEOREM IS UNTOUCHED; what run
1 refuted is the assumption that "lawful state key" is convention-independent
on stratum (ii). The note's S6.2 is stated for a GMN-LAWFUL key (R_lambda ~
psi1); the harness key is the FGMN-normalized one; the two COINCIDE at e0 = 1
and DIVERGE by exactly the character at e0 >= 2.

RUN 2 (v2 predictions, preregistered below BEFORE run 2): test BOTH key
conventions with MATCHED label pairs, plus the divergence meter.
=============================================================================

================ PREREGISTERED PREDICTIONS v2 (exact arithmetic) ============
Towers: e0 >= 2 rows C, D, E, H, J (N-1 roster) + K, L, M, N (strata_probe
designed rows, CERT-certified there); e0 = 1 controls A, B, G, I. All over
{Z_2, Z_3, F_2[[t]], F_3[[t]]}. Reading: C only. seed: 20260816.

TS2a  per-slot compose chain, at every abscissa of the union range:
      support match (C^F_j != 0 iff s_j on the independently computed on-line
      set), and at every ON-LINE slot the three links:
        (k1) kernel (EXP) as INTEGERS:
             (l0p*s(b_j) - l0*u(b_j)) + m0 == t1(s_j) + l0*g0*h0*s_j,
             with m0 = (s1(a) - s(b_j))/e0 an integer >= 0 and t1 integral;
        (k2) Lemma A-GEN factorization:
             C^F_j == eps1(b_j) * z1^m0 * R1^GMN(a)(z1);
        (k3) the closed form: C^F_j == z1^(theta*s_j) * c^G_{s_j}.
      PREDICTED: 0 violations. [RUN 1: 0/3,536 GREEN — the proved kernel]
TS2b  the assembled two-form on side reads: R2s(f)[k] ==
      z1^(theta*(s + k*e1)) * c^G_{s+k*e1} for k = 0..d, length == d+1,
      nonzero ends, and j0 == (s - s(gamma))/e1 == floor(s/e1).
      PREDICTED: 0 violations. [RUN 1: 0/3,536 GREEN]
TS2c  label ties at BOTH key conventions (one per tower):
      (c-i)  harness key Phi2 (FGMN-normalized; N-1 T5 object):
             side(Phi2) == psi1 exactly, s0 = 0, d = g1, j0 = 0, and
             R_lambda(Phi2) == T_{1/c}psi1 = [psi1_k * z1^(-theta*e1*k)]_k
             — the note's two-form at f = Phi2 read backwards;
      (c-ii) constructed GMN-LAWFUL key Phi2' (built from
             psitilde_k := psi1_k * z1^(theta*e1*(k-g1)) by the same
             realize1 machinery): side(Phi2') == psitilde exactly, and
             R_lambda(Phi2') == z1^(-theta*e1*g1) * psi1 — i.e.
             R_lambda(Phi2') ~ psi1: the note's S6.2 label tie with its
             EXPLICIT scalar;
      (c-iii) divergence meter: the two key classes diverge (monicized
             R_lambda(Phi2) != psi1) EXACTLY on towers where psitilde is not
             a scalar multiple of psi1 (i.e. some k < g1 has psi1_k != 0 and
             z1^(theta*e1*(g1-k)) != 1); counts must be EQUAL, and > 0
             overall (else the family lost its teeth).
      PREDICTED: 0 violations; divergence counts equal, > 0.
TS2d  MATCHED-label ord transport (TR-3-ORD-X-on-(ii) transport leg;
      Cor-5.15 FGMN-internal leg excluded), per sample f:
      (d-i)  GMN-lawful pairing:  ord_{psi1}(R_lambda(f)) ==
             ord_{psitilde}(R2s(f))   [psitilde = side(Phi2') = sigma psi2'^F,
             monic; label and argument rescale TOGETHER — the note's S6.2];
      (d-ii) harness pairing:     ord_{monicized R_lambda(Phi2)}(R_lambda(f))
             == ord_{psi1}(R2s(f)).
      PREDICTED: 0 mismatches; ord histogram REPORTED, must contain >= 1.
      [RUN 1's mismatched pairing 214/3,536 RED — now itself PREDICTED: the
      run-1 phenomenon is the divergence, not a transport failure.]
TS2e  e0 = 1 controls through the SAME code path: theta = 0, both keys
      coincide, all of the above degenerate; additionally R2s(f) == the GMN
      list exactly (the TR3-S1 identity re-derived by this fresh code).
      PREDICTED: 0 violations. [RUN 1: 0/1,088 GREEN]
==========================================================================
"""
import random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal,
                              fp_norm, fp_scal, fp_ord, eq12, INF, Tower)
import strata_probe as SP          # NEW_ROWS only (module has no side effects)

VIOL = []
COUNTS = {}
ORD_HIST = {}
DIV = {"obs": 0, "pred": 0, "towers": 0}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

# ---------------- the FRESH GMN side (order 1 then order 2, all e0) ----------
def gmn1(T, a):
    """GMN order-1 data for a nonzero digit a, first read (e0,h0), slope
    lambda0 = -h0/e0: returns (s1, r1val) with s1 = initial abscissa of the
    component of N1(a), r1val = R_1(a)(z1) = sum_k c_{s1+k*e0} z1^k in K1."""
    R, K1 = T.R, T.K1
    d0v = dev(R, a, T.Phi0)
    um = [w0(R, b) if b else INF for b in d0v]
    line = min(T.e0*um[m] + m*T.h0 for m in range(len(d0v)) if um[m] < INF)
    on = [m for m in range(len(d0v)) if um[m] < INF
          and T.e0*um[m] + m*T.h0 == line]
    s1, sp1 = min(on), max(on)
    val = K1["zero"]; zp = K1["one"]
    for m in range(s1, sp1 + 1, T.e0):
        b = d0v[m] if m < len(d0v) else []
        if b and um[m] < INF and T.e0*um[m] + m*T.h0 == line:
            val = K1["add"](val, K1["mul"](K1["embed"](T.res_digit(b, um[m])),
                                           zp))
        zp = K1["mul"](zp, T.z1)
    return s1, val

def gmn2(T, f):
    """GMN (18) + Defs 2.19-2.21 at r = 2, all e0: returns
    (s, d, coeffs, on, s1map, umap) with coeffs = [c_s, c_{s+e1}, ...] in K1."""
    R, K1 = T.R, T.K1
    d1 = dev(R, f, T.Phi1)
    u = [(T.w1(a) + i*T.w1Phi1) if a else INF for i, a in enumerate(d1)]
    vals = [(T.e1*u[i] + i*T.h1) if u[i] < INF else INF for i in range(len(d1))]
    m = min(v for v in vals if v < INF)
    on = [i for i in range(len(d1)) if vals[i] == m]
    s, sp = min(on), max(on)
    if (sp - s) % T.e1 != 0:
        viol("TS2a", T.tag, "component endpoints not e1-congruent")
    d = (sp - s)//T.e1
    coeffs, s1map, umap = [], {}, {}
    for k in range(d + 1):
        i = s + k*T.e1
        ai = d1[i] if i < len(d1) else []
        if (not ai) or vals[i] != m:
            coeffs.append(K1["zero"]); continue
        s1, r1val = gmn1(T, ai)
        s1map[i], umap[i] = s1, u[i]
        num = s1 - T.l0*u[i]                    # t1(i) = (s1 - l0*u_i)/e0
        if num % T.e0 != 0:
            viol("TS2a", T.tag, f"t1({i}) not integral")
            coeffs.append(K1["zero"]); continue
        coeffs.append(K1["mul"](K1["pow"](T.z1, num//T.e0), r1val))
    return s, d, coeffs, set(on), s1map, umap

def build_key(T, psi):
    """The Tower's own canonical lift machinery (build_Phi2 verbatim) applied
    to an arbitrary monic label psi over K1: FGMN side read of the result is
    psi (realize1's guarantee, N-1 T5/CERT-tested)."""
    R = T.R; P = []
    for k, cc in enumerate(psi):
        if T.K1["isz"](cc): continue
        gp = (T.g1 - k)*T.gamma2
        tau = T.K1["mul"](T.K1["inv"](T.eps1(gp)), cc) if gp else cc
        Ck = T.realize1(tau, gp) if gp else T.liftK0(tuple([1]+[0]*(T.d0-1)))
        P = padd(R, P, pmul(R, Ck, ppow(R, T.Phi1, T.e1*k)))
    return P

# --------------------------------- families ----------------------------------
def ts2_compare(T, f, shape, labels):
    K1, th = T.K1, T.l0*T.g0*T.h0
    note("TS2a")
    coeffs, meta = T.R2w(f, with_meta=True)
    gamma, s2 = meta["gamma"], meta["s2"]
    s, d, gco, on, s1map, umap = gmn2(T, f)
    jmax = max(len(coeffs) - 1, (s + d*T.e1 - s2)//T.e1)
    for j in range(jmax + 1):
        sj = s2 + j*T.e1
        CF = coeffs[j] if j < len(coeffs) else K1["zero"]
        cG = gco[(sj - s)//T.e1] if (s <= sj <= s + d*T.e1
                                     and (sj - s) % T.e1 == 0) else K1["zero"]
        if (not K1["isz"](CF)) != (sj in on):
            viol("TS2a", T.tag, f"[{shape}] support mismatch at abscissa {sj}")
            return
        if K1["isz"](CF):
            continue
        gj = (gamma - sj*T.gamma2)//T.e1
        sfa, ufa = eq12(gj, T.e0, T.h0)
        s1 = s1map.get(sj)
        # (k1) the integer kernel (EXP)
        if s1 is None or (s1 - sfa) % T.e0 != 0 or s1 < sfa:
            viol("TS2a", T.tag, f"[{shape}] m0 not in Z_>=0 at abscissa {sj}")
            return
        m0 = (s1 - sfa)//T.e0
        tnum = s1 - T.l0*umap[sj]
        if tnum % T.e0 != 0:
            viol("TS2a", T.tag, f"[{shape}] t1({sj}) not integral")
            return
        t1 = tnum//T.e0
        if (T.l0p*sfa - T.l0*ufa) + m0 != t1 + th*sj:
            viol("TS2a", T.tag, f"[{shape}] KERNEL (EXP) FAILS at abscissa "
                 f"{sj}: lhs={(T.l0p*sfa - T.l0*ufa) + m0}, rhs={t1 + th*sj}")
            return
        # (k2) Lemma A-GEN factorization
        _, r1val = gmn1(T, meta["dev"][sj])
        pred = K1["mul"](T.eps1(gj), K1["mul"](K1["pow"](T.z1, m0), r1val))
        if CF != pred:
            viol("TS2a", T.tag, f"[{shape}] A-GEN factorization fails at {sj}")
            return
        # (k3) the closed form
        if CF != K1["mul"](K1["pow"](T.z1, th*sj), cG):
            viol("TS2a", T.tag, f"[{shape}] closed form fails at {sj}")
            return
    # ---- TS2b: the assembled two-form on side reads ----
    note("TS2b")
    side, j0, _ = T.R2s(f)
    pred = [K1["mul"](K1["pow"](T.z1, th*(s + k*T.e1)), gco[k])
            for k in range(d + 1)]
    if list(side) != fp_norm(K1, pred):
        viol("TS2b", T.tag, f"[{shape}] two-form side list mismatch")
        return
    if len(side) != d + 1 or K1["isz"](side[0]) or K1["isz"](side[-1]):
        viol("TS2b", T.tag, f"[{shape}] length/ends: len={len(side)} vs "
                            f"d+1={d+1}")
        return
    if j0 != (s - s2)//T.e1 or j0 != s//T.e1:
        viol("TS2b", T.tag, f"[{shape}] j0={j0} != (s-s2)/e1 or floor(s/e1)")
        return
    # ---- TS2e: e0 = 1 control — the TR3-S1 identity through this code ----
    if T.e0 == 1:
        note("TS2e")
        if list(side) != fp_norm(K1, gco):
            viol("TS2e", T.tag, f"[{shape}] e0=1 control: side != R_lambda")
            return
    # ---- TS2d: MATCHED-label ord transport (v2) ----
    if labels is not None:
        psitilde, rlam2m = labels
        note("TS2d")
        o1 = fp_ord(K1, gco, T.psi1)          # GMN side, GMN-lawful label
        o2 = fp_ord(K1, side, psitilde)       # FGMN side, matched label
        ORD_HIST[o1] = ORD_HIST.get(o1, 0) + 1
        if o1 != o2:
            viol("TS2d", T.tag, f"[{shape}] (d-i) ord mismatch: "
                 f"ord_psi1(R_lam)={o1}, ord_psitilde(side)={o2}")
            return
        o3 = fp_ord(K1, gco, rlam2m)          # GMN side, harness-key label
        o4 = fp_ord(K1, side, T.psi1)         # FGMN side, matched label
        if o3 != o4:
            viol("TS2d", T.tag, f"[{shape}] (d-ii) ord mismatch: "
                 f"ord_Rlam2(R_lam)={o3}, ord_psi1(side)={o4}")

def label_ties(T):
    """TS2c v2: both key conventions; returns (psitilde, rlam2m) labels."""
    K1, th = T.K1, T.l0*T.g0*T.h0
    note("TS2c")
    # (c-i) the harness (FGMN-normalized) key
    s, d, gco, _, _, _ = gmn2(T, T.Phi2)
    side, j0, _ = T.R2s(T.Phi2)
    ok = (s == 0 and d == T.g1 and j0 == 0)
    if list(side) != fp_norm(K1, T.psi1):
        ok = False
    t1c = fp_norm(K1, [K1["mul"](T.psi1[k], K1["pow"](T.z1, -th*T.e1*k))
                       for k in range(len(T.psi1))])
    if fp_norm(K1, gco) != t1c:
        ok = False
    if not ok:
        viol("TS2c", T.tag, f"(c-i) harness-key tie fails: s0={s}, d={d} "
                            f"(g1={T.g1}), j0={j0}")
    # (c-ii) the constructed GMN-lawful key
    psitilde = fp_norm(K1, [K1["mul"](T.psi1[k],
                                      K1["pow"](T.z1, th*T.e1*(k - T.g1)))
                            for k in range(len(T.psi1))])
    P2p = build_key(T, psitilde)
    sp, dp, gcop, _, _, _ = gmn2(T, P2p)
    sidep, j0p, _ = T.R2s(P2p)
    okp = (sp == 0 and dp == T.g1 and j0p == 0)
    if list(sidep) != list(psitilde):
        okp = False
    lawful = fp_norm(K1, [K1["mul"](K1["pow"](T.z1, -th*T.e1*T.g1), c)
                          for c in T.psi1])
    if fp_norm(K1, gcop) != lawful:
        okp = False
    if not okp:
        viol("TS2c", T.tag, f"(c-ii) lawful-key tie fails: s0={sp}, d={dp}, "
                            f"j0={j0p}")
    # (c-iii) divergence meter
    DIV["towers"] += 1
    lc = gco[-1]
    rlam2m = fp_norm(K1, [K1["mul"](K1["inv"](lc), c) for c in gco])
    obs = (rlam2m != fp_norm(K1, T.psi1))
    pred = any((not K1["isz"](T.psi1[k]))
               and K1["pow"](T.z1, th*T.e1*(T.g1 - k)) != K1["one"]
               for k in range(T.g1))
    if obs: DIV["obs"] += 1
    if pred: DIV["pred"] += 1
    if obs != pred:
        viol("TS2c", T.tag, f"(c-iii) divergence meter: obs={obs}, "
                            f"pred={pred}")
    return psitilde, rlam2m

def run_tower(T, nf=24):
    R = T.R
    labels = label_ties(T)
    def go(f, shape): ts2_compare(T, f, shape, labels)
    for _ in range(nf):
        f = T.rand_opoly(random.randrange(0, int(2.2*T.degPhi2) + 1), pimax=5)
        if not f: f = [R["pi_pow"](random.randrange(0, 4))]
        go(f, "rand")
    for _ in range(nf//2):
        go(T.rand_structured(random.choice([2, 3, 4])), "struct")
    for _ in range(nf//2):
        a = random.randrange(1, 2*T.e1 + 2)
        g = T.rand_opoly(random.randrange(0, T.degPhi1 + 2), pimax=3)
        if not g: g = [R["one"]]
        go(pmul(R, ppow(R, T.Phi1, a), g), f"Phi1^{a}*g")
    for k in range(0, 4):
        go([R["pi_pow"](k)], f"pi^{k}")
    for _ in range(nf//4):
        go(pscal(R, R["pi_pow"](random.randrange(1, 4)),
                 T.rand_structured(2)), "pi^k*struct")
    for _ in range(nf//3):
        mu = random.choice([1, 2])
        go(pmul(R, ppow(R, T.Phi2, mu), T.rand_structured(2)), f"Phi2^{mu}*Q")
    go(T.Phi2, "Phi2")
    go(ppow(R, T.Phi2, 2), "Phi2^2")

def main():
    random.seed(20260816)
    rows = {tag: (tag, d0, r0, r1) for tag, d0, r0, r1 in G.ROSTER}
    for tag, d0, r0, r1 in SP.NEW_ROWS:
        rows[tag] = (tag, d0, r0, r1)
    E0GE2 = ["C", "D", "E", "H", "J", "K", "L", "M", "N"]
    CTRL = ["A", "B", "G", "I"]
    for kind, p in [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]:
        for tag in E0GE2 + CTRL:
            _, d0, r0, r1 = rows[tag]
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}", mode="C")
            run_tower(T, nf=24)
        print(f"ring ({kind}, p={p}) done: cumulative violations = {len(VIOL)}")
    print("=" * 74)
    print("TR3-S2 PREREGISTERED v2 vs OBSERVED (violations; samples in parens)")
    fams = [("TS2a", "per-slot compose chain (support,k1,k2,k3)",    0),
            ("TS2b", "assembled two-form on side reads + j0",        0),
            ("TS2c", "label ties BOTH key conventions + meter",      0),
            ("TS2d", "MATCHED-label ord transport (d-i)+(d-ii)",     0),
            ("TS2e", "e0=1 controls: TR3-S1 identity",               0)]
    ok = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == pred else "RED"
        if obs != pred: ok = False
        print(f"{fam:5} {desc:47} pred {pred}  obs {obs:4d} ({n:5d})  {verdict}")
    dmeter = "MATCH" if (DIV["obs"] == DIV["pred"] and DIV["obs"] > 0) \
             else "MISMATCH"
    if dmeter == "MISMATCH": ok = False
    print(f"TS2c key-divergence meter: obs {DIV['obs']} == pred "
          f"{DIV['pred']} of {DIV['towers']} towers (pred: equal, > 0)  "
          f"{dmeter}")
    hist = " ".join(f"{k}:{v}" for k, v in sorted(ORD_HIST.items()))
    meter = "MATCH" if any(k >= 1 and v > 0 for k, v in ORD_HIST.items()) \
            else "MISMATCH"
    if meter == "MISMATCH": ok = False
    print(f"TS2d ord histogram (ord: count): {hist}   "
          f"(pred: some ord >= 1)  {meter}")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 20):")
        for v in VIOL[:20]: print("  ", v)
    print(f"TOTAL samples: {sum(COUNTS.values())}")
    print(f"VERDICT: {'ALL GREEN' if ok and not VIOL else 'RED'}")
    return 0 if (ok and not VIOL) else 1

if __name__ == "__main__":
    sys.exit(main())
