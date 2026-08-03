#!/usr/bin/env python3
"""strata3e2_probe.py — TWIST-3 PROBE (synthesis-7 queue #5; charter =
docs/SYNTHESIS_PASS7_2026-08-08.md F2b + queue item 5: "preregistered
order-3 e1 >= 2 measurement of the sealed candidate (theta2 = l1*g1*gamma2);
extends strata3_probe.py; TR3-S4 charters ONLY on an exact law").

THE PROBED STRATUM: order-3 towers with e0 = 1, e1 >= 2, e2 = 1 — the e1
ramification ISOLATED (the charge's "e0 = 1, e2 = 1 first"): the only
nontrivial eq-(12) splits and the only nontrivial eps live at the level-2
read (eps2), exactly where the parent (STRATA3_2026-08-08.md) left the
revival question ("e1 >= 2 exactly where the revival question lives").
Mixed g_j (several >= 2, all three g_j = 1 corners covered), d0 in {1,2},
over the four base rings {Z_2, Z_3, F_2[[t]], F_3[[t]]} = 24 towers.

MACHINERY LINEAGE (inherited, not rewritten): strata3_probe.py's Tower3
(levels 0-2 = grb_order2_check.Tower VERBATIM, N-1-certified; level-3
layer written e2/e1-general there and only stratum-guarded by its roster)
+ its FRESH GMN r=3 side (gmn3/gmn2/gmn1, Defs 2.19-2.21, print
gmn.txt:1823-1906) — imported and reused VERBATIM.  This file adds ONLY:
the e1 >= 2 roster, the (TWIST-3) comparison, the twisted-key rows
(P4'/P5', the ORD-INV discipline one level up), and the meters.  The
parent note sealed exactly this inheritance: "A future probe there
inherits this harness (the general-e2 code paths are written and only the
stratum guard confines them; realize2/gmn3 need the e1 >= 2 abscissa
strides exercised)."

MATCHED-KEY DISCIPLINE (TR3S2 ORD-INV, one level up): both sides consume
the SAME keys Phi0/Phi1/Phi2 at every level.  On THIS stratum theta2 =
l1*g1*gamma2 != 0, so the FGMN-normalized and GMN-lawful level-3 key
classes are PREDICTED TO DIVERGE exactly on the twist-visible towers (the
TR3S2 Lemma-KEY0 bifurcation one level up) — displayed and checked (P4');
the ord transport must therefore use MATCHED LABELS (each side keyed by
its OWN key read, P5'), never the shared-psi2 naive pairing (M8 reports
its failures; TR3S2 measured the naive pairing failing exactly on the
twist-visible set at order 2).

DETERMINISTIC: random.seed(20260818) (fresh; 20260815/16/17 used by the
parents).  EXACT arithmetic only.  PARI fires on the Z_p rows (CERT2 T11
+ CERT3).

=========================== EPS TRANSCRIPTION =================================
Unchanged from the sealed parent (strata3_probe.py header): Def 3.15
corrected reading C (N-1 triple pin at level 1; parent M1 pin at level 2):
    eps2(beta) = z2^(l1p*s - l1*u),  (s,u) = eq12(beta, e1, h1),
    Bezout l1*h1 + l1p*e1 = 1, 0 <= l1 < e1.
On THIS stratum l1 != 0: eps2 is GENUINELY NONTRIVIAL for the first time
in the depth-3 genre — the revival regime.  eps1 == 1 (e0 = 1); level-3
splits have s == 0 and l2 = 0 (e2 = 1).  Def 3.16 at i = 3 as in the
parent: C^F3_j = eps2(gamma_j) * R_{2,gamma_j}(A_{s_j})(z2).

======================= PREREGISTERED CANDIDATE LAWS ==========================
(sealed BEFORE the run; the derivation below is itself part of what the
run tests — the strata_probe A3 discipline)

CANDIDATE 1 (TWIST-3) — THE SEALED CANDIDATE (preregistered UNTESTED at
STRATA3 seal d8ef8d8, S3 of the parent note; THE PROBED LAW):
    (TWIST-3)   C^F3_j = z2^(theta2 * s_j) * c^G3_{s_j},
                theta2 := l1 * g1 * gamma2
— the exact level shift of TR3-S2's accepted order-2 law
theta = l0*g0*gamma1 (gamma1 = h0).
DERIVATION (fixed pre-run; the level-3 transcription of the strata_probe
FAMILY-A derivation).  Let j be an on-line slot at abscissa s_j, digit
A = A_{s_j}, gamma_j = w2(A) its on-line weight, (s,u') = eq12(gamma_j,
e1, h1).
  (i)  FGMN: C^F3_j = eps2(gamma_j) * R_{2,gamma_j}(A)(z2), the inner sum
       indexed from the FORCED abscissa s(gamma_j) = s.
  (ii) GMN (Defs 2.19-2.21 at r = 3, under (H-v3)): c^G3_{s_j} =
       z2^(t2) * R_2(A)(z2) from the ACTUAL initial abscissa s2(A),
       t2 = (s2(A) - l1*u)/e1,  u = w2(A) + s_j*w2Phi2.
  (iii) level-3 Lemma A-GEN (row P2, the parent's mechanism): forced-vs-
       actual bookkeeping gives eps2(gamma_j)^{-1} C^F3_j =
       z2^(m0) * R_2^GMN(A)(z2), m0 = (s2(A) - s)/e1 in Z_{>=0}; the
       inner coefficientwise identity is TR3-S1 on the digit (e0 = 1,
       row P3).
  (iv) hence  C^F3_j / c^G3_{s_j} = eps2(gamma_j) * z2^(m0 - t2)  with
       m0 - t2 = (l1*u - s)/e1.  Bezout: l1*gamma_j = s + e1*(l1*u' -
       l1p*s); w2Phi2 = e1*g1*gamma2; so
           (l1*u - s)/e1 = (l1*u' - l1p*s) + l1*g1*gamma2*s_j,
       and eps2(gamma_j) = z2^(l1p*s - l1*u') cancels the split-dependent
       part EXACTLY:
           C^F3_j / c^G3_{s_j} = z2^(theta2 * s_j),  theta2 = l1*g1*gamma2.
QED (conditional on: the reading-C eps2 transcription, (H-v3), TR3-S1 on
the digits, and the level-3 A-GEN — each its own preregistered row).
Equivalently the MARCHED form: the per-slot ratio ratio(j) := C^F3_j /
c^G3_{s_j} satisfies ratio(j+1) = ratio(j) * z2^(theta2*e2) on
consecutive on-line slots (meter M7).

CANDIDATE 2 (IDENT-3-persists) — THE DEGENERATE/IDENTITY ALTERNATIVE:
    C^F3_j = c^G3_{s_j}  identically even at e1 >= 2
— the no-revival continuation of the parent's measured all-e_j = 1 law.
DISCRIMINATION: at every twist-visible slot (z2^(theta2*s_j) != 1 — the
design table below guarantees such slots exist on 22/24 towers) exactly
one candidate can hold.  If CANDIDATE 2 is the truth, C1 goes RED with
measured residue table == the pure inverse character z2^(-theta2*s_j)
and meter M6 == 0; that table is then the unit's result (no-law report).
If NEITHER holds, the marched-eps residue table (below) is the measured
shape — the D-ITER precedent: RED => the measured table IS the result.

THE MARCHED-EPS RESIDUE TABLE (the RED-catcher, recorded ALWAYS):
    residue(j) := C^F3_j / (z2^(theta2*s_j) * c^G3_{s_j})
per on-line slot, decomposed in z2^a*z1^b where possible.  Under
CANDIDATE 1: residue == 1 everywhere.  Under CANDIDATE 2: residue ==
z2^(-theta2*s_j).  Any other shape: the measured law, reported in full
for the first failing tower (and one sample table per tower goes to the
JSON regardless of verdict).

===================== PREREGISTERED PREDICTIONS (exact) =======================
C1  (TWIST-3) exact at every on-line slot, every sample, every tower
    (including the two designed twist-BLIND towers, where it degenerates
    to IDENT-3).  PREDICTED: 0 violations.  [THE PROBED LAW]
    RED handling: bug-detector rows (P0/V*/CERT*/M0) green first; then
    the witness (tower, f, slot, both values) is printed and the FULL
    measured residue table of the first failing tower is reported — the
    measured shape is then the unit's result (no-law report, D-ITER
    precedent).
P0  GMN-3 side integrity: t2 integral (Def 2.19's printed congruence, now
    GENUINE at l1 != 0), component endpoints e2-congruent, c^G3 != 0
    on-line.  PREDICTED: 0.  [SEALED — GMN's printed proofs, under (H-v3)]
P1  Support agreement level 3: C^F3_j != 0 iff abscissa on the GMN
    on-line set.  PREDICTED: 0.  [CONJ component]
P2  Level-3 Lemma A-GEN z-shift: eps2(gamma_j)^{-1} C^F3_j ==
    z2^(m0) * R_2^GMN(A_j)(z2), m0 = (s2(A_j) - s(gamma_j))/e1 in Z_{>=0}
    — now with NONTRIVIAL eps2 on the left.  PREDICTED: 0.  [CONJ comp.]
P3  Digit-level order-2 identity (TR3-S1 on the probed digits, e0 = 1,
    matched abscissas; e1 does NOT enter the order-2 twist constant
    theta = l0*g0*h0 = 0).  PREDICTED: 0.  [SEALED — TR3-S1 accepted]
P4' Key-class law (Lemma-KEY0 one level up): gmn3(Phi3) has s0 = 0,
    d = g2, and coefficients c^G3_k == z2^(-theta2*k*e2) * psi2_k — the
    GMN-lawful key class is the theta2-TWISTED psi2 class.  Divergence
    from psi2 must occur EXACTLY on towers where some psi2_k != 0
    (k < g2) has z2^(theta2*k*e2) != 1 (computed per tower at runtime).
    PREDICTED: 0 violations; divergent-tower count REPORTED, > 0 overall.
    [derived consequence of C1 + V4; the ORD-INV display]
P5' Matched-LABEL ord transport (ORD-INV one level up): with kG :=
    monic theta2-twisted key (kG_k = z2^(theta2*e2*(g2-k)) * psi2_k),
    ord_{kG}(gmn3-side poly) == ord_{psi2}(R3s(f)) for every sample.
    PREDICTED: 0 mismatches; ord histogram REPORTED, must contain >= 1.
    [derived consequence of C1; matched labels — each side keyed by its
    OWN key read]
V1  VAL-3 multiplicativity w3(fg) = w3(f) + w3(g).  PREDICTED: 0. [BUG-DET]
V2  R3 total multiplicativity R3(fg) = R3(f)R3(g) in K2[y].
    PREDICTED: 0.  [transcription validator]
V3  W-MULT level 3 with delta = floor((s(wf)+s(wg))/e2) == 0 identically
    at e2 = 1 (level-3 carry empty BY STRATUM; the level-2 carry is
    inside R2w, N-1-certified).  PREDICTED: 0, all deltas 0.
V4  Key lift: Phi3 monic, deg = e2*g2*deg(Phi2), w3(Phi3) = e2*g2*gamma3,
    one-sided, R3(Phi3) == psi2 EXACTLY, j0 = 0 — at e1 >= 2 this is the
    FIRST genuine test of build_Phi3's eps2-correction (the tau =
    eps2(gp)^{-1}*c twist in the canonical lift).  PREDICTED: 0.
V5  Two-form/support shape: support at on-line slots, j0 = floor(s0/e2),
    nonzero ends, length = d+1.  PREDICTED: 0.
CERT2  underlying order-2 tower certification (NOW e1 >= 2 rows): G.T1_T2
    (8 samples), G.T5, G.T11 (PARI, Z_p) per instance.  PREDICTED: 0.
CERT3  order-3 external leg (Z_p rows): PARI factorpadic(Phi3)
    irreducible over Q_p; idealprimedec on Q[x]/(Phi3): UNIQUE prime,
    (e,f) == (e0*e1*e2, d0*g0*g1*g2) = (e1, d0*g0*g1*g2) — RAMIFIED
    order-3 keys for the first time in the genre.  PREDICTED: 0.
    Honest deferral: no PARI analogue for the F_p[[t]] rows (as N-1).
M0  DESIGN-TABLE tripwire: measured (theta2, ord(z2), visible) per tower
    == the sealed design table below (design script
    strata3e2_design.py, tower constants only, disclosed).
    PREDICTED: 24/24 match.  [BUG-DET/transcription]
M1  Reading-P discrimination at level 2 (live: BOTH readings nontrivial
    here): at every on-line slot where pfac := eps2_P(gamma_j) /
    eps2_C(gamma_j) != 1, the reading-P prediction pfac*C^F3_j ==
    z2^(theta2*s_j)*c^G3 must FAIL.  PREDICTED: p_refuted == p_visible,
    > 0 overall.  [conditional discrimination given C1; external teeth
    via CERT3 as in the parent]
M2  Inner z-shift m0 > 0 exercised: count > 0 overall.
M3  t2 != 0 exercised: count > 0 overall.
M4  Twist-visible towers (z2^theta2 != 1): PREDICTED == the design table
    (22/24; the two blind = R2C at p = 2, both rings — designed
    degenerate controls where CANDIDATES 1 and 2 coincide).
M5  Twist-visible on-line slots (z2^(theta2*s_j) != 1): count > 0.
M6  CANDIDATE-2 adjudicator: naive IDENT-3 refuted at EVERY twist-visible
    slot: ident_refuted == M5 count, > 0.  [derived consequence of C1]
M7  Marched increment: on consecutive on-line slot pairs, ratio(j+1) /
    ratio(j) == z2^(theta2*e2).  PREDICTED: 0 mismatches, pairs > 0.
M8  Naive shared-psi2 ord pairing (the ORD-INV mismatched form):
    mismatch count REPORTED, no prediction (TR3S2 measured it failing
    exactly on twist-visible towers at order 2; here it fails only where
    the twisted class meets the support — report only).
P5-hist  ord histogram contains ord >= 1 (Phi3^mu families).

(H-v3) DISPLAYED HYPOTHESIS (unchanged from the parent): the GMN-3
ordinate u_i = w2(A_i) + i*w2(Phi2) consumes v3 = w2 — the order-3
extension of the pinned order-2 Def-2.5 identity v2 = w1.  Shared-input
scope: both sides consume the SAME w2.

RED DISCIPLINE: classify via P0/V*/CERT*/M0 first; only with those green
does a RED count as mathematics; any surviving RED is the headline
result, reported with the exact witness and the full measured residue
table (D-ITER precedent).

========================= TOWER ROSTER + DESIGN TABLE =========================
All rows e0 = 1, e2 = 1, e1 in {2,3}; triples (e_j, h_j, g_j); designed
via strata3e2_design.py (tower constants ONLY — theta2, ord(z2),
visibility; NO C^F3/c^G3 comparison was computed pre-seal).  deg Phi3 =
d0*g0*g1*g2*e1 <= 12.
  R2A (1; 1,1,2; 2,1,1; 1,1,2)  e1=2 baseline; g1=1 corner (z2 in K1)
  R2B (1; 1,1,2; 2,3,1; 1,3,3)  h1=3: l1p=-1; cubic psi2; h2=3
  R2C (1; 1,1,1; 2,1,2; 1,1,2)  g0=1 corner (K1=K0); g1=2 (true K2/K1)
  R2D (2; 1,1,1; 2,1,2; 1,1,1)  g2=1 refinement corner; d0=2; K2=F_p^4
  R2E (1; 1,1,2; 3,1,1; 1,1,2)  e1=3 (l1=1)
  R2F (1; 1,1,1; 3,2,2; 1,1,1)  e1=3, h1=2: l1=2, l1p=-1; g1=2; g2=1
Sealed design table (theta2, ord(z2), visible), from strata3e2_design.py:
  R2A: theta2=5   p=2: ord 3 VIS | p=3: ord 2 VIS   (both ring kinds)
  R2B: theta2=7   p=2: ord 3 VIS | p=3: ord 2 VIS
  R2C: theta2=6   p=2: ord 3 BLIND | p=3: ord 8 VIS
  R2D: theta2=6   p=2: ord 5 VIS | p=3: ord 5 VIS
  R2E: theta2=7   p=2: ord 3 VIS | p=3: ord 2 VIS
  R2F: theta2=20  p=2: ord 3 VIS | p=3: ord 8 VIS
(identical for Zp and Fpt at each p — residue arithmetic only), i.e.
22/24 towers visible, the 2 blind = R2C at p=2.

EXIT: 0 iff every preregistered row at its predicted count and all meters
MATCH.  Output: strata3e2_probe_output.txt (tee),
strata3e2_probe_results.json.
"""
import random, math, sys, os, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
import strata3_probe as S3
from grb_order2_check import (dev, pnorm, padd, pmul, ppow, pscal,
                              fp_norm, fp_mul, fp_ord, eq12, bezout,
                              INF)
from strata3_probe import Tower3, gmn2, gmn3, k2_repr

VIOL = []
COUNTS = {}
ORD_HIST = {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))
# re-point the imported GMN side's logging (gmn1/gmn2/gmn3 log via their
# module globals) at THIS unit's ledgers:
S3.note, S3.viol = note, viol

def theta2_of(T3):
    return T3.T.l1 * T3.T.g1 * T3.T.gamma2

# ============================ sealed design table =============================
# (kind-independent: keyed (p, tag) -> (theta2, ord_z2, visible))
DESIGN = {
    (2, "R2A"): (5, 3, True),  (3, "R2A"): (5, 2, True),
    (2, "R2B"): (7, 3, True),  (3, "R2B"): (7, 2, True),
    (2, "R2C"): (6, 3, False), (3, "R2C"): (6, 8, True),
    (2, "R2D"): (6, 5, True),  (3, "R2D"): (6, 5, True),
    (2, "R2E"): (7, 3, True),  (3, "R2E"): (7, 2, True),
    (2, "R2F"): (20, 3, True), (3, "R2F"): (20, 8, True),
}

def ordmul(K, x):
    n = 1; y = x
    while y != K["one"]:
        y = K["mul"](y, x); n += 1
        if n > 10**6: return -1
    return n

# =============================== probe families ===============================
class Meters:
    def __init__(self):
        self.p_visible = 0; self.p_refuted = 0
        self.m0pos = 0; self.t2nz = 0
        self.vis_slots = 0; self.ident_refuted = 0
        self.m7_pairs = 0; self.m7_bad = 0
        self.m8_naive_ord_mismatch = 0

def probe3e2(T3, f, shape, M, sample_tables, want_table=False):
    T, K2 = T3.T, T3.K2
    th2 = theta2_of(T3)
    note("C1")
    coeffs, meta = T3.R3w(f, with_meta=True)
    g, s3 = meta["gamma"], meta["s3"]
    s, d, gco, on, s2map, r2map, uvec = gmn3(T3, f)
    if s < s3 or (s - s3) % T3.e2 != 0:
        viol("P1", T3.tag, f"[{shape}] GMN on-line start {s} below/off the "
                           f"forced abscissa class {s3}")
        return
    jmax = max(len(coeffs) - 1, (s + d*T3.e2 - s3)//T3.e2)
    residue_table = []
    red_here = False
    prev = None   # (j, ratio) of previous on-line slot
    zstep = K2["pow"](T3.z2, th2*T3.e2)
    for j in range(jmax + 1):
        sj = s3 + j*T3.e2
        CF = coeffs[j] if j < len(coeffs) else K2["zero"]
        if s <= sj <= s + d*T3.e2 and (sj - s) % T3.e2 == 0:
            cG = gco[(sj - s)//T3.e2]
        else:
            cG = K2["zero"]
        note("P1")
        if (not K2["isz"](CF)) != (sj in on):
            viol("P1", T3.tag, f"[{shape}] support mismatch at abscissa {sj}: "
                 f"CF!=0 is {not K2['isz'](CF)}, on-line is {sj in on}")
            return
        if K2["isz"](CF):
            continue
        gj = (g - sj*T3.gamma3)//T3.e2
        # C1 THE LAW (TWIST-3)
        note("C1x")
        twist = K2["pow"](T3.z2, th2*sj)
        ratio = K2["mul"](CF, K2["inv"](cG))
        residue = K2["mul"](ratio, K2["inv"](twist))
        residue_table.append((sj, k2_repr(T3, ratio), k2_repr(T3, residue)))
        if residue != K2["one"]:
            viol("C1", T3.tag,
                 f"[{shape}] TWIST-3 FAILS at abscissa {sj} (slot {j}): "
                 f"measured ratio CF/cG = {k2_repr(T3, ratio)}, residue "
                 f"ratio/z2^(theta2*sj) = {k2_repr(T3, residue)} "
                 f"[theta2={th2}, CF={CF}, cG={cG}]")
            red_here = True
        # M5/M6 the CANDIDATE-2 adjudicator
        if twist != K2["one"]:
            M.vis_slots += 1
            if CF != cG: M.ident_refuted += 1
        # M7 marched increment
        if prev is not None and prev[0] == j - 1:
            M.m7_pairs += 1
            if K2["mul"](ratio, K2["inv"](prev[1])) != zstep:
                M.m7_bad += 1
        prev = (j, ratio)
        if red_here:
            continue                    # keep measuring the full table
        # P2 level-3 Lemma A-GEN z-shift (nontrivial eps2 now)
        note("P2")
        sfa, ufa = eq12(gj, T.e1, T.h1)
        s2i = s2map.get(sj)
        if s2i is None or (s2i - sfa) % T.e1 != 0 or s2i < sfa:
            viol("P2", T3.tag, f"[{shape}] m0 not in Z>=0 at abscissa {sj}")
            return
        m0 = (s2i - sfa)//T.e1
        inner = K2["mul"](K2["inv"](T3.eps2(gj)), CF)
        if inner != K2["mul"](K2["pow"](T3.z2, m0), r2map[sj]):
            viol("P2", T3.tag, f"[{shape}] level-3 A-GEN z-shift fails "
                               f"at abscissa {sj} (m0={m0})")
            return
        if m0 > 0: M.m0pos += 1
        if (s2i - T3.l1*uvec[sj])//T.e1 != 0: M.t2nz += 1
        # P3 digit-level order-2 identity (TR3-S1 on the digit, e0 = 1)
        note("P3")
        A = meta["dev"][sj]
        co2F, meta2 = T.R2w(A, with_meta=True)
        s2F = meta2["s2"]
        s2G, d2G, co2G, on2G, _, _ = gmn2(T, A, tag=T3.tag)
        kmax = max(len(co2F) - 1, (s2G + d2G*T.e1 - s2F)//T.e1)
        for k in range(kmax + 1):
            ak = s2F + k*T.e1
            c2F = co2F[k] if k < len(co2F) else T.K1["zero"]
            if s2G <= ak <= s2G + d2G*T.e1 and (ak - s2G) % T.e1 == 0:
                c2G = co2G[(ak - s2G)//T.e1]
            else:
                c2G = T.K1["zero"]
            if c2F != c2G:
                viol("P3", T3.tag, f"[{shape}] digit-level order-2 identity "
                                   f"fails at inner abscissa {ak}")
                return
        # M1 reading-P discrimination (both readings nontrivial here)
        pfac = K2["mul"](T3.eps2(gj, mode="P"),
                         K2["inv"](T3.eps2(gj, mode="C")))
        if pfac != K2["one"]:
            M.p_visible += 1
            if K2["mul"](pfac, CF) != K2["mul"](twist, cG):
                M.p_refuted += 1
    if want_table or red_here:
        sample_tables.append(dict(tower=T3.tag, shape=shape, theta2=th2,
                                  red=red_here, table=residue_table))
    if red_here:
        viol("C1", T3.tag, f"[{shape}] full measured residue table "
                           f"(abscissa, CF/cG, residue): {residue_table}")
        return
    # V5 two-form/support shape
    note("V5")
    side, j0, _ = T3.R3s(f)
    if j0 != (meta["s0"] - s3)//T3.e2 or j0 != meta["s0"]//T3.e2:
        viol("V5", T3.tag, f"[{shape}] j0={j0} != floor(s0/e2)")
        return
    d_pred = (meta["sprime"] - meta["s0"])//T3.e2
    if len(side) != d_pred + 1 or (side and (K2["isz"](side[0])
                                             or K2["isz"](side[-1]))):
        viol("V5", T3.tag, f"[{shape}] side length/ends: len={len(side)} "
                           f"vs d+1={d_pred+1}")
        return
    # P5' matched-LABEL ord transport (ORD-INV one level up): GMN side
    # keyed by the theta2-twisted monic key kG, FGMN side by psi2
    note("P5")
    kG = [K2["mul"](K2["pow"](T3.z2, th2*T3.e2*(T3.g2 - k)), c)
          for k, c in enumerate(T3.psi2)]
    o1 = fp_ord(K2, fp_norm(K2, gco), kG)
    o2 = fp_ord(K2, side, T3.psi2)
    ORD_HIST[o1] = ORD_HIST.get(o1, 0) + 1
    if o1 != o2:
        viol("P5", T3.tag, f"[{shape}] matched-label ord mismatch: "
                           f"ord_kG(R_lam3)={o1}, ord_psi2(R3)={o2}")
    # M8 naive shared-psi2 pairing (report only)
    if fp_ord(K2, fp_norm(K2, gco), fp_norm(K2, T3.psi2)) != o2:
        M.m8_naive_ord_mismatch += 1

def pairs3e2(T3, npairs=10):
    K2 = T3.K2
    for _ in range(npairs):
        f = T3.rand_structured3(random.choice([2, 3]))
        h = T3.rand_structured3(random.choice([2, 3]))
        fh = pmul(T3.R, f, h)
        note("V1")
        wf, wh, wfh = T3.w3(f), T3.w3(h), T3.w3(fh)
        if wfh != wf + wh:
            viol("V1", T3.tag, f"VAL-3: w3(fh)={wfh} != {wf}+{wh}")
            continue
        note("V2")
        Rf, _, _ = T3.R3s(f); Rh, _, _ = T3.R3s(h); Rfh, _, _ = T3.R3s(fh)
        if fp_norm(K2, Rfh) != fp_mul(K2, Rf, Rh):
            viol("V2", T3.tag, "R3(fh) != R3(f)R3(h)")
        note("V3")
        sf, _ = eq12(wf, T3.e2, T3.h2); sh, _ = eq12(wh, T3.e2, T3.h2)
        delta = (sf + sh)//T3.e2
        if delta != 0:
            viol("V3", T3.tag, f"delta={delta} != 0 on the e2=1 stratum")
        Wf = T3.R3w(f); Wh = T3.R3w(h); Wfh = T3.R3w(fh)
        pred = fp_mul(K2, [K2["zero"]]*delta + [K2["one"]],
                      fp_mul(K2, fp_norm(K2, Wf), fp_norm(K2, Wh)))
        if fp_norm(K2, Wfh) != pred:
            viol("V3", T3.tag, f"W-MULT-3 fails (delta={delta})")

def key3e2(T3, tower_rec):
    T, R, K2 = T3.T, T3.R, T3.K2
    th2 = theta2_of(T3)
    note("V4")
    P3p = T3.Phi3
    if len(P3p) - 1 != T3.degPhi3:
        viol("V4", T3.tag, f"deg Phi3 = {len(P3p)-1} != {T3.degPhi3}")
    lead = P3p[-1] if P3p else R["zero"]
    if R["isz"](lead) or not R["isz"](R["add"](lead, R["neg"](R["one"]))):
        viol("V4", T3.tag, "Phi3 not monic")
    d2, vals, g = T3.w3_data(P3p)
    if g != T3.w3Phi3:
        viol("V4", T3.tag, f"w3(Phi3) = {g} != e2*g2*gamma3 = {T3.w3Phi3}")
    for j, c in enumerate(d2):
        if c and T3.e2*vals[j] + j*T3.gamma3 < T3.w3Phi3:
            viol("V4", T3.tag, f"Phi3 slot {j} below weight")
    side, j0, meta = T3.R3s(P3p)
    if j0 != 0:
        viol("V4", T3.tag, f"R3(Phi3): j0 = {j0} != 0")
    if side != fp_norm(K2, T3.psi2):
        viol("V4", T3.tag, "R3(Phi3) != psi2 exactly (eps2-corrected "
                           "canonical lift broken at e1 >= 2?)")
    # P4' GMN-side key class: the theta2-TWISTED psi2 (Lemma-KEY0 one up)
    note("P4")
    s, d, gco, on, _, _, _ = gmn3(T3, P3p)
    if s != 0 or d != T3.g2:
        viol("P4", T3.tag, f"gmn3(Phi3): s0={s}, d={d} (g2={T3.g2})")
    else:
        pred = [K2["mul"](K2["pow"](T3.z2, -th2*k*T3.e2), c)
                for k, c in enumerate(T3.psi2)]
        if [gco[k] if k < len(gco) else K2["zero"] for k in range(T3.g2+1)] \
           != pred:
            viol("P4", T3.tag, "gmn3(Phi3) != z2^(-theta2*k*e2)-twisted psi2")
        kdiv = fp_norm(K2, gco) != fp_norm(K2, T3.psi2)
        kdiv_pred = any(not K2["isz"](c)
                        and K2["pow"](T3.z2, th2*k*T3.e2) != K2["one"]
                        for k, c in enumerate(T3.psi2) if k < T3.g2)
        if kdiv != kdiv_pred:
            viol("P4", T3.tag, f"key-divergence criterion mismatch: "
                               f"observed {kdiv}, predicted {kdiv_pred}")
        tower_rec["key_diverges"] = kdiv

def run_tower(T3, M, sample_tables, nf=24):
    T, R = T3.T, T3.R
    first = [True]
    def probe(f, shape):
        probe3e2(T3, f, shape, M, sample_tables, want_table=first[0])
        first[0] = False
    for _ in range(nf):
        f = T.rand_opoly(random.randrange(0, int(2.2*T3.degPhi3) + 1),
                         pimax=5)
        if not f: f = [R["pi_pow"](random.randrange(0, 4))]
        probe(f, "rand")
    for _ in range(nf//2):
        probe(T3.rand_structured3(random.choice([2, 3, 4])), "struct")
    for _ in range(nf//2):
        a = random.randrange(1, 2*T3.e2 + 2)
        h = T.rand_opoly(random.randrange(0, T.degPhi2 + 2), pimax=3)
        if not h: h = [R["one"]]
        probe(pmul(R, ppow(R, T.Phi2, a), h), f"Phi2^{a}*g")
    for _ in range(nf//2):
        a = random.randrange(1, 4)
        h = T.rand_opoly(random.randrange(0, T.degPhi1 + 2), pimax=3)
        if not h: h = [R["one"]]
        probe(pmul(R, ppow(R, T.Phi1, a), h), f"Phi1^{a}*g")
    for k in range(0, 3):
        probe([R["pi_pow"](k)], f"pi^{k}")
    for _ in range(nf//4):
        mu = random.choice([1, 2])
        probe(pmul(R, ppow(R, T3.Phi3, mu), T3.rand_structured3(2)),
              f"Phi3^{mu}*Q")
    pairs3e2(T3, npairs=10)

# ==================================== main ====================================
ROSTER3E2 = [
    # (tag, d0, (e0,h0,g0), (e1,h1,g1), (e2,h2,g2))
    ("R2A", 1, (1,1,2), (2,1,1), (1,1,2)),
    ("R2B", 1, (1,1,2), (2,3,1), (1,3,3)),
    ("R2C", 1, (1,1,1), (2,1,2), (1,1,2)),
    ("R2D", 2, (1,1,1), (2,1,2), (1,1,1)),
    ("R2E", 1, (1,1,2), (3,1,1), (1,1,2)),
    ("R2F", 1, (1,1,1), (3,2,2), (1,1,1)),
]

def cert3_pari(T3, pari):
    if T3.kind != "Zp" or pari is None: return
    note("CERT3")
    coeffs = [int(c) for c in T3.Phi3]
    F = pari.Pol(list(reversed(coeffs)))
    fac = pari.factorpadic(F, T3.p, 80)
    if len(fac[0]) != 1 or int(fac[1][0]) != 1:
        viol("CERT3", T3.tag, f"PARI: Phi3 NOT irreducible over Q_{T3.p}")
        return
    nf = pari.nfinit([F, [T3.p]])
    dec = pari.idealprimedec(nf, T3.p)
    T = T3.T
    e_pred, f_pred = T3.E3, T.d0*T.g0*T.g1*T3.g2
    if len(dec) != 1:
        viol("CERT3", T3.tag, f"PARI: {len(dec)} primes above p (pred 1)")
        return
    pr = dec[0]
    if (int(pr[2]), int(pr[3])) != (e_pred, f_pred):
        viol("CERT3", T3.tag, f"PARI (e,f) = ({int(pr[2])},{int(pr[3])}) "
                              f"!= pred ({e_pred},{f_pred})")

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
        print(f"WARNING: cypari2 unavailable ({exc}); CERT PARI legs skipped "
              "-> RED if predicted")
    configs = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]
    M = Meters()
    tower_recs = []
    sample_tables = []
    m0_bad = 0
    cert2_viol = 0; cert2_n = 0
    for kind, p in configs:
        for tag, d0, r0, r1, r2 in ROSTER3E2:
            full = f"{kind},p={p},{tag}"
            T3 = Tower3(kind, p, d0, r0, r1, r2, full)
            th2 = theta2_of(T3)
            # M0 design-table tripwire
            note("M0")
            oz = ordmul(T3.K2, T3.z2)
            vis = T3.K2["pow"](T3.z2, th2) != T3.K2["one"]
            if DESIGN[(p, tag)] != (th2, oz, vis):
                m0_bad += 1
                viol("M0", full, f"design-table mismatch: measured "
                     f"({th2},{oz},{vis}) != sealed {DESIGN[(p, tag)]}")
            # CERT2: re-certify the underlying order-2 tower (e1 >= 2 rows)
            gv0 = len(G.VIOL)
            gc0 = sum(G.COUNTS.get(k, 0) for k in ("T1", "T2", "T5", "T11"))
            G.T1_T2(T3.T, nf=8)
            G.T5(T3.T)
            G.T11(T3.T, pari)
            cert2_viol += len(G.VIOL) - gv0
            cert2_n += sum(G.COUNTS.get(k, 0)
                           for k in ("T1", "T2", "T5", "T11")) - gc0
            # CERT3: external leg on the (now ramified) order-3 key
            cert3_pari(T3, pari)
            # the probe
            rec = dict(tower=full, d0=d0, r0=r0, r1=r1, r2=r2,
                       gamma2=T3.T.gamma2, gamma3=T3.gamma3,
                       theta2=th2, ord_z2=oz, twist_visible=vis,
                       degPhi3=T3.degPhi3)
            key3e2(T3, rec)
            run_tower(T3, M, sample_tables, nf=24)
            tower_recs.append(rec)
        print(f"[{time.time()-t0:6.1f}s] ring ({kind},p={p}) done: "
              f"cumulative violations = {len(VIOL)} "
              f"(+CERT2 {cert2_viol}, G-side {len(G.VIOL)})")
    # ------------------------------- report ---------------------------------
    print()
    print("=" * 78)
    print("TWIST-3 PROBE (order-3, e0=1, e1>=2, e2=1) — PREDICTED vs OBSERVED")
    print("=" * 78)
    fams = [
        ("C1", "(TWIST-3) CF = z2^(th2*sj)*cG        [THE LAW]   ", 0),
        ("P0", "GMN-3 integrity (t2 int, comp, c!=0) [SEALED]    ", 0),
        ("P1", "support agreement level 3            [CONJ comp.]", 0),
        ("P2", "level-3 A-GEN z-shift (m0 in Z>=0)   [CONJ comp.]", 0),
        ("P3", "digit-level order-2 identity         [TR3-S1]    ", 0),
        ("P4", "key class = theta2-twisted psi2      [KEY0 lift] ", 0),
        ("P5", "matched-LABEL ord transport (kG)     [ORD-INV]   ", 0),
        ("V1", "VAL-3 multiplicativity               [BUG-DET]   ", 0),
        ("V2", "R3 total multiplicativity            [BUG-DET]   ", 0),
        ("V3", "W-MULT-3, delta == 0 (no-carry ctrl) [BUG-DET]   ", 0),
        ("V4", "key lift R3(Phi3)=psi2 exact         [BUG-DET]   ", 0),
        ("V5", "two-form/support shape + j0          [BUG-DET]   ", 0),
        ("M0", "design-table tripwire                [BUG-DET]   ", 0),
    ]
    all_green = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == pred else "RED"
        if verdict == "RED": all_green = False
        print(f"{fam:3} {desc:57} pred {pred}  obs {obs:5d} ({n:6d})  "
              f"{verdict}")
    print(f"    (C1 on-line slot comparisons: {COUNTS.get('C1x', 0)})")
    cert3_obs = sum(1 for v in VIOL if v[0] == "CERT3")
    c3v = "GREEN" if cert3_obs == 0 else "RED"
    if cert3_obs: all_green = False
    print(f"CERT3 PARI order-3 external leg (Zp rows, e=e1 ramified)   "
          f"pred 0  obs {cert3_obs:5d} ({COUNTS.get('CERT3',0):6d})  {c3v}")
    c2v = "GREEN" if cert2_viol == 0 else "RED"
    if cert2_viol: all_green = False
    print(f"CERT2 order-2 tower certification (G.T1/T2/T5/T11)         "
          f"pred 0  obs {cert2_viol:5d} ({cert2_n:6d})  {c2v}")
    m1 = "MATCH" if (M.p_refuted == M.p_visible and M.p_visible > 0) \
         else "MISMATCH"
    if m1 == "MISMATCH": all_green = False
    print(f"M1 reading-P refuted at P-visible slots: {M.p_refuted}"
          f"/{M.p_visible} (pred: equal, > 0)  {m1}")
    m2 = "MATCH" if M.m0pos > 0 else "MISMATCH"
    m3 = "MATCH" if M.t2nz > 0 else "MISMATCH"
    if m2 == "MISMATCH" or m3 == "MISMATCH": all_green = False
    print(f"M2 inner z-shift m0 > 0 exercised: {M.m0pos} slots "
          f"(pred > 0)  {m2}")
    print(f"M3 t2 != 0 exercised: {M.t2nz} slots (pred > 0)  {m3}")
    vis_towers = sum(1 for r in tower_recs if r["twist_visible"])
    m4 = "MATCH" if vis_towers == 22 else "MISMATCH"
    if m4 == "MISMATCH": all_green = False
    print(f"M4 twist-visible towers: {vis_towers}/{len(tower_recs)} "
          f"(pred 22 per design table)  {m4}")
    m5 = "MATCH" if M.vis_slots > 0 else "MISMATCH"
    if m5 == "MISMATCH": all_green = False
    print(f"M5 twist-visible on-line slots: {M.vis_slots} (pred > 0)  {m5}")
    m6 = "MATCH" if (M.ident_refuted == M.vis_slots and M.vis_slots > 0) \
         else "MISMATCH"
    if m6 == "MISMATCH": all_green = False
    print(f"M6 naive IDENT-3 refuted at visible slots: {M.ident_refuted}"
          f"/{M.vis_slots} (pred: equal, > 0)  {m6}")
    m7 = "MATCH" if (M.m7_bad == 0 and M.m7_pairs > 0) else "MISMATCH"
    if m7 == "MISMATCH": all_green = False
    print(f"M7 marched increment == z2^(theta2*e2): {M.m7_bad} bad of "
          f"{M.m7_pairs} consecutive pairs (pred 0 bad, pairs > 0)  {m7}")
    print(f"M8 naive shared-psi2 ord pairing mismatches (REPORT ONLY): "
          f"{M.m8_naive_ord_mismatch}")
    kdiv_towers = sum(1 for r in tower_recs if r.get("key_diverges"))
    kd = "MATCH" if kdiv_towers > 0 else "MISMATCH"
    if kd == "MISMATCH": all_green = False
    print(f"P4' key-class divergent towers: {kdiv_towers}/{len(tower_recs)} "
          f"(pred > 0; criterion checked per tower)  {kd}")
    hist = " ".join(f"{k}:{v}" for k, v in sorted(ORD_HIST.items()))
    m5h = "MATCH" if any(k >= 1 and v > 0 for k, v in ORD_HIST.items()) \
          else "MISMATCH"
    if m5h == "MISMATCH": all_green = False
    print(f"P5 ord histogram (ord: count): {hist}   (pred: some ord >= 1)  "
          f"{m5h}")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 30):")
        for v in VIOL[:30]:
            print("  ", v)
    if G.VIOL:
        print(f"{len(G.VIOL)} CERT2 VIOLATIONS (first 10):")
        for v in G.VIOL[:10]:
            print("  ", v)
    total = sum(COUNTS.values()) + cert2_n
    print(f"TOTAL samples: {total}   elapsed {time.time()-t0:.1f}s")
    verdict = all_green and not VIOL and not G.VIOL
    print(f"VERDICT (preregistered rows): "
          f"{'ALL GREEN' if verdict else 'RED — see above'}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "strata3e2_probe_results.json"), "w") as fh:
        json.dump(dict(
            seed=20260818,
            violations=[list(v) for v in VIOL],
            cert2_violations=[list(v) for v in G.VIOL],
            counts=COUNTS,
            cert2_n=cert2_n,
            meters=dict(p_visible=M.p_visible, p_refuted=M.p_refuted,
                        m0pos=M.m0pos, t2nz=M.t2nz,
                        vis_slots=M.vis_slots,
                        ident_refuted=M.ident_refuted,
                        m7_pairs=M.m7_pairs, m7_bad=M.m7_bad,
                        m8_naive_ord_mismatch=M.m8_naive_ord_mismatch),
            ord_hist=ORD_HIST,
            towers=tower_recs,
            residue_tables=sample_tables), fh, indent=1, default=str)
    return 0 if verdict else 1

if __name__ == "__main__":
    sys.exit(main())
