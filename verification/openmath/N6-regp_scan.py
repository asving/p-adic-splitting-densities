#!/usr/bin/env python3
"""N6-regp — numeric scan of Conjecture M17: the per-p regularity gate (REG-p)
= (r1) ∧ (r2) at the REAL (bridged) instance, all n ∈ {2,3}, all primes p < 500.

===========================================================================
WHAT THE LEAN/NOTE STATEMENT ASSERTS (fidelity mapping — read this first)
===========================================================================

Lean form (MovesU/Defs.lean:209, the round-2 retype; statement-fenced):

    def RegP {p} (D : RegData p) : Prop :=
      ∀ q₀ ∈ D.Pool, ∀ e : D.Block,
        (r1)  DefinedAt (det (1 - K_e)) q₀  ∧  (det (1 - K_e)).eval q₀ ≠ 0
        (r2)  ∀ g ∈ E(e), DefinedAt g q₀ ∧ g.eval q₀ = D.act g q₀

with E(e) = {K_e entries} ∪ {b_e^{term,fin}} ∪ {b_e^split} ∪ {per-cell J}
          ∪ {ι_e} ∪ {W_Ŝ} ∪ {β legs at every δ ∈ depthSet}          (SQ.4 schema,
MOVES_2026-07-24.md:13160-13199), Pool = {p^δ : δ ∈ depthSet}.

At the BRIDGED instance D = bridgeRegData(C_real) (MovesU/BridgeB8_regData.lean):
  * act = bridgeAct (BridgeB3_act.lean) = the literal RatFunc evaluation whenever
    q₀ is not a pole, junk 0 otherwise.  Hence the value-agreement half of (r2)
    follows from DefinedAt BY CONSTRUCTION at the bridge (`bridgeAct_ok` = dif_pos).
    The SUBSTANTIVE per-pool agreement — that the fixed ℚ(q)-elements' values at
    q₀ = p^δ ARE the classifier's active reads (CTS-M(ii-c)) — lives in the claim
    that the table's count/mass polynomials are the true finite-field counts at
    every prime power q₀, including wild ones (the "ENTRY VANISHING" exactness of
    CASE_RESUMN3_SEALED_PREDICTIONS.md S3).  That is what we test as (r2-act).
  * The IB-B15a countermodel (BridgeB15a_r2Neg.lean) shows (r2) definedness on the
    dite families (b^split / β legs = blockSolve read through powSubst at descent
    pools) is NOT a formal consequence of the carried laws — it must be checked at
    the REAL tables.  That per-pool obligation (`BridgeDiteOK`) is exactly the
    (r2-def) scan below applied to the β-solve entries at every pool point.

THE REAL TABLES USED (with provenance):
  * n = 2, the Lean gate instance (MovesS N2 corpus; the ONLY UCarriers-shaped
    instance in the repo): block 1 K = 0; block 2 one state, kcol = q^{-3},
    termFin masses 1 - 1/q -> (1,1)^2 and 1/q - q^{-3} -> (1,2);
    det(1-K_2) = (q^3-1)/q^3 (Lean-PROVED, N2Det.lean n2_det); solve
    β = (q^2/(q^2+q+1), (q+1)/(q^2+q+1)); consumedDeltas = {1} (Lean-PROVED,
    N2ShapeFam.lean n2_shapefam).  NOTE: this is the dual-audited GATE instance
    (coarsened verdict roster), kept as the literal Lean-bridged object.
  * n = 2, the true monic quadratic solve (padic_types.monic_quad_pred provenance;
    block 2 = the RESUM-n3 S1 block-2 = the true quadratic cluster law):
    K_2 = (q-1)/(q^3-1); b_2 = (split (q-1)(q-2)/(2(q^3-1)),
    inert q(q-1)/(2(q^3-1)), w2 q^2/(q^2+q+1), vv 1/(q^2+q+1));
    root read: dist (q-1)/(2q), inert (q-1)/(2q), double 1/q -> β_2 leg (δ=1).
  * n = 3, the RESUM-n3 S1 SEALED solve (CASE_RESUMN3_SEALED_PREDICTIONS.md,
    dual-accepted, census-verified 65/65): blocks 2 and 3 as displayed there
    (transcribed below verbatim), root letters over q^3, J split legs at δ = 1
    ("NO delta = 2 legs exist at n = 3" — sealed).

POOLS.  Faithful Q(p) = {p} for both n (n=2: consumedDeltas = {1} Lean-proved;
n=3: all split/shape legs at δ = 1 per the seal).  We ALSO scan the conservative
superset {p, p^2, p^3} (labelled 'superset'), which subsumes any δ ≤ 3 reading of
the depth closure and the powSubst descent reads of the dite families — passing
on the superset a fortiori passes the faithful form.

WHAT IS COMPUTED, PER (n, p, q₀):
  (r1)      det(1-K_e) as an exact cancelled num/den pair: den(q₀) ≠ 0 AND
            num(q₀) ≠ 0, for every block e.
  (r2-def)  every roster entry g (all seven families + the β-solve entries, the
            dite/BridgeDiteOK obligation included): cancelled den(q₀) ≠ 0.
  (r2-act)  (i) every count polynomial's value at q₀ is a NONNEGATIVE INTEGER
            (necessary to be an active-read cardinality; a negative or fractional
            value = active-value disagreement = (r2) failure);
            (ii) at small prime powers q₀ (2,3,4,5,7,8,9,11,13,25,27): the count
            polynomials EQUAL brute-force factor-shape counts over F_{q₀}
            (exhaustive enumeration; this pins the literal values to the true
            active reads, wild pools included).
  (extra)   E0 escape margin K_e(q₀) < 1 and activity-cell size q₀-1 ≠ 0
            (all states active => full matrix = active submatrix, junk blocks
            empty) — NOT part of (REG-p) (rev-5 separateness), reported only.

SIMPLIFICATIONS / GAPS FLAGGED (the honesty ledger):
  F1. ι_e at these instances is the trivial entry normalization (≡ 1); included
      pro forma.  The Lean n2 gate's concrete ι/W values are not re-derived from
      the N2 corpus here; its mathematically substantive entries (K, bterm, det,
      β) are covered.  (The true-table W entries ARE covered: the root letters.)
  F2. The ACT agreement is anchored at depth-1 reads (residual/root counts) by
      brute force; deeper-read agreement is structural (the same residual laws
      repeat per level, summed geometrically) and was census-sealed at
      q₀ ∈ {2,3,4} by RESUM-n3 (65/65).  We do NOT re-run a census here.
  F3. No Lean UCarriers instance exists yet for n=3; the n=3 table is the sealed
      S1 display (the note-level real object the bridge will consume).
  F4. p^δ pools with δ ≥ 2 are prime powers, not primes; the brute anchors cover
      the prime-power values 4, 8, 9, 25, 27 so the superset pools of p = 2, 3, 5
      are anchored too.

VERDICT SEMANTICS: (REG-p) FAILS at p iff any (r1)/(r2-def)/(r2-act-i) check
fails at a faithful pool q₀ = p.  Superset-pool failures are reported separately.
Cross-check GATES (A-E below) must all pass BEFORE the scan is trusted: they tie
the transcribed tables to the sealed closed forms, the independent padic_types
laws (PARI-validated per om_density_engine gates), and the Lean-proved n2 facts.

Run:  python3 N6-regp_scan.py   (pure sympy/Fractions; ~1 min, CPU only)
"""

import sys
import os
import json
import time
from fractions import Fraction as Fr
from itertools import product as iproduct

import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))          # verification/
import padic_types                                  # independent monic laws
from om_density_engine import _beta_anchor          # engine anchors (= laws at 1/q)

q = sp.symbols('q', positive=True)

FAILURES = []       # (n, p, q0, clause, entry, detail)  — faithful pools
SUP_FAILURES = []   # same, superset pools only
GATE_FAILS = []

def gate(name, cond, detail=""):
    tag = "PASS" if cond else "GATE-FAIL"
    if not cond:
        GATE_FAILS.append(name)
    print(f"[{tag}] {name}  {detail}")

def simp0(e):
    return sp.simplify(sp.together(e)) == 0

# ===========================================================================
# 1. THE TABLES (transcribed; every line sourced in the header)
# ===========================================================================
D3 = q**3 - 1
D6 = q**6 - 1

# ---- block 2 = the true quadratic cluster law (S1, n3 seal; also n=2 block) ----
K2 = (q - 1) / D3                                   # kappa_2 = 1/(q^2+q+1)
b2 = {                                              # terminal masses, per stratum
    'split': (q - 1) * (q - 2) / (2 * D3),          # -> (1,1)+(1,1)
    'inert': q * (q - 1) / (2 * D3),                # -> (1,2)
    'w2':    q**2 / (q**2 + q + 1),                 # -> (2,1)   (odd-k0 face, summed)
    'vv':    1 / (q**2 + q + 1),                    # -> (1,1)^2 (v-v face, summed)
}
det2 = 1 - K2
beta2 = {v: sp.cancel(m / det2) for v, m in b2.items()}   # the block-2 solve
# verdict-graded map for split legs / root legs: sigma_1 -> mass
beta2_by_type = {
    ((1, 1), (1, 1)): sp.cancel(beta2['split'] + beta2['vv']),
    ((1, 2),):        beta2['inert'],
    ((2, 1),):        beta2['w2'],
}

# ---- block 3 (RESUM-n3 S1, verbatim strata) ----
K3 = (q - 1) / D6
b3 = {  # terminal masses per stratum -> verdict
    'A3dist':   (q - 1) * (q - 2) * (q - 3) / 6 / D6,   # (1,1)^3
    'Alinquad': q * (q - 1)**2 / 2 / D6,                # (1,1)+(1,2)
    'Airr':     (q**3 - q) / 3 / D6,                    # (1,3)
    'B':        (q - 1) * (q**5 + q**3) / D6,           # (3,1)
    'Codd':     (q - 1) * q**4 / D6,                    # (1,1)+(2,1)
    'Cdist':    (q - 1) * (q - 2) / 2 / D6,             # (1,1)^3
    'Cirr':     q * (q - 1) / 2 / D6,                   # (1,1)+(1,2)
    'Dodd':     (q - 1)**2 * q**2 / (D3 * D6),          # (1,1)+(2,1)
    'Ddist':    (q - 1)**2 * (q - 2) / 2 / (D3 * D6),   # (1,1)^3
    'Dirr':     q * (q - 1)**2 / 2 / (D3 * D6),         # (1,1)+(1,2)
    'E':        (q - 1)**2 / (D3 * D6),                 # (1,1)^3
}
b3_verdict = {'111': b3['A3dist'] + b3['Cdist'] + b3['Ddist'] + b3['E'],
              '112': b3['Alinquad'] + b3['Cirr'] + b3['Dirr'],
              '13':  b3['Airr'],
              '121': b3['Codd'] + b3['Dodd'],
              '31':  b3['B']}
# per-cell J entries (CL-18): the three split legs, each: halted (1,1) + blk2 child, δ=1
Jcells = {'J_A': (q - 1) * (q - 2) / D6,
          'J_C': (q - 1) / D6,
          'J_D': (q - 1)**2 / (D3 * D6)}
Jtot = sp.cancel(Jcells['J_A'] + Jcells['J_C'] + Jcells['J_D'])
det3 = 1 - K3
# beta_3(sigma) = (t_sigma + J * beta2map(sigma)) / (1 - kappa_3)
beta3 = {
    '111': sp.cancel((b3_verdict['111'] + Jtot * beta2_by_type[((1, 1), (1, 1))]) / det3),
    '112': sp.cancel((b3_verdict['112'] + Jtot * beta2_by_type[((1, 2),)]) / det3),
    '13':  sp.cancel(b3_verdict['13'] / det3),
    '121': sp.cancel((b3_verdict['121'] + Jtot * beta2_by_type[((2, 1),)]) / det3),
    '31':  sp.cancel(b3_verdict['31'] / det3),
}

# ---- root reads (W_Ŝ coefficients; monic box) ----
rootW_n2 = {'dist':  (q - 1) / (2 * q),   # -> (1,1)^2
            'inert': (q - 1) / (2 * q),   # -> (1,2)
            'dbl':   1 / q}               # -> beta_2 leg, δ=1
rootW_n3 = {'m_H3':   (q - 1) * (q - 2) / (6 * q**2),  # -> (1,1)^3
            'm_H12':  (q - 1) / (2 * q),               # -> (1,1)+(1,2)
            'm_Hirr': (q**2 - 1) / (3 * q**2),         # -> (1,3)
            'm_21':   (q - 1) / q**2,                  # -> (1,1) ⊕ beta_2, δ=1
            'm_3':    1 / q**2}                        # -> beta_3, δ=1

# ---- assembled monic densities R_sigma ----
R_n2 = {'split': sp.cancel(rootW_n2['dist'] + rootW_n2['dbl'] * beta2_by_type[((1, 1), (1, 1))]),
        'inert': sp.cancel(rootW_n2['inert'] + rootW_n2['dbl'] * beta2_by_type[((1, 2),)]),
        'ram':   sp.cancel(rootW_n2['dbl'] * beta2_by_type[((2, 1),)])}
R_n3 = {'111': sp.cancel(rootW_n3['m_H3'] + rootW_n3['m_21'] * beta2_by_type[((1, 1), (1, 1))]
                         + rootW_n3['m_3'] * beta3['111']),
        '112': sp.cancel(rootW_n3['m_H12'] + rootW_n3['m_21'] * beta2_by_type[((1, 2),)]
                         + rootW_n3['m_3'] * beta3['112']),
        '13':  sp.cancel(rootW_n3['m_Hirr'] + rootW_n3['m_3'] * beta3['13']),
        '121': sp.cancel(rootW_n3['m_21'] * beta2_by_type[((2, 1),)]
                         + rootW_n3['m_3'] * beta3['121']),
        '31':  sp.cancel(rootW_n3['m_3'] * beta3['31'])}

# ---- the Lean n=2 GATE instance (N2 corpus; Lean-proved facts) ----
lean_n2 = {'K': q**-3,
           't11': 1 - 1 / q,          # -> (1,1)^2
           't12': 1 / q - q**-3,      # -> (1,2)
           }
lean_n2_det = sp.cancel(1 - lean_n2['K'])
lean_n2_beta = {'b11': sp.cancel(lean_n2['t11'] / lean_n2_det),
                'b12': sp.cancel(lean_n2['t12'] / lean_n2_det)}

# ---- count polynomials (the integer-cardinality objects behind the masses) ----
counts_quad_residual = {          # monic deg-2 over F_q, R(0) != 0 (block-2 read)
    'split': (q - 1) * (q - 2) / 2, 'inert': q * (q - 1) / 2, 'double': q - 1}
counts_cubic_residual = {         # monic deg-3 over F_q, R(0) != 0 (block-3 A-face)
    '3dist': (q - 1) * (q - 2) * (q - 3) / 6, 'linquad': q * (q - 1)**2 / 2,
    'irr': (q**3 - q) / 3, 'dblsimple': (q - 1) * (q - 2), 'triple': q - 1}
counts_root_n3 = {                # ALL monic deg-3 over F_q (root read)
    'H3': q * (q - 1) * (q - 2) / 6, 'H12': q**2 * (q - 1) / 2,
    'Hirr': (q**3 - q) / 3, 'c21': q * (q - 1), 'c3': q}
counts_root_n2 = {                # ALL monic deg-2 over F_q (root read)
    'dist': q * (q - 1) / 2, 'inert': q * (q - 1) / 2, 'double': q}
counts_units = {'units': q - 1}   # deg-1 nonzero-const residuals (w2/vv faces),
                                  # ALSO the activity T-cell size (S3)

# ===========================================================================
# 2. CROSS-CHECK GATES — tie the transcription to sealed/independent sources
# ===========================================================================
print("=" * 74)
print("GATES: the transcribed tables ARE the sealed/independent real solve")
print("=" * 74)

# GATE A — books close
gate("A1 block-2 books: K2 + sum b2 = 1", simp0(K2 + sum(b2.values()) - 1))
gate("A2 block-3 books: K3 + sum b3term + J = 1",
     simp0(K3 + sum(b3.values()) + Jtot - 1))
gate("A3 root letters n=2 sum = 1", simp0(sum(rootW_n2.values()) - 1))
gate("A4 root letters n=3 sum = 1", simp0(sum(rootW_n3.values()) - 1))
gate("A5 beta_2 sums to 1", simp0(sum(beta2.values()) - 1))
gate("A6 beta_3 sums to 1", simp0(sum(beta3.values()) - 1))
gate("A7 quad residual counts total q(q-1)",
     simp0(sum(counts_quad_residual.values()) - q * (q - 1)))
gate("A8 cubic residual counts total q^3-q^2",
     simp0(sum(counts_cubic_residual.values()) - (q**3 - q**2)))
     # (all five shapes — incl. the triple = K_3 column and dblsimple = J leg —
     #  tile the q^3-q^2 nonzero-constant face box)
gate("A9 root n=3 counts total q^3", simp0(sum(counts_root_n3.values()) - q**3))
gate("A10 Lean-n2 part1: kcol+t11+t12 = 1",
     simp0(lean_n2['K'] + lean_n2['t11'] + lean_n2['t12'] - 1))

# GATE B — solve equals the independent cluster laws (padic_types at 1/q;
# om_density_engine anchors, themselves PARI-gate-validated)
mq = padic_types.monic_quad_pred            # Fraction-valued at rational q
mc = padic_types.monic_cubic_pred
okB2 = all(sp.Rational(mq(Fr(1, qq))[nm].numerator, mq(Fr(1, qq))[nm].denominator)
           == sp.nsimplify(beta2_by_type[t].subs(q, qq))
           for qq in (2, 3, 5, 7, 11)
           for t, nm in [(((1, 1), (1, 1)), 'split'), (((1, 2),), 'inert'),
                         (((2, 1),), 'ram')])
gate("B1 beta_2 == monic_quad_pred(1/q) at q=2,3,5,7,11", okB2)
code3 = {'111': '111', '112': '12', '13': '3', '121': '1r1', '31': '1c'}
okB3 = all(sp.Rational(mc(Fr(1, qq))[code3[s]].numerator,
                       mc(Fr(1, qq))[code3[s]].denominator)
           == sp.nsimplify(beta3[s].subs(q, qq))
           for qq in (2, 3, 5, 7, 11) for s in beta3)
gate("B2 beta_3 == monic_cubic_pred(1/q) at q=2,3,5,7,11", okB3)
anc2 = _beta_anchor(2)
okB4 = all(simp0(beta2_by_type[t] - anc2[t]) for t in beta2_by_type)
anc3 = _beta_anchor(3)
key3 = {'111': ((1, 1), (1, 1), (1, 1)), '112': ((1, 1), (1, 2)), '13': ((1, 3),),
        '121': ((1, 1), (2, 1)), '31': ((3, 1),)}
okB5 = all(simp0(beta3[s] - anc3[key3[s]]) for s in beta3)
gate("B3 beta_2 == engine anchor (symbolic)", okB4)
gate("B4 beta_3 == engine anchor (symbolic)", okB5)

# GATE C — assembled monic R_sigma equal the independent monic laws + sealed forms
okC1 = all(sp.Rational(mq(Fr(qq))[s].numerator, mq(Fr(qq))[s].denominator)
           == sp.nsimplify(R_n2[s].subs(q, qq))
           for qq in (2, 3, 5, 7, 11, 13) for s in R_n2)
gate("C1 R_sigma(n=2) == monic_quad_pred(q) at 6 primes", okC1)
okC2 = all(sp.Rational(mc(Fr(qq))[code3[s]].numerator, mc(Fr(qq))[code3[s]].denominator)
           == sp.nsimplify(R_n3[s].subs(q, qq))
           for qq in (2, 3, 5, 7, 11, 13) for s in R_n3)
gate("C2 R_sigma(n=3) == monic_cubic_pred(q) at 6 primes", okC2)
gate("C3 sum R_sigma(n=2) = 1", simp0(sum(R_n2.values()) - 1))
gate("C4 sum R_sigma(n=3) = 1", simp0(sum(R_n3.values()) - 1))
P5 = q**5 + 2*q**4 + 2*q**3 + 2*q**2 + 2*q + 1
P4 = q**4 + q**3 + q**2 + q + 1
sealedR = {'111': (q**5 - q**4 + q**3) / (6 * P5), '112': (q**5 + q**4 + q**3) / (2 * P5),
           '13': (q**4 + q**3) / (3 * P4), '121': (q**4 + q**2 + q) / P5,
           '31': (q**2 + 1) / P4}
gate("C5 R_sigma(n=3) == S2 SEALED closed forms (symbolic)",
     all(simp0(R_n3[s] - sealedR[s]) for s in R_n3))
S2_table = {2: {'111': Fr(4, 93), '112': Fr(28, 93), '13': Fr(8, 31),
                '121': Fr(22, 93), '31': Fr(5, 31)},
            3: {'111': Fr(63, 968), '112': Fr(351, 968), '13': Fr(36, 121),
                '121': Fr(93, 484), '31': Fr(10, 121)},
            5: {'111': Fr(875, 9372), '112': Fr(3875, 9372), '13': Fr(250, 781),
                '121': Fr(655, 4686), '31': Fr(26, 781)},
            7: {'111': Fr(14749, 134448), '112': Fr(19551, 44816), '13': Fr(2744, 8403),
                '121': Fr(2457, 22408), '31': Fr(50, 2801)}}
okC6 = all(sp.Rational(S2_table[qq][s].numerator, S2_table[qq][s].denominator)
           == sp.nsimplify(R_n3[s].subs(q, qq)) for qq in S2_table for s in R_n3)
gate("C6 R_sigma(n=3) == S2 sealed 4-prime table", okC6)

# GATE D — the sealed S3 pool table (K/det/J at q0 = 2,3,4)
S3_table = {2: (Fr(1, 7), Fr(6, 7), Fr(1, 63), Fr(62, 63), Fr(8, 441)),
            3: (Fr(1, 13), Fr(12, 13), Fr(1, 364), Fr(363, 364), Fr(27, 4732)),
            4: (Fr(1, 21), Fr(20, 21), Fr(1, 1365), Fr(1364, 1365), Fr(64, 28665))}
okD = True
for qq, (k2v, d2v, k3v, d3v, jv) in S3_table.items():
    got = tuple(sp.nsimplify(e.subs(q, qq)) for e in (K2, det2, K3, det3, Jtot))
    want = tuple(sp.Rational(x.numerator, x.denominator) for x in (k2v, d2v, k3v, d3v, jv))
    okD = okD and got == want
gate("D1 (K2, det2, K3, det3, J) == S3 sealed table at q0 = 2,3,4", okD)

# GATE E — the Lean-proved n2 gate facts
gate("E1 Lean n2 det == (q^3-1)/q^3 (n2_det)", simp0(lean_n2_det - (q**3 - 1) / q**3))
gate("E2 Lean n2 beta == sealed (q^2, q+1)/(q^2+q+1)",
     simp0(lean_n2_beta['b11'] - q**2 / (q**2 + q + 1))
     and simp0(lean_n2_beta['b12'] - (q + 1) / (q**2 + q + 1)))

# ===========================================================================
# 3. BRUTE-FORCE ACT ANCHORS — factor-shape counts over F_q, q in prime powers
#    (the computable core of the (r2) active-value agreement, (ii-c))
# ===========================================================================
print()
print("=" * 74)
print("(r2-act ii): brute-force active reads over F_q vs the count polynomials")
print("=" * 74)

def make_field(p, k):
    """Tiny GF(p^k) (k<=3): elements = tuples of length k (coeffs of x^i),
    multiplication mod an irreducible degree-k poly found by search."""
    if k == 1:
        els = list(range(p))
        add = lambda a, b: (a + b) % p
        mul = lambda a, b: (a * b) % p
        neg = lambda a: (-a) % p
        return els, add, mul, neg, 0, 1
    # find irreducible monic poly of degree k over F_p (k in {2,3}: no roots)
    def polyval(cs, x):  # cs = low-first coeffs of monic poly (without leading 1)
        v = 1
        for c in reversed(cs):
            v = (v * x + c) % p
        return v
    irr = None
    for cs in iproduct(range(p), repeat=k):
        if all(polyval(list(cs), x) != 0 for x in range(p)):
            # degree 2/3: no roots <=> irreducible
            irr = list(cs)
            break
    assert irr is not None
    els = [tuple(t) for t in iproduct(range(p), repeat=k)]
    def add(a, b): return tuple((x + y) % p for x, y in zip(a, b))
    def neg(a): return tuple((-x) % p for x in a)
    def mul(a, b):
        prod = [0] * (2 * k - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    prod[i + j] = (prod[i + j] + x * y) % p
        for d in range(2 * k - 2, k - 1, -1):     # reduce x^d = -irr shifted
            c = prod[d]
            if c:
                prod[d] = 0
                for j in range(k):
                    prod[d - k + j] = (prod[d - k + j] - c * irr[j]) % p
        return tuple(prod[:k])
    zero = tuple([0] * k)
    one = tuple([1] + [0] * (k - 1))
    return els, add, mul, neg, zero, one

def shape_counts(p, k, deg, nonzero_const):
    """Counts of factor shapes of monic degree-`deg` polys over GF(p^k)."""
    els, add, mul, neg, zero, one = make_field(p, k)
    def pv(coeffs, x):     # monic: coeffs low-first, length deg (no leading 1)
        v = one
        for c in reversed(coeffs):
            v = add(mul(v, x), c)
        return v
    out = {}
    for coeffs in iproduct(els, repeat=deg):
        if nonzero_const and coeffs[0] == zero:
            continue
        roots = [x for x in els if pv(list(coeffs), x) == zero]
        r = len(roots)
        if deg == 2:
            if r == 2: shp = 'split'
            elif r == 0: shp = 'inert'
            else:
                # one root found: double iff disc = 0 <=> b^2 = 4c
                b, c = coeffs[1], coeffs[0]
                four_c = mul(add(one, one), mul(add(one, one), c))
                shp = 'double' if mul(b, b) == four_c else 'split??'
                if shp == 'split??':  # p=2 special: x^2+bx+c with 1 root => double? no:
                    # over any field, a monic quadratic with exactly one distinct root
                    # in the field is (x-r)^2 -- else both roots are in the field.
                    shp = 'double'
        else:  # deg == 3
            # multiplicity via deflation
            mult = {}
            for x in roots:
                # synthetic division count
                m, cs = 0, [coeffs[0], coeffs[1], coeffs[2], one]
                while True:
                    # divide cs (low-first, monic top) by (X - x)
                    n = len(cs) - 1
                    newcs, rem = [None] * n, zero
                    carry = cs[-1]
                    for i in range(n - 1, -1, -1):
                        newcs[i] = carry
                        carry = add(cs[i], mul(x, carry))
                    rem = carry
                    if rem != zero:
                        break
                    m += 1
                    cs = newcs
                    if len(cs) == 1:
                        break
                mult[x] = m
            tot = sum(mult.values())
            if len(roots) == 3: shp = '3dist'
            elif len(roots) == 0: shp = 'irr'
            elif len(roots) == 1 and mult[roots[0]] == 3: shp = 'triple'
            elif len(roots) == 1 and mult[roots[0]] == 1: shp = 'linquad'
            elif len(roots) == 2: shp = 'dblsimple'
            else: shp = f'UNEXPECTED(r={len(roots)},m={mult})'
        out[shp] = out.get(shp, 0) + 1
    return out

def ev_int(expr, q0):
    v = sp.nsimplify(sp.cancel(expr).subs(q, sp.Integer(q0)))
    return v

BRUTE_QS = [(2, 1), (3, 1), (2, 2), (5, 1), (7, 1), (2, 3), (3, 2), (11, 1),
            (13, 1), (5, 2), (3, 3)]     # q = 2,3,4,5,7,8,9,11,13,25,27
brute_ok = True
t0 = time.time()
for (p, k) in BRUTE_QS:
    Q = p**k
    # quad residual (nonzero const): split/inert/double
    got = shape_counts(p, k, 2, True)
    want = {s: ev_int(cpoly, Q) for s, cpoly in counts_quad_residual.items()}
    ok1 = all(got.get(s, 0) == want[s] for s in want)
    # cubic residual (nonzero const)
    got3 = shape_counts(p, k, 3, True)
    want3 = {s: ev_int(cpoly, Q) for s, cpoly in counts_cubic_residual.items()}
    ok2 = all(got3.get({'3dist': '3dist', 'linquad': 'linquad', 'irr': 'irr',
                        'dblsimple': 'dblsimple', 'triple': 'triple'}[s], 0) == want3[s]
              for s in want3)
    # root read n=3 (full box)
    gotr = shape_counts(p, k, 3, False)
    wantr = {'H3': ev_int(counts_root_n3['H3'], Q), 'H12': ev_int(counts_root_n3['H12'], Q),
             'Hirr': ev_int(counts_root_n3['Hirr'], Q), 'c21': ev_int(counts_root_n3['c21'], Q),
             'c3': ev_int(counts_root_n3['c3'], Q)}
    okr = (gotr.get('3dist', 0) == wantr['H3'] and gotr.get('linquad', 0) == wantr['H12']
           and gotr.get('irr', 0) == wantr['Hirr'] and gotr.get('dblsimple', 0) == wantr['c21']
           and gotr.get('triple', 0) == wantr['c3'])
    # root read n=2 (full box)
    gotr2 = shape_counts(p, k, 2, False)
    okr2 = (gotr2.get('split', 0) == ev_int(counts_root_n2['dist'], Q)
            and gotr2.get('inert', 0) == ev_int(counts_root_n2['inert'], Q)
            and gotr2.get('double', 0) == ev_int(counts_root_n2['double'], Q))
    ok = ok1 and ok2 and okr and okr2
    brute_ok = brute_ok and ok
    gate(f"ACT q={Q:>2} ({'wild' if p <= 3 else 'tame'} base): residual+root counts exact",
         ok, f"[quad {got}]" if not ok else "")
print(f"(brute anchors: {time.time()-t0:.1f}s)")

# ===========================================================================
# 4. THE SCAN — (r1), (r2-def), (r2-act i) at every prime p < 500
# ===========================================================================
print()
print("=" * 74)
print("SCAN: (REG-p) at the real tables, all p < 500, pools p^delta, delta<=3")
print("=" * 74)

def primes_below(N):
    sieve = [True] * N
    sieve[0] = sieve[1] = False
    for i in range(2, int(N**0.5) + 1):
        if sieve[i]:
            for j in range(i * i, N, i):
                sieve[j] = False
    return [i for i in range(N) if sieve[i]]

PRIMES = primes_below(500)

def prep(expr):
    """cancelled (num, den) integer-coefficient Polys for exact evaluation."""
    ee = sp.cancel(sp.together(expr))
    nu, de = sp.fraction(ee)
    return sp.Poly(nu, q), sp.Poly(de, q)

def ev_frac(nd, q0):
    nu, de = nd
    dv = de.eval(sp.Integer(q0))
    if dv == 0:
        return None          # POLE
    return sp.Rational(nu.eval(sp.Integer(q0)), dv)

# rosters: name -> (num, den); is_count marks integer-cardinality objects
def build_roster(n):
    roster = {}          # (r2-def) definedness objects
    counts = {}          # (r2-act i) count polynomials
    dets = {}            # (r1) objects
    kents = {}           # E0 margin extras
    if n == 2:
        # -- the true monic quadratic instance --
        dets['det_blk1'] = prep(sp.Integer(1))         # block 1: K = 0
        dets['det_blk2'] = prep(det2)
        kents['K2'] = prep(K2)
        roster['K2'] = prep(K2)
        for s, m in b2.items():
            roster[f'b2term_{s}'] = prep(m)
        for w, m in rootW_n2.items():
            roster[f'W_{w}'] = prep(m)
        roster['iota'] = prep(sp.Integer(1))           # F1: trivial at this instance
        for t, m in beta2_by_type.items():
            roster[f'betaLeg2_{t}'] = prep(m)
        for s, m in R_n2.items():
            roster[f'R_{s}'] = prep(m)                 # derived R_defined consequence
        for s, cpoly in counts_quad_residual.items():
            counts[f'cnt_quadres_{s}'] = prep(cpoly)
        for s, cpoly in counts_root_n2.items():
            counts[f'cnt_root2_{s}'] = prep(cpoly)
        counts['cnt_units'] = prep(counts_units['units'])
        # -- the Lean gate instance (secondary roster, same clause typing) --
        dets['det_LEANn2_blk2'] = prep(lean_n2_det)
        kents['K_LEANn2'] = prep(lean_n2['K'])
        roster['K_LEANn2'] = prep(lean_n2['K'])
        roster['LEANn2_t11'] = prep(lean_n2['t11'])
        roster['LEANn2_t12'] = prep(lean_n2['t12'])
        roster['LEANn2_beta11'] = prep(lean_n2_beta['b11'])
        roster['LEANn2_beta12'] = prep(lean_n2_beta['b12'])
    else:
        dets['det_blk1'] = prep(sp.Integer(1))
        dets['det_blk2'] = prep(det2)
        dets['det_blk3'] = prep(det3)
        kents['K2'] = prep(K2)
        kents['K3'] = prep(K3)
        roster['K2'] = prep(K2)
        roster['K3'] = prep(K3)
        for s, m in b2.items():
            roster[f'b2term_{s}'] = prep(m)
        for s, m in b3.items():
            roster[f'b3term_{s}'] = prep(m)
        for s, m in b3_verdict.items():
            roster[f'b3row_{s}'] = prep(m)
        for jn, m in Jcells.items():
            roster[f'Jcell_{jn}'] = prep(m)
        roster['J_total'] = prep(Jtot)
        # bsplit rows: J-leg x beta_2 child (delta = 1), sigma-graded
        for t, m in beta2_by_type.items():
            roster[f'bsplit_row_{t}'] = prep(Jtot * m)
        for w, m in rootW_n3.items():
            roster[f'W_{w}'] = prep(m)
        roster['iota'] = prep(sp.Integer(1))
        for t, m in beta2_by_type.items():
            roster[f'betaLeg2_{t}'] = prep(m)
        for s, m in beta3.items():
            roster[f'betaLeg3_{s}'] = prep(m)
        for s, m in R_n3.items():
            roster[f'R_{s}'] = prep(m)
        for s, cpoly in counts_quad_residual.items():
            counts[f'cnt_quadres_{s}'] = prep(cpoly)
        for s, cpoly in counts_cubic_residual.items():
            counts[f'cnt_cubres_{s}'] = prep(cpoly)
        for s, cpoly in counts_root_n3.items():
            counts[f'cnt_root3_{s}'] = prep(cpoly)
        counts['cnt_units'] = prep(counts_units['units'])
    return roster, counts, dets, kents

results = {}
E0_min_margin = None   # min over scan of 1 - K_e(q0)  (extra, not REG-p)
for n in (2, 3):
    roster, counts, dets, kents = build_roster(n)
    n_pass = 0
    for p in PRIMES:
        p_ok_faithful = True
        for delta in (1, 2, 3):
            q0 = p**delta
            faithful = (delta == 1)
            sink = FAILURES if faithful else SUP_FAILURES
            # (r1)
            for name, nd in dets.items():
                v = ev_frac(nd, q0)
                if v is None:
                    sink.append((n, p, q0, 'r1-pole', name, 'det denominator vanishes'))
                    p_ok_faithful &= not faithful
                elif v == 0:
                    sink.append((n, p, q0, 'r1-zero', name, 'det(1-K) = 0'))
                    if faithful: p_ok_faithful = False
            # (r2-def)
            for name, nd in roster.items():
                v = ev_frac(nd, q0)
                if v is None:
                    sink.append((n, p, q0, 'r2-pole', name, 'entry denominator vanishes'))
                    if faithful: p_ok_faithful = False
                elif not (0 <= v <= 1) and not name.startswith(('K_', 'Jcell')):
                    # masses must be probabilities; a value outside [0,1] means the
                    # literal evaluation cannot be the active read => (ii-c) fails
                    sink.append((n, p, q0, 'r2-act-range', name, f'value {v} not in [0,1]'))
                    if faithful: p_ok_faithful = False
            # (r2-act i): counts are nonnegative integers
            for name, nd in counts.items():
                v = ev_frac(nd, q0)
                if v is None or v < 0 or v.q != 1:
                    sink.append((n, p, q0, 'r2-act-count', name, f'count value {v}'))
                    if faithful: p_ok_faithful = False
            # extras (E0 margin; activity cell size)
            for name, nd in kents.items():
                v = ev_frac(nd, q0)
                if v is not None and v < 1:
                    m = 1 - v
                    if E0_min_margin is None or m < E0_min_margin[0]:
                        E0_min_margin = (m, n, p, q0, name)
        if p_ok_faithful:
            n_pass += 1
    results[n] = n_pass
    print(f"n={n}: {n_pass}/{len(PRIMES)} primes < 500 PASS (REG-p) at faithful pools "
          f"Q(p) = {{p}}")

faith_fail_primes = sorted(set((f[0], f[1]) for f in FAILURES))
sup_fail = sorted(set((f[0], f[1], f[2]) for f in SUP_FAILURES))
print()
print(f"FAILING SET (faithful pools): {faith_fail_primes if faith_fail_primes else 'EMPTY'}")
print(f"FAILING SET (superset pools p^2, p^3): {sup_fail if sup_fail else 'EMPTY'}")
if FAILURES:
    print("  smallest faithful counterexample:", min(FAILURES, key=lambda f: (f[0], f[1])))
if SUP_FAILURES:
    for f in SUP_FAILURES[:10]:
        print("  superset failure:", f)
if E0_min_margin:
    m, n_, p_, q0_, nm = E0_min_margin
    print(f"E0 extra (not REG-p): min escape margin 1-K = {m} at n={n_}, p={p_}, "
          f"q0={q0_}, {nm}  (K < 1 everywhere: {'YES' if m > 0 else 'NO'})")

print()
print("=" * 74)
verdict_ok = (not GATE_FAILS) and brute_ok and not FAILURES
print(f"GATES: {'ALL PASS' if not GATE_FAILS else 'FAILED: ' + str(GATE_FAILS)}")
print(f"VERDICT (faithful REG-p, p < 500, n in {{2,3}}): "
      f"{'NO FAILING PRIME — passing density 95/95 = 1' if verdict_ok else 'SEE FAILURES'}")
print("=" * 74)

out = {'id': 'N6-regp',
       'primes_scanned': len(PRIMES),
       'faithful_pass': {str(n): results[n] for n in results},
       'faithful_failures': [list(map(str, f)) for f in FAILURES],
       'superset_failures': [list(map(str, f)) for f in SUP_FAILURES],
       'gate_failures': GATE_FAILS,
       'brute_act_anchors_ok': brute_ok,
       'E0_min_margin': str(E0_min_margin[0]) if E0_min_margin else None}
with open(os.path.join(HERE, 'N6-regp_results.json'), 'w') as fh:
    json.dump(out, fh, indent=1)
print("results JSON -> N6-regp_results.json")
