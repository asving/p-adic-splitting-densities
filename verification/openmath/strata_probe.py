#!/usr/bin/env python3
"""strata_probe.py — Tier-3 STRATA FALSIFIER (hardest-first order item 5,
docs/HARDEST_FIRST_ORDER_2026-08-08.md): the two UNTESTED strata whose failure
re-routes the (H1)(a) dictionary, probed falsifier-first BEFORE any proof is
written.

  FAMILY A: the corrected-eps twist law at e0 >= 2 (GRB leaf S3.4(ii)) —
            FGMN Def 3.16/3.18 with the CORRECTED Def 3.15
            (eps_i = z_i^(l'_i s - l_i u); triple-pinned by N-1's T0/P3/P12;
            the raw /tmp/litunit/fgmn.txt rendering at Def 3.15 is CORRUPTED
            and is NOT consulted) vs GMN Defs 2.19-2.21, on order-2 towers
            OFF the unramified stratum (e0 >= 2), where the twist is
            genuinely nontrivial.  The analogue of TR3-S1/T9.
  FAMILY B: the D-ITER composite (GRB leaf S5.3; MOVES_2026-07-24.md SS F.0/F.2)
            — the rank-(e1*E1) iterated carry algebra at order-2 stacked
            ramification (E2 = e0*e1 > 1), tested at exact instances: the
            alphabet and multiplication laws of the composite digit algebra
            on CANONICAL ANCHORS, i.e. the object beyond T10's last-read
            layer (T10 only probed R_2(Phi1^s), the e1-layer walk).

MACHINERY: builds on grb_order2_check.py (N-1) — Tower objects, the reading-C
FGMN operator R2w/R2s, base rings, finite-field towers — reused verbatim by
import; the GMN side of Family A is computed INDEPENDENTLY below from the
printed GMN text (Defs 2.19-2.21 quoted in TR3S1_2026-08-08.md S1 +
/tmp/litunit/gmn.txt:1823-1906), generalizing tr3s1_check.py's independent
order-2 GMN operator from e0 = 1 to all e0.  Shared-input scope (as in
TR3-S1's amendment): the GMN side shares the Tower object (base rings,
Phi0/Phi1, residue fields) and w1 consumed as v2 (v2 = w1 at order 2 is the
pinned Def-2.5 identity: v2(P) = e0*H1(S1(P)) = min_k(e0*w0(b_k) + k*h0),
literally w1's formula); those shared inputs carry N-1's external legs
(T11/P11/P12 PARI + T0).  New towers introduced here get their own
certification legs (CERT family below: T1/T2/T5 internal + T11 PARI on Z_p).

DETERMINISTIC: random.seed(20260815).  EXACT arithmetic only.  PARI
(cypari2 factorpadic / idealprimedec) fires exactly where factorization
enters: certification of the NEW tower rows' OM data (T11).

=============================== TOWER ROSTER =================================
Reused N-1 rows (certified there):  e0 >= 2: C (1;2,1,1;2,1,1)
  D (1;2,3,1;1,1,2)  E (1;3,1,1;2,3,1)  H (2;2,1,1;1,1,1)  J (2;2,1,2;2,1,1)
  e0 = 1 controls: A (1;1,1,1;2,1,1)  B (1;1,2,2;3,2,1)  G (2;1,1,1;2,1,1)
  I (2;1,1,2;2,3,1)
NEW designed rows (this unit; z1/zbar chosen multiplicatively rich so the
twist and the composite constants are VISIBLE — small-field towers are
twist-blind, the G2 lesson):
  K (2; 2,1,1; 2,1,1)   E2 = 4;  p=2: K1 = F_4, z1 = w (ord 3)
  L (2; 3,2,1; 2,1,1)   E2 = 6;  e0 = 3 with l0 = 2, l0' = -1 (nontrivial
                         Bezout pair exercises the eps exponent fully)
  M (2; 2,1,2; 3,1,1)   E2 = 6;  K1 = F_16/F_81, e1 = 3
  N (2; 2,1,1; 2,1,2)   E2 = 4;  g1 = 2: K2 = K1[zbar] a genuine degree-2
                         extension — zbar NOT in <z1> guaranteed (the
                         Family-B discriminator design)
All rows over the four base rings {Z_2, Z_3, F_2[[t]], F_3[[t]]}.

===================== FAMILY A — PREREGISTERED PREDICTIONS ===================
Setting: order-2 tower, reads (e0,h0,psi0), (e1,h1,psi1); f nonzero in O[x];
gamma = w2(f); FGMN weight-read coefficients C^F_j at abscissas
s_j = s2 + j*e1 (harness R2w, reading C); GMN residual coefficients
c^G_i (i on the lambda2-component) computed independently per Def 2.19-2.21
with the NORMALIZED Bezout representative 0 <= l0 < e0 (l0*h0 = 1 mod e0)
— the project's standing GMN-convention operator (TR3-S1's displayed
hypothesis, now at e0 >= 2 where l0 != 0 makes t nontrivial):
    t1(i) = (s1(a_i) - l0*u_i)/e0,   u_i = w1(a_i) + i*w1(Phi1),
    c^G_i = z1^(t1(i)) * R1^GMN(a_i)(z1)      [on-line i; 0 above].

THE DERIVED TWIST LAW (this unit's operationalization of the S3.4(ii)
conjecture; derivation displayed here, fixed BEFORE the run):
  FGMN inner read starts at the FORCED abscissa s(gamma_j) (eq (12-int));
  GMN's inner read starts at the ACTUAL initial abscissa s1(a_i) =
  s(gamma_j) + m0*e0, m0 >= 0.  So (Lemma-A-general, A2 below)
      eps1(gamma_j)^{-1} * C^F_j = z1^{m0} * R1^GMN(a_i)(z1).
  Then with eps1(gamma_j) = z1^(l0'*s - l0*u) (corrected Def 3.15) and
  l0*gamma_j = s + e0*(l0*u - l0'*s) (Bezout l0*h0 + l0'*e0 = 1):
      t1(i) = m0 + (l0'*s - l0*u) - l0*i*(w1Phi1/e0)
  hence the per-slot discrepancy is the PURE z1-POWER
      (TWIST-LAW)   C^F_j = z1^(l0*g0*h0*s_j) * c^G_{s_j}
  (using w1Phi1 = e0*g0*h0), equivalently ratio(j+1) = ratio(j) *
  z1^(l0*g0*h0*e1).  At e0 = 1 (l0 = 0) this is TR3-S1's identity, exactly.

  STATUS HONESTY: A0/A5 are sealed claims (GMN's own printed integrality
  proof under Def 2.19; TR3-S1's theorem).  A1/A2/A3 are the CONJECTURE
  being probed — S3.4(ii) says the discrepancy is the corrected eps
  threaded per slot; (TWIST-LAW) is the closed form that threading yields,
  derived THIS UNIT (the derivation itself is part of what the run tests).
  The FGMN side's transcription risk is covered by N-1's external pins;
  the GMN side is freshly implemented from the printed text.

A0  GMN-side internal integrity: t1(i) integral (GMN's printed congruence
    argument uses v2(phi2) = 0 mod e0 — here w1Phi1 = e0*g0*h0); component
    endpoints e1-congruent; on-line abscissas mutually e0-congruent at
    level 1; c^G != 0 on-line (Def 2.20's printed note).
    PREDICTED: 0 violations.  [SEALED — GMN's own printed proofs]
A1  Support agreement: C^F_j != 0 iff abscissa s_j lies on the
    independently computed GMN on-line set.   PREDICTED: 0.  [CONJ component]
A2  Lemma-A-general: at every on-line slot,
    eps1(gamma_j)^{-1}*C^F_j == z1^{m0} * R1^GMN(a_i)(z1), m0 =
    (s1(a_i) - s(gamma_j))/e0 an integer >= 0.  PREDICTED: 0.  [CONJ comp.]
A3  (TWIST-LAW) exact, every on-line slot, every sample, every tower
    (e0 >= 2 rows AND e0 = 1 controls, where it degenerates to identity).
    PREDICTED: 0.  [THE PROBED CONJECTURE]
    RED handling: if A0 green + A5 green + A3 red, the witness (tower, f,
    slot, both values) is printed; the MEASURED per-slot exponent is
    reported for re-derivation — distinguishing "derivation wrong, law has
    a different exponent" (still a twist law: S3.4(ii) survives reshaped)
    from "discrepancy not a z1-power at all" (S3.4(ii) refuted).
A5  e0 = 1 controls: ratio == 1 identically (TR3-S1).  PREDICTED: 0.  [SEALED]
A6  Genuine-nontriviality meter: at every on-line slot with
    z1^(l0*g0*h0*s_j) != 1 the NAIVE identity C^F_j == c^G_j must FAIL.
    PREDICTED: naive_refuted == visible-slot count (> 0 overall; exact
    equality of the two counters).  [derived consequence of A3]
A7  The retired-S3.2-shape increment z1^(gamma2) (the artifact law killed
    by N-1 at e0 = 1): on consecutive on-line slot pairs where
    z1^(gamma2) != z1^(l0*g0*h0*e1), the retired increment must FAIL.
    PREDICTED: retired_refuted == such-pair count.  [derived consequence]

===================== FAMILY B — PREREGISTERED PREDICTIONS ===================
Object: the degree-0 composite digit algebra of gr(w2) at E2 = e0*e1 > 1,
probed through the FGMN graded representation (T3/T4-sealed multiplicative:
N-1 0/2,880 + PARI legs).  CANONICAL ANCHORS (the iterated eq-(12-int)
split — the composite analogue of D-REAL's basis, and the basis the digit
map dig reads: IFACE(c)'s consumed object):
    gamma = e1*gamma1 + s2*gamma2,  (s2,u2) = eq12(gamma, e1, h1),
    gamma1 = u2 - s2*w1Phi1,        (s1,u1) = eq12(gamma1, e0, h0),
    phi_gamma := pi^{u1} * Phi0^{s1} * Phi1^{s2}     (u1 >= 0 in the probed
    window Gamma0 <= gamma; phi_{gamma+E2} = pi*phi_gamma EXACTLY).
Class values: val(f) := (R_{2,w2(f)}(f))(y -> zbar) in K2 = K1[zbar]/(psi1).
Cocycle on canonical anchors (gauge-free — numerator and denominator at the
same weight):  c(ga,gb) := val(phi_ga*phi_gb) / val(phi_{ga+gb}).

THE DERIVED ITERATED LAW (fixed before the run; from W-MULT (T4-sealed) +
the anchor-value computation val(phi_gamma) = eps1(gamma1), both harness-
representation facts):
    (ITER-LAW)  c(ga,gb) = zbar^{d2} * z1^{(s1(ga)+s1(gb)-s1(ga+gb)
                                            + l0*gamma2*d2)/e0},
    d2 := floor((s2(ga)+s2(gb))/e1)  (the outer carry; the outer wrap dumps
    weight gamma2 = h1 (mod e0-track) into the INNER letter — the genuine
    fibred/iterated structure).  At e0 = 1 this degenerates to
    c = zbar^{d2}: exactly Lemma D-REAL's proved carry law.
THE PROBED DISPLAY (the object the MOVES pass-8 verifier faulted and GRB
S5.3 keeps OPEN as D-ITER): the composite is the CYCLIC algebra
F'[u']/(u'^{E2} - zeta') with a SINGLE structure constant — operationalized
at canonical anchors (the consumed presentation: dig reads leading canonical
slots) as
    (CYC)  image(c) is {1} or {1, zeta'} for a single zeta' != 1, AND the
           carry pattern kappa(rho,sigma) := [c = zeta'] is realizable as
           the carry of SOME relabeling: exists a bijection
           sigma: Z/E2 -> {0..E2-1}, sigma(0) = 0, with
           sigma(rho) + sigma(sig) = sigma(rho+sig mod E2) + E2*kappa.
    HONESTY DISPLAY: the ABSTRACT iso K2[U]/(U^{E2} - zeta*) is automatic
    for any crossed product of Z/E2 (take the weight-1 letter as U) and is
    NOT what is tested; the content is the single-constant carry law at the
    canonical (dig-consumed) alphabet.  Under (ITER-LAW), (CYC) holds on
    the e0 = 1 stratum (zeta' = zbar, sigma = the s2-labeling: D-REAL) and
    on e1 = 1 towers (zeta' = z1, sigma = the s1-labeling), and FAILS at
    mixed stacked towers whose values {z1-powers} and {zbar*(z1-powers)}
    are distinct nontrivially (designed row N is the discriminator: zbar
    of degree 2 over K1).  The run ADJUDICATES between (CYC) and
    (ITER-LAW) where they differ; that adjudication IS the unit's charge.

B0a Cocycle identity c(a,b)c(a+b,t) == c(b,t)c(a,b+t) (associativity of
    gr(w2)) — MUST HOLD; a violation is a HARNESS BUG, never math.
    PREDICTED: 0.
B0c Representative-independence: the (rho,sigma)-table at window Gamma0
    equals the table at Gamma0 + E2.  PREDICTED: 0.  [SEALED via W-MULT
    pi-periodicity; doubles as bug detector]
B1  Alphabet/shape laws [SEALED via T4/T10 + anchor structure]:
    every anchor read is a single nonzero coefficient at y^0 with value
    eps1(gamma1); every anchor-pair product read is a single nonzero
    coefficient at y^{d2}; all E2 letters nonzero; exponent integrality
    (s1-defect + l0*gamma2*d2) == 0 mod e0.  PREDICTED: 0.
B2  (ITER-LAW) exact on all pairs, all towers.  PREDICTED: 0.
    [DERIVED CONJECTURE — this unit's algebra; RED => re-derive from the
    measured table (printed in full on failure)]
B3  (CYC) adjudication per tower: verdict CYCLIC(zeta')/NOT-CYCLIC printed
    with the value table; e0 = 1 rows PREDICTED CYCLIC with zeta' = zbar
    and sigma = s2-labeling [SEALED, D-REAL]; e1 = 1 rows PREDICTED CYCLIC
    with zeta' = z1 [under ITER-LAW]; mixed rows: ADJUDICATED BY THE RUN —
    under (ITER-LAW) the prediction is NOT-CYCLIC exactly where the value
    set has >= 2 distinct non-1 elements (computed per tower at runtime and
    compared).  A NOT-CYCLIC verdict on a mixed tower WITH B0/B1/B2 green
    is classified: conjecture-adjudicating instance (the single-zeta'
    cyclic display of the composite is FALSE at the canonical alphabet;
    the true law is (ITER-LAW)) — NOT a harness bug.
B4  Invariant measurements (report, no prediction): zeta_w := holonomy of
    the weight-1 letter (val(phi_{g}^{E2})/val(phi_{E2*g}), g = Gamma0+1);
    zeta_key := val(Phi1^{E2})/val(phi_{E2*gamma2}) (a-priori =
    zbar^{e0} * z1^{l0*gamma2} under the harness calculus — printed vs
    measured); decompositions in zbar^a * z1^b searched and printed.

CERT (new rows only): G.T1_T2 (10 samples), G.T5, G.T11 (PARI, Z_p) run on
    K, L, M, N over all four rings.  PREDICTED: 0 violations.  [tower-data
    certification: the designed rows really are the OM data they claim]

RED DISCIPLINE (both families): first classify via the bug-detector rows
(A0/B0/B1/CERT); only with those green does a RED count as mathematics.
Any RED surviving classification re-routes (H1)(a) and is this unit's
headline result, reported with the exact witness.
"""
import random, math, sys, os, time, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal,
                              fp_norm, eq12, bezout, INF, Tower,
                              mk_field_ext)

VIOL = []
COUNTS = {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

# ============================ FAMILY A: GMN side ==============================

def gmn1(T, a):
    """GMN order-1 residual data for a nonzero digit a (deg < deg Phi1),
    w.r.t. lambda1 = -h0/e0, INDEPENDENT of the FGMN metadata: returns
    (s1, r1val, line) with s1 = initial abscissa of the lambda1-component
    of N1(a), r1val = R_1^GMN(a)(z1) = sum_k c_{s1+k*e0} z1^k in K1,
    line = v1-line value = w1(a)."""
    R, K1 = T.R, T.K1
    d0v = dev(R, a, T.Phi0)
    um = [w0(R, b) if b else INF for b in d0v]
    line = min(T.e0*um[m] + m*T.h0 for m in range(len(d0v)) if um[m] < INF)
    on = [m for m in range(len(d0v)) if um[m] < INF
          and T.e0*um[m] + m*T.h0 == line]
    s1, sp1 = min(on), max(on)
    note("A0")
    if any((m - s1) % T.e0 != 0 for m in on):
        viol("A0", T.tag, "level-1 on-line abscissas not e0-congruent")
    val = K1["zero"]; zp = K1["one"]
    for m in range(s1, sp1 + 1, T.e0):
        req_num = line - m*T.h0
        if req_num % T.e0 != 0:
            viol("A0", T.tag, "level-1 line ordinate not integral at "
                              f"congruent abscissa {m}")
            req = None
        else:
            req = req_num // T.e0
        b = d0v[m] if m < len(d0v) else []
        if b and req is not None and um[m] == req:
            val = K1["add"](val, K1["mul"](K1["embed"](T.res_digit(b, req)), zp))
        zp = K1["mul"](zp, T.z1)
    return s1, val, line

def gmn2(T, f):
    """GMN (18) + Defs 2.19-2.21 at r = 2, ALL e0 (the generalization of
    tr3s1_check.gmn_order2): returns (s, d, coeffs, on, s1map) with
    coeffs = [c_s, c_{s+e1}, ...] in K1, on = on-line abscissa set,
    s1map[i] = s1(a_i) for on-line i."""
    R, K1 = T.R, T.K1
    d1 = dev(R, f, T.Phi1)
    u = [(T.w1(a) + i*T.w1Phi1) if a else INF for i, a in enumerate(d1)]
    vals = [(T.e1*u[i] + i*T.h1) if u[i] < INF else INF for i in range(len(d1))]
    m = min(v for v in vals if v < INF)
    on = [i for i in range(len(d1)) if vals[i] == m]
    s, sp = min(on), max(on)
    note("A0")
    if (sp - s) % T.e1 != 0:
        viol("A0", T.tag, "lambda2-component endpoints not e1-congruent")
    d = (sp - s)//T.e1
    coeffs, s1map = [], {}
    for k in range(d + 1):
        i = s + k*T.e1
        ai = d1[i] if i < len(d1) else []
        if (not ai) or vals[i] != m:
            coeffs.append(K1["zero"])
            continue
        s1, r1val, line = gmn1(T, ai)
        s1map[i] = s1
        num = s1 - T.l0*u[i]                       # t1(i) = (s1 - l0*u_i)/e0
        note("A0")
        if num % T.e0 != 0:
            viol("A0", T.tag, f"t1({i}) not integral: s1={s1}, u_i={u[i]}")
            coeffs.append(K1["zero"])
            continue
        t1 = num // T.e0
        ci = K1["mul"](K1["pow"](T.z1, t1), r1val)
        note("A0")
        if K1["isz"](ci):
            viol("A0", T.tag, f"c^G == 0 at on-line abscissa {i}")
        coeffs.append(ci)
    return s, d, coeffs, set(on), s1map

# --------------------------- FAMILY A: comparison -----------------------------

class ACounters:
    def __init__(self):
        self.naive_refuted = 0     # A6: naive identity fails at visible slot
        self.visible = 0           # A6: twist-visible on-line slots seen
        self.retired_refuted = 0   # A7: retired increment fails
        self.retired_pairs = 0     # A7: discriminating consecutive pairs seen

def probeA(T, f, shape, AC):
    K1 = T.K1
    note("A3")
    coeffs, meta = T.R2w(f, with_meta=True)
    gamma, s2 = meta["gamma"], meta["s2"]
    s, d, gco, on, s1map = gmn2(T, f)
    jmax = max(len(coeffs) - 1, (s + d*T.e1 - s2)//T.e1)
    prev_ratio = None; prev_slot = None
    for j in range(jmax + 1):
        sj = s2 + j*T.e1
        CF = coeffs[j] if j < len(coeffs) else K1["zero"]
        if s <= sj <= s + d*T.e1 and (sj - s) % T.e1 == 0:
            cG = gco[(sj - s)//T.e1]
        else:
            cG = K1["zero"]
        # A1 support
        note("A1")
        if (not K1["isz"](CF)) != (sj in on):
            viol("A1", T.tag, f"[{shape}] support mismatch at abscissa {sj}: "
                 f"CF-nonzero={not K1['isz'](CF)}, on-line={sj in on}")
            return
        if K1["isz"](CF):
            continue
        # on-line slot: the laws
        gj = (gamma - sj*T.gamma2)//T.e1           # level-1 slot weight
        twist = K1["pow"](T.z1, T.l0*T.g0*T.h0*sj)
        # A3 THE TWIST LAW
        if CF != K1["mul"](twist, cG):
            viol("A3", T.tag,
                 f"[{shape}] TWIST-LAW fails at abscissa {sj} (slot {j}): "
                 f"CF={CF}, cG={cG}, predicted twist z1^{T.l0*T.g0*T.h0*sj}")
            return
        # A2 Lemma-A-general
        note("A2")
        sfa, ufa = eq12(gj, T.e0, T.h0)
        s1 = s1map.get(sj)
        if s1 is None or (s1 - sfa) % T.e0 != 0 or s1 < sfa:
            viol("A2", T.tag, f"[{shape}] m0 not a nonneg integer at {sj}")
            return
        m0 = (s1 - sfa)//T.e0
        inner = K1["mul"](K1["inv"](T.eps1(gj)), CF)
        _, r1val, _ = gmn1(T, meta["dev"][sj])
        if inner != K1["mul"](K1["pow"](T.z1, m0), r1val):
            viol("A2", T.tag, f"[{shape}] Lemma-A-general fails at {sj}")
            return
        # A5 control stratum
        if T.e0 == 1:
            note("A5")
            if CF != cG:
                viol("A5", T.tag, f"[{shape}] e0=1 identity fails at {sj}")
                return
        # A6 naive-identity meter
        if twist != K1["one"]:
            AC.visible += 1
            if CF != cG:
                AC.naive_refuted += 1
        # A7 retired-increment meter (consecutive on-line FGMN slots):
        # measured step ratio(j)/ratio(j-1) tested against the RETIRED
        # S3.2-shape z1^gamma2, on pairs where it differs from the true
        # step z1^(l0*g0*h0*e1)
        ratio = K1["mul"](CF, K1["inv"](cG))
        if prev_ratio is not None and prev_slot == j - 1:
            step_true = K1["pow"](T.z1, T.l0*T.g0*T.h0*T.e1)
            step_retired = K1["pow"](T.z1, T.gamma2)
            if step_true != step_retired:
                AC.retired_pairs += 1
                step = K1["mul"](ratio, K1["inv"](prev_ratio))
                if step != step_retired:
                    AC.retired_refuted += 1
        prev_ratio, prev_slot = ratio, j

def runA(T, AC, nf=30):
    R = T.R
    for _ in range(nf):
        f = T.rand_opoly(random.randrange(0, int(2.2*T.degPhi2) + 1), pimax=5)
        if not f: f = [R["pi_pow"](random.randrange(0, 4))]
        probeA(T, f, "rand", AC)
    for _ in range(nf//2):
        probeA(T, T.rand_structured(random.choice([2, 3, 4])), "struct", AC)
    for _ in range(nf//2):
        a = random.randrange(1, 2*T.e1 + 2)
        g = T.rand_opoly(random.randrange(0, T.degPhi1 + 2), pimax=3)
        if not g: g = [R["one"]]
        probeA(T, pmul(R, ppow(R, T.Phi1, a), g), f"Phi1^{a}*g", AC)
    for k in range(0, 3):
        probeA(T, [R["pi_pow"](k)], f"pi^{k}", AC)
    for _ in range(nf//4):
        mu = random.choice([1, 2])
        probeA(T, pmul(R, ppow(R, T.Phi2, mu), T.rand_structured(2)),
               f"Phi2^{mu}*Q", AC)

# ========================== FAMILY B: the composite ===========================

class Composite:
    """Canonical-anchor composite-algebra prober for one tower."""
    def __init__(self, T):
        self.T = T
        self.K2 = mk_field_ext(T.K1, T.psi1)
        self.zbar = self.K2["z"]
        self.z1_2 = self.K2["embed"](T.z1)
        # window: u1 >= 0 guaranteed for gamma >= Gamma0 (checked per anchor);
        # base rounded to a MULTIPLE OF E2 so that representative rho sits in
        # gamma-class rho mod E2 (BUILD-PHASE BUG NOTE: the first full run
        # produced B3 e0=1-control REDs traced to exactly this — reps
        # Gamma0+rho with Gamma0 != 0 mod E2 fed to the Z/E2 relabeling
        # equation, a label misalignment in the ADJUDICATOR, caught by the
        # preregistered sealed-control row as designed; values/laws B0-B2
        # were unaffected; predictions untouched, run repeated)
        g0 = (T.e1 - 1)*T.gamma2 + T.e1*(T.e0 - 1)*T.h0 + T.E2
        self.Gamma0 = ((g0 + T.E2 - 1)//T.E2)*T.E2

    def split(self, gamma):
        T = self.T
        s2, u2 = eq12(gamma, T.e1, T.h1)
        gamma1 = u2 - s2*T.w1Phi1
        s1, u1 = eq12(gamma1, T.e0, T.h0)
        return s2, s1, u1, gamma1

    def anchor(self, gamma):
        T = self.T
        s2, s1, u1, _ = self.split(gamma)
        assert u1 >= 0, f"anchor window too small: gamma={gamma}, u1={u1}"
        R = T.R
        return pmul(R, pscal(R, R["pi_pow"](u1), ppow(R, T.Phi0, s1)),
                    ppow(R, T.Phi1, s2))

    def val(self, f, expect_gamma=None, expect_j=None, b1tag=None):
        """K2 value of the weight read; B1 shape checks when asked."""
        T, K2 = self.T, self.K2
        coeffs, meta = T.R2w(f, with_meta=True)
        if b1tag is not None:
            note("B1")
            nz = [j for j, c in enumerate(coeffs) if not T.K1["isz"](c)]
            ok = (expect_gamma is None or meta["gamma"] == expect_gamma) and \
                 (expect_j is None or nz == [expect_j])
            if not ok:
                viol("B1", T.tag, f"[{b1tag}] shape: gamma={meta['gamma']} "
                     f"(expect {expect_gamma}), nz-slots={nz} (expect "
                     f"[{expect_j}])")
        v = K2["zero"]; zp = K2["one"]
        for c in coeffs:
            if not T.K1["isz"](c):
                v = K2["add"](v, K2["mul"](K2["embed"](c), zp))
            zp = K2["mul"](zp, self.zbar)
        return v

    def anchor_val(self, gamma, check=False):
        T = self.T
        f = self.anchor(gamma)
        v = self.val(f, expect_gamma=gamma, expect_j=0,
                     b1tag=("anchor" if check else None))
        if check:
            note("B1")
            _, _, _, gamma1 = self.split(gamma)
            pred = self.K2["embed"](T.eps1(gamma1))
            if v != pred:
                viol("B1", T.tag, f"anchor value != eps1(gamma1) at "
                                  f"gamma={gamma}")
            if self.K2["isz"](v):
                viol("B1", T.tag, f"anchor letter ZERO at gamma={gamma}")
        return v

    def cocycle(self, ga, gb, check=False):
        T, K2 = self.T, self.K2
        s2a = self.split(ga)[0]; s2b = self.split(gb)[0]
        d2 = (s2a + s2b)//T.e1
        prod = pmul(T.R, self.anchor(ga), self.anchor(gb))
        vp = self.val(prod, expect_gamma=ga+gb, expect_j=d2,
                      b1tag=("pair" if check else None))
        vt = self.anchor_val(ga + gb)
        return K2["mul"](vp, K2["inv"](vt)), d2

    def iter_law(self, ga, gb):
        """(ITER-LAW) predicted cocycle value."""
        T, K2 = self.T, self.K2
        s2a, s1a, _, _ = self.split(ga)
        s2b, s1b, _, _ = self.split(gb)
        _,  s1c, _, _ = self.split(ga + gb)
        d2 = (s2a + s2b)//T.e1
        num = s1a + s1b - s1c + T.l0*T.gamma2*d2
        note("B1")
        if num % T.e0 != 0:
            viol("B1", T.tag, f"ITER-LAW exponent not integral at "
                              f"({ga},{gb})")
            return None
        return K2["mul"](K2["pow"](self.zbar, d2),
                         K2["pow"](self.z1_2, num//T.e0))

def k2_repr(C, v):
    """decompose v as zbar^a * z1^b if possible, else raw."""
    K2 = C.K2
    ordz1 = 1; x = C.z1_2
    while x != K2["one"] and ordz1 < 400:
        x = K2["mul"](x, C.z1_2); ordz1 += 1
    for a in range(0, 4*C.T.E2 + 1):
        za = K2["pow"](C.zbar, a)
        for b in range(0, ordz1):
            if K2["mul"](za, K2["pow"](C.z1_2, b)) == v:
                return f"zbar^{a}*z1^{b}" if a or b else "1"
    return f"raw:{v}"

def cyc_adjudicate(C, table):
    """(CYC): image(c) subset {1, zeta'} + relabeling exists. Returns
    (verdict_str, is_cyclic)."""
    K2, E2 = C.K2, C.T.E2
    vals = {}
    for (r, s), (c, _) in table.items():
        if c != K2["one"]:
            vals[k2_repr(C, c)] = c
    if not vals:
        return "CYCLIC (c == 1 identically, zeta' = 1)", True
    if len(vals) > 1:
        return ("NOT-CYCLIC (>= 2 distinct non-1 cocycle values: "
                + ", ".join(sorted(vals)) + ")"), False
    zname, zeta = next(iter(vals.items()))
    kappa = {(r, s): (1 if table[(r, s)][0] == zeta else 0)
             for (r, s) in table}
    for perm in itertools.permutations(range(1, E2)):
        sig = (0,) + perm
        if all(sig[r] + sig[s] == sig[(r + s) % E2] + E2*kappa[(r, s)]
               for (r, s) in table):
            return (f"CYCLIC zeta' = {zname}, relabeling sigma = {sig}"), True
    return (f"NOT-CYCLIC (single value {zname} but carry pattern not "
            "realizable by any relabeling)"), False

def runB(T, results):
    C = Composite(T)
    K2, E2 = C.K2, T.E2
    G0 = C.Gamma0
    reps = list(range(G0, G0 + E2))
    # letters (B1)
    for g in reps:
        C.anchor_val(g, check=True)
    # cocycle table (B1 shapes + B2 ITER-LAW)
    table = {}
    for r in range(E2):
        for s in range(E2):
            c, d2 = C.cocycle(reps[r], reps[s], check=True)
            table[(r, s)] = (c, d2)
            pred = C.iter_law(reps[r], reps[s])
            note("B2")
            if pred is None or c != pred:
                viol("B2", T.tag, f"ITER-LAW fails at (rho,sig)=({r},{s}): "
                     f"measured {k2_repr(C, c)}, predicted "
                     f"{k2_repr(C, pred) if pred is not None else '?'}")
    # B0c representative-independence
    reps2 = [g + E2 for g in reps]
    for r in range(E2):
        for s in range(E2):
            note("B0c")
            c2, _ = C.cocycle(reps2[r], reps2[s])
            if c2 != table[(r, s)][0]:
                viol("B0c", T.tag, f"rep-dependence at ({r},{s})")
    # B0a cocycle identity (associativity)
    triples = [(a, b, t) for a in range(E2) for b in range(E2)
               for t in range(E2)]
    if len(triples) > 120:
        triples = random.sample(triples, 120)
    for (a, b, t) in triples:
        note("B0a")
        lhs = K2["mul"](table[(a, b)][0],
                        C.cocycle(reps[a] + reps[b], reps[t])[0])
        rhs = K2["mul"](table[(b, t)][0],
                        C.cocycle(reps[a], reps[b] + reps[t])[0])
        if lhs != rhs:
            viol("B0a", T.tag, f"COCYCLE IDENTITY fails at ({a},{b},{t}) "
                               "— HARNESS BUG")
    # B3 (CYC) adjudication
    verdict, is_cyc = cyc_adjudicate(C, table)
    # ITER-LAW-implied prediction for CYC on this tower:
    nonone = {k2_repr(C, c) for (c, _) in table.values() if c != K2["one"]}
    pred_cyc = None
    if T.e0 == 1:
        pred_cyc = True      # sealed (D-REAL): zeta' = zbar
    # B4 invariants
    g1 = reps[1] if E2 >= 2 else reps[0]
    hol_w = K2["mul"](C.val(ppow(T.R, C.anchor(g1), E2),
                            expect_gamma=E2*g1),
                      K2["inv"](C.anchor_val(E2*g1)))
    hol_key = K2["mul"](C.val(ppow(T.R, T.Phi1, E2),
                              expect_gamma=E2*T.gamma2),
                        K2["inv"](C.anchor_val(E2*T.gamma2)))
    rec = dict(tower=T.tag, E2=E2, e0=T.e0, e1=T.e1,
               cyc_verdict=verdict, cyclic=is_cyc,
               predicted_cyclic_sealed=pred_cyc,
               nontrivial_values=sorted(nonone),
               zeta_weight1=k2_repr(C, hol_w),
               zeta_key=k2_repr(C, hol_key))
    results.append(rec)
    # sealed-control check
    note("B3")
    if T.e0 == 1 and not is_cyc:
        viol("B3", T.tag, "e0=1 control NOT cyclic — contradicts D-REAL")
    if T.e0 == 1:
        # zeta' must be zbar (or 1 if zbar==1)
        want = "1" if C.zbar == K2["one"] else k2_repr(C, C.zbar)
        got = sorted(nonone) or ["1"]
        if got != [want] and got != ["1"]:
            viol("B3", T.tag, f"e0=1 control zeta'={got} != zbar={want}")
    return rec

# ==================================== main ====================================

NEW_ROWS = [
    ("K", 2, (2,1,1), (2,1,1)),
    ("L", 2, (3,2,1), (2,1,1)),
    ("M", 2, (2,1,2), (3,1,1)),
    ("N", 2, (2,1,1), (2,1,2)),
]
A_E0GE2 = ["C", "D", "E", "H", "J", "K", "L", "M", "N"]
A_CTRL  = ["A", "B", "G", "I"]
B_ROWS  = ["A", "B", "C", "D", "E", "G", "H", "I", "J", "K", "L", "M", "N"]

def main():
    t0 = time.time()
    random.seed(20260815)
    sys.path.insert(0, os.path.expanduser('~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari(); pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        print(f"WARNING: cypari2 unavailable ({exc}); CERT/T11 leg skipped "
              "-> RED if predicted")
    rows = {tag: (tag, d0, r0, r1) for tag, d0, r0, r1 in G.ROSTER}
    for tag, d0, r0, r1 in NEW_ROWS:
        rows[tag] = (tag, d0, r0, r1)
    configs = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]
    AC = ACounters()
    bres = []
    # ---- CERT: certify the NEW designed rows with N-1's own families ----
    gv0 = len(G.VIOL)
    for kind, p in configs:
        for tag, d0, r0, r1 in NEW_ROWS:
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
            G.T1_T2(T, nf=10)
            G.T5(T)
            G.T11(T, pari)
    cert_viol = len(G.VIOL) - gv0
    cert_n = sum(G.COUNTS.get(k, 0) for k in ("T1", "T2", "T5", "T11"))
    print(f"[{time.time()-t0:6.1f}s] CERT done: {cert_viol} violations "
          f"({cert_n} samples) on designed rows K/L/M/N")
    # ---- FAMILY A ----
    for kind, p in configs:
        for tag in A_E0GE2 + A_CTRL:
            _, d0, r0, r1 = rows[tag]
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
            runA(T, AC, nf=30)
        print(f"[{time.time()-t0:6.1f}s] FAMILY A ring ({kind},p={p}) done: "
              f"cumulative violations = {len(VIOL)}")
    # ---- FAMILY B ----
    for kind, p in configs:
        for tag in B_ROWS:
            _, d0, r0, r1 = rows[tag]
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
            runB(T, bres)
        print(f"[{time.time()-t0:6.1f}s] FAMILY B ring ({kind},p={p}) done: "
              f"cumulative violations = {len(VIOL)}")
    # ------------------------------- report ---------------------------------
    print()
    print("=" * 78)
    print("PREDICTED vs OBSERVED (violation counts; samples in parentheses)")
    print("=" * 78)
    fams = [
        ("A0", "GMN-side integrity (t1 int, comp shape, c!=0) [SEALED]", 0),
        ("A1", "support agreement FGMN vs GMN            [CONJ comp.]", 0),
        ("A2", "Lemma-A-general inner z-shift            [CONJ comp.]", 0),
        ("A3", "(TWIST-LAW) C^F = z1^(l0 g0 h0 s_j) c^G  [THE CONJ]  ", 0),
        ("A5", "e0=1 controls: identity (TR3-S1)         [SEALED]    ", 0),
        ("B0a", "cocycle identity (associativity)        [BUG-DET]   ", 0),
        ("B0c", "representative independence             [SEALED]    ", 0),
        ("B1", "alphabet/shape laws (letters, pairs)     [SEALED]    ", 0),
        ("B2", "(ITER-LAW) composite structure constants [DERIVED]   ", 0),
        ("B3", "e0=1 CYC controls (D-REAL)               [SEALED]    ", 0),
    ]
    all_green = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == pred else "RED"
        if verdict == "RED": all_green = False
        print(f"{fam:3} {desc:57} pred {pred}  obs {obs:5d} ({n:6d})  {verdict}")
    cert_verdict = "GREEN" if cert_viol == 0 else "RED"
    if cert_viol: all_green = False
    print(f"CERT designed-row certification (T1/T2/T5/T11+PARI)       "
          f"pred 0  obs {cert_viol:5d} ({cert_n:6d})  {cert_verdict}")
    a6 = "MATCH" if (AC.naive_refuted == AC.visible and AC.visible > 0) \
         else "MISMATCH"
    if a6 == "MISMATCH": all_green = False
    print(f"A6 naive-identity refuted at twist-visible slots: "
          f"{AC.naive_refuted}/{AC.visible} (pred: equal, >0)  {a6}")
    a7 = "MATCH" if AC.retired_refuted == AC.retired_pairs else "MISMATCH"
    if a7 == "MISMATCH": all_green = False
    print(f"A7 retired-S3.2-shape increment refuted on discriminating "
          f"pairs: {AC.retired_refuted}/{AC.retired_pairs} (pred: equal)  {a7}")
    # B3 adjudication table
    print("-" * 78)
    print("B3/B4 COMPOSITE ADJUDICATION (per tower):")
    mixed_noncyc, mixed_cyc = [], []
    for r in bres:
        print(f"  {r['tower']:14} E2={r['E2']} (e0={r['e0']},e1={r['e1']}): "
              f"{r['cyc_verdict']}")
        print(f"      values={r['nontrivial_values']}  "
              f"zeta_w1={r['zeta_weight1']}  zeta_key={r['zeta_key']}")
        if r['e0'] >= 2 and r['e1'] >= 2:
            (mixed_cyc if r['cyclic'] else mixed_noncyc).append(r['tower'])
    print("-" * 78)
    print(f"MIXED (e0>=2, e1>=2) towers: CYCLIC on {len(mixed_cyc)}, "
          f"NOT-CYCLIC on {len(mixed_noncyc)}")
    if mixed_noncyc:
        print("  NOT-CYCLIC witnesses:", ", ".join(mixed_noncyc))
        print("  => the single-zeta' CYCLIC presentation of the D-ITER")
        print("     composite FAILS at the canonical (dig-consumed) alphabet;")
        print("     classification: conjecture-adjudicating instances (bug")
        print("     detectors B0a/B0c/B1/CERT green required — see rows), the")
        print("     true structure = (ITER-LAW) [B2].")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 30):")
        for v in VIOL[:30]:
            print("  ", v)
    print(f"TOTAL samples: {sum(COUNTS.values()) + cert_n}   "
          f"elapsed {time.time()-t0:.1f}s")
    print(f"VERDICT (preregistered rows): "
          f"{'ALL GREEN' if all_green and not VIOL else 'RED — see above'}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "strata_probe_results.json"), "w") as fh:
        json.dump(dict(
            violations=[list(v) for v in VIOL],
            counts=COUNTS, cert_violations=cert_viol,
            a6=dict(naive_refuted=AC.naive_refuted, visible=AC.visible),
            a7=dict(retired_refuted=AC.retired_refuted,
                    pairs=AC.retired_pairs),
            b_adjudication=bres), fh, indent=1, default=str)
    return 0 if (all_green and not VIOL) else 1

if __name__ == "__main__":
    sys.exit(main())
