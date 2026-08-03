#!/usr/bin/env python3
"""iterlawlift_corner.py — the (ITER-LAW-LIFT) CORNER probe: GENERAL LAWFUL
LIFTS at g0 = 1 (the one open stratum of the ACCEPTED ITER-LAW; violations can
only live at delta1 = 1 pairs, the lone lift-form-consuming step PAIR-VAL
Case II).  Wave-18 unit 5 (docs/SYNTHESIS_PASS8_2026-08-08.md S4 queue #5,
S3(iii)); prereg note lean/notes/openmath/ITERLAWLIFT_CORNER_2026-08-08.md.
TWO-COMMIT SEAL: this file + the prereg note commit BEFORE any run; the run
verdict lands at commit 2.  The sealed ITER-LAW falsifier iterlaw_check.py is
NOT touched.

CHARGE.  The accepted ITER-LAW (ITERLAW_2026-08-08.md; ACCEPTED 2026-08-03 on
the harness tower class, STANDARD-LIFT) leaves residual (ITER-LAW-LIFT) open
exactly at g0 = 1 AND delta1 = 1.  This probe instantiates GENERAL lawful monic
lifts Phi1 at g0 = 1 — the full lawful class (TR3-S2 S0: deg Phi1 = e0*g0*d0,
w1(Phi1) = e0*g0*h0, order-1 residual condition R_{lambda0}(Phi1) ~ psi0),
parameterized digit-by-digit (see LIFT FREEDOM below) — and measures the
accepted law's display verbatim on anchor-pair blocks.

CANDIDATE (preregistered): the accepted display
    c(gamma,gamma') = zbar^{d2} * z1^{(s1+s1'-s1(gamma+gamma')+l0*gamma2*d2)/e0}
HOLDS UNCHANGED for every lawful lift at the corner.  WHY (the degeneration
rationale, sealed pre-run): at g0 = 1 the level-1 extension is trivial
(K1 = K0, z1 = -psi0(0) a SCALAR); lawfulness PINS the single on-line lift
datum — the k = 0 digit's residue res(b0/pi^{h0}) = psi0(0) — so the Case-II
on-line read residue -res(b0/pi^{h0}) = -psi0(0) = z1 is LIFT-COVARIANT and
cancels identically against the standard-lift computation; ALL lift freedom
(the b0 tail, the mid digits b_1..b_{e0-1}) sits STRICTLY ABOVE the line and
reads 0; the anchor normalizations val(phi_gamma) are single-digit
developments, lift-form-free.  THE ONE OPEN STEP the probe cannot decide (the
honest gap named in the prereg): strictly-above-the-line must survive the
RECURSIVE re-reduction of the correction tail (when S1''+k >= e0 the mid
digits re-enter the reduction Phi0^{e0} = Phi1 - correction); variants V3/V5
are designed to maximize exactly that recursion.

LIFT FREEDOM at g0 = 1 (derived in prereg S1; Phi0-development
Phi1 = Phi0^{e0} + sum_{k<e0} b_k Phi0^k, deg b_k < d0):
  lawful <=> w0(b0) = h0 with res(b0/pi^{h0}) = psi0(0) = c0,  and for
  1 <= k <= e0-1: w0(b_k) >= amin(k) := ceil((e0-k)h0/e0)  (strictly above the
  line automatically, since gcd(e0,h0) = 1 makes equality impossible).
VARIANTS per (ring,row) instance (residues drawn fresh, global seed):
  V0-std     the standard lift (control: reproduces the ACCEPTED setting)
  V1-tail x3 b0 tail: + pi^{h0+1 or h0+2} * r(x), r random nonzero (residue
             preserved; includes the chat -> chat + pi*r lift freedom)
  V2-mid  x3 one mid digit k in [1,e0) at the MINIMAL lawful valuation amin(k)
  V3-dense x2 b0 tail + ALL mid digits at amin(k), random nonzero residues
             (the adversarial extreme; maximal recursive re-reduction)
  V4-deep x2 random subset of digits at amin + rand(1..3) (deep tail)
  V5-top  x1 k = e0-1 alone at amin(e0-1) (top-adjacent recursion trigger)

================================ TOWER ROSTER =================================
(d0; e0,h0,g0; e1,h1,g1) over all four rings {Z_2, Z_3, F_2[[t]], F_3[[t]]};
ALL rows g0 = 1 (the corner); every tuple FRESH vs the grb_order2 roster A-J,
the strata-probe rows K/L/M/N, the iterlaw_check rows P/Q/R/S/U/V/W/X, and the
COR-4 supplement rows Y/Z:
  CA (1; 2,1,1; 2,3,1)  E2=4   minimal corner; h1=3 outer offset
  CB (2; 3,1,1; 2,1,1)  E2=6   d0=2 (polynomial digit freedom); l0=1
  CC (1; 4,3,1; 2,1,2)  E2=8   E2 >= 8; g1=2 (zbar a genuine generator); l0=3
  CD (2; 2,1,1; 3,2,1)  E2=6   e1=3, h1=2 (nontrivial outer Bezout, l1=2)
  CE (1; 5,2,1; 2,1,1)  E2=10  E2 >= 8; e0=5: four mid digits, richest freedom
  CF (1; 3,2,1; 1,1,2)  E2=3   e1=1 control: d2 == 0, pure inner carry; the
                               slot-S2+1 digit IS on the grid (grid-live leg)
Windows: W1 = [Gamma0, Gamma0+E2), W3 = W1 + 7*E2; pair blocks W1xW1 AND the
MIXED block W1xW3 (the COR-4 lesson: mixed blocks in the FIRST battery).

========================= PREREGISTERED PREDICTIONS ===========================
(violation counts; RED = observed != predicted; exit 0 iff ALL as predicted)
P1 LAWCERT  every generated variant tower passes the lawfulness gate (monic,
            degree, w1 = e0*g0*h0, residual poly == psi0 — at g0 = 1 the class
            "~ psi0" degenerates to equality, both sides monic deg 1).
            PREDICTED: 0 failures (a failure = generation bug; battery skipped
            for that variant and the run is RED).
P2 AV       L6 ANCHOR-VAL val(phi_gamma) == eps1(gamma1(gamma)) != 0 on every
            letter of W1, W3, every variant (lift-free leg: bug detector).
            PREDICTED: 0.
P3 LAW      THE CANDIDATE: measured cocycle == the accepted closed form, all
            pair blocks, all variants.                        PREDICTED: 0.
P4 PV       L7 PAIR-VAL both displayed forms + the single-slot shape clause
            (single nonzero coefficient, slot y^{d2}, weight gamma+gamma').
            PREDICTED: 0.
P5 INT      COR-1 exponent integrality.                       PREDICTED: 0.
P6 LOC      localization: violations in P3/P4/P5 with delta1 == 0 counted
            separately (those legs are lift-form-FREE-proved: L1-L6/EXP/
            Case I; a delta1=0 red is a BUG DETECTOR first). PREDICTED: 0.
P7 COVERAGE every (ring,row,variant) block has > 0 pairs with delta1 == 1
            (else NON-PROBATIVE — a seal failure, not a math verdict); roster
            includes E2 = 8 and E2 = 10 rows.                 PREDICTED: met.
P8 CONTROLS four mutation controls, each PREDICTED TO FIRE on all 4 rings:
  M1 unlawful residue swap (row CB, V3 spec + residue c0 -> c0' != c0,
     c0' != 0; K0 = F_{p^2} so c0' exists): LAW mismatches > 0 (fires at
     every delta1=1 pair by the c0'/c0 != 1 ratio).
  M2 below-line digit (row CB, V3 spec + k=1 digit at amin(1)-1 = 0): the
     LAWCERT gate flags it (w1 = 1 != 3) — validates the gate all accepted
     variants passed.
  M3 fibration-term drop (row CB, lawful V3 tower; compare measured vs the
     mutated form WITHOUT l0*gamma2*d2): fires at every d2=1 pair
     (num - 7 != 0 mod 3: deterministic non-integrality).
  M4 outer-carry drop (row CC, lawful V3 tower; mutated form without
     zbar^{d2}): fires at every d2=1 pair (g1=2 makes zbar a genuine
     generator, zbar != 1 deterministically).
CERT the BASE (standard-lift) tower data of all 24 (ring,row) instances
     certified by the harness's own families: G.T1_T2 (nf=6) + G.T5 internal
     + G.T11 (PARI factorpadic) on the Z_p instances (cypari2 importability
     confirmed on this box pre-seal).                         PREDICTED: 0.

DETERMINISTIC: random.seed(20260903) (fresh seed; iterlaw_check used 20260825,
the COR-4 supplement 20260808).  EXACT arithmetic only.  Exit 0 iff all GREEN.
JSON: iterlawlift_corner_results.json.  Any RED: classify per the standing
discipline (CERT/LAWCERT/AV/LOC reds are bug detectors first); a surviving RED
means the CANDIDATE is wrong — the violating (row, ring, variant, lift
parameter, pair) tuple is the unit's headline result; do not touch the seal.
"""
import random, sys, os, time, json, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal, pneg,
                              eq12, bezout, INF, Tower)
import strata_probe as SP

VIOL = []
COUNTS = {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

ROWS = [
    ("CA", 1, (2,1,1), (2,3,1)),
    ("CB", 2, (3,1,1), (2,1,1)),
    ("CC", 1, (4,3,1), (2,1,2)),
    ("CD", 2, (2,1,1), (3,2,1)),
    ("CE", 1, (5,2,1), (2,1,1)),
    ("CF", 1, (3,2,1), (1,1,2)),
]
CONFIGS = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]

# ---------------------------- lift construction ------------------------------
def a_min(T, k):
    """minimal lawful pi-valuation of mid digit k, 1 <= k <= e0-1:
    ceil((e0-k)*h0/e0); strictly above the line since gcd(e0,h0)=1."""
    return -((-(T.e0 - k)*T.h0)//T.e0)

def make_tower(kind, p, d0, r0, r1, tag):
    T = Tower(kind, p, d0, r0, r1, tag)
    T.Phi1_std = list(T.Phi1)
    return T

def apply_pert(T, spec):
    """spec: list of (k, a, resK0) — add pi^a * lift(res) * Phi0^k to the
    STANDARD lift.  Sets T.Phi1 (and rebuilds T.Phi2 for hygiene)."""
    R = T.R
    P = list(T.Phi1_std)
    for (k, a, c) in spec:
        term = pscal(R, R["pi_pow"](a), pmul(R, T.liftK0(c), ppow(R, T.Phi0, k)))
        P = padd(R, P, term)
    T.Phi1 = P
    T.Phi2 = T.build_Phi2()
    return T

def lawful_check(T):
    """The lawful-monic-lift gate at g0 = 1 (prereg S1): monic, degree
    e0*g0*d0, w1(Phi1) = e0*g0*h0, level-1 residual polynomial == psi0
    (the '~' of the class degenerates to equality at g0 = 1: both sides monic
    degree 1).  Returns (ok, why)."""
    R = T.R
    A = pnorm(R, T.Phi1)
    if len(A) - 1 != T.e0*T.g0*T.d0:
        return False, f"degree {len(A)-1} != {T.e0*T.g0*T.d0}"
    if A[-1] != R["one"]:
        return False, "not monic"
    wv = T.w1(T.Phi1)
    if wv != T.e0*T.g0*T.h0:
        return False, f"w1 = {wv} != {T.e0*T.g0*T.h0}"
    try:
        rp = T.R1w(T.Phi1, T.e0*T.g0*T.h0)
    except AssertionError as exc:
        return False, f"residual read: {exc}"
    want = [T.psi0[0], T.psi0[1]]
    if len(rp) != 2 or list(rp) != want:
        return False, f"residual poly {rp} != psi0 {want}"
    return True, ""

def gen_specs(T):
    """The preregistered variant sweep for one (ring,row) instance."""
    e0, h0 = T.e0, T.h0
    rr = lambda: T.rand_K0(nonzero=True)
    specs = [("V0-std", [])]
    for i in range(3):
        specs.append((f"V1-tail{i}", [(0, h0 + 1 + random.randrange(0, 2), rr())]))
    for i in range(3):
        k = random.randrange(1, e0)
        specs.append((f"V2-mid{i}", [(k, a_min(T, k), rr())]))
    for i in range(2):
        sp = [(0, h0 + 1, rr())] + [(k, a_min(T, k), rr()) for k in range(1, e0)]
        specs.append((f"V3-dense{i}", sp))
    for i in range(2):
        sp = []
        for k in range(0, e0):
            if random.random() < 0.5:
                base = (h0 + 1) if k == 0 else a_min(T, k)
                sp.append((k, base + random.randrange(1, 4), rr()))
        specs.append((f"V4-deep{i}", sp))
    specs.append(("V5-top", [(e0 - 1, a_min(T, e0 - 1), rr())]))
    return specs

# ------------------------------- the battery ---------------------------------
def val_and_shape(T, C, ga, gb):
    """K2 value of the pair read + the L7 shape clause; returns
    (value, d2, shape_bad_or_None)."""
    K2 = C.K2
    s2a = C.split(ga)[0]; s2b = C.split(gb)[0]
    d2 = (s2a + s2b)//T.e1
    prod = pmul(T.R, C.anchor(ga), C.anchor(gb))
    coeffs, meta = T.R2w(prod, with_meta=True)
    nz = [j for j, c in enumerate(coeffs) if not T.K1["isz"](c)]
    shape_bad = None
    if meta["gamma"] != ga + gb or nz != [d2]:
        shape_bad = (f"gamma={meta['gamma']} (want {ga+gb}), nz={nz} "
                     f"(want [{d2}])")
    v = K2["zero"]; zp = K2["one"]
    for c in coeffs:
        if not T.K1["isz"](c):
            v = K2["add"](v, K2["mul"](K2["embed"](c), zp))
        zp = K2["mul"](zp, C.zbar)
    return v, d2, shape_bad

def closed_form(T, C, ga, gb):
    """Local transcription of the accepted S5 display (checked against
    C.iter_law, the probe-era implementation, as a transcription control)."""
    K2 = C.K2
    s2a, s1a, _, _ = C.split(ga)
    s2b, s1b, _, _ = C.split(gb)
    _,   s1c, _, _ = C.split(ga + gb)
    d2 = (s2a + s2b)//T.e1
    num = s1a + s1b - s1c + T.l0*T.gamma2*d2
    if num % T.e0 != 0:
        return None, d2, num
    return K2["mul"](K2["pow"](C.zbar, d2),
                     K2["pow"](C.z1_2, num//T.e0)), d2, num

def run_variant(T, C, vname, results):
    K2, E2 = C.K2, T.E2
    W1 = list(range(C.Gamma0, C.Gamma0 + E2))
    W3 = [g + 7*E2 for g in W1]
    tag = f"{T.tag}:{vname}"
    for g in W1 + W3:
        note("AV")
        v = C.anchor_val(g)
        pred = K2["embed"](T.eps1(C.split(g)[3]))
        if v != pred or K2["isz"](v):
            viol("AV", tag, f"ANCHOR-VAL fails at gamma={g}")
    cov = 0
    for A, B in ((W1, W1), (W1, W3)):
        for ga in A:
            for gb in B:
                s2a, s1a, u1a, b1a = C.split(ga)
                s2b, s1b, u1b, b1b = C.split(gb)
                d2 = (s2a + s2b)//T.e1
                d1 = (s1a + s1b)//T.e0
                if d1 == 1: cov += 1
                # PV: PAIR-VAL both forms + shape
                note("PV")
                v, d2v, shape_bad = val_and_shape(T, C, ga, gb)
                z1K2 = C.z1_2
                predA = K2["mul"](K2["pow"](C.zbar, d2),
                        K2["mul"](K2["pow"](z1K2, d1),
                                  K2["embed"](T.eps1(b1a + b1b))))
                predB = K2["mul"](K2["pow"](C.zbar, d2),
                        K2["mul"](K2["embed"](T.eps1(b1a)),
                                  K2["embed"](T.eps1(b1b))))
                pv_bad = shape_bad is not None or v != predA or v != predB
                if pv_bad:
                    viol("PV", tag, f"PAIR-VAL at ({ga},{gb}) d1={d1}: "
                         f"{shape_bad or 'value mismatch'}")
                    if d1 == 0: viol("LOC", tag, f"PV red at delta1=0 ({ga},{gb})")
                # INT
                note("INT")
                cf, _, num = closed_form(T, C, ga, gb)
                if num % T.e0 != 0:
                    viol("INT", tag, f"integrality at ({ga},{gb})")
                    if d1 == 0: viol("LOC", tag, f"INT red at delta1=0 ({ga},{gb})")
                # LAW: measured cocycle vs the accepted display
                note("LAW")
                vt = C.anchor_val(ga + gb)
                c = K2["mul"](v, K2["inv"](vt))
                if cf is None or c != cf:
                    viol("LAW", tag, f"LAW at ({ga},{gb}) d1={d1} d2={d2}: "
                         f"measured {SP.k2_repr(C, c)}")
                    if d1 == 0: viol("LOC", tag, f"LAW red at delta1=0 ({ga},{gb})")
                # TRS: transcription control vs the probe-era implementation
                note("TRS")
                pf = C.iter_law(ga, gb)
                if (cf is None) != (pf is None) or (cf is not None and cf != pf):
                    viol("TRS", tag, f"transcription mismatch at ({ga},{gb})")
    results["coverage"][tag] = cov
    if cov == 0:
        viol("COV", tag, "no delta1=1 pairs: NON-PROBATIVE block")

# ------------------------------ mutation controls ----------------------------
def dense_spec(T):
    rr = lambda: T.rand_K0(nonzero=True)
    return [(0, T.h0 + 1, rr())] + \
           [(k, a_min(T, k), rr()) for k in range(1, T.e0)]

def law_mismatches(T, C, block_only_W1=True):
    E2 = T.E2
    W1 = list(range(C.Gamma0, C.Gamma0 + E2))
    bad = 0
    for ga in W1:
        for gb in W1:
            v, d2, _ = val_and_shape(T, C, ga, gb)
            vt = C.anchor_val(ga + gb)
            c = C.K2["mul"](v, C.K2["inv"](vt))
            cf, _, _ = closed_form(T, C, ga, gb)
            if cf is None or c != cf:
                bad += 1
    return bad

def run_controls(results):
    ROWMAP = {tag: (tag, d0, r0, r1) for tag, d0, r0, r1 in ROWS}
    fires = {"M1": [], "M2": [], "M3": [], "M4": []}
    for kind, p in CONFIGS:
        # ---- M1: unlawful residue swap (row CB) ----
        tag, d0, r0, r1 = ROWMAP["CB"]
        T = make_tower(kind, p, d0, r0, r1, f"{kind},p={p},CB")
        c0 = T.psi0[0]
        c0p = next(c for c in T.K0["elements"]()
                   if not T.K0["isz"](c) and c != c0)
        spec = dense_spec(T) + [(0, T.h0, T.K0["add"](c0p, T.K0["neg"](c0)))]
        apply_pert(T, spec)
        C = SP.Composite(T)
        bad = law_mismatches(T, C)
        note("M1"); fires["M1"].append(bad)
        if bad == 0:
            viol("M1", T.tag, "control did NOT fire (0 LAW mismatches)")
        # ---- M2: below-line digit (row CB) ----
        T2 = make_tower(kind, p, d0, r0, r1, f"{kind},p={p},CB")
        spec2 = dense_spec(T2) + [(1, a_min(T2, 1) - 1, T2.rand_K0(nonzero=True))]
        apply_pert(T2, spec2)
        ok, why = lawful_check(T2)
        note("M2"); fires["M2"].append(0 if ok else 1)
        if ok:
            viol("M2", T2.tag, "gate did NOT flag the below-line digit")
        # ---- M3: fibration-term drop (row CB, LAWFUL V3 tower) ----
        T3 = make_tower(kind, p, d0, r0, r1, f"{kind},p={p},CB")
        apply_pert(T3, dense_spec(T3))
        okl, _ = lawful_check(T3)
        C3 = SP.Composite(T3)
        bad3 = 0
        W1 = list(range(C3.Gamma0, C3.Gamma0 + T3.E2))
        for ga in W1:
            for gb in W1:
                v, d2, _ = val_and_shape(T3, C3, ga, gb)
                vt = C3.anchor_val(ga + gb)
                c = C3.K2["mul"](v, C3.K2["inv"](vt))
                s1a = C3.split(ga)[1]; s1b = C3.split(gb)[1]
                s1c = C3.split(ga + gb)[1]
                num = s1a + s1b - s1c            # fibration term DROPPED
                if num % T3.e0 != 0:
                    bad3 += 1
                    continue
                mut = C3.K2["mul"](C3.K2["pow"](C3.zbar, d2),
                                   C3.K2["pow"](C3.z1_2, num//T3.e0))
                if mut != c:
                    bad3 += 1
        note("M3"); fires["M3"].append(bad3)
        if not okl:
            viol("M3", T3.tag, "M3 base tower unexpectedly unlawful")
        if bad3 == 0:
            viol("M3", T3.tag, "control did NOT fire")
        # ---- M4: outer-carry drop (row CC, LAWFUL V3 tower) ----
        tag4, d04, r04, r14 = ROWMAP["CC"]
        T4 = make_tower(kind, p, d04, r04, r14, f"{kind},p={p},CC")
        apply_pert(T4, dense_spec(T4))
        okl4, _ = lawful_check(T4)
        C4 = SP.Composite(T4)
        bad4 = 0
        W14 = list(range(C4.Gamma0, C4.Gamma0 + T4.E2))
        for ga in W14:
            for gb in W14:
                v, d2, _ = val_and_shape(T4, C4, ga, gb)
                vt = C4.anchor_val(ga + gb)
                c = C4.K2["mul"](v, C4.K2["inv"](vt))
                s1a = C4.split(ga)[1]; s1b = C4.split(gb)[1]
                s1c = C4.split(ga + gb)[1]
                num = s1a + s1b - s1c + T4.l0*T4.gamma2*d2
                if num % T4.e0 != 0:
                    bad4 += 1
                    continue
                mut = C4.K2["pow"](C4.z1_2, num//T4.e0)   # zbar^{d2} DROPPED
                if mut != c:
                    bad4 += 1
        note("M4"); fires["M4"].append(bad4)
        if not okl4:
            viol("M4", T4.tag, "M4 base tower unexpectedly unlawful")
        if bad4 == 0:
            viol("M4", T4.tag, "control did NOT fire")
    results["controls"] = fires

# ----------------------------------- main ------------------------------------
def main():
    t0 = time.time()
    random.seed(20260903)
    sys.path.insert(0, os.path.expanduser(
        '~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari(); pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        print(f"WARNING: cypari2 unavailable ({exc}); CERT/T11 leg skipped "
              "-> RED if predicted")
    results = {"coverage": {}, "lawcert": [], "controls": {}, "variants": {}}
    # ---- CERT on the BASE (standard-lift) towers ----
    gv0 = len(G.VIOL)
    for kind, p in CONFIGS:
        for tag, d0, r0, r1 in ROWS:
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
            G.T1_T2(T, nf=6)
            G.T5(T)
            G.T11(T, pari)
    cert_viol = len(G.VIOL) - gv0
    cert_n = sum(G.COUNTS.get(k, 0) for k in ("T1", "T2", "T5", "T11"))
    print(f"[{time.time()-t0:6.1f}s] CERT done: {cert_viol} violations "
          f"({cert_n} samples) on base rows CA/CB/CC/CD/CE/CF")
    # ---- the variant battery ----
    nvar = 0
    for kind, p in CONFIGS:
        for tag, d0, r0, r1 in ROWS:
            T0v = make_tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
            specs = gen_specs(T0v)
            for vname, spec in specs:
                T = make_tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
                apply_pert(T, spec)
                note("LAWCERT")
                ok, why = lawful_check(T)
                if not ok:
                    viol("LAWCERT", f"{T.tag}:{vname}", why)
                    continue
                nvar += 1
                results["variants"][f"{T.tag}:{vname}"] = [
                    [k, a, list(c) if isinstance(c, tuple) else c]
                    for (k, a, c) in spec]
                C = SP.Composite(T)
                run_variant(T, C, vname, results)
        print(f"[{time.time()-t0:6.1f}s] ring ({kind},p={p}) done: "
              f"cumulative violations = {len(VIOL)}")
    # ---- mutation controls ----
    run_controls(results)
    print(f"[{time.time()-t0:6.1f}s] controls done")
    # -------------------------------- report --------------------------------
    print()
    print("=" * 78)
    print("PREDICTED vs OBSERVED (violation counts; samples in parentheses)")
    print("=" * 78)
    fams = [
        ("LAWCERT", "P1 lawfulness gate on every variant       "),
        ("AV",      "P2 L6 ANCHOR-VAL letters W1+W3 (lift-free)"),
        ("LAW",     "P3 THE CANDIDATE: accepted display, pairs "),
        ("PV",      "P4 L7 PAIR-VAL both forms + shape         "),
        ("INT",     "P5 COR-1 exponent integrality             "),
        ("TRS",     "closed-form transcription vs C.iter_law   "),
        ("LOC",     "P6 delta1=0 localization (bug detector)   "),
        ("COV",     "P7 coverage: delta1=1 pairs per block     "),
    ]
    all_green = True
    for fam, desc in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == 0 else "RED"
        if verdict == "RED": all_green = False
        print(f"{fam:8} {desc} pred 0  obs {obs:5d} ({n:6d})  {verdict}")
    cert_verdict = "GREEN" if cert_viol == 0 else "RED"
    if cert_viol: all_green = False
    print(f"CERT     base-tower certification (T1/T2/T5/T11+PARI)      "
          f"pred 0  obs {cert_viol:5d} ({cert_n:6d})  {cert_verdict}")
    for m in ("M1", "M2", "M3", "M4"):
        fr = results["controls"].get(m, [])
        obs = sum(1 for v in VIOL if v[0] == m)
        fired = sum(1 for x in fr if x > 0)
        okc = (fired == len(fr) == 4 and obs == 0)
        if not okc: all_green = False
        print(f"{m}       control fires (pred 4/4 rings): {fired}/{len(fr)} "
              f"counts={fr}  {'GREEN' if okc else 'RED'}")
    cov = results["coverage"]
    czero = [k for k, c in cov.items() if c == 0]
    cov_ok = not czero and len(cov) > 0
    if not cov_ok: all_green = False
    print(f"P7 coverage: {len(cov)} blocks, min delta1=1 pairs "
          f"{min(cov.values()) if cov else 0}, zero-coverage blocks "
          f"{len(czero)}  {'MET' if cov_ok else 'NOT MET'}")
    print(f"variant towers accepted by the gate: {nvar} "
          f"(of {COUNTS.get('LAWCERT', 0)} generated)")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 30):")
        for v in VIOL[:30]:
            print("  ", v)
    total = sum(COUNTS.values()) + cert_n
    print(f"TOTAL samples: {total}   elapsed {time.time()-t0:.1f}s")
    print(f"VERDICT (preregistered rows): "
          f"{'ALL GREEN' if all_green and not VIOL else 'RED — see above'}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "iterlawlift_corner_results.json"), "w") as fh:
        json.dump(dict(violations=[list(v) for v in VIOL], counts=COUNTS,
                       cert_violations=cert_viol, cert_samples=cert_n,
                       coverage=results["coverage"],
                       controls=results["controls"],
                       variants=results["variants"],
                       sp_bugdetector_viol=len(SP.VIOL),
                       n_variants_accepted=nvar),
                  fh, indent=1, default=str)
    return 0 if (all_green and not VIOL) else 1

if __name__ == "__main__":
    sys.exit(main())
