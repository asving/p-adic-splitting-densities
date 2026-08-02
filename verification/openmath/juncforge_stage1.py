#!/usr/bin/env python3
"""juncforge_stage1.py — FORGE junc_bundle STAGE 1 (synthesis-6 queue #2, F1
charter, docs/SYNTHESIS_PASS6_2026-08-08.md): the corpus's FIRST DEEP RUN,
numerics-first — OM tower runs with deg f > deg Phi1 and real digit data,
tracing the clause-(iii) OUT-OF-CARRIER residual at deg f = deg Phi read
sites, testing the `gate_glue_junction` hypothesis shape, and locating the
ITER-LAW constants where DITER_RESTATE_2026-08-08.md S3 predicts.

MACHINERY: grb_order2_check.py Tower objects (N-1-certified; base rings Z_2,
Z_3, F_2[[t]], F_3[[t]]; reading-C FGMN operators R2w/R2s; w1/w2; realize1;
build_Phi2) + strata_probe.py Composite (canonical anchors phi_gamma, K2
values, window Gamma0) and k2_repr.  ITER-LAW cocycle re-implemented locally
(iter_c) to keep counters separate.  DETERMINISTIC: random.seed(20260816);
EXACT arithmetic only.

THE OBJECT UNDER TEST (Lean side, for the record).  `SideReads` clause (iii)
(HC2/Defs.lean) reads `HasAnchorK (nu.sigma.R f) nu.a nu.Ranch` and
`OrdPsiPoly nu.psi nu.Ranch nu.mu` — the STAGE residual of the WHOLE
classificand f (out-of-carrier: deg f >= deg Phi), demanded equal to the
recorded SIDE pattern T^a * (sum pat_k z^k).  `GlueJunction.junc_bundle`
(H1/GlueRun.lean:259) forces the full bundle at the junction read; the
compiled gate `gate_glue_junction` (GlueRun.lean:1105) carries it as the ONE
hypothesis at the choice-built sigma1rec, where f = fq = sigma1rec.Phi
(deg f = deg Phi, development 0 + 1*Phi).  A stage valuation is a lambda-
augmented MacLane valuation: in cumulative (harness) scale, slot functional
w1(B_j) + j*lambda on the Phi1-development, with lambda = w1Phi1 the FLAT
extension, lambda = gamma2/e1 the READ-SIDE endpoint (the harness w2), and
choice-built stages sitting at some transition-chosen lambda in between.
The stage residual R f is carried by the argmin slot set S(lambda).

============================ TOWER ROSTER ====================================
(tag, d0, (e0,h0,g0), (e1,h1,g1)) — several e0/e1 mixes incl. e0 >= 2, all
with e1*g1 >= 2 so deg Phi2 > deg Phi1 (the deep-run requirement):
  A (1; 1,1,1; 2,1,1)  e0=1 control, E2=2
  B (1; 1,2,2; 3,2,1)  e0=1, g0=2, (e1,h1)=(3,2)
  C (1; 2,1,1; 2,1,1)  e0=2, e1=2 mixed, E2=4
  K (2; 2,1,1; 2,1,1)  d0=2 mixed, K1=F_{p^4}-ish
  L (2; 3,2,1; 2,1,1)  e0=3 (nontrivial Bezout l0=2)
  M (2; 2,1,2; 3,1,1)  e1=3, g0=2
  N (2; 2,1,1; 2,1,2)  g1=2: K2 = K1[zbar] genuine extension (ITER-LAW
                        discriminator row)
over all four base rings.  N-1/strata-probe rows reused where they exist;
CERT legs (G.T1_T2 nf=6 + G.T5 + G.T11 PARI where available) re-run here on
every instance used.

===================== DEEP-RUN FAMILIES (per tower instance) =================
All f MONIC with deg f in {deg Phi2, 2*deg Phi2} > deg Phi1:
  D0 (1): f = Phi2 exactly — the DEGENERATE stratum: the compiled gate's own
      shape (U31/RCW: f = fq = sigma1rec.Phi, dev = 0 + 1*Phi).
  D1 (3): f = Phi2 + pi^m*u, unit u, m minimal + {0,1,2} with w2 > w2Phi2.
  D2 (<=4, >=2 required): f = Phi2 + C*Phi1^k, C = realize1(tau, gp) at
      controlled weight w2 = w2Phi2 + delta (delta scanned, k in {0,1}) —
      REAL DIGIT DATA with known level-1 class tau.
  D3 (2): f = Phi2^2 + pi^m*u with m*E2 > 2*w2Phi2 — deg f > deg Phi2
      strictly; width-2 terminal polygon; mu1 = 2 (nontrivial seam_window).
  DA (2): f = Phi2 + u0*phi_{gammaD} (u0 a K0-unit lift; canonical anchor at
      in-window gammaD > w2Phi2) — the terminal digit with a KNOWN anchor
      coordinate.
  D4 (2, REPORT-ONLY, no sealed rows): f = Phi2 + pi^m*u with
      0 < m*E2 < w2Phi2 — the refinement stratum (Phi2 not an approximant).

===================== PREREGISTERED PREDICTIONS ==============================
Bug detectors / sealed rows (a RED here = harness bug, never math):
 P0  CERT: G.T1_T2(nf=6) + G.T5 (+ G.T11/PARI on Z_p rows where cypari2
     loads) on every tower instance used.                     PREDICTED 0.
 P1  MacLane/K1 commutation at the terminal key: for every D0-D3/DA run,
     min_j(w2(B_j) + j*w2Phi2) over the Phi2-development == w2(f) computed
     at the Phi1 level.                                       PREDICTED 0.
     [SEALED: S2/K1 at the child key]
 P4n Every pooled run class (node-1 on-line classes B_j*Phi1^j and terminal
     B0 classes; NO Phi2-multiples, whose level-2 value is 0 by T5) has
     nonzero K2 value and nonzero anchor coordinate kappa.    PREDICTED 0.

The clause-(iii) residual (THE charter measurement):
 P2  Terminal-site case census at deg f = deg Phi2 sites (dev = B0 + Phi2):
     D0: 100% KEY-ONLY (B0 = 0; R f = R Phi2 = T^s pure key monomial: the
         residual holds NO pattern data — Ranch = 1, mu = 0; the recorded
         recentering shape (pat0 != 0 at slot 0, Ranch = z - c, mu = 1) is
         UNSATISFIABLE at this stratum's unique development: bundle clause
         (ii) demands B(s0) != 0, clause (iii) demands a binomial).
     D1/D2/DA: 100% TIE-AUGMENTED: lambda3 := w2(B0) - w2Phi2 > 0 strictly;
         the terminal side holds BOTH slots; the residual is the RANK-2
         BINOMIAL R f = R(B0) + T^s(key term): one carrier digit + one pure
         key letter — never a monomial, never carrier-only, never key-only.
     D4: lambda3 < 0 (REFINE) — report-only.        PREDICTED: exact census.
 P3  Two-scale support adjudication at every deep node-1 read site (key
     Phi1, deg f > deg Phi1), S(lambda) := argmin_j(w1(B_j) + j*lambda):
  P3a S(gamma2/e1) == the on-line (side/pattern) abscissa set. PREDICTED 0
      violations [T1/T2-adjacent consistency].
  P3b for lambda in {FLAT = w1Phi1, MID = w1Phi1 + h1/(2e1)}: S(lambda) ==
      {top slot} (the single monic key-power vertex), i.e. the stage
      residual at EVERY pre-read scale is the key-power MONOMIAL
      R(B_top)*T^(s*jtop) carrying ZERO pattern/psi/mu data. PREDICTED 0
      violations on D0-D3/DA sites.
  P3c THE AS-WRITTEN METER: #sites where S(FLAT) != S(side-endpoint) ==
      #sites (ALL of them; pattern width g1 >= 1 everywhere here), i.e.
      clause (iii)'s sigma.R-rendering reads the recorded pattern ONLY at
      the side-endpoint scale (the sigmaV/regraded scale = the harness w2);
      at every strictly-coarser stage scale it reads the top-vertex
      monomial instead.  PREDICTED: meter == site count exactly.
 P5  Landing/pattern tie at node 1 (ends_at leg): side pattern of f == psi1
     exactly (D0/D1/D2/DA; reading C, T5) and ord_psi1 == 2 with width 2*g1
     for D3 (product pattern; scalar reported, not pinned). PREDICTED 0.
 P6  GlueJunction structural legs on the measured seam (node-1 -> terminal):
     seam_width: deg Phi2 == e1*g1*deg Phi1                   PREDICTED 0;
     seam_window: terminal s0 + wSide <= mu1  (1 <= 1 on D1/D2/DA; 2 <= 2
       on D3)                                                 PREDICTED 0;
     seam_steep (cumulative-scale transcription): h1 >= 1 AND lambda3 > 0
       strictly at TIE sites (strict per-seam augmentation)   PREDICTED 0.
 P4  ITER-LAW ON RUN CLASSES (the S3(b) question): pool the runs' own
     graded classes chi (node-1 on-line slot classes, terminal B0 classes),
     in-window shifted, with anchor coordinates kappa := val(chi)/val(phi);
     for sampled pairs: val(chi_a * chi_b) ==
       kappa_a * kappa_b * c_ITER(ga, gb) * val(phi_{ga+gb}),
     c_ITER = zbar^{d2} * z1^{(s1(ga)+s1(gb)-s1(ga+gb)+l0*gamma2*d2)/e0},
     d2 = floor((s2(ga)+s2(gb))/e1)  (DITER_RESTATE S2, measured law row B2).
     PREDICTED 0 violations; METER: #pairs with c_ITER != 1 printed per
     tower (the constants APPEAR in the junction bundle's own digit
     algebra; expected > 0 on E2 > 1 rows with carry-realizing grades).
 P7  DA anchor coordinate: kappa0(terminal digit of u0*phi_gammaD) ==
     embed_K2(embed_K1(class(u0))) exactly — the terminal center digit IS
     the 𝒟₂-anchor coordinate, unit-transparent.              PREDICTED 0.

RED DISCIPLINE: P0/P1/P4n first; only with those green does a RED elsewhere
count as mathematics — then it is this unit's headline result, reported
with the exact witness (D-ITER precedent).

WHAT THIS RUN DOES NOT CLAIM: no Lean statement is proved or refuted by
numerics (falsifiers only); the D0 unsatisfiability display is a measured
shape whose Lean-side counterpart (development uniqueness at f = key) is
flagged for the stage-2 unit to adjudicate; no order >= 3 claim; no change
to any sealed strata-probe/GRB row.
"""
import random, sys, os, time, json, itertools
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal,
                              fp_norm, fp_ord, eq12, bezout, INF, Tower)
from strata_probe import Composite, k2_repr

VIOL, COUNTS = [], {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

ROWS = [
    ("A", 1, (1,1,1), (2,1,1)),
    ("B", 1, (1,2,2), (3,2,1)),
    ("C", 1, (2,1,1), (2,1,1)),
    ("K", 2, (2,1,1), (2,1,1)),
    ("L", 2, (3,2,1), (2,1,1)),
    ("M", 2, (2,1,2), (3,1,1)),
    ("N", 2, (2,1,1), (2,1,2)),
]
CONFIGS = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]

# ------------------------- local ITER-LAW cocycle -----------------------------

def iter_c(C, ga, gb):
    """(ITER-LAW) c(ga,gb) per DITER_RESTATE S2; None on non-integral exponent
    (counted as a P4 violation by the caller)."""
    T, K2 = C.T, C.K2
    s2a, s1a, _, _ = C.split(ga)
    s2b, s1b, _, _ = C.split(gb)
    _,   s1c, _, _ = C.split(ga + gb)
    d2 = (s2a + s2b)//T.e1
    num = s1a + s1b - s1c + T.l0*T.gamma2*d2
    if num % T.e0 != 0:
        return None
    return K2["mul"](K2["pow"](C.zbar, d2), K2["pow"](C.z1_2, num//T.e0))

def in_window(C, chi, gamma):
    """pi-shift a graded class into the anchor window; returns (chi~, gamma~)."""
    T = C.T
    m = 0
    if gamma < C.Gamma0:
        m = (C.Gamma0 - gamma + T.E2 - 1)//T.E2
    if m:
        chi = pscal(T.R, T.R["pi_pow"](m), chi)
        gamma += m*T.E2
    return chi, gamma

def kappa_of(C, chi, gamma):
    """anchor coordinate kappa = val(chi~)/val(phi_{gamma~}) in K2 (P4n checks)."""
    K2 = C.K2
    chit, gt = in_window(C, chi, gamma)
    v = C.val(chit, expect_gamma=gt)
    a = C.anchor_val(gt)
    note("P4n")
    if K2["isz"](v) or K2["isz"](a):
        viol("P4n", C.T.tag, f"zero class value at gamma={gt}")
        return None, None, None
    return K2["mul"](v, K2["inv"](a)), chit, gt

# ------------------------------ measurements ----------------------------------

def support_at(d1, vals, lam):
    """argmin_j (w1(B_j) + j*lam) over nonzero slots (Fractions exact)."""
    best, S = None, []
    for j in range(len(d1)):
        if vals[j] == INF:
            continue
        v = Fraction(vals[j]) + Fraction(j)*lam
        if best is None or v < best:
            best, S = v, [j]
        elif v == best:
            S.append(j)
    return set(S)

def node1_site(T, f, fam, sites):
    """Deep read at key Phi1: two-scale supports (P3), pattern tie (P5),
    returns (pattern side list, mu1, on-line slot list, dev, gamma)."""
    d1, vals, gamma = T.w2_data(f)
    K1 = T.K1
    online = [j for j in range(len(d1))
              if vals[j] < INF and T.e1*vals[j] + j*T.gamma2 == gamma]
    lamF = Fraction(T.w1Phi1)
    lamM = Fraction(T.w1Phi1) + Fraction(T.h1, 2*T.e1)
    lamS = Fraction(T.gamma2, T.e1)
    SF, SM, SS = (support_at(d1, vals, l) for l in (lamF, lamM, lamS))
    note("P3a")
    if SS != set(online):
        viol("P3a", T.tag, f"[{fam}] side-endpoint support {sorted(SS)} != "
                           f"on-line {online}")
    top = len(d1) - 1
    note("P3b")
    if SF != {top} or SM != {top}:
        viol("P3b", T.tag, f"[{fam}] stage-scale support not the top vertex: "
             f"S(FLAT)={sorted(SF)}, S(MID)={sorted(SM)}, top={top}")
    sites.append(dict(fam=fam, tower=T.tag, width=len(online),
                      as_written_differs=(SF != SS)))
    side, j0, _ = T.R2s(f)
    psi1n = fp_norm(K1, list(T.psi1))
    mu1 = fp_ord(K1, side, psi1n)
    note("P5")
    if fam in ("D0", "D1", "D2", "DA"):
        if side != psi1n:
            viol("P5", T.tag, f"[{fam}] node-1 pattern != psi1 exactly")
    elif fam == "D3":
        if mu1 != 2 or len(side) - 1 != 2*T.g1:
            viol("P5", T.tag, f"[{fam}] node-1 pattern: mu1={mu1} (want 2), "
                 f"width={len(side)-1} (want {2*T.g1})")
    return side, mu1, online, d1, gamma

def terminal_site(T, C, f, fam, mu1, records, pool):
    """Terminal read at key Phi2: P1 commutation, P2 case census, P6 legs,
    pool the B0 class."""
    R, K2 = T.R, C.K2
    d2 = dev(R, f, T.Phi2)
    v2 = [T.w2(c) if c else INF for c in d2]
    note("P1")
    mac = min(v2[j] + j*T.w2Phi2 for j in range(len(d2)) if v2[j] < INF)
    if mac != T.w2(f):
        viol("P1", T.tag, f"[{fam}] MacLane commutation: Phi2-slot-min {mac} "
                          f"!= w2(f) {T.w2(f)}")
        return
    # P6 width
    note("P6")
    if T.degPhi2 != T.e1*T.g1*T.degPhi1:
        viol("P6", T.tag, "seam_width: deg Phi2 != e1*g1*deg Phi1")
    rec = dict(tower=T.tag, fam=fam, deg=len(pnorm(R, f)) - 1)
    if len(d2) - 1 == 1:
        B0 = d2[0]
        if not B0:
            rec.update(case="KEY-ONLY", lambda3=None)
        else:
            lam3 = v2[0] - T.w2Phi2
            if lam3 > 0:
                rec.update(case="TIE-AUG", lambda3=lam3)
                kap, chit, gt = kappa_of(C, B0, v2[0])
                if kap is not None:
                    rec.update(kappa0=k2_repr(C, kap), gammaB=v2[0],
                               gB_mod_E2=v2[0] % T.E2)
                    pool.append((chit, gt, kap))
                # P6 window + steep at the TIE seam
                note("P6")
                if not (0 + 1 <= mu1):
                    viol("P6", T.tag, f"[{fam}] seam_window: 1 > mu1={mu1}")
                if not (T.h1 >= 1 and lam3 > 0):
                    viol("P6", T.tag, f"[{fam}] seam_steep: lambda3={lam3}")
            else:
                rec.update(case="REFINE", lambda3=lam3)
        note("P2")
        want = dict(D0="KEY-ONLY", D1="TIE-AUG", D2="TIE-AUG",
                    DA="TIE-AUG", D4="REFINE").get(fam)
        if want and rec["case"] != want:
            viol("P2", T.tag, f"[{fam}] terminal case {rec['case']} != "
                              f"predicted {want} (lambda3={rec['lambda3']})")
    else:
        # D3: width-2 terminal polygon (slots 0 and 2)
        onl = [j for j in range(len(d2)) if v2[j] < INF]
        rec.update(case="MULTI", slots=onl,
                   heights=[v2[j] for j in onl])
        if fam == "D3":
            B0 = d2[0]
            note("P6")
            if not (0 + 2 <= mu1):
                viol("P6", T.tag, f"[D3] seam_window: 2 > mu1={mu1}")
            if B0:
                kap, chit, gt = kappa_of(C, B0, v2[0])
                if kap is not None:
                    pool.append((chit, gt, kap))
    records.append(rec)
    return rec

def pool_node1_classes(T, C, d1, online, pool, cap=3):
    R = T.R
    take = online if len(online) <= cap else [online[0],
                                              online[len(online)//2],
                                              online[-1]]
    for j in take:
        chi = pmul(R, d1[j], ppow(R, T.Phi1, j))
        gam = T.e1*T.w1(d1[j]) + j*T.gamma2
        # class weight in w2 scale is the on-line value == gamma of the read
        kap, chit, gt = kappa_of(C, chi, gam)
        if kap is not None:
            pool.append((chit, gt, kap))

def run_pairs(T, C, pool, nmax=30):
    """P4: ITER-LAW on run-realized classes."""
    K2 = C.K2
    meter = 0
    pairs = list(itertools.combinations_with_replacement(range(len(pool)), 2))
    if len(pairs) > nmax:
        pairs = random.sample(pairs, nmax)
    for (ia, ib) in pairs:
        (ca, ga, ka), (cb, gb, kb) = pool[ia], pool[ib]
        note("P4")
        c = iter_c(C, ga, gb)
        if c is None:
            viol("P4", T.tag, f"ITER-LAW exponent non-integral at ({ga},{gb})")
            continue
        lhs = C.val(pmul(T.R, ca, cb), expect_gamma=ga + gb)
        rhs = K2["mul"](K2["mul"](ka, kb),
                        K2["mul"](c, C.anchor_val(ga + gb)))
        if lhs != rhs:
            viol("P4", T.tag, f"ITER-LAW fails on run classes at "
                 f"({ga},{gb}): lhs={lhs}, rhs={rhs}, c={k2_repr(C, c)}")
        if c != K2["one"]:
            meter += 1
    return meter, len(pairs)

# ------------------------------ family builders -------------------------------

def build_families(T, C):
    R = T.R
    fams = []
    fams.append(("D0", T.Phi2))
    m0 = (T.w2Phi2 // T.E2) + 1
    for dm in range(3):
        u = T.liftK0(T.rand_K0(nonzero=True))
        fams.append(("D1", padd(R, T.Phi2,
                                pscal(R, R["pi_pow"](m0 + dm), u))))
    got = 0
    for delta in range(1, 4*T.E2 + 2):
        if got >= 4: break
        for k in (0, 1):
            if got >= 4: break
            num = T.w2Phi2 + delta - k*T.gamma2
            if num <= 0 or num % T.e1:
                continue
            gp = num // T.e1
            s, u_ = eq12(gp, T.e0, T.h0)
            if u_ - (T.g0 - 1)*T.h0 < 0:
                continue
            Ck = T.realize1(T.rand_K1(nonzero=True), gp)
            fams.append(("D2", padd(R, T.Phi2,
                                    pmul(R, Ck, ppow(R, T.Phi1, k)))))
            got += 1
    m3 = (2*T.w2Phi2 // T.E2) + 1
    for dm in range(2):
        u = T.liftK0(T.rand_K0(nonzero=True))
        fams.append(("D3", padd(R, ppow(R, T.Phi2, 2),
                                pscal(R, R["pi_pow"](m3 + dm), u))))
    das = []
    for delta in (1, 3):
        g0d = T.w2Phi2 + delta
        m = 0
        if g0d < C.Gamma0:
            m = (C.Gamma0 - g0d + T.E2 - 1)//T.E2
        gD = g0d + m*T.E2
        u0 = T.rand_K0(nonzero=True)
        D = pmul(R, T.liftK0(u0), C.anchor(gD))
        fams.append(("DA", padd(R, T.Phi2, D)))
        das.append((gD, u0))
    m4 = max(1, T.w2Phi2 // (2*T.E2))
    if m4*T.E2 < T.w2Phi2:
        for dm in range(2):
            u = T.liftK0(T.rand_K0(nonzero=True))
            fams.append(("D4", padd(R, T.Phi2,
                                    pscal(R, R["pi_pow"](m4), u))))
    return fams, das

# ----------------------------------- main --------------------------------------

def main():
    t0 = time.time()
    random.seed(20260816)
    sys.path.insert(0, os.path.expanduser(
        '~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari(); pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        print(f"WARNING: cypari2 unavailable ({exc}); T11 leg skipped")
    sites, records, meters = [], [], []
    da_checks = 0
    for kind, p in CONFIGS:
        for tag, d0, r0, r1 in ROWS:
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}")
            # P0 CERT
            gv0 = len(G.VIOL)
            G.T1_T2(T, nf=6)
            G.T5(T)
            if pari is not None:
                G.T11(T, pari)
            note("P0", 0)
            if len(G.VIOL) > gv0:
                for v in G.VIOL[gv0:]:
                    viol("P0", T.tag, f"CERT {v[0]}: {v[2]}")
            C = Composite(T)
            fams, das = build_families(T, C)
            pool = []
            dai = 0
            for fam, f in fams:
                if fam != "D4":
                    side, mu1, online, d1, gamma = node1_site(T, f, fam, sites)
                    rec = terminal_site(T, C, f, fam, mu1, records, pool)
                    if fam in ("D1", "D2"):
                        pool_node1_classes(T, C, d1, online, pool)
                    if fam == "DA" and rec and rec.get("case") == "TIE-AUG":
                        gD, u0 = das[dai]; dai += 1
                        want = C.K2["embed"](T.K1["embed"](u0))
                        kapname = rec.get("kappa0")
                        note("P7"); da_checks += 1
                        got = None
                        # recompute kappa directly for the exact comparison
                        d2f = dev(T.R, f, T.Phi2)
                        kap, _, _ = kappa_of(C, d2f[0], T.w2(d2f[0]))
                        if kap != want:
                            viol("P7", T.tag,
                                 f"DA anchor coordinate {kapname} != u0 class")
                else:
                    d1, vals, gg = T.w2_data(f)
                    mu1 = None
                    terminal_site(T, C, f, fam, 0, records, pool)
            m, npairs = run_pairs(T, C, pool)
            meters.append(dict(tower=T.tag, nontriv_pairs=m, pairs=npairs,
                               pool=len(pool)))
        print(f"[{time.time()-t0:6.1f}s] ring ({kind},p={p}) done: "
              f"cumulative violations = {len(VIOL)}")
    # --------------------------------- report ---------------------------------
    print()
    print("=" * 78)
    print("PREREGISTERED vs OBSERVED (violations; samples in parens)")
    print("=" * 78)
    fams_tbl = [
        ("P0", "CERT (T1/T2/T5/T11+PARI) on used instances  [SEALED]", 0),
        ("P1", "MacLane/K1 commutation at the terminal key  [SEALED]", 0),
        ("P4n", "pooled run classes nonzero (val, kappa)    [SEALED]", 0),
        ("P2", "terminal case census (D0 KEY-ONLY; D1/D2/DA TIE-AUG)", 0),
        ("P3a", "side-endpoint support == on-line set                ", 0),
        ("P3b", "stage-scale support == {top vertex} (FLAT and MID)  ", 0),
        ("P5", "node-1 pattern tie (psi1 exact; D3 mu=2,width=2g1)   ", 0),
        ("P6", "seam legs: width / window / steep                    ", 0),
        ("P4", "ITER-LAW on run-realized classes (S3 carrier)        ", 0),
        ("P7", "DA terminal digit == anchor coordinate (u0 class)    ", 0),
    ]
    all_green = True
    for fam, desc, pred in fams_tbl:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == pred else "RED"
        if verdict == "RED": all_green = False
        print(f"{fam:3} {desc:57} pred {pred}  obs {obs:4d} ({n:5d})  {verdict}")
    # P3c meter
    nsites = len(sites)
    ndiff = sum(1 for s in sites if s["as_written_differs"])
    p3c = "MATCH" if ndiff == nsites and nsites > 0 else "MISMATCH"
    if p3c == "MISMATCH": all_green = False
    print(f"P3c AS-WRITTEN METER: S(FLAT) != S(side) at {ndiff}/{nsites} deep "
          f"node-1 sites (pred: ALL)  {p3c}")
    # P2 census table
    print("-" * 78)
    cases = {}
    for r in records:
        key = (r["fam"], r.get("case"))
        cases[key] = cases.get(key, 0) + 1
    print("P2 TERMINAL CASE CENSUS:", dict(sorted(cases.items())))
    tie_reprs = sorted({(r["tower"], r["fam"], str(r.get("kappa0")),
                         r.get("gB_mod_E2"))
                        for r in records if r.get("case") == "TIE-AUG"
                        and "kappa0" in r})
    print(f"  TIE-AUG terminal digit coordinates measured: "
          f"{len(tie_reprs)} distinct (tower,fam,kappa0,gB mod E2) rows")
    for row in tie_reprs[:12]:
        print("   ", row)
    print("-" * 78)
    print("P4 ITER-LAW METERS (nontrivial-c pairs / sampled pairs / pool):")
    agg = {}
    for m in meters:
        k = m["tower"].split(",")[-1]
        a = agg.setdefault(k, [0, 0])
        a[0] += m["nontriv_pairs"]; a[1] += m["pairs"]
    for k in sorted(agg):
        print(f"   row {k}: {agg[k][0]}/{agg[k][1]} pairs with c != 1")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 30):")
        for v in VIOL[:30]:
            print("  ", v)
    print(f"TOTAL samples {sum(COUNTS.values())}  elapsed {time.time()-t0:.1f}s")
    verdict = all_green and not VIOL
    print(f"VERDICT (preregistered rows): "
          f"{'ALL GREEN' if verdict else 'RED — see above'}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "juncforge_stage1_results.json"), "w") as fh:
        json.dump(dict(violations=[list(v) for v in VIOL], counts=COUNTS,
                       sites=sites, records=records, meters=meters,
                       p3c=dict(differs=ndiff, sites=nsites)),
                  fh, indent=1, default=str)
    return 0 if verdict else 1

if __name__ == "__main__":
    sys.exit(main())
