#!/usr/bin/env python3
"""tr3s1_check.py — the TR3-S1 preregistered falsifier family (2026-08-08).

UNIT UNDER TEST: lean/notes/openmath/TR3S1_2026-08-08.md — the assembled
coefficient agreement for the marched order-2 read on the unramified-below
stratum (state order 2, e0 = 1): sigma-coefficientwise,

    R^FGMN_{2,gamma}(f) = y^{j0} * R_lambda^{GMN-conv}(f)   and
    R^FGMN_2(f)         =        R_lambda^{GMN-conv}(f),

per-argument units == 1, for EVERY nonzero f in scope (not just the T9
instance family). The FGMN side is the N-1 harness's reading-C operator
(grb_order2_check.Tower.R2w/R2s — Def 3.16/3.18 + corrected Def 3.15 in
integer weights via RESCALE). The GMN side is computed INDEPENDENTLY below
from GMN Defs 1.6/1.9 (order 1) + (18)/Defs 2.19-2.21 (order 2), with its
own polygon/on-line/initial-abscissa arithmetic (no reuse of the FGMN
metadata beyond the shared tower object and base-ring helpers).

CONVENTIONS PINNED (note S1/S2): GMN level-1 data at r = 2 are the first
read's (e1,h1,l1)^GMN = (e0,h0,l0)^proj = (1,h0,0) — the Bezout
representative NORMALIZED to 0 <= l < e (GMN print only "fixed integers"
with l*h - l'*e = 1; the project's standing GMN-convention operator takes
the normalized choice, which at e = 1 forces l = 0, t1(i) = s1(a_i)).
sigma_1 is the identity in this concrete model: the harness realizes both
papers' residue towers in the SAME K1 = K0[z]/(psi0) with z1 = zbar = K1["z"]
— the note's sigma-construction content is exactly that this identification
is the lawful one; the family tests the coefficient identity in that model.

WHY A NEW FAMILY (beyond T9/T2): T9 samples one instance shape — three
consecutive on-line slots, s(gamma) = 0, digits built by realize1 (every
digit exactly on-line, no above-line noise). The TR3-S1 statement is
UNIVERSAL over nonzero f. This family feeds ARBITRARY f: random polynomials
of any degree, structured multi-slot mixtures, Phi1^a*g corners (s0 > 0,
j0 > 0), constants and pi-powers, pi^k*f weight shifts, Phi2-multiples
(slope -infty side present), and f = Phi2 itself (the clause-(3) label tie:
both side reads == psi1).

================ PREREGISTERED PREDICTIONS (exact arithmetic) =============
Towers: the e0 = 1 roster rows A, B, F, G, I of grb_order2_check (the
stratum), over all four base rings {Z_2, Z_3, F_2[[t]], F_3[[t]]}.
Reading: C only (the corrected Def 3.15; pinned by T0/P3/P12 of N-1).
seed: 20260812 (fresh; independent of N-1's 20260808).

TS1a  per-abscissa coefficient agreement: for EVERY abscissa i of the
      lambda2-component range [s, s'] with i == s mod e1 (and every FGMN
      slot j with abscissa s_j in range), sigma(C^F_j) == c^G_{s_j}, with
      c^G computed independently (Defs 2.19-2.21, t1 = s1(a_i)); support
      match: nonzero exactly on the independently computed on-line set.
      PREDICTED: 0 violations. A violation falsifies TR3-S1 clause (c).
TS1b  side-read alignment: FGMN R2s(f) == the GMN list
      [c_s, c_{s+e1}, ..., c_{s+d*e1}] EXACTLY (same length d+1, nonzero
      ends), and j0_FGMN == (s - s(gamma))/e1 == floor(s/e1).
      PREDICTED: 0 violations. Falsifies the two-form corollary.
TS1c  the label tie at f = Phi2: both side reads == psi1 exactly.
      PREDICTED: 0 violations (one check per tower). Falsifies the
      TR-3-ORD-X label-tie corollary (note S6).
TS1d  twist audit: eps1(gamma_j) == 1 at every on-line slot encountered
      (the stratum's twist triviality, note S4). PREDICTED: 0 violations.
==========================================================================

AMENDMENT (2026-08-08, pass-1 gap-4 fold; note REVISION 2). (i) The
independence claim is scoped exactly in the note's S8.2: the GMN side shares
the Tower object (base rings, Phi0/Phi1/Phi2, residue fields) and w0/w1
consumed as v1/v2, and hard-codes the normalized l1 = 0 (t1 = s1) — those
shared inputs are covered by the N-1 external legs (T11/P11/P12 PARI + T0),
not by this family. (ii) TS1b STRENGTHENED: the side-read comparison is now
raw-list equality (no fp_norm masking) + length == d+1 + nonzero ends, so a
spurious trailing-zero R2s output can no longer pass. Predictions unchanged
(still 0); re-run after the amendment: still 0 violations.
"""
import random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import grb_order2_check as G
from grb_order2_check import (dev, w0, pnorm, padd, pmul, ppow, pscal,
                              fp_norm, fp_mul, eq12, INF, Tower)

VIOL = []
COUNTS = {}
def note(fam, n=1): COUNTS[fam] = COUNTS.get(fam, 0) + n
def viol(fam, tag, detail): VIOL.append((fam, tag, detail))

# ----------------- the INDEPENDENT GMN side (order 1 then order 2) ---------
def gmn_order1(T, a):
    """GMN Defs 1.6/1.9 for a nonzero digit a (deg a < deg Phi1), first-read
    data (e,h) = (e0,h0) = (1,h0): returns (s1, clist) with s1 = initial
    abscissa of the lambda1-component of N1(a), clist = the residual-poly
    coefficients [c_{s1}, c_{s1+1}, ..., c_{s1+d}] as K0 elements
    (c_i = red(b_i/pi^{u_i}) on the component line, 0 strictly above)."""
    R = T.R
    d0v = dev(R, a, T.Phi0)
    um = [w0(R, b) if b else INF for b in d0v]
    # lambda1-line value: min over m of u_m + m*h0  (slope -h0, e0 = 1)
    line = min(um[m] + m*T.h0 for m in range(len(d0v)) if um[m] < INF)
    on = [m for m in range(len(d0v)) if um[m] < INF and um[m] + m*T.h0 == line]
    s1, sp1 = min(on), max(on)
    clist = []
    for m in range(s1, sp1 + 1):                    # stride e0 = 1
        if um[m] < INF and um[m] + m*T.h0 == line:
            clist.append(T.res_digit(d0v[m], um[m]))
        else:
            clist.append(tuple([0]*T.d0))           # strictly above the line
    return s1, clist

def gmn_order2(T, f):
    """GMN (18) + Defs 2.19-2.21 at r = 2, independently: returns
    (s, d, coeffs, online) with coeffs = [c_s, c_{s+e1}, ..., c_{s+d*e1}]
    in K1, online = the set of on-line abscissas."""
    R, K1 = T.R, T.K1
    d1 = dev(R, f, T.Phi1)
    # u_i = v2(a_i phi2^i) = w1(a_i) + i*w1(Phi1)   [v2 = w1, v2(phi2) = w1Phi1]
    u = [ (T.w1(a) + i*T.w1Phi1) if a else INF for i, a in enumerate(d1) ]
    # lambda2-component: minimizers of e1*u_i + i*h1 (slope -h1/e1)
    vals = [ (T.e1*u[i] + i*T.h1) if u[i] < INF else INF for i in range(len(d1)) ]
    m = min(v for v in vals if v < INF)
    on = [i for i in range(len(d1)) if vals[i] == m]
    s, sp = min(on), max(on)
    assert (sp - s) % T.e1 == 0, "component endpoints not e1-congruent"
    d = (sp - s)//T.e1
    coeffs = []
    for k in range(d + 1):
        i = s + k*T.e1
        ai = d1[i] if i < len(d1) else []
        if (not ai) or vals[i] != m:
            coeffs.append(K1["zero"])               # strictly above N
            continue
        s1, clist = gmn_order1(T, ai)
        # t1(i) = (s1(a_i) - l1*u_i)/e1 with (e1,l1)^GMN = (1,0):  t1 = s1
        val = K1["zero"]; zp = K1["pow"](T.z1, s1)
        for c in clist:
            if any(c):
                val = K1["add"](val, K1["mul"](K1["embed"](c), zp))
            zp = K1["mul"](zp, T.z1)
        coeffs.append(val)
    return s, d, coeffs, set(on)

# ------------------------------- the family --------------------------------
def ts1_compare(T, f, shape):
    K1 = T.K1
    note("TS1a")
    coeffs, meta = T.R2w(f, with_meta=True)
    gamma = meta["gamma"]
    s2, _ = eq12(gamma, T.e1, T.h1)
    if s2 != meta["s2"]:
        viol("TS1a", T.tag, f"[{shape}] s(gamma) mismatch vs eq12")
    s, d, gco, on = gmn_order2(T, f)
    # support + per-abscissa agreement over the union of both ranges
    jmax = max(len(coeffs) - 1, (s + d*T.e1 - s2)//T.e1)
    for j in range(jmax + 1):
        sj = s2 + j*T.e1
        CF = coeffs[j] if j < len(coeffs) else K1["zero"]
        if s <= sj <= s + d*T.e1 and (sj - s) % T.e1 == 0:
            cG = gco[(sj - s)//T.e1]
        else:
            cG = K1["zero"]                          # outside the component
        if CF != cG:
            viol("TS1a", T.tag,
                 f"[{shape}] coeff mismatch at abscissa {sj} (slot {j})")
            return
        nz = not K1["isz"](CF)
        if nz != (sj in on):
            viol("TS1a", T.tag,
                 f"[{shape}] support mismatch at abscissa {sj}: "
                 f"nonzero={nz}, on-line={sj in on}")
            return
    # TS1d: the twist is 1 at every on-line slot
    note("TS1d")
    for j, is_on in enumerate(meta["online"]):
        if is_on:
            gj = (gamma - (s2 + j*T.e1)*T.gamma2)//T.e1
            if T.eps1(gj) != K1["one"]:
                viol("TS1d", T.tag, f"[{shape}] eps1 != 1 at slot {j}")
                return
    # TS1b: side-read alignment (raw lists — no fp_norm masking; REV-2 form)
    note("TS1b")
    side, j0, _ = T.R2s(f)
    if list(side) != list(gco):
        viol("TS1b", T.tag, f"[{shape}] R2(f) != GMN R_lambda(f) raw list")
        return
    if len(side) != d + 1 or K1["isz"](side[0]) or K1["isz"](side[-1]):
        viol("TS1b", T.tag, f"[{shape}] length/{'ends'}: len={len(side)} "
                            f"!= d+1={d+1} or zero end")
        return
    if j0 != (s - s2)//T.e1 or j0 != s//T.e1:
        viol("TS1b", T.tag, f"[{shape}] j0={j0} != (s-s2)/e1={(s-s2)//T.e1} "
                            f"or floor(s/e1)={s//T.e1}")

def run_tower(T, nf=40):
    R = T.R
    # (a) arbitrary random polynomials
    for _ in range(nf):
        f = T.rand_opoly(random.randrange(0, int(2.2*T.degPhi2) + 1), pimax=5)
        if not f: f = [R["pi_pow"](random.randrange(0, 4))]
        ts1_compare(T, f, "rand")
    # (b) structured multi-slot mixtures
    for _ in range(nf//2):
        ts1_compare(T, T.rand_structured(random.choice([2, 3, 4])), "struct")
    # (c) Phi1^a * g corners (s0 > 0, j0 > 0)
    for _ in range(nf//2):
        a = random.randrange(1, 2*T.e1 + 2)
        g = T.rand_opoly(random.randrange(0, T.degPhi1 + 2), pimax=3)
        if not g: g = [R["one"]]
        ts1_compare(T, pmul(R, ppow(R, T.Phi1, a), g), f"Phi1^{a}*g")
    # (d) constants and pi-powers; pi^k * f weight shifts
    for k in range(0, 4):
        ts1_compare(T, [R["pi_pow"](k)], f"pi^{k}")
    for _ in range(nf//4):
        f = T.rand_structured(2)
        k = random.randrange(1, 4)
        ts1_compare(T, pscal(R, R["pi_pow"](k), f), "pi^k*struct")
    # (e) Phi2-multiples (slope -infty side present at order-2 read? no —
    #     the -infty side belongs to the Phi1-development only via zero
    #     digits; Phi2^mu*Q exercises high ord_{psi1} residues)
    for _ in range(nf//4):
        mu = random.choice([1, 2])
        Q = T.rand_structured(2)
        ts1_compare(T, pmul(R, ppow(R, T.Phi2, mu), Q), f"Phi2^{mu}*Q")
    # (f) the label tie f = Phi2 (TS1c)
    note("TS1c")
    sideF, j0F, _ = T.R2s(T.Phi2)
    sF, dF, gcoF, _ = gmn_order2(T, T.Phi2)
    psi1 = fp_norm(T.K1, T.psi1)
    if sideF != psi1 or fp_norm(T.K1, gcoF) != psi1 or j0F != 0 or sF != 0:
        viol("TS1c", T.tag, "label tie: side reads != psi1 exactly")

def main():
    random.seed(20260812)
    ROSTER = [row for row in G.ROSTER if row[2][0] == 1]   # e0 = 1 stratum
    assert [r[0] for r in ROSTER] == ["A", "B", "F", "G", "I"]
    for kind, p in [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]:
        for tag, d0, r0, r1 in ROSTER:
            T = Tower(kind, p, d0, r0, r1, f"{kind},p={p},{tag}", mode="C")
            run_tower(T, nf=40)
        print(f"ring ({kind}, p={p}) done: cumulative violations = {len(VIOL)}")
    print("=" * 74)
    print("TR3-S1 PREREGISTERED vs OBSERVED (violation counts; samples in parens)")
    fams = [("TS1a", "per-abscissa coefficient + support agreement", 0),
            ("TS1b", "side-read alignment R2 == R_lambda list + j0", 0),
            ("TS1c", "label tie at f = Phi2 (both == psi1)",         0),
            ("TS1d", "eps1 == 1 at every on-line slot",              0)]
    ok = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        verdict = "GREEN" if obs == pred else "RED"
        if obs != pred: ok = False
        print(f"{fam:5} {desc:47} pred {pred}  obs {obs:4d} ({n:5d})  {verdict}")
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 20):")
        for v in VIOL[:20]: print("  ", v)
    print(f"TOTAL samples: {sum(COUNTS.values())}")
    print(f"VERDICT: {'ALL GREEN' if ok and not VIOL else 'RED'}")
    return 0 if (ok and not VIOL) else 1

if __name__ == "__main__":
    sys.exit(main())
