#!/usr/bin/env python3
"""grb_order2_check.py — N-1: the blueprint falsifier harness for the (GR-B) order-2
leaf (GRB_ORDER2_2026-08-05.md), per HDISCHARGE_H1.md section 5.4.

EXACT ORDER-2 TOWERS over the four base rings O in {Z_2, Z_3, F_2[[t]], F_3[[t]]},
root-key degree d0 in {1, 2}: genuine two-read MacLane towers
    (Phi_0, w_0) --(e0,h0,psi0)--> (Phi_1, w_1) --(e1,h1,psi1)--> w_2,
with the state key Phi_2 = the canonical (twist-corrected) lift of psi1, and the
FGMN residual operators R_{2,gamma} (Def 3.16) / R_2 (Def 3.18) transcribed from the
printed formulas in integer weights via Lemma RESCALE (leaf S2.1): the eq-(12)
integral form u*e_i + s*h_i = gamma (S5.2 (12-int)), the twist units
eps_1(beta) = z1^(l0*s(beta) - l0p*u(beta)) (Def 3.15), eps_0 == 1.

Extends gd23_check.py (whose machinery for O, O[x], developments, std level-1 lift
is reused nearly verbatim) to the queued perimeter: state order 2, both sides of
each dictionary claim computed exactly, violations counted. NOT duplicated here:
G1/G2 of grb_order2_gate.py (pure carry arithmetic; single symbolic depth-2
instance) and gd23_check's order-1 families — N-1's marginal value is real order-2
towers over all four rings.

DETERMINISTIC: random.seed(20260808). EXACT arithmetic only: Z coefficients for
Z_p; exact finite F_p[t] tuples for F_p[[t]] (all operations polynomial, no
truncation ever needed); finite-field towers K0 = F_p[X]/(phibar), K1 = K0[z]/(psi0)
as exact quotient rings. No floats anywhere.

================================ TOWER ROSTER =================================
Per base ring, 10 towers (d0; e0,h0,g0; e1,h1,g1) — covering d0 in {1,2}, the
e0 = 1 stratum (S3.2's TR-3 scope), stacked ramification E_2 = 4, g0 = 2 residue
growth, and the e1*g1 = 1 refinement state reads (the e*g = 1 corner):
  A (1; 1,1,1; 2,1,1)   B (1; 1,2,2; 3,2,1)   C (1; 2,1,1; 2,1,1)
  D (1; 2,3,1; 1,1,2)   E (1; 3,1,1; 2,3,1)   F (1; 1,1,1; 1,1,1)  <- e1*g1 = 1
  G (2; 1,1,1; 2,1,1)   H (2; 2,1,1; 1,1,1)   I (2; 1,1,2; 2,3,1)  <- H: e1*g1 = 1
  J (2; 2,1,2; 2,1,1)   (deg Phi_2 up to 16)

========================= PREREGISTERED PREDICTIONS ===========================
(counts are VIOLATION counts; sample counts printed at run time; any test family
whose observed count differs from its prediction is RED)

T1  A-LAW-2 + slope dictionary + VAL-2:  w2(f) = e1*(polygon ordinate at s0)
    + s0*h1; realized face slope == h1/e1 == E1*(h1/E2) as exact rationals
    (TR-1-corr: lambda^GMN = -E_i * lambda_r^FGMN); s0 == s(gamma) mod e1
    ((12-int) consistency); w2(f*g) = w2(f)+w2(g).
    PREDICTED: 0 violations. A violation falsifies the leaf's TR-1/TR-5/S5.2
    (12-int) displays (and TR-2's rescaling application).
T2  (2') two-form / support (Cor 4.4(2)(3)(4) retarget): R_{2,gamma}(f) support
    exactly at the on-line slots; lowest index j0 == floor(s0(f)/e1) (so
    R_{2,gamma} = y^j0 * R_2, discrepancy exactly ybar^j0); R_2 constant term != 0;
    top degree == j0 + d (polygon face length / e1).
    PREDICTED: 0. A violation falsifies (GR-B-STR)(2')'s two-form display (S6.2).
T3  Law (1) TOTAL multiplicativity, FGMN convention (Cor 4.7(3) pin, S6.1):
    R_2(f*g) == R_2(f) * R_2(g) exactly in K1[y] (theta == 1).
    PREDICTED: 0. A violation falsifies S6.1's re-pricing (the Cor 4.7(3) pin).
T4  (W-MULT) weight-pair carry law (S6a): R_{2,gf+gg}(f*g) ==
    y^delta * R_{2,gf}(f) * R_{2,gg}(g), delta = floor((s(gf)+s(gg))/e1) in {0,1}.
    PREDICTED: 0. A violation falsifies S6a's (W-MULT) = CARRY-1's graded
    realization (OP-A2/OP-A4).
T5  Key lift + clause (3) (Cor 5.6(2) pin, S6.3): the canonical lift Phi_2 is
    monic of degree e1*g1*deg(Phi_1); every term of w2-weight e1*g1*gamma_2
    (one-sided polygon); w2(Phi_2) = e1*g1*gamma_2; R_2(Phi_2) == psi1 EXACTLY;
    (level-1 re-asserts: w1(Phi_1) = e0*g0*h0, terms homogeneous).
    PREDICTED: 0. A violation falsifies clause (3)'s retarget or the S5.2
    anchor-exponent arithmetic the lift rides.
T6  (d2) block at the j=1 (state) key: ord_{psi1}(R_2(B)) == 0 for random
    nonzero B with deg B < deg Phi_2.
    PREDICTED: 0. A violation falsifies the (d1)/(d2) = (KPa)+(KPirr) block
    (H1 blueprint section 4.1) at order-2 sites.
T7  GUARDED (4)/(d3) ord tie at realized sites: f = Phi_2^mu * Q + high noise;
    first-attainment index in the Phi_2-development (the graded side
    ord_{psihat}(in f), GD3-MIN's displayed computation) == ord_{psi1}(R_2(f));
    plus DEVID-2: min_k(w2(C_k) + k*w2(Phi_2)) == w2(f).
    PREDICTED: 0. A violation falsifies Cor 5.15's retarget = law (4) at
    recorded sites (S6.4).
T8  TOTAL-form faithfulness (H1-U14's gate): the same tie for ARBITRARY nonzero
    f — random polynomials of any shape, plus injected Phi_1^a * g corners
    (s(f) > 0: f NOT mu-proper — the improper-key-adjacent corner Lemma 5.13's
    proof excludes), plus constants and low-degree f, ON ALL TOWERS including
    the e1*g1 = 1 refinement towers.
    PREDICTED: UNKNOWN — preregistered per the blueprint ("0 violations on every
    clause EXCEPT possibly the total form — that is what the gate decides").
    The printed Cor 5.15 (unconditional in g, proper phi — our state keys are
    always proper, deg Phi_2 = e1*g1*m_r) implies 0. OBSERVED == 0 => U14 may be
    stated; OBSERVED > 0 => U14 CLOSED-NEGATIVE with the failing instance below.
T9  TR-3 twist dictionary, S3.2's claimed scope (the e0 = 1 stratum, general
    h0, d0, g0, (e1,h1,g1)): per on-line slot j,
      (i)  pre-eps assembled agreement (S3.1 REV-5): z1^(t1(s_j)) *
           R1^GMN-side(a_{s_j})(z1) == the inner FGMN coefficient (before eps_1);
      (ii) ratio C^F_j / c^G_j == z1^(-gamma_j) exactly;
      (iii) the weight-geometric law ratio(j+1) == ratio(j) * z1^(gamma_2).
    PREDICTED (ORIGINAL, wave-0 — inherited the leaf's eps reading; SUPERSEDED
    by the AMENDMENT below): 0 violations of (i)-(iii).
    A violation of (i)-(iii) falsifies S3.2's displayed law / S3.1's REV-5 row.
T10 D-REAL / eq (14) s-walk (the single-wrap law x^e1 = ybar*p^h1 realized):
    R_{2,gamma}(Phi_1^s) == y^floor(s/e1) and R_2(Phi_1^s) == 1, s = 0..2*e1+1.
    PREDICTED: 0. A violation falsifies S5.3's D-REAL generator/wrap
    identification at the decided (last) read.
T11 PARI ORACLE (independent; Z_p towers only): Phi_2 has Z coefficients; PARI
    factorpadic says Phi_2 irreducible over Q_p, and idealprimedec on the global
    field Q[x]/(Phi_2) (nfinit maximal at p) gives a UNIQUE prime above p with
    (e, f) == (e0*e1, d0*g0*g1).
    PREDICTED: 0 mismatches on all 20 Z_p towers. A mismatch means the
    constructed tower is NOT the OM data it claims (harness/tower bug) or a
    genuine key-lift-theory failure.
    HONEST DEFERRAL (displayed): no PARI analogue is run for F_p[[t]] (PARI has
    no equal-characteristic local factorization entry point here); the F_p[[t]]
    towers are cross-checked only internally (T1-T10).

Runtime budget: sized to < 20 min (sample counts per tower in main()).

=================== AMENDMENT (2026-08-08, PRE-FULL-RUN) =====================
The build-phase smoke run (tower rosters at reduced counts, seed 1) produced
T3/T4/T7 violations concentrated EXACTLY on the e0 >= 2, z1 != 1 towers, e.g.:
    O = Z_3, d0 = 1, reads (2,1,y+1),(2,1): f ~ 2*3^9*x*Phi1 (single on-line
    slot): R_2(f) = [1], R_2(f)^2 = [1], but R_2(f^2) = [2]  — Cor 4.7(3),
    FGMN's own printed theorem, violated by the harness operator.
Diagnosis (hand graded-ring computation, recorded here; x^2 = -3bar in
gr(w_2) forces the coefficient of f^2 to be 1bar, not 2bar): the harness's
eps_1 = z1^(l0*s - l0p*u) — transcribed from the leaf's S3.1 quote of
Def 3.15, itself from the pdftotext extraction — is NOT FGMN's twist.  In the
PDF the prime is a FLOATING GLYPH that pdftotext attaches to the wrong ell.
Three independent pins fix the true exponent as l0p*s(beta) - l0*u(beta):
  (pin 1) FGMN's own remark under Def 3.15: "For i = 0, we get eps_0(alpha) =
      (z0)^0 for all alpha" — with (e0,h0)^F = (1,0), (l,l') = (0,1) the
      garbled reading gives z0^(-alpha), the corrected reading gives z0^0
      verbatim;
  (pin 2) Lemma 4.3's proof algebra (fgmn.txt:1478-1489): the displayed chain
      (Phi)^sbar (pi)^ubar (gamma)^(l*ubar - l'*sbar) = ... = pi_i^(h*sbar+e*ubar)
      is an identity ONLY with the gamma-exponent l*ubar - l'*sbar (checked
      symbolically in family T0 below), and threading it through eq (17)/(19)
      of Thm 4.2's proof yields eps_{i-1}(alpha_j) = z^(l'*s(alpha_j) -
      l*u(alpha_j)) exactly;
  (pin 3) the graded-ring hand instance above (and its automation, families
      P3/P11): only the corrected reading is consistent with Thm 4.2/Cor 4.7.
CONSEQUENCE FOR THE LEAF (the headline finding of this run): S3.1's quoted
eps display, S3.2's computed "weight-geometric discrepancy law"
ratio(j+1) = ratio(j)*z1^(gamma_2), gate G2's FGMN side, and TR-3'-GEN's
"exact shape displayed" all inherit the garbled prime.  Under the corrected
eps, at e0 = 1 one has l0 = 0 and s == 0, so eps_1 == 1 IDENTICALLY: the
FGMN weight coefficient and the GMN coefficient AGREE ON THE NOSE at the
S3.2 instance (ratio == 1, constant).  S3.2's refutation-of-collapse at that
instance is an artifact; the two printed operators coincide there.

AMENDED PREREGISTRATION (before the full run; the full battery runs under the
proof-derived reading "C"; a focused demonstration family runs under the
leaf's reading "P"):
T0   Lemma-4.3 exponent algebra, symbolic: for all 1<=e<=12, gcd(h,e)=1,
     h<=25, and gamma in [-60,60]: sbar+e*(l*ubar-l'*sbar) == l*(h*sbar+e*ubar)
     and ubar-h*(l*ubar-l'*sbar) == l'*(h*sbar+e*ubar).  PREDICTED: 0
     violations (this pins reading C mechanically).
T1-T8, T10, T11 (reading C): predictions AS IN THE ORIGINAL TABLE (T8 stays
     UNKNOWN/gate-deciding).
T9 (reading C, e0 = 1 stratum), REVISED: (i) pre-eps agreement 0 violations;
     (ii-C) ratio C^F_j / c^G_j == 1 at EVERY slot (the two operators agree;
     naive collapse HOLDS at e0 = 1) — 0 violations; (iii-C) the S3.2 law
     ratio(j+1) = ratio(j)*z1^(gamma_2) FAILS in every sample on towers with
     z1^gamma_2 != 1 (counted as s32_refuted, prediction: = sample count on
     those towers), i.e. the leaf's displayed law is refuted against the
     true operator.
P3   (reading P demo): Cor 4.7(3) multiplicativity under the leaf's eps on
     the e0 >= 2 towers C/D/E/H/J: PREDICTED > 0 violations total, with >= 1
     on (Z_3, tower C) (the recorded instance genre); 0 violations on towers
     with z1 = 1 (the twist is invisible there).  (At e0 = 1 reading P is a
     CHARACTER twist z1^(-gamma) of reading C, so it passes every internal
     law — which is exactly why gate G2 could not catch it; the e0 >= 2
     carry breaks the character property.)
P9   (reading P demo): S3.2's geometric law under the leaf's eps at e0 = 1
     towers: PREDICTED 0 violations (the law is internally consistent for
     reading P — it is a statement ABOUT reading P, as gate G2 already
     showed; this locates the leaf defect at the eps quote, not in G2's
     arithmetic).
P11  (discriminating PARI family, Z_p towers with e0 >= 2): the reading-P
     canonical lift Phi2^P differs from the reading-C lift by per-slot unit
     twists; under reading-C-as-truth its residual is the twisted polynomial
     psi1_twist(y) = sum_k (epsC/epsP)(gamma'_k) psi1_k y^k, and Phi2^P is
     irreducible over Q_p iff psi1_twist is a power of a single irreducible
     over K1 (Lemma 5.3 + OM factorization).  The harness computes that
     verdict exactly and PARI factorpadic independently decides
     irreducibility.  PREDICTED: 0 mismatches harness-vs-PARI — and any
     tower where psi1_twist is genuinely reducible AND PARI confirms
     reducibility is a machine refutation of reading P (under reading P the
     lift would be a key polynomial, hence irreducible).
P12  (kill-shot search): the roster's P11 instances can be twist-blind (small
     residue-field orders kill the exponent difference), so search the Z_p
     e0 >= 2, g1 = 2 perimeter for (tower, psi1) with psi1 irreducible but
     psi1_twist SPLIT (two distinct roots), and give PARI both lifts:
     PREDICTED per found instance: P-lift factors over Q_p (PARI reducible),
     C-lift irreducible — [False, True]; 0 prediction mismatches.  This is
     the fully external, oracle-decided discrimination between the two
     readings of Def 3.15.
"""
import random, math, sys, os, time
from fractions import Fraction

random.seed(20260808)
INF = 10**9
VIOL = []          # (family, tower_tag, detail)
COUNTS = {}        # family -> samples run

def note(fam, n=1):
    COUNTS[fam] = COUNTS.get(fam, 0) + n

def viol(fam, tag, detail):
    VIOL.append((fam, tag, detail))

# ======================= base rings O (from gd23_check) =======================
def _vp(n, p):
    v = 0; n = abs(n)
    while n % p == 0: n //= p; v += 1
    return v

def mk_ring(kind, p):
    if kind == "Zp":
        return dict(kind=kind, p=p, zero=0, one=1,
            add=lambda a,b: a+b, neg=lambda a: -a, mul=lambda a,b: a*b,
            isz=lambda a: a == 0,
            val=lambda a: INF if a == 0 else _vp(a, p),
            divpi=lambda a,k: a // (p**k),
            pi_pow=lambda k: p**k,
            res=lambda a: a % p)
    else:  # Fpt: exact F_p[t] tuples (coefficient of t^i)
        def norm(t):
            t = [x % p for x in t]
            while t and t[-1] == 0: t.pop()
            return tuple(t)
        def add(a,b):
            n = max(len(a), len(b))
            return norm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                         for i in range(n)])
        def mul(a,b):
            if not a or not b: return ()
            out = [0]*(len(a)+len(b)-1)
            for i,x in enumerate(a):
                if x % p == 0: continue
                for j,y in enumerate(b):
                    out[i+j] += x*y
            return norm(out)
        return dict(kind=kind, p=p, zero=(), one=(1,),
            add=add, neg=lambda a: tuple((-x) % p for x in a), mul=mul,
            isz=lambda a: len(a) == 0 or all(x % p == 0 for x in a),
            val=lambda a: INF if all(x % p == 0 for x in a) or not a
                          else min(i for i,x in enumerate(a) if x % p != 0),
            divpi=lambda a,k: tuple(a[k:]),
            pi_pow=lambda k: tuple([0]*k + [1]),
            res=lambda a: (a[0] % p) if a else 0)

# ============================ O[x] polynomials ================================
def pnorm(R, A):
    A = list(A)
    while A and R["isz"](A[-1]): A.pop()
    return A
def padd(R, A, B):
    n = max(len(A), len(B))
    return pnorm(R, [R["add"](A[i] if i < len(A) else R["zero"],
                              B[i] if i < len(B) else R["zero"]) for i in range(n)])
def pneg(R, A): return [R["neg"](a) for a in A]
def pmul(R, A, B):
    if not A or not B: return []
    out = [R["zero"]]*(len(A)+len(B)-1)
    for i,a in enumerate(A):
        if R["isz"](a): continue
        for j,b in enumerate(B):
            out[i+j] = R["add"](out[i+j], R["mul"](a,b))
    return pnorm(R, out)
def pscal(R, c, A): return pnorm(R, [R["mul"](c,a) for a in A])
def ppow(R, A, k):
    out = [R["one"]]
    for _ in range(k): out = pmul(R, out, A)
    return out
def pdivmod(R, A, B):    # B monic
    A = list(A); dB = len(B)-1; Qc = {}
    while len(A)-1 >= dB and A:
        d = len(A)-1; c = A[-1]; Qc[d-dB] = c
        for j,b in enumerate(B):
            A[d-dB+j] = R["add"](A[d-dB+j], R["neg"](R["mul"](c,b)))
        A = pnorm(R, A)
    Qd = max(Qc) if Qc else -1
    return pnorm(R, [Qc.get(i, R["zero"]) for i in range(Qd+1)]), pnorm(R, A)
def dev(R, A, Phi):
    out = []
    A = pnorm(R, list(A))
    while A:
        Q, rem = pdivmod(R, A, Phi)
        out.append(rem)
        A = Q
    return out
def w0(R, A):
    if not A: return INF
    return min(R["val"](a) for a in A)

# ==================== finite-field towers (exact quotients) ===================
# K0 = F_p[X]/(phibar): elements = tuples (len d0) of ints mod p.
# K1 = K0[z]/(psi0):   elements = tuples (len g0) of K0 elements.
def mk_field_base(p, phibar):     # phibar: list of d0+1 ints, monic
    d = len(phibar) - 1
    red = [(-phibar[i]) % p for i in range(d)]   # X^d = sum red[i] X^i
    zero = tuple([0]*d); one = tuple([1] + [0]*(d-1))
    def add(u,v): return tuple((u[i]+v[i]) % p for i in range(d))
    def neg(u):   return tuple((-u[i]) % p for i in range(d))
    def mul(u,v):
        out = [0]*(2*d-1) if d > 1 else [0]
        for i,x in enumerate(u):
            if x == 0: continue
            for j,y in enumerate(v):
                out[i+j] += x*y
        for k in range(len(out)-1, d-1, -1):     # reduce X^k
            c = out[k] % p
            if c:
                for i in range(d):
                    out[k-d+i] += c*red[i]
            out[k] = 0
        return tuple(out[i] % p for i in range(d))
    q = p**d
    F = dict(p=p, q=q, dim=d, zero=zero, one=one, add=add, neg=neg, mul=mul,
             isz=lambda u: all(x % p == 0 for x in u))
    def powf(a, n):
        n %= (q-1) if a != zero else 1
        r = one; b = a
        while n:
            if n & 1: r = mul(r, b)
            b = mul(b, b); n >>= 1
        return r
    F["pow"] = powf
    F["inv"] = lambda a: powf(a, q-2)
    F["elements"] = lambda: (tuple(c) for c in _tuples(p, d))
    return F

def _tuples(p, d):
    if d == 0:
        yield (); return
    for rest in _tuples(p, d-1):
        for c in range(p):
            yield (c,) + rest

def mk_field_ext(K, psi):         # psi: list of K-elements, monic, deg g >= 1
    g = len(psi) - 1
    red = [K["neg"](psi[i]) for i in range(g)]   # z^g = sum red[i] z^i
    zero = tuple([K["zero"]]*g); one = tuple([K["one"]] + [K["zero"]]*(g-1))
    def add(u,v): return tuple(K["add"](u[i], v[i]) for i in range(g))
    def neg(u):   return tuple(K["neg"](u[i]) for i in range(g))
    def mul(u,v):
        out = [K["zero"]]*(2*g-1) if g > 1 else [K["zero"]]
        for i,x in enumerate(u):
            if K["isz"](x): continue
            for j,y in enumerate(v):
                out[i+j] = K["add"](out[i+j], K["mul"](x,y))
        for k in range(len(out)-1, g-1, -1):
            c = out[k]
            if not K["isz"](c):
                for i in range(g):
                    out[k-g+i] = K["add"](out[k-g+i], K["mul"](c, red[i]))
            out[k] = K["zero"]
        return tuple(out[:g])
    q = K["q"]**g
    F = dict(p=K["p"], q=q, dim=K["dim"]*g, base=K, deg=g,
             zero=zero, one=one, add=add, neg=neg, mul=mul,
             isz=lambda u: all(K["isz"](x) for x in u))
    def powf(a, n):
        n %= (q-1) if not F["isz"](a) else 1
        r = one; b = a
        while n:
            if n & 1: r = mul(r, b)
            b = mul(b, b); n >>= 1
        return r
    F["pow"] = powf
    F["inv"] = lambda a: powf(a, q-2)
    # z = class of the variable
    F["z"] = tuple([K["zero"], K["one"]] + [K["zero"]]*(g-2)) if g >= 2 \
             else (red[0],)                                   # z == -psi[0], g = 1
    F["embed"] = lambda c: tuple([c] + [K["zero"]]*(g-1))     # K -> F
    return F

# ------------------------------ F[y] polynomials ------------------------------
def fp_norm(F, A):
    A = list(A)
    while A and F["isz"](A[-1]): A.pop()
    return A
def fp_add(F, A, B):
    n = max(len(A), len(B))
    return fp_norm(F, [F["add"](A[i] if i < len(A) else F["zero"],
                                B[i] if i < len(B) else F["zero"]) for i in range(n)])
def fp_mul(F, A, B):
    if not A or not B: return []
    out = [F["zero"]]*(len(A)+len(B)-1)
    for i,a in enumerate(A):
        if F["isz"](a): continue
        for j,b in enumerate(B):
            out[i+j] = F["add"](out[i+j], F["mul"](a,b))
    return fp_norm(F, out)
def fp_scal(F, c, A): return fp_norm(F, [F["mul"](c,a) for a in A])
def fp_divmod(F, A, B):   # B monic over field F
    A = list(A); dB = len(B)-1; Qc = {}
    while len(A)-1 >= dB and A:
        d = len(A)-1; c = A[-1]; Qc[d-dB] = c
        for j,b in enumerate(B):
            A[d-dB+j] = F["add"](A[d-dB+j], F["neg"](F["mul"](c,b)))
        A = fp_norm(F, A)
    Qd = max(Qc) if Qc else -1
    return fp_norm(F, [Qc.get(i, F["zero"]) for i in range(Qd+1)]), fp_norm(F, A)
def fp_ord(F, A, psi):
    mu = 0; A = fp_norm(F, A)
    while A:
        Q, rem = fp_divmod(F, A, psi)
        if rem: break
        mu += 1; A = fp_norm(F, Q)
    return mu
def fp_eval(F, A, x):
    r = F["zero"]
    for c in reversed(A):
        r = F["add"](F["mul"](r, x), c)
    return r
def fp_irreducible(F, A):   # deg <= 2 test: no root in F (deg 1 always irr)
    d = len(A)-1
    if d == 1: return True
    if d == 2:
        return all(not F["isz"](fp_eval(F, A, e)) for e in _field_elems(F))
    raise ValueError("only deg <= 2 supported")
def _field_elems(F):
    if "base" in F:
        K = F["base"]; g = F["deg"]
        def rec(i):
            if i == 0:
                yield (); return
            for rest in rec(i-1):
                for c in _field_elems(K):
                    yield (c,) + rest
        return rec(g)
    return F["elements"]()

def pick_irreducible(F, g, idx=0):
    """(idx mod #matches)-th monic irreducible of degree g over F with nonzero
    constant term, in the deterministic enumeration order of _field_elems."""
    matches = []
    if g == 1:
        for c in _field_elems(F):
            if F["isz"](c): continue
            matches.append([F["neg"](c), F["one"]])   # y - c, constant -c != 0
    else:
        for b in _field_elems(F):
            if F["isz"](b): continue                  # constant term != 0
            for a in _field_elems(F):
                cand = [b, a, F["one"]]
                if fp_irreducible(F, cand):
                    matches.append(cand)
    if not matches:
        raise RuntimeError("no irreducible found")
    return matches[idx % len(matches)]

# ========================= eq (12) integral / Bezout ==========================
def bezout(e, h):
    """l*h + lp*e = 1, 0 <= l < e (l = 0, lp = 1 at e = 1)."""
    if e == 1: return 0, 1
    l = pow(h, -1, e)
    lp = (1 - l*h) // e
    return l, lp

def eq12(gamma, e, h):
    """(12-int): u*e + s*h = gamma, 0 <= s < e."""
    if e == 1:
        return 0, gamma
    l, _ = bezout(e, h)
    s = (l * gamma) % e
    u = (gamma - s*h) // e
    assert u*e + s*h == gamma
    return s, u

# ============================== the tower object ==============================
class Tower:
    """One exact order-2 tower over O.  mode = "C" (proof-derived eps reading,
    the default and the truth per the AMENDMENT pins) or "P" (the leaf's
    printed-extraction reading, kept for the demonstration families)."""
    def __init__(self, kind, p, d0, r0, r1, tag, mode="C", psi1_override=None):
        self.kind, self.p, self.tag, self.mode = kind, p, tag, mode
        self._psi1_override = psi1_override
        self.R = mk_ring(kind, p)
        R = self.R
        self.d0 = d0
        self.e0, self.h0, self.g0 = r0
        self.e1, self.h1, self.g1 = r1
        assert math.gcd(self.e0, self.h0) == 1 and math.gcd(self.e1, self.h1) == 1
        # root key Phi0 (monic lift of irreducible phibar, t-noise in eq char)
        if d0 == 1:
            phibar = [0, 1]                       # X
            self.Phi0 = pnorm(R, [R["zero"], R["one"]])
        else:
            phibar = [1, 1, 1] if p == 2 else [1, 0, 1]   # irred over F_p
            if kind == "Zp":
                self.Phi0 = pnorm(R, [phibar[0], phibar[1], 1])
            else:
                self.Phi0 = pnorm(R, [(phibar[0] % p,), (phibar[1] % p, 1), (1,)])
        self.phibar = phibar
        self.K0 = mk_field_base(p, phibar)
        # read 0: psi0 over K0, deg g0, psi0(0) != 0  (deterministic pick; idx
        # varies with h1 to diversify)
        self.psi0 = pick_irreducible(self.K0, self.g0, idx=(self.h1) % 2)
        self.K1 = mk_field_ext(self.K0, self.psi0)
        self.z1 = self.K1["z"]
        assert not self.K1["isz"](self.z1)
        # level-1 std lift  Phi1 = sum_k lift(psi0_k) pi^{(g0-k)h0} Phi0^{e0 k}
        self.gamma1 = self.h0                     # e0*w0(Phi0) + h0, w0(Phi0)=0
        Phi1 = []
        self.lift_terms1 = []
        for k, c in enumerate(self.psi0):
            if self.K0["isz"](c): continue
            term = pscal(R, R["pi_pow"]((self.g0-k)*self.h0),
                         pmul(R, self.liftK0(c), ppow(R, self.Phi0, self.e0*k)))
            self.lift_terms1.append(term)
            Phi1 = padd(R, Phi1, term)
        self.Phi1 = Phi1
        self.degPhi1 = self.e0*self.g0*d0
        self.w1Phi1 = self.e0*self.g0*self.h0
        self.gamma2 = self.e1*self.w1Phi1 + self.h1
        self.l0, self.l0p = bezout(self.e0, self.h0)
        self.l1, self.l1p = bezout(self.e1, self.h1)
        self.E1, self.E2 = self.e0, self.e0*self.e1
        # read 1: psi1 over K1, deg g1, psi1(0) != 0
        self.psi1 = self._psi1_override if self._psi1_override is not None \
                    else pick_irreducible(self.K1, self.g1, idx=(self.h0) % 2)
        # state key Phi2 (canonical twist-corrected lift; tested in T5)
        self.Phi2 = self.build_Phi2()
        self.degPhi2 = self.e1*self.g1*self.degPhi1
        self.w2Phi2 = self.e1*self.g1*self.gamma2

    # ---- O-level lifts of residue classes ----
    def liftK0(self, c):     # K0 element (tuple of ints) -> O[x] poly deg < d0
        R = self.R
        if R["kind"] == "Zp":
            return pnorm(R, [int(x) for x in c])
        return pnorm(R, [((x % self.p),) if x % self.p else () for x in c])

    # ---- valuations ----
    def w1(self, A):
        if not A: return INF
        return min(self.e0*w0(self.R, b) + k*self.gamma1
                   for k, b in enumerate(dev(self.R, A, self.Phi0)) if b) \
               if pnorm(self.R, A) else INF
    def w2_data(self, A):
        """Phi1-development + per-slot w1 values + w2."""
        d1 = dev(self.R, A, self.Phi1)
        vals = [self.w1(c) if c else INF for c in d1]
        if all(v == INF for v in vals): return d1, vals, INF
        g = min(self.e1*vals[j] + j*self.gamma2 for j in range(len(d1))
                if vals[j] < INF)
        return d1, vals, g
    def w2(self, A):
        return self.w2_data(A)[2]

    # ---- level-1 residue of a digit: class of b/pi^delta in K0 ----
    def res_digit(self, b, delta):
        R = self.R
        out = [0]*self.d0
        for i, c in enumerate(b):
            out[i] = R["res"](R["divpi"](c, delta))
        return tuple(out)

    # ---- level-1 FGMN weight read: R_{1,beta}(a) as K0-coefficient list,
    #      and its value at z1 in K1 (eps_0 == 1; Def 3.16 at i = 1) ----
    def R1w(self, a, beta):
        d0v = dev(self.R, a, self.Phi0)
        s, u = eq12(beta, self.e0, self.h0)
        out = []
        m = 0
        while True:
            k = s + m*self.e0
            if k >= len(d0v) and m >= self.g0: break
            b = d0v[k] if k < len(d0v) else []
            req = u - m*self.h0
            if b and req >= 0 and w0(self.R, b) == req:
                out.append(self.res_digit(b, req))
            else:
                if b and req >= 0 and w0(self.R, b) < req:
                    raise AssertionError("R1w: digit below line (w1(a) < beta)")
                out.append(tuple([0]*self.d0))
            m += 1
            if k >= len(d0v): break
        return out
    def R1w_at_z1(self, a, beta):
        K1 = self.K1
        val = K1["zero"]; zp = K1["one"]
        for c in self.R1w(a, beta):
            if any(c):
                val = K1["add"](val, K1["mul"](K1["embed"](c), zp))
            zp = K1["mul"](zp, self.z1)
        return val

    # ---- eps_1(beta), Def 3.15, in the active reading (see AMENDMENT):
    #      "C": z1^(l0p*s - l0*u)  (proof-derived; Lemma 4.3 / eq (17))
    #      "P": z1^(l0*s - l0p*u)  (the leaf's S3.1 quote of the extraction) ----
    def eps1(self, beta, mode=None):
        s, u = eq12(beta, self.e0, self.h0)
        m = mode or self.mode
        expo = (self.l0p*s - self.l0*u) if m == "C" else (self.l0*s - self.l0p*u)
        return self.K1["pow"](self.z1, expo)

    # ---- level-2 FGMN weight read R_{2,gamma}(f): K1[y] with support meta ----
    def R2w(self, f, with_meta=False):
        d1, vals, g = self.w2_data(f)
        assert g < INF, "R2w of 0"
        s2, u2 = eq12(g, self.e1, self.h1)
        jmax = (len(d1)-1 - s2)//self.e1 if len(d1)-1 >= s2 else -1
        coeffs = []; online = []
        for j in range(jmax+1):
            sj = s2 + j*self.e1
            a = d1[sj]
            num = g - sj*self.gamma2
            assert num % self.e1 == 0, "gamma_j not integral"
            gj = num // self.e1
            on = bool(a) and (vals[sj] == gj)
            if a and vals[sj] < gj:
                raise AssertionError("slot below the line: w2 min wrong")
            if a and gj >= 0:
                inner = self.R1w_at_z1(a, gj) if vals[sj] >= gj else None
                c = self.K1["mul"](self.eps1(gj), inner) if inner is not None \
                    else self.K1["zero"]
            else:
                c = self.K1["zero"]
            coeffs.append(c); online.append(on)
        coeffs = coeffs if any(not self.K1["isz"](c) for c in coeffs) else []
        if with_meta:
            # polygon-side data: attained abscissas
            att = [j for j in range(len(d1))
                   if vals[j] < INF and self.e1*vals[j] + j*self.gamma2 == g]
            return coeffs, dict(gamma=g, s2=s2, u2=u2, online=online,
                                s0=min(att), sprime=max(att), dev=d1, vals=vals)
        return coeffs
    def R2s(self, f):
        """side read: strip y^j0; returns (list, j0_observed, gamma)."""
        coeffs, meta = self.R2w(f, with_meta=True)
        j0 = 0
        while j0 < len(coeffs) and self.K1["isz"](coeffs[j0]): j0 += 1
        return fp_norm(self.K1, coeffs[j0:]), j0, meta

    # ---- realize a K1 residue class at level-1 weight gammap (anchor rep) ----
    def realize1(self, tau, gammap):
        """O[x] poly C, deg < deg Phi1, w1(C) = gammap, level-1 FGMN weight-read
        value R_{1,gammap}(C)(z1) == tau.  Needs u(gammap) >= (g0-1)*h0."""
        R = self.R
        s, u = eq12(gammap, self.e0, self.h0)
        assert u - (self.g0-1)*self.h0 >= 0, "realize1 infeasible"
        C = []
        for m in range(self.g0):
            cm = tau[m] if m < len(tau) else self.K0["zero"]
            if self.K0["isz"](cm): continue
            t = pscal(R, R["pi_pow"](u - m*self.h0),
                      pmul(R, self.liftK0(cm), ppow(R, self.Phi0, s + m*self.e0)))
            C = padd(R, C, t)
        return C

    # ---- canonical state-key lift ----
    def build_Phi2(self):
        R = self.R
        Phi2 = []
        for k, c in enumerate(self.psi1):
            if self.K1["isz"](c): continue
            gp = (self.g1 - k)*self.gamma2
            tau = self.K1["mul"](self.K1["inv"](self.eps1(gp)), c) if gp else c
            Ck = self.realize1(tau, gp) if gp else self.liftK0(
                    tuple([1] + [0]*(self.d0-1)))     # k = g1: C = 1
            Phi2 = padd(R, Phi2, pmul(R, Ck, ppow(R, self.Phi1, self.e1*k)))
        return Phi2

    # ---- random sample builders ----
    def rand_K0(self, nonzero=False):
        while True:
            c = tuple(random.randrange(self.p) for _ in range(self.d0))
            if not nonzero or any(c): return c
    def rand_K1(self, nonzero=False):
        while True:
            c = tuple(self.rand_K0() for _ in range(self.g0))
            if not nonzero or not self.K1["isz"](c): return c
    def rand_opoly(self, maxdeg, pimax=4):
        R = self.R
        out = []
        for i in range(maxdeg+1):
            if random.random() < 0.35: out.append(R["zero"]); continue
            a = random.randrange(0, pimax)
            c = random.randrange(1, self.p)
            base = c if R["kind"] == "Zp" else (c,)
            out.append(R["mul"](R["pi_pow"](a), base))
        f = pnorm(R, out)
        return f
    def rand_structured(self, nslots=3):
        """mixture: on-line-ish realizations + noise (never zero)."""
        R = self.R
        base = self.gamma2*(nslots + 2) + (self.g0-1)*self.h0*self.e0 + 4
        f = []
        for j in range(nslots):
            gp = base - j*self.gamma2 + random.choice([0, 0, 1])*self.e1
            if gp < 0 or eq12(gp, self.e0, self.h0)[1] < (self.g0-1)*self.h0:
                continue
            if random.random() < 0.15: continue
            C = self.realize1(self.rand_K1(nonzero=True), gp)
            f = padd(R, f, pmul(R, C, ppow(R, self.Phi1, j)))
        noise = self.rand_opoly(random.randrange(0, self.degPhi1 + 3), pimax=3)
        f = padd(R, f, pscal(R, R["pi_pow"](base), noise))
        if not f:
            f = [R["pi_pow"](base)]
        return f

# ================================ test families ===============================
def T1_T2(T, nf=30):
    K1 = T.K1
    for _ in range(nf):
        f = T.rand_structured(nslots=random.choice([2,3,4]))
        coeffs, meta = T.R2w(f, with_meta=True)
        g = meta["gamma"]; s0 = meta["s0"]; sp = meta["sprime"]
        note("T1")
        # T1: A-LAW-2 — the min is attained at the left vertex: gamma =
        # e1*w1(a_{s0}) + s0*gamma2, equivalently (integer ordinates
        # u'_j = w1(a_j) + j*w1Phi1) the displayed e1*u0' + s0*h1 form.
        if g != T.e1*meta["vals"][s0] + s0*T.gamma2:
            viol("T1", T.tag, f"A-LAW-2: gamma={g} != e1*w1+s0*gamma2 at s0={s0}")
        u0p = meta["vals"][s0] + s0*T.w1Phi1     # polygon ordinate at s0
        if T.e1*u0p + s0*T.h1 != g:              # gamma2 = e1*w1Phi1 + h1
            viol("T1", T.tag, f"A-LAW-2 ordinate form fails at s0={s0}")
        if (s0 - meta["s2"]) % T.e1 != 0:
            viol("T1", T.tag, f"s0={s0} !== s(gamma)={meta['s2']} mod e1")
        # slope dictionary on the realized face (needs >= 2 attained abscissas)
        if sp > s0:
            v0 = meta["vals"][s0] + s0*T.w1Phi1
            v1 = meta["vals"][sp] + sp*T.w1Phi1
            if Fraction(v0 - v1, sp - s0) != Fraction(T.h1, T.e1) or \
               Fraction(T.h1, T.e1) != T.E1*Fraction(T.h1, T.E2):
                viol("T1", T.tag, f"slope {(v0-v1)}/{(sp-s0)} != h1/e1 (TR-1-corr)")
        # T2: support/two-form
        note("T2")
        ok = True
        for j, on in enumerate(meta["online"]):
            has = j < len(coeffs) and not K1["isz"](coeffs[j])
            if has != on:
                ok = False
                viol("T2", T.tag, f"support at slot j={j}: online={on} coeff!=0={has}")
        j0_pred = (s0 - meta["s2"])//T.e1
        side, j0_obs, meta2 = T.R2s(f)
        if j0_obs != j0_pred or j0_pred != s0//T.e1:
            ok = False
            viol("T2", T.tag, f"j0 obs={j0_obs} pred=floor(s0/e1)={s0//T.e1}")
        if not side or K1["isz"](side[0]):
            viol("T2", T.tag, "side read constant term zero")
        d_pred = (sp - s0)//T.e1
        if len(side)-1 != d_pred:
            viol("T2", T.tag, f"deg R2 = {len(side)-1} != d = {d_pred}")

def T3_T4(T, npairs=20):
    K1 = T.K1
    for _ in range(npairs):
        f = T.rand_structured(random.choice([2,3]))
        g = T.rand_structured(random.choice([2,3]))
        fg = pmul(T.R, f, g)
        note("T1")   # VAL-2 multiplicativity counted under T1
        wf, wg, wfg = T.w2(f), T.w2(g), T.w2(fg)
        if wfg != wf + wg:
            viol("T1", T.tag, f"VAL-2: w2(fg)={wfg} != {wf}+{wg}")
            continue
        Rf, j0f, mf = T.R2s(f)
        Rg, j0g, mg = T.R2s(g)
        Rfg, j0fg, mfg = T.R2s(fg)
        note("T3")
        if fp_norm(K1, Rfg) != fp_mul(K1, Rf, Rg):
            viol("T3", T.tag, f"R2(fg) != R2(f)R2(g)  [w2: {wf},{wg}]")
        # T4: weight-pair carry law
        note("T4")
        Wf = T.R2w(f); Wg = T.R2w(g); Wfg = T.R2w(fg)
        sf, _ = eq12(wf, T.e1, T.h1); sg, _ = eq12(wg, T.e1, T.h1)
        delta = (sf + sg)//T.e1
        if delta not in (0, 1):
            viol("T4", T.tag, f"delta={delta} not in {{0,1}}")
        pred = fp_mul(K1, [K1["zero"]]*delta + [K1["one"]], fp_mul(K1, Wf, Wg))
        if fp_norm(K1, Wfg) != pred:
            viol("T4", T.tag, f"W-MULT fails (delta={delta})")

def T5(T):
    R, K1 = T.R, T.K1
    note("T5")
    # level-1 re-asserts
    if T.w1(T.Phi1) != T.w1Phi1 or len(T.Phi1)-1 != T.degPhi1:
        viol("T5", T.tag, "level-1 key lift degree/weight wrong")
    for term in T.lift_terms1:
        if T.w1(term) != T.w1Phi1:
            viol("T5", T.tag, "level-1 lift term not homogeneous")
    # state key
    P2 = T.Phi2
    if len(P2)-1 != T.degPhi2:
        viol("T5", T.tag, f"deg Phi2 = {len(P2)-1} != {T.degPhi2}")
    lead = P2[-1] if P2 else R["zero"]
    if R["isz"](lead) or not R["isz"](R["add"](lead, R["neg"](R["one"]))):
        viol("T5", T.tag, "Phi2 not monic")
    d1, vals, g = T.w2_data(P2)
    if g != T.w2Phi2:
        viol("T5", T.tag, f"w2(Phi2) = {g} != e1*g1*gamma2 = {T.w2Phi2}")
    # one-sidedness: every nonzero slot weight >= w2Phi2, slots multiples of e1
    for j, c in enumerate(d1):
        if c and T.e1*vals[j] + j*T.gamma2 < T.w2Phi2:
            viol("T5", T.tag, f"Phi2 slot {j} below weight")
    side, j0, meta = T.R2s(P2)
    if j0 != 0:
        viol("T5", T.tag, f"R2(Phi2): j0 = {j0} != 0 (s(Phi2) != 0)")
    if side != fp_norm(K1, T.psi1):
        viol("T5", T.tag, "clause (3): R2(Phi2) != psi1 exactly")

def T6(T, nB=25):
    for _ in range(nB):
        B = T.rand_opoly(random.randrange(0, T.degPhi2), pimax=4)
        if not B: B = [T.R["one"]]
        note("T6")
        side, j0, meta = T.R2s(B)
        if fp_ord(T.K1, side, T.psi1) != 0:
            viol("T6", T.tag, f"(d2): ord_psi1 R2(B) > 0 at deg B = {len(B)-1}")

def _ord_tie(T, f, fam):
    """the (d3)/(4) tie: first-attainment in the Phi2-development vs
    ord_{psi1}(R2(f)); plus DEVID-2."""
    note(fam)
    C = dev(T.R, f, T.Phi2)
    us = [(T.w2(ck) + k*T.w2Phi2) if ck else INF for k, ck in enumerate(C)]
    finite = [(u, k) for k, u in enumerate(us) if u < INF]
    umin = min(u for u, _ in finite)
    kstar = min(k for u, k in finite if u == umin)
    wf = T.w2(f)
    if umin != wf:
        viol(fam, T.tag, f"DEVID-2: min dev weight {umin} != w2(f) = {wf}")
        return
    side, j0, meta = T.R2s(f)
    mu_res = fp_ord(T.K1, side, T.psi1)
    if mu_res != kstar:
        viol(fam, T.tag,
             f"ord tie: graded mu = {kstar} != ord_psi1(R2 f) = {mu_res} "
             f"[deg f = {len(f)-1}, w2 = {wf}, s0 = {meta['s0']}]")

def T7(T, nf=20):
    for _ in range(nf):
        mu = random.choice([0, 1, 1, 2])
        Q = T.rand_structured(random.choice([2,3]))
        f = pmul(T.R, ppow(T.R, T.Phi2, mu), Q)
        # high additive noise (leaves in(f) alone; scrambles the development):
        # pi^k * n has w2 >= e1*e0*k, so pick k with e0*e1*k > w2(f)
        wf = T.w2(f)
        n_ = T.rand_opoly(random.randrange(0, len(f)), pimax=2)
        if n_:
            k = wf//(T.e0*T.e1) + 2
            noise = pscal(T.R, T.R["pi_pow"](k), n_)
            if T.w2(noise) > wf:
                f = padd(T.R, f, noise)
        _ord_tie(T, f, "T7")

def T8(T, nf=50, ncorner=10):
    for _ in range(nf):
        f = T.rand_opoly(random.randrange(0, int(2.2*T.degPhi2) + 1), pimax=5)
        if not f: f = [T.R["pi_pow"](random.randrange(0, 4))]
        _ord_tie(T, f, "T8")
    for _ in range(ncorner):   # s(f) > 0 corners: f = Phi1^a * g (not mu-proper)
        a = random.randrange(1, 2*T.e1 + 1)
        g = T.rand_opoly(random.randrange(0, T.degPhi1 + 2), pimax=3)
        if not g: g = [T.R["one"]]
        f = pmul(T.R, ppow(T.R, T.Phi1, a), g)
        _ord_tie(T, f, "T8")

def gmn_coeff(T, a, v1a):
    """GMN Def 2.19/2.20 coefficient at e0 = 1: z1^(t1) * R1^GMN-side(a)(z1),
    t1 = s1(a) (initial level-1 abscissa; l0 = 0 at e0 = 1)."""
    K1 = T.K1
    d0v = dev(T.R, a, T.Phi0)
    onk = [k for k, b in enumerate(d0v) if b and w0(T.R, b) + k*T.h0 == v1a]
    s1a = min(onk)
    cG = K1["zero"]; zp = K1["pow"](T.z1, s1a)
    for k in range(s1a, max(onk)+1):
        b = d0v[k] if k < len(d0v) else []
        req = v1a - k*T.h0
        if b and req >= 0 and w0(T.R, b) == req:
            cG = K1["add"](cG, K1["mul"](K1["embed"](T.res_digit(b, req)), zp))
        zp = K1["mul"](zp, T.z1)
    return cG

def T9(T, nf=25):
    """TR-3 dictionary tests, e0 = 1 stratum only (reading C, amended):
    (i) pre-eps agreement; (ii-C) ratio == 1 per slot (operators agree);
    (iii-C) count samples refuting the S3.2 geometric law against the true
    operator.  Returns s32_refuted count."""
    if T.e0 != 1: return 0
    K1 = T.K1
    z_g2 = K1["pow"](T.z1, T.gamma2)
    z_nontriv = not (z_g2 == K1["one"])
    s32_refuted = 0
    for _ in range(nf):
        # 3 consecutive on-line slots (abscissas j*e1, so s2 = 0 and the total
        # weight is g = e1*base), all slot residues nonzero
        J = 3
        base = T.gamma2*(J + 2) + (T.g0-1)*T.h0 + 3
        taus = [T.rand_K1(nonzero=True) for _ in range(J)]
        f = []
        for j in range(J):
            gp = base - j*T.gamma2
            f = padd(T.R, f, pmul(T.R, T.realize1(taus[j], gp),
                                  ppow(T.R, T.Phi1, j*T.e1)))
        coeffs, meta = T.R2w(f, with_meta=True)
        g = meta["gamma"]
        if meta["s2"] != 0 or g != T.e1*base:
            viol("T9", T.tag, f"T9 sample malformed: s2={meta['s2']}")
            continue
        note("T9")
        ratios = []
        ok = True
        for j in range(J):
            sj = j*T.e1
            a = meta["dev"][sj]
            gj = base - j*T.gamma2
            CF = coeffs[j]
            cG = gmn_coeff(T, a, meta["vals"][sj])
            # (i) pre-eps agreement: cG == inner FGMN sum = eps1(gj)^{-1} * CF
            inner = K1["mul"](K1["inv"](T.eps1(gj)), CF)
            if cG != inner:
                ok = False
                viol("T9", T.tag, f"pre-eps agreement fails at slot {j}")
            # (ii-C) the operators AGREE: ratio CF/cG == 1 (eps1 == 1 at e0=1)
            ratio = K1["mul"](CF, K1["inv"](cG))
            if ratio != K1["one"]:
                ok = False
                viol("T9", T.tag, f"ratio != 1 at slot {j} (reading C)")
            ratios.append(ratio)
        # (iii-C) the S3.2 geometric law, held against the TRUE operator:
        # it demands ratio(j+1) = ratio(j)*z1^gamma2 — refuted whenever
        # z1^gamma2 != 1 (with true ratios == 1)
        s32_holds_here = all(K1["mul"](ratios[j], z_g2) == ratios[j+1]
                             for j in range(J-1))
        if z_nontriv:
            if s32_holds_here:
                viol("T9", T.tag, "S3.2 law UNEXPECTEDLY holds vs true operator")
            else:
                s32_refuted += 1
        elif not s32_holds_here:
            viol("T9", T.tag, "S3.2 law fails though z1^gamma2 == 1")
    return s32_refuted

def T10(T):
    K1 = T.K1
    for s in range(0, 2*T.e1 + 2):
        note("T10")
        f = ppow(T.R, T.Phi1, s)
        coeffs, meta = T.R2w(f, with_meta=True)
        if meta["gamma"] != s*T.gamma2:
            viol("T10", T.tag, f"w2(Phi1^{s}) != s*gamma2")
        pred = [K1["zero"]]*(s//T.e1) + [K1["one"]]
        if fp_norm(K1, coeffs) != fp_norm(K1, pred):
            viol("T10", T.tag, f"eq(14): R2w(Phi1^{s}) != y^floor(s/e1)")
        side, j0, _ = T.R2s(f)
        if side != [K1["one"]] or j0 != s//T.e1:
            viol("T10", T.tag, f"eq(14) side read at s={s}")

def T0():
    """Lemma-4.3 exponent algebra, symbolic (pins reading C)."""
    for e in range(1, 13):
        for h in range(1, 26):
            if math.gcd(e, h) != 1: continue
            l, lp = bezout(e, h)
            for gamma in range(-60, 61):
                sb, ub = eq12(gamma, e, h)
                note("T0")
                d = l*ub - lp*sb
                if sb + e*d != l*(h*sb + e*ub) or ub - h*d != lp*(h*sb + e*ub):
                    viol("T0", "symbolic", (e, h, gamma))

def P3(T, npairs=20):
    """Cor 4.7(3) multiplicativity under reading P (T must have mode='P')."""
    K1 = T.K1
    v = 0
    for _ in range(npairs):
        f = T.rand_structured(random.choice([2,3]))
        g = T.rand_structured(random.choice([2,3]))
        fg = pmul(T.R, f, g)
        note("P3")
        Rf, _, _ = T.R2s(f); Rg, _, _ = T.R2s(g); Rfg, _, _ = T.R2s(fg)
        if fp_norm(K1, Rfg) != fp_mul(K1, Rf, Rg):
            v += 1
    return v

def P9(T, nf=15):
    """S3.2's geometric law under reading P at e0 = 1 (G2 reproduction on
    real towers; T must have mode='P').  Violations of the P-law counted."""
    if T.e0 != 1: return
    K1 = T.K1
    z_g2 = K1["pow"](T.z1, T.gamma2)
    for _ in range(nf):
        J = 3
        base = T.gamma2*(J + 2) + (T.g0-1)*T.h0 + 3
        taus = [T.rand_K1(nonzero=True) for _ in range(J)]
        f = []
        for j in range(J):
            f = padd(T.R, f, pmul(T.R, T.realize1(taus[j], base - j*T.gamma2),
                                  ppow(T.R, T.Phi1, j*T.e1)))
        coeffs, meta = T.R2w(f, with_meta=True)   # mode P operator
        note("P9")
        # G2 reproduction: ratio C^F_j(P) / c^G_j, S3.2's geometric law
        ratios = []
        for j in range(J):
            cG = gmn_coeff(T, meta["dev"][j*T.e1], meta["vals"][j*T.e1])
            ratios.append(K1["mul"](coeffs[j], K1["inv"](cG)))
        okP = all(K1["mul"](ratios[j], z_g2) == ratios[j+1] for j in range(J-1))
        if not okP:
            viol("P9", T.tag, "S3.2 law fails even under reading P")

def P11(T, pari):
    """Discriminating PARI family on the reading-P lift (T mode='P', Zp,
    e0 >= 2).  Harness verdict: Phi2^P irreducible over Q_p iff the
    reading-C-truth residual psi1_twist is a power of one irreducible."""
    if T.kind != "Zp" or pari is None or T.e0 < 2: return
    K1 = T.K1
    note("P11")
    # psi1_twist_k = (epsC/epsP)(gamma'_k) * psi1_k
    tw = []
    for k, c in enumerate(T.psi1):
        gp = (T.g1 - k)*T.gamma2
        fac = K1["mul"](T.eps1(gp, mode="C"), K1["inv"](T.eps1(gp, mode="P")))
        tw.append(K1["mul"](fac, c))
    tw = fp_norm(K1, tw)
    # power-of-one-irreducible test (deg <= 2 residuals here)
    dtw = len(tw) - 1
    verdict_irr = None
    if dtw == 1:
        verdict_irr = True
    elif dtw == 2:
        # roots in K1?
        roots = [e for e in _field_elems(K1) if K1["isz"](fp_eval(K1, tw, e))]
        if not roots:
            verdict_irr = True                      # irreducible quadratic
        else:
            # monic-normalize, check square: tw = lead*(y-r)^2?
            lead = tw[-1]
            mon = [K1["mul"](K1["inv"](lead), c) for c in tw]
            r = roots[0]
            sq = fp_mul(K1, [K1["neg"](r), K1["one"]], [K1["neg"](r), K1["one"]])
            verdict_irr = (fp_norm(K1, mon) == fp_norm(K1, sq))  # ramified power
    else:
        return  # out of scope
    coeffs = [int(c) for c in T.Phi2]
    F = pari.Pol(list(reversed(coeffs)))
    fac = pari.factorpadic(F, T.p, 80)
    pari_irr = (len(fac[0]) == 1 and int(fac[1][0]) == 1)
    if pari_irr != verdict_irr:
        viol("P11", T.tag,
             f"PARI irreducible={pari_irr} but twist-residual verdict={verdict_irr}")
    return (verdict_irr, pari_irr)

def P12(pari):
    """The kill-shot discriminator: search the Z_p perimeter for a tower and a
    psi1 (deg 2, irreducible over K1) whose reading-P twisted residual
    psi1_twist = sum_k (epsC/epsP)(gamma'_k) psi1_k y^k is REDUCIBLE with
    DISTINCT irreducible factors over K1.  Then under reading-C-as-truth the
    reading-P canonical lift Phi2^P FACTORS over Q_p, while under
    reading-P-as-truth it would be a key polynomial (irreducible).  PARI
    decides.  Also cross-checks: the reading-C lift of the SAME psi1 is
    irreducible.  PREDICTED: on every instance found, PARI = reducible for
    the P-lift and irreducible for the C-lift (0 mismatches)."""
    if pari is None: return []
    found = []
    grid = [(p, d0, r0, (1, 1, 2))
            for p in (2, 3) for d0 in (1, 2)
            for r0 in ((2, 1, 1), (2, 1, 2), (3, 1, 1), (2, 3, 1))]
    for p, d0, r0, r1 in grid:
        try:
            T = Tower("Zp", p, d0, r0, r1, f"Zp,p={p},{d0}{r0}{r1}/P12", mode="P")
        except AssertionError:
            continue
        K1 = T.K1
        # enumerate irreducible deg-2 psi1 candidates; find reducible twist
        # with distinct factors
        for b in _field_elems(K1):
            if K1["isz"](b): continue
            for a in _field_elems(K1):
                cand = [b, a, K1["one"]]
                if not fp_irreducible(K1, cand): continue
                tw = []
                for k, c in enumerate(cand):
                    gp = (T.g1 - k)*T.gamma2
                    fac = K1["mul"](T.eps1(gp, mode="C"),
                                    K1["inv"](T.eps1(gp, mode="P")))
                    tw.append(K1["mul"](fac, c))
                roots = [e for e in _field_elems(K1)
                         if K1["isz"](fp_eval(K1, tw, e))]
                if len(roots) == 2 and roots[0] != roots[1]:
                    found.append((p, d0, r0, r1, cand))
                    break
            else:
                continue
            break
        if len(found) >= 2: break
    results = []
    for p, d0, r0, r1, cand in found[:2]:
        note("P12")
        TP = Tower("Zp", p, d0, r0, r1, f"Zp,p={p},P12", mode="P",
                   psi1_override=cand)
        TC = Tower("Zp", p, d0, r0, r1, f"Zp,p={p},P12", mode="C",
                   psi1_override=cand)
        verdicts = []
        for TT, pred_irr in ((TP, False), (TC, True)):
            F = pari.Pol(list(reversed([int(c) for c in TT.Phi2])))
            fac = pari.factorpadic(F, p, 80)
            pari_irr = (len(fac[0]) == 1 and int(fac[1][0]) == 1)
            verdicts.append(pari_irr)
            if pari_irr != pred_irr:
                viol("P12", TT.tag,
                     f"PARI irr={pari_irr}, predicted {pred_irr} "
                     f"(mode {TT.mode} lift)")
        results.append((p, d0, r0, r1, verdicts))
    return results

def T11(T, pari):
    if T.kind != "Zp" or pari is None: return
    note("T11")
    coeffs = [int(c) for c in T.Phi2]
    F = pari.Pol(list(reversed(coeffs)))
    fac = pari.factorpadic(F, T.p, 60)
    nfac = len(fac[0])
    if nfac != 1 or int(fac[1][0]) != 1:
        viol("T11", T.tag, f"PARI: Phi2 NOT irreducible over Q_{T.p} ({nfac} factors)")
        return
    nf = pari.nfinit([F, [T.p]])
    dec = pari.idealprimedec(nf, T.p)
    e_pred, f_pred = T.e0*T.e1, T.d0*T.g0*T.g1
    if len(dec) != 1:
        viol("T11", T.tag, f"PARI: {len(dec)} primes above p (pred 1)")
        return
    pr = dec[0]
    e_obs, f_obs = int(pr[2]), int(pr[3])
    if (e_obs, f_obs) != (e_pred, f_pred):
        viol("T11", T.tag, f"PARI (e,f) = ({e_obs},{f_obs}) != pred ({e_pred},{f_pred})")

# ==================================== main ====================================
ROSTER = [
    # (tag, d0, (e0,h0,g0), (e1,h1,g1))
    ("A", 1, (1,1,1), (2,1,1)),
    ("B", 1, (1,2,2), (3,2,1)),
    ("C", 1, (2,1,1), (2,1,1)),
    ("D", 1, (2,3,1), (1,1,2)),
    ("E", 1, (3,1,1), (2,3,1)),
    ("F", 1, (1,1,1), (1,1,1)),     # e1*g1 = 1 refinement state read
    ("G", 2, (1,1,1), (2,1,1)),
    ("H", 2, (2,1,1), (1,1,1)),     # e1*g1 = 1
    ("I", 2, (1,1,2), (2,3,1)),
    ("J", 2, (2,1,2), (2,1,1)),     # E2 = 4, deg Phi2 = 16
]

def main():
    t_start = time.time()
    sys.path.insert(0, os.path.expanduser('~/.local/lib/python3.10/site-packages'))
    try:
        import cypari2
        pari = cypari2.Pari()
        pari.allocatemem(1 << 28, silent=True)
    except Exception as exc:
        pari = None
        print(f"WARNING: cypari2 unavailable ({exc}); T11 skipped -> RED if predicted")
    T0()
    print(f"[{time.time()-t_start:7.1f}s] T0 (Lemma-4.3 symbolic pin) done: "
          f"{sum(1 for v in VIOL if v[0]=='T0')} violations / {COUNTS.get('T0',0)}")
    s32_refuted = 0
    s32_expected = 0
    p3_viol_total = 0
    p3_viol_z3C = 0
    p3_viol_z1triv = 0
    p11_results = []
    configs = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]
    for kind, p in configs:
        for tag, d0, r0, r1 in ROSTER:
            full_tag = f"{kind},p={p},{tag}"
            T = Tower(kind, p, d0, r0, r1, full_tag)
            T1_T2(T, nf=30)
            T3_T4(T, npairs=20)
            T5(T)
            T6(T, nB=25)
            T7(T, nf=20)
            T8(T, nf=50, ncorner=10)
            cv = T9(T, nf=25)
            if T.e0 == 1:
                s32_refuted += cv
                if not (T.K1["pow"](T.z1, T.gamma2) == T.K1["one"]):
                    s32_expected += 25
            T10(T)
            T11(T, pari)
            # --- reading-P demonstration families ---
            if tag in ("C", "D", "E", "H", "J"):   # e0 >= 2 towers (D: g1 = 2)
                TP = Tower(kind, p, d0, r0, r1, full_tag + "/P", mode="P")
                v = P3(TP, npairs=20)
                p3_viol_total += v
                if kind == "Zp" and p == 3 and tag == "C":
                    p3_viol_z3C += v
                if TP.K1["pow"](TP.z1, 1) == TP.K1["one"]:   # z1 == 1
                    p3_viol_z1triv += v
                r = P11(TP, pari)
                if r: p11_results.append((full_tag, r))
            if tag in ("A", "B", "G", "I"):        # e0 = 1 towers, z1 varied
                TP = Tower(kind, p, d0, r0, r1, full_tag + "/P", mode="P")
                P9(TP, nf=15)
        print(f"[{time.time()-t_start:7.1f}s] ring ({kind}, p={p}) done: "
              f"cumulative violations = {len(VIOL)}")
    p12_results = P12(pari)
    # -------------------------- report --------------------------
    print()
    print("=" * 78)
    print("PREDICTED vs OBSERVED  (violation counts; samples in parentheses)")
    print("=" * 78)
    fams = [
        ("T0",  "Lemma-4.3 exponent algebra (pins reading C)",  "0"),
        ("T1",  "A-LAW-2 + TR-1-corr slope + (12-int) + VAL-2", "0"),
        ("T2",  "(2') two-form/support (Cor 4.4(2)(3)(4))",     "0"),
        ("T3",  "law (1) total mult (Cor 4.7(3), theta=1)",     "0"),
        ("T4",  "(W-MULT) carry law, delta in {0,1}",           "0"),
        ("T5",  "key lift + clause (3) R2(Phi2)=psi1",          "0"),
        ("T6",  "(d2) low-degree block",                        "0"),
        ("T7",  "guarded (4)/(d3) ord tie + DEVID-2",           "0"),
        ("T8",  "TOTAL-form faithfulness (U14 gate)",           "UNKNOWN(gate)"),
        ("T9",  "TR-3 e0=1: pre-eps agree + ratio==1 (amended)","0"),
        ("T10", "D-REAL/eq(14) s-walk (single wrap)",           "0"),
        ("T11", "PARI oracle (e,f) tie, Zp towers",             "0"),
        ("P9",  "S3.2 law internal to reading P (G2 repro)",    "0"),
        ("P11", "reading-P lift vs PARI (discriminator)",       "0"),
        ("P12", "PARI kill-shot: P-lift reducible, C-lift irr", "0"),
    ]
    all_green = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        n = COUNTS.get(fam, 0)
        if pred == "0":
            verdict = "GREEN" if obs == 0 else "RED"
        else:  # T8
            verdict = "GREEN(U14-stateable)" if obs == 0 else "RED(U14-negative)"
        if "RED" in verdict: all_green = False
        print(f"{fam:4} {desc:47} pred {pred:>13}  obs {obs:5d} ({n:5d})  {verdict}")
    print("-" * 78)
    print(f"T9(iii-C) S3.2-law-vs-true-operator refutations: {s32_refuted}"
          f"/{s32_expected} predicted "
          f"{'MATCH' if s32_refuted == s32_expected else 'MISMATCH'}"
          f"  [each = one sample where the leaf's displayed geometric law fails"
          f" against the proof-derived operator]")
    if s32_refuted != s32_expected:
        all_green = False
    p3_pred_ok = (p3_viol_total > 0 and p3_viol_z3C >= 1 and p3_viol_z1triv == 0)
    print(f"P3 reading-P Cor 4.7(3) violations: total {p3_viol_total} "
          f"(pred > 0), on (Z_3,C): {p3_viol_z3C} (pred >= 1), on z1==1 towers: "
          f"{p3_viol_z1triv} (pred 0)  -> {'MATCH' if p3_pred_ok else 'MISMATCH'}")
    if not p3_pred_ok:
        all_green = False
    if p11_results:
        print("P11 per-tower (harness-irreducible?, PARI-irreducible?):")
        for tag, r in p11_results:
            print(f"    {tag}: {r}" + ("  <- reading-P lift NOT a key (machine"
                  " refutation of reading P)" if r == (False, False) else ""))
    if p12_results:
        print("P12 kill-shot instances (p, d0, r0, r1, [PARI-irr P-lift, "
              "PARI-irr C-lift]; predicted [False, True]):")
        for rec in p12_results:
            print(f"    {rec}" + ("  <- reading-P canonical lift FACTORS over"
                  " Q_p (external refutation of reading P)"
                  if rec[4] == [False, True] else ""))
    elif pari is not None:
        print("P12: no reducible-twist instance found in the search perimeter "
              "(discriminator inconclusive; reading-P refutation rests on "
              "P3 + T0 + the Def-3.15 i=0 remark)")
    print("-" * 78)
    if VIOL:
        print(f"{len(VIOL)} VIOLATIONS (first 25):")
        for v in VIOL[:25]:
            print("  ", v)
    print(f"TOTAL samples: {sum(COUNTS.values())}   elapsed {time.time()-t_start:.1f}s")
    print(f"VERDICT: {'ALL GREEN' if all_green and not VIOL else 'RED — see above'}")
    return 0 if (all_green and not VIOL) else 1

if __name__ == "__main__":
    sys.exit(main())
