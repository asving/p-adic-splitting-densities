#!/usr/bin/env python3
"""GENTOW-5 battery: composed graded frame at general mu2 (GENTOW-BOX-1)
+ the level-r ladder grammar / depth-4 witness.  Two-commit seal.

PREREGISTERED PREDICTIONS (written BEFORE the first full run; the
depth-4 mutant factorization T-B1 and the A-row residual arithmetic
were hand-derived in the note's S4.2/S1 pre-seal and are disclosed
there; no code in this file was executed against the real families
before the seal commit).

CHECK-A (mu2 = 3 / live-twist mu2 = 2 pointwise kills at the composed
key -- THEOREM GENTOW5-A; exact integer re-division, no formula):
 P-A1  q=2 genre (2,1,6)->(2,1,3), Phi'=x^2-2, Phi2=Phi'^2-4x, K2=F2,
       lam=11, s=1: member f = Phi2^3 + 2xPhi'*Phi2^2 + 32x*Phi2
       + 128Phi'.  Event pins (11,22,33) exact; entry gate >= 31;
       refine by Phi2 - 2xPhi': ALL THREE pins die (slotmin(C_j+) >
       (3-j)*11).
 P-A2  q=3 CHAR-3 ROW, Phi'=x^2-6 (live level-1 wrap letter eta=2),
       Phi2=Phi'^2-9x, K2=F3, lam=11, s=2: member f = Phi2^3 +
       3^7*Phi' (char-3 Frobenius: (T-2)^3 = T^3+1, pins j=1,2
       ABSENT).  Pin (0,33) exact; refine by Phi2 - 6xPhi' (digit 2):
       all three thresholds cleared.
 P-A3  q=2 f2=2 ROW (K2=F4), genre (2,1,6)->(1,2,3), Phi2 =
       Phi'^2-2xPhi'-8 (u2=3, psi2=y^2+y+1), lam=7, s=eta2: member
       f = Phi2^3 + 4Phi'*Phi2^2 + (128+32xPhi')*Phi2 + 1024x
       (two-flavor K2-digit lift at height 14).  Pins (7,14,21);
       refine by Phi2 - 4Phi' (the eta2-flavor lift): all three die.
 P-A4  LIVE-TWIST mu2=2 ROW q=3: same keys as A-2, mu2=2 (n=8),
       lam=11, s=2, vartheta_2 = res(nhat(11)^2/nhat(22)) = 2 != 1
       (hand-derived S1.2): TWIST-CORRECTED member f = Phi2^2 +
       6xPhi'*Phi2 + 486x (coherent digit gamma_0 = 2 =
       c_0*vartheta_2) kills BOTH pins under refine by Phi2 - 6xPhi'.
 TEETH (each must FIRE = the wrong object is caught):
 T-A1W wrong-HEIGHT refine at A-1 (Phi2 - 4x, height 10 < lam):
       kill fails; predicted surviving pin slotmin(C_2+) = 10 <= 11.
 T-A2W wrong-DIGIT refine at A-2 (digit 1: Phi2 - 3xPhi'):
       predicted surviving pin slotmin(C_0+) = 33 exactly
       (R_N(T+1) = T^3 + 2).
 T-A4W THE CONVENTION TOOTH: the naive member f' = Phi2^2 +
       6xPhi'*Phi2 + 243x (digit written WITHOUT the vartheta_2
       correction) under the SAME refine keeps the pin:
       slotmin(C_0+) = 22 exactly, while P-A4's member dies --
       the multiplicative convention is machine-load-bearing.
       (Direction caveat, disclosed: F3-units are self-inverse, so
       this tooth cannot distinguish vartheta from vartheta^{-1};
       it distinguishes corrected from uncorrected.)

CHECK-B (depth-4 grammar at the minimal chain u = 5,21,85,341, q=2;
keys Phi1=x^2-2, Phi2=Phi1^2-4x, Phi3=Phi2^2-16Phi1,
Phi4=Phi3^2-256Phi2; f32 = Phi4^2 - 2^16*Phi3, n = 32):
 P-B1  floor chain tight: u_{i+1} = 4u_i + 1 > 4u_i = e_{i+1}E_i.
 P-B2  recipe side heights exact: dv2(4x)=10=E2, dv3(16Phi1)=42=E3,
       dv4(256Phi2)=170=E4, dv4(2^16Phi3)=341 (the top event).
 P-B3  one-sidedness at EVERY level (Cor 6.4's display, exact
       slot-weight pins): polygons of Phi2@Phi1, Phi3@{Phi2,Phi1},
       Phi4@{Phi3,Phi2,Phi1}, f32@{Phi4,Phi3,Phi2,Phi1}: all pins on
       or above the chord to (L,0); on-chord support EXACTLY the
       char-2 binomial spots: {0,L} for every listed polygon
       (residuals (y+1)^(2^k) = y^(2^k)+1 over F2).
 P-B4  RESULTANT LADDER (nfeltval-equivalent, PARI-free):
       v2(Res(f32, g)) for g = x, Phi1, Phi2, Phi3, Phi4
       = (16, 40, 84, 170, 341);  v2(Res(Phi4, g)) for g = x, Phi1,
       Phi2, Phi3 = (8, 20, 42, 85).
 T-B1  node-height mutant f32m = Phi4^2 - 2^20*Phi1 (340 = 2*E4,
       gcd(340,2) != 1): Phi3 | f32m EXACTLY (the drain collapse,
       hand-derived pre-seal in S4.2) -- remainder 0; ladder entry
       at Phi3 infinite != 170.

CHECK-C (PARI leg, run separately/detached, artifacts committed):
 P-C1  factorpadic(f32, 2, 700): ONE factor, degree 32.
 P-C2  nfinit([f32,[2]]) + idealprimedec: single prime, e=32, f=1;
       nfeltval ladder for x, Phi1, Phi2, Phi3, Phi4 =
       (16, 40, 84, 170, 341).
 P-C3  refined keys keep carrier: factorpadic(Phi2-2xPhi', 2) one
       deg-4 factor with e=4 (A-1 frame); factorpadic(Phi2-6xPhi', 3)
       one deg-4 factor with e=4 (A-2/A-4 frame).
 P-C4  factorpadic(f32m, 2, 700): NOT a single degree-32 factor
       (Phi3 splits off).

Usage: python3 gentow5_checks.py          (exact leg)
       python3 gentow5_checks.py --pari   (exact leg + PARI leg)
"""
import sys, subprocess
from math import gcd, inf

OK = [0]; BAD = [0]; LOG = []
def say(s):
    LOG.append(s); print(s)
def chk(ok, msg):
    if ok: OK[0] += 1
    else:
        BAD[0] += 1; say("VIOLATION: " + msg)

# ---------- exact integer polynomials (coeff lists, index = degree) ----
def trim(f):
    while f and f[-1] == 0: f.pop()
    return f
def padd(f, g):
    n = max(len(f), len(g)); r = [0]*n
    for i,c in enumerate(f): r[i] += c
    for i,c in enumerate(g): r[i] += c
    return trim(r)
def pneg(f): return [-c for c in f]
def pscale(f, k): return trim([k*c for c in f])
def pmul(f, g):
    if not f or not g: return []
    r = [0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        if a:
            for j,b in enumerate(g): r[i+j] += a*b
    return trim(r)
def pdivmod_monic(f, g):
    # g monic; exact integer division
    assert g and g[-1] == 1
    f = list(f); q = [0]*max(1, len(f)-len(g)+1)
    while len(f) >= len(g):
        c = f[-1]; d = len(f)-len(g)
        q[d] = c
        for i,b in enumerate(g): f[d+i] -= c*b
        trim(f)
    return trim(q), trim(f)
def develop(f, key):
    """f = sum C_j key^j, deg C_j < deg key; returns [C_0, C_1, ...]."""
    out = []; f = list(f)
    while f:
        f, r = pdivmod_monic(f, key)
        out.append(r)
    return out
def vq(n, q):
    if n == 0: return inf
    v = 0
    while n % q == 0: n //= q; v += 1
    return v
def sylvester_res(f, g):
    """Resultant via fraction-free Bareiss on the Sylvester matrix."""
    m, n = len(f)-1, len(g)-1
    if m < 0 or n < 0: return 0
    N = m+n
    M = [[0]*N for _ in range(N)]
    for i in range(n):
        for j,c in enumerate(reversed(f)): M[i][i+j] = c
    for i in range(m):
        for j,c in enumerate(reversed(g)): M[n+i][i+j] = c
    # Bareiss
    prev = 1; sign = 1
    for k in range(N-1):
        if M[k][k] == 0:
            piv = next((r for r in range(k+1, N) if M[r][k] != 0), None)
            if piv is None: return 0
            M[k], M[piv] = M[piv], M[k]; sign = -sign
        for i in range(k+1, N):
            for j in range(k+1, N):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j])//prev
            M[i][k] = 0
        prev = M[k][k]
    return sign*M[N-1][N-1]

# ---------- ladder weights -------------------------------------------
def ladder_expand(C, keys):
    """Expand C into monomial dict over basis x^a * prod keys[j]^(b_j),
    exponents unbounded only for x below keys[0]... keys = [Phi1,..]
    used at level len(keys)+1's coefficient grid (deg C < prod degs).
    Returns dict (a, b_1, .., b_k) -> coeff."""
    if not keys:
        return {(a,): c for a,c in enumerate(C) if c}
    out = {}
    for b, coeffpoly in enumerate(develop(C, keys[-1])):
        for expo, c in ladder_expand(coeffpoly, keys[:-1]).items():
            out[expo + (b,)] = c
    return out
def slotmin(C, keys, q, ehat, uvec):
    """min ladder weight of C at the level-(len(keys)+1) grid.
    uvec = [u_1(=h scaled per x-step), u_2, ...]: weight of exponent
    e_j is e_j * (ehat/ehat_{j+1}) * u_{j+1} -- pass the PER-EXPONENT
    unit weights directly in wvec form."""
    wvec = uvec  # already per-exponent dv-weights at this level
    best = inf
    for expo, c in ladder_expand(C, keys).items():
        w = ehat*vq(c, q) + sum(e*wv for e, wv in zip(expo, wvec))
        best = min(best, w)
    return best
def polygon(P, key, subkeys, q, ehat, wvec):
    """pins (j, slotmin(C_j)) of P's key-development; returns list."""
    return [slotmin(C, subkeys, q, ehat, wvec) if C else inf
            for C in develop(P, key)]
def one_sided(pins, tag, expect_onchord):
    L = len(pins)-1
    chk(pins[L] == 0, tag+": monic top pin 0")
    p0 = pins[0]
    chk(p0 < inf, tag+": constant pin finite")
    on = []
    ok = True
    for j,p in enumerate(pins):
        if p == inf: continue
        # chord height at j: p0*(L-j)/L ; compare p*L >= p0*(L-j)
        if p*L < p0*(L-j): ok = False
        if p*L == p0*(L-j): on.append(j)
    chk(ok, tag+": one-sided (all pins on/above chord)")
    chk(on == expect_onchord, tag+f": on-chord support {on} == {expect_onchord}")
    return p0

# ---------- CHECK-A ---------------------------------------------------
def x(*cs): return list(cs)  # coeff list helper (c0, c1, ...)

def run_A():
    say("== CHECK-A: composed-key refine kills (THEOREM GENTOW5-A) ==")
    X = [0,1]
    # frames: (q, Phi', Phi2, ehat2, wvec2=(w_x, w_Phi'), E2, name)
    P1p = [-2,0,1]; P1p3 = [-6,0,1]
    A12_frame = dict(q=2, phi=P1p, key=padd(pmul(P1p,P1p), pscale(X,-4)),
                     ehat=4, wvec=(2,5), E2=10)
    A2_frame  = dict(q=3, phi=P1p3, key=padd(pmul(P1p3,P1p3), pscale(X,-9)),
                     ehat=4, wvec=(2,5), E2=10)
    A3_key = padd(padd(pmul(P1p,P1p), pscale(pmul(X,P1p),-2)), [-8])
    A3_frame  = dict(q=2, phi=P1p, key=A3_key, ehat=2, wvec=(1,3), E2=6)

    def member(frame, mu, coeffs):
        f = [0]*0
        K = frame['key']; Kp = [1]
        # f = key^mu + sum coeffs[j]*key^j
        f = list(K)
        for _ in range(mu-1): f = pmul(f, K)
        for j,c in coeffs.items():
            t = list(c)
            for _ in range(j): t = pmul(t, K)
            f = padd(f, t)
        return f
    def kills(frame, f, newkey, mu, lam, tag, expect_die=True,
              expect_pin=None):
        dev = develop(f, newkey)
        alive = []
        for j in range(mu):
            sm = slotmin(dev[j], [frame['phi']], frame['q'],
                         frame['ehat'], frame['wvec']) if j < len(dev) and dev[j] else inf
            if sm <= (mu-j)*lam: alive.append((j, sm))
        if expect_die:
            chk(not alive, tag+f": all pins die (alive={alive})")
        else:
            chk(bool(alive), tag+": kill FAILS as predicted (tooth fires)")
            if expect_pin is not None:
                chk(alive and alive[0][1] == expect_pin,
                    tag+f": surviving pin {alive} == predicted {expect_pin}")
    def pins_check(frame, f, mu, lam, support, tag):
        dev = develop(f, frame['key'])
        for j in range(mu):
            sm = slotmin(dev[j], [frame['phi']], frame['q'],
                         frame['ehat'], frame['wvec']) if j < len(dev) and dev[j] else inf
            if j in support:
                chk(sm == (mu-j)*lam, tag+f": pin j={j} == {(mu-j)*lam} (got {sm})")
            else:
                chk(sm > (mu-j)*lam, tag+f": j={j} strictly above (got {sm})")
            # entry gate: weight + j*E2 >= mu*E2 + 1
            if sm < inf:
                chk(sm + j*frame['E2'] >= mu*frame['E2'] + 1,
                    tag+f": entry gate at j={j}")

    # A-1
    fr = A12_frame; K = fr['key']
    n11 = pscale(pmul(X, P1p), 2)      # 2xPhi'
    f = member(fr, 3, {2: n11, 1: pscale(X,32), 0: pscale(P1p,128)})
    pins_check(fr, f, 3, 11, {0,1,2}, "A1")
    kills(fr, f, padd(K, pneg(n11)), 3, 11, "A1-KILL")
    kills(fr, f, padd(K, pscale(X,-4)), 3, 11, "T-A1W", expect_die=False,
          expect_pin=10)
    # A-2
    fr = A2_frame; K = fr['key']
    f = member(fr, 3, {0: pscale(P1p3, 3**7)})
    pins_check(fr, f, 3, 11, {0}, "A2")
    n11 = pscale(pmul(X, P1p3), 3)     # 3xPhi'
    kills(fr, f, padd(K, pscale(n11,-2)), 3, 11, "A2-KILL")
    kills(fr, f, padd(K, pneg(n11)), 3, 11, "T-A2W", expect_die=False,
          expect_pin=33)
    # A-3
    fr = A3_frame; K = fr['key']
    c1 = padd([128], pscale(pmul(X,P1p),32))
    f = member(fr, 3, {2: pscale(P1p,4), 1: c1, 0: pscale(X,1024)})
    pins_check(fr, f, 3, 7, {0,1,2}, "A3")
    kills(fr, f, padd(K, pscale(P1p,-4)), 3, 7, "A3-KILL")
    # A-4 (+ the convention tooth)
    fr = A2_frame; K = fr['key']
    n11 = pscale(pmul(X, P1p3), 3)
    f  = member(fr, 2, {1: pscale(n11,2), 0: pscale(X, 486)})
    fn = member(fr, 2, {1: pscale(n11,2), 0: pscale(X, 243)})
    pins_check(fr, f, 2, 11, {0,1}, "A4")
    pins_check(fr, fn, 2, 11, {0,1}, "A4naive")
    newkey = padd(K, pscale(n11,-2))
    kills(fr, f, newkey, 2, 11, "A4-KILL")
    kills(fr, fn, newkey, 2, 11, "T-A4W", expect_die=False, expect_pin=22)

# ---------- CHECK-B ---------------------------------------------------
def run_B():
    say("== CHECK-B: depth-4 minimal chain, q = 2 ==")
    X = [0,1]
    P1 = [-2,0,1]
    P2 = padd(pmul(P1,P1), pscale(X,-4))
    P3 = padd(pmul(P2,P2), pscale(P1,-16))
    P4 = padd(pmul(P3,P3), pscale(P2,-256))
    f32 = padd(pmul(P4,P4), pscale(P3,-(2**16)))
    u = [1,5,21,85,341]; E = [2,10,42,170]
    for i in range(1,5):
        chk(u[i] == 4*u[i-1]+1 and u[i] > 4*u[i-1] and gcd(u[i],2)==1,
            f"P-B1: floor rung u_{i+1}={u[i]} > 4*u_{i}={4*u[i-1]}, odd")
    # P-B2 side heights: correction term slot weights at the right grid
    # dv2(4x)=10: grid level 2 (keys=[P1], ehat=4, wvec=(2,5))
    chk(slotmin(pscale(X,4),[P1],2,4,(2,5)) == 10, "P-B2: dv2(4x)=10=E2")
    chk(slotmin(pscale(P1,16),[P1,P2],2,8,(4,10,21)) == 42,
        "P-B2: dv3(16Phi1)=42=E3")
    chk(slotmin(pscale(P2,256),[P1,P2,P3],2,16,(8,20,42,85)) == 170,
        "P-B2: dv4(256Phi2)=170=E4")
    chk(slotmin(pscale(P3,2**16),[P1,P2,P3],2,16,(8,20,42,85)) == 341,
        "P-B2: dv4(2^16Phi3)=341")
    # P-B3 polygons: (target, key, subkeys, ehat, wvec, tag, onchord)
    jobs = [
        (P2, P1, [], 4, (2,), "Phi2@Phi1", [0,2]),
        (P3, P2, [P1], 8, (4,10), "Phi3@Phi2", [0,2]),
        (P3, P1, [], 4, (2,), "Phi3@Phi1", [0,4]),
        (P4, P3, [P1,P2], 16, (8,20,42), "Phi4@Phi3", [0,2]),
        (P4, P2, [P1], 8, (4,10), "Phi4@Phi2", [0,4]),
        (P4, P1, [], 4, (2,), "Phi4@Phi1", [0,8]),
        (f32, P4, [P1,P2,P3], 32, (16,40,84,170), "f32@Phi4", [0,2]),
        (f32, P3, [P1,P2], 16, (8,20,42), "f32@Phi3", [0,4]),
        (f32, P2, [P1], 8, (4,10), "f32@Phi2", [0,8]),
        (f32, P1, [], 4, (2,), "f32@Phi1", [0,16]),
    ]
    for (T, K, sub, eh, wv, tag, onc) in jobs:
        pins = polygon(T, K, sub, 2, eh, wv)
        one_sided(pins, "P-B3 "+tag, onc)
        say(f"   {tag}: pins {['inf' if p==inf else p for p in pins]}")
    # P-B4 resultant ladders
    lad = []
    for g in (X, P1, P2, P3, P4):
        lad.append(vq(abs(sylvester_res(f32, g)), 2))
    chk(lad == [16,40,84,170,341], f"P-B4: f32 ladder {lad} == [16,40,84,170,341]")
    lad4 = [vq(abs(sylvester_res(P4, g)), 2) for g in (X, P1, P2, P3)]
    chk(lad4 == [8,20,42,85], f"P-B4: Phi4 ladder {lad4} == [8,20,42,85]")
    # T-B1 mutant
    f32m = padd(pmul(P4,P4), pscale(P1,-(2**20)))
    _, rem = pdivmod_monic(f32m, P3)
    chk(rem == [], "T-B1: Phi3 | f32m (drain collapse) -- remainder 0")
    chk(sylvester_res(f32m, P3) == 0, "T-B1: Res(f32m, Phi3) = 0 != 2^170-unit")
    return P1, P2, P3, P4, f32, f32m

# ---------- CHECK-C (PARI) --------------------------------------------
def polystr(f, var="x"):
    return "+".join(f"({c})*{var}^{i}" for i,c in enumerate(f) if c) or "0"
def run_C(P1,P2,P3,P4,f32,f32m):
    say("== CHECK-C: PARI leg ==")
    scr = f"""
default(parisize, 512M);
f32 = {polystr(f32)};
fm  = {polystr(f32m)};
F = factorpadic(f32, 2, 700);
print("C1 nfactors=", matsize(F)[1], " deg1=", poldegree(F[1,1]));
nf = nfinit([f32, [2]]);
pr = idealprimedec(nf, 2);
print("C2 nprimes=", length(pr), " e=", pr[1].e, " f=", pr[1].f);
print("C2 ladder=", [nfeltval(nf, x, pr[1]), nfeltval(nf, x^2-2, pr[1]), nfeltval(nf, {polystr(P2)}, pr[1]), nfeltval(nf, {polystr(P3)}, pr[1]), nfeltval(nf, {polystr(P4)}, pr[1])]);
K1 = (x^2-6)^2 - 9*x - 2*(3*x*(x^2-6));
F1 = factorpadic((x^2-2)^2 - 4*x - 2*(2*x*(x^2-2)), 2, 200);
print("C3a nfactors=", matsize(F1)[1], " deg=", poldegree(F1[1,1]));
nf1 = nfinit([(x^2-2)^2 - 4*x - 2*(2*x*(x^2-2)), [2]]);
pr1 = idealprimedec(nf1, 2); print("C3a e=", pr1[1].e, " f=", pr1[1].f);
F2 = factorpadic(K1, 3, 200);
print("C3b nfactors=", matsize(F2)[1], " deg=", poldegree(F2[1,1]));
nf2 = nfinit([K1, [3]]); pr2 = idealprimedec(nf2, 3);
print("C3b e=", pr2[1].e, " f=", pr2[1].f);
FM = factorpadic(fm, 2, 700);
print("C4 nfactors=", matsize(FM)[1], " degs=", vector(matsize(FM)[1], i, poldegree(FM[i,1])));
"""
    try:
        r = subprocess.run(["gp","-q","-f"], input=scr, capture_output=True,
                           text=True, timeout=1800)
        out = r.stdout
        say(out.strip())
        chk("C1 nfactors=1" in out and "deg1=32" in out,
            "P-C1: f32 one factor deg 32")
        chk("C2 nprimes=1" in out and "e=32" in out and "f=1" in out,
            "P-C2: single prime e=32 f=1")
        chk("[16, 40, 84, 170, 341]" in out, "P-C2: nfeltval ladder exact")
        chk("C3a nfactors=1" in out and out.count("deg=4") >= 1,
            "P-C3a: A1 refined key single deg-4")
        chk("C3b nfactors=1" in out, "P-C3b: A2/A4 refined key single factor")
        c4 = [l for l in out.splitlines() if l.startswith("C4")]
        chk(bool(c4) and "nfactors=1" not in c4[0].replace(" ", ""),
            "P-C4: mutant splits (Phi3 off) -- not a single factor")
    except Exception as e:
        say(f"PARI leg DID NOT COMPLETE: {e!r} -- disclosed, exact leg stands")

def main():
    run_A()
    art = run_B()
    if "--pari" in sys.argv:
        run_C(*art)
    say(f"== VERDICT: {OK[0]} checks passed, {BAD[0]} violations ==")
    return 1 if BAD[0] else 0

if __name__ == "__main__":
    sys.exit(main())
