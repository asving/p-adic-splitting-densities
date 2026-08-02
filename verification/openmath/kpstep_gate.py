#!/usr/bin/env python3
"""KP-STEP leaf-local gate (unit B-M1, HDISCHARGE_H1 §2.2) — order-2 exact checks.

Perimeter: O = Z_p, d0 = 1, g0 = 1 (K0 = K1 = F_p, level-1 residual root
z1 in F_p^*), level-0 read (e0, h0) with e0 >= 2 (so level-2 twist units are
NONTRIVIAL), state read (e1, h1, psi1) including the refinement corner
e1*g1 = 1.  w1/w2 are the GD23 SS1.2 development-min valuations; the level-2
residual read is GMN Def 2.19-2.21 at r = 2 (t1(i) = (s1(a_i) - l0*u_i)/e0,
l0*h0 == 1 mod e0; c_i = z1^t1(i) * R1(a_i)(z1)), transcribed from
/tmp/litunit/gmn.txt:1823-1906 this session.

The state standard lift is built in DEVELOPMENT form Phi2 = sum_k D_k Phi1^(e1 k),
D_k = chat_k * Phi0^(a_k) * pi^(b_k), a_k*h0 + b_k*e0 = (g1-k)*gamma2,
0 <= a_k < e0 (so deg D_k < deg Phi1 and b_k >= 0), two variants:
  TWIST-AWARE: chat_k lifts psi1_k * z1^(-t1(e1*k))  (residual-conformant);
  NAKED:       chat_k lifts psi1_k                    (no twist inversion).

PREREGISTERED PREDICTIONS (any violation of P1-P4 refutes the named claim):
  P1 (K1-clause):    every stride monomial D_k*Phi1^(e1 k) has w2 = gammahat2
                     = e1*g1*gamma2, and w2(Phi2) = gammahat2 -- BOTH variants.
                     0 violations expected.
  P2 (DEVID canary): w2(P) = min_k (w2(C_k) + k*gammahat2) over the
                     Phi2-development, random P -- BOTH variants (the (KPa)
                     degree-block consequence is twist-INsensitive).
                     0 violations expected.
  P3 (KPb, GMN face): the level-2 residual of the TWIST-AWARE lift equals
                     tau_g * psi1, tau_g = the TOP-stride twist (D_g = 1 is
                     forced by monicity, so the top twist cannot be inverted
                     away: this is exactly why (KPb) is a "~" statement, GMN
                     Def 2.12).  0 violations expected.  (Partially circular:
                     builder and checker share the twist formula; the
                     non-circular teeth are P1/P2/P4.)
  P4 (twist is load-bearing): at instances with a nontrivial twist pattern,
                     the NAKED lift's residual differs from psi1 (up to
                     scalar); we HUNT for an instance where the naked
                     residual is REDUCIBLE over F_p -- i.e. the naked lift
                     violates (KPa)+(KPirr) outright.  Expected: mismatches
                     occur, and at least one reducible naked residual is
                     found (if not, report honestly).
"""
import random, sys

random.seed(20260806)
INF = 10**9

def vp(n, p):
    if n == 0: return INF
    v = 0; n = abs(n)
    while n % p == 0: n //= p; v += 1
    return v

# ---- Z[x] polynomials as int lists (coeff of x^i) ----
def pnorm(A):
    A = list(A)
    while A and A[-1] == 0: A.pop()
    return A
def padd(A, B):
    n = max(len(A), len(B))
    return pnorm([(A[i] if i < len(A) else 0) + (B[i] if i < len(B) else 0) for i in range(n)])
def pmul(A, B):
    if not A or not B: return []
    out = [0]*(len(A)+len(B)-1)
    for i, a in enumerate(A):
        if a == 0: continue
        for j, b in enumerate(B):
            out[i+j] += a*b
    return pnorm(out)
def ppow(A, k):
    R = [1]
    for _ in range(k): R = pmul(R, A)
    return R
def pdivmod(A, B):
    # B monic
    A = list(A); Q = []
    while len(A) >= len(B) and A:
        c = A[-1]; d = len(A) - len(B)
        Q = padd(Q, [0]*d + [c])
        A = pnorm([A[i] - (c*B[i-d] if 0 <= i-d < len(B) else 0) for i in range(len(A))])
    return pnorm(Q), pnorm(A)
def dev(A, Phi):
    """Phi-adic development: list of coefficient polys, slot 0 first."""
    out = []
    A = pnorm(A)
    if not A: return []
    while A:
        A, r = pdivmod(A, Phi)
        out.append(r)
    return out

# ---- the tower: d0 = 1, g0 = 1 ----
def w0(A, p):
    A = pnorm(A)
    return INF if not A else min(vp(c, p) for c in A)

def w1(A, Phi0, e0, h0, p):
    A = pnorm(A)
    if not A: return INF
    return min(e0*w0(b, p) + t*h0 for t, b in enumerate(dev(A, Phi0)) if pnorm(b))

def w2(A, Phi0, Phi1, e0, h0, e1, gamma2, p):
    A = pnorm(A)
    if not A: return INF
    return min(e1*w1(c, Phi0, e0, h0, p) + j*gamma2
               for j, c in enumerate(dev(A, Phi1)) if pnorm(c))

def R1_at(a, Phi0, e0, h0, p, z1):
    """Level-1 residual of a (deg a < deg Phi1 = e0) read at its own
    lambda0-vertex; single coefficient (unique minimizing slot for slots
    < e0, gcd(e0,h0)=1); returns (s1(a), value in F_p)."""
    D = dev(a, Phi0)
    best, tstar = None, None
    for t, b in enumerate(D):
        if not pnorm(b): continue
        u = e0*w0(b, p) + t*h0
        if best is None or u < best:
            best, tstar = u, t
    b = D[tstar]                      # deg b < d0 = 1: a scalar
    c = b[0] // (p ** vp(b[0], p))    # unit part
    return tstar, c % p

def lvl2_residual(Phi2, Phi0, Phi1, e0, h0, e1, h1, gamma2, p, z1, l0):
    """GMN Def 2.19-2.21 at r=2: residual coefficients on the lambda2-side of
    Phi2's own polygon (initial abscissa s = least minimizing slot).
    Returns list of F_p coefficients c_{s+e1*k}, k = 0..d."""
    D = dev(Phi2, Phi1)
    w1Phi1 = e0*h0                    # g0 = 1: w1(Phi1) = e0*g0*h0
    pts = []
    for j, c in enumerate(D):
        if not pnorm(c): continue
        u = w1(c, Phi0, e0, h0, p) + j*w1Phi1   # u_j = v2(c_j phi2^j)
        pts.append((j, u))
    m = min(e1*u + j*h1 for j, u in pts)
    onside = sorted([(j, u) for j, u in pts if e1*u + j*h1 == m])
    s = onside[0][0]
    dstr = (onside[-1][0] - s) // e1
    coeffs = []
    for k in range(dstr + 1):
        j = s + e1*k
        hit = [u for jj, u in onside if jj == j]
        if not hit:
            coeffs.append(0); continue
        u = hit[0]
        s1a, r1 = R1_at(D[j], Phi0, e0, h0, p, z1)
        t1 = (s1a - l0*u)  # / e0 below; integrality asserted
        assert t1 % e0 == 0, "t1 not integral -- transcription error"
        t1 //= e0
        coeffs.append((pow(z1, t1 % (p-1) if p > 2 else t1 % 1 if False else t1 % (p-1) or (p-1), p) * r1) % p if p > 2 else (z1**abs(t1) * r1) % p)
    return s, coeffs

def zpow(z1, t1, p):
    """z1^t1 in F_p^*, t1 any sign."""
    e = t1 % (p - 1)
    return pow(z1, e, p)

# (replace the inline mess above with zpow)
def lvl2_residual2(Phi2, Phi0, Phi1, e0, h0, e1, h1, gamma2, p, z1, l0):
    D = dev(Phi2, Phi1)
    w1Phi1 = e0*h0
    pts = []
    for j, c in enumerate(D):
        if not pnorm(c): continue
        u = w1(c, Phi0, e0, h0, p) + j*w1Phi1
        pts.append((j, u))
    m = min(e1*u + j*h1 for j, u in pts)
    onside = sorted([(j, u) for j, u in pts if e1*u + j*h1 == m])
    s = onside[0][0]
    dstr = (onside[-1][0] - s) // e1
    coeffs = []
    for k in range(dstr + 1):
        j = s + e1*k
        hit = [u for jj, u in onside if jj == j]
        if not hit:
            coeffs.append(0); continue
        u = hit[0]
        s1a, r1 = R1_at(D[j], Phi0, e0, h0, p, z1)
        t1 = s1a - l0*u
        assert t1 % e0 == 0, "t1 not integral"
        coeffs.append((zpow(z1, t1 // e0, p) * r1) % p)
    return s, coeffs

def fp_factor_has_root_or_reducible(poly, p):
    """poly: list of F_p coeffs, monic, deg >= 1. Reducible over F_p?
    (deg <= 3: reducible iff it has a root; deg 4: root or two quadratics --
    we only use deg <= 3 in the hunt, plus deg 4 via root+pair check)."""
    d = len(poly) - 1
    if d <= 1: return False
    for r in range(p):
        if sum(c * pow(r, i, p) for i, c in enumerate(poly)) % p == 0:
            return True
    if d >= 4:
        # try factor into two monic quadratics (d == 4 only)
        if d == 4:
            for b in range(p):
                for c in range(p):
                    for e in range(p):
                        for f in range(p):
                            prod = [c*f, c*e + b*f, c + f + b*e, b + e, 1]
                            if all((prod[i] - poly[i]) % p == 0 for i in range(5)):
                                return True
    return False

def run():
    fails = {"P1": 0, "P2": 0, "P3": 0}
    naked_mismatch = 0
    naked_total_twisted = 0
    naked_reducible_found = []
    ninst = 0

    irr = {  # monic irreducibles over F_p with nonzero constant term, by (p, deg)
    }
    def irreducibles(p, g):
        if (p, g) in irr: return irr[(p, g)]
        out = []
        import itertools
        for tup in itertools.product(range(p), repeat=g):
            if tup[0] == 0: continue
            poly = list(tup) + [1]
            if not fp_factor_has_root_or_reducible(poly, p) if g > 1 else True:
                if g == 1:
                    out.append(poly)
                else:
                    # crude: no root => irreducible for deg 2,3
                    if g <= 3 and not any(
                        sum(c*pow(r, i, p) for i, c in enumerate(poly)) % p == 0
                        for r in range(p)):
                        out.append(poly)
        irr[(p, g)] = out
        return out

    for p in (2, 3, 5):
        for e0, h0 in ((2, 1), (2, 3), (3, 1), (3, 2)):
            from math import gcd
            if gcd(e0, h0) != 1: continue
            l0 = pow(h0, -1, e0)
            for z1 in range(1, p):
                Phi0 = [random.randrange(p), 1]          # x - a, d0 = 1
                # level-1 standard lift for psi0 = y - z1 (g0 = 1):
                # Phi1 = Phi0^{e0} + zhat1 * pi^{h0}  (KEY-g shape, k=0 term)
                zh = z1 if z1 else 1
                Phi1 = padd(ppow(Phi0, e0), [zh * p**h0])
                assert w1(Phi1, Phi0, e0, h0, p) == e0*h0
                for e1, h1 in ((1, 1), (1, 2), (2, 1), (3, 2)):
                    if gcd(e1, h1) != 1: continue
                    for g1 in (1, 2, 3):
                        cands = irreducibles(p, g1)
                        if not cands: continue
                        psi1 = random.choice(cands)
                        gamma2 = e1*e0*h0 + h1
                        ghat2 = e1*g1*gamma2
                        ninst += 1
                        # top-stride twist tau_g (D_g = 1: s1 = 0, w1 = 0)
                        u_top = e1*g1*e0*h0
                        assert (l0*u_top) % e0 == 0 or True
                        t1_top = (0 - l0*u_top)
                        assert t1_top % e0 == 0
                        tau_g = zpow(z1, t1_top // e0, p)
                        for variant in ("aware", "naked"):
                            # build D_k
                            Dks = {}
                            ok = True
                            for k in range(g1 + 1):
                                if psi1[k] % p == 0: continue
                                if k == g1:
                                    Dks[k] = [1]; continue
                                W = (g1 - k) * gamma2
                                a_k = (l0 * W) % e0
                                b_k = (W - a_k*h0) // e0
                                assert b_k >= 0
                                mono = pmul(ppow(Phi0, a_k), [p**b_k])
                                # twist of the STRIDE j = e1*k for this monomial:
                                u_j = W + e1*k*e0*h0
                                t1 = a_k - l0*u_j
                                assert t1 % e0 == 0
                                t1 //= e0
                                if variant == "aware":
                                    # invert the twist RELATIVE to the top stride
                                    cbar = (psi1[k] * tau_g * zpow(z1, -t1, p)) % p
                                else:
                                    cbar = psi1[k] % p
                                if cbar == 0: ok = False
                                Dks[k] = pmul([cbar], mono)
                            if not ok: continue
                            Phi2 = []
                            for k, Dk in Dks.items():
                                Phi2 = padd(Phi2, pmul(Dk, ppow(Phi1, e1*k)))
                            # P1: stride weights + w2(Phi2)
                            for k, Dk in Dks.items():
                                wm = w2(pmul(Dk, ppow(Phi1, e1*k)),
                                        Phi0, Phi1, e0, h0, e1, gamma2, p)
                                if wm != ghat2: fails["P1"] += 1
                            if w2(Phi2, Phi0, Phi1, e0, h0, e1, gamma2, p) != ghat2:
                                fails["P1"] += 1
                            # P2: DEVID at (w2, Phi2), random P
                            for _ in range(6):
                                P = [random.randrange(-p**3, p**3)
                                     for _ in range(random.randrange(1, 2*len(Phi2)))]
                                P = pnorm(P)
                                if not P: continue
                                lhs = w2(P, Phi0, Phi1, e0, h0, e1, gamma2, p)
                                rhs = min((w2(C, Phi0, Phi1, e0, h0, e1, gamma2, p)
                                           + kk*ghat2)
                                          for kk, C in enumerate(dev(P, Phi2))
                                          if pnorm(C))
                                if lhs != rhs: fails["P2"] += 1
                            # P3/P4: level-2 residual
                            s, coeffs = lvl2_residual2(Phi2, Phi0, Phi1, e0, h0,
                                                       e1, h1, gamma2, p, z1, l0)
                            if variant == "aware":
                                expect = [(tau_g * c) % p for c in psi1]
                                if s != 0 or coeffs != expect:
                                    fails["P3"] += 1
                            else:
                                # is the twist pattern nontrivial for this instance?
                                tw = set()
                                for k in range(g1 + 1):
                                    if psi1[k] % p == 0 or k == g1: continue
                                    W = (g1 - k)*gamma2
                                    a_k = (l0*W) % e0
                                    u_j = W + e1*k*e0*h0
                                    tw.add(zpow(z1, (a_k - l0*u_j)//e0, p))
                                nontriv = (len(tw - {1}) > 0)
                                if nontriv:
                                    naked_total_twisted += 1
                                    # compare up to scalar
                                    prop = False
                                    if s == 0 and len(coeffs) == g1 + 1 and coeffs[-1] != 0:
                                        lam = None; prop = True
                                        for i in range(g1 + 1):
                                            a, b = coeffs[i], psi1[i] % p
                                            if (a == 0) != (b == 0): prop = False; break
                                            if a and b:
                                                l = (a * pow(b, -1, p)) % p
                                                if lam is None: lam = l
                                                elif l != lam: prop = False; break
                                    if not prop:
                                        naked_mismatch += 1
                                        # normalize monic & test reducibility
                                        if s == 0 and len(coeffs) == g1 + 1 and coeffs[-1] % p:
                                            inv = pow(coeffs[-1], -1, p)
                                            mon = [(c*inv) % p for c in coeffs]
                                            if g1 >= 2 and fp_factor_has_root_or_reducible(mon, p):
                                                naked_reducible_found.append(
                                                    (p, e0, h0, z1, e1, h1, tuple(psi1), tuple(mon)))
    print(f"instances: {ninst}")
    print(f"P1 (stride/lift weights = gammahat2): {fails['P1']} violations")
    print(f"P2 (DEVID at the state key, both variants): {fails['P2']} violations")
    print(f"P3 (twist-aware lift residual == psi1): {fails['P3']} violations")
    print(f"P4 naked-lift contrast: {naked_mismatch}/{naked_total_twisted} "
          f"nontrivially-twisted instances have naked residual !~ psi1")
    print(f"P4 reducible naked residuals found: {len(naked_reducible_found)}")
    for t in naked_reducible_found[:5]:
        print("   e.g.", t)
    ok = (fails["P1"] == 0 and fails["P2"] == 0 and fails["P3"] == 0)
    print("GATE:", "PASS" if ok else "FAIL")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(run())
