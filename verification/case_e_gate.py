#!/usr/bin/env python3
"""case_e_gate.py — the note §7 Case E gate: n = 4, p = 2, deg φ = 2 descent (the D1 probe).

The MINIMAL class-3 stratum: root read f̄ = ḡ², ḡ = x² + x + 1 (the unique irreducible
quadratic over F₂); φ-adic development f = φ² + a₁·φ + a₀ (φ = x² + x + 1 the canonical
lift, deg aᵢ ≤ 1); stratum conditions v(a₀) = 1 EXACT with unit F₄-digit, v(a₁) ≥ 1
(v = Gauss valuation = min coefficient v₂). Leaf (e,f) = (2,2), σ = {(2,2)}.

GATE 1 (count, the decisive D1-marginal probe): the census is run in ORIGINAL coordinates
— iterate all monic quartics mod 2^N and perform GENUINE φ-adic division — so the count
tests the unipotent-bijection mechanism, not the ledger tautologically. Expected mass:
(Q−1)·Q^{−3} with Q = q² = 4, i.e. 3/64 exactly at every N ≥ 2 (N = 2: 12 of 256).

GATE 2 (type): for every stratum member (N small) / samples (N larger), a RIGOROUS
{(2,2)}-certificate: Hensel-factor f = G·Ḡ over the unramified quadratic W = ℚ₂(ω)
(Galois-ring arithmetic mod 2^N; the mod-2 factors (x−ω)², (x−ω̄)² are coprime), then
 (i) G's constant term ≡ ω² mod 2 ∉ F₂ ⟹ f has no ℚ₂-quadratic factor with G in its
     W-refinement; G, Ḡ irreducible over W (from (ii)) ⟹ no linear/quadratic ℚ₂-factors
     ⟹ f irreducible over ℚ₂;
 (ii) L = W(√disc G) RAMIFIED over W ⟹ (e,f) = (2,2). 2-ADIC classifier (the odd-p
     "v(disc) odd ⟺ ramified" is FALSE at p = 2 — first version of this oracle had that
     bug; its own FAILs caught it): v odd → ramified; v even → normalize the unit part
     u' ≡ 1 mod 2 (every F₄ residue is a square: odd group order), then u' ≡ 3 mod 4 →
     ramified; u' = 1+4t → Tr_{F₄/F₂}(t̄) = 1 unramified (type (1,4): FAIL) / = 0 square
     (G splits: FAIL); u' ≡ 1 mod 8 square. [(4,1) would keep f irreducible over W.]

Run: python3 case_e_gate.py [Nmax]   (default 5; N=6 adds ~2^24 divisions).
"""
import sys
from fractions import Fraction as F


def phi_divide(coeffs, M):
    """f = (x^4 + c3 x^3 + c2 x^2 + c1 x + c0); divide twice by phi = x^2+x+1 mod M.
    Returns (a1, a0) with f = phi^2 + a1*phi + a0, deg ai <= 1, coefficients mod M.
    Division: for f = sum c_i x^i (monic deg 4), q = f div phi, r = f mod phi."""
    c3, c2, c1, c0 = coeffs
    # first division: f = q1 * phi + a0, q1 monic quadratic q1 = x^2 + q1_1 x + q1_0
    q1_1 = (c3 - 1) % M
    q1_0 = (c2 - 1 - q1_1) % M
    r1_1 = (c1 - q1_1 - q1_0) % M          # coefficient of x in a0
    r1_0 = (c0 - q1_0) % M                 # constant of a0
    # second: q1 = 1*phi + a1 -> a1 = q1 - phi = (q1_1 - 1) x + (q1_0 - 1)
    a1_1 = (q1_1 - 1) % M
    a1_0 = (q1_0 - 1) % M
    return (a1_1, a1_0), (r1_1, r1_0)


def v2_pair(pair, cap):
    """Gauss valuation of a deg<=1 poly with coefficients mod 2^cap (min of coefficient v2)."""
    v = cap
    for u in pair:
        if u == 0:
            continue
        w = 0
        while u % 2 == 0:
            u //= 2
            w += 1
        v = min(v, w)
    return v


def in_stratum(coeffs, N):
    M = 1 << N
    (a1_1, a1_0), (a0_1, a0_0) = phi_divide(coeffs, M)
    # root read f-bar = phi-bar^2  <=>  a1, a0 both == 0 mod 2
    if (a1_1 | a1_0 | a0_1 | a0_0) & 1:
        return False
    # v(a0) = 1 exact (unit F4 digit at height 1)
    if v2_pair((a0_1, a0_0), N) != 1:
        return False
    # v(a1) >= 1 already checked by the mod-2 test
    return True


# ---------- Galois ring W = Z2[omega]/(omega^2+omega+1), elements (a, b) = a + b*omega ----
def gr_mul(x, y, M):
    a, b = x
    c, d = y
    # (a+b w)(c+d w) = ac + (ad+bc) w + bd w^2 ;  w^2 = -w - 1
    return ((a * c - b * d) % M, (a * d + b * c - b * d) % M)


def gr_sub(x, y, M):
    return ((x[0] - y[0]) % M, (x[1] - y[1]) % M)


def gr_v2(x, N):
    v = N
    for u in x:
        if u == 0:
            continue
        w = 0
        while u % 2 == 0:
            u //= 2
            w += 1
        v = min(v, w)
    return v


def poly_mul(P, Q, M):
    R = [(0, 0)] * (len(P) + len(Q) - 1)
    for i, p in enumerate(P):
        for j, q in enumerate(Q):
            m = gr_mul(p, q, M)
            R[i + j] = ((R[i + j][0] + m[0]) % M, (R[i + j][1] + m[1]) % M)
    return R


def poly_divmod_monic(P, D, M):
    """P, D lists of GR coefficients (low->high), D monic. Returns (Q, R)."""
    P = list(P)
    dd = len(D) - 1
    Q = [(0, 0)] * (len(P) - dd)
    for i in range(len(P) - 1, dd - 1, -1):
        c = P[i]
        Q[i - dd] = c
        for j in range(dd + 1):
            m = gr_mul(c, D[j], M)
            P[i - dd + j] = ((P[i - dd + j][0] - m[0]) % M, (P[i - dd + j][1] - m[1]) % M)
    return Q, P[:dd]


def gr_inv_unit(x, M, N):
    """inverse of a unit in the Galois ring, by Newton iteration from the F4 inverse."""
    a, b = x[0] % 2, x[1] % 2
    inv_tbl = {(1, 0): (1, 0), (0, 1): (1, 1), (1, 1): (0, 1)}  # F4 inverses
    y = inv_tbl[(a, b)]
    for _ in range(N.bit_length() + 1):
        # y <- y*(2 - x*y)
        xy = gr_mul(x, y, M)
        t = ((2 - xy[0]) % M, (-xy[1]) % M)
        y = gr_mul(y, t, M)
    return y


def hensel_factor_over_W(coeffs, N):
    """f monic quartic over Z2 -> (G, H) monic quadratics over GR(2^N,2) with f = G*H,
    G == (x-w)^2, H == (x-w*)^2 mod 2. Naive quadratic-convergence lift."""
    M = 1 << N
    c3, c2, c1, c0 = [c % M for c in coeffs]
    f = [(c0, 0), (c1, 0), (c2, 0), (c3, 0), (1, 0)]
    # mod 2: (x-w)^2 = x^2 - 2wx + w^2 = x^2 + w^2 = x^2 + (w+1)  [mod 2]
    G = [(1, 1), (0, 0), (1, 0)]   # (w+1) + 0*x + x^2
    H = [(1, 1), (0, 0), (1, 0)]   # placeholder; w*^2 = w*+1 = (0,1)+(1,0)=... compute:
    # w* = w+1 (the conjugate); w*^2 = w* + 1 = w + 2 = w  -> H = x^2 + w
    H = [(0, 1), (0, 0), (1, 0)]
    for _ in range(N + 2):
        FF = poly_mul(G, H, M)
        E = [gr_sub(f[i] if i < len(f) else (0, 0), FF[i] if i < len(FF) else (0, 0), M)
             for i in range(5)]
        if all(e == (0, 0) for e in E):
            break
        # solve G*dH + H*dG = E with deg dG,dH <= 1 via Bezout mod 2 then lift greedily:
        # simple approach: dH = (E * Ginv) mod H etc. Use: since G,H coprime, correct via
        # dG = E mod G * (H^{-1} mod G), dH = E mod H * (G^{-1} mod H)
        _, EmodG = poly_divmod_monic(E, G, M)
        _, EmodH = poly_divmod_monic(E, H, M)
        _, HmodG = poly_divmod_monic(H, G, M)
        _, GmodH = poly_divmod_monic(G, H, M)
        dG = lin_mul_inv(EmodG, HmodG, G, M, N)
        dH = lin_mul_inv(EmodH, GmodH, H, M, N)
        G = [((G[i][0] + (dG[i][0] if i < 2 else 0)) % M,
              (G[i][1] + (dG[i][1] if i < 2 else 0)) % M) for i in range(3)]
        H = [((H[i][0] + (dH[i][0] if i < 2 else 0)) % M,
              (H[i][1] + (dH[i][1] if i < 2 else 0)) % M) for i in range(3)]
    return G, H


def lin_mul_inv(E, A, MOD, M, N):
    """(E * A^{-1}) mod MOD, all deg<=1 over GR, MOD monic quadratic.
    A must be a unit in GR[x]/MOD (true here: A = H mod G has unit... ) — implement via
    2x2 linear solve: find X (deg<=1) with A*X == E mod MOD."""
    # brute 2x2 solve over the ring: X = x1*t + x0; A*X mod MOD is GR-linear in (x0, x1).
    # columns: A*1 mod MOD and A*t mod MOD
    col0 = poly_divmod_monic(poly_mul(A, [(1, 0)], M), MOD, M)[1]
    col1 = poly_divmod_monic(poly_mul(A, [(0, 0), (1, 0)], M), MOD, M)[1]
    while len(col0) < 2: col0.append((0, 0))
    while len(col1) < 2: col1.append((0, 0))
    # solve [col0 col1] (x0,x1)^T = E over GR (2 GR-equations, 2 GR-unknowns) — Cramer
    det = gr_sub(gr_mul(col0[0], col1[1], M), gr_mul(col1[0], col0[1], M), M)
    detinv = gr_inv_unit(det, M, N)
    e0 = E[0] if len(E) > 0 else (0, 0)
    e1 = E[1] if len(E) > 1 else (0, 0)
    x0 = gr_mul(gr_sub(gr_mul(e0, col1[1], M), gr_mul(col1[0], e1, M), M), detinv, M)
    x1 = gr_mul(gr_sub(gr_mul(col0[0], e1, M), gr_mul(e0, col0[1], M), M), detinv, M)
    return [x0, x1]


def type_certificate(coeffs, N):
    """Return ('(2,2)', info) if certified; ('FAIL', reason) otherwise.
    2-adic-correct ramification classifier for L = W(sqrt(disc G)):
      v(disc) odd                                   -> ramified -> (2,2)
      v even, unit part u' == 3 mod 4 (normalized)  -> ramified -> (2,2)
      v even, u' = 1+4t, Tr_{F4/F2}(t) = 1          -> unramified -> (1,4): FAIL
      v even, u' = 1+4t, Tr(t) = 0 (or u'==1 mod 8) -> square -> G splits: FAIL
    Unit normalization: every F4 residue is a square (odd group order); y = ubar^2 is
    the square root of ubar in F4; u' = u * (y^{-1})^2 == 1 mod 2."""
    M = 1 << N
    G, H = hensel_factor_over_W(coeffs, N)
    FF = poly_mul(G, H, M)
    c3, c2, c1, c0 = [c % M for c in coeffs]
    f = [(c0, 0), (c1, 0), (c2, 0), (c3, 0), (1, 0)]
    if FF != f:
        return ('FAIL', 'hensel did not converge')
    B, C = G[1], G[0]
    if (C[0] % 2, C[1] % 2) not in [(1, 1), (0, 1)]:
        return ('FAIL', 'constant term of G unexpectedly rational mod 2')
    B2 = gr_mul(B, B, M)
    disc = ((B2[0] - 4 * C[0]) % M, (B2[1] - 4 * C[1]) % M)
    v = gr_v2(disc, N)
    if v >= N - 4:
        return ('FAIL', f'v(disc) = {v} too deep for certainty at N = {N}')
    if v % 2 == 1:
        return ('(2,2)', f'v(disc)={v} odd')
    u = (disc[0] >> v, disc[1] >> v)  # unit part, exact in GR(2^{N-v})
    Mv = 1 << (N - v)
    # square root of ubar in F4 is ubar^2 (Frobenius); lift and invert
    ybar = gr_mul((u[0] % 2, u[1] % 2), (u[0] % 2, u[1] % 2), 2)
    y = (ybar[0], ybar[1])
    yinv = gr_inv_unit(y, Mv, N)
    up = gr_mul(u, gr_mul(yinv, yinv, Mv), Mv)   # u' == 1 mod 2
    d1 = ((up[0] - 1) % Mv, up[1] % Mv)
    vd = gr_v2(d1, N - v)
    if vd == 1:
        return ('(2,2)', f'v(disc)={v} even, unit class 3 mod 4 (ramified)')
    if vd >= 3:
        return ('FAIL', f'disc a square in W (u\' == 1 mod 8): G splits')
    # vd == 2: u' = 1 + 4t
    t = ((d1[0] >> 2) % 2, (d1[1] >> 2) % 2)
    tr = (t[0] + t[1] * 0) % 2  # Tr(a + b*omega) over F4->F2: Tr(1)=0, Tr(omega)=1
    # careful: Tr(x) = x + x^2; Tr(1) = 0, Tr(omega) = omega + omega^2 = -1 = 1,
    # Tr(omega+1) = Tr(omega) + Tr(1) = 1. So Tr(a+b*omega) = b + (a? no):
    # Tr(a + b w) = a*Tr(1) + b*Tr(w) = b  ... plus a*0 = b? Tr(1)=1+1=0 yes. => tr = b.
    tr = t[1] % 2
    if tr == 1:
        return ('FAIL', f'unramified quadratic over W (Tr=1): type (1,4), not (2,2)')
    return ('FAIL', f'disc square class trivial (Tr=0): G splits over W')


def main(Nmax):
    print('GATE 1 — count (original coordinates, genuine phi-adic division):')
    all_ok = True
    for N in range(2, Nmax + 1):
        M = 1 << N
        cnt = 0
        members = []
        for c3 in range(M):
            for c2 in range(M):
                for c1 in range(M):
                    for c0 in range(M):
                        if in_stratum((c3, c2, c1, c0), N):
                            cnt += 1
                            if len(members) < 64:
                                members.append((c3, c2, c1, c0))
        mass = F(cnt, M ** 4)
        ok = mass == F(3, 64)
        all_ok = all_ok and ok
        print(f'  N={N}: count {cnt} of {M**4}, mass {mass} '
              f'{"== 3/64 OK" if ok else "MISMATCH vs 3/64"}')
        if N == 2:
            ok12 = cnt == 12
            all_ok = all_ok and ok12
            print(f'        note anchor N=2: 12 expected, got {cnt} '
                  f'[{"OK" if ok12 else "FAIL"}]')
    print('\nGATE 2 — type certificates over W = Q2(omega), N = 8 arithmetic:')
    # certify every N=2 stratum member, lifted with zero higher digits, PLUS random lifts
    Ncert = 8
    M2 = 4
    checked = passed = 0
    import random
    random.seed(20260723)
    for c3 in range(M2):
        for c2 in range(M2):
            for c1 in range(M2):
                for c0 in range(M2):
                    if not in_stratum((c3, c2, c1, c0), 2):
                        continue
                    for trial in range(3):  # zero-lift + 2 random lifts per member
                        if trial == 0:
                            cf = (c3, c2, c1, c0)
                        else:
                            cf = tuple(c + 4 * random.randrange(1 << (Ncert - 2))
                                       for c in (c3, c2, c1, c0))
                        if not in_stratum(cf, Ncert):
                            continue  # random lift left the stratum (fine)
                        checked += 1
                        verdict, info = type_certificate(cf, Ncert)
                        if verdict == '(2,2)':
                            passed += 1
                        else:
                            print(f'  FAIL at {cf}: {info}')
    print(f'  certified {passed}/{checked} sampled stratum members as (e,f) = (2,2)')
    all_ok = all_ok and (checked > 0 and passed == checked)
    print('\nVERDICT:', 'CASE E GATE PASSES' if all_ok else 'CASE E GATE FAILS')
    return 0 if all_ok else 1


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 4))
