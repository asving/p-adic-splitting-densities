#!/usr/bin/env python3
"""GENTOW6 passPE3 fresh instrument (hostile verifier; acceptance attempt).
Own exact-integer core; NO import of any sealed runner; gp/PARI = the
decorrelated oracle. Frames DISJOINT from every prior leg: the level-1 key is
Phi' = x^2 - 6 over Q3 (e1 = 2, f1 = 1, h = 1) whose stage residue
eta = res(x^2/3) = 2 != 1 -- the FIRST eta != 1 frame in the GENTOW6 arc
(every sealed/PE1 frame: eta = 1 per the S5 GAUGE AXIS row; PE2's eta != 1
frames were f1 = 2 cert frames, not tie frames).

LEG A -- THE GAUGE-LIVE TIE (PE2's suggested surface; first anywhere).
Genre: Q3, Phi' = x^2-6, inner side slope 5/2 (u2 = 5, l = e2 = 2).
Keys: Phi2_L = Phi'^2 - 9x (class L: f2 = 1, D2 = 4, E2 = 10, psi_L deg 1);
Phi2_C = Phi'^4 - 243 (class C: f2 = 2, D2 = 8, E2 = 20, psi_C deg 2).
Member f = g1*g2*B_C*S, deg 18: g1 = Phi2_L + 27, g2 = Phi2_L + 81 (class L,
m_L = 2), B_C = Phi2_C + 3^6 (class C, m_C = 1), sibling S = Phi' - 27
(slope-6 side, no class).
Coherent residual convention DERIVED BY HAND for this frame (graded algebra
F_3[X,P], X = gr(x) height 1, P = gr(3) height 2, X^2 = 2P from x^2 = 6 mod
Phi'): R_coh(T) = sum_k d_k * 2^(w_k) T^k, d_k the plain residue of the
height-y_k monomial of A_{i0+2k}, w_k = #(x-carries left of position k) =
floor(k/2) if the left-endpoint height y_0 is even, ceil(k/2) if odd. This
matches the erratum-59c1966 gauge on keys (chat_t = lift(c_t eta^{W(t)}),
W(t) = floor((f2-t) i(u2)/e1)) up to the degree/multiplicity-preserving
rescale T -> eta*T; all preregistered checks are stated in THIS convention
and the tie content (degrees, multiplicities, mu2*, PARI degree sums) is
twist-invariant.
PREREGISTERED (P-A1..P-A9 + tooth):
P-A1 gp: Phi', Phi2_L, Phi2_C each irreducible over Q3; poldisc(f) != 0.
P-A2 level-1 hull of f = (0,26)-(1,20)-(9,0) exactly (dv = 2*v3 + xdeg).
P-A3 key/block residuals (monicized, my convention): R(Phi2_L) = T+1 =: psi_L
     (raw 2T-1, w = ceil); R(Phi2_C) = T^2+1 =: psi_C (raw 2T^2+0T-1,
     w = floor); R(g1) = R(g2) = T+1; R(B_L=g1*g2) = (T+1)^2 with raw
     digits d = (2,1,1); R(B_C) = T^2+1 (raw d = (2,0,1)).
P-A4 THE TIE INPUT: monicized R_coh(f) = (T+1)^2 (T^2+1); raw digits
     d_k = gamma*(1,2,1,1,1) for one gamma in {1,2}; j-pattern (0,1,0,1,0),
     w = (0,0,1,1,2).
P-A5 composed read of f at Phi2_L: pins (p_0..p_4) = (53,37,25,15,5);
     slopes > T2 = E2_L = 10 have total length 2 => mu2*(L) = 2 = m_L.
P-A6 composed read of f at Phi2_C: pins (p_0,p_1,p_2) = (49,25,5); slope
     above T2 = E2_C = 20 has length 1 => mu2*(C) = 1 = m_C.
P-A7 gp factorpadic(f,3): degrees {4,4,8,2}; poldisc != 0.
P-A8 class degree sums via resultant valuations: v3(Res(g1,Phi2_L)) = 12,
     v3(Res(g2,Phi2_L)) = 16 (per-root 3,4 > 2.5 = E2_L/4: IN class L);
     v3(Res(B_C,Phi2_C)) = 48 (per-root 6 > 5 = E2_C/4: IN class C); class
     degree sums 4+4 = D2_L*m_L = 8 and 8 = D2_C*m_C = 8 -- LEMMA 6.1's
     degree display, dual oracle.
P-A9 cross-exclusions EXACT: v3(Res(g1,Phi2_C)) = v3(Res(g2,Phi2_C)) = 20
     (per-root 5 = floor, NOT >); v3(Res(B_C,Phi2_L)) = 20 (per-root 5/2);
     v3(Res(S,Phi2_L)) = 5, v3(Res(S,Phi2_C)) = 10 (sibling AT the floors:
     per-root 5/2 and 5). [run-1 RED disclosed: the seal wrote the S/Phi2_C
     TOTAL as 5 -- a verifier-side arithmetic slip (per-root 5 x 2 roots =
     10); hand-traced 27^4 - 243 = 531198 = 2*3^5*..., per-root floor value
     5 = E2_C/4 EXACTLY as predicted; exclusion verdict unchanged.]
T-GAUGE (tooth): the eta-blind residual R_naive(T) = sum d_k T^k (w == 0)
     has R_naive(1) = 0 mod 3 while (psi_L^2 psi_C)(1) = 2 != 0; its
     monicization != (T+1)^2(T^2+1): an eta-blind reader breaks EXACTLY here
     -- the wrap units are load-bearing at this frame (first gauge-live tie).

LEG B -- LEMMA 6.4 + THE RIDER CODOMAIN at fresh D2-nmod grids (deg-18
member, never used in any leg). Grid L (key Phi2_L, D2 = 4): n = 18,
M = 4, 20 slots, 18 mod 4 = 2 != 3 -> above-top count 1 (slot degree 19).
Grid C (key Phi2_C, D2 = 8): M = 2, 24 slots, 18 mod 8 = 2 != 7 ->
above-top count 5 (degrees 19..23) -- a FIVE-above-top instance of the
rider's exact-count formula D2-1-(n mod D2), new value.
PREREGISTERED (P-B1..P-B6 + tooth):
P-B1 both grids: slot-degree map bijective; above-top counts 1 and 5.
P-B2 reconstruction exact on both grids.
P-B3 above-top digits all 0; slot-degree-18 digit = 1 (both grids).
P-B4 TRI diagonal (grid L): perturbing [f]_d by eps in {1,-1} for d in
     0..17 shifts the slot-degree-d digit by exactly eps and leaves digits
     at slot degrees > d byte-unchanged (36 members, aggregated).
P-B5 band-1 (grid L, N = 3, cap e1e2*N = 12): 8 seeded random 3^3-lifts:
     digits congruent mod 27, in-window (v < 3) valuations equal, p_4 = 5
     stable; undercut lift f + 27*Phi2_L^3 moves p_3 15 -> exactly 12
     while p_4 = 5 holds and other digits are byte-identical.
P-B6 c_g = p_{mu2*} = 25 (grid L pins from P-A5).
T-COD2 (tooth): tampering one above-top digit (each grid) reconstructs to
     degree > 18: the tuple is NOT in the corrected codomain's image.

LEG C -- THE GAUGE-LIVE CERTIFICATE at the in-coordinate top corner.
Genre (Q3, Phi' = x^2-6, e2 = 2, f2 = 1, u2 = 5, E2 = 10, delta = 1,
THETA_0 = 21): Phi2 = Phi'^2 - 9c*x for c in {1,2}; f = Phi2^2 (mu2 = 2).
i_0 = 1, 2*i_0 = 2 = D' (regime-2 boundary 2i_{t*} = D' exactly);
certificate slot (j*,a*,b*) = (0, 0, 1): b* = 1 = e2f2 - 1 the TOP
in-coordinate corner (PE1's corner was (0,0) via quotient transfer; the
sealed battery rows sit at b* interior or a* > 0) -- and the FIRST
eta != 1 certificate row anywhere in the arc (S5 exposed face: the S3
digit VALUES at eta != 1).
PREREGISTERED (P-C1..P-C5 + teeth), hand-derived: dev(Phi2^2) =
Y^4 - 18c x Y^2 + 81c^2 Y + 486c^2 (single x-carry 81c^2 x^2 =
81c^2 Phi' + 486c^2); honest read DRAIN (C_2 = 1, C_1 = C_0 = 0); shadow
Ghat_2 = 1, Ghat_1 = 0, Ghat_0 = 81c^2 * Y exactly: slot (0,1) digit
81c^2, v = 4 = 2a_{t*}, unit res(digit/3^4) = c^2 mod 3, wrap unit = 1
measured, height 16 + w(0,1) = 16 + 5 = 21 = THETA_0 EXACTLY (attainment
ON the floor); every other Ghat_0/Ghat_1 slot = 0.
P-C5 gp: Phi2 irreducible over Q3 at c = 1 and c = 2 (genuine keys).
T-CERTV2 (teeth): the a/b-swapped slot (1,0) carries digit 0 (a mutant
     reading the certificate at the swapped slot finds nothing); v = 3
     and height = 22 mutants both fail (v = 4, height = 21 exact).
"""

import subprocess

CHECKS = []


def check(name, ok):
    CHECKS.append((name, bool(ok)))
    print(("PASS" if ok else "FAIL"), name)


def v3(n):
    n = abs(n)
    assert n != 0
    v = 0
    while n % 3 == 0:
        n //= 3
        v += 1
    return v


# ---------- exact Z[x] arithmetic (low-first coefficient lists)
def trim(u):
    while len(u) > 1 and u[-1] == 0:
        u = u[:-1]
    return u


def pmul(u, v):
    out = [0] * (len(u) + len(v) - 1)
    for i, a in enumerate(u):
        for j, b in enumerate(v):
            out[i + j] += a * b
    return trim(out)


def padd(u, v):
    n = max(len(u), len(v))
    return trim([(u[i] if i < len(u) else 0) + (v[i] if i < len(v) else 0)
                 for i in range(n)])


def pdivmod(u, m):
    assert m[-1] == 1
    u = list(u)
    q = [0] * max(1, len(u) - len(m) + 1)
    while len(u) >= len(m) and any(u):
        d = len(u) - len(m)
        c = u[-1]
        q[d] += c
        for i, b in enumerate(m):
            u[d + i] -= c * b
        u = trim(u)
        if u == [0]:
            break
    return trim(q), trim(u)


# ---------- F_3[T] helpers
def f3(u):
    return trim([c % 3 for c in u])


def f3mul(u, v):
    return f3(pmul(u, v))


def f3monic(u):
    u = f3(u)
    lc = u[-1]
    inv = {1: 1, 2: 2}[lc]
    return f3([c * inv for c in u])


def f3eval(u, t):
    return sum(c * t**i for i, c in enumerate(u)) % 3


# ---------- level-1 dev (Phi'-adic) + side residual, THIS frame (dv=2v3+j)
PHIP = [-6, 0, 1]                       # x^2 - 6 over Q3, eta = 2


def phidev(f):
    A, rest = [], list(f)
    while True:
        rest, a = pdivmod(rest, PHIP)
        A.append(a)
        if rest == [0]:
            break
    return A


def coeff_height(a):
    """dv-height of an x-poly deg<2: min over monomials of 2*v3 + xdeg."""
    hs = []
    if len(a) > 0 and a[0] != 0:
        hs.append(2 * v3(a[0]))
    if len(a) > 1 and a[1] != 0:
        hs.append(2 * v3(a[1]) + 1)
    return min(hs) if hs else None


def digit_at(a, y):
    """plain residue of a's monomial at dv-height exactly y (0 if none)."""
    j = y % 2
    if len(a) > j and a[j] != 0 and 2 * v3(a[j]) + j == y:
        return (a[j] // 3 ** ((y - j) // 2)) % 3
    return 0


def hull(points):
    """lower convex hull of (i, h) points, left-to-right."""
    pts = sorted(points)
    out = []
    for p in pts:
        while len(out) >= 2 and (
            (out[-1][1] - out[-2][1]) * (p[0] - out[-1][0])
                >= (p[1] - out[-1][1]) * (out[-1][0] - out[-2][0])):
            out.pop()
        out.append(p)
    return out


def side_residual(f, i0, y0, length):
    """coherent residual on the slope-5/2 side from (i0,y0), l=2.
    returns (raw digits d, coherent coeffs R_coh over F_3, w list)."""
    A = phidev(f)
    d, w, carries = [], [], 0
    for k in range(length // 2 + 1):
        i, y = i0 + 2 * k, y0 - 5 * k
        a = A[i] if i < len(A) else [0]
        d.append(digit_at(a, y))
        w.append(carries)
        if y % 2 == 1:                  # this position carries an x; the
            carries += 1                # NEXT step wraps (X*X = 2P)
    Rc = f3([d[k] * 2 ** w[k] for k in range(len(d))])
    return d, Rc, w


# ---------- composed digits on the (j,a,b) grid + pins
def digits_grid(f, Phi2, e2f2):
    Dp, D2 = 2, 2 * e2f2
    n = len(f) - 1
    M = n // D2
    C, rest = [], list(f)
    for _ in range(M + 1):
        rest, cj = pdivmod(rest, Phi2)
        C.append(cj)
    assert rest == [0]
    dig = {}
    for j in range(M + 1):
        cur = C[j]
        for b in range(e2f2):
            cur, cb = pdivmod(cur, PHIP)
            for a in range(Dp):
                dig[(j, a, b)] = cb[a] if a < len(cb) else 0
        assert cur == [0]
    return dig, M


def pins(dig, M, u2=5):
    """p_j = slot-min of e1e2*v3(c) + w(a,b), w = a*e2*h + b*u2 = 2a + 5b."""
    out = []
    for j in range(M + 1):
        hs = [4 * v3(c) + 2 * a + 5 * b
              for (jj, a, b), c in dig.items() if jj == j and c != 0]
        out.append(min(hs) if hs else None)
    return out


def reconstruct(dig, Phi2, e2f2):
    tot = [0]
    for (j, a, b), c in dig.items():
        term = [0] * a + [c]
        for _ in range(b):
            term = pmul(term, PHIP)
        for _ in range(j):
            term = pmul(term, Phi2)
        tot = padd(tot, term)
    return tot


# ---------- gp oracle
def gp(cmd):
    r = subprocess.run(["gp", "-q", "-f"], input=cmd, capture_output=True,
                       text=True, timeout=300)
    return r.stdout.strip()


def poly_gp(f):
    return "+".join(f"({c})*x^{i}" for i, c in enumerate(f) if c != 0)


# ============================ LEG A ============================
print("== LEG A: the gauge-live tie (eta = 2, f1 = 1) ==")
Phi2L = padd(pmul(PHIP, PHIP), [0, -9])          # Phi'^2 - 9x
Phi2C = padd(pmul(pmul(PHIP, PHIP), pmul(PHIP, PHIP)), [-243])
g1 = padd(Phi2L, [27])
g2 = padd(Phi2L, [81])
BL = pmul(g1, g2)
BC = padd(Phi2C, [729])
S = padd(PHIP, [-27])
f = pmul(pmul(BL, BC), S)
check("A0 deg f = 18", len(f) - 1 == 18)

# P-A1 keys genuine (gp)
for tag, P in (("Phi'", PHIP), ("Phi2_L", Phi2L), ("Phi2_C", Phi2C)):
    out = gp(f"F=factorpadic({poly_gp(P)},3,60); print(matsize(F)[1])")
    check(f"A1 {tag} irreducible over Q3", out == "1")

# P-A2 level-1 hull
A = phidev(f)
pts = [(i, coeff_height(a)) for i, a in enumerate(A)
       if coeff_height(a) is not None]
H = hull(pts)
check("A2 level-1 hull = (0,26)-(1,20)-(9,0)",
      H == [(0, 26), (1, 20), (9, 0)])

# P-A3 key/block residuals (my coherent convention)
dL, RL, wL = side_residual(Phi2L, 0, 5, 2)
check("A3 R(Phi2_L) raw = 2T-1, monic = T+1 (w=ceil: j0=1)",
      f3(dL) == [2, 1] and wL == [0, 1] and f3monic(RL) == [1, 1])
psiL = f3monic(RL)
dC, RC, wC = side_residual(Phi2C, 0, 10, 4)
check("A3 R(Phi2_C) raw d = (2,0,1), monic = T^2+1 (w=floor: j0=0)",
      f3(dC) == [2, 0, 1] and wC == [0, 0, 1]
      and f3monic(RC) == [1, 0, 1])
psiC = f3monic(RC)
for tag, g in (("g1", g1), ("g2", g2)):
    _, R, _ = side_residual(g, 0, 5, 2)
    check(f"A3 R({tag}) monic = T+1", f3monic(R) == psiL)
dBL, RBL, _ = side_residual(BL, 0, 10, 4)
check("A3 R(B_L) raw d = (2,1,1), monic = (T+1)^2",
      f3(dBL) == [2, 1, 1] and f3monic(RBL) == f3mul(psiL, psiL))
dBC, RBC, _ = side_residual(BC, 0, 10, 4)
check("A3 R(B_C) raw d = (2,0,1), monic = T^2+1",
      f3(dBC) == [2, 0, 1] and f3monic(RBC) == psiC)

# P-A4 the tie input on f's side (abscissas 1..9, y0 = 20)
df, Rf, wf = side_residual(f, 1, 20, 8)
target = f3mul(f3mul(psiL, psiL), psiC)          # (T+1)^2 (T^2+1)
check("A4 w-pattern = (0,0,1,1,2)", wf == [0, 0, 1, 1, 2])
gamma = Rf[-1]                                    # leading unit
check("A4 monicized R_coh(f) = (T+1)^2(T^2+1), gamma in {1,2}",
      f3monic(Rf) == target and gamma in (1, 2))
check("A4 raw digits d = gamma*(1,2,1,1,1)",
      f3(df) == f3([gamma * c for c in [1, 2, 1, 1, 1]]))

# T-GAUGE tooth
Rnaive = f3(df)
check("T-GAUGE naive residual has root 1 while (psiL^2 psiC)(1) = 2 != 0",
      f3eval(Rnaive, 1) == 0 and f3eval(target, 1) == 2)
check("T-GAUGE monicized naive != (T+1)^2(T^2+1)",
      f3monic(Rnaive) != target)

# P-A5/P-A6 composed reads (normalization-free) => the tie
digL, ML = digits_grid(f, Phi2L, 2)
pL = pins(digL, ML)
check("A5 pins at Phi2_L = (53,37,25,15,5)", pL == [53, 37, 25, 15, 5])
hullL = hull(list(enumerate(pL)) + [(4.5, 0)])
mu2L = 0
for (x1, y1), (x2, y2) in zip(hullL, hullL[1:]):
    if (y1 - y2) / (x2 - x1) > 10:                # T2 = E2_L = 10
        mu2L += x2 - x1
check("A5 THE TIE at class L: mu2*(L) = 2 = m_L", mu2L == 2)
digC, MC = digits_grid(f, Phi2C, 4)
pC = pins(digC, MC)
check("A6 pins at Phi2_C = (49,25,5)", pC == [49, 25, 5])
hullC = hull(list(enumerate(pC)) + [(2.25, 0)])
mu2C = 0
for (x1, y1), (x2, y2) in zip(hullC, hullC[1:]):
    if (y1 - y2) / (x2 - x1) > 20:                # T2 = E2_C = 20
        mu2C += x2 - x1
check("A6 THE TIE at class C: mu2*(C) = 1 = m_C", mu2C == 1)

# P-A7 PARI factor degrees
out = gp(f"F=factorpadic({poly_gp(f)},3,80);"
         "print(vecsort(vector(matsize(F)[1],k,poldegree(F[k,1]))));"
         f"print(valuation(poldisc({poly_gp(f)}),3)>=0)")
check("A7 factorpadic degrees {2,4,4,8}", out.splitlines()[0]
      == "[2, 4, 4, 8]")
out = gp(f"print(poldisc({poly_gp(f)})!=0)")
check("A7 poldisc(f) != 0", out == "1")

# P-A8/P-A9 resultant class sums + exact cross-exclusions
def resv(g, P):
    out = gp(f"print(valuation(polresultant({poly_gp(g)},{poly_gp(P)}),3))")
    return int(out)

check("A8 v3Res(g1,Phi2_L) = 12 (per-root 3 > 2.5: IN)",
      resv(g1, Phi2L) == 12)
check("A8 v3Res(g2,Phi2_L) = 16 (per-root 4 > 2.5: IN)",
      resv(g2, Phi2L) == 16)
check("A8 v3Res(B_C,Phi2_C) = 48 (per-root 6 > 5: IN)",
      resv(BC, Phi2C) == 48)
check("A8 class degree sums: 4+4 = D2_L*m_L, 8 = D2_C*m_C",
      4 + 4 == 4 * 2 and 8 == 8 * 1)
check("A9 v3Res(g1,Phi2_C) = 20 (per-root 5 = floor: OUT)",
      resv(g1, Phi2C) == 20)
check("A9 v3Res(g2,Phi2_C) = 20 (per-root 5 = floor: OUT)",
      resv(g2, Phi2C) == 20)
check("A9 v3Res(B_C,Phi2_L) = 20 (per-root 5/2: OUT)",
      resv(BC, Phi2L) == 20)
check("A9 sibling at the floors: v3Res(S,Phi2_L) = 5 (per-root 5/2), "
      "v3Res(S,Phi2_C) = 10 (per-root 5)",
      resv(S, Phi2L) == 5 and resv(S, Phi2C) == 10)

# ============================ LEG B ============================
print("== LEG B: LEMMA 6.4 + rider codomain at the fresh member ==")
for tag, Phi2, e2f2, above_n in (("gridL", Phi2L, 2, 1),
                                 ("gridC", Phi2C, 4, 5)):
    D2 = 2 * e2f2
    dig, M = digits_grid(f, Phi2, e2f2)
    degs = sorted(j * D2 + b * 2 + a for (j, a, b) in dig)
    check(f"B1 {tag} slot-degree map bijective onto 0..{(M+1)*D2-1}",
          degs == list(range((M + 1) * D2)))
    above = [s for s in dig if s[0] * D2 + s[2] * 2 + s[1] > 18]
    check(f"B1 {tag} above-top count = D2-1-(18 mod D2) = {above_n}",
          len(above) == D2 - 1 - 18 % D2 == above_n)
    check(f"B2 {tag} reconstruction exact",
          reconstruct(dig, Phi2, e2f2) == f)
    top = [s for s in dig if s[0] * D2 + s[2] * 2 + s[1] == 18][0]
    check(f"B3 {tag} above-top digits all 0; slot-degree-18 digit = 1",
          all(dig[s] == 0 for s in above) and dig[top] == 1)
    bad = dict(dig)
    bad[above[0]] = 1
    check(f"T-COD2 {tag} tampered above-top tuple reconstructs off-degree",
          len(reconstruct(bad, Phi2, e2f2)) - 1 > 18)

digL, ML = digits_grid(f, Phi2L, 2)
sd = {s: s[0] * 4 + s[2] * 2 + s[1] for s in digL}
ok_tri = True
for d in range(18):
    for eps in (1, -1):
        g = list(f)
        g[d] += eps
        dg, _ = digits_grid(g, Phi2L, 2)
        for s in digL:
            want = digL[s] + (eps if sd[s] == d else 0) \
                if sd[s] <= d else digL[s]
            if sd[s] >= d and dg[s] != want:
                ok_tri = False
check("B4 TRI diagonal exact across 36 perturbed members (grid L)", ok_tri)

import random
random.seed(20260810)
ok_cong, ok_win, ok_pin = True, True, True
for _ in range(8):
    lift = [27 * random.randint(-4, 4) for _ in range(18)] + [0]
    fl = padd(f, lift)
    dl, _ = digits_grid(fl, Phi2L, 2)
    for s in digL:
        if (dl[s] - digL[s]) % 27 != 0:
            ok_cong = False
        if digL[s] != 0 and v3(digL[s]) < 3:
            if dl[s] == 0 or v3(dl[s]) != v3(digL[s]):
                ok_win = False
    if pins(dl, ML)[4] != 5:
        ok_pin = False
check("B5 8 random 3^3-lifts: digits congruent mod 27", ok_cong)
check("B5 in-window (v<3) valuations equal on the lifts", ok_win)
check("B5 below-cap pin p_4 = 5 stable on the lifts (cap 12)", ok_pin)
fu = padd(f, pmul([27], pmul(Phi2L, pmul(Phi2L, Phi2L))))
du, _ = digits_grid(fu, Phi2L, 2)
pu = pins(du, ML)
check("B5 undercut f + 27*Phi2_L^3: p_3 15 -> 12 = e1e2*N exactly, "
      "p_4 = 5 held", pu[3] == 12 and pu[4] == 5 and pL[3] == 15)
check("B5 undercut touches only slot (3,0,0): others byte-identical",
      all(du[s] == digL[s] for s in digL if s != (3, 0, 0))
      and du[(3, 0, 0)] == digL[(3, 0, 0)] + 27)
check("B6 c_g = p_mu2* = 25", pL[2] == 25)

# ============================ LEG C ============================
print("== LEG C: gauge-live certificate at the (0, e2f2-1) corner ==")


def ydivmod(F, K, e2f2):
    """division in (O[x]/Phi')[Y]: F, K lists of x-polys (low Y first),
    K monic in Y; coefficients reduced mod Phi'."""
    F = [list(c) for c in F]
    while len(F) > 0 and trim(F[-1]) == [0]:
        F.pop()
    q = [[0]] * max(1, len(F) - len(K) + 1)
    q = [list(c) for c in q]
    while len(F) >= len(K):
        d = len(F) - len(K)
        c = F[-1]
        q[d] = padd(q[d], c)
        for i, b in enumerate(K):
            F[d + i] = padd(F[d + i], pmul([-1], pmul(c, b)))
            _, F[d + i] = pdivmod(F[d + i], PHIP)
        while len(F) > 0 and trim(F[-1]) == [0]:
            F.pop()
    while len(F) < len(K) - 1:
        F.append([0])
    return q, F


for c in (1, 2):
    Phi2 = padd(pmul(PHIP, PHIP), [0, -9 * c])
    out = gp(f"F=factorpadic({poly_gp(Phi2)},3,60); print(matsize(F)[1])")
    check(f"C5 c={c}: Phi2 = Phi'^2-{9*c}x irreducible over Q3 (key)",
          out == "1")
    f2sq = pmul(Phi2, Phi2)
    # honest read: DRAIN
    _, r0 = pdivmod(f2sq, Phi2)
    q1, _ = pdivmod(f2sq, Phi2)
    _, r1 = pdivmod(q1, Phi2)
    check(f"C2 c={c}: honest read DRAIN (C_0 = C_1 = 0)",
          r0 == [0] and r1 == [0])
    # dev over the grid: list of x-polys per Y-power
    F, rest = [], list(f2sq)
    while True:
        rest, a = pdivmod(rest, PHIP)
        F.append(a)
        if rest == [0]:
            break
    want = [[486 * c * c], [81 * c * c], [0, -18 * c], [0], [1]]
    check(f"C1 c={c}: dev(Phi2^2) = Y^4 - 18cx Y^2 + 81c^2 Y + 486c^2",
          [trim(x) for x in F] == [trim(x) for x in want])
    # shadow: divide by K2 = Y^2 - 9cx twice over O[x]/Phi'
    K2 = [[0, -9 * c], [0], [1]]
    q, G0 = ydivmod(F, K2, 2)
    q2, G1 = ydivmod(q, K2, 2)
    check(f"C3 c={c}: Ghat_2 = 1, Ghat_1 = 0",
          [trim(x) for x in q2] == [[1]]
          and all(trim(x) == [0] for x in G1))
    dig0 = {(a, b): (G0[b][a] if b < len(G0) and a < len(G0[b]) else 0)
            for a in range(2) for b in range(2)}
    check(f"C3 c={c}: Ghat_0 slot (0,1) digit = 81c^2 = {81*c*c}, "
          "other slots 0",
          dig0[(0, 1)] == 81 * c * c
          and all(dig0[s] == 0 for s in dig0 if s != (0, 1)))
    dgt = dig0[(0, 1)]
    check(f"C4 c={c}: v = 4 = 2a_t*, unit = c^2 mod 3 (wrap unit 1), "
          "height 16+5 = 21 = THETA_0 EXACT",
          v3(dgt) == 4 and (dgt // 81) % 3 == (c * c) % 3
          and 4 * v3(dgt) + 2 * 0 + 5 * 1 == 21)
    check(f"T-CERTV2 c={c}: swapped slot (1,0) empty; v = 3 mutant and "
          "height-22 mutant both fail",
          dig0[(1, 0)] == 0 and v3(dgt) != 3
          and 4 * v3(dgt) + 5 != 22)

n_fail = sum(1 for _, ok in CHECKS if not ok)
print(f"\n=== PE3 FRESH VERDICT: {'GREEN' if n_fail == 0 else 'RED'} -- "
      f"{len(CHECKS)} checks, {n_fail} violations "
      f"(teeth: T-GAUGE x2, T-COD2 x2, T-CERTV2 x2) ===")
raise SystemExit(1 if n_fail else 0)
