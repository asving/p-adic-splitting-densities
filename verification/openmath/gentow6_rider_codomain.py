#!/usr/bin/env python3
"""GENTOW6 rider (post-PE2) — the LEMMA GENTOW-6.4(a) codomain correction,
machine leg. Exact integer polynomial arithmetic; self-contained (no import
of any sealed runner); frames = the S6.2 caplemma frames, members verbatim.

DERIVATION UNDER TEST (from (a)'s own triangular display, not from the PE2
report): the digit grid (j <= M = floor(n/D2), a < D', b < e2f2) has
(M+1)*D2 slots at slot degrees 0..(M+1)*D2-1, while monic f of degree n has
digits [f]_0..[f]_n only. Since c_{j,a,b} = [f]_{slotdeg} + O-comb of
strictly-higher [f]_{d'}, every ABOVE-TOP slot (slot degree > n) is FORCED
to 0 and the slot-degree-n digit is FORCED to 1. Corrected codomain: digit
tuples mod pi^N SUPPORTED ON SLOT DEGREES <= n, top digit pinned to 1
(above-top digits pinned to 0). Above-top slots exist iff
n mod D2 != D2 - 1 — at BOTH partial frames (n = 10, 12-slot grids: 1 slot
each) AND the full-side power member (n = 8: 3 slots).

PREREGISTERED PREDICTIONS
P-R1 grid: slot-degree map (j,a,b) -> j*D2 + b*D' + a bijects the grid onto
     0..(M+1)*D2-1; above-top count = D2 - 1 - (n mod D2): FRAME-P 1,
     FRAME-P2 1, FRAME-F 3.
P-R2 reconstruction: sum c_{j,a,b} x^a Phi'^b Phi2^j == f, each frame.
P-R3 forced zeros: every above-top digit == 0; slot-degree-n digit == 1.
P-R4 FORCED means forced: for eps = +/-1 at each degree d in 0..n-1 (2n
     perturbed monic members per frame), above-top digits still all 0, top
     still 1 (the free coordinates are exactly slot degrees < n).
TOOTH T-COD: a tuple with a nonzero above-top digit reconstructs to a
     polynomial of degree > n — such a tuple is NOT in the image (the
     sealed codomain wording over-counts; the corrected one does not).
"""

CHECKS = []


def check(name, ok):
    CHECKS.append((name, bool(ok)))
    print(("PASS" if ok else "FAIL"), name)


# ---- exact Z[x] arithmetic: polys as coefficient lists, low degree first
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


def trim(u):
    while len(u) > 1 and u[-1] == 0:
        u = u[:-1]
    return u


def pdivmod(u, m):
    """u = q*m + r, m MONIC; exact over Z."""
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


def digits(f, Phi2, Phip, Dp, e2f2):
    """composed digits c[(j,a,b)] on the FULL grid j<=M, a<Dp, b<e2f2."""
    D2 = Dp * e2f2
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
            cur, cb = pdivmod(cur, Phip)
            for a in range(Dp):
                dig[(j, a, b)] = cb[a] if a < len(cb) else 0
        assert cur == [0]
    return dig, M


def reconstruct(dig, Phi2, Phip, Dp, e2f2, M):
    tot = [0]
    for (j, a, b), c in dig.items():
        term = [0] * a + [c]
        for _ in range(b):
            term = pmul(term, Phip)
        for _ in range(j):
            term = pmul(term, Phi2)
        tot = padd(tot, term)
    return tot


def run_frame(tag, Phip, Phi2, f, Dp, e2f2, n_expect):
    D2 = Dp * e2f2
    n = len(f) - 1
    check(f"{tag} member degree n = {n_expect}", n == n_expect)
    dig, M = digits(f, Phi2, Phip, Dp, e2f2)
    # P-R1 grid census
    degs = sorted(j * D2 + b * Dp + a for (j, a, b) in dig)
    check(f"{tag} P-R1 slot-degree map bijective onto 0..{(M+1)*D2-1}",
          degs == list(range((M + 1) * D2)))
    above = [(j, a, b) for (j, a, b) in dig if j * D2 + b * Dp + a > n]
    check(f"{tag} P-R1 above-top count = D2-1-(n mod D2) = "
          f"{D2 - 1 - n % D2}", len(above) == D2 - 1 - n % D2)
    # P-R2 reconstruction
    check(f"{tag} P-R2 reconstruction exact",
          reconstruct(dig, Phi2, Phip, Dp, e2f2, M) == trim(list(f)))
    # P-R3 forced zeros + top pin
    check(f"{tag} P-R3 above-top digits all 0 ({len(above)} slots)",
          all(dig[s] == 0 for s in above))
    top = [s for (s) in dig if s[0] * D2 + s[2] * Dp + s[1] == n]
    check(f"{tag} P-R3 slot-degree-n digit = 1", dig[top[0]] == 1)
    # P-R4 forced under every monic perturbation at degrees < n
    ok = True
    for d in range(n):
        for eps in (1, -1):
            g = list(f)
            g[d] += eps
            dg, _ = digits(g, Phi2, Phip, Dp, e2f2)
            ok &= all(dg[s] == 0 for s in above) and dg[top[0]] == 1
    check(f"{tag} P-R4 above-top zeros + top pin FORCED across "
          f"{2*n} perturbed members", ok)
    # T-COD tooth: tamper an above-top digit -> reconstructs off-degree
    if above:
        bad = dict(dig)
        bad[above[0]] = 1
        r = reconstruct(bad, Phi2, Phip, Dp, e2f2, M)
        check(f"{tag} T-COD tampered above-top tuple leaves the member set "
              f"(degree {len(r)-1} > {n})", len(r) - 1 > n)


# ---- FRAME-P (partial, p = 3): Phi' = x^2-3, Phi2 = Phi'^2 - 9x,
#      f = (Phi2^2 + 81*Phi')*(Phi' - 27), deg 10
Phip = [-3, 0, 1]
Phi2 = padd(pmul(Phip, Phip), [0, -9])
f = pmul(padd(pmul(Phi2, Phi2), pmul([81], Phip)), padd(Phip, [-27]))
run_frame("FRAME-P", Phip, Phi2, f, 2, 2, 10)

# ---- FRAME-P2 (partial, p = 2, FAM-B genre): Phi' = x^2-2,
#      Phi2 = Phi'^2 - 2x*Phi' - 8, f = (Phi2^2 + 2^6*x)*(Phi' - 8), deg 10
Phip = [-2, 0, 1]
Phi2 = padd(padd(pmul(Phip, Phip), pmul([0, -2], Phip)), [-8])
f = pmul(padd(pmul(Phi2, Phi2), [0, 64]), padd(Phip, [-8]))
run_frame("FRAME-P2", Phip, Phi2, f, 2, 2, 10)

# ---- FRAME-F (full-side, FAM-B genre): f = Phi2^2 + 2^6*x, deg 8
f = padd(pmul(Phi2, Phi2), [0, 64])
run_frame("FRAME-F", Phip, Phi2, f, 2, 2, 8)

n_fail = sum(1 for _, ok in CHECKS if not ok)
print(f"\nTOTAL {len(CHECKS)} checks, {n_fail} violations "
      f"(tooth T-COD x3 included)")
raise SystemExit(1 if n_fail else 0)
