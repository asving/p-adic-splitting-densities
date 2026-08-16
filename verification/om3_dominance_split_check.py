#!/usr/bin/env python3
"""OM-3 certification leg 1 (HYP.26 / blueprint CHAP-H §16 item 6): the dominance-region split.

CLAIM CERTIFIED (the §A theorem of docs/openmath-campaign/OM-3_count-layer_2026-08-16.md):
for an affine form d(t) = C + Σ B_i t_i with INTEGER coefficients on ℕ^r, the region
{t ∈ ℕ^r : d(t) ≥ 0} is a FINITE DISJOINT union of images of injective, monotone-nondegenerate
ℕ-affine maps φ : ℕ^k → ℕ^r ("pieces"); consequently the intersection of an A1Cell locus
(shifted product of arithmetic progressions) with {ν₁ ≥ ν₂} for ℕ-affine ν₁, ν₂ is such a union,
and strictly-positive exponent coefficients transport to every piece.

This script IMPLEMENTS the decomposition algorithm of the §A proof verbatim and verifies, by
exact integer enumeration on truncated windows (exhaustive within the window, with a soundness
argument for the parameter truncation given in `piece_points`):
  (1) COVERAGE:      union of piece images  ==  the region, inside the window;
  (2) DISJOINTNESS + INJECTIVITY: no point is generated twice (across or within pieces);
  (3) NONDEGENERACY: every piece-matrix column is nonzero (each parameter moves a coordinate);
  (4) TRANSPORT:     a strictly-positive affine exponent form pulled back through every piece
                     has strictly positive coefficients;
  (5) the AUTOMATIC-POSITIVITY assertions inside the algorithm (the proof's Lemma A.1) never
      fail on any constructed branch.

Battery: deterministic instances at r ≤ 3, coefficients in [−4, 4] (exercising the mod-B sub-box
split at B ∈ {2, 3, 4} and the bounded-fiber second induction at c ∈ {2, 3}), strides up to 3 and
nonzero offsets (the full A1Cell reduction), and the corpus's own 2SIDED instance
(ν₁ − ν₂ = w₂ − w₁ − 1, W-12 §S3.4) in both orientations.  Everything exact-integer; no q enters
(the statement is q-independent lattice combinatorics — the two-prime rule is vacuous here and the
regime diversity is carried by the coefficient/sign battery instead).

Exit 0 iff every check passes; prints a per-instance line and a final tally.
"""

from itertools import product
import sys

# ---------------------------------------------------------------------------------------------
# Affine forms over ℕ^k: (coeffs tuple of ints length k, const int).  Value on t ∈ ℕ^k.
# Pieces: affine maps ℕ^k → ℕ^r given by (matrix M: r rows × k cols of ℕ-ints, offset v ∈ ℕ^r).
# ---------------------------------------------------------------------------------------------


def aval(form, t):
    coeffs, const = form
    return const + sum(c * x for c, x in zip(coeffs, t))


def compose_form_piece(form, piece):
    """Pull an affine form on ℕ^r back through a piece (M, v): returns a form on ℕ^k."""
    coeffs, const = form
    M, off = piece
    r = len(off)
    k = len(M[0]) if M and r else (len(M[0]) if M else 0)
    k = len(M[0]) if r > 0 and len(M) > 0 else 0
    newconst = const + sum(coeffs[i] * off[i] for i in range(r))
    newcoeffs = tuple(sum(coeffs[i] * M[i][j] for i in range(r)) for j in range(k))
    return (newcoeffs, newconst)


def compose_pieces(outer, inner):
    """outer: ℕ^m → ℕ^r, inner: ℕ^k → ℕ^m  ⟹  ℕ^k → ℕ^r."""
    Mo, vo = outer
    Mi, vi = inner
    r, m = len(vo), len(vi)
    k = len(Mi[0]) if m > 0 and len(Mi) > 0 else 0
    off = tuple(vo[i] + sum(Mo[i][j] * vi[j] for j in range(m)) for i in range(r))
    M = [[sum(Mo[i][j] * Mi[j][l] for j in range(m)) for l in range(k)] for i in range(r)]
    return (M, off)


def ceil_div(a, b):
    return -((-a) // b)


# ---------------------------------------------------------------------------------------------
# The algorithm (the §A proof, constructively).
# ---------------------------------------------------------------------------------------------


def bounded_fiber(g, m0):
    """Decompose {(u, x) ∈ ℕ^k × ℕ : x ≤ g(u) + m0} (g with ℕ coefficients, m0 ≥ 0)
    into pieces χ : ℕ^j → ℕ^{k+1}.  Second induction of the §A proof (on the number of
    variables of g carrying a nonzero coefficient)."""
    coeffs, const = g
    k = len(coeffs)
    assert all(c >= 0 for c in coeffs) and const >= 0 and m0 >= 0, "Lemma A.1 violated (fiber)"
    # find last variable with nonzero coefficient
    last = max((j for j in range(k) if coeffs[j] > 0), default=None)
    if last is None:
        # constant bound: x ∈ {0..const+m0}; pieces (u ↦ (u, j0)), dim k
        out = []
        for j0 in range(const + m0 + 1):
            M = [[1 if jj == i else 0 for jj in range(k)] for i in range(k)] + [[0] * k]
            out.append((M, tuple([0] * k) + (j0,)))
        return out
    c = coeffs[last]
    # variables after `last` are coefficient-0: they ride along free.  Reduce to vars 0..last.
    free_tail = k - 1 - last  # number of free variables strictly after `last` (before x)
    g0 = (coeffs[:last], const)  # g = g0(u') + c·v, v = u_last
    out = []
    # Region 1: x ≤ g0(u') + m0, v (and tail) free.
    for chi in bounded_fiber(g0, m0):
        # chi : ℕ^j → ℕ^{last+1}  (u' coords 0..last-1, then x)
        Mc, vc = chi
        j = len(Mc[0]) if len(Mc) > 0 and len(vc) > 0 else 0
        # target coords: u' (last), v (1), tail (free_tail), x (1); params: chi-params + v + tail
        rows = []
        # u' rows from chi
        for i in range(last):
            rows.append(list(Mc[i]) + [0] * (1 + free_tail))
        # v row: new free param
        rows.append([0] * j + [1] + [0] * free_tail)
        # tail rows: new free params
        for tji in range(free_tail):
            rows.append([0] * (j + 1) + [1 if z == tji else 0 for z in range(free_tail)])
        # x row from chi's last row
        rows.append(list(Mc[last]) + [0] * (1 + free_tail))
        off = tuple(vc[:last]) + (0,) * (1 + free_tail) + (vc[last],)
        out.append((rows, off))
    # Region 2: x = g0(u') + m0 + c·w + j0 + 1,  v = w + 1 + z,  for j0 ∈ {0..c−1}.
    g0c, g0const = g0
    for j0 in range(c):
        # params: u' (last of them), w, z, tail
        j = last
        rows = []
        for i in range(last):  # u' coords: identity
            rows.append([1 if jj == i else 0 for jj in range(j)] + [0, 0] + [0] * free_tail)
        # v row: w + 1 + z
        rows.append([0] * j + [1, 1] + [0] * free_tail)
        # tail rows
        for tji in range(free_tail):
            rows.append([0] * (j + 2) + [1 if z == tji else 0 for z in range(free_tail)])
        # x row: g0(u') + c·w + (m0 + j0 + 1)
        rows.append([g0c[i] for i in range(j)] + [c, 0] + [0] * free_tail)
        off = (0,) * last + (1,) + (0,) * free_tail + (g0const + m0 + j0 + 1,)
        out.append((rows, off))
    return out


def decompose(d, r):
    """Decompose {t ∈ ℕ^r : d(t) ≥ 0} into pieces (M, v) : ℕ^k → ℕ^r.  Main induction on r."""
    coeffs, const = d
    assert len(coeffs) == r
    if r == 0:
        return [([], ())] if const >= 0 else []
    B = coeffs[-1]
    dprime = (coeffs[:-1], const)
    out = []
    if B == 0:
        for M, v in decompose(dprime, r - 1):
            k = len(M[0]) if len(M) > 0 and r - 1 > 0 else 0
            rows = [row + [0] for row in M] + [[0] * k + [1]]
            out.append((rows, tuple(v) + (0,)))
        return out
    if B > 0:
        # P-side: d'(t') ≥ 0 ⟹ every x works.
        for M, v in decompose(dprime, r - 1):
            k = len(M[0]) if len(M) > 0 and r - 1 > 0 else 0
            rows = [row + [0] for row in M] + [[0] * k + [1]]
            out.append((rows, tuple(v) + (0,)))
        # N-side: −d'−1 ≥ 0.  Fiber x ≥ ⌈e/B⌉ with e = −d'∘ψ (ℕ-coeffs, ≥ 1 — Lemma A.1).
        negd = (tuple(-c for c in coeffs[:-1]), -const - 1)
        for psi in decompose(negd, r - 1):
            Mp, vp = psi
            k = len(Mp[0]) if len(Mp) > 0 and r - 1 > 0 else 0
            e = compose_form_piece((tuple(-c for c in coeffs[:-1]), -const), psi)
            ec, e0 = e
            assert all(c >= 0 for c in ec) and e0 >= 1, "Lemma A.1 violated (N-side)"
            # sub-box t'_i = B·s_i + ρ_i
            for rho in product(range(B), repeat=k):
                E0 = e0 + sum(ec[i] * rho[i] for i in range(k))
                m0 = ceil_div(E0, B)
                # piece params: s (k of them), y;  t' = B·s + ρ;  x = Σ ec_i s_i + m0 + y
                sub = ([[B if jj == i else 0 for jj in range(k)] for i in range(k)], rho)
                box = compose_pieces(psi, sub)  # ℕ^k → ℕ^{r−1}
                Mb, vb = box
                rows = [list(Mb[i]) + [0] for i in range(r - 1)] + [[ec[i] for i in range(k)] + [1]]
                off = tuple(vb) + (m0,)
                out.append((rows, off))
        return out
    # B < 0: b = −B; only d' ≥ 0 contributes; fiber x ≤ ⌊e/b⌋ with e = d'∘ψ.
    b = -B
    for psi in decompose(dprime, r - 1):
        Mp, vp = psi
        k = len(Mp[0]) if len(Mp) > 0 and r - 1 > 0 else 0
        e = compose_form_piece(dprime, psi)
        ec, e0 = e
        assert all(c >= 0 for c in ec) and e0 >= 0, "Lemma A.1 violated (P-side, B<0)"
        for rho in product(range(b), repeat=k):
            E0 = e0 + sum(ec[i] * rho[i] for i in range(k))
            m0 = E0 // b
            g = (tuple(ec), m0)  # bound: x ≤ Σ ec_i s_i + m0  (in sub-box coords s)
            sub = ([[b if jj == i else 0 for jj in range(k)] for i in range(k)], rho)
            box = compose_pieces(psi, sub)  # s ↦ t' ∈ ℕ^{r−1}
            for chi in bounded_fiber((tuple(ec), 0), m0):
                # chi : ℕ^j → ℕ^{k+1}, coords (s, x)
                Mc, vc = chi
                j = len(Mc[0]) if len(Mc) > 0 and len(vc) > 0 else 0
                # target: (box(s), x)
                Mb, vb = box
                rows = []
                for i in range(r - 1):
                    rows.append([sum(Mb[i][l] * Mc[l][jj] for l in range(k)) for jj in range(j)])
                off_top = tuple(vb[i] + sum(Mb[i][l] * vc[l] for l in range(k)) for i in range(r - 1))
                rows.append(list(Mc[k]))
                out.append((rows, off_top + (vc[k],)))
    return out


# ---------------------------------------------------------------------------------------------
# Verification harness.
# ---------------------------------------------------------------------------------------------


def piece_points(piece, W, r):
    """All points of the piece image inside the window {0..W}^r.
    SOUND TRUNCATION: monotone nondegeneracy (checked) means every parameter j has some
    coordinate i with M[i][j] ≥ 1, so a parameter value > W pushes coordinate i beyond W;
    hence enumerating parameters in {0..W}^k finds EVERY in-window image point."""
    M, v = piece
    k = len(M[0]) if len(M) > 0 and r > 0 else 0
    pts = []
    for t in product(range(W + 1), repeat=k):
        p = tuple(v[i] + sum(M[i][j] * t[j] for j in range(k)) for i in range(r))
        if all(0 <= c <= W for c in p):
            pts.append(p)
    return pts


def check_instance(name, d, r, W, expfail=False):
    pieces = decompose(d, r)
    # (3) nondegeneracy
    for M, v in pieces:
        k = len(M[0]) if len(M) > 0 and r > 0 else 0
        for j in range(k):
            assert any(M[i][j] > 0 for i in range(r)), f"{name}: degenerate column"
        assert all(all(x >= 0 for x in row) for row in M) and all(x >= 0 for x in v), \
            f"{name}: non-ℕ piece data"
    # (1)+(2)
    gen = []
    for pc in pieces:
        gen.extend(piece_points(pc, W, r))
    region = [t for t in product(range(W + 1), repeat=r) if aval(d, t) >= 0]
    ok_cover = sorted(gen) == sorted(set(gen)) == sorted(region)
    ok_disj = len(gen) == len(set(gen))
    # (4) transport of a strictly positive exponent form
    ell = (tuple([1 + (i % 3) for i in range(r)]), 2)
    ok_transport = True
    for pc in pieces:
        lc, l0 = compose_form_piece(ell, pc)
        if not all(c > 0 for c in lc):
            ok_transport = False
    ok = ok_cover and ok_disj and ok_transport
    tag = "OK " if ok else "FAIL"
    print(f"[{tag}] {name}: r={r} d={d} pieces={len(pieces)} region|W={len(region)} "
          f"gen={len(gen)} uniq={len(set(gen))} transport={'ok' if ok_transport else 'BAD'}")
    return ok


def check_cell_instance(name, offsets, strides, nu1, nu2, r, W):
    """The full A1 reduction: locus {p = o + s·t} ∩ {ν₁(p) ≥ ν₂(p)} — decompose in t-space
    via d(t) = ν₁(o+st) − ν₂(o+st), compose with t ↦ o + s·t, verify in p-space."""
    c1, k1 = nu1
    c2, k2 = nu2
    dco = tuple((c1[i] - c2[i]) * strides[i] for i in range(r))
    dct = (k1 - k2) + sum((c1[i] - c2[i]) * offsets[i] for i in range(r))
    d = (dco, dct)
    pieces = decompose(d, r)
    cellmap = ([[strides[i] if j == i else 0 for j in range(r)] for i in range(r)], tuple(offsets))
    ppieces = [compose_pieces(cellmap, pc) for pc in pieces]
    gen = []
    for pc in ppieces:
        gen.extend(piece_points(pc, W, r))
    region = [p for p in product(range(W + 1), repeat=r)
              if all((p[i] - offsets[i]) % strides[i] == 0 and p[i] >= offsets[i] for i in range(r))
              and aval(nu1, p) >= aval(nu2, p)]
    ok = sorted(gen) == sorted(set(gen)) == sorted(region) and len(gen) == len(set(gen))
    print(f"[{'OK ' if ok else 'FAIL'}] {name}: cell o={offsets} s={strides} pieces={len(ppieces)} "
          f"region|W={len(region)} gen={len(gen)}")
    return ok


def main():
    okall = True
    W2, W3 = 12, 8
    # r = 1: signs and magnitudes
    for B in [-4, -3, -2, -1, 0, 1, 2, 3, 4]:
        for C in [-7, -3, -1, 0, 2, 5]:
            okall &= check_instance(f"r1 B={B} C={C}", ((B,), C), 1, 20)
    # r = 2: all sign patterns, magnitudes to 4 (sub-box + bounded-fiber stress)
    grid2 = [(1, -1, 0), (1, -1, -1), (-1, 1, -1), (2, -3, 1), (-3, 2, -2), (3, -2, -5),
             (-2, -3, 7), (2, 3, -9), (-4, 3, 2), (3, -4, 6), (-1, -1, 5), (4, -3, -2),
             (0, -2, 5), (-3, 0, 4), (2, 0, -3), (0, 0, -1), (0, 0, 0), (-2, 4, -7)]
    for (b1, b2, C) in grid2:
        okall &= check_instance(f"r2 ({b1},{b2};{C})", ((b1, b2), C), 2, W2)
    # r = 3: mixed signs
    grid3 = [(1, -1, 1, 0), (2, -3, 1, -2), (-1, 2, -2, 1), (-2, -1, 3, -1),
             (3, -2, -1, 4), (-1, -1, -1, 6), (1, 2, -3, -4), (-3, 1, 2, 0)]
    for (b1, b2, b3, C) in grid3:
        okall &= check_instance(f"r3 ({b1},{b2},{b3};{C})", ((b1, b2, b3), C), 3, W3)
    # The corpus's 2SIDED instance (W-12 §S3.4): ν₁ = w₂, ν₂ = w₁ + 1 and its complement,
    # on the trivial cell and on a strided/shifted cell.
    okall &= check_cell_instance("2SIDED region", (0, 0), (1, 1), ((0, 1), 0), ((1, 0), 1), 2, W2)
    okall &= check_cell_instance("2SIDED complement", (0, 0), (1, 1), ((1, 0), 0), ((0, 1), 0), 2, W2)
    okall &= check_cell_instance("2SIDED strided", (1, 2), (2, 3), ((0, 1), 0), ((1, 0), 1), 2, W2)
    okall &= check_cell_instance("mixed cell r2", (2, 1), (3, 2), ((2, 1), 1), ((1, 3), 4), 2, 14)
    okall &= check_cell_instance("mixed cell r3", (1, 0, 2), (2, 1, 3),
                                 ((1, 2, 1), 0), ((2, 1, 2), 3), 3, W3)
    # visibility-max motivation: ν = max(ν₁, ν₂) region pair partitions the cell — check the two
    # dominance regions of a pair tile the locus disjointly (ν₁ ≥ ν₂  ⊔  ν₂ ≥ ν₁ + 1).
    o, s = (0, 1), (1, 2)
    n1, n2 = ((2, 1), 0), ((1, 2), 1)
    c1o = check_cell_instance("max-split A (ν₁≥ν₂)", o, s, n1, n2, 2, W2)
    c2o = check_cell_instance("max-split B (ν₂≥ν₁+1)", o, s, (n2[0], n2[1]), (n1[0], n1[1] + 1), 2, W2)
    okall &= c1o and c2o
    print("\nRESULT:", "ALL CHECKS PASS" if okall else "FAILURES PRESENT")
    sys.exit(0 if okall else 1)


if __name__ == "__main__":
    main()
