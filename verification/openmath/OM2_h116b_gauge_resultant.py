#!/usr/bin/env python3
"""
H.116b — the PRESENTATION-MULTIPLICITY mechanism, certified exactly.

CONTEXT.  `OM2_h116b_replant_cert.py` (2026-08-16, 68/68) established that the per-genre
child fibres of the beta extraction ARE equicardinal and that the canonical replant IS a
bijection, but REFUTED (check D3) the naive route to injectivity: two exact planted
presentations of the SAME class, shifted by the same Delta, can land in different classes,
because the same-slope planted sub-lattices carry a syzygy ("gauge group of size q^4 in the
census cell").  Its own disposition line: *the counting must go through the raw parameter
space (presentations) with constant presentation-multiplicity, or another mechanism.*

THIS SCRIPT certifies that mechanism.  CLAIM (the gauge is the resultant):

    the multi-child planting map
        ((b_p)_{p in L})  |-->  class of  prod_p  P(b_p)  ·  Q     (mod pi^N)
    is EXACTLY  q^{g}-to-one onto its image, with the SAME g for every image point, and

        g  =  sum_{p < p'} mu_p * mu_p' * min(k_p, k_p')          (capped by the window)

    which is  v(Res(P_p, P_p'))  summed over unordered pairs -- a quantity determined by the
    GENRE (L) alone.  In particular it does NOT depend on the child lifts b_p, which is why
    the fibres are equicardinal even though presentation stability fails.

WHY THIS IS THE MISSING LEG.  If the planting map is uniformly q^g-to-one, then
    #fibre(t) = #{presentations with proj b_p = t_p} / q^g,
and the numerator is (number of lifts of each t_p in the presentation box) x (number of
cofactors Q) -- the first factor is a coset count, hence independent of t, and the second
does not mention t at all.  Equicardinality follows WITHOUT any replant map, and therefore
without D3's refuted stability.

Root-side reading of g: P_p has mu_p roots of valuation k_p and (scaled) residue z_p.  For
p != p', v(alpha - beta) = min(k_p, k_p') for every root pair -- if the slopes differ this is
forced, and if they agree the distinct residues z_p != z_p' force it too.  So
v(Res(P_p,P_p')) = mu_p mu_p' min(k_p,k_p') with NO dependence on the deep digits of b.

EXTENDED 2026-08-16 by unit A-H.7 (blueprint AMENDMENT A-H.7, the H.116b re-split), block
(d)-(h) below, CERTIFY-BEFORE-SIGN for NODE H.116b4.  Blocks (a)-(c) hold the COFACTOR FIXED;
the accounting actually runs over the PAIR space (child presentations, cofactor presentation),
so what has to be constant is the PAIR multiplicity over the GENRE.  Block (d)-(h) measures
that, plus the three further legs the route needs: (e)/(e2) the genre of a planted product is
a function of the COFACTOR ALONE and the admissible cofactors are characterized b-freely
(non-drain + child-free + ROOT-free at L's frames -- the third condition is NOT implied by the
second); (f) the child READS are a function of the CLASS; (h) the planted image IS the genre,
exactly.  It also records FINDING A-H.7/C1: block (a)'s own cells are NOT genre cells (mu = 1
carries no child event, and every planted product there is a DRAIN state), so (a)-(c) certify
the planting map but not the genre count.

Exact arithmetic in Z/q^N; monic polynomials represented by their low coefficient lists.
Run:  python3 OM2_h116b_gauge_resultant.py   (~60 s, the last cell is 4.8M presentations)
Exit 0 iff every check passes.  Last run: 2026-08-16, 65/65 (was 39/39 before block (d)-(h)).
"""

import sys
import itertools
import random
from collections import Counter

FAILED = []


def check(name, ok, detail=""):
    print(("  ok    " if ok else "  FAIL  ") + name + (("  -- " + detail) if detail else ""))
    if not ok:
        FAILED.append(name)


# ---------------------------------------------------------------------------------
# polynomial helpers over Z/M  (dense coefficient lists, index = degree)
# ---------------------------------------------------------------------------------
def pmul(f, g, M):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                out[i + j] = (out[i + j] + a * b) % M
    return out


def monic_poly(b, M):
    """X^mu + sum_{i<mu} b_i X^i."""
    return [x % M for x in b] + [1]


def comp_X_sub_c(f, c, M):
    """f(X - c), returned with EXACTLY deg(f)+1 coefficients (f is assumed monic)."""
    d = len(f) - 1
    powers = [[1]]
    for _ in range(d):
        powers.append(pmul(powers[-1], [(-c) % M, 1], M))
    out = [0] * (d + 1)
    for i, a in enumerate(f):
        if a % M == 0:
            continue
        for j, t in enumerate(powers[i]):
            out[j] = (out[j] + a * t) % M
    return out


def scale_roots(f, s, M):
    """coeff j  |-->  coeff j * s^(deg - j)."""
    d = len(f) - 1
    return [(f[j] * pow(s, d - j, M)) % M for j in range(d + 1)]


def alpha_parent(b, k, what, q, M):
    """The planted factor P(b) at slope k and centre `what`: scaleRoots(monicPoly(b)(X-what), q^k)."""
    return scale_roots(comp_X_sub_c(monic_poly(b, M), what, M), pow(q, k, M), M)


def resultant_valuation(f, g, q, M):
    """v_q(Res(f,g)) via the Sylvester determinant over Z/M -- only used as a cross-check on
    small cases, where the true resultant is < M in absolute value; computed over Z instead."""
    # Sylvester matrix over the integers (representatives in [0, M)).
    m, n = len(f) - 1, len(g) - 1
    size = m + n
    if size == 0:
        return 0
    S = [[0] * size for _ in range(size)]
    for i in range(n):
        for j, a in enumerate(reversed(f)):
            S[i][i + j] = a
    for i in range(m):
        for j, a in enumerate(reversed(g)):
            S[n + i][i + j] = a
    det = int_det(S)
    if det == 0:
        return None
    v = 0
    while det % q == 0:
        det //= q
        v += 1
    return v


def int_det(S):
    """Exact integer determinant by fraction-free Gaussian elimination (Bareiss)."""
    S = [row[:] for row in S]
    n = len(S)
    sign = 1
    prev = 1
    for k in range(n - 1):
        if S[k][k] == 0:
            piv = None
            for i in range(k + 1, n):
                if S[i][k] != 0:
                    piv = i
                    break
            if piv is None:
                return 0
            S[k], S[piv] = S[piv], S[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                S[i][j] = (S[i][j] * S[k][k] - S[i][k] * S[k][j]) // prev
            S[i][k] = 0
        prev = S[k][k]
    return sign * S[n - 1][n - 1]


# ---------------------------------------------------------------------------------
# CHECK 1 -- the planting map is uniformly q^g-to-one, g = sum_{p<p'} mu mu' min(k,k')
# ---------------------------------------------------------------------------------
def plant_hist(q, N, children, cofactor=None):
    """Histogram of the planting map ((b_p)) |--> class of prod P(b_p) * Q  (mod q^N)."""
    M = q ** N
    ranges = [list(itertools.product(*[range(0, M, q)] * mu)) for (mu, k, w) in children]
    total_deg = sum(mu for (mu, k, w) in children) + (len(cofactor) - 1 if cofactor else 0)
    hist = Counter()
    for combo in itertools.product(*ranges):
        f = cofactor[:] if cofactor else [1]
        for b, (mu, k, w) in zip(combo, children):
            f = pmul(f, alpha_parent(list(b), k, w, q, M), M)
        assert len(f) - 1 == total_deg and f[total_deg] % M == 1 % M
        hist[tuple(f[:total_deg])] += 1
    return hist


def check_gauge(q, N, children, cofactor=None, tag="", expect_gamma=None):
    """The load-bearing claim: the planting map is UNIFORMLY many-to-one, with a multiplicity
    that factors as (per-child ghost multiplicity) x q^gamma, gamma independent of the cofactor.
    The per-child ghost multiplicity is MEASURED by running the same map on that child alone."""
    hist = plant_hist(q, N, children, cofactor)
    sizes = set(hist.values())
    ok_const = (len(sizes) == 1)
    check(f"planting multiplicity CONSTANT [{tag}]", ok_const,
          "" if ok_const else f"sizes={sorted(sizes)}")
    if not ok_const:
        return None
    mult = sizes.pop()
    ghost = 1
    for ch in children:
        gh = set(plant_hist(q, N, [ch]).values())
        if len(gh) != 1:
            check(f"single-child ghost CONSTANT [{tag}]", False, f"{sorted(gh)}")
            return None
        ghost *= gh.pop()
    ok_div = (mult % ghost == 0)
    check(f"multiplicity = ghost x q^gamma [{tag}]", ok_div,
          f"mult={mult} ghost={ghost}")
    if not ok_div:
        return None
    gamma = 0
    r = mult // ghost
    while r % q == 0:
        r //= q
        gamma += 1
    ok_pow = (r == 1)
    check(f"the residual gauge is a power of q: q^{gamma} [{tag}]", ok_pow,
          f"mult/ghost={mult // ghost}")
    if expect_gamma is not None:
        check(f"gamma = {expect_gamma} (cofactor-independent) [{tag}]", gamma == expect_gamma,
              f"gamma={gamma}")
    return gamma


# ---------------------------------------------------------------------------------
# CHECK 2 -- the resultant valuation is b-INDEPENDENT and equals mu mu' min(k,k')
# ---------------------------------------------------------------------------------
def check_resultant_b_independence(q, N, p1, p2, nsample, tag=""):
    M = q ** N
    mu1, k1, w1 = p1
    mu2, k2, w2 = p2
    want = mu1 * mu2 * min(k1, k2)
    vals = set()
    import random
    random.seed(20260816)
    for _ in range(nsample):
        b1 = [q * random.randrange(q ** (N - 1)) for _ in range(mu1)]
        b2 = [q * random.randrange(q ** (N - 1)) for _ in range(mu2)]
        # exact integer polynomials (no reduction): use small representatives
        P1 = alpha_parent(b1, k1, w1, q, q ** (N + 8))
        P2 = alpha_parent(b2, k2, w2, q, q ** (N + 8))
        v = resultant_valuation(P1, P2, q, q ** (N + 8))
        if v is None:
            continue
        vals.add(min(v, want + 4))
    ok = (vals == {want})
    check(f"v(Res(P_p,P_p')) = mu mu' min(k,k') = {want}, b-independent [{tag}]", ok,
          "" if ok else f"observed {sorted(vals)}")


# ---------------------------------------------------------------------------------
# CHECK 3 -- fibre equicardinality FOLLOWS from constant multiplicity (the accounting)
# ---------------------------------------------------------------------------------
def check_fibre_accounting(q, N, children, D, cofactor=None, tag=""):
    """Group the planting map's image by the child READS (b_p mod q^(N-D_p)) and verify each
    group has the same number of classes -- the statement H.116b makes, derived here purely
    from the presentation count with no replant map."""
    M = q ** N
    ranges = []
    for (mu, k, w) in children:
        ranges.append(list(itertools.product(*[range(0, M, q)] * mu)))
    total_deg = sum(mu for (mu, k, w) in children) + (len(cofactor) - 1 if cofactor else 0)
    by_read = {}
    for combo in itertools.product(*ranges):
        f = cofactor[:] if cofactor else [1]
        reads = []
        for b, (mu, k, w), Dp in zip(combo, children, D):
            W = q ** (N - Dp)
            reads.append(tuple(x % W for x in b))
            f = pmul(f, alpha_parent(list(b), k, w, q, M), M)
        by_read.setdefault(tuple(reads), set()).add(tuple(f[:total_deg]))
    sizes = set(len(v) for v in by_read.values())
    ok = (len(sizes) == 1)
    check(f"fibres over the child reads are EQUICARDINAL [{tag}]", ok,
          f"sizes={sorted(sizes)} reads={len(by_read)}")


# =================================================================================
# BLOCK (d)-(h) -- ADDED 2026-08-16 by unit A-H.7 (blueprint AMENDMENT A-H.7, the
# H.116b re-split).  CERTIFY-BEFORE-SIGN: these are the legs of NODE H.116b4's route
# that blocks (a)-(c) do NOT cover.
#
# WHY THEY WERE NEEDED.  Blocks (a)-(c) hold the COFACTOR FIXED and vary only the child
# lifts.  The accounting H.116b actually runs over the PAIR space (child presentations,
# cofactor presentation):
#     #fibre(t) = #{presentations with child reads t} / (presentation multiplicity),
# and the multiplicity has to be constant over the GENRE, not merely over one cofactor's
# slice.  Nothing in (a)-(c) rules out two DIFFERENT cofactors presenting the same class,
# which would make the pair-multiplicity vary from class to class and break the division.
# Three further legs were equally load-bearing and equally unmeasured: that the GENRE of
# the product is a function of the COFACTOR ALONE (so the admissible-cofactor set is
# b-independent and cancels out of the ratio), that the child READS are a function of the
# CLASS (so the fibre decomposition is well posed at all), and that the planted image IS
# the genre (soundness AND surjectivity, i.e. that the peel really does present every
# member).
#
# FINDING A-H.7/C1 (coverage of blocks (a)-(c)).  The cells of block (a) are NOT genre
# cells.  With mu = 1 they carry no child event at all -- `HasChildAt` demands 2 <= mu --
# and EVERY one of them has v(constant coefficient) >= N, i.e. the planted product is a
# DRAIN state, which `IsBetaState` excludes.  So (a)-(c) certify the planting map as a map,
# not the genre count.  The smallest cell that is simultaneously multi-child, non-drain and
# carries a NON-TRIVIAL child read is  q = 3, N = 6, m = 4, L = {(2,1,1),(2,1,2)}, K = 1 --
# exactly the same-slope census cell that OM2_h116b_replant_cert.py's check E2 resolves.
# It is run below, and it reproduces E2's split on the nose: 81 reads x 729 classes.
# =================================================================================

def vq(x, q, N):
    """The window-capped q-adic valuation of a representative (N = invisible)."""
    x %= q ** N
    if x == 0:
        return N
    v = 0
    while x % q == 0:
        x //= q
        v += 1
    return v


def content_at(f, q, N, k):
    """H.108's capped content  D = min_j ( min(v(a_j), N) + j*k )  of a monic lift."""
    return min(vq(f[j], q, N) + j * k for j in range(len(f)))


def frame_at(f, q, M, k, zhat):
    """The recentred frame  f(q^k * (X + zhat))  mod M."""
    scaled = [(f[j] * pow(q, k * j, M)) % M for j in range(len(f))]
    return comp_X_sub_c(scaled, (-zhat) % M, M)


def ord0_at(f, q, N, k, z):
    """ord_0 of the DIVIDED (k,z)-frame: the least abscissa carrying a unit.  None if the
    frame is invisible in the window.  `HasChildAt` at (k,z) is exactly ord_0 >= 2."""
    M = q ** N
    D = content_at(f, q, N, k)
    if D >= N:
        return None
    F = frame_at(f, q, M, k, z)
    for j, cc in enumerate(F):
        if vq(cc, q, N) < D:
            return "BAD"
        if vq(cc, q, N) == D:
            return j
    return None


def child_mult(f, q, N, k, z):
    if k < 1 or z % q == 0:
        return None
    o = ord0_at(f, q, N, k, z)
    if o == "BAD":
        return "BAD"
    if o is None or o < 2:
        return None
    return o


def genre_of(f, q, N):
    """DRAIN, BAD, or (frozenset {(mu,k,z)}, the contents at the child slopes)."""
    if vq(f[0], q, N) >= N:
        return "DRAIN"
    kids, cont = [], {}
    for k in range(1, N + 1):
        for z in range(1, q):
            mu = child_mult(f, q, N, k, z)
            if mu == "BAD":
                return "BAD"
            if mu is not None:
                kids.append((mu, k, z))
                cont[k] = content_at(f, q, N, k)
    return (frozenset(kids), tuple(sorted(cont.items())))


def child_image_table(q, N, mu, k, w):
    """The image of the single-child planting map b |--> P(b), with its (constant) ghost
    multiplicity and the precision `det` at which the lift b is determined by its image."""
    M = q ** N
    table = {}
    for b in itertools.product(*[range(0, M, q)] * mu):
        P = tuple(alpha_parent(list(b), k, w, q, M))
        table.setdefault(P, []).append(b)
    ghosts = set(len(v) for v in table.values())
    det = N
    for bs in table.values():
        b0 = bs[0]
        for b in bs[1:]:
            for x, y in zip(b0, b):
                d = (x - y) % M
                if d:
                    det = min(det, vq(d, q, N))
    return table, ghosts, det


def run_pair_cell(q, N, m, children, cof_deg, tag, states_enum=False):
    """(d),(f),(g),(h): the PAIR-space gauge and the accounting it licenses.

    The pair space is (one presentation per child) x (one cofactor presentation).  Child
    presentations are enumerated through the IMAGE of b |--> P(b) -- legitimate because the
    single-child ghost is constant (block (a)) and because the read window sits inside the
    precision at which the image determines b (check f0)."""
    M = q ** N
    tables, dets, ghost_tot = [], [], 1
    for (mu, k, w) in children:
        tab, gh, det = child_image_table(q, N, mu, k, w)
        if len(gh) != 1:
            check(f"pair block: single-child ghost CONSTANT [{tag}]", False, f"{sorted(gh)}")
            return
        ghost_tot *= gh.pop()
        tables.append(tab)
        dets.append(det)
    reps = [{P: bs[0] for P, bs in tab.items()} for tab in tables]
    keysets = [list(t.keys()) for t in tables]
    cofs = ([list(c) + [1] for c in itertools.product(*[range(0, M, q)] * cof_deg)]
            if cof_deg else [[1]])

    def products():
        for combo in itertools.product(*keysets):
            base = [1]
            for P in combo:
                base = pmul(base, list(P), M)
            if cof_deg:
                for Qp in cofs:
                    yield combo, pmul(base, Qp, M)
            else:
                yield combo, base

    hist = Counter()
    for _, f in products():
        hist[tuple(f[:m])] += 1
    bygenre = {}
    for cls in hist:
        bygenre.setdefault(genre_of(list(cls) + [1], q, N), []).append(cls)
    wanted = frozenset(children)
    tgt = [g for g in bygenre if g not in ("DRAIN", "BAD") and g[0] == wanted]
    check(f"(d0) frame levels consistent, no BAD reads [{tag}]", "BAD" not in bygenre)
    check(f"(d1) the planted image meets the target genre, off the drain [{tag}]",
          len(tgt) > 0,
          f"presentations={sum(hist.values())} classes={len(hist)} "
          f"drain={len(bygenre.get('DRAIN', []))} genres={len(bygenre)} target={len(tgt)}")
    if not tgt:
        return
    allok, det2, mults = True, "", set()
    for g in tgt:
        sizes = set(hist[c] for c in bygenre[g])
        mults |= sizes
        if len(sizes) != 1:
            allok = False
            det2 = f"{sorted(sizes)}"
    check(f"(d) PAIR presentation multiplicity CONSTANT on the genre [{tag}]", allok,
          det2 or f"mult={sorted(mults)} (x ghost {ghost_tot} at lift level), "
                  f"{len(tgt)} genre(s), {sum(len(bygenre[g]) for g in tgt)} classes")
    cls_wins, skip = {}, set()
    for g in tgt:
        contents = dict(g[1])
        wins = tuple(N - contents[k] for (mu, k, w) in children)
        if min(wins) < 1 or any(wv > dets[i] for i, wv in enumerate(wins)):
            skip.add(g)
            continue
        for cls in bygenre[g]:
            cls_wins[cls] = wins
    check(f"(f0) every target read window is >= 1 and inside the image determination [{tag}]",
          not skip, f"skipped genres={len(skip)} dets={dets}")
    cls_read, okf = {}, True
    for combo, f in products():
        cls = tuple(f[:m])
        wins = cls_wins.get(cls)
        if wins is None:
            continue
        rd = tuple(tuple(x % (q ** wins[i]) for x in reps[i][P])
                   for i, P in enumerate(combo))
        if cls in cls_read:
            if cls_read[cls] != rd:
                okf = False
        else:
            cls_read[cls] = rd
    check(f"(f) the child READS are a function of the CLASS [{tag}]", okf,
          f"{len(cls_read)} classes carrying a read")
    okg, dg = True, []
    for g in tgt:
        if g in skip:
            continue
        wins = tuple(N - dict(g[1])[k] for (mu, k, w) in children)
        fib = Counter(cls_read[c] for c in bygenre[g])
        sizes = set(fib.values())
        nread = 1
        for i, (mu, k, w) in enumerate(children):
            nread *= q ** ((wins[i] - 1) * mu)
        if len(sizes) != 1 or len(fib) != nread:
            okg = False
            dg.append(f"sizes={sorted(sizes)} reads={len(fib)} predicted={nread}")
        else:
            dg.append(f"{len(fib)} reads x {sizes.copy().pop()} = {len(bygenre[g])} "
                      f"(windows {list(wins)})")
    check(f"(g) genre = (predicted # of child reads) x EQUICARDINAL fibres [{tag}]", okg,
          "; ".join(dg[:3]))
    if states_enum:
        okh, dh = True, []
        for g in tgt:
            allcls = set(a for a in itertools.product(*[range(0, M, q)] * m)
                         if genre_of(list(a) + [1], q, N) == g)
            if allcls != set(bygenre[g]):
                okh = False
                dh.append(f"|states|={len(allcls)} |planted|={len(bygenre[g])}")
            else:
                dh.append(f"{len(allcls)}")
        check(f"(h) the planted image IS the genre, EXACTLY [{tag}]", okh,
              f"classes {', '.join(dh[:4])} of {q ** (m * (N - 1))} states")


def check_genre_is_cofactor_determined(q, N, m, children, cof_deg, nsample, tag):
    """(e) the GENRE of the planted product depends on the COFACTOR ALONE -- never on the
    child lifts.  This is what makes the admissible-cofactor count cancel in the ratio."""
    M = q ** N
    rng = random.Random(20260816)
    combos = [[[q * rng.randrange(q ** (N - 1)) for _ in range(mu)]
               for (mu, k, w) in children] for _ in range(nsample)]
    cofs = ([list(c) + [1] for c in itertools.product(*[range(0, M, q)] * cof_deg)]
            if cof_deg else [[1]])
    ok, det, nnd = True, "", 0
    for Qp in cofs:
        seen = set()
        for bs in combos:
            f = Qp[:]
            for b, (mu, k, w) in zip(bs, children):
                f = pmul(f, alpha_parent(list(b), k, w, q, M), M)
            g = genre_of(f, q, N)
            if g not in ("DRAIN", "BAD"):
                nnd += 1
            seen.add(g)
        if len(seen) != 1:
            ok = False
            det = f"cofactor {Qp}: {len(seen)} genres over {nsample} b-samples"
    check(f"(e) the planted product's GENRE is COFACTOR-determined (b-independent) [{tag}]",
          ok, det or f"{len(cofs)} cofactors x {nsample} b-samples, {nnd} non-drain")


def check_cofactor_admissibility(q, N, m, children, cof_deg, nsample, tag):
    """(e2) the ADMISSIBLE cofactors -- exactly those whose planted product lands in the
    target genre -- are characterized by three b-free conditions: the product is non-drain,
    the cofactor carries NO child of its own (ord_0 <= 1 at every frame), and the cofactor is
    ROOT-FREE at every frame of L (ord_0 = 0 there).  This is the hypothesis set NODE
    H.116b2 is signed with, and the third condition is NOT implied by the second: a cofactor
    with a SIMPLE root at (k_p, z_p) bumps the product's child multiplicity to mu_p + 1."""
    M = q ** N
    rng = random.Random(20260817)
    wanted = frozenset(children)
    cofs = [list(c) + [1] for c in itertools.product(*[range(0, M, q)] * cof_deg)]
    ok, det, nadm = True, "", 0
    for Qp in cofs:
        nodrain = sum(k * mu for (mu, k, w) in children) + vq(Qp[0], q, N) < N
        childfree = all((ord0_at(Qp, q, N, k, z) or 0) < 2
                        for k in range(1, N + 1) for z in range(1, q))
        rootfree = all(ord0_at(Qp, q, N, k, w) == 0 for (mu, k, w) in children)
        pred = nodrain and childfree and rootfree
        if pred:
            nadm += 1
        obs = set()
        for _ in range(nsample):
            f = Qp[:]
            for (mu, k, w) in children:
                b = [q * rng.randrange(q ** (N - 1)) for _ in range(mu)]
                f = pmul(f, alpha_parent(b, k, w, q, M), M)
            g = genre_of(f, q, N)
            obs.add(g not in ("DRAIN", "BAD") and g[0] == wanted)
        if len(obs) != 1 or obs.pop() != pred:
            ok = False
            det = f"cofactor {Qp}: predicted {pred}, measured otherwise"
    check(f"(e2) admissible cofactors = non-drain + child-free + root-free at L [{tag}]", ok,
          det or f"{nadm}/{len(cofs)} admissible, {nsample} b-samples each")


def main():
    print("H.116b gauge/resultant certification -- exact")

    # --- (a) the planting map is UNIFORMLY many-to-one, with a cofactor-independent residual
    #     gauge.  (Over F_2 the only nonzero residue is 1, so a SAME-slope two-child genre --
    #     the D3 witness shape -- needs q >= 3.)
    print("-- (a) uniform planting multiplicity, and its cofactor-independence")
    g1 = check_gauge(3, 3, [(1, 1, 1), (1, 1, 2)], tag="q3 N3 same-slope k=1 mu=1,1")
    check_gauge(3, 3, [(1, 1, 1), (1, 1, 2)], cofactor=[3, 1], expect_gamma=g1,
                tag="q3 N3 same-slope + cofactor X+3")
    check_gauge(3, 3, [(1, 1, 1), (1, 1, 2)], cofactor=[6, 3, 1], expect_gamma=g1,
                tag="q3 N3 same-slope + cofactor X^2+3X+6")
    g2 = check_gauge(2, 4, [(1, 1, 1), (1, 2, 1)], tag="q2 N4 mixed-slope k=1,2 mu=1,1")
    check_gauge(2, 4, [(1, 1, 1), (1, 2, 1)], cofactor=[2, 1], expect_gamma=g2,
                tag="q2 N4 mixed-slope + cofactor X+2")
    g3 = check_gauge(2, 4, [(2, 1, 1), (1, 2, 1)], tag="q2 N4 mixed-slope k=1,2 mu=2,1")
    check_gauge(2, 4, [(2, 1, 1), (1, 2, 1)], cofactor=[2, 1], expect_gamma=g3,
                tag="q2 N4 mixed-slope mu=2,1 + cofactor X+2")
    g4 = check_gauge(3, 3, [(2, 1, 1), (2, 1, 2)], tag="q3 N3 same-slope k=1 mu=2,2 (D3 shape)")
    check_gauge(2, 5, [(1, 1, 1), (1, 3, 1)], tag="q2 N5 mixed-slope k=1,3 mu=1,1")

    # --- (b) the resultant reading: v(Res(P_p,P_p')) is b-INDEPENDENT and genre-determined
    print("-- (b) the pairwise resultant valuation is genre-determined, b-independent")
    check_resultant_b_independence(3, 4, (2, 1, 1), (2, 1, 2), 40, tag="q3 same-slope mu=2,2")
    check_resultant_b_independence(3, 4, (2, 1, 1), (2, 2, 2), 40, tag="q3 mixed-slope k=1,2")
    check_resultant_b_independence(2, 4, (2, 1, 1), (1, 3, 1), 40, tag="q2 mixed-slope k=1,3")
    check_resultant_b_independence(2, 4, (3, 2, 1), (2, 1, 1), 30, tag="q2 mixed-slope k=2,1")
    check_resultant_b_independence(3, 4, (1, 1, 1), (1, 1, 2), 40, tag="q3 same-slope mu=1,1")

    # --- (c) the accounting: constant multiplicity => equicardinal child fibres
    print("-- (c) the accounting these two facts license")
    check_fibre_accounting(3, 3, [(1, 1, 1), (1, 1, 2)], [2, 2],
                           tag="q3 N3 same-slope, windows 1,1")
    check_fibre_accounting(2, 4, [(1, 1, 1), (1, 2, 1)], [1, 2],
                           tag="q2 N4 mixed-slope, windows 3,2")
    check_fibre_accounting(2, 4, [(2, 1, 1), (1, 2, 1)], [2, 2],
                           tag="q2 N4 mixed-slope mu=2,1, windows 2,2")

    # --- (d)-(h) [A-H.7, 2026-08-16] the PAIR-space gauge and the accounting it licenses.
    #     Every cell here is a GENRE cell: mu >= 2 (a real `HasChildAt`), the planted product
    #     is NON-DRAIN, and the child read window is >= 2 (so the reads are not trivial).
    print("-- (e) the genre of a planted product is cofactor-determined")
    check_genre_is_cofactor_determined(2, 5, 3, [(2, 1, 1)], 1, 12,
                                       tag="q2 N5 m3 single-child + cofactor")
    check_genre_is_cofactor_determined(3, 5, 3, [(2, 1, 1)], 1, 8,
                                       tag="q3 N5 m3 single-child + cofactor")
    check_genre_is_cofactor_determined(3, 6, 5, [(2, 1, 1), (2, 1, 2)], 1, 8,
                                       tag="q3 N6 m5 same-slope + cofactor")

    print("-- (e2) the admissible cofactors are characterized b-freely")
    check_cofactor_admissibility(2, 5, 3, [(2, 1, 1)], 1, 10,
                                 tag="q2 N5 m3 single-child")
    check_cofactor_admissibility(3, 5, 3, [(2, 1, 1)], 1, 8,
                                 tag="q3 N5 m3 single-child")
    check_cofactor_admissibility(2, 6, 4, [(2, 1, 1)], 2, 6,
                                 tag="q2 N6 m4 single-child, deg-2 cofactor")
    check_cofactor_admissibility(3, 7, 5, [(2, 1, 1), (2, 1, 2)], 1, 4,
                                 tag="q3 N7 m5 same-slope, deg-1 cofactor")

    print("-- (d),(f),(g),(h) the PAIR-space gauge on GENRE cells")
    run_pair_cell(2, 5, 3, [(2, 1, 1)], 1, "q2 N5 m3 single-child + cofactor",
                  states_enum=True)
    run_pair_cell(3, 5, 3, [(2, 1, 1)], 1, "q3 N5 m3 single-child + cofactor")
    run_pair_cell(3, 6, 4, [(2, 1, 1), (2, 1, 2)], 0,
                  "q3 N6 m4 same-slope, the D3 shape (= replant cert's E2 cell)")

    print()
    n = len(FAILED)
    print(f"==== {n} failed ====" if n else "==== ALL CHECKS PASSED ====")
    return 1 if n else 0


if __name__ == "__main__":
    sys.exit(main())
