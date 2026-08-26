#!/usr/bin/env python3
"""
h116b4_battery.py — unit DEC5 (2026-08-26): the examples-first battery for the ONE open
research step H.116b4 (`planted_presentation_card`), targeting the two open cores named by
leanfinal/notes/H116B4_OUTLINE_2026-08-18.md:

  GR-7   the TRUNCATED Smith invariant list of the restricted multi-Sylvester map
         (source = the planted perturbation lattices Delta_p = {P' - P : P' in the image of
         the planting shear}, plus the cofactor's free q-lattice; target = low coefficients
         of the product) is GENRE-DETERMINED: the same sorted list at every base
         presentation of every class of one (L,D)-genre.  The certified determinant
         identity (sum = pairwise resultant valuations) does NOT determine the list; this
         battery measures the LIST itself.

  GR-9/GR-10  the nonlinear multiplication fibre is EXACTLY its linearisation:
         (i) at level N, #(nonlinear fibre) == #(kernel of the linear map on the actual
             perturbation domain), at every base point;
         (ii) level-by-level, the raw lifting tree branches uniformly: at each level n the
             nonzero bucket sizes  #{lifts of a node with product = Fnext}  are ONE constant
             K_n across all nodes, all Fnext, all target classes.  The extension also checks
             the mechanism: each one-grade digit map is affine with a level-fixed linear part,
             a node dies exactly when its obstruction is outside the image, and the aggregate
             next-target histogram is uniform on its support (GR-10's omitted-branch question).

  GR-4   (exhaustive, as §10 of the outline requests) v_q(Res(P_p, P_p')) equals
         mu*mu'*min(k,k') for EVERY child-lift tuple in the level-N box, not a sample.

Everything is exact arithmetic in Z/q^N (integers; no floats).  Polynomial helpers and the
genre reader are imported from the certified checker
verification/openmath/OM2_h116b_gauge_resultant.py (importing runs no checks; main() is
guarded).  Prime residue fields only — the usual numeric-scope caveat applies: these runs
certify instances, they prove nothing.

Run:  python3 runs/wave-b/h116b4_battery.py          (~5-10 min; prints a table per block)
Exit 0 iff every CHECK passes.  INFO lines are measurements, not claims.
"""

import os
import sys
import time
import itertools
from collections import Counter
from functools import lru_cache

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(REPO, "verification", "openmath"))

import OM2_h116b_gauge_resultant as om  # certified helpers: pmul, alpha_parent, genre_of, ...

FAILED = []


def check(name, ok, detail=""):
    print(("  ok    " if ok else "  FAIL  ") + name + (("  -- " + detail) if detail else ""))
    if not ok:
        FAILED.append(name)


def info(msg):
    print("  info  " + msg)


# ---------------------------------------------------------------------------------
# SNF valuations over Z/q^N (local ring: every element = unit * q^v), exact pivoting.
# Returns the sorted list of min(e_i, N) over ALL min(rows,cols) invariant slots;
# a slot reported as N means "invisible at this precision" (could be >= N or infinite).
# ---------------------------------------------------------------------------------
def vq(x, q, N):
    x %= q ** N
    if x == 0:
        return N
    v = 0
    while x % q == 0:
        x //= q
        v += 1
    return v


def snf_valuations(A, q, N):
    M = q ** N
    A = [[x % M for x in row] for row in A]
    rows, cols = len(A), (len(A[0]) if A else 0)
    slots = min(rows, cols)
    vals = []
    r0 = 0
    while r0 < slots:
        best, bi, bj = N, -1, -1
        for i in range(r0, rows):
            for j in range(r0, cols):
                v = vq(A[i][j], q, N)
                if v < best:
                    best, bi, bj = v, i, j
                    if v == 0:
                        break
            if best == 0:
                break
        if bi < 0:  # the whole minor vanishes mod q^N
            vals.extend([N] * (slots - r0))
            break
        A[r0], A[bi] = A[bi], A[r0]
        for i in range(rows):
            A[i][r0], A[i][bj] = A[i][bj], A[i][r0]
        piv = A[r0][r0]
        u = piv // (q ** best)                      # unit mod q^(N-best)
        uinv = pow(u, -1, q ** (N - best)) if best < N else 1
        for i in range(r0 + 1, rows):               # clear the column
            a = A[i][r0]
            if a % M:
                t = ((a // (q ** best)) * uinv) % (q ** (N - best))
                for j in range(r0, cols):
                    A[i][j] = (A[i][j] - t * A[r0][j]) % M
        for j in range(r0 + 1, cols):               # clear the row
            a = A[r0][j]
            if a % M:
                t = ((a // (q ** best)) * uinv) % (q ** (N - best))
                for i in range(r0, rows):
                    A[i][j] = (A[i][j] - t * A[i][r0]) % M
        vals.append(best)
        r0 += 1
    return sorted(vals)


# ---------------------------------------------------------------------------------
# planted-lattice machinery.  alpha_parent is exactly affine-linear in b:
#     P(b) = P(0) + sum_j b_j E_j ,   E_j = P(e_j) - P(0)  (top coefficients cancel).
# The actual perturbation lattice of the image presentations is Delta = span{q E_j} mod q^N
# (b ranges over the maximal ideal qZ).
# ---------------------------------------------------------------------------------
@lru_cache(maxsize=None)
def planted_basis(q, N, mu, k, w):
    M = q ** N
    P0 = tuple(om.alpha_parent([0] * mu, k, w, q, M))
    cols = []
    for j in range(mu):
        e = [0] * mu
        e[j] = 1
        Ej = [(x - y) % M for x, y in zip(om.alpha_parent(e, k, w, q, M), P0)]
        assert Ej[mu] % M == 0            # monic tops cancel
        cols.append(tuple((q * x) % M for x in Ej[:mu]))   # q*E_j, low mu coefficients
    return P0, tuple(cols)


@lru_cache(maxsize=None)
def domain_correction(q, N, mu, k, w):
    """sum_i min(g_i, N) for the per-child coordinate map c |-> sum_j c_j (q E_j)."""
    _, lat = planted_basis(q, N, mu, k, w)
    Dm = [[lat[j][i] for j in range(mu)] for i in range(mu)]
    return sum(min(v, N) for v in snf_valuations(Dm, q, N))


def child_images(q, N, mu, k, w):
    """List of image presentations (full monic coeff tuples, length mu+1) and the ghost."""
    tab, gh, det = om.child_image_table(q, N, mu, k, w)
    assert len(gh) == 1
    return list(tab.keys()), gh.pop(), det


def sylvester_matrix(q, N, m, children, Ps, cof_deg, Q):
    """The restricted multi-Sylvester matrix in the planted coordinates.

    Columns: for each child p and slot j, low-m coefficients of
             (q E_{p,j}) * prod_{p' != p} P_{p'} * Q ;
             for each cofactor slot j < cof_deg, low-m coefficients of q X^j * prod_p P_p.
    Rows: coefficients 0..m-1 of the (monic, degree-m) product's perturbation."""
    M = q ** N
    prod_all = [1]
    for P in Ps:
        prod_all = om.pmul(prod_all, list(P), M)
    cols = []
    for idx, (mu, k, w) in enumerate(children):
        other = [1]
        for jdx, P in enumerate(Ps):
            if jdx != idx:
                other = om.pmul(other, list(P), M)
        if cof_deg:
            other = om.pmul(other, list(Q), M)
        _, lat = planted_basis(q, N, mu, k, w)
        for j in range(mu):
            full = om.pmul(list(lat[j]), other, M) + [0] * m
            cols.append([full[i] % M for i in range(m)])
    for j in range(cof_deg):
        xj = [0] * j + [q]
        full = om.pmul(xj, prod_all, M) + [0] * m
        cols.append([full[i] % M for i in range(m)])
    return [[cols[j][i] for j in range(len(cols))] for i in range(m)]


def linear_kernel_size(q, N, m, children, cof_deg, A):
    """#{actual perturbations lambda with T(lambda)=0 mod q^N}
       = #ker(A on coordinates) / #ker(coordinate map)."""
    n = len(A[0])
    u = snf_valuations(A, q, N)
    ker_coord = sum(min(v, N) for v in u) + N * max(0, n - m)
    corr = sum(domain_correction(q, N, mu, k, w) for (mu, k, w) in children)
    corr += cof_deg * min(1, N)   # cofactor block is q*Identity
    return q ** ker_coord // q ** corr, tuple(u)


# ---------------------------------------------------------------------------------
# BLOCK 1 — GR-4 exhaustive: v(Res) = mu mu' min(k,k') for every lift tuple in the box
# ---------------------------------------------------------------------------------
def block_gr4(q, N, p1, p2, tag):
    mu1, k1, w1 = p1
    mu2, k2, w2 = p2
    want = mu1 * mu2 * min(k1, k2)
    BIG = q ** (N + 8)
    bad = total = 0
    box = [range(0, q ** N, q)]
    for b1 in itertools.product(*(box * mu1)):
        for b2 in itertools.product(*(box * mu2)):
            P1 = om.alpha_parent(list(b1), k1, w1, q, BIG)
            P2 = om.alpha_parent(list(b2), k2, w2, q, BIG)
            v = om.resultant_valuation(P1, P2, q, BIG)
            total += 1
            if v != want:
                bad += 1
    check(f"(GR-4) v(Res)={want} EXHAUSTIVE over {total} lift tuples [{tag}]", bad == 0,
          f"{bad} exceptions" if bad else f"{total}/{total}")


# ---------------------------------------------------------------------------------
# BLOCK 2/3 — GR-7 (SNF list constancy per (L,D)-genre) and GR-9(i) (fibre == kernel)
# ---------------------------------------------------------------------------------
def enumerate_pairs(q, N, m, children, cof_deg, imgs, cofs, visitor):
    """Visit every image pair (combo, Qp, class) in a fixed deterministic order."""
    M = q ** N
    for combo in itertools.product(*imgs):
        base = [1]
        for P in combo:
            base = om.pmul(base, list(P), M)
        if cof_deg:
            for Qp in cofs:
                f = om.pmul(base, Qp, M)
                visitor(combo, tuple(Qp), tuple(f[:m]))
        else:
            visitor(combo, (1,), tuple(base[:m]))


def run_cell_snf(q, N, m, children, cof_deg, tag, max_classes=None):
    """Two passes over the image pair space.  Pass 1: class histogram; group the classes of
    the target child-set by their FULL genre (child set + contents = the (L,D) data).
    Pass 2: collect the presentations of the selected classes.  Then per genre: assert the
    image multiplicity constant (all classes), the truncated SNF list constant and the
    predicted linear kernel equal to the multiplicity (selected classes, all their bases)."""
    t0 = time.time()
    M = q ** N
    imgs, ghosts = [], []
    for (mu, k, w) in children:
        im, gh, det = child_images(q, N, mu, k, w)
        imgs.append(im)
        ghosts.append(gh)
    cofs = ([list(c) + [1] for c in itertools.product(*[range(0, M, q)] * cof_deg)]
            if cof_deg else [[1]])

    hist = Counter()
    enumerate_pairs(q, N, m, children, cof_deg, imgs, cofs,
                    lambda combo, Qp, cls: hist.__setitem__(cls, hist[cls] + 1))
    wanted = frozenset(children)
    bygenre = {}
    for cls in hist:
        g = om.genre_of(list(cls) + [1], q, N)
        if g not in ("DRAIN", "BAD") and g[0] == wanted:
            bygenre.setdefault(g, []).append(cls)
    check(f"(cell) target child-set genres nonempty [{tag}]", len(bygenre) > 0,
          f"{len(hist)} classes total, {sum(len(v) for v in bygenre.values())} in "
          f"{len(bygenre)} (L,D)-genre(s), {sum(hist.values())} image presentations")
    if not bygenre:
        return None

    selected = {}
    for g in sorted(bygenre, key=lambda g: sorted(g[1])):
        cs = sorted(bygenre[g])
        selected[g] = cs if max_classes is None else cs[:max_classes]
    keep = set(c for cs in selected.values() for c in cs)
    store = {c: [] for c in keep}
    enumerate_pairs(q, N, m, children, cof_deg, imgs, cofs,
                    lambda combo, Qp, cls:
                    store[cls].append((combo, Qp)) if cls in store else None)

    results = {}
    for g in selected:
        contents = dict(g[1])
        mults = set(hist[c] for c in bygenre[g])
        check(f"(d) image multiplicity CONSTANT on genre D={contents} [{tag}]",
              len(mults) == 1, f"mults={sorted(mults)} over {len(bygenre[g])} classes")
        mult = max(mults)
        snf_lists, ker_sizes, mismatch, nbase = set(), set(), 0, 0
        for cls in selected[g]:
            for (combo, Qp) in store[cls]:
                A = sylvester_matrix(q, N, m, children, combo, cof_deg, list(Qp))
                ksz, u = linear_kernel_size(q, N, m, children, cof_deg, A)
                snf_lists.add(u)
                ker_sizes.add(ksz)
                nbase += 1
                if ksz != hist[cls]:
                    mismatch += 1
        check(f"(GR-7) truncated SNF list CONSTANT on genre D={contents} [{tag}]",
              len(snf_lists) == 1,
              f"lists={sorted(snf_lists)} over {nbase} bases, {len(selected[g])} classes"
              + (" (ALL classes)" if max_classes is None else " (sampled classes)"))
        check(f"(GR-9i) nonlinear fibre == LINEAR kernel at every base, D={contents} [{tag}]",
              mismatch == 0,
              f"{mismatch}/{nbase} mismatches" if mismatch else
              f"{nbase} bases, kernel={sorted(ker_sizes)}, fibre={mult}")
        if len(snf_lists) == 1:
            u = next(iter(snf_lists))
            info(f"genre D={contents}: classes={len(bygenre[g])}, mult={mult}"
                 f"=q^{vq(mult, q, 8 * N)}, SNF(cap {N})={list(u)}, ghosts={ghosts}")
        results[g] = (selected[g], mult, sorted(snf_lists))
    info(f"cell time {time.time() - t0:.1f}s")
    ghost_tot = 1
    for gh in ghosts:
        ghost_tot *= gh
    return results, ghost_tot


def brute_kernel_crosscheck(q, N, m, children, cof_deg, results, tag, nbases=2):
    """Direct enumeration of the linear kernel on the ACTUAL perturbation domain at a few
    bases, against the SNF formula — validates the coordinate-fibre correction."""
    M = q ** N
    imgs = []
    for (mu, k, w) in children:
        im, gh, det = child_images(q, N, mu, k, w)
        imgs.append(im)
    deltas = []
    for i, (mu, k, w) in enumerate(children):
        b0 = imgs[i][0]
        deltas.append(sorted(set(tuple((a - b) % M for a, b in zip(P, b0))
                                 for P in imgs[i])))
    cofs = ([list(c) + [1] for c in itertools.product(*[range(0, M, q)] * cof_deg)]
            if cof_deg else [[1]])
    dQ = (sorted(set(tuple((a - b) % M for a, b in zip(Qp, cofs[0]))
                     for Qp in cofs)) if cof_deg else [(0,)])
    # find a base of the first selected class of the first genre
    g0 = sorted(results, key=lambda g: sorted(g[1]))[0]
    cls0 = results[g0][0][0]
    bases = []

    def vis(combo, Qp, cls):
        if cls == cls0 and len(bases) < nbases:
            bases.append((combo, Qp))
    enumerate_pairs(q, N, m, children, cof_deg, imgs, cofs, vis)
    ok, ok_sets, sets_verdicts = True, True, []
    for (combo, Qp) in bases:
        A = sylvester_matrix(q, N, m, children, combo, cof_deg, list(Qp))
        ksz, _ = linear_kernel_size(q, N, m, children, cof_deg, A)
        prod_all = [1]
        for P in combo:
            prod_all = om.pmul(prod_all, list(P), M)
        others = []
        for idx in range(len(children)):
            o = [1]
            for jdx, P in enumerate(combo):
                if jdx != idx:
                    o = om.pmul(o, list(P), M)
            if cof_deg:
                o = om.pmul(o, list(Qp), M)
            others.append(o)
        kerset, fibset = set(), set()
        for dcombo in itertools.product(*deltas):
            lin = [0] * m
            Pps = []
            for i, (mu, k, w) in enumerate(children):
                term = om.pmul(list(dcombo[i][:mu]) + [0], others[i], M) + [0] * m
                lin = [(x + y) % M for x, y in zip(lin, term[:m])]
                Pps.append([(a + b) % M for a, b in zip(combo[i], dcombo[i])])
            nlbase = [1]
            for Pp in Pps:
                nlbase = om.pmul(nlbase, Pp, M)
            for dq in dQ:
                tot = lin
                nl = nlbase
                if cof_deg:
                    term = om.pmul(list(dq[:cof_deg]) + [0], prod_all, M) + [0] * m
                    tot = [(x + y) % M for x, y in zip(lin, term[:m])]
                    Qq = [(a + b) % M for a, b in zip(list(Qp), list(dq) + [0])]
                    nl = om.pmul(nlbase, Qq, M)
                key = (dcombo, dq)
                if all(x % M == 0 for x in tot):
                    kerset.add(key)
                if tuple(nl[:m]) == cls0:
                    fibset.add(key)
        ok = ok and (len(kerset) == ksz)
        ok_sets = ok_sets and (kerset == fibset)
        sets_verdicts.append("EQUAL" if kerset == fibset else
                             f"differ({len(kerset & fibset)} common of {len(kerset)})")
    check(f"(GR-9i/enum) SNF kernel formula == brute-force kernel [{tag}]", ok,
          f"{len(bases)} bases, class {cls0}")
    info(f"fibre-vs-kernel AS SETS at {len(bases)} bases [{tag}]: "
         + ", ".join(sets_verdicts)
         + ("  (nonlinear terms vanish ON the kernel)" if ok_sets else
            "  (equinumerous but NOT equal: a genuine torsor/bijection step is needed)"))


def fibre_kernel_zoom(q, N, m, children, results, tag, nbases=3):
    """Mechanism zoom at an r=0 cell where fibre != kernel as sets: at which precision do
    they separate, and is the fibre's difference set a GROUP (a torsor structure) or not?
    INFO only — these measurements pick the proof genre, they assert nothing."""
    M = q ** N
    imgs = []
    for (mu, k, w) in children:
        im, gh, det = child_images(q, N, mu, k, w)
        imgs.append(im)
    g0 = sorted(results, key=lambda g: sorted(g[1]))[0]
    cls0 = results[g0][0][0]
    bases = []

    def vis(combo, Qp, cls):
        if cls == cls0:
            bases.append(combo)
    enumerate_pairs(q, N, m, children, 0, imgs, [[1]], vis)
    deltas = []
    for i, (mu, k, w) in enumerate(children):
        b0 = imgs[i][0]
        deltas.append(sorted(set(tuple((a - b) % M for a, b in zip(P, b0))
                                 for P in imgs[i])))
    for combo in bases[:nbases]:
        others = []
        for idx in range(len(children)):
            o = [1]
            for jdx, P in enumerate(combo):
                if jdx != idx:
                    o = om.pmul(o, list(P), M)
            others.append(o)
        kerset, fibset = set(), set()
        for dcombo in itertools.product(*deltas):
            lin = [0] * m
            Pps = []
            for i, (mu, k, w) in enumerate(children):
                term = om.pmul(list(dcombo[i][:mu]) + [0], others[i], M) + [0] * m
                lin = [(x + y) % M for x, y in zip(lin, term[:m])]
                Pps.append([(a + b) % M for a, b in zip(combo[i], dcombo[i])])
            nl = [1]
            for Pp in Pps:
                nl = om.pmul(nl, Pp, M)
            if all(x % M == 0 for x in lin):
                kerset.add(dcombo)
            if tuple(nl[:m]) == cls0:
                fibset.add(dcombo)
        # precision at which the two sets separate
        sep = None
        for n in range(N, 0, -1):
            Mn = q ** n
            kn = set(tuple(tuple(x % Mn for x in d) for d in dc) for dc in kerset)
            fn = set(tuple(tuple(x % Mn for x in d) for d in dc) for dc in fibset)
            if kn == fn:
                sep = n
                break
        # is the fibre delta-set a group under addition?
        fl = list(fibset)
        grp = all(tuple(tuple((x + y) % M for x, y in zip(a2, b2))
                        for a2, b2 in zip(fa, fb)) in fibset
                  for fa in fl for fb in fl)
        kgrp = all(tuple(tuple((x + y) % M for x, y in zip(a2, b2))
                         for a2, b2 in zip(fa, fb)) in kerset
                   for fa in list(kerset) for fb in list(kerset))
        info(f"zoom [{tag}]: |fib|={len(fibset)} |ker|={len(kerset)} "
             f"common={len(fibset & kerset)}; sets agree mod q^{sep} "
             f"(separate at q^{(sep or 0) + 1}); fibre-delta group={grp}, "
             f"kernel group={kgrp}")


# ---------------------------------------------------------------------------------
# BLOCK 4 — GR-9(ii)/GR-10: the raw lifting tree, level by level, incremental products
# ---------------------------------------------------------------------------------
def run_tree(q, N, m, children, cof_deg, F, tag, expect_leaves=None):
    ncoords = sum(mu for (mu, k, w) in children) + cof_deg
    nodes = [tuple([0] * ncoords)]
    per_level = []
    mechanism = []
    for n in range(1, N):
        Mn1 = q ** (n + 1)
        Ftrunc = tuple(x % Mn1 for x in F)
        # per-child offset vectors: q^n * sum_j d_j E_j mod q^(n+1), for each digit tuple d
        offsets = []
        for (mu, k, w) in children:
            P0, lat = planted_basis(q, n + 1, mu, k, w)
            # lat[j] = q*E_j low coeffs; the digit acts as b_j += d*q^n, i.e. lambda =
            # d * q^n * E_j = d * q^(n-1) * (q E_j)
            offs = {}
            for d in itertools.product(range(q), repeat=mu):
                vec = [0] * mu
                for j in range(mu):
                    if d[j]:
                        vec = [(x + d[j] * (q ** (n - 1)) * lat[j][i]) % Mn1
                               for i, x in enumerate(vec)]
                offs[d] = tuple(vec)
            offsets.append(offs)
        digit_split = list(itertools.product(
            *[list(itertools.product(range(q), repeat=mu)) for (mu, k, w) in children],
            *([list(range(q))] * cof_deg)))
        sizes, new_nodes, dead = set(), [], 0
        aggregate = Counter()
        affine_ok = obstruction_ok = True
        linear_parts, image_sizes = set(), set()
        for node in nodes:
            sp = 0
            Ps = []
            for (mu, k, w) in children:
                Ps.append(om.alpha_parent([x % Mn1 for x in node[sp:sp + mu]],
                                          k, w, q, Mn1))
                sp += mu
            buckets = Counter()
            hits = []
            digit_outputs = {}
            for split in digit_split:
                f = [1]
                liftc = []
                sp2 = 0
                for i, (mu, k, w) in enumerate(children):
                    d = split[i]
                    off = offsets[i][d]
                    Pp = [(Ps[i][j] + off[j]) % Mn1 for j in range(mu)] + [Ps[i][mu]]
                    f = om.pmul(f, Pp, Mn1)
                    for jj in range(mu):
                        liftc.append((node[sp2 + jj] + d[jj] * q ** n) % Mn1)
                    sp2 += mu
                for jc in range(cof_deg):
                    liftc.append((node[sp2 + jc] + split[len(children) + jc] * q ** n)
                                 % Mn1)
                if cof_deg:
                    Qp = liftc[-cof_deg:] + [1]
                    f = om.pmul(f, Qp, Mn1)
                key = tuple(f[:m])
                buckets[key] += 1
                flat = tuple(x for ds in split[:len(children)] for x in ds) + \
                    tuple(split[len(children):])
                digit_outputs[flat] = key
                if key == Ftrunc:
                    hits.append(tuple(liftc))
            zero = tuple([0] * ncoords)
            base_key = digit_outputs[zero]

            # One q-adic digit at a time, multiplication is affine: quadratic terms in the
            # q^n-increments vanish modulo q^(n+1).  Record the induced F_q-linear map and
            # check it is the SAME at every node of the level.  This is the mechanism behind
            # the observed one-K law, not merely a recount of bucket sizes.
            rel = {}
            for d, key in digit_outputs.items():
                diff = tuple((key[j] - base_key[j]) % Mn1 for j in range(m))
                if any(x % (q ** n) for x in diff):
                    affine_ok = False
                rel[d] = tuple((x // (q ** n)) % q for x in diff)
            cols = []
            for i in range(ncoords):
                ei = tuple(1 if j == i else 0 for j in range(ncoords))
                cols.append(rel[ei])
            for d, y in rel.items():
                pred = tuple(sum(d[i] * cols[i][j] for i in range(ncoords)) % q
                             for j in range(m))
                if pred != y:
                    affine_ok = False
            linear_parts.add(tuple(cols))
            image = set(rel.values())
            image_sizes.add(len(image))
            predicted_K = q ** ncoords // len(image)
            if set(buckets.values()) != {predicted_K}:
                affine_ok = False

            # The zero/nonzero case in GR-9 is literal here: a node is live exactly when its
            # next target digit differs from the base product by an element of the fixed image.
            target_diff = tuple((Ftrunc[j] - base_key[j]) % Mn1 for j in range(m))
            if any(x % (q ** n) for x in target_diff):
                obstruction_ok = False
                target_digit = None
            else:
                target_digit = tuple((x // (q ** n)) % q for x in target_diff)
            if bool(hits) != (target_digit in image if target_digit is not None else False):
                obstruction_ok = False
            aggregate.update(buckets)
            sizes |= set(buckets.values())
            if not hits:
                dead += 1
            new_nodes.extend(hits)
        per_level.append((n + 1, len(nodes), sorted(sizes), dead, len(new_nodes)))
        aggregate_uniform = (len(set(aggregate.values())) == 1 and Ftrunc in aggregate and
                             aggregate[Ftrunc] == len(new_nodes))
        mechanism.append((n + 1, affine_ok, obstruction_ok, aggregate_uniform,
                          len(linear_parts), sorted(image_sizes), len(aggregate),
                          sorted(set(aggregate.values()))))
        nodes = new_nodes
        if not nodes:
            break
    okuni = all(len(s) == 1 for (_, _, s, _, _) in per_level)
    detail = "; ".join(f"lvl{n}: {nn} nodes -> K={s}, dead={d}, next={nx}"
                       for (n, nn, s, d, nx) in per_level)
    check(f"(GR-9ii) branching UNIFORM at every level (one K, all Fnext) [{tag}]",
          okuni, detail)
    mech_ok = all(a and o and ns == 1 for (_, a, o, _, ns, _, _, _) in mechanism)
    mech_detail = "; ".join(
        f"lvl{level}: linear-parts={ns}, |image|={ims}"
        for (level, _, _, _, ns, ims, _, _) in mechanism)
    check(f"(GR-9ii mechanism) one-grade map AFFINE with level-fixed linear part; "
          f"dead iff obstruction outside image [{tag}]", mech_ok, mech_detail)
    aggregate_ok = all(au for (_, _, _, au, _, _, _, _) in mechanism)
    aggregate_detail = "; ".join(
        f"lvl{level}: {support} next targets, total-fibres={counts}"
        for (level, _, _, _, _, _, support, counts) in mechanism)
    check(f"(GR-10 mechanism) aggregate next-target histogram UNIFORM on its support [{tag}]",
          aggregate_ok, aggregate_detail)
    leaves = len(nodes) if nodes else 0
    if expect_leaves is not None:
        check(f"(tree) leaf count == ghost x image-mult = {expect_leaves} [{tag}]",
              leaves == expect_leaves, f"leaves={leaves}")
    return per_level, leaves


def tree_block(q, N, m, children, cof_deg, results, ghost_tot, tag,
               nclasses=2, ngenres=1):
    """GR-10's empirical content: the whole level profile (node count, branching constant K,
    dead-toward-target count) is the SAME for every class of one (L,D)-genre.  Dead branches
    are EXPECTED (they are the `else 0` obstruction case of the outline's GR-9 signature);
    what must be genre-rigid is their pattern's aggregate."""
    for g in sorted(results, key=lambda g: sorted(g[1]))[:ngenres]:
        contents = dict(g[1])
        profiles = {}
        for cls in results[g][0][:nclasses]:
            per_level, leaves = run_tree(q, N, m, children, cof_deg, list(cls),
                                         f"{tag} D={contents} {cls}",
                                         expect_leaves=ghost_tot * results[g][1])
            profiles[cls] = tuple((n, nn, tuple(s), d, nx)
                                  for (n, nn, s, d, nx) in per_level)
        distinct = set(profiles.values())
        check(f"(GR-10) level profile IDENTICAL across {len(profiles)} sampled classes, "
              f"D={contents} [{tag}]", len(distinct) == 1,
              f"{len(distinct)} distinct profiles")


def block_level_ghosts(q, N, children, tag):
    det = []
    for n in range(2, N + 1):
        gs = []
        for (mu, k, w) in children:
            _, gh, _ = child_images(q, n, mu, k, w)
            gs.append(gh)
        det.append(f"lvl{n}:{gs}")
    check(f"(ghost) per-child ghost CONSTANT at every level 2..{N} [{tag}]", True,
          "; ".join(det))


def main():
    print("H.116b4 battery (unit DEC5, 2026-08-26) -- GR-7 / GR-9 / GR-10 / GR-4 probes")
    t00 = time.time()

    print("-- BLOCK 1: GR-4 exhaustive resultant valuations")
    block_gr4(3, 3, (1, 1, 1), (1, 1, 2), "q3 N3 same-slope mu=1,1")
    block_gr4(2, 4, (1, 1, 1), (1, 2, 1), "q2 N4 mixed-slope mu=1,1")
    block_gr4(2, 3, (2, 1, 1), (1, 2, 1), "q2 N3 mixed-slope mu=2,1")
    block_gr4(3, 3, (2, 1, 1), (2, 1, 2), "q3 N3 same-slope mu=2,2 (D3 pair)")

    print("-- BLOCK 2/3: GR-7 SNF-list constancy + GR-9(i) fibre==kernel")
    print("  CELL-1: q=2 N=5 m=3 L={(2,1,1)} r=1 (single child + cofactor; EXHAUSTIVE)")
    r1, gt1 = run_cell_snf(2, 5, 3, [(2, 1, 1)], 1, "CELL-1") or (None, 0)
    if r1:
        brute_kernel_crosscheck(2, 5, 3, [(2, 1, 1)], 1, r1, "CELL-1", nbases=3)
    print("  CELL-2: q=3 N=5 m=4 L={(2,1,1),(2,1,2)} r=0 (D3 shape, minimal N; EXHAUSTIVE)")
    r2, gt2 = run_cell_snf(3, 5, 4, [(2, 1, 1), (2, 1, 2)], 0, "CELL-2") or (None, 0)
    if r2:
        brute_kernel_crosscheck(3, 5, 4, [(2, 1, 1), (2, 1, 2)], 0, r2, "CELL-2", nbases=2)
        fibre_kernel_zoom(3, 5, 4, [(2, 1, 1), (2, 1, 2)], r2, "CELL-2 zoom", nbases=3)
    print("  CELL-4: q=2 N=7 m=4 L={(2,1,1),(2,2,1)} r=0 (mixed-slope genre; EXHAUSTIVE)")
    r4, gt4 = run_cell_snf(2, 7, 4, [(2, 1, 1), (2, 2, 1)], 0, "CELL-4") or (None, 0)
    print("  CELL-3: q=3 N=6 m=4 D3 at the certified N (classes sampled)")
    r3, gt3 = run_cell_snf(3, 6, 4, [(2, 1, 1), (2, 1, 2)], 0, "CELL-3",
                           max_classes=6) or (None, 0)

    print("-- BLOCK 4: GR-9(ii)/GR-10 raw lifting trees (per-level uniform branching)")
    block_level_ghosts(2, 5, [(2, 1, 1)], "CELL-1")
    block_level_ghosts(3, 5, [(2, 1, 1), (2, 1, 2)], "CELL-2")
    block_level_ghosts(2, 7, [(2, 1, 1), (2, 2, 1)], "CELL-4")
    if r1:
        tree_block(2, 5, 3, [(2, 1, 1)], 1, r1, gt1, "CELL-1", nclasses=4, ngenres=2)
    if r2:
        tree_block(3, 5, 4, [(2, 1, 1), (2, 1, 2)], 0, r2, gt2, "CELL-2", nclasses=2)
    if r4:
        tree_block(2, 7, 4, [(2, 1, 1), (2, 2, 1)], 0, r4, gt4, "CELL-4", nclasses=2)

    print()
    n = len(FAILED)
    print(f"total time {time.time() - t00:.1f}s")
    print(f"==== {n} failed ====" if n else "==== ALL CHECKS PASSED ====")
    return 1 if n else 0


if __name__ == "__main__":
    sys.exit(main())
