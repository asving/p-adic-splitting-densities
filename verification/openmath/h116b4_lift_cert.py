#!/usr/bin/env python3
"""h116b4_lift_cert.py — unit MLIFT (2026-08-26): certificates for the II-a/II-b write-up
docs/in-progress/H116B4_LIFT_PROOF_2026-08-26.md.  Exact arithmetic in Z/q^NB; prime
residue fields only; these runs certify instances of the named lemmas, they prove nothing.

C1  closed form (1.1):  alpha_parent(b,k,w) == (X-w q^k)^mu + sum_j b_j q^{k(mu-j)}(X-w q^k)^j
C2  Lemma GRADE as MAPS: at sampled tree nodes/levels the one-grade columns are exactly
    child |-> 0, cofactor c |-> X^{s+c}  (kernel = child digits AS A SET, image = W).
C3  schedule law (6.2): observed I_n (= #image omega_n on S_n(F)) equals #V_n(T_x) from
    the honest saturated-grade-image computation (Lemma 6.1) at a fibre base; and the
    aggregate support equals q^r * I_n.
C4  tower affinity (5.1/5.3): omega_n across each K-fibre is omega_n(x0) - sigma(u)X^{m-1}
    (mod W), sigma(u) = sum of u_{p,mu_p-1} over slope-1 children.
C5  fibrewise coset sweep (5.3): each K-fibre's omega-multiset is one coset of Im(Lbar),
    uniformly covered — includes the choice-compensation.
C6  (info) sibling uniformity at a NON-genre CELL-1 tower — quantifier probe for MLIFT-1.
C7  Lemma TDC (MLFIX 2026-08-27): the exponent-1 Smith target directions are exactly a
    basis of W, the remaining directions form a basis modulo W, and
    dim V_n = #{i : e_i <= n} - r at every tested level.

Run: python3 verification/openmath/h116b4_lift_cert.py   (~1-2 min)
"""

import os
import sys
import itertools
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, os.path.join(REPO, "verification", "openmath"))
sys.path.insert(0, os.path.join(REPO, "runs", "wave-b"))

import OM2_h116b_gauge_resultant as om
import h116b4_battery as bat

FAILED = []


def check(name, ok, detail=""):
    print(("  ok    " if ok else "  FAIL  ") + name + (("  -- " + detail) if detail else ""))
    if not ok:
        FAILED.append(name)


def info(msg):
    print("  info  " + msg)


# ---------------------------------------------------------------- C1: closed form (1.1)
def closed_form(b, k, w, q, M):
    mu = len(b)
    base = [(-w * pow(q, k, M)) % M, 1]          # X - w q^k
    pw = [[1]]
    for _ in range(mu):
        pw.append(om.pmul(pw[-1], base, M))
    out = list(pw[mu]) + [0] * 4
    for j in range(mu):
        for i, t in enumerate(pw[j]):
            out[i] = (out[i] + b[j] * pow(q, k * (mu - j), M) * t) % M
    return [x % M for x in out[:mu + 1]]


def block_c1():
    cases = [(2, 2, 1, 1, 5), (3, 2, 1, 2, 4), (2, 2, 2, 1, 6), (3, 1, 1, 1, 4),
             (2, 3, 1, 1, 4)]
    for (q, mu, k, w, N) in cases:
        M = q ** N
        bad = tot = 0
        for b in itertools.product(range(0, M, q), repeat=mu):
            tot += 1
            if closed_form(list(b), k, w, q, M) != \
               [x % M for x in om.alpha_parent(list(b), k, w, q, M)]:
                bad += 1
        check(f"(C1) closed form == alpha_parent, q={q} mu={mu} k={k} w={w} N={N}",
              bad == 0, f"{tot - bad}/{tot} boxes")


# ------------------------------------------------- tree with omega bookkeeping (raw pairs)
def phi(coords, q, M, children, cof_deg, m):
    sp = 0
    f = [1]
    for (mu, k, w) in children:
        f = om.pmul(f, om.alpha_parent([x % M for x in coords[sp:sp + mu]], k, w, q, M), M)
        sp += mu
    if cof_deg:
        f = om.pmul(f, [x % M for x in coords[sp:sp + cof_deg]] + [1], M)
    return [x % M for x in (f + [0] * m)[:m]]


def run_tree(q, N, m, children, cof_deg, F, collect_samples=3):
    """Level-by-level raw tree over target F (length-m ints).  Returns per-level records:
    (n, #nodes, K-set, dead, #next, aggregate-support, I_n, omega-fibre-multiset),
    sampled (node, level) pairs, and the leaves."""
    s = sum(mu for (mu, k, w) in children)
    ncoords = s + cof_deg
    nodes = [tuple([0] * ncoords)]
    recs, samples = [], []
    for n in range(1, N):
        Mn1 = q ** (n + 1)
        Ftr = tuple(x % Mn1 for x in F)
        digit_split = list(itertools.product(range(q), repeat=ncoords))
        aggregate = Counter()
        omega_hist = Counter()
        sizes, new_nodes, dead = set(), [], 0
        live_children = {}
        for node in nodes:
            buckets = Counter()
            hits = []
            for split in digit_split:
                lift = tuple((node[i] + split[i] * q ** n) % Mn1 for i in range(ncoords))
                key = tuple(phi(lift, q, Mn1, children, cof_deg, m))
                buckets[key] += 1
                if key == Ftr:
                    hits.append(lift)
            base = tuple(phi(node, q, Mn1, children, cof_deg, m))
            gd = tuple((Ftr[i] - base[i]) % Mn1 for i in range(m))
            assert all(x % (q ** n) == 0 for x in gd)
            omega = tuple((gd[i] // q ** n) % q for i in range(s))     # mod W = first s coords
            omega_hist[omega] += 1
            aggregate.update(buckets)
            sizes |= set(buckets.values())
            if hits:
                live_children[node] = hits
            else:
                dead += 1
            new_nodes.extend(hits)
        recs.append((n + 1, len(nodes), sorted(sizes), dead, len(new_nodes),
                     len(aggregate), len(omega_hist), sorted(omega_hist.values())))
        picks = sorted(live_children)[:collect_samples]
        samples.append((n, [(y, live_children[y]) for y in picks]))
        nodes = new_nodes
        if not nodes:
            break
    return recs, samples, nodes


# ----------------------------------------------------- C2: GRADE columns at sampled nodes
def block_c2(q, N, m, children, cof_deg, F, tag):
    s = sum(mu for (mu, k, w) in children)
    ncoords = s + cof_deg
    recs, samples, _ = run_tree(q, N, m, children, cof_deg, F)
    bad = tot = 0
    for (n, pairs) in samples:
        Mn1 = q ** (n + 1)
        for (node, _) in pairs:
            base = phi(node, q, Mn1, children, cof_deg, m)
            for i in range(ncoords):
                lift = tuple((node[j] + (q ** n if j == i else 0)) % Mn1
                             for j in range(ncoords))
                out = phi(lift, q, Mn1, children, cof_deg, m)
                col = tuple(((out[j] - base[j]) % Mn1) // q ** n % q for j in range(m))
                want = tuple(0 for _ in range(m)) if i < s else \
                    tuple(1 if j == s + (i - s) else 0 for j in range(m))
                tot += 1
                if col != want:
                    bad += 1
    check(f"(C2) GRADE columns exact (child->0, cofactor c->X^(s+c)) [{tag}]",
          bad == 0, f"{tot - bad}/{tot} columns over sampled nodes, all levels")
    return recs, samples


# --------------------------------------- C3: honest V_n via SNF with left transform
def snf_left(A, q, NB):
    M = q ** NB
    A = [[x % M for x in row] for row in A]
    rows = len(A)
    L = [[1 if i == j else 0 for j in range(rows)] for i in range(rows)]
    cols = len(A[0])
    slots = min(rows, cols)
    es = []
    r0 = 0
    while r0 < slots:
        best, bi, bj = NB, -1, -1
        for i in range(r0, rows):
            for j in range(r0, cols):
                v = bat.vq(A[i][j], q, NB)
                if v < best:
                    best, bi, bj = v, i, j
        if bi < 0:
            es.extend([NB] * (slots - r0))
            break
        A[r0], A[bi] = A[bi], A[r0]
        L[r0], L[bi] = L[bi], L[r0]
        for i in range(rows):
            A[i][r0], A[i][bj] = A[i][bj], A[i][r0]
        piv = A[r0][r0]
        u = piv // q ** best
        uinv = pow(u, -1, q ** (NB - best)) if best < NB else 1
        for i in range(rows):                       # clear the column by ROW ops
            if i != r0 and A[i][r0] % M:
                t = (A[i][r0] // q ** best * uinv) % (q ** (NB - best))
                for j in range(cols):
                    A[i][j] = (A[i][j] - t * A[r0][j]) % M
                for j in range(rows):
                    L[i][j] = (L[i][j] - t * L[r0][j]) % M
        for j in range(r0 + 1, cols):               # clear the row by COLUMN ops (R only)
            if A[r0][j] % M:
                t = (A[r0][j] // q ** best * uinv) % (q ** (NB - best))
                for i in range(rows):
                    A[i][j] = (A[i][j] - t * A[i][r0]) % M
        es.append(best)
        r0 += 1
    return es, L


def mat_inv(L, q, NB):
    M = q ** NB
    n = len(L)
    A = [row[:] + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(L)]
    for c in range(n):
        piv = next(i for i in range(c, n) if A[i][c] % q)
        A[c], A[piv] = A[piv], A[c]
        inv = pow(A[c][c], -1, M)
        A[c] = [(x * inv) % M for x in A[c]]
        for i in range(n):
            if i != c and A[i][c]:
                t = A[i][c]
                A[i] = [(x - t * y) % M for x, y in zip(A[i], A[c])]
    return [row[n:] for row in A]


def rank_modq(vs, q):
    vs = [list(v) for v in vs if any(x % q for x in v)]
    r = 0
    for c in range(len(vs[0]) if vs else 0):
        piv = next((i for i in range(r, len(vs)) if vs[i][c] % q), None)
        if piv is None:
            continue
        vs[r], vs[piv] = vs[piv], vs[r]
        inv = pow(vs[r][c], -1, q)
        vs[r] = [(x * inv) % q for x in vs[r]]
        for i in range(len(vs)):
            if i != r and vs[i][c] % q:
                t = vs[i][c]
                vs[i] = [(x - t * y) % q for x, y in zip(vs[i], vs[r])]
        r += 1
        if r == len(vs):
            break
    return r


def block_c3(q, N, m, children, cof_deg, F, recs, leaves, tag):
    s = sum(mu for (mu, k, w) in children)
    NB = N + 2
    MB = q ** NB
    leaf = sorted(leaves)[0]
    Ps, sp = [], 0
    for (mu, k, w) in children:
        Ps.append(tuple(om.alpha_parent([x % MB for x in leaf[sp:sp + mu]], k, w, q, MB)))
        sp += mu
    Q = [x % MB for x in leaf[sp:sp + cof_deg]] + [1]
    A = bat.sylvester_matrix(q, NB, m, children, Ps, cof_deg, Q)
    es, L = snf_left(A, q, NB)
    Linv = mat_inv(L, q, NB)
    dirs = [[Linv[i][j] % q for i in range(m)] for j in range(m)]   # column j
    ok_sched, det = True, []
    ok_agg = True
    for (lvl, nn, K, dd, nx, agg, In, fib) in recs:
        n = lvl - 1
        sel = [dirs[i][:s] for i in range(len(es)) if es[i] <= n]
        predV = q ** rank_modq(sel, q) if sel else 1
        det.append(f"n={n}: I_n={In} V_n={predV}")
        if In != predV:
            ok_sched = False
        if agg != (q ** cof_deg) * In:
            ok_agg = False
    check(f"(C3) schedule law: observed I_n == #V_n(T_x) at every level [{tag}]",
          ok_sched, "; ".join(det) + f"; exponents(cap {NB})={sorted(es)}")
    check(f"(C3b) aggregate support == q^r * I_n at every level [{tag}]", ok_agg)
    # C7: GRADE fixes the target directions missing from the exponent-only interface.
    # In coefficient order, quotienting by W discards the last r coordinates, so the
    # quotient direction of A_i is dirs[i][:s].
    e1 = [i for i, e in enumerate(es) if e == 1]
    e1_in_W = all(not any(x % q for x in dirs[i][:s]) for i in e1)
    e1_basis_W = (len(e1) == cof_deg and rank_modq([dirs[i] for i in e1], q) == cof_deg)
    complement_basis = rank_modq([dirs[i][:s] for i, e in enumerate(es) if e > 1], q) == s
    dim_rows = []
    dim_formula = True
    for n in range(1, N):
        actual = rank_modq([dirs[i][:s] for i, e in enumerate(es) if e <= n], q)
        predicted = sum(e <= n for e in es) - cof_deg
        dim_rows.append(f"n={n}:{actual}={predicted}")
        dim_formula &= actual == predicted
    check(f"(C7) TDC: e=1 directions form W and remaining directions basis mod W [{tag}]",
          e1_in_W and e1_basis_W and complement_basis,
          f"#e1={len(e1)}, dimW={cof_deg}, quotient-rank={s}")
    check(f"(C7b) dim V_n == #{{e_i<=n}}-r at every level [{tag}]", dim_formula,
          "; ".join(dim_rows))
    info(f"[{tag}] truncated exponent list at fibre base: {sorted(min(e, N) for e in es)}")


# ------------------------------------ C4/C5: tower affinity and fibrewise coset sweep
def omega_of(x, F, q, n, m, s, children, cof_deg):
    Mn1 = q ** (n + 1)
    out = phi(x, q, Mn1, children, cof_deg, m)
    gd = [(F[i] % Mn1 - out[i]) % Mn1 for i in range(m)]
    if any(v % (q ** n) for v in gd):
        return None
    return tuple((gd[i] // q ** n) % q for i in range(s))


def block_c45(q, N, m, children, cof_deg, F, samples, tag):
    s = sum(mu for (mu, k, w) in children)
    slope1 = []
    sp = 0
    for (mu, k, w) in children:
        if k == 1:
            slope1.append(sp + mu - 1)
        sp += mu
    lm_in_W = cof_deg >= 1          # X^{m-1} in W iff r>=1
    bad4 = tot4 = 0
    bad5 = tot5 = 0
    for (nm1, pairs) in samples:
        n = nm1 + 1
        if n >= N:
            continue
        for (y, kids) in pairs:
            x0 = kids[0]
            w0 = omega_of(x0, F, q, n, m, s, children, cof_deg)
            oms = Counter()
            for x in kids:
                u = tuple(((x[i] - x0[i]) % q ** n) // q ** (n - 1) % q for i in range(s))
                sig = sum(u[i] for i in slope1) % q
                w = omega_of(x, F, q, n, m, s, children, cof_deg)
                tot4 += 1
                pred = list(w0)
                if not lm_in_W and s == m and slope1:
                    pred[m - 1] = (pred[m - 1] - sig) % q
                if lm_in_W or not slope1:
                    predt = tuple(w0)
                else:
                    predt = tuple(pred)
                if w != predt:
                    bad4 += 1
                oms[w] += 1
            tot5 += 1
            vals = sorted(oms.values())
            csz = len(oms)
            okc = (len(set(vals)) == 1) and (csz in (1, q)) if slope1 and not lm_in_W \
                else (csz == 1)
            if not okc:
                bad5 += 1
    check(f"(C4) omega across K-fibre == omega(x0) - sigma(u)X^(m-1) mod W [{tag}]",
          bad4 == 0, f"{tot4 - bad4}/{tot4} children over sampled fibres, all levels")
    check(f"(C5) K-fibre omega-multiset = one uniformly-covered coset of Im(Lbar) [{tag}]",
          bad5 == 0, f"{tot5 - bad5}/{tot5} fibres")


# ---------------------------------------------------------------- C6: non-genre probe
def block_c6():
    q, N, m, children, cof_deg = 2, 5, 3, [(2, 1, 1)], 1
    M = q ** N
    im, gh, det = bat.child_images(q, N, 2, 1, 1)
    cofs = [list(c) + [1] for c in itertools.product(range(0, M, q), repeat=1)]
    hist = Counter()
    for P in im:
        for Qp in cofs:
            f = om.pmul(list(P), Qp, M)
            hist[tuple(f[:m])] += 1
    wanted = frozenset(children)
    nong = [c for c in sorted(hist)
            if (lambda g: g in ("DRAIN", "BAD") or g[0] != wanted)(
                om.genre_of(list(c) + [1], q, N))]
    cls = nong[len(nong) // 2]
    recs, _, leaves = run_tree(q, N, m, children, cof_deg, list(cls))
    uni = all(len(set(f)) <= 1 for (_, _, _, _, _, _, _, f) in recs)
    info(f"(C6) NON-genre CELL-1 tower {cls} (genre_of={om.genre_of(list(cls) + [1], q, N)}):"
         f" per-level omega-fibre multisets "
         + "; ".join(f"n={lvl - 1}:{f}" for (lvl, _, _, _, _, _, _, f) in recs)
         + f"; leaves={len(leaves)}; sibling-uniformity {'HOLDS' if uni else 'FAILS'} here")


def main():
    print("h116b4_lift_cert (unit MLIFT, 2026-08-26) -- II-a/II-b certificates")
    print("-- C1: the closed form (1.1) against alpha_parent")
    block_c1()
    cells = [
        (2, 5, 3, [(2, 1, 1)], 1, (16, 4, 0), "CELL-1"),
        (3, 5, 4, [(2, 1, 1), (2, 1, 2)], 0, (81, 0, 9, 0), "CELL-2"),
        (2, 7, 4, [(2, 1, 1), (2, 2, 1)], 0, (64, 0, 4, 0), "CELL-4"),
    ]
    expect = {"CELL-1": 32, "CELL-2": 59049, "CELL-4": 8192}
    for (q, N, m, children, cof_deg, F, tag) in cells:
        print(f"-- {tag}: q={q} N={N} m={m} L={children} r={cof_deg} target={F}")
        recs, samples = block_c2(q, N, m, children, cof_deg, list(F), tag)
        _, _, leaves = run_tree(q, N, m, children, cof_deg, list(F))
        check(f"(tree) leaf count == battery ({expect[tag]}) [{tag}]",
              len(leaves) == expect[tag], f"leaves={len(leaves)}")
        block_c3(q, N, m, children, cof_deg, list(F), recs, leaves, tag)
        block_c45(q, N, m, children, cof_deg, list(F), samples, tag)
    print("-- C6: non-genre tower probe (info)")
    block_c6()
    print()
    n = len(FAILED)
    print(f"==== {n} failed ====" if n else "==== ALL CHECKS PASSED ====")
    return 1 if n else 0


if __name__ == "__main__":
    sys.exit(main())
