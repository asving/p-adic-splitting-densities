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
C8  [MLF2 2026-08-27] exhaustive reachable-target scan: sibling uniformity and the
    schedule law hold for every reachable target in two complete small towers, not only
    for the selected genre targets.
C9  [MLF2 2026-08-27] peel-packaging model: arbitrary q^N-congruent lifts have cofactor
    reduction X^r and canonicalizing every coordinate preserves the planted product class.
C10 [MLF2 2026-08-27] exact secant identity and mixed-Sylvester flag probe: sampled
    terminal/node pairs have the tangent Smith list and the same saturated quotient flag.
C11 [FML1 2026-08-27] Lemma BP (base-point transport): omega_n on S_n(F) is the
    translate by omega_n(x) of the digit map of Psi_x(kappa) = Phi(x) - Phi(x-kappa)
    at ANY base x in S_n(F) -- the identity that makes MLIFT-1 target-unconditional.
C12 [FML1 2026-08-27] global uniformity scans: U(n|F) for EVERY reachable target class
    at EVERY level, in q=3/q=5 hunt cells (where squares are not linear, so a
    quadratic obstruction digit would skew fibres) and q=2 cross-check cells.
C13 [FML1 2026-08-27] MSF depth probe: V_j(D_{x,y}) vs V_j(T_x) as a function of the
    depth n of y and the grade j; hard check in the load-bearing range j <= n.
C14 [FML1 2026-08-27] Lemma REM (cofactor elimination): S_n(F) is in b-projection
    bijection with the child divisibility tower {b : prod P_p(b_p) | F mod q^n}, and
    omega_n is the remainder digit.
C15 [FML1 2026-08-27] Lemma RES: v(Res(P_p, P_p')) = mu mu' min(k,k') exactly,
    b-independent; plus an (info) CRT decoupling depth table.

Run: python3 verification/openmath/h116b4_lift_cert.py   (~5-10 min)
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


# ---------------------- C8/C9: exhaustive target scan and packaging model
def reachable_witnesses(q, N, m, children, cof_deg):
    M = q ** N
    ncoords = sum(mu for (mu, _, _) in children) + cof_deg
    out = {}
    for x in itertools.product(range(0, M, q), repeat=ncoords):
        F = tuple(phi(x, q, M, children, cof_deg, m))
        out.setdefault(F, x)
    return out


def schedule_at_leaf(q, N, m, children, cof_deg, leaf):
    s = sum(mu for (mu, _, _) in children)
    NB = N + 2
    MB = q ** NB
    Ps, sp = [], 0
    for (mu, k, w) in children:
        Ps.append(tuple(om.alpha_parent([x % MB for x in leaf[sp:sp + mu]],
                                        k, w, q, MB)))
        sp += mu
    Q = [x % MB for x in leaf[sp:sp + cof_deg]] + [1]
    A = bat.sylvester_matrix(q, NB, m, children, Ps, cof_deg, Q)
    es, L = snf_left(A, q, NB)
    Linv = mat_inv(L, q, NB)
    dirs = [[Linv[i][j] % q for i in range(m)] for j in range(m)]
    return tuple(q ** rank_modq([dirs[i][:s] for i, e in enumerate(es) if e <= n], q)
                 for n in range(1, N))


def block_c89(q, N, m, children, cof_deg, tag):
    M = q ** N
    witnesses = reachable_witnesses(q, N, m, children, cof_deg)
    bad_uni = bad_sched = bad_pack = 0
    wanted = frozenset(children)
    genre_targets = 0
    schedule_families = Counter()
    for F, witness in sorted(witnesses.items()):
        recs, _, leaves = run_tree(q, N, m, children, cof_deg, list(F), collect_samples=0)
        observed = tuple(row[6] for row in recs)
        predicted = schedule_at_leaf(q, N, m, children, cof_deg, sorted(leaves)[0])
        schedule_families[(observed, predicted)] += 1
        bad_uni += not all(len(set(row[7])) <= 1 for row in recs)
        bad_sched += observed != predicted

        genre = om.genre_of(list(F) + [1], q, N)
        if genre not in ("DRAIN", "BAD") and genre[0] == wanted:
            genre_targets += 1
            # Integer-model version of GR-11's final conversion.  The witness is the
            # projected child/cofactor state.  Change it by q^N in every coordinate to
            # model arbitrary peel lifts, then canonicalize back to [0,q^N).
            lifted = tuple(x + (i + 1) * M for i, x in enumerate(witness))
            low_residue_zero = not any(phi(lifted, q, q, children, cof_deg, m))
            canonical_product = tuple(phi(witness, q, M, children, cof_deg, m)) == F
            replacement_product = tuple(phi(lifted, q, M, children, cof_deg, m)) == F
            cofactor_in_q = (all(x % q == 0 for x in lifted[-cof_deg:])
                             if cof_deg else True)
            bad_pack += not (low_residue_zero and canonical_product and
                             replacement_product and cofactor_in_q)
    check(f"(C8) U(n|F) for EVERY reachable target in the complete scan [{tag}]",
          bad_uni == 0, f"{len(witnesses) - bad_uni}/{len(witnesses)} targets")
    check(f"(C8b) I_n(F) == #V_n(T_x) for EVERY reachable target [{tag}]",
          bad_sched == 0,
          f"{len(witnesses) - bad_sched}/{len(witnesses)}; "
          f"{len(schedule_families)} schedule families")
    if genre_targets:
        check(f"(C9) peel lift -> projected states -> canonical sections preserves class [{tag}]",
              bad_pack == 0, f"{genre_targets - bad_pack}/{genre_targets} genre targets")
    else:
        info(f"(C9) packaging coverage [{tag}]: no target of the requested genre in this scan")


def block_c9_witness(q, N, m, children, cof_deg, F, witness, tag):
    M = q ** N
    wanted = frozenset(children)
    genre = om.genre_of(list(F) + [1], q, N)
    lifted = tuple(x + (i + 1) * M for i, x in enumerate(witness))
    low_residue_zero = not any(phi(lifted, q, q, children, cof_deg, m))
    canonical_product = tuple(phi(witness, q, M, children, cof_deg, m)) == tuple(F)
    replacement_product = tuple(phi(lifted, q, M, children, cof_deg, m)) == tuple(F)
    cofactor_in_q = (all(x % q == 0 for x in lifted[-cof_deg:]) if cof_deg else True)
    right_genre = genre not in ("DRAIN", "BAD") and genre[0] == wanted
    check(f"(C9b) packaging at the established genre target [{tag}]",
          right_genre and low_residue_zero and canonical_product and
          replacement_product and cofactor_in_q,
          f"genre_of={genre}")


# ------------------------------ C10: exact secants and mixed saturated flags
def factors_at(coords, q, M, children, cof_deg):
    out, sp = [], 0
    for (mu, k, w) in children:
        out.append(om.alpha_parent([z % M for z in coords[sp:sp + mu]], k, w, q, M))
        sp += mu
    out.append(([z % M for z in coords[sp:sp + cof_deg]] + [1])
               if cof_deg else [1])
    return out


def secant_matrix(q, NB, m, children, cof_deg, x, y):
    """Telescoping secant on Lambda=q*C.  Columns use q*E_j (and q*X^c)."""
    M = q ** NB
    fx = factors_at(x, q, M, children, cof_deg)
    fy = factors_at(y, q, M, children, cof_deg)
    cols = []
    for bi, (mu, k, w) in enumerate(children):
        _, lat = bat.planted_basis(q, NB, mu, k, w)
        for c in range(mu):
            z = list(lat[c])
            for j in range(bi):
                z = om.pmul(fx[j], z, M)
            for j in range(bi + 1, len(fx)):
                z = om.pmul(z, fy[j], M)
            cols.append((z + [0] * m)[:m])
    bi = len(children)
    for c in range(cof_deg):
        z = [0] * c + [q]
        for j in range(bi):
            z = om.pmul(fx[j], z, M)
        cols.append((z + [0] * m)[:m])
    return [[cols[j][i] % M for j in range(len(cols))] for i in range(m)]


def smith_flag(A, q, NB, s, N):
    es, L = snf_left(A, q, NB)
    Linv = mat_inv(L, q, NB)
    dirs = [[Linv[i][j] % q for i in range(len(A))] for j in range(len(A))]
    return es, [[dirs[i][:s] for i, e in enumerate(es) if e <= n]
                for n in range(1, N)]


def same_span(vs, ws, q):
    rv, rw = rank_modq(vs, q), rank_modq(ws, q)
    return rv == rw == rank_modq(vs + ws, q)


def block_c10(q, N, m, children, cof_deg, F, samples, leaves, tag):
    s = sum(mu for (mu, _, _) in children)
    NB, M = N + 2, q ** (N + 2)
    x = sorted(leaves)[0]
    fxs = factors_at(x, q, M, children, cof_deg)
    tangent = bat.sylvester_matrix(q, NB, m, children, fxs[:-1], cof_deg, fxs[-1])
    tes, tflags = smith_flag(tangent, q, NB, s, N)
    exact_ok = flags_ok = lists_ok = True
    total = 0
    for _, pairs in samples:
        for y, _ in pairs:
            A = secant_matrix(q, NB, m, children, cof_deg, x, y)
            ses, sflags = smith_flag(A, q, NB, s, N)
            lists_ok &= ses == tes
            flags_ok &= all(same_span(a, b, q) for a, b in zip(tflags, sflags))
            dx = [(a - b) % M for a, b in zip(x, y)]
            lhs = [(a - b) % M for a, b in
                   zip(phi(x, q, M, children, cof_deg, m),
                       phi(y, q, M, children, cof_deg, m))]
            rhs = [sum(A[i][j] * (dx[j] // q) for j in range(len(dx))) % M
                   for i in range(m)]
            exact_ok &= lhs == rhs
            total += 1
    check(f"(C10) exact product secant identity on sampled terminal/node pairs [{tag}]",
          exact_ok, f"{total} pairs")
    check(f"(C10b) mixed secants keep tangent Smith list and saturated quotient flag [{tag}]",
          lists_ok and flags_ok, f"{total} pairs; exponents={sorted(tes)}")


# ==================== FML1 (2026-08-27): C11-C15 extensions =====================
def tree_levels(q, N, m, children, cof_deg, F):
    """All canonical members of S_n(F), n = 1..N, as integer tuples < q^n."""
    nc = sum(mu for (mu, k, w) in children) + cof_deg
    zero = tuple([0] * nc)
    first = [zero] if all(v % q == 0 for v in phi(zero, q, q, children, cof_deg, m)
                          ) and all(f % q == 0 for f in F) else []
    levels = {1: first}
    for n in range(1, N):
        Mn1 = q ** (n + 1)
        Ftr = tuple(x % Mn1 for x in F)
        nxt = []
        for node in levels[n]:
            for split in itertools.product(range(q), repeat=nc):
                lift = tuple(node[i] + split[i] * q ** n for i in range(nc))
                if tuple(phi(lift, q, Mn1, children, cof_deg, m)) == Ftr:
                    nxt.append(lift)
        levels[n + 1] = nxt
        if not nxt:
            break
    return levels


def block_c11(q, N, m, children, cof_deg, F, levels, tag):
    """Lemma BP (base-point transport): for ANY base x in S_n(F) and every y in S_n(F),
    with the canonical lifts,  omega_n(y) = omega_n(x) + [Psi_x(x-y)/q^n mod q] mod W,
    where Psi_x(kappa) := Phi(x) - Phi(x - kappa) (= D_{x,x-kappa}(kappa) by SEC).
    Checked pointwise at every level 2 <= n < N with two independent base choices."""
    s = sum(mu for (mu, k, w) in children)
    bad = tot = 0
    for n in range(2, N):
        mem = levels.get(n, [])
        if not mem:
            continue
        Mn1 = q ** (n + 1)
        for x in {mem[0], mem[-1]}:
            wx = omega_of(x, F, q, n, m, s, children, cof_deg)
            px = phi(x, q, Mn1, children, cof_deg, m)
            for y in mem:
                py = phi(y, q, Mn1, children, cof_deg, m)
                psi = [(px[i] - py[i]) % Mn1 for i in range(m)]
                tot += 1
                if any(v % q ** n for v in psi):     # y in S_n forces Psi == 0 mod q^n
                    bad += 1
                    continue
                dig = tuple((psi[i] // q ** n) % q for i in range(s))
                wy = omega_of(y, F, q, n, m, s, children, cof_deg)
                if wy != tuple((wx[i] + dig[i]) % q for i in range(s)):
                    bad += 1
    check(f"(C11) BP: omega_n(y) == omega_n(x) + digit_n Psi_x(x-y) mod W [{tag}]",
          bad == 0, f"{tot - bad}/{tot} (base,y) pairs, levels 2..{N - 1}")


def block_c12(q, N, m, children, cof_deg, tag, max_report=3):
    """Global uniformity scan: at every level n, bucket ALL canonical level-n raw points
    z by Phi(z) mod q^n; within each bucket the digit map z -> [digit_n Phi(z)] mod W
    must have equal fibre sizes.  By the translation law 4.2 this is exactly U(n|F) for
    EVERY target lift F over every reachable class -- the complete MLIFT-1 scan."""
    s = sum(mu for (mu, k, w) in children)
    nc = s + cof_deg
    bad = buckets_tot = 0
    rows, worst = [], []
    for n in range(1, N):
        Mn1 = q ** (n + 1)
        buckets = {}
        for z in itertools.product(range(0, q ** n, q), repeat=nc):
            f = phi(z, q, Mn1, children, cof_deg, m)
            key = tuple(x % (q ** n) for x in f)
            dig = tuple((f[i] // q ** n) % q for i in range(s))
            buckets.setdefault(key, Counter())[dig] += 1
        nbad = sum(1 for h in buckets.values() if len(set(h.values())) > 1)
        for key, h in buckets.items():
            if len(set(h.values())) > 1 and len(worst) < max_report:
                worst.append((n, key, sorted(Counter(h.values()).items())))
        buckets_tot += len(buckets)
        bad += nbad
        rows.append(f"n={n}:{len(buckets)}cls" + (f"/{nbad}BAD" if nbad else ""))
    check(f"(C12) U(n|F) for EVERY reachable target class at EVERY level [{tag}]",
          bad == 0, "; ".join(rows))
    for (n, key, sizes) in worst:
        info(f"(C12) NON-UNIFORM witness [{tag}]: n={n} target-class={key} "
             f"(fibre-size, count)={sizes}")


def block_c13(q, N, m, children, cof_deg, F, levels, tag, cap=40):
    """MSF depth probe: x = a terminal presentation; for y in S_n(F) (canonical lifts,
    sampled), compare V_j(D_{x,y}) with V_j(T_x) at every grade j.  Hard check in the
    load-bearing range j <= n (what the schedule at level n consumes, cf. (6.7)); the
    beyond-depth pattern j > n is reported as discovery output."""
    s = sum(mu for (mu, k, w) in children)
    NB, M = N + 2, q ** (N + 2)
    leaves = levels.get(N, [])
    if not leaves:
        info(f"(C13) empty terminal fibre, skipped [{tag}]")
        return
    x = sorted(leaves)[0]
    fxs = factors_at(x, q, M, children, cof_deg)
    tangent = bat.sylvester_matrix(q, NB, m, children, fxs[:-1], cof_deg, fxs[-1])
    tes, tflags = smith_flag(tangent, q, NB, s, N)
    bad_load = tot = 0
    deep_fail, deep_tot, list_mismatch = Counter(), Counter(), Counter()
    for n in range(2, N):
        mem = levels.get(n, [])
        step = max(1, len(mem) // cap)
        for y in mem[::step]:
            A = secant_matrix(q, NB, m, children, cof_deg, x, y)
            ses, sflags = smith_flag(A, q, NB, s, N)
            tot += 1
            if [min(e, N) for e in ses] != [min(e, N) for e in tes]:
                list_mismatch[n] += 1
            for j in range(1, N):
                okj = same_span(tflags[j - 1], sflags[j - 1], q)
                if j <= n:
                    bad_load += not okj
                else:
                    deep_tot[(n, j)] += 1
                    deep_fail[(n, j)] += not okj
    check(f"(C13) MSF in the load-bearing range: V_j(D_x,y)==V_j(T_x), j<=depth(y) [{tag}]",
          bad_load == 0, f"{tot} sampled fibre points, depths 2..{N - 1}")
    fails = {k: v for k, v in deep_fail.items() if v}
    if fails or any(list_mismatch.values()):
        info(f"(C13) beyond-depth V_j mismatches [{tag}]: "
             + ("; ".join(f"n={n},j={j}:{v}/{deep_tot[(n, j)]}"
                          for (n, j), v in sorted(fails.items())) or "none")
             + "; truncated-Smith-list mismatches by depth: "
             + (", ".join(f"n={n}:{v}" for n, v in sorted(list_mismatch.items())) or "none"))
    else:
        info(f"(C13) V_j(D)==V_j(T_x) at ALL grades j<{N} and truncated Smith lists agree,"
             f" every sampled depth [{tag}]")


def polydiv_rem(F, P, M):
    """Remainder of division of F by MONIC P over Z/M (coeff lists, low to high)."""
    R = [x % M for x in F]
    dP = len(P) - 1
    for i in range(len(R) - 1, dP - 1, -1):
        c = R[i]
        if c:
            for j in range(dP + 1):
                R[i - dP + j] = (R[i - dP + j] - c * P[j]) % M
    return R[:dP]


def block_c14(q, N, m, children, cof_deg, F, levels, tag):
    """Lemma REM (cofactor elimination): the child-only divisibility tower
    R_n := { b : prod_p P_p(b_p) divides F mod q^n } is in bijection with S_n(F)
    (b-projection; the cofactor digit path is division-determined), and
    omega_n == [(F rem prod P_p)/q^n mod q] under V ~ F_q[X]_{<s}."""
    if cof_deg == 0:
        info(f"(C14) r=0: REM is the identity reformulation, skipped [{tag}]")
        return
    s = sum(mu for (mu, k, w) in children)
    Ffull = list(F) + [1]
    ok_count = ok_proj = ok_omega = True
    det = []
    for n in range(1, N):
        Mn1 = q ** (n + 1)
        Rn = {}
        for b in itertools.product(range(0, q ** n, q), repeat=s):
            P = [1]
            sp = 0
            for (mu, k, w) in children:
                P = om.pmul(P, om.alpha_parent(list(b[sp:sp + mu]), k, w, q, Mn1), Mn1)
                sp += mu
            rem = polydiv_rem(Ffull, P, Mn1)
            if all(v % q ** n == 0 for v in rem):
                Rn[b] = tuple((rem[i] // q ** n) % q for i in range(s))
        mem = levels.get(n, [])
        ok_count &= len(Rn) == len(mem)
        ok_proj &= set(Rn) == {tuple(y[i] % q ** n for i in range(s)) for y in mem}
        hist_R = Counter(Rn.values())
        hist_S = Counter(omega_of(y, F, q, n, m, s, children, cof_deg) for y in mem)
        ok_omega &= hist_R == hist_S
        det.append(f"n={n}:{len(Rn)}")
    check(f"(C14) REM: child divisibility tower == b-projection of S_n, all levels [{tag}]",
          ok_count and ok_proj, "; ".join(det))
    check(f"(C14b) REM: remainder digit histogram == omega_n histogram, all levels [{tag}]",
          ok_omega)


def block_c15(q, N, m, children, cof_deg, F, tag, nsamp=120, seed=116):
    """Lemma RES check (exact child-child resultant valuation, b-independent) plus an
    (info) CRT decoupling table: joint vs per-child divisibility depths."""
    import random
    if len(children) < 2:
        info(f"(C15) single child: no child-child resultant [{tag}]")
        return
    rng = random.Random(seed)
    NB, MB = N + 3, q ** (N + 3)
    bad = 0
    pairs = [(i, j) for i in range(len(children)) for j in range(i + 1, len(children))]
    for (i, j) in pairs:
        (mu1, k1, w1), (mu2, k2, w2) = children[i], children[j]
        cexp = mu1 * mu2 * min(k1, k2)
        for _ in range(nsamp):
            b1 = [q * rng.randrange(q ** (NB - 1)) for _ in range(mu1)]
            b2 = [q * rng.randrange(q ** (NB - 1)) for _ in range(mu2)]
            P1 = om.alpha_parent(b1, k1, w1, q, MB)
            P2 = om.alpha_parent(b2, k2, w2, q, MB)
            v = om.resultant_valuation(list(P1), list(P2), q, MB)
            bad += v != cexp
    check(f"(C15) RES: v(Res(P_p,P_p')) == mu*mu'*min(k,k') exactly, b-independent [{tag}]",
          bad == 0, f"{nsamp} samples x {len(pairs)} pairs")
    # (info) decoupling depth table on the two-child box at moderate precision
    (mu1, k1, w1), (mu2, k2, w2) = children[0], children[1]
    t = min(N - 1, 5 if q == 2 else 3)
    Mt = q ** t
    Ffull = list(F) + [1]
    table = Counter()
    for b in itertools.product(range(0, Mt, q), repeat=mu1 + mu2):
        P1 = om.alpha_parent(list(b[:mu1]), k1, w1, q, Mt)
        P2 = om.alpha_parent(list(b[mu1:]), k2, w2, q, Mt)
        r1, r2 = polydiv_rem(Ffull, P1, Mt), polydiv_rem(Ffull, P2, Mt)
        r12 = polydiv_rem(Ffull, om.pmul(P1, P2, Mt), Mt)
        tv = lambda rr: min((bat.vq(v, q, t) for v in rr), default=t)
        table[(tv(r1), tv(r2), tv(r12))] += 1
    top = ", ".join(f"{k}:{v}" for k, v in sorted(table.items())[:18])
    info(f"(C15) depth law table (t1,t2,t_joint):count at precision {t} [{tag}]: {top}")


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
        block_c10(q, N, m, children, cof_deg, list(F), samples, leaves, tag)
        block_c9_witness(q, N, m, children, cof_deg, list(F), sorted(leaves)[0], tag)
        levels = tree_levels(q, N, m, children, cof_deg, list(F))
        block_c11(q, N, m, children, cof_deg, list(F), levels, tag)
        block_c13(q, N, m, children, cof_deg, list(F), levels, tag)
        block_c14(q, N, m, children, cof_deg, list(F), levels, tag)
        block_c15(q, N, m, children, cof_deg, list(F), tag)
    print("-- C6: non-genre tower probe (info)")
    block_c6()
    print("-- C8/C9: complete reachable-target scans and peel packaging")
    block_c89(2, 5, 3, [(2, 1, 1)], 1, "CELL-1 ALL 96 TARGETS")
    block_c89(2, 5, 4, [(2, 1, 1), (2, 2, 1)], 0, "MIXED ALL 32 TARGETS")
    print("-- C12 [FML1]: global uniformity scans (q=3/q=5 hunt for quadratic-digit skew;")
    print("--            q=2 cross-checks of C8).  Every reachable class, every level.")
    hunts = [
        (3, 6, 3, [(2, 1, 1)], 1, "H1 q3 mu2 k1 r1 (grade-4/5 child*cofactor quadratics)"),
        (3, 5, 4, [(2, 1, 1), (2, 1, 2)], 0, "H2 q3 = CELL-2, ALL targets"),
        (3, 5, 4, [(3, 1, 1)], 1, "H3 q3 mu3 r1"),
        (3, 6, 3, [(2, 2, 1)], 1, "H4 q3 k2 r1"),
        (5, 5, 3, [(2, 1, 1)], 1, "H5 q5 mu2 k1 r1"),
        (2, 6, 4, [(3, 1, 1)], 1, "H6 q2 mu3 r1"),
        (3, 5, 4, [(2, 1, 1)], 2, "H7 q3 r2"),
        (2, 5, 3, [(2, 1, 1)], 1, "X1 q2 CELL-1 cross-check of C8"),
        (2, 5, 4, [(2, 1, 1), (2, 2, 1)], 0, "X2 q2 MIXED cross-check of C8"),
    ]
    for (q, N, m, children, cof_deg, tag) in hunts:
        block_c12(q, N, m, children, cof_deg, tag)
    print()
    n = len(FAILED)
    print(f"==== {n} failed ====" if n else "==== ALL CHECKS PASSED ====")
    return 1 if n else 0


if __name__ == "__main__":
    sys.exit(main())
