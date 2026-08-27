#!/usr/bin/env python3
"""
h116b4_smith_cert.py — unit MSMITH (2026-08-26): certificate for the GR-7 restricted
Smith IDENTIFICATION (docs/in-progress/H116B4_SMITH_PROOF_2026-08-26.md).

CONJECTURE C1 tested here: the truncated Smith exponent list of the restricted
multi-Sylvester matrix equals the ASSIGNMENT SPECTRUM of the genre-determined
Newton-polygon valuation pattern V:

    V[i,(p,j)]  = 1 + k_p*(mu_p - j) + conv(env(X - pi^k zhat)^j (+) env(P_p') (+) envQ)(i)
    V[i,(Q,j)]  = 1 + conv(all child envelopes)(i - j)
    beta_t      = min over t rows, t cols, bijections of  sum V[i, sigma(i)]
    e_t         = beta_t - beta_{t-1},   truncated list = sorted(min(e_t, N)).

env(P) for a child (mu,k) is the segment (0,k*mu)->(mu,0); envQ is the genre envelope
max_a(betaQ(k_a) - i*k_a)^+ pinned to (r,0).  V depends on (L, D, N, r) ONLY, so C1
implies GR-7 (genre-determined truncated list).  Both battery anchors and NEW cells
(third slope, three children, deg-2 cofactors, two genres in one cell, q=5) are run.

Exact arithmetic in Z/q^N.  Imports (no checks run at import): the certified helpers
OM2_h116b_gauge_resultant.py and the battery runs/wave-b/h116b4_battery.py (for
snf_valuations / sylvester_matrix / planted_basis — this file does NOT edit them).
Prime residue fields only: these runs certify instances, they prove nothing.

Extended by unit MSM2 (2026-08-27), BLOCK C: proof-oriented r=0 assignment/Hall
checks, the exact B5 counterexample to the former Schur/V-inheritance claim,
and exact example checks for GR-4a/b/c and GR-5.  The negative check is an
expected, pinned refutation and does not weaken Blocks A/B.

Run:  python3 verification/openmath/h116b4_smith_cert.py     (exit 0 iff all checks pass)
"""

import os
import sys
import time
import random
import itertools

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(REPO, "runs", "wave-b"))

import OM2_h116b_gauge_resultant as om   # pmul, alpha_parent, ord0_at, content_at, ...
import h116b4_battery as bt              # snf_valuations, sylvester_matrix, planted_basis

FAILED = []
INF = 10 ** 6


def check(name, ok, detail=""):
    print(("  ok    " if ok else "  FAIL  ") + name + (("  -- " + detail) if detail else ""))
    if not ok:
        FAILED.append(name)


def info(msg):
    print("  info  " + msg)


# ---------------------------------------------------------------------------------
# The genre-determined valuation pattern V and its assignment spectrum.
# Envelopes are dense lists env[0..deg]; min-plus convolution = Minkowski sum.
# ---------------------------------------------------------------------------------
def conv(a, b):
    out = [INF] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if x + y < out[i + j]:
                out[i + j] = x + y
    return out


def child_env(mu, k):
    """Envelope of a planted factor: the segment (0, k*mu) -> (mu, 0)."""
    return [k * (mu - i) for i in range(mu + 1)]


def centered_pow_env(j, k):
    """Envelope of (X - pi^k zhat)^j: the segment (0, k*j) -> (j, 0)."""
    return [k * (j - i) for i in range(j + 1)]


def cofactor_env(r, betaQ):
    """Genre envelope of an admissible cofactor: max_a(betaQ[k_a] - i*k_a)^+ , (r,0) pinned.
    betaQ: dict slope -> content.  For r = 0 this is [0] (the constant 1)."""
    return [max([0] + [betaQ[k] - i * k for k in betaQ]) if i < r else 0
            for i in range(r + 1)]


def build_V(children, r, betaQ):
    """V[i][col] for the restricted matrix; columns ordered as in bt.sylvester_matrix:
    child (p, j<mu_p) blocks in order, then cofactor slots j<r.  m = sum mu + r rows."""
    m = sum(mu for (mu, k, w) in children) + r
    qenv = cofactor_env(r, betaQ)
    cols = []
    for idx, (mu, k, w) in enumerate(children):
        other = [0]
        for jdx, (mu2, k2, w2) in enumerate(children):
            if jdx != idx:
                other = conv(other, child_env(mu2, k2))
        other = conv(other, qenv)
        for j in range(mu):
            e = conv(centered_pow_env(j, k), other)
            cols.append([1 + k * (mu - j) + (e[i] if i < len(e) else INF)
                         for i in range(m)])
    allp = [0]
    for (mu, k, w) in children:
        allp = conv(allp, child_env(mu, k))
    for j in range(r):
        cols.append([1 + (allp[i - j] if 0 <= i - j < len(allp) else INF)
                     for i in range(m)])
    return [[cols[c][i] for c in range(m)] for i in range(m)]  # V[row][col]


def assignment_spectrum(V, N):
    """beta_t = min assignment over t x t submatrices; returns capped [min(e_t, N)] sorted."""
    m = len(V)
    beta = [0]
    for t in range(1, m + 1):
        best = INF
        for rows in itertools.combinations(range(m), t):
            for cs in itertools.combinations(range(m), t):
                for perm in itertools.permutations(cs):
                    s = 0
                    for i, c in zip(rows, perm):
                        s += V[i][c]
                        if s >= best:
                            break
                    if s < best:
                        best = s
        beta.append(best)
    es = [beta[t] - beta[t - 1] for t in range(1, m + 1)]
    return sorted(min(e, N) for e in es)


def assignment_betas_dp(V):
    """All subassignment optima by a row-scan DP (exact, O(m 2^m)).

    Unlike assignment_spectrum this also exposes the partial sums beta_t.  It is
    used below to sweep abstract r=0 slope configurations beyond the small
    factorial-time battery cells.
    """
    m = len(V)
    dp = [INF] * (1 << m)
    dp[0] = 0
    for row in range(m):
        nxt = dp[:]                         # do not use this row
        for mask, old in enumerate(dp):
            if old >= INF:
                continue
            for col in range(m):
                if not (mask >> col) & 1:
                    nm = mask | (1 << col)
                    nxt[nm] = min(nxt[nm], old + V[row][col])
        dp = nxt
    return [min(dp[mask] for mask in range(1 << m) if mask.bit_count() == t)
            for t in range(m + 1)]


def r0_tail_values(children):
    """The uncapped C2 values for r=0, as global descending-slope tails."""
    weights = sorted((k for (mu, k, w) in children for _ in range(mu)), reverse=True)
    return [1 + sum(weights[i:]) for i in range(len(weights))]


def r0_deadlines(children):
    """(deadline,column) for the equality graph V[i,c] = 1 + slope-tail(i).

    A column (p,j), with d=mu_p-j deleted copies of k_p, has equality in every
    row i <= #{child slope slots >= k_p} - d.
    """
    out, col = [], 0
    for mu, k, w in children:
        upper = sum(mu2 for (mu2, k2, w2) in children if k2 >= k)
        for j in range(mu):
            out.append((upper - (mu - j), col))
            col += 1
    return out


# ---------------------------------------------------------------------------------
# shared: genre reading -> betaQ -> predicted list (cached per genre)
# ---------------------------------------------------------------------------------
def betaQ_of_genre(children, contents):
    """betaQ[k_a] = D(k_a) - sum_p mu_p*min(k_p,k_a); admissibility makes this >= 0."""
    return {k: contents[k] - sum(mu2 * min(k2, k) for (mu2, k2, w2) in children)
            for k in set(k for (mu, k, w) in children)}


def predicted_of_genre(children, r, contents, N):
    return assignment_spectrum(build_V(children, r, betaQ_of_genre(children, contents)), N)


def closed_form_C2(children, r, contents, N):
    """CONJECTURE C2: sorted({1}^r  u  U_a {1+D_a - k_a*i : t_a <= i < t_a+s_a}), cap N,
    where blocks a are the slopes, s_a = sum of mu over block a, D_a the block content,
    and t_a = sum of s_b over blocks with k_b > k_a (descending-slope stacking)."""
    slopes = sorted(set(k for (mu, k, w) in children))
    s = {k: sum(mu for (mu, k2, w) in children if k2 == k) for k in slopes}
    out = [1] * r
    for k in slopes:
        t = sum(s[k2] for k2 in slopes if k2 > k)
        out += [1 + contents[k] - k * i for i in range(t, t + s[k])]
    return sorted(min(e, N) for e in out)


# ---------------------------------------------------------------------------------
# BLOCK C — proof-oriented checks for the new MSM2 lemmas/counterexample.
# ---------------------------------------------------------------------------------
def check_r0_assignment_lemma(children, tag):
    """Check every inequality and Hall witness used in the paper proof of GR-7b-I (r=0)."""
    contents = {k: sum(mu2 * min(k2, k) for (mu2, k2, w2) in children)
                for k in set(k for (mu, k, w) in children)}
    V = build_V(children, 0, betaQ_of_genre(children, contents))
    tails = r0_tail_values(children)       # decreasing with the row index
    m = len(tails)
    lower = all(V[i][c] >= tails[i] for i in range(m) for c in range(m))
    deadlines = sorted(r0_deadlines(children), reverse=True)
    witnesses, detail = True, ""
    for t in range(1, m + 1):
        rows = list(range(m - t, m))
        chosen = sorted(deadlines[:t])     # earliest row to smallest chosen deadline
        if any(deadline < row or V[row][col] != tails[row]
               for row, (deadline, col) in zip(rows, chosen)):
            witnesses = False
            detail = f"t={t}, rows={rows}, chosen={chosen}"
            break
    betas = assignment_betas_dp(V)
    wanted = [sum(sorted(tails)[:t]) for t in range(m + 1)]
    check(f"(C-r0) row lower bound + deadline Hall witnesses [{tag}]",
          lower and witnesses, detail)
    check(f"(C-r0) DP assignment beta_t == suffix-tail partial sums [{tag}]",
          betas == wanted, f"got={betas}, want={wanted}")
    check(f"(C-r0) tail form == C2 [{tag}]",
          sorted(tails) == closed_form_C2(children, 0, contents, INF),
          f"tails={sorted(tails)} C2={closed_form_C2(children, 0, contents, INF)}")


def sweep_r0_assignment_lemma():
    """73 bounded multisets of 1--3 abstract (mu,k) types, mu=2,3 and k=1,2,3."""
    types = [(mu, k) for mu in (2, 3) for k in (1, 2, 3)]
    tested, bad, first = 0, 0, ""
    for nchild in (1, 2, 3):
        for combo in itertools.combinations_with_replacement(types, nchild):
            children = [(mu, k, idx + 1) for idx, (mu, k) in enumerate(combo)]
            m = sum(mu for mu, k in combo)
            if m > 8:
                continue
            contents = {k: sum(mu2 * min(k2, k) for (mu2, k2, w2) in children)
                        for k in set(k for (mu, k, w) in children)}
            V = build_V(children, 0, betaQ_of_genre(children, contents))
            tails = r0_tail_values(children)
            deadlines = sorted(r0_deadlines(children), reverse=True)
            ok = all(V[i][c] >= tails[i] for i in range(m) for c in range(m))
            for t in range(1, m + 1):
                rows = range(m - t, m)
                chosen = sorted(deadlines[:t])
                ok &= all(deadline >= row and V[row][col] == tails[row]
                          for row, (deadline, col) in zip(rows, chosen))
            wanted = [sum(sorted(tails)[:t]) for t in range(m + 1)]
            ok &= assignment_betas_dp(V) == wanted
            tested += 1
            if not ok:
                bad += 1
                if not first:
                    first = f"children={children}"
    check("(C-r0-sweep) proof schema over all abstract slope multisets",
          bad == 0 and tested == 73, f"{tested} configurations" if not bad else first)


def cofactor_schur(A, q, N, child_degree, r):
    """Clear the monic cofactor staircase, returning its child Schur block."""
    M = q ** N
    B = [[x % M for x in row] for row in A]
    for j in range(r - 1, -1, -1):
        pivot_row, pivot_col = child_degree + j, child_degree + j
        pivot = B[pivot_row][pivot_col]
        assert pivot == q % M                # product of the children is monic
        for col in range(child_degree):
            entry = B[pivot_row][col]
            assert entry % q == 0
            mult = entry // q
            for row in range(pivot_row + 1):
                B[row][col] = (B[row][col] - mult * B[row][pivot_col]) % M
    return [row[:child_degree] for row in B[:child_degree]]


def check_schur_counterexample():
    """Certified B5 refutation of the original GR-7b-0 V-inheritance clause."""
    q, N = 2, 10
    children = [(2, 1, 1), (2, 2, 1)]
    Q = [8, 1]
    M = q ** N
    Ps = [om.alpha_parent([0] * mu, k, w, q, M) for (mu, k, w) in children]
    A = bt.sylvester_matrix(q, N, 5, children, Ps, 1, Q)
    S = cofactor_schur(A, q, N, 4, 1)
    contents = {1: 5, 2: 8}
    V = build_V(children, 1, betaQ_of_genre(children, contents))
    measured = {(i, c): bt.vq(S[i][c], q, N) for i in range(4) for c in range(4)}
    violations = sorted((i, c, measured[i, c], V[i][c])
                        for i in range(4) for c in range(4)
                        if measured[i, c] < V[i][c])
    check("(C-Schur) B5 data are admissible", admissible(Q, q, N, children))
    check("(C-Schur) original GR-7b-0 V-inheritance is refuted (expected negative)",
          violations == [(0, 1, 8, 9), (2, 1, 4, 5)], f"violations={violations}")
    check("(C-Schur) refuting base still has the C2 Smith list",
          bt.snf_valuations(A, q, N) == [1, 3, 4, 7, 9],
          f"snf={bt.snf_valuations(A, q, N)}")


def resultant_int(f, g):
    """Exact integer resultant, with sign convention irrelevant to the checks."""
    m, n = len(f) - 1, len(g) - 1
    S = [[0] * (m + n) for _ in range(m + n)]
    for i in range(n):
        for j, a in enumerate(reversed(f)):
            S[i][i + j] = a
    for i in range(m):
        for j, a in enumerate(reversed(g)):
            S[n + i][i + j] = a
    return om.int_det(S)


def multi_sylvester_det(polys):
    """Determinant of (delta_i) |-> sum delta_i prod_{j != i} f_j, low-degree bases."""
    def imul(f, g):
        out = [0] * (len(f) + len(g) - 1)
        for i, a in enumerate(f):
            for j, b in enumerate(g):
                out[i + j] += a * b
        return out

    degrees = [len(f) - 1 for f in polys]
    total = sum(degrees)
    cols = []
    for idx, degree in enumerate(degrees):
        other = [1]
        for j, f in enumerate(polys):
            if j != idx:
                other = imul(other, f)
        for shift in range(degree):
            cols.append([0] * shift + other + [0] * (total - shift - len(other)))
    matrix = [[cols[c][i] for c in range(total)] for i in range(total)]
    return om.int_det(matrix)


def check_resultants_and_multisylvester():
    """Fresh exact examples for the proved GR-4a/b/c scaling and GR-5 identity."""
    q, big = 3, 3 ** 12
    pairs = [((2, 1, 1), [3, 6]), ((2, 1, 2), [6, 3]),
             ((2, 2, 1), [3, 0]), ((3, 2, 2), [3, 6, 0])]
    factors = []
    for (mu, k, w), b in pairs:
        factors.append(om.alpha_parent(b, k, w, q, big))
    pair_ok = True
    for i, p in enumerate(pairs):
        for j in range(i + 1, len(pairs)):
            mu, k, w = p[0]
            mu2, k2, w2 = pairs[j][0]
            if k == k2 and w == w2:        # same frame is outside GR-4a
                continue
            pair_ok &= om.resultant_valuation(factors[i], factors[j], q, big) == \
                mu * mu2 * min(k, k2)
    check("(C-GR4ab) planted pair resultant valuations, same/unequal slopes", pair_ok)

    q, N, M = 2, 10, 2 ** 18
    children = [(2, 1, 1), (2, 2, 1)]
    Q = [8, 1]
    cofactor_ok = True
    planted = []
    for mu, k, w in children:
        P = om.alpha_parent([0] * mu, k, w, q, M)
        planted.append(P)
        beta = min(bt.vq(Q[i], q, N) + k * i for i in range(len(Q)))
        cofactor_ok &= om.resultant_valuation(P, Q, q, M) == mu * beta
    check("(C-GR4c) planted/cofactor resultant valuation on B5", cofactor_ok)

    families = [
        [[1, 1], [2, -1, 1]],
        [[1, 1], [2, -1, 1], [3, 0, 1]],
        [[-1, 0, 1], [2, 1], [1, -2, 0, 1]],
        planted + [Q],
    ]
    det_ok, details = True, []
    for polys in families:
        lhs = multi_sylvester_det(polys)
        rhs = 1
        for i in range(len(polys)):
            for j in range(i + 1, len(polys)):
                rhs *= resultant_int(polys[i], polys[j])
        if abs(lhs) != abs(rhs):
            det_ok = False
            details.append((lhs, rhs))
    check("(C-GR5) exact multi-Sylvester determinant == product of pairwise resultants",
          det_ok, f"mismatches={details}")


# ---------------------------------------------------------------------------------
# BLOCK A — battery anchor cells, EXHAUSTIVE: predicted == true SNF at every base
# ---------------------------------------------------------------------------------
def block_anchor(q, N, m, children, cof_deg, tag, expect=None):
    M = q ** N
    imgs = [bt.child_images(q, N, mu, k, w)[0] for (mu, k, w) in children]
    cofs = ([list(c) + [1] for c in itertools.product(*[range(0, M, q)] * cof_deg)]
            if cof_deg else [[1]])
    wanted = frozenset(children)
    genre_cache, pred_cache = {}, {}
    nbase, bad, off_target = 0, 0, 0
    badex = ""
    for combo in itertools.product(*imgs):
        base = [1]
        for P in combo:
            base = om.pmul(base, list(P), M)
        for Qp in cofs:
            f = om.pmul(base, Qp, M) if cof_deg else base
            cls = tuple(f[:m])
            if cls not in genre_cache:
                genre_cache[cls] = om.genre_of(list(cls) + [1], q, N)
            g = genre_cache[cls]
            if g in ("DRAIN", "BAD") or g[0] != wanted:
                off_target += 1
                continue
            if g not in pred_cache:
                pred_cache[g] = predicted_of_genre(children, cof_deg, dict(g[1]), N)
                check(f"(C2) closed form == assignment spectrum, D={dict(g[1])} [{tag}]",
                      closed_form_C2(children, cof_deg, dict(g[1]), N) == pred_cache[g],
                      f"C2={closed_form_C2(children, cof_deg, dict(g[1]), N)}"
                      f" asgn={pred_cache[g]}")
            A = bt.sylvester_matrix(q, N, m, children, combo, cof_deg, list(Qp))
            true = bt.snf_valuations(A, q, N)
            nbase += 1
            if true != pred_cache[g]:
                bad += 1
                if not badex:
                    badex = f"true={true} pred={pred_cache[g]} D={dict(g[1])}"
    det = f"{nbase} bases in {len(pred_cache)} genre(s), {off_target} off-target"
    check(f"(A) predicted assignment-spectrum == true SNF, EXHAUSTIVE [{tag}]",
          bad == 0 and nbase > 0, badex if bad else det)
    for g, pl in sorted(pred_cache.items(), key=lambda x: sorted(x[0][1])):
        info(f"[{tag}] genre D={dict(g[1])}: predicted+observed list = {pl}")
    if expect is not None and pred_cache:
        got = sorted(pred_cache.values())[0]
        check(f"(A-pin) list == battery-recorded {expect} [{tag}]", got == list(expect),
              f"got {got}")


# ---------------------------------------------------------------------------------
# BLOCK B — NEW sampled cells: random + structured lifts, random admissible cofactors
# ---------------------------------------------------------------------------------
def admissible(Qp, q, N, children):
    nodrain = sum(k * mu for (mu, k, w) in children) + om.vq(Qp[0], q, N) < N
    childfree = all((om.ord0_at(Qp, q, N, k, z) or 0) < 2
                    for k in range(1, N + 1) for z in range(1, q))
    rootfree = all(om.ord0_at(Qp, q, N, k, w) == 0 for (mu, k, w) in children)
    return nodrain and childfree and rootfree


def structured_lifts(q, N, children):
    """Adversarial deterministic bases: all-zero, all-q, equal-across-children, deep-digit."""
    M = q ** N
    outs = []
    for pat in ["zero", "allq", "equal", "deep", "mix"]:
        bs = []
        for i, (mu, k, w) in enumerate(children):
            if pat == "zero":
                b = [0] * mu
            elif pat == "allq":
                b = [q] * mu
            elif pat == "equal":
                b = [q * (j + 1) % M for j in range(mu)]
            elif pat == "deep":
                b = [q ** (N - 1)] * mu
            else:
                b = [(q * (i + 1) * (j + 2)) % M for j in range(mu)]
            bs.append(b)
        outs.append(bs)
    return outs


def block_sampled(q, N, m, children, cof_deg, tag, nsamp=40, seed=20260826):
    M = q ** N
    rng = random.Random(seed)
    wanted = frozenset(children)
    lifts = structured_lifts(q, N, children)
    while len(lifts) < nsamp:
        lifts.append([[q * rng.randrange(q ** (N - 1)) for _ in range(mu)]
                      for (mu, k, w) in children])
    cof_pool = []
    if cof_deg:
        tries = 0
        while len(cof_pool) < min(8, nsamp) and tries < 4000:
            tries += 1
            Qp = [q * rng.randrange(q ** (N - 1)) for _ in range(cof_deg)] + [1]
            if admissible(Qp, q, N, children):
                cof_pool.append(Qp)
        if not cof_pool:
            check(f"(B) found admissible cofactors [{tag}]", False, f"{tries} tries")
            return
    else:
        cof_pool = [[1]]
    pred_cache, nbase, bad, badex, genres = {}, 0, 0, "", set()
    for bs in lifts:
        Ps = [tuple(om.alpha_parent(b, k, w, q, M))
              for b, (mu, k, w) in zip(bs, children)]
        for Qp in cof_pool:
            f = [1]
            for P in Ps:
                f = om.pmul(f, list(P), M)
            f = om.pmul(f, Qp, M)
            g = om.genre_of(f[:m] + [1], q, N)
            if g in ("DRAIN", "BAD") or g[0] != wanted:
                check(f"(B) admissible pair lands in the target genre [{tag}]", False,
                      f"genre={g if isinstance(g, str) else 'other child set'}")
                return
            genres.add(g)
            if g not in pred_cache:
                pred_cache[g] = predicted_of_genre(children, cof_deg, dict(g[1]), N)
                check(f"(C2) closed form == assignment spectrum, D={dict(g[1])} [{tag}]",
                      closed_form_C2(children, cof_deg, dict(g[1]), N) == pred_cache[g],
                      f"C2={closed_form_C2(children, cof_deg, dict(g[1]), N)}"
                      f" asgn={pred_cache[g]}")
            A = bt.sylvester_matrix(q, N, m, children, Ps, cof_deg, list(Qp))
            true = bt.snf_valuations(A, q, N)
            nbase += 1
            if true != pred_cache[g]:
                bad += 1
                if not badex:
                    badex = f"true={true} pred={pred_cache[g]} D={dict(g[1])}"
    check(f"(B) predicted == true SNF over {nbase} sampled bases [{tag}]",
          bad == 0 and nbase > 0, badex if bad else
          f"{len(genres)} genre(s), {len(cof_pool)} cofactor(s), {len(lifts)} lift tuples")
    for g in sorted(genres, key=lambda g: sorted(g[1])):
        info(f"[{tag}] genre D={dict(g[1])}: list = {pred_cache[g]}")


def main():
    print("H.116b4 Smith identification certificate (MSMITH + MSM2, 2026-08-27)")
    t0 = time.time()
    print("-- BLOCK A: battery anchors, exhaustive")
    block_anchor(2, 5, 3, [(2, 1, 1)], 1, "CELL-1 q2 N5", expect=(1, 3, 4))
    block_anchor(3, 5, 4, [(2, 1, 1), (2, 1, 2)], 0, "CELL-2 q3 N5", expect=(2, 3, 4, 5))
    block_anchor(2, 7, 4, [(2, 1, 1), (2, 2, 1)], 0, "CELL-4 q2 N7", expect=(2, 3, 5, 7))

    print("-- BLOCK B: new sampled cells (structured + random lifts)")
    block_sampled(3, 10, 4, [(2, 2, 1), (2, 2, 2)], 0, "B1 equal-slope k=2 q3 N10")
    block_sampled(3, 9, 4, [(2, 2, 1), (2, 2, 2)], 0, "B1c cap-binding N9")
    block_sampled(5, 8, 6, [(2, 1, 1), (2, 1, 2), (2, 1, 3)], 0,
                  "B2 three children k=1 q5 N8", nsamp=25)
    block_sampled(2, 9, 5, [(3, 1, 1), (2, 2, 1)], 0, "B3 mu=3 mixed q2 N9", nsamp=30)
    block_sampled(2, 6, 4, [(2, 1, 1)], 2, "B4 deg-2 cofactor q2 N6 (two genres)",
                  nsamp=25)
    # note: at N=9 this cell's genre is EMPTY (root-freeness forces v(q0)>=3, non-drain
    # forces v(q0)<3) — the N=10 cell below is the smallest inhabited one.
    block_sampled(2, 10, 5, [(2, 1, 1), (2, 2, 1)], 1, "B5 mixed + cofactor q2 N10",
                  nsamp=25)
    block_sampled(5, 5, 4, [(2, 1, 1), (2, 1, 2)], 0, "B6 CELL-2 shape at q5 N5")
    block_sampled(2, 6, 4, [(3, 1, 1)], 1, "B7 mu=3 single child q2 N6 (char-2 binomial)",
                  nsamp=25)
    block_sampled(2, 9, 4, [(2, 1, 1), (2, 3, 1)], 0, "B8 slope gap 1,3 q2 N9", nsamp=30)
    block_sampled(3, 13, 6, [(2, 1, 1), (2, 2, 1), (2, 3, 1)], 0,
                  "B9 three slopes q3 N13", nsamp=20)
    block_sampled(3, 7, 5, [(3, 1, 1), (2, 1, 2)], 0, "B10 same slope mu 3,2 q3 N7",
                  nsamp=25)
    block_sampled(3, 11, 7, [(2, 1, 1), (2, 1, 2), (2, 2, 1)], 1,
                  "B11 grand mix q3 N11", nsamp=15)
    print("-- BLOCK C: MSM2 proof-oriented unequal-slope/resultant checks")
    check_r0_assignment_lemma([(2, 1, 1), (2, 3, 1)], "two slopes with gap")
    check_r0_assignment_lemma([(2, 1, 1), (2, 2, 1), (2, 3, 1)], "three slopes")
    check_r0_assignment_lemma([(3, 1, 1), (2, 1, 2), (2, 3, 1)],
                              "same-slope block plus higher block")
    sweep_r0_assignment_lemma()
    check_schur_counterexample()
    check_resultants_and_multisylvester()
    print()
    n = len(FAILED)
    print(f"total time {time.time() - t0:.1f}s")
    print(f"==== {n} failed ====" if n else "==== ALL CHECKS PASSED ====")
    return 1 if n else 0


if __name__ == "__main__":
    sys.exit(main())
