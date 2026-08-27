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
    print("H.116b4 Smith identification certificate (unit MSMITH, 2026-08-26)")
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
    print()
    n = len(FAILED)
    print(f"total time {time.time() - t0:.1f}s")
    print(f"==== {n} failed ====" if n else "==== ALL CHECKS PASSED ====")
    return 1 if n else 0


if __name__ == "__main__":
    sys.exit(main())
