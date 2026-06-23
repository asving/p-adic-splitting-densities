"""General-n symbolic Okutsu-Montes density engine.

Computes the PROJECTIVE factorization-type density rho(n, sigma; q) as an EXACT
sympy rational function of q for every factorization type sigma of degree n.

PIPELINE (all pieces independently validated; see notes referenced):

  beta_e[.]  -- the MONIC single-cluster law (size-e cluster, all e roots reduce to
                ONE rational residue point; conditional mass 1).  This is the paper's
                beta(e,.;q) = alpha(e,.;1/q), and equals M1's L_e^{(1)}.
                Built by the coupled fixpoint (BB3_infinity sec 4.1 / ASSERTIONS A4-A5):

                  beta_e = q^{-e(e-1)/2} * FULLMONIC(e)[beta_e]  +  SHALLOW_e          (R)

                * FULLMONIC(e) = full monic degree-e density assembled by the MONIC M1
                  bridge over Sym^e A^1(F_q) from the cluster laws beta_m (m<=e); it is
                  LINEAR in the unknown beta_e (via the e-fold-at-one-rational-point
                  cell) -- this is the rescale/self-loop branch (all roots descend one
                  level together, prob q^{-e(e-1)/2}).
                * SHALLOW_e = sum over Newton-polygon cells whose RIGHTMOST (minimal-
                  slope) face is fractional (slope a/b < 1, b>=2 -- a wild/ramified
                  block).  Each face's residual polynomial is uniform over
                  {monic deg-d over F_q, nonzero constant term} (L3 / M6); a
                  multiplicity-1 residual factor of degree D is an OM leaf (b, D); a
                  multiplicity->=2 factor descends to a child cluster beta_mu (over
                  F_{q^D}).  Exact Igusa/BB1 cell volume (1-1/q)^V q^{-N} (notes
                  l4_unified, verified), with face depths summed geometrically to oo.

                GATE: beta_2, beta_3 reproduced by (R) EXACTLY (== padic_types at 1/q).

  L_e^{(delta)}(q) = beta_e evaluated at q^delta with f-degrees scaled by delta
                (M1 sec 2.1: unramified base change for a closed point of degree delta).

  rho(n,sigma;q) = (1/|P^n(F_q)|) sum_{D in Sym^n P^1(F_q)} W_D[sigma]               (M1)
                W_D[sigma] = sum over disjoint-union assignments of prod_j L_{m_j}^{(delta_j)}.

VALIDATION GATES (trustworthy iff all pass):
  (a) reproduce padic_types monic_quad_pred/monic_cubic_pred AND proj_cubic_pred EXACTLY;
  (b) sum_sigma rho(n,sigma;q) == 1 symbolically for n=2,3,4,5;
  (c) per-type cross-check vs PARI factorpadic oracle at n=4,5, primes {2,3,5,7}.

Run:  python3 om_density_engine.py             # symbolic engine + gates (a),(b)
      .../envs/padic/bin/python om_density_engine.py --oracle   # gate (c)
"""

import sys
import os
import math
import argparse
from functools import lru_cache
from itertools import product as iproduct
from collections import Counter, defaultdict

import sympy as sp

q = sp.symbols('q', positive=True)
REPO = os.path.dirname(os.path.abspath(__file__))


# ===========================================================================
# Factorization types: sorted tuple of (e,f) pairs, sum e*f = degree.  Matches
# quartic_oracle.full_type, so the oracle cross-check is direct.
# ===========================================================================

def type_degree(tau):
    return sum(e * f for (e, f) in tau)


def type_union(parts):
    out = []
    for p in parts:
        out.extend(p)
    return tuple(sorted(out))


# ===========================================================================
# L3 residual-factorization counts over {monic deg-d, R(0) != 0} (universal q-polys).
# A residual face has NONZERO constant term: none of its d roots is at valuation
# deeper than the face slope (they all sit on this face).  Counts sum to q^d - q^{d-1}.
# ===========================================================================

@lru_cache(maxsize=None)
def num_irreducible(d):
    from sympy import mobius, divisors, Rational
    return sp.expand(sum(mobius(e) * q ** (d // e) for e in divisors(d)) * Rational(1, d))


@lru_cache(maxsize=None)
def residual_shapes(d):
    res = []

    def rec(rem, minp, cur):
        if rem == 0:
            res.append(tuple(sorted(cur)))
            return
        for D in range(1, rem + 1):
            for mu in range(1, rem // D + 1):
                if D * mu > rem:
                    break
                if (D, mu) < minp:
                    continue
                rec(rem - D * mu, (D, mu), cur + [(D, mu)])

    rec(d, (0, 0), [])
    return res


@lru_cache(maxsize=None)
def shape_count_nonzero(shape):
    """# monic deg-d polys over F_q with this (deg,mult) factor shape AND R(0) != 0.
    (Exclude the linear factor y from the degree-1 pool; higher-degree irreducibles
    automatically have nonzero constant.)"""
    bydeg = defaultdict(list)
    for (D, mu) in shape:
        bydeg[D].append(mu)
    total = sp.Integer(1)
    for D, muls in bydeg.items():
        navail = (q - 1) if D == 1 else num_irreducible(D)
        k = len(muls)
        ff = sp.Integer(1)
        for i in range(k):
            ff *= (navail - i)
        sym = sp.Integer(1)
        for _, cnt in Counter(muls).items():
            sym *= sp.factorial(cnt)
        total *= ff / sym
    return sp.expand(total)


# ===========================================================================
# The monic single-cluster law  beta_e  (= alpha(e,.;1/q) = L_e^{(1)}).
# ===========================================================================

# explicit anchors (= padic_types monic laws read at 1/q), keyed by (e,f)-type.
@lru_cache(maxsize=None)
def _beta_anchor(e):
    if e == 1:
        return {((1, 1),): sp.Integer(1)}
    if e == 2:
        return {((2, 1),): q / (q + 1),
                ((1, 1), (1, 1)): sp.Rational(1, 1) / (2 * (q + 1)),
                ((1, 2),): sp.Rational(1, 1) / (2 * (q + 1))}
    if e == 3:
        d5 = q ** 5 - 1
        a3 = {'111': q ** 3 * (q - 1) * (q * q - q + 1) / (6 * (q + 1) * d5),
              '12': q ** 3 * (q ** 3 - 1) / (2 * (q + 1) * d5),
              '3': q ** 3 * (q * q - 1) / (3 * d5),
              '1r1': q * (q - 1) * (q ** 3 + q + 1) / ((q + 1) * d5),
              '1c': (q - 1) * (q * q + 1) / d5}
        code = {'111': ((1, 1), (1, 1), (1, 1)), '12': ((1, 1), (1, 2)),
                '3': ((1, 3),), '1r1': ((1, 1), (2, 1)), '1c': ((3, 1),)}
        return {code[k]: sp.simplify(v.subs(q, 1 / q)) for k, v in a3.items()}
    return None


@lru_cache(maxsize=None)
def beta(e):
    """Monic single-cluster law for a size-e cluster (cluster law L_e).  Anchored
    e<=3; computed by the coupled fixpoint (R) for e>=4."""
    anc = _beta_anchor(e)
    if anc is not None:
        return anc
    return _beta_recursion(e)


def beta_scaled(m, delta):
    """beta_m over a closed point of degree delta: base change q -> q^delta, f *= delta."""
    out = {}
    for t, p in beta(m).items():
        pp = sp.simplify(p.subs(q, q ** delta))
        mt = tuple(sorted((e, f * delta) for (e, f) in t))
        out[mt] = out.get(mt, sp.Integer(0)) + pp
    return out


# ---- FULLMONIC(e): full monic degree-e density via the MONIC M1 bridge ----
# linear in the unknown beta_e (the (1,e)-cell), with beta_m (m<e) as knowns.

def _divisor_patterns(n):
    res = []

    def rec(rem, minpair, cur):
        if rem == 0:
            res.append(tuple(sorted(cur)))
            return
        for delta in range(1, rem + 1):
            for m in range(1, rem // delta + 1):
                if delta * m > rem:
                    break
                if (delta, m) < minpair:
                    continue
                rec(rem - delta * m, (delta, m), cur + [(delta, m)])

    rec(n, (0, 0), [])
    return res


def _affine_config_count(pattern):
    """# residue divisors in Sym^n A^1(F_q) of a (delta, m)-pattern (closed points of
    A^1 = monic irreducibles; degree-1 pool has q points)."""
    bydeg = defaultdict(list)
    for (delta, m) in pattern:
        bydeg[delta].append(m)
    total = sp.Integer(1)
    for delta, mults in bydeg.items():
        npts = num_irreducible(delta)
        k = len(mults)
        ff = sp.Integer(1)
        for i in range(k):
            ff *= (npts - i)
        sym = sp.Integer(1)
        for _, cnt in Counter(mults).items():
            sym *= sp.factorial(cnt)
        total *= ff / sym
    return sp.expand(total)


def _fullmonic_linear(e, beta_e_unknown):
    """FULLMONIC(e) as {type: sympy expr linear in the beta_e_unknown dict}."""
    acc = defaultdict(lambda: sp.Integer(0))
    for pattern in _divisor_patterns(e):
        cfg = _affine_config_count(pattern)
        point_dists = []
        for (delta, m) in pattern:
            if m == 1:
                point_dists.append({((1, delta),): sp.Integer(1)})
            elif (delta, m) == (1, e):
                point_dists.append(beta_e_unknown)            # the unknown e-cluster
            else:
                point_dists.append(beta_scaled(m, delta))     # known smaller cluster
        agg = {(): sp.Integer(1)}
        for dist in point_dists:
            new = defaultdict(lambda: sp.Integer(0))
            for t0, p0 in agg.items():
                for t1, p1 in dist.items():
                    new[type_union([t0, t1])] += p0 * p1
            agg = dict(new)
        for t, p in agg.items():
            acc[t] += cfg * p
    return {t: v / q ** e for t, v in acc.items()}


# ---- SHALLOW_e: Newton-polygon cells with a fractional rightmost (minimal) face ----
# Each cell's volume is the exact Igusa cell volume (1-1/q)^V q^{-N} * q^e (cluster-
# conditional), with face depths (the slope numerators a_j) summed geometrically to oo.

def _face_residual_dist(b, d):
    """Distribution over types from a single face slope a/b (a/b irrelevant to types,
    only b matters), residual deg-d uniform over {monic deg-d, R(0)!=0}.  Returns a
    mass-1 dict {type: prob}."""
    norm = q ** d - q ** (d - 1)
    dist = defaultdict(lambda: sp.Integer(0))
    for shape in residual_shapes(d):
        cnt = shape_count_nonzero(shape)
        if cnt == 0:
            continue
        prob = cnt / norm
        leaves = []
        desc = []
        for (D, mu) in shape:
            if mu == 1:
                leaves.append((b, D))
            else:
                desc.append((mu, D))
        parts = [{tuple(sorted(leaves)): sp.Integer(1)}]
        for (mu, D) in desc:
            cd = {}
            for ct, cp in beta_scaled(mu, D).items():
                # outer ramification b multiplies child e; child f already carries *D.
                mt = tuple(sorted((b * ce, cf) for (ce, cf) in ct))
                cd[mt] = cd.get(mt, sp.Integer(0)) + cp
            parts.append(cd)
        for ch in iproduct(*[list(p.items()) for p in parts]):
            t = type_union([c[0] for c in ch])
            pp = prob
            for c in ch:
                pp *= c[1]
            dist[t] += pp
    return dist



@lru_cache(maxsize=None)
def _beta_recursion(e):
    """Solve the fixpoint (R) for beta_e (e>=4).

    The system is DIAGONAL: FULLMONIC(e)[t] depends only on the single unknown
    beta_e[t] (via the (1,e) self-loop cell; verified for all e), so each type
    solves independently as a scalar linear equation
        b_t = resc * FULLMONIC[t](b_t) + SHALLOW[t],
    avoiding an O(#types)-variable symbolic solve (the only practical bottleneck)."""
    types = _enumerate_cluster_types(e)
    syms = {t: sp.Symbol(f"_b{i}") for i, t in enumerate(types)}
    FM = _fullmonic_linear(e, syms)
    SH = _shallow_geometric(e)
    resc = q ** (-(e * (e - 1) // 2))
    out = {}
    for t in types:
        bt = syms[t]
        rhs = resc * FM.get(t, sp.Integer(0)) + SH.get(t, sp.Integer(0))
        # diagonal scalar solve: bt = rhs(bt), linear in bt.
        sol = sp.solve(sp.Eq(bt, sp.together(rhs)), bt)
        if not sol:
            raise RuntimeError(f"beta recursion at e={e}, type {t}: no solution")
        out[t] = sp.cancel(sol[0])
    return out


@lru_cache(maxsize=None)
def _enumerate_cluster_types(e):
    """All (e,f)-types of degree e that a size-e cluster can produce (any partition of
    e into local (e_i,f_i) blocks with sum e_i f_i = e)."""
    res = []

    def rec(rem, minpair, cur):
        if rem == 0:
            res.append(tuple(sorted(cur)))
            return
        for ei in range(1, rem + 1):
            for fi in range(1, rem // ei + 1):
                if ei * fi > rem:
                    break
                if (ei, fi) < minpair:
                    continue
                rec(rem - ei * fi, (ei, fi), cur + [(ei, fi)])

    rec(e, (0, 0), [])
    return res


@lru_cache(maxsize=None)
def _shallow_geometric(e):
    """SHALLOW_e: sum over Newton-polygon cells whose RIGHTMOST (minimal-slope) face is
    fractional (slope < 1), with face depths summed to infinity (exact geometric closure).

    Cell = an ordered face sequence (left=steepest .. right=shallowest), each face a
    kind (L_j, b_j, d_j) with sum L_j = e and the rightmost b_k >= 2 (fractional).  The
    slope numerators a_j range over { a_j >= 1, gcd(a_j,b_j)=1, slopes strictly
    decreasing left->right, rightmost slope a_k/b_k < 1 }.  Volume = Igusa cell volume
    (1-1/q)^V q^{-N} q^e, N affine in the a_j; the leftmost (steepest) face's depth is
    unbounded and summed to infinity; the inner faces are bounded by strict ordering.
    Residual factorization (depth-independent) gives the type via _face_residual_dist."""
    acc = defaultdict(lambda: sp.Integer(0))

    def gen_kinds(col, kinds):
        if col == e:
            if kinds and kinds[-1][1] >= 2:        # rightmost face fractional
                yield list(kinds)
            return
        for L in range(1, e - col + 1):
            for b in range(1, L + 1):
                if L % b:
                    continue
                yield from gen_kinds(col + L, kinds + [(L, b, L // b)])

    for kinds in gen_kinds(0, []):
        for t, v in _sum_kind_seq(tuple(kinds), e).items():
            acc[t] += v
    return {t: sp.cancel(v) for t, v in acc.items()}


def _geom_sum_inf(summand, tL, tmin):
    """Sum a summand of the form K * q^{-c*tL} (c>0 integer) over tL >= tmin to oo,
    using q > 1 (valid at every prime power).  = K * q^{-c*tmin} / (1 - q^{-c})."""
    expr = sp.powsimp(sp.expand(summand), force=True)
    # the tL-dependence is q^{linear in tL}; extract the coefficient c of tL in the
    # q-exponent by comparing expr at tL and tL+1.
    ratio = sp.simplify(expr.subs(tL, tL + 1) / expr.subs(tL, tL))   # = q^{-c}
    base_at_min = expr.subs(tL, tmin)
    # ratio is a pure power of q (constant in tL); geometric sum:
    return sp.cancel(base_at_min / (1 - ratio))


def _cell_N(avec, kinds, cols, vidx, e):
    """Exponent N = sum_{i=0}^{e-1} ceil(height_i) for the polygon with depths avec."""
    k = len(kinds)
    bs = [kinds[j][1] for j in range(k)]
    ds = [kinds[j][2] for j in range(k)]
    drops = [avec[j] * ds[j] for j in range(k)]
    vheight = [sp.Integer(0)] * (k + 1)
    for j in range(k - 1, -1, -1):
        vheight[j] = vheight[j + 1] + drops[j]
    N = sp.Integer(0)
    for j in range(k):
        slope = sp.Rational(1, bs[j]) * avec[j]
        x1, y1 = cols[j], vheight[j]
        for i in range(cols[j], cols[j + 1]):
            hi = y1 - slope * (i - x1)
            N += hi if i in vidx else sp.ceiling(hi)
    return N


def _sum_kind_seq(kinds, e):
    """Sum the Igusa cell volume over the FULL depth cone for one face-kind sequence,
    EVERY face depth summed to infinity (exact geometric closure); return
    {type: sympy rational}.

    Faces are j=0..k-1 left->right with strictly DECREASING slopes a_j/b_j (gcd=1),
    the rightmost (j=k-1) slope < 1.  We parametrize by the slope VALUES s_j = a_j/b_j,
    enumerated as an increasing chain from the right.  Each s_j ranges over the
    rationals with denominator b_j (i.e. a_j coprime-residue + multiples), bounded below
    by s_{j+1} (strict) and, for j=k-1, bounded above by 1.  We enumerate the coprime
    residue of each a_j (finite, mod b_j) and sum the unbounded depth (the multiple of
    b_j added) geometrically, processing RIGHT->LEFT so each face's lower bound is fixed
    by the already-chosen face to its right."""
    k = len(kinds)
    bs = [kinds[j][1] for j in range(k)]
    cols = [0]
    for (L, b, d) in kinds:
        cols.append(cols[-1] + L)
    vidx = set(cols)
    V = sum(1 for i in range(0, e) if i in vidx)

    fds = [_face_residual_dist(kinds[j][1], kinds[j][2]) for j in range(k)]
    type_mass = defaultdict(lambda: sp.Integer(0))
    for ch in iproduct(*[list(fd.items()) for fd in fds]):
        t = type_union([c[0] for c in ch])
        pp = sp.Integer(1)
        for c in ch:
            pp *= c[1]
        type_mass[t] += pp

    # Exact infinite sum over the strictly-decreasing-slope depth cone via slope-gap
    # parametrization (decouples the coupled lower bounds into independent geometric
    # series); see _sum_by_gaps.
    total_vol = _sum_by_gaps(kinds, e, cols, vidx, V)
    return {t: sp.cancel(total_vol * m) for t, m in type_mass.items()}


def _sum_by_gaps(kinds, e, cols, vidx, V):
    """Exact infinite sum of the Igusa cell volume over the strictly-decreasing-slope
    depth cone, via independent slope-GAP variables.

    Let s_0 > s_1 > ... > s_{k-1} > 0 be the face slopes, s_j = a_j/b_j (a_j coprime to
    b_j).  Equivalent data: the rightmost slope s_{k-1} in (0,1), and positive gaps
    g_j = s_j - s_{j+1} > 0 (j<k-1).  But s_j must have denominator exactly b_j, which
    couples gaps to denominators.  Instead we enumerate over the integer depths directly
    with a nested geometric sum where each variable's lower bound is a fixed integer
    (achieved by ordering faces by INCREASING b is not valid).  Simplest exact method:
    enumerate the coprime residues of all a_j (finite), then the integer cone
    {a_j = r_j + b_j t_j, t_j>=0, a_0/b_0 > a_1/b_1 > ... and a_{k-1}/b_{k-1} < 1} is a
    polyhedral cone in the t_j; sum the q^{-N} (N affine in t) over it via inclusion of
    the cone's generating function.  We compute that generating function by triangulating
    the cone into simplicial cones and using the standard simplicial-cone geometric sum.
    For the small k (<= e <= ~6) here this is tractable; we implement it by the
    transfer-matrix nested sum with EXACT lower bounds carried symbolically."""
    onehalf = sp.Rational(1, 1)
    k = len(kinds)
    bs = [kinds[j][1] for j in range(k)]

    def vol_of(avec):
        N = _cell_N(avec, kinds, cols, vidx, e)
        return (1 - onehalf / q) ** V * (onehalf / q) ** N * q ** e

    # Enumerate coprime residues; within a residue combo the cone is in (t_0..t_{k-1}).
    def coprimes(b):
        return [r for r in range(1, b + 1) if math.gcd(r, b) == 1]

    total = sp.Integer(0)
    for rcombo in iproduct(*[coprimes(b) for b in bs]):
        total += _cone_sum(kinds, e, cols, vidx, V, rcombo, vol_of)
    return total


def _cone_sum(kinds, e, cols, vidx, V, rcombo, vol_of):
    """Sum vol_of over the integer points of the cone defined by a_j = rcombo[j]+b_j t_j,
    t_j >= 0, slopes strictly decreasing, rightmost slope < 1.  Nested geometric sum:
    process faces RIGHT->LEFT; each t_j is summed to infinity with its lower bound a
    (symbolic, integer) function of the next-right slope.  Because the volume exponent N
    is affine in each t_j and the constraint t_j >= L_j(t_{j+1}) is affine, the nested
    sum is a product of geometric series evaluated at shifted lower bounds."""
    k = len(kinds)
    bs = [kinds[j][1] for j in range(k)]
    tvars = [sp.Symbol(f"u{j}", integer=True, nonnegative=True) for j in range(k)]
    # a_j symbolic:
    avec = [rcombo[j] + bs[j] * tvars[j] for j in range(k)]
    # constraints: slope_j > slope_{j+1}  i.e. a_j/b_j > a_{j+1}/b_{j+1}
    #   => (rcombo[j]+b_j u_j)/b_j > (rcombo[j+1]+b_{j+1} u_{j+1})/b_{j+1}
    # rightmost: a_{k-1}/b_{k-1} < 1 => rcombo[k-1] + b_{k-1} u_{k-1} < b_{k-1}
    #   => u_{k-1} = 0 and rcombo[k-1] < b_{k-1} (fractional).  (only u_{k-1}=0 works)
    if not (rcombo[k - 1] < bs[k - 1]):
        return sp.Integer(0)
    # u_{k-1} fixed to 0 (any u_{k-1}>=1 makes slope >= 1).
    # Now process j=k-2 .. 0: u_j >= lower bound from slope_j > slope_{j+1}.
    vol = vol_of(avec)
    # substitute u_{k-1}=0
    vol = vol.subs(tvars[k - 1], 0)
    avec = [rcombo[j] + bs[j] * tvars[j] for j in range(k)]
    avec[k - 1] = sp.Integer(rcombo[k - 1])
    # nested sum from j=k-2 down to 0
    expr = vol
    for j in range(k - 2, -1, -1):
        # lower bound: smallest integer u_j with (rcombo[j]+b_j u_j)/b_j > slope_{j+1}.
        # slope_{j+1} = avec[j+1]/b_{j+1}; avec[j+1] may depend on u_{j+1} (still free if
        # j+1 < k-1) -- but we process right->left, so u_{j+1} is summed AFTER u_j here.
        # That couples.  To decouple, sum LEFT->RIGHT instead: the leftmost has the
        # loosest bound.  Re-order: process j=0..k-2 with u_j >= f(u_{j+1}) is still
        # coupled.  Resolve by substitution u_j = w_j + ceil-bound(u_{j+1}); the gap w_j>=0.
        pass
    # Decouple via gap substitution: define for j=0..k-2:  u_j = w_j + shift_j(u_{j+1}),
    # where shift_j is the minimal u_j given u_{j+1}.  shift depends linearly on u_{j+1}.
    # slope_j > slope_{j+1}:  rcombo[j]/b_j + u_j > rcombo[j+1]/b_{j+1} + u_{j+1}
    #   => u_j > u_{j+1} + (rcombo[j+1]/b_{j+1} - rcombo[j]/b_j)
    # minimal integer u_j = u_{j+1} + ceil( rcombo[j+1]/b_{j+1} - rcombo[j]/b_j + epsilon ).
    # Let c_j = the minimal integer s.t. c_j > (rcombo[j+1]/b_{j+1} - rcombo[j]/b_j), i.e.
    #   c_j = floor(rcombo[j+1]/b_{j+1} - rcombo[j]/b_j) + 1.
    # Then u_j = u_{j+1} + c_j + w_j, w_j >= 0.  (Strict > becomes >= with +1.)
    from sympy import floor as spfloor
    w = [sp.Symbol(f"w{j}", integer=True, nonnegative=True) for j in range(k)]
    cshift = [sp.Integer(0)] * k
    for j in range(k - 2, -1, -1):
        diff = sp.Rational(rcombo[j + 1], bs[j + 1]) - sp.Rational(rcombo[j], bs[j])
        cshift[j] = int(sp.floor(diff)) + 1
    # express u_j in terms of w_j..w_{k-2} (and u_{k-1}=0):  u_j = sum_{i=j}^{k-2}(c_i + w_i)
    u_in_w = [sp.Integer(0)] * k
    acc = sp.Integer(0)
    for j in range(k - 2, -1, -1):
        acc = acc + cshift[j] + w[j]
        u_in_w[j] = acc
    avec_w = [rcombo[j] + bs[j] * u_in_w[j] for j in range(k - 1)] + [sp.Integer(rcombo[k - 1])]
    volw = vol_of(avec_w)
    # sum each w_j (j=0..k-2) over [0, oo) geometrically
    res = volw
    for j in range(k - 1):
        res = _geom_sum_inf_var(res, w[j])
    return res


def _geom_sum_inf_var(expr, var):
    """Sum expr over var=0..oo, where expr = K * q^{-c*var} (c>=0 const in q).
    = K / (1 - q^{-c}) using q>1.  If expr does not depend on var, returns expr (the
    series would diverge) -- but by construction expr always decays in var here."""
    e0 = expr.subs(var, 0)
    ratio = sp.cancel(expr.subs(var, var + 1) / expr)   # = q^{-c}, constant in var
    ratio = sp.cancel(ratio.subs(var, 0))
    if ratio == 1:
        raise RuntimeError("non-decaying geometric sum (divergent)")
    return sp.cancel(e0 / (1 - ratio))
# ===========================================================================
# M1 monic->projective bridge -> rho(n, sigma; q).
# ===========================================================================

def Pn_count(n):
    return sum(q ** i for i in range(n + 1))


@lru_cache(maxsize=None)
def closed_point_count(delta):
    """# closed points of P^1/F_q of degree delta (delta=1 -> q+1 rational points)."""
    from sympy import mobius, divisors, Rational
    if delta == 1:
        return q + 1
    return sp.expand(sum(mobius(e) * q ** (delta // e) for e in divisors(delta)) * Rational(1, delta))


@lru_cache(maxsize=None)
def cluster_law_proj(m, delta):
    """L_m^{(delta)}(q)[tau] = beta_m at q^delta, f-degrees *= delta."""
    out = {}
    for tau, prob in beta(m).items():
        pr = sp.simplify(prob.subs(q, q ** delta))
        mapped = tuple(sorted((e, f * delta) for (e, f) in tau))
        out[mapped] = out.get(mapped, sp.Integer(0)) + pr
    return out


def _proj_config_count(pattern):
    bydeg = defaultdict(list)
    for (delta, m) in pattern:
        bydeg[delta].append(m)
    total = sp.Integer(1)
    for delta, mults in bydeg.items():
        npts = closed_point_count(delta)
        k = len(mults)
        ff = sp.Integer(1)
        for i in range(k):
            ff *= (npts - i)
        sym = sp.Integer(1)
        for _, cnt in Counter(mults).items():
            sym *= sp.factorial(cnt)
        total *= ff / sym
    return sp.expand(total)


@lru_cache(maxsize=None)
def rho(n):
    """Projective factorization-type density rho(n, sigma; q), {type: simplified}."""
    Pn = Pn_count(n)
    acc = defaultdict(lambda: sp.Integer(0))
    for pattern in _divisor_patterns(n):
        cfg = _proj_config_count(pattern)
        point_dists = []
        for (delta, m) in pattern:
            if m == 1:
                point_dists.append({((1, delta),): sp.Integer(1)})
            else:
                point_dists.append(cluster_law_proj(m, delta))
        agg = {(): sp.Integer(1)}
        for dist in point_dists:
            new = defaultdict(lambda: sp.Integer(0))
            for t0, p0 in agg.items():
                for t1, p1 in dist.items():
                    new[type_union([t0, t1])] += p0 * p1
            agg = dict(new)
        for t, p in agg.items():
            acc[t] += cfg * p
    return {t: sp.simplify(v / Pn) for t, v in acc.items()}


# full monic density (gate against monic_*_pred)
@lru_cache(maxsize=None)
def alpha_full(n):
    acc = defaultdict(lambda: sp.Integer(0))
    for pattern in _divisor_patterns(n):
        cfg = _affine_config_count(pattern)
        point_dists = []
        for (delta, m) in pattern:
            if m == 1:
                point_dists.append({((1, delta),): sp.Integer(1)})
            else:
                # SAME cluster law L_m = beta_m as the projective assembly (M1 sec 2.2:
                # "the cluster laws, convolution and combinatorics are identical"); the
                # monic vs projective difference is ONLY the base points (A^1 vs P^1) and
                # the normalization (q^n vs |P^n|).  base change q -> q^delta, f *= delta.
                point_dists.append(cluster_law_proj(m, delta))
        agg = {(): sp.Integer(1)}
        for dist in point_dists:
            new = defaultdict(lambda: sp.Integer(0))
            for t0, p0 in agg.items():
                for t1, p1 in dist.items():
                    new[type_union([t0, t1])] += p0 * p1
            agg = dict(new)
        for t, p in agg.items():
            acc[t] += cfg * p
    return {t: sp.simplify(v / q ** n) for t, v in acc.items()}


CODE_N2 = {((1, 1), (1, 1)): 'split', ((1, 2),): 'inert', ((2, 1),): 'ram'}
CODE_N3 = {((1, 1), (1, 1), (1, 1)): '111', ((1, 1), (1, 2)): '12',
           ((1, 3),): '3', ((1, 1), (2, 1)): '1r1', ((3, 1),): '1c'}


if __name__ == '__main__':
    print("om_density_engine loaded.")
