#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
N3-cl6-polygeom — numerical test of conjecture M08 (BK.cl6, the general-n
PolyGeomLaws / CL-6 count+valuation package) on the natural general-n pack,
built by direct enumeration of Newton polygons of monic polys over Q_p.

======================================================================
WHAT THE LEAN CONJECTURE SAYS (fidelity extraction)
======================================================================
`BridgeKernels.cl6 : Nonempty (MovesS.PolyGeomLaws C.T C.MS C.RB)` asserts that
the (future, general-n) table pack carries a CL-6 package
(lean/LeanUrat/MovesS/Defs.lean, `PolyGeom` L322 / `PolyGeomLaws` L411):

  (VAL / PolyGeom.geom_denom_dvd)  every roster-row mass is
      countT(X) * countS(X) * geom  with  geom.denom | X^b * prod_{a in A}(1 - X^a)
      (X = q; A a finite set of positive integers), interpolating the measured
      row mass at every pool q0 = p^delta      [tg_interp / "valued correctly
      at every prime power"].
  (T-COUNT / tcount_val)   countT.eval(q0) = tCount(q0) : NAT at every pool.
  (S-COUNT / scount_val)   countS.eval(q0) = sum over the outcome's cell fiber
      of #cellInst(c, q0)  — the CELL CENSUS — at every pool.
  (DEG / tcount_deg, scount_deg)  deg countT <= Wloc(o), deg countS <= Wstate(tau).

The only Lean instance so far is n = 2 (`MovesS/N2PolyGeom.lean`), an R44
"consistency device" (per-depth masses q^-3 / 1-q^-1 / q^-1 - q^-3, all counts
pinned to the constant 1).  `MovesU/SynK2_cl6N2.lean` proved PolyGeomLaws EMPTY
at that as-built pack: the roster PADDING rows (duplicate Fin-3 outcomes at
e /= 2) carry countS = 1 against an empty cell fiber (census 0) — the known
n = 2 countS-padding bug.

======================================================================
THE SURROGATE PACK TESTED HERE (the "natural general-n form")
======================================================================
The note's REAL block instance (dual-accepted §S-RESUM; hand-derived at n = 3 in
verification/CASE_RESUMN3_SEALED_PREDICTIONS.md S1) is:

  block-n state = entry state {v(a_i) >= 1 for all i < n} of a monic degree-n
  f = x^n + a_{n-1} x^{n-1} + ... + a_0 over Z_p (i.e. fbar = x^n), coefficients
  Haar-uniform, masses CONDITIONAL on entry.  One step = read the Newton
  polygon (lower hull of {(i, v(a_i))} u {(n,0)}) + the residual polynomial
  factorization type on each hull segment.  Roster outcome = the multiset of
  members (e_seg, g, mult) over residual irreducible factors (degree g,
  multiplicity mult) of the segments (slope denominator e_seg); mult = 1
  members are decided verdicts (e, f) = (e_seg, g); mult >= 2 members continue
  (sub-blocks); the member (1,1,n) is the self-similar kcol column K_n.

This script CONSTRUCTS that pack for n = 2, 3, 4 by an automated exact
stratification (no hand case analysis):

  stratum = (V, rho, profile):  V = hull vertex abscissas; rho = per-segment
  slope residues D_j mod len_j (fixing e_j = len_j/gcd, d_j = gcd); profile =
  per-segment residual factorization type.  Heights resum geometrically:
     mass = COUNT(q) * q^(-E0) * prod_j 1/(1 - q^(-gamma_j))     (exact, sympy)
  with COUNT(q) = prod_j Mono_{d_j}(type_j; q), Mono the number of monic
  degree-d const/=0 polys over F_q of the given type (the digit-cell census
  polynomial; the vertex-digit chain telescopes to exactly this product), and
  E, gamma from the exact lattice geometry (ceilings of hull heights).

MAPPING Lean field -> computed surrogate (each tested below):
  part1 (MeasuredSide)     -> [P1] sum over all strata = 1, symbolically.
  VAL / geom_denom_dvd     -> [P3a] the reduced denominator of every row mass,
                              kernel K_n, det(1-K_n), and resummed beta_n(sigma)
                              has only X and cyclotomic factors (divides
                              X^b prod(1 - X^a)); the (b, {a}) inventory is
                              reported.
  tcount_val (NAT at pools)-> [P3b] COUNT(q0) is a nonnegative integer at every
                              prime power q0 <= 49 (and the census equalities
                              below).
  scount_val (cell census) -> [P4] EXHAUSTIVE census: over all entry boxes
                              mod p^N (and over the unramified quadratic
                              O/p^N for pools q = 4, 9), the number of boxes
                              realizing each stratum instance equals
                              COUNT(q0) * q0^(n(N-1) - E) exactly — i.e. the
                              count polynomial IS the digit-cell census at
                              every tested pool, including wild p <= n and
                              prime-power pools.
  tcount_deg/scount_deg    -> [P3c] deg COUNT <= n (the natural Wloc+Wstate
                              candidate = block size); observed degrees
                              reported.
  the SynK2 padding bug    -> [P4z] zero-fiber law: COUNT(q0) = 0 exactly where
                              the census finds ZERO boxes (empty fibers get
                              count 0, never a padded 1); the n = 3 vanishing
                              list is checked against RESUMN3's sealed
                              ENTRY-VANISHING list, and the n = 4 list is new.
ANCHORS (external ground truth):
  [P2a] n = 2: the four RESUMN3 block-2 strata (m2 split/inert, m_w2, m_vv),
        K_2 = (q-1)/(q^3-1), beta_2 = (1/(2(q+1)), 1/(2(q+1)), q/(q+1)).
  [P2b] n = 3: RESUMN3 S1 strata A/B/C/D/E (per-type), K_3 = (q-1)/(q^6-1),
        J, t_3 totals, composed beta_3 == the S1 hand solve.
  [P2c] n = 4: composed beta_4(sigma) == verification/results/beta4.json
        (the project's order-4 cluster law, BCFG-reconciled), all 11 types,
        as exact rational functions.  Composition legs: (1,1,k) -> beta_k(q);
        (1,2,2) -> beta_2(q^2) with f doubled; (2,1,2) -> beta_2(q) with e
        doubled (the cert_crosschecks slope-1/2 wild atom q/(q+1)).
  [P5]  PARI factorpadic (gp subprocess, quartic_oracle.py's Krasner-lift +
        idealprimedec method): sampled entry-state boxes whose one-step read is
        fully terminal must have exactly the predicted splitting type sigma
        (wild p = 2, 3 included).

======================================================================
FLAGGED SIMPLIFICATIONS (honesty inventory)
======================================================================
S1. The Lean n = 2 instance's own masses (q^-3 etc.) are an R44 consistency
    device, NOT the note's block pack; the general-n law is tested on the
    note's real pack (RESUMN3 semantics).  The device's padding failure is
    reproduced here only in its general form [P4z].
S2. countT and countS are tested through their PRODUCT (the stratum count
    polynomial).  The Lean split (T-table count vs cell sizes) is presentation
    data; only the product is pinned by val+census at this grain.  The natural
    split (type-count x digit powers) is reported, not separately tested.
S3. cells/cellInst are surrogated: cell = stratum (V, rho, profile) instance,
    instances = digit configurations at the stratum's read levels.  The Lean
    carrier is abstract; what is faithfully tested is scount_val's content:
    ONE polynomial per row valued at every pool = the census.
S4. Pools are all prime powers; integrality is tested at prime powers <= 49
    and the census at q0 in {2,3,4,5,7,9(shallow),...} per n as listed.
S5. beta composition assumes independent sub-block evolution (Hensel
    factorization) and the ramified-frame leg (2,1,2) -> beta_2(q) with e
    doubled; a [P2c] failure would first indict these composition assumptions,
    not CL-6 itself.  The core law tests [P1,P3,P4] are composition-free.

Outputs: log (tee'd by the caller) + JSON results next to this script.
Runtime: ~10-15 min (census-dominated), CPU only.
"""

import itertools
import json
import math
import os
import random
import subprocess
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction

sys.path.insert(0, os.path.expanduser("~/.local/lib/python3.10/site-packages"))
import sympy as sp

q = sp.symbols('q')
HERE = os.path.dirname(os.path.abspath(__file__))
T0 = time.time()

FAILURES = []
CHECKS = [0]


def chk(name, cond, detail=""):
    CHECKS[0] += 1
    tag = "PASS" if cond else "FAIL"
    if not cond:
        FAILURES.append(f"{name} :: {detail}")
    print(f"[{tag}] {name}" + (f"  {detail}" if detail and not cond else ""))
    return cond


def banner(s):
    print("\n" + "=" * 74 + f"\n{s}\n" + "=" * 74)


# ======================================================================
# SECTION 1 — the exact symbolic stratification engine
# ======================================================================

def divisors(m):
    return [d for d in range(1, m + 1) if m % d == 0]


def Nprime(g):
    """# admissible monic irreducibles of degree g over F_q (const != 0 allowed
    factors only, i.e. exclude the irreducible x at g = 1)."""
    if g == 1:
        return q - 1
    return sp.expand(sum(sp.mobius(e) * q ** (g // e) for e in divisors(g)) / g)


def factorization_types(d):
    """All factorization types of a monic degree-d poly with const != 0 over F_q:
    multisets of (g, mult), sum g*mult = d.  Entries with equal (g, mult) mean
    DISTINCT irreducibles.  Returned as sorted tuples."""
    out = set()

    def rec(remaining, min_pair, cur):
        if remaining == 0:
            out.add(tuple(sorted(cur)))
            return
        for g in range(1, remaining + 1):
            for m in range(1, remaining // g + 1):
                if (g, m) >= min_pair and g * m <= remaining:
                    rec(remaining - g * m, (g, m), cur + [(g, m)])
    rec(d, (0, 0), [])
    return sorted(out)


def mono_count(typ):
    """# monic degree-d const!=0 polys over F_q with factorization type `typ`
    (exact polynomial in q, rational coefficients)."""
    by_g = defaultdict(list)
    for (g, m) in typ:
        by_g[g].append(m)
    total = sp.Integer(1)
    for g, mults in by_g.items():
        r = len(mults)
        Np = Nprime(g)
        ff = sp.prod([Np - i for i in range(r)])       # falling factorial: distinct irreducibles
        dup = sp.prod([sp.factorial(c) for c in Counter(mults).values()])
        total *= ff / dup
    return sp.expand(total)


# --- exact hull geometry (Fractions; shared by engine and census) -----------

def hull_heights(n, V, D):
    """Heights of the hull at abscissas 0..n given vertex set V (ascending,
    0 and n included) and drops D_j >= 1 per segment.  Returns (heights list of
    Fractions indexed 0..n, seg_of list: segment index j (1-based) per abscissa,
    vertex heights dict)."""
    r = len(V) - 1
    hV = {V[r]: Fraction(0)}
    for j in range(r, 0, -1):
        hV[V[j - 1]] = hV[V[j]] + D[j - 1]
    heights = [None] * (n + 1)
    segof = [None] * (n + 1)
    for j in range(1, r + 1):
        a, b = V[j - 1], V[j]
        s = Fraction(D[j - 1], b - a)
        for i in range(a, b + 1):
            heights[i] = hV[b] + s * (b - i)
            segof[i] = j
    return heights, segof, hV


def E_Nreq_slots(n, V, D):
    """Exact exponent E (conditional on entry), the decidability level N_req,
    and the slot levels, for the concrete stratum (V, D).
    slot(i)  <=> hull(i) integral  <=> e_j | (v_j - i) on segment j.
    E     = sum_{i<n} (slot ? hull(i)+1 : ceil(hull(i))) - n
    N_req = max_i    (slot ? hull(i)+1 : ceil(hull(i)))"""
    heights, segof, _ = hull_heights(n, V, D)
    E = 0
    Nreq = 0
    slot_levels = {}
    for i in range(n):
        h = heights[i]
        if h.denominator == 1:
            term = int(h) + 1
            slot_levels[i] = int(h)
        else:
            term = int(math.ceil(h))
        E += term
        Nreq = max(Nreq, term if h.denominator == 1 else int(math.ceil(h)))
    return E - n, Nreq, slot_levels


# --- strata --------------------------------------------------------------

class Stratum:
    """One (V, rho) residue stratum: fixed hull combinatorics + slope residues.
    Heights are D_j = rho_j + len_j * m_j over the convexity chain cone."""

    def __init__(self, n, V, rho):
        self.n, self.V, self.rho = n, tuple(V), tuple(rho)
        r = self.r = len(V) - 1
        self.lens = [V[j] - V[j - 1] for j in range(1, r + 1)]
        self.e = [self.lens[j] // math.gcd(self.lens[j], rho[j]) if rho[j] else 1
                  for j in range(r)]
        self.d = [self.lens[j] // self.e[j] for j in range(r)]
        # chain: s_j > s_{j+1}; s_j = m_j + rho_j/len_j
        # m_j >= m_{j+1} + t_j, t_j = floor(rho_{j+1}/len_{j+1} - rho_j/len_j) + 1
        self.t = []
        for j in range(r - 1):
            delta = Fraction(rho[j + 1], self.lens[j + 1]) - Fraction(rho[j], self.lens[j])
            self.t.append(int(math.floor(delta)) + 1)
        self.base = 1 if rho[r - 1] == 0 else 0    # s_r > 0
        # apex m*
        m = [0] * r
        m[r - 1] = self.base
        for j in range(r - 2, -1, -1):
            m[j] = m[j + 1] + self.t[j]
        self.apex = tuple(m)
        # E linear data: E0 at apex; gamma_j = E(apex + 1 on m_1..m_j) - E0
        self.E0, self.Nreq0, _ = self._END(self.apex)
        self.gammas = []
        for j in range(1, r + 1):
            m1 = tuple(mi + (1 if k < j else 0) for k, mi in enumerate(self.apex))
            m2 = tuple(mi + (2 if k < j else 0) for k, mi in enumerate(self.apex))
            g1 = self._END(m1)[0] - self.E0
            g2 = self._END(m2)[0] - self._END(m1)[0]
            assert g1 == g2 and g1 > 0, f"E not linear on {self}: {g1} vs {g2}"
            self.gammas.append(g1)
        # geometric height sum
        self.HS = q ** (-self.E0) * sp.prod([1 / (1 - q ** (-g)) for g in self.gammas])
        self.HS = sp.cancel(sp.together(self.HS))

    def D_of(self, m):
        return tuple(self.rho[j] + self.lens[j] * m[j] for j in range(self.r))

    def _END(self, m):
        return E_Nreq_slots(self.n, self.V, self.D_of(m))

    def m_instances(self, N):
        """All m-vectors in the cone with N_req <= N (finite).  Returns
        [(m, E, Nreq)].  N_req >= hull(0)+1 is strictly increasing in every
        m_j, which bounds the enumeration (asserted)."""
        out = []
        BOUND = N + 2

        # enumerate from the last segment upward (m_r outermost)
        def rec2(j, mnext, cur):
            if j == -1:
                m = tuple(cur)
                E, Nr, _ = self._END(m)
                if Nr <= N:
                    assert max(m) < BOUND, f"enumeration bound hit on {self}: {m}"
                    out.append((m, E, Nr))
                return
            lo = self.base if j == self.r - 1 else cur[0] + self.t[j]
            mj = lo
            while True:
                probe = [mj] + cur
                # minimal completion of remaining coords uses chain minima; if even
                # that exceeds N in N_req, stop.
                mm = list(probe)
                for k in range(j - 1, -1, -1):
                    mm = [mm[0] + self.t[k]] + mm
                if self._END(tuple(mm))[1] > N:
                    break
                rec2(j - 1, mj, probe)
                mj += 1
        rec2(self.r - 1, None, [])
        return out

    def __repr__(self):
        return f"Stratum(n={self.n},V={self.V},rho={self.rho})"


def vertex_sets(n):
    inner = [set(c) for k in range(n) for c in itertools.combinations(range(1, n), k)]
    return sorted(sorted({0, n} | s) for s in inner)


def build_pack(n):
    """The full one-step block-n pack: list of stratum-profile records + lumped
    roster rows.  Record: dict(V, rho, e, d, profile, members, count, mass)."""
    records = []
    rows = defaultdict(lambda: sp.Integer(0))
    strata = []
    for V in vertex_sets(n):
        lens = [V[j] - V[j - 1] for j in range(1, len(V))]
        for rho in itertools.product(*(range(l) for l in lens)):
            st = Stratum(n, V, rho)
            strata.append(st)
            type_lists = [factorization_types(dj) for dj in st.d]
            profs = []
            for profile in itertools.product(*type_lists):
                count = sp.expand(sp.prod([mono_count(tp) for tp in profile]))
                members = []
                for j, tp in enumerate(profile):
                    for (g, mult) in tp:
                        members.append((st.e[j], g, mult))
                members = tuple(sorted(members))
                mass = sp.cancel(count * st.HS)
                rec = dict(V=st.V, rho=st.rho, e=tuple(st.e), d=tuple(st.d),
                           profile=profile, members=members, count=count,
                           mass=mass, stratum=st)
                records.append(rec)
                profs.append(rec)
                rows[members] = sp.cancel(rows[members] + mass)
            st.profiles = profs
    return dict(n=n, records=records, rows=dict(rows), strata=strata)


# ======================================================================
# SECTION 2 — CL-6 law-shape tests on the symbolic pack
# ======================================================================

PRIME_POWERS = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32,
                37, 41, 43, 47, 49]


def polygeom_denominator(expr, amax=40):
    """Decompose the reduced denominator of expr in ZZ[X]-factors; return
    (ok, b, alist) where ok <=> every irreducible factor is X or divides
    X^a - 1 for some a <= amax; b = X-power; alist = the multiset of minimal
    a's (with multiplicity of the factor)."""
    expr = sp.cancel(sp.together(expr))
    den = sp.denom(expr)
    poly = sp.Poly(den, q)
    b = 0
    alist = []
    const, factors = sp.factor_list(poly.as_expr(), q)
    for f, mult in factors:
        pf = sp.Poly(f, q)
        if pf.degree() == 0:
            continue
        if pf.as_expr() == q:
            b += mult
            continue
        found = None
        for a in range(1, amax + 1):
            if sp.rem(sp.Poly(q ** a - 1, q), pf).is_zero:
                found = a
                break
        if found is None:
            return (False, b, alist + [("BAD", sp.sstr(f), mult)])
        alist.extend([found] * mult)
    return (True, b, sorted(alist))


def nat_valued(expr, points=PRIME_POWERS):
    """Check expr(q0) is a nonnegative integer at each point."""
    bad = []
    for q0 in points:
        v = sp.Rational(sp.nsimplify(expr.subs(q, q0)))
        if v.q != 1 or v < 0:
            bad.append((q0, str(v)))
    return bad


def member_str(members):
    return "+".join((f"({e},{g})" if m == 1 else f"[{e},{g}]^{m}")
                    for (e, g, m) in members)


def test_pack_laws(pack, results):
    n = pack['n']
    banner(f"[P1/P3] CL-6 law shapes on the block-{n} one-step pack "
           f"({len(pack['records'])} strata, {len(pack['rows'])} roster rows)")
    # P1 part1
    total = sp.cancel(sum(r['mass'] for r in pack['records']))
    chk(f"n={n} [P1] part1: sum of all stratum masses = 1", sp.simplify(total - 1) == 0,
        f"got {total}")
    # P3a PolyGeom membership per roster row
    denom_inventory = {}
    all_ok = True
    for members, mass in sorted(pack['rows'].items()):
        ok, b, alist = polygeom_denominator(mass)
        denom_inventory[member_str(members)] = dict(qpow=b, geomDenoms=alist,
                                                    mass=sp.sstr(mass))
        if not ok:
            all_ok = False
            print(f"    ROW {member_str(members)}: BAD denominator {alist}")
    chk(f"n={n} [P3a] every roster-row mass has denom | X^b prod(1-X^a)", all_ok)
    # P3b count integrality + P3c degrees, per stratum-profile
    bad_int, bad_deg, maxdeg = [], [], 0
    for r in pack['records']:
        bad = nat_valued(r['count'])
        if bad:
            bad_int.append((member_str(r['members']), r['V'], r['rho'], bad))
        dg = sp.Poly(r['count'], q).degree()
        maxdeg = max(maxdeg, dg)
        if dg > n:
            bad_deg.append((member_str(r['members']), r['V'], r['rho'], dg))
    chk(f"n={n} [P3b] every stratum count polynomial is NAT-valued at all prime powers <= 49",
        not bad_int, str(bad_int[:5]))
    chk(f"n={n} [P3c] degree law: deg(count) <= n for every stratum (max observed {maxdeg})",
        not bad_deg, str(bad_deg[:5]))
    results[f"n{n}_rows"] = {member_str(k): sp.sstr(v) for k, v in pack['rows'].items()}
    results[f"n{n}_denom_inventory"] = denom_inventory
    results[f"n{n}_max_count_degree"] = maxdeg
    # kernel and det
    Kn = pack['rows'].get(((1, 1, n),), sp.Integer(0))
    detK = sp.cancel(1 - Kn)
    okK, bK, aK = polygeom_denominator(Kn)
    okD, bD, aD = polygeom_denominator(detK)
    chk(f"n={n} [P3a] K_n and det(1-K_n) in the PolyGeom class", okK and okD,
        f"K={Kn}")
    results[f"n{n}_K"] = sp.sstr(Kn)
    print(f"    K_{n} = {Kn} ;  det(1-K_{n}) = {sp.factor(detK)}")
    return Kn


# ======================================================================
# SECTION 3 — anchors: RESUMN3 (n=2,3) and beta4.json (n=4)
# ======================================================================

def solve_beta(pack, sub_betas):
    """Resummed block solve: beta_n(sigma) = [sum_rows mass * verdict-dist] / (1-K_n).
    sub_betas: dict k -> {sigma(tuple of (e,f)): rational fn} for k < n."""
    n = pack['n']
    Kn = pack['rows'].get(((1, 1, n),), sp.Integer(0))

    def member_dist(mem):
        e, g, mult = mem
        if mult == 1:
            return {((e, g),): sp.Integer(1)}
        if e == 1 and g == 1 and mult == n:
            return None  # kcol
        beta = sub_betas[mult]
        if e == 1 and g == 1:
            return beta
        if e == 1 and g >= 2:      # unramified frame F_{q^g}: q -> q^g, f *= g
            return {tuple(sorted((ee, ff * g) for (ee, ff) in sig)):
                    sp.cancel(val.subs(q, q ** g)) for sig, val in beta.items()}
        if g == 1 and e >= 2:      # ramified frame: same q, e *= e_seg
            return {tuple(sorted((ee * e, ff) for (ee, ff) in sig)): val
                    for sig, val in beta.items()}
        raise ValueError(f"unhandled continuation member {mem}")

    num = defaultdict(lambda: sp.Integer(0))
    for members, mass in pack['rows'].items():
        if members == ((1, 1, n),):
            continue
        dists = [member_dist(m) for m in members]
        for combo in itertools.product(*(d.items() for d in dists)):
            sigma = tuple(sorted(sum((list(sig) for sig, _ in combo), [])))
            pr = sp.prod([v for _, v in combo])
            num[sigma] = num[sigma] + mass * pr
    return {sig: sp.cancel(v / (1 - Kn)) for sig, v in num.items()}


def anchors_n2(pack2, results):
    banner("[P2a] n = 2 anchors vs CASE_RESUMN3 block-2 (hand-derived, sealed)")
    D3 = q ** 3 - 1
    rows = pack2['rows']
    recs = pack2['records']

    def lump(pred):
        return sp.cancel(sum(r['mass'] for r in recs if pred(r)))

    chk("n=2 m2-split (V={0,2}, int slope, distinct) = (q-1)(q-2)/2 / (q^3-1)",
        sp.simplify(lump(lambda r: r['V'] == (0, 2) and r['rho'] == (0,)
                         and r['members'] == ((1, 1, 1), (1, 1, 1)))
                    - (q - 1) * (q - 2) / 2 / D3) == 0)
    chk("n=2 m2-inert  = q(q-1)/2 / (q^3-1)",
        sp.simplify(rows[((1, 2, 1),)] - q * (q - 1) / 2 / D3) == 0)
    chk("n=2 m_w2 (2,1) = (q-1)q^2 / (q^3-1)",
        sp.simplify(rows[((2, 1, 1),)] - (q - 1) * q ** 2 / D3) == 0)
    chk("n=2 m_vv (V={0,1,2}) = (q-1)/(q^3-1)",
        sp.simplify(lump(lambda r: r['V'] == (0, 1, 2)) - (q - 1) / D3) == 0)
    chk("n=2 K_2 = (q-1)/(q^3-1)",
        sp.simplify(rows[((1, 1, 2),)] - (q - 1) / D3) == 0)
    beta2 = solve_beta(pack2, {})
    chk("n=2 beta_2 = (1/(2(q+1)), 1/(2(q+1)), q/(q+1))",
        sp.simplify(beta2[((1, 1), (1, 1))] - 1 / (2 * (q + 1))) == 0 and
        sp.simplify(beta2[((1, 2),)] - 1 / (2 * (q + 1))) == 0 and
        sp.simplify(beta2[((2, 1),)] - q / (q + 1)) == 0,
        str({k: sp.sstr(v) for k, v in beta2.items()}))
    chk("n=2 beta_2 sums to 1", sp.simplify(sum(beta2.values()) - 1) == 0)
    results['beta2'] = {str(k): sp.sstr(v) for k, v in beta2.items()}
    return beta2


def anchors_n3(pack3, beta2, results):
    banner("[P2b] n = 3 anchors vs CASE_RESUMN3 S1 (hand-derived, sealed)")
    D3, D6 = q ** 3 - 1, q ** 6 - 1
    recs = pack3['records']

    def lump(pred):
        return sp.cancel(sum(r['mass'] for r in recs if pred(r)))

    # A: V={0,3}, integer slope (rho=0)
    A = {tuple(sorted(t)): c for t, c in [
        ([(1, 1, 1)] * 3, (q - 1) * (q - 2) * (q - 3) / 6),
        ([(1, 1, 1), (1, 2, 1)], q * (q - 1) ** 2 / 2),
        ([(1, 3, 1)], (q ** 3 - q) / 3),
        ([(1, 1, 1), (1, 1, 2)], (q - 1) * (q - 2)),
        ([(1, 1, 3)], (q - 1))]}
    okA = all(sp.simplify(
        lump(lambda r, mm=mm: r['V'] == (0, 3) and r['rho'] == (0,) and r['members'] == mm)
        - c / D6) == 0 for mm, c in A.items())
    chk("n=3 stratum A (V={0,3}, int slope): all five per-type masses = counts/D6", okA)
    # B: V={0,3}, fractional slope -> (3,1)
    chk("n=3 stratum B total = (q-1)(q^5+q^3)/D6",
        sp.simplify(lump(lambda r: r['V'] == (0, 3) and r['rho'] != (0,))
                    - (q - 1) * (q ** 5 + q ** 3) / D6) == 0)
    # C: V={0,1,3}
    chk("n=3 C-odd ((1,1)+(2,1)) = (q-1)q^4/D6",
        sp.simplify(lump(lambda r: r['V'] == (0, 1, 3) and r['e'][1] == 2)
                    - (q - 1) * q ** 4 / D6) == 0)
    okCe = all(sp.simplify(lump(
        lambda r, mm=mm: r['V'] == (0, 1, 3) and r['e'][1] == 1 and r['members'] == mm)
        - c / D6) == 0 for mm, c in [
        (tuple(sorted([(1, 1, 1)] * 3)), (q - 1) * (q - 2) / 2),
        (tuple(sorted([(1, 1, 1), (1, 2, 1)])), q * (q - 1) / 2),
        (tuple(sorted([(1, 1, 1), (1, 1, 2)])), (q - 1))])
    chk("n=3 C-even per-type = counts/D6 (distinct, irred, double)", okCe)
    # D: V={0,2,3}
    chk("n=3 D-odd ((1,1)+(2,1)) = (q-1)^2 q^2/(D3 D6)",
        sp.simplify(lump(lambda r: r['V'] == (0, 2, 3) and r['e'][0] == 2)
                    - (q - 1) ** 2 * q ** 2 / (D3 * D6)) == 0)
    okDe = all(sp.simplify(lump(
        lambda r, mm=mm: r['V'] == (0, 2, 3) and r['e'][0] == 1 and r['members'] == mm)
        - c / (D3 * D6)) == 0 for mm, c in [
        (tuple(sorted([(1, 1, 1)] * 3)), (q - 1) ** 2 * (q - 2) / 2),
        (tuple(sorted([(1, 1, 1), (1, 2, 1)])), q * (q - 1) ** 2 / 2),
        (tuple(sorted([(1, 1, 1), (1, 1, 2)])), (q - 1) ** 2)])
    chk("n=3 D-even per-type = counts/(D3 D6)", okDe)
    # E: all vertices
    chk("n=3 stratum E = (q-1)^2/(D3 D6) -> (1,1)^3",
        sp.simplify(lump(lambda r: r['V'] == (0, 1, 2, 3)) - (q - 1) ** 2 / (D3 * D6)) == 0)
    # K_3, J, t_3, beta_3 vs the hand solve (resum_n3_seal transcription)
    rows = pack3['rows']
    chk("n=3 K_3 = (q-1)/(q^6-1)", sp.simplify(rows[((1, 1, 3),)] - (q - 1) / D6) == 0)
    Jhand = ((q - 1) * (q - 2) + (q - 1)) / D6 + (q - 1) ** 2 / (D3 * D6)
    Jmine = sp.cancel(sum(m for k, m in rows.items() if any(x == (1, 1, 2) for x in k)))
    chk("n=3 J (split-leg coefficient) matches RESUMN3", sp.simplify(Jmine - Jhand) == 0,
        f"mine {Jmine} vs {sp.cancel(Jhand)}")
    t3 = {'111': ((q - 1) * (q - 2) * (q - 3) / 6) / D6 + ((q - 1) * (q - 2) / 2) / D6
                 + ((q - 1) ** 2 * (q - 2) / 2) / (D3 * D6) + (q - 1) ** 2 / (D3 * D6),
          '112': (q * (q - 1) ** 2 / 2) / D6 + (q * (q - 1) / 2) / D6
                 + (q * (q - 1) ** 2 / 2) / (D3 * D6),
          '13': ((q ** 3 - q) / 3) / D6,
          '1121': ((q - 1) * q ** 4) / D6 + ((q - 1) ** 2 * q ** 2) / (D3 * D6),
          '31': ((q - 1) * (q ** 5 + q ** 3)) / D6}
    key = {'111': ((1, 1), (1, 1), (1, 1)), '112': ((1, 1), (1, 2)),
           '13': ((1, 3),), '1121': ((1, 1), (2, 1)), '31': ((3, 1),)}
    k3 = (q - 1) / D6
    b2m = {'111': beta2[((1, 1), (1, 1))], '112': beta2[((1, 2),)],
           '1121': beta2[((2, 1),)], '13': 0, '31': 0}
    beta3_hand = {key[s]: sp.cancel((t3[s] + Jhand * b2m[s]) / (1 - k3)) for s in t3}
    beta3 = solve_beta(pack3, {2: beta2})
    ok3 = all(sp.simplify(beta3[sig] - beta3_hand[sig]) == 0 for sig in beta3_hand)
    chk("n=3 composed beta_3 == RESUMN3 hand solve (all five sigma)", ok3,
        str({str(k): sp.sstr(v) for k, v in beta3.items()}))
    chk("n=3 beta_3 sums to 1", sp.simplify(sum(beta3.values()) - 1) == 0)
    results['beta3'] = {str(k): sp.sstr(v) for k, v in beta3.items()}
    return beta3


def anchors_n4(pack4, beta2, beta3, results):
    banner("[P2c] n = 4 anchor: composed beta_4 vs results/beta4.json (order-4 "
           "cluster law, BCFG-reconciled)")
    import ast
    with open(os.path.join(HERE, "..", "results", "beta4.json")) as fh:
        raw = json.load(fh)
    ref = {tuple(sorted(ast.literal_eval(k))): sp.cancel(sp.sympify(v, locals={'q': q}))
           for k, v in raw.items()}
    beta4 = solve_beta(pack4, {2: beta2, 3: beta3})
    chk("n=4 beta_4 sums to 1", sp.simplify(sum(beta4.values()) - 1) == 0)
    ok = True
    for sig in sorted(set(ref) | set(beta4)):
        mine, theirs = beta4.get(sig), ref.get(sig)
        if mine is None or theirs is None:
            ok = chk(f"n=4 beta_4[{sig}] present in both", False,
                     f"mine={mine} ref={theirs}") and ok
            continue
        same = sp.simplify(mine - theirs) == 0
        ok = chk(f"n=4 beta_4[{sig}] == beta4.json", same,
                 f"mine={sp.sstr(mine)}  ref={sp.sstr(theirs)}") and ok
    results['beta4'] = {str(k): sp.sstr(v) for k, v in beta4.items()}
    # PolyGeom membership of the resummed solve values (the CL-6 consumer shape)
    bad = [str(sig) for sig, v in beta4.items() if not polygeom_denominator(v)[0]]
    chk("n=4 [P3a] every beta_4(sigma) in the PolyGeom denominator class", not bad,
        str(bad))
    return beta4


# ======================================================================
# SECTION 4 — exhaustive census (the scount_val / tcount_val content)
# ======================================================================

class Fq:
    """Tiny F_q arithmetic + monic-poly factorization typing, q = p^delta,
    delta in {1,2}.  Elements are ints 0..q-1; for delta=2, x = c0 + p*c1
    represents c0 + c1*t with t^2 = red (p=2: t^2=t+1; p=3: t^2=2)."""

    def __init__(self, p, delta):
        self.p, self.delta, self.q = p, delta, p ** delta
        qq = self.q
        if delta == 1:
            self.mul = [[(a * b) % p for b in range(p)] for a in range(p)]
            self.add = [[(a + b) % p for b in range(p)] for a in range(p)]
        else:
            def unpack(x):
                return (x % p, x // p)

            def pack(c0, c1):
                return c0 + p * c1
            if p == 2:
                red = (1, 1)     # t^2 = 1 + t
            elif p == 3:
                red = (2, 0)     # t^2 = 2
            else:
                raise ValueError
            self.add = [[pack((a % p + b % p) % p, (a // p + b // p) % p)
                         for b in range(qq)] for a in range(qq)]
            M = []
            for a in range(qq):
                row = []
                a0, a1 = unpack(a)
                for b in range(qq):
                    b0, b1 = unpack(b)
                    c0 = a0 * b0
                    c1 = a0 * b1 + a1 * b0
                    c2 = a1 * b1
                    row.append(pack((c0 + c2 * red[0]) % p, (c1 + c2 * red[1]) % p))
                M.append(row)
            self.mul = M
        self.inv = [None] * qq
        for a in range(1, qq):
            for b in range(1, qq):
                if self.mul[a][b] == 1:
                    self.inv[a] = b
                    break
        self._build_types()

    # monic polys as tuples (a_0,...,a_{d-1}) (leading 1 implicit)
    def polmul(self, u, v):
        du, dv = len(u), len(v)   # degrees (monic)
        out = [0] * (du + dv + 1)
        cu = list(u) + [1]
        cv = list(v) + [1]
        for i, a in enumerate(cu):
            if a == 0:
                continue
            for jj, b in enumerate(cv):
                if b == 0:
                    continue
                out[i + jj] = self.add[out[i + jj]][self.mul[a][b]]
        assert out[du + dv] == 1
        return tuple(out[:du + dv])

    def _build_types(self):
        """type_table[d][coeff-tuple] = sorted tuple of (g, mult) for monic
        degree-d polys with const != 0, d <= 4."""
        irr = {1: [(c,) for c in range(self.q)]}
        for d in (2, 3, 4):
            allp = set(itertools.product(range(self.q), repeat=d))
            # composite = any product of lower-degree monics
            comp = set()
            monics = {dd: list(itertools.product(range(self.q), repeat=dd))
                      for dd in range(1, d)}
            for d1 in range(1, d):
                d2 = d - d1
                if d1 > d2:
                    break
                for u in monics[d1]:
                    for v in monics[d2]:
                        comp.add(self.polmul(u, v))
            irr[d] = [t for t in allp if t not in comp]
        self.irreducibles = irr
        # factor by trial division
        self.type_table = {d: {} for d in (1, 2, 3, 4)}

        # additive inverse table
        self.neg = [None] * self.q
        for a in range(self.q):
            for b in range(self.q):
                if self.add[a][b] == 0:
                    self.neg[a] = b
                    break

        def poldiv(f, g):
            """f, g monic coeff-tuples (implicit leading 1); return (quot tuple,
            is_exact) for exact division test."""
            df, dg = len(f), len(g)
            F = list(f) + [1]
            for k in range(df - dg, -1, -1):
                c = F[dg + k]
                if c != 0:
                    # F -= c * g * x^k   (g monic with implicit leading 1)
                    gg = list(g) + [1]
                    for jj in range(dg + 1):
                        F[jj + k] = self.add[F[jj + k]][self.neg[self.mul[c][gg[jj]]]]
                # record quotient coefficient c... (monic case: c is quot coeff)
            # after elimination, remainder = F[0:dg]
            return all(x == 0 for x in F[:dg])

        def factor_type(f):
            d = len(f)
            rem = f
            fac = Counter()
            for dd in (1, 2, 3, 4):
                if dd > len(rem):
                    break
                for g in self.irreducibles.get(dd, []):
                    while len(rem) >= len(g) and poldiv(rem, g):
                        fac[(dd, g)] += 1
                        rem = self._exact_quot(rem, g)
                        if len(rem) == 0:
                            break
                    if len(rem) == 0:
                        break
                if len(rem) == 0:
                    break
            assert len(rem) == 0, f"factorization failed {f}"
            return tuple(sorted((g_deg, m) for (g_deg, _), m in fac.items()
                                for _ in [0]))

        self._poldiv_exact = poldiv
        for d in (1, 2, 3, 4):
            for f in itertools.product(range(self.q), repeat=d):
                if f[0] == 0:
                    continue   # const != 0 only (never needed otherwise)
                self.type_table[d][f] = factor_type(f)

    def _exact_quot(self, f, g):
        """f / g for monic tuples, assuming exact."""
        df, dg = len(f), len(g)
        F = list(f) + [1]
        Q = [0] * (df - dg + 1)
        gg = list(g) + [1]
        for k in range(df - dg, -1, -1):
            c = F[dg + k]
            Q[k] = c
            if c != 0:
                for jj in range(dg + 1):
                    F[jj + k] = self.add[F[jj + k]][self.neg[self.mul[c][gg[jj]]]]
        assert all(x == 0 for x in F[:dg])
        assert Q[-1] == 1
        return tuple(Q[:-1])


def lower_hull(pts):
    """Lower convex hull of integer points (x asc).  Returns hull vertices."""
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # keep only strict lower turns: remove x2 if it's above or on the
            # segment (x1,y1)-(pt)
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull


def classify_box(avec, n, p, N, fq, PPOW):
    """One-step read of the entry-state box (a_0..a_{n-1}), a_i given as:
      delta=1: ints mod p^N;  delta=2: (c0, c1) int pairs mod p^N.
    Returns ('ok', stratum_instance_key, row_key) or ('undec',) .
    stratum_instance_key = (V, rho, profile, m)."""
    delta = fq.delta
    vals = []
    for a in avec:
        if delta == 1:
            if a == 0:
                vals.append(None)
                continue
            v = 0
            while a % p == 0:
                a //= p
                v += 1
            vals.append(v)
        else:
            c0, c1 = a
            if c0 == 0 and c1 == 0:
                vals.append(None)
                continue
            v = 0
            while c0 % p == 0 and c1 % p == 0:
                c0 //= p
                c1 //= p
                v += 1
            vals.append(v)
    if vals[0] is None:
        return ('undec',)
    pts = [(i, v) for i, v in enumerate(vals) if v is not None] + [(n, 0)]
    hull = lower_hull(pts)
    V = [x for x, _ in hull]
    hy = {x: y for x, y in hull}
    r = len(V) - 1
    D = tuple(hy[V[j - 1]] - hy[V[j]] for j in range(1, r + 1))
    lens = [V[j] - V[j - 1] for j in range(1, r + 1)]
    # hull heights everywhere + decidability
    heights = [None] * (n + 1)
    for j in range(1, r + 1):
        a_, b_ = V[j - 1], V[j]
        for i in range(a_, b_ + 1):
            heights[i] = Fraction(hy[b_] * (b_ - a_) + D[j - 1] * (b_ - i), b_ - a_)
    for i in range(n):
        h = heights[i]
        if h.denominator == 1:
            if int(h) + 1 > N:
                return ('undec',)
        else:
            if math.ceil(h) > N:
                return ('undec',)
        if vals[i] is None and math.ceil(h) > N:
            return ('undec',)

    def digit(i, l):
        if i == n:
            return 1 if l == 0 else 0
        a = avec[i]
        if delta == 1:
            return (a // PPOW[l]) % p
        c0, c1 = a
        return (c0 // PPOW[l]) % p + p * ((c1 // PPOW[l]) % p)

    rho, es, ds, profile, members = [], [], [], [], []
    for j in range(1, r + 1):
        lj = lens[j - 1]
        Dj = D[j - 1]
        rho_j = Dj % lj
        gg = math.gcd(lj, Dj)
        e_j, d_j = lj // gg, gg
        rho.append(rho_j)
        es.append(e_j)
        ds.append(d_j)
        # residual coefficients at lattice points v_{j-1} + m*e_j, m = 0..d_j
        coeffs = []
        for m in range(d_j + 1):
            i = V[j - 1] + m * e_j
            l = int(heights[i])
            coeffs.append(digit(i, l))
        lead = coeffs[-1]
        assert lead != 0
        il = fq.inv[lead]
        monic = tuple(fq.mul[c][il] for c in coeffs[:-1])
        assert monic[0] != 0
        tp = fq.type_table[d_j][monic]
        profile.append(tp)
        for (g_, m_) in tp:
            members.append((e_j, g_, m_))
    mvec = tuple((D[j] - rho[j]) // lens[j] for j in range(r))
    key = (tuple(V), tuple(rho), tuple(profile), mvec)
    return ('ok', key, tuple(sorted(members)))


def run_census(pack, p, delta, N, results):
    n = pack['n']
    fq = Fq(p, delta)
    q0 = fq.q
    label = f"n={n} q={q0}(p={p},delta={delta}) N={N}"
    t0 = time.time()
    # predicted: per stratum instance
    pred = {}
    for st in pack['strata']:
        for (m, E, Nr) in st.m_instances(N):
            for rec in st.profiles:
                cnt = sp.Rational(sp.nsimplify(rec['count'].subs(q, q0)))
                assert cnt.q == 1 and cnt >= 0
                c = int(cnt) * q0 ** (n * (N - 1) - E)
                key = (st.V, st.rho, rec['profile'], m)
                pred[key] = pred.get(key, 0) + c
    pred_total = sum(pred.values())
    # enumerate boxes: a_i = p * b_i, b_i over Z/p^(N-1) reps (delta=1)
    # or pairs (delta=2)
    PPOW = [p ** l for l in range(N + 1)]
    got = defaultdict(int)
    undec = 0
    if delta == 1:
        reps = range(p ** (N - 1))
        coeff_of = lambda b: p * b
    else:
        reps = list(itertools.product(range(p ** (N - 1)), repeat=2))
        coeff_of = lambda b: (p * b[0], p * b[1])
    nbox = 0
    for combo in itertools.product(reps, repeat=n):
        nbox += 1
        avec = [coeff_of(b) for b in combo]
        res = classify_box(avec, n, p, N, fq, PPOW)
        if res[0] == 'undec':
            undec += 1
        else:
            got[res[1]] += 1
    # compare
    mism = []
    for key in set(pred) | set(got):
        if pred.get(key, 0) != got.get(key, 0):
            mism.append((key, pred.get(key, 0), got.get(key, 0)))
    ok = chk(f"[P4] census tie {label}: every stratum instance count == "
             f"COUNT(q0)*q0^(n(N-1)-E)  [{len(pred)} predicted instances, "
             f"{nbox} boxes, {time.time()-t0:.0f}s]",
             not mism, f"first mismatches {mism[:5]}")
    chk(f"[P4] census complement {label}: undecided = box - sum(decided)",
        undec == nbox - pred_total,
        f"undec {undec} vs {nbox - pred_total}")
    # zero-fiber law [P4z]: strata instances with predicted 0 got 0 (subsumed by
    # the tie above, but report the count-vanishing profile sites explicitly)
    zero_sites = sorted({(member_str(rec['members']), sp.sstr(rec['count']))
                         for st in pack['strata'] for rec in st.profiles
                         if sp.nsimplify(rec['count'].subs(q, q0)) == 0})
    results.setdefault('zero_fiber_sites', {})[label] = [list(z) for z in zero_sites]
    if zero_sites:
        print(f"    [P4z] {label}: count-polynomial zero fibers (census must be "
              f"and is 0): {[z[0] for z in zero_sites]}")
    return ok


# ======================================================================
# SECTION 5 — PARI/gp oracle spot-check of terminal verdicts
# ======================================================================

def gp_full_types(polys, p):
    """sigma (sorted (e,f) multiset) per integer monic poly via gp:
    factorpadic + liftall + nfinit([G,[p]]) + idealprimedec (the
    quartic_oracle.py method)."""
    lines = ["default(parisize, 256000000);"]
    for k, coeffs in enumerate(polys):
        pol = "+".join(f"({c})*x^{i}" for i, c in enumerate(coeffs))
        lines.append(
            f"F = factorpadic({pol}, {p}, 80);"
            f"S = []; for(i=1, matsize(F)[1],"
            f" G = liftall(F[i,1]);"
            f" if(poldegree(G)==1, S = concat(S,[[1,1]]),"
            f"  nf = nfinit([G,[{p}]]); pr = idealprimedec(nf,{p})[1];"
            f"  S = concat(S,[[pr.e, pr.f]])));"
            f"print(\"RES {k} \", S);")
    proc = subprocess.run([os.path.expanduser("~/.local/bin/gp"), "-q", "-f"],
                          input="\n".join(lines), capture_output=True, text=True,
                          timeout=600)
    out = {}
    for line in proc.stdout.splitlines():
        if line.startswith("RES "):
            _, k, rest = line.split(" ", 2)
            sig = tuple(sorted(tuple(x) for x in json.loads(rest)))
            out[int(k)] = sig
    return out


def oracle_spotcheck(pack, p, nsamp, results):
    n = pack['n']
    fq = Fq(p, 1)
    N = 14
    PPOW = [p ** l for l in range(N + 1)]
    rng = random.Random(12345 + n * 100 + p)
    samples = []
    tries = 0
    while len(samples) < nsamp and tries < nsamp * 60:
        tries += 1
        avec = [p * rng.randrange(p ** (N - 1)) for _ in range(n)]
        res = classify_box(avec, n, p, N, fq, PPOW)
        if res[0] != 'ok':
            continue
        members = res[2]
        if all(m == 1 for (_, _, m) in members):
            sig = tuple(sorted((e, g) for (e, g, _) in members))
            samples.append((avec, sig))
    polys = [coeffs + [1] for coeffs, _ in samples]
    got = gp_full_types(polys, p)
    bad = []
    for k, (avec, sig) in enumerate(samples):
        if got.get(k) != sig:
            bad.append((avec, sig, got.get(k)))
    chk(f"[P5] oracle n={n} p={p}: {len(samples)} terminal one-step reads, "
        f"predicted sigma == factorpadic/idealprimedec", not bad,
        f"first {bad[:3]}")
    results.setdefault('oracle', {})[f"n{n}_p{p}"] = dict(
        samples=len(samples), mismatches=len(bad))


# ======================================================================
# MAIN
# ======================================================================

def main():
    results = {}
    banner("N3-cl6-polygeom: building the symbolic packs (n = 2, 3, 4)")
    packs = {}
    # mono sanity: sum over types = (q-1) q^(d-1)
    for d in (1, 2, 3, 4):
        tot = sp.expand(sum(mono_count(t) for t in factorization_types(d)))
        chk(f"engine sanity: sum of Mono_{d}(type) = (q-1)q^{d-1}",
            sp.simplify(tot - (q - 1) * q ** (d - 1)) == 0, sp.sstr(tot))
    for n in (2, 3, 4):
        t0 = time.time()
        packs[n] = build_pack(n)
        print(f"  pack n={n}: {len(packs[n]['records'])} stratum-profiles, "
              f"{len(packs[n]['rows'])} roster rows  ({time.time()-t0:.1f}s)")

    for n in (2, 3, 4):
        test_pack_laws(packs[n], results)

    beta2 = anchors_n2(packs[2], results)
    beta3 = anchors_n3(packs[3], beta2, results)
    anchors_n4(packs[4], beta2, beta3, results)

    banner("[P4] exhaustive census over entry boxes (wild p and prime-power "
           "pools emphasized)")
    census_cfg = [
        (2, 2, 1, 8), (2, 3, 1, 5), (2, 5, 1, 4), (2, 7, 1, 3),
        (2, 2, 2, 4), (2, 3, 2, 3),
        (3, 2, 1, 8), (3, 3, 1, 5), (3, 5, 1, 4), (3, 7, 1, 3),
        (3, 2, 2, 4), (3, 3, 2, 3),
        (4, 2, 1, 6), (4, 3, 1, 4), (4, 5, 1, 3), (4, 7, 1, 2),
        (4, 2, 2, 3), (4, 3, 2, 2),
    ]
    for (n, p, delta, N) in census_cfg:
        run_census(packs[n], p, delta, N, results)

    banner("[P4z] n = 3 zero-fiber list vs RESUMN3 sealed ENTRY-VANISHING; "
           "n = 4 list (new)")
    # RESUMN3 sealed (block-3, entry-conditional strata): at q0=2 the vanishing
    # profiles are exactly {A-3dist, A-split, C-even-distinct, D-even-distinct}
    # (all with a (q-2) factor; 3dist also (q-3)); at q0=3: A-3dist only.
    van = {}
    for n in (2, 3, 4):
        for q0 in (2, 3, 4, 5):
            sites = sorted({member_str(rec['members'])
                            for st in packs[n]['strata'] for rec in st.profiles
                            if sp.nsimplify(rec['count'].subs(q, q0)) == 0})
            van[(n, q0)] = sites
            if sites:
                print(f"  n={n} q0={q0}: count-polynomial vanishes for rows {sites}")
    n3_q2 = set(van[(3, 2)])
    chk("n=3 q0=2 vanishing rows match RESUMN3 (split-type rows with (q-2) factors)",
        n3_q2 == {"(1,1)+(1,1)+(1,1)", "(1,1)+[1,1]^2"},
        str(n3_q2))
    chk("n=3 q0=3 vanishing rows match RESUMN3 (A-3dist only)",
        set(van[(3, 3)]) == {"(1,1)+(1,1)+(1,1)"}, str(van[(3, 3)]))
    results['vanishing'] = {f"n{n}_q{q0}": v for (n, q0), v in van.items()}

    banner("[P5] PARI oracle spot-check (terminal one-step verdicts, wild p incl.)")
    try:
        for n in (3, 4):
            for p in (2, 3, 5):
                oracle_spotcheck(packs[n], p, 60, results)
    except Exception as e:
        print(f"  oracle leg SKIPPED: {type(e).__name__}: {e}")
        results['oracle_error'] = str(e)

    banner("SUMMARY")
    print(f"total checks: {CHECKS[0]}; failures: {len(FAILURES)}")
    for f in FAILURES:
        print(f"  FAIL {f}")
    results['n_checks'] = CHECKS[0]
    results['failures'] = FAILURES
    results['elapsed_s'] = round(time.time() - T0, 1)
    with open(os.path.join(HERE, "N3-cl6-polygeom_results.json"), "w") as fh:
        json.dump(results, fh, indent=1, default=str)
    print(f"\nresults JSON written; elapsed {time.time()-T0:.0f}s")
    return 0 if not FAILURES else 1


if __name__ == "__main__":
    sys.exit(main())
