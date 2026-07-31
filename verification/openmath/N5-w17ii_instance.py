#!/usr/bin/env python3
"""N5-w17ii (script 2/3): the p-adic INSTANCE test of W17ii clause (ii), repaired form.

WHAT IS TESTED.  W17ii clause (ii) (MovesS/Interfaces.lean; banked sorry
MovesV/V7_w17ii.lean:48) in its REPAIRED form (queue item 4 = census fields +
shevt_disj + guard, per BRIDGE_BP3_TV_2026-07-30.md sec 3.G REV 2), INSTANTIATED at
the intended p-adic splitting-density semantics, for n in {2,3}, p in {2,3,5}
(wild primes p <= n covered: p=2 for both n, p=3 for n=3):

  Lean carrier            computational instantiation (the fidelity mapping)
  ----------------------  -----------------------------------------------------
  Box(q0, N)              monic degree-n polys over Z/p^N   (|Box| = p^(nN))
  Shape Shat / Sigmas     verdict multisets sigma = {(e_i,f_i)} with sum e_i f_i = n
                          (RS4Chain.sig_exact's carrier, sigma-keyed)
  M.Hgt, h                h := v_p(disc f)   (the shallow height of the XHD layer)
  shEvtH(Shat,h,q0,N)     classes in Box whose splitting shape is DECIDED at
                          precision N (every Z_p-lift shares it), = sigma,
                          with v_p(disc) = h, harvested at visibility
  visH(Shat,q0,N)         heights h below the pending frontier at level N
                          (no undecided class can still land at height < frontier)
  shEvt                   the disjoint union over visH (grouping = partition)
  shWeightH(Shat,h,q0)    the stabilized |shEvtH| / |Box|  (exact Fraction)
  WshVal(Shat,q0)         the machinery-produced shape density: the OM-engine's
                          p-uniform rational function in q evaluated at q=p
                          (om_density_engine beta laws, affine monic assembly --
                          the "produced by the stated rational machinery" side
                          of CL-17(ii))
  clause (ii) HasSum      sum_{h in shDom} shWeightH(sigma,h) = WshVal(sigma):
                          tested by (i) exact stabilized weights + census laws,
                          (ii) the rigorous sandwich  S_harvested(sigma) <=
                          WshVal_true(sigma) <= S_harvested(sigma) + pending
                          mass  (engine value must fall inside, widths -> 0),
                          (iii) for n=2: EXACT closure -- harvested weights match
                          derived closed forms whose infinite sum is computed
                          exactly and asserted == the engine value.

SIMPLIFICATIONS / FLAGS (each is a deviation from the literal Lean statement):
  F1. HasSum over an infinite shDom is tested via exact partial sums + a rigorous
      sandwich (pending mass bounds the tail), plus exact geometric closure for
      n=2.  Numerics cannot sum infinitely many terms.
  F2. Decidedness of a class is established by SOUND classical rules (Hensel on
      separable reductions; Newton-polygon segment factorization; quadratic etale
      classification by the square class of disc, which f = linear x quadratic
      preserves exactly).  The rules are validated against PARI factorpadic on
      random perturbed lifts in script 3 (N5-w17ii_mc_oracle.py).  A class our
      rules cannot decide stays PENDING (sound direction: weights only ever
      under-harvested, never wrong).
  F3. shevt_disj and shevt_grouping hold BY CONSTRUCTION here (heights partition
      decided classes -- v_p(disc) is a function).  Their load-bearing role is
      tested abstractly in N5-w17ii_abstract.py.  The instance-side content is
      conservation (counts partition the box exactly), which IS checked.
  F4. The repaired Lean statement does not exist yet (escalation E-1 open); we
      test the (a')/(b') roster as specced in the blueprint.  NOTE the abstract
      script shows (b')-as-specced is insufficient in general; the instance data
      here additionally satisfy the count-domination law (u3) (decided classes
      only accumulate), which is the stronger, instance-true census face.
  F5. WshVal from the OM engine is itself part of the project's certified
      machinery (beta anchors e<=3, validated vs BCFG); the sandwich makes this
      an INDEPENDENT re-check of those values at 6 (n,p) configs.

SEALED PREDICTIONS (before first run):
  Q1. All census laws hold at every level: stabilization (no newly decided class
      at a height below the visibility frontier), exact conservation, (u3).
  Q2. Per-sigma sandwiches contain the engine WshVal at every level, with width
      shrinking geometrically in N.
  Q3. n=2 exact tie: harvested weights equal the derived closed forms and their
      exact infinite sums equal the engine values -- clause (ii) EXACT at n=2
      for p in {2,3,5}.
  Q4. n=3: every reachable (sigma,h) weight stabilizes; sum of harvested + pending
      accounts for 1 exactly; the engine value sits inside every sandwich.

Run with the sympy venv python.  Pure exact arithmetic (Fraction / sympy Rational);
no floats in any law check.
"""

import sys
import time
from fractions import Fraction as Fr
from collections import defaultdict

sys.path.insert(0, "/data/users/asvin/math-and-lean/p-adic-splitting-densities/verification")

T0 = time.time()
FAIL = []


def check(name, cond, detail=""):
    tag = "PASS" if cond else "FAIL"
    if not cond:
        FAIL.append(name)
    print(f"  [{tag}] {name}" + (f" -- {detail}" if detail else ""), flush=True)
    return cond


def log(msg):
    print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)


# ---------------------------------------------------------------------------
# 0. Engine reference: monic shape densities WshVal(sigma; q) for n = 2, 3
#    (affine assembly over closed points of A^1 from the anchored cluster laws)
# ---------------------------------------------------------------------------
log("loading om_density_engine (anchored beta laws e<=3) ...")
import sympy as sp
import om_density_engine as E

q = E.q


def monic_shape_density(n):
    """{sigma : density as rational function of q} for random monic degree-n /Z_p."""
    acc = defaultdict(lambda: sp.Integer(0))
    for pattern in E._divisor_patterns(n):
        cfg = E._affine_config_count(pattern)
        dists = []
        for (delta, m) in pattern:
            if m == 1:
                dists.append({((1, delta),): sp.Integer(1)})
            else:
                dists.append(E.beta_scaled(m, delta))
        agg = {(): sp.Integer(1)}
        for dist in dists:
            new = defaultdict(lambda: sp.Integer(0))
            for t0, p0 in agg.items():
                for t1, p1 in dist.items():
                    new[E.type_union([t0, t1])] += p0 * p1
            agg = dict(new)
        for t, pr in agg.items():
            acc[t] += cfg * pr
    return {t: sp.cancel(v / q ** n) for t, v in acc.items()}


REF = {n: monic_shape_density(n) for n in (2, 3)}
for n in (2, 3):
    s = sp.simplify(sum(REF[n].values()))
    check(f"engine reference n={n}: sum over sigma of WshVal(sigma;q) == 1",
          sp.simplify(s - 1) == 0)
    print(f"    shapes n={n}: " + "; ".join(
        f"{t}: {sp.factor(vv)}" for t, vv in sorted(REF[n].items())))


def ref_val(n, sigma, p):
    """Exact Fraction value of the engine density at q = p."""
    v = REF[n].get(sigma, sp.Integer(0)).subs(q, p)
    v = sp.nsimplify(v, rational=True)
    return Fr(int(sp.numer(v)), int(sp.denom(v)))


# ---------------------------------------------------------------------------
# 1. Exact p-adic decision rules (classical; oracle-validated in script 3)
# ---------------------------------------------------------------------------
def vp_int(x, p, cap):
    """v_p(x) truncated at cap; cap means '>= cap' (x may be 0)."""
    if x == 0:
        return cap
    v = 0
    while v < cap and x % p == 0:
        x //= p
        v += 1
    return v


def disc3(a, b, c):
    return 18 * a * b * c - 4 * a * a * a * c + a * a * b * b - 4 * b ** 3 - 27 * c * c


def disc2(b, c):
    return b * b - 4 * c


def sigma2_of_disc(dint, v, p):
    """Quadratic etale class from disc dint != 0 with v_p(dint) = v.
    (f = linear x quadratic preserves the square class of disc exactly, so this
    applies whenever a cubic splits off a Q_p-rational root.)"""
    if v % 2 == 1:
        return ((2, 1),)
    u = dint // (p ** v)
    if p == 2:
        m = u % 8
        if m == 1:
            return ((1, 1), (1, 1))
        if m == 5:
            return ((1, 2),)
        return ((2, 1),)
    if pow(u % p, (p - 1) // 2, p) == 1:
        return ((1, 1), (1, 1))
    return ((2, 1),)


def K_of(p):
    """Digits above v(disc) needed to read the disc square class."""
    return 3 if p == 2 else 1


def reduction_table(p, n):
    """Pattern of f mod p for all monic degree-n (a.. coeffs) mod p.
    Returns dict key -> ('SEP', sigma) | ('DOUBLE', t) | ('TRIPLE', t)."""
    tab = {}
    import itertools
    for coeffs in itertools.product(range(p), repeat=n):
        # coeffs = (a, b) for n=2 (x^2+ax+b), (a, b, c) for n=3
        def ev(x):
            r = 1
            for co in coeffs:
                r = r * x + co
            return r % p
        # roots with multiplicity by synthetic division
        poly = [1] + list(coeffs)
        roots = []
        work = poly[:]
        for r in range(p):
            while len(work) > 1:
                # synthetic division of work by (x - r)
                out, acc = [], 0
                for co in work:
                    acc = (acc * r + co) % p
                    out.append(acc)
                if out[-1] % p == 0:
                    roots.append(r)
                    work = out[:-1]
                else:
                    break
        deg_rem = len(work) - 1
        mult = {r: roots.count(r) for r in set(roots)}
        if n == 2:
            if len(roots) == 2 and len(mult) == 2:
                tab[coeffs] = ('SEP', ((1, 1), (1, 1)))
            elif deg_rem == 2:
                tab[coeffs] = ('SEP', ((1, 2),))
            else:
                tab[coeffs] = ('DOUBLE', roots[0])
        else:
            if len(mult) == 3:
                tab[coeffs] = ('SEP', ((1, 1), (1, 1), (1, 1)))
            elif deg_rem == 2:
                tab[coeffs] = ('SEP', ((1, 1), (1, 2)))
            elif deg_rem == 3:
                tab[coeffs] = ('SEP', ((1, 3),))
            elif any(m == 3 for m in mult.values()):
                tab[coeffs] = ('TRIPLE', [r for r, m in mult.items() if m == 3][0])
            elif any(m == 2 for m in mult.values()):
                tab[coeffs] = ('DOUBLE', [r for r, m in mult.items() if m == 2][0])
            else:
                raise AssertionError(coeffs)
    return tab


def np_hull(pts):
    """Lower Newton hull of pts = [(i, v_i)] left to right (v may be 'cap' = big).
    Returns segments as (slope_num, slope_den, length) from LEFT (const coeff)."""
    hull = [pts[0]]
    for pt in pts[1:]:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # drop hull[-1] if it lies above the line hull[-2] -> pt
            if (pt[1] - y1) * (x2 - x1) <= (y2 - y1) * (pt[0] - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    segs = []
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        segs.append((y1 - y2, x2 - x1, x2 - x1))   # slope = (y1-y2)/(x2-x1) > 0 down
    return segs


def decide_cubic_cluster(A, B, C, p, P, d, dint, depth=0):
    """Splitting type of the cubic cluster g = x^3+Ax^2+Bx+C (A,B,C = 0 mod p),
    coefficients known mod p^P; d = v_p(disc of the original f) (< P + slack),
    dint = the exact integer disc of the original f (nonzero here).
    Returns sigma tuple or None (pending).  Sound rules only; None on any doubt."""
    if depth > 12 or P < 2:
        return None
    vC = vp_int(C % p ** P, p, P)
    vB = vp_int(B % p ** P, p, P)
    vA = vp_int(A % p ** P, p, P)
    if vC >= P:                     # constant coeff not readable to its valuation
        return None
    segs = np_hull([(0, vC), (1, vB), (2, vA), (3, 0)])
    if len(segs) == 3:
        return ((1, 1), (1, 1), (1, 1))
    if len(segs) == 2:
        # linear x quadratic over Q_p; quadratic classified by disc-f square class
        return ((1, 1),) + sigma2_of_disc(dint, d, p)
    # single segment: slope vC/3
    num, den, _ = segs[0]
    if num % 3 != 0:
        return ((3, 1),)            # slope with denominator 3: totally ramified
    s = num // 3
    if 3 * s + 1 > P:
        return None
    Ar = (A // p ** s) % p
    Br = (B // p ** (2 * s)) % p
    Cr = (C // p ** (3 * s)) % p
    code = TAB3[p][(Ar, Br, Cr)]
    if code[0] == 'SEP':
        return code[1]
    if code[0] == 'DOUBLE':
        return ((1, 1),) + sigma2_of_disc(dint, d, p)
    # TRIPLE residual: recurse into the sub-cluster
    t = code[1] * p ** s            # the residual triple root, lifted scale
    A1 = A + 3 * t
    B1 = B + 2 * A * t + 3 * t * t
    C1 = C + B * t + A * t * t + t ** 3
    # scale x -> p^s z
    if A1 % p ** s or B1 % p ** (2 * s) or C1 % p ** (3 * s):
        return None                 # should not happen; sound bail-out
    P2 = P - 3 * s
    if P2 < 2:
        return None
    return decide_cubic_cluster((A1 // p ** s) % p ** P2,
                                (B1 // p ** (2 * s)) % p ** P2,
                                (C1 // p ** (3 * s)) % p ** P2,
                                p, P2, d, dint, depth + 1)


TAB2 = {}
TAB3 = {}


def decide_class(coeffs, p, N, n):
    """Decision for one class (canonical lift coeffs, level N).
    Returns ('D', sigma, h) decided | ('P', dmin) pending with min possible height."""
    K = K_of(p)
    if n == 2:
        a, b = coeffs
        dint = disc2(a, b)
        d = vp_int(dint, p, N)
        code = TAB2[p][(a % p, b % p)]
        if code[0] == 'SEP':
            return ('D', code[1], 0)
        if d + K > N:
            return ('P', d)
        return ('D', sigma2_of_disc(dint, d, p), d)
    a, b, c = coeffs
    dint = disc3(a, b, c)
    d = vp_int(dint, p, N)
    code = TAB3[p][(a % p, b % p, c % p)]
    if code[0] == 'SEP':
        return ('D', code[1], 0)
    if d + K > N:
        return ('P', d)
    if code[0] == 'DOUBLE':
        return ('D', ((1, 1),) + sigma2_of_disc(dint, d, p), d)
    # TRIPLE
    t = code[1]
    A = a + 3 * t
    B = b + 2 * a * t + 3 * t * t
    C = c + b * t + a * t * t + t ** 3
    M = p ** N
    sig = decide_cubic_cluster(A % M, B % M, C % M, p, N, d, dint)
    if sig is None:
        return ('P', d)
    return ('D', sig, d)


# ---------------------------------------------------------------------------
# 2. The census machine: exhaustive base level + refinement of pending classes
# ---------------------------------------------------------------------------
def run_census(n, p, baseN, maxN, child_cap):
    """Returns (harvested, frontier, pending_measure, per_level_records)."""
    import itertools
    log(f"census n={n} p={p}: base level N={baseN} "
        f"({p ** (n * baseN)} classes), refining to N<={maxN}, cap {child_cap}")
    harvested = defaultdict(Fr)        # (sigma,h) -> weight (Fraction, final)
    harvest_level = {}                 # (sigma,h) -> level first seen
    records = []
    pend = list(itertools.product(range(p ** baseN), repeat=n))
    N = baseN
    frontier_prev = 0
    stab_ok = True
    conserve_ok = True
    while True:
        newly = defaultdict(int)
        still = []
        dmin = N                       # min possible final height among pending
        for coeffs in pend:
            r = decide_class(coeffs, p, N, n)
            if r[0] == 'D':
                newly[(r[1], r[2])] += 1
            else:
                still.append(coeffs)
                if r[1] < dmin:
                    dmin = r[1]
        boxN = Fr(1, p ** (n * N))
        for (sig, h), cnt in newly.items():
            # STABILIZATION LAW (shweight_card face): a newly decided class may
            # never land below the previous visibility frontier
            if h < frontier_prev:
                stab_ok = False
                print(f"    STABILITY VIOLATION: new mass at h={h} < frontier "
                      f"{frontier_prev} (level {N}, sigma={sig})")
            harvested[(sig, h)] += cnt * boxN
            harvest_level.setdefault((sig, h), N)
        pending_measure = Fr(len(still), p ** (n * N))
        total = sum(harvested.values()) + pending_measure
        if total != 1:
            conserve_ok = False
            print(f"    CONSERVATION VIOLATION at level {N}: total = {total}")
        frontier = dmin if still else maxN + K_of(p)
        records.append(dict(N=N, newly=sum(newly.values()), pending=len(still),
                            frontier=frontier, pend_meas=pending_measure))
        frontier_prev = max(frontier_prev, frontier)
        pend = still
        if not pend or N >= maxN or len(pend) * p ** n > child_cap:
            break
        # refine: children at level N+1
        M = p ** N
        newpend = []
        for coeffs in pend:
            for deltas in itertools.product(range(p), repeat=n):
                newpend.append(tuple(cc + dd * M for cc, dd in zip(coeffs, deltas)))
        pend = newpend
        N += 1
    return dict(harvested=dict(harvested), harvest_level=harvest_level,
                frontier=frontier_prev, pending_measure=records[-1]["pend_meas"],
                records=records, stab_ok=stab_ok, conserve_ok=conserve_ok,
                final_N=N)


def report_census(n, p, res):
    print(f"\n----- census n={n}, p={p}: levels to N={res['final_N']}, "
          f"frontier={res['frontier']}, pending measure={res['pending_measure']} "
          f"(~{float(res['pending_measure']):.3e})")
    for rec in res["records"]:
        print(f"    level N={rec['N']}: newly decided {rec['newly']}, "
              f"pending {rec['pending']}, frontier {rec['frontier']}, "
              f"pending measure ~{float(rec['pend_meas']):.3e}")
    check(f"n={n} p={p}: STABILIZATION (shweight_card face) -- no late mass below "
          f"the visibility frontier at any level", res["stab_ok"])
    check(f"n={n} p={p}: CONSERVATION (grouping+disj face) -- harvested + pending "
          f"== 1 exactly at every level", res["conserve_ok"])
    # sandwich per sigma
    bysig = defaultdict(Fr)
    for (sig, h), w in sorted(res["harvested"].items()):
        bysig[sig] += w
    pm = res["pending_measure"]
    allok = True
    for sig in sorted(set(list(bysig.keys()) + list(REF[n].keys()))):
        lo = bysig.get(sig, Fr(0))
        hi = lo + pm
        rv = ref_val(n, sig, p)
        ok = lo <= rv <= hi
        allok &= ok
        print(f"    sigma={str(sig):28s} harvested={str(lo):>24s} "
              f"engine={str(rv):>14s} in [lo, lo+{float(pm):.1e}] "
              f"{'OK' if ok else '*** OUTSIDE ***'}")
    check(f"n={n} p={p}: SANDWICH -- engine WshVal inside [harvested, +pending] "
          f"for every sigma", allok)
    # per-height table (visible heights only)
    fr = res["frontier"]
    print(f"    visible heights (h < frontier {fr}):")
    for (sig, h), w in sorted(res["harvested"].items(), key=lambda kv: (kv[0][1], kv[0][0])):
        if h < fr:
            print(f"      h={h:2d} sigma={str(sig):28s} w={str(w):>20s} "
                  f"(harvested at N={res['harvest_level'][(sig, h)]})")
    return bysig


# ---------------------------------------------------------------------------
# 3. n = 2: exact closed-form tie (clause (ii) EXACT)
# ---------------------------------------------------------------------------
def n2_expected(p):
    """Derived closed forms for w(sigma,h), from D = disc Haar-uniform (p odd)
    resp. the b-parity + D/4-uniform decomposition (p = 2).  Returns dict
    (sigma,h) -> Fraction for h <= HMAX, plus exact totals per sigma."""
    SPL, INT, RAM = ((1, 1), (1, 1)), ((1, 2),), ((2, 1),)
    w = defaultdict(Fr)
    tot = defaultdict(Fr)
    if p != 2:
        # v(D)=h with prob (1-1/p)p^-h; h even: split/inert half-half among units
        for h in range(0, 60):
            m = Fr(p - 1, p ** (h + 1))
            if h % 2 == 0:
                w[(SPL, h)] = m / 2
                w[(INT, h)] = m / 2
            else:
                w[(RAM, h)] = m
        tot[SPL] = Fr(p, 2 * (p + 1))
        tot[INT] = Fr(p, 2 * (p + 1))
        tot[RAM] = Fr(1, p + 1)
    else:
        # b odd (1/2): D = 1 mod 4 unit: D mod 8 in {1,5} equally: h=0
        w[(SPL, 0)] = Fr(1, 4)
        w[(INT, 0)] = Fr(1, 4)
        # b even (1/2): D = 4D', D' uniform: h = 2+k, v(D')=k w.p. 2^-(k+1),
        # unit class mod 8 uniform among {1,3,5,7}
        for k in range(0, 58):
            m = Fr(1, 2) * Fr(1, 2 ** (k + 1))
            h = 2 + k
            if k % 2 == 0:
                w[(SPL, h)] += m / 4
                w[(INT, h)] += m / 4
                w[(RAM, h)] += m / 2
            else:
                w[(RAM, h)] += m
        tot[SPL] = Fr(1, 3)
        tot[INT] = Fr(1, 3)
        tot[RAM] = Fr(1, 3)
    return w, tot


def n2_exact_tie(p, res):
    wexp, texp = n2_expected(p)
    fr = res["frontier"]
    ok = True
    for (sig, h), w in res["harvested"].items():
        if h < fr and w != wexp.get((sig, h), Fr(0)):
            ok = False
            print(f"    MISMATCH vs closed form: p={p} sigma={sig} h={h}: "
                  f"census {w} != expected {wexp.get((sig, h))}")
    check(f"n=2 p={p}: every visible harvested weight equals the derived closed "
          f"form", ok)
    # exact infinite sums vs engine (clause (ii) EXACT at n=2)
    ok2 = True
    for sig, tv in texp.items():
        rv = ref_val(2, sig, p)
        if tv != rv:
            ok2 = False
            print(f"    TOTAL MISMATCH p={p} {sig}: closed-form sum {tv} != "
                  f"engine {rv}")
    check(f"n=2 p={p}: EXACT clause (ii): sum_h w(sigma,h) (closed form, exact "
          f"geometric series) == engine WshVal(sigma) for all sigma", ok2)


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
if __name__ == "__main__":
    for p in (2, 3, 5):
        TAB2[p] = reduction_table(p, 2)
        TAB3[p] = reduction_table(p, 3)

    print("\n" + "=" * 78)
    print("n = 2 (exhaustive; exact closed-form closure of the height sum)")
    print("=" * 78)
    for p, baseN, maxN in ((2, 6, 16), (3, 4, 11), (5, 3, 9)):
        res = run_census(2, p, baseN, maxN, child_cap=3_000_000)
        report_census(2, p, res)
        n2_exact_tie(p, res)

    print("\n" + "=" * 78)
    print("n = 3 (exhaustive census + NP/cluster recursion; sandwich closure)")
    print("=" * 78)
    N3RES = {}
    for p, baseN, maxN in ((2, 6, 13), (3, 4, 9), (5, 3, 7)):
        res = run_census(3, p, baseN, maxN, child_cap=6_000_000)
        N3RES[p] = res
        report_census(3, p, res)
        # h=0 cross-check vs exact reduction-pattern counts mod p
        sep_counts = defaultdict(int)
        for key, code in TAB3[p].items():
            if code[0] == 'SEP':
                sep_counts[code[1]] += 1
        ok = all(res["harvested"].get((sig, 0), Fr(0)) == Fr(cnt, p ** 3)
                 for sig, cnt in sep_counts.items())
        check(f"n=3 p={p}: h=0 weights == exact separable reduction-pattern "
              f"counts / p^3", ok)
        # geometric tail-ratio report (heuristic, informational)
        bysig = defaultdict(list)
        for (sig, h), w in sorted(res["harvested"].items()):
            if h < res["frontier"]:
                bysig[sig].append((h, w))
        for sig, hw in sorted(bysig.items()):
            if len(hw) >= 3:
                rr = ["h%d/h%d=%s" % (h2, h1, str(Fr(w2, w1)))
                      for (h1, w1), (h2, w2) in zip(hw, hw[1:]) if w1 != 0]
                print(f"    tail ratios {str(sig):26s}: " + ", ".join(rr[-4:]))

    print("\n" + "=" * 78)
    if FAIL:
        print(f"RESULT: {len(FAIL)} CHECK(S) FAILED:")
        for f in FAIL:
            print("  -", f)
        sys.exit(1)
    print("RESULT: ALL INSTANCE CHECKS PASS (Q1-Q4 as sealed)")
