#!/usr/bin/env python3
"""U6_krun_probe.py — IFK-U6-FIRST: the V4-ordered falsifier (V4_ifk_review.jsonl
item 22) for K-RUN's no-phantom face at depth >= 2.

CLAIM UNDER TEST (IFK_BLUEPRINT_2026-07-31.md, Face K-RUN + §4 U6; M18 §7
NUMERIC-TESTS = M18-realization-complete_fable.md):
  K-RUN (roster/realization faithfulness), depth-2 slice: at every level N,
  the realized run set on canDec x is EXACTLY the level-N truncation of the
  canonical OM tree T_can — in the numerically testable form of M18 Theorem C,
  the counting tie  T_gamma(x,h) = T-hat_gamma(x,h)  on length-2 templates.
  Blueprint's own falsifier: "any T < T-hat length-2 stratum is a
  real-instance negation witness" (a PHANTOM: a chain the per-step census
  counts but no polynomial realizes).

========================= FIDELITY MAP (Lean/blueprint -> computation) ======
Lean-side objects (none of the Phase-B instance carriers exist on disk, per
M18 B§6; we compute at the intended p-adic semantics M18 §6):
  * canonical branch tree T_can(f)  <->  the classical Okutsu-Montes cluster
    walk: residual factorization mod p, then per repeated linear residue root
    a Newton-polygon read of the recentered cluster (one node per polygon
    read; the m01_quad_walker.py / N7-track-count_test.py engine idiom).
  * step (m_k, h_k, cell a_k)  <->  one certified cluster read: species m_k
    (continuing / terminal kind), height h_k = the side slope (Fraction),
    fresh digit cell a_k = the repeated residual root (continuing) or the
    full residual read-off datum (terminal), matching M18 §6.2 (I0)
    "Assign(m,x,h) = fresh digit cells realizing (m,h) from x".
  * marked pair (f mod p^N, eta)  <->  (g, chain) with g in the enumerated
    coefficient box and chain = the depth-2 read path (a1-cell, d2-datum).
  * T_gamma (census count, D4R.4-normalized)  <->  #realized chains, with the
    equal-fiber law (each chain's locus = p^{dim - A(P-hat)} boxes) checked
    EXPLICITLY per stratum (failures reported: they break the D4R.4
    normalization that defines T, i.e. duties (I1)/(I2)).
  * T-hat_gamma (chain census, Sigma-shaped product recursion, M18 §2/§5)
    <->  Sigma over realized step-1 cells a1 of #(step-2 menu from the
    a1-extended history). MENU SEMANTICS (the load-bearing choice): the
    step-2 menu is computed PER-STEP from the frame state only —
    (h1, mu2) := (previous height, cluster size) — as the set of reads d2
    realizable by SOME box polynomial satisfying the frame's cluster
    condition (all mu2 cluster roots at valuation > h1), NOT jointly with
    the step-1 read. This is the "formal fresh-assignment chain" of K-RUN's
    nonempty-locus clause: M18 Test B's failure mode is verbatim "a formal
    chain with empty locus, a direct counterexample to duty (I0)/(I1)";
    under joint menus the tie is a tautology and nothing is tested.
    Structural fact used: realized chains' step-2 reads always satisfy the
    frame cluster condition, so T <= T-hat holds by construction and any
    strict inequality is a phantom.
  * PHANTOM (the FIRES witness)  <->  a pair (extended prefix x1 =
    (h1, a1, mu2), d2) with d2 in the per-step menu of the frame state but
    ZERO polynomials in the exhaustively enumerated box realizing the
    composite (step-1 read (m1,h1) via a1, then step-2 read d2).

DEVIATIONS from the M18 §7 test rows (declared, with why):
  D1. CYLINDER enumeration + translation invariance instead of full monic
      boxes. f |-> f(y+r) is a bijection of the level-N monic box sending
      the entry-cluster at residue r to the cluster at 0; all reads are
      invariant. So we enumerate the r=0 entry-cluster cylinder
      { g : all non-leading coeffs of the cluster part have v >= 1 } once;
      full-box censuses = p * (cylinder censuses) + decided depth-0 mass.
      The tie T = T-hat is per-stratum and unaffected. VALIDATED by gate V2
      (tiny full box, all r, vs the cylinder).
  D2. Levels N re-chosen per row so that every read with heights within the
      row's cap is CERTIFIED below the precision horizon (the spec's own
      instruction: "never trust an unstabilized count ... raise N for that
      stratum"). Spec rows (2,3,6) and (3,3,4) cannot certify their stated
      H at their stated N (an h2=3 quadratic read needs v up to 7; a mu2=2
      h2=2 read needs v up to 5). Rows run here (cylinder sizes):
        n=2, p=2: N=9  (2^16),  caps h1<=3, h2<=4
        n=2, p=3: N=7  (3^12),  caps h1<=2, h2<=3
        n=3, p=2: N=7  (2^18),  mu=3 entry; h1<=2, h2<=3 (mu2=2), h2<=2 (mu2=3)
        n=3, p=3: N=5  (3^12),  mu=3 entry; h1=1,  h2<=2
      This includes the spec's wild-corner emphasis (p=2 n=2; p=3 n=3).
  D3. n=3 with a DOUBLE root entry (mu=2, third root simple): by Hensel the
      level-N box factors bijectively as (cluster quadratic) x (unit linear)
      and the cluster reads equal the quadratic's reads, so this row's tie
      is the n=2 row's tie. We VERIFY the reduction numerically (gate V4)
      on random samples instead of re-enumerating 3.2M polynomials.
  D4. Reads whose deciding valuations touch the precision horizon are
      binned IMPRECISE and excluded from BOTH sides symmetrically (counted,
      reported as coverage loss). Reads with heights beyond the cap are
      binned DEEP likewise.
  D5. Depth is truncated at 2 (the face under test); step-2 continuing
      reads are recorded as continuing cells, not walked further.

TESTS RUN (M18 §7 NUMERIC-TESTS, executed at the D2 rows):
  Test A (length-1 tie / tmark_last_surj analogue): per length-1 stratum
    (m1,h1): all cell fibers equal and a power of p; census = #cells * fiber.
  Test B (length-2 counting tie, THE direct K-RUN test): per stratum
    (m1,h1)(m2,h2): T-hat (per-step menus) vs T (realized chains), plus the
    equal-fiber law across chains in the stratum, plus N vs N-1
    stabilization of every count.
  Test C (targeted phantom scan): every (prefix, d2) pair with d2 in the
    per-step menu but empty realized locus, over ALL templates reachable in
    two reads including terminal second steps — reported exactly.
VALIDATION GATES: V1 PARI factorpadic leaf tie on samples; V2 full-box vs
  cylinder (tiny N); V3 realized-menu subset of per-step menu (assert);
  V4 Hensel mu=2 reduction; V5 stabilization N vs N-1.

VERDICT SEMANTICS: FIRES (phantom found: K-RUN as drafted false at depth 2;
  witness printed exactly) | SURVIVES (no phantom, no fiber-law violation,
  all gates green; coverage printed) | UNTESTABLE (exact obstruction).

Run:  python3 verification/openmath/U6_krun_probe.py [--quick]
Log:  verification/openmath/logs/U6.log (tee'd by the caller)
JSON: verification/openmath/results/U6_krun_results.json
"""
import sys, os, json, time, argparse, itertools, random
from fractions import Fraction

sys.path.insert(0, os.path.expanduser('~/.local/lib/python3.10/site-packages'))

# ------------------------------------------------------------------ basics
def vp(x, p, horizon):
    """(valuation, exact?) of integer x known mod p^horizon.
    exact=False means x = 0 mod p^horizon, so v >= horizon only."""
    x %= p ** horizon
    if x == 0:
        return horizon, False
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v, True

def poly_shift(coeffs, z, pN):
    """coeffs = [c0..c_{n-1}] of monic f = x^n + ...; return coeffs of
    f(y+z) mod pN (monic, same length). Exact integer Taylor shift."""
    n = len(coeffs)
    full = list(coeffs) + [1]
    for i in range(n):                    # synthetic division shift
        for j in range(n - 1, i - 1, -1):
            full[j] = (full[j] + z * full[j + 1]) % pN
    return full[:n]

def lower_hull(pts):
    """Lower convex hull of pts=[(j, v)] (j increasing). Returns vertices."""
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (x2 - x1) * (pt[1] - y1) <= (pt[0] - x1) * (y2 - y1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull

def fp_poly_roots(coeffs, p):
    """Roots with multiplicity of a monic poly over F_p given low->high
    coeffs (with leading 1 appended by caller). Trial division, p<=3, deg<=3."""
    cs = [c % p for c in coeffs]
    roots = {}
    for r in range(p):
        m = 0
        work = list(cs)
        while True:
            # evaluate and divide by (x - r) while root
            val = 0
            for c in reversed(work):
                val = (val * r + c) % p
            if val != 0:
                break
            # synthetic division by (x - r)
            out = []
            acc = 0
            for c in reversed(work):
                acc = (acc * r + c) % p
                out.append(acc)
            out = out[:-1][::-1]  # drop remainder (=0), back to low->high
            # out is one degree lower, leading coeff retained
            work = out
            m += 1
            if len(work) == 1:
                break
        if m:
            roots[r] = m
    deg = len(cs) - 1
    used = sum(roots.values())
    return roots, deg - used   # (root->mult, degree of rootless part)

# ------------------------------------------------------- certified reads
# A "read" of a cluster (the mu roots of monic g with valuation > h_prev,
# centered at 0) returns branches. Branch encodings (all data F_p digits /
# small ints; heights as Fraction):
#   ('cont', h, digit, mu_next)   repeated residual root -> walk continues
#   ('splitleaf', h, digit)       simple residual root   -> decided leaf (1,1)
#   ('inert', h, d, psi)          irreducible residual factor deg d>=2 ->
#                                 decided leaf (1,d); psi = canonical coeffs
#   ('ram', h, e, digit)          fractional slope h, e = denominator ->
#                                 decided leaf (e,1) (residual length 1 here)
#   ('deep', size)                certified beyond height cap (out of scope)
# status 'imprecise': some needed valuation not certified at this N.

def hull_of(coeffs, p, N):
    """Lower hull data of monic poly (coeffs = c0..c_{n-1}, leading 1).
    Returns (hull_vertices, ok) where ok=False marks an uncertifiable hull.
    Inexact points (coeff = 0 mod p^N) are certified to lie on/above the
    exact-point hull iff N >= hull value there; leading (n,0) always exact.
    A fully-inexact left block [0,j0) is returned via 'left_block'."""
    n = len(coeffs)
    vals = [vp(c, p, N) for c in coeffs] + [(0, True)]
    exact_pts = [(j, v) for j, (v, ex) in enumerate(vals) if ex]
    hull = lower_hull(exact_pts)

    def hull_at(x):
        for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
            if x1 <= x <= x2:
                return Fraction(y1) + Fraction(y2 - y1, x2 - x1) * (x - x1)
        return None  # left of hull

    j0 = exact_pts[0][0]           # leftmost exact index
    ok = True
    for j, (v, ex) in enumerate(vals):
        if ex or j < j0:
            continue
        hv = hull_at(j)
        if hv is not None and Fraction(N) < hv:
            ok = False             # inexact point could dip below the hull
    return hull, j0, ok

def side_reads(coeffs, p, N, hull, j0, h_prev, hcap):
    """All branch reads from hull sides with slope steeper than -h_prev
    (root valuation lam > h_prev), heights capped at hcap.
    Returns (branches, cluster_len, status). cluster_len counts roots at
    valuation > h_prev including any certified left block."""
    branches, clen = [], 0
    if j0 > 0:
        # left block [0,j0): all coeffs inexact; root valuations >=
        # (N - v(c_{j0}))/j0 each (conservative). Certify as deep or fail.
        vj0 = hull[0][1]
        bound = Fraction(N - vj0, j0)
        if bound > hcap and bound > h_prev:
            branches.append(('deep', j0))
            clen += j0
        else:
            return None, None, 'imprecise'
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        lam = Fraction(y1 - y2, x2 - x1)          # root valuation on side
        if lam <= h_prev:
            continue
        clen += x2 - x1
        if lam > hcap:
            branches.append(('deep', x2 - x1))
            continue
        e, a = lam.denominator, lam.numerator     # slope = a/e lowest terms
        ell = (x2 - x1) // e
        # residual coefficients: exactness needed at v_i < N (guaranteed:
        # v_i <= y1 < N since (x1,y1) is an exact vertex)
        rc = []
        for i in range(ell + 1):
            j, v_i = x1 + i * e, y1 - i * a
            c = coeffs[j] if j < len(coeffs) else 1
            v, ex = vp(c, p, N)
            rc.append((c // p ** v_i) % p if (ex and v == v_i) else 0)
        assert rc[0] != 0 and rc[-1] != 0, "side endpoints must be exact units"
        if e > 1:
            assert ell == 1, "unexpected long ramified side at n<=3"
            root = (-rc[0] * pow(rc[1], -1, p)) % p
            branches.append(('ram', lam, e, root))
            continue
        roots, rootless_deg = fp_poly_roots(rc, p)
        for r, m in sorted(roots.items()):
            if m == 1:
                branches.append(('splitleaf', lam, r))
            else:
                branches.append(('cont', lam, r, m))
        if rootless_deg:
            # normalize the rootless part is not needed: deg 2/3 with no
            # roots over F_p is a single irreducible; datum = full residual
            # shape (canonical: monic-normalized residual coeffs)
            lead_inv = pow(rc[-1], -1, p)
            psi = tuple((c * lead_inv) % p for c in rc)
            branches.append(('inert', lam, rootless_deg, psi))
    return branches, clen, 'ok'

def read_cluster(coeffs, p, N, mu, h_prev, hcap):
    """Certified read of the size-mu cluster (valuation > h_prev) of monic
    g (coeffs mod p^N). Returns (branches, status); status 'imprecise' or
    'no-cluster' (cluster condition fails: sides steeper than h_prev do not
    total mu) or 'ok'."""
    hull, j0, ok = hull_of(coeffs, p, N)
    if not ok:
        return None, 'imprecise'
    br, clen, st = side_reads(coeffs, p, N, hull, j0, h_prev, hcap)
    if st != 'ok':
        return None, st
    if clen != mu:
        return None, 'no-cluster'
    return br, 'ok'

# ------------------------------------------------------------- the walker
def walk_depth2(coeffs, p, N, mu, hcap):
    """Depth-2 canonical walk of the entry cluster (size mu, center 0,
    h_prev = 0). Returns dict:
      status: 'ok'|'imprecise'
      step1:  list of step-1 branches (as read datums)
      chains: list of (h1, a1, mu2, d2) for each realized length-2 marked
              prefix (d2 = full step-2 branch datum)
      step2imprecise: count of continuing step-1 branches whose step-2 read
              was imprecise (coverage loss, excluded both sides)"""
    br1, st = read_cluster(coeffs, p, N, mu, 0, hcap)
    if st != 'ok':
        return {'status': 'imprecise'}
    out = {'status': 'ok', 'step1': br1, 'chains': [], 'step2imprecise': 0}
    pN = p ** N
    for b in br1:
        if b[0] != 'cont':
            continue
        _, h1, a1, mu2 = b
        assert h1.denominator == 1
        g2 = poly_shift(coeffs, a1 * p ** int(h1), pN)
        br2, st2 = read_cluster(g2, p, N, mu2, int(h1), hcap)
        if st2 != 'ok':
            # 'no-cluster' cannot happen after a genuine continuing read
            assert st2 == 'imprecise', st2
            out['step2imprecise'] += 1
            continue
        for d2 in br2:
            out['chains'].append((int(h1), a1, mu2, d2))
    return out

def frame_menu_reads(coeffs, p, N, hcap, h1_range, n):
    """Per-step (fresh-frame) reads: for each integer h1 in h1_range and
    mu2 >= 2, if g satisfies the frame cluster condition at (h1, mu2)
    (sides steeper than h1 total exactly mu2), contribute the step-2 reads.
    Returns list of ((h1, mu2), d2). Imprecise hulls contribute
    (('imprecise',), None) markers."""
    hull, j0, ok = hull_of(coeffs, p, N)
    if not ok:
        return [(('imprecise',), None)]
    out = []
    for h1 in h1_range:
        br, clen, st = side_reads(coeffs, p, N, hull, j0, h1, hcap)
        if st != 'ok':
            out.append((('imprecise',), None))
            continue
        if clen < 2 or clen > n:
            continue
        mu2 = clen
        for d2 in br:
            out.append(((h1, mu2), d2))
    return out

# ---------------------------------------------------------------- sweeps
def cylinder_iter(n, p, N):
    """All monic degree-n coefficient tuples (c0..c_{n-1}) mod p^N with every
    ci divisible by p (the r=0 entry-cluster cylinder; f-bar = y^n)."""
    reps = [p * k for k in range(p ** (N - 1))]
    return itertools.product(reps, repeat=n)

def s1_stratum(b):
    """Length-1 stratum key (species, height) of a step-1 branch."""
    kind = b[0]
    if kind == 'cont':
        return ('cont', b[1], b[3])          # (kind, h1, mu_next)
    if kind == 'ram':
        return ('ram', b[1], b[2])           # (kind, h, e)
    if kind == 'inert':
        return ('inert', b[1], b[2])         # (kind, h, deg)
    if kind == 'splitleaf':
        return ('splitleaf', b[1], None)
    return ('deep', None, None)

def s1_cell(b):
    """Cell datum of a step-1 branch (the read-off digits)."""
    kind = b[0]
    if kind == 'cont':
        return b[2]
    if kind in ('ram', 'splitleaf'):
        return b[2] if kind == 'splitleaf' else b[3]
    if kind == 'inert':
        return b[3]
    return None

def run_row(n, p, N, mu_entry, hcap, h1max, sample_cap=400, seed=0):
    """One exhaustive cylinder sweep. Returns the raw censuses."""
    pN = p ** N
    rng = random.Random(seed)
    s1_census = {}        # (stratum1, cell) -> count
    ch_census = {}        # (h1, a1, mu2, d2) -> count   [realized chains]
    menus = {}            # (h1, mu2) -> {d2: witness_coeffs}
    menu_imprecise = 0
    n_entry_imprecise = n_noclus = n_step2_imprecise = n_total = 0
    oracle_samples = []   # (coeffs, decided (e,f) multiset) for gate V1
    h1_range = range(1, h1max + 1)
    for coeffs in cylinder_iter(n, p, N):
        n_total += 1
        w = walk_depth2(list(coeffs), p, N, mu_entry, hcap)
        if w['status'] != 'ok':
            n_entry_imprecise += 1
        else:
            n_step2_imprecise += w['step2imprecise']
            leaves, decided = [], True
            for b in w['step1']:
                key = (s1_stratum(b), s1_cell(b))
                s1_census[key] = s1_census.get(key, 0) + 1
                if b[0] == 'splitleaf':
                    leaves.append((1, 1))
                elif b[0] == 'inert':
                    leaves.append((1, b[2]))
                elif b[0] == 'ram':
                    leaves.append((b[2], 1))
                elif b[0] == 'deep':
                    decided = False
            if w['step2imprecise']:
                decided = False
            for ch in w['chains']:
                ch_census[ch] = ch_census.get(ch, 0) + 1
                d2 = ch[3]
                if d2[0] == 'splitleaf':
                    leaves.append((1, 1))
                elif d2[0] == 'inert':
                    leaves.append((1, d2[2]))
                elif d2[0] == 'ram':
                    leaves.append((d2[2], 1))
                else:
                    decided = False
            if decided and leaves and len(oracle_samples) < sample_cap \
               and rng.random() < 0.02:
                oracle_samples.append((coeffs, tuple(sorted(leaves))))
        for fkey, d2 in frame_menu_reads(list(coeffs), p, N, hcap,
                                         h1_range, n):
            if fkey == ('imprecise',):
                menu_imprecise += 1
                continue
            if d2[0] == 'deep':
                continue
            menus.setdefault(fkey, {}).setdefault(d2, coeffs)
    return dict(n=n, p=p, N=N, mu=mu_entry, hcap=hcap, h1max=h1max,
                total=n_total, s1=s1_census, chains=ch_census, menus=menus,
                entry_imprecise=n_entry_imprecise,
                step2_imprecise=n_step2_imprecise,
                menu_imprecise=menu_imprecise, samples=oracle_samples)

# ----------------------------------------------------------------- tests
def is_ppow(x, p):
    while x % p == 0:
        x //= p
    return x == 1

def test_A(row):
    """Length-1 tie: per stratum (m1,h1): equal cell fibers, power of p,
    census = #cells * fiber. Returns (ok, table, violations)."""
    strata = {}
    for (st, cell), cnt in row['s1'].items():
        if st[0] == 'deep':
            continue
        strata.setdefault(st, {})[cell] = cnt
    table, viol = [], []
    for st in sorted(strata, key=str):
        cells = strata[st]
        fibers = sorted(set(cells.values()))
        ok = len(fibers) == 1 and is_ppow(fibers[0], row['p'])
        census = sum(cells.values())
        table.append((st, len(cells), fibers, census, ok))
        if not ok:
            viol.append((st, dict(cells)))
    return (not viol), table, viol

def test_BC(row):
    """Length-2 counting tie T vs T-hat (per-step menus) + equal-fiber law
    + the targeted phantom scan (Test C shape: menu entry, empty locus).
    Returns dict with per-stratum table, phantom list, fiber violations."""
    p = row['p']
    # realized step-1 continuing cells per (h1, mu2)
    a1_sets = {}
    for (st, cell), cnt in row['s1'].items():
        if st[0] == 'cont':
            a1_sets.setdefault((int(st[1]), st[2]), set()).add(cell)
    # realized chains grouped by stratum2 = (h1, mu2, kind2, h2, extra2)
    def s2_key(h1, mu2, d2):
        kind = d2[0]
        extra = d2[3] if kind == 'cont' else (d2[2] if kind in
                                              ('ram', 'inert') else None)
        return (h1, mu2, kind, d2[1], extra)
    strata = {}
    for (h1, a1, mu2, d2), cnt in row['chains'].items():
        if d2[0] == 'deep':
            continue
        strata.setdefault(s2_key(h1, mu2, d2), {})[(a1, d2)] = cnt
    # menu entries grouped the same way
    menu_by_stratum = {}
    for (h1, mu2), dd in row['menus'].items():
        for d2, wit in dd.items():
            menu_by_stratum.setdefault(s2_key(h1, mu2, d2), {})[d2] = wit
    table, phantoms, fib_viol, v3_viol = [], [], [], []
    all_strata = sorted(set(strata) | set(menu_by_stratum), key=str)
    for sk in all_strata:
        h1, mu2 = sk[0], sk[1]
        A1 = a1_sets.get((h1, mu2), set())
        chains = strata.get(sk, {})
        menu = menu_by_stratum.get(sk, {})
        # V3: every realized d2 must be in the per-step menu
        for (a1, d2) in chains:
            if d2 not in menu:
                v3_viol.append((sk, a1, d2))
        T = len(chains)
        That = len(A1) * len(menu)
        fibers = sorted(set(chains.values()))
        fib_ok = (T == 0) or (len(fibers) == 1 and is_ppow(fibers[0], p))
        if not fib_ok:
            fib_viol.append((sk, {str(k): v for k, v in chains.items()}))
        # the phantom scan (Test C granularity)
        for a1 in sorted(A1):
            for d2, wit in sorted(menu.items(), key=str):
                if (a1, d2) not in chains:
                    phantoms.append(dict(stratum=sk, a1=a1, d2=d2,
                                         menu_witness=wit))
        table.append((sk, len(A1), len(menu), T, That, fibers,
                      T == That, fib_ok))
    return dict(table=table, phantoms=phantoms, fib_viol=fib_viol,
                v3_viol=v3_viol)

def test_V5(row_N, row_Nm1):
    """Stabilization: certified chain keys and menus at N-1 must persist at
    N with fiber scale p^n on common chains; T/T-hat per stratum equal on
    strata fully certified at both levels. Code-level regression check
    (certified reads are N-independent by construction)."""
    p, n = row_N['p'], row_N['n']
    issues = []
    # chains certified at N-1 must appear at N with fiber ratio p^n
    for ch, cnt in row_Nm1['chains'].items():
        if ch[3][0] == 'deep':
            continue
        big = row_N['chains'].get(ch)
        if big is None:
            issues.append(('chain-lost-at-N', ch))
        elif big != cnt * p ** n:
            issues.append(('fiber-scale', ch, cnt, big, p ** n))
    for fkey, dd in row_Nm1['menus'].items():
        for d2 in dd:
            if d2 not in row_N['menus'].get(fkey, {}):
                issues.append(('menu-lost-at-N', fkey, d2))
    return issues
