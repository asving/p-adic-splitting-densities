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
    """Roots with multiplicity of a poly over F_p given low->high coeffs.
    Returns (root->mult, rootless quotient factor coeffs, its degree).
    Trial division; p<=3, deg<=3 in this probe."""
    work = [c % p for c in coeffs]
    roots = {}
    for r in range(p):
        m = 0
        while len(work) > 1:
            val = 0
            for c in reversed(work):
                val = (val * r + c) % p
            if val != 0:
                break
            out = []           # synthetic division by (x - r)
            acc = 0
            for c in reversed(work):
                acc = (acc * r + c) % p
                out.append(acc)
            work = out[:-1][::-1]
            m += 1
        if m:
            roots[r] = m
    return roots, work, len(work) - 1

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
        # species carries the branch's OWN side profile ell (residual
        # degree): one-side vs split-polygon configurations are different
        # reads (XNode letter fields (e, ell, h) in the N7 engine mapping)
        roots, rootless, rootless_deg = fp_poly_roots(rc, p)
        for r, m in sorted(roots.items()):
            if m == 1:
                branches.append(('splitleaf', lam, ell, r))
            else:
                branches.append(('cont', lam, ell, r, m))
        if rootless_deg:
            # rootless quotient: deg 2/3 with no roots over F_p (p<=3
            # keeps it a single irreducible here); monic-normalized
            lead_inv = pow(rootless[-1], -1, p)
            psi = tuple((c * lead_inv) % p for c in rootless)
            branches.append(('inert', lam, ell, rootless_deg, psi))
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
        _, h1, _ell1, a1, mu2 = b
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
    """Length-1 stratum key (species incl. own side profile, height)."""
    kind = b[0]
    if kind == 'cont':
        return ('cont', b[1], (b[2], b[4]))     # (h1, (ell, mu_next))
    if kind == 'ram':
        return ('ram', b[1], b[2])              # (h, e)
    if kind == 'inert':
        return ('inert', b[1], (b[2], b[3]))    # (h, (ell, deg))
    if kind == 'splitleaf':
        return ('splitleaf', b[1], b[2])        # (h, ell)
    return ('deep', None, None)

def s1_cell(b):
    """Cell datum of a step-1 branch (the read-off digits)."""
    kind = b[0]
    if kind == 'cont':
        return b[3]
    if kind == 'ram':
        return b[3]
    if kind == 'splitleaf':
        return b[3]
    if kind == 'inert':
        return b[4]
    return None

def leaves_of(w):
    """Decided (e,f) leaves of a depth-2 walk; None if walk not fully
    decided at depth 2 (a continuing or deep branch remains)."""
    leaves, decided = [], True
    for b in list(w['step1']) + [ch[3] for ch in w['chains']]:
        if b[0] == 'splitleaf':
            leaves.append((1, 1))
        elif b[0] == 'inert':
            leaves.append((1, b[3]))
        elif b[0] == 'ram':
            leaves.append((b[2], 1))
        elif b[0] in ('deep', 'cont'):
            decided = False
    return tuple(sorted(leaves)) if decided else None

def probe_one(coeffs, n, p, N, mu_entry, hcap, h1max):
    """Walk + per-step menu reads for one coefficient tuple at horizon N.
    Returns (certified?, walk, menu_reads). certified=False means some read
    (entry, step-2, or frame) touched the horizon: the coset must be
    resolved by lifting before ANY of its data is counted."""
    w = walk_depth2(list(coeffs), p, N, mu_entry, hcap)
    if w['status'] != 'ok':
        return False, None, None
    if w['step2imprecise'] > 0:
        return False, None, None
    mreads = frame_menu_reads(list(coeffs), p, N, hcap,
                              range(1, h1max + 1), n)
    if any(fk == ('imprecise',) for fk, _ in mreads):
        return False, None, None
    return True, w, mreads

def commit(res, coeffs, w, mreads, mass):
    """Add one certified coset's data (with Haar mass in level-N-box units)
    into the row censuses."""
    for b in w['step1']:
        key = (s1_stratum(b), s1_cell(b))
        res['s1'][key] = res['s1'].get(key, 0) + mass
    for ch in w['chains']:
        res['chains'][ch] = res['chains'].get(ch, 0) + mass
    for fkey, d2 in mreads:
        if d2[0] == 'deep':
            continue
        res['menus'].setdefault(fkey, {}).setdefault(d2, coeffs)

def run_row(n, p, N, mu_entry, hcap, h1max, sample_cap=400, seed=0,
            kmax=None):
    if kmax is None:
        # by horizon N + kmax every in-scope read certifies except cosets
        # converging to discZero (their residual mass is the tolerance)
        kmax = int((n + 1) * hcap) + 3
    """One exhaustive cylinder sweep with lift-resolution of horizon-
    touching cosets (masses in level-N-box units; exact Fractions)."""
    rng = random.Random(seed)
    res = dict(n=n, p=p, N=N, mu=mu_entry, hcap=hcap, h1max=h1max,
               total=0, s1={}, chains={}, menus={}, pending0=0,
               unresolved_mass=Fraction(0), samples=[])
    pending = []
    for coeffs in cylinder_iter(n, p, N):
        res['total'] += 1
        cert, w, mreads = probe_one(coeffs, n, p, N, mu_entry, hcap, h1max)
        if not cert:
            pending.append(coeffs)
            continue
        commit(res, coeffs, w, mreads, 1)
        if len(res['samples']) < sample_cap and rng.random() < 0.02:
            lv = leaves_of(w)
            if lv:
                res['samples'].append((coeffs, lv))
    res['pending0'] = len(pending)
    # lift-resolution: a coset unreadable at horizon N is replaced by its
    # p^n children at horizon N+1 (mass /p^n), until certified or kmax.
    level, mass = 0, Fraction(1)
    while pending and level < kmax:
        level += 1
        mass = Fraction(1, p ** (n * level))
        Nk = N + level
        nxt = []
        for coeffs in pending:
            for digs in itertools.product(range(p), repeat=n):
                child = tuple(c + d * p ** (Nk - 1)
                              for c, d in zip(coeffs, digs))
                cert, w, mreads = probe_one(child, n, p, Nk, mu_entry,
                                            hcap, h1max)
                if cert:
                    commit(res, child, w, mreads, mass)
                else:
                    nxt.append(child)
        pending = nxt
    res['unresolved_mass'] = len(pending) * mass if pending else Fraction(0)
    res['unresolved'] = len(pending)
    return res

# ----------------------------------------------------------------- tests
def is_ppow(x, p):
    if isinstance(x, Fraction):
        if x.denominator != 1:
            return False
        x = x.numerator
    if x < 1:
        return False
    while x % p == 0:
        x //= p
    return x == 1

def fiber_law(fibers, p, tol):
    """Equal-fiber check up to the unresolved-mass tolerance: the true
    common fiber F* is the smallest p-power >= max(fibers); each observed
    fiber may be short by at most tol (mass hiding in unresolved cosets).
    Returns (ok, F*, used_tol?)."""
    mx = max(fibers)
    Fs = 1
    while Fs < mx:
        Fs *= p
    if Fs - mx > tol:
        return False, Fs, True
    exact = (len(set(fibers)) == 1 and mx == Fs)
    if exact:
        return True, Fs, False
    return all(Fs - f <= tol for f in fibers), Fs, True

def test_A(row):
    """Length-1 tie: per stratum (m1,h1): equal cell fibers, power of p,
    census = #cells * fiber. Returns (ok, table, violations)."""
    strata = {}
    for (st, cell), cnt in row['s1'].items():
        if st[0] == 'deep':
            continue
        strata.setdefault(st, {})[cell] = cnt
    tol = row['unresolved_mass']
    table, viol = [], []
    for st in sorted(strata, key=str):
        cells = strata[st]
        fibers = sorted(set(cells.values()))
        ok, Fs, used_tol = fiber_law(list(cells.values()), row['p'], tol)
        census = sum(cells.values())
        table.append((st, len(cells), fibers if not ok else Fs, census,
                      ok, used_tol))
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
    # extra2 = the step-2 species' own side profile (mirrors s1_stratum)
    def s2_key(h1, mu2, d2):
        kind = d2[0]
        if kind == 'cont':
            extra = (d2[2], d2[4])
        elif kind == 'inert':
            extra = (d2[2], d2[3])
        elif kind == 'ram':
            extra = d2[2]
        else:
            extra = d2[2] if kind == 'splitleaf' else None
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
        fib_ok = (T == 0) or fiber_law(list(chains.values()), p,
                                       row['unresolved_mass'])[0]
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

# ------------------------------------------------------- validation gates
def gate_V1(row):
    """PARI factorpadic oracle tie on the row's fully-decided samples:
    walker (e,f) leaf multiset == oracle (e,f) multiset. Returns
    (checked, mismatches)."""
    import cypari2
    pari = cypari2.Pari()
    pari.allocatemem(1 << 27, silent=True)
    n, p = row['n'], row['p']
    mism, checked = [], 0
    for coeffs, leaves in row['samples']:
        terms = [f"({c})*x^{i}" for i, c in enumerate(coeffs)] + [f"x^{n}"]
        pol = pari(" + ".join(terms))
        disc = pari.poldisc(pol)
        if disc == 0:
            continue
        vd = int(pari.valuation(disc, p))
        fac = pari.factorpadic(pol, p, 2 * vd + 10 + row['N'])
        oracle = []
        nfac = len(fac[0])
        for i in range(nfac):
            F = pari.liftall(fac[0][i])
            assert int(fac[1][i]) == 1, "inseparable factor"
            d = int(pari.poldegree(F))
            if d == 1:
                oracle.append((1, 1))
                continue
            # exact (e,f): number field of the lifted factor, maximal
            # order at p, prime decomposition (quartic_oracle.py idiom;
            # Krasner: at this precision the lift generates the same
            # Q_p-field, so a single prime lies above p)
            K = pari.nfinit([F, [p]])
            dec = pari.idealprimedec(K, p)
            assert len(dec) == 1, (coeffs, str(F))
            e, f = int(dec[0][2]), int(dec[0][3])
            assert e * f == d, (coeffs, e, f, d)
            oracle.append((e, f))
        checked += 1
        if tuple(sorted(oracle)) != leaves:
            mism.append((coeffs, leaves, tuple(sorted(oracle))))
    return checked, mism

def gate_V2(n, p, N, hcap, h1max):
    """Translation invariance / cylinder faithfulness on a tiny FULL monic
    box: per entry residue r (repeated root of f-bar), the recentered
    censuses must agree across r, and the r=0 census must equal the
    cylinder sweep's. Compares raw certified data + pending counts."""
    per_r = {}
    for coeffs in itertools.product(range(p ** N), repeat=n):
        fb = [c % p for c in coeffs] + [1]
        roots, _ = fp_poly_roots(fb, p)
        for r, mu in roots.items():
            if mu < 2:
                continue
            g = poly_shift(list(coeffs), r, p ** N)
            cert, w, mreads = probe_one(tuple(g), n, p, N, mu, hcap, h1max)
            bucket = per_r.setdefault((mu, r), dict(s1={}, chains={},
                                                    menus=set(), pend=0))
            if not cert:
                bucket['pend'] += 1
                continue
            for b in w['step1']:
                k = (s1_stratum(b), s1_cell(b))
                bucket['s1'][k] = bucket['s1'].get(k, 0) + 1
            for ch in w['chains']:
                bucket['chains'][ch] = bucket['chains'].get(ch, 0) + 1
            for fk, d2 in mreads:
                if d2[0] != 'deep':
                    bucket['menus'].add((fk, d2))
    issues = []
    mus = sorted({mu for mu, _ in per_r})
    for mu in mus:
        buckets = [per_r[(m, r)] for (m, r) in sorted(per_r) if m == mu]
        b0 = buckets[0]
        for b in buckets[1:]:
            if (b['s1'], b['chains'], b['menus'], b['pend']) != \
               (b0['s1'], b0['chains'], b0['menus'], b0['pend']):
                issues.append(('r-variance', mu))
        if mu == n and (mu, 0) in per_r:
            # r=0, full-cluster entries = the cylinder sweep (no lifting;
            # compare certified data + pending count)
            res = dict(n=n, p=p, N=N, s1={}, chains={}, menus={})
            pend = 0
            for coeffs in cylinder_iter(n, p, N):
                cert, w, mreads = probe_one(coeffs, n, p, N, mu,
                                            hcap, h1max)
                if not cert:
                    pend += 1
                    continue
                commit(res, coeffs, w, mreads, 1)
            cyl_menus = {(fk, d2) for fk, dd in res['menus'].items()
                         for d2 in dd}
            b0 = per_r[(mu, 0)]
            if (b0['s1'], b0['chains'], b0['menus'], b0['pend']) != \
               (res['s1'], res['chains'], cyl_menus, pend):
                issues.append(('cylinder-mismatch', mu))
    return sorted(per_r), issues

def gate_V4(p, N, hcap, h1max, trials=400, seed=1):
    """Hensel mu=2 reduction for n=3 (deviation D3): the cluster walk of
    g = (y^2+sy+t)(y-w), w a unit, equals the n=2 walk of y^2+sy+t
    (branch datums are unit-scaling invariant). Compared when both certify
    at horizon N."""
    rng = random.Random(seed)
    pN = p ** N
    mism, compared = [], 0
    for _ in range(trials):
        s = p * rng.randrange(p ** (N - 1))
        t = p * rng.randrange(p ** (N - 1))
        w = rng.randrange(1, pN)
        while w % p == 0:
            w = rng.randrange(1, pN)
        g = ((-t * w) % pN, (t - s * w) % pN, (s - w) % pN)
        cert_g, wg, mg = probe_one(g, 3, p, N, 2, hcap, h1max)
        cert_q, wq, mq = probe_one((t, s), 2, p, N, 2, hcap, h1max)
        if not (cert_g and cert_q):
            continue
        compared += 1
        cg = (sorted(map(str, wg['step1'])), sorted(map(str, wg['chains'])))
        cq = (sorted(map(str, wq['step1'])), sorted(map(str, wq['chains'])))
        if cg != cq:
            mism.append(((s, t, w), cq, cg))
    return compared, mism

# ------------------------------------------------------------ report/main
def jsonable(x):
    if isinstance(x, dict):
        return {str(k): jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple, set)):
        return [jsonable(v) for v in sorted(x, key=str)] \
            if isinstance(x, set) else [jsonable(v) for v in x]
    if isinstance(x, Fraction):
        return str(x)
    return x

def report_row(tag, row, resA, resBC, v5_issues, out):
    p, n = row['p'], row['n']
    out(f"\n===== ROW {tag}: n={n} p={p} N={row['N']} mu={row['mu']} "
        f"hcap={row['hcap']} h1max={row['h1max']} =====")
    out(f"  cylinder size p^(n(N-1)) = {row['total']}; "
        f"horizon-pending at N: {row['pending0']} "
        f"(unresolved after lifting: {row['unresolved']}, "
        f"mass {row['unresolved_mass']} level-N boxes)")
    okA, tableA, violA = resA
    out(f"  Test A (length-1 tie): {'PASS' if okA else 'FAIL'} "
        f"({len(tableA)} strata)")
    for st, ncells, fibers, census, ok, used_tol in tableA:
        tag_ = 'ok' if ok else 'VIOLATION'
        if ok and used_tol:
            tag_ = 'ok (within unresolved tolerance)'
        out(f"    m1={st[0]:<9} h1={str(st[1]):<4} x={st[2]}  "
            f"cells={ncells:<3} fiber={fibers}  census={census}  {tag_}")
    tie_fail = [r for r in resBC['table'] if not r[6]]
    fib_fail = resBC['fib_viol']
    out(f"  Test B (length-2 counting tie T vs T-hat): "
        f"{len(resBC['table'])} strata, "
        f"{'ALL TIED' if not tie_fail else str(len(tie_fail)) + ' UNTIED'}; "
        f"fiber law: {'PASS' if not fib_fail else 'FAIL'}")
    for sk, nA1, nMenu, T, That, fibers, tie, fib_ok in resBC['table']:
        h1, mu2, kind, h2, extra = sk
        mark = 'ok' if (tie and fib_ok) else '**'
        out(f"    (h1={h1},mu2={mu2})->({kind},h2={h2},x={extra}): "
            f"|A1|={nA1} |menu|={nMenu}  T={T} T-hat={That} "
            f"fiber={fibers[0] if len(fibers) == 1 else fibers}  {mark}")
    out(f"  Test C (phantom scan): {len(resBC['phantoms'])} phantom(s)")
    for ph in resBC['phantoms']:
        out(f"    PHANTOM: stratum={ph['stratum']} a1={ph['a1']} "
            f"d2={ph['d2']} menu-witness={ph['menu_witness']}")
    if resBC['v3_viol']:
        out(f"  V3 VIOLATION (realized read outside per-step menu): "
            f"{resBC['v3_viol'][:5]}")
    out(f"  V5 stabilization vs N-1: "
        f"{'PASS' if not v5_issues else f'{len(v5_issues)} ISSUE(S)'}")
    for iss in v5_issues[:8]:
        out(f"    V5: {iss}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--quick', action='store_true')
    args = ap.parse_args()
    here = os.path.dirname(os.path.abspath(__file__))
    os.makedirs(os.path.join(here, 'results'), exist_ok=True)
    lines = []

    def out(s):
        print(s, flush=True)
        lines.append(s)

    out(f"U6_krun_probe — K-RUN depth-2 no-phantom falsifier "
        f"(IFK-U6-FIRST, V4 item 22).  {time.strftime('%F %T')}")
    out("Claim: length-2 counting tie T = T-hat; any T < T-hat stratum "
        "(phantom chain) negates K-RUN as drafted.")
    if args.quick:
        ROWS = [('R1', 2, 2, 7, 2, Fraction(3), 2),
                ('R2', 2, 3, 6, 2, Fraction(2), 1),
                ('R3', 3, 2, 6, 3, Fraction(2), 1),
                ('R4', 3, 3, 4, 3, Fraction(3, 2), 1)]
    else:
        ROWS = [('R1', 2, 2, 9, 2, Fraction(4), 3),
                ('R2', 2, 3, 7, 2, Fraction(3), 2),
                ('R3', 3, 2, 7, 3, Fraction(3), 2),
                ('R4', 3, 3, 5, 3, Fraction(2), 1)]
    results, phantoms, fib_viols, gate_fail = {}, [], [], []
    for tag, n, p, N, mu, hcap, h1max in ROWS:
        t0 = time.time()
        row = run_row(n, p, N, mu, hcap, h1max)
        rowm1 = run_row(n, p, N - 1, mu, hcap, h1max)
        resA = test_A(row)
        resBC = test_BC(row)
        v5 = test_V5(row, rowm1)
        report_row(tag, row, resA, resBC, v5, out)
        out(f"  [{time.time()-t0:.1f}s]")
        for ph in resBC['phantoms']:
            confirmed = (row['unresolved'] == 0)
            phantoms.append((tag, ph, confirmed))
        fib_viols += [(tag, v) for v in resBC['fib_viol']]
        if not resA[0]:
            fib_viols += [(tag, ('testA', v)) for v in resA[2]]
        if resBC['v3_viol'] or v5:
            gate_fail.append((tag, 'V3' if resBC['v3_viol'] else 'V5',
                              (resBC['v3_viol'] + v5)[:5]))
        results[tag] = dict(
            params=dict(n=n, p=p, N=N, mu=mu, hcap=str(hcap),
                        h1max=h1max),
            coverage=dict(total=row['total'], pending0=row['pending0'],
                          unresolved=row['unresolved'],
                          unresolved_mass=str(row['unresolved_mass'])),
            testA=dict(ok=resA[0], strata=jsonable(resA[1]),
                       violations=jsonable(resA[2])),
            testB=dict(table=jsonable(resBC['table']),
                       fib_viol=jsonable(resBC['fib_viol']),
                       v3_viol=jsonable(resBC['v3_viol'])),
            testC=dict(phantoms=jsonable(resBC['phantoms'])),
            v5=jsonable(v5))
        # gate V1 per row (oracle tie)
        try:
            checked, mism = gate_V1(row)
            out(f"  gate V1 (PARI factorpadic tie): {checked} samples, "
                f"{len(mism)} mismatch(es)")
            if mism:
                gate_fail.append((tag, 'V1', jsonable(mism[:3])))
                for m in mism[:3]:
                    out(f"    V1 MISMATCH: {m}")
            results[tag]['gateV1'] = dict(checked=checked,
                                          mism=jsonable(mism))
        except Exception as e:
            out(f"  gate V1 SKIPPED (oracle unavailable: {e!r})")
            results[tag]['gateV1'] = dict(skipped=repr(e))
    # gate V2: tiny full boxes, translation invariance / cylinder tie
    out("\n===== GATES (global) =====")
    for n, p, N, hcap, h1max in [(2, 2, 5, Fraction(2), 1),
                                 (2, 3, 4, Fraction(3, 2), 1),
                                 (3, 2, 5, Fraction(2), 1),
                                 (3, 3, 3, Fraction(1), 1)]:
        keys, issues = gate_V2(n, p, N, hcap, h1max)
        out(f"  gate V2 n={n} p={p} N={N}: entry classes {keys} "
            f"-> {'PASS' if not issues else issues}")
        if issues:
            gate_fail.append(('V2', (n, p, N), jsonable(issues)))
    for p, N, hcap, h1max in [(2, 7, Fraction(3), 2),
                              (3, 5, Fraction(2), 1)]:
        compared, mism = gate_V4(p, N, hcap, h1max)
        out(f"  gate V4 (Hensel mu=2-in-n=3 reduction) p={p}: "
            f"{compared} compared, {len(mism)} mismatch(es)")
        if mism:
            gate_fail.append(('V4', p, jsonable(mism[:3])))
    # ------------------------------------------------------------ verdict
    out("\n===== VERDICT =====")
    confirmed = [x for x in phantoms if x[2]]
    candidates = [x for x in phantoms if not x[2]]
    if confirmed:
        verdict = 'FIRES'
        out("FIRES — phantom chain(s) found: K-RUN's no-phantom face is "
            "FALSE at depth 2 as drafted. Witnesses:")
        for tag, ph, _ in confirmed:
            out(f"  {tag}: {jsonable(ph)}")
    elif candidates or fib_viols:
        verdict = 'FIRES-CANDIDATE' if candidates else 'FIRES-FIBER'
        out(f"ANOMALY — candidates={jsonable(candidates)} "
            f"fiber-violations={jsonable(fib_viols)} (see log)")
    elif gate_fail:
        verdict = 'UNTESTABLE'
        out(f"UNTESTABLE — validation gate failure(s): {gate_fail}")
    else:
        verdict = 'SURVIVES'
        out("SURVIVES — no phantom and no fiber-law violation on any "
            "probed stratum; every per-step-counted length-2 chain is "
            "realized, with exact equal fibers (all gates green).")
    tot_strata = sum(len(r['testB']['table']) for r in results.values())
    tot_chains = sum(sum(x[3] for x in r['testB']['table'])
                     for r in results.values())
    out(f"Coverage: {tot_strata} length-2 strata, {tot_chains} realized "
        f"chains, 4 exhaustive rows (+2 reduction rows via gate V4).")
    payload = dict(unit='IFK-U6-FIRST', date=time.strftime('%F %T'),
                   verdict=verdict, rows=results,
                   gate_failures=jsonable(gate_fail),
                   phantoms=jsonable(phantoms))
    jpath = os.path.join(here, 'results', 'U6_krun_results.json')
    with open(jpath, 'w') as f:
        json.dump(payload, f, indent=1)
    out(f"JSON: {jpath}")
    return 0 if verdict in ('SURVIVES', 'FIRES') else 2

if __name__ == '__main__':
    sys.exit(main())
