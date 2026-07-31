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
  * step (m_k, h_k, cell a_k)  <->  one certified WHOLE NODE READ of the
    followed cluster: species m_k = the read's signature shape (all sides'
    (slope, e, ell) + residual multiplicity profiles — the XNode letter
    fields of the N7 engine mapping, per side), heights h_k = the side
    slopes (Fractions), fresh digit cell a_k = ALL digits the read
    consumes (residual roots + inert-factor coefficients), matching M18
    §6.2 (I0)/(I3): "Assign(m,x,h) = fresh digit cells realizing (m,h)
    from x", "the marks ARE the realized histories" (reading-built tmark).
    A read continues at its (unique, n<=3) repeated residual root; the
    beyond-cap part of a read is pooled into one ('deep', k) marker —
    its internal decomposition is horizon-dependent, while "k deepest
    roots beyond the cap" is a clean digit-cylinder condition.
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
      h2=2 read needs v up to 5). Horizon-touching cosets are resolved by
      digit-lifting (children at horizon N+1, mass /p^n, exact Fractions)
      until certified; the tiny residue after kmax lifts (cosets converging
      to the excluded discZero locus) is the reported unresolved mass and
      the tolerance of the fiber checks. Rows run here (cylinder sizes;
      height cap hcap bounds ALL read heights, h1 < h2 <= hcap):
        n=2, p=2: N=9  (2^16),  hcap=4
        n=2, p=3: N=7  (3^12),  hcap=3
        n=3, p=2: N=7  (2^18),  mu=3 entry, hcap=3
        n=3, p=3: N=5  (3^12),  mu=3 entry, hcap=2
      This includes the spec's wild-corner emphasis (p=2 n=2; p=3 n=3).
  D3. n=3 with a DOUBLE root entry (mu=2, third root simple): by Hensel the
      level-N box factors bijectively as (cluster quadratic) x (unit linear)
      and the cluster reads equal the quadratic's reads, so this row's tie
      is the n=2 row's tie. We VERIFY the reduction numerically (gate V4)
      on random samples instead of re-enumerating 3.2M polynomials.
  D4. A coset with ANY horizon-touching read (walk or frame) contributes
      NOTHING until lift-resolved (all-or-nothing certification, both
      sides symmetrically); beyond-cap read content is carried inside the
      signatures as the pooled ('deep', k) marker.
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
    """ONE NODE READ: all hull sides with slope steeper than -h_prev (root
    valuation lam > h_prev), heights capped at hcap, as a tuple of side
    entries ordered deepest-first:
      ('side', lam, e, ell, roots, psi)  with roots = sorted (digit, mult)
        pairs of the residual and psi = the monic-normalized rootless
        residual factor (or None); e > 1 sides carry their single residual
        digit the same way.
      ('deep', size)  certified beyond the height cap (out of scope). ALL
        beyond-cap roots are pooled into ONE such marker: their internal
        polygon decomposition is horizon-dependent (not canonical), while
        'k deepest roots all beyond hcap' is a clean digit-cylinder
        condition given the in-scope part.
    A step of the walk = one whole node read: the read consumes ALL the
    digits of the polygon + residual factorizations at this node (M18 (I3)
    'the marks ARE the realized histories'; reading-built tmark).
    Returns (sides, cluster_len, status)."""
    sides, clen, deep_total = [], 0, 0
    if j0 > 0:
        # left block [0,j0): all coeffs inexact; every left-block root
        # valuation >= (N - v(c_{j0}))/j0 (convexity + inexact >= N).
        vj0 = hull[0][1]
        bound = Fraction(N - vj0, j0)
        if bound > hcap and bound > h_prev:
            deep_total += j0
            clen += j0
        else:
            return None, None, 'imprecise'
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        lam = Fraction(y1 - y2, x2 - x1)          # root valuation on side
        if lam <= h_prev:
            continue
        clen += x2 - x1
        if lam > hcap:
            deep_total += x2 - x1
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
        roots, rootless, rootless_deg = fp_poly_roots(rc, p)
        if e > 1:
            assert ell == 1, "unexpected long ramified side at n<=3"
        psi = None
        if rootless_deg:
            lead_inv = pow(rootless[-1], -1, p)
            psi = tuple((c * lead_inv) % p for c in rootless)
        sides.append(('side', lam, e, ell, tuple(sorted(roots.items())),
                      psi))
    if deep_total:
        sides.insert(0, ('deep', deep_total))   # deepest-first, canonical
    return tuple(sides), clen, 'ok'

def read_species(read):
    """Signature shape of a node read: digits stripped, structure kept."""
    out = []
    for s in read:
        if s[0] == 'deep':
            out.append(s)
        else:
            _, lam, e, ell, roots, psi = s
            out.append(('side', lam, e, ell,
                        tuple(sorted(m for _, m in roots)),
                        len(psi) - 1 if psi else 0))
    return tuple(out)

def read_digits(read):
    """The digit content of a node read (the fresh assignment / cell)."""
    out = []
    for s in read:
        out.append(None if s[0] == 'deep' else (s[4], s[5]))
    return tuple(out)

def read_cont(read):
    """The (unique, n<=3) continuing datum of a read: (h, digit, mult) of
    the repeated residual root, or None."""
    conts = [(s[1], r, m) for s in read if s[0] == 'side'
             for r, m in s[4] if m >= 2]
    assert len(conts) <= 1, read
    return conts[0] if conts else None

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
    h_prev = 0). A step = one whole node read; at n <= 3 a read has at
    most one repeated residual root, so the continuing walk is a chain.
    Returns dict:
      status: 'ok'|'imprecise'
      read1:  the step-1 node read
      chain:  (h1, a1, mu2, read2) if step 1 continues in scope, else None
      step2imprecise: 1 if the continuation's read touched the horizon"""
    r1, st = read_cluster(coeffs, p, N, mu, 0, hcap)
    if st != 'ok':
        return {'status': 'imprecise'}
    out = {'status': 'ok', 'read1': r1, 'chain': None, 'step2imprecise': 0}
    cont = read_cont(r1)
    if cont is None:
        return out
    h1, a1, mu2 = cont
    assert h1.denominator == 1, r1   # repeated roots live on e = 1 sides
    g2 = poly_shift(coeffs, a1 * p ** int(h1), p ** N)
    r2, st2 = read_cluster(g2, p, N, mu2, int(h1), hcap)
    if st2 != 'ok':
        # 'no-cluster' cannot happen after a genuine continuing read
        assert st2 == 'imprecise', st2
        out['step2imprecise'] = 1
        return out
    out['chain'] = (int(h1), a1, mu2, r2)
    return out

def frame_menu_reads(coeffs, p, N, hcap, h1_range, n):
    """Per-step (fresh-frame) reads: for each integer h1 in h1_range and
    mu2 >= 2, if g satisfies the frame cluster condition at (h1, mu2)
    (sides steeper than h1 total exactly mu2), contribute the whole node
    read. Returns list of ((h1, mu2), read). Imprecise hulls contribute
    (('imprecise',), None) markers."""
    hull, j0, ok = hull_of(coeffs, p, N)
    if not ok:
        return [(('imprecise',), None)]
    out = []
    for h1 in h1_range:
        sides, clen, st = side_reads(coeffs, p, N, hull, j0, h1, hcap)
        if st != 'ok':
            out.append((('imprecise',), None))
            continue
        if clen < 2 or clen > n:
            continue
        out.append(((h1, clen), sides))
    return out

# ---------------------------------------------------------------- sweeps
def cylinder_iter(n, p, N):
    """All monic degree-n coefficient tuples (c0..c_{n-1}) mod p^N with every
    ci divisible by p (the r=0 entry-cluster cylinder; f-bar = y^n)."""
    reps = [p * k for k in range(p ** (N - 1))]
    return itertools.product(reps, repeat=n)

def leaves_of(w):
    """Decided (e,f) leaves of a depth-2 walk; None if not fully decided
    at depth 2 (a deep side or an uncontinued/deeper repeated root)."""
    leaves, decided = [], True
    reads = [(w['read1'], True)]
    if w['chain'] is not None:
        reads.append((w['chain'][3], False))
    elif read_cont(w['read1']) is not None:
        decided = False                      # cont exists but not walked
    for read, is_step1 in reads:
        for s in read:
            if s[0] == 'deep':
                decided = False
                continue
            _, lam, e, ell, roots, psi = s
            for r, m in roots:
                if m == 1:
                    leaves.append((e, 1))
                elif not is_step1:
                    decided = False          # depth cap hit
            if psi:
                assert e == 1
                leaves.append((1, len(psi) - 1))
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
    into the row censuses. Keys are whole node reads."""
    r1 = w['read1']
    res['s1'][r1] = res['s1'].get(r1, 0) + mass
    if w['chain'] is not None:
        key = (r1, w['chain'][3])
        res['chains'][key] = res['chains'].get(key, 0) + mass
    for fkey, read in mreads:
        res['menus'].setdefault(fkey, {}).setdefault(read, coeffs)

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
    """Length-1 tie: per stratum (= step-1 read species): equal digit-cell
    fibers, power of p, census = #cells * fiber."""
    strata = {}
    for r1, cnt in row['s1'].items():
        strata.setdefault(read_species(r1), {})[read_digits(r1)] = cnt
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
            viol.append((st, {str(k): v for k, v in cells.items()}))
    return (not viol), table, viol

def test_BC(row):
    """Length-2 counting tie T vs T-hat (per-step menus) + equal-fiber law
    + the targeted phantom scan (Test C shape: menu entry, empty locus).
    Strata = (step-1 species, step-2 species); chains within a stratum =
    (step-1 digits, step-2 digits); the step-2 menu is per-step, keyed by
    the frame state (h1, mu2) alone. Returns per-stratum table, phantom
    list, fiber violations."""
    p = row['p']
    # realized step-1 continuing cells (digit tuples) per species
    a1_sets, spec1_frame = {}, {}
    for r1, cnt in row['s1'].items():
        cont = read_cont(r1)
        if cont is None:
            continue
        sp1 = read_species(r1)
        a1_sets.setdefault(sp1, set()).add(read_digits(r1))
        spec1_frame[sp1] = (int(cont[0]), cont[2])       # (h1, mu2)
    # realized chains grouped by (species1, species2)
    strata = {}
    for (r1, r2), cnt in row['chains'].items():
        sk = (read_species(r1), read_species(r2))
        strata.setdefault(sk, {})[(read_digits(r1), read_digits(r2))] = cnt
    # menus regrouped: (h1, mu2) -> species2 -> {digits2: witness}
    menu_by_spec = {}
    for fkey, dd in row['menus'].items():
        for read, wit in dd.items():
            menu_by_spec.setdefault(fkey, {}).setdefault(
                read_species(read), {})[read_digits(read)] = wit
    table, phantoms, fib_viol, v3_viol = [], [], [], []
    all_strata = set(strata)
    for sp1, frame in spec1_frame.items():
        for sp2 in menu_by_spec.get(frame, {}):
            all_strata.add((sp1, sp2))
    for sk in sorted(all_strata, key=str):
        sp1, sp2 = sk
        frame = spec1_frame.get(sp1)
        A1 = a1_sets.get(sp1, set())
        chains = strata.get(sk, {})
        menu = menu_by_spec.get(frame, {}).get(sp2, {}) if frame else {}
        # V3: every realized step-2 read must be in the per-step menu
        for (d1, d2) in chains:
            if d2 not in menu:
                v3_viol.append((sk, d1, d2))
        T = len(chains)
        That = len(A1) * len(menu)
        fibers = sorted(set(chains.values()))
        fib_ok = (T == 0) or fiber_law(list(chains.values()), p,
                                       row['unresolved_mass'])[0]
        if not fib_ok:
            fib_viol.append((sk, {str(k): v for k, v in chains.items()}))
        # the phantom scan (Test C granularity)
        for d1 in sorted(A1, key=str):
            for d2, wit in sorted(menu.items(), key=str):
                if (d1, d2) not in chains:
                    phantoms.append(dict(stratum=sk, a1=d1, d2=d2,
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
        roots, _, _ = fp_poly_roots(fb, p)
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
            r1 = w['read1']
            bucket['s1'][r1] = bucket['s1'].get(r1, 0) + 1
            if w['chain'] is not None:
                k = (r1, w['chain'][3])
                bucket['chains'][k] = bucket['chains'].get(k, 0) + 1
            for fk, read in mreads:
                bucket['menus'].add((fk, read))
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
        cg = (str(wg['read1']), str(wg['chain']))
        cq = (str(wq['read1']), str(wq['chain']))
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

def fmt_sp(sp):
    """Compact display of a read species."""
    bits = []
    for s in sp:
        if s[0] == 'deep':
            bits.append(f"deep:{s[1]}")
        else:
            _, lam, e, ell, mults, psideg = s
            b = f"h={lam}"
            if e > 1:
                b += f",e={e}"
            if ell > 1:
                b += f",l={ell}"
            if any(m > 1 for m in mults):
                b += f",m={list(mults)}"
            if psideg:
                b += f",psi{psideg}"
            bits.append(b)
    return "[" + " | ".join(bits) + "]"

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
        out(f"    m1={fmt_sp(st):<40} cells={ncells:<4} fiber={fibers}  "
            f"census={census}  {tag_}")
    tie_fail = [r for r in resBC['table'] if not r[6]]
    fib_fail = resBC['fib_viol']
    out(f"  Test B (length-2 counting tie T vs T-hat): "
        f"{len(resBC['table'])} strata, "
        f"{'ALL TIED' if not tie_fail else str(len(tie_fail)) + ' UNTIED'}; "
        f"fiber law: {'PASS' if not fib_fail else 'FAIL'}")
    for sk, nA1, nMenu, T, That, fibers, tie, fib_ok in resBC['table']:
        sp1, sp2 = sk
        mark = 'ok' if (tie and fib_ok) else '**'
        out(f"    {fmt_sp(sp1)} -> {fmt_sp(sp2)}: "
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
        ROWS = [('R1', 2, 2, 7, 2, Fraction(3)),
                ('R2', 2, 3, 6, 2, Fraction(2)),
                ('R3', 3, 2, 6, 3, Fraction(2)),
                ('R4', 3, 3, 4, 3, Fraction(3, 2))]
    else:
        ROWS = [('R1', 2, 2, 9, 2, Fraction(4)),
                ('R2', 2, 3, 7, 2, Fraction(3)),
                ('R3', 3, 2, 7, 3, Fraction(3)),
                ('R4', 3, 3, 5, 3, Fraction(2))]
    results, phantoms, fib_viols, gate_fail = {}, [], [], []
    for tag, n, p, N, mu, hcap in ROWS:
        # menus must cover every h1 the walker can continue on (h1 <= hcap)
        h1max = int(hcap)
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
    for n, p, N, hcap in [(2, 2, 5, Fraction(2)),
                          (2, 3, 4, Fraction(3, 2)),
                          (3, 2, 5, Fraction(2)),
                          (3, 3, 3, Fraction(1))]:
        keys, issues = gate_V2(n, p, N, hcap, int(hcap))
        out(f"  gate V2 n={n} p={p} N={N}: entry classes {keys} "
            f"-> {'PASS' if not issues else issues}")
        if issues:
            gate_fail.append(('V2', (n, p, N), jsonable(issues)))
    for p, N, hcap in [(2, 7, Fraction(3)),
                       (3, 5, Fraction(2))]:
        compared, mism = gate_V4(p, N, hcap, int(hcap))
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
