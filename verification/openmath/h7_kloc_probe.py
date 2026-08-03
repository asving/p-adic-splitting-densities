#!/usr/bin/env python3
"""N-H7-1 — the (H7) (I-tau)/K-LOC numerics probe: REAL m >= 2 decision points.

Charter: lean/notes/openmath/H7PROBE_2026-08-08.md P-4 (near-term (H7) decision
point) + lean/blueprints/HDISCHARGE_H7.md section 5 (N-H7-1 spec) and sections
1.1 (K-LOC (i)/(ii)/(iii')) / 2.1 (IT-1/IT-2 product identity).

Pure Python, exact integers, no dependencies.  Numerics are FALSIFIERS, never
proofs: GREEN = faces survive first contact; RED = a measured countermodel
shape (site, face, clause) = the restatement pin.

================================ SEALED PREDICTIONS ============================
(Sealed before first run.  Battery: 6 sites, all with genuine m >= 2 rosters.)

Sites (f0 = 1 unless noted; tau = rho + 1; frames per branch displayed):
  S1  p=5 n=4  f1=x^2-2x+6, f2=x^2-4x+9   rho=0 tau=1  es=(0,0,0,0)
      residue-separated (z=1 / z=2 double roots), both branches RAM (e=2).
  S2  p=2 n=4  f1=x^2+2,   f2=x^2+2x+2    rho=3 tau=4  es=(0,0,1,2)
      the blueprint-named wild pair; order-2 separation; frames Phi_j = f_j.
  S3  p=3 n=3  x-1, x-4, x-7              rho=3 tau=4  es=(0,1,2)
      m=3 HEN roster, depth-1 residual separation at shared residue root 1.
  S3b p=3 n=5  S3 roster + f0 = x^2+1     rho=3 (f0 cross-resultants all units)
      the genuine-f0/C0 face; roster reads must ignore f0's free digits.
  S5  p=3 n=4  f1=x^2+3,   f2=x^2+3x+3    rho=3 tau=4  es=(0,0,1,2)
      wild pair at p=3: NONTRIVIAL unit scalar u_2 = 2 (F_3^x).
  S6  p=3 n=3  f1=x-3,     f2=x^2-3       rho=1 tau=2  es=(0,0,1)
      SIDE-separation site (slope 1 vs 1/2) = the KL-1b face; mixed degrees.

P-A (K-JAC within-cell constancy): v_p(det Phi(g-tuple)) = rho at EVERY
    sampled polydisc member, every site.
P-B (K-LOC (i), lambda-side translation): per branch j, the branch-side data
    of F in the t_j frame = the side data of g_j translated by a CONSTANT
    delta_j over the whole cell; sealed values (doubled-valuation units for
    RAM frames, plain v_p for HEN frames):
      S1: delta=(0,0) both branches         S2: delta_w = 3 both branches
      S3: delta = 2 all three branches      S3b: delta = 2 all roster branches
      S5: delta_w = 3 both branches         S6: HEN delta = 1; RAM delta_w = 1
P-C (K-LOC (ii), unit-scalar transport): residual units of F's branch side =
    u_j * (units of g_j's side), u_j constant over the cell; sealed:
      S1: u=1,1   S2: u=1,1   S3: u=2,2,2   S3b: u=2,2,2 (f0(r_j) units:
      f0(1)=2,f0(4)=17,f0(7)=50 -> unit digits 2,2,2 mod 3 => u_j = 2*2 = 4
      = 1 mod 3 ... SEALED u_j = unit(prod_{i!=j}(r_j-r_i) * f0(r_j)) mod 3
      = 2*u_f0 where u_f0 = unit digit of f0(r_j): u_1=unit(2)=2 -> u=2*2=4=1;
      u_2=unit(17)=2 -> 1; u_3=unit(50)=2 -> 1.  SEALED S3b u=(1,1,1).)
      S5: u_1=1, u_2=2   S6: HEN u=2; RAM u=1
P-D (K-LOC (iii') core, event pullback): each branch read word W_j(F)
    (computed from F alone in the t_j frame, depth-1/2 slots displayed per
    site in SITES below) is (d1) COFACTOR-INDEPENDENT: constant on the set of
    members sharing g_j exactly (incl. f0 variation at S3b); (d2) the pairing
    (factor word w_j(g_j), F word W_j(F)) is a BIJECTION on attained values
    (reads equal up to cell-constant renormalization); (d3) measured minimal
    K with W_j factoring through g_j mod p^K satisfies K <= tau + rho + 1.
    DISPLAYED BOUNDARY (INFO, not a face): at S1 the raw depth-2 B0 digit is
    NOT an order-1 OM read (needs order-2 refinement) and is EXPECTED to leak
    cofactor dependence; measured and reported as INFO only.
P-E ((I-tau) product identity, IT-1/IT-2): at level N_scan, with survivors :=
    {F monic : F = prod f_j mod p^tau} (direct parametrization):
    (e1) image mu_N(polydisc) subset of survivors and extraction (constructive
         Lemma A: Newton-Cramer from the pinned base) ACCEPTS every image
         member with round-trip factors in the pins;
    (e2) extraction REJECTS every non-image survivor (acceptance is
         certificate-checked; any accept of a non-image F is impossible,
         any reject of an image F = extractor false-negative, reported);
    (e3) counts: #image * p^{sM} = prod_j #C_j (* #C0 at S3b), with
         sM = sum_i min(e_i, N_scan - tau); sealed per site:
         S1 N=2: survivors 625, image 625 (all), fibers 1.
         S2 N=5: survivors 16,  image 4;  N=6: survivors 256, image 32.
         S3 N=6: survivors 729, image 27.
         S3b N=6: #image * 3^{sM} = 3^10 (sM measured from 5x5 Smith,
                  sealed sum e_i = rho = 3).
         S6 N=4: survivors 729, image 243.
P-F (IT-4b probe, route B's open kernel — falsifier before proof): at S2
    (N=8, full 65536-tuple enumeration, 16 sub-cells pinned at level tau'=4
    digits... precisely: sub-cell = joint class of all four beta-digits at
    level 4) and S3 (N=8, full enumeration, 27 sub-cells = root digit at
    level 4): (f1) within each sub-cell the tuple-counts over attained joint
    depth-2 words are CONSTANT; (f2) the attained word alphabet is identical
    across sub-cells.  Expected GREEN with full alphabets (S2: 16 words x 256
    tuples per sub-cell; S3: 27 words x 27... S3 sub-cell size 3^{12-3-... }
    derived in-run); a RED here pins the IT-4b restatement, it does NOT
    refute section 1.1.
P-G (route-B mini, H7-C1a/C1b arithmetic): (g1) sub-cell uniformity with
    common alphabet aggregates to full-cell uniformity (C1a instance);
    (g2) the (SIB) identity N(joint word)*N(cell)^{m-1} = prod_j N(marginal)
    holds for every attained joint word on the full-cell table (C1b shape,
    tuple counts; fibers are constant by P-A/O-10 T1 so F-counts scale).

Ancillary battery-integrity checks (harness self-checks, not (H7) faces):
computed rho == sealed rho; computed Smith == sealed es; guard/headroom
arithmetic.  A mismatch there is a HARNESS derivation bug, displayed as such.
===============================================================================
"""
import itertools, json, random, sys, time

random.seed(20260808)

OUTDIR = "/data/users/asvin/math-and-lean/p-adic-splitting-densities/verification/openmath"

# ------------------------- exact poly / matrix helpers -----------------------

def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return tuple(r)

def polymul_many(fs):
    r = (1,)
    for f in fs:
        r = polymul(r, f)
    return r

def polmod_q(f, q):
    return tuple(c % q for c in f)

def polsub(a, b):
    n = max(len(a), len(b))
    aa = list(a) + [0] * (n - len(a))
    bb = list(b) + [0] * (n - len(b))
    return tuple(aa[i] - bb[i] for i in range(n))

def poleval(f, x):
    r = 0
    for c in reversed(f):
        r = r * x + c
    return r

def polderiv(f):
    return tuple(i * c for i, c in enumerate(f))[1:] if len(f) > 1 else (0,)

def vp(x, p):
    if x == 0:
        return None
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

def digit(x, level, p, K=64):
    return (x % p ** K) // p ** level % p

def unit_digit(x, p):
    v = vp(x, p)
    if v is None:
        return None
    return digit(x, v, p)

def det_bareiss(mat):
    m = [list(r) for r in mat]
    n = len(m)
    if n == 0:
        return 1
    sign, prev = 1, 1
    for k in range(n - 1):
        if m[k][k] == 0:
            for r in range(k + 1, n):
                if m[r][k] != 0:
                    m[k], m[r] = m[r], m[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                m[i][j] = (m[i][j] * m[k][k] - m[i][k] * m[k][j]) // prev
        prev = m[k][k]
    return sign * m[n - 1][n - 1]

def resultant(f, g):
    df, dg = len(f) - 1, len(g) - 1
    n = df + dg
    rows = []
    for i in range(dg):
        row = [0] * n
        for j, c in enumerate(f):
            row[i + j] = c
        rows.append(row)
    for i in range(df):
        row = [0] * n
        for j, c in enumerate(g):
            row[i + j] = c
        rows.append(row)
    return det_bareiss(rows)

def phi_matrix(fs):
    """Sylvester-block Jacobian of (g_j) |-> prod g_j at the tuple fs."""
    m = len(fs)
    degs = [len(f) - 1 for f in fs]
    n = sum(degs)
    cols = []
    for j in range(m):
        Fj = polymul_many([fs[i] for i in range(m) if i != j])
        for t in range(degs[j]):
            col = [0] * n
            for k, c in enumerate(Fj):
                if t + k < n:
                    col[t + k] = c
                # t+k == n only for the leading 1*x^n term, absent: deg Fj = n-d_j,
                # t <= d_j - 1 => t + deg Fj <= n - 1.  (assert below)
            assert t + len(Fj) - 1 <= n - 1
            cols.append(col)
    return [[cols[c][r] for c in range(n)] for r in range(n)]

def smith_profile(mat, p, cap=60):
    n = len(mat)
    dks = []
    for k in range(1, n + 1):
        best = None
        for rows in itertools.combinations(range(n), k):
            for colsel in itertools.combinations(range(n), k):
                sub = [[mat[r][c] for c in colsel] for r in rows]
                v = vp(det_bareiss(sub), p)
                if v is not None and (best is None or v < best):
                    best = v
                    if best == 0:
                        break
            if best == 0:
                break
        dks.append(best if best is not None else cap)
    es = [dks[0]] + [dks[k] - dks[k - 1] for k in range(1, n)]
    return tuple(sorted(es))

def poldivmod_monic(f, g):
    """f = q*g + r with g MONIC; exact integer arithmetic."""
    f = list(f)
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while len(f) - 1 >= dg and any(f):
        d = len(f) - 1
        if f[-1] == 0:
            f.pop()
            continue
        c = f[-1]
        q[d - dg] += c
        for i, gc in enumerate(g):
            f[d - dg + i] -= c * gc
        f.pop()
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return tuple(q), tuple(f)

def phidev(f, Phi):
    """Phi-adic development: f = sum B_k Phi^k, deg B_k < deg Phi."""
    Bs = []
    cur = tuple(f)
    while any(cur):
        cur, r = poldivmod_monic(cur, Phi)
        Bs.append(r if any(r) else (0,))
    if not Bs:
        Bs = [(0,)]
    return Bs

def w_lin(B, p):
    """Doubled valuation of a (<=linear) coefficient poly in a v(x)=1/2 frame:
    w(a*x + b) = min(2 v(b), 2 v(a) + 1); None if B = 0."""
    b = B[0] if len(B) > 0 else 0
    a = B[1] if len(B) > 1 else 0
    cands = []
    if b != 0:
        cands.append(2 * vp(b, p))
    if a != 0:
        cands.append(2 * vp(a, p) + 1)
    return min(cands) if cands else None

def w_lin_unit(B, p):
    """Residual unit digit of B at its w-level (parities differ: no tie)."""
    w = w_lin(B, p)
    if w is None:
        return None
    b = B[0] if len(B) > 0 else 0
    a = B[1] if len(B) > 1 else 0
    if w % 2 == 0:
        return digit(b, w // 2, p)
    return digit(a, (w - 1) // 2, p)

# --------------------- constructive Lemma-A extractor ------------------------

def solve_cramer_padic(M, rhs, p, K):
    """Integer vector a (mod p^K) with M a = rhs over Z_p, or None if the
    exact rational solution is not p-integral."""
    n = len(M)
    D = det_bareiss(M)
    assert D != 0
    vD = vp(D, p)
    Du = D // p ** vD
    pK = p ** K
    Duinv = pow(Du % pK, -1, pK)
    a = []
    for i in range(n):
        Mi = [row[:] for row in M]
        for r in range(n):
            Mi[r][i] = rhs[r]
        Di = det_bareiss(Mi)
        if Di == 0:
            a.append(0)
            continue
        vi = vp(Di, p)
        if vi < vD:
            return None
        a.append(p ** (vi - vD) * (Di // p ** vi) * Duinv % pK)
    return a

def extract_factors(F, base, p, tau, N, rho, max_iter=40):
    """Newton-Cramer extraction of the pinned factorization from F alone.
    F: integer coeff tuple (monic, deg n).  base: pinned factor tuples.
    Returns list of factor tuples mod p^N, or None (reject)."""
    BIG = N + 2 * rho + 6
    PB = p ** BIG
    degs = [len(f) - 1 for f in base]
    n = sum(degs)
    g = [list(polmod_q(f, PB)) for f in base]
    last_v, stall = -1, 0
    for _ in range(max_iter):
        E = polsub(F, polymul_many(g))
        E = polmod_q(E, PB)[:n]  # deg <= n-1
        E = tuple(E) + (0,) * (n - len(E))
        if all(c == 0 for c in E):
            break
        vE = min(vp(c, p) for c in E if c != 0)
        if vE >= N + rho + 2:
            break
        if vE <= last_v:
            stall += 1
            if stall >= 3:
                return None
        else:
            stall = 0
        last_v = vE
        M = phi_matrix([tuple(gj) for gj in g])
        a = solve_cramer_padic(M, list(E), p, BIG)
        if a is None:
            return None
        idx = 0
        for j, d in enumerate(degs):
            for t in range(d):
                g[j][t] = (g[j][t] + a[idx]) % PB
                idx += 1
    prod = polmod_q(polymul_many(g), p ** N)
    if prod != polmod_q(F, p ** N):
        return None
    ptau = p ** tau
    for gj, fj in zip(g, base):
        if polmod_q(gj, ptau) != polmod_q(fj, ptau):
            return None
    return [polmod_q(gj, p ** N) for gj in g]

# ------------------------------ frame readers --------------------------------

def taylor_shift(f, c):
    """Coefficients of f(c + y) by repeated synthetic division (exact)."""
    f = list(f)
    out = []
    while f:
        rem = f[:]
        qq = [0] * (len(f) - 1)
        for i in range(len(f) - 1, 0, -1):
            qq[i - 1] = rem[i]
            rem[i - 1] += rem[i] * c
        out.append(rem[0])
        f = qq
    return tuple(out)

def hen_root(F, c0, p, N, big_extra=6):
    """Newton root of F near c0 (p-adic).  Returns (root mod p^(N-vd), vd)
    or None on non-contraction."""
    BIG = N + big_extra
    PB = p ** BIG
    Fd = polderiv(F)
    r = c0 % PB
    vd = None
    for _ in range(80):
        t = poleval(F, r) % PB
        d = poleval(Fd, r) % PB
        vd = vp(d, p)
        if vd is None:
            return None
        if t == 0 or (vp(t, p) is not None and vp(t, p) >= N + 2):
            break
        vt = vp(t, p)
        if vt - vd <= vd:
            return None
        ut = t // p ** vt
        ud = d // p ** vd
        corr = (-(p ** (vt - vd)) * ut * pow(ud % PB, -1, PB)) % PB
        r = (r + corr) % PB
    else:
        return None
    return r % p ** (N - vd), vd

def hen_side(F, c0, p):
    """Order-1 side data of F at the fixed center c0:
    (v(F(c0)), unit(F(c0)), v(F'(c0)), unit(F'(c0))); None-entries if zero."""
    a = poleval(F, c0)
    b = poleval(polderiv(F), c0)
    return (vp(a, p), unit_digit(a, p), vp(b, p), unit_digit(b, p))

def ramq_side(h, Phi, p):
    """Principal branch-side data of h in the monic-quadratic frame Phi:
    (w(B1), unit(B1), w(B0), unit(B0)) in doubled-valuation units."""
    Bs = phidev(h, Phi)
    B0 = Bs[0] if len(Bs) > 0 else (0,)
    B1 = Bs[1] if len(Bs) > 1 else (0,)
    return (w_lin(B1, p), w_lin_unit(B1, p), w_lin(B0, p), w_lin_unit(B0, p))

def lin_coeff(B, which):
    if which == 'c':
        return B[0] if len(B) > 0 else 0
    return B[1] if len(B) > 1 else 0

def ramq_word(h, Phi, p, slots):
    """Raw digit word of the B0-coefficients of h in frame Phi at the given
    slots [(which, level), ...]."""
    Bs = phidev(h, Phi)
    B0 = Bs[0] if len(Bs) > 0 else (0,)
    return tuple(digit(lin_coeff(B0, w), lv, p) for (w, lv) in slots)

def species_word_ramq(b_x, b_c, p, tau, cap=2):
    """Depth-read SPECIES word of a factor deviation b = b_x*x + b_c in a
    RAMQ frame: (min(w(b)-2tau, cap), unit-at-w if < cap).  Merging read."""
    w = w_lin((b_c, b_x), p)
    if w is None or w - 2 * tau >= cap:
        return ('deep',)
    return (w - 2 * tau, w_lin_unit((b_c, b_x), p))

def species_word_hen(r, r_base, p, tau, cap=2):
    d = (r - r_base)
    v = vp(d, p)
    if v is None or v - tau >= cap:
        return ('deep',)
    return (v - tau, digit(d, v, p))

# ------------------------------ sweep generator ------------------------------

def free_positions(degs, tau, N):
    """[(j, t, level)] for all free digit positions of the polydisc."""
    pos = []
    for j, d in enumerate(degs):
        for t in range(d):
            for lv in range(tau, N):
                pos.append((j, t, lv))
    return pos

def tuple_from_digits(base, assign, p, tau, N):
    """Build member tuple from base + digit assignment {(j,t,level): digit}."""
    pN = p ** N
    out = []
    for j, f in enumerate(base):
        g = list(polmod_q(f, pN))
        for (jj, t, lv), dg in assign.items():
            if jj == j:
                g[t] = (g[t] + dg * p ** lv) % pN
        out.append(tuple(g))
    return tuple(out)

def gen_sweep(p, base, tau, N, full_cap, axis_variants, n_random):
    """Members of the tau-pinned polydisc at level N.  Full enumeration when
    the domain is <= full_cap, else axis sweeps + deterministic variants +
    random sample.  Returns (list of member tuples, mode-string)."""
    degs = [len(f) - 1 for f in base]
    pos = free_positions(degs, tau, N)
    dom = p ** len(pos)
    if dom <= full_cap:
        members = []
        for digs in itertools.product(range(p), repeat=len(pos)):
            assign = {pos[i]: digs[i] for i in range(len(pos))}
            members.append(tuple_from_digits(base, assign, p, tau, N))
        return members, "full(%d)" % dom
    rng = random.Random(20260808)
    seen = set()
    members = []

    def add(assign):
        t = tuple_from_digits(base, assign, p, tau, N)
        if t not in seen:
            seen.add(t)
            members.append(t)

    for j in range(len(base)):
        own = [q for q in pos if q[0] == j]
        oth = [q for q in pos if q[0] != j]
        for var in range(axis_variants):
            vr = random.Random(1000 * j + var)
            oth_assign = {q: (0 if var == 0 else vr.randrange(p)) for q in oth}
            for digs in itertools.product(range(p), repeat=len(own)):
                assign = dict(oth_assign)
                assign.update({own[i]: digs[i] for i in range(len(own))})
                add(assign)
    for _ in range(n_random):
        add({q: rng.randrange(p) for q in pos})
    return members, "axis+rand(%d)" % len(members)

# ------------------------------ the site table -------------------------------

X = None  # marker for measured-only entries

SITES = [
    dict(label="S1", p=5, factors=((6, -2, 1), (9, -4, 1)), roster=(0, 1),
         rho=0, es=(0, 0, 0, 0), N_words=3,
         sweep=dict(full_cap=20000, axis_variants=8, n_random=1500),
         branches=[
             dict(kind="RAMS", j=0, center=1, delta=0, u=1, wlevel=1, info_level=2),
             dict(kind="RAMS", j=1, center=2, delta=0, u=1, wlevel=1, info_level=2)],
         itau=[dict(N=2, surv=625, image=625)],
         it4b=None),
    dict(label="S2", p=2, factors=((2, 0, 1), (2, 2, 1)), roster=(0, 1),
         rho=3, es=(0, 0, 1, 2), N_words=8,
         sweep=dict(full_cap=70000, axis_variants=6, n_random=1500),
         branches=[
             dict(kind="RAMQ", j=0, delta_w=3, u=1,
                  fslots=(('x', 5), ('x', 6), ('c', 6), ('c', 7)),
                  gslots=(('c', 4), ('c', 5), ('x', 4), ('x', 5))),
             dict(kind="RAMQ", j=1, delta_w=3, u=1,
                  fslots=(('x', 5), ('x', 6), ('c', 6), ('c', 7)),
                  gslots=(('c', 4), ('c', 5), ('x', 4), ('x', 5)))],
         itau=[dict(N=5, surv=16, image=4), dict(N=6, surv=256, image=32)],
         it4b=dict(N=8, subpin_level=4, word_level=5)),
    dict(label="S3", p=3, factors=((-1, 1), (-4, 1), (-7, 1)), roster=(0, 1, 2),
         rho=3, es=(0, 1, 2), N_words=8,
         sweep=dict(full_cap=0, axis_variants=6, n_random=1500),
         branches=[
             dict(kind="HEN", j=0, center=1, delta=2, u=2, wlevels=(4, 5)),
             dict(kind="HEN", j=1, center=4, delta=2, u=2, wlevels=(4, 5)),
             dict(kind="HEN", j=2, center=7, delta=2, u=2, wlevels=(4, 5))],
         itau=[dict(N=6, surv=729, image=27)],
         it4b=dict(N=8, subpin_level=4, word_level=5)),
    dict(label="S3b", p=3, factors=((-1, 1), (-4, 1), (-7, 1), (1, 0, 1)),
         roster=(0, 1, 2),  # index 3 = f0 = x^2+1 (C0: pinned, no event)
         rho=3, es=None, es_sum=3, N_words=8,
         sweep=dict(full_cap=0, axis_variants=6, n_random=2000),
         branches=[
             dict(kind="HEN", j=0, center=1, delta=2, u=1, wlevels=(4, 5)),
             dict(kind="HEN", j=1, center=4, delta=2, u=1, wlevels=(4, 5)),
             dict(kind="HEN", j=2, center=7, delta=2, u=1, wlevels=(4, 5))],
         itau=[dict(N=5, surv=243, image=X)],  # image = 3^(5-sM(1)), sM measured
         it4b=None),
    dict(label="S5", p=3, factors=((3, 0, 1), (3, 3, 1)), roster=(0, 1),
         rho=3, es=(0, 0, 1, 2), N_words=8,
         sweep=dict(full_cap=0, axis_variants=6, n_random=2000),
         branches=[
             dict(kind="RAMQ", j=0, delta_w=3, u=1,
                  fslots=(('x', 5), ('x', 6), ('c', 6), ('c', 7)),
                  gslots=(('c', 4), ('c', 5), ('x', 4), ('x', 5))),
             dict(kind="RAMQ", j=1, delta_w=3, u=2,
                  fslots=(('x', 5), ('x', 6), ('c', 6), ('c', 7)),
                  gslots=(('c', 4), ('c', 5), ('x', 4), ('x', 5)))],
         itau=[dict(N=5, surv=81, image=9), dict(N=6, surv=6561, image=243)],
         it4b=None),
    dict(label="S6", p=3, factors=((-3, 1), (-3, 0, 1)), roster=(0, 1),
         rho=1, es=(0, 0, 1), N_words=6,
         sweep=dict(full_cap=0, axis_variants=6, n_random=1500),
         branches=[
             dict(kind="HEN", j=0, center=3, delta=1, u=2, wlevels=(2, 3)),
             # PRICING NOTE (sealed pre-run): slots stop at level tau+rho = 3;
             # a ('c',4) slot would sit AT level tau+rho+1 = 2*tau where the
             # deviation*deviation interaction term lands (out of priced
             # scope, K would need 5 > ceiling 4) — same boundary as S1's
             # displayed depth-2 leak.
             dict(kind="RAMQ", j=1, delta_w=1, u=1,
                  fslots=(('x', 2), ('x', 3), ('c', 3)),
                  gslots=(('c', 2), ('c', 3), ('x', 2)))],
         itau=[dict(N=4, surv=729, image=243)],
         it4b=None),
]

# ------------------------------- test runners --------------------------------

RESULTS = []
LOG = []

def rec(site, test, ok, detail=""):
    tag = {True: "PASS", False: "FAIL", None: "INFO"}[ok]
    line = "[%s] %s | %s | %s" % (tag, site, test, detail)
    print(line, flush=True)
    LOG.append(line)
    RESULTS.append(dict(site=site, test=test, status=tag, detail=detail))

def inv_mod_p(x, p):
    return pow(x % p, p - 2, p) if p > 2 else (x % p)

def branch_reads(site, member, F, br, p, N, tau):
    """Returns (ok_i1, ok_i2, obs_d1, obs_u1, obs_d0, obs_u0, w_g, W_F, skip0)
    for one member at one branch; obs_* are observed translation/unit data,
    skip0 = the (0,.) comparison was skipped (blind-zone/base member)."""
    gj = member[br["j"]]
    if br["kind"] == "HEN":
        c0 = br["center"]
        vF, uF, vFd, uFd = hen_side(F, c0, p)
        gc = poleval(gj, c0)
        vg, ug = vp(gc, p), unit_digit(gc, p)
        obs_d1, obs_u1 = vFd, uFd
        skip0 = vg is None or vg >= N - br["delta"] - 1
        obs_d0 = None if skip0 else (vF - vg if vF is not None else None)
        obs_u0 = None if skip0 else (uF * inv_mod_p(ug, p)) % p
        rt = hen_root(F, c0, p, N)
        if rt is None:
            return None
        rF, vd = rt
        root_g = (-gj[0]) % p ** N
        W_F = tuple(digit(rF, lv, p) for lv in br["wlevels"])
        w_g = tuple(digit(root_g, lv, p) for lv in br["wlevels"])
        return obs_d1, obs_u1, obs_d0, obs_u0, w_g, W_F, skip0, None
    if br["kind"] == "RAMQ":
        Phi = site["factors"][br["j"]]
        w1, u1, w0, u0 = ramq_side(F, Phi, p)
        b = polsub(gj, Phi)
        wb, ub = w_lin(b, p), w_lin_unit(b, p)
        obs_d1, obs_u1 = w1, u1
        skip0 = wb is None or wb >= 2 * (N - 2)
        obs_d0 = None if skip0 else (w0 - wb if w0 is not None else None)
        obs_u0 = None if skip0 else (u0 * inv_mod_p(ub, p)) % p
        W_F = ramq_word(F, Phi, p, br["fslots"])
        w_g = ramq_word(gj, Phi, p, br["gslots"])
        return obs_d1, obs_u1, obs_d0, obs_u0, w_g, W_F, skip0, \
            (None if skip0 else wb % 2)
    if br["kind"] == "RAMS":
        c0 = br["center"]
        dev = taylor_shift(F, c0)
        B0F, B2F = dev[0], dev[2]
        gc = poleval(gj, c0)
        vg, ug = vp(gc, p), unit_digit(gc, p)
        obs_d1, obs_u1 = vp(B2F, p), unit_digit(B2F, p)
        skip0 = vg is None or vg >= N - 1
        obs_d0 = None if skip0 else (vp(B0F, p) - vg if vp(B0F, p) is not None else None)
        obs_u0 = None if skip0 else (unit_digit(B0F, p) * inv_mod_p(ug, p)) % p
        W_F = (digit(B0F, br["wlevel"], p),)
        w_g = (digit(gc, br["wlevel"], p),)
        # INFO leak channel rides along as an extra slot, tested separately
        return obs_d1, obs_u1, obs_d0, obs_u0, w_g, W_F, skip0, None
    raise ValueError(br["kind"])

def run_kloc(site):
    lab, p = site["label"], site["p"]
    base = site["factors"]
    rho, tau, N = site["rho"], site["rho"] + 1, site["N_words"]
    pN = p ** N
    members, mode = gen_sweep(p, base, tau, N, site["sweep"]["full_cap"],
                              site["sweep"]["axis_variants"],
                              site["sweep"]["n_random"])
    rec(lab, "sweep", None, "mode=%s members=%d N=%d" % (mode, len(members), N))
    # P-A: K-JAC within-cell constancy on a sample
    sam = members if len(members) <= 300 else random.Random(7).sample(members, 300)
    bad = [m for m in sam if vp(det_bareiss(phi_matrix(list(m))), p) != rho]
    rec(lab, "P-A K-JAC v(detPhi)=rho on cell", len(bad) == 0,
        "sampled=%d bad=%d rho=%d" % (len(sam), len(bad), rho))
    Fs = [polymul_many(m) for m in members]
    for bi, br in enumerate(site["branches"]):
        tagb = "branch%d(%s)" % (br["j"], br["kind"])
        d1set, u1set, d0set, u0set = set(), set(), set(), set()
        u0_by_par = {0: set(), 1: set()}
        data = []
        nskip, nfail = 0, 0
        for m, F in zip(members, Fs):
            out = branch_reads(site, m, F, br, p, N, tau)
            if out is None:
                nfail += 1
                continue
            obs_d1, obs_u1, obs_d0, obs_u0, w_g, W_F, skip0, par = out
            d1set.add(obs_d1)
            u1set.add(obs_u1)
            if skip0:
                nskip += 1
            else:
                d0set.add(obs_d0)
                u0set.add(obs_u0)
                if par is not None:
                    u0_by_par[par].add(obs_u0)
            data.append((m[br["j"]], w_g, W_F))
        sealed_d = br.get("delta", br.get("delta_w"))
        sealed_u = br["u"]
        rec(lab, "P-B (i) %s delta cell-constant" % tagb,
            d1set == {sealed_d} and d0set <= {sealed_d},
            "d1set=%s d0set=%s sealed=%s skip0=%d noroot=%d"
            % (sorted(d1set), sorted(d0set), sealed_d, nskip, nfail))
        rec(lab, "P-C (ii) %s unit-scalar cell-constant" % tagb,
            u1set == {sealed_u % p} and u0set <= {sealed_u % p},
            "u1set=%s u0set=%s sealed=%s" % (sorted(u1set), sorted(u0set), sealed_u % p))
        if br["kind"] == "RAMQ" and any(u0_by_par.values()):
            # SUPPLEMENTARY (post-hoc, added after run-2's S5 countermodel):
            # clause (ii) is PER-SLOPE in the blueprint (lambda_{j,r} fixed);
            # the pooled u0set above is the slope-POOLED strengthening.  The
            # measured restatement pin: u0 constant per slope-parity class
            # (the R_lambda ell-shift covariance, blueprint 1.3 risk (c);
            # sign = unit of the frame's x^2-reduction constant when the
            # deviation is x-dominated).
            okp = all(len(s) <= 1 for s in u0_by_par.values())
            rec(lab, "P-C (ii') %s per-slope-parity unit constancy "
                "[SUPPLEMENTARY]" % tagb, okp,
                "u0 even-w=%s odd-w=%s" % (sorted(u0_by_par[0]),
                                           sorted(u0_by_par[1])))
        # P-D d1: cofactor independence
        by_g = {}
        for gj, w_g, W_F in data:
            by_g.setdefault(gj, set()).add(W_F)
        viol = sum(1 for s in by_g.values() if len(s) > 1)
        rec(lab, "P-D d1 %s cofactor-independence" % tagb, viol == 0,
            "gj-classes=%d violations=%d" % (len(by_g), viol))
        # P-D d2: word-graph bijection
        fwd, bwd = {}, {}
        for gj, w_g, W_F in data:
            fwd.setdefault(w_g, set()).add(W_F)
            bwd.setdefault(W_F, set()).add(w_g)
        ok2 = all(len(s) == 1 for s in fwd.values()) and \
              all(len(s) == 1 for s in bwd.values())
        rec(lab, "P-D d2 %s word-graph bijection" % tagb, ok2,
            "gwords=%d Fwords=%d maxfwd=%d maxbwd=%d"
            % (len(fwd), len(bwd), max(map(len, fwd.values())),
               max(map(len, bwd.values()))))
        # P-D d3: measured K
        Kmin = None
        for K in range(0, N + 1):
            pk = p ** K
            byk = {}
            okK = True
            for gj, w_g, W_F in data:
                key = tuple(c % pk for c in gj)
                if key in byk:
                    if byk[key] != W_F:
                        okK = False
                        break
                else:
                    byk[key] = W_F
            if okK:
                Kmin = K
                break
        ceil = tau + rho + 1
        rec(lab, "P-D d3 %s measured K <= tau+rho+1" % tagb,
            Kmin is not None and Kmin <= ceil,
            "K_measured=%s ceiling=%d" % (Kmin, ceil))
        # S1 INFO leak channel (raw depth-2 B0 digit, NOT an order-1 OM read)
        if br["kind"] == "RAMS":
            leak = {}
            for m, F in zip(members, Fs):
                gj = m[br["j"]]
                d2 = digit(poleval(F, br["center"]), br["info_level"], p)
                leak.setdefault(gj, set()).add(d2)
            nl = sum(1 for s in leak.values() if len(s) > 1)
            rec(lab, "P-D INFO %s raw depth-2 digit leak (expected)" % tagb,
                None, "violating gj-classes=%d/%d (leak EXPECTED: not an "
                "order-1 OM read; order-2 refinement required)" % (nl, len(leak)))

def run_integrity(site):
    lab, p, base = site["label"], site["p"], site["factors"]
    rho_c = 0
    m = len(base)
    for i in range(m):
        for j in range(i + 1, m):
            r = resultant(base[i], base[j])
            assert r != 0
            rho_c += vp(r, p)
    ok = rho_c == site["rho"]
    rec(lab, "integrity rho", ok, "computed=%d sealed=%d" % (rho_c, site["rho"]))
    es = smith_profile(phi_matrix(list(base)), p)
    site["es_measured"] = es
    if site.get("es") is not None:
        rec(lab, "integrity Smith es", es == tuple(site["es"]),
            "measured=%s sealed=%s" % (list(es), list(site["es"])))
    else:
        rec(lab, "integrity Smith es (sum sealed)", sum(es) == site["es_sum"],
            "measured=%s sealed_sum=%d" % (list(es), site["es_sum"]))

def run_itau(site):
    lab, p, base = site["label"], site["p"], site["factors"]
    rho, tau = site["rho"], site["rho"] + 1
    es = site["es_measured"]
    degs = [len(f) - 1 for f in base]
    n = sum(degs)
    for spec in site["itau"]:
        N = spec["N"]
        pN = p ** N
        members, mode = gen_sweep(p, base, tau, N, 300000, 0, 0)
        assert mode.startswith("full"), "itau scan needs full polydisc"
        image = {}
        for mtuple in members:
            F = polmod_q(polymul_many(mtuple), pN)
            image[F] = image.get(F, 0) + 1
        # survivors: all monic F = prod(base) mod p^tau, coefficientwise tail
        F0 = polmod_q(polymul_many(base), pN)
        ptau, M = p ** tau, N - tau
        tails = itertools.product(range(p ** M), repeat=n)
        survivors = [tuple((F0[i] + ptau * t[i]) % pN for i in range(n)) + (1,)
                     for t in tails]
        survivors = [s for s in survivors]
        sM = sum(min(e, M) for e in es)
        pred_img = p ** (sum(d * M for d in degs) - sM)
        rec(lab, "P-E counts N=%d" % N,
            len(survivors) == spec["surv"] and len(image) == pred_img
            and (spec["image"] is X or spec["image"] == len(image)),
            "survivors=%d(sealed %s) image=%d(sealed %s; smith-pred %d)"
            % (len(survivors), spec["surv"], len(image), spec["image"], pred_img))
        fib = set(image.values())
        rec(lab, "P-E fiber constancy N=%d" % N, fib == {p ** sM},
            "fiber sizes=%s pred=%d" % (sorted(fib), p ** sM))
        prodC = p ** sum(d * M for d in degs)
        rec(lab, "P-E (e3) product law N=%d" % N,
            len(image) * p ** sM == prodC,
            "#Sigma*p^sM=%d prod#C_j=%d (sM=%d)" % (len(image) * p ** sM, prodC, sM))
        # extraction decides every survivor
        img_set = set(image)
        acc, fneg, fpos = set(), [], []
        for Fv in survivors:
            got = extract_factors(list(Fv), base, p, tau, N, rho)
            if got is not None:
                acc.add(Fv)
        fneg = [Fv for Fv in img_set if Fv not in acc]
        fpos = [Fv for Fv in acc if Fv not in img_set]
        rec(lab, "P-E (e1) extraction accepts image N=%d" % N, len(fneg) == 0,
            "false-negatives=%d/%d" % (len(fneg), len(img_set)))
        rec(lab, "P-E (e2) accepted == image N=%d" % N,
            len(fpos) == 0 and len(fneg) == 0,
            "accepted=%d image=%d false-pos=%d" % (len(acc), len(img_set), len(fpos)))
        emax = max(es)
        rec(lab, "P-E guard diagnosis N=%d" % N, None,
            "D-8 guard tau+2rho=%d (scan %s-guard); blind zone N-emax=%d vs "
            "tau=%d => pins %scovered (extraction round-trip promised only "
            "when covered)" % (tau + 2 * rho,
                               "in" if N >= tau + 2 * rho else "BELOW",
                               N - emax, tau,
                               "" if N - emax >= tau else "NOT "))
    # supplementary in-guard constructive-surjectivity sample (Lemma A face)
    Ng = tau + 2 * rho
    if all(spec["N"] < Ng for spec in site["itau"]):
        rng = random.Random(99)
        pNg, Mg = p ** Ng, Ng - tau
        nbad = 0
        for _ in range(200):
            mem = tuple(tuple((f[i] + p ** tau * rng.randrange(p ** Mg)) % pNg
                              if i < len(f) - 1 else 1
                              for i in range(len(f))) for f in base)
            Fv = polmod_q(polymul_many(mem), pNg)
            if extract_factors(list(Fv), base, p, tau, Ng, rho) is None:
                nbad += 1
        rec(lab, "P-E (e1g) IN-GUARD extraction sample N=%d" % Ng, nbad == 0,
            "random image members=200 false-negatives=%d" % nbad)

def run_it4b(site):
    spec = site.get("it4b")
    if not spec:
        return
    lab, p, base = site["label"], site["p"], site["factors"]
    rho, tau = site["rho"], site["rho"] + 1
    N, subL, wL = spec["N"], spec["subpin_level"], spec["word_level"]
    degs = [len(f) - 1 for f in base]
    roster = site["roster"]
    pN, M = p ** N, N - tau
    PL = [p ** i for i in range(N + 2)]

    def dig(c, lv):
        return (c // PL[lv]) % p

    slots = [(j, t) for j in range(len(base)) for t in range(degs[j])]
    rslots = [(j, t) for (j, t) in slots if j in roster]
    ptau = p ** tau
    sub_tab, sub_alph = {}, {}
    sub_spec_tab, sub_spec_alph = {}, {}
    joint_tab, marg_tab = {}, {j: {} for j in roster}
    sjoint_tab, smarg_tab = {}, {j: {} for j in roster}
    total = 0
    for Ts in itertools.product(range(p ** M), repeat=len(slots)):
        cf = {}
        for (jt, T) in zip(slots, Ts):
            j, t = jt
            cf[jt] = (base[j][t] + ptau * T) % pN
        subkey = tuple(dig(cf[jt], subL) for jt in rslots)
        word = tuple(dig(cf[jt], wL) for jt in rslots)
        # species (merging OM-style read): from EXACT deviations p^tau * T
        sww, per_j_w, per_j_s = [], {}, {}
        for j in roster:
            if degs[j] == 1:
                T0 = Ts[slots.index((j, 0))]
                dvv = ptau * T0
                v = vp(dvv, p)
                s = ('deep',) if (v is None or v - tau >= 2) else (v - tau, dig(dvv, v))
                wj = (dig(cf[(j, 0)], wL),)
            else:
                Tc = Ts[slots.index((j, 0))]
                Tx = Ts[slots.index((j, 1))]
                s = species_word_ramq(ptau * Tx, ptau * Tc, p, tau)
                wj = (dig(cf[(j, 0)], wL), dig(cf[(j, 1)], wL))
            sww.append(s)
            per_j_w[j], per_j_s[j] = wj, s
        sword = tuple(sww)
        d1 = sub_tab.setdefault(subkey, {})
        d1[word] = d1.get(word, 0) + 1
        d2 = sub_spec_tab.setdefault(subkey, {})
        d2[sword] = d2.get(sword, 0) + 1
        jw = tuple(per_j_w[j] for j in roster)
        joint_tab[jw] = joint_tab.get(jw, 0) + 1
        sjoint_tab[sword] = sjoint_tab.get(sword, 0) + 1
        for j in roster:
            marg_tab[j][per_j_w[j]] = marg_tab[j].get(per_j_w[j], 0) + 1
            smarg_tab[j][per_j_s[j]] = smarg_tab[j].get(per_j_s[j], 0) + 1
        total += 1
    # P-F f1: within-sub-cell read-fiber constancy (raw word)
    bad_f1 = [k for k, d in sub_tab.items() if len(set(d.values())) > 1]
    rec(lab, "P-F f1 sub-cell read-fiber constancy (raw)", len(bad_f1) == 0,
        "subcells=%d nonuniform=%d" % (len(sub_tab), len(bad_f1)))
    alphs = {k: frozenset(d) for k, d in sub_tab.items()}
    rec(lab, "P-F f2 alphabet stability (raw)", len(set(alphs.values())) == 1,
        "distinct alphabets=%d sizes=%s"
        % (len(set(alphs.values())), sorted({len(a) for a in alphs.values()})))
    # species tables: MEASURED DATA for the IT-4b restatement (INFO by seal)
    bad_s1 = [k for k, d in sub_spec_tab.items() if len(set(d.values())) > 1]
    salphs = {k: frozenset(d) for k, d in sub_spec_tab.items()}
    rec(lab, "P-F species read-fiber constancy [measured data]", None,
        "subcells=%d nonuniform=%d distinct-alphabets=%d"
        % (len(sub_spec_tab), len(bad_s1), len(set(salphs.values()))))
    ex = sorted(sjoint_tab.items(), key=lambda kv: str(kv))[:6]
    rec(lab, "P-F species joint table sample [measured data]", None,
        "total=%d entries=%d sample=%s" % (total, len(sjoint_tab), ex))
    # P-G g1: aggregation (C1a instance)
    agg = {}
    for d in sub_tab.values():
        for w, c in d.items():
            agg[w] = agg.get(w, 0) + c
    rec(lab, "P-G g1 aggregate uniformity (C1a instance)",
        len(set(agg.values())) == 1,
        "aggregate counts=%s" % sorted(set(agg.values())))
    # P-G g2: (SIB) identity on joint words (C1b shape), raw + species
    m = len(roster)
    bad = 0
    for jw, cnt in joint_tab.items():
        lhs = cnt * total ** (m - 1)
        rhs = 1
        for j, wj in zip(roster, jw):
            rhs *= marg_tab[j][wj]
        if lhs != rhs:
            bad += 1
    rec(lab, "P-G g2 (SIB) product identity raw words", bad == 0,
        "joint words=%d violations=%d" % (len(joint_tab), bad))
    bad = 0
    for sw, cnt in sjoint_tab.items():
        lhs = cnt * total ** (m - 1)
        rhs = 1
        for j, sj in zip(roster, sw):
            rhs *= smarg_tab[j][sj]
        if lhs != rhs:
            bad += 1
    rec(lab, "P-G g2 (SIB) product identity species words", bad == 0,
        "joint species=%d violations=%d" % (len(sjoint_tab), bad))

def main():
    t0 = time.time()
    print("N-H7-1 h7_kloc_probe — sealed run, seed 20260808", flush=True)
    for site in SITES:
        ts = time.time()
        run_integrity(site)
        run_kloc(site)
        run_itau(site)
        run_it4b(site)
        rec(site["label"], "site wall-time", None, "%.1fs" % (time.time() - ts))
    npass = sum(1 for r in RESULTS if r["status"] == "PASS")
    nfail = sum(1 for r in RESULTS if r["status"] == "FAIL")
    ninfo = sum(1 for r in RESULTS if r["status"] == "INFO")
    line = "SUMMARY: %d PASS, %d FAIL, %d INFO (%.1fs total)" % (
        npass, nfail, ninfo, time.time() - t0)
    print(line, flush=True)
    LOG.append(line)
    with open(OUTDIR + "/h7_kloc_probe_results.json", "w") as fh:
        json.dump(dict(results=RESULTS, npass=npass, nfail=nfail,
                       ninfo=ninfo, seconds=round(time.time() - t0, 1)), fh, indent=1)
    with open(OUTDIR + "/h7_kloc_probe_output.txt", "w") as fh:
        fh.write("\n".join(LOG) + "\n")
    return 1 if nfail else 0

if __name__ == "__main__":
    sys.exit(main())


