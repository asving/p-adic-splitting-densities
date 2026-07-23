#!/usr/bin/env python3
"""case_g_gate.py — Case G: the ORDER-INCREMENT move (an e = 2, mu = 2 descend at a
deg-1 key creating a deg-2 key), n = 4, at p = 2 and p = 3.

p = 2 instance:
  Ambient: monic quartics f = x^4 + a3 x^3 + a2 x^2 + a1 x + a0 over Z_2, mod 2^N.
  Read 0 (root): f-bar = x^4, i.e. all four a_i even.
  Read 1 (Newton polygon of (i, v2(a_i)) with (4,0)): the slope -1/2 side spanning
    (0,2)-(4,0) with SQUARE residual. The side's residual is
    R(y) = y^2 + (a2/2 mod 2) y + (a0/4 mod 2); square <=> v(a2) >= 2, and then
    R = (y-1)^2, center c~ = 1. Closed-form stratum conditions (derive-checked below
    against an independent NP/residual read over the full box):
      v(a3) >= 1, v(a2) >= 2, v(a1) >= 2, v(a0) = 2 EXACT (a0/4 odd).
    Nominal mass 2^-8 of the full box.
  The order-2 key: phi2 := x^2 - 2 (lift of the residual root y = 1 under y <-> x^2/2).
  Read 2: the phi2-adic development f = phi2^2 + b1*phi2 + b0 (two GENUINE divisions
    by phi2 per member; deg b_i <= 1, each represented as its (x-coeff, const) pair).

p = 3 instance (same move, run per center):
  Read 1: slope -1/2 side (0,2)-(4,0); residual R(y) = y^2 + (a2/3 mod 3) y
    + (a0/9 mod 3); square <=> disc = (a2/3)^2 - 4(a0/9) == 0 mod 3, center
    c~ = -(a2/3)/2 == a2/3 mod 3, and mu = 2 needs c~ != 0. Centers c~ in {1, 2}.
    Closed-form stratum per center: v(a3) >= 1, v(a1) >= 2,
      v(a2) = 1 EXACT with digit1(a2) = -2c~ == c~ mod 3,
      v(a0) = 2 EXACT with digit2(a0) = c~^2 == 1 mod 3 (both centers).
    Nominal mass per center: 3^-1 * 3^-2 * 3^-2 * 3^-3 = 3^-8.
  The key: phi2 := x^2 - 3*c~ (c~ in {1,2} as integers).

Gates:
  G0  (mass): stratum count / p^{4N} == nominal mass EXACTLY at each censused N
      (p=2: N = 4,5,6 nominal 2^-8; p=3: N = 3,4,5 nominal 3^-8 per center).
  G0a (derive-check): at the smallest N the closed-form membership is compared,
      f-by-f over the FULL box, against an independent Newton-polygon + residual-square
      read (including the center assignment). Zero mismatches required.
  G1  (landing zone): joint distribution of (v-profile of b1, v-profile of b0),
      v-profile of a deg<=1 pair = (v of x-coeff, v of const), capped at N-1; report
      full 2D table, attained minima/maxima per coordinate, which components are
      FORCED (constant on the stratum).
  G2  (joint uniformity — the point): bucket stratum members by the first K = 2 digits
      of each of the 4 coordinates above its GLOBAL minimum over the stratum (the
      per-member minima VARY upward, none of the four valuations is constant, so
      bucketing is from the global minimum — stated in the output as the spec directs).
      All buckets must have EXACTLY equal counts. Report bucket count, sizes, verdict.
  G3  (sub-strata, p = 2): the same distributions restricted to the two sub-strata cut
      by the digit of a0/4 at height 1 (the bit (a0>>3)&1), to detect hidden
      dependence. Recorded raw (per-coordinate window marginals, pairwise-window
      uniformity scan, bucket occupancy/sizes); no pre-registered pass condition.
      (The spec asks G0/G1/G2 per center at p = 3; G3 is a p = 2 probe.)

Enumeration (stated per spec): the G0 counts are full-box censuses via per-coefficient
pruned loops — identical to the naive per-f count because the (derive-checked) stratum
conditions are per-coefficient; the derive-check at the smallest N IS a naive
unpruned full-box census with an independent membership read. G1/G2/G3 enumerate the
STRATUM directly from its digit parametrization (p=2 N=6: 2^16 members out of the
2^24 box; p=3 N=5: 3^12 per center), and the phi2-adic development is genuine
polynomial division per member, spot-verified by reconstructing
f = phi2^2 + b1*phi2 + b0 mod p^N.

Run: python3 case_g_gate.py           (full: p=2 up to N=6, p=3 up to N=5; ~1-2 min)
     python3 case_g_gate.py --quick   (p=2 up to N=5, p=3 up to N=4; G2/p=3 skipped
                                       there since its digit window needs N >= 5)
"""
import sys
from collections import Counter
from fractions import Fraction as F

COORD_NAMES = ('b1.x', 'b1.c', 'b0.x', 'b0.c')


# ------------------------------------------------------------------ p-adic helpers

def vp(x, p, cap):
    """p-adic valuation of the residue x mod p^cap; v(0) reported as cap."""
    if x == 0:
        return cap
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v if v < cap else cap


def polydiv(f, d, M):
    """f, d coefficient lists (low->high), d monic. Returns (q, r), f = q*d + r mod M."""
    f = list(f)
    dd = len(d) - 1
    q = [0] * (len(f) - dd)
    for i in range(len(f) - 1, dd - 1, -1):
        c = f[i] % M
        q[i - dd] = c
        for j in range(dd + 1):
            f[i - dd + j] = (f[i - dd + j] - c * d[j]) % M
    return q, [x % M for x in f[:dd]]


def develop(coeffs, phi, M):
    """f = x^4 + c3 x^3 + c2 x^2 + c1 x + c0 -> (b1, b0), each an (x-coeff, const)
    pair, with f = phi^2 + b1*phi + b0 via two genuine divisions by the monic
    quadratic phi (low->high list)."""
    c3, c2, c1, c0 = coeffs
    q1, b0 = polydiv([c0, c1, c2, c3, 1], phi, M)
    q2, b1 = polydiv(q1, phi, M)
    assert q2 == [1]
    return (b1[1], b1[0]), (b0[1], b0[0])


def polymul(A, B, M):
    R = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            R[i + j] = (R[i + j] + a * b) % M
    return R


# ------------------------------------------------------------------ membership reads

def closed_member(a3, a2, a1, a0, p):
    """Closed-form stratum conditions (the derive-checked digit conditions).
    Returns the center c~ (1 at p=2; 1 or 2 at p=3) or None."""
    if p == 2:
        if a3 % 2 or a2 % 4 or a1 % 4:
            return None
        if a0 % 4 or (a0 // 4) % 2 != 1:
            return None
        return 1
    # p = 3
    if a3 % 3 or a1 % 9:
        return None
    if a0 % 9 or (a0 // 9) % 3 != 1:        # digit2(a0) = c~^2 == 1 for both centers
        return None
    if a2 % 3:
        return None
    c = (a2 // 3) % 3                        # digit1(a2) = -2c~ == c~ mod 3
    return c if c != 0 else None


def np_member(a3, a2, a1, a0, p, N):
    """INDEPENDENT membership read for the derive-check: the Newton polygon of
    {(i, v(a_i)) : i=0..3} u {(4,0)} must be the single side (0,2)-(4,0)
    [left endpoint exactly (0,2); every interior point on-or-above the line
    y = 2 - x/2, i.e. 2*v(a_i) >= 4 - i], and the side's residual
    R(y) = y^2 + beta*y + gamma (beta from (2,1) if on the line, gamma from (0,2))
    must be the square (y - c~)^2 with c~ != 0. Returns c~ or None."""
    if vp(a0, p, N) != 2:
        return None
    if 2 * vp(a1, p, N) < 3:
        return None
    v2_ = vp(a2, p, N)
    if 2 * v2_ < 2:
        return None
    if 2 * vp(a3, p, N) < 1:
        return None
    beta = (a2 // p) % p if v2_ == 1 else 0
    gamma = (a0 // p ** 2) % p
    if p == 2:
        # over F2: (y - c)^2 = y^2 + c^2, so square <=> beta = 0; c = sqrt(gamma) = gamma
        if beta != 0:
            return None
        c = gamma
    else:
        if (beta * beta - 4 * gamma) % p:    # disc(R) == 0 <=> R is a square
            return None
        c = (-beta * pow(2, p - 2, p)) % p   # c~ = -beta/2 mod p
    return c if c != 0 else None


def derive_check(p, N):
    """Naive UNPRUNED full-box census at level N comparing closed_member vs np_member
    f-by-f. Returns (per-center counts from the independent read, #mismatches)."""
    q = p ** N
    counts = Counter()
    mism = 0
    for a3 in range(q):
        for a2 in range(q):
            for a1 in range(q):
                for a0 in range(q):
                    m1 = closed_member(a3, a2, a1, a0, p)
                    m2 = np_member(a3, a2, a1, a0, p, N)
                    if m1 != m2:
                        mism += 1
                        if mism <= 5:
                            print(f'    DERIVE MISMATCH at (a3,a2,a1,a0)='
                                  f'{(a3, a2, a1, a0)}: closed={m1} np={m2}')
                    if m2 is not None:
                        counts[m2] += 1
    return counts, mism


def census_g0(p, N):
    """Full-box stratum census via per-coefficient pruned loops (exactly the naive
    per-f count: the conditions are per-coefficient). Returns Counter center->count."""
    q = p ** N
    counts = Counter()
    if p == 2:
        for a0 in range(q):
            if a0 % 4 or (a0 // 4) % 2 != 1:
                continue
            for a1 in range(q):
                if a1 % 4:
                    continue
                for a2 in range(q):
                    if a2 % 4:
                        continue
                    for a3 in range(q):
                        if a3 % 2 == 0:
                            counts[1] += 1
    else:
        for a0 in range(q):
            if a0 % 9 or (a0 // 9) % 3 != 1:
                continue
            for a1 in range(q):
                if a1 % 9:
                    continue
                for a2 in range(q):
                    if a2 % 3:
                        continue
                    c = (a2 // 3) % 3
                    if c == 0:
                        continue
                    for a3 in range(q):
                        if a3 % 3 == 0:
                            counts[c] += 1
    return counts


def stratum(p, N, center):
    """Direct digit parametrization of the stratum (free digits explicit).
    Yields (a3, a2, a1, a0) reduced mod p^N."""
    q = p ** N
    if p == 2:
        for t3 in range(q // 2):
            a3 = 2 * t3
            for t2 in range(q // 4):
                a2 = 4 * t2
                for t1 in range(q // 4):
                    a1 = 4 * t1
                    for s in range(q // 8):
                        yield a3, a2, a1, 4 * (2 * s + 1)
    else:
        for t3 in range(q // 3):
            a3 = 3 * t3
            for k in range(q // 9):
                a2 = 3 * (center + 3 * k)
                for t1 in range(q // 9):
                    a1 = 9 * t1
                    for s in range(q // 27):
                        yield a3, a2, a1, 9 * (1 + 3 * s)


# ------------------------------------------------------------------ analysis passes

def pass1_g1(p, N, center, recon_stride):
    """Pass 1 over the stratum: G1 joint v-profile distribution (cap N-1), attained
    min/max per coordinate, 4-coordinate joint (for the independence observation),
    reconstruction spot-checks every recon_stride members."""
    q = p ** N
    phi2 = [(-p * center) % q, 0, 1]
    cap = N - 1
    joint = Counter()
    joint4 = Counter()
    mins = [N] * 4
    maxs = [-1] * 4
    total = 0
    recon = 0
    for a3, a2, a1, a0 in stratum(p, N, center):
        b1, b0 = develop((a3, a2, a1, a0), phi2, q)
        coords = (b1[0], b1[1], b0[0], b0[1])
        vs = tuple(vp(x, p, N) for x in coords)
        for i in range(4):
            if vs[i] < mins[i]:
                mins[i] = vs[i]
            if vs[i] > maxs[i]:
                maxs[i] = vs[i]
        cvs = tuple(min(v, cap) for v in vs)
        joint[(cvs[0], cvs[1]), (cvs[2], cvs[3])] += 1
        joint4[cvs] += 1
        if total % recon_stride == 0:
            lhs = polymul(phi2, phi2, q)
            t = polymul([b1[1], b1[0]], phi2, q)
            r = [(lhs[i] + (t[i] if i < len(t) else 0)
                  + ((b0[1], b0[0])[i] if i < 2 else 0)) % q for i in range(5)]
            assert r == [a0, a1, a2, a3, 1], \
                f'RECONSTRUCTION FAILURE at {(a3, a2, a1, a0)}'
            recon += 1
        total += 1
    return dict(joint=joint, joint4=joint4, mins=mins, maxs=maxs,
                total=total, recon=recon)


def pass2_g2(p, N, center, mins, do_g3):
    """Pass 2 over the stratum: G2 window buckets (K=2 digits above the global minima
    from pass 1) and, if do_g3, the same restricted to the two a0-digit sub-strata."""
    q = p ** N
    pp = p * p
    phi2 = [(-p * center) % q, 0, 1]
    cap = N - 1
    pows = [p ** m for m in mins]
    win = Counter()
    sub_win = {}
    sub_joint = {}
    for a3, a2, a1, a0 in stratum(p, N, center):
        b1, b0 = develop((a3, a2, a1, a0), phi2, q)
        coords = (b1[0], b1[1], b0[0], b0[1])
        key = tuple((x // pw) % pp for x, pw in zip(coords, pows))
        win[key] += 1
        if do_g3:
            bit = (a0 // p ** 3) % p        # digit of a0/p^2 at height 1
            sub_win.setdefault(bit, Counter())[key] += 1
            vs = tuple(min(vp(x, p, N), cap) for x in coords)
            sub_joint.setdefault(bit, Counter())[(vs[0], vs[1]), (vs[2], vs[3])] += 1
    return win, sub_win, sub_joint


# ------------------------------------------------------------------ reporting

def print_joint_table(joint, indent='    '):
    rows = sorted({r for r, _ in joint})
    cols = sorted({c for _, c in joint})
    w = max(7, max(len(str(c)) for c in cols) + 1)
    print(indent + 'rows = v-profile(b1) = (v(b1.x), v(b1.c)); '
                   'cols = v-profile(b0) = (v(b0.x), v(b0.c))')
    print(indent + ' ' * 8 + ''.join(f'{str(c):>{w}}' for c in cols))
    for r in rows:
        line = ''.join(f'{joint.get((r, c), 0):>{w}}' for c in cols)
        print(indent + f'{str(r):<8}' + line)


def marginals_of(joint):
    rowm, colm = Counter(), Counter()
    for (r, c), n in joint.items():
        rowm[r] += n
        colm[c] += n
    return rowm, colm


def product_form_ok(joint, total):
    """Exactness of joint == outer product of its two marginals (data observation)."""
    rowm, colm = marginals_of(joint)
    if len(joint) != len(rowm) * len(colm):
        return False
    return all(n * total == rowm[r] * colm[c] for (r, c), n in joint.items())


def coord_marginals4(joint4):
    ms = [Counter() for _ in range(4)]
    for vs, n in joint4.items():
        for i, v in enumerate(vs):
            ms[i][v] += n
    return ms


def product_form4_ok(joint4, total):
    ms = coord_marginals4(joint4)
    if len(joint4) != len(ms[0]) * len(ms[1]) * len(ms[2]) * len(ms[3]):
        return False
    t3 = total ** 3
    return all(n * t3 == ms[0][a] * ms[1][b] * ms[2][c] * ms[3][d]
               for (a, b, c, d), n in joint4.items())


def report_g2(win, total, pp, label, indent='  '):
    sizes = Counter(win.values())
    nb = len(win)
    uniform = len(sizes) == 1
    full = nb == pp ** 4
    exp = total // nb if nb else 0
    print(f'{indent}GATE G2 {label}: {nb} buckets (window space {pp ** 4}'
          f'{", fully covered" if full else " — NOT fully covered"}), '
          f'sizes {dict(sorted(sizes.items()))} '
          f'(uniform would be {exp} each) '
          f'[{"UNIFORM OK" if uniform else "NON-UNIFORM — G2 FAILS"}]')
    return uniform


def pairwise_scan(win_counter, pp, names=COORD_NAMES):
    """For each pair of window coordinates: is the restricted pairwise joint exactly
    uniform on the full pp x pp grid? Returns (list of failing pairs, their tables)."""
    bad = []
    for i in range(4):
        for j in range(i + 1, 4):
            pj = Counter()
            for key, n in win_counter.items():
                pj[(key[i], key[j])] += n
            szs = set(pj.values())
            if len(pj) != pp * pp or len(szs) != 1:
                bad.append(((names[i], names[j]), pj))
    return bad


def print_pair_table(pj, pp, indent='      '):
    print(indent + 'cols = second coordinate window value 0..' + str(pp - 1))
    print(indent + '     ' + ''.join(f'{c:>7}' for c in range(pp)))
    for r in range(pp):
        print(indent + f'{r:>5}' + ''.join(f'{pj.get((r, c), 0):>7}' for c in range(pp)))


# ------------------------------------------------------------------ instance driver

def run_instance(p, N, center, nominal, do_g3, print_g1_table=True):
    """Full G1/G2(/G3) analysis of one (p, N, center) instance. Returns dict of
    verdict bits."""
    q = p ** N
    pp = p * p
    print(f'\n--- p={p}, N={N}, center c~={center} '
          f'(key phi2 = x^2 - {p * center}) ---')
    print(f'  enumeration: direct stratum digit parametrization; '
          f'phi2-development by genuine division per member')
    r1 = pass1_g1(p, N, center, recon_stride=1 if p == 2 else 997)
    total = r1['total']
    print(f'  stratum size {total} (of box {q ** 4}); '
          f'reconstruction f == phi2^2+b1*phi2+b0 spot-checked on '
          f'{r1["recon"]} members: OK')
    ok_mass = F(total, q ** 4) == nominal
    print(f'  stratum mass {F(total, q ** 4)} vs nominal {nominal} '
          f'[{"OK" if ok_mass else "MISMATCH"}]')

    # ---- G1
    cap = N - 1
    print(f'  GATE G1 (landing zone) — joint (v-profile(b1), v-profile(b0)), '
          f'valuations capped at N-1 = {cap}:')
    if print_g1_table:
        print_joint_table(r1['joint'])
    ms = coord_marginals4(r1['joint4'])
    for i, nm in enumerate(COORD_NAMES):
        print(f'    v({nm}) marginal: {dict(sorted(ms[i].items()))}')
    forced = [i for i in range(4) if r1['mins'][i] == r1['maxs'][i]]
    print(f'    attained minima per coordinate {tuple(zip(COORD_NAMES, r1["mins"]))}')
    print(f'    attained maxima per coordinate {tuple(zip(COORD_NAMES, r1["maxs"]))} '
          f'(cap {N} = v(0))')
    if forced:
        print(f'    FORCED (constant) components: '
              f'{[COORD_NAMES[i] for i in forced]}')
    else:
        print(f'    FORCED components: NONE constant; the forced part is the '
              f'lower-bound box v >= {tuple(r1["mins"])} '
              f'(every coordinate valuation varies upward)')
    p2 = product_form_ok(r1['joint'], total)
    p4 = product_form4_ok(r1['joint4'], total)
    print(f'    observation: joint == product of the two pair-profile marginals '
          f'EXACTLY: {p2}; == product of all four coordinate marginals EXACTLY: {p4}')

    # ---- G2 (+G3 data)
    ok_g2 = None
    g3_data = None
    if r1['mins'][3] + 2 > N:
        print(f'  GATE G2: SKIPPED at N={N} (deepest window needs digits at heights '
              f'{r1["mins"][3]}..{r1["mins"][3] + 1}, i.e. N >= {r1["mins"][3] + 2})')
    else:
        win, sub_win, sub_joint = pass2_g2(p, N, center, r1['mins'], do_g3)
        print(f'  G2 bucketing: K=2 digit window above the GLOBAL minima '
              f'{tuple(r1["mins"])} (per-member minima vary — none constant — so '
              f'windows are anchored at the stratum-global minimum, as specced)')
        ok_g2 = report_g2(win, total, pp, f'(joint uniformity, {pp ** 4} nominal buckets)')
        if do_g3:
            g3_data = (sub_win, sub_joint, win)
    return dict(ok_mass=ok_mass, ok_g2=ok_g2, r1=r1, g3=g3_data, total=total, pp=pp)


def report_g3(g3_data, total, pp, p):
    sub_win, sub_joint, full_win = g3_data
    print(f'\n  GATE G3 (sub-strata by the digit of a0/{p ** 2} at height 1) '
          f'— recorded raw, no pre-registered pass condition:')
    joints = {}
    for bit in sorted(sub_win):
        sw = sub_win[bit]
        sizes = Counter(sw.values())
        print(f'    sub-stratum digit={bit}: size {sum(sw.values())}, '
              f'occupied buckets {len(sw)} of {pp ** 4}, '
              f'bucket sizes {dict(sorted(sizes.items()))}')
        # per-coordinate window marginals
        for i, nm in enumerate(COORD_NAMES):
            m = Counter()
            for key, n in sw.items():
                m[key[i]] += n
            uni = len(m) == pp and len(set(m.values())) == 1
            print(f'      {nm} window marginal: {dict(sorted(m.items()))} '
                  f'[{"uniform" if uni else "NON-uniform"}]')
        bad = pairwise_scan(sw, pp)
        if not bad:
            print(f'      pairwise window scan: all 6 coordinate pairs exactly '
                  f'uniform on the {pp}x{pp} grid')
        else:
            print(f'      pairwise window scan: NON-uniform pairs: '
                  f'{[nms for nms, _ in bad]} — tables:')
            for nms, pj in bad:
                print(f'      pair {nms}:')
                print_pair_table(pj, pp)
        joints[bit] = sub_joint[bit]
    bits = sorted(joints)
    if len(bits) == 2 and joints[bits[0]] == joints[bits[1]]:
        print('    restricted G1 v-profile tables: IDENTICAL across the two '
              'sub-strata (hence each is exactly half the full-stratum G1 table):')
        print_joint_table(joints[bits[0]])
    else:
        for bit in bits:
            print(f'    restricted G1 v-profile table, digit={bit}:')
            print_joint_table(joints[bit])
    # bucket-support overlap across the sub-strata (dependence signature)
    if len(bits) == 2:
        s0, s1 = set(sub_win[bits[0]]), set(sub_win[bits[1]])
        print(f'    bucket-support overlap: |digit0-only|={len(s0 - s1)}, '
              f'|digit1-only|={len(s1 - s0)}, |both|={len(s0 & s1)}, '
              f'union covers {len(s0 | s1)} of {pp ** 4}')


# ------------------------------------------------------------------ main

def main(argv):
    quick = '--quick' in argv
    allok = True
    print('=' * 78)
    print('CASE G GATE — the ORDER-INCREMENT move (e=2, mu=2 descend at a deg-1 key')
    print('creating the deg-2 key phi2), n = 4, at p = 2 and p = 3')
    print('=' * 78)

    # ================================================================= p = 2
    print('\n################ p = 2 (center c~ = 1, key phi2 = x^2 - 2) ################')
    print('\nGATE G0a (derive-check) — naive full-box census at N=4, closed-form vs')
    print('independent Newton-polygon/residual-square read, f-by-f over all 2^16:')
    counts, mism = derive_check(2, 4)
    ok = mism == 0
    allok &= ok
    print(f'  mismatches: {mism} [{"OK" if ok else "FAIL"}]; '
          f'independent-read count {dict(counts)} '
          f'(expect {{1: {2 ** (4 * 4 - 8)}}})')
    allok &= counts == Counter({1: 2 ** 8})

    print('\nGATE G0 (mass exactness, nominal 2^-8) — full-box pruned census:')
    for N in range(4, (5 if quick else 6) + 1):
        cnt = census_g0(2, N)[1]
        mass = F(cnt, 2 ** (4 * N))
        ok = mass == F(1, 256)
        allok &= ok
        print(f'  N={N}: count {cnt} of {2 ** (4 * N)}, mass {mass} '
              f'[{"== 2^-8 OK" if ok else "MISMATCH vs 2^-8"}]')

    Nmain2 = 5 if quick else 6
    # secondary-N G2 point (full mode only), compact report
    if not quick:
        res5 = run_instance(2, 5, 1, F(1, 256), do_g3=False, print_g1_table=False)
        allok &= res5['ok_mass'] and bool(res5['ok_g2'])
    res2 = run_instance(2, Nmain2, 1, F(1, 256), do_g3=True, print_g1_table=True)
    allok &= res2['ok_mass'] and bool(res2['ok_g2'])
    if res2['g3'] is not None:
        report_g3(res2['g3'], res2['total'], res2['pp'], 2)

    # ================================================================= p = 3
    print('\n################ p = 3 (centers c~ in {1, 2}, keys x^2-3, x^2-6) ##########')
    print('\nGATE G0a (derive-check) — naive full-box census at N=3, closed-form vs')
    print('independent NP/residual read (incl. center assignment), all 3^12 quartics:')
    counts, mism = derive_check(3, 3)
    ok = mism == 0
    allok &= ok
    exp = 3 ** (4 * 3 - 8)
    print(f'  mismatches: {mism} [{"OK" if ok else "FAIL"}]; '
          f'independent-read per-center counts {dict(sorted(counts.items()))} '
          f'(expect {{1: {exp}, 2: {exp}}})')
    allok &= counts == Counter({1: exp, 2: exp})

    print('\nGATE G0 (mass exactness, nominal 3^-8 PER CENTER — the digit conditions:')
    print('  a3: 1/3; a1: 1/9; a2 digit1 = c~: 1/9; a0 v=2 digit2 = 1: 1/27) —')
    print('full-box pruned census:')
    for N in range(3, (4 if quick else 5) + 1):
        cnts = census_g0(3, N)
        for c in (1, 2):
            mass = F(cnts[c], 3 ** (4 * N))
            ok = mass == F(1, 3 ** 8)
            allok &= ok
            print(f'  N={N} c~={c}: count {cnts[c]} of {3 ** (4 * N)}, mass {mass} '
                  f'[{"== 3^-8 OK" if ok else "MISMATCH vs 3^-8"}]')

    Nmain3 = 4 if quick else 5
    for c in (1, 2):
        res3 = run_instance(3, Nmain3, c, F(1, 3 ** 8), do_g3=False)
        allok &= res3['ok_mass']
        if res3['ok_g2'] is not None:
            allok &= res3['ok_g2']

    print('\n' + '=' * 78)
    print('VERDICT:', 'CASE G GATE PASSES (G0 exact, G2 exactly uniform everywhere '
          'run; G3 recorded)' if allok else
          'CASE G GATE FAILS — see MISMATCH/NON-UNIFORM lines above')
    return 0 if allok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
