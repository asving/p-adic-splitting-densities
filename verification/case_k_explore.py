#!/usr/bin/env python3
"""case_k_explore.py — EXPLORATORY census of the LEVEL-2 INTERIOR of Case K.
RAW DATA ONLY: no pass/fail gates are pre-registered; nothing here is a proof.
(Sibling of case_g2_explore.py, one branch over: here the level-1 side residual is
the SQUARE of the F2-irreducible z^2+z+1, so the level-2 leading digits live in
F4 = F2[zbar]/(zbar^2+zbar+1) and BOTH w1-slots can tie — the F4\\F2 digit cells
are the point of this exploration.  DO NOT COMMIT.)

Setting (n = 4, p = 2, N = 12; all arithmetic mod 2^12 = 4096; v = v_2):
  Case-K parent stratum (level 1): monic quartics f = x^4 + a3 x^3 + a2 x^2 + a1 x + a0
  over Z_2 with Newton-polygon side of slope -1 through (0,4)-(4,0) and side residual
  R(z) = z^4 + z^2 + 1 = (z^2+z+1)^2 over F_2.  Explicitly (digit_{4-i}(a_i) must
  equal the z^i coefficient of R = [1,0,1,0,1]):
    v(a3) >= 2,  v(a2) = 2 EXACT (digit_2(a2) = 1),  v(a1) >= 4,
    v(a0) = 4 EXACT (digit_4(a0) = 1).
  Nominal stratum mass: 2^-14 of the monic-quartic coefficient box (fixed digits
  2+3+4+5 = 14; the uncapped stratum mod 2^12 has 2^(10+9+8+7) = 2^34 members
  = 2^-14 * (2^12)^4).

  Level-2 key: Phi = x^2 + 2x + 4 (the standard lift of psi = z^2+z+1 at slope 1);
  as the monic x^2 - alpha*x - beta: (alpha, beta) = (-2, -4) mod 2^N.
  Phi-development: f = Phi^2 + B1*Phi + B0, deg B_i <= 1, each B_i recorded as its
  (x-coeff, const) pair.

  LEVEL-2 COEFFICIENT WEIGHT (e = 1, h = 1 — plain integer scale, NOT the doubled
  scale of case_g2_explore.py), for B = b1*x + b0:
    w1(B) := min( v(b0), v(b1) + 1 ),  +infinity capped at N = 12.
  LEVEL-2 F4-DIGIT of B at m = w1(B): the pair (eps_x, eps_c) with
    eps_c = digit_m(b0)     if v(b0) = m      else 0,
    eps_x = digit_{m-1}(b1) if v(b1) = m - 1  else 0,
  read as the F4-element eps_x*zbar + eps_c (integer code 2*eps_x + eps_c).
  Below the cap some slot always achieves the min, so the digit 0 is impossible
  there; a 0 reading means both coordinates vanished mod 2^N (cap artifact) and is
  FLAGGED wherever it occurs.  UNLIKE the G2 setting (doubled scale, parity splits
  the slots) both slots CAN tie here (m = v(b0) AND m-1 = v(b1) together), giving
  the genuine F4\\F2 digit zbar+1; the x-slot alone gives zbar.

FREE-DIGIT CAP (stated, per spec): the cap IS NEEDED — the uncapped stratum mod
2^12 has 2^34 members.  Each coefficient keeps its 6 lowest FREE digits:
    a3 = 4*t3, a2 = 4 + 8*t2, a1 = 16*t1, a0 = 16 + 32*s,  t3,t2,t1,s in [0, 2^6)
(digit windows: a3 heights 2..7, a2 heights 3..8, a1 heights 4..9, a0 heights
5..10; forced digits: a2 height 2 = 1, a0 height 4 = 1; all lower digits 0, all
higher free digits 0).  Enumerated members: 2^24 = 16777216; --quick mode uses
cap 4 (2^16).  A full re-census at cap 5 (cap 3 in quick mode) is run and compared
cell-by-cell as a cap-stability record (raw).  Deep tail cells of the tables (large
w1 values) ARE cap-truncation-biased (a coordinate with all capped digits 0 reports
v = N); that bias is recorded, not corrected.

Development closed form (used in the bulk loops for speed; VERIFIED member-by-member
against genuine two-step polynomial division — develop_polydiv, the same two-division
routine as case_g_gate.py / case_g2_explore.py — on (a) the FULL cap-4 stratum x all
6 keys, (b) a stride-4999 slice of the cap-6 stratum x all 6 keys, (c) 500
seeded-random points of the FULL box x all 6 keys; plus reconstruction
f == Phi^2 + B1*Phi + B0 mod 2^N at all the same points.  Additionally the entire
hoisted/histogrammed fast census is compared TABLE-BY-TABLE against a naive
per-member scalar reference census — develop_closed + literal digit reads — on the
full cap-4 stratum):
  dividing f twice by the monic key phi = x^2 - alpha*x - beta gives
    c1 = a3 + alpha,  d2 = a2 + beta + alpha*c1,
    B1 = ( a3 + 2*alpha ,  d2 + beta )                      as (x-coeff, const),
    B0 = ( a1 + beta*c1 + alpha*d2 ,  a0 + beta*d2 )        as (x-coeff, const).
  Base key Phi = x^2 + 2x + 4: (alpha, beta) = (-2, -4).
  Recentered key Phi' = Phi - t, t = tau1*x + tau0, implemented per spec as
    (alpha, beta) = (-2 - tau1, -4 - tau0).

RECENTERING CANDIDATES (three w1 = 3 digit values + two wrong-weight controls):
    t = 8       (w1 = 3, dig = 1)
    t = 4x      (w1 = 3, dig = zbar)
    t = 4x + 8  (w1 = 3, dig = zbar+1)
    t = 4       (w1 = 2, WRONG-WEIGHT control)
    t = 16      (w1 = 4, WRONG-WEIGHT control)

REPORTS (all raw):
 (1) stratum count vs nominal mass sanity; the joint (w1(B1), w1(B0)) distribution
     on the capped stratum (table folded at 14 — trivial here since w1 <= N = 12;
     uncapped marginals also printed).
 (2) on SUB := { w1(B0) = 6 exact AND w1(B1) >= 4 }: the distribution of the
     F4-digit dig(B0) over {1, zbar, zbar+1} (0 should be impossible; FLAGGED if
     seen), plus sanity marginals per cell: the joint with w1(B1) and with dig(B1).
 (3) RECENTERING PROBE on SUB, split BY the F4-digit cell of B0: re-develop f at
     Phi' = Phi - t for each candidate t; per (cell x candidate) the joint
     (w1(B1'), w1(B0')) table, a RISE flag = does w1(B0') >= 8 hold uniformly on
     the cell (the side value is 6; "rise" = the minimum jumped past it), and the
     post-move F4-digit distributions of B0' and B1'.
 (4) member counts and exact masses of every sub-stratum touched (fractions of the
     capped stratum, and absolute box mass via the stratum's nominal mass 2^-14).

Run:  python3 case_k_explore.py            (full: cap 6 + cap-5 stability; ~1-3 min)
      python3 case_k_explore.py --quick    (cap 4 + cap-3 stability; seconds)
"""
import random
import sys
import time
from collections import Counter
from fractions import Fraction as Frac

N = 12                     # working precision: everything mod 2^N
M = 1 << N
MASK = M - 1
WCAP = N                   # +infinity cap for w1 (plain scale; e = 1, h = 1)
NW = N + 1                 # w1 takes values 0..N
TABCAP = 14                # display fold for joint tables (per spec; trivial: w1 <= 12)
NOMINAL_LOG2 = 14          # stratum nominal box mass = 2^-14

DIGNAME = {0: '0(FLAG!)', 1: '1', 2: 'zbar', 3: 'zbar+1'}

BASE_AB = (-2, -4)         # Phi = x^2 + 2x + 4 = x^2 - alpha*x - beta

# recentering candidates: (label, tau1, tau0) with t = tau1*x + tau0
CANDS = [('t = 8', 0, 8),
         ('t = 4x', 4, 0),
         ('t = 4x + 8', 4, 8),
         ('t = 4', 0, 4),         # wrong-weight control (w1(t) = 2)
         ('t = 16', 0, 16)]       # wrong-weight control (w1(t) = 4)
NC = len(CANDS)
# per spec: Phi' = Phi - t is implemented as (alpha, beta) = (-2 - tau1, -4 - tau0)
CAND_AB = [(-2 - tau1, -4 - tau0) for _, tau1, tau0 in CANDS]
ALL_KEYS = [BASE_AB] + CAND_AB


# --------------------------------------------------------------- p-adic helpers

def vp2(x, cap=N):
    """2-adic valuation of the residue x mod 2^cap; v(0) reported as cap."""
    if x == 0:
        return cap
    v = (x & -x).bit_length() - 1
    return v if v < cap else cap


VT = [vp2(x) for x in range(M)]              # valuation table
VTX1 = [min(v + 1, WCAP) for v in VT]        # x-slot weight v+1, capped at N


def w1_pair(bx, bc):
    """w1 of B = bx*x + bc (plain scale, e = 1, h = 1), capped at N."""
    return min(vp2(bc), vp2(bx) + 1, WCAP)


def f4_digit(bx, bc):
    """LITERAL spec digit read at m = w1(B): eps_c = digit_m(bc) if v(bc) = m else 0;
    eps_x = digit_{m-1}(bx) if v(bx) = m-1 else 0.  Returns the integer code
    2*eps_x + eps_c for the F4-element eps_x*zbar + eps_c.  Reads genuine binary
    digits of the residues (so a coordinate == 0 mod 2^N reads digit 0 at the cap)."""
    m = w1_pair(bx, bc)
    eps_c = (bc >> m) & 1 if vp2(bc) == m else 0
    eps_x = (bx >> (m - 1)) & 1 if (m >= 1 and vp2(bx) == m - 1) else 0
    return 2 * eps_x + eps_c


def coeffs(t3, t2, t1, s):
    """Stratum member from the free digits: a3 = 4*t3, a2 = 4 + 8*t2, a1 = 16*t1,
    a0 = 16 + 32*s (all mod 2^N)."""
    return ((4 * t3) & MASK, (4 + 8 * t2) & MASK,
            (16 * t1) & MASK, (16 + 32 * s) & MASK)


def polydiv(f, d, Mod):
    """f, d coefficient lists (low->high), d monic. (q, r) with f = q*d + r mod Mod."""
    f = list(f)
    dd = len(d) - 1
    q = [0] * (len(f) - dd)
    for i in range(len(f) - 1, dd - 1, -1):
        c = f[i] % Mod
        q[i - dd] = c
        for j in range(dd + 1):
            f[i - dd + j] = (f[i - dd + j] - c * d[j]) % Mod
    return q, [x % Mod for x in f[:dd]]


def polymul(A, B, Mod):
    R = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            R[i + j] = (R[i + j] + a * b) % Mod
    return R


def develop_polydiv(coefs, phi, Mod):
    """GENUINE two-division Phi-development (same routine as case_g_gate.develop):
    f = phi^2 + B1*phi + B0; returns ((B1.x, B1.c), (B0.x, B0.c))."""
    c3, c2, c1, c0 = coefs
    q1, r0 = polydiv([c0, c1, c2, c3, 1], phi, Mod)
    q2, r1 = polydiv(q1, phi, Mod)
    assert q2 == [1]
    return (r1[1], r1[0]), (r0[1], r0[0])


def develop_closed(a3, a2, a1, a0, alpha, beta):
    """Closed form of the same development for phi = x^2 - alpha*x - beta (mod 2^N)."""
    c1 = a3 + alpha
    d2 = a2 + beta + alpha * c1
    return ((a3 + 2 * alpha) % M, (d2 + beta) % M), \
           ((a1 + beta * c1 + alpha * d2) % M, (a0 + beta * d2) % M)


# --------------------------------------------------------------- verification

def check_one(f4):
    """closed form == genuine polydiv development, all 6 keys, + reconstruction."""
    a3, a2, a1, a0 = (x % M for x in f4)
    for alpha, beta in ALL_KEYS:
        phi = [(-beta) % M, (-alpha) % M, 1]
        gd = develop_polydiv((a3, a2, a1, a0), phi, M)
        cf = develop_closed(a3, a2, a1, a0, alpha, beta)
        assert gd == cf, ('closed-form mismatch', f4, alpha, beta, gd, cf)
        (b1x, b1c), (b0x, b0c) = cf
        lhs = polymul(phi, phi, M)
        tt = polymul([b1c, b1x], phi, M)
        b0l = (b0c, b0x)
        rec = [(lhs[i] + (tt[i] if i < len(tt) else 0)
                + (b0l[i] if i < 2 else 0)) % M for i in range(5)]
        assert rec == [a0, a1, a2, a3, 1], ('reconstruction failure', f4, alpha, beta)


def verify(capmain):
    """(a) full cap-4 stratum; (b) strided capmain stratum; (c) 500 random box pts."""
    n_a = 0
    Tc = 1 << 4
    for t3 in range(Tc):
        for t2 in range(Tc):
            for t1 in range(Tc):
                for s in range(Tc):
                    check_one(coeffs(t3, t2, t1, s))
                    n_a += 1
    n_b = 0
    T = 1 << capmain
    tot = T ** 4
    for i in range(0, tot, 4999):
        s = i & (T - 1)
        t1 = (i >> capmain) & (T - 1)
        t2 = (i >> (2 * capmain)) & (T - 1)
        t3 = (i >> (3 * capmain)) & (T - 1)
        check_one(coeffs(t3, t2, t1, s))
        n_b += 1
    rng = random.Random(20260725)
    n_c = 0
    for _ in range(500):
        check_one(tuple(rng.randrange(M) for _ in range(4)))
        n_c += 1
    return n_a, n_b, n_c


def verify_digit_formula():
    """LITERAL digit read (f4_digit, genuine binary digits) == the valuation-
    comparison form used inside the fast census, over a structured valuation-
    exhaustive set of pairs + 20000 seeded-random pairs.  Returns #pairs checked."""
    vals = {0}
    for k in range(N):
        for u in (1, 3, 5, (M >> k) - 1 if (M >> k) - 1 > 0 else 1):
            vals.add(((u << k) & MASK) or 0)
    vals = sorted(vals)
    rng = random.Random(20260726)
    pairs = [(bx, bc) for bx in vals for bc in vals]
    pairs += [(rng.randrange(M), rng.randrange(M)) for _ in range(20000)]
    n = 0
    for bx, bc in pairs:
        vx, vc = VT[bx], VT[bc]
        w0 = vc if vc < VTX1[bx] else VTX1[bx]
        dig = 2 * (1 if vx == w0 - 1 else 0) + (1 if (vc == w0 and w0 < N) else 0)
        assert w0 == w1_pair(bx, bc), (bx, bc, w0, w1_pair(bx, bc))
        assert dig == f4_digit(bx, bc), (bx, bc, dig, f4_digit(bx, bc))
        n += 1
    return n


# --------------------------------------------------------------- the census

def blank_tables():
    return dict(joint=[0] * (NW * NW),
                n_sub=0,
                tab_cell=[0] * 4,
                tab_cell_w1b1=[0] * (4 * NW),
                tab_cell_digb1=[0] * 16,
                probe_joint=[[0] * (4 * NW * NW) for _ in range(NC)],
                probe_digs=[[0] * 64 for _ in range(NC)])


def census(capfree):
    """One full pass over the capped stratum (hoisted closed-form fast path;
    the (t1, s)-bulk of the base joint uses a valuation-histogram factorization
    in blocks that cannot meet SUB).  Tables returned:
      joint          flat NW x NW, idx = w1(B1)*NW + w1(B0)      (base development)
      n_sub          |SUB|,  SUB = {w1(B0) = 6 exact & w1(B1) >= 4}
      tab_cell       [4]     counts of SUB by F4-digit code of B0
      tab_cell_w1b1  [4*NW]  idx = cell*NW + w1(B1)              (on SUB)
      tab_cell_digb1 [16]    idx = cell*4 + dig(B1)              (on SUB)
      probe_joint    per candidate, flat 4*NW*NW, idx = cell*NW*NW + w1(B1')*NW + w1(B0')
      probe_digs     per candidate, flat 64, idx = cell*16 + dig(B0')*4 + dig(B1')
      total          (2^capfree)^4."""
    T = 1 << capfree
    r = blank_tables()
    joint = r['joint']
    tab_cell = r['tab_cell']
    tab_cell_w1b1 = r['tab_cell_w1b1']
    tab_cell_digb1 = r['tab_cell_digb1']
    probe_joint = r['probe_joint']
    probe_digs = r['probe_digs']
    n_sub = 0
    vt, vtx1 = VT, VTX1
    alpha_b, beta_b = BASE_AB
    a0_list = [(16 + 32 * s) & MASK for s in range(T)]
    a1_list = [(16 * t1) & MASK for t1 in range(T)]
    crange = range(NC)
    for t3 in range(T):
        a3 = (4 * t3) & MASK
        for t2 in range(T):
            a2 = (4 + 8 * t2) & MASK
            # base development, coefficient level
            c1 = a3 + alpha_b
            d2 = a2 + beta_b + alpha_b * c1
            b1x = (a3 + 2 * alpha_b) & MASK
            b1c = (d2 + beta_b) & MASK
            vb1x, vb1c = vt[b1x], vt[b1c]
            w1b1 = vb1c if vb1c < vtx1[b1x] else vtx1[b1x]
            jrow = w1b1 * NW
            kx_b = (beta_b * c1 + alpha_b * d2) & MASK
            kc_b = (beta_b * d2) & MASK
            vc_b = [vt[(a0s + kc_b) & MASK] for a0s in a0_list]
            if w1b1 >= 4:
                # this block can meet SUB: plain (t1, s) loop with probe hoists
                digb1 = 2 * (1 if vb1x == w1b1 - 1 else 0) \
                    + (1 if (vb1c == w1b1 and w1b1 < N) else 0)
                cst = []
                for alpha_c, beta_c in CAND_AB:
                    c1p = a3 + alpha_c
                    d2p = a2 + beta_c + alpha_c * c1p
                    b1xp = (a3 + 2 * alpha_c) & MASK
                    b1cp = (d2p + beta_c) & MASK
                    w1b1p = vt[b1cp] if vt[b1cp] < vtx1[b1xp] else vtx1[b1xp]
                    digb1p = 2 * (1 if vt[b1xp] == w1b1p - 1 else 0) \
                        + (1 if (vt[b1cp] == w1b1p and w1b1p < N) else 0)
                    kxp = (beta_c * c1p + alpha_c * d2p) & MASK
                    kcp = (beta_c * d2p) & MASK
                    vcp_l = [vt[(a0s + kcp) & MASK] for a0s in a0_list]
                    cst.append((kxp, vcp_l, w1b1p * NW, digb1p))
                for t1 in range(T):
                    a1t = a1_list[t1]
                    b0x = (a1t + kx_b) & MASK
                    vx, vx1 = vt[b0x], vtx1[b0x]
                    cst1 = [(vt[(a1t + kxp) & MASK], vtx1[(a1t + kxp) & MASK],
                             vcp_l, rowp, digb1p)
                            for (kxp, vcp_l, rowp, digb1p) in cst]
                    for s in range(T):
                        vc = vc_b[s]
                        w0 = vc if vc < vx1 else vx1
                        joint[jrow + w0] += 1
                        if w0 == 6:
                            n_sub += 1
                            cell = 2 * (1 if vx == 5 else 0) + (1 if vc == 6 else 0)
                            tab_cell[cell] += 1
                            tab_cell_w1b1[cell * NW + w1b1] += 1
                            tab_cell_digb1[cell * 4 + digb1] += 1
                            coff = cell * (NW * NW)
                            coffd = cell * 16
                            for ci in crange:
                                vxp, vxp1, vcp_l, rowp, digb1p = cst1[ci]
                                vcp = vcp_l[s]
                                w0p = vcp if vcp < vxp1 else vxp1
                                digp = 2 * (1 if vxp == w0p - 1 else 0) \
                                    + (1 if (vcp == w0p and w0p < N) else 0)
                                probe_joint[ci][coff + rowp + w0p] += 1
                                probe_digs[ci][coffd + digp * 4 + digb1p] += 1
            else:
                # SUB is unreachable here (needs w1(B1) >= 4): histogram trick
                hc = [0] * NW
                for v in vc_b:
                    hc[v] += 1
                hx = [0] * NW
                for a1t in a1_list:
                    hx[vtx1[(a1t + kx_b) & MASK]] += 1
                for vxv in range(NW):
                    nx = hx[vxv]
                    if nx:
                        for vcv in range(NW):
                            nc = hc[vcv]
                            if nc:
                                joint[jrow + (vcv if vcv < vxv else vxv)] += nx * nc
    r['n_sub'] = n_sub
    r['total'] = T ** 4
    return r


def census_reference(capfree):
    """NAIVE per-member scalar census: develop_closed on every member for the base
    key and (on SUB) all 5 candidates; weights via w1_pair, digits via the LITERAL
    f4_digit (genuine binary digit reads).  Same table set as census(); used to
    verify the fast path table-by-table."""
    T = 1 << capfree
    r = blank_tables()
    joint = r['joint']
    n_sub = 0
    for t3 in range(T):
        for t2 in range(T):
            for t1 in range(T):
                for s in range(T):
                    f = coeffs(t3, t2, t1, s)
                    (b1x, b1c), (b0x, b0c) = develop_closed(*f, *BASE_AB)
                    w1 = w1_pair(b1x, b1c)
                    w0 = w1_pair(b0x, b0c)
                    joint[w1 * NW + w0] += 1
                    if w0 == 6 and w1 >= 4:
                        n_sub += 1
                        d0 = f4_digit(b0x, b0c)
                        d1 = f4_digit(b1x, b1c)
                        r['tab_cell'][d0] += 1
                        r['tab_cell_w1b1'][d0 * NW + w1] += 1
                        r['tab_cell_digb1'][d0 * 4 + d1] += 1
                        for ci, ab in enumerate(CAND_AB):
                            (c1x, c1c), (c0x, c0c) = develop_closed(*f, *ab)
                            w1p = w1_pair(c1x, c1c)
                            w0p = w1_pair(c0x, c0c)
                            r['probe_joint'][ci][d0 * (NW * NW) + w1p * NW + w0p] += 1
                            r['probe_digs'][ci][d0 * 16 + f4_digit(c0x, c0c) * 4
                                                + f4_digit(c1x, c1c)] += 1
    r['n_sub'] = n_sub
    r['total'] = T ** 4
    return r


def compare_census(ra, rb):
    """Exact table-by-table comparison; returns list of mismatching field names."""
    bad = []
    for k in ('total', 'n_sub', 'joint', 'tab_cell', 'tab_cell_w1b1',
              'tab_cell_digb1'):
        if ra[k] != rb[k]:
            bad.append(k)
    for k in ('probe_joint', 'probe_digs'):
        for ci in range(NC):
            if ra[k][ci] != rb[k][ci]:
                bad.append(f'{k}[{ci}]')
    return bad


# --------------------------------------------------------------- reporting

def lab(v):
    return f'>={TABCAP}' if v == TABCAP else str(v)


def fold_joint(tbl):
    d = Counter()
    for r in range(NW):
        base = r * NW
        for c in range(NW):
            n = tbl[base + c]
            if n:
                d[(min(r, TABCAP), min(c, TABCAP))] += n
    return d


def print_joint(tbl, rowname, colname, indent='    '):
    d = fold_joint(tbl)
    if not d:
        print(indent + '(empty)')
        return
    rows = sorted({r for r, _ in d})
    cols = sorted({c for _, c in d})
    print(f'{indent}rows = {rowname} (down); cols = {colname} (across); '
          f'entries = member counts; fold at {TABCAP} (trivial: w1 <= {N})')
    print(indent + ' ' * 6 + ''.join(f'{lab(c):>9}' for c in cols))
    for r in rows:
        print(indent + f'{lab(r):<6}'
              + ''.join(f'{d.get((r, c), 0):>9}' for c in cols))


def marg(tbl, axis):
    m = Counter()
    for r in range(NW):
        for c in range(NW):
            n = tbl[r * NW + c]
            if n:
                m[(r, c)[axis]] += n
    return dict(sorted(m.items()))


def mass_str(cnt, total):
    fr = Frac(cnt, total)
    ab = fr * Frac(1, 1 << NOMINAL_LOG2)
    def p2(x):
        return (x.numerator == 1 and (x.denominator & (x.denominator - 1)) == 0)
    tail = f' = 2^-{ab.denominator.bit_length() - 1}' if ab != 0 and p2(ab) else ''
    return (f'count {cnt}; fraction of capped stratum {fr}; '
            f'absolute box mass {fr} * 2^-{NOMINAL_LOG2} = {ab}{tail}')


def digs_marg(digs16):
    """(dig(B0') marginal, dig(B1') marginal) of a flat 16 cell block."""
    d0 = {DIGNAME[d]: sum(digs16[d * 4:(d + 1) * 4]) for d in range(4)
          if sum(digs16[d * 4:(d + 1) * 4])}
    d1 = {DIGNAME[d]: sum(digs16[d::4]) for d in range(4) if sum(digs16[d::4])}
    return d0, d1


def probe_cell_stats(r, cell, ci):
    """(min, max, ge8, tot) of the w1(B0') marginal on SUB-cell `cell`, cand ci."""
    tbl = r['probe_joint'][ci][cell * NW * NW:(cell + 1) * NW * NW]
    m0 = marg(tbl, 1)
    if not m0:
        return None
    tot = sum(m0.values())
    return min(m0), max(m0), sum(n for w, n in m0.items() if w >= 8), tot


def report_probe_cell(r, cell, count):
    for ci, (labl, tau1, tau0) in enumerate(CANDS):
        tbl = r['probe_joint'][ci][cell * NW * NW:(cell + 1) * NW * NW]
        tot = sum(tbl)
        assert tot == count, (cell, labl, tot, count)
        print(f'\n    candidate {labl:10s} (w1(t) = {w1_pair(tau1, tau0)}, '
              f'dig(t) = {DIGNAME[f4_digit(tau1, tau0)]}):')
        print_joint(tbl, "w1(B1')", "w1(B0')", indent='      ')
        m0 = marg(tbl, 1)
        mn, mx = min(m0), max(m0)
        ge8 = sum(n for w, n in m0.items() if w >= 8)
        print(f"      w1(B0') marginal: {m0}")
        print(f"      w1(B0') attained min {mn}, max {mx}; fraction >= 8: "
              f"{ge8}/{tot} = {Frac(ge8, tot) if tot else '-'}")
        print(f"      RISE FLAG (w1(B0') >= 8 uniformly on the cell): "
              f"{'YES' if mn >= 8 else 'no'}")
        d0m, d1m = digs_marg(r['probe_digs'][ci][cell * 16:(cell + 1) * 16])
        print(f"      post-move dig(B0') distribution: {d0m}")
        print(f"      post-move dig(B1') distribution: {d1m}")


# --------------------------------------------------------------- main

def main(argv):
    quick = '--quick' in argv
    capmain, capchk = (4, 3) if quick else (6, 5)
    t_start = time.time()
    print('=' * 78)
    print('CASE K EXPLORE — LEVEL-2 INTERIOR of Case K (n = 4, p = 2) — RAW CENSUS')
    print('=' * 78)
    print(f'N = {N} (all arithmetic mod 2^{N} = {M}); '
          f'w1(b1*x + b0) = min(v2(b0), v2(b1)+1), inf-capped at N = {WCAP} '
          f'(plain scale, e = 1, h = 1).')
    print('Stratum (level-1 Case K): v(a3)>=2, v(a2)=2 exact (digit_2 = 1), '
          'v(a1)>=4, v(a0)=4 exact (digit_4 = 1)')
    print('  [side residual R(z) = z^4 + z^2 + 1 = (z^2+z+1)^2 on the slope -1 '
          'side (0,4)-(4,0)].')
    print('Level-2 key Phi = x^2 + 2x + 4, i.e. (alpha, beta) = (-2, -4); '
          'development f = Phi^2 + B1*Phi + B0.')
    print(f'FREE-DIGIT CAP: {capmain} free digits per coefficient '
          f'(NEEDED: uncapped stratum mod 2^{N} has 2^34 members).')
    print(f'  a3 = 4*t3, a2 = 4 + 8*t2, a1 = 16*t1, a0 = 16 + 32*s;  '
          f't3,t2,t1,s in [0, 2^{capmain})  ->  2^{4 * capmain} members.')
    print("\nRecentering candidates (Phi' = Phi - t, per spec "
          "(alpha, beta) = (-2 - tau1, -4 - tau0)):")
    for (labl, tau1, tau0), (alpha, beta) in zip(CANDS, CAND_AB):
        print(f'  {labl:10s}: w1(t) = {w1_pair(tau1, tau0)}, '
              f'dig(t) = {DIGNAME[f4_digit(tau1, tau0)]:7s};   '
              f"Phi' = x^2 - ({alpha})*x - ({beta})")

    print('\nVERIFICATION (closed-form development == genuine two-step polydiv, '
          'all 6 keys,\n  + reconstruction f == Phi^2 + B1*Phi + B0 mod 2^N):')
    n_a, n_b, n_c = verify(capmain)
    print(f'  (a) FULL cap-4 stratum: {n_a} members x 6 keys — all OK')
    print(f'  (b) stride-4999 slice of the cap-{capmain} stratum: {n_b} members '
          f'x 6 keys — all OK')
    print(f'  (c) 500 seeded-random points of the full box: {n_c} members '
          f'x 6 keys — all OK')
    n_d = verify_digit_formula()
    print(f'  (d) literal F4-digit read == valuation-comparison form (census '
          f'internal): {n_d} pairs — all OK')
    print('  (e) fast census == naive per-member scalar reference census '
          '(develop_closed +\n      literal digit reads), FULL cap-4 stratum, '
          'table-by-table: ', end='', flush=True)
    r_fast4 = census(4)
    r_ref4 = census_reference(4)
    bad = compare_census(r_fast4, r_ref4)
    assert not bad, ('fast/reference census mismatch', bad)
    print('ALL TABLES EQUAL — OK')

    print(f'\nMain census at cap {capmain} ...', flush=True)
    t_c = time.time()
    r = census(capmain) if capmain != 4 else r_fast4
    total = r['total']
    joint = r['joint']
    assert sum(joint) == total
    # internal consistency: SUB count vs the joint-table column 6, rows >= 4
    chk = sum(joint[w1 * NW + 6] for w1 in range(4, NW))
    assert chk == r['n_sub'] == sum(r['tab_cell']), (chk, r['n_sub'])
    print(f'  done in {time.time() - t_c:.1f}s; {total} members; SUB count '
          f'consistent with the joint table (col 6, rows >= 4: {chk})')

    # ---------------- (1)
    print('\n' + '-' * 78)
    print('(1) STRATUM COUNT vs NOMINAL MASS SANITY, and the joint '
          '(w1(B1), w1(B0)) table:')
    print(f'  enumerated members: 2^{4 * capmain} = {total} '
          f'(= 4 coefficients x {capmain} free digits).')
    print(f'  uncapped stratum mod 2^{N}: 2^(10+9+8+7) = 2^34 = {1 << 34} members; '
          f'capped/uncapped = 2^-{34 - 4 * capmain}.')
    print(f'  nominal stratum mass: 2^34 / 2^{4 * N} = 2^-{NOMINAL_LOG2} '
          f'= {Frac(1, 1 << NOMINAL_LOG2)} of the monic-quartic box '
          f'(fixed digits 2+3+4+5 = 14).')
    print_joint(joint, 'w1(B1)', 'w1(B0)', indent='  ')
    print(f'  w1(B1) marginal (uncapped): {marg(joint, 0)}')
    print(f'  w1(B0) marginal (uncapped): {marg(joint, 1)}')

    # ---------------- (2)
    print('\n' + '-' * 78)
    n_sub = r['n_sub']
    print('(2) SUB := {w1(B0) = 6 exact AND w1(B1) >= 4}: F4-digit distribution '
          f'of B0 ({n_sub} members):')
    print('    dig(B0) read at m = 6: eps_c = digit_6(B0.c) if v(B0.c) = 6, '
          'eps_x = digit_5(B0.x) if v(B0.x) = 5.')
    for d in range(4):
        cnt = r['tab_cell'][d]
        if d == 0:
            note = ('  <-- FLAG: digit 0 occurred!' if cnt else
                    '  (0 is impossible below the cap: none seen, as expected)')
        else:
            note = ''
        print(f'    dig(B0) = {DIGNAME[d]:8s}: {mass_str(cnt, total)}{note}')
    print('\n  sanity marginal A — joint (dig(B0) cell) x w1(B1) on SUB '
          '(counts, then per-cell conditional fractions):')
    w1vals = sorted({w for c in range(4) for w in range(NW)
                     if r['tab_cell_w1b1'][c * NW + w]})
    print('    ' + f'{"cell":<10}' + ''.join(f'{lab(w):>10}' for w in w1vals))
    for c in range(4):
        row = [r['tab_cell_w1b1'][c * NW + w] for w in w1vals]
        if sum(row) == 0:
            continue
        print('    ' + f'{DIGNAME[c]:<10}' + ''.join(f'{n:>10}' for n in row))
        fr = [str(Frac(n, sum(row))) for n in row]
        print('    ' + ' ' * 10 + ''.join(f'{f:>10}' for f in fr))
    print('\n  sanity marginal B — joint (dig(B0) cell) x dig(B1) on SUB '
          '(counts, then per-cell conditional fractions):')
    d1vals = [d for d in range(4) if any(r['tab_cell_digb1'][c * 4 + d]
                                         for c in range(4))]
    print('    ' + f'{"cell":<10}'
          + ''.join(f'{DIGNAME[d]:>10}' for d in d1vals))
    for c in range(4):
        row = [r['tab_cell_digb1'][c * 4 + d] for d in d1vals]
        if sum(row) == 0:
            continue
        print('    ' + f'{DIGNAME[c]:<10}' + ''.join(f'{n:>10}' for n in row))
        fr = [str(Frac(n, sum(row))) for n in row]
        print('    ' + ' ' * 10 + ''.join(f'{f:>10}' for f in fr))

    # ---------------- (3)
    print('\n' + '-' * 78)
    print('(3) RECENTERING PROBE on SUB, split BY the F4-digit cell of B0:')
    print("    re-development at Phi' = Phi - t, per spec "
          "(alpha, beta) = (-2 - tau1, -4 - tau0);")
    print("    RISE flag = w1(B0') >= 8 uniformly on the cell "
          "(side value 6; rise = min jumped past it).")
    cells_present = [d for d in range(4) if r['tab_cell'][d]]
    for cell in cells_present:
        print(f'\n  CELL dig(B0) = {DIGNAME[cell]}  '
              f'({r["tab_cell"][cell]} members):')
        report_probe_cell(r, cell, r['tab_cell'][cell])
    print('\n  RISE SUMMARY (rows = dig(B0) cell, cols = candidate; entry = '
          "flag with min..max of w1(B0')):")
    hdr = '    ' + f'{"cell":<10}' + ''.join(f'{labl:>16}'
                                             for labl, _, _ in CANDS)
    print(hdr)
    for cell in cells_present:
        ents = []
        for ci in range(NC):
            st = probe_cell_stats(r, cell, ci)
            mn, mx, ge8, tot = st
            ents.append(f'{"RISE" if mn >= 8 else "no":>4s} {mn}..{mx}')
        print('    ' + f'{DIGNAME[cell]:<10}' + ''.join(f'{e:>16}' for e in ents))

    # ---------------- (4)
    print('\n' + '-' * 78)
    print(f'(4) MEMBER COUNTS AND EXACT MASSES (capped stratum total '
          f'2^{4 * capmain} = {total}; stratum nominal box mass '
          f'2^-{NOMINAL_LOG2}):')
    print(f'  full capped stratum: {mass_str(total, total)}')
    for w0v, cnt in marg(joint, 1).items():
        print(f'  {{w1(B0) = {w0v}}}: {mass_str(cnt, total)}')
    print(f'  SUB {{w1(B0)=6 exact & w1(B1)>=4}}: {mass_str(n_sub, total)}')
    for d in range(4):
        if r['tab_cell'][d]:
            print(f'  SUB cell dig(B0) = {DIGNAME[d]:8s}: '
                  f'{mass_str(r["tab_cell"][d], total)}')

    # ---------------- cap-stability record
    print('\n' + '-' * 78)
    print(f'CAP-STABILITY RECORD (full re-census at cap {capchk}; scale factor '
          f'{(1 << (capmain - capchk)) ** 4} per cell):')
    r2 = census(capchk)
    total2 = r2['total']
    scale = total // total2
    same_sub = Frac(r['n_sub'], total) == Frac(r2['n_sub'], total2)
    print(f'  SUB fraction: cap{capmain} {Frac(r["n_sub"], total)} vs '
          f'cap{capchk} {Frac(r2["n_sub"], total2)}  '
          f'[{"EQUAL" if same_sub else "DIFFERENT"}]')
    for d in range(4):
        c1, c2 = r['tab_cell'][d], r2['tab_cell'][d]
        if c1 == 0 and c2 == 0:
            continue
        same = Frac(c1, total) == Frac(c2, total2)
        print(f'  SUB cell {DIGNAME[d]:8s} fraction: cap{capmain} '
              f'{Frac(c1, total)} vs cap{capchk} {Frac(c2, total2)}  '
              f'[{"EQUAL" if same else "DIFFERENT"}]')
    diffs = [(i // NW, i % NW, joint[i], scale * r2['joint'][i])
             for i in range(NW * NW) if joint[i] != scale * r2['joint'][i]]
    if diffs:
        mm = sum(abs(a - b) for _, _, a, b in diffs)
        print(f'  joint-table cells with cap{capmain} != {scale} * cap{capchk}: '
              f'{len(diffs)} cells; min w1(B1) among them '
              f'{min(d[0] for d in diffs)}, min w1(B0) among them '
              f'{min(d[1] for d in diffs)}; total |count diff| {mm} '
              f'(cap-truncation tail, recorded raw)')
    else:
        print('  joint-table cells: ALL cells scale exactly')
    for ci, (labl, _, _) in enumerate(CANDS):
        ta, tb = r['probe_joint'][ci], r2['probe_joint'][ci]
        nd = sum(1 for i in range(4 * NW * NW) if ta[i] != scale * tb[i])
        da, db = r['probe_digs'][ci], r2['probe_digs'][ci]
        ndd = sum(1 for i in range(64) if da[i] != scale * db[i])
        flags = []
        for cell in range(4):
            sa = probe_cell_stats(r, cell, ci)
            sb = probe_cell_stats(r2, cell, ci)
            if sa is None and sb is None:
                continue
            fa = 'YES' if (sa and sa[0] >= 8) else 'no'
            fb = 'YES' if (sb and sb[0] >= 8) else 'no'
            flags.append(f'{DIGNAME[cell]}:{fa}/{fb}')
        print(f'  probe candidate {labl:10s}: joint cells with cap{capmain} != '
              f'{scale} * cap{capchk}: {nd:3d}; dig cells: {ndd:2d}; '
              f'RISE flags cap{capmain}/cap{capchk}: {", ".join(flags)}')

    print(f'\ntotal wall time {time.time() - t_start:.1f}s')
    print('END OF RAW CENSUS (exploratory; no verdicts).')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
