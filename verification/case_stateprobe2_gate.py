#!/usr/bin/env python3
"""case_stateprobe2_gate.py — STATE-probe-2 SEALED GATE (n = 6, vtx-VARYING).

Spec: lean/notes/ASSEMBLY_PLAN_2026-07-26.md §4 STATE-probe-2 (blocks the
[2b] and [3] acceptance events).  Seal: CASE_STATEPROBE2_SEALED_PREDICTIONS.md
(P1-P6; written BEFORE this census ran).  Tests M2(ii) = CTS-M(iv)-REP: two
concrete states of one CTS type (same VAL.1 vtx-stratum; vtx VALUE, retained
r, loop position h' varying) must have IDENTICAL full outgoing one-step laws.

Configuration (derived in the seal doc §1): p = 2, monic sextics, root Newton
side slope 1 with residual R0 = psi^2*chi, psi = z^2+z+1, chi in
{z^2+z, z^2+1, z^2} -> vtx = chi(alpha) in {1, alpha, alpha^2}.  12 RS
self-loop states S(vtx, r, h'), each an exact coordinate cylinder of size
2^27 in the Phi1-frame (Q-coordinates); one-step word read in the recentered
Phi2-frame.  15 exhaustive boxes: 3 nu1 root boxes (N = 9, a-coords,
independent dictionary layer) + 9 h'=1 states (N = 10) + 3 h'=2 states
(N = 11).  Exact integer arithmetic throughout (numpy uint32 masked mod 2^N;
products < 2^22); literal pure-Python long-division cross-checks per box.
No sampling in any verdict row.

Run:  python3 case_stateprobe2_gate.py
      long output -> /tmp/stateprobe2_census.out
      histograms + verdict -> results/case_stateprobe2_results.json
"""
import json
import os
import random
import sys
import time
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUTTXT = '/tmp/stateprobe2_census.out'
OUTJSON = os.path.join(HERE, 'results', 'case_stateprobe2_results.json')
NPROC = 12
INNER = 20                      # vectorized inner bits per task (2^20 members)
OUTERB = 7                      # outer bits -> 128 tasks per box

# ---------- F_4 tables (code = 2*eps_x + eps_c; alpha = code 2) ----------
def f4_mul(a, b):
    c1, x1, c2, x2 = a & 1, a >> 1, b & 1, b >> 1
    return ((c1 * c2 + x1 * x2) & 1) + 2 * ((c1 * x2 + x1 * c2 + x1 * x2) & 1)

F4_SQ = [f4_mul(t, t) for t in range(4)]            # sq = sqrt on F_4
F4_CONJ = [0, 1, 3, 2]                              # Frobenius t -> t^2 relabel

# ---------- the three chi strata: chi = z^2 + c1 z + c0, vtx = chi(alpha) ----
# vtx = (c1+1)*alpha + (c0+1)  (seal doc §1).  Residues r_i of R0 = psi^2*chi.
def gf2_mul(A, B):
    R = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            R[i + j] ^= a & b
    return R

PSI2 = gf2_mul([1, 1, 1], [1, 1, 1])                # psi^2 = z^4+z^2+1
CHIS = {}                                           # vtx code -> (c1, c0, name, R0 residues r_0..r_5)
for (c1, c0, name) in ((1, 0, 'z^2+z'), (0, 1, 'z^2+1'), (0, 0, 'z^2')):
    vtx = 2 * ((c1 + 1) & 1) + ((c0 + 1) & 1)
    R0 = gf2_mul(PSI2, [c0, c1, 1])                 # degree 6, R0[6] = 1
    assert len(R0) == 7 and R0[6] == 1
    CHIS[vtx] = (c1, c0, name, R0[:6])
assert sorted(CHIS) == [1, 2, 3]                    # vtx = 1, alpha, alpha^2

def vtx_bits(vtx):
    return vtx & 1, vtx >> 1                        # (eps_c, eps_x)

# ---------- box specs ----------
# Streams indexed 0..5 = q0c, q0x, q1c, q1x, q2c, q2x (state boxes, Q-coords)
# or u0..u5 (nu1 boxes, a-coords).  Each box: N, base values, inner/outer
# bit-segment lists (stream, idx_shift, nbits, bit_shift), plus reading spec.
def state_box(vtx, r, hp):
    """RS self-loop state S(vtx, r, h'); seal doc §1 pinning."""
    N = 10 if hp == 1 else 11
    d0 = f4_mul(vtx, F4_SQ[r])                      # d0 = vtx * r^2
    d0c, d0x = d0 & 1, d0 >> 1
    vc, vx = vtx_bits(vtx)
    m = 2 + hp                                      # recenter weight = side slope
    rc, rx = r & 1, r >> 1
    c1p = (2 - (rx << (m - 1))) % (1 << N)          # Phi2 = x^2 + c1p x + c0p
    c0p = (4 - (rc << m)) % (1 << N)
    if hp == 1:
        base = {'q0c': d0c << 8, 'q0x': d0x << 7, 'q1c': 0, 'q1x': 0,
                'q2c': vc << 2, 'q2x': vx << 1}
        inner = [('q2c', 0, 7, 3), ('q2x', 7, 8, 2),
                 ('q1c', 15, 4, 6), ('q0c', 19, 1, 9)]
        outer = [('q1x', 0, 5, 5), ('q0x', 5, 2, 8)]
    else:
        base = {'q0c': d0c << 10, 'q0x': d0x << 9, 'q1c': 0, 'q1x': 0,
                'q2c': vc << 2, 'q2x': vx << 1}
        inner = [('q2c', 0, 8, 3), ('q2x', 8, 9, 2), ('q1c', 17, 3, 7)]
        outer = [('q1c', 0, 1, 10), ('q1x', 1, 5, 6), ('q0x', 6, 1, 10)]
    assert sum(s[2] for s in inner) == INNER and sum(s[2] for s in outer) == OUTERB
    return dict(kind='state', name='S(v=%d,r=%d,h%d)' % (vtx, r, hp),
                vtx=vtx, r=r, hp=hp, N=N, base=base, inner=inner, outer=outer,
                c1p=c1p, c0p=c0p, ncells=1024 if hp == 1 else 256)

def nu1_box(vtx):
    """The chi(vtx) root stratum, a-coordinates, N = 9 (seal doc P4)."""
    c1, c0, name, R = CHIS[vtx]
    # a_i = 2^(6-i)*r_i + 2^(7-i)*u_i, u_i free over N-7+i = 2+i bits.
    base = {'u%d' % i: R[i] for i in range(6)}      # residue r_i stored in base
    inner = [('u5', 0, 7, 0), ('u4', 7, 6, 0), ('u3', 13, 5, 0), ('u0', 18, 2, 0)]
    outer = [('u1', 0, 3, 0), ('u2', 3, 4, 0)]
    assert sum(s[2] for s in inner) == INNER and sum(s[2] for s in outer) == OUTERB
    return dict(kind='nu1', name='NU1(chi=%s,v=%d)' % (name, vtx), vtx=vtx,
                N=9, base=base, inner=inner, outer=outer, ncells=64)

BOXES = ([nu1_box(v) for v in (1, 2, 3)]
         + [state_box(v, r, 1) for v in (1, 2, 3) for r in (1, 2, 3)]
         + [state_box(v, 1, 2) for v in (1, 2, 3)])
assert len(BOXES) == 15

# ---------- vectorized assembly ----------
def assemble(box, outer_val, idx):
    """Return stream arrays (uint32) for the 2^INNER inner members."""
    vals = {}
    for st in box['base']:
        vals[st] = np.full(idx.shape, box['base'][st] if box['kind'] == 'state'
                           else 0, dtype=np.uint32)
    if box['kind'] == 'nu1':
        for st in vals:
            vals[st][:] = 0
    for (st, sh, nb, bs) in box['inner']:
        vals[st] |= ((idx >> np.uint32(sh)) & np.uint32((1 << nb) - 1)) << np.uint32(bs)
    for (st, sh, nb, bs) in box['outer']:
        vals[st] |= np.uint32(((outer_val >> sh) & ((1 << nb) - 1)) << bs)
    return vals

def a_from_q(q0c, q0x, q1c, q1x, q2c, q2x, mask):
    """f = Phi1^3 + Q2 Phi1^2 + Q1 Phi1 + Q0 -> x-coefficients a0..a5 (a6=1).
    Phi1 = x^2+2x+4; Phi1^2 = x^4+4x^3+12x^2+16x+16;
    Phi1^3 = x^6+6x^5+24x^4+56x^3+96x^2+96x+64."""
    a5 = (6 + q2x) & mask
    a4 = (24 + 4 * q2x + q2c) & mask
    a3 = (56 + 12 * q2x + 4 * q2c + q1x) & mask
    a2 = (96 + 16 * q2x + 12 * q2c + 2 * q1x + q1c) & mask
    a1 = (96 + 16 * q2x + 16 * q2c + 4 * q1x + 2 * q1c + q0x) & mask
    a0 = (64 + 16 * q2c + 4 * q1c + q0c) & mask
    return a0, a1, a2, a3, a4, a5

def a_from_u(box, vals, mask):
    """nu1 box: a_i = 2^(6-i)*r_i + 2^(7-i)*u_i mod 2^9."""
    R = [CHIS[box['vtx']][3][i] for i in range(6)]
    a = []
    for i in range(6):
        a.append(((R[i] << (6 - i)) + (vals['u%d' % i] << np.uint32(7 - i))) & mask)
    return tuple(a)

def div_chain(a0, a1, a2, a3, a4, a5, c1, c0, mask):
    """Two exact divisions of monic sextic by monic x^2+c1x+c0 mod 2^N.
    Returns Q0'=(r0c,r1x), Q1'=(s0c,s1x), Q2'=(t2c,t2x); Q3'=1."""
    q3 = (a5 - c1) & mask
    q2 = (a4 - c1 * q3 - c0) & mask
    q1 = (a3 - c1 * q2 - c0 * q3) & mask
    q0 = (a2 - c1 * q1 - c0 * q2) & mask
    r1x = (a1 - c1 * q0 - c0 * q1) & mask
    r0c = (a0 - c0 * q0) & mask
    p1 = (q3 - c1) & mask
    p0 = (q2 - c1 * p1 - c0) & mask
    s1x = (q1 - c1 * p0 - c0 * p1) & mask
    s0c = (q0 - c0 * p0) & mask
    t2c = (p0 - c0) & mask
    t2x = (p1 - c1) & mask
    return r0c, r1x, s0c, s1x, t2c, t2x

def dig(bc, bx, m):
    """F_4 digit at weight m: (bit_{m-1} of bx)*alpha + (bit_m of bc)."""
    return (((bx >> np.uint32(m - 1)) & 1) << 1) | ((bc >> np.uint32(m)) & 1)

def task(args):
    """One (box_index, outer_val) slice: 2^INNER members, exact."""
    bi, outer_val = args
    box = BOXES[bi]
    mask = np.uint32((1 << box['N']) - 1)
    idx = np.arange(1 << INNER, dtype=np.uint32)
    vals = assemble(box, outer_val, idx)
    if box['kind'] == 'nu1':
        a = a_from_u(box, vals, mask)
        r0c, r1x, s0c, s1x, t2c, t2x = div_chain(*a, np.uint32(2), np.uint32(4), mask)
        viol = int(np.count_nonzero((r0c & 0x7F) | (r1x & 0x3F)
                                    | (s0c & 0x1F) | (s1x & 0xF)))
        vbad = int(np.count_nonzero((t2c & 3) | (t2x & 1)
                                    | (dig(t2c, t2x, 2) != box['vtx'])))
        word = (dig(s0c, s1x, 5) | (dig(r0c, r1x, 7) << 2)
                | (dig(r0c, r1x, 8) << 4))
    else:
        a = a_from_q(vals['q0c'], vals['q0x'], vals['q1c'], vals['q1x'],
                     vals['q2c'], vals['q2x'], mask)
        r0c, r1x, s0c, s1x, t2c, t2x = div_chain(
            *a, np.uint32(box['c1p']), np.uint32(box['c0p']), mask)
        if box['hp'] == 1:
            viol = int(np.count_nonzero((s0c & 0x3F) | (s1x & 0x1F)
                                        | (r0c & 0x1FF) | (r1x & 0xFF)))
            word = (dig(s0c, s1x, 6) | (dig(s0c, s1x, 7) << 2)
                    | (dig(s0c, s1x, 8) << 4) | (dig(s0c, s1x, 9) << 6)
                    | (dig(r0c, r1x, 9) << 8))
        else:
            viol = int(np.count_nonzero((s0c & 0x7F) | (s1x & 0x3F)
                                        | r0c | (r1x & 0x3FF)))
            word = (dig(s0c, s1x, 7) | (dig(s0c, s1x, 8) << 2)
                    | (dig(s0c, s1x, 9) << 4) | (dig(s0c, s1x, 10) << 6))
        vbad = int(np.count_nonzero((t2c & 3) | (t2x & 1)
                                    | (dig(t2c, t2x, 2) != box['vtx'])))
    hist = np.bincount(word, minlength=box['ncells']).astype(np.int64)
    return bi, hist, viol, vbad

# ---------- literal pure-Python verification layer (independent path) ----------
def polymul(A, B, mod):
    R = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            R[i + j] = (R[i + j] + a * b) % mod
    return R

def polyadd(A, B, mod):
    R = [0] * max(len(A), len(B))
    for i, a in enumerate(A):
        R[i] = a % mod
    for i, b in enumerate(B):
        R[i] = (R[i] + b) % mod
    return R

def polydiv(f, d, mod):
    """Literal long division by monic d (low->high lists); (quotient, rem)."""
    f = [x % mod for x in f]
    dd = len(d) - 1
    q = [0] * (len(f) - dd)
    for i in range(len(f) - 1, dd - 1, -1):
        c = f[i] % mod
        q[i - dd] = c
        for j in range(dd + 1):
            f[i - dd + j] = (f[i - dd + j] - c * d[j]) % mod
    return q, [x % mod for x in f[:dd]]

def scalar_member(box, outer_val, inner_val):
    """Scalar reproduction of the vectorized path (python ints)."""
    mask = (1 << box['N']) - 1
    vals = {st: (box['base'][st] if box['kind'] == 'state' else 0)
            for st in box['base']}
    for (st, sh, nb, bs) in box['inner']:
        vals[st] |= ((inner_val >> sh) & ((1 << nb) - 1)) << bs
    for (st, sh, nb, bs) in box['outer']:
        vals[st] |= ((outer_val >> sh) & ((1 << nb) - 1)) << bs
    if box['kind'] == 'nu1':
        R = CHIS[box['vtx']][3]
        a = tuple(((R[i] << (6 - i)) + (vals['u%d' % i] << (7 - i))) & mask
                  for i in range(6))
        c1, c0 = 2, 4
    else:
        a = a_from_q(vals['q0c'], vals['q0x'], vals['q1c'], vals['q1x'],
                     vals['q2c'], vals['q2x'], mask)
        c1, c0 = box['c1p'], box['c0p']
    return vals, a, c1, c0, mask

def verify_box(box, nsub=500, seed=20260727):
    """Literal-division + reconstruction + dictionary cross-checks.
    Returns dict of failure counts (sealed: all 0)."""
    rng = random.Random(seed + hash(box['name']) % 100000)
    bad = dict(div=0, rec=0, stratum=0, roundtrip=0)
    mod0 = 1 << box['N']
    for _ in range(nsub):
        ov = rng.randrange(1 << OUTERB)
        iv = rng.randrange(1 << INNER)
        vals, a, c1, c0, mask = scalar_member(box, ov, iv)
        f = list(a) + [1]
        # (1) literal long division chain vs closed-form div_chain
        r0c, r1x, s0c, s1x, t2c, t2x = div_chain(*a, c1, c0, mask)
        qq, rem1 = polydiv(f, [c0, c1, 1], mod0)
        pp, rem2 = polydiv(qq, [c0, c1, 1], mod0)
        ok = (rem1 == [r0c, r1x] and rem2 == [s0c, s1x]
              and pp == [(t2c + c0) % mod0, (t2x + c1) % mod0, 1])
        bad['div'] += not ok
        # (2) polymul reconstruction from the Phi2-frame back to f
        P = [c0, c1, 1]
        acc = [1]
        for Q in ([t2c, t2x], [s0c, s1x], [r0c, r1x]):
            acc = polyadd(polymul(acc, P, mod0), Q, mod0)
        bad['rec'] += acc != [x % mod0 for x in f]
        if box['kind'] == 'state':
            # (3) root-stratum membership in a-coordinates
            R = CHIS[box['vtx']][3]
            bad['stratum'] += any(a[i] % (1 << (7 - i)) != (R[i] << (6 - i))
                                  for i in range(6))
            # (4) Phi1-frame round trip: literal division recovers the Q pins
            qq1, remA = polydiv(f, [4, 2, 1], mod0)
            pp1, remB = polydiv(qq1, [4, 2, 1], mod0)
            ok = (remA == [vals['q0c'], vals['q0x']]
                  and remB == [vals['q1c'], vals['q1x']]
                  and (pp1[0] - 4) % mod0 == vals['q2c']
                  and (pp1[1] - 2) % mod0 == vals['q2x'] and pp1[2] == 1)
            bad['roundtrip'] += not ok
    return bad

def unit_tests():
    """Worked instance from the seal doc + dictionary spot checks."""
    fails = []
    # f = Phi1^2*(x^2+2x) = Phi1^3 - 4*Phi1^2 must land in the chi_A stratum.
    mask = (1 << 10) - 1
    a = a_from_q(0, 0, 0, 0, (-4) & mask, 0, mask)
    R = CHIS[1][3]                                   # chi_A = z^2+z -> vtx 1
    if any(a[i] % (1 << (7 - i)) != (R[i] << (6 - i)) for i in range(6)):
        fails.append('worked instance not in chi_A stratum: %s' % (a,))
    lit = polymul(polymul([4, 2, 1], [4, 2, 1], 1 << 10), [0, 2, 1], 1 << 10)
    if list(a) + [1] != lit:
        fails.append('worked instance mismatch: %s vs %s' % (a, lit))
    if F4_SQ != [0, 1, 3, 2] or f4_mul(2, 3) != 1:   # alpha*alpha^2 = 1
        fails.append('F4 table wrong')
    return fails

# ---------- decoding / diagnosis helpers ----------
def decode_h1(w):
    return (w & 3, (w >> 2) & 3, (w >> 4) & 3, (w >> 6) & 3, (w >> 8) & 3)

def decode_h2(w):
    return (w & 3, (w >> 2) & 3, (w >> 4) & 3, (w >> 6) & 3)

def bucket_h1(w):
    e6, e7, e8, e9, u9 = decode_h1(w)
    if u9:
        return "RAM9'(u=%d)" % u9
    if e6:
        return "L10+w1'=6(e6=%d)" % e6
    return "w1'>=7(e7=%d,e8=%d,e9=%d)" % (e7, e8, e9)

def bucket_nu1(cell, vtx):
    t, u7, u8 = cell & 3, (cell >> 2) & 3, (cell >> 4) & 3
    if u7:
        return 'RAM7'
    if u8:
        if t == 0:
            return 'RS1(r=%d)' % f4_mul(F4_SQ[u8], vtx)
        return 'SPLIT1' if F4_SQ[t] == f4_mul(u8, vtx) else 'INERT1'
    return 'TS(5,>=9)' if t else 'DEEP'

def diff_report(name1, h1, name2, h2, decoder, bucketer, out):
    d = np.nonzero(h1 != h2)[0]
    if len(d) == 0:
        out.append('  EQUAL  %-16s == %-16s (all %d cells)'
                   % (name1, name2, len(h1)))
        return 0
    out.append('  MISMATCH %s vs %s: %d differing cells; first 10:'
               % (name1, name2, len(d)))
    for w in d[:10]:
        out.append('    cell %s [%s]: %d vs %d'
                   % (decoder(int(w)), bucketer(int(w)), h1[w], h2[w]))
    return len(d)

def conj_perm_h1():
    """Frobenius relabeling of the h'=1 word (per-digit F4 conjugation)."""
    p = np.zeros(1024, dtype=np.int64)
    for w in range(1024):
        ds = decode_h1(w)
        cs = [F4_CONJ[t] for t in ds]
        p[w] = (cs[0] | (cs[1] << 2) | (cs[2] << 4) | (cs[3] << 6) | (cs[4] << 8))
    return p

# ---------- main ----------
def main():
    t0 = time.time()
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
    out = ['STATE-PROBE-2 SEALED GATE — exhaustive exact census',
           'seal: CASE_STATEPROBE2_SEALED_PREDICTIONS.md (P1-P6, sealed 2026-07-27'
           ' BEFORE this run)',
           'boxes: 3 nu1 root strata (N=9, a-coords) + 9 h\'=1 states (N=10) + '
           '3 h\'=2 states (N=11), each 2^27 members']
    fails = unit_tests()
    out.append('\n== UNIT TESTS (worked instance, F4 tables): %s =='
               % ('OK' if not fails else fails))
    arith = {}
    for box in BOXES:
        arith[box['name']] = verify_box(box)
    nbad_arith = sum(sum(v.values()) for v in arith.values()) + len(fails)
    out.append('== LITERAL-DIVISION LAYER (500 members/box, literal polydiv + '
               'reconstruction + stratum + Phi1 round trip) ==')
    for k in sorted(arith):
        out.append('  %-22s %s' % (k, arith[k]))
    tasks = [(bi, ov) for bi in range(len(BOXES)) for ov in range(1 << OUTERB)]
    hists = {bi: np.zeros(BOXES[bi]['ncells'], dtype=np.int64)
             for bi in range(len(BOXES))}
    viols = {bi: 0 for bi in range(len(BOXES))}
    vbads = {bi: 0 for bi in range(len(BOXES))}
    with Pool(NPROC) as pool:
        for bi, hist, viol, vbad in pool.imap_unordered(task, tasks, chunksize=8):
            hists[bi] += hist
            viols[bi] += viol
            vbads[bi] += vbad
    out.append('\ncensus done in %.0fs' % (time.time() - t0))
    name2bi = {BOXES[bi]['name']: bi for bi in range(len(BOXES))}

    # ---- P3 + P4(i): sizes, floors, vtx transport ----
    p3_bad = []
    for bi, box in enumerate(BOXES):
        n = int(hists[bi].sum())
        line = '%-22s |S|=%d floors_viol=%d vtx_viol=%d' % (
            box['name'], n, viols[bi], vbads[bi])
        if n != 1 << 27 or viols[bi] or vbads[bi]:
            p3_bad.append(line)
        out.append('  ' + line)
    out.append('P3/P4(i) (sizes 2^27, 0 floor viol, 0 vtx-transport viol): %s'
               % ('PASS' if not p3_bad else 'FAIL %s' % p3_bad))

    # ---- P1: THE REP IDENTITY (same type => identical full law) ----
    out.append('\n== P1 SAME-TYPE IDENTITY (M2(ii) = CTS-M(iv)-REP; sealed '
               'falsifier) ==')
    groups = {
        'P1a typeB h1 (vtx in {a,a^2} x r)': ['S(v=%d,r=%d,h1)' % (v, r)
                                              for v in (2, 3) for r in (1, 2, 3)],
        'P1b typeA h1 (vtx=1, r varying)': ['S(v=1,r=%d,h1)' % r for r in (1, 2, 3)],
        'P1c typeB h2 (vtx a vs a^2)': ['S(v=2,r=1,h2)', 'S(v=3,r=1,h2)'],
    }
    p1_bad = 0
    for gname, members in groups.items():
        out.append(' group %s:' % gname)
        base = hists[name2bi[members[0]]]
        dec, buc = ((decode_h1, bucket_h1) if 'h1' in members[0]
                    else (decode_h2, lambda w: 'h2'))
        for mname in members[1:]:
            p1_bad += diff_report(members[0], base, mname,
                                  hists[name2bi[mname]], dec, buc, out)
    out.append('P1: %s' % ('PASS (all same-type laws identical cell-by-cell)'
                           if p1_bad == 0 else 'FAIL (%d cells)' % p1_bad))

    # ---- P2: sealed uniform rows ----
    out.append('\n== P2 SEALED PER-TAU ROWS (uniform: h1 cells = 2^17, '
               'h2 cells = 2^19) ==')
    p2_bad = 0
    for bi, box in enumerate(BOXES):
        if box['kind'] != 'state':
            continue
        target = 1 << 17 if box['hp'] == 1 else 1 << 19
        off = np.nonzero(hists[bi] != target)[0]
        p2_bad += len(off)
        out.append('  %-16s off-uniform cells: %d%s' % (
            box['name'], len(off),
            '' if len(off) == 0 else '; first 5: %s' % [
                (decode_h1(int(w)) if box['hp'] == 1 else decode_h2(int(w)),
                 int(hists[bi][w])) for w in off[:5]]))
    out.append('P2: %s' % ('PASS' if p2_bad == 0 else 'FAIL (%d cells)' % p2_bad))

    # ---- P4(ii)+(iii): nu1 uniformity + named-bucket row ----
    out.append('\n== P4 NU1 ROOT-BOX LAYER (a-coords, N=9; dictionary + '
               'entry masses) ==')
    sealed_nu1 = {'RAM7': 48 << 21, 'SPLIT1': 3 << 21, 'INERT1': 6 << 21,
                  'TS(5,>=9)': 3 << 21, 'DEEP': 1 << 21,
                  'RS1(r=1)': 1 << 21, 'RS1(r=2)': 1 << 21, 'RS1(r=3)': 1 << 21}
    p4_bad = 0
    nu1_rows = {}
    for bi, box in enumerate(BOXES):
        if box['kind'] != 'nu1':
            continue
        off = np.nonzero(hists[bi] != (1 << 21))[0]
        p4_bad += len(off)
        row = {}
        for cell in range(64):
            b = bucket_nu1(cell, box['vtx'])
            row[b] = row.get(b, 0) + int(hists[bi][cell])
        nu1_rows[box['name']] = row
        bad_row = {k: (row.get(k, 0), sealed_nu1[k]) for k in sealed_nu1
                   if row.get(k, 0) != sealed_nu1[k]}
        p4_bad += len(bad_row)
        out.append('  %-24s off-uniform (t,u7,u8) cells: %d; bucket row: %s'
                   % (box['name'], len(off), row))
        if bad_row:
            out.append('    SEALED-ROW MISMATCH: %s' % bad_row)
    out.append('P4(ii,iii): %s' % ('PASS (64x2^21 uniform; bucket rows exact '
                                   'incl. RS1 entry masses)' if p4_bad == 0
                                   else 'FAIL (%d)' % p4_bad))

    # ---- P5: loop-position invariance (height-shift alignment) ----
    out.append('\n== P5 LOOP-POSITION INVARIANCE (h1 marginal over u9, digits '
               '@6..9, vs h2 word @7..10; floor-aligned shift) ==')
    p5_bad = 0
    for v in (1, 2, 3):
        marg = hists[name2bi['S(v=%d,r=1,h1)' % v]].reshape(4, 256).sum(axis=0)
        p5_bad += diff_report('h1-marg(v=%d,r=1)' % v, marg,
                              'h2(v=%d,r=1)' % v,
                              hists[name2bi['S(v=%d,r=1,h2)' % v]],
                              decode_h2, lambda w: 'shift', out)
    out.append('P5: %s' % ('PASS' if p5_bad == 0 else 'FAIL (%d cells)' % p5_bad))

    # ---- P6 (report-only) + Galois relabel layer (adjudication aid) ----
    out.append('\n== P6 CROSS-TYPE (typeA vs typeB raw rows; report-only, '
               'NON-falsifying) ==')
    d = int(np.count_nonzero(hists[name2bi['S(v=1,r=1,h1)']]
                             != hists[name2bi['S(v=2,r=1,h1)']]))
    out.append('  S(v=1,r=1,h1) vs S(v=2,r=1,h1): %d differing cells '
               '(differences expected-permitted; carried by the block system)' % d)
    perm = conj_perm_h1()
    out.append('== GALOIS RELABEL LAYER (S(a,r) vs S(a^2,r^2) with conjugated '
               'words; adjudication aid, not a pass condition) ==')
    g_bad = 0
    for r in (1, 2, 3):
        h_a = hists[name2bi['S(v=2,r=%d,h1)' % r]]
        h_c = hists[name2bi['S(v=3,r=%d,h1)' % F4_CONJ[r]]]
        nd = int(np.count_nonzero(h_a[perm] != h_c))
        g_bad += nd
        out.append('  S(v=2,r=%d,h1)^conj vs S(v=3,r=%d,h1): %d differing cells'
                   % (r, F4_CONJ[r], nd))

    # ---- verdict (seal doc §3) ----
    p3_ok = not p3_bad
    verdict_parts = {
        'arith_layer': nbad_arith == 0, 'P1_identity': p1_bad == 0,
        'P2_sealed_rows': p2_bad == 0, 'P3_floors_sizes': p3_ok,
        'P4_nu1_dictionary': p4_bad == 0, 'P5_loop_position': p5_bad == 0,
    }
    verdict = 'PASS' if all(verdict_parts.values()) else 'FAIL'
    summary = ['=' * 72,
               'STATE-PROBE-2 SEALED GATE SUMMARY',
               '12 states (9 h\'=1 @N=10, 3 h\'=2 @N=11) + 3 nu1 root boxes '
               '@N=9; 15 x 2^27 members, exhaustive',
               'arith layer: %s (unit tests %s)' % (
                   'clean' if nbad_arith == 0 else '%d FAILURES' % nbad_arith,
                   'OK' if not fails else fails),
               'P1 same-type identity: %s | P2 sealed uniform rows: %s'
               % ('PASS' if p1_bad == 0 else 'FAIL(%d cells)' % p1_bad,
                  'PASS' if p2_bad == 0 else 'FAIL(%d cells)' % p2_bad),
               'P3 floors/sizes/vtx-transport: %s | P4 nu1 dictionary+row: %s '
               '| P5 loop-position: %s' % (
                   'PASS' if p3_ok else 'FAIL', 'PASS' if p4_bad == 0 else 'FAIL',
                   'PASS' if p5_bad == 0 else 'FAIL(%d)' % p5_bad),
               'P6 cross-type (report-only): %d differing cells; Galois layer: '
               '%d differing cells' % (d, g_bad),
               'VERDICT: %s' % verdict,
               'wall time %.0fs' % (time.time() - t0), '=' * 72]
    out.extend(summary)
    with open(OUTTXT, 'w') as fh:
        fh.write('\n'.join(out) + '\n')
    with open(OUTJSON, 'w') as fh:
        json.dump({'verdict': verdict, 'verdict_parts': verdict_parts,
                   'p1_bad_cells': p1_bad, 'p2_bad_cells': p2_bad,
                   'p4_bad': p4_bad, 'p5_bad_cells': p5_bad,
                   'p6_crosstype_cells': d, 'galois_cells': g_bad,
                   'arith': arith, 'unit_test_fails': fails,
                   'floors_viol': {BOXES[bi]['name']: viols[bi] for bi in viols},
                   'vtx_viol': {BOXES[bi]['name']: vbads[bi] for bi in vbads},
                   'nu1_rows': nu1_rows,
                   'hists': {BOXES[bi]['name']: hists[bi].tolist()
                             for bi in hists}}, fh, indent=1)
    print('\n'.join(summary))
    return 0 if verdict == 'PASS' else 1

if __name__ == '__main__':
    sys.exit(main())
