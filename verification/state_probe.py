#!/usr/bin/env python3
"""state_probe.py — R2/C5 wall probe: does the depth recursion close over a
FINITE state-type system?  (STATE-probe per ASSEMBLY_PLAN_2026-07-26.md §4
RS.0 / §8 R2.)  EXPLORATION-CLASS (no seal; the plan's spec defines the
reading).  Exact exhaustive enumeration only — no sampling in any verdict row.

THE QUESTION (RS.0 TYPE-CLOSURE).  The RESUM block system needs: every
same-cluster-size move's conditional next-move law depends on the source state
only through its TYPE tau = (residual shape, anchor a, tower phase, vtx
stratum) — never on untyped retained VALUES or loop position.  The probe takes
same-type states differing in a retained value, measures their exact
conditional next-move laws by exhaustive enumeration, and compares.

CONFIGURATION-FEASIBILITY FINDING (derivation, recorded).  The plan expected
"two same-shape states in different VAL.1 vtx-strata at n = 4 or 5".  In the
monic ROOT boxes actually exhaustible at p = 2, 3 this vtx-coordinate is RIGID:
(i) at a recentering m-hat' = 0 and R(Phi') = z - c (D.10 unit note), so
vtx(RS state) = the transported cluster lead d2; (ii) with the cluster = the
whole monic f (n = 4: R0 = psi^2), C2 = 1 forces d2 = 1 identically; (iii) at
n = 5 (R0 = psi^2*(Az+B)) monicity forces A = 1, and the remaining pair
(1,1) vs (1,2) is x -> -x symmetric — provably equal laws, vacuous; (iv) a
vtx-varying continuing state needs in-cluster increments: n >= 6.  The value
datum that DOES vary at n = 4 is the RS residual ROOT r in F_{q^2}*: the
same-size self-loop's own retained value — untyped by M2's vocabulary (the
residual SHAPE forgets r), and stratified by exactly the VAL.1 cells (subfield
line F_q* vs the non-subfield lines).  All probe states have LITERALLY EQUAL
vtx (= 1), so they are same-type under the current T AND under any
vtx-stratum refinement: a law difference would be a same-TYPE mismatch, the
R2 signal.  This is the faithful minimal-configuration reading of the spec.

PROBE STATES.  Root stratum: monic quartic, Newton side [0,4] slope 1,
residual R0 = psi^2 (p = 2: psi = z^2+z+1; p = 3: psi = z^2+1) — the mu = 2,
g = 2 cluster is all of f (block e = 4).  Key Phi1 = the (S6b) standard lift
(p = 2: x^2+2x+4; p = 3: x^2+9).  Frame 2: f = Phi1^2 + C1*Phi1 + C0,
w(B) := min(v(b_c), v(b_x)+1), slot weights (0, w(C0)), (1, w(C1)), (2, 0),
floors w(C1) >= 3, w(C0) >= 5 (carry-algebra theorems; violations counted).
nu1 = single side [0,2] slope 3 (w(C0) = 6) with repeated-root pattern:
  p = 2: R1 = y^2 + d0, d1 = 0, r = sqrt(d0);  p = 3: R1 = y^2 + d1*y + d0,
  d0 = d1^2, r = d1.   STATE S_r := that (nu0, nu1) cylinder.
  p = 2: r in {1, w, w^2} — cells {1} (subfield) vs {w, w^2} (one Galois
  orbit: x -> -x is trivial at p = 2, conjugation is a relabeling check).
  p = 3: r in F_9* (8 states) — physical cells {1}, {2}, {a, 2a}, {a+1, 2a+1},
  {a+2, 2a+2} (x -> -x realizes conjugation r -> r^3): FIVE distinct states;
  {1} vs {2} is a same-LINE (same refined-type) pair — the refinement-round
  pair; {1} vs {a}-cell and {a+1}-cell vs {a+2}-cell cross lines.
NEXT MOVE nu2: recenter Phi2 = Phi1 - lift(r)@weight3 ((S6b): const level 3,
x-part level 2), frame 3: f = Phi2^2 + C1'*Phi2 + C0'; floors w(C1') >= 4,
w(C0') >= 7 (recentering kills line digits: (y+r)^2 -> y'^2 exactly).
CONDITIONAL LAW measured = exact histogram of the READABLE FRESH WORD
  p = 2, N = 10: (dig(C1')@4, @5, dig(C0')@7, @8, @9) in F_4^5 (1024 cells);
  p = 3, N = 8:  (dig(C1')@4, @5, dig(C0')@7) in F_9^3 (729 cells);
which refines the nu2 bucket row: RAM7 (u7 != 0, e_read = 2 exit), h''=1 side
(u7 = 0, u8 != 0): RS'(r' = sqrt(u8)) / SPLIT' / INERT', TS' (two-sided),
RAM9', DEEP-lump.   SECONDARY LAYER (p = 2): the h' = 2 states S2_r
(w(C0) = 8, side slope 4, same shape, different HEIGHT = loop-position probe),
readable word (dig(C1')@5, dig(C0')@9) in F_4^2; cross-height row comparison.

CLAIMED ROW (the theory's M_e row; in-context derivation, exploration-class —
Theorem C freshness + D.10/TRANS-RS graded landing): every readable fresh word
is UNIFORM and r-INDEPENDENT:
  p = 2 h'=1: |S_r| = 2^20 = 1048576, every word cell EXACTLY 1024;
  p = 2 h'=2: |S2_r| = 2^14 = 16384,  every word cell EXACTLY 1024;
  p = 3 h'=1: |S_r| = 3^12 = 531441,  every word cell EXACTLY 729.

READING (the plan's criterion, verbatim logic):
  MATCH  = all same-type states' histograms equal cell-by-cell, exactly
           -> same type => same law at the probed configuration: R2 NO-WALL
           (probe-level), no T-refinement used.
  DIFFER = adjudicate (code/truncation vs theory); a genuine same-type
           mismatch triggers the ONE allowed T-refinement (type the loop
           value's VAL.1 line-cell); the within-cell pair S_1 vs S_2 (p = 3)
           then re-probes; a second failure = R2 WALL (§8 protocol).

Run:  python3 state_probe.py          (multiprocessing, ~40 workers)
      tables -> results/state_probe_output.txt, hists ->
      results/state_probe_hist.json, summary on stdout.
"""
import json
import os
import sys
import time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
OUTTXT = os.path.join(HERE, 'results', 'state_probe_output.txt')
OUTJSON = os.path.join(HERE, 'results', 'state_probe_hist.json')
NPROC = 40

# ---------- p = 2 layer constants (N = 10) ----------
N2 = 10
M2 = 1 << N2                     # 1024
# root stratum: a0 = 16 + 32*u0, a1 = 16*u1, a2 = 4 + 8*u2, a3 = 4*u3
U0_2, U1_2, U2_2, U3_2 = 1 << 5, 1 << 6, 1 << 7, 1 << 8   # 2^26 total
PHI1_2 = (2, 4)                  # x^2 + 2x + 4 (S6b lift of psi = z^2+z+1)

# ---------- p = 3 layer constants (N = 8) ----------
N3 = 8
P3 = [3 ** i for i in range(N3 + 1)]
M3 = P3[N3]                      # 6561
# root stratum: a0 = 81 + 243*u0, a1 = 81*u1, a2 = 18 + 27*u2, a3 = 9*u3
U0_3, U1_3, U2_3, U3_3 = 27, 81, 243, 729                 # 3^18 total
PHI1_3 = (0, 9)                  # x^2 + 9 (S6b lift of psi = z^2+1)

# ---------- finite-field tables (code = base*eps_x + eps_c) ----------
def _f4_mul(a, b):
    c1, x1, c2, x2 = a & 1, a >> 1, b & 1, b >> 1
    return ((c1 * c2 + x1 * x2) & 1) + 2 * ((c1 * x2 + x1 * c2 + x1 * x2) & 1)

F4_SQ = [_f4_mul(t, t) for t in range(4)]          # sqrt = sq on F_4
def _f9_mul(a, b):
    c1, x1, c2, x2 = a % 3, a // 3, b % 3, b // 3
    return (c1 * c2 - x1 * x2) % 3 + 3 * ((c1 * x2 + x1 * c2) % 3)

F9_SQ = [_f9_mul(t, t) for t in range(9)]
F9_CONJ = [(t % 3) + 3 * ((-(t // 3)) % 3) for t in range(9)]   # t -> t^3
F9_SQUARES = sorted({F9_SQ[t] for t in range(1, 9)})            # nonzero squares

# ---------- valuation tables ----------
def vtable2(mod, cap):
    vt = [0] * mod
    vt[0] = cap
    for y in range(1, mod):
        vt[y] = 0 if y & 1 else min(vt[y >> 1] + 1, cap)
    return vt

def vtable3(mod, cap):
    vt = [0] * mod
    vt[0] = cap
    for y in range(1, mod):
        vt[y] = 0 if y % 3 else min(vt[y // 3] + 1, cap)
    return vt

VT2 = vtable2(M2, N2)
VT3 = vtable3(M3, N3)

# ---------- closed-form quartic division by monic x^2 + c1 x + c0 ----------
def dev4(a0, a1, a2, a3, c1, c0, m):
    """f = x^4+a3x^3+a2x^2+a1x+a0 = (x^2+q1x+q0)(x^2+c1x+c0) + rx*x + rc.
    Returns (q0, q1, rc, rx), exact mod m."""
    q1 = (a3 - c1) % m
    q0 = (a2 - c1 * q1 - c0) % m
    rx = (a1 - c1 * q0 - c0 * q1) % m
    rc = (a0 - c0 * q0) % m
    return q0, q1, rc, rx

# ---------- p = 2 member classification ----------
def wpair2(bc, bx):
    """w = min(v(bc), v(bx)+1), capped at N2."""
    vc, vx = VT2[bc], VT2[bx] + 1
    return vc if vc < vx else (vx if vx < N2 else N2)

def dig2(bc, bx, m):
    """Raw F_4 digit of the pair at weight m (valid when w >= m), m <= N2-1."""
    return (((bx >> (m - 1)) & 1) << 1) | ((bc >> m) & 1)

def classify2(a0, a1, a2, a3):
    """One p = 2 root-stratum member -> (bucket, state, word).
    bucket: nu1 taxonomy label; state: ('S1', r) or ('S2', r) or None;
    word: readable fresh nu2 word for probe states, else None.
    Also returns floor-violation flags."""
    q0, q1, rc, rx = dev4(a0, a1, a2, a3, 2, 4, M2)
    c1c, c1x = (q0 - 4) % M2, (q1 - 2) % M2          # C1 = Q - Phi1
    w1, w0 = wpair2(c1c, c1x), wpair2(rc, rx)
    viol1 = (w1 < 3) or (w0 < 5)
    if 2 * w1 < w0:                                   # vertex at slot 1
        return ('TS(%d,%s)' % (w1, w0 if w0 < N2 else 'ge10'), None, None, viol1)
    if w0 >= N2:
        return ('DEEP', None, None, viol1)
    if w0 & 1:                                        # e_read = 2 side
        return ('RAM%d' % w0, None, None, viol1)
    hp = (w0 - 4) >> 1                                # h' >= 1
    d1, d0 = dig2(c1c, c1x, w0 >> 1), dig2(rc, rx, w0)
    if d1 == 0:                                       # repeated root (char 2)
        r = F4_SQ[d0]                                 # sqrt(d0)
        if hp == 1:
            return ('RS1', ('S1', r), nu2_word2(a0, a1, a2, a3, r, 1), viol1)
        if hp == 2:
            return ('RS2', ('S2', r), nu2_word2(a0, a1, a2, a3, r, 2), viol1)
        return ('RS%d' % hp, None, None, viol1)
    if d0 == F4_SQ[d1]:                               # split: d0 = d1^2
        return ('SPLIT%d' % hp, None, None, viol1)
    return ('INERT%d' % hp, None, None, viol1)

def nu2_word2(a0, a1, a2, a3, r, hp):
    """Recenter Phi2 = Phi1 - lift(r)@weight(2+hp) and read the fresh word.
    h'=1: lift = 8r_c + 4r_x*x, word = (d(C1')@4, @5, d(C0')@7, @8, @9)
    h'=2: lift = 16r_c + 8r_x*x, word = (d(C1')@5, d(C0')@9)
    Word prefixed by floor-violation flag for C1'/C0' floors."""
    rcc, rxx = r & 1, r >> 1
    lc, lx = (8 << (hp - 1)) * rcc, (4 << (hp - 1)) * rxx
    c1n, c0n = (2 - lx) % M2, (4 - lc) % M2
    q0, q1, rc, rx = dev4(a0, a1, a2, a3, c1n, c0n, M2)
    d1c, d1x = (q0 - c0n) % M2, (q1 - c1n) % M2       # C1'
    w1p, w0p = wpair2(d1c, d1x), wpair2(rc, rx)
    if hp == 1:
        viol2 = (w1p < 4) or (w0p < 7)
        word = (dig2(d1c, d1x, 4), dig2(d1c, d1x, 5),
                dig2(rc, rx, 7), dig2(rc, rx, 8), dig2(rc, rx, 9))
    else:
        viol2 = (w1p < 5) or (w0p < 9)
        word = (dig2(d1c, d1x, 5), dig2(rc, rx, 9))
    return (viol2, word)

def worker2(u3):
    """Exhaust the p = 2 box slice at fixed u3: 2^18 members."""
    a3 = 4 * u3
    buckets, hists = {}, {}
    viol1 = viol2 = 0
    for u2 in range(U2_2):
        a2 = 4 + 8 * u2
        for u1 in range(U1_2):
            a1 = 16 * u1
            for u0 in range(U0_2):
                a0 = 16 + 32 * u0
                b, st, wd, v1 = classify2(a0, a1, a2, a3)
                viol1 += v1
                buckets[b] = buckets.get(b, 0) + 1
                if st is not None:
                    v2, word = wd
                    viol2 += v2
                    key = (st[0], st[1], word)
                    hists[key] = hists.get(key, 0) + 1
    return buckets, hists, viol1, viol2

def merge(results):
    B, H = {}, {}
    v1 = v2 = 0
    for b, h, x1, x2 in results:
        v1 += x1
        v2 += x2
        for k, v in b.items():
            B[k] = B.get(k, 0) + v
        for k, v in h.items():
            H[k] = H.get(k, 0) + v
    return B, H, v1, v2

# ---------- p = 3 member classification ----------
def wpair3(bc, bx):
    vc, vx = VT3[bc], VT3[bx] + 1
    return vc if vc < vx else (vx if vx < N3 else N3)

def dig3(bc, bx, m):
    """Raw F_9 digit at weight m (code = 3*eps_x + eps_c), m <= N3-1."""
    return 3 * ((bx // P3[m - 1]) % 3) + ((bc // P3[m]) % 3)

def classify3(a0, a1, a2, a3):
    q0, q1, rc, rx = dev4(a0, a1, a2, a3, 0, 9, M3)
    c1c, c1x = (q0 - 9) % M3, q1                      # C1 = Q - Phi1
    w1, w0 = wpair3(c1c, c1x), wpair3(rc, rx)
    viol1 = (w1 < 3) or (w0 < 5)
    if 2 * w1 < w0:
        return ('TS(%d,%s)' % (w1, w0 if w0 < N3 else 'ge8'), None, None, viol1)
    if w0 >= N3:
        return ('DEEP', None, None, viol1)
    if w0 & 1:
        return ('RAM%d' % w0, None, None, viol1)
    hp = (w0 - 4) >> 1
    d1, d0 = dig3(c1c, c1x, w0 >> 1), dig3(rc, rx, w0)
    if d0 == F9_SQ[d1] and d1 != 0:                   # (y-r)^2, r = d1 (char 3)
        if hp == 1:
            return ('RS1', ('S1', d1), nu2_word3(a0, a1, a2, a3, d1), viol1)
        return ('RS%d' % hp, None, None, viol1)
    disc = (F9_SQ[d1] - d0) % 3 + 3 * (((F9_SQ[d1] // 3) - (d0 // 3)) % 3)
    if disc != 0 and disc in F9_SQUARES:
        return ('SPLIT%d' % hp, None, None, viol1)
    return ('INERT%d' % hp, None, None, viol1)

def nu2_word3(a0, a1, a2, a3, r):
    """Phi2 = Phi1 - (27 r_c + 9 r_x x); word = (d(C1')@4, @5, d(C0')@7)."""
    rcc, rxx = r % 3, r // 3
    c1n, c0n = (-9 * rxx) % M3, (9 - 27 * rcc) % M3
    q0, q1, rc, rx = dev4(a0, a1, a2, a3, c1n, c0n, M3)
    d1c, d1x = (q0 - c0n) % M3, (q1 - c1n) % M3
    w1p, w0p = wpair3(d1c, d1x), wpair3(rc, rx)
    viol2 = (w1p < 4) or (w0p < 7)
    return (viol2, (dig3(d1c, d1x, 4), dig3(d1c, d1x, 5), dig3(rc, rx, 7)))

def worker3(u3):
    """Exhaust the p = 3 box slice at fixed u3: 3^12 members."""
    a3 = 9 * u3
    buckets, hists = {}, {}
    viol1 = viol2 = 0
    for u2 in range(U2_3):
        a2 = 18 + 27 * u2
        for u1 in range(U1_3):
            a1 = 81 * u1
            for u0 in range(U0_3):
                a0 = 81 + 243 * u0
                b, st, wd, v1 = classify3(a0, a1, a2, a3)
                viol1 += v1
                buckets[b] = buckets.get(b, 0) + 1
                if st is not None:
                    v2, word = wd
                    viol2 += v2
                    key = (st[0], st[1], word)
                    hists[key] = hists.get(key, 0) + 1
    return buckets, hists, viol1, viol2

# ---------- verification pass: literal division vs closed form ----------
def polydiv(f, d, mod):
    """Genuine long division by monic d (low->high lists)."""
    f = list(f)
    dd = len(d) - 1
    q = [0] * (len(f) - dd)
    for i in range(len(f) - 1, dd - 1, -1):
        c = f[i] % mod
        q[i - dd] = c
        for j in range(dd + 1):
            f[i - dd + j] = (f[i - dd + j] - c * d[j]) % mod
    return q, [x % mod for x in f[:dd]]

def polymul(A, B, mod):
    R = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            R[i + j] = (R[i + j] + a * b) % mod
    return R

def verify_pass(nsub=4000, seed=20260726):
    """Closed dev4 vs literal polydiv + full reconstruction, both primes,
    both frames (Phi1 and a random recentered Phi2).  Returns failure counts."""
    import random
    rng = random.Random(seed)
    bad = dict(div2=0, rec2=0, div3=0, rec3=0)
    for _ in range(nsub):
        a = [16 + 32 * rng.randrange(U0_2), 16 * rng.randrange(U1_2),
             4 + 8 * rng.randrange(U2_2), 4 * rng.randrange(U3_2)]
        for (c1, c0) in ((2, 4), ((2 - 4 * rng.randrange(2)) % M2,
                                  (4 - 8 * rng.randrange(2)) % M2)):
            q0, q1, rc, rx = dev4(*a, c1, c0, M2)
            qL, rL = polydiv(a + [1], [c0, c1, 1], M2)
            bad['div2'] += (qL != [q0, q1, 1]) or (rL != [rc, rx])
            rec = polymul([q0, q1, 1], [c0, c1, 1], M2)
            rec[0], rec[1] = (rec[0] + rc) % M2, (rec[1] + rx) % M2
            bad['rec2'] += rec != a + [1]
        b = [81 + 243 * rng.randrange(U0_3), 81 * rng.randrange(U1_3),
             18 + 27 * rng.randrange(U2_3), 9 * rng.randrange(U3_3)]
        for (c1, c0) in ((0, 9), ((-9 * rng.randrange(3)) % M3,
                                  (9 - 27 * rng.randrange(3)) % M3)):
            q0, q1, rc, rx = dev4(*b, c1, c0, M3)
            qL, rL = polydiv(b + [1], [c0, c1, 1], M3)
            bad['div3'] += (qL != [q0, q1, 1]) or (rL != [rc, rx])
            rec = polymul([q0, q1, 1], [c0, c1, 1], M3)
            rec[0], rec[1] = (rec[0] + rc) % M3, (rec[1] + rx) % M3
            bad['rec3'] += rec != b + [1]
    return bad

# ---------- comparison / verdict ----------
def state_hists(H, layer):
    """H: merged {(layer, r, word): count} -> {r: {word: count}}."""
    out = {}
    for (lay, r, word), c in H.items():
        if lay == layer:
            out.setdefault(r, {})[word] = c
    return out

def hist_eq(h1, h2):
    return h1 == h2

def conj_hist(h, conj):
    return {tuple(conj[d] for d in w): c for w, c in h.items()}

def diff_cells(h1, h2):
    keys = set(h1) | set(h2)
    return [(w, h1.get(w, 0), h2.get(w, 0)) for w in sorted(keys)
            if h1.get(w, 0) != h2.get(w, 0)]

def uniform_check(h, nletters, wordlen, target):
    """All nletters^wordlen cells present with exactly target members?"""
    bad = [(w, c) for w, c in sorted(h.items()) if c != target]
    missing = nletters ** wordlen - len(h)
    return bad, missing

def bucket_p2s1(word):
    d4, d5, u7, u8, u9 = word
    if u7:
        return 'RAM7(u=%d)' % u7
    if u8:
        if d4 == 0:
            return "RS'(r'=%d)" % F4_SQ[u8]
        return "SPLIT'(d=%d)" % d4 if u8 == F4_SQ[d4] else "INERT'(%d,%d)" % (d4, u8)
    if d4:
        return "TS'(d=%d)" % d4
    if u9:
        return 'RAM9(u=%d)' % u9
    return "DEEP'(d5=%d)" % d5

def bucket_rows(hists, bucketer):
    rows = {}
    for r, h in hists.items():
        for w, c in h.items():
            b = bucketer(w)
            rows.setdefault(b, {})[r] = rows.setdefault(b, {}).get(r, 0) + c
    return rows

F4_CONJ = [0, 1, 3, 2]

def run_verdict(h2s1, h2s2, h3s1, out):
    """The plan's reading.  Returns (verdict, refinement_used)."""
    mm = []                                    # (label, ncells) mismatch log
    def cmp_group(hs, label, order):
        ok = True
        base = hs[order[0]]
        for r in order[1:]:
            d = diff_cells(base, hs[r])
            if d:
                ok = False
                mm.append(('%s: r=%s vs r=%s' % (label, order[0], r), len(d)))
                out.append('  MISMATCH %s r=%s vs r=%s: %d cells; first 5: %s'
                           % (label, order[0], r, len(d), d[:5]))
        return ok
    m1 = cmp_group(h2s1, 'p2/S1', sorted(h2s1))
    m2 = cmp_group(h2s2, 'p2/S2', sorted(h2s2))
    m3 = cmp_group(h3s1, 'p3/S1', sorted(h3s1))
    if m1 and m2 and m3:
        return 'NO-WALL', False
    # ONE T-refinement: type the loop value's VAL.1 line-cell (F_q* . r).
    # Within-cell pairs that must then agree:
    #   p3: S_1 vs S_2 (same line F_3*); Galois relabelings S_r vs S_{r^3};
    #   p2: Galois relabeling S_w vs S_w2 (each line-cell is a singleton).
    ok = True
    if 1 in h3s1 and 2 in h3s1:
        d = diff_cells(h3s1[1], h3s1[2])
        if d:
            ok = False
            out.append('  REFINED-TYPE MISMATCH p3 S_1 vs S_2 (same line-cell '
                       'F_3*): %d cells; first 5: %s' % (len(d), d[:5]))
    for r in list(h3s1):
        rc = F9_CONJ[r]
        if rc in h3s1:
            d = diff_cells(conj_hist(h3s1[r], F9_CONJ), h3s1[rc])
            if d:
                ok = False
                out.append('  GALOIS-RELABEL MISMATCH p3 S_%d vs S_%d: %d cells'
                           % (r, rc, len(d)))
    if 2 in h2s1 and 3 in h2s1:
        d = diff_cells(conj_hist(h2s1[2], F4_CONJ), h2s1[3])
        if d:
            ok = False
            out.append('  GALOIS-RELABEL MISMATCH p2 S_w vs S_w2: %d cells'
                       % len(d))
    return ('NEEDS-REFINEMENT' if ok else 'WALL'), True

# ---------- main ----------
def report_layer(out, hists, label, target, nletters, wordlen, exp_size):
    out.append('\n== %s: per-state sizes and word histograms (theory: |S_r| = '
               '%d, every word cell = %d) ==' % (label, exp_size, target))
    for r in sorted(hists):
        h = hists[r]
        n = sum(h.values())
        bad, missing = uniform_check(h, nletters, wordlen, target)
        out.append('  r=%s: |S_r| = %d (%s); cells %d/%d; off-uniform cells: %d'
                   % (r, n, 'OK' if n == exp_size else 'UNEXPECTED',
                      len(h), nletters ** wordlen, len(bad))
                   + ('' if not bad else '; first 5: %s' % bad[:5])
                   + ('' if not missing else '; MISSING %d cells' % missing))

def main():
    t0 = time.time()
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
    out = ['STATE-PROBE (R2/C5 wall probe) — exploration-class, exact '
           'exhaustive enumeration',
           'spec: ASSEMBLY_PLAN_2026-07-26.md §4 STATE-probe + §8 R2; '
           'configuration per the feasibility finding in this script\'s '
           'docstring',
           'p=2: N=%d, box 2^26 = %d members; p=3: N=%d, box 3^18 = %d members'
           % (N2, U0_2 * U1_2 * U2_2 * U3_2, N3, U0_3 * U1_3 * U2_3 * U3_3)]
    bad = verify_pass()
    out.append('\n== CLOSED-FORM VERIFICATION (4000 members/prime, literal '
               'subtract-multiples division + reconstruction): %s ==' % bad)
    arith_ok = not any(bad.values())
    with Pool(NPROC) as pool:
        res2 = pool.map(worker2, range(U3_2), chunksize=4)
        B2, H2, v1_2, v2_2 = merge(res2)
        t2 = time.time()
        out.append('\np=2 census done in %.0fs; nu1 buckets:' % (t2 - t0))
        for k in sorted(B2):
            out.append('  %-12s %d' % (k, B2[k]))
        out.append('  nu1 floor violations: %d; nu2 floor violations: %d'
                   % (v1_2, v2_2))
        res3 = pool.map(worker3, range(U3_3), chunksize=8)
        B3, H3, v1_3, v2_3 = merge(res3)
    t3 = time.time()
    out.append('\np=3 census done in %.0fs; nu1 buckets:' % (t3 - t2))
    for k in sorted(B3):
        out.append('  %-12s %d' % (k, B3[k]))
    out.append('  nu1 floor violations: %d; nu2 floor violations: %d'
               % (v1_3, v2_3))
    h2s1 = state_hists(H2, 'S1')
    h2s2 = state_hists(H2, 'S2')
    h3s1 = state_hists(H3, 'S1')
    report_layer(out, h2s1, 'p=2 h\'=1 states (r in F_4*)', 1024, 4, 5, 1 << 20)
    report_layer(out, h2s2, 'p=2 h\'=2 states (height/position layer)',
                 1024, 4, 2, 1 << 14)
    report_layer(out, h3s1, 'p=3 h\'=1 states (r in F_9*, 5 physical cells '
                 '{1},{2},{a,2a},{a+1,2a+1},{a+2,2a+2})', 729, 9, 3, 3 ** 12)
    out.append('\n== nu2 NAMED-BUCKET ROW, p=2 h\'=1 (per state r) ==')
    rows = bucket_rows(h2s1, bucket_p2s1)
    for b in sorted(rows):
        out.append('  %-16s %s' % (b, {r: rows[b].get(r, 0)
                                       for r in sorted(h2s1)}))
    out.append('\n== CROSS-HEIGHT (loop-position) CHECK: S1 marginal (d@4,d@7)'
               ' vs S2 word (d@5,d@9), fractions (x64) ==')
    xh_bad = 0
    for r in sorted(h2s2):
        marg = {}
        for w, c in h2s1.get(r, {}).items():
            k = (w[0], w[2])
            marg[k] = marg.get(k, 0) + c
        d = [(k, marg.get(k, 0), 64 * h2s2[r].get(k, 0))
             for k in set(marg) | set(h2s2[r])
             if marg.get(k, 0) != 64 * h2s2[r].get(k, 0)]
        xh_bad += len(d)
        out.append('  r=%s: %s' % (r, 'MATCH (all 16 cells)' if not d
                                   else 'MISMATCH %s' % d[:5]))
    out.append('\n== VERDICT LAYER (the plan\'s reading) ==')
    verdict, refined = run_verdict(h2s1, h2s2, h3s1, out)
    if not arith_ok or v1_2 or v2_2 or v1_3 or v2_3:
        verdict = 'ADJUDICATE (arithmetic layer or floors failed — no theory '\
                  'reading until repaired)'
    summary = ['=' * 72,
               'STATE-PROBE SUMMARY: p2/S1 states %d, p2/S2 states %d, '
               'p3/S1 states %d' % (len(h2s1), len(h2s2), len(h3s1)),
               'floors: %d violations; closed-form: %s; cross-height '
               'mismatched cells: %d' % (v1_2 + v2_2 + v1_3 + v2_3, bad, xh_bad),
               'T-refinement round used: %s' % refined,
               'R2 VERDICT (probe-level): %s' % verdict,
               'wall time %.0fs' % (time.time() - t0), '=' * 72]
    out.extend(summary)
    with open(OUTTXT, 'w') as fh:
        fh.write('\n'.join(out) + '\n')
    with open(OUTJSON, 'w') as fh:
        json.dump({'p2s1': {str(r): {str(w): c for w, c in h.items()}
                            for r, h in h2s1.items()},
                   'p2s2': {str(r): {str(w): c for w, c in h.items()}
                            for r, h in h2s2.items()},
                   'p3s1': {str(r): {str(w): c for w, c in h.items()}
                            for r, h in h3s1.items()},
                   'buckets_p2': B2, 'buckets_p3': B3}, fh, indent=1)
    print('\n'.join(summary))
    return 0

if __name__ == '__main__':
    sys.exit(main())
