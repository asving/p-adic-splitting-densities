#!/usr/bin/env python3
# case_sib_gate.py — CASE-SIB census. Written AFTER CASE_SIB_SEALED_PREDICTIONS.md was
# sealed (Case-K discipline; seal S5 is this script's specification).
# L1: F1 branching cell p=5 n=4 cell (4,3,3,4): joint depth-1 word law, 5^8 exhaustive
#     members of Sigma_c in the minimal word-sufficient box B22 + full 5^12 h-pass.
# L2: p=2 n=3 cell (0,0,1) = (z+1)(z^2+z+1), mixed shapes: below-halt refinement words,
#     2^15 exhaustive + literal 2^24 membership pass. L3: p=5 n=3 cell (4,1,4), m=3.
# Output -> /tmp/sib_census.out (redirect); JSON -> verification/results/case_sib_results.json
import numpy as np, json, time, math
T0 = time.time()
def log(s=''): print(s, flush=True)
verdicts = []
def check(name, ok, detail=''):
    verdicts.append({'name': name, 'ok': bool(ok), 'detail': str(detail)})
    log(f"[{'PASS' if ok else 'FAIL'}] {name}  {detail}")
def digit(x, p, l): return (x // p**l) % p

def synth_divide(c, s):
    """c: poly high->low (numpy arrays); divide by (x - s), exact ints."""
    q = [c[0]]
    for a in c[1:-1]:
        q.append(a + s*q[-1])
    return q, c[-1] + s*q[-1]

def develop(c, s, k):
    """First k development coefficients B0..B(k-1) of the poly at (x - s)."""
    B = []
    cur = c
    for _ in range(k):
        cur, rem = synth_divide(cur, s)
        B.append(rem)
    return B

# ================================ LAYER 1 ================================
log('=== LAYER 1: F1 cell p=5 n=4 (4,3,3,4), joint depth-1 word law ===')
idx = np.arange(5**8, dtype=np.int64)
e0, e1, e2, e3 = [(idx // 5**k) % 5 for k in range(4)]
g0, g1, g2, g3 = [(idx // 5**(4+k)) % 5 for k in range(4)]
NSIG = 5**8

def coeffs_L1(h=(0, 0, 0, 0)):
    h0, h1, h2, h3 = h
    return (5*(4 + 5*e3 + 25*g3 + 125*h3), 25*(3 + 5*e2 + 25*g2 + 125*h2),
            125*(3 + 5*e1 + 25*g1 + 125*h1), 625*(4 + 5*e0 + 25*g0 + 125*h0))

def words_L1(c3, c2, c1, c0, state_checks=False):
    W, states = {}, {}
    ONE = np.ones_like(c3)
    for r in (1, 2):
        B0, B1, B2 = develop([ONE, c3, c2, c1, c0], 5*r, 3)
        if state_checks:
            states[r] = (bool((digit(B2, 5, 2) == 1).all()), bool((digit(B1, 5, 3) == 0).all()),
                         bool((digit(B0, 5, 4) == 0).all()))
        W[r] = digit(B1, 5, 4)*25 + digit(B0, 5, 5)*5 + digit(B0, 5, 6)
    return W, states

c3, c2, c1, c0 = coeffs_L1()
W, states = words_L1(c3, c2, c1, c0, state_checks=True)
for r in (1, 2):
    check(f'P6 transported state r={r}: digit2(B2)=1, digit3(B1)=0, digit4(B0)=0 on ALL members',
          all(states[r]), states[r])
# P6b in-script branch table at the cell (Taylor shift, d4m2 method)
R0 = [4, 3, 3, 4, 1]  # low->high: z^4+4z^3+3z^2+3z+4
brs = []
for rr in range(1, 5):
    ec = [sum(R0[j]*math.comb(j, k)*pow(rr, j-k, 5) for j in range(k, 5)) % 5 for k in range(3)]
    if ec[0] == 0 and ec[1] == 0 and ec[2] != 0:
        brs.append(rr)
check('P6b branch set at (4,3,3,4) = {1,2} (Taylor-shift re-derivation)', brs == [1, 2], brs)
# P8 form check (S2 closed forms vs literal development digits)
T51 = 3 + e3+e2+e1+e0
T52 = 14 + 8*e3+4*e2+2*e1+e0
W1f = ((3*e3+2*e2+e1) % 5)*25 + (T51 % 5)*5 + ((T51//5 + g3+g2+g1+g0) % 5)
W2f = ((4 + 2*e3+4*e2+e1) % 5)*25 + (T52 % 5)*5 + ((T52//5 + 3*g3+4*g2+2*g1+g0) % 5)
check('P8 S2 form tables == literal digits (all members, both branches)',
      bool((W1f == W[1]).all() and (W2f == W[2]).all()))
# P1/P2 marginals + joint contingency
m1 = np.bincount(W[1], minlength=125); m2 = np.bincount(W[2], minlength=125)
check('P1 marginal words: N(W_r=w)=3125 for all 125 words, both branches',
      bool((m1 == 3125).all() and (m2 == 3125).all()),
      f'r=1 min/max {m1.min()}/{m1.max()}, r=2 {m2.min()}/{m2.max()}')
J = np.bincount(W[1]*125 + W[2], minlength=15625)
check('P2 joint contingency: N(pair)=25 at ALL 15625 pairs (uniform on F5^6)',
      bool((J == 25).all()), f'min={J.min()} max={J.max()}')
check('P2b product identity N(pair)*N(Sigma)==N(w1)*N(w2) at EVERY pair (census numbers)',
      bool((J*NSIG == np.outer(m1, m2).ravel()).all()))
# P3-P5 families (S1, S2 events; counts + product identities from census numbers)
res = {'L1': {}}
def fam(name, S1, S2, sealed):
    N1, N2, NJ = int(S1.sum()), int(S2.sum()), int((S1 & S2).sum())
    check(f'{name} counts N1/N2/NJ = {sealed[0]}/{sealed[1]}/{sealed[2]}',
          (N1, N2, NJ) == sealed, f'{N1}/{N2}/{NJ}')
    check(f'{name} product identity NJ*NSigma == N1*N2', NJ*NSIG == N1*N2,
          f'{NJ}*{NSIG} = {NJ*NSIG} vs {N1}*{N2} = {N1*N2}')
    return (N1, N2, NJ)
u1w, v1w, w1w = W[1]//25, (W[1]//5) % 5, W[1] % 5
u2w, v2w, w2w = W[2]//25, (W[2]//5) % 5, W[2] % 5
res['L1']['famA'] = fam('P3 family A: S1={v1=1} x S2={v2=2}', v1w == 1, v2w == 2,
                        (78125, 78125, 15625))
res['L1']['famB'] = fam('P4 family B: S1={W1=(0,0,1)} x S2={v2=2}', W[1] == 1, v2w == 2,
                        (3125, 78125, 625))
# in-script residual classification z^2+uz+w over F5 (w != 0)
SPLIT, INERT, DBL = set(), set(), set()
for uu in range(5):
    for ww in range(1, 5):
        rts = [z for z in range(5) if (z*z + uu*z + ww) % 5 == 0]
        (SPLIT if len(rts) == 2 else (DBL if len(rts) == 1 else INERT)).add((uu, ww))
check('P5 in-script split set == sealed {(2,2),(1,3),(0,4),(0,1),(4,3),(3,2)}',
      SPLIT == {(2, 2), (1, 3), (0, 4), (0, 1), (4, 3), (3, 2)}, sorted(SPLIT))
split_idx = np.array(sorted(uu*25 + ww for (uu, ww) in SPLIT))
res['L1']['famC'] = fam('P5 family C: S1={b1 SPLITS} x S2={b2 RAM}',
                        np.isin(W[1], split_idx), v2w != 0, (18750, 312500, 15000))
# P7 outcome classes per branch
inert_idx = np.array(sorted(uu*25 + ww for (uu, ww) in INERT))
dbl_idx = np.array(sorted(uu*25 + ww for (uu, ww) in DBL))
for r, (uw, vw, ww_) in ((1, (u1w, v1w, w1w)), (2, (u2w, v2w, w2w))):
    side2 = vw == 0
    cls = (int((vw != 0).sum()), int((side2 & np.isin(W[r], split_idx)).sum()),
           int((side2 & np.isin(W[r], inert_idx)).sum()),
           int((side2 & np.isin(W[r], dbl_idx)).sum()), int((side2 & (ww_ == 0)).sum()))
    check(f'P7 outcome classes r={r} RAM/split/inert/double/deep = '
          f'312500/18750/31250/12500/15625 (sum {sum(cls)})',
          cls == (312500, 18750, 31250, 12500, 15625), cls)
    res['L1'][f'classes_r{r}'] = cls
log(f'  L1 primary done, {time.time()-T0:.0f}s')
# P13 L1 deepened pass: full 5^12 (e,g,h)-enumeration, chunked over the 625 h-tuples
mism = 0
Jdeep = np.zeros(15625, np.int64)
for hidx in range(625):
    h = (hidx % 5, (hidx//5) % 5, (hidx//25) % 5, (hidx//125) % 5)
    Wh, _ = words_L1(*coeffs_L1(h))
    mism += int((Wh[1] != W[1]).sum() + (Wh[2] != W[2]).sum())
    Jdeep += np.bincount(Wh[1]*125 + Wh[2], minlength=15625)
check('P13 L1 h-invariance: 0 word changes across the FULL 5^12 (e,g,h) pass', mism == 0,
      f'{mism} changes')
check('P13 L1 deepened joint contingency == 625 x primary (15625 per pair)',
      bool((Jdeep == 625*J).all()), f'min={Jdeep.min()} max={Jdeep.max()}')
res['L1'].update(NSigma=NSIG, joint_min=int(J.min()), joint_max=int(J.max()),
                 marg_ok=bool((m1 == 3125).all() and (m2 == 3125).all()))
log(f'  L1 deepened 5^12 pass done, {time.time()-T0:.0f}s')

# ================================ LAYER 2 ================================
log('=== LAYER 2: mixed-shape cubic cell p=2 n=3 (0,0,1) ===')
i2 = np.arange(2**15, dtype=np.int64)
mm2, mm1, mm0 = i2 // 512, (i2 // 16) % 32, i2 % 16
L2NS = 2**15

def inv_odd(x, mod):
    i = x % 8
    for _ in range(5):
        i = (i * (2 - x*i)) % mod
    return i % mod

def words_L2(cc2, cc1, cc0, KK=16):
    mod = 1 << KK
    A, Bq, C = (cc2 // 2) % mod, (cc1 // 4) % mod, (cc0 // 8) % mod
    z = np.ones_like(A)
    for _ in range(6):
        Gz = (((z + A) * z + Bq) * z + C) % mod
        Gp = ((3*z + 2*A) * z + Bq) % mod
        z = (z - Gz * inv_odd(Gp, mod)) % mod
    Gz = (((z + A) * z + Bq) * z + C) % mod
    alpha = 2*z
    a = (cc2 + alpha) % (2*mod)
    b = (cc1 + alpha*a) % (2*mod)
    resid = (cc0 + alpha*b) % mod
    ok = bool((Gz == 0).all() and (resid == 0).all() and (a % 4 == 2).all()
              and (b % 8 == 4).all() and (z % 2 == 1).all())
    WL = ((z >> 1) & 1)*2 + ((z >> 2) & 1)   # (t1, t2)
    WQ = ((a >> 2) & 1)*2 + ((b >> 3) & 1)   # (a2, b3)
    return WL, WQ, ok

cc2, cc1, cc0 = 4*mm2, 8*mm1, 8*(1 + 2*mm0)
WL, WQ, okL2 = words_L2(cc2, cc1, cc0)
check('L2 exactness: G(zeta)=0, c0+alpha*b=0 (mod 2^16), alpha=2 mod 4, a=2 mod 4, '
      'b=4 mod 8 on ALL 32768 members', okL2)
mL = np.bincount(WL, minlength=4); mQ = np.bincount(WQ, minlength=4)
check('P9 marginals: N(W_L=x)=N(W_Q=y)=8192 for all x,y',
      bool((mL == 8192).all() and (mQ == 8192).all()), f'{list(mL)} {list(mQ)}')
J2 = np.bincount(WL*4 + WQ, minlength=16)
check('P10 joint: N=2048 at all 16 pairs', bool((J2 == 2048).all()), list(map(int, J2)))
check('P10b product identity at every pair', bool((J2*L2NS == np.outer(mL, mQ).ravel()).all()))
res['L2'] = {'joint': list(map(int, J2)), 'margL': list(map(int, mL)), 'margQ': list(map(int, mQ))}
# P11 union pair
S1u = (WL // 2) == 0                      # t1 = 0
S2u = (WQ == 0) | (WQ == 3)               # (a2,b3) in {(0,0),(1,1)}
N1u, N2u, NJu = int(S1u.sum()), int(S2u.sum()), int((S1u & S2u).sum())
check('P11 union pair counts 16384/16384/8192', (N1u, N2u, NJu) == (16384, 16384, 8192),
      f'{N1u}/{N2u}/{NJu}')
check('P11 product identity NJ*NSigma == N1*N2', NJu*L2NS == N1u*N2u,
      f'{NJu}*{L2NS} vs {N1u}*{N2u}')
res['L2']['famU'] = (N1u, N2u, NJu)
# P12 literal 2^24 membership pass (chunked over c2)
tot = 0
c1c0 = np.arange(2**16, dtype=np.int64)
c1v, c0v = c1c0 >> 8, c1c0 & 255
inner = ((c1v % 8 == 0) & (c0v % 16 == 8))
for c2r in range(256):
    tot += int(inner.sum()) if c2r % 4 == 0 else 0
check('P12 literal 2^24 membership count == 32768', tot == 2**15, tot)
# P13 L2 deepening: 1e5 random extensions beyond level 8, words unchanged
rng = np.random.default_rng(20260727)
nS = 10**5
pk = rng.integers(0, L2NS, nS)
d2, d1, d0 = (rng.integers(0, 256, nS) for _ in range(3))
WLd, WQd, okd = words_L2(cc2[pk] + 256*d2, cc1[pk] + 256*d1, cc0[pk] + 256*d0)
check('P13 L2 deepening: 0 word changes over 1e5 random extensions (exactness holds too)',
      okd and bool((WLd == WL[pk]).all() and (WQd == WQ[pk]).all()),
      f'{int((WLd != WL[pk]).sum() + (WQd != WQ[pk]).sum())} changes')
log(f'  L2 done, {time.time()-T0:.0f}s')

# ================================ LAYER 3 ================================
log('=== LAYER 3: m=3 depth-0 cell p=5 n=3 (4,1,4) ===')
i3 = np.arange(5**6, dtype=np.int64)
n2, n1, n0 = i3 // 125, (i3 // 5) % 25, i3 % 5
L3NS = 5**6

def inv_unit5(x, mod):
    i = pow5inv[x % 5] * np.ones_like(x)
    i = np.where(x % 5 == 0, 1, i)        # never used at multiples of 5 (units only)
    for _ in range(5):
        i = (i * (2 - x*i)) % mod
    return i % mod

pow5inv = np.array([0, 1, 3, 2, 4], dtype=np.int64)   # inverses mod 5

def roots_L3(cc2, cc1, cc0, KK=7):
    mod = 5**KK
    A, Bq, C = (cc2 // 5) % mod, (cc1 // 25) % mod, (cc0 // 125) % mod
    ts, ok = [], True
    for j in (1, 2, 3):
        z = j*np.ones_like(A)
        for _ in range(6):
            Gz = (((z + A) * z + Bq) * z + C) % mod
            Gp = ((3*z + 2*A) * z + Bq) % mod
            z = (z - Gz * inv_unit5(Gp, mod)) % mod
        Gz = (((z + A) * z + Bq) * z + C) % mod
        ok = ok and bool((Gz == 0).all() and (z % 5 == j).all())
        ts.append(((z - j) // 5) % 5)
    return ts, ok

cc2, cc1, cc0 = 5*(4 + 5*n2), 25*(1 + 5*n1), 125*(4 + 5*n0)
(t1, t2, t3), okL3 = roots_L3(cc2, cc1, cc0)
check('L3 exactness: G(zeta_j)=0 mod 5^7, zeta_j = j mod 5, all members, j=1,2,3', okL3)
m3 = [np.bincount(t, minlength=5) for t in (t1, t2, t3)]
check('P14 marginals: N(t_j=t)=3125 for all t, j',
      all(bool((m == 3125).all()) for m in m3), [list(map(int, m)) for m in m3])
pw_ok = True
for (a, b) in ((t1, t2), (t1, t3), (t2, t3)):
    pw_ok = pw_ok and bool((np.bincount(a*5 + b, minlength=25) == 625).all())
check('P15 pairwise contingencies: 625 at all 25 cells, all 3 pairs', pw_ok)
J3 = np.bincount(t1*25 + t2*5 + t3, minlength=125)
check('P15 triple contingency: 125 at all 125 cells', bool((J3 == 125).all()),
      f'min={J3.min()} max={J3.max()}')
trip_ok = bool((J3.astype(np.int64)*L3NS*L3NS ==
                np.einsum('i,j,k->ijk', m3[0], m3[1], m3[2]).ravel()).all())
check('P15 triple product identity NJ*NSigma^2 == N1*N2*N3 at every cell', trip_ok)
res['L3'] = {'triple_min': int(J3.min()), 'triple_max': int(J3.max()),
             'marg': [list(map(int, m)) for m in m3]}
# P13 L3 deepening: 1e5 random extensions, working modulus 5^9
pk = rng.integers(0, L3NS, nS)
d2, d1, d0 = rng.integers(0, 5**4, nS), rng.integers(0, 5**4, nS), rng.integers(0, 5**4, nS)
(t1d, t2d, t3d), okd3 = roots_L3(cc2[pk] + 5**5*d2, cc1[pk] + 5**5*d1, cc0[pk] + 5**5*d0, KK=9)
check('P13 L3 deepening: 0 word changes over 1e5 random extensions',
      okd3 and bool((t1d == t1[pk]).all() and (t2d == t2[pk]).all() and (t3d == t3[pk]).all()),
      f'{int((t1d != t1[pk]).sum() + (t2d != t2[pk]).sum() + (t3d != t3[pk]).sum())} changes')
log(f'  L3 done, {time.time()-T0:.0f}s')

# ================================ SUMMARY ================================
res['verdicts'] = verdicts
npass = sum(1 for v in verdicts if v['ok']); nfail = len(verdicts) - npass
log(f'\n==== CASE-SIB GATE: {npass} PASS / {nfail} FAIL of {len(verdicts)} sealed verdict '
    f'families ({time.time()-T0:.0f}s) ====')
log('GATE VERDICT: ' + ('PASS' if nfail == 0 else 'FAIL — falsifier(s) fired; seal untouched'))
with open('/data/users/asvin/math-and-lean/p-adic-splitting-densities/verification/results/'
          'case_sib_results.json', 'w') as fh:
    json.dump(res, fh, indent=1, default=str)
log('JSON written.')
