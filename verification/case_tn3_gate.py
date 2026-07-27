#!/usr/bin/env python3
# case_tn3_gate.py — CASE-TN3 census (T-n3, the RECURSION gate). Written AFTER
# CASE_TN3_SEALED_PREDICTIONS.md was sealed (Case-K discipline; seal S4 is the spec).
# A: B22 5^8 depth-1 tree walk (hull walker = independent VP, not word lookup);
# B: B26 5^12 (625 h-chunks x 5^8) depth-2 prescribed subtree; C: marks/dictionary
# vs committed d4m2. Output -> /tmp/tn3_census.out; JSON -> results/case_tn3_results.json
import numpy as np, json, time, math
T0 = time.time()
def log(s=''): print(s, flush=True)
verdicts = []
def check(name, ok, detail=''):
    verdicts.append({'name': name, 'ok': bool(ok), 'detail': str(detail)})
    log(f"[{'PASS' if ok else 'FAIL'}] {name}  {detail}")
def digit(x, l): return (x // 5**l) % 5

def develop(c, s, k):
    """First k development coefficients B0..B(k-1) of poly c (high->low) at (x-s)."""
    B, cur = [], list(c)
    for _ in range(k):
        q = [cur[0]]
        for a in cur[1:-1]:
            q.append(a + s*q[-1])
        B.append(cur[-1] + s*q[-1]); cur = q
    return B

def factor_marks(a):
    """a: low->high coeff list over F5, monic. -> {root r: ord_r} (exact ords)."""
    out = {}
    for r in range(5):
        c, o = [x % 5 for x in a], 0
        while len(c) > 1:
            hi = c[::-1]; q = [hi[0]]
            for t in hi[1:-1]:
                q.append((t + r*q[-1]) % 5)
            if (hi[-1] + r*q[-1]) % 5 != 0:
                break
            o += 1; c = q[::-1]
        if o: out[r] = o
    return out

# residual quadratic z^2 + u z + w (w != 0) classification tables (in-script derived)
QC = np.zeros(25, np.int8); QS = np.full(25, -1, np.int8)
for u in range(5):
    for w in range(1, 5):
        rts = [z for z in range(5) if (z*z + u*z + w) % 5 == 0]
        if len(rts) == 2: QC[u*5+w] = 1                       # split
        elif len(rts) == 0: QC[u*5+w] = 2                     # inert
        else:
            s = rts[0]; assert (-2*s) % 5 == u and (s*s) % 5 == w
            QC[u*5+w] = 3; QS[u*5+w] = s                      # double root s

idx = np.arange(5**8, dtype=np.int64)
E = [(idx // 5**k) % 5 for k in range(4)]        # e0,e1,e2,e3
G = [(idx // 5**(4+k)) % 5 for k in range(4)]    # g0,g1,g2,g3
NA = 5**8
Z4 = (0, 0, 0, 0)

def make_coeffs(e, g, h=Z4, k=Z4):
    """e,g,h,k indexed (c3-part, c2-part, c1-part, c0-part)."""
    c3 = 5*(4 + 5*e[0] + 25*g[0] + 125*h[0] + 625*k[0])
    c2 = 25*(3 + 5*e[1] + 25*g[1] + 125*h[1] + 625*k[1])
    c1 = 125*(3 + 5*e[2] + 25*g[2] + 125*h[2] + 625*k[2])
    c0 = 625*(4 + 5*e[3] + 25*g[3] + 125*h[3] + 625*k[3])
    return c3, c2, c1, c0
EB = (E[3], E[2], E[1], E[0]); GB = (G[3], G[2], G[1], G[0])

def walk1(c3, c2, c1, c0):
    """Depth-1 hull walker per branch r=1,2 (independent VP: valuation reads, hull
    test, residual factorization, tau = saturation). cls: 0 RAM leaf (2,1) / 1 split
    (two (1,1) leaves) / 2 inert ((1,2) leaf) / 3 double (CONTINUE) / 4 DEEPER."""
    ONE = np.ones_like(c3)
    out = {}
    for r in (1, 2):
        B0, B1, B2 = develop([ONE, c3, c2, c1, c0], 5*r, 3)
        state = bool(((B2 % 25 == 0) & (digit(B2, 2) == 1) & (B1 % 5**4 == 0)
                      & (B0 % 5**5 == 0)).all())
        u, v, w = digit(B1, 4), digit(B0, 5), digit(B0, 6)
        vB1 = np.where(u != 0, 4, np.where(digit(B1, 5) != 0, 5, 6))   # capped read
        vB0 = np.where(v != 0, 5, np.where(w != 0, 6, 7))              # capped read
        two_side = (2*vB1 < 2 + vB0)     # genuine hull test vs segment (2,2)-(0,vB0)
        # vB0=5: slope 3/2 side, e=2, linear residual, mu=1 -> tau-irr halt (2,1);
        # vB0=6: slope 2 side (on-line (1,4) coeff = u), quadratic residual -> QC;
        # vB0>=7 (cap): DEEPER (incl. two_side partial hulls) — not T_A/T_B.
        cls = np.where(vB0 == 5, 0,
                       np.where(vB0 == 6, QC[(u*5 + w).astype(np.int64)], 4))
        out[r] = dict(cls=cls, leaf=np.where(cls == 0, v, 0),
                      dbl=np.where(cls == 3, QS[(u*5 + w).astype(np.int64)], -1),
                      word=u*25 + v*5 + w, state=state,
                      twoside=int((two_side & (vB0 == 7)).sum()))
    return out

def walk2(c3, c2, c1, c0, mask):
    """Depth-2 walk at the naive recentre x-30 (s=1). Returns v' = digit7(C0) and
    the count of transported-state violations on the mask (sealed B1: zero)."""
    C0, C1, C2 = develop([np.ones_like(c3), c3, c2, c1, c0], 30, 3)
    stviol = int((mask & ~((C2 % 25 == 0) & (digit(C2, 2) == 1)
                           & (C1 % 5**5 == 0) & (C0 % 5**7 == 0))).sum())
    return digit(C0, 7), stviol

# ================================ LAYER A ================================
log('=== LAYER A: B22 5^8 depth-1 tree walk (hull walker) ===')
res = {}
c3, c2, c1, c0 = make_coeffs(EB, GB)
pins = bool(((c3 % 5 == 0) & (digit(c3, 1) == 4) & (c2 % 25 == 0) & (digit(c2, 2) == 3)
             & (c1 % 125 == 0) & (digit(c1, 3) == 3) & (c0 % 625 == 0)
             & (digit(c0, 4) == 4)).all())
R0m = factor_marks([4, 3, 3, 4, 1])
W = walk1(c3, c2, c1, c0)
cls1, cls2 = W[1]['cls'], W[2]['cls']
leaf1, leaf2 = W[1]['leaf'], W[2]['leaf']
check('A1 root read re-derived: 14 pins on all members; R0 = (z-1)^2(z-2)^2, branch '
      'set {1,2} mu=2 both (continue: E*F=1 != 2)', pins and R0m == {1: 2, 2: 2}, R0m)
CLS_SEAL = (312500, 18750, 31250, 12500, 15625)
for r in (1, 2):
    cc = tuple(int((W[r]['cls'] == k).sum()) for k in range(5))
    check(f'A1 walker classes r={r} RAM/split/inert/double/DEEPER = {CLS_SEAL} '
          f'(state transport ok={W[r]["state"]})',
          cc == CLS_SEAL and W[r]['state'], f'{cc}, twoside-partial={W[r]["twoside"]}')
    res[f'A1_classes_r{r}'] = cc
# A2/A3: the fixed value tree T_A = (a1,a2) = (1,2)
fibA = (cls1 == 0) & (leaf1 == 1) & (cls2 == 0) & (leaf2 == 2)
NfibA = int(fibA.sum())
check('A2 direct fiber N{T_can^tau(f) = T_A} = 15625', NfibA == 15625, NfibA)
N1 = int(((cls1 == 0) & (leaf1 == 1)).sum()); N2 = int(((cls2 == 0) & (leaf2 == 2)).sum())
check('A3 branch masses 78125/78125 and N(fib)*N_A == N(S1)*N(S2) = 6103515625',
      (N1, N2) == (78125, 78125) and NfibA*NA == N1*N2 == 6103515625,
      f'{N1}/{N2}; {NfibA}*{NA}={NfibA*NA} vs {N1*N2}')
# A4/A5: the 16-fiber grid + sigma aggregate (verdict multisets honestly compared)
VER = {0: [(2, 1)], 1: [(1, 1), (1, 1)], 2: [(1, 2)]}
sig_pairs = [(i, j) for i in range(3) for j in range(3)
             if sorted(VER[i] + VER[j]) == [(2, 1), (2, 1)]]
bothRAM = (cls1 == 0) & (cls2 == 0)
grid = np.bincount(((leaf1 - 1)*4 + (leaf2 - 1))[bothRAM], minlength=16)
m1 = np.bincount(leaf1[cls1 == 0], minlength=5)[1:]
m2 = np.bincount(leaf2[cls2 == 0], minlength=5)[1:]
sig_direct = sum(int(((cls1 == i) & (cls2 == j)).sum()) for (i, j) in sig_pairs)
check('A4 sigma-aggregate: all 16 fibers = 15625 (min=max); Sigma = 250000 = 16*15625;'
      ' direct typemult count = 250000; sigma-pairs = {(RAM,RAM)} only (multiset calc)',
      bool((grid == 15625).all()) and int(grid.sum()) == 250000
      and sig_direct == 250000 and sig_pairs == [(0, 0)],
      f'min={grid.min()} max={grid.max()} sum={int(grid.sum())} direct={sig_direct}')
check('A4b SIBLING INDEXING: fiber(1,2) and fiber(2,1) BOTH 15625 (no /2; the false'
      ' alternative 125000 refuted)', int(grid[0*4+1]) == 15625 == int(grid[1*4+0])
      and int(grid.sum()) != 125000, f'{int(grid[1])}/{int(grid[4])}')
check('A5 per-fiber identities N(fib)*N_A == N(v1=a1)*N(v2=a2) at ALL 16 pairs '
      '(all branch masses 78125)',
      bool((grid.astype(object)*NA == np.outer(m1, m2).astype(object).ravel()).all())
      and bool((m1 == 78125).all() and (m2 == 78125).all()),
      f'm1={list(map(int, m1))} m2={list(map(int, m2))}')
# A6 joint class contingency -> sigma partition of the depth-1-decided set
CT = np.bincount((cls1*5 + cls2).astype(np.int64), minlength=25).reshape(5, 5)
rows = dict(RR=int(CT[0, 0]), RS=int(CT[0, 1] + CT[1, 0]), RI=int(CT[0, 2] + CT[2, 0]),
            SS=int(CT[1, 1]), SI=int(CT[1, 2] + CT[2, 1]), II=int(CT[2, 2]))
decided = int(CT[:3, :3].sum())
A6_SEAL = dict(RR=250000, RS=30000, RI=50000, SS=900, SI=3000, II=2500)
check('A6 sigma-partition RR/RS/RI/SS/SI/II = 250000/30000/50000/900/3000/2500; '
      'decided 336400; undecided 54225',
      rows == A6_SEAL and decided == 336400 and NA - decided == 54225,
      f'{rows} decided={decided}')
res['A6'] = rows | {'decided': decided}
# A7 SIB re-confirmation (attribution prerequisite): joint word contingency
JA = np.bincount(W[1]['word']*125 + W[2]['word'], minlength=15625)
check('A7 SIB word law re-confirmed: joint contingency = 25 at ALL 15625 pairs',
      bool((JA == 25).all()), f'min={JA.min()} max={JA.max()}')
# C4 (computed here, verdict logged with Layer C): RAM-marks histogram + dictionary
rammarks = (cls1 == 0).astype(np.int64) + (cls2 == 0).astype(np.int64)
mh = np.bincount(rammarks, minlength=3)
res['C4_hist'] = [int(x) for x in mh]
log(f'  Layer A done, {time.time()-T0:.0f}s')

# ================================ LAYER B ================================
log('=== LAYER B: B26 5^12 depth-2 prescribed subtree (625 h-chunks) ===')
CELL_W = 3*25 + 0*5 + 1                                   # word (u,v,w) = (3,0,1)
Jacc = np.zeros(15625, np.int64)
vp_hist = np.zeros(5, np.int64)
Ncell = NST2 = Nfib = stviol_tot = word_mism = b6_mism = mask_mism = 0
w1_0, w2_0 = W[1]['word'].copy(), W[2]['word'].copy()
mask0 = (w1_0 == CELL_W)
vp0 = None
for hidx in range(625):
    h = (hidx % 5, (hidx//5) % 5, (hidx//25) % 5, (hidx//125) % 5)   # (h3,h2,h1,h0)
    hc3, hc2, hc1, hc0 = make_coeffs(EB, GB, h)
    Wh = walk1(hc3, hc2, hc1, hc0)
    word_mism += int((Wh[1]['word'] != w1_0).sum() + (Wh[2]['word'] != w2_0).sum())
    Jacc += np.bincount(Wh[1]['word']*125 + Wh[2]['word'], minlength=15625)
    mask = Wh[1]['word'] == CELL_W
    mask_mism += int((mask != mask0).sum())
    vp, sv = walk2(hc3, hc2, hc1, hc0, mask)
    stviol_tot += sv
    if hidx == 0:
        vp0 = vp.copy()
    else:
        b6_mism += int((vp[mask] != (vp0[mask] + sum(h)) % 5).sum())
    Ncell += int(mask.sum())
    vp_hist += np.bincount(vp[mask], minlength=5)
    s2 = (Wh[2]['cls'] == 0) & (Wh[2]['leaf'] == 3)
    NST2 += int(s2.sum())
    Nfib += int((mask & (vp == 2) & s2).sum())
    if hidx % 125 == 124:
        log(f'  chunk {hidx+1}/625, {time.time()-T0:.0f}s')

NB = 5**12
check('B7 SIB re-confirmed in B26: depth-1 words h-invariant member-wise (0 changes);'
      ' joint contingency = 15625 at ALL 15625 pairs (= 5^4 x SIB P2)',
      word_mism == 0 and mask_mism == 0 and bool((Jacc == 15625).all()),
      f'word_mism={word_mism} Jmin={Jacc.min()} Jmax={Jacc.max()}')
check('B1 N{W1=(3,0,1)} = 1953125; transported state v(C2)=2 unit 1, v(C1)>=5, '
      'v(C0)>=7 on ALL its members', Ncell == 1953125 and stviol_tot == 0,
      f'Ncell={Ncell} state_violations={stviol_tot}')
check('B2 direct depth-2 fiber N{T_can^tau(f) = T_B} = 78125', Nfib == 78125, Nfib)
NST1 = int(vp_hist[2])
check('B3 recursion both ways: N(S_T1)=390625, N(S_T2)=48828125; N(fib)*N_B == '
      'N(S_T1)*N(S_T2) = 5^19', NST1 == 390625 and NST2 == 48828125
      and Nfib*NB == NST1*NST2 == 19073486328125,
      f'{NST1}/{NST2}; {Nfib}*{NB}={Nfib*NB} vs {NST1*NST2}')
check('B4 depth-2 chain step exactly uniform: N{vp=t & cell} = 390625 for EVERY t; '
      'N(S_T1) = N(cell)/5', bool((vp_hist == 390625).all()) and NST1*5 == Ncell,
      f'vp_hist={[int(x) for x in vp_hist]}')
check('B6 h-block form: vp(e,g,h) - vp(e,g,0) == h3+h2+h1+h0 (mod 5) on all mask '
      'members, all 624 nonzero h-chunks (F3-style: display check)', b6_mism == 0,
      f'{b6_mism} mismatches')
res['B'] = dict(Ncell=Ncell, NST1=NST1, NST2=NST2, Nfib=Nfib,
                vp_hist=[int(x) for x in vp_hist])
log(f'  Layer B done, {time.time()-T0:.0f}s')

# B5 stability: >= 1e5 random members of B26, random fresh digits beyond the box
rng = np.random.default_rng(20260727)
nS = 10**5
re_ = tuple(rng.integers(0, 5, nS) for _ in range(4))
rg = tuple(rng.integers(0, 5, nS) for _ in range(4))
rh = tuple(rng.integers(0, 5, nS) for _ in range(4))
rk = tuple(rng.integers(0, 5, nS) for _ in range(4))

def walk_all(k):
    cs = make_coeffs(re_, rg, rh, k)
    Ws = walk1(*cs)
    mask = Ws[1]['word'] == CELL_W
    vp, sv = walk2(*cs, mask)
    fib = mask & (vp == 2) & (Ws[2]['cls'] == 0) & (Ws[2]['leaf'] == 3)
    return Ws[1]['word'], Ws[2]['word'], np.where(mask, vp, -1), fib, sv

w1a, w2a, vpa, fa, sva = walk_all(Z4)
w1b, w2b, vpb, fb, svb = walk_all(rk)
ch = int((w1a != w1b).sum() + (w2a != w2b).sum() + (vpa != vpb).sum() + (fa != fb).sum())
check('B5 stability: 10^5 random extensions beyond B26 (k-digits at c3 lv5, c2 lv6, '
      'c1 lv7, c0 lv8): W1, W2, vp, fiber membership all unchanged',
      ch == 0 and sva == 0 and svb == 0, f'{ch} changes')

# ================================ LAYER C ================================
log('=== LAYER C: marks/dictionary vs committed d4m2 ===')
event_tab = {}
mism_marks = tot_marks = 0
for t in range(625):
    d3, d2, d1, d0 = t//125, (t//25) % 5, (t//5) % 5, t % 5
    if d0 == 0:
        continue
    a = [d0, d1, d2, d3, 1]
    ords = factor_marks(a)
    assert 0 not in ords
    marks = tuple(sorted(r for r, o in ords.items() if o == 2))
    # independent Taylor-shift mult (d4m2 method)
    mult = tuple(r for r in range(1, 5)
                 if [sum(a[j]*math.comb(j, kk)*pow(r, j-kk, 5) for j in range(kk, 5)) % 5
                     for kk in range(3)][:2] == [0, 0]
                 and sum(a[j]*math.comb(j, 2)*pow(r, j-2, 5) for j in range(2, 5)) % 5 != 0)
    if marks != mult:
        mism_marks += 1
    tot_marks += len(marks)
    if marks:
        event_tab[(d3, d2, d1, d0)] = marks
hist = {k: sum(1 for v in event_tab.values() if len(v) == k) for k in (1, 2)}
hist3 = sum(1 for v in event_tab.values() if len(v) >= 3)
check('C1 marks == mult member-wise (full factorization vs Taylor shift, all d0!=0 '
      'tuples); event hist {1: 52, 2: 6, >=3: 0}; one cell per event box',
      mism_marks == 0 and hist == {1: 52, 2: 6} and hist3 == 0,
      f'mism={mism_marks} hist={hist}')
with open('/data/users/asvin/math-and-lean/p-adic-splitting-densities/verification/'
          'results/case_d4m2_results.json') as fh:
    d4 = json.load(fh)
ess = d4['essential_p5']
reg = {tuple(int(x) for x in kk.strip('()').split(',')): tuple(vv)
       for kk, vv in ess['REG'].items()}
check('C2 totals vs committed d4m2: marked 64 / event 58 / gap 6; committed registry'
      ' == walker table verbatim (58 cells)',
      tot_marks == 64 == ess['SUM'] and len(event_tab) == 58 == ess['EVENT']
      and ess['GAP'] == 6 and reg == event_tab, f'C={tot_marks} E={len(event_tab)}')
SIX = {(0, 2, 0, 1): (2, 3), (0, 3, 0, 1): (1, 4), (1, 3, 2, 4): (3, 4),
       (2, 2, 1, 4): (1, 3), (3, 2, 4, 4): (2, 4), (4, 3, 3, 4): (1, 2)}
two = {cell: v for cell, v in event_tab.items() if len(v) == 2}
check('C3 two-double-root sigma: direct per-f count = 6 (the six sealed cells '
      'verbatim) = tree-fiber sum; marked on them = 12; overcount = 6',
      two == SIX and sum(len(v) for v in two.values()) == 12
      and tot_marks - len(event_tab) == 6, f'{sorted(two)}')
mh0, mh1, mh2 = (int(x) for x in res['C4_hist'])
wtot = mh1 + 2*mh2
check('C4 the F1 (ONE-F) instance: #RAM-marks hist {0: 15625, 1: 125000, 2: 250000};'
      ' marked total 625000 = 2*312500 = 2*250000 + 125000; per-f sigma count 250000'
      ' (= tree-fiber sum, NOT the marked total; excess 375000)',
      (mh0, mh1, mh2) == (15625, 125000, 250000) and wtot == 625000 == 2*312500
      and wtot == 2*250000 + 125000 and mh2 == 250000 and wtot - mh2 == 375000,
      f'hist=({mh0},{mh1},{mh2}) marked={wtot}')

# ================================ SUMMARY ================================
res['verdicts'] = verdicts
npass = sum(1 for v in verdicts if v['ok']); nfail = len(verdicts) - npass
log(f'\n==== CASE-TN3 GATE: {npass} PASS / {nfail} FAIL of {len(verdicts)} sealed '
    f'verdict families ({time.time()-T0:.0f}s) ====')
log('GATE VERDICT: ' + ('PASS' if nfail == 0 else 'FAIL — falsifier(s) fired; seal untouched'))
with open('/data/users/asvin/math-and-lean/p-adic-splitting-densities/verification/'
          'results/case_tn3_results.json', 'w') as fh:
    json.dump(res, fh, indent=1, default=str)
log('JSON written.')
