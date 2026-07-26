#!/usr/bin/env python3
# case_d4m2_gate.py — CASE-D4M2 census. Written AFTER CASE_D4M2_SEALED_PREDICTIONS.md
# was sealed (Case-K discipline; seal S5 is this script's specification).
# R1 p=5 essential 5^14; R2 p=3 FULL level-5 3^20; R3 p=3 essential 3^14 (+ an
# unhoisted cross-pass); R4 sampled deepening. Output -> /tmp/d4m2_census.out;
# JSON -> verification/results/case_d4m2_results.json
import numpy as np, json, time, math
T0 = time.time()
def log(s=''): print(s, flush=True)

# ---- sealed comparison targets (verbatim from the seal; the census may not edit) ----
SEAL = {
 5: dict(C=64, E=58, GAP=6, HIST={1: 52, 2: 6}, PERBR={1: 16, 2: 16, 3: 16, 4: 16},
         TYPES=(12, 40, 6),
         MULT2={(0,2,0,1): (2,3), (0,3,0,1): (1,4), (1,3,2,4): (3,4),
                (2,2,1,4): (1,3), (3,2,4,4): (2,4), (4,3,3,4): (1,2)}),
 3: dict(C=8, E=7, GAP=1, HIST={1: 6, 2: 1}, PERBR={1: 4, 2: 4}, TYPES=(0, 6, 1),
         TABLE={(0,2,1,2): (1,), (0,2,2,2): (2,), (1,1,0,2): (2,), (1,2,1,1): (1,),
                (2,1,0,2): (1,), (2,2,2,1): (2,), (0,1,0,1): (1,2)}),
}
LEVELS = {(5,5): dict(SUM=1000000, EVENT=906250, GAP=93750, H1=812500, H2=93750),
          (5,6): dict(SUM=625000000, EVENT=566406250, GAP=58593750, H1=507812500, H2=58593750),
          (3,5): dict(SUM=5832, EVENT=5103, GAP=729, H1=4374, H2=729),
          (3,6): dict(SUM=472392, EVENT=413343, GAP=59049, H1=354294, H2=59049)}
A_LEDGER = 14
verdicts = []
def check(name, ok, detail=''):
    verdicts.append({'name': name, 'ok': bool(ok), 'detail': str(detail)})
    log(f"[{'PASS' if ok else 'FAIL'}] {name}  {detail}")

# ---- branch table: INDEPENDENT re-derivation (Taylor shift; pre-seal used synthetic
# division stripping). B[T, r] = True iff (z-r)^2 || z^4+d3z^3+d2z^2+d1z+d0,
# T = ((d3*p+d2)*p+d1)*p+d0. Defined for all tuples; endpoint d0!=0 is a stratum pin.
def branch_table(p):
    n4 = p**4; idx = np.arange(n4)
    d0 = idx % p; d1 = (idx//p) % p; d2 = (idx//p**2) % p; d3 = (idx//p**3) % p
    a = [d0, d1, d2, d3, np.ones(n4, dtype=np.int64)]
    B = np.zeros((n4, p), dtype=bool)
    for r in range(p):
        e = [np.zeros(n4, dtype=np.int64) for _ in range(3)]
        for k in range(3):                      # need e0, e1, e2 only
            for j in range(k, 5):
                e[k] = (e[k] + a[j] * math.comb(j, k) * pow(r, j-k, p)) % p
        B[:, r] = (e[0] == 0) & (e[1] == 0) & (e[2] != 0)
    return B

def poly_roots(p, coeffs):                      # roots in F_p of poly given low->high
    return [r for r in range(p) if sum(c*pow(r, i, p) for i, c in enumerate(coeffs)) % p == 0]

def table_aggregates(p, B):
    """E, C, hist, per-branch, mult2 cells, and the (a)/(b)/(c) type counts."""
    idx = np.arange(p**4)
    tup = lambda t: (int((t//p**3) % p), int((t//p**2) % p), int((t//p) % p), int(t % p))
    ok = (idx % p) != 0
    m = B.sum(axis=1) * ok
    C = int(m.sum()); E = int((m > 0).sum())
    hist = {k: int((m == k).sum()) for k in (1, 2)}
    hist3 = int((m >= 3).sum())
    perbr = {r: int((B[:, r] & ok).sum()) for r in range(1, p)}
    mult2 = {tup(t): tuple(int(r) for r in range(1, p) if B[t, r])
             for t in np.nonzero(m >= 2)[0]}
    ta = tb = 0                                  # classify mult-1 cells: cofactor split?
    for t in np.nonzero(m == 1)[0]:
        d3, d2, d1, d0 = tup(t); r = int(np.nonzero(B[t])[0][0])
        c = [d0, d1, d2, d3, 1]                  # divide twice by (z-r), synthetic
        for _ in range(2):
            q, acc = [0]*(len(c)-1), 0
            for i in range(len(c)-1, 0, -1):
                acc = (acc*r + c[i]) % p; q[i-1] = acc
            c = q
        nroots = len(poly_roots(p, c))           # monic quadratic cofactor
        if nroots == 2: ta += 1
        elif nroots == 0: tb += 1
        else: raise AssertionError(f'cofactor with a double root at mult-1 cell {tup(t)}')
    tc = len(mult2)
    return dict(C=C, E=E, GAP=C-E, HIST=hist, HIST3=hist3, PERBR=perbr,
                MULT2=mult2, TYPES=(ta, tb, tc), mvec=m)

# ---- R1/R3: exhaustive essential box (c3 mod p^2, c2 mod p^3, c1 mod p^4, c0 mod p^5).
# Outer loop (c3, c2); inner 2-D broadcast (c1, c0). Outer pins (a30=a20=a21=0) are
# scalar stratum equations: a failed pin classifies the whole inner block as
# non-member (constant condition) — hoisted, tallied into hist[0]. An UNHOISTED full
# 4-D cross-pass is run at p=3 (below) to validate the hoisting code path.
def run_essential(p, B):
    P2, P3, P4, P5 = p**2, p**3, p**4, p**5
    c1v, c0v = np.arange(P4), np.arange(P5)
    a1 = [((c1v//p**l) % p)[:, None] for l in range(4)]
    a0 = [((c0v//p**l) % p)[None, :] for l in range(5)]
    inner_zero = ((a1[0]==0) & (a1[1]==0) & (a1[2]==0) &
                  (a0[0]==0) & (a0[1]==0) & (a0[2]==0) & (a0[3]==0) & (a0[4]!=0))
    Tin = (a1[3]*p + a0[4]).astype(np.int32)
    hist = np.zeros(8, np.int64); perbr = np.zeros(p, np.int64)
    sumw = event = total = 0; registry = {}
    for c3 in range(P2):
        a30, d3 = c3 % p, c3 // p
        for c2 in range(P3):
            a20, a21, d2 = c2 % p, (c2//p) % p, c2 // p**2
            total += P4*P5
            if a30 or a20 or a21:
                hist[0] += P4*P5; continue
            T = d3*P3 + d2*P2 + Tin
            M = B[T] & inner_zero[..., None]          # (P4, P5, p)
            mult = M.sum(axis=2, dtype=np.uint8)
            sumw += int(mult.sum()); event += int((mult > 0).sum())
            hist += np.bincount(mult.ravel(), minlength=8)
            perbr += M.sum(axis=(0, 1))
            for i1, i0 in np.argwhere(mult > 0):
                cell = (d3, d2, int(c1v[i1]//p**3), int(c0v[i0]//p**4))
                assert cell not in registry, f'cell {cell} realized twice in essential box'
                registry[cell] = tuple(int(r) for r in range(1, p) if M[i1, i0, r])
    assert total == p**14
    return dict(SUM=sumw, EVENT=event, GAP=sumw-event, HIST={1: int(hist[1]), 2: int(hist[2])},
                HIST3=int(hist[3:].sum()), PERBR={r: int(perbr[r]) for r in range(1, p)},
                REG=registry, TOTAL=total)

def run_essential_unhoisted(p, B):                     # full 4-D broadcast, no outer skip
    P2, P3, P4, P5 = p**2, p**3, p**4, p**5
    c3 = np.arange(P2)[:, None, None, None]; c2 = np.arange(P3)[None, :, None, None]
    c1 = np.arange(P4)[None, None, :, None]; c0 = np.arange(P5)[None, None, None, :]
    Z = ((c3 % p == 0) & (c2 % p == 0) & ((c2//p) % p == 0) &
         (c1 % p == 0) & ((c1//p) % p == 0) & ((c1//p**2) % p == 0) &
         (c0 % p == 0) & ((c0//p) % p == 0) & ((c0//p**2) % p == 0) & ((c0//p**3) % p == 0) &
         (c0//p**4 != 0))
    T = ((c3//p)*P3 + (c2//p**2)*P2 + (c1//p**3)*p + c0//p**4).astype(np.int32)
    mult = np.zeros(T.shape, np.uint8); perbr = np.zeros(p, np.int64)
    for r in range(1, p):
        Mr = B[:, r][T] & Z
        mult += Mr; perbr[r] = int(Mr.sum())
    hist = np.bincount(mult.ravel(), minlength=8)
    return dict(SUM=int(mult.sum()), EVENT=int((mult > 0).sum()),
                GAP=int(mult.sum()) - int((mult > 0).sum()),
                HIST={1: int(hist[1]), 2: int(hist[2])}, HIST3=int(hist[3:].sum()),
                PERBR={r: int(perbr[r]) for r in range(1, p)})

# ---- R2: p=3 FULL literal level-5 box (every (c3,c2,c1,c0) mod 3^5) ----
def run_full3(B):
    p, Q = 3, 3**5
    v = np.arange(Q); dig = [(v//p**l) % p for l in range(5)]
    ok3 = dig[0] == 0
    ok2 = ok3 & (dig[1] == 0)
    ok1 = ok2 & (dig[2] == 0)
    ok0 = ok1 & (dig[3] == 0) & (dig[4] != 0)          # v(c0) == 4 exactly
    hist = np.zeros(8, np.int64); perbr = np.zeros(p, np.int64)
    sumw = event = total = 0
    fiber = {r: np.zeros(p**4, np.int64) for r in range(1, p)}
    Z = ok2[:, None, None] & ok1[None, :, None] & ok0[None, None, :]
    Tbase = (dig[2][:, None, None]*9 + dig[3][None, :, None]*3 + dig[4][None, None, :]).astype(np.int32)
    for c3 in range(Q):
        total += Q**3
        if not ok3[c3]:
            hist[0] += Q**3; continue
        T = int(dig[1][c3])*27 + Tbase
        mult = np.zeros(T.shape, np.uint8)
        for r in range(1, p):
            Mr = B[:, r][T] & Z
            mult += Mr; perbr[r] += int(Mr.sum())
            fiber[r] += np.bincount(T[Mr].ravel(), minlength=p**4)
        sumw += int(mult.sum()); event += int((mult > 0).sum())
        hist += np.bincount(mult.ravel(), minlength=8)
    assert total == 3**20
    fibers = {(t, r): int(fiber[r][t]) for r in fiber for t in np.nonzero(fiber[r])[0]}
    return dict(SUM=sumw, EVENT=event, GAP=sumw-event, HIST={1: int(hist[1]), 2: int(hist[2])},
                HIST3=int(hist[3:].sum()), PERBR={r: int(perbr[r]) for r in range(1, p)},
                FIBERS=fibers, TOTAL=total)

# ---- R4: sampled deepening stability (valuation-reading code path) ----
def classify(p, B, cs, precs):
    """Branch bitmask per box from integer coefficients cs=(c3,c2,c1,c0) known mod
    p^precs[j]. Valuations computed by digit scan (capped at prec)."""
    def val(c, prec):
        v = np.full(c.shape, prec, np.int8)
        for l in range(prec-1, -1, -1):
            v[(c//p**l) % p != 0] = l
        return v
    c3, c2, c1, c0 = cs
    v3, v2, v1, v0 = (val(c, m) for c, m in zip(cs, precs))
    memb = (v3 >= 1) & (v2 >= 2) & (v1 >= 3) & (v0 == 4)
    T = (((c3//p) % p)*p**3 + ((c2//p**2) % p)*p**2 + ((c1//p**3) % p)*p + (c0//p**4) % p).astype(np.int32)
    bits = np.zeros(c3.shape, np.uint8)
    for r in range(1, p):
        bits |= (B[:, r][T] & memb).astype(np.uint8) << (r-1)
    return bits

def run_deepening(p, B, nsamp=10**6, seed=20260726):
    rng = np.random.default_rng(seed)
    deep = tuple(rng.integers(0, p**m, nsamp) for m in (4, 5, 6, 7))
    ess = tuple(c % p**m for c, m in zip(deep, (2, 3, 4, 5)))
    b_deep = classify(p, B, deep, (4, 5, 6, 7))
    b_ess = classify(p, B, ess, (2, 3, 4, 5))
    return int((b_deep != b_ess).sum())

# ================================ MAIN ================================
log(f'CASE-D4M2 census start {time.strftime("%F %T")}')
res = {}
for p in (5, 3):
    B = branch_table(p)
    agg = table_aggregates(p, B)
    s = SEAL[p]
    check(f'F6/P5 in-script table p={p}: C/E/gap/hist/perbr/types',
          agg['C'] == s['C'] and agg['E'] == s['E'] and agg['GAP'] == s['GAP'] and
          agg['HIST'] == s['HIST'] and agg['HIST3'] == 0 and agg['PERBR'] == s['PERBR'] and
          agg['TYPES'] == s['TYPES'],
          f"C={agg['C']} E={agg['E']} gap={agg['GAP']} hist={agg['HIST']} types={agg['TYPES']}")
    sealed_cells = s.get('MULT2') if p == 5 else {k: v for k, v in s['TABLE'].items() if len(v) == 2}
    check(f'P5 mult-2 cells p={p}', agg['MULT2'] == sealed_cells, agg['MULT2'])
    if p == 3:
        full_table = {tuple(map(int, k)): v for k, v in agg['MULT2'].items()}
    ess = run_essential(p, B)
    log(f'  R-essential p={p}: {ess["TOTAL"]:,} boxes, {time.time()-T0:.0f}s')
    check(f'P1 essential SUM p={p} = {s["C"]}', ess['SUM'] == s['C'], ess['SUM'])
    check(f'P2 essential EVENT p={p} = {s["E"]} (strictly below)',
          ess['EVENT'] == s['E'] and ess['EVENT'] < ess['SUM'], ess['EVENT'])
    check(f'P3 essential GAP p={p} = {s["GAP"]} (= {s["GAP"]}*{p}^-14 mass overcount)',
          ess['GAP'] == s['GAP'], ess['GAP'])
    check(f'P4 histogram p={p} {s["HIST"]} (+0 with mult>=3)',
          ess['HIST'] == s['HIST'] and ess['HIST3'] == 0, f"{ess['HIST']} mult>=3:{ess['HIST3']}")
    reg_seal = s['TABLE'] if p == 3 else None
    if p == 3:
        check('P5 registry p=3 (all 7 cells verbatim)', ess['REG'] == reg_seal, ess['REG'])
    else:
        m2 = {k: v for k, v in ess['REG'].items() if len(v) == 2}
        check('P5 registry p=5 (58 cells; 6 mult-2 verbatim; perbr 16 each)',
              len(ess['REG']) == 58 and m2 == s['MULT2'] and ess['PERBR'] == s['PERBR'], m2)
    check(f'P5 max branch count = 2 = mbar (L11 tight) p={p}',
          max(len(v) for v in ess['REG'].values()) == 2, '')
    for N in (5, 6):
        mul, L = p**(4*N-14), LEVELS[(p, N)]
        ok = (ess['SUM']*mul == L['SUM'] and ess['EVENT']*mul == L['EVENT'] and
              ess['GAP']*mul == L['GAP'] and ess['HIST'][1]*mul == L['H1'] and ess['HIST'][2]*mul == L['H2'])
        src = 'essential x p^(4N-14)' if p == 5 or N == 6 else 'essential (R2 literal below)'
        check(f'P6 level p={p} N={N} SUM/EVENT/GAP/hist ({src})', ok,
              f"{ess['SUM']*mul:,}/{ess['EVENT']*mul:,}/{ess['GAP']*mul:,}")
    check(f'P9 pool bound p={p}: C <= M*p^W', s['C'] <= 2*p**4, f"{s['C']} <= {2*p**4}")
    mism = run_deepening(p, B)
    check(f'F6/R4 deepening stability p={p} (10^6 samples)', mism == 0, f'{mism} mismatches')
    res[f'essential_p{p}'] = {k: v for k, v in ess.items() if k != 'REG'} | {'REG': {str(k): v for k, v in ess['REG'].items()}}
    if p == 5:
        spot = classify(5, B, tuple(np.array([x]) for x in (20, 75, 375, 2500)), (2, 3, 4, 5))
        check('P8 spot check f=x^4+20x^3+75x^2+375x+2500: cell (4,3,3,4), branches {1,2}',
              int(spot[0]) == 0b11, f'bitmask={int(spot[0]):04b}')
        u = run_essential_unhoisted(3, branch_table(3))   # placed here only to keep p=5 pass timing clean
res['unhoisted_p3'] = u

# ---- R2: the literal full-box run at p=3, N=5, and R2-vs-R3 multiplier ----
B3 = branch_table(3)
full = run_full3(B3)
log(f'  R2 full p=3 N=5: {full["TOTAL"]:,} boxes, {time.time()-T0:.0f}s')
L = LEVELS[(3, 5)]
check('P6 LITERAL p=3 N=5 SUM/EVENT/GAP', full['SUM'] == L['SUM'] and
      full['EVENT'] == L['EVENT'] and full['GAP'] == L['GAP'],
      f"{full['SUM']:,}/{full['EVENT']:,}/{full['GAP']:,}")
check('P6 LITERAL p=3 N=5 histogram {1: 4374, 2: 729}, 0 with mult>=3',
      full['HIST'] == {1: L['H1'], 2: L['H2']} and full['HIST3'] == 0, full['HIST'])
tup_of = lambda t: ((t//27) % 3, (t//9) % 3, (t//3) % 3, t % 3)
fib_cells = {(tup_of(t), r): n for (t, r), n in full['FIBERS'].items()}
exp_fibers = {(cell, r): 729 for cell, rs in SEAL[3]['TABLE'].items() for r in rs}
check('P7 per-eta fibers p=3 N=5: all 8 branches exactly 3^6 = 729 each',
      fib_cells == exp_fibers, fib_cells)
mult2cell = (0, 1, 0, 1)
check('P7 mult-2 cell (0,1,0,1): both branch fibers = 729 over the SAME 729 boxes '
      '(equal strata: event 729, sum 1458)',
      fib_cells.get((mult2cell, 1)) == 729 and fib_cells.get((mult2cell, 2)) == 729 and
      full['SUM'] - full['EVENT'] == 729, '')
ess3 = res['essential_p3']
check('F6/P9 multiplier R2 == 3^6 x R3 (SUM/EVENT/GAP/hist/perbr, enumerated)',
      all(full[k] == 729*ess3[k] for k in ('SUM', 'EVENT', 'GAP')) and
      full['HIST'] == {k: 729*v for k, v in ess3['HIST'].items()} and
      full['PERBR'] == {int(k): 729*v for k, v in ess3['PERBR'].items()},
      f"R2 SUM {full['SUM']} = 729*{ess3['SUM']}")
check('F6 unhoisted p=3 essential cross-pass == hoisted (SUM/EVENT/GAP/hist/perbr)',
      all(u[k] == ess3[k] for k in ('SUM', 'EVENT', 'GAP')) and u['HIST'] == ess3['HIST'] and
      {int(k): v for k, v in u['PERBR'].items()} == {int(k): v for k, v in ess3['PERBR'].items()}, '')
check('P6 N-ratio between levels = p^4 per prime (from the level table)',
      all(LEVELS[(p, 6)][k] == p**4 * LEVELS[(p, 5)][k] for p in (5, 3)
          for k in ('SUM', 'EVENT', 'GAP', 'H1', 'H2')), '')
from fractions import Fraction
check('P9 masses: event <= sum = C*p^-14 <= 2*p^-10 (M=2), both primes',
      all(Fraction(SEAL[p]['E'], p**14) < Fraction(SEAL[p]['C'], p**14) <= Fraction(2, p**10)
          for p in (5, 3)), '')
res['full_p3_N5'] = {k: (v if k != 'FIBERS' else {f'{tup_of(t)},r={r}': n for (t, r), n in v.items()})
                     for k, v in full.items()}
res['verdicts'] = verdicts
npass = sum(1 for v in verdicts if v['ok']); nfail = len(verdicts) - npass
log(f'\n==== CASE-D4M2 GATE: {npass} PASS / {nfail} FAIL of {len(verdicts)} '
    f'sealed verdict families ({time.time()-T0:.0f}s) ====')
log('GATE VERDICT: ' + ('PASS' if nfail == 0 else 'FAIL — falsifier(s) fired; seal untouched'))
with open('/data/users/asvin/math-and-lean/p-adic-splitting-densities/verification/results/case_d4m2_results.json', 'w') as fh:
    json.dump(res, fh, indent=1, default=str)
log('JSON written.')
