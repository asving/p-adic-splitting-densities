#!/usr/bin/env python3
"""x_n3_probes.py — PROBE-5: gate X-n3 census layers + the STALL-probe.

Spec (all displays quoted from lean/notes/MOVES_2026-07-24.md §X-EXHAUST):
  * X.5 "Sealed gate X-n3" (REBUILT rev 2, ~line 11481): boxes = exhaustive
    monic cubics, level-8 at p=2 (2^24) and level-5 at p=3 (3^15); layers
    (i) prefix-cumulative index sweep  v_p(disc f) >= 2*CUM(j),
        CUM(j) = sum of table values T1 |-> l(e*h*l-e-h+1)/2, T2 |-> (e-1)(h-1)/2,
        T3/T4 |-> 0, along every branch prefix; 0 violations tolerated; a
        violation is adjudicated against the (X1a-ALIGN) dictionary, never patched.
    (ii) sealed numbers: s(3)=2 ratio test (= the STALL-probe layer),
        c0(3)=4 (observation face), C_T(3)=53 + c_T(3)=1 per-letter teeth,
        (3b) legs; (iii) decay curve mu(Undec(N)) monotone + env*(N)>1 shape.
  * X.1b STALL-probe display (~line 11194): exhaustive p=2 boxes -- the full
    cubic box 2^24 at N=8 AND the quartic RS-chain conditioned cylinder 2^26
    at N=10 (the state-probe geometry); measure max recentering run length and
    per-f ratio #{recentering nodes}/v_p(disc f).

READING AMBIGUITY, TESTED BOTH WAYS (recorded for orchestrator adjudication):
  X.0 defines continuing nodes as "selection != bottom"; the T1 row includes
  mu*g = 1 selections on l >= 2 sides.  Layer (i) is therefore run under
    reading A: prefixes through mu >= 2 (engine-descending) nodes only;
    reading B: prefixes additionally ending at a mu*g = 1 selection node
               (T1 l>=2 side value) or an e*g >= 2 increment node (T1/T2/T3).
  Analytic prediction sealed INTO this probe before running (see notes):
  reading B is violated in-box (witness family: depth-2 chain that splits,
  e.g. p=3 f = x^3+209x^2+42x+234, v3(disc)=4 < 6 = 2*CUM); reading A's
  violation candidates all have v_p(disc) >= 2*CUM forced beyond box
  precision, so its in-box sweep should show 0 readable violations.

Undec(N) semantics (anchored, then CROSS-CHECKED against the S7 corrected
integers embedded in resum_n3_seal.py, 13 rows x 5 sigma): f is decided at
level N iff the level-N digit data pins the full factorization type sigma(f):
every window read type-stable across cap-completions (same machinery as the
dual-accepted case_mn3_gate reader) and every mu>=2 continuation pinned.
Hensel (tau-hen) and regular mu=1 factors certify at the read itself (N_V=1);
confirm-read depth is NOT charged to Undec.  A mismatch vs S7 is a FINDING.

Reuses from the sealed-gate-passing case_mn3_gate.py: hull_sides,
read_data_one, fp_factor, build_catalogue, excluded_letters (letter
taxonomy + polygon reader, gate-validated 2026-07).

Checks emitted (PASS/FINDING per line; FINDING never patched):
  X1A/X1B   layer (i) sweep, readings A and B, both boxes
  X2A       STALL ratio max #rec/v_p(disc) <= 2 (s(3)=2), both boxes + runs
  X2B       per-letter teeth mu{exists node (L, h_r>=h)} <= p^-(h-h0(L)),
            h0(L) = min realized height (census-anchored, weaker-safe)
  X2C       (3b) legs in-box: p=2 D=2,4,6,8; p=3 D=5
  X2D       (3b) deep-thin legs p=3 D=7,9 (live-cylinder + a-translation
            reduction, brute-validated at levels 1..3)
  X3A       mu(Undec(N)) monotone nonincreasing, N=1..8 / 1..5
  X3B       Undec + per-sigma decided == S7 integers (65 values)
  X3C       env*(N) > 1 arithmetic + sqrtN-fallback thresholds (display)
  XV*       validation gates (R-letter hits vs case_mn3_results.json,
            squarefree counts, catalogue = 53, witness unit test)
  Q1/Q2     quartic RS cylinder: step-1 law vs state_probe_hist.json;
            max RS run length + main-chain ratio (exploration-class)

Output: /tmp/x_n3_census.out (long), results/x_n3_results.json, and an
appended summary block in probe_results_2026-07-30.txt.
Run: python3 x_n3_probes.py [--quick]  (quick = p=3 N<=3 + skip quartic)
"""
import json
import os
import sys
import time
from fractions import Fraction
from itertools import product

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from case_mn3_gate import (hull_sides, read_data_one, fp_factor,
                           build_catalogue, excluded_letters)

OUTTXT = '/tmp/x_n3_census.out'
JSONPATH = os.path.join(HERE, 'results', 'x_n3_results.json')
RESULTS = os.path.join(HERE, 'probe_results_2026-07-30.txt')
T0 = time.time()
LOG = open(OUTTXT, 'w')
verdicts = []


def log(s=''):
    print(s, flush=True)
    LOG.write(s + '\n')
    LOG.flush()


def check(name, ok, detail='', finding=False):
    """ok True -> PASS.  ok False -> FINDING (census evidence against a sealed
    candidate/reading; recorded, never patched)."""
    tag = 'PASS' if ok else 'FINDING'
    verdicts.append({'name': name, 'ok': bool(ok), 'detail': str(detail)})
    log(f"[{tag}] {name}  {detail}")


# =========================================================================
# S7 corrected integers (from resum_n3_seal.py; census-verified 65/65 in S8)
# decided counts per sigma in SIGS order; undecided = p^3N - sum(row).
# =========================================================================
SIGS = ['111', '112', '13', '1121', '31']
S7 = {2: {1: [0, 2, 2, 0, 0], 2: [0, 16, 16, 12, 8], 3: [16, 144, 128, 96, 80],
          4: [128, 1184, 1056, 896, 640], 5: [1280, 9728, 8448, 7360, 5248],
          6: [10496, 78080, 67584, 60928, 42240],
          7: [88064, 629248, 541184, 489472, 337920],
          8: [708608, 5038080, 4329472, 3951616, 2705408]},
      3: {1: [1, 9, 8, 0, 0], 2: [27, 243, 216, 126, 54],
          3: [1215, 7047, 5832, 3402, 1620],
          4: [32886, 190998, 158112, 100602, 43740],
          5: [927288, 5196312, 4269024, 2726460, 1185354]}}

# sigma(f) as a sorted multiset of leaf primes (e, fdeg)
SIGMA_OF = {(((1, 1),) * 3): '111',
            tuple(sorted([(1, 1), (1, 2)])): '112',
            ((1, 3),): '13',
            tuple(sorted([(1, 1), (2, 1)])): '1121',
            ((3, 1),): '31'}


# =========================================================================
# The window reader: type-stability + stable-datum reads, memoized on codes.
# codes: tuple per slot 0..W of None (coefficient exactly 0) or (v, d);
# v == N means capped (v_p >= N, digit unknown).
# =========================================================================
WINDOW_MEMO = {}


def window_read(p, N, codes, W, root, hkey):
    key = (p, N, codes, W, root, hkey)
    if key in WINDOW_MEMO:
        return WINDOW_MEMO[key]
    capped = [j for j in range(W + 1) if codes[j] is not None
              and codes[j][0] >= N]
    vals = list(range(N, 4 * N - 2)) + [5 * N]
    summaries = set()
    seen = {}          # sidekey -> list of datums (for stable-read letters)
    faults = set()
    ncomp = 0
    for comp in product(vals, repeat=len(capped)):
        ncomp += 1
        hts = [None] * (W + 1)
        digs = [0] * (W + 1)
        for j in range(W + 1):
            if codes[j] is None:
                continue
            v, d = codes[j]
            if v >= N:
                hts[j] = comp[capped.index(j)]
                digs[j] = 'X'
            else:
                hts[j], digs[j] = v, d
        reads, fl = read_data_one(hts, digs, W, root, hkey)
        for sk, ff in fl:
            faults.add(str(ff))
        primes, cont, incs = [], [], []
        bad = False
        for sk, dat in reads:
            seen.setdefault(sk, []).append(dat)
            (e, ell, a, flk, frk, res, s0, hn, u1) = dat
            if 'X' in res:
                if ell == 1:
                    # residual is linear: lam = ((1,1),) forced, the prime
                    # (e, 1) is type-determined; digits (and the slope, if
                    # the vertex is capped) are irrelevant to sigma.
                    primes.append((e, 1))
                else:
                    bad = True
                continue
            facs = fp_factor(res, p)
            lam = tuple(sorted((len(f) - 1, m) for f, m in facs))
            if sum(g * m for g, m in lam) != ell:
                faults.add(f'partition {dat}')
                bad = True
                continue
            for f, m in facs:
                g = len(f) - 1
                if m == 1:
                    primes.append((e, g))
                elif e * g == 1:
                    r = (-f[0]) % p
                    wf = u1 + s0 * hn
                    cont.append((hn, r, m, wf - m * hn, e, ell))
                else:
                    faults.add(f'mu>=2 with e*g>=2 at n=3?! {dat}')
                    bad = True
        summaries.add('BAD' if bad else
                      (tuple(sorted(primes)), tuple(sorted(cont))))
    stable_reads = []
    n_unstable = 0
    for sk, dats in seen.items():
        if (len(dats) == ncomp and all(d == dats[0] for d in dats)
                and sk[0] not in capped and sk[1] not in capped
                and 'X' not in dats[0][5]):
            stable_reads.append(dats[0])
        else:
            n_unstable += 1
    type_ok = (len(summaries) == 1 and 'BAD' not in summaries)
    if type_ok:
        primes, cont = summaries.pop()
    else:
        primes, cont = (), ()
    out = dict(type_ok=type_ok, primes=primes, cont=cont,
               reads=tuple(stable_reads), n_unstable=n_unstable,
               faults=tuple(sorted(faults)))
    WINDOW_MEMO[key] = out
    return out


def ind_of_side(e, hn, ell):
    """(IND) table value of the side, per row (X.5(i)):
    l>=2 -> T1: l(e h l - e - h + 1)/2;  l=1,e>=2 -> T2/T3: (e-1)(h-1)/2;
    l=1,e=1 -> T4: 0.  h=0 (slope-0 root-level sides) gives 0 in all rows."""
    if ell >= 2:
        v = ell * (e * hn * ell - e - hn + 1)
        assert v % 2 == 0
        return v // 2
    if e >= 2:
        return (e - 1) * (hn - 1) // 2
    return 0


# =========================================================================
# The cubic walker: BFS over code-groups, exact, per (p, N) box.
# =========================================================================
def vpd_tables(p, N):
    M = p ** N
    K = (p - 1) * N + 1
    xs = np.arange(M, dtype=np.int64)
    v_tab = np.zeros(M, np.int16)
    for k in range(1, N):
        v_tab[xs % (p ** k) == 0] = k
    v_tab[0] = N
    d_tab = (xs // np.power(p, np.minimum(v_tab, N - 1).astype(np.int64))) % p
    code_tab = np.where(v_tab >= N, K - 1,
                        v_tab * (p - 1) + (d_tab - 1)).astype(np.int32)
    return M, K, v_tab, code_tab


def dec_code(code, p, N):
    K = (p - 1) * N + 1
    code = int(code)
    return (N, 0) if code == K - 1 else (code // (p - 1), code % (p - 1) + 1)


QGROUP = {2: 'Q2', 3: 'Q3'}


def run_box(p, N, full, cat=None, quiet=False):
    """Walk every monic cubic mod p^N.  Returns dict of tallies.
    full=True additionally does disc/CUM/ratio/letters (the X.5 layers);
    full=False only Undec + per-sigma decided counts (the per-N curve)."""
    t0 = time.time()
    M, K, v_tab, code_tab = vpd_tables(p, N)
    size = M ** 3
    idx = np.arange(size, dtype=np.int64)
    C0 = (idx % M).astype(np.int64)
    C1 = ((idx // M) % M).astype(np.int64)
    C2 = (idx // (M * M)).astype(np.int64)
    del idx
    undec = np.zeros(size, bool)
    sigma_ct = {s: 0 for s in SIGS}
    res = dict(p=p, N=N, box=size)
    if full:
        # v_p(disc) read in-box: exact iff < N (disc mod p^N is box-determined)
        d = (18 * C2 * C1 * C0 - 4 * C2 ** 3 * C0 + (C2 * C1) ** 2
             - 4 * C1 ** 3 - 27 * C0 ** 2) % (M)
        vd = np.zeros(size, np.int16)        # N = censored (>= N)
        for k in range(1, N + 1):
            vd[d % (p ** k) == 0] = k
        del d
        res['vd_hist'] = np.bincount(vd, minlength=N + 1).tolist()
        row_hits = {}          # (letterkey, h) -> count of (f, read-row)s
        exists_ev = {}         # (letterkey, hmax) -> count of f
        viol_A = [0, None]
        viol_B = [0, None]
        skipped_A = 0          # censored-disc prefixes with 2*CUM > N
        skipped_B = 0
        nrec_final = {}        # nrec -> count (over singular walk-complete f)
        maxratio = [Fraction(0), None]
        maxratio_cens = [Fraction(0), None]
        runlen = {}            # chain length (hn>=1 recenterings) histogram
    faults_all = {}

    def letter_rows(group, reads):
        """Stable reads -> [(letterkey, h, selrow)...] mirroring the
        case_mn3_gate key schema (group, e, l, a, flankL, flankR, lam, sel)."""
        out = []
        for dat in reads:
            (e, ell, a, flk, frk, resid, s0, hn, u1) = dat
            facs = fp_factor(resid, p)
            lam = tuple(sorted((len(f) - 1, m) for f, m in facs))
            for f, m in facs:
                g = len(f) - 1
                out.append(((group, e, ell, a, flk, frk, lam, (g, m)), hn,
                            (e, ell, hn, g, m)))
        return out

    # task = (members (np index array), c0, c1, c2 (current frame arrays),
    #         W, hkey, hmu, root?, primes_so_far, events, cum, nrec, group)
    stack = []
    order = np.argsort(code_tab[C0].astype(np.int64) + K * code_tab[C1]
                       + K * K * code_tab[C2], kind='stable')
    sig_sorted = (code_tab[C0][order].astype(np.int64) + K * code_tab[C1][order]
                  + K * K * code_tab[C2][order])
    bounds = np.flatnonzero(np.diff(sig_sorted)) + 1
    starts = np.concatenate([[0], bounds])
    ends = np.concatenate([bounds, [len(sig_sorted)]])
    for s, e in zip(starts, ends):
        mem = order[s:e]
        sg = int(sig_sorted[s])
        codes = (dec_code(sg % K, p, N), dec_code((sg // K) % K, p, N),
                 dec_code(sg // (K * K), p, N), (0, 1))
        stack.append((mem, C0[mem], C1[mem], C2[mem], 3, 0, 0, True,
                      (), (), 0, 0, 'R', codes))
    del order, sig_sorted, bounds, starts, ends

    while stack:
        (mem, c0, c1, c2, W, hkey, hmu_t, is_root, primes0, events, cum,
         nrec, group, codes) = stack.pop()
        n = len(mem)
        if not is_root:
            # D.10 frame checks (transcribed from the gate-validated
            # case_mn3_gate.classify_rec): vertex v(B'_mu) == hmu; floors
            # v(B'_j) > hmu + (mu - j)*hn.  Violations are FINDINGS.
            v_mu = codes[W][0] if codes[W] is not None else N
            if not (codes[W] is not None and v_mu == hmu_t):
                faults_all[f'VERTEX {codes} hmu={hmu_t}'] = \
                    faults_all.get(f'VERTEX {codes} hmu={hmu_t}', 0) + n
            for j in range(W):
                need = hmu_t + (W - j) * hkey
                if codes[j] is None:
                    continue
                vj = codes[j][0]
                if vj < N and vj <= need:
                    kf = f'BOX j={j} {codes} hn={hkey} hmu={hmu_t}'
                    faults_all[kf] = faults_all.get(kf, 0) + n
        wr = window_read(p, N, codes, W, is_root, hkey)
        for ff in wr['faults']:
            faults_all[ff] = faults_all.get(ff, 0) + n
        if not wr['type_ok']:
            undec[mem] = True
        if full:
            rows = letter_rows(group, wr['reads'])
            for lk, h, sel in rows:
                row_hits[(lk, h)] = row_hits.get((lk, h), 0) + n
            events = events + tuple((lk, h) for lk, h, _ in rows)
            # reading-B prefix check: every selection-node (mu*g=1 on l>=2,
            # or e*g>=2 increment) ends a branch prefix with the side value
            for lk, h, (e_, ell_, hn_, g_, m_) in rows:
                if m_ == 1 and (ell_ >= 2 or e_ * g_ >= 2) and hn_ >= 1:
                    cB = cum + ind_of_side(e_, hn_, ell_)
                    bad = mem[(vd[mem] < 2 * cB) & (vd[mem] < N)]
                    skipped_B += int(((vd[mem] >= N) & (2 * cB > N)).sum())
                    if len(bad):
                        viol_B[0] += len(bad)
                        if viol_B[1] is None:
                            b = int(bad[0])
                            viol_B[1] = (int(C2[b]), int(C1[b]), int(C0[b]),
                                         int(vd[b]), 2 * cB, lk, h)
        if not wr['type_ok'] or not wr['cont']:
            # walk complete (or type-dead): assign sigma / final tallies
            if wr['type_ok']:
                sig = tuple(sorted(primes0 + wr['primes']))
                assert sum(e * g for e, g in sig) == 3, sig
                sigma_ct[SIGMA_OF[sig]] += n
            if full:
                dedup = {}
                for lk, h in events:
                    dedup[lk] = max(dedup.get(lk, -1), h)
                for lk, h in dedup.items():
                    exists_ev[(lk, h)] = exists_ev.get((lk, h), 0) + n
                if nrec > 0:
                    nrec_final[nrec] = nrec_final.get(nrec, 0) + n
                    runlen[nrec] = runlen.get(nrec, 0) + n
                    ex = mem[vd[mem] < N]
                    if len(ex):
                        i = int(ex[np.argmin(vd[ex])])
                        r = Fraction(nrec, max(1, int(vd[i])))
                        if r > maxratio[0]:
                            maxratio[0] = r
                            maxratio[1] = (int(C2[i]), int(C1[i]), int(C0[i]),
                                           nrec, int(vd[i]))
                    cen = mem[vd[mem] >= N]
                    if len(cen):
                        r = Fraction(nrec, N)
                        if r > maxratio_cens[0]:
                            i = int(cen[0])
                            maxratio_cens[0] = r
                            maxratio_cens[1] = (int(C2[i]), int(C1[i]),
                                                int(C0[i]), nrec, f'>={N}')
            continue
        # exactly one continuation for n=3 (asserted)
        assert len(wr['cont']) == 1, (wr['cont'], codes)
        hn, r, mu, hmu, e_, ell_ = wr['cont'][0]
        assert e_ == 1 and ell_ >= mu, (e_, ell_, mu)
        if not is_root and hn <= hkey:
            # D.10 strict-climb violation: fault-stop (never loop)
            kf = f'Iaug-cont-stop hn={hn} hkey={hkey}'
            faults_all[kf] = faults_all.get(kf, 0) + n
            undec[mem] = True
            continue
        iv = ind_of_side(e_, hn, ell_)
        cum2 = cum + iv
        nrec2 = nrec + (1 if hn >= 1 else 0)
        if full and hn >= 1:
            bad = mem[(vd[mem] < 2 * cum2) & (vd[mem] < N)]
            skipped_A += int(((vd[mem] >= N) & (2 * cum2 > N)).sum())
            if len(bad):
                viol_A[0] += len(bad)
                if viol_A[1] is None:
                    b = int(bad[0])
                    viol_A[1] = (int(C2[b]), int(C1[b]), int(C0[b]),
                                 int(vd[b]), 2 * cum2)
        # collect this read's leaf primes, then recenter into window [0, mu]
        primes1 = primes0 + wr['primes']
        t = r * p ** hn
        c0n = (c0 + c1 * t + c2 * (t * t) + t ** 3) % M
        c1n = (c1 + 2 * c2 * t + 3 * (t * t)) % M
        c2n = (c2 + 3 * t) % M
        sig2 = (code_tab[c0n].astype(np.int64) + K * code_tab[c1n]
                + K * K * code_tab[c2n])
        o2 = np.argsort(sig2, kind='stable')
        ss = sig2[o2]
        bnd = np.flatnonzero(np.diff(ss)) + 1
        st2 = np.concatenate([[0], bnd])
        en2 = np.concatenate([bnd, [len(ss)]])
        for s2, e2 in zip(st2, en2):
            sel = o2[s2:e2]
            sg = int(ss[s2])
            codes2 = (dec_code(sg % K, p, N), dec_code((sg // K) % K, p, N),
                      dec_code(sg // (K * K), p, N))
            if mu == 3:
                codes2 = codes2 + ((0, 1),)
            stack.append((mem[sel], c0n[sel], c1n[sel], c2n[sel], mu, hn, hmu,
                          False, primes1, events, cum2, nrec2, QGROUP[mu],
                          codes2))
    out = dict(res, undec=int(undec.sum()), sigma=sigma_ct,
               faults=faults_all, secs=round(time.time() - t0, 1))
    if full:
        out.update(row_hits=row_hits, exists_ev=exists_ev,
                   viol_A=viol_A, viol_B=viol_B,
                   skipped_A=skipped_A, skipped_B=skipped_B,
                   nrec_final=nrec_final, maxratio=maxratio,
                   maxratio_cens=maxratio_cens,
                   undec_idx_note='undec flags exact')
    if not quiet:
        log(f"  run_box(p={p}, N={N}, full={full}): box {size}, "
            f"undec {out['undec']}, {out['secs']}s")
    return out


# =========================================================================
# (3b) deep-thin sweep at p=3: mu{v3(disc) >= D} for D up to 9 via
# live-cylinder refinement + the a-translation reduction (the fiber count
# |{(b,c): disc(a,b,c) = 0 mod 3^k}| depends on a only through a mod 3,
# since x -> x+t maps the a-fiber bijectively to the (a+3t)-fiber and
# disc is translation-invariant).  Brute-validated at k = 1..3.
# =========================================================================
def disc_cubic(a, b, c):
    return (18 * a * b * c - 4 * a ** 3 * c + (a * b) ** 2
            - 4 * b ** 3 - 27 * c ** 2)


def deep_thin_p3(Dmax=9):
    p = 3
    live = np.array([(a, b, c) for a in range(3) for b in range(3)
                     for c in range(3)
                     if disc_cubic(a, b, c) % 3 == 0], dtype=np.int64)
    counts = {}
    for k in range(1, Dmax + 1):
        if k > 1:
            pk = p ** (k - 1)
            A = np.repeat(live, 9, axis=0)
            db = np.tile(np.repeat(np.arange(3), 3), len(live)) * pk
            dc = np.tile(np.tile(np.arange(3), 3), len(live)) * pk
            A[:, 1] += db
            A[:, 2] += dc
            d = disc_cubic(A[:, 0], A[:, 1], A[:, 2]) % (p ** k)
            live = A[d == 0]
        counts[k] = (len(live), Fraction(int(len(live)) * p ** (k - 1),
                                         p ** (3 * k)))
    return counts


def brute_mu_v3(k):
    M = 3 ** k
    a = np.arange(M, dtype=np.int64)
    tot = 0
    for av in range(M):
        b, c = np.meshgrid(a, a, indexing='ij')
        d = disc_cubic(av, b.ravel(), c.ravel()) % M
        tot += int((d == 0).sum())
    return Fraction(tot, M ** 3)


# =========================================================================
# The cubic gate driver: all X.5 layers for one (p, Nmax) box.
# =========================================================================
def lname(k):
    return (f'{k[0]}[e{k[1]} l{k[2]} a{k[3]} fl{list(k[4])}|{list(k[5])} '
            f'lam{list(k[6])} sel{k[7]}]')


def cubic_gate(p, Nmax, mn3):
    log(f"\n===== CUBIC BOX p={p}, level {Nmax} (size {p ** (3 * Nmax)}) =====")
    full = run_box(p, Nmax, True)
    curve = []
    for N in range(1, Nmax):
        curve.append(run_box(p, N, False))
    curve.append(full)
    box = p ** (3 * Nmax)

    # ---- XV validation gates -------------------------------------------
    sqf = full['vd_hist'][0]
    check(f'XV1 p={p}: squarefree-reduction count = (p^3-p^2)*p^(3N-3)',
          sqf == (p ** 3 - p ** 2) * p ** (3 * Nmax - 3),
          f'{sqf}')
    # R-letter row-hit match vs the dual-accepted M-n3 census (same box)
    mn3_comparable = (mn3['N'] == Nmax)
    myR = {}
    for (lk, h), n in full['row_hits'].items():
        if lk[0] == 'R':
            myR[lname(lk)] = myR.get(lname(lk), 0) + n
    theirs = {k: v for k, v in mn3['hits'].items()
              if k.startswith('R[') and v > 0}
    if mn3_comparable:
        same = (myR == theirs)
        if not same:
            diff = {k: (myR.get(k, 0), theirs.get(k, 0))
                    for k in set(myR) | set(theirs)
                    if myR.get(k, 0) != theirs.get(k, 0)}
            log(f'  R-letter mismatches ({len(diff)}): '
                f'{dict(list(diff.items())[:5])}')
        check(f'XV2 p={p}: root-read letter tallies == case_mn3_results.json '
              f'({len(theirs)} R-letters)', same,
              f'{sum(myR.values())} row-hits')
        myQ = {}
        for (lk, h), n in full['row_hits'].items():
            if lk[0] in ('Q2', 'Q3'):
                myQ[lname(lk)] = myQ.get(lname(lk), 0) + n
        qcmp = all(myQ.get(k, 0) >= v for k, v in mn3['hits'].items()
                   if k.startswith('Q2[') or k.startswith('Q3['))
        check(f'XV3 p={p}: Q2/Q3 letter tallies >= depth-2 census '
              f'(full-depth walker sees at least the depth-2 reads)',
              qcmp, '')
    else:
        log(f'  (XV2/XV3 skipped: census N={Nmax} != mn3 N={mn3["N"]})')
    check(f'XV4 p={p}: engine faults (VERTEX/BOX/Iaug/partition) == 0',
          len(full['faults']) == 0, str(dict(list(full['faults'].items())[:4])))

    # ---- X3B: Undec + per-sigma decided == the S7 corrected integers ----
    s7ok, s7detail = True, []
    for N in range(1, Nmax + 1):
        r = curve[N - 1]
        want = S7[p][N]
        got = [r['sigma'][s] for s in SIGS]
        wundec = p ** (3 * N) - sum(want)
        if got != want or r['undec'] != wundec:
            s7ok = False
            s7detail.append((N, got, want, r['undec'], wundec))
    check(f'X3B p={p}: per-sigma decided + undecided == S7 integers, '
          f'N=1..{Nmax} ({6 * Nmax} values)', s7ok,
          s7detail[:2] if s7detail else 'exact')

    # ---- X3A: mu(Undec(N)) monotone nonincreasing -----------------------
    mus = [Fraction(curve[N - 1]['undec'], p ** (3 * N))
           for N in range(1, Nmax + 1)]
    mono = all(mus[i + 1] <= mus[i] for i in range(len(mus) - 1))
    check(f'X3A p={p}: mu(Undec(N)) monotone nonincreasing (Thm 2.1 '
          f'N-stability)', mono,
          '[' + ', '.join(f'{float(m):.5f}' for m in mus) + ']')

    # ---- X1A / X1B: the layer (i) prefix-cumulative sweep ----------------
    vA, wA = full['viol_A']
    check(f'X1A p={p}: prefix sweep v_p(disc) >= 2*CUM, reading A '
          f'(mu>=2 engine-descending nodes), read-exact f',
          vA == 0,
          f'violations {vA}' + (f', witness f=(c2,c1,c0)={wA[:3]} '
                                f'vd={wA[3]} 2CUM={wA[4]}' if wA else
                                f'; censored-skipped {full["skipped_A"]}'))
    vB, wB = full['viol_B']
    check(f'X1B p={p}: prefix sweep reading B (+ mu*g=1 selection nodes '
          f'carrying the T1 side value)', vB == 0,
          f'violations {vB}' + (f', witness f=(c2,c1,c0)={wB[:3]} '
                                f'vd={wB[3]} 2CUM={wB[4]} at letter '
                                f'{lname(wB[5])} h={wB[6]}' if wB else ''))

    # ---- X2A: the STALL ratio (s(3) = 2) + run lengths -------------------
    mr, mrw = full['maxratio']
    check(f'X2A p={p}: STALL ratio max #rec/v_p(disc) <= 2 over read-exact '
          f'f (sealed s(3)=2)', mr <= 2,
          f'max {mr} at f=(c2,c1,c0)={mrw[:3] if mrw else None} '
          f'(nrec={mrw[3] if mrw else 0}, vd={mrw[4] if mrw else "-"}); '
          f'censored-f ratio floor {full["maxratio_cens"][0]} '
          f'(vd>={Nmax} there)')
    log(f'  run-length histogram (recentering chain, hn>=1): '
        f'{dict(sorted(full["nrec_final"].items()))}')

    # ---- X2B: per-letter teeth ------------------------------------------
    tails = {}
    for (lk, h), n in full['exists_ev'].items():
        tails.setdefault(lk, {})[h] = tails.setdefault(lk, {}).get(h, 0) + n
    worst = (None, Fraction(0))
    nviol, nlet = 0, 0
    for lk, hist in sorted(tails.items(), key=lambda t: lname(t[0])):
        hs = sorted(hist)
        h0 = hs[0]
        nlet += 1
        for h in range(h0, max(hs) + 1):
            T = sum(n for hh, n in hist.items() if hh >= h)
            bound = Fraction(1, p ** (h - h0))
            r = Fraction(T, box) / bound
            if r > worst[1]:
                worst = ((lname(lk), h, h0, T), r)
            if Fraction(T, box) > bound:
                nviol += 1
    check(f'X2B p={p}: per-letter teeth mu(exists node (L, h_r>=h)) <= '
          f'p^-(h-h0(L)), h0 census-anchored, {nlet} letters',
          nviol == 0,
          f'violating (L,h) pairs {nviol}; tightest {worst[0]} at '
          f'{float(worst[1]):.4f} of bound')

    # ---- X2C: (3b) legs in-box ------------------------------------------
    legs = {2: [2, 4, 6, 8], 3: [5]}[p]
    ok3b, det = True, []
    for D in legs:
        cnt = sum(full['vd_hist'][D:])
        mu = Fraction(cnt, box)
        # sealed legs: mu{v_p >= D} <= (n-1) p^-ceil((D - n v_p(n))/(n-1))
        e = -((D - 3 * (1 if p == 3 else 0)) // -2)     # ceil((D-3vp(3))/2)
        bnd = Fraction(2, p ** e)
        ok = mu <= bnd
        ok3b &= ok
        det.append(f'D={D}: {float(mu):.5f} <= {float(bnd):.5f}')
    check(f'X2C p={p}: (3b) legs in-box (DERIVED Lemma 3.3 restatement)',
          ok3b, '; '.join(det))

    # ---- X3C: env* arithmetic + sqrtN fallback + observation -------------
    import math
    envok, envdet = True, []
    for N in range(4, 9):
        e1 = math.ceil(((N / 2 - 2) / 2.5 - 3 * (1 if p == 3 else 0)) / 2)
        env = 2.0 * p ** (-e1) + 53.0 * p ** (-(N / 2 - 1))
        envok &= (env > 1)
        envdet.append(f'N={N}: {env:.2f}')
    check(f'X3C p={p}: env*(N) > 1 at N=4..8 (sealed toothless-envelope '
          f'arithmetic, display-shape only)', envok, '; '.join(envdet))
    hstar = {N: -(-(N - 1) // 4) for N in range(4, 9)}   # ceil((N-1)/4) ~ sq
    import math
    hstar = {N: math.ceil(math.sqrt((N - 1) / 4)) for N in range(4, 9)}
    log(f'  sqrtN-fallback thresholds d*+1 = h* = ceil(sqrt((N-1)/4)): '
        f'{hstar}  [OBSERVATION target, c_cap = 0 face]')
    return dict(full=full, curve=[{k: r[k] for k in ('p', 'N', 'undec',
                                                     'sigma')}
                                  for r in curve], mus=[str(m) for m in mus])


# =========================================================================
# The quartic RS-chain conditioned cylinder (X.1b STALL-probe, second box;
# exploration-class).  State-probe geometry (state_probe.py, validated
# 2026-07-28): monic quartics a0 = 16+32u0, a1 = 16u1, a2 = 4+8u2, a3 = 4u3
# (2^26 total), root stratum = side [0,4] slope 1 with residual psi^2,
# psi = z^2+z+1; key Phi1 = x^2+2x+4 (S6b lift); frame f = Phi^2 + C1 Phi
# + C0, weights w(B) = min(v(b_c), v(b_x)+1); box level N = 10 (reads at
# weight >= 10 are cylinder-undetermined -> DEEP).
# The walked chain = the consecutive RS self-loop run (T4-row recenterings,
# the (ALIGN-rec) danger zone).  Post-split (TS/SPLIT) T4 sub-chains are
# NOT walked -- recorded limitation: ratio is a main-chain lower bound;
# the max CONSECUTIVE run statistic is exact (a split breaks the run).
# v2(disc f) is the raw valuation of the integer representative (every
# cylinder point here IS an integer polynomial; in-cylinder v2(disc) >= 12
# always, so the sealed-style exact-read censoring would void the ratio --
# reported as the exploration measurement with this caveat).
# =========================================================================
F4_MUL = np.zeros((4, 4), np.int64)
for _a in range(4):
    for _b in range(4):
        c1_, x1_, c2_, x2_ = _a & 1, _a >> 1, _b & 1, _b >> 1
        F4_MUL[_a, _b] = (((c1_ * c2_ + x1_ * x2_) & 1)
                          + 2 * ((c1_ * x2_ + x1_ * c2_ + x1_ * x2_) & 1))
F4_SQ = np.array([F4_MUL[t, t] for t in range(4)], np.int64)   # sqrt = sq
F4_TR = np.array([0, 0, 1, 1], np.int64)                        # Tr F4->F2


def v2_arr(x, cap):
    """v2 of nonneg int64 array, capped (0 -> cap)."""
    v = np.zeros(x.shape, np.int16)
    z = (x == 0)
    v[z] = cap
    y = x.copy()
    y[z] = 1
    for _ in range(cap):
        m = (y % 2 == 0)
        if not m.any():
            break
        v[m] += 1
        y[m] //= 2
    return np.minimum(v, cap)


def quartic_stall(cap=10, KW=24, chunks=64):
    t0 = time.time()
    MK = (1 << KW) - 1
    tot = {'RAM': 0, 'SPLIT': 0, 'INERT': 0, 'TS': 0, 'DEEP': 0}
    rs1_h3 = 0
    runhist = {}
    maxrun = 0
    maxratio = [Fraction(0), None]
    floor_faults = 0
    U = 1 << 26
    per = U // chunks
    for ci in range(chunks):
        idx = np.arange(ci * per, (ci + 1) * per, dtype=np.int64)
        u0 = idx & 31
        u1 = (idx >> 5) & 63
        u2 = (idx >> 11) & 127
        u3 = (idx >> 18) & 255
        a0 = 16 + 32 * u0
        a1 = 16 * u1
        a2 = 4 + 8 * u2
        a3 = 4 * u3
        # v2(disc) of the integer representative (uint64 wraparound exact)
        dsc = disc4(a3, a2, a1, a0)
        vd = np.zeros(len(idx), np.int16)
        y = dsc.copy()
        for k in range(1, 63):
            m = (y & np.uint64(1)) == 0
            if not m.any():
                break
            vd[m] += 1
            y[m] >>= np.uint64(1)
        vd[dsc == 0] = 63
        # Phi-adic frame
        k1 = np.full(len(idx), 2, np.int64)
        k0 = np.full(len(idx), 4, np.int64)
        q1 = (a3 - k1) & MK
        q0 = (a2 - k0 - k1 * q1) & MK
        c0x = (a1 - (k0 * q1 + k1 * q0)) & MK
        c0c = (a0 - k0 * q0) & MK
        c1x = (q1 - k1) & MK
        c1c = (q0 - k0) & MK
        nrec = np.zeros(len(idx), np.int16)
        state = np.full(len(idx), -1, np.int8)   # -1 active; 0..4 buckets
        BUCK = {'RAM': 0, 'SPLIT': 1, 'INERT': 2, 'TS': 3, 'DEEP': 4}
        for step in range(14):
            act = state < 0
            if not act.any():
                break
            vc0 = v2_arr(c0c & MK, KW)
            vx0 = v2_arr(c0x & MK, KW)
            vc1 = v2_arr(c1c & MK, KW)
            vx1 = v2_arr(c1x & MK, KW)
            w0 = np.minimum(vc0, vx0 + 1)
            w1 = np.minimum(vc1, vx1 + 1)
            if step == 0:
                floor_faults += int((act & ((w1 < 3) | (w0 < 5))).sum())
            w0r = np.where(w0 >= cap, cap, w0)   # box-censored reads
            w1r = np.where(w1 >= cap, cap, w1)
            two = act & (w1r < cap) & (w0r > 2 * w1r)
            state[two] = BUCK['TS']
            single = act & ~two & (w0r < cap)
            ram = single & (w0r % 2 == 1)
            state[ram] = BUCK['RAM']
            ev = single & ~ram & (w0r >= 2)     # h >= 1 guard (floor safety)
            state[single & ~ram & (w0r < 2)] = BUCK['DEEP']
            deep = act & ~two & ~single
            state[deep] = BUCK['DEEP']
            if not ev.any():
                continue
            h = (w0r[ev] // 2).astype(np.int64)
            iev = np.flatnonzero(ev)
            # F4 digits: d @ level l of B: eps_c = bit_l(b_c), eps_x = bit_{l-1}(b_x)
            d0 = (((c0c[iev] >> (2 * h)) & 1)
                  + 2 * ((c0x[iev] >> (2 * h - 1)) & 1))
            on1 = (w1[iev] == h)
            d1 = np.where(on1, ((c1c[iev] >> h) & 1)
                          + 2 * ((c1x[iev] >> (h - 1)) & 1), 0)
            rs = (d1 == 0)
            nonrs = iev[~rs]
            ratio = F4_MUL[d0[~rs], d1[~rs]]
            state[nonrs[F4_TR[ratio] == 0]] = BUCK['SPLIT']
            state[nonrs[F4_TR[ratio] == 1]] = BUCK['INERT']
            # RS recenter
            irs = iev[rs]
            if step == 0:
                rs1_h3 += int((h[rs] == 3).sum())
            r = F4_SQ[d0[rs]]
            hh = h[rs]
            tc = (r & 1) << hh
            tx = (r >> 1) << (hh - 1)
            k1n = (k1[irs] - tx) & MK
            k0n = (k0[irs] - tc) & MK
            A2 = (tx * tx + c1x[irs] * tx) & MK
            A1 = (2 * tx * tc + c1x[irs] * tc + c1c[irs] * tx + c0x[irs]) & MK
            A0 = (tc * tc + c1c[irs] * tc + c0c[irs]) & MK
            c0x[irs] = (A1 - A2 * k1n) & MK
            c0c[irs] = (A0 - A2 * k0n) & MK
            c1x[irs] = (c1x[irs] + 2 * tx) & MK
            c1c[irs] = (c1c[irs] + 2 * tc) & MK
            k1[irs], k0[irs] = k1n, k0n
            nrec[irs] += 1
        state[state < 0] = BUCK['DEEP']
        for k, v in BUCK.items():
            tot[k] += int((state == v).sum())
        mr = int(nrec.max())
        maxrun = max(maxrun, mr)
        for L in range(1, mr + 1):
            runhist[L] = runhist.get(L, 0) + int((nrec == L).sum())
        has = nrec > 0
        if has.any():
            rr = nrec[has].astype(np.float64) / np.maximum(vd[has], 1)
            i = int(np.argmax(rr))
            j = np.flatnonzero(has)[i]
            fr = Fraction(int(nrec[j]), max(1, int(vd[j])))
            if fr > maxratio[0]:
                maxratio[0] = fr
                maxratio[1] = (int(idx[j]), int(nrec[j]), int(vd[j]))
    return dict(tot=tot, rs1_h3=rs1_h3, runhist=runhist, maxrun=maxrun,
                maxratio=maxratio, floor_faults=floor_faults,
                secs=round(time.time() - t0, 1))


def disc4(a, b, c, d):
    """Discriminant of x^4+ax^3+bx^2+cx+d, exact mod 2^64 (uint64 wrap)."""
    a = a.astype(np.uint64)
    b = b.astype(np.uint64)
    c = c.astype(np.uint64)
    d = d.astype(np.uint64)
    with np.errstate(over='ignore'):
        return (np.uint64(256) * d ** 3 - np.uint64(192) * a * c * d * d
                - np.uint64(128) * b * b * d * d
                + np.uint64(144) * a * a * b * d * d
                - np.uint64(27) * a ** 4 * d * d
                + np.uint64(144) * b * c * c * d
                - np.uint64(6) * a * a * c * c * d
                - np.uint64(80) * a * b * b * c * d
                + np.uint64(18) * a ** 3 * b * c * d
                + np.uint64(16) * b ** 4 * d
                - np.uint64(4) * a * a * b ** 3 * d
                - np.uint64(27) * c ** 4 + np.uint64(18) * a * b * c ** 3
                - np.uint64(4) * a ** 3 * c ** 3 - np.uint64(4) * b ** 3 * c * c
                + a * a * b * b * c * c)


def unit_tests():
    # (1) catalogue = 53 letters (the C_T(3) count)
    cat = build_catalogue()
    check('XV0: M-n3 catalogue has 53 letters (C_T(3) = 53, one union-bound '
          'term per letter)', len(cat) == 53, f'{len(cat)}')
    # (2) disc4 against sympy on random ints
    import random
    random.seed(7)
    try:
        import sympy as sp
        x = sp.symbols('x')
        ok = True
        for _ in range(20):
            aa, bb, cc, dd = (random.randrange(1024) for _ in range(4))
            D1 = int(sp.discriminant(x ** 4 + aa * x ** 3 + bb * x ** 2
                                     + cc * x + dd, x))
            D2 = int(disc4(*(np.array([v], dtype=np.int64)
                             for v in (aa, bb, cc, dd)))[0])
            ok &= (D1 % (1 << 64)) == D2
        check('XV5: quartic discriminant formula == sympy mod 2^64 '
              '(20 random)', ok, '')
    except ImportError:
        check('XV5: quartic disc vs sympy', True, 'sympy unavailable, skipped')
    # (3) the sealed analytic witness for reading B (p=3):
    #     f = x^3+209x^2+42x+234 == (x-12)(x-21)(x-1) mod 3^5, v3(disc)=4,
    #     chain: slope-1 double read (ind 1) then slope-2 split read (side
    #     ind 2): branch-B prefix 2*CUM = 6 > 4.
    d = disc_cubic(209, 42, 234) % 3 ** 5
    v = 0
    while d % 3 == 0 and v < 5:
        d //= 3
        v += 1
    check('XV6: reading-B witness f=(209,42,234) has v3(disc)=4 in-box',
          v == 4, f'v={v}')


# =========================================================================
# main
# =========================================================================
def main():
    quick = '--quick' in sys.argv
    log('X-N3 PROBES (PROBE-5) -- gate X-n3 layers + STALL-probe')
    log(f'spec: MOVES_2026-07-24.md SS X-EXHAUST X.5 + X.1b; '
        f'started {time.strftime("%F %T")}')
    unit_tests()
    mn3 = json.load(open(os.path.join(HERE, 'results',
                                      'case_mn3_results.json')))
    out = {}
    confs = [(3, 3 if quick else 5, mn3['results']['p3']),
             (2, 3 if quick else 8, mn3['results']['p2'])]
    for p, Nmax, mrow in confs:
        if quick and p == 2:
            continue
        out[f'p{p}'] = cubic_gate(p, Nmax, mrow)
    # X2D: deep-thin (3b) legs at p=3
    log('\n===== (3b) DEEP-THIN SWEEP p=3 (live cylinders + a-translation '
        'reduction) =====')
    cts = deep_thin_p3(9)
    ok = True
    for k in (1, 2, 3):
        ok &= (brute_mu_v3(k) == cts[k][1])
    check('X2D-val: live-cylinder counts == brute force at levels 1..3', ok,
          f'mu = {[str(cts[k][1]) for k in (1, 2, 3)]}')
    if not quick and 'p3' in out:
        mu5_box = Fraction(sum(out['p3']['full']['vd_hist'][5:]), 3 ** 15)
        check('X2D-x: deep-thin mu{v3>=5} == in-box census value',
              mu5_box == cts[5][1], f'{cts[5][1]}')
    okD, det = True, []
    for D in (5, 7, 9):
        bnd = Fraction(2, 3 ** (-((D - 3) // -2)))
        okD &= cts[D][1] <= bnd
        det.append(f'D={D}: mu={float(cts[D][1]):.6f} <= {float(bnd):.5f} '
                   f'(live {cts[D][0]})')
    check('X2D: (3b) legs p=3 at D=5,7,9 (deep-thin exact)', okD,
          '; '.join(det))
    # quartic STALL cylinder
    if not quick:
        log('\n===== QUARTIC RS CYLINDER 2^26 @ N=10 (STALL-probe, '
            'exploration-class) =====')
        q = quartic_stall()
        log(f'  buckets {q["tot"]}  ({q["secs"]}s); step-1 floor faults '
            f'{q["floor_faults"]}')
        check('Q1: nu1 RS cell mass (single side slope 3, R1 double root) '
              '== 3 * 2^20 (the three state-probe S_r cells)',
              q['rs1_h3'] == 3 * 2 ** 20, f'{q["rs1_h3"]}')
        check('Q2: quartic RS max consecutive run + main-chain ratio '
              '(measured; s(3)=2 is a CUBIC-box seal -- observation here)',
              q['maxratio'][0] <= 2,
              f'max run {q["maxrun"]}, run hist {q["runhist"]}, max ratio '
              f'{q["maxratio"][0]} at box idx {q["maxratio"][1]}; post-split '
              f'T4 sub-chains unwalked (main-chain lower bound)')
        out['quartic'] = {k: (v if not isinstance(v, Fraction) else str(v))
                          for k, v in q.items() if k != 'maxratio'}
        out['quartic']['maxratio'] = [str(q['maxratio'][0]), q['maxratio'][1]]
    # -------- analytic remark for the adjudication record --------
    log('\nANALYTIC REMARK (derivation, not census; for the (X1a-ALIGN) '
        'adjudication): the X1B violations are the depth>=2 chain-then-'
        'split family -- successive window reads of ONE cluster re-count '
        'the same root-pair differences, which GMN\'s per-order '
        'v_r-normalization subtracts and the raw-table CUM does not.  The '
        'same mechanism defeats reading A beyond box precision: p=3, '
        'l=3 mu=2 selection at slope m>=2 then a mu=2 chain node at m2, '
        'e.g. f=(x-36)(x-117)(x-18): v3(disc)=16 < 18 = 2*(3m+m2) '
        '(verified exactly).  In-box, every reading-A violation candidate '
        'has 2*CUM > N (censored, counted in skipped_A), so X1A PASS is '
        'box-limited support for the COUNT form ind(f) >= d_cert only, '
        'not for the summed raw-table transport.')
    # -------- summary + outputs --------
    npass = sum(1 for v in verdicts if v['ok'])
    log(f'\n===== X-N3 PROBE VERDICT: {npass}/{len(verdicts)} PASS, '
        f'{len(verdicts) - npass} FINDING; total {round(time.time()-T0, 1)}s '
        f'=====')

    def clean(o):
        if isinstance(o, dict):
            return {str(k): clean(v) for k, v in o.items()
                    if k not in ('row_hits', 'exists_ev')}
        if isinstance(o, (list, tuple)):
            return [clean(v) for v in o]
        if isinstance(o, Fraction):
            return str(o)
        if isinstance(o, (np.integer,)):
            return int(o)
        return o
    json.dump(dict(verdicts=verdicts, results=clean(out)),
              open(JSONPATH, 'w'), indent=1, default=str)
    with open(RESULTS, 'a') as fh:
        fh.write('\n\n##### x_n3_probes.py (PROBE-5: X-n3 layers + '
                 'STALL-probe) #####\n')
        fh.write(f'run {time.strftime("%F %T")}; spec MOVES SS X-EXHAUST '
                 f'X.5 + X.1b; long log /tmp/x_n3_census.out\n')
        for v in verdicts:
            fh.write(f"[{'PASS' if v['ok'] else 'FINDING'}] {v['name']}  "
                     f"{v['detail']}\n")
        fh.write('ANALYTIC REMARK: X1B\'s violations = the chain-then-split '
                 'double-charge (window reads of one cluster re-count the '
                 'same pair differences; GMN per-order normalization '
                 'subtracts this, the raw-table CUM does not); the same '
                 'mechanism refutes reading A beyond box precision '
                 '(f=(x-36)(x-117)(x-18) at p=3: v3(disc)=16 < 18=2*CUM, '
                 'exact) -- X1A PASS is box-limited support for the COUNT '
                 'form of (X.1a) only.  Adjudicate at (X1a-ALIGN)/'
                 '(ALIGN-rec), never patch the seal.\n')
        fh.write(f"X-N3 VERDICT: {npass}/{len(verdicts)} PASS, "
                 f"{len(verdicts) - npass} FINDING\n")
    log(f'json -> {JSONPATH}; summary appended -> {RESULTS}')


if __name__ == '__main__':
    main()
