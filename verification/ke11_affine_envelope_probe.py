#!/usr/bin/env python3
"""ke11_affine_envelope_probe.py — UNIT KE11 (bridge campaign, area BP4,
cluster BP4-c1, GATE unit) — the affine-envelope probe.

[CM-first gate for KE2 + KE3 — NEW at blueprint REV 2 (F5); explicit
dependency of both provers, sequenced FIRST (KE11(gate) → KE2/KE3).]

STATEMENT (blueprint BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE11 + §3.E
(E-ii)/(E-iii)): across the n = 3 (and n = 2) census, tabulate per branch
history H
  threshold(H)  vs  1 + Σ_r h_r      (the X2AffP face: threshold(H) <=
                                      1 + c0(n)·Σ h_r, KE2's target), and
  cap(H)        vs  1 + Σ_r h_r      (the X2CapP face: cap(H) <=
                                      c_cap·(1 + Σ h_r), KE3's target, from
                                      TB-CAP's per-clause caps — (tau-hen)
                                      N_V = 1; (tau-irr) per-realized-cell);
FIT empirical c0/c_cap candidates, and SEARCH for branch families whose
threshold/cap outrun every affine candidate.  X2AffP/X2CapP carry XConsts
data (existential constants) like the tails — the gate genre is
candidate-stress + growth detection, NOT ∀-refutation.

DEPS: verification/ census infra (the x_n3 probes branch reader supplies
per-prefix heights h_r, thresholds, and caps; the D.11 per-move form
"largest constrained height + 1" with scale factors Π e_i <= n is the
sketch whose candidate c0 = n·C_move gets computed and stressed).

SEALED PREDICTIONS (Q6 discipline — sealed 2026-07-30, BEFORE any run):
  P1 (threshold leg): threshold(H) <= 1 + c0·Σ h_r holds across the n = 3
      and n = 2 censuses with the sketch candidate c0 = n·C_move (computed
      in-probe from D.11's per-move constants; the earlier X-n3 observation
      face recorded c0(3) = 4 — stressed alongside as reference).  The
      probe reports the empirical minimal c0 per box.
  P2 (cap leg): cap(H) <= c_cap·(1 + Σ h_r) holds in-census; empirical
      minimal c_cap reported per box (TB-CAP clause bookkeeping: hen
      leaves contribute N_V = 1; irr leaves per realized cell,
      level-indexed by the leaf cell's own heights).
  P3 (growth detector): NO branch family whose threshold/cap ratio against
      1 + Σ h_r grows along the census depth scan — the detector trend is
      flat.  A growing family is a FINDING: KE2/KE3 rerouted toward their
      obstruction records naming the branch shape whose threshold outruns
      the affine bound (the blueprint's pre-declared fallback genre); a
      candidate failure alone (P1/P2 with a bigger constant) only replaces
      the candidate and is recorded as such.

OUTPUT (run phase): PASS/FINDING rows appended to
probe_results_2026-07-30.txt; JSON to results/ke11_affine_envelope.json;
exit 0 = seals clean, 1 = FINDING.

STATUS: RUN PHASE (2026-07-30) — body implemented AFTER the seal above
(predictions P1-P3 verbatim untouched).

RUN-PHASE READING NOTES (recorded, not sealed — the census transcription
of the two Lean-side free-data fields, each choice tied to its note):
  * threshold(H) (XCtx.threshold, "Thm 2.1's per-stratum N0"): D.11 reads
    "the finite-level threshold is the largest constrained height + 1"
    (MOVES ~line 126/2678).  Along a branch, the constrained heights are
    the D.10 box-constraint lines of the continuing reads; the walker's
    own per-read weight wf = u1 + s0·hn (the side's line extrapolated to
    slot 0 — exactly the `need` bound the walker's D.10 frame check uses)
    is the largest such height per move.  So threshold(H) := 1 +
    max(wf over the continuing prefix reads), 1 for the empty prefix.
    Scale factors Pi e_i: every continuing node of the n = 3 and n = 2
    censuses has e = 1 (walker-asserted), so heights are already
    original-frame and the product is 1.
  * cap(H) (XCtx.detCap, "TB-CAP cap of the branch's OWN cells"):
    TB-CAP(hen) N_V = 1; TB-CAP(irr) N_V = 1 + the largest base level
    among the halting read's equations (MOVES §T.2), level-indexed by the
    leaf cell's own heights.  Census transcription: cap(row) := 1 +
    wf(row) with wf(row) = u1 + s0·hn of the halting read's side datum
    (hen rows sit at height 0, giving exactly N_V = 1; irr rows give
    1 + the side's own constrained line).
  * Sigma h_r: sum of node heights as census-realized; depth-0 height-0
    selections contribute 0 (the Lean XNode has hpos : 1 <= h, so the
    census sum is <= the Lean sumH — the envelope test run here is the
    HARDER one, weaker-safe).
  * Branch roster: internal branches = realized continuing prefixes;
    leaf branches = prefix + one stable terminal row (the continuing
    (m >= 2, e·g = 1) row is the chain, never a cell).  Only box-exact
    rows enter the tables; unstable/capped reads are counted as margin
    (the honest error bar), mirroring KE4's frac_low convention.
  * n = 3 walker transcribed from ke4_tails_stress_probe.py (itself the
    gate-passed x_n3_probes.run_box adaptation, KE4-V1 = S7 sigma
    integers); the same V1 gate re-run here.  n = 2 leg: bespoke exact
    3-slot polygon walker (chain recenterings t = r·p^h, no rescale, as
    in the n = 3 walker), validated per-f against the disc square-class
    oracle qp_type of census_n2_uniform.py (import-safe): ZERO jointly-
    decided type disagreements tolerated (KE11-V3).
  * C_move (D.11 per-move constant): max over census continuing moves
    (h >= 1) of (threshold increment)/h, exact fractions; height-0 moves
    asserted to have zero increment.  Cap-side sketch candidate:
    c_cap = n + 1 (clause bookkeeping cap = 1 + wf(leaf) with the in-box
    ledger check wf(leaf) <= n·(1 + Sigma h)); the KE3-shape decomposition
    (C_root^emp, C_cell^emp, candidate C_root + 2·C_cell) is recorded for
    the KE3 prover's hccap hypothesis.
"""

import json
import os
import sys
import time
from fractions import Fraction
from itertools import product

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS_TXT = os.path.join(HERE, 'probe_results_2026-07-30.txt')
OUTJSON = os.path.join(HERE, 'results', 'ke11_affine_envelope.json')
OUTTXT = '/tmp/ke11_affine_envelope.out'

sys.path.insert(0, HERE)
from case_mn3_gate import read_data_one, fp_factor      # gate-validated 2026-07
from census_n2_uniform import qp_type, v_p              # import-safe oracle

REFERENCE_C0_N3 = 4       # the earlier X-n3 observation-face number

E_PHASE = False

T0 = time.time()
LOG = open(OUTTXT, 'w')
verdicts = []


def log(s=''):
    print(s, flush=True)
    LOG.write(s + '\n')
    LOG.flush()


def check(name, ok, detail=''):
    tag = 'PASS' if ok else 'FINDING'
    verdicts.append({'name': name, 'ok': bool(ok), 'detail': str(detail)})
    log(f"[{tag}] {name}  {detail}")


# =========================================================================
# n = 3 leg — S7 dictionary + window reader, transcribed VERBATIM from
# ke4_tails_stress_probe.py (which transcribed the gate-passed
# x_n3_probes.py; importing either would truncate its /tmp long log at
# module level; reuse is by transcription + the KE11-V1 end-to-end check).
# =========================================================================
SIGS = ['111', '112', '13', '1121', '31']
S7 = {2: {8: [708608, 5038080, 4329472, 3951616, 2705408]},
      3: {5: [927288, 5196312, 4269024, 2726460, 1185354]}}
SIGMA_OF = {(((1, 1),) * 3): '111',
            tuple(sorted([(1, 1), (1, 2)])): '112',
            ((1, 3),): '13',
            tuple(sorted([(1, 1), (2, 1)])): '1121',
            ((3, 1),): '31'}
CONFIGS = {2: 8, 3: 5}                            # the X.5 box levels

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


# =========================================================================
# PIECE 1 (n = 3) — the branch census: per realized branch (internal
# prefixes + stable leaf rows) the triple (depth, Sigma h_r, threshold,
# [cap]); adapted from the KE4 walker (same reader, same recentering, same
# grouping; tallies changed); validated end-to-end by KE11-V1 = S7 sigma.
# =========================================================================
def census_branches(p):
    """The n = 3 branch roster at (p, CONFIGS[p]): returns dict with
    `internal` = {chainkey: (d, sumh, thr)}, `leaf` = {(chainkey, rowkey):
    (d, sumh, thr, cap)}, `moves` = per-move (h, delta_thr) ledger,
    sigma/undec/fault gate data, and the margin counters."""
    N = CONFIGS[p]
    t0 = time.time()
    M, K, v_tab, code_tab = vpd_tables(p, N)
    size = M ** 3
    idx = np.arange(size, dtype=np.int64)
    C0 = (idx % M).astype(np.int64)
    C1 = ((idx // M) % M).astype(np.int64)
    C2 = (idx // (M * M)).astype(np.int64)
    del idx

    sigma_ct = {s: 0 for s in SIGS}
    undec = 0
    faults_all = {}
    internal = {(): (0, 0, 1)}            # root branch: empty history, thr 1
    leaf = {}
    moves = {}                            # (h, delta) -> count (dedup by chain)
    move_seen = set()
    margin_events = 0                     # unstable sidekeys + dead pops (count of f's)
    wf_gt = 0                             # ledger: leaf rows with wf > n*(1+sumh)

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
                      (), 0, 0, 0, (), 'R', codes))
    del order, sig_sorted, bounds, starts, ends

    while stack:
        (mem, c0, c1, c2, W, hkey, hmu_t, is_root, primes0,
         maxwf, sumh, d, pk, group, codes) = stack.pop()
        n = len(mem)
        if not is_root:
            v_mu = codes[W][0] if codes[W] is not None else N
            if not (codes[W] is not None and v_mu == hmu_t):
                kf = f'VERTEX {codes} hmu={hmu_t}'
                faults_all[kf] = faults_all.get(kf, 0) + n
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
        thr_here = 1 + maxwf
        # stable leaf rows: every (factor, m=1) row of a stable side datum
        # is a cell; the continuing (m>=2, e*g=1) row is the chain.
        for dat in wr['reads']:
            (e, ell, a, flk, frk, res, s0, hn, u1) = dat
            facs = fp_factor(res, p)
            wf_row = u1 + s0 * hn
            for f, m in facs:
                g = len(f) - 1
                if m >= 2:
                    continue               # the chain selection, never a cell
                rowkey = (e, ell, a, flk, frk, tuple(f), s0, hn, u1)
                kk = (pk, rowkey)
                if kk not in leaf:
                    cap = 1 + wf_row
                    sh = sumh + hn
                    leaf[kk] = (d, sh, thr_here, cap)
                    if wf_row > 3 * (1 + sh):
                        wf_gt += 1
        margin_events += n if wr['n_unstable'] > 0 else 0
        if not wr['type_ok']:
            undec += n
        if not wr['type_ok'] or not wr['cont']:
            if wr['type_ok']:
                sig = tuple(sorted(primes0 + wr['primes']))
                assert sum(e * g for e, g in sig) == 3, sig
                sigma_ct[SIGMA_OF[sig]] += n
            if not wr['type_ok']:
                margin_events += n
            continue
        assert len(wr['cont']) == 1, (wr['cont'], codes)
        hn, r, mu, hmu, e_, ell_ = wr['cont'][0]
        assert e_ == 1 and ell_ >= mu, (e_, ell_, mu)
        if not is_root and hn <= hkey:
            kf = f'Iaug-cont-stop hn={hn} hkey={hkey}'
            faults_all[kf] = faults_all.get(kf, 0) + n
            margin_events += n
            undec += n
            continue
        wf_cont = hmu + mu * hn
        nodekey = (mu, ell_, hn, r)
        pk2 = pk + (nodekey,)
        maxwf2 = max(maxwf, wf_cont)
        sumh2 = sumh + hn
        if pk2 not in internal:
            internal[pk2] = (d + 1, sumh2, 1 + maxwf2)
        if pk2 not in move_seen:
            move_seen.add(pk2)
            delta = (1 + maxwf2) - (1 + maxwf)
            assert hn >= 1 or delta == 0, (pk2, delta)
            moves[(hn, delta)] = moves.get((hn, delta), 0) + 1
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
                          False, primes1, maxwf2, sumh2, d + 1, pk2,
                          QGROUP[mu], codes2))

    return dict(p=p, N=N, box=size, internal=internal, leaf=leaf,
                moves=moves, sigma=sigma_ct, undec=undec, faults=faults_all,
                margin_events=margin_events, wf_gt=wf_gt,
                secs=round(time.time() - t0, 1))


# =========================================================================
# PIECE 2 (n = 2) — bespoke exact 3-slot polygon walker (chain
# recenterings t = r·p^h, no rescale), oracle-validated per f (KE11-V3).
# =========================================================================
def _sqrt_roots(u, p):
    """Roots z of z^2 = u mod p (p odd)."""
    return [z for z in range(p) if (z * z - u) % p == 0]


def walk_n2_one(p, N, a1, a0):
    """Walk x^2 + a1 x + a0 (residues mod p^N).  Returns (dtype, rows,
    censored, moves, chain): dtype in {'split','inert','ram',None};
    rows = [(kind, d, sumh, thr, cap)] exact branch rows (internal rows for
    d>=1 prefixes, leaf rows per certificate side); censored = True if some
    branch data is box-capped (margin); moves = [(h, delta_thr)]."""
    M = p ** N
    b1, b0 = a1 % M, a0 % M
    d = 0
    sumh = 0
    maxwf = 0
    rows = []
    moves = []
    chain = []
    censored = False
    dtype = None
    while True:
        thr = 1 + maxwf
        v1 = v_p(b1, p, N)
        v0 = v_p(b0, p, N)
        if v0 == 0:
            # slope-0 full side; residual = f mod p
            res = [b0 % p, b1 % p, 1]
            facs = fp_factor(res, p) if b0 % p != 0 else None
            # fp_factor needs nonzero constant; v0 == 0 guarantees it
            dbl = [(-f[0]) % p for f, m in facs if m == 2 and len(f) == 2]
            if dbl:
                r = dbl[0]
                # height-0 continuing selection (depth-0 only)
                chain.append((0, r))
                moves.append((0, 0))
                d += 1
                rows.append(('int', d, sumh, thr))
                b0 = (b0 + r * b1 + r * r) % M
                b1 = (b1 + 2 * r) % M
                continue
            simple = [f for f, m in facs if m == 1]
            if len(simple) == 2 or (len(simple) == 1 and len(simple[0]) == 2):
                dtype = 'split'
            elif len(simple) == 1 and len(simple[0]) == 3:
                dtype = 'inert'
            for f in simple:
                rows.append(('leaf', d, sumh + 0, thr, 1))
            break
        # v0 >= 1 here (possibly capped at N)
        if v1 == 0:
            # vertex (1,0): sides slope v0 (linear) + slope 0 (linear)
            dtype = 'split'
            rows.append(('leaf', d, sumh + 0, thr, 1))          # slope-0 hen
            if v0 >= N:
                censored = True                     # height of the tall side unknown
            else:
                rows.append(('leaf', d, sumh + v0, thr, 1 + v0))
            break
        # v1 >= 1, v0 >= 1
        v1_exact, v0_exact = v1 < N, v0 < N
        if not v0_exact and not v1_exact:
            censored = True                          # b0, b1 both cap out
            break
        if not v0_exact and 2 * v1 >= N:
            censored = True                          # v0 vs 2*v1 undecidable
            break
        if v0_exact and (not v1_exact or v0 < 2 * v1):
            # single side (0,v0)-(2,0), slope v0/2; middle slot above
            if v0 % 2 == 1:
                dtype = 'ram'
                rows.append(('leaf', d, sumh + v0, thr, 1 + v0))
                break
            m = v0 // 2
            u0 = (b0 // p ** v0) % p
            if p == 2:
                # z^2 + 1 = (z+1)^2: continue at height m, center 1
                t = p ** m
                chain.append((m, 1))
                delta = max(0, v0 - maxwf)
                moves.append((m, delta))
                maxwf = max(maxwf, v0)
                sumh += m
                d += 1
                rows.append(('int', d, sumh, 1 + maxwf))
                b0 = (b0 + t * b1 + t * t) % M
                b1 = (b1 + 2 * t) % M
                continue
            rts = _sqrt_roots((-u0) % p, p)
            if len(rts) == 2:
                dtype = 'split'
                rows.append(('leaf', d, sumh + m, thr, 1 + v0))
                rows.append(('leaf', d, sumh + m, thr, 1 + v0))
            else:
                dtype = 'inert'
                rows.append(('leaf', d, sumh + m, thr, 1 + v0))
            break
        if v0_exact and v1_exact and v0 == 2 * v1:
            # single side through the middle: residual z^2 + u1 z + u0
            u1 = (b1 // p ** v1) % p
            u0 = (b0 // p ** v0) % p
            facs = fp_factor([u0, u1, 1], p)
            dbl = [(-f[0]) % p for f, m in facs if m == 2 and len(f) == 2]
            if dbl:
                c = dbl[0]
                t = (c * p ** v1) % M
                chain.append((v1, c))
                delta = max(0, v0 - maxwf)
                moves.append((v1, delta))
                maxwf = max(maxwf, v0)
                sumh += v1
                d += 1
                rows.append(('int', d, sumh, 1 + maxwf))
                b0 = (b0 + t * b1 + t * t) % M
                b1 = (b1 + 2 * t) % M
                continue
            simple = [f for f, m in facs if m == 1]
            if len(simple) == 2:
                dtype = 'split'
                rows.append(('leaf', d, sumh + v1, thr, 1 + v0))
                rows.append(('leaf', d, sumh + v1, thr, 1 + v0))
            else:
                dtype = 'inert'
                rows.append(('leaf', d, sumh + v1, thr, 1 + v0))
            break
        # v0 > 2*v1 (v1 exact; v0 exact or capped): two linear sides
        dtype = 'split'
        rows.append(('leaf', d, sumh + v1, thr, 1 + 2 * v1))
        if v0_exact:
            rows.append(('leaf', d, sumh + (v0 - v1), thr, 1 + v0))
        else:
            censored = True                          # tall side height unknown
        break
    return dtype, rows, censored, moves, chain


def census_branches_n2(p, N):
    """The n = 2 branch roster + the per-f oracle gate (KE11-V3)."""
    t0 = time.time()
    M = p ** N
    internal = {(): (0, 0, 1)}
    leaf = {}
    moves = {}
    move_seen = set()
    margin = 0
    walker_dec = oracle_dec = both = disagree = 0
    disagree_w = None
    for a1 in range(M):
        for a0 in range(M):
            dtype, rows, cens, mvs, chain = walk_n2_one(p, N, a1, a0)
            ot = qp_type(a1, a0, p, N)
            if dtype:
                walker_dec += 1
            if ot != 'und':
                oracle_dec += 1
            if dtype and ot != 'und':
                both += 1
                if dtype != ot:
                    disagree += 1
                    if disagree_w is None:
                        disagree_w = (a1, a0, dtype, ot)
            if cens or dtype is None:
                margin += 1
            for i, (h, delta) in enumerate(mvs):
                ck = tuple(chain[:i + 1])
                if ck not in move_seen:
                    move_seen.add(ck)
                    moves[(h, delta)] = moves.get((h, delta), 0) + 1
            for row in rows:
                if row[0] == 'int':
                    _, dd, sh, th = row
                    ck = tuple(chain[:dd])
                    if ck not in internal:
                        internal[ck] = (dd, sh, th)
                else:
                    _, dd, sh, th, cp = row
                    kk = (tuple(chain[:dd]), (sh, th, cp))
                    if kk not in leaf:
                        leaf[kk] = (dd, sh, th, cp)
    gate = dict(walker_dec=walker_dec, oracle_dec=oracle_dec, both=both,
                disagree=disagree, disagree_witness=disagree_w)
    return dict(p=p, N=N, box=M * M, internal=internal, leaf=leaf,
                moves=moves, margin_events=margin, gate=gate, wf_gt=0,
                secs=round(time.time() - t0, 1))


# =========================================================================
# PIECE 3 — the sketch candidate c0 = n·C_move (D.11 per-move constants).
# =========================================================================
def sketch_candidate_c0(n, movesdict):
    """c0 = n·C_move from D.11's per-move threshold form ('largest
    constrained height + 1', scale factors Pi e_i <= n; e_i = 1 in these
    censuses); C_move = max per-move (threshold increment)/h over h >= 1
    moves, exact.  Returns the candidate + the per-move constant ledger."""
    ratios = [Fraction(delta, h) for (h, delta) in movesdict if h >= 1]
    cmove = max(ratios, default=Fraction(0))
    ledger = sorted(((h, delta, cnt) for (h, delta), cnt in movesdict.items()),
                    key=lambda t: (t[0], t[1]))
    return n * cmove, cmove, ledger


# =========================================================================
# PIECE 4 — the stress + fit legs (P1 threshold, P2 cap).
# =========================================================================
def stress_threshold(branch_rows, c0_candidates):
    """P1: threshold <= 1 + c0·Sigma h per candidate; empirical min c0.
    branch_rows: [(d, sumh, thr)].  Sanity leg: sumh = 0 forces thr <= 1
    (else NO affine constant works — the P3 finding genre)."""
    bad_form = [(d, sh, th) for (d, sh, th) in branch_rows
                if sh == 0 and th > 1]
    c0_min = max((Fraction(th - 1, sh) for (d, sh, th) in branch_rows
                  if sh >= 1), default=Fraction(0))
    viols = {}
    for name, c0 in c0_candidates.items():
        viols[name] = [(d, sh, th) for (d, sh, th) in branch_rows
                       if Fraction(th) > 1 + Fraction(c0) * sh][:3]
    return dict(bad_form=bad_form[:3], n_bad_form=len(bad_form),
                c0_min=c0_min, violations=viols)


def stress_cap(leaf_rows, ccap_candidates):
    """P2: cap <= c_cap·(1 + Sigma h) per candidate; empirical min c_cap;
    the KE3-shape (C_root^emp, C_cell^emp) decomposition recorded."""
    ccap_min = max((Fraction(cp, 1 + sh) for (d, sh, th, cp) in leaf_rows),
                   default=Fraction(0))
    croot = max((cp for (d, sh, th, cp) in leaf_rows if d == 0), default=1)
    # per-branch cap increment against its own (1 + h)-weighted length:
    # C_cell^emp = max (cap - C_root)/(len + Sigma h) over deeper leaves
    ccell = max((Fraction(max(cp - croot, 0), d + sh)
                 for (d, sh, th, cp) in leaf_rows if d + sh >= 1),
                default=Fraction(0))
    viols = {}
    for name, cc in ccap_candidates.items():
        viols[name] = [(d, sh, th, cp) for (d, sh, th, cp) in leaf_rows
                       if Fraction(cp) > Fraction(cc) * (1 + sh)][:3]
    return dict(ccap_min=ccap_min, croot_emp=croot, ccell_emp=ccell,
                violations=viols)


def growth_detector(branch_rows, leaf_rows):
    """P3: per-depth max ratios (thr-1)/max(Sigma h,1) and cap/(1+Sigma h)
    along the census depth scan; a growing trend (positive slope AND a
    rising tail) is the finding.  Returns per-depth tables + verdicts."""
    import math
    thr_by_d, cap_by_d = {}, {}
    for (d, sh, th) in branch_rows:
        r = Fraction(th - 1, max(sh, 1))
        thr_by_d[d] = max(thr_by_d.get(d, Fraction(0)), r)
    for (d, sh, th, cp) in leaf_rows:
        r = Fraction(cp, 1 + sh)
        cap_by_d[d] = max(cap_by_d.get(d, Fraction(0)), r)

    def trend(table):
        pts = sorted((d, float(v)) for d, v in table.items())
        if len(pts) < 2:
            return dict(pts=pts, slope=0.0, growing=False)
        xs = [d for d, _ in pts]
        ys = [v for _, v in pts]
        nn = len(xs)
        xm, ym = sum(xs) / nn, sum(ys) / nn
        den = sum((x - xm) ** 2 for x in xs)
        slope = (sum((x - xm) * (y - ym) for x, y in zip(xs, ys)) / den
                 if den else 0.0)
        tail_up = len(pts) >= 3 and ys[-1] > ys[-2] > ys[-3]
        return dict(pts=pts, slope=round(slope, 4),
                    growing=(slope > 0.1 and tail_up))
    return dict(thr=trend(thr_by_d), cap=trend(cap_by_d))


# =========================================================================
# main
# =========================================================================
def run_box(tag, n, p, walk):
    """All checks for one census box; returns the JSON row."""
    log(f"\n===== {tag}: n={n} p={p} N={walk['N']} (box {walk['box']}) =====")
    log(f"  walk: {walk['secs']}s; internal branches {len(walk['internal'])}; "
        f"leaf branches {len(walk['leaf'])}; margin events "
        f"{walk['margin_events']}")
    branch_rows = list(walk['internal'].values()) \
        + [(d, sh, th) for (d, sh, th, cp) in walk['leaf'].values()]
    leaf_rows = list(walk['leaf'].values())

    c0_sk, cmove, ledger = sketch_candidate_c0(n, walk['moves'])
    log(f'  D.11 per-move ledger (h, delta_thr, #chains): {ledger}')
    log(f'  C_move = {cmove} => sketch c0 = n·C_move = {c0_sk}')

    cands = {'sketch_nCmove': c0_sk, 'reference_c0_4': Fraction(REFERENCE_C0_N3)}
    st = stress_threshold(branch_rows, cands)
    okform = st['n_bad_form'] == 0
    ok_sk = not st['violations']['sketch_nCmove']
    ok_ref = not st['violations']['reference_c0_4']
    check(f'KE11-P1 {tag}: threshold(H) <= 1 + c0·Sigma h_r with the sketch '
          f'candidate c0 = n·C_move = {c0_sk} (and Sigma h = 0 => thr <= 1)',
          okform and ok_sk,
          f"empirical minimal c0 = {st['c0_min']}; sketch violations "
          f"{st['violations']['sketch_nCmove']}; bad-form rows "
          f"{st['bad_form']} (n={st['n_bad_form']})")
    check(f'KE11-P1r {tag}: the X-n3 observation-face reference c0 = 4 '
          f'passes alongside', ok_ref,
          f"violations {st['violations']['reference_c0_4']}")

    ccands = {'sketch_n_plus_1': Fraction(n + 1)}
    sc = stress_cap(leaf_rows, ccands)
    ke3_cand = sc['croot_emp'] + 2 * sc['ccell_emp']
    ccands2 = dict(ccands)
    ccands2['ke3_shape_Croot_2Ccell'] = ke3_cand
    sc = stress_cap(leaf_rows, ccands2)
    ok_cap = not sc['violations']['sketch_n_plus_1']
    check(f'KE11-P2 {tag}: cap(H) <= c_cap·(1 + Sigma h_r) with the clause '
          f'candidate c_cap = n + 1 = {n + 1}', ok_cap,
          f"empirical minimal c_cap = {sc['ccap_min']}; violations "
          f"{sc['violations']['sketch_n_plus_1']}; KE3-shape "
          f"(C_root^emp, C_cell^emp) = ({sc['croot_emp']}, {sc['ccell_emp']}) "
          f"=> C_root + 2·C_cell = {ke3_cand}, violations "
          f"{sc['violations']['ke3_shape_Croot_2Ccell']}; "
          f"wf>n(1+Sigma h) ledger count {walk['wf_gt']}")

    gd = growth_detector(branch_rows, leaf_rows)
    check(f'KE11-P3 {tag}: growth detector — per-depth max ratios flat '
          f'(no super-affine branch family)',
          not gd['thr']['growing'] and not gd['cap']['growing'],
          f"thr ratios by depth {gd['thr']['pts']} (slope "
          f"{gd['thr']['slope']}); cap ratios by depth {gd['cap']['pts']} "
          f"(slope {gd['cap']['slope']})")

    return dict(
        n=n, p=p, N=walk['N'], box=walk['box'],
        n_internal=len(walk['internal']), n_leaf=len(walk['leaf']),
        margin_events=int(walk['margin_events']),
        move_ledger=[[h, dlt, c] for h, dlt, c in ledger],
        C_move=str(cmove), c0_sketch=str(c0_sk),
        c0_min=str(st['c0_min']), bad_form=st['bad_form'],
        thr_violations={k: v for k, v in st['violations'].items()},
        ccap_min=str(sc['ccap_min']), croot_emp=int(sc['croot_emp']),
        ccell_emp=str(sc['ccell_emp']), ke3_candidate=str(ke3_cand),
        cap_violations={k: v for k, v in sc['violations'].items()},
        growth=dict(thr=gd['thr'], cap=gd['cap']),
        secs=walk['secs'])


def main():
    if E_PHASE:
        print(__doc__)
        return 3
    log('KE11 AFFINE-ENVELOPE PROBE — RUN PHASE (gate for KE2 + KE3)')
    log(f'spec: BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE11 + §3.E (E-ii)/(E-iii); '
        f'sealed predictions P1-P3 of 2026-07-30 (header); '
        f'started {time.strftime("%F %T")}')
    out = {'boxes': {}}

    # ---- n = 3 legs (walker validated by S7 + zero faults) ----
    for p in (2, 3):
        N = CONFIGS[p]
        walk = census_branches(p)
        want = S7[p][N]
        got = [walk['sigma'][s] for s in SIGS]
        wundec = p ** (3 * N) - sum(want)
        check(f'KE11-V1 n=3 p={p}: adapted walker reproduces the S7 decided '
              f'integers + undecided count (x_n3 gate values)',
              got == want and walk['undec'] == wundec,
              f'sigma {got} vs {want}; undec {walk["undec"]} vs {wundec}')
        check(f'KE11-V2 n=3 p={p}: engine faults (VERTEX/BOX/Iaug/partition) '
              f'== 0', len(walk['faults']) == 0,
              str(dict(list(walk['faults'].items())[:3])))
        out['boxes'][f'n3_p{p}'] = run_box(f'n=3 p={p}', 3, p, walk)

    # ---- n = 2 legs (walker validated per-f against the disc oracle) ----
    for p, N in ((2, 8), (3, 6)):
        walk = census_branches_n2(p, N)
        g = walk['gate']
        check(f'KE11-V3 n=2 p={p}: walker type == disc square-class oracle '
              f'on every jointly decided f', g['disagree'] == 0,
              f"walker decided {g['walker_dec']}, oracle decided "
              f"{g['oracle_dec']}, both {g['both']}, disagreements "
              f"{g['disagree']} (witness {g['disagree_witness']})")
        row = run_box(f'n=2 p={p}', 2, p, walk)
        row['oracle_gate'] = {k: v for k, v in g.items()}
        out['boxes'][f'n2_p{p}'] = row

    npass = sum(1 for v in verdicts if v['ok'])
    nfind = len(verdicts) - npass
    log(f'\n===== KE11 VERDICT: {npass}/{len(verdicts)} PASS, {nfind} '
        f'FINDING; total {round(time.time() - T0, 1)}s =====')
    log('GATE CONSEQUENCE: '
        + ('seals clean — KE2/KE3 provers UNBLOCKED (candidate constants '
           'recorded; the ThresholdStep/CapStep named laws are census-'
           'consistent as sketched).'
           if nfind == 0 else
           'FINDING on record — adjudicate per the P3 genre (candidate '
           'replacement vs obstruction reroute) BEFORE accepting KE2/KE3.'))
    out['verdicts'] = verdicts
    os.makedirs(os.path.dirname(OUTJSON), exist_ok=True)
    with open(OUTJSON, 'w') as fh:
        json.dump(out, fh, indent=1, default=str)
    with open(RESULTS_TXT, 'a') as fh:
        fh.write('\n\n##### ke11_affine_envelope_probe.py (UNIT KE11: '
                 'affine-envelope gate for KE2 + KE3) #####\n')
        fh.write(f'run {time.strftime("%F %T")}; spec '
                 f'BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE11 + §3.E '
                 f'(E-ii)/(E-iii); long log {OUTTXT}\n')
        for v in verdicts:
            fh.write(f"[{'PASS' if v['ok'] else 'FINDING'}] {v['name']}  "
                     f"{v['detail']}\n")
        fh.write(f'KE11 VERDICT: {npass}/{len(verdicts)} PASS, {nfind} '
                 f'FINDING\n')
    log(f'json -> {OUTJSON}; summary appended -> {RESULTS_TXT}')
    return 1 if nfind else 0


if __name__ == '__main__':
    sys.exit(main())
