#!/usr/bin/env python3
"""ke13_align_rowcheck_probe.py — UNIT KE13 (bridge campaign, area BP4,
cluster BP4-c1, GATE unit) — the ALIGN transport row-check probe.

[CM-first gate for KE8 — NEW at blueprint REV 2 (F5); explicit dependency of
the KE8 prover, sequenced FIRST (KE13(gate) → KE8).]

STATEMENT (blueprint BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE13 + §3.E
(E-vii)): recompute the T0-T5 index-table increments on the census under
READING A and check GMN Cor 4.19's accounting ROW-BY-ROW; a violating row
pins the failing transport row of KE8's certified-increment transport
(ALIGN-inc: GMN Cor 4.19's accounting through the X.1a index table) BEFORE
any prover runs — KE8's pre-declared fallback is exactly the per-row
obstruction record (which table row's transport fails).

READING FENCE (binding on every KD/KE unit — the X1B adjudication, tasks
57/58): all consumption is the (CD)-pinned READING A — d_cert counts only
CERTIFIED nodes, row-0 = no bound certified; prefixes through mu >= 2
(engine-descending) nodes only.  The over-broad reading (T1-row mu·g = 1
selections charged) was REFUTED with 155,648 in-box violations and is a
RECORDED COUNTERMODEL, not a target: this probe never runs it.

DEPS: verification/ census infra (the x_n3_probes layer-(i) sweep machinery
— reading A sealed 0 violations there for the CUMULATIVE index inequality
v_p(disc f) >= 2·CUM(j); this unit refines that seal from the cumulative
form to the PER-ROW increments of the T0-T5 table against Cor 4.19's
accounting).  Consumes the declared GMN axiom's accounting as the reference
values (allowed: already-trusted cite; nothing new is asserted about GMN).

SEALED PREDICTIONS (Q6 discipline — sealed 2026-07-30, BEFORE any run):
  P1 (row-check, sealed CLEAN): 0 violations of the per-row accounting
      under reading A across both census boxes (p = 2 cubic 2^24 level-8;
      p = 3 3^15 level-5): on every census branch prefix, each certified
      node's index increment equals (or is bounded by, per the row's stated
      direction in the T0-T5 table: T1 -> l(e·h·l−e−h+1)/2,
      T2 -> (e−1)(h−1)/2, T3/T4 -> 0, with the T0/T5 rows as the table
      states them) the Cor 4.19 accounting value for its row.  Consistent
      with the prior layer-(i) reading-A seal (0 violations, cumulative
      form).
  P2 (per-row resolution): the violation tally is reported PER ROW
      (T0..T5) — a violating row is a FINDING naming that row (the exact
      shape KE8's fallback consumes); a violation in the cumulative sweep
      that no single row explains is a DEVIATION for adjudication (reader
      drift vs table transcription), never patched in-probe.
  P3 (consistency): the reading-A cumulative sweep re-run reproduces the
      prior x_n3 X1A seal (0 in-box violations); mismatch = infrastructure
      finding, stop and adjudicate before reading P1/P2.

OUTPUT (run phase): PASS/FINDING rows appended to
probe_results_2026-07-30.txt; JSON to results/ke13_align_rowcheck.json;
exit 0 = P1-P3 clean, 1 = FINDING.

STATUS: RUN PHASE (2026-07-30) — body implemented AFTER the seal above
(predictions P1-P3 verbatim untouched).  Reader transcribed VERBATIM from
the gate-passed x_n3_probes.py per the KE4 precedent (importing that module
would truncate its /tmp long log at module level; reuse is by transcription
+ the walker-faithfulness S7 tie below instead).

RUN-PHASE READING NOTES (recorded, not sealed):
  * Node/row semantics: a READING-A charged node is a mu >= 2
    engine-descending continuation (the walker's `cont`, unique at n = 3)
    with node letters (e, l, h) = (side e, side l, continuation height h_n);
    its row per the frozen Lean classifier (MovesX/Defs.lean `rowOf`):
    l >= 2 -> T1; l = 1, e >= 2 -> T2 (h >= 2) / T3 (h = 1); l = 1,
    e = 1 -> T4; terminal reads -> T5 (T0 is folded into T5 per the Lean
    `Row` docstring).  The walker's own increment (`ind_of_side`, the
    layer-(i) CUM contribution) is checked per realized (row, e, l, h)
    tuple against an INDEPENDENT transcription of the Cor 4.19 accounting
    values from the sealed-prediction text above; h = 0 (slope-0
    root-level) continuations charge 0 in all rows and are tallied
    uncharged, exactly as the prior X1A sweep charged them.
  * n = 3 realization scope (recorded): every mu >= 2 continuation at
    n = 3 has e = 1 and l >= mu >= 2 (walker invariant, asserted), so the
    CHARGED population realizes ONLY the T1 row; T2/T3/T4 are emitted as
    0-tally table rows with their transcribed accounting values (the KE8
    prover's reference ledger), and T5 rows are the walk-complete terminal
    reads (charged 0).  This matches the prior X1A seal's scope — the
    cumulative reading-A CUM at n = 3 is a pure-T1 sum.
  * P3's reproduction targets: the prior x_n3 X1A seal rows (run
    2026-07-29, probe_results): p = 2 — violations 0, censored-skipped
    21504; p = 3 — violations 0, censored-skipped 26244; plus the S7
    decided integers + undec count at max level (walker faithfulness, the
    KE4-V1 pattern).
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
OUTJSON = os.path.join(HERE, 'results', 'ke13_align_rowcheck.json')
OUTTXT = '/tmp/ke13_align_rowcheck.out'

sys.path.insert(0, HERE)
from case_mn3_gate import read_data_one, fp_factor  # gate-validated 2026-07

ROWS = ['T0', 'T1', 'T2', 'T3', 'T4', 'T5']
CONFIGS = {2: 8, 3: 5}                    # p -> box level (the X.5 boxes)
PRIOR_X1A = {2: dict(viol=0, skipped=21504),   # x_n3 X1A seal, 2026-07-29
             3: dict(viol=0, skipped=26244)}

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
# S7 integers (max level) + sigma dictionary — VERBATIM from x_n3_probes
# (walker-faithfulness tie, the KE4-V1 pattern).
# =========================================================================
SIGS = ['111', '112', '13', '1121', '31']
S7MAX = {2: [708608, 5038080, 4329472, 3951616, 2705408],
         3: [927288, 5196312, 4269024, 2726460, 1185354]}
SIGMA_OF = {(((1, 1),) * 3): '111',
            tuple(sorted([(1, 1), (1, 2)])): '112',
            ((1, 3),): '13',
            tuple(sorted([(1, 1), (2, 1)])): '1121',
            ((3, 1),): '31'}


# =========================================================================
# The window reader — transcribed VERBATIM from x_n3_probes.py (see STATUS).
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
    seen = {}
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


def ind_of_side(e, hn, ell):
    """The walker's OWN (IND) table value (transcribed VERBATIM from
    x_n3_probes — the object under test): l>=2 -> T1; l=1,e>=2 -> T2/T3;
    l=1,e=1 -> T4: 0; h=0 gives 0 in all rows."""
    if ell >= 2:
        v = ell * (e * hn * ell - e - hn + 1)
        assert v % 2 == 0
        return v // 2
    if e >= 2:
        return (e - 1) * (hn - 1) // 2
    return 0


def row_increment(node):
    """Classify a certified node into its T0-T5 row and return (row,
    observed index increment, Cor 4.19 accounting value for that row).
    `node` = (e, ell, hn) — the reading-A continuation letters.  The row
    classifier transcribes the frozen Lean `rowOf` (MovesX/Defs.lean); the
    accounting value is an INDEPENDENT transcription of the sealed P1 row
    formulas (T1 -> l(e·h·l−e−h+1)/2, T2 -> (e−1)(h−1)/2, T3/T4 -> 0).
    Integrality of the halved rows is asserted (an odd product is a
    transcription DEVIATION, reported)."""
    e, ell, hn = node
    if ell >= 2:
        row = 'T1'
        num = ell * (e * hn * ell - e - hn + 1)
        ok_parity = (num % 2 == 0)
        acct = num // 2
    elif e >= 2:
        row = 'T2' if hn >= 2 else 'T3'
        if row == 'T2':
            num = (e - 1) * (hn - 1)
            ok_parity = (num % 2 == 0)
            acct = num // 2
        else:
            ok_parity, acct = True, 0
    else:
        row, ok_parity, acct = 'T4', True, 0
    observed = ind_of_side(e, hn, ell)
    return row, observed, acct, ok_parity


def rowcheck_sweep(p):
    """P1/P2 + P3: one full-level census walk (the x_n3 run_box FULL path
    transcribed verbatim minus the letter/teeth/ratio machinery), collecting
    (i) per-node row records at every reading-A continuation — realized
    (row, e, l, h) tuples with member counts, walker increment, accounting
    value, match flag; (ii) the reading-A cumulative sweep viol_A/skipped_A
    (P3 reproduction); (iii) sigma/undec (walker faithfulness); (iv) T5
    terminal-read tallies (charged 0)."""
    N = CONFIGS[p]
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
    faults_all = {}
    # v_p(disc) read in-box (exact iff < N)
    d = (18 * C2 * C1 * C0 - 4 * C2 ** 3 * C0 + (C2 * C1) ** 2
         - 4 * C1 ** 3 - 27 * C0 ** 2) % M
    vd = np.zeros(size, np.int16)
    for k in range(1, N + 1):
        vd[d % (p ** k) == 0] = k
    del d
    viol_A = [0, None]
    skipped_A = 0
    rows_tally = {}     # (row, e, ell, hn) -> [members, observed, acct, ok]
    parity_dev = 0
    t5_members = 0      # walk-complete terminal reads (row T5, charged 0)

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
                      (), 0, 'R', codes))
    del order, sig_sorted, bounds, starts, ends

    while stack:
        (mem, c0, c1, c2, W, hkey, hmu_t, is_root, primes0, cum, group,
         codes) = stack.pop()
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
        if not wr['type_ok']:
            undec[mem] = True
        if not wr['type_ok'] or not wr['cont']:
            if wr['type_ok']:
                sig = tuple(sorted(primes0 + wr['primes']))
                assert sum(e * g for e, g in sig) == 3, sig
                sigma_ct[SIGMA_OF[sig]] += n
                t5_members += n     # terminal read: T5 row, charged 0
            continue
        assert len(wr['cont']) == 1, (wr['cont'], codes)
        hn, r, mu, hmu, e_, ell_ = wr['cont'][0]
        assert e_ == 1 and ell_ >= mu, (e_, ell_, mu)
        if not is_root and hn <= hkey:
            kf = f'Iaug-cont-stop hn={hn} hkey={hkey}'
            faults_all[kf] = faults_all.get(kf, 0) + n
            undec[mem] = True
            continue
        # --- THE ROW CHECK: the reading-A continuation node ---
        row, observed, acct, ok_parity = row_increment((e_, ell_, hn))
        if not ok_parity:
            parity_dev += n
        key = (row, e_, ell_, hn)
        if key not in rows_tally:
            rows_tally[key] = [0, observed, acct, observed == acct]
        rows_tally[key][0] += n
        iv = ind_of_side(e_, hn, ell_)
        cum2 = cum + iv
        # reading-A cumulative sweep (charged when hn >= 1, as in run_box)
        if hn >= 1:
            bad = mem[(vd[mem] < 2 * cum2) & (vd[mem] < N)]
            skipped_A += int(((vd[mem] >= N) & (2 * cum2 > N)).sum())
            if len(bad):
                viol_A[0] += len(bad)
                if viol_A[1] is None:
                    b = int(bad[0])
                    viol_A[1] = (int(C2[b]), int(C1[b]), int(C0[b]),
                                 int(vd[b]), 2 * cum2, row)
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
                          False, primes1, cum2, QGROUP[mu], codes2))
    return dict(p=p, N=N, box=size, undec=int(undec.sum()), sigma=sigma_ct,
                faults=faults_all, viol_A=viol_A, skipped_A=skipped_A,
                rows_tally=rows_tally, parity_dev=parity_dev,
                t5_members=t5_members, secs=round(time.time() - t0, 1))


def cumulative_consistency(walk, p):
    """P3: reproduce the prior X1A reading-A cumulative seal (0 in-box
    violations + the recorded censored-skipped count), plus the S7 walker
    faithfulness tie at max level."""
    prior = PRIOR_X1A[p]
    ok_cum = (walk['viol_A'][0] == prior['viol']
              and walk['skipped_A'] == prior['skipped'])
    want = S7MAX[p]
    got = [walk['sigma'][s] for s in SIGS]
    wundec = p ** (3 * CONFIGS[p]) - sum(want)
    ok_s7 = (got == want and walk['undec'] == wundec)
    return ok_cum, ok_s7, got, want, wundec


def append_results():
    npass = sum(1 for v in verdicts if v['ok'])
    with open(RESULTS_TXT, 'a') as fh:
        fh.write('\n\n##### ke13_align_rowcheck_probe.py (UNIT KE13: ALIGN '
                 'transport row-check gate for KE8) #####\n')
        fh.write(f'run {time.strftime("%F %T")}; spec '
                 f'BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE13 + §3.E (E-vii); '
                 f'sealed P1-P3 of 2026-07-30 in force; reading A ONLY '
                 f'(X1B fence); long log {OUTTXT}\n')
        for v in verdicts:
            fh.write(f"[{'PASS' if v['ok'] else 'FINDING'}] {v['name']}  "
                     f"{v['detail']}\n")
        fh.write(f'KE13 VERDICT: {npass}/{len(verdicts)} PASS, '
                 f'{len(verdicts) - npass} FINDING\n')


def main():
    log('KE13 ALIGN TRANSPORT ROW-CHECK PROBE (gate for KE8)')
    log(f'spec: BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE13 + §3.E (E-vii); '
        f'sealed predictions P1-P3 of 2026-07-30 (header); reading A ONLY; '
        f'started {time.strftime("%F %T")}')
    out = {'boxes': {}}
    for p in sorted(CONFIGS):
        N = CONFIGS[p]
        log(f'\n===== CUBIC BOX p={p}, level {N} (size {p ** (3 * N)}) =====')
        walk = rowcheck_sweep(p)
        log(f'  walk: {walk["secs"]}s; undec {walk["undec"]}; '
            f'T5 (terminal, charged 0) members {walk["t5_members"]}')
        # P3 FIRST (per the seal: infrastructure gate before P1/P2)
        ok_cum, ok_s7, got, want, wundec = cumulative_consistency(walk, p)
        check(f'KE13-P3a p={p}: reading-A cumulative sweep reproduces the '
              f'prior X1A seal (violations {PRIOR_X1A[p]["viol"]}, '
              f'censored-skipped {PRIOR_X1A[p]["skipped"]})', ok_cum,
              f'violations {walk["viol_A"][0]} (witness {walk["viol_A"][1]}), '
              f'skipped {walk["skipped_A"]}')
        check(f'KE13-P3b p={p}: walker faithfulness — S7 decided integers + '
              f'undec at level {N}', ok_s7,
              f'sigma {got} vs {want}; undec {walk["undec"]} vs {wundec}')
        check(f'KE13-V1 p={p}: engine faults == 0',
              len(walk['faults']) == 0,
              str(dict(list(walk['faults'].items())[:3])))
        if not (ok_cum and ok_s7):
            log('  P3 MISMATCH — infrastructure finding; P1/P2 NOT read at '
                'this p (per the seal: stop and adjudicate).')
            out['boxes'][f'p{p}'] = dict(p=p, p3_ok=False)
            continue
        # P1/P2: the per-row table
        per_row = {r: dict(tuples=0, members=0, violations=0,
                           viol_tuples=[]) for r in ROWS}
        table_lines = []
        for (row, e, ell, hn), (nmem, observed, acct, ok) in \
                sorted(walk['rows_tally'].items()):
            pr = per_row[row]
            pr['tuples'] += 1
            pr['members'] += nmem
            if not ok:
                pr['violations'] += nmem
                pr['viol_tuples'].append((e, ell, hn, observed, acct))
            table_lines.append(
                f'    {row} (e={e}, l={ell}, h={hn}): members {nmem}, '
                f'walker increment {observed}, Cor 4.19 accounting {acct} '
                f'-> {"MATCH" if ok else "VIOLATION"}')
        per_row['T5']['members'] = walk['t5_members']
        log('  T0-T5 row table (realized reading-A continuation tuples + '
            'terminal reads):')
        for line in table_lines:
            log(line)
        log(f'    T5 (terminal reads): members {walk["t5_members"]}, '
            f'charged 0 (as the table states); T0 folded into T5 per the '
            f'Lean Row docstring')
        empty_rows = [r for r in ('T2', 'T3', 'T4')
                      if per_row[r]['members'] == 0]
        log(f'    realized-empty charged rows at n=3: {empty_rows} '
            f'(recorded scope: every mu>=2 continuation has e=1, l>=2 '
            f'-> pure T1 charging; matches the prior X1A seal scope)')
        nviol = sum(pr['violations'] for pr in per_row.values())
        check(f'KE13-P1 p={p}: 0 per-row accounting violations under '
              f'reading A (each realized node increment == its row\'s '
              f'Cor 4.19 value)', nviol == 0 and walk['parity_dev'] == 0,
              f'violations {nviol}; parity deviations {walk["parity_dev"]}; '
              f'realized T1 tuples {per_row["T1"]["tuples"]} '
              f'({per_row["T1"]["members"]} members)')
        viol_rows = [r for r in ROWS if per_row[r]['violations']]
        check(f'KE13-P2 p={p}: per-row violation tally (a violating row '
              f'names KE8\'s failing transport row)', not viol_rows,
              f'violating rows {viol_rows or "NONE"}; per-row '
              f'{ {r: per_row[r]["violations"] for r in ROWS} }')
        out['boxes'][f'p{p}'] = dict(
            p=p, N=N, p3_ok=True,
            viol_A=walk['viol_A'][0], skipped_A=walk['skipped_A'],
            rows={f'{row}(e={e},l={ell},h={hn})':
                  dict(members=nmem, observed=observed, acct=acct,
                       ok=bool(ok))
                  for (row, e, ell, hn), (nmem, observed, acct, ok)
                  in sorted(walk['rows_tally'].items())},
            t5_members=walk['t5_members'],
            per_row_viol={r: per_row[r]['violations'] for r in ROWS},
            empty_rows=empty_rows, secs=walk['secs'])

    npass = sum(1 for v in verdicts if v['ok'])
    nfind = len(verdicts) - npass
    log(f'\n===== KE13 VERDICT: {npass}/{len(verdicts)} PASS, {nfind} '
        f'FINDING; total {round(time.time() - T0, 1)}s =====')
    log('GATE CONSEQUENCE: '
        + ('row-check seal CLEAN — the KE8 prover is UNBLOCKED (reading A; '
           'the realized charged population at n=3 is the T1 row).'
           if nfind == 0 else
           'FINDING on record — the named row feeds KE8\'s per-row '
           'obstruction fallback; adjudicate BEFORE the KE8 prover runs.'))
    out['verdicts'] = verdicts
    os.makedirs(os.path.dirname(OUTJSON), exist_ok=True)
    with open(OUTJSON, 'w') as fh:
        json.dump(out, fh, indent=1, default=str)
    append_results()
    log(f'json -> {OUTJSON}; summary appended -> {RESULTS_TXT}')
    return 1 if nfind else 0


if __name__ == '__main__':
    sys.exit(main())
