#!/usr/bin/env python3
"""ke12_undec_cover_probe.py — UNIT KE12 (bridge campaign, area BP4, cluster
BP4-c1, GATE unit) — the Undec-decomposition probe.

[CM-first gate for KE6 — NEW at blueprint REV 2 (F5); explicit dependency of
the KE6 prover, sequenced FIRST (KE12(gate) → KE6 → KE7).]

STATEMENT (blueprint BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE12 + §3.E (E-v)):
enumerate the members of Undec(N) at the census and check KE6's four-set
cover CLAUSE-BY-CLAUSE:

    Undec(N) ⊆ discZero ∪ nsFibers ∪ InfTree ∪ {thr + cap > N leaf branch}

A census member of Undec(N) outside the union REFUTES KE6's set
decomposition OUTRIGHT — clause 1 is a genuine ∀-statement, finitely
refutable: the strongest gate genre in this area.  (KE6's prover may also
need the ⚑ named XCtx law `DetectAtThr` — a complete branch tree with
thr + cap <= N is decided at N; a clean run here is the empirical warrant
for that law's shape, a finding pins the violating branch.)

Undec(N) SEMANTICS (anchored to the x_n3_probes reader, verbatim reuse): f
is decided at level N iff the level-N digit data pins the full factorization
type sigma(f) — every window read type-stable across cap-completions, every
mu >= 2 continuation pinned; (tau-hen) and regular mu = 1 factors certify at
the read itself (N_V = 1); confirm-read depth is NOT charged to Undec.

DEPS: verification/ census infra (x_n3_probes X3A/X3B machinery — the
Undec(N) enumerator already cross-checked against the S7-corrected integers,
65 values; reuse recorded).

SEALED PREDICTIONS (Q6 discipline — sealed 2026-07-30, BEFORE any run):
  P1 (THE cover check, sealed CLEAN): ZERO census members of Undec(N)
      outside the four-set union, at every probed level — p = 2, N = 1..8
      (the 2^24 cubic box) and p = 3, N = 1..5 (the 3^15 box), clause
      attribution recorded per member.  In-box proxies, recorded not
      patched: discZero readable at box precision; InfTree/nsFibers proxied
      by their observable in-box faces; members undecided at max box
      precision (DEEP) must land in a named clause on their observable
      prefix or be flagged DEEP-UNATTRIBUTED — any DEEP-UNATTRIBUTED
      member is reported as a deviation for adjudication, never silently
      binned.  A member provably outside the union is THE finding: KE6's
      decomposition refuted before its prover runs.
  P2 (consistency): the Undec(N) membership counts reproduce the
      S7-corrected integers already sealed in x_n3_probes X3B (65 values);
      a mismatch is an INFRASTRUCTURE finding (reader drift) — stop and
      adjudicate before reading P1.

OUTPUT (run phase): PASS/FINDING rows appended to
probe_results_2026-07-30.txt; JSON to results/ke12_undec_cover.json; exit
0 = P1+P2 clean, 1 = FINDING.

STATUS: RUN PHASE (2026-07-30) — body implemented AFTER the seal above
(predictions P1-P2 verbatim untouched).  Reader transcribed VERBATIM from
the gate-passed x_n3_probes.py per the KE4 precedent (importing that module
would truncate its /tmp long log at module level; reuse is by transcription
+ the P2 S7 end-to-end check instead).

RUN-PHASE READING NOTES (recorded, not sealed):
  * Member = a box point at MAX box precision (p=2: mod 2^8 coefficients,
    2^24 points; p=3: mod 3^5, 3^15 points).  Level-N Undec membership
    depends only on the level-N truncation (the level-N walker's undec
    flag); clause attribution is at max precision, where the in-box
    observables live.
  * Clause proxies (the recorded in-box faces):
      'thrcap'   — the member's truncation DECIDES at some in-box level
                   N' with N < N' <= Nmax: the leaf branch is walked
                   complete, ns-free (see below), and non-detection at N
                   with detection at N' is the observable face of
                   thr + cap > N (detectBranch's contrapositive shape —
                   exactly the KE6 sketch's fourth clause witness).
      'discZero' — DEEP member (undecided at Nmax) with disc f ≡ 0 mod
                   p^Nmax (vd censored at box precision): the observable
                   face of discZero; the true discZero ∪ InfTree ∪
                   nsFibers legs are box-indistinguishable inside this
                   face, so it is the face of the UNION's first three
                   clauses, reported under the discZero label.
      'nsFibers'/'InfTree' — observable in-box faces EMPTY at n = 3: the
                   cubic reader realizes no (tau-ns) track, and every
                   in-box walk terminates (D.10 strict climb + box
                   censoring), so no direct InfTree face exists; both are
                   subsumed in the DEEP faces above.  Recorded, not
                   patched.
      'DEEP-UNATTRIBUTED' — DEEP member with READABLE vd < Nmax: undecided
                   at full precision yet certifiably off the discZero
                   face — lands in no named clause on its observable
                   prefix; the deviation channel of P1.
      'OUTSIDE'  — a member positively certified outside all four clauses.
                   Under this reader Undec is DEFINED by non-detection, so
                   an in-box detection at level <= N would remove
                   membership: a positively-certified OUTSIDE member is
                   logically impossible for the fourth clause + this
                   reader; the empirical refutation channel of the cover
                   is therefore DEEP-UNATTRIBUTED (recorded reading).
  * Internal integrity checks run alongside P1/P2: per-member Undec
    antitonicity across levels (undec_antitone's census face; a violation
    is reader drift → INFRA finding) and the cylinder-count identity
    #members(N) = undec_N · p^{3(Nmax−N)}.
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
OUTJSON = os.path.join(HERE, 'results', 'ke12_undec_cover.json')
OUTTXT = '/tmp/ke12_undec_cover.out'

sys.path.insert(0, HERE)
from case_mn3_gate import read_data_one, fp_factor  # gate-validated 2026-07

LEVELS = {2: range(1, 9), 3: range(1, 6)}   # p -> probed N range
NMAX = {2: 8, 3: 5}

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
# S7 corrected integers + sigma dictionary — transcribed VERBATIM from
# x_n3_probes.py (gate-passed 2026-07-29); the P2 faithfulness gate.
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
# The Undec(N) enumerator — the x_n3 run_box(p, N, full=False) walk
# transcribed verbatim (same reader, same recentering, same grouping),
# returning the PER-MEMBER undec flag array the cover sweep needs
# (run_box only returns the count).  Faithfulness gated by P2 (S7, 65
# values) + the engine-fault check per level.
# =========================================================================
def undec_members(p, N):
    """Enumerate Undec(N) members in the census box at p (x_n3 X3A/X3B
    enumerator reuse, verbatim semantics; reuse recorded).  Returns
    dict with the level-N undec bool array (index = c0 + M·c1 + M²·c2),
    sigma decided counts, faults, secs."""
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

    # task = (members, c0, c1, c2, W, hkey, hmu, root?, primes_so_far,
    #         group, codes)
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
                      (), 'R', codes))
    del order, sig_sorted, bounds, starts, ends

    while stack:
        (mem, c0, c1, c2, W, hkey, hmu_t, is_root, primes0, group,
         codes) = stack.pop()
        n = len(mem)
        if not is_root:
            # D.10 frame checks (transcribed): violations are FINDINGS.
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
            continue
        assert len(wr['cont']) == 1, (wr['cont'], codes)
        hn, r, mu, hmu, e_, ell_ = wr['cont'][0]
        assert e_ == 1 and ell_ >= mu, (e_, ell_, mu)
        if not is_root and hn <= hkey:
            kf = f'Iaug-cont-stop hn={hn} hkey={hkey}'
            faults_all[kf] = faults_all.get(kf, 0) + n
            undec[mem] = True
            continue
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
                          False, primes1, QGROUP[mu], codes2))
    return dict(p=p, N=N, box=size, undec=undec, sigma=sigma_ct,
                faults=faults_all, secs=round(time.time() - t0, 1))


def vd_censored(p, N):
    """v_p(disc) over the level-N box, censored at N (vd = N means
    disc ≡ 0 mod p^N) — the run_box full-mode disc read, transcribed."""
    M = p ** N
    size = M ** 3
    idx = np.arange(size, dtype=np.int64)
    C0 = (idx % M).astype(np.int64)
    C1 = ((idx // M) % M).astype(np.int64)
    C2 = (idx // (M * M)).astype(np.int64)
    del idx
    d = (18 * C2 * C1 * C0 - 4 * C2 ** 3 * C0 + (C2 * C1) ** 2
         - 4 * C1 ** 3 - 27 * C0 ** 2) % M
    del C0, C1, C2
    vd = np.zeros(size, np.int16)
    for k in range(1, N + 1):
        vd[d % (p ** k) == 0] = k
    return vd


# =========================================================================
# clause attribution + the cover sweep (P1)
# =========================================================================
def clause_attribution(declev, vd, N, Nmax):
    """Attribute the full-precision members of Undec(N) to the first
    applicable clause (vectorized; the per-f semantics of the E-phase
    skeleton, applied to the whole box at once): 'thrcap' (decided in-box
    at N' > N — the fourth-clause observable face) | 'discZero' (DEEP with
    vd censored at Nmax — the first-three-clauses face) | 'nsFibers' /
    'InfTree' (observable faces EMPTY at n = 3; recorded) |
    'DEEP-UNATTRIBUTED' (DEEP with readable vd < Nmax; deviation) |
    'OUTSIDE' (impossible for this reader — see header; tallied 0 by
    construction and recorded as such).  Returns boolean masks."""
    inU = declev > N
    thrcap = inU & (declev <= Nmax)
    deep = inU & (declev > Nmax)
    disc_face = deep & (vd >= Nmax)
    deep_un = deep & (vd < Nmax)
    return dict(inU=inU, thrcap=thrcap, deep=deep,
                discZero=disc_face, deep_un=deep_un)


def cover_sweep(p, walks):
    """P1: full sweep over LEVELS[p]; witness list of OUTSIDE members
    (empty = PASS) + the DEEP-UNATTRIBUTED deviation list + per-clause
    tallies.  Also the per-member antitonicity + cylinder-count integrity
    checks (INFRA)."""
    Nmax = NMAX[p]
    Mx = p ** Nmax
    size = Mx ** 3
    idx = np.arange(size, dtype=np.int64)
    C0 = (idx % Mx).astype(np.int64)
    C1 = ((idx // Mx) % Mx).astype(np.int64)
    C2 = (idx // (Mx * Mx)).astype(np.int64)
    del idx

    # dec_level: min in-box level at which the member's truncation decides
    # (127 = DEEP, undecided at every probed level incl. Nmax).
    declev = np.full(size, 127, np.int16)
    for N in sorted(LEVELS[p], reverse=True):
        MN = p ** N
        idxN = (C0 % MN) + MN * (C1 % MN) + MN * MN * (C2 % MN)
        declev[~walks[N]['undec'][idxN]] = N
        del idxN

    # per-member antitonicity (undec_antitone's census face): decided at N
    # must stay decided at N+1; checked at level-(N+1) resolution.
    anti_viol = 0
    for N in sorted(LEVELS[p])[:-1]:
        MN, MN1 = p ** N, p ** (N + 1)
        sz1 = MN1 ** 3
        i1 = np.arange(sz1, dtype=np.int64)
        c0 = (i1 % MN1)
        c1 = ((i1 // MN1) % MN1)
        c2 = (i1 // (MN1 * MN1))
        iN = (c0 % MN) + MN * (c1 % MN) + MN * MN * (c2 % MN)
        anti_viol += int(((~walks[N]['undec'][iN])
                          & walks[N + 1]['undec']).sum())
        del i1, c0, c1, c2, iN

    vd = vd_censored(p, Nmax)
    per_level = {}
    outside_total = 0
    deep_un_total = 0
    cyl_ok = True
    deep_un_wit = []
    for N in sorted(LEVELS[p]):
        att = clause_attribution(declev, vd, N, Nmax)
        n_mem = int(att['inU'].sum())
        expect = int(walks[N]['undec'].sum()) * p ** (3 * (Nmax - N))
        cyl_ok &= (n_mem == expect)
        row = dict(members=n_mem,
                   thrcap=int(att['thrcap'].sum()),
                   discZero_face=int(att['discZero'].sum()),
                   nsFibers_face=0, InfTree_face=0,        # empty at n=3
                   deep_unattributed=int(att['deep_un'].sum()),
                   outside=0)
        # witnesses: first few DEEP-UNATTRIBUTED members (deviation channel)
        if row['deep_unattributed'] and len(deep_un_wit) < 5:
            ws = np.flatnonzero(att['deep_un'])[:5]
            for w in ws:
                deep_un_wit.append((N, int(C2[w]), int(C1[w]), int(C0[w]),
                                    int(vd[w]), int(declev[w])))
        outside_total += row['outside']
        deep_un_total += row['deep_unattributed']
        per_level[N] = row
        log(f"  p={p} N={N}: members {row['members']} = thrcap "
            f"{row['thrcap']} + discZero-face {row['discZero_face']} + "
            f"deep-unattributed {row['deep_unattributed']} "
            f"(outside {row['outside']}; cylinder-count "
            f"{'ok' if n_mem == expect else 'MISMATCH ' + str(expect)})")
    return dict(per_level=per_level, outside=outside_total,
                deep_un=deep_un_total, deep_un_wit=deep_un_wit,
                anti_viol=anti_viol, cyl_ok=cyl_ok)


def s7_crosscheck(p, walks):
    """P2: Undec counts + per-sigma decided vs the S7-corrected integers
    (65 sigma values over both boxes, as in x_n3_probes X3B)."""
    ok, detail = True, []
    for N in sorted(LEVELS[p]):
        want = S7[p][N]
        got = [walks[N]['sigma'][s] for s in SIGS]
        wundec = p ** (3 * N) - sum(want)
        gundec = int(walks[N]['undec'].sum())
        if got != want or gundec != wundec:
            ok = False
            detail.append((N, got, want, gundec, wundec))
    return ok, (detail[:2] if detail else 'exact')


def append_results():
    npass = sum(1 for v in verdicts if v['ok'])
    with open(RESULTS_TXT, 'a') as fh:
        fh.write('\n\n##### ke12_undec_cover_probe.py (UNIT KE12: '
                 'Undec-decomposition gate for KE6) #####\n')
        fh.write(f'run {time.strftime("%F %T")}; spec '
                 f'BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE12 + §3.E (E-v); '
                 f'sealed P1-P2 of 2026-07-30 in force; long log {OUTTXT}\n')
        for v in verdicts:
            fh.write(f"[{'PASS' if v['ok'] else 'FINDING'}] {v['name']}  "
                     f"{v['detail']}\n")
        fh.write(f'KE12 VERDICT: {npass}/{len(verdicts)} PASS, '
                 f'{len(verdicts) - npass} FINDING\n')


def main():
    log('KE12 UNDEC-DECOMPOSITION PROBE (gate for KE6)')
    log(f'spec: BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE12 + §3.E (E-v); '
        f'sealed predictions P1-P2 of 2026-07-30 (header); '
        f'started {time.strftime("%F %T")}')
    out = {'boxes': {}}
    for p in sorted(LEVELS):
        log(f'\n===== CUBIC BOX p={p}, levels N=1..{NMAX[p]} '
            f'(size {p ** (3 * NMAX[p])}) =====')
        walks = {}
        for N in LEVELS[p]:
            walks[N] = undec_members(p, N)
            log(f'  undec_members(p={p}, N={N}): box {walks[N]["box"]}, '
                f'undec {int(walks[N]["undec"].sum())}, '
                f'{walks[N]["secs"]}s')
        # P2 FIRST (per the seal: infrastructure gate before reading P1)
        ok2, det2 = s7_crosscheck(p, walks)
        check(f'KE12-P2 p={p}: Undec(N) counts + per-sigma decided '
              f'reproduce the S7 integers, N=1..{NMAX[p]}', ok2, det2)
        faults = {}
        for N in LEVELS[p]:
            faults.update(walks[N]['faults'])
        check(f'KE12-V1 p={p}: engine faults (VERTEX/BOX/Iaug/partition) '
              f'== 0 across all levels', len(faults) == 0,
              str(dict(list(faults.items())[:3])))
        if not ok2:
            log('  P2 MISMATCH — infrastructure finding; P1 NOT read at '
                'this p (per the seal: stop and adjudicate).')
            out['boxes'][f'p{p}'] = dict(p=p, p2_ok=False)
            continue
        sweep = cover_sweep(p, walks)
        check(f'KE12-V2 p={p}: per-member Undec antitonicity across levels '
              f'(undec_antitone census face)', sweep['anti_viol'] == 0,
              f'violations {sweep["anti_viol"]}')
        check(f'KE12-V3 p={p}: cylinder-count identity #members(N) = '
              f'undec_N · p^(3(Nmax−N))', sweep['cyl_ok'], '')
        check(f'KE12-P1 p={p}: ZERO Undec(N) members outside the four-set '
              f'union at every probed level (cover check)',
              sweep['outside'] == 0,
              f'outside {sweep["outside"]}; per-level '
              f'{ {N: r["members"] for N, r in sweep["per_level"].items()} }')
        check(f'KE12-P1d p={p}: DEEP-UNATTRIBUTED deviation channel EMPTY '
              f'(DEEP members all land on the discZero face)',
              sweep['deep_un'] == 0,
              f'deviations {sweep["deep_un"]}'
              + (f'; witnesses (N,c2,c1,c0,vd,declev) '
                 f'{sweep["deep_un_wit"]}' if sweep['deep_un'] else
                 '; every DEEP member has vd >= Nmax (disc ≡ 0 at box '
                 'precision)'))
        out['boxes'][f'p{p}'] = dict(
            p=p, Nmax=NMAX[p], p2_ok=True,
            per_level={int(N): r for N, r in sweep['per_level'].items()},
            anti_viol=sweep['anti_viol'], outside=sweep['outside'],
            deep_unattributed=sweep['deep_un'],
            deep_un_witnesses=sweep['deep_un_wit'],
            undec_counts={int(N): int(walks[N]['undec'].sum())
                          for N in LEVELS[p]},
            secs={int(N): walks[N]['secs'] for N in LEVELS[p]})
        del walks

    npass = sum(1 for v in verdicts if v['ok'])
    nfind = len(verdicts) - npass
    log(f'\n===== KE12 VERDICT: {npass}/{len(verdicts)} PASS, {nfind} '
        f'FINDING; total {round(time.time() - T0, 1)}s =====')
    log('GATE CONSEQUENCE: '
        + ('cover seal CLEAN — the KE6 prover is UNBLOCKED.'
           if nfind == 0 else
           'FINDING/deviation on record — adjudicate BEFORE the KE6 '
           'prover runs (a member outside the union refutes the '
           'decomposition; a DEEP-UNATTRIBUTED member is a deviation '
           'for adjudication).'))
    out['verdicts'] = verdicts
    os.makedirs(os.path.dirname(OUTJSON), exist_ok=True)
    with open(OUTJSON, 'w') as fh:
        json.dump(out, fh, indent=1, default=str)
    append_results()
    log(f'json -> {OUTJSON}; summary appended -> {RESULTS_TXT}')
    return 1 if nfind else 0


if __name__ == '__main__':
    sys.exit(main())
