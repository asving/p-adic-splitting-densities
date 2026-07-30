#!/usr/bin/env python3
"""ke4_tails_stress_probe.py — UNIT KE4 (bridge campaign, area BP4, cluster
BP4-c1, GATE unit) — the tails candidate-stress probe, TWO-PHASE.

[CM-first for KE5, TWO-PHASE per blueprint REV 2 (F10): X2TailsP is
EXISTENTIAL in the pair (C_T, c_T) (XConsts data), so NO finite probe can
refute it, and a probe run before the prover knows no candidate constants.
The honest gate shape is candidate-stress + divergence detection.]

STATEMENT (blueprint BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE4 + §3.E (E-iv) +
risk R8):
  PHASE 1 (BEFORE the KE5 prover; this spec's primary content): exhaustive
  tall-event masses at n = 3, p in {2, 3}, h* <= 8 — frac(TallEvent h*) =
  the census mass of branches whose FIRST height->= h* read occurs; fit the
  empirical decay exponent; COMPUTE the explicit candidate pair (C_T, c_T)
  the KE5 sketch implies (the D4R.2 pool-bound composition mu(P-hat) <=
  M(P-hat)·p^{W(P-hat)−A(P-hat)}, A growing with the tall read's height,
  summed over prefixes with the per-depth species-menu branching factor)
  and STRESS it in-box; track mass·p^{c·h*} growth in h* as the divergence
  detector — per-depth branching outrunning per-height decay is the known
  divergence risk (R8).
  PHASE 2 (AFTER KE5 drafts its actual constants, BEFORE acceptance):
  re-run the stress against the prover's actual (C_T, c_T).  KE5's
  acceptance is GATED on phase 2.  Phase 2 is BLOCKED until the KE5 draft
  exists (a within-unit sequencing stub, not a unit blockage).

DEPS: verification/ census infra (the x_n3_probes X2B per-letter teeth
machinery already prices per-letter height tails mu <= p^{−(h−h0(L))};
reuse recorded).  Phase 2 additionally: the KE5 draft's constants.

SEALED PREDICTIONS (Q6 discipline — sealed 2026-07-30, BEFORE any run):
  P1: frac(TallEvent h*) decays geometrically in h* at both p — the fitted
      empirical exponent c_T^emp is > 0 (the X2B teeth h0(L)-anchored decay
      suggests c_T ~ 1 per letter).
  P2 (candidate-stress): the sketch-implied explicit pair passes in-box:
      frac(TallEvent h*) <= C_T·p^{−c_T·h*} for every h* <= 8; the prior
      X-n3 sealed reference numbers C_T(3) = 53, c_T(3) = 1 are stressed
      alongside as the reference candidates.  A candidate failure kills
      THAT candidate (the composition's constants recomputed and the gap
      recorded), never the existential.
  P3 (divergence detector): mass·p^{c_T·h*} stays bounded (no growing
      trend in h*) at the candidate c_T.  A growing trend is THE divergence
      FINDING (R8) — KE5 rerouted toward its divergent-series obstruction
      record (the union over prefixes with the species-menu factor is the
      exact suspect, named in the record).
  P4 (phase 2 — sealed CONDITIONALLY, constants unknown at spec time): the
      prover's actual (C_T, c_T) passes the same in-box stress; failure =
      acceptance blocked, constants returned to the prover with the
      violating (p, h*) rows.

OUTPUT (run phase): PASS/FINDING rows appended to
probe_results_2026-07-30.txt; JSON to results/ke4_tails_stress.json; exit
0 = phase-1 seals clean, 1 = FINDING, and the phase flag recorded per run.

STATUS: RUN PHASE (2026-07-30) — body implemented AFTER the seal above
(predictions P1–P4 verbatim untouched).  Phase 1 executes on invocation;
phase 2 is implemented (`--phase2 CT cT` re-runs the stress from the cached
census masses).  PHASE 2 RAN 2026-07-30 (P4 discharged, 2/2 PASS, exit 0):
the KE5 prover's actual pair (C_T, c_T) = (1200488, 1) — the D4R.2
pool-bound composition's constants made n-only by taking the max of the two
per-box phase-1 sketch values (p=2: 3.74e5; p=3: 1.20e6), c_T = 1 — passes
the in-box stress at both p with no violations and no growing detector
trend; KE5's `x2Tails_of_route` (MovesX/KE5.lean) is PROVED and its
acceptance gate is thereby CLEAR.

RUN-PHASE READING NOTES (recorded, not sealed):
  * TallEvent transcription (MovesX/Defs.lean:307 `TallEvent`): f is tall at
    h* iff SOME node of SOME branch history has node height >= h*.  In the
    n = 3 walker every window read's (side x factor) rows are exactly the
    branch-tree nodes, so max-height-over-all-rows >= h* IS the event; the
    first-read framing of the blueprint decomposes the same set.
  * Census exactness: node heights are exact for type-stable, uncapped
    reads; the walker tallies frac_low(h*) from certified-exact heights
    (a LOWER bound on frac) and reports the box-censored margin (f with a
    capped/unstable read, an undecided walk, or an engine fault) once per
    box.  Max box-exact node height is N−1 (v_p < N), so rows h* > N−1
    have frac_low = 0 with the margin as the honest error bar.
  * Depth convention: probe depth d = number of CONTINUING nodes walked
    (Lean dTotal); KE5's realizedHists counts full history length (off by
    the terminal node) — seam note for the KE5 prover, not a gate issue.
  * Sketch-composition caveat: multiplying per-node teeth prices along a
    chain is exactly the D4R.2 pool-bound composition KE5 must PROVE
    (read_price x series_ok); the probe stresses its numeric consequence.
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
OUTJSON = os.path.join(HERE, 'results', 'ke4_tails_stress.json')
OUTTXT = '/tmp/ke4_tails_stress.out'

sys.path.insert(0, HERE)
from case_mn3_gate import read_data_one, fp_factor  # gate-validated 2026-07

PRIMES = [2, 3]
HSTAR_MAX = 8
REFERENCE_CANDIDATES = {'C_T3': 53, 'c_T3': 1}   # prior X-n3 sealed numbers
CONFIGS = {2: 8, 3: 5}                            # the X.5 box levels

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
# x_n3_probes.py (gate-passed 2026-07-29); used here as the walker
# faithfulness gate (KE4-V1): the adapted walker must reproduce them.
# =========================================================================
SIGS = ['111', '112', '13', '1121', '31']
S7 = {2: {8: [708608, 5038080, 4329472, 3951616, 2705408]},
      3: {5: [927288, 5196312, 4269024, 2726460, 1185354]}}
SIGMA_OF = {(((1, 1),) * 3): '111',
            tuple(sorted([(1, 1), (1, 2)])): '112',
            ((1, 3),): '13',
            tuple(sorted([(1, 1), (2, 1)])): '1121',
            ((3, 1),): '31'}


# =========================================================================
# The window reader — transcribed VERBATIM from x_n3_probes.py (importing
# that module would truncate its /tmp long log at module level; reuse is
# by transcription + the KE4-V1 end-to-end check instead).
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


def lname(k):
    return (f'{k[0]}[e{k[1]} l{k[2]} a{k[3]} fl{list(k[4])}|{list(k[5])} '
            f'lam{list(k[6])} sel{k[7]}]')


# =========================================================================
# PHASE-1 PIECE 1 — the tall-event census walker (adapted from the
# gate-passed x_n3_probes.run_box: same reader, same recentering, same
# grouping; tallies changed to the per-f max-node-height joint the tall
# event needs; validated end-to-end by KE4-V1 = the S7 sigma integers).
# =========================================================================
def tall_event_masses(p, hstar_max=HSTAR_MAX):
    """Exact census masses frac(TallEvent h*) for h* = 1..hstar_max at
    n = 3: the mass of f whose branch history contains a read of height
    >= h* (certified-exact heights => frac_low; censored margin separate).
    Also collects the sketch-composition ledger inputs (letters h0(L),
    per-depth realized-prefix counts, per-prefix branching)."""
    N = CONFIGS[p]
    t0 = time.time()
    M, K, v_tab, code_tab = vpd_tables(p, N)
    size = M ** 3
    idx = np.arange(size, dtype=np.int64)
    C0 = (idx % M).astype(np.int64)
    C1 = ((idx // M) % M).astype(np.int64)
    C2 = (idx // (M * M)).astype(np.int64)
    del idx

    tall_hist = {}          # hmax_known -> count (all f; hmax 0 = no h>=1 node)
    margin = 0              # censored mass (capped read / undec / fault)
    undec = 0
    sigma_ct = {s: 0 for s in SIGS}
    faults_all = {}
    witness = {}            # hmax -> (c2, c1, c0) original coefficients
    letter_minh = {}        # letterkey -> min realized height (h0(L), census)
    letter_maxh = {}
    realized = {}           # depth d -> set of full prefix keys
    children_sd = {}        # (d, pk) -> set of species-digit extension keys
    nrow_max = 0            # max #letter rows in one window read (read menu)

    def note_rows(group, reads):
        """Stable reads -> [(letterkey, h)] (the x_n3 letter_rows schema)."""
        out = []
        for dat in reads:
            (e, ell, a, flk, frk, resid, s0, hn, u1) = dat
            facs = fp_factor(resid, p)
            lam = tuple(sorted((len(f) - 1, m) for f, m in facs))
            for f, m in facs:
                g = len(f) - 1
                out.append(((group, e, ell, a, flk, frk, lam, (g, m)), hn))
        return out

    # stack entries: (mem, c0, c1, c2, W, hkey, hmu, is_root, primes_so_far,
    #                 hmax_known, censored, depth, prefix_key, group, codes)
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
                      (), 0, False, 0, (), 'R', codes))
    del order, sig_sorted, bounds, starts, ends
    realized[0] = {()}

    while stack:
        (mem, c0, c1, c2, W, hkey, hmu_t, is_root, primes0,
         hmax0, cens0, d, pk, group, codes) = stack.pop()
        n = len(mem)
        if not is_root:
            # D.10 frame checks (as in run_box): violations are FINDINGS.
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
        rows = note_rows(group, wr['reads'])
        nrow_max = max(nrow_max, len(rows))
        hmax1 = hmax0
        for lk, h in rows:
            letter_minh[lk] = min(letter_minh.get(lk, 99), h)
            letter_maxh[lk] = max(letter_maxh.get(lk, -1), h)
            if h >= 1:
                hmax1 = max(hmax1, h)
        cens1 = cens0 or (wr['n_unstable'] > 0) or (not wr['type_ok'])
        if not wr['type_ok']:
            undec += n
        if not wr['type_ok'] or not wr['cont']:
            # walk complete (or type-dead): final tallies
            if wr['type_ok']:
                sig = tuple(sorted(primes0 + wr['primes']))
                assert sum(e * g for e, g in sig) == 3, sig
                sigma_ct[SIGMA_OF[sig]] += n
            tall_hist[hmax1] = tall_hist.get(hmax1, 0) + n
            if cens1:
                margin += n
            if hmax1 not in witness:
                i = int(mem[0])
                witness[hmax1] = (int(C2[i]), int(C1[i]), int(C0[i]))
            continue
        assert len(wr['cont']) == 1, (wr['cont'], codes)
        hn, r, mu, hmu, e_, ell_ = wr['cont'][0]
        assert e_ == 1 and ell_ >= mu, (e_, ell_, mu)
        if not is_root and hn <= hkey:
            kf = f'Iaug-cont-stop hn={hn} hkey={hkey}'
            faults_all[kf] = faults_all.get(kf, 0) + n
            tall_hist[hmax1] = tall_hist.get(hmax1, 0) + n
            margin += n            # walk stopped: deeper reads unknown
            undec += n
            continue
        # the CONTINUING node: exact by type_ok-uniformity, counts as a node
        if hn >= 1:
            hmax1 = max(hmax1, hn)
        nodekey = (mu, ell_, hn, r)
        pk2 = pk + (nodekey,)
        realized.setdefault(d + 1, set()).add(pk2)
        children_sd.setdefault((d, pk), set()).add((mu, ell_, r))
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
                          False, primes1, hmax1, cens1, d + 1, pk2,
                          QGROUP[mu], codes2))

    box = size
    masses = {}
    for h in range(1, hstar_max + 1):
        masses[h] = Fraction(sum(c for hh, c in tall_hist.items() if hh >= h),
                             box)
    Rd = {d: len(s) for d, s in sorted(realized.items())}
    branch_sd = max((len(s) for s in children_sd.values()), default=0)
    # minimal integer menu with R(d) <= menu^d for all d >= 1 (KE5 menu_card)
    menu_min = 1
    for dd, cnt in Rd.items():
        if dd >= 1:
            while menu_min ** dd < cnt:
                menu_min += 1
    return dict(p=p, N=N, box=box, masses=masses, tall_hist=tall_hist,
                margin=Fraction(margin, box), undec=undec, sigma=sigma_ct,
                faults=faults_all, witness=witness,
                letter_minh=letter_minh, letter_maxh=letter_maxh,
                Rd=Rd, branch_sd=branch_sd, menu_min=menu_min,
                nrow_max=nrow_max, secs=round(time.time() - t0, 1))


# =========================================================================
# PHASE-1 PIECE 2 — the empirical decay-exponent fit (P1).
# =========================================================================
def fit_decay_exponent(masses, p):
    """Empirical decay exponent: per-step slopes log_p(m(h)/m(h+1)) over the
    positive-mass range; report min/mean (P1 verdict: c_T^emp > 0)."""
    import math
    pos = [h for h in sorted(masses) if masses[h] > 0]
    slopes = []
    for h in pos:
        if h + 1 in masses and masses[h + 1] > 0:
            slopes.append(math.log(masses[h] / masses[h + 1]) / math.log(p))
    if not slopes:
        return dict(slopes=[], cmin=None, cmean=None, pos_range=pos)
    return dict(slopes=[round(s, 4) for s in slopes],
                cmin=round(min(slopes), 4),
                cmean=round(sum(slopes) / len(slopes), 4), pos_range=pos)


# =========================================================================
# PHASE-1 PIECE 3 — the sketch-implied candidate pair (the D4R.2
# composition), computed from census-anchored ledger inputs.
# Composition (each factor named; finite by D.10 strict climb, summed to
# the convergent infinite series for an h*-uniform constant):
#   frac(TallEvent h*)
#     <= sum_{d>=0} [#realized (species,digit)-chains of depth d]
#                   x [height-summed chain price]  x [tall-read price]
#     <= sum_{d>=0} B^d x prod_{i=1..d} G_i x Lmenu·p^{h0r}·p^{-h*}
#   G_i := sum_{h >= i-1} p^{-max(0, h-h0c)}   (strict climb: h_i >= i-1;
#          per-node X2B tooth at the census-anchored continuing offset h0c)
#   => c_T := 1,  C_T := Lmenu·p^{h0r}·S,  S := sum_d B^d·prod G_i.
# Multiplicativity of the per-node teeth along a chain = the D4R.2
# pool-bound composition KE5 must prove (recorded caveat, header note).
# =========================================================================
def candidate_pair_from_sketch(p, walk):
    Lmenu = len(walk['letter_minh'])
    h0r = max(walk['letter_minh'].values())
    cont_h0 = [h0 for lk, h0 in walk['letter_minh'].items() if lk[7][1] >= 2]
    h0c = max(cont_h0) if cont_h0 else 0
    B = walk['branch_sd']
    ledger = [
        f'Lmenu = {Lmenu} census-realized letters (union-bound terms of the '
        f'tall read; catalogue caps it at 53)',
        f'h0r = {h0r} = max_L h0(L) (census-anchored tall-read tooth offset, '
        f'weaker-safe)',
        f'h0c = {h0c} = max h0 over continuing (sel m>=2) letters '
        f'(chain-node tooth offset)',
        f'B = {B} = max realized per-prefix (species,digit) branching '
        f'(the species-menu factor; heights priced separately in G_i)',
        f'strict climb (D.10): chain heights h_1 < h_2 < ... with h_i >= i-1 '
        f'=> depth before the first tall read <= h*+1; summed to the '
        f'convergent infinite series for an h*-uniform C_T',
    ]

    def G(i):
        lo = max(0, i - 1)
        if lo <= h0c:
            return Fraction(h0c - lo + 1) + Fraction(1, p - 1)
        return Fraction(1, p ** (lo - h0c)) * Fraction(p, p - 1)

    S = Fraction(0)
    term = Fraction(1)
    d = 0
    diverged = False
    while True:
        S += term
        d += 1
        term = term * B * G(d)
        if S > 0 and term / S < Fraction(1, 10 ** 18):
            break
        if d > 500:
            diverged = True      # cannot happen: prod G_i decays ~ p^{-d^2/2}
            break
    CT = Lmenu * Fraction(p ** h0r) * S
    ledger.append(f'S = sum_d B^d prod G_i = {float(S):.4f} (converged at '
                  f'depth {d}; diverged={diverged})')
    ledger.append(f'=> sketch pair at p={p}: C_T = Lmenu·p^h0r·S = '
                  f'{float(CT):.2f}, c_T = 1')
    return dict(CT=CT, cT=1, S=S, Lmenu=Lmenu, h0r=h0r, h0c=h0c, B=B,
                diverged=diverged, ledger=ledger)


# =========================================================================
# PHASE-1 PIECE 4 — candidate stress + divergence detector (P2 + P3).
# =========================================================================
def stress_candidates(masses, pairs, p, margin):
    """P2: frac_low(h*) <= C_T·p^{−c_T·h*} for each candidate pair at every
    h* <= HSTAR_MAX (violation = certified in-box failure of THAT pair);
    P3: divergence detector seq(h*) = frac_low·p^{c_T·h*} trend."""
    import math
    out = {}
    for name, (CT, cT) in pairs.items():
        viol = []
        margin_could_hide = []
        seq = []
        for h in sorted(masses):
            bnd = Fraction(CT) / Fraction(p ** (cT * h))   # exact comparison
            if masses[h] > bnd:
                viol.append((h, str(masses[h]), float(bnd)))
            if masses[h] + margin > bnd:
                margin_could_hide.append(h)
            seq.append(float(masses[h]) * p ** (cT * h))
        pos = [(h, v) for h, v in zip(sorted(masses), seq)
               if masses[h] > 0]
        growing = False
        trend_slope = None
        if len(pos) >= 2:
            xs = [h for h, _ in pos]
            ys = [math.log(v) / math.log(p) for _, v in pos]
            nn = len(xs)
            xm, ym = sum(xs) / nn, sum(ys) / nn
            den = sum((x - xm) ** 2 for x in xs)
            trend_slope = (sum((x - xm) * (y - ym)
                               for x, y in zip(xs, ys)) / den if den else 0.0)
            tail_up = (len(pos) >= 3 and pos[-1][1] > pos[-2][1] > pos[-3][1])
            growing = (trend_slope > 0.1) or (tail_up
                                              and pos[-1][1] > pos[0][1])
        out[name] = dict(CT=float(CT), cT=cT, violations=viol,
                         margin_could_hide=margin_could_hide,
                         detector_seq=[round(v, 6) for v in seq],
                         trend_slope=(round(trend_slope, 4)
                                      if trend_slope is not None else None),
                         growing_trend=growing)
    return out


# =========================================================================
# PHASE 2 — implemented, BLOCKED on the KE5 draft constants (sequencing
# stub).  `--phase2 CT cT` re-runs the stress from the cached phase-1
# census masses in results/ke4_tails_stress.json.
# =========================================================================
def phase2_stress(prover_CT, prover_cT):
    with open(OUTJSON) as fh:
        cached = json.load(fh)
    log(f'KE4 PHASE 2 — stressing the KE5 prover constants '
        f'(C_T={prover_CT}, c_T={prover_cT}) against cached phase-1 masses')
    any_viol = False
    for pk, row in cached['boxes'].items():
        p = row['p']
        masses = {int(h): Fraction(m) for h, m in row['masses'].items()}
        margin = Fraction(row['margin'])
        res = stress_candidates(masses,
                                {'prover': (Fraction(prover_CT), prover_cT)},
                                p, margin)['prover']
        ok = not res['violations']
        any_viol |= (not ok)
        check(f'KE4-P4 p={p}: prover pair (C_T={prover_CT}, c_T={prover_cT}) '
              f'in-box stress', ok,
              f'violations {res["violations"]}; margin-could-hide rows '
              f'{res["margin_could_hide"]}; detector growing='
              f'{res["growing_trend"]}')
    append_results('phase 2 (prover constants '
                   f'C_T={prover_CT}, c_T={prover_cT})')
    return 1 if any_viol else 0


def append_results(phase_desc):
    npass = sum(1 for v in verdicts if v['ok'])
    with open(RESULTS_TXT, 'a') as fh:
        fh.write('\n\n##### ke4_tails_stress_probe.py (UNIT KE4: tails '
                 'candidate-stress gate for KE5) #####\n')
        fh.write(f'run {time.strftime("%F %T")}; PHASE FLAG: {phase_desc}; '
                 f'spec BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE4 + §3.E '
                 f'(E-iv) + R8; long log {OUTTXT}\n')
        for v in verdicts:
            fh.write(f"[{'PASS' if v['ok'] else 'FINDING'}] {v['name']}  "
                     f"{v['detail']}\n")
        fh.write(f'KE4 VERDICT: {npass}/{len(verdicts)} PASS, '
                 f'{len(verdicts) - npass} FINDING\n')


# =========================================================================
# main — phase 1
# =========================================================================
def main():
    if len(sys.argv) == 4 and sys.argv[1] == '--phase2':
        return phase2_stress(Fraction(sys.argv[2]), Fraction(sys.argv[3]))
    log('KE4 TAILS CANDIDATE-STRESS PROBE — PHASE 1 (gate for KE5)')
    log(f'spec: BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE4 + §3.E (E-iv) + R8; '
        f'sealed predictions P1-P4 of 2026-07-30 (header); '
        f'started {time.strftime("%F %T")}')
    log('PHASE FLAG: phase 1 (pre-prover). Phase 2 BLOCKED: MovesX/KE5.lean '
        'is an E-phase sorry statement with NO drafted constants '
        '(within-unit sequencing stub).')
    out = {'phase': 1, 'boxes': {}}
    for p in PRIMES:
        N = CONFIGS[p]
        log(f'\n===== CUBIC BOX p={p}, level {N} (size {p ** (3 * N)}) =====')
        walk = tall_event_masses(p)
        log(f'  walk: {walk["secs"]}s; undec {walk["undec"]}; margin '
            f'{float(walk["margin"]):.6f}; letters {len(walk["letter_minh"])}')

        # V1: walker faithfulness — the S7 sigma integers (x_n3 gate values)
        want = S7[p][N]
        got = [walk['sigma'][s] for s in SIGS]
        wundec = p ** (3 * N) - sum(want)
        check(f'KE4-V1 p={p}: adapted walker reproduces the S7 decided '
              f'integers + undecided count (x_n3 gate values)',
              got == want and walk['undec'] == wundec,
              f'sigma {got} vs {want}; undec {walk["undec"]} vs {wundec}')
        # V2: engine faults
        check(f'KE4-V2 p={p}: engine faults (VERTEX/BOX/Iaug/partition) == 0',
              len(walk['faults']) == 0,
              str(dict(list(walk['faults'].items())[:3])))

        masses = walk['masses']
        log('  frac_low(TallEvent h*), h*=1..8: '
            + '; '.join(f'h*={h}: {float(m):.6g}'
                        for h, m in masses.items()))
        log(f'  tall witness f=(c2,c1,c0) per hmax: '
            f'{ {h: w for h, w in sorted(walk["witness"].items()) if h >= 1} }')
        log(f'  realized-prefix counts R(d): {walk["Rd"]}; menu_min '
            f'(min m with R(d)<=m^d) = {walk["menu_min"]}; per-prefix '
            f'(species,digit) branching B = {walk["branch_sd"]}; max rows '
            f'per read = {walk["nrow_max"]}')
        hexact = N - 1
        log(f'  censoring: max box-exact node height = N-1 = {hexact}; rows '
            f'h* > {hexact} have frac_low = 0 with margin '
            f'{float(walk["margin"]):.6f} as the error bar')

        # P1: geometric decay / positive fitted exponent
        fit = fit_decay_exponent(masses, p)
        check(f'KE4-P1 p={p}: fitted empirical decay exponent c_T^emp > 0 '
              f'(geometric decay of frac(TallEvent h*))',
              fit['cmin'] is not None and fit['cmin'] > 0,
              f'per-step slopes {fit["slopes"]} (min {fit["cmin"]}, mean '
              f'{fit["cmean"]}) over positive range h*={fit["pos_range"]}')

        # P2: candidate stress — sketch-implied pair + reference pair
        sk = candidate_pair_from_sketch(p, walk)
        for line in sk['ledger']:
            log(f'  LEDGER: {line}')
        check(f'KE4-R8a p={p}: the sketch composition series CONVERGES '
              f'(analytic divergence check on sum_d B^d prod G_i)',
              not sk['diverged'], f'S = {float(sk["S"]):.4f}')
        pairs = {'sketch': (sk['CT'], sk['cT']),
                 'reference_Xn3': (Fraction(REFERENCE_CANDIDATES['C_T3']),
                                   REFERENCE_CANDIDATES['c_T3'])}
        stress = stress_candidates(masses, pairs, p, walk['margin'])
        for name, res in stress.items():
            check(f'KE4-P2 p={p}: candidate {name} (C_T={res["CT"]:.4g}, '
                  f'c_T={res["cT"]}) passes in-box at every h* <= '
                  f'{HSTAR_MAX}', not res['violations'],
                  f'violations {res["violations"]}; margin-could-hide rows '
                  f'{res["margin_could_hide"]}')
        # P3: divergence detector at the candidate c_T = 1
        det = stress['reference_Xn3']
        check(f'KE4-P3 p={p}: divergence detector frac_low·p^(h*) bounded, '
              f'no growing trend (R8)', not det['growing_trend'],
              f'seq {det["detector_seq"]}; log_p trend slope '
              f'{det["trend_slope"]}')
        cmin_emp = max((Fraction(m) * p ** h for h, m in masses.items()),
                       default=Fraction(0))
        log(f'  empirical minimal C_T at c_T=1 (data-implied): '
            f'{float(cmin_emp):.4f}')

        out['boxes'][f'p{p}'] = dict(
            p=p, N=N, box=walk['box'],
            masses={h: str(m) for h, m in masses.items()},
            tall_hist={int(h): int(c) for h, c in walk['tall_hist'].items()},
            margin=str(walk['margin']), undec=walk['undec'],
            witness={int(h): w for h, w in walk['witness'].items()},
            letters_h0={lname(k): int(v)
                        for k, v in sorted(walk['letter_minh'].items(),
                                           key=lambda t: lname(t[0]))},
            Rd=walk['Rd'], menu_min=walk['menu_min'],
            branch_sd=walk['branch_sd'], fit=fit,
            sketch=dict(CT=str(sk['CT']), CT_float=float(sk['CT']),
                        cT=sk['cT'], S=float(sk['S']), Lmenu=sk['Lmenu'],
                        h0r=sk['h0r'], h0c=sk['h0c'], B=sk['B'],
                        ledger=sk['ledger']),
            stress={k: {kk: vv for kk, vv in v.items()}
                    for k, v in stress.items()},
            cmin_emp=str(cmin_emp), secs=walk['secs'])

    npass = sum(1 for v in verdicts if v['ok'])
    nfind = len(verdicts) - npass
    log(f'\n===== KE4 PHASE-1 VERDICT: {npass}/{len(verdicts)} PASS, '
        f'{nfind} FINDING; total {round(time.time() - T0, 1)}s =====')
    log('GATE CONSEQUENCE: '
        + ('phase-1 seals clean — KE5 prover UNBLOCKED with the recorded '
           'candidate constants; acceptance stays gated on phase 2.'
           if nfind == 0 else
           'FINDING on record — adjudicate per R8 (candidate recomputation '
           'vs divergence reroute) BEFORE the KE5 prover runs.'))
    out['verdicts'] = verdicts
    os.makedirs(os.path.dirname(OUTJSON), exist_ok=True)
    with open(OUTJSON, 'w') as fh:
        json.dump(out, fh, indent=1, default=str)
    append_results('phase 1 (pre-prover; phase 2 blocked on the KE5 draft)')
    log(f'json -> {OUTJSON}; summary appended -> {RESULTS_TXT}')
    return 1 if nfind else 0


if __name__ == '__main__':
    sys.exit(main())
