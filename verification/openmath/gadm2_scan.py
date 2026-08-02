#!/usr/bin/env python3
"""G-ADM-2 — the realized-strata ATTAINMENT SCAN (the (ADM) track-A/B router).

UNIT: synthesis-6 queue #4 (docs/SYNTHESIS_PASS6_2026-08-08.md F4-(ADM) +
queue line 4); gate spec = lean/blueprints/HDISCHARGE_H3.md section 1.3
"Numerics gates" (G-ADM-2) as instrumented by the ADM-U5 spec in
verification/h3_classd_scan.py (spec's runner name gadm2_attainment_run.py;
this chartered file gadm2_scan.py IS that runner).  The gate has NEVER run
before this file (pass-6 F4 finding; ADM_U7_TRACKA_ATTEMPT.md checked
2026-08-01: no runner, no jsonl, no disposition).

ROLE (Codex pass-1 finding 7, ACCEPTED): falsifier-ROUTER, not adjudicator.
A realized PARTIAL slot off the boundary kills track A (fires ADM-U6a /
track B); an all-FULL or boundary-only profile only SUPPORTS track A — the
proof burden stays with ADM-U7's hostile-passed argument.  A no-hit is
never cited as proof.

ROUTER SEMANTICS — REPAIRED per ADM_U7_TRACKA_ATTEMPT.md section 6 (adopted
here; the un-repaired spec predicate "PARTIAL at any slot = track A DEAD"
would misroute): each row logs is_right_end := (slot == mu) (the harness
fiber chain provably ends at the junction slot mu — n2_online_slots
enforces it); track B fires ONLY on a partial row with is_right_end =
False.  A right-end-only partial profile CONFIRMS the ADM-U7 dichotomy
(NON-END clearance off the end + the k_s carve-out): verdict
MIXED-WITH-BOUNDARY.  Any non-right-end partial row additionally REFUTES
Theorem NON-END (unconditional, ADM_U7 section 3) — theorem-grade
falsifier, doubling as a harness-integrity gate.

QUANTITY (spec verbatim): per fiber and per on-line slot k of the fiber's
floor chain, A_k = attained nonzero floor-height reads, n_att = #A_k,
q = p^g; FULL <=> n_att = q-1; PARTIAL <=> 0 < n_att < q-1; n_att = 0 =
anomaly_empty (informational); subgroup_ok = A_k + {0} closed under
componentwise F_p addition (the O-9 rev4/5 section 5.1 image-subgroup
shape; a False is a SHAPE anomaly, never routes).

COVERAGE (spec): the harness's 10-config battery (n <= 4, p in {2,3,5},
M <= 6, full + restricted) PLUS the three n = 5 restricted configs under
the p^(sum(M-m_i)) <= 10^7 box budget:
  (2,5,6,(4,3,2,2,1)) [2^18], (3,5,5,(3,3,2,2,1)) [3^14],
  (5,5,3,(2,2,1,1,1)) [5^8].
Determinacy: the harness cap IS the N-cap (only beta <= e*M - 1 slots are
read; CAP slots never enter the floor chain).  Restricted-mode soundness
rides the harness's own pooling note (delta_ceils guard inside
run_n2_config).

================================================================================
PREREGISTERED PREDICTIONS (sealed in this header BEFORE the first run;
committed pre-run.  Derivations: the junction rho-pin (O-9 (FRESH)(c),
clause (c)) + NON-END/W-CAP (ADM_U7_TRACKA_ATTEMPT sections 2-3) + the
section-5.1 image law.  Prior-battery baselines: verification/openmath/
logs/o9_census_h2n2_20260801_114313.log — chain_anom = 0 and junc_anom = 0
on all 10 battery configs; the n = 5 configs are unprobed extrapolation.)

  P1 (THE ROUTER PREDICTION, load-bearing): ZERO partial rows with
      is_right_end = False, battery-wide.  Falsifier force of a hit: track
      A DEAD (ADM-U6a fires with the row as its worked gate) AND NON-END
      refuted (stop-the-line: by ADM_U7 section 3 that needs O-9's pinned
      (P1)/(P3) or the datum reader broken).
  P2: partial rows DO occur, and the partial set is EXACTLY
      {rows with is_right_end = True and q > 2}: every chain-ok fiber's
      junction read is rho-pinned to ONE nonzero value (n_att = 1 at mu,
      from junc_anom = 0), so at mu: PARTIAL <=> q > 2, FULL <=> q = 2.
      Expected sources: all p = 3 and p = 5 fibers (g = 1, q = p) and any
      g = 2 fibers (q = p^2 > 2 always).
  P3: EVERY non-right-end on-line slot is FULL (n_att = q - 1) — NON-END
      clearance + the free-box structure (prior N2ii = 0 violations).
  P4: subgroup_ok = False EXACTLY on right-end rows with p >= 3 (the pin
      set {0, v} is F_p-closed iff p = 2); True on every other row (at
      non-end rows the image is all of F_q by P3; at p = 2 right ends
      {0, v} is closed).  All False rows are pin-explained SHAPE anomalies;
      none route.
  P5: anomaly_empty = 0 rows battery-wide (junc_anom = 0 baseline: no
      vanishing pinned reads).
  P6: chain anomalies = 0 on the 10 battery configs (pinned baseline);
      extrapolated 0 on the three n = 5 configs (unpinned).
  P7 (VERDICT PREDICTION): right-end-only partial profile ->
      MIXED-WITH-BOUNDARY: no track-B fire; track A stays live in its
      repaired (ADM-REAL') form; the ADM-U7 sections 4-5 dichotomy is
      CONFIRMED at scan scope; next (ADM) unit = the ADM-U7 hostile pass
      + the O-9 rev-6 re-scope (sign-off gated), NOT ADM-U6a.
================================================================================

OUTPUT.  One JSON line per (config, fiber, on-line slot) to
verification/logs/gadm2_attainment_<UTCstamp>.jsonl (spec H3 schema + the
is_right_end column); disposition aggregate to
verification/logs/GADM2_DISPOSITION.md (spec H4); stdout mirrors the
tallies.  Exit codes: 0 = all predictions hold; 2 = TRACK-B FIRE (P1
broken — also a NON-END integrity event); 1 = any other prediction drift.

Run:  python3 gadm2_scan.py            (full battery, ~15-45 min)
      python3 gadm2_scan.py smoke      (first config only; NOT the gate)
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)                       # harness + its o1thr deps
sys.path.insert(0, os.path.dirname(HERE))      # verification/ for the hooks
from o9_order2_census_check import run_n2_config, n2_online_slots  # noqa: E402
from h3_classd_scan import attainment_profile, gadm2_emit          # noqa: E402

# The spec coverage: the harness's own 10-config battery + the three n = 5
# restricted configs (box budgets 2^18, 3^14, 5^8 — all <= 10^7).
CONFIGS = [
    (2, 3, 5, None), (3, 3, 5, None),
    (2, 4, 4, None), (3, 4, 4, None),
    (2, 4, 3, None), (3, 4, 3, None), (5, 4, 3, None),
    (5, 3, 5, (3, 2, 1)),
    (2, 4, 6, (4, 3, 2, 1)), (3, 4, 6, (4, 3, 2, 1)),
    (2, 5, 6, (4, 3, 2, 2, 1)),
    (3, 5, 5, (3, 3, 2, 2, 1)),
    (5, 5, 3, (2, 2, 1, 1, 1)),
]


def main():
    smoke = 'smoke' in sys.argv[1:]
    cfgs = CONFIGS[:1] if smoke else CONFIGS
    stamp = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
    logdir = os.path.join(os.path.dirname(HERE), 'logs')
    os.makedirs(logdir, exist_ok=True)
    jsonl = os.path.join(logdir, 'gadm2_attainment_%s%s.jsonl'
                         % (stamp, '_smoke' if smoke else ''))
    tal = dict(fibers=0, chain_anom=0, rows=0, full=0,
               partial_end=0, partial_offend=0, empty=0,
               sub_false_end_podd=0, sub_false_other=0,
               slots_total=0, slots_capped=0)
    offenders, partial_end_rows = [], []
    p2_viol, p3_viol, p4_viol = [], [], []
    for cfg in cfgs:
        p, n, M, mins = cfg
        t0 = time.time()
        fibers = run_n2_config(p, n, M, list(mins) if mins else None)
        c = dict(fibers=0, chain=0, rows=0, full=0, pend=0, poff=0, empty=0)
        for (pkey, rkey), fib in sorted(fibers.items(), key=lambda kv: str(kv[0])):
            _pk, _s_idx, g, mu = fib['shape']
            e, h = fib['ehg']
            tal['fibers'] += 1
            c['fibers'] += 1
            tal['slots_total'] += len(fib['floors'])
            tal['slots_capped'] += sum(1 for f in fib['floors'] if f is None)
            online, ok = n2_online_slots(fib['floors'], e, h, g, mu)
            if not ok:
                tal['chain_anom'] += 1
                c['chain'] += 1
                continue
            rows = attainment_profile(fib, p, online)
            for row in rows:
                row['is_right_end'] = (row['slot'] == mu)
                tal['rows'] += 1
                c['rows'] += 1
                q = row['q']
                if row['full']:
                    tal['full'] += 1
                    c['full'] += 1
                if row['anomaly_empty']:
                    tal['empty'] += 1
                    c['empty'] += 1
                if row['partial']:
                    if row['is_right_end']:
                        tal['partial_end'] += 1
                        c['pend'] += 1
                        partial_end_rows.append((cfg, pkey, rkey, row))
                    else:
                        tal['partial_offend'] += 1
                        c['poff'] += 1
                        offenders.append((cfg, pkey, rkey, row))
                # P2: partial <=> (right end and q > 2); at mu n_att = 1
                pred_partial = row['is_right_end'] and q > 2
                if row['partial'] != pred_partial or \
                        (row['is_right_end'] and row['n_att'] != 1):
                    p2_viol.append((cfg, pkey, rkey, row))
                # P3: non-end rows FULL
                if not row['is_right_end'] and not row['full']:
                    p3_viol.append((cfg, pkey, rkey, row))
                # P4: subgroup_ok False <=> (right end and p >= 3)
                pred_subfalse = row['is_right_end'] and p >= 3
                if row['subgroup_ok'] == pred_subfalse:
                    p4_viol.append((cfg, pkey, rkey, row))
                if not row['subgroup_ok']:
                    key = ('sub_false_end_podd'
                           if row['is_right_end'] and p >= 3
                           else 'sub_false_other')
                    tal[key] += 1
            gadm2_emit(rows, jsonl, (p, n, M, mins), pkey, rkey)
        print("config p=%d n=%d M=%d %s: fibers=%d chain_anom=%d rows=%d "
              "full=%d partial@end=%d partial@OFFEND=%d empty=%d  [%.1fs]"
              % (p, n, M, 'restr' + str(mins) if mins else 'full',
                 c['fibers'], c['chain'], c['rows'], c['full'], c['pend'],
                 c['poff'], c['empty'], time.time() - t0), flush=True)

    # ------------- verdict (repaired router semantics, ADM-U7 section 6) --
    if tal['partial_offend'] > 0:
        verdict = 'PARTIAL-SLOT HIT (off the right end): TRACK A DEAD; ' \
                  'ADM-U6a fires; NON-END INTEGRITY EVENT'
    elif tal['partial_end'] > 0:
        verdict = 'RIGHT-END-ONLY PARTIAL (mixed-with-boundary): no ' \
                  'track-B fire; track A live as (ADM-REAL\'); ADM-U7 ' \
                  'dichotomy CONFIRMED at scan scope'
    else:
        verdict = 'ALL-FULL: track A SUPPORTED (only); K7 shape unrealized ' \
                  'in scan scope'
    preds = {
        'P1 (router: no off-end partial)': tal['partial_offend'] == 0,
        'P2 (partial <=> right-end & q>2; pin n_att=1)': not p2_viol,
        'P3 (non-end rows all FULL)': not p3_viol,
        'P4 (subgroup_ok False <=> right-end & p>=3)': not p4_viol,
        'P5 (no empty-attainment rows)': tal['empty'] == 0,
        'P6 (no chain anomalies)': tal['chain_anom'] == 0,
        'P7 (verdict = mixed-with-boundary)': 'mixed-with-boundary'
                                              in verdict,
    }
    print('\n== G-ADM-2 TALLIES ==')
    for k, v in tal.items():
        print('  %s = %s' % (k, v))
    print('CAP-truncated slot fraction: %d/%d'
          % (tal['slots_capped'], tal['slots_total']))
    print('\n== PREREGISTERED PREDICTIONS ==')
    for k, v in preds.items():
        print('  [%s] %s' % ('PASS' if v else 'FAIL', k))
        if not v and 'P2' in k and p2_viol:
            print('     first P2 violation:', p2_viol[0])
        if not v and 'P3' in k and p3_viol:
            print('     first P3 violation:', p3_viol[0])
        if not v and 'P4' in k and p4_viol:
            print('     first P4 violation:', p4_viol[0])
    print('\nVERDICT:', verdict)
    if offenders:
        print('FIRST OFF-END PARTIAL ROW (the track-B worked gate):')
        print('  ', offenders[0])
    if smoke:
        print('(smoke run: NOT the gate; no disposition written)')
        return 0

    # ------------- disposition (spec H4) ----------------------------------
    dpath = os.path.join(logdir, 'GADM2_DISPOSITION.md')
    with open(dpath, 'w') as fh:
        fh.write('# G-ADM-2 DISPOSITION — realized-strata attainment scan '
                 '(%s)\n\n' % stamp)
        fh.write('Runner: `verification/openmath/gadm2_scan.py` (predictions '
                 'sealed in header pre-run).  Log: `%s` (%d rows).  Spec: '
                 'HDISCHARGE_H3.md 1.3 numerics gates + the ADM-U5 '
                 'instrumentation spec in `verification/h3_classd_scan.py`; '
                 'router semantics REPAIRED per ADM_U7_TRACKA_ATTEMPT.md '
                 'section 6 (is_right_end column; track B fires only on an '
                 'off-end partial).\n\n' % (os.path.basename(jsonl),
                                            tal['rows']))
        fh.write('**VERDICT: %s**\n\n' % verdict)
        fh.write('Tallies: configs=%d, fibers=%d, chain_anomalies=%d, '
                 'rows=%d, full=%d, partial@right-end=%d, '
                 'partial@off-end=%d, anomaly_empty=%d, '
                 'subgroup_ok=False rows=%d (all right-end p>=3 '
                 'pin-explained: %s), CAP-truncated slots %d/%d.\n\n'
                 % (len(cfgs), tal['fibers'], tal['chain_anom'], tal['rows'],
                    tal['full'], tal['partial_end'], tal['partial_offend'],
                    tal['empty'],
                    tal['sub_false_end_podd'] + tal['sub_false_other'],
                    tal['sub_false_other'] == 0,
                    tal['slots_capped'], tal['slots_total']))
        fh.write('Predictions: %s.\n\n'
                 % '; '.join('%s=%s' % (k.split(' ')[0],
                                        'PASS' if v else 'FAIL')
                             for k, v in preds.items()))
        if partial_end_rows:
            cfg0, pk0, rk0, r0 = partial_end_rows[0]
            fh.write('First right-end partial row (pin mechanism, q=%d, '
                     'n_att=%d): config=%s pkey=%s slot=%d.\n\n'
                     % (r0['q'], r0['n_att'], cfg0, pk0, r0['slot']))
        if offenders:
            fh.write('FIRST OFF-END PARTIAL ROW (track-B worked gate): '
                     '%s\n\n' % (offenders[0],))
        fh.write('A no-hit is never cited as proof (finding 7); the '
                 'right-end partials sit at the one slot CEN-J never '
                 'charges (rho-pinned, subtracted via L\' — ADM-U7 '
                 'section 5).  Full routing + next-unit call: '
                 'lean/notes/openmath/GADM2_2026-08-08.md.\n')
    print('disposition ->', dpath)
    print('jsonl ->', jsonl)
    if not preds['P1 (router: no off-end partial)']:
        return 2
    return 0 if all(preds.values()) else 1


if __name__ == '__main__':
    sys.exit(main())
