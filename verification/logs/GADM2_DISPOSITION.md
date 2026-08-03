# G-ADM-2 DISPOSITION — realized-strata attainment scan (20260802T232440Z)

Runner: `verification/openmath/gadm2_scan.py` (predictions sealed in header pre-run).  Log: `gadm2_attainment_20260802T232440Z.jsonl` (198 rows).  Spec: HDISCHARGE_H3.md 1.3 numerics gates + the ADM-U5 instrumentation spec in `verification/h3_classd_scan.py`; router semantics REPAIRED per ADM_U7_TRACKA_ATTEMPT.md section 6 (is_right_end column; track B fires only on an off-end partial).

**VERDICT: RIGHT-END-ONLY PARTIAL (mixed-with-boundary): no track-B fire; track A live as (ADM-REAL'); ADM-U7 dichotomy CONFIRMED at scan scope**

Tallies: configs=13, fibers=99, chain_anomalies=0, rows=198, full=113, partial@right-end=85, partial@off-end=0, anomaly_empty=0, subgroup_ok=False rows=83 (all right-end p>=3 pin-explained: True), CAP-truncated slots 14/432.

Predictions: P1=PASS; P2=PASS; P3=PASS; P4=PASS; P5=PASS; P6=PASS; P7=PASS.

First right-end partial row (pin mechanism, q=3, n_att=1): config=(3, 3, 5, None) pkey=(((0, 3), (3, 0)), (((1, 1), (1, 2)),)) slot=2.

A no-hit is never cited as proof (finding 7); the right-end partials sit at the one slot CEN-J never charges (rho-pinned, subtracted via L' — ADM-U7 section 5).  Full routing + next-unit call: lean/notes/openmath/GADM2_2026-08-08.md.
