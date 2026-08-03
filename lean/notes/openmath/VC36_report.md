# VC36 — Codex end-to-end audit of ROOT REVISION 34 (pinned 23282f5): NOT-CONFIRMED, 1C/3G

Charge: /tmp/openmath/VC36_charge_v2.txt (839,009 bytes; FROZEN-HISTORY TRIM per checklist rule 7 — v1 at 1,210,905 bytes exceeded the 1,048,576-char Codex input cap and died silently at launch; v2 = full §§0-6 + all 8 r35 diff hunks in context + full §§38-40 + diff-verified byte-identity disclosure for §§7-37 + census transcripts over the FULL pinned text, 69/69 matching).

## Orchestrator adjudication (2026-08-03)

- F1 [CRITICAL] + F2 [GAP]: FOLD-LAG, cured post-pin — the audited text honestly recorded the then-live PC1 scope critical and F8 gap; the errata arc (7566ccd: S0 scope erratum + iterlaw_cor4_mixed.py 18,396/0) and the acceptance (PC2 CLEAN 804b88a + PE2 CLEAN c40a1da; adjudicated 33373cb) resolve both. r36 folds the resolution + rewrites the §40.(i)/closing ITER-LAW displays to the scope-corrected ACCEPTED form.
- F3 [GAP]: GENUINE qualifier omission at the REVISION-34 close (gr(w2) residual missing from the ITER-LAW summary) — r36 erratum.
- F4 [GAP]: GENUINE qualifier omission at the same close (depth-1 honesty + synthetic-but-lawful missing from the H7 summary) — r36 erratum. Defect class: qualifier-propagation at closing restatements (recurring); both sites get the full qualifier lists.
- Cadence: r36 fold (REVISION 35) applies all four remedies -> VC36b narrow confirming pass -> on CONFIRMED, anchor re-anchors at REVISION 34/VC36+VC36b.

## Codex output (verbatim)

I’ll audit the pinned commit directly, using the appendices as the charge map and the repository copy only for read-only verification. I’ll pay particular attention to the known ITER-LAW scope critical, qualifier propagation, touched-file claims, and the exact census unit.
1. [CRITICAL] ITER-LAW proof scope does not match the statement of record
    QUOTE: "The Codex content leg returned NOT-CLEAN, 1 critical + 1 gap (acc955a — the critical: an E₂ > 1 SCOPE MISMATCH between the proof note's setting (e₀, e₁ ≥ 1) and the statement of record's pinned E₂ > 1 composite-stage setting, orchestrator-confirmed; the gap: an F8 mixed-block under-test)."
    DIAGNOSIS: Charge item (lxxx) requires the attempt-grade proof to establish DITER_RESTATE §S2's pinned class. The document itself records an orchestrator-confirmed scope mismatch, so its claim that the statement of record is proved at attempt grade is unsupported. This breaks the ITER-LAW record chain; dependent J3b uses cannot be confirmed.

2. [GAP] Mixed-block coverage is under-tested
    QUOTE: "the gap: an F8 mixed-block under-test"
    DIAGNOSIS: Against charge item (lxxx), the displayed 35,232-sample falsifier record does not adequately justify the mixed-block leg. Assuming that leg for downstream checking does not cure the missing coverage.

3. [GAP] The gr(w₂) residual is omitted from an operative ITER-LAW summary
    QUOTE: "**ITER-LAW PROVED AT ATTEMPT GRADE on the harness tower class** (standard-lift towers — the class DITER_RESTATE §S2 pins; seal ab7c31c, run 242ba1e, ALL GREEN FIRST PASS 35,232/0; acceptance counter 0, hostile passes in flight — both landed at the fold's close, one CLEAN and one NOT-CLEAN 1C/1G with the errata round owed, per the §40.(i) concurrency disclosure; (ITER-LAW-LIFT) open exactly at g₀ = 1 ∧ δ₁ = 1; orders ≥ 3 untouched)"
    DIAGNOSIS: Charge item (lxxx) requires all three residuals wherever the result is used. This REVISION-34 closing site displays the lift and order residuals but omits that the gr(w₂) semantics wrapper rides the GRB retarget consumer-side.

4. [GAP] H7 depth and synthetic-node qualifications are omitted from an operative summary
    QUOTE: "**the first compiled non-vacuous (H7) decision point** (037ac6f — both OL-2 rfl-degeneracies broken, the N-H7-1 pins decided at the instance, NOTHING discharged)"
    DIAGNOSIS: Charge item (lxxxii) requires every H7-forge site to display depth-1 honesty, synthetic-but-lawful nodes, and that nothing discharges (H7). This closing site includes only the last qualification.

NOTES:
Execution was unavailable because bubblewrap is absent on this host; per standing disclosure (a), this is not a finding. The pinned Appendix-D transcripts report 69/69 census rows matching at the declared occurrence unit.

VC36 FINDINGS: 1 critical, 3 gaps
VERDICT: NOT-CONFIRMED
