# Verdict — MH1: MH.1 promoted to production (transcription unit)

**Date:** 2026-08-27
**Unit:** MH1 (Sonnet transcription tier)
**Charge:** transcribe the corrected Hensel-engine root node MH.1
(`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §3.1′, `[MHFIX 2026-08-27]`) from
`leanfinal/scratch/MHFIX_probe.lean` into a production ChapC module, per
`runs/wave-b/verdict_MHFIX.md`'s regrade (MH.1 "transcription-ready").

## Landed

`leanfinal/Uniformity/ChapC/C133mh1.lean`, namespace `Uniformity.Density.Tower.C133mh1`,
imports `C35`, `C130nv3`, `C131f`, `C141defs` (the probe's chain, reused verbatim):

* `twistExp_add_carry` — **PROVED**, Lemma TW-δ (the carry-exponent cocycle
  `q(k)+q(k')+δ = q(k+k')`, `δ ≤ 1`, `e₁δ = i(k)+i(k')−i(k+k')`), from C.16's specs alone.
* `twistRead_mul_of_slotRes_carry` — **PROVED**, the carry ⟹ twist bridge (clause (2)
  implies clause (1) given TW-δ; the C.22 inverse twist cancels `η^δ`).
* `M1TwistProductLawStatement`, `M1SlotCarryLawStatement`, `M1DigitFaithfulStatement` —
  **STATEMENT SHAPES** (`Prop`-valued defs, nothing asserted), the three M1′ clauses
  (twist product / slot carry / digit faithfulness recovering old M1(1)), named exactly
  per the doc's §3.1′ node-table naming.
* `isKey_X`, `localFieldStageField` — private D9 plumbing (byte-identical re-declaration
  per the standing convention at C.04/C.12/C.26/C.47/C.80/C.97; not importable, so
  re-declared here rather than imported).

Statements are byte-identical to the probe and to the doc's §3.1′ pins; only plumbing
changed (namespace, `import` path, docstring). No theorem/def signature was altered.

## Explicitly out of scope (left for other units)

* The full M1′ proof (doc §3.1′ Steps 1–6: the associated-graded model, the reading
  homomorphism `ρ̃`, and the assembly discharging the three statement shapes) —
  MATH-PROVED, Lean-transcription OPEN, sized 250–450 lines. Not attempted here; would
  not be a "plumbing adjustment" on the probe.
* `MixedResidualLawTauOneStatement` / `MixedResidualLawExistsUnitStatement` /
  `existsUnit_of_tauOne` — Theorem M clause 3, node **MH.3**, not MH.1.
* The probe's executable F₉-gate/numeral-mirror teeth — cert-style sanity instances,
  already covered by `verification/mhfix_cert.py`; not generic reusable declarations.
* MH.2's `dvSideMax`-additivity half (still PROOF-OUTLINE grade per the regrade) —
  untouched.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C133mh1.lean` — **exit 0**, zero `sorry`,
zero `error`, zero `warning`. AxChk footer (`#print axioms`):

```
'Uniformity.Density.Tower.C133mh1.twistExp_add_carry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh1.twistRead_mul_of_slotRes_carry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh1.M1TwistProductLawStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh1.M1SlotCarryLawStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh1.M1DigitFaithfulStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only ({propext, Classical.choice, Quot.sound}); zero new axiom.

## Not done

`C133mh1.lean` is NOT wired into the `Uniformity/ChapC.lean` roll-up (roll-ups are
out of scope for this unit per its charge). No commit made.
