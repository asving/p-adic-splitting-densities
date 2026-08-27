# Verdict — MH8 promotion of MH.8+X1 to production

**Date:** 2026-08-27

**Unit:** MH8 (SONNET, transcription tier)

**Charge:** promote MHG's probe-proved Hensel gates (`leanfinal/scratch/MHG_probe.lean`,
green, orchestrator-verified) to a production declaration file, node tag
`[MH.8+X1, 2026-08-27]`.

**Result:** transcription complete. `leanfinal/Uniformity/ChapC/C133mh8.lean` created,
plumbing-only relative to the probe (namespace `Uniformity.Density.Tower.C133mh8`,
production imports `C35`/`C129`/`C130s6`/`Uniformity.HenselFactorization`, docstrings per
the `C133mh1` precedent). All nine theorem statements are byte-identical to the probe's:

* `dvOnSide_weight_eq`, `onSide_weight_le_slot` (X1's supporting-line helpers)
* `otherSlope_pointSide` (**X1 / OPEN-4**, the stronger singleton-side form)
* `inf_devGauss_le_gaussVal`, `stageHeight_le_gaussVal_add_loss` (MH.8 inner lemmas)
* `dvSupp_le_scaled_gaussVal_add_window` (**MH8-U**, forward upper comparison)
* `gaussVal_of_shifted_dvSupp` (**MH8-F**, forward conversion)
* `reverseTransport` (**MH8-R**, reverse transport)
* `exists_dvGradedLimit` (**MH.8, fully assembled** graded limit, in the `Complete`
  section under `IsAdicComplete`)

Private helpers `gaussVal_eq_zero_of_monic`, `inf_gaussVal_le_gaussVal_sum`,
`le_dvSupp_sub` and the two statement-shape defs (`BoundedWindowUpperComparisonStatement`,
`ReverseTransportStatement`) are also transcribed verbatim.

## Build check

```
cd leanfinal
lake env lean Uniformity/ChapC/C133mh8.lean
```

Exit 0. Zero `sorry`, zero error, zero warning (13 lines of output total, all from the
nine `#print axioms` calls in the AxCheck footer).

## AxCheck footer (all Lean-core)

```
'Uniformity.Density.Tower.C133mh8.dvOnSide_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh8.onSide_weight_le_slot' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh8.otherSlope_pointSide' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh8.inf_devGauss_le_gaussVal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh8.stageHeight_le_gaussVal_add_loss' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh8.dvSupp_le_scaled_gaussVal_add_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh8.gaussVal_of_shifted_dvSupp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh8.reverseTransport' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133mh8.exists_dvGradedLimit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Zero new axiom declared; footprint identical to the probe's.

## Scope discipline

Did not touch `leanfinal/scratch/MHG_probe.lean`, `docs/in-progress/HENSEL_ENGINE_2026-08-26.md`,
roll-ups/leanspec, or sibling files `C133mh1.lean`, `C133mh2.lean`, `C133mh3.lean`. Only
new file: `leanfinal/Uniformity/ChapC/C133mh8.lean`. No commit made.
