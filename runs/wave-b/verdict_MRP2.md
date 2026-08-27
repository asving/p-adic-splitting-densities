# Verdict — node M3-RP2: the total μ₃ graded operator `s2Mu3GradedRes` assembled

Date: 2026-08-27 · Unit MRP2 (Sonnet transcription tier) ·
`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP2 · REUSE-WITH-NUMERALS
(mechanical port, no invention needed) · Deliverable: `leanfinal/Uniformity/ChapC/C132rp2.lean`
(184 lines, node tag `[M3-RP2, 2026-08-27]`).

## What landed

A mechanical port of the μ₂ polynomial assembly (`C130rp1.lean:279-345`, Parts 3-4) onto
the just-landed μ₃ recursive coefficient `s2Mu3Coeff` (M3-RP1, `C132rp1.lean`):

* `s2Mu3GradedRes β g : Polynomial ((s2DepthTwo h2 hq).fld 2)` — the assembled total
  operator, `Σ t ∈ range (β+1), C (s2Mu3Coeff β g t) * X^t` (published Def 3.13's `R_β(g)`
  at the μ₃ numerals), plus the abstract `FGMNSourceData.gradedResidual` shape pin.
* **the master coefficient law** `s2Mu3GradedRes_coeff`.
* **range independence** `s2Mu3GradedRes_eq_sum_range` (sum over any `M ≥ β+1`).
* **finite support**: packaged (`s2Mu3GradedRes_natDegree_le`, `natDegree ≤ β`) and raw
  (`s2Mu3GradedRes_coeff_eq_zero_of_natDegree_lt`, lifting M3-RP1's coefficient-level
  `s2Mu3Coeff_eq_zero_of_natDegree_lt`).
* **the zero-above law** `s2Mu3GradedRes_zero_of_above` (published Lemma 3.14's
  `graded_zero_of_above` field shape) plus the zero-polynomial tooth `s2Mu3GradedRes_zero`.

Seven declarations total, all `#print axioms`-checked.

## One simplification over the μ₂ ancestor (noted, not a deviation)

The μ₂ `s2GradedRes_zero_of_above` (`C130rp1.lean:345-353`) re-derives the gate negation
inline from `S2AboveGrade_iff_dvSupp`/`dvSupp_le_of_slotOnGrade`, because no
coefficient-level zero-above law existed yet at that μ₂ node. At μ₃, M3-RP1 already landed
the coefficient-level `s2Mu3Coeff_eq_zero_of_above` (its own docstring: "M3-RP2 lifts it to
the assembled polynomial"), so `s2Mu3GradedRes_zero_of_above` here is a direct
`Polynomial.ext` + rewrite — three lines shorter, same content, no new mechanism.

## BLOCKED-BECAUSE ledger

None. Every law in the μ₂ Part 3/4 bank (`C130rp1.lean:279-358`) ported directly with
`s2GradedCoeff`→`s2Mu3Coeff`, `S2AboveGrade`→`S2Mu3AboveGrade`, `5`→`21` (already baked
into `s2Mu3Coeff`'s own pins, so no numeral literally appears in this file). No law failed
to port; no invented statement.

## Build verification

`C132rp1`'s `.olean` did not yet exist in the build cache (freshly landed by the sibling
node); built it via the SCOPED target `lake build Uniformity.ChapC.C132rp1` (not a bare
whole-project `lake build`) — succeeded, 8784/8784 jobs, Lean-core-only footprint on all 37
of its declarations. Then, from `leanfinal/`:

```
lake env lean Uniformity/ChapC/C132rp2.lean
```

Exit 0. Zero errors, zero warnings, zero `sorry`. Every one of the seven declarations below
prints exactly `[propext, Classical.choice, Quot.sound]` (Lean core only, no new axiom):

`s2Mu3GradedRes`, `s2Mu3GradedRes_coeff`, `s2Mu3GradedRes_eq_sum_range`,
`s2Mu3GradedRes_natDegree_le`, `s2Mu3GradedRes_coeff_eq_zero_of_natDegree_lt`,
`s2Mu3GradedRes_zero_of_above`, `s2Mu3GradedRes_zero`.

## Scope discipline

No roll-up, leanspec, or other existing file touched. `C132rp4.lean` untouched (sibling
node). No commit made.
