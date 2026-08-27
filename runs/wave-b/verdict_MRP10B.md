# Verdict — M3-RP10b LANDED (orchestrator, solo, ~2h during the codex-cap/Claude-storm window)

**Node:** the non-recipe `normalized_exists` discharge — the μ₃ campaign's harder closer.
**File:** `leanfinal/Uniformity/ChapC/C132rp10b.lean` (landed in five committed stages:
48f1816f → e6487e84 → 78bf8cbd → 93df4f8a → final). `lake env lean` exit 0, zero sorry,
zero new axiom; every AxChk footprint exactly `[propext, Classical.choice, Quot.sound]`.

## What is proved

* **The candidate is RP-10's own `g₈ = Φ₂² − 2⁴Φ′`** at the corrected grade `42 = e′·u′`
  (the printed grade 21 is machine-impossible — RP-10's certificates stand).
  Calibration that found it: `dv2Hgt = dvSupp at (5,2)` with weights 4-per-π/2-per-X/5-per-key
  (checked against the landed `31` tooth); the 2⁴ correction has inner height `4·4+5 = 21`,
  putting BOTH development slots on the 42-line.
* `s2Hgt₂_corr = 21`, `g8_dev_zero` (the j=0 digit is `−corr`), `dv2Supp_corr = 42`,
  `s2Hgt₃_g8 = 42`, `g8_exactGrade : S2Mu3ExactGrade 42 g₈`.
* **The μ₂ leaf** `s2GradedRes_corr : s2GradedRes 21 corr = 1` (the constant's read is a
  nonzero constant by the scalar law + coefficient fence; `tooth_gradedRes_key`; the
  two-element-field collapse).
* **The μ₃ residual** `mu3GradedRes_g8 : s2Mu3GradedRes 42 g₈ = X + 1`, assembled from
  `mu3GradedRes_Φ₂ = 1` (eq (11), polynomial form), `mu3GradedRes_Φ₂_sq = X` (the odd×odd
  carry through RP-6's twisted law), `mu3GradedRes_neg_corr = 1` (the on-gate eval; the
  minus dies in char 2), and RP-3's additivity at grade 42.
* ★★ `s2Mu3NormRes_g8 : s2Mu3NormRes g₈ = X + 1` (trailing degree 0, trivial strip).
* ★★★ `s2Mu3_hex` — exactly `C132fd0.s2SourceLawsTwo_of`'s `hex` hypothesis, discharged
  (ψ = X+1 forced by RP-10's `s2Mu3_unique_admissible_linear`; witness g₈).
* ★★★ `s2Mu3_calculus_nonempty_of_conv` — the depth-2 calculus
  `Nonempty (FGMNCalculus (s2DepthTwo) 2 1 21)` now conditional on ONLY M3-KP6b's
  converse (`hconv`).

## Consequence

The μ₃/deepTwist campaign's closure chain is one node from done: KP6b's converse →
`s2Mu3_calculus_nonempty_of_conv` fires unconditionally → M3-SG's consumer applications.

## Process notes

Two false starts recorded honestly: the orchestrator's first worked route proposed a wrong
candidate (2⁸·X·Φ′, inner height 39 — caught by calibrating against the landed 31 tooth
BEFORE any Lean was written); the launcher brief was corrected in place (commit 20ff7aa9).
The 22:07 codex MRP10B unit is superseded by this verdict (the launcher's skip guard fires).
