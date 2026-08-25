# Verdict — unit RP56: S2-source plan nodes RP-5 + RP-6 (CORES 3/4 and 4/4) — `graded_mul` CLOSED

Date: 2026-08-25 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, rows RP-5
("Discharge the inner residual product and twist normalization", B39a `resPoly_mul_gen`
dependency) and RP-6 ("Assemble exact-grade product plus polynomial identity for arbitrary
inputs"), under the A-C.13 amendment (verdict_AC13.md: the `PrevGrade β'` premise RESTORED
in `FGMNSourceLaws.graded_mul`, S2 realization = evenness) and RP-4's landing
(verdict_RP4.md: general convolution + assembled exact-grade identities).
File created (the ONLY repo file touched): `leanfinal/Uniformity/ChapC/C130rp6.lean`
(371 lines, 12 public declarations + 1 private helper + 1 shape-pin example; not added to
`Uniformity/ChapC.lean` or any roll-up; no leanspec/ or other units' files touched; NO git
commit).

## RP-5 — the audit (recorded in the module docstring), and the one genuine landing

**Audit verdict: the inner residual product and the twist normalization ARE genuinely
discharged by RP-4's engine; B39a `resPoly_mul_gen` has no remaining S2 work.**  At the S2
frame the inner (level-one) residual of a depth-two slot is a SINGLE ϖ-digit
(`s2_twistRead_eq_digAt`: window `{0}`, letter `η = 1`), so the row's "inner residual
product" is the reduced two-digit product `(a·b) %ₘ Φ′` — discharged inside RP-4's
convolution by RP-3's survival core `s2_twistRead_mul_modByMonic` (value) with NV-3's `≤`
and RP-4's `≥` height halves; the twist `X^c` is fully normalized at the coefficient
(`s2GradedCoeff_mul` at `T+c`, `_zero_of_odd` below) and polynomial
(`s2GradedRes_mul_of_exact`) levels.

**The one residual-normalization case RP-4's forms do NOT cover — landed**: the twist's
honesty at the `y`-ORDER level.  `X^c` shifts orders only against a NONZERO product, and no
landed or planned row gives polynomial-level nonvanishing at exact grade (RP-7 is `coeff 0`
under the `< deg φ₂` fence — false without it; RP-8's is the normalized residual; on B39a's
route this was `natDegree_resPoly`'s nonzero half).  Landed:
★ **`s2GradedRes_ne_zero_of_exact`** (`S2ExactGrade β g → R_β(g) ≠ 0`, NO degree fence) via
the new **`exists_slotOnGrade_of_exact`** (inf-attainment gate witness: `dvSupp` is a finite
`Finset.inf`, so an exact grade is some slot's own line term — closes the existence side of
RP-1's gate) + C.23's attained-height nonvanishing `KeyFrame.slotRes_ne_zero`.  Consequence
for RP-9/RP-10: "including all zero cases" collapses — at exact grades there are none.
Deliberately NOT landed (RP-9's own row): the `y`-order addition arithmetic itself.

## RP-6 — `graded_mul` ASSEMBLED (the A-C.13-amended C130fg field shape, verbatim)

* **`S2PrevGrade β := 2 ∣ β`** — the S2 realization of the restored `PrevGrade` field (U14
  §8.1: preceding-group membership; under full-current-group clearing `e' ∣ β`, `e₂ = 2` at
  S2 — evenness); shape-pinned `ℕ → Prop`; normal form `S2PrevGrade_iff_mod` (`↔ β % 2 = 0`).
* ★ **`s2_graded_mul`** — the amended field BYTE-PARALLEL at the S2 operators:
  `∀ β β' (g h), S2ExactGrade β g → S2ExactGrade β' h → S2PrevGrade β' →
  S2ExactGrade (β+β') (g·h) ∧ R_{β+β'}(g·h) = R_β(g)·R_{β'}(h)` — grade conjunct from RP-0's
  `S2ExactGrade_mul`, polynomial conjunct from RP-4's `s2GradedRes_mul_of_prevGrade`.
  Junk-input handling exactly as the field's totality demands: total in `g, h` (RP-1's
  junk-total residual, RP-0's total grade `Prop`s), hypotheses alone fence (the zero
  polynomial satisfies no `S2ExactGrade` — RP-0's `S2ExactGrade_zero_false`).
* ★ **`s2_graded_mul_twisted`** — the S2 BONUS law (repo's OWN arbitrary-grade
  generalization, U14 §5/§8.2, NOT published Cor 4.12(2)): no `PrevGrade` premise, twist
  `X^{(β%2)(β'%2)}`, exact-grade conjunct bundled — RP-4's `_of_exact` in FD-0-ready
  conjunction shape.
* **`s2_graded_mul_fills`** — the FD-0 pin, TYPED against the actual C130fg structure: for
  ANY `S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 5` with `nextValue = s2Hgt₂`,
  `gradedResidual = s2GradedRes`, `PrevGrade = S2PrevGrade`, the amended `graded_mul` field
  for `S` holds verbatim — FD-0's record assembly has zero residual proof work for this
  clause.  (Conditional pin, NOT an instance: `normalizedResidual` etc. are RP-8+.)

## Teeth

`tooth_prevGrade_two` / `tooth_prevGrade_fence`: `S2PrevGrade 2` holds, `S2PrevGrade 5`
FAILS — the restored premise fences out exactly the odd×odd genre whose plain conclusion is
machine-refuted (`C130rp2.tooth_graded_mul_plain_shape_refuted`, `R₁₀(Φ′²) = X ≠ 1`).
`tooth_graded_mul_fires` + `tooth_graded_mul_value`: the assembled law fires at `(5,2)` on
`(Φ′, x)` — grade 7 exactly AND `R₇ = 1·1 = 1`, matching RP-1's landed hand computation.
`tooth_twisted_fires`: the bonus law at `(5,5)` delivers grade 10 AND re-derives
`R₁₀(Φ′²) = X` — the fenced-out genre is carried by the twist, not lost.
`tooth_ne_zero_key`: RP-5's nonvanishing fires on the landed grade-5 key.

## What was deliberately NOT claimed

No `FGMNSourceData/Laws/ChainRealization` instance (FD-0); no `graded_scalar_nonzero`
(RP-7); no normalized residual, twist absorption, or `y`-order addition (RP-8/RP-9/RP-10 —
only RP-9's missing nonvanishing input landed).  Only the `PrevGrade`-fenced conjunction may
be cited as published Cor 4.12(2); the twisted law is the repo's own generalization.
Flagged for human review (new statements): `S2PrevGrade` (the evenness realization, carried
as a definition until OPEN-DICT-2 proves the divisibility test),
`exists_slotOnGrade_of_exact`, `s2GradedRes_ne_zero_of_exact`, the three assembly theorems.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C130rp6.lean` — CLEAN (exit 0, 0 errors,
0 warnings, 0 sorry).  `lake build Uniformity.ChapC.C130rp6` — success (8745 jobs).  13
`#print axioms` rows, ALL within `[propext, Classical.choice, Quot.sound]` (`S2PrevGrade`
and `tooth_prevGrade_two` axiom-free; 0 `sorryAx`); no new axiom, no `unsafe`, no statement
touched, no other file modified (`git status` on `leanfinal/Uniformity` shows only this file
plus NP3F's own in-flight `C130np3.lean`, untouched).  No git commit (per brief).
