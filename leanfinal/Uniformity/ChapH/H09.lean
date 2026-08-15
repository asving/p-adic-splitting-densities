/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H02
import Uniformity.ChapH.H13
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapH.H09 — `StageInterface`, the stage interface

**Chapter H, NODE H.09** (`blueprint/CHAP-H_general_induction.md` §3). The `(CS-1Q)` + `(CS-2)` +
`(CS-3)` clause family of `[GENIND-H]`, carried as the fields of one structure over a genre datum
`G` (H.01) at ambient window `N`, entry height `H`, and actual side length `S`.

**Nothing in this structure is proved by chapter H.** The chapter proves the count and rate
theorems of §10 FROM these fields; the fields with no teeth are exactly the capstone's
conditionality, and §16's disposition table lists them as such.

DEPENDS: H.01, H.02, H.13 (`clusterC`) · landed `Uniformity.FactorizationType`,
`FactorizationType.degree` (`Density/LocalData.lean`).

**⚠ ORDERING** (leanspec FINDING O1 / blueprint AMENDMENT A-H.1/O1). `hbracket` mentions
`clusterC`, which is H.13 of §4 — so §3-before-§4 is NOT the landing order and this module imports
`Uniformity.ChapH.H13` explicitly.

**⚠ SIGNATURE NOTE — hypothesis strength at its true minimum (the G.28 lesson).** Three
deliberate weakenings against the corpus's displayed forms, each because the chapter's proofs use
no more:

* `hwin` is `(CS-1Q.a)`, **not** the withdrawn scalar bound `M★ ≥ e(N−1−H)`. `EFF.GENIND.196`
  withdraws the scalar bound *"for general embedded and mixed genres"*; a `StageInterface` field
  stating it would be unsatisfiable there. At `stageLoss = 0` the field degenerates to the scalar
  bound — exactly the two standalone quartic genres (`EFF.GENIND.199`).
* `hprice` is stated with `2 *` throughout because `b_S = (S+1)/2` is a half-integer and
  `ℕ`-division would silently floor it. The `(S − 2 · keyDeg)` factor is `2(b_S − a − 1/2)`, which
  H.33 proves is a genuine `ℕ` (i.e. `2 · keyDeg ≤ S`), so no truncation occurs.
* `hdrain_nonneg`/`hdrain_le_one` replace the corpus's `(CS-EXACT)` **for the rate consumers
  only**. `EFF.GENIND.170` (R6.2) is the licence: *"(CS-EXACT) is required because the induction
  propagates the exact-complement IDENTITY … NOT because bounds fail to propagate: upper bounds
  propagate by monotonicity + union bound"*. Chapter H's rate theorems (H.67, H.68, H.72) are
  bound-direction only, so they need `0 ≤ drainFrac ≤ 1` and nothing more. **A node that needs the
  exactness identity must return `RE-PLAN` for an `exactDrain` field, not assume it.**

**⚠ THE NORMALIZATION IS LOAD-BEARING.** `hbracket` is stated in the **mass** normalization
(`(|K|−1)|K|^{(c(μ)+1)κ−1}`), not the letter-sum (`(|K|−1)|K|^{κ−1}`). `EFF.GENIND.64`: the two
differ by exactly the ghost `|K|^{c(μ)κ}`, *"invisible at genre E and visible at genre F"*. H.42's
genre-F instance is where a wrong normalization would surface; H.21's audit reproduces the
reconciliation `16 · 12 = 192`.

SOURCE: `EFF.GENIND.197` (the `(CS-1Q.a)`/`(CS-1Q.b)` display, with `λ_G`, `r_G`, `Δ_G`, `M_G`,
`C_G^{extra}` and `b_S := (S+1)/2`); `EFF.GENIND.64` (`(CS-2)`, **with its NORMALIZATION
DECLARED**); `EFF.GENIND.66` (`(CS-EXACT)`); `EFF.GENIND.65` (`(CS-3)`); `EFF.GENHN.12`
(`GENHN.A`(v), the stage bracket in stage `dv`-slope units).

TEETH: `(CS-1)`/`(CS-1Q)` and `(CS-3)` have **NONE, at any degree, anywhere in the corpus** —
signed vacuity disclosure (`EFF.GENIND.63`, `.65`, `.197`). `(CS-2)`: the in-line numeric
certificate of `EFF.GENIND.64`, discharged as a **Lean theorem** at H.21.

## Status

Definitional, no proof obligation. Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **The stage interface.** Every field is a clause of `[GENIND-H]` in its TERMINAL wording:
`(CS-1Q.a)`/`(CS-1Q.b)` (ledger `HYP.36`, disposition CARRY), `(CS-2)` (the stage bracket, in the
MASS normalization), `(CS-EXACT)`, and the degree-consistency half of `(CS-3)`.  **Nothing in this
structure is proved by chapter H**; the chapter proves the count and rate theorems of §10 FROM these
fields. -/
structure StageInterface (G : GenreDatum) (N H S : ℕ) where
  /-- The common uniform stage window `M_G`. -/
  stageWindow : ℕ
  /-- `Δ_G = λ_G + r_G`: the sibling-Hensel loss plus the ragged truncation loss. -/
  stageLoss : ℕ
  /-- `C_G^{extra}`: the entry codimension beyond the supporting-line price. -/
  entryCodim : ℕ
  /-- `O_G(1)`: the genre-local slack. -/
  slack : ℕ
  /-- The stage's own α-aggregation bracket, per stage-slope-sum `κ`. -/
  bracket : ℕ → ℕ
  /-- The stage's conservative-drain fraction at stage window `M`. -/
  drainFrac : ℕ → ℝ
  /-- The σ-multiset the stage's decided leaves carry. -/
  stageSigma : FactorizationType
  /-- The actual side length dominates the block's own length. -/
  hS : G.sideLen ≤ S
  /-- **(CS-1Q.a)** — the ragged/loss-corrected stage-window supply. -/
  hwin : G.e₁ * (N - 1 - H) ≤ stageWindow + stageLoss
  /-- **(CS-1Q.b)** — every lost `K`-digit is paid by entry codimension or supporting-line slack. -/
  hprice : 2 * (G.f₁ * stageLoss) ≤ 2 * entryCodim + (S - 2 * G.keyDeg) * H + 2 * slack
  /-- **(CS-2)** — the stage bracket is `GENIND-2(b)` inside the stage, MASS-normalized. -/
  hbracket : ∀ κ, 1 ≤ κ →
    bracket κ * G.stageCard = (G.stageCard - 1) * G.stageCard ^ ((clusterC G.μ + 1) * κ)
  /-- The drain fraction is a genuine fraction. -/
  hdrain_nonneg : ∀ M, 0 ≤ drainFrac M
  hdrain_le_one : ∀ M, drainFrac M ≤ 1
  /-- **(CS-3)**, degree half — at `μ = 2` the leaf dictionary exhausts the block degree. -/
  hsigma : G.μ = 2 → stageSigma.degree = 2 * G.keyDeg

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.StageInterface
#print axioms Uniformity.Density.Induction.StageInterface.mk

end AxCheck
