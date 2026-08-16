/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapD.D45 — `thresholdTheta`, T4's composed thresholds `Θ_j = (μ₂−j)E₂ + δ`

**Chapter D, NODE D.45** [def+lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §7, the
certificate witness (T4); amendments A-1, A-D.1 govern). ENV-D1 (the arithmetic arena: no `O`,
no polynomials — `ℕ`/`ℤ` statements, provable outright). Two signed declarations, the chapter's
head of §7 and one of its ten immediately fireable nodes.

*The composed thresholds.* In T4's setting (`EFF.T4.01`) the level-2 data are
`D′ = e₁f₁`, `E₂ = e₂f₂u₂` and `δ = u₂ − e₂D′h ≥ 1`, and the certificate thresholds are

```
Θ_j = (μ₂ − j)·E₂ + δ        for j < μ₂.
```

* `thresholdTheta μ₂ E₂ δ j` — that composite, as a function of the four numerals. `E₂` and `δ`
  are ARGUMENTS, not recomputed from `(e₂, f₂, u₂, h, D′)`: the node is the threshold's
  arithmetic, and the concrete suppliers of `E₂`/`δ` are the T4 instances (D.53/D.54, chapter-C
  placeholders).
* `thresholdTheta_anti` — the only property the downstream lemmas consume: on the coordinate
  range `j < j′ < μ₂` the thresholds strictly DECREASE as `j` grows.

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (one definition; parent CLAUDE.md trust boundary).
Three recasts against `EFF.T4.01`, all flagged for the chapter cross-read:

* *`ℕ` with truncated subtraction.* `μ₂ - j` is `Nat`-subtraction, so outside the corpus's own
  range `j < μ₂` the definition silently reads `Θ_j = δ`. That is why the antitony lemma carries
  `h' : j' < μ₂` as an explicit hypothesis rather than deriving it: the statement is FALSE
  without it (at `μ₂ = 1, j = 1, j' = 2` both sides are `δ`, so the strict inequality fails).
  The hypothesis is exactly the corpus's own quantifier "`for j < μ₂`".
* *`δ ≥ 1` is not a hypothesis.* `EFF.T4.01` records `δ = u₂ − e₂D′h ≥ 1`, and the blueprint's
  STATEMENT quotes the antitony with `δ ≥ 1` in front of it; the inequality is in fact
  independent of `δ` (it cancels), so the signed signature carries no `hδ` and nothing is
  weakened by its absence — the SIGNATURE block is landed byte-for-byte.
* *`0 < E₂` is a hypothesis, and it is necessary.* At `E₂ = 0` every `Θ_j` equals `δ` and
  antitony fails. `EFF.T4.01`'s `E₂ = e₂f₂u₂` is positive at every instance; the Lean statement
  asks for it rather than deriving it, since `e₂, f₂, u₂` are not arguments of this node.

**DEPENDS.** none (the blueprint's DEPENDS field is empty; this node is fireable at the start of
the chapter).

**PROOF.** `omega` for the truncated-subtraction step `μ₂ - j' < μ₂ - j`, then multiplication by
the positive `E₂` and translation by `δ`. (The blueprint's PROOF field says "`omega`"; `omega`
alone cannot finish it, because the goal multiplies two variables — `omega` is linear-arithmetic
only. The nonlinear step is one `mul_lt_mul_of_pos_right`. No statement changed; this is a proof
note, not a signature note.)

SOURCE: `EFF.T4.01` (the setting: `D′ = e₁f₁`, `E₂ = e₂f₂u₂`, `δ = u₂ − e₂D′h ≥ 1`,
`Θ_j = (μ₂−j)E₂ + δ` for `j < μ₂`).

**TEETH.** T4 S8 PE1(4) → gate **D.66**'s `Θ` table at the X-frame numbers
(`thresholdTheta 3 3 1 = (10, 7, 4)`, with the `[12, 7, 4]` self-shadow separator of the FR-M3
frame and this node's antitony executed there). Nothing is scored in this file — the gate node
owns the numerals, and duplicating them here would put two copies of a battery row in the
chapter.

ENVIRONMENT: ENV-D1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.45** T4's composed threshold `Θ_j = (μ₂ − j)·E₂ + δ` (`EFF.T4.01`), with `E₂ = e₂f₂u₂`
and `δ = u₂ − e₂D′h` supplied as numerals by the instances. -/
def thresholdTheta (μ₂ E₂ δ j : ℕ) : ℕ := (μ₂ - j) * E₂ + δ

/-- **D.45** Strict antitony on the coordinate range `j < j′ < μ₂` (`EFF.T4.01`).  Both
hypotheses are necessary: at `E₂ = 0` the thresholds are constant, and beyond `μ₂` the truncated
subtraction flattens them. -/
theorem thresholdTheta_anti (μ₂ E₂ δ : ℕ) (hE : 0 < E₂) {j j' : ℕ}
    (h : j < j') (h' : j' < μ₂) :
    thresholdTheta μ₂ E₂ δ j' < thresholdTheta μ₂ E₂ δ j := by
  have hsub : μ₂ - j' < μ₂ - j := by omega
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_lt_of_le hsub (le_refl E₂) hE) δ

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.thresholdTheta
#print axioms Uniformity.Density.Gauge.thresholdTheta_anti

end AxCheck
