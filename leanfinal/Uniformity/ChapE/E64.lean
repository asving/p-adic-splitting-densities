/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E60

/-!
# Uniformity.ChapE.E64 — depth ≥ 3 is unreachable below `n = 16` (the necessary direction)

**Chapter E, NODE E.64** [lemma] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §9 — the
`(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` indexed carriers). ENVIRONMENT: ENV-E1. One signed declaration,
`depth3_needs_16`.

## What the node says

A read history that performs `J ≥ 2` level jumps needs initial mass `μ₀ ≥ 8` — that is E.60's
FOURTH clause, `2 ≤ J → 8 ≤ μ 0`, which this node consumes as the hypothesis `hJ8` rather than
re-deriving. The node's own content is the `n`-bookkeeping on top of it: the degree at which the
read starts is `n = D₀ · μ₀`, and a composite stage has `D₀ ≥ 2` (the stage's own key degree
`D′ = e₁f₁ ≥ 2`), so

```
J ≥ 2   ⟹   μ₀ ≥ 8   ⟹   n = D₀·μ₀ ≥ 2·8 = 16.
```

Contrapositively — and this is the sentence the corpus states — *level 3 is unreachable below
`n = 16`*: below degree 16 the σ-ladder cannot host two jumps, hence never opens a level-3 rung,
hence never instantiates the Display-A `∀ i ≥ 3` deep-twist conjunct (E.63). Together with
E.60's clause 3 (`μ 0 ≤ 7 → μ i ≤ 3` for `1 ≤ i ≤ J`) this is what gives chapter E its `n ≤ 15`
coverage without any level-3 machinery.

## ⚠ THE NECESSARY DIRECTION ONLY — no existential converse is stated

Per ANNEX R R3 (the rider quoted at E.07's ⚠ note), `n = 16` is *the first degree NOT EXCLUDED*
by the bound. This node does **not** claim that depth 3 is REACHED at `n = 16`. ANNEX R R1.3's
constructed `n = 16` family (`μ = 8 → 4 → 2`, 79/79 machine witnesses, `he7rannex_supp.py`) is
machine evidence for non-vacuity of the threshold and is recorded as such — it is NOT a Lean
theorem here, and no chapter-E node states the existential. A consumer that reads this lemma as
"depth 3 occurs at `n = 16`" has read it backwards.

The gate section below fires the lemma on exactly that family (`D₀ = 2`, `μ₀ = 8`, `J = 2`,
with `hJ8` supplied by E.60 rather than by hand) and records the two-sided witness that both
hypotheses are load-bearing: dropping `hD` or weakening `μ₀` to `7` breaks the conclusion.

## Signature check against the committed stub

`leanspec/Leanspec/ChapE.lean` §9 signs

```lean
axiom depth3_needs_16 {D₀ μ₀ J : ℕ} (hD : 2 ≤ D₀) (hJ8 : 2 ≤ J → 8 ≤ μ₀)
    (hJ : 2 ≤ J) : 16 ≤ D₀ * μ₀
```

and the blueprint's SIGNATURE block is byte-identical to it. What lands below is that statement
unchanged, as a `theorem`.

**DEPENDS.** E.60 (clause 4 is the `hJ8` hypothesis; imported so the gate can fire it, and so the
DAG edge is a real Lean edge). **PROOF.** `hJ8 hJ` then `Nat.mul_le_mul`.

**SOURCE.** `EFF.HE7.15` + ANNEX R R3's rider; `EFF.HE7.114` (*"the first level at which any new
symbol (a `ϑ_t ≠ 1`, …) can appear is level 3, unreachable below `n = 16` (THEOREM HE7.C)"*).

**TEETH.** `he7rannex_supp.py` (the `n = 16` family, 79/79) → instance evidence for non-vacuity
of the threshold; the theorem is the necessary direction only.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **NODE E.64.** *Depth ≥ 3 is unreachable below `n = 16`, necessary direction (ANNEX R R3's
rider).* At a composite stage (`2 ≤ D₀`), a read history performing `J ≥ 2` level jumps carries
initial mass `μ₀ ≥ 8` (E.60's clause 4, supplied as `hJ8`), so its degree `n = D₀·μ₀` is at
least `2·8 = 16`. NO existential converse is claimed: `n = 16` is the first degree the bound
fails to exclude, not a degree at which depth 3 is exhibited. -/
theorem depth3_needs_16 {D₀ μ₀ J : ℕ} (hD : 2 ≤ D₀) (hJ8 : 2 ≤ J → 8 ≤ μ₀)
    (hJ : 2 ≤ J) : 16 ≤ D₀ * μ₀ :=
  calc (16 : ℕ) = 2 * 8 := by norm_num
    _ ≤ D₀ * μ₀ := Nat.mul_le_mul hD (hJ8 hJ)

end Uniformity.Density.Ladder

/-! ## Numeric gate — the lemma fired at ANNEX R R1.3's `n = 16` family

The mass sequence `μ = 8 → 4 → 2` with `J = 2` jumps is the corpus's own machine-exhibited
witness family. Below, its `hJ8` is NOT supplied by hand: it comes out of E.60's clause 4 at that
sequence, so the gate exercises the real E.60 → E.64 edge. -/

section Gate

open Uniformity.Density.Ladder

/-- ANNEX R R1.3's `n = 16` mass sequence: `μ 0 = 8`, `μ 1 = 4`, `μ i = 2` thereafter. -/
private def mu16 : ℕ → ℕ := fun i => if i = 0 then 8 else if i = 1 then 4 else 2

/-- The two-jump hypotheses hold at that sequence (floors at the jump STARTS `i < 2`, halvings
at the same indices) — the A-E.1/E-D11 hypothesis set, under which the family is admissible. -/
example : (∀ i < 2, 4 ≤ mu16 i) ∧ (∀ i < 2, 2 * mu16 (i + 1) ≤ mu16 i) := by decide

/-- **The E.60 → E.64 edge, executed.** With `D₀ = 2` (a composite stage) and E.60's clause 4
firing at the `n = 16` family, E.64 returns `16 ≤ 2 * 8`. -/
example : 16 ≤ 2 * mu16 0 :=
  depth3_needs_16 (D₀ := 2) (μ₀ := mu16 0) (J := 2) (by norm_num)
    ((ladder_finite_bounds mu16 2 (by decide) (by decide)).2.2.2) (by norm_num)

/-- The threshold is EXACTLY 16 at that family — the bound is attained, not slack. -/
example : 2 * mu16 0 = 16 := by decide

/-- `hD` is load-bearing: at a `D₀ = 1` stage the conclusion is false even with `μ₀ = 8`
(`1·8 = 8 < 16`). So the "composite stage" hypothesis cannot be dropped. -/
example : ¬ (16 ≤ 1 * 8) := by decide

/-- `hJ8` is load-bearing at its own value: `μ₀ = 7` (E.60 clause 3's edge configuration) gives
`2·7 = 14 < 16`. The `8` is the exact mass the two-jump bound supplies. -/
example : ¬ (16 ≤ 2 * 7) := by decide

/-- The contrapositive reading, on the bounded range the chapter covers: no `n ≤ 15` factors as
`D₀·μ₀` with `2 ≤ D₀` and `8 ≤ μ₀`, so **no `n ≤ 15` admits two jumps at a composite stage** —
the `n`-reading of R1-d's "unreachable below `n = 16`". -/
example : ∀ D₀ ≤ 15, ∀ μ₀ ≤ 15, 2 ≤ D₀ → 8 ≤ μ₀ → 16 ≤ D₀ * μ₀ := by decide

end Gate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.depth3_needs_16

end AxCheck
