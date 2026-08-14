/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.GenuineDensity

/-!
# Uniformity.Density.Statement — THE CAPSTONE TARGETS (statements only)

The `Prop`s below are the **targets** of the whole repo. They are *definitions*, not sorried
theorems: this repo carries zero `sorry`s from day one, so a target is a named `Prop` until it
is proved.

## The two densities, and hence the two targets

Since the 2026-08-13 rewire there are two limits in play, both proved to be limits, and each
target comes in a version over each:

* `genuineDensity O n σ = ⨅ N, possibleSeq O n σ N` — **THE density**: the limit of the
  proportion of level-`N` coefficient classes *consistent with* type `σ`. Outer approximation.
* `decidedDensity O n σ = ⨆ N, decidedSeq O n σ N` — the **certified** density: the limit of
  the proportion of classes on which the type is already *forced*. Inner approximation.

`decidedDensity ≤ genuineDensity` always, with equality exactly under drainage
(`genuineDensity_eq_of_drainage`, `drainage_of_genuineDensity_eq`), which is proved
unconditionally at `n = 1` and `n = 2`.

**`UniformityStatement`** — for each degree `n > 0` and each splitting type `σ` of degree `n`
there is ONE rational function `num/den` such that for EVERY complete DVR `O` with finite
residue field (so: every `ℤ_[p]`, every finite extension of `ℤ_[p]`, every `𝔽_q⟦t⟧`), with
`q = #(residue field)`,

    genuineDensity O n σ = num(q) / den(q).

**`UniformityStatementDecided`** — the same shape over `decidedDensity`. Kept because it is
the unconditional-shape option: it is what a census of decided strata proves directly, with no
drainage input at all. Under drainage the two are equivalent
(`UniformityStatement.ofDecided`, `UniformityStatement.toDecided`).

**Why neither Prop carries a drainage conjunct.** Both are honest as they stand: each
quantifies over a limit that is *proved* to exist and *proved* to be the limit of an explicitly
counted proportion, so neither can be satisfied vacuously or by an abstract model's carried
value. Drainage is not needed to make either statement meaningful — it is what makes them
*equivalent*, and it therefore appears as the hypothesis of the cross-implications rather than
as a conjunct inside either target. (Contrast the old `lean/` corpus's theorem shape, where
drainage sits as conjunct A2 of a conditionality display: there the density itself was only
ever defined as a decided limit, so without drainage the theorem was about the wrong object.
Here the outer limit is a first-class object, so the honest statement is available directly.)

The `∃ (num, den)` stands OUTSIDE the `∀ O`: that ∃-before-∀ order *is* the uniformity claim
(one law, all primes, wild ones included).

## Signature points (signed off by Asvin, 2026-08-13) — PRESERVED VERBATIM BY THE REWIRE

(i) The `∀ O` is over `Type` (universe 0). `ℤ_[p]` and every concrete local ring live there.
(ii) The rational function is evaluated at `(q : ℚ)` and the equality is read in `ℝ` via the
coercion. (iii) `den.eval q ≠ 0` is demanded per-`O`, not globally. (iv) The hypothesis
`σ.degree = n` does real work (`typeOf_degree`): off-degree `σ` are forced to density `0`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-- **THE CAPSTONE TARGET.** One rational function in `q` per `(n, σ)`, valid at every complete
DVR with finite residue field, for THE density `genuineDensity` (the limit of the proportion of
coefficient classes consistent with type `σ`). See the module docstring. -/
def UniformityStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          genuineDensity O n σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

/-- **THE CAPSTONE TARGET, certified form.** Identical to `UniformityStatement` except that it
speaks about the CERTIFIED density `decidedDensity` (the limit of the proportion of classes on
which the type is forced). No drainage anywhere: this is what a census of decided strata
establishes directly, so it keeps the unconditional-shape option open. -/
def UniformityStatementDecided : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          decidedDensity O n σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

/-- **THE CAPSTONE TARGET, `ℤ_[p]` form.** The same law at every prime, with `q = p`, over THE
density. -/
def UniformityStatementPadic : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        den.eval (p : ℚ) ≠ 0 ∧
          genuineDensity ℤ_[p] n σ = ((num.eval (p : ℚ) / den.eval (p : ℚ) : ℚ) : ℝ)

/-- The general target implies the `ℤ_[p]` target: `ℤ_[p]` is an instance of the bundle with
`q = p` (`residueCard_padicInt`). -/
theorem UniformityStatement.toPadic (h : UniformityStatement) : UniformityStatementPadic := by
  intro n hn σ hσ
  obtain ⟨num, den, hden, hlaw⟩ := h n hn σ hσ
  refine ⟨num, den, hden, ?_⟩
  intro p _
  have := hlaw ℤ_[p]
  rwa [residueCard_padicInt p] at this

/-! ## Drainage as a named hypothesis, and the cross-implications -/

/-- **Drainage at degree `n`, uniformly in `O` and `σ`**: the ambiguity gap drains for every
complete DVR with finite residue field and every splitting type. PROVED at `n = 1`
(`drainage_one`, `Gates.lean`) and at `n = 2` (`drainage_two`, `Drainage.lean`); open for
`n ≥ 3`. -/
def DrainageAt (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
    ∀ σ : FactorizationType, UndecidedVanishes O n σ

/-- Under drainage the certified target implies THE target. -/
theorem UniformityStatement.ofDecided (hd : ∀ n, DrainageAt n)
    (h : UniformityStatementDecided) : UniformityStatement := by
  intro n hn σ hσ
  obtain ⟨num, den, hden, hlaw⟩ := h n hn σ hσ
  refine ⟨num, den, hden, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨h1, h2⟩ := hlaw O
  exact ⟨h1, (genuineDensity_eq_of_drainage (hd n O σ)).trans h2⟩

/-- Under drainage THE target implies the certified target. -/
theorem UniformityStatement.toDecided (hd : ∀ n, DrainageAt n)
    (h : UniformityStatement) : UniformityStatementDecided := by
  intro n hn σ hσ
  obtain ⟨num, den, hden, hlaw⟩ := h n hn σ hσ
  refine ⟨num, den, hden, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨h1, h2⟩ := hlaw O
  exact ⟨h1, ((genuineDensity_eq_of_drainage (hd n O σ)).symm).trans h2⟩

/-! ## `Σ_σ R_σ = 1` at general `n` — a named target, not a theorem -/

/-- **`Σ_σ R_σ = 1`, ALL DEGREES — A NAMED TARGET, NOT PROVED.**

For every degree `n > 0`, every complete DVR `O` with finite residue field, and every finite
menu `S` of splitting types that covers degree `n` over `O` (`CoveringMenu`: every monic
degree-`n` polynomial over `O` has its type in `S`), the genuine densities of the menu sum to
exactly `1`.

**Status, stated exactly.** This is NOT a theorem of this repo, and it is not a sorried one
either — it is a `Prop` definition, like the two capstone targets above. What IS proved:

* `≥ 1` holds UNCONDITIONALLY for every covering menu, at every `n`
  (`one_le_sum_genuineDensity`);
* the full equality holds at every `n` GIVEN drainage at every type of the menu
  (`sum_genuineDensity_eq_one_of_drainage`), hence `totalMassOne_of_drainage` below;
* drainage, and therefore the equality, is proved unconditionally at `n = 1` and at `n = 2`
  (`totalMass_one`, `totalMass_two`; the concrete degree-2 instance is
  `sum_three_decidedDensities_eq_one`).

So `TotalMassOne` is *the general-`n` drainage leg in disguise*: drainage implies it outright,
and the frontier that blocks it is exactly the open one (order ≥ 2 of the Okutsu–Montes
tower). Anyone tempted to record `Σ_σ R_σ = 1` as "done" should read this paragraph first. -/
def TotalMassOne : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ S : Finset FactorizationType, CoveringMenu O n S →
        ∑ σ ∈ S, genuineDensity O n σ = 1

/-- **The exact conditionality of `TotalMassOne`**: general-`n` drainage buys it outright. -/
theorem totalMassOne_of_drainage (hd : ∀ n, DrainageAt n) : TotalMassOne := by
  intro n _ O _ _ _ _ _ S hS
  exact sum_genuineDensity_eq_one_of_drainage hS (fun σ _ => hd n O σ)

end Uniformity.Density
