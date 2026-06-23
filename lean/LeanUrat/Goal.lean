/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.L6M4
import LeanUrat.L7
import LeanUrat.CountingModel
import LeanUrat.MontesAxiom
import LeanUrat.Decomposition

/-!
# LeanUrat.Goal — the GOAL THEOREM (`notes/HUMAN_PROOF.md §1, §13`)

> **GOAL THEOREM (Uniform Rationality + Functional Equation), as formalized.** Fix any
> `DensityFoundation F` (the structure recording the cited measure-foundational identities — the
> cluster-tree stratification `decomposition`, the OM-bridge `clusterVolume_eq_measure`,
> nonnegativity). Then for each `n` and each factorization type `σ` of degree `n` there is a single
> rational function `R_σ ∈ ℚ(t)` such that `F.density(n,σ;q) = R_σ(q)` for **every** prime power `q`
> (all `p`, including wild `p ≤ n`), and `R_σ` is palindromic: `R_σ(1/t) = R_σ(t)`.

**HONEST SCOPE (GAP-2 audit, 2026-06-19).** The theorem is `∀ F : DensityFoundation, …`: it is a
statement about EVERY abstract `DensityFoundation`, NOT about a single constructed object identified
with the paper's real `p`-adic factorization-type density `ρ(n,σ;q)`. Two honesty points:

* **Non-vacuity is now witnessed.** `DensityFoundation` previously had ZERO instances; it is now
  proven INHABITED (`Witness.DensityFoundation_nonempty`, an explicit `witnessFoundation` over
  `𝔽₂`), so the `∀ F` quantification is not vacuous over an empty type and the structural fields are
  jointly satisfiable.
* **The witness is NOT the real `ρ`, and no constructed `F` is proven to be.** Identifying some
  `F.density` with the paper's honest `p`-adic Haar volume `ρ` requires `p`-adic Haar integration,
  which **mathlib v4.31.0 lacks** (no Haar measure on `PadicInt`/any DVR). So `goal_theorem` is the
  CONDITIONAL statement "every `DensityFoundation` has uniform-palindromic-rational density"; the
  real-`ρ` instantiation is the un-constructed measure foundation (the genuine wall, see
  `Witness.lean` header). It is honest to read `goal_theorem` as proving the GMN/Igusa-Denef + tame
  machinery yields rationality+palindromy for any object satisfying the recorded measure identities —
  not as already proving the paper's `ρ` is rational (that needs the measure wall crossed).

**Mechanism (unchanged, the genuine derivation under the interface).**
* **Uniform rationality is DERIVED** by `L6M4.density_rational`, a genuine proof that the per-type
  density is rational *because* it is the finite multiplicity-weighted sum
  (`DensityFoundation.decomposition`) of per-**shape** cluster volumes, each rational by
  the correctly-scoped boundary THEOREM `clusterVolume_rational` (itself derived through the proved
  OM engine on the now-`q`-VARYING BB3 count `residualCountFn`, the box volume `T_BB1`, and the
  self-loop pivot — see `PadicMeasure`). The deep machinery is not decorative: the Goal's rationality
  flows through L6M4.
* **Tame palindromy** is the `tame_functionalEquation` axiom (H-tame, paper §5).
* **The palindromy transfer** is PROVED (L7): `L7.tame_to_all_primes` gives that `num/den`
  agrees with the tame representative in `ℚ(t)` on the infinite tame prime set (identity theorem),
  and `L7.isPalindromic_of_agree` transfers the tame functional equation. No `sorry`.

`#print axioms goal_theorem` shows dependence on exactly `propext, Classical.choice, Quot.sound,
AX_cellRecursion, clusterMeasure, descend_size_lt, omCells, tame_functionalEquation` — the cited
interface axioms plus Lean core, with NO `sorryAx` and NO conclusion-axiom. (`clusterVolume_rational`
is now a THEOREM, not an axiom, so it no longer appears; its measure-layer footprint does.) -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Goal

open Polynomial CountingModel MontesAxiom MontesAxiom.MontesData

/-- **GOAL THEOREM (conditional on an abstract `DensityFoundation`).** For ANY `DensityFoundation F`
and each `n` and `σ` of degree `n`, there is a single `num/den ∈ ℚ(t)` (`den ≠ 0`) with
`F.density n σ q = num(q)/den(q)` for every prime power `q > 1` (uniform rationality at all `p`, wild
included; denominator pole-free there), and `num/den` is palindromic in the faithful semantic sense
(`IsPalindromic num den`, i.e. `R(1/x) = R(x)` wherever defined).

**Honest scope (GAP-2):** this is `∀ F`, a statement about every abstract foundation `F` satisfying
the recorded measure identities — NOT a proof that the paper's real `ρ` is rational. `F` ranges over
a type now known INHABITED (`Witness.DensityFoundation_nonempty`), so the statement is non-vacuous;
but no constructed `F.density` is proven equal to the genuine `p`-adic Haar density (that needs the
`p`-adic Haar measure foundation absent from mathlib — the wall). See the module docstring and
`Witness.lean`.

**This is the OLD measure-route theorem.** Its rationality flows through `L6M4.density_rational`,
which consumes `clusterVolume_rational` and hence the OM bridge `B : OMBridge F` (now a SEPARATE
argument, factored out of `DensityFoundation`) and the measure axioms
`clusterMeasure`/`AX_cellRecursion`/`omCells`/`descend_size_lt`. The only-Montes replacement is
`goal_theorem_montes` below, which drops the entire measure route. -/
theorem goal_theorem
    (F : DensityFoundation) (B : OMBridge F) (n : ℕ) (σ : FactorizationType) (hσ : σ.degree = n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q : ℕ, 1 < q → den.eval (q : ℚ) ≠ 0 ∧
        F.density n σ q = num.eval (q : ℚ) / den.eval (q : ℚ)) ∧
      IsPalindromic num den := by
  -- (1) Uniform rationality — DERIVED by L6M4 (decomposition + per-shape clusterVolume_rational):
  obtain ⟨num, den, hden, hall⟩ := L6M4.density_rational F B n σ hσ
  -- (2) Tame palindromic representative (H-tame axiom):
  obtain ⟨tnum, tden, htden, htame, hpalin⟩ := tame_functionalEquation F n σ hσ
  refine ⟨num, den, hden, hall, ?_⟩
  -- (3) L7 palindromy transfer: `num/den` and the palindromic `tnum/tden` agree on the infinite
  -- tame prime set (`hall` vs `htame`), so by the ℚ(t) identity theorem they coincide in `ℚ(t)`
  -- (`L7.tame_to_all_primes`); the tame functional equation then transfers to `num/den`
  -- (`L7.isPalindromic_of_agree`).
  have hagree : num * tden = tnum * den :=
    L7.tame_to_all_primes F n σ hσ num den tnum tden hden htden hall htame
  exact L7.isPalindromic_of_agree num den tnum tden hden htden hagree hpalin

/-! ## The only-Montes GOAL THEOREM (the 2026-06-20 propagation)

`goal_theorem_montes` re-points the GOAL through the count-native (only-Montes) path. Its
**rationality** half flows through `MontesData.countingDensity_isRational` (Lean-core + the
`MontesData` hypothesis bundle only — NO `clusterMeasure`, NO `AX_cellRecursion`, NO `omCells`, NO
`descend_size_lt`), and its **palindromy** half flows through L7 applied to the SAME count-native
rational representative of the genuine counting density (consuming `tame_functionalEquation`, the
separate deferred functional-equation input — paper §5 H-tame — which is NOT Montes and stays).

The DensityFoundation / clusterVolume / clusterMeasure route is DROPPED: this theorem does not call
`L6M4.density_rational` and never touches `PadicMeasure`.

### What the theorem MEANS, and the honest hypotheses

`M.countingDensity σ` is the genuine level-`N` DECIDED limit (the genuine `p`-adic factorization-type
density of the counting model — `CountingModel`/`undecidedVanishes`). The decomposition theorem
`countingDensity_eq_sum_coeff` proves `M.countingDensity σ = ∑_{T ∈ shapesOf σ} C_T(q)`, i.e. it is
the value at this model's residue cardinality `q` of the count-native tree-sum function
`g_σ := fun q' => ∑_T C_T(q')`. `countingDensity_isRational` proves `g_σ` is a single uniform rational
function of `q'` (one `num/den ∈ ℚ(t)` at every `q' > 1`).

So the conclusion below is FAITHFULLY "the genuine counting density is a uniform rational function of
`q` AND palindromic":
* uniform rationality: `∃ num den, den ≠ 0 ∧ ∀ q' > 1, den(q') ≠ 0 ∧ g_σ(q') = num(q')/den(q')`,
  AND `M.countingDensity σ = g_σ(q) = num(q)/den(q)` at THIS model's `q` (the `hq` clause ties the
  single number to the rational function);
* palindromy: `IsPalindromic num den` (the FAITHFUL semantic `R(1/x) = R(x)`), about the SAME
  `num/den` the rationality is about.

**The one honest hypothesis — the measure-wall identification (`hbridge`).** `tame_functionalEquation`
is the cited tame palindromic-rationality input, stated about an abstract `DensityFoundation F`'s
density `F.density n σ`. To transfer its palindromy to the count-native density we must identify the
two densities. That identification — that the abstract foundation's density coincides with the genuine
OM counting tree-sum at every residue cardinality — is the un-constructed `p`-adic measure foundation
(mathlib v4.31.0 has no `p`-adic Haar measure). It is surfaced HONESTLY as the explicit hypothesis
`hbridge : ∀ q' > 1, F.density n σ q' = g_σ(q')`. This is NOT the conclusion (it asserts nothing about
rationality or palindromy — `g_σ` is an arbitrary function here), and NOT an axiom; it is the genuine
interpretive boundary, the same wall flagged in `Decomposition.wiring_assessment`. With it, L7's
identity-theorem transfer carries `tame_functionalEquation`'s palindromy onto `num/den`.

`#print axioms goal_theorem_montes` shows dependence on exactly
`{propext, Classical.choice, Quot.sound, tame_functionalEquation}` — Lean core + the cited tame input;
the `MontesData`/`CountingModel`/`DensityFoundation` content is carried as HYPOTHESES (`M`, `D`, `F`,
`hbridge`), not axioms. There is NO `clusterMeasure`, NO `AX_cellRecursion`, NO `omCells`, NO
`descend_size_lt`, NO `sorryAx`. -/
theorem goal_theorem_montes
    {q n : ℕ} (M : CountingModel q n) (D : MontesAxiom.MontesData q n M)
    (σ : FactorizationType) (F : DensityFoundation) (hσ : σ.degree = n)
    -- The honest measure-wall identification: the abstract tame foundation's density coincides
    -- with the genuine count-native OM tree-sum `g_σ` at every residue cardinality (NOT a
    -- rationality/palindromy claim; see docstring):
    (hbridge : ∀ q' : ℕ, 1 < q' →
      F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.coeff T q') :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      -- (uniform rationality of the count-native density family `g_σ`):
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ D.shapesOf σ, D.coeff T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      -- (the genuine counting density at THIS model's `q` IS that rational function's value):
      (1 < q → M.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ)) ∧
      -- (palindromy R(1/t) = R(t), the FAITHFUL semantic form, about the SAME num/den):
      IsPalindromic num den := by
  -- (1) RATIONALITY — count-native, only-Montes path (NO clusterMeasure / AX_cellRecursion):
  obtain ⟨num, den, hden, hall0⟩ := D.countingDensity_isRational σ
  -- beta-reduce the `IsRationalFn` lambda so the count-native sum appears literally:
  have hall : ∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
      (∑ T ∈ D.shapesOf σ, D.coeff T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ) := hall0
  -- (2) The genuine counting density at this model's `q` is `g_σ(q)` (decomposition theorem), hence
  -- the value of the rational function `num/den` at `q`:
  have hdensq : 1 < q → M.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ) := by
    intro hq
    rw [D.countingDensity_eq_sum_coeff σ]
    exact (hall q hq).2
  -- (3) Tame palindromic representative for `F.density n σ` (the H-tame axiom — stays):
  obtain ⟨tnum, tden, htden, htame, hpalin⟩ := tame_functionalEquation F n σ hσ
  refine ⟨num, den, hden, hall, hdensq, ?_⟩
  -- (4) `num/den` represents `F.density n σ` at every prime power (via `hbridge` + the count-native
  -- rationality), so it agrees in ℚ(t) with the tame palindromic `tnum/tden` (L7 identity theorem),
  -- and the tame functional equation transfers to `num/den` (L7 palindromy transfer):
  have hF : ∀ q' : ℕ, 1 < q' →
      den.eval (q' : ℚ) ≠ 0 ∧ F.density n σ q' = num.eval (q' : ℚ) / den.eval (q' : ℚ) := by
    intro q' hq'
    obtain ⟨hdenq', hgeq⟩ := hall q' hq'
    exact ⟨hdenq', by rw [hbridge q' hq', hgeq]⟩
  have hagree : num * tden = tnum * den :=
    L7.tame_to_all_primes F n σ hσ num den tnum tden hden htden hF htame
  exact L7.isPalindromic_of_agree num den tnum tden hden htden hagree hpalin

end LeanUrat.Goal
