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
-- (W4b, 2026-07-21) `import LeanUrat.MontesAxiom` / `import LeanUrat.Decomposition` removed with
-- the old-`MontesData` Goal bridge (`goal_theorem_montes`/`goal_theorem_via_montes`), RETIRED to
-- `quarantine/MontesData_oldSpine_2026-07-21.lean.txt`; the V2 siblings carrying those names live
-- in `LeanUrat/MontesV2.lean`.

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
* **Tame palindromy** is the `TameFunctionalEquation F n σ` HYPOTHESIS (H-tame, paper §5; the old
  global axiom over a free `F` was FALSE-AS-STATED — see `Interface.TameFunctionalEquation`).
* **The palindromy transfer** is PROVED (L7): `L7.tame_to_all_primes` gives that `num/den`
  agrees with the tame representative in `ℚ(t)` on the infinite tame prime set (identity theorem),
  and `L7.isPalindromic_of_agree` transfers the tame functional equation. No `sorry`.

`#print axioms goal_theorem` shows dependence on exactly `propext, Classical.choice, Quot.sound,
AX_cellRecursion, clusterMeasure, descend_size_lt, omCells` — the cited interface axioms plus Lean
core, with NO `sorryAx` and NO conclusion-axiom. (`clusterVolume_rational` is now a THEOREM, not an
axiom, so it no longer appears; its measure-layer footprint does. `tame_functionalEquation` is GONE
from the footprint: the tame input is the explicit HYPOTHESIS `htameFE` — U1 fix, 2026-07-02.) -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Goal

open Polynomial CountingModel

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
`MontesV2.goal_theorem_montes` (`LeanUrat/MontesV2.lean`), which drops the entire measure route
(W4b, 2026-07-21: the old-`MontesData` sibling that lived below is retired to
`quarantine/MontesData_oldSpine_2026-07-21.lean.txt`). -/
theorem goal_theorem
    (F : DensityFoundation) (B : OMBridge F) (n : ℕ) (σ : FactorizationType) (hσ : σ.degree = n)
    -- (U1 fix) the tame functional equation is now an explicit HYPOTHESIS (the old global axiom over
    -- a free `F` was FALSE-AS-STATED; see `Interface.TameFunctionalEquation`):
    (htameFE : TameFunctionalEquation F n σ) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q : ℕ, 1 < q → den.eval (q : ℚ) ≠ 0 ∧
        F.density n σ q = num.eval (q : ℚ) / den.eval (q : ℚ)) ∧
      IsPalindromic num den := by
  -- (1) Uniform rationality — DERIVED by L6M4 (decomposition + per-shape clusterVolume_rational):
  obtain ⟨num, den, hden, hall⟩ := L6M4.density_rational F B n σ hσ
  -- (2) Tame palindromic representative (H-tame, the hypothesis):
  obtain ⟨tnum, tden, htden, htame, hpalin⟩ := htameFE
  refine ⟨num, den, hden, hall, ?_⟩
  -- (3) L7 palindromy transfer: `num/den` and the palindromic `tnum/tden` agree on the infinite
  -- tame prime set (`hall` vs `htame`), so by the ℚ(t) identity theorem they coincide in `ℚ(t)`
  -- (`L7.tame_to_all_primes`); the tame functional equation then transfers to `num/den`
  -- (`L7.isPalindromic_of_agree`).
  have hagree : num * tden = tnum * den :=
    L7.tame_to_all_primes F n σ hσ num den tnum tden hden htden hall htame
  exact L7.isPalindromic_of_agree num den tnum tden hden htden hagree hpalin

/-! ## (RETIRED, W4b 2026-07-21) the old-`MontesData` only-Montes bridge

`goal_theorem_montes` / `goal_theorem_via_montes` — the Goal-layer siblings typed over the old
`MontesAxiom.MontesData` — formerly lived here. They are RETIRED VERBATIM to
`quarantine/MontesData_oldSpine_2026-07-21.lean.txt` (blueprint
`notes/M9_REBASE_BLUEPRINT_2026-07-19.md`, W4b): after W4a the old spine had no non-quarantined
instance left. Their V2 replacements carry the SAME canonical names over the abstract-coefficient
`MontesDataV2`: `LeanUrat.MontesV2.goal_theorem_montes` / `goal_theorem_via_montes`
(`LeanUrat/MontesV2.lean`, bodies verbatim modulo `MontesData → MontesDataV2`, `D.coeff → D.C`;
fired by the real capstone `OM.RealInstanceV2.montes_unconditional` and the trivial witness
`Witness.montes_full_instance`). -/

end LeanUrat.Goal
