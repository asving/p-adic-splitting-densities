/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.RatFn
import LeanUrat.CountingModel
import LeanUrat.L7

/-!
# LeanUrat.MontesV2 — the abstract-coefficient V2 spine (blueprint W1)

This module is **Wave 1 of `notes/M9_REBASE_BLUEPRINT_2026-07-19.md`** (signed off 2026-07-19):
the ADDITIVE V2 spine that replaces the old `MontesAxiom.MontesData`'s hard-pinned per-node
coefficient shape (`boxMeasure`/`boxHaarEquidist`/`nodeMeasure_boxSum` — the numerically-REFUTED
box-sum semantics, blueprint §1) with an ABSTRACT per-shape coefficient (blueprint D2).

Contents:
* `MontesDataV2` — the minimal abstract-coefficient interface: shape menu + stratum counts +
  partition + an abstract coefficient `C` with rationality and the per-shape counting limit.
* `MontesDataV2.countingDensity_eq_sum_coeff` / `countingDensity_isRational` — the V2 siblings of
  `Decomposition.countingDensity_eq_sum_coeff` / `countingDensity_isRational` (same proofs; the
  abstraction does the work).
* `goal_theorem_montes` / `goal_theorem_via_montes` — the V2 siblings of the OLD
  `Goal.goal_theorem_montes` / `Goal.goal_theorem_via_montes`, verbatim modulo `MontesData →
  MontesDataV2` and `D.coeff → D.C`. Footprint must be Lean core only. (W4b, 2026-07-21: renamed
  from `goal_theorem_montes_v2` / `goal_theorem_via_montes_v2` — they now CARRY the canonical
  names; the old-`MontesData` siblings are retired to
  `quarantine/MontesData_oldSpine_2026-07-21.lean.txt`.)

This was landed as a LEAF module (W1); as of W4a/W4b it is the ONE capstone spine: the W2 real
instance `OM/RealInstanceV2.lean` and the ported `Witness.lean` fire the goal theorems below, and
the old `MontesData` chain is retired.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MontesV2

open Polynomial CountingModel RatFn Filter Topology

/-- **The abstract-coefficient Montes data (blueprint D2) — the V2 replacement of
`MontesAxiom.MontesData`.**

The old `MontesData` froze the ENGINE INTERNALS into the interface: its
`boxMeasure`/`boxHaarEquidist`/`nodeMeasure_boxSum` fields pinned every instance to the per-node
box-sum coefficient shape, which the 2026-07 numeric campaign REFUTED (blueprint §1, defects
D1–D6). The Goal layer never consumed that shape — it only ever consumed the three derived facts
(the menu-sum decomposition, its rationality, the value tie). `MontesDataV2` therefore carries the
per-shape coefficient ABSTRACTLY: a function `C` together with (i) its uniform rationality and
(ii) the per-shape counting limit `stratumCount T N / q^{nN} → C T q`, plus the level-`N`
partition of the decided count over the shape menu.

⚠ **Statement-fence note (blueprint D2, verbatim intent).** This interface is DELIBERATELY WEAK —
weaker than the old `MontesData`: it demands no per-node recursion shape, so it is satisfiable by
degenerate instances (e.g. an empty menu with `C ≡ 0`). That is by design: the semantics are pinned
at the INSTANCE, not the interface — the corrected real instance sets `C := omCount` (W2), and
non-vacuity/σ-separation are enforced against the REAL instance by the W3 gates
(`gate_rootCount_inert2`-style positivity, the O1-reversal σ-separation examples), NOT here.
Interface-weakening is how vacuity crept in before, so this weakening is flagged for audit
explicitly; any consumer claiming non-vacuity must cite the instance gates, never this structure. -/
structure MontesDataV2 (q n : ℕ) (M : CountingModel q n) where
  /-- For each factorization type `σ`, the finite menu of cluster-tree shapes `T` attached to `σ`
  (the shapes whose strata make up the level-`N` decided count of type `σ`). -/
  shapesOf : FactorizationType → Finset ClusterShape
  /-- The level-`N` stratum count `# S_T^{(N)}` of a shape `T` (the count of level-`N` decided
  monic cosets realizing the combinatorial shape `T`). A `ℚ`-valued integer count. -/
  stratumCount : ClusterShape → ℕ → ℚ
  /-- **PARTITION (`ax:partition`).** At each level `N`, the decided count of type `σ` is the
  finite sum over the σ-menu of the per-shape stratum counts (each decided coset realizes exactly
  one shape). -/
  partition : ∀ (σ : FactorizationType) (N : ℕ),
    M.decidedCount σ N = ∑ T ∈ shapesOf σ, stratumCount T N
  /-- **The abstract per-shape coefficient `C T q'`** — the limiting normalized stratum measure of
  shape `T`, as a function of the residue cardinality `q'`. Carried abstractly (no per-node
  recursion shape is demanded — blueprint D2); the corrected real instance sets `C := omCount`. -/
  C : ClusterShape → ℕ → ℚ
  /-- **Uniform rationality of the abstract coefficient**: each `C T` is one `num/den ∈ ℚ(t)`,
  denominator nonvanishing at every `q' > 1`, representing `C T q'` there. (For the real instance
  this is `OMCountV2.omCount_isRational`.) -/
  C_isRational : ∀ T : ClusterShape, IsRationalFn (fun q' => C T q')
  /-- **The per-shape counting limit (the value tie).** For every shape on some type's menu, the
  normalized level-`N` stratum count converges to the abstract coefficient evaluated at THIS
  model's residue cardinality `q`. (For the real instance these are the `hNodeLimit` legs.) -/
  stratum_tendsto_C : ∀ (σ : FactorizationType), ∀ T ∈ shapesOf σ,
    Filter.Tendsto (fun N => stratumCount T N / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds (C T q))

/-- Finite `Finset`-indexed sums of uniform rational functions are uniform rational functions.

NOTE (deliberate duplication): this is a local re-proof of `OM.Order0.isRationalFn_finsetSum`
(`OM/Order0Capstone.lean`). Importing that module would drag the heavy `OM/RealInstance` chain
into this deliberately-light leaf, so the 10-line general closure lemma is re-proved here instead. -/
theorem isRationalFn_finsetSum {α : Type*} (s : Finset α) (f : α → ℕ → ℚ)
    (h : ∀ a ∈ s, IsRationalFn (f a)) :
    IsRationalFn (fun q => ∑ a ∈ s, f a q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isRationalFn_const 0
  | insert a s ha ih =>
      have hfa : IsRationalFn (f a) := h a (Finset.mem_insert_self a s)
      have hs : IsRationalFn (fun q => ∑ b ∈ s, f b q) :=
        ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
      have := isRationalFn_add hfa hs
      simpa [Finset.sum_insert ha] using this

namespace MontesDataV2

variable {q n : ℕ} {M : CountingModel q n} (D : MontesDataV2 q n M)

/-- **The V2 DECOMPOSITION THEOREM: `countingDensity σ = ∑_{T ∈ shapesOf σ} C T q`** — the sibling
of `Decomposition.countingDensity_eq_sum_coeff` over `MontesDataV2`. The genuine DECIDED-LIMIT
density is the finite menu-sum of the abstract per-shape coefficients at this model's `q`. PROVED
modulo the `MontesDataV2` hypotheses:
* at each `N`, `decidedMeasure σ N = ∑_T (stratumCount T N / q^{nN})` (`partition` over the box);
* each summand `→ C T q` (`stratum_tendsto_C`), so the FINITE sum tends to `∑_T C T q`;
* but `decidedMeasure σ N → countingDensity σ` (`CountingModel.density_isLimit`);
* limits in `ℚ` are unique.
No rationality is used. -/
theorem countingDensity_eq_sum_coeff (σ : FactorizationType) :
    M.countingDensity σ = ∑ T ∈ D.shapesOf σ, D.C T q := by
  -- (1) at each level `N`, the decided measure is the menu-sum of normalized stratum counts
  -- (`partition`, divided by the box `q^{nN}`):
  have hN : (fun N => M.decidedMeasure σ N)
      = (fun N => ∑ T ∈ D.shapesOf σ, D.stratumCount T N / (q : ℚ) ^ (n * N)) := by
    funext N
    unfold CountingModel.decidedMeasure
    rw [D.partition σ N, Finset.sum_div]
  -- (2) each normalized summand tends to `C T q` (`stratum_tendsto_C`), so the finite sum tends
  -- to the menu-sum of coefficients:
  have hsum_tendsto :
      Tendsto (fun N => ∑ T ∈ D.shapesOf σ, D.stratumCount T N / (q : ℚ) ^ (n * N)) atTop
        (nhds (∑ T ∈ D.shapesOf σ, D.C T q)) :=
    tendsto_finsetSum (D.shapesOf σ) (fun T hT => D.stratum_tendsto_C σ T hT)
  -- (3) but the decided measures tend to `countingDensity σ` (`density_isLimit`); limits are unique:
  have hdec_tendsto :
      Tendsto (fun N => M.decidedMeasure σ N) atTop (nhds (∑ T ∈ D.shapesOf σ, D.C T q)) := by
    rw [hN]; exact hsum_tendsto
  exact tendsto_nhds_unique (M.density_isLimit σ) hdec_tendsto

/-- **The V2 RATIONALITY THEOREM: the menu-sum density function is a uniform rational function of
`q'`** — the sibling of `Decomposition.countingDensity_isRational` over `MontesDataV2`. Each
abstract coefficient is rational (`C_isRational`, an interface field here — for the real instance a
THEOREM, `omCount_isRational`), and `IsRationalFn` is closed under finite `Finset` sums.

Honest scope: this is rationality of the FUNCTION `q' ↦ ∑_T C T q'`; the decomposition theorem
ties `countingDensity σ` (at this `M`'s `q`) to that function's value at `q`. -/
theorem countingDensity_isRational (σ : FactorizationType) :
    IsRationalFn (fun q' => ∑ T ∈ D.shapesOf σ, D.C T q') :=
  isRationalFn_finsetSum (D.shapesOf σ) (fun T q' => D.C T q') (fun T _ => D.C_isRational T)

end MontesDataV2

/-- **The V2 only-Montes GOAL THEOREM — the sibling of the OLD `Goal.goal_theorem_montes` over
`MontesDataV2` (blueprint W1, verbatim modulo `MontesData → MontesDataV2`, `D.coeff → D.C`;
W4b 2026-07-21: renamed from `goal_theorem_montes_v2`, now carrying the canonical name — the
old-`MontesData` sibling is retired to `quarantine/MontesData_oldSpine_2026-07-21.lean.txt`).**

For a counting model `M`, abstract-coefficient Montes data `D`, a degree-`n` type `σ`, and an
abstract foundation `F`, GIVEN (i) the honest measure-wall identification `hbridge` (the abstract
foundation's density coincides with the count-native menu-sum `g_σ := q' ↦ ∑_T C T q'` at every
`q' > 1` — NOT a rationality or palindromy claim) and (ii) the tame functional equation `htameFE`
(explicit HYPOTHESIS per the U1 fix — the old global axiom over a free `F` was FALSE-AS-STATED),
there is a single `num/den ∈ ℚ(t)` with: `den ≠ 0`; uniform rationality of `g_σ` at every
`q' > 1`; the genuine counting density at THIS model's `q` equal to `num(q)/den(q)`; and
`IsPalindromic num den` (the faithful semantic `R(1/x) = R(x)`).

The conclusion clauses are IDENTICAL to the old `Goal.goal_theorem_montes`'s; only the hypothesis bundle changed
(abstract `C` in place of the refuted box-sum `coeff`). Rationality flows through
`MontesDataV2.countingDensity_isRational`, the value tie through
`MontesDataV2.countingDensity_eq_sum_coeff`, palindromy through L7's identity-theorem transfer
(`L7.tame_to_all_primes` + `L7.isPalindromic_of_agree`) — all against the SAME `num/den`.

`#print axioms` must show Lean core ONLY (`propext, Classical.choice, Quot.sound` — see the
`AxCheck` section below): every Montes/counting/tame input is a HYPOTHESIS, never an axiom. -/
theorem goal_theorem_montes
    {q n : ℕ} (M : CountingModel q n) (D : MontesDataV2 q n M)
    (σ : FactorizationType) (F : DensityFoundation) (hσ : σ.degree = n)
    -- The honest measure-wall identification: the abstract tame foundation's density coincides
    -- with the count-native menu-sum `g_σ` at every residue cardinality (NOT a
    -- rationality/palindromy claim; see docstring):
    (hbridge : ∀ q' : ℕ, 1 < q' →
      F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.C T q')
    -- (U1 fix) the tame functional equation is an explicit HYPOTHESIS (the old global axiom over
    -- a free `F` was FALSE-AS-STATED; see `Interface.TameFunctionalEquation`):
    (htameFE : TameFunctionalEquation F n σ) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      -- (uniform rationality of the count-native density family `g_σ`):
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ D.shapesOf σ, D.C T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      -- (the genuine counting density at THIS model's `q` IS that rational function's value):
      (1 < q → M.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ)) ∧
      -- (palindromy R(1/t) = R(t), the FAITHFUL semantic form, about the SAME num/den):
      IsPalindromic num den := by
  -- (1) RATIONALITY — count-native, abstract-coefficient path:
  obtain ⟨num, den, hden, hall0⟩ := D.countingDensity_isRational σ
  -- beta-reduce the `IsRationalFn` lambda so the count-native sum appears literally:
  have hall : ∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
      (∑ T ∈ D.shapesOf σ, D.C T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ) := hall0
  -- (2) The genuine counting density at this model's `q` is `g_σ(q)` (V2 decomposition theorem),
  -- hence the value of the rational function `num/den` at `q`:
  have hdensq : 1 < q → M.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ) := by
    intro hq
    rw [D.countingDensity_eq_sum_coeff σ]
    exact (hall q hq).2
  -- (3) Tame palindromic representative for `F.density n σ` (the H-tame hypothesis):
  obtain ⟨tnum, tden, htden, htame, hpalin⟩ := htameFE
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

/-- **The V2 re-based uniformity capstone — the sibling of the OLD `Goal.goal_theorem_via_montes`
over `MontesDataV2` (blueprint W1, verbatim modulo names; W4b 2026-07-21: renamed from
`goal_theorem_via_montes_v2`, now carrying the canonical name — the old-`MontesData` sibling is
retired to `quarantine/MontesData_oldSpine_2026-07-21.lean.txt`).** Produces the `F.density`-shaped conclusion
(uniform rationality of the per-type density + palindromy), routing rationality through the
count-native abstract-coefficient pair `(M, D)` plus the honest measure-wall identification
`hbridge`, with the tame functional equation as the explicit hypothesis `htameFE`.

Proof: obtain the count-native `num/den` (rationality + palindromy) from `goal_theorem_montes`,
drop its value clause, and rewrite the count-native rationality onto `F.density` via `hbridge`.

`#print axioms` must show Lean core ONLY (see the `AxCheck` section below). -/
theorem goal_theorem_via_montes
    {q n : ℕ} (M : CountingModel q n) (D : MontesDataV2 q n M)
    (F : DensityFoundation) (σ : FactorizationType) (hσ : σ.degree = n)
    (hbridge : ∀ q' : ℕ, 1 < q' →
      F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.C T q')
    -- (U1 fix) the tame functional equation is an explicit HYPOTHESIS (the old global axiom over
    -- a free `F` was FALSE-AS-STATED; see `Interface.TameFunctionalEquation`):
    (htameFE : TameFunctionalEquation F n σ) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        F.density n σ q' = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      IsPalindromic num den := by
  obtain ⟨num, den, hden, hgrat, _hval, hpalin⟩ :=
    goal_theorem_montes M D σ F hσ hbridge htameFE
  refine ⟨num, den, hden, fun q' hq' => ?_, hpalin⟩
  obtain ⟨hdenq', hgeq⟩ := hgrat q' hq'
  exact ⟨hdenq', by rw [hbridge q' hq', hgeq]⟩

end LeanUrat.MontesV2

section AxCheck

-- The V2 spine (blueprint W1 gate): every footprint below MUST be Lean core only
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
#print axioms LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff
#print axioms LeanUrat.MontesV2.MontesDataV2.countingDensity_isRational
#print axioms LeanUrat.MontesV2.goal_theorem_montes
#print axioms LeanUrat.MontesV2.goal_theorem_via_montes

end AxCheck
