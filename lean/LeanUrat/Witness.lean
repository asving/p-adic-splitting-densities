/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.CountingModel
import LeanUrat.MontesAxiom
-- (W4b, 2026-07-21) `import LeanUrat.Decomposition` / `import LeanUrat.Goal` replaced by
-- `import LeanUrat.MontesV2`: the old-`MontesData` witness members are RETIRED to
-- `quarantine/MontesData_oldSpine_2026-07-21.lean.txt` and PORTED below onto the V2 spine
-- (`MontesDataV2`; the goal theorem fired is now `MontesV2.goal_theorem_montes`).
import LeanUrat.MontesV2

/-!
# LeanUrat.Witness — non-vacuity of the `DensityFoundation` interface (GAP-2 fix)

`Goal.goal_theorem` and `Interface.clusterVolume_rational` are stated `∀ F : DensityFoundation, …`.
Before this file, `DensityFoundation` had **zero** instances, so an `∀ F` statement was honest about
its hypotheses but had **never been witnessed to be non-vacuous** (no concrete `F` was known to
exist). This file constructs one explicit `witnessFoundation : DensityFoundation`, proving the
interface is **inhabited** (`DensityFoundation_nonempty`).

## HONEST SCOPE — what this does and does NOT establish (GAP-2)

* **It DOES** establish non-vacuity: the `DensityFoundation` hypothesis-bundle is jointly
  satisfiable (its equational fields — `decomposition`, `clusterVolume_eq_measure`, `density_nonneg` —
  are mutually consistent), so the `∀ F` theorems are not vacuously quantifying over an empty type,
  and the structural OM-bridge fields can be simultaneously met. In particular `goal_theorem` and
  `clusterVolume_rational` have at least one genuine instance to which they apply.

* **It does NOT** establish that any constructed `F.density` is the REAL `p`-adic factorization-type
  density `ρ(n,σ;q)` of the paper. The witness's `density` is the trivial `0` (with `shapes := ∅`),
  chosen only to satisfy the structural identities; it is NOT an honest Haar volume. Constructing a
  `DensityFoundation` whose `density` IS the paper's `ρ` requires `p`-adic Haar integration, which
  **mathlib v4.31.0 lacks** (no `MeasureSpace`/`haarMeasure` on `PadicInt`/any DVR; grep of
  `Mathlib/MeasureTheory` for `Padic` is empty). That is the genuine, un-crossed measure wall.

So the honest reading of `goal_theorem` is: *for every abstract `DensityFoundation` `F` (a structure
recording the cited measure-foundational identities), `F.density` is a uniform palindromic rational
function of `q`; such `F` exist; but identifying a specific `F` with the paper's `ρ` is the
un-constructed `p`-adic-Haar measure foundation.* `Goal.goal_theorem`'s docstring is relabeled to
state exactly this. -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.Witness

open Polynomial LeanUrat LeanUrat.PadicMeasure

/-- A minimal concrete `OMShape` over `𝔽₂ = ZMod 2` (a finite field), used to anchor the witness
`DensityFoundation`'s OM-bridge `decode`. All A0 ties are met definitionally: `residueDeg = 1 =
finrank (ZMod 2) (ZMod 2)`, `residual := 1`, `residualDeg := residual.natDegree`, empty Newton
polygon. This is a genuine inhabitant of `OMShape`, demonstrating that the A0-faithful shape type is
itself inhabited. -/
noncomputable def minimalOMShape : OMShape := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact
    { size := 0
      order := 0
      Fr := ZMod 2
      baseField := ZMod 2
      residueDeg := 1
      hResidueDeg := (Module.finrank_self (ZMod 2)).symm
      polygon := { width := 0, ceilHeights := Fin.elim0, isVertex := Fin.elim0 }
      residual := 1
      residualDeg := (1 : Polynomial (ZMod 2)).natDegree
      hResidualDeg := rfl }

/-- **The witness `DensityFoundation` (non-vacuity, GAP-2).** Trivial data — `shapes := ∅`,
`density := 0`, `clusterVolume := clusterMeasure minimalOMShape` — chosen so every structural field
holds:

* `decomposition`: both sides are `0` (`∑` over `∅` is `0`, and `density := 0`);
* `density_nonneg`: `0 ≤ 0`.

The OM bridge (`decode`/`clusterVolume_eq_measure`) was FACTORED OUT of `DensityFoundation` into the
separate `OMBridge` structure (2026-06-20); the witness bridge is `witnessOMBridge` below. So the
(now measure-free) `witnessFoundation` no longer references `PadicMeasure.clusterMeasure` in its
structural fields — though its `clusterVolume` field still picks the concrete `clusterMeasure
minimalOMShape` value so the bridge is satisfiable.

This proves the interface is INHABITED; it does NOT make `density` the paper's `ρ` (see file header). -/
noncomputable def witnessFoundation : DensityFoundation where
  density := fun _ _ _ => 0
  clusterVolume := fun _ q => PadicMeasure.clusterMeasure minimalOMShape q
  shapes := fun _ _ => ∅
  multiplicity := fun _ => 0
  decomposition := by
    intro n σ _ q _
    simp
  density_nonneg := by intro n σ q; exact le_refl 0

/-- **The witness `OMBridge` for `witnessFoundation` (non-vacuity of the SEPARATED OM bridge).**
`decode := fun _ => minimalOMShape`, and `clusterVolume_eq_measure` is `rfl` because
`witnessFoundation.clusterVolume T q = clusterMeasure minimalOMShape q = clusterMeasure (decode T) q`.
This shows the factored-out `OMBridge` structure is itself inhabited over the witness, so the OLD
measure-route theorems (`clusterVolume_rational`, `goal_theorem`) — which now take `(F, B : OMBridge F)`
— are non-vacuous. -/
noncomputable def witnessOMBridge : OMBridge witnessFoundation where
  decode := fun _ => minimalOMShape
  clusterVolume_eq_measure := by intro T q; rfl

/-- **GAP-2 non-vacuity: `DensityFoundation` is inhabited.** Hence the genuine `∀ F : DensityFoundation`
theorems (`clusterVolume_rational`, `goal_theorem`) are not vacuous over an empty type. The OM bridge
is separately inhabited (`witnessOMBridge`), so the OLD measure-route theorems' `(F, B)` hypotheses are
jointly satisfiable. (This does NOT identify the witness `density` with the real `ρ` — see file header
/ `Goal.goal_theorem`'s relabeled docstring.)

**NOTE (2026-06-21; V2-ported in W4b, 2026-07-21):** this inhabits ONLY `DensityFoundation`. That
is NOT sufficient for `MontesV2.goal_theorem_montes`, whose coupled bundle `(M, D, F, hbridge)`
ties `F` to a `MontesDataV2 D` — and `witnessFoundation` (density ≡ 0) is incompatible with any
non-trivial `D`. The full-bundle non-vacuity of `goal_theorem_montes` is established separately by
`montes_bundle_nonempty` / `montes_full_instance` below (a genuine coupled
`CountingModel`/`MontesDataV2`/foundation witness with non-trivial density `1`). -/
theorem DensityFoundation_nonempty : Nonempty DensityFoundation :=
  ⟨witnessFoundation⟩

/-- **The separated OM bridge is inhabited** (over the witness foundation). -/
theorem OMBridge_nonempty : Nonempty (OMBridge witnessFoundation) :=
  ⟨witnessOMBridge⟩

/-! ## Non-vacuity of the FULL `goal_theorem_montes` bundle (Witness-nit fix, 2026-06-21;
PORTED onto the V2 spine in W4b, 2026-07-21)

The audit flagged that `DensityFoundation_nonempty` only inhabits `DensityFoundation`, which is
NECESSARY but NOT SUFFICIENT for `MontesV2.goal_theorem_montes`: that theorem takes the coupled
bundle `(M : CountingModel q n) (D : MontesDataV2 q n M) (σ) (F : DensityFoundation) (hσ)
(hbridge)`, where `hbridge : ∀ q' > 1, F.density n σ q' = ∑_T D.C T q'` COUPLES `F` to `D`. The
trivial `witnessFoundation` (density ≡ 0) is in fact INCOMPATIBLE with any non-trivial `D` (it
would force `0 = ∑_T D.C T q'`). So we construct a genuine coupled witness — a complete
`CountingModel`, `MontesDataV2`, and a foundation whose density IS the count-native tree-sum — and
prove the whole bundle is JOINTLY SATISFIABLE with a NON-TRIVIAL density `g ≡ 1`.

This crosses NO measure wall: `trivM` is a trivial degree-0 model (`q=2, n=0`), not the paper's
`p`-adic `ρ`; that honest limitation stands. The point is only that `goal_theorem_montes`'s hypothesis
bundle has a genuine sorry-free inhabitant (so the theorem is demonstrably non-vacuous).

**W4b port note.** The old-`MontesData` members (`trivD`, the old `trivF`/`montes_bundle_nonempty`/
`trivD_sum_coeff_eq_one`/`trivF_tame`/`montes_full_instance`) are retired VERBATIM to
`quarantine/MontesData_oldSpine_2026-07-21.lean.txt` and re-established here over `MontesDataV2`
with the SAME names and the SAME semantic content: `trivD2.C` is pinned to the SAME pure-counting
value the old witness carried (`clusterCount trivCells …`, = `1` on `trivShape`, `0` off it —
blueprint D2: "the old `clusterCount` instance remains expressible (for the Witness)"), so the
non-vacuity certificate is unchanged, only the spine it certifies is the V2 one. The old minimal
box-wise axiom fields (`boxHaarEquidist`/`nodeMeasure_boxSum`) no longer exist on the V2 interface;
their witness content survives as the `stratum_tendsto_C` constant-sequence discharge. -/

open LeanUrat.CountingModel LeanUrat.MontesAxiom

/-- The degree-`0` factorization type `σ₀` (empty multiset of `(e,f)` pairs), `σ₀.degree = 0`. -/
def trivType : FactorizationType := ⟨0⟩

/-- A single leaf cluster shape `T₀` (empty decorated OM tree, no cell payload). -/
def trivShape : ClusterShape := ⟨[], []⟩

/-- The single trivial leaf cell: residual degree `dS = 1`, residue-extension `δ = 0`, an empty
(width-`0`) Newton polygon, no descent children. Then `countCellCoeff` over it is `(2^0)^0 ·
bb1Value (width-0) = 1·1 = 1` and `countPivot 0 = 1`, so `clusterCount = 1`. -/
def trivCell : CountCell :=
  { dS := 1, δ := 0, polygon := { width := 0, ceilHeights := Fin.elim0, isVertex := Fin.elim0 },
    children := [] }

/-- The trivial counting model over `q = 2`, `n = 0`. Box count `2^{0·N} = 1`; the single degree-`0`
type `σ₀` is fully decided at every level (`decidedCount = 1`), nothing undecided. -/
noncomputable def trivM : CountingModel 2 0 where
  hq := le_refl 2
  decidedCount := fun σ _ => if σ = trivType then 1 else 0
  undecidedCount := fun _ => 0
  decidedCount_nonneg := by intro σ N; by_cases h : σ = trivType <;> simp [h]
  undecidedCount_nonneg := by intro N; exact le_refl 0
  typeMenu := {trivType}
  typeMenu_degree := by
    intro σ hσ; rw [Finset.mem_singleton] at hσ; subst hσ; rfl
  decidedCount_off_menu := by
    intro σ N hσ
    rw [Finset.mem_singleton] at hσ
    simp [hσ]
  box_partition := by
    intro N; simp [trivType]
  decided_mono := by
    intro σ a b _; simp
  densityVal := fun σ => if σ = trivType then 1 else 0
  decided_tendsto := by
    intro σ
    simp only [Nat.zero_mul, pow_zero, div_one]
    exact tendsto_const_nhds
  upper_tail := by
    intro σ N K _
    simp only [Nat.zero_mul, pow_zero, div_one]
    by_cases h : σ = trivType <;> simp [h]

/-- The single-cell list of a shape `T`: the leaf cell `[trivCell]` exactly on `trivShape`, empty
otherwise. So `clusterCount T 2 = 1` on `trivShape` (one leaf box of measure `1`, pivot `1`) and `0`
off it, matching `stratumCount`. -/
-- `noncomputable` because the enriched `ClusterShape` carries a classical (`noncomputable`)
-- `DecidableEq` (decision 2b: the recursive, polygon-carrying shape has no derivable structural
-- instance); the `if T = trivShape` decision is the only computable shape-equality consumer, so this
-- is the single ripple of that instance change. Its uses are proofs/`rfl`/`MontesData` fields, all of
-- which are insensitive to computability.
noncomputable def trivCells (T : ClusterShape) : List CountCell := if T = trivShape then [trivCell] else []

/-- Strict-descent for `trivCells`: every cell is the childless `trivCell`, so the child membership is
vacuous. Defined standalone so the structure's `cells_descend` field and the `nodeMeasure_boxSum`
proof share the SAME proof term. -/
theorem trivCells_descend :
    ∀ (T : ClusterShape), ∀ c ∈ trivCells T, ∀ ch ∈ c.children, (fun _ : ClusterShape => 0) ch
      < (fun _ : ClusterShape => 0) T := by
  intro T c hc ch hch
  -- every cell of `trivCells T` is `trivCell`, which has no children, so `hch` is impossible
  have hc' : c = trivCell := by
    by_cases h : T = trivShape
    · have : trivCells T = [trivCell] := by rw [trivCells, if_pos h]
      rw [this, List.mem_singleton] at hc; exact hc
    · have : trivCells T = [] := by rw [trivCells, if_neg h]
      rw [this] at hc; simp at hc
  subst hc'
  simp [trivCell] at hch

/-- `countCellCoeff trivCell q = 1` for every `q` (the box-volume `bb1Value` of the empty width-0
polygon is `1`, the residual count `(q^0)^{1-1} = 1`). PROVED by `simp` arithmetic. -/
theorem countCellCoeff_trivCell (q : ℕ) : countCellCoeff trivCell q = 1 := by
  simp [countCellCoeff, trivCell, L4.bb1Value, L4.newtonVertexCount, L4.newtonExponent]

/-- `countPivot 0 q = 1` (a leaf node, `0 < 2`). -/
theorem countPivot_zero (q : ℕ) : countPivot 0 q = 1 := by
  simp [countPivot]

/-- `clusterCount` of the witness equals `1` on `trivShape`, `0` elsewhere (matching `stratumCount`).
PROVED from `clusterCount_rec` + `countCellCoeff_trivCell`. -/
theorem clusterCount_trivCells (hdesc) (T : ClusterShape) (q : ℕ) :
    clusterCount trivCells (fun _ => 0) hdesc T q = (if T = trivShape then 1 else 0) := by
  rw [clusterCount_rec]
  by_cases h : T = trivShape
  · have hcells : trivCells T = [trivCell] := by rw [trivCells, if_pos h]
    have hch : trivCell.children = [] := rfl
    rw [hcells, if_pos h, countPivot_zero]
    simp only [List.map_cons, List.map_nil, hch, List.prod_nil, List.sum_cons, List.sum_nil,
      mul_one, add_zero, countCellCoeff_trivCell, div_one]
  · have hcells : trivCells T = [] := by rw [trivCells, if_neg h]
    rw [hcells, if_neg h]
    simp only [List.map_nil, List.sum_nil, zero_div]

/-- **The trivial `MontesDataV2` over `trivM` — the W4b V2 port of the old `trivD`** (old text in
`quarantine/MontesData_oldSpine_2026-07-21.lean.txt`): the single shape `T₀` of type `σ₀`, with the
abstract per-shape coefficient pinned to the SAME pure-counting value the old witness carried,
`C := clusterCount trivCells (fun _ => 0) trivCells_descend` (blueprint D2: the old `clusterCount`
instance remains expressible — instantiation, not statement, carries the semantics). By
`clusterCount_trivCells`, `C T q' = 1` on `trivShape` and `0` elsewhere, so:
* `C_isRational` is constant-function rationality (`RatFn.isRationalFn_const`);
* `stratum_tendsto_C` is the constant-sequence limit `stratumCount T N / 2^{0·N} = C T 2` — exactly
  the limit the old `nodeMeasure_boxSum` discharge encoded (the old box-wise fields
  `boxMeasure`/`boxHaarEquidist`/`nodeMeasure_boxSum` do not exist on the V2 interface). -/
noncomputable def trivD2 : MontesV2.MontesDataV2 2 0 trivM where
  shapesOf := fun σ => if σ = trivType then {trivShape} else ∅
  stratumCount := fun T N => if T = trivShape then 1 else 0
  partition := by
    intro σ N
    by_cases h : σ = trivType
    · subst h
      simp only [trivM, if_true, Finset.sum_singleton]
    · simp only [trivM, if_neg h, Finset.sum_empty]
  C := fun T q' => clusterCount trivCells (fun _ => 0) trivCells_descend T q'
  C_isRational := by
    intro T
    have h : (fun q' : ℕ => clusterCount trivCells (fun _ => 0) trivCells_descend T q')
        = fun _ : ℕ => (if T = trivShape then (1 : ℚ) else 0) := by
      funext q'
      exact clusterCount_trivCells trivCells_descend T q'
    rw [h]
    exact RatFn.isRationalFn_const _
  stratum_tendsto_C := by
    intro σ T hT
    have hC : clusterCount trivCells (fun _ => 0) trivCells_descend T 2
        = (if T = trivShape then (1 : ℚ) else 0) := clusterCount_trivCells trivCells_descend T 2
    simp only [Nat.zero_mul, pow_zero, div_one, hC]
    exact tendsto_const_nhds

/-- The coupled witness foundation (W4b: re-expressed over `trivD2`; the conveyed density values
are UNCHANGED — `trivD2.C = trivD.coeff` pointwise): its density IS the count-native tree-sum
`∑_T trivD2.C T q`, so the `goal_theorem_montes` bridge `hbridge` holds by `rfl`. The structural
`decomposition` field holds with `multiplicity ≡ 1`, `clusterVolume := trivD2.C`,
`shapes := trivD2.shapesOf`. -/
noncomputable def trivF : DensityFoundation where
  density := fun _ σ q => ∑ T ∈ trivD2.shapesOf σ, trivD2.C T q
  clusterVolume := fun T q => trivD2.C T q
  shapes := fun _ σ => trivD2.shapesOf σ
  multiplicity := fun _ => 1
  decomposition := by
    intro n σ _ q _
    simp
  density_nonneg := by
    intro n σ q
    apply Finset.sum_nonneg
    intro T hT
    -- `C T q = clusterCount trivCells … T q = if T = trivShape then 1 else 0` (PROVED helper),
    -- both nonnegative.
    change (0 : ℚ) ≤ trivD2.C T q
    have hC : trivD2.C T q = clusterCount trivCells (fun _ => 0) trivCells_descend T q := rfl
    rw [hC, clusterCount_trivCells trivCells_descend T q]
    by_cases h : T = trivShape <;> simp [h]

/-- **FULL-BUNDLE NON-VACUITY (Witness-nit fix; W4b: over the V2 spine).** The complete
`MontesV2.goal_theorem_montes` hypothesis bundle is jointly satisfiable: there exist `q, n,
M : CountingModel q n, D : MontesDataV2 q n M, σ, F : DensityFoundation, hσ` such that the coupling
`hbridge` holds. Unlike `DensityFoundation_nonempty` (which only inhabits `F`), this exhibits the
COUPLED `(M, D, F, hbridge)` bundle, with NON-TRIVIAL density `∑_T D.C T q = 1`. So
`MontesV2.goal_theorem_montes` is demonstrably non-vacuous over genuine inhabited types (it does
NOT cross the measure wall: `trivM` is a trivial degree-0 model). -/
theorem montes_bundle_nonempty :
    ∃ (q n : ℕ) (M : CountingModel q n) (D : MontesV2.MontesDataV2 q n M)
      (σ : FactorizationType) (F : DensityFoundation), σ.degree = n ∧
      (∀ q' : ℕ, 1 < q' → F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.C T q') :=
  ⟨2, 0, trivM, trivD2, trivType, trivF, rfl, fun _ _ => rfl⟩

/-- **The coupled witness's density sum is the constant `1`** (W4b port of the old
`trivD_sum_coeff_eq_one`, same value). `trivD2.shapesOf trivType = {trivShape}` and
`trivD2.C trivShape q' = clusterCount trivCells … trivShape q' = 1` (`clusterCount_trivCells`),
so the tree-sum is `1` at every `q'`. Feeds `trivF_tame`. -/
theorem trivD2_sum_C_eq_one (q' : ℕ) :
    (∑ T ∈ trivD2.shapesOf trivType, trivD2.C T q') = 1 := by
  have hs : trivD2.shapesOf trivType = {trivShape} := if_pos rfl
  rw [hs, Finset.sum_singleton]
  have hC : trivD2.C trivShape q'
      = clusterCount trivCells (fun _ => 0) trivCells_descend trivShape q' := rfl
  rw [hC, clusterCount_trivCells trivCells_descend trivShape q', if_pos rfl]

/-- **The tame functional equation holds (PROVABLY, no axiom) for the coupled witness** (U1 fix,
2026-07-02; W4b: over `trivD2`). `trivF.density 0 trivType` is the constant `1`
(`trivD2_sum_C_eq_one`), represented by the palindromic rational function `1/1`. So the witness
bundle discharges `goal_theorem_montes`'s `htameFE` hypothesis by a PROOF, keeping the full-bundle
non-vacuity instance tame-axiom-free. -/
theorem trivF_tame : TameFunctionalEquation trivF 0 trivType := by
  refine ⟨1, 1, one_ne_zero, fun q' _ _ => ?_, fun x _ _ _ => by simp⟩
  show (∑ T ∈ trivD2.shapesOf trivType, trivD2.C T q') = _
  rw [trivD2_sum_C_eq_one q']
  simp

/-- **`goal_theorem_montes` applied to the full witness bundle (a sorry-free instance; W4b: the V2
`MontesV2.goal_theorem_montes` fired on the ported bundle).** The conclusion of
`goal_theorem_montes` holds for the coupled `(trivM, trivD2, trivType, trivF)` bundle — witnessing
that the theorem genuinely fires on an inhabited bundle with non-trivial density. The tame
hypothesis is discharged by the PROVED `trivF_tame` (no axiom), so this instance's footprint is
Lean core only. -/
theorem montes_full_instance :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ trivD2.shapesOf trivType, trivD2.C T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      (1 < 2 → trivM.countingDensity trivType = num.eval ((2 : ℕ) : ℚ) / den.eval ((2 : ℕ) : ℚ)) ∧
      IsPalindromic num den :=
  MontesV2.goal_theorem_montes trivM trivD2 trivType trivF rfl (fun _ _ => rfl) trivF_tame

end LeanUrat.Witness
