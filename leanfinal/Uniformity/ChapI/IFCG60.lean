/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG58
import Uniformity.ChapI.IFCG59

/-!
# Uniformity.ChapI.IFCG60 — [VCL 2026-08-31] the cell-side depth-graded census of the
visible sector: the singleton-type fire, the exact graded count identities, and the
cluster bridge

Stage VCL of the cone census (design record `runs/wave-c/verdict_VCL.md`; consumes
PCD = `IFCG58` and TBT = `IFCG59`, with RCD's tiling toolkit through `IFCG56`).
PCD left the master's one convolution premise `∀ g, VisCensusLaw g e σ` open at
`e ≥ 5` ramified; RCD's fence located its content on the CELL side (which visible
cells carry how many table clusters).  This file lands the cell-side structure that
is provable today and fires the census where it closes:

* **§1 ★★★ THE TYPE-SUPPORT FIRE.**  `two_le_card_of_visGenre`: every visible cell of
  EITHER convolution genre forces `2 ≤ Multiset.card σ.data` — both refinement maps
  (`splitSector_refines_decided`, `powerSectorProper_refines_decided`) produce a
  decided factor pair of positive masses whose types SUM to `σ.data`, and
  positive-mass decided types are nonempty (`typeOf_degree`).  Hence the visible
  sectors are EMPTY at every singleton type, and ★★★ `visCensusLaw_of_card_le_one`:
  **`VisCensusLaw g m σ` holds OUTRIGHT at every `σ` with `card σ.data ≤ 1`, both
  genres, every mass** — with the weight/collision/defect-law singleton fires as
  corollaries.  (TBT's `leafSectorLaw_singleton` closed row 5 at singleton types;
  this is the same shrink for rows 3/4.)
* **§2 ★★★ THE MASTERS RECOMPUTED.**  `decidedSliceAt_all_of_visCensus''` /
  `decidedSliceAt_all_of_MASTER'''` / `capstoneHypotheses_of_MASTER'''`: on all three
  spines the convolution rows' premises weaken to NON-SINGLETON σ — after this file
  EVERY sector row of the census master (split, power, leaf) carries the guard
  `2 ≤ Multiset.card σ.data`.
* **§3 THE DEPTH-GRADED CENSUS** (exact at every finite level, genre-uniform):
  `visDepthMass g v` — the table pair mass at mixing depth `v` on the genre's visible
  cells; ★ `sum_multCount_eq_sum_visDepthMass` (the weight census IS the depth-graded
  pair census); ★ `card_visGenre_cast` — THE CELL-SIDE COUNT THROUGH THE PAIR SIDE:

      #vis(g) = Σ_{v ≤ M+m} visDepthMass g v − genreCollisionTotal g

  (the charge's `#vis = Σ_v (pairs at depth v)/q^v` in its honest exact form: the
  depth-`v` mass carries each cell with its cluster multiplicity, the `q^v` division
  happens per cluster in §5, and the collision total is exactly the multiplicity
  excess).
* **§4 THE TRIANGLE RE-BASE.**  ★ `visCountLaw_of_weight_collision` and the power
  analogue: with RCD's `collisionLaw_of_visLaws`, any two of {weight census, cell
  census, collision law} now give the third — the master's cell censuses officially
  rest on the WEIGHT censuses plus the collision structure.
* **§5 THE CLUSTER BRIDGE** (pure Lean core): ★ `sum_shiftedDepthFiber_vis_eq` — the
  vis-summed drainage tiling, `#(shifted pairs at depth v) = q^v · #(clusters)`
  EXACTLY; ★ the tiled lower bound and ★ the gap bound (vis mass exceeds its tiled
  part by at most the full slice gap); ★★ `tendsto_visDepth_sub_clusters` — the
  depth-`v` visible pair mass IS `q^v` times the cluster count asymptotically (KDW's
  unconditional drainage); ★ `zcURLim_visDepth_of_clusters` — the per-depth mass
  census rests on the CLUSTER census; ★ `sum_card_depthPairSet_eq` — the depth strata
  partition the full box (the summability/domination instrument; the `(1,1)` box
  value is IFCG56's, the general values are the Igusa remainder).

## THE HONEST FENCE

`VisCensusLaw g m σ` at `σ` ramified with `2 ≤ card σ.data` (`.split` at `4 ≤ m`,
`.power` at `5 ≤ m`) is NOT fired — the charge's item 3 full fire is not reachable
today, exactly as RCD/PCD/TBT fenced.  After this file its content is factored into
named axes: (i) per depth, the CLUSTER censuses (§5's re-base; carrier at the N-free
shifted level — the general `(n₁,n₂)` box values are the Igusa census), (ii) the
summed rationality across depths (an infinite sum of per-depth rational values need
not be rational — the geometric structure across `v` is the block-decomposition
mathematics, deliberately NOT assumed here), and (iii) the collision structure
(B.42's block-grouping genre; §4 shows it is the exact gap between weight and count).
The `#vis = Σ_v (pairs at depth v)/q^v` identity of the charge is TRUE only with the
collision correction (§3) — a cell hit by `k` clusters is counted `k` times by the
divided pair mass; the uncorrected identity would be dishonest and is not stated.

## Axiom fence (machine-exact at landing)

Pure Lean core `{propext, Classical.choice, Quot.sound}`: all of §3's grading
identities except the cast (`sum_multCount_eq_sum_visDepthMass`,
`visWeight_eq_sum_visDepthMass`, `powerVisWeight_eq_sum_visDepthMass`) and ALL of §5.
Lean core + the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42, inherited through the
refinement maps / SDL's casts / IFCG59's masters — never re-consumed): §1, §2,
`card_visGenre_cast`, §4.  The capstone master additionally inherits
`Uniformity.Density.Tower.agnprw_termination` (ID12's, previously declared).
C.33 and `AX_cellRecursion` must NOT occur.  Zero sorries, zero new axioms; the only
new definitions are the two ℕ-valued counters `visDepthMass`/`genreCollisionTotal`
(finite sums of landed counters — no new trust surface).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG60

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ConeRemainderLaw)
open Uniformity.Density.IFCG35 (LeafSectorLaw)
open Uniformity.Density.IFCG38 (splitSectorVis convPairs convCount mulClassAt
  SplitConvolutionDefectLaw zcURLim_sub zcURLim_conv CornerVisible
  splitSector_refines_decided)
open Uniformity.Density.IFCG40 (pairFiber multCount)
open Uniformity.Density.IFCG41 (mixDepth mixDepth_le pairDepthFiber CollisionLaw
  StrayLaw collisionTotal strayTotal multCount_eq_sum_pairDepthFiber)
open Uniformity.Density.IFCG44 (powerSectorProperVis PowerConvolutionDefectLaw
  PowerFullSpanLaw powerSectorProper_refines_decided)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt)
open Uniformity.Density.IFCG49 (decidedAt_of_coeffFactor)
open Uniformity.Density.IFCG51 (EisFullSpanRemainderLaw)
open Uniformity.Density.IFCG56 (VisCountLaw VisWeightLaw visWeight
  collisionTotal_cast visWeight_eq_zero_of_empty collisionTotal_eq_zero_of_empty
  splitSectorVis_eq_empty_of_mass_le_three decidedPairSet depthPairSet tableSlice
  shiftedSlice shiftedDepthFiber natCard_shiftedDepthFiber
  qpow_mul_card_le_pairDepthFiber pairDepthFiber_eq_natCard pairFactor
  splitConvolutionDefectLaw_of_visCountLaw tendsto_slice_drainage_of_complete)
open Uniformity.Density.IFCG57 (LeafSubfaceLaw)
open Uniformity.Density.IFCG58 (VisGenre visGenreSet VisCensusLaw
  visCensusLaw_split_iff visCensusLaw_power_iff PowerVisCountLaw PowerVisWeightLaw
  powerVisWeight powerCollisionTotal powerCollisionTotal_cast
  powerVisWeight_eq_zero_of_empty powerCollisionTotal_eq_zero_of_empty
  powerSectorProperVis_eq_empty_of_mass_le_four
  powerConvolutionDefectLaw_of_powerVisCountLaw)

/-! ## §0 — the kit: counting spines and the decided-type support reader -/

section Kit

open Classical in
/-- `Nat.card` of a set in a finite type, as a `Finset.filter` card (the corpus's
counting bridge, reproduced). -/
private theorem natCard_set_eq_card_filter {α : Type*} [Fintype α] (s : Set α) :
    Nat.card s = (Finset.univ.filter (fun a => a ∈ s)).card := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

open Classical in
/-- Fiberwise decomposition of a set count along any map, over any `Finset` containing
the image of the set (the cluster decomposition's counting spine). -/
private theorem natCard_eq_sum_fiber_of_mem {α β : Type*} [Finite α]
    (s : Set α) (φ : α → β) (T : Finset β) (hT : ∀ a ∈ s, φ a ∈ T) :
    Nat.card s = ∑ b ∈ T, Nat.card ((s ∩ φ ⁻¹' {b} : Set α)) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  rw [natCard_set_eq_card_filter s,
    Finset.card_eq_sum_card_fiberwise (f := φ) (t := T)
      (fun a ha => hT a (Finset.mem_filter.mp ha).2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [natCard_set_eq_card_filter, Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/-- Bridge: a finite set's `toFinset` card is its `Nat.card` (the corpus's private
copy, reproduced). -/
private theorem toFinset_card_eq_natCard {α : Type*} (s : Set α) (hs : s.Finite) :
    hs.toFinset.card = Nat.card s := by
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card s hs]

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The decided-type support reader**: a `σ₁`-decided class of POSITIVE mass has
nonempty type data (`typeOf_degree`: the type's degree is the lift's degree `n ≥ 1`,
and the empty multiset has degree `0`). -/
private theorem data_ne_zero_of_decided {n : ℕ} (hn : 0 < n) {σ₁ : FactorizationType}
    {L : ℕ} {c₁ : Coeff O n L} (hd : DecidedAt O n σ₁ L c₁) : σ₁.data ≠ 0 := by
  obtain ⟨a, ha⟩ := proj_surjective O n L c₁
  have hdeg : σ₁.degree = n := by
    rw [← hd a ha, typeOf_degree (monicPoly_monic a), monicPoly_natDegree]
  intro h0
  have h1 : σ₁.degree = 0 := by
    simp [FactorizationType.degree, h0]
  omega

end Kit

/-! ## §1 — ★★★ THE TYPE-SUPPORT FIRE: visible convolution-genre cells force
`2 ≤ card σ.data`, so the census laws fire OUTRIGHT at every singleton type -/

section TypeSupport

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★★ **THE TYPE-SUPPORT CONSTRAINT** (TBT's genre, enacted on the convolution
genres): every visible cell of EITHER convolution-descending genre forces at least two
type entries — both refinement maps (`splitSector_refines_decided`,
`powerSectorProper_refines_decided`) produce a decided pair of POSITIVE masses whose
types sum to `σ.data`, and positive-mass decided types are nonempty. -/
theorem two_le_card_of_visGenre {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    {σ : FactorizationType} {M : ℕ} (g : VisGenre) {c : Coeff O m (M + m)}
    (hc : c ∈ visGenreSet g O π m σ M) : 2 ≤ Multiset.card σ.data := by
  have href : ∃ (n₁ n₂ : ℕ) (_ : 0 < n₁) (_ : 0 < n₂) (hsum : n₁ + n₂ = m)
      (σ₁ σ₂ : FactorizationType)
      (c₁ : Coeff O n₁ (M + m)) (c₂ : Coeff O n₂ (M + m)),
      DecidedAt O n₁ σ₁ (M + m) c₁ ∧ DecidedAt O n₂ σ₂ (M + m) c₂ ∧
      σ₁.data + σ₂.data = σ.data ∧ mulClass c₁ c₂ = hsum.symm ▸ c := by
    cases g with
    | split => exact splitSector_refines_decided hπ hm hc.1 hc.2
    | power => exact powerSectorProper_refines_decided hπ hm hc.1 hc.2
  obtain ⟨n₁, n₂, hn₁, hn₂, hsum, σ₁, σ₂, c₁, c₂, hd₁, hd₂, hsumty, -⟩ := href
  have h1 : 0 < Multiset.card σ₁.data :=
    Multiset.card_pos.mpr (data_ne_zero_of_decided hn₁ hd₁)
  have h2 : 0 < Multiset.card σ₂.data :=
    Multiset.card_pos.mpr (data_ne_zero_of_decided hn₂ hd₂)
  have hcard : Multiset.card σ.data
      = Multiset.card σ₁.data + Multiset.card σ₂.data := by
    rw [← hsumty, Multiset.card_add]
  omega

/-- ★★ **The singleton-type emptiness**: at `card σ.data ≤ 1` the visible cells of
both convolution genres are EMPTY, at every level, mass, and uniformizer. -/
theorem visGenreSet_eq_empty_of_card_le_one {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 0 < m) {σ : FactorizationType} (hcard : Multiset.card σ.data ≤ 1)
    (g : VisGenre) (M : ℕ) : visGenreSet g O π m σ M = ∅ := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hc
  exact absurd (two_le_card_of_visGenre hπ hm g hc) (by omega)

end TypeSupport

section TypeSupportFires

/-- ★★★ **THE SINGLETON-TYPE FIRE of the unified census** — `VisCensusLaw g m σ` holds
OUTRIGHT at every type with `card σ.data ≤ 1`, both genres, every mass (the value is
`0`: the visible sector is empty by the type-support constraint at `0 < m`, and by the
mass emptiness at `m = 0`). -/
theorem visCensusLaw_of_card_le_one {m : ℕ} {σ : FactorizationType}
    (hcard : Multiset.card σ.data ≤ 1) : ∀ g, VisCensusLaw g m σ := by
  intro g
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  have hempty : visGenreSet g O π m σ M = ∅ := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · cases g with
      | split => exact splitSectorVis_eq_empty_of_mass_le_three hπ (by omega) σ M
      | power => exact powerSectorProperVis_eq_empty_of_mass_le_four hπ (by omega) σ M
    · exact visGenreSet_eq_empty_of_card_le_one hπ hm hcard g M
  have h0 : Nat.card (visGenreSet g O π m σ M) = 0 := by
    rw [hempty, Nat.card_coe_set_eq, Set.ncard_empty]
  show (0 : ℝ) = (Nat.card (visGenreSet g O π m σ M) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [h0]
  simp

/-- The split instance of the singleton emptiness, all masses (the `m = 0` case by the
mass emptiness). -/
theorem splitSectorVis_eq_empty_of_card_le_one {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {π : O} (hπ : Irreducible π) {m : ℕ}
    {σ : FactorizationType} (hcard : Multiset.card σ.data ≤ 1) (M : ℕ) :
    splitSectorVis O π m σ M = ∅ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact splitSectorVis_eq_empty_of_mass_le_three hπ (by omega) σ M
  · exact visGenreSet_eq_empty_of_card_le_one hπ hm hcard .split M

/-- The power instance of the singleton emptiness, all masses. -/
theorem powerSectorProperVis_eq_empty_of_card_le_one {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {π : O} (hπ : Irreducible π) {m : ℕ}
    {σ : FactorizationType} (hcard : Multiset.card σ.data ≤ 1) (M : ℕ) :
    powerSectorProperVis O π m σ M = ∅ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact powerSectorProperVis_eq_empty_of_mass_le_four hπ (by omega) σ M
  · exact visGenreSet_eq_empty_of_card_le_one hπ hm hcard .power M

/-- ★ **The singleton-type fire of the split weight census** (`VisWeightLaw m σ` at
`card σ.data ≤ 1`, unconditional — the weight vanishes on the empty visible sector). -/
theorem visWeightLaw_of_card_le_one {m : ℕ} {σ : FactorizationType}
    (hcard : Multiset.card σ.data ≤ 1) : VisWeightLaw m σ := by
  unfold VisWeightLaw
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  rw [visWeight_eq_zero_of_empty (splitSectorVis_eq_empty_of_card_le_one hπ hcard M)]
  simp

/-- ★ **The singleton-type fire of the power weight census**. -/
theorem powerVisWeightLaw_of_card_le_one {m : ℕ} {σ : FactorizationType}
    (hcard : Multiset.card σ.data ≤ 1) : PowerVisWeightLaw m σ := by
  unfold PowerVisWeightLaw
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  rw [powerVisWeight_eq_zero_of_empty
    (powerSectorProperVis_eq_empty_of_card_le_one hπ hcard M)]
  simp

/-- ★ **The singleton-type fire of `CollisionLaw`** (unconditional — the collision
total vanishes on the empty visible sector). -/
theorem collisionLaw_of_card_le_one {m : ℕ} {σ : FactorizationType}
    (hcard : Multiset.card σ.data ≤ 1) : CollisionLaw m σ := by
  unfold CollisionLaw
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  rw [collisionTotal_eq_zero_of_empty
    (splitSectorVis_eq_empty_of_card_le_one hπ hcard M)]
  simp

/-- ★★ **The singleton-type fire of the split defect law** (under the `< m` decided
value laws, through RCD's re-base). -/
theorem splitConvolutionDefectLaw_of_card_le_one {m : ℕ} {σ : FactorizationType}
    (hcard : Multiset.card σ.data ≤ 1)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    SplitConvolutionDefectLaw m σ :=
  splitConvolutionDefectLaw_of_visCountLaw σ hDV
    ((visCensusLaw_split_iff m σ).mp (visCensusLaw_of_card_le_one hcard .split))

/-- ★★ **The singleton-type fire of the power defect law** (under the `< m` decided
value laws, through PCD's re-base). -/
theorem powerConvolutionDefectLaw_of_card_le_one {m : ℕ} {σ : FactorizationType}
    (hcard : Multiset.card σ.data ≤ 1)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    PowerConvolutionDefectLaw m σ :=
  powerConvolutionDefectLaw_of_powerVisCountLaw σ hDV
    ((visCensusLaw_power_iff m σ).mp (visCensusLaw_of_card_le_one hcard .power))

end TypeSupportFires

/-! ## §2 — ★★★ THE MASTERS RECOMPUTED: the convolution rows weaken to NON-SINGLETON σ

TBT shrank the leaf row (row 5) to `2 ≤ Multiset.card σ.data`; §1 does the same to the
two convolution rows (rows 3/4): singleton types are closed outright, so the surviving
census/defect premises add the guard `2 ≤ Multiset.card σ.data` — strictly weaker, and
the exact honest remainder (a visible convolution-genre cell FORCES at least two type
entries, so no content is lost). -/

section Masters

/-- ★★★ **THE CENSUS MASTER, CONVOLUTION ROW RECOMPUTED**: TBT's
`decidedSliceAt_all_of_visCensus'` with the unified-census premise guarded by
`2 ≤ Multiset.card σ.data` (the singleton types are §1's unconditional fire).  The
all-degree decided slice rests on {`∀ g, VisCensusLaw g` at NON-SINGLETON ramified σ,
`PowerFullSpanLaw`, `LeafSubfaceLaw` at NON-SINGLETON σ, the `e = 4` remainder laws}. -/
theorem decidedSliceAt_all_of_visCensus''
    (hVC : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → ∀ g, VisCensusLaw g e σ)
    (hPF : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerFullSpanLaw e σ)
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG59.decidedSliceAt_all_of_visCensus'
    (fun e he hsm σ hσ hwit hram => by
      by_cases hcard : 2 ≤ Multiset.card σ.data
      · exact hVC e he hsm σ hσ hwit hram hcard
      · exact visCensusLaw_of_card_le_one (by omega))
    hPF hLeafSub hR4

/-- ★★★ **THE CENSUS MASTER ON LSC's SPINE, CONVOLUTION ROWS RECOMPUTED**: IFCG59's
`decidedSliceAt_all_of_MASTER''` with BOTH convolution-defect premises guarded by
`2 ≤ Multiset.card σ.data` (the singleton types discharge through §1's fires and the
`< e` value laws). -/
theorem decidedSliceAt_all_of_MASTER'''
    (hFC : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D)
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hSD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
          SplitConvolutionDefectLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
          PowerConvolutionDefectLaw e σ)
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG59.decidedSliceAt_all_of_MASTER'' hFC hEis
    (fun e he hsm σ hσ hwit hram => by
      by_cases hcard : 2 ≤ Multiset.card σ.data
      · exact hSD e he hsm σ hσ hwit hram hcard
      · exact splitConvolutionDefectLaw_of_card_le_one (by omega) hsm)
    (fun e he hsm σ hσ hwit hram => by
      by_cases hcard : 2 ≤ Multiset.card σ.data
      · exact hPD e he hsm σ hσ hwit hram hcard
      · exact powerConvolutionDefectLaw_of_card_le_one (by omega) hsm)
    hLeafSub

universe uW uG uKt uL

/-- ★★★ **THE CAPSTONE MASTER, CONVOLUTION ROWS RECOMPUTED**: IFCG59's
`capstoneHypotheses_of_MASTER''` with BOTH convolution-defect premises guarded by
`2 ≤ Multiset.card σ.data` (ID12's honesty frame applies verbatim; all three
sector rows of the master now carry the non-singleton guard). -/
theorem capstoneHypotheses_of_MASTER''' (n : ℕ)
    (hladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      CanonicalLadderConfig C B G Kt L N v ρ q n →
      Uniformity.Density.IFC5.LadderSupplyLive₃.{uW, uG, uKt, uL}
        C B G Kt L N v ρ q n)
    (hdeepTwist : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
      Ladder.DeepTwistConjunctLive r v ρ q A R w)
    (hFC : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D)
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hSD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
          SplitConvolutionDefectLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
          PowerConvolutionDefectLaw e σ)
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ) :
    CapstoneHypotheses.{uW, uG, uKt, uL} n :=
  Uniformity.Density.IFCG59.capstoneHypotheses_of_MASTER'' n hladder hdeepTwist hFC
    hEis
    (fun e he hsm σ hσ hwit hram => by
      by_cases hcard : 2 ≤ Multiset.card σ.data
      · exact hSD e he hsm σ hσ hwit hram hcard
      · exact splitConvolutionDefectLaw_of_card_le_one (by omega) hsm)
    (fun e he hsm σ hσ hwit hram => by
      by_cases hcard : 2 ≤ Multiset.card σ.data
      · exact hPD e he hsm σ hσ hwit hram hcard
      · exact powerConvolutionDefectLaw_of_card_le_one (by omega) hsm)
    hLeafSub

end Masters

/-! ## §3 — THE DEPTH-GRADED CENSUS: the cell-side count through the pair side,
exact at every finite level -/

section GradedCensus

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The depth-`v` visible pair mass of genre `g`**: the convolution-table pair count
at mixing depth exactly `v` landing on the genre-`g` visible cells — the depth-`v`
grade of the visible weight census (RDC's `pairDepthFiber`, summed over the genre's
visible cells and the table entries). -/
noncomputable def visDepthMass (g : VisGenre) (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O) (m : ℕ)
    (σ : FactorizationType) (M v : ℕ) : ℕ :=
  ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
    ∑ p ∈ convPairs m σ, pairDepthFiber O π m σ M p c v

/-- **The genre-`g` collision total** (`.split` ↦ SDL's `collisionTotal`, `.power` ↦
PCD's `powerCollisionTotal`) — the multiplicity excess of the table over the genre's
visible cells. -/
noncomputable def genreCollisionTotal (g : VisGenre) (O : Type*) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O)
    (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  match g with
  | .split => collisionTotal O π m σ M
  | .power => powerCollisionTotal O π m σ M

/-- ★ **THE GRADED COUNT IDENTITY** (genre-uniform, exact at every finite level): the
multiplicity-weighted count of the genre-`g` visible cells is the sum of the depth-`v`
visible pair masses over `v ≤ M + m` — the visible weight census IS the depth-graded
pair census, restricted to the genre's cells. -/
theorem sum_multCount_eq_sum_visDepthMass (g : VisGenre) (π : O) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) :
    ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset, multCount O m σ M c
      = ∑ v ∈ Finset.range (M + m + 1), visDepthMass g O π m σ M v := by
  unfold visDepthMass
  calc ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset, multCount O m σ M c
      = ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
          ∑ p ∈ convPairs m σ, ∑ v ∈ Finset.range (M + m + 1),
            pairDepthFiber O π m σ M p c v :=
        Finset.sum_congr rfl fun c _ => multCount_eq_sum_pairDepthFiber π m σ M c
    _ = ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
          ∑ v ∈ Finset.range (M + m + 1), ∑ p ∈ convPairs m σ,
            pairDepthFiber O π m σ M p c v :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ v ∈ Finset.range (M + m + 1),
          ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
            ∑ p ∈ convPairs m σ, pairDepthFiber O π m σ M p c v :=
        Finset.sum_comm

/-- The split weight census is the depth-graded pair census (RCD's `visWeight`,
graded). -/
theorem visWeight_eq_sum_visDepthMass (π : O) (m : ℕ) (σ : FactorizationType)
    (M : ℕ) :
    visWeight O π m σ M
      = ∑ v ∈ Finset.range (M + m + 1), visDepthMass .split O π m σ M v :=
  sum_multCount_eq_sum_visDepthMass .split π m σ M

/-- The power weight census is the depth-graded pair census (PCD's `powerVisWeight`,
graded). -/
theorem powerVisWeight_eq_sum_visDepthMass (π : O) (m : ℕ) (σ : FactorizationType)
    (M : ℕ) :
    powerVisWeight O π m σ M
      = ∑ v ∈ Finset.range (M + m + 1), visDepthMass .power O π m σ M v :=
  sum_multCount_eq_sum_visDepthMass .power π m σ M

variable [IsAdicComplete (maximalIdeal O) O]

/-- ★ **THE CELL-SIDE COUNT THROUGH THE PAIR SIDE** — exact at every finite level,
both genres: the genre-`g` visible CELL count is the depth-graded visible pair mass
minus the genre collision total,

    #vis(g) = Σ_{v ≤ M+m} visDepthMass g v − genreCollisionTotal g.

(The charge's `#vis = Σ_v (pairs at depth v)/q^v` in its honest exact form: the
depth-`v` pair mass carries each cell with its cluster multiplicity — the `q^v`
division happens per cluster in §4's tiling bridge, and the collision total is
exactly the multiplicity excess.) -/
theorem card_visGenre_cast {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (g : VisGenre) (σ : FactorizationType) (M : ℕ) :
    (Nat.card (visGenreSet g O π m σ M) : ℝ)
      = (∑ v ∈ Finset.range (M + m + 1), (visDepthMass g O π m σ M v : ℝ))
        - (genreCollisionTotal g O π m σ M : ℝ) := by
  cases g with
  | split =>
      have h1 := collisionTotal_cast hπ hm σ M
      have h2 : (visWeight O π m σ M : ℝ)
          = ∑ v ∈ Finset.range (M + m + 1), (visDepthMass .split O π m σ M v : ℝ) := by
        exact_mod_cast congrArg (Nat.cast (R := ℝ))
          (visWeight_eq_sum_visDepthMass π m σ M)
      show (Nat.card (splitSectorVis O π m σ M) : ℝ)
          = (∑ v ∈ Finset.range (M + m + 1), (visDepthMass .split O π m σ M v : ℝ))
            - (collisionTotal O π m σ M : ℝ)
      linarith
  | power =>
      have h1 := powerCollisionTotal_cast hπ hm σ M
      have h2 : (powerVisWeight O π m σ M : ℝ)
          = ∑ v ∈ Finset.range (M + m + 1), (visDepthMass .power O π m σ M v : ℝ) := by
        exact_mod_cast congrArg (Nat.cast (R := ℝ))
          (powerVisWeight_eq_sum_visDepthMass π m σ M)
      show (Nat.card (powerSectorProperVis O π m σ M) : ℝ)
          = (∑ v ∈ Finset.range (M + m + 1), (visDepthMass .power O π m σ M v : ℝ))
            - (powerCollisionTotal O π m σ M : ℝ)
      linarith

end GradedCensus

/-! ## §4 — THE TRIANGLE RE-BASE: any two of {weight, count, collision} give the
third.  RCD landed `collisionLaw_of_visLaws : (weight, count) ⟹ collision`; this
closes the remaining arrow `(weight, collision) ⟹ count` in both genres, so the
CELL censuses (the master's premises) officially rest on the WEIGHT censuses (whose
depth grading is §3, with §5's cluster bridge per depth) plus the collision structure
(the block-decomposition territory). -/

section Triangle

/-- ★ **`VisCountLaw` from weight + collision** — the split cell census rests on the
weight census and the collision law (`#vis = weight − collision` pointwise). -/
theorem visCountLaw_of_weight_collision {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hW : VisWeightLaw m σ) (hC : CollisionLaw m σ) : VisCountLaw m σ := by
  unfold VisCountLaw
  refine (zcURLim_sub hW hC).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (visWeight O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      - (collisionTotal O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = (Nat.card (splitSectorVis O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [div_sub_div_same, collisionTotal_cast hπ hm σ M]
  congr 1
  ring

/-- ★ **`PowerVisCountLaw` from weight + collision** (the power collision limit is the
raw `ZcURLim` conclusion — PCD's convention: no pre-named power collision Prop). -/
theorem powerVisCountLaw_of_weight_collision {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (hW : PowerVisWeightLaw m σ)
    (hC : ZcURLim (fun O _ _ _ _ _ π M =>
      (powerCollisionTotal O π m σ M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))) :
    PowerVisCountLaw m σ := by
  unfold PowerVisCountLaw
  refine (zcURLim_sub hW hC).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (powerVisWeight O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      - (powerCollisionTotal O π m σ M : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = (Nat.card (powerSectorProperVis O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [div_sub_div_same, powerCollisionTotal_cast hπ hm σ M]
  congr 1
  ring

/-- ★ **The unified census from the weights and collisions** — the master's one
convolution premise `∀ g, VisCensusLaw g m σ` rests on the two weight censuses plus
the two collision limits. -/
theorem visCensusLaw_of_weights_collisions {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (hW : VisWeightLaw m σ) (hC : CollisionLaw m σ)
    (hPW : PowerVisWeightLaw m σ)
    (hPC : ZcURLim (fun O _ _ _ _ _ π M =>
      (powerCollisionTotal O π m σ M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))) :
    ∀ g, VisCensusLaw g m σ := by
  intro g
  cases g with
  | split =>
      exact (visCensusLaw_split_iff m σ).mpr
        (visCountLaw_of_weight_collision hm σ hW hC)
  | power =>
      exact (visCensusLaw_power_iff m σ).mpr
        (powerVisCountLaw_of_weight_collision hm σ hPW hPC)

end Triangle

/-! ## §5 — THE CLUSTER BRIDGE: the `q^v` division of the visible depth strata
(RCD's tiling summed over the genre's cells), and the strata domination -/

section ClusterBridge

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★ **THE STRATA PARTITION THE FULL BOX** (the Tannery domination instrument): at
every level the depth strata exhaust the pair space exactly — so every stratum
measure is dominated by the total mass `1`, uniformly in the level.  (The per-`v`
box VALUES at general `(n₁, n₂)` are the Igusa census — the honest named remainder;
the `(1,1)` value `(q−1)·q^{v+1}` is landed in IFCG56.) -/
theorem sum_card_depthPairSet_eq (π : O) (n₁ n₂ N : ℕ) :
    ∑ v ∈ Finset.range (N + 1), Nat.card (depthPairSet O π n₁ n₂ N v)
      = residueCard O ^ ((n₁ + n₂) * N) := by
  have hfib : ∀ v : ℕ,
      ((Set.univ ∩ (fun q : Coeff O n₁ N × Coeff O n₂ N => mixDepth π q.1 q.2) ⁻¹' {v})
        : Set (Coeff O n₁ N × Coeff O n₂ N)) = depthPairSet O π n₁ n₂ N v := by
    intro v
    ext q
    simp [depthPairSet]
  have h := natCard_eq_sum_fiber_of_mem
    (Set.univ : Set (Coeff O n₁ N × Coeff O n₂ N))
    (fun q => mixDepth π q.1 q.2) (Finset.range (N + 1))
    (fun q _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (mixDepth_le π q.1 q.2)))
  rw [Finset.sum_congr rfl (fun v _ => congrArg Nat.card (congrArg Set.Elem (hfib v)))] at h
  rw [← h, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_prod, card_coeff, card_coeff,
    ← pow_add, ← add_mul]

/-- ★ **THE VIS-SUMMED CLUSTER IDENTITY** — RCD's drainage tiling summed over the
genre's visible cells: at exact depth `v` with `2v + 1 ≤ M + (n₁ + n₂)`, the
shifted-decided pairs landing on the genre-`g` visible cells number EXACTLY `q^v`
times the cluster-root count — "#(pairs at depth v) = q^v · #(clusters)" on the
shifted carrier. -/
theorem sum_shiftedDepthFiber_vis_eq {π : O} (hπ : Irreducible π) {n₁ n₂ M v : ℕ}
    (hN : 2 * v + 1 ≤ M + (n₁ + n₂)) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0) (g : VisGenre)
    (σ : FactorizationType) (part : Multiset (ℕ × ℕ)) :
    ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
        Nat.card (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
          (M + (n₁ + n₂)) v c)
      = residueCard O ^ v
        * ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
            Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
              (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                (M + (n₁ + n₂)) v c)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ =>
    natCard_shiftedDepthFiber hπ hN hpos ⟨part⟩ ⟨σ.data - part⟩ c

/-- ★ **THE TILED LOWER BOUND, VIS-SUMMED**: the depth-`v` visible pair mass at one
table entry dominates `q^v` times its cluster-root count. -/
theorem qpow_mul_clusters_le_visDepth {π : O} (hπ : Irreducible π) {n₁ n₂ M v : ℕ}
    (hN : 2 * v + 1 ≤ M + (n₁ + n₂)) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0) (g : VisGenre)
    (σ : FactorizationType) (part : Multiset (ℕ × ℕ)) :
    residueCard O ^ v
        * ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
            Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
              (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                (M + (n₁ + n₂)) v c))
      ≤ ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
          pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ =>
    qpow_mul_card_le_pairDepthFiber hπ σ M part c hN hpos

/-- The per-cell monotonicity: the shifted-decided depth-`v` fiber sits inside RDC's
depth-graded fiber (shifted decidedness refines to full decidedness). -/
private theorem natCard_shiftedDepthFiber_le_pairDepthFiber {π : O} {n₁ n₂ M v : ℕ}
    (σ : FactorizationType) (part : Multiset (ℕ × ℕ))
    (c : Coeff O (n₁ + n₂) (M + (n₁ + n₂))) :
    Nat.card (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c)
      ≤ pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v := by
  rw [pairDepthFiber_eq_natCard π σ M ((n₁, n₂), part) rfl c v]
  have hsub : shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c
      ⊆ (decidedPairSet O n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂))
          ∩ {q | mulClassAt rfl q.1 q.2 = c}
          ∩ depthPairSet O π n₁ n₂ (M + (n₁ + n₂)) v) := by
    rintro q ⟨hdec, hmul, hdep⟩
    exact ⟨⟨⟨decidedAt_of_coeffFactor (Nat.sub_le _ v) hdec.1,
      decidedAt_of_coeffFactor (Nat.sub_le _ v) hdec.2⟩, hmul⟩, hdep⟩
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-- ★ **THE GAP BOUND, VIS-SUMMED**: the depth-`v` visible pair mass exceeds its
shifted-decided part by at most the FULL slice gap (`tableSlice − shiftedSlice`) —
stated additively in `ℕ`.  (The two univ-partition identities `Σ_c fiber = slice` run
inside; the vis-restriction only shrinks the nonnegative excess.) -/
theorem visDepth_add_shiftedSlice_le {π : O} {n₁ n₂ M v : ℕ} (g : VisGenre)
    (σ : FactorizationType) (part : Multiset (ℕ × ℕ)) :
    (∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
        pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v)
        + Nat.card (shiftedSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v)
      ≤ (∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
          Nat.card (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
            (M + (n₁ + n₂)) v c))
        + Nat.card (tableSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v) := by
  classical
  letI : Fintype (Coeff O (n₁ + n₂) (M + (n₁ + n₂))) := Fintype.ofFinite _
  -- the table slice partitions along the product class into RDC's depth fibers
  have htab : Nat.card (tableSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v)
      = ∑ c : Coeff O (n₁ + n₂) (M + (n₁ + n₂)),
          pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v := by
    rw [natCard_eq_sum_fiber_of_mem
      (tableSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v)
      (fun q => mulClassAt rfl q.1 q.2) Finset.univ (fun q _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [pairDepthFiber_eq_natCard π σ M ((n₁, n₂), part) rfl c v]
    have hset : (tableSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v
          ∩ (fun q : Coeff O n₁ (M + (n₁ + n₂)) × Coeff O n₂ (M + (n₁ + n₂)) =>
              mulClassAt rfl q.1 q.2) ⁻¹' {c})
        = (decidedPairSet O n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂))
            ∩ {q | mulClassAt rfl q.1 q.2 = c}
            ∩ depthPairSet O π n₁ n₂ (M + (n₁ + n₂)) v) := by
      ext q
      simp only [tableSlice, depthPairSet, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_setOf_eq]
      tauto
    rw [hset]
  -- the shifted slice partitions along the product class into the shifted fibers
  have hsh : Nat.card (shiftedSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v)
      = ∑ c : Coeff O (n₁ + n₂) (M + (n₁ + n₂)),
          Nat.card (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
            (M + (n₁ + n₂)) v c) := by
    rw [natCard_eq_sum_fiber_of_mem
      (shiftedSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v)
      (fun q => mulClass q.1 q.2) Finset.univ (fun q _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hset : (shiftedSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v
          ∩ (fun q : Coeff O n₁ (M + (n₁ + n₂)) × Coeff O n₂ (M + (n₁ + n₂)) =>
              mulClass q.1 q.2) ⁻¹' {c})
        = shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c := by
      ext q
      simp only [shiftedSlice, shiftedDepthFiber, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_setOf_eq]
      tauto
    rw [hset]
  -- the complement's excess is nonnegative termwise
  have hTsub : (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset
      ⊆ Finset.univ := Finset.subset_univ _
  have h1 : ∑ c ∈ Finset.univ \ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
        Nat.card (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
          (M + (n₁ + n₂)) v c)
      ≤ ∑ c ∈ Finset.univ \ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
          pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v :=
    Finset.sum_le_sum fun c _ => natCard_shiftedDepthFiber_le_pairDepthFiber σ part c
  have h2 := Finset.sum_sdiff
    (f := fun c => pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v) hTsub
  have h3 := Finset.sum_sdiff
    (f := fun c => Nat.card (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
      (M + (n₁ + n₂)) v c)) hTsub
  omega

end ClusterBridge

section ClusterDrainage

/-- ★★ **THE CLUSTER DRAINAGE** — the depth-`v` visible pair mass IS `q^v` times the
cluster count, asymptotically exactly: their normalized gap drains to `0` as the level
diverges (KDW's unconditional drainage through RCD's slice limit; per table entry,
per genre, per depth — uniform in everything else). -/
theorem tendsto_visDepth_sub_clusters (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] {π : O} (hπ : Irreducible π) (n₁ n₂ : ℕ)
    (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0) (g : VisGenre) (σ : FactorizationType)
    (part : Multiset (ℕ × ℕ)) (v : ℕ) :
    Tendsto (fun M =>
        (((∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
            pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v : ℕ) : ℝ)
          - ((residueCard O ^ v
              * ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
                  Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
                    (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                      (M + (n₁ + n₂)) v c)) : ℕ) : ℝ))
          / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂))))
      atTop (nhds 0) := by
  have hdrain := (tendsto_slice_drainage_of_complete O π n₁ n₂ ⟨part⟩
    ⟨σ.data - part⟩ v).comp (tendsto_add_atTop_nat (n₁ + n₂))
  refine squeeze_zero' ?_ ?_ hdrain
  · -- nonnegativity, eventually (the tiled lower bound)
    refine Filter.eventually_atTop.mpr ⟨2 * v + 1, fun M hM => ?_⟩
    have hN : 2 * v + 1 ≤ M + (n₁ + n₂) := by omega
    apply div_nonneg _ (by positivity)
    rw [sub_nonneg]
    exact_mod_cast qpow_mul_clusters_le_visDepth hπ hN hpos g σ part
  · -- the gap bound, eventually
    refine Filter.eventually_atTop.mpr ⟨2 * v + 1, fun M hM => ?_⟩
    have hN : 2 * v + 1 ≤ M + (n₁ + n₂) := by omega
    have hmain := visDepth_add_shiftedSlice_le (π := π) (n₁ := n₁) (n₂ := n₂)
      (M := M) (v := v) g σ part
    rw [sum_shiftedDepthFiber_vis_eq hπ hN hpos g σ part] at hmain
    have hmainR : ((∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
          pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v : ℕ) : ℝ)
          + (Nat.card (shiftedSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
              (M + (n₁ + n₂)) v) : ℝ)
        ≤ ((residueCard O ^ v
              * ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
                  Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
                    (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                      (M + (n₁ + n₂)) v c)) : ℕ) : ℝ)
          + (Nat.card (tableSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
              (M + (n₁ + n₂)) v) : ℝ) := by
      exact_mod_cast hmain
    show _ ≤ ((Nat.card (tableSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
          (M + (n₁ + n₂)) v) : ℝ)
        - (Nat.card (shiftedSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
            (M + (n₁ + n₂)) v) : ℝ))
      / (residueCard O : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂)))
    gcongr ?_ / _
    linarith

end ClusterDrainage

section ClusterReBase

/-- ★ **THE PER-DEPTH RE-BASE**: the depth-`v` visible pair-mass census at one table
entry rests on its CLUSTER census — under the cluster-count `ZcURLim`, the visible
depth-mass `ZcURLim` follows (the gap is §5's drainage, a `ZcURLim`-zero family).
The remaining pair-side content of the visible censuses is officially the cluster
counts, whose carrier lives at the N-free shifted level. -/
theorem zcURLim_visDepth_of_clusters {n₁ n₂ : ℕ} (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    (g : VisGenre) (σ : FactorizationType) (part : Multiset (ℕ × ℕ)) (v : ℕ)
    (hcl : ZcURLim (fun O _ _ _ _ _ π M =>
      ((residueCard O ^ v
          * ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
              Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
                (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                  (M + (n₁ + n₂)) v c)) : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂))))) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
          pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂)))) := by
  have hgap : ZcURLim (fun O _ _ _ _ _ π M =>
      (((∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
          pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v : ℕ) : ℝ)
        - ((residueCard O ^ v
            * ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
                Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
                  (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                    (M + (n₁ + n₂)) v c)) : ℕ) : ℝ))
        / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂)))) := by
    refine ⟨0, 1, one_ne_zero, ?_⟩
    intro O _ _ _ _ _
    refine ⟨by simp, fun π hπ => ?_⟩
    simpa using tendsto_visDepth_sub_clusters O hπ n₁ n₂ hpos g σ part v
  refine (hcl.add hgap).congr ?_
  intro O _ _ _ _ _ π hπ M
  rw [← add_div]
  congr 1
  ring

end ClusterReBase

end Uniformity.Density.IFCG60

end

/-! ## AXCHECK FOOTER — §3's graded identities (except the cast) and ALL of §5 expect
PURE Lean core `{propext, Classical.choice, Quot.sound}`; §1, §2, the cast, and §4
expect Lean core + the owner-signed B.42 cite
`Uniformity.Density.Leaf.exists_slope_factorization`; the capstone master
additionally inherits `Uniformity.Density.Tower.agnprw_termination`.  C.33 and
`AX_cellRecursion` must NOT occur. -/
#print axioms Uniformity.Density.IFCG60.two_le_card_of_visGenre
#print axioms Uniformity.Density.IFCG60.visGenreSet_eq_empty_of_card_le_one
#print axioms Uniformity.Density.IFCG60.visCensusLaw_of_card_le_one
#print axioms Uniformity.Density.IFCG60.splitSectorVis_eq_empty_of_card_le_one
#print axioms Uniformity.Density.IFCG60.powerSectorProperVis_eq_empty_of_card_le_one
#print axioms Uniformity.Density.IFCG60.visWeightLaw_of_card_le_one
#print axioms Uniformity.Density.IFCG60.powerVisWeightLaw_of_card_le_one
#print axioms Uniformity.Density.IFCG60.collisionLaw_of_card_le_one
#print axioms Uniformity.Density.IFCG60.splitConvolutionDefectLaw_of_card_le_one
#print axioms Uniformity.Density.IFCG60.powerConvolutionDefectLaw_of_card_le_one
#print axioms Uniformity.Density.IFCG60.decidedSliceAt_all_of_visCensus''
#print axioms Uniformity.Density.IFCG60.decidedSliceAt_all_of_MASTER'''
#print axioms Uniformity.Density.IFCG60.capstoneHypotheses_of_MASTER'''
#print axioms Uniformity.Density.IFCG60.sum_multCount_eq_sum_visDepthMass
#print axioms Uniformity.Density.IFCG60.visWeight_eq_sum_visDepthMass
#print axioms Uniformity.Density.IFCG60.powerVisWeight_eq_sum_visDepthMass
#print axioms Uniformity.Density.IFCG60.card_visGenre_cast
#print axioms Uniformity.Density.IFCG60.visCountLaw_of_weight_collision
#print axioms Uniformity.Density.IFCG60.powerVisCountLaw_of_weight_collision
#print axioms Uniformity.Density.IFCG60.visCensusLaw_of_weights_collisions
#print axioms Uniformity.Density.IFCG60.sum_card_depthPairSet_eq
#print axioms Uniformity.Density.IFCG60.sum_shiftedDepthFiber_vis_eq
#print axioms Uniformity.Density.IFCG60.qpow_mul_clusters_le_visDepth
#print axioms Uniformity.Density.IFCG60.visDepth_add_shiftedSlice_le
#print axioms Uniformity.Density.IFCG60.tendsto_visDepth_sub_clusters
#print axioms Uniformity.Density.IFCG60.zcURLim_visDepth_of_clusters
