/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG44
import Uniformity.ChapI.IFCG56

/-!
# Uniformity.ChapI.IFCG58 — [PCD 2026-08-31] the power-defect census: RCD's template
replayed on the power sector, and the UNIFIED visible-genre census

Stage PCD of the cone census (design record `runs/wave-c/verdict_PCD.md`; consumes
PSL4 = `IFCG44` and RCD = `IFCG56`).  PSL4 left `PowerConvolutionDefectLaw m σ` (the
proper power part's overcount of the convolution table) as one of the census master's
premises, with the observation that the proper part descends through THE SAME
convolution table as the split sector (`card_powerSectorProperVis_le ≤ convCount`).
This file replays RCD's whole defect template on the power sector:

* **§1 THE POWER DEFECT DECOMPOSITION** (SDL's engine at the power fibers):
  `one_le_multCount_of_powerVis` — every visible-corner proper power cell is hit by
  the table at least once (PSL4's refinement `powerSectorProper_refines_decided`;
  B.42 leg) — hence ★ `convCount_eq_card_powerVis_add_totals`:

      convCount = #powerVis + (powerCollisionTotal + powerStrayTotal)

  EXACT at every finite level, with `powerCollisionTotal = Σ_{c ∈ powerVis}
  (multCount c − 1)` and `powerStrayTotal = Σ_{c ∉ powerVis} multCount c` the
  instance-free totals.  The pair table, its depth grading, and RCD's drainage tiling
  (`IFCG56` §§1–4) are SECTOR-AGNOSTIC — stated at free `(n₁, n₂, σ₁, σ₂, v)` on the
  decided pair table — so the whole tiling toolkit applies to these fibers verbatim,
  with NO replay needed.
* **§2 THE CENSUS LAWS AND THE RE-BASE.**  `PowerVisCountLaw m σ` (the visible proper
  power cell census) and `PowerVisWeightLaw m σ` (its multiplicity-weighted census);
  the exact cast identities `powerCollisionTotal_cast` / `powerStrayTotal_cast`; the
  collision/stray `ZcURLim`s under the pair of laws; and ★★
  `powerConvolutionDefectLaw_of_powerVisCountLaw`: **`PowerConvolutionDefectLaw m σ`
  rests on the `< m` decided value laws plus the SINGLE Prop `PowerVisCountLaw m σ`,
  CITE-FREE** (the defect is `conv − #powerVis` pointwise) — exactly parallel to RCD's
  split re-base.  ★★ `powerSectorLaw_of_visCountLaw` then fires `PowerSectorLaw m σ`
  from `< m` laws + `PowerVisCountLaw` + `PowerFullSpanLaw`.
* **§3 THE FIRES.**  ★ `powerSectorProper_eq_empty_of_mass_le_four` (Lean-core): a
  proper power cell needs `4 ≤ e'·k·deg ψ < m`, so the proper part is EMPTY at
  `m ≤ 4` — ONE MASS BETTER than the split sector's `m ≤ 3`.  Hence
  `PowerVisCountLaw`/`PowerVisWeightLaw` fire unconditionally at `m ≤ 4` and at every
  unramified type, and ★ `powerConvolutionDefectLaw_of_mass_le_four` is a NEW fire
  (PSL4 had only the unramified one).
* **§4 ★★ THE UNIFICATION** (the honest joint form): the split and proper-power
  visible cells are DISJOINT sub-genres of the same visible carrier (RECUR's
  trichotomy, `visGenreSet_disjoint`), and their two censuses are the SAME Prop at
  two genre indices — `VisCensusLaw g m σ` over `VisGenre = split | power`, with
  `VisCensusLaw .split ↔ VisCountLaw` and `VisCensusLaw .power ↔ PowerVisCountLaw`
  both DEFINITIONAL (`Iff.rfl`).  A single union-count Prop would NOT recover the two
  defect laws (a sum limit does not split), so the genre-INDEXED family is the honest
  unification; both defect laws re-base onto `∀ g, VisCensusLaw g m σ`
  (`splitConvolutionDefectLaw_of_visCensus`, `powerConvolutionDefectLaw_of_visCensus`).
* **§5 ★★★ THE MASTER RECOMPUTED.**  `decidedSliceAt_all_of_visCounts`: the
  all-degree decided slice rests on {`VisCountLaw`, `PowerVisCountLaw`,
  `PowerFullSpanLaw`, `LeafSectorLaw`, the five `e = 4` remainder laws} — BOTH
  convolution-defect premises replaced by their visible-cell censuses; and
  `decidedSliceAt_all_of_visCensus`: the two census premises fused into the ONE
  genre-quantified Prop — the master's premise list is now
  {`∀ g, VisCensusLaw g`, `PowerFullSpanLaw`, `LeafSectorLaw`, R4}.

## Honest scope

NOT proved here: `VisCensusLaw g m σ` at `5 ≤ m`, σ ramified (for either genre) —
the exact remaining convolution-sector content, unchanged in strength, now ONE named
family.  Its discharge toolkit on the pair side is RCD's (sector-agnostic: tiling,
N-free root boxes, unconditional drainage); the cell-side structure (which visible
cells of each genre carry how many table pairs — B.42's block-decomposition genre for
split, the polygon-factorization image description for power) is the open territory.
`PowerFullSpanLaw` (the fractional-recentring residue) is untouched — its territory
is the OM decision transport (C136), not the convolution table.  Nothing weakened;
`PowerConvolutionDefectLaw`'s statement is PSL4's, byte-untouched.

## Axiom fence (machine-exact at landing)

Pure Lean core `{propext, Classical.choice, Quot.sound}`:
`powerSectorProper_eq_empty_of_mass_le_four` (+`Vis`),
`powerVisCountLaw_of_mass_le_four`, `powerVisWeightLaw_of_mass_le_four`,
★★ `powerConvolutionDefectLaw_of_powerVisCountLaw`,
`powerConvolutionDefectLaw_of_mass_le_four`, `visCountLaw_of_mass_le_three`,
`visCensusLaw_of_mass_le_three`, `splitConvolutionDefectLaw_of_visCensus`,
`powerConvolutionDefectLaw_of_visCensus`.  Lean core + the owner-signed gate-(b)
cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42, inherited through
PSL4's refinement / SDL / IFCG33 / IFCG35's front — never re-consumed):
`one_le_multCount_of_powerVis`, `convCount_eq_card_powerVis_add_totals`, the casts,
the collision/stray `ZcURLim`s, the unramified emptiness/fires,
`powerSectorLaw_of_visCountLaw`, `visGenreSet_disjoint`, and the two masters.
The C.33 cites and `AX_cellRecursion` must NOT occur.  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG58

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ConeRemainderLaw)
open Uniformity.Density.IFCG35 (PowerSectorLaw SplitSectorLaw LeafSectorLaw
  splitSector powerSector sectors_disjoint minFaceAt_unique classResidualPoly
  MinFaceAt)
open Uniformity.Density.IFCG38 (splitSectorVis convPairs convCount mulClassAt
  SplitConvolutionDefectLaw zcURLim_sub zcURLim_conv CornerVisible)
open Uniformity.Density.IFCG39 (powerSector_data)
open Uniformity.Density.IFCG40 (pairFiber multCount convCount_eq_sum_multCount)
open Uniformity.Density.IFCG44 (powerSectorProper powerSectorProperVis
  powerSectorFull powerSectorProper_refines_decided PowerConvolutionDefectLaw
  PowerFullSpanLaw powerSectorLaw_of_rebase decidedSliceAt_all_of_defects)
open Uniformity.Density.IFCG56 (VisCountLaw VisWeightLaw
  splitConvolutionDefectLaw_of_visCountLaw splitSectorVis_eq_empty_of_mass_le_three
  splitSectorVis_eq_empty_unramified)

/-! ## §0 — kit (private replicas of the established counting bridges) -/

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

/-- Bridge: a finite set's `toFinset` card is its `Nat.card` (IFCG56's private copy). -/
private theorem toFinset_card_eq_natCard {α : Type*} (s : Set α) (hs : s.Finite) :
    hs.toFinset.card = Nat.card s := by
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card s hs]

private theorem isKey_X {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

end Kit

/-! ## §1 — THE POWER DEFECT DECOMPOSITION (SDL's engine at the power fibers) -/

section Decomposition

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The power collision total** — the collision excess of the convolution table over
the visible-corner proper power cells, `Σ_{c ∈ powerVis} (multCount c − 1)`, as one
instance-free `ℕ` (SDL's `collisionTotal` at the power fibers). -/
noncomputable def powerCollisionTotal (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O)
    (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  ∑ c ∈ (Set.toFinite (powerSectorProperVis O π m σ M)).toFinset,
    (multCount O m σ M c - 1)

/-- **The power stray total** — the table mass landing OUTSIDE the visible-corner
proper power cells, `Σ_{c ∉ powerVis} multCount c`. -/
noncomputable def powerStrayTotal (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O)
    (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  ∑ c ∈ (Set.toFinite ((powerSectorProperVis O π m σ M)ᶜ)).toFinset,
    multCount O m σ M c

/-- **The power visible weight**: the multiplicity-weighted count of the visible
proper power cells (RCD's `visWeight` at the power fibers). -/
noncomputable def powerVisWeight (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O)
    (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  ∑ c ∈ (Set.toFinite (powerSectorProperVis O π m σ M)).toFinset, multCount O m σ M c

variable [IsAdicComplete (maximalIdeal O) O]

/-- Every VISIBLE proper power cell is hit by the table at least once (PSL4's
refinement map `powerSectorProper_refines_decided` — the B.42-citing leg; the exact
replay of SDL's `one_le_multCount_of_vis` on the power sector). -/
theorem one_le_multCount_of_powerVis {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ powerSectorProperVis O π m σ M) : 1 ≤ multCount O m σ M c := by
  classical
  obtain ⟨hcs, hcv⟩ := hc
  obtain ⟨n₁, n₂, hn₁, hn₂, hsum, σ₁, σ₂, c₁, c₂, hd₁, hd₂, hsumty, hkey⟩ :=
    powerSectorProper_refines_decided hπ hm hcs hcv
  subst hsum
  have hpmem : ((n₁, n₂), σ₁.data) ∈ convPairs (n₁ + n₂) σ := by
    rw [convPairs, Finset.mem_product, Finset.mem_filter, Finset.mem_product]
    dsimp only
    refine ⟨⟨⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩,
      rfl, hn₁, hn₂⟩, ?_⟩
    rw [Multiset.mem_toFinset, Multiset.mem_powerset]
    exact Multiset.le_iff_exists_add.mpr ⟨σ₂.data, hsumty.symm⟩
  have hfmem : ((c₁, c₂) : Coeff O n₁ (M + (n₁ + n₂)) × Coeff O n₂ (M + (n₁ + n₂)))
      ∈ ((decidedSet O n₁ ⟨σ₁.data⟩ (M + (n₁ + n₂)))
          ×ˢ (decidedSet O n₂ ⟨σ.data - σ₁.data⟩ (M + (n₁ + n₂)))
        ∩ (fun q : Coeff O n₁ (M + (n₁ + n₂)) × Coeff O n₂ (M + (n₁ + n₂)) =>
            mulClassAt rfl q.1 q.2) ⁻¹' {c} : Set _) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (show (⟨σ₁.data⟩ : FactorizationType) = σ₁ from rfl) ▸ hd₁
    · have h6 : σ.data - σ₁.data = σ₂.data := by
        rw [← hsumty, add_tsub_cancel_left]
      rw [show (⟨σ.data - σ₁.data⟩ : FactorizationType) = σ₂ from
        FactorizationType.ext h6]
      exact hd₂
    · exact hkey
  have hfpos : 1 ≤ pairFiber O (n₁ + n₂) σ M ((n₁, n₂), σ₁.data) c := by
    unfold pairFiber
    dsimp only
    rw [dif_pos rfl]
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨(c₁, c₂), hfmem⟩
  have hle := Finset.single_le_sum
    (f := fun p => pairFiber O (n₁ + n₂) σ M p c) (fun i _ => Nat.zero_le _) hpmem
  calc 1 ≤ pairFiber O (n₁ + n₂) σ M ((n₁, n₂), σ₁.data) c := hfpos
    _ ≤ multCount O (n₁ + n₂) σ M c := hle

open Classical in
/-- ★ **THE POWER DEFECT DECOMPOSITION** — at every finite level, every mass, every
type, every uniformizer:

    convCount = #powerVis + (powerCollisionTotal + powerStrayTotal)

The bracket IS PSL4's power defect (`convCount − #powerVis`), decomposed exactly into
the COLLISION excess over the visible proper power cells plus the STRAY mass (table
pairs whose product is not a visible proper power cell) — the exact replay of SDL's
decomposition on the power fibers. -/
theorem convCount_eq_card_powerVis_add_totals {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 0 < m) (σ : FactorizationType) (M : ℕ) :
    convCount O m σ M
      = Nat.card (powerSectorProperVis O π m σ M)
        + (powerCollisionTotal O π m σ M + powerStrayTotal O π m σ M) := by
  classical
  letI : Fintype (Coeff O m (M + m)) := Fintype.ofFinite _
  have hcoll : powerCollisionTotal O π m σ M
      = ∑ c ∈ Finset.univ.filter (· ∈ powerSectorProperVis O π m σ M),
          (multCount O m σ M c - 1) := by
    unfold powerCollisionTotal
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext c
    simp
  have hstray : powerStrayTotal O π m σ M
      = ∑ c ∈ Finset.univ.filter (· ∉ powerSectorProperVis O π m σ M),
          multCount O m σ M c := by
    unfold powerStrayTotal
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext c
    simp
  have hsplit : ∑ c : Coeff O m (M + m), multCount O m σ M c
      = ∑ c ∈ Finset.univ.filter (· ∈ powerSectorProperVis O π m σ M),
          multCount O m σ M c
        + ∑ c ∈ Finset.univ.filter (· ∉ powerSectorProperVis O π m σ M),
            multCount O m σ M c :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (· ∈ powerSectorProperVis O π m σ M) _).symm
  have hvis : ∑ c ∈ Finset.univ.filter (· ∈ powerSectorProperVis O π m σ M),
        multCount O m σ M c
      = (Finset.univ.filter (· ∈ powerSectorProperVis O π m σ M)).card
        + ∑ c ∈ Finset.univ.filter (· ∈ powerSectorProperVis O π m σ M),
            (multCount O m σ M c - 1) := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have h1 : 1 ≤ multCount O m σ M c :=
      one_le_multCount_of_powerVis hπ hm (Finset.mem_filter.mp hc).2
    omega
  have hcard : Nat.card (powerSectorProperVis O π m σ M)
      = (Finset.univ.filter (· ∈ powerSectorProperVis O π m σ M)).card :=
    natCard_set_eq_card_filter _
  rw [hcoll, hstray, convCount_eq_sum_multCount, hsplit, hvis, hcard]
  omega

end Decomposition

/-! ## §2 — the census laws, the cast identities, and ★★ THE RE-BASE -/

section Laws

/-- **THE VISIBLE PROPER-POWER CELL CENSUS at `(m, σ)`** — the power sector's analogue
of RCD's `VisCountLaw`: the normalized count of visible-corner proper power cells is a
uniform rational limit. -/
def PowerVisCountLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (Nat.card (powerSectorProperVis O π m σ M) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- **THE VISIBLE PROPER-POWER WEIGHT CENSUS at `(m, σ)`**: the normalized
multiplicity-weighted count of visible proper power cells is a uniform rational
limit. -/
def PowerVisWeightLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (powerVisWeight O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The power collision total is the visible weight minus the visible cell count
(exact; every visible proper power cell is hit at least once — the B.42-citing leg). -/
theorem powerCollisionTotal_cast {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (M : ℕ) :
    (powerCollisionTotal O π m σ M : ℝ)
      = (powerVisWeight O π m σ M : ℝ)
        - (Nat.card (powerSectorProperVis O π m σ M) : ℝ) := by
  classical
  unfold powerCollisionTotal powerVisWeight
  rw [Nat.cast_sum, Nat.cast_sum]
  rw [Finset.sum_congr rfl (fun c hc => Nat.cast_sub
    (one_le_multCount_of_powerVis hπ hm ((Set.Finite.mem_toFinset _).mp hc)))]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_one, mul_one]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℝ)
    (toFinset_card_eq_natCard (powerSectorProperVis O π m σ M) (Set.toFinite _))

/-- The power stray total is the table minus the visible weight (exact). -/
theorem powerStrayTotal_cast {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (M : ℕ) :
    (powerStrayTotal O π m σ M : ℝ)
      = (convCount O m σ M : ℝ) - (powerVisWeight O π m σ M : ℝ) := by
  have h1 := powerCollisionTotal_cast hπ hm σ M
  have h2 : (convCount O m σ M : ℝ)
      = (Nat.card (powerSectorProperVis O π m σ M) : ℝ)
        + ((powerCollisionTotal O π m σ M : ℝ) + (powerStrayTotal O π m σ M : ℝ)) := by
    exact_mod_cast convCount_eq_card_powerVis_add_totals hπ hm σ M
  linarith

/-- The power visible weight vanishes on an empty visible proper sector. -/
theorem powerVisWeight_eq_zero_of_empty {π : O} {m : ℕ} {σ : FactorizationType}
    {M : ℕ} (h : powerSectorProperVis O π m σ M = ∅) :
    powerVisWeight O π m σ M = 0 := by
  unfold powerVisWeight
  rw [Set.Finite.toFinset_eq_empty.mpr h, Finset.sum_empty]

/-- The power collision total vanishes on an empty visible proper sector. -/
theorem powerCollisionTotal_eq_zero_of_empty {π : O} {m : ℕ} {σ : FactorizationType}
    {M : ℕ} (h : powerSectorProperVis O π m σ M = ∅) :
    powerCollisionTotal O π m σ M = 0 := by
  unfold powerCollisionTotal
  rw [Set.Finite.toFinset_eq_empty.mpr h, Finset.sum_empty]

end Laws

section ReBase

/-- ★ **The power collision mass rests on the two power censuses** — at every mass and
type (the analogue of RCD's `collisionLaw_of_visLaws`; no pre-named power collision
Prop exists, so the `ZcURLim` conclusion is stated directly). -/
theorem zcURLim_powerCollision_of_visLaws {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hW : PowerVisWeightLaw m σ) (hV : PowerVisCountLaw m σ) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      (powerCollisionTotal O π m σ M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
  refine (zcURLim_sub hW hV).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (powerVisWeight O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      - (Nat.card (powerSectorProperVis O π m σ M) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = (powerCollisionTotal O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [div_sub_div_same, powerCollisionTotal_cast hπ hm σ M]

/-- ★ **The power stray mass rests on the weight census** (under the `< m` decided
value laws, which supply the table law). -/
theorem zcURLim_powerStray_of_visWeightLaw {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (hW : PowerVisWeightLaw m σ) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      (powerStrayTotal O π m σ M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
  refine (zcURLim_sub (zcURLim_conv σ hDV) hW).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      - (powerVisWeight O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = (powerStrayTotal O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [div_sub_div_same, powerStrayTotal_cast hπ hm σ M]

/-- ★★ **THE POWER DEFECT LAW RESTS ON THE CELL CENSUS ALONE** (under the `< m`
decided value laws): the defect is `conv − #powerVis` pointwise, and the table law is
landed — CITE-FREE, exactly parallel to RCD's
`splitConvolutionDefectLaw_of_visCountLaw`. -/
theorem powerConvolutionDefectLaw_of_powerVisCountLaw {m : ℕ} (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (hV : PowerVisCountLaw m σ) : PowerConvolutionDefectLaw m σ := by
  unfold PowerConvolutionDefectLaw
  refine (zcURLim_sub (zcURLim_conv σ hDV) hV).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      - (Nat.card (powerSectorProperVis O π m σ M) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = ((convCount O m σ M : ℝ) - (Nat.card (powerSectorProperVis O π m σ M) : ℝ))
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [div_sub_div_same]

/-- ★★ **THE POWER FRONT RE-BASED**: `PowerSectorLaw m σ` rests on the `< m` decided
value laws plus the pair (`PowerVisCountLaw m σ`, `PowerFullSpanLaw m σ`) — the
convolution-defect premise replaced by its cell census. -/
theorem powerSectorLaw_of_visCountLaw {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (hV : PowerVisCountLaw m σ) (hF : PowerFullSpanLaw m σ) : PowerSectorLaw m σ :=
  powerSectorLaw_of_rebase hm σ hDV
    (powerConvolutionDefectLaw_of_powerVisCountLaw σ hDV hV) hF

end ReBase

/-! ## §3 — THE FIRES: the `m ≤ 4` emptiness (one mass better than split) and the
unramified forcing -/

section Emptiness

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★ **Below mass 5 the proper power sector is EMPTY** (Lean-core): a proper power
cell carries face data with `e' ≥ 2`, `k ≥ 2`, `deg ψ ≥ 1` and
`e'·k·deg ψ < m`, so `4 ≤ e'·k·deg ψ < m` forces `m ≥ 5`.  (One mass better than the
split sector's `m ≤ 3` emptiness: the power residual needs multiplicity `k ≥ 2` where
the split residual needs two coprime factors.) -/
theorem powerSectorProper_eq_empty_of_mass_le_four {π : O} (hπ : Irreducible π)
    {m : ℕ} (hm4 : m ≤ 4) (σ : FactorizationType) (M : ℕ) :
    powerSectorProper O π m σ M = ∅ := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hcp, h₂, e₂, hF₂, hlt₂⟩
  obtain ⟨h, e', k, ψ, hF, he'2, hψm, hψirr, hψ0, hk, heq, hd1, hle⟩ :=
    powerSector_data σ hπ hcp
  obtain ⟨hh, he⟩ := minFaceAt_unique hF hF₂
  subst hh
  subst he
  have hdeg : (classResidualPoly π c h e').natDegree = k * ψ.natDegree := by
    rw [heq, Polynomial.natDegree_pow]
  rw [hdeg] at hlt₂
  have h4 : 4 ≤ e' * (k * ψ.natDegree) := by
    calc 4 = 2 * (2 * 1) := by norm_num
      _ ≤ e' * (k * ψ.natDegree) := Nat.mul_le_mul he'2 (Nat.mul_le_mul hk hd1)
  omega

/-- The visible-corner part inherits the `m ≤ 4` emptiness. -/
theorem powerSectorProperVis_eq_empty_of_mass_le_four {π : O} (hπ : Irreducible π)
    {m : ℕ} (hm4 : m ≤ 4) (σ : FactorizationType) (M : ℕ) :
    powerSectorProperVis O π m σ M = ∅ := by
  refine Set.subset_empty_iff.mp ?_
  have hsub : powerSectorProperVis O π m σ M ⊆ powerSectorProper O π m σ M :=
    fun c hc => hc.1
  rw [powerSectorProper_eq_empty_of_mass_le_four hπ hm4 σ M] at hsub
  exact hsub

/-- At every unramified type the visible proper power sector is empty (UZL's forcing
through IFCG33, exactly as PSL4's `powerLaws_unramified` interior). -/
theorem powerSectorProperVis_eq_empty_unramified {π : O} {m : ℕ}
    (σ : FactorizationType) (hunr : ∀ p ∈ σ.data, p.1 = 1) (M : ℕ) :
    powerSectorProperVis O π m σ M = ∅ := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hcp, -⟩, -⟩
  obtain ⟨⟨⟨hdec, hstr⟩, hsh⟩, -⟩ := hcp.1
  exact Uniformity.Density.IFCG33.not_decidedAt_unramified_of_shallow
    (by omega : m ≤ M + m) hstr hsh hunr hdec

end Emptiness

section Fires

/-- ★ **FIRST FIRE of `PowerVisCountLaw`** — unconditional at mass `≤ 4`. -/
theorem powerVisCountLaw_of_mass_le_four {m : ℕ} (hm4 : m ≤ 4)
    (σ : FactorizationType) : PowerVisCountLaw m σ := by
  unfold PowerVisCountLaw
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  have h0 : Nat.card (powerSectorProperVis O π m σ M) = 0 := by
    rw [powerSectorProperVis_eq_empty_of_mass_le_four hπ hm4 σ M,
      Nat.card_coe_set_eq, Set.ncard_empty]
  show (0 : ℝ) = (Nat.card (powerSectorProperVis O π m σ M) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [h0]
  simp

/-- ★ `PowerVisCountLaw` fires unconditionally at every UNRAMIFIED type. -/
theorem powerVisCountLaw_unramified {m : ℕ} (σ : FactorizationType)
    (hunr : ∀ p ∈ σ.data, p.1 = 1) : PowerVisCountLaw m σ := by
  unfold PowerVisCountLaw
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  have h0 : Nat.card (powerSectorProperVis O π m σ M) = 0 := by
    rw [powerSectorProperVis_eq_empty_unramified σ hunr M,
      Nat.card_coe_set_eq, Set.ncard_empty]
  show (0 : ℝ) = (Nat.card (powerSectorProperVis O π m σ M) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [h0]
  simp

/-- ★ `PowerVisWeightLaw` fires unconditionally at mass `≤ 4`. -/
theorem powerVisWeightLaw_of_mass_le_four {m : ℕ} (hm4 : m ≤ 4)
    (σ : FactorizationType) : PowerVisWeightLaw m σ := by
  unfold PowerVisWeightLaw
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  rw [powerVisWeight_eq_zero_of_empty
    (powerSectorProperVis_eq_empty_of_mass_le_four hπ hm4 σ M)]
  simp

/-- ★ `PowerVisWeightLaw` fires unconditionally at every unramified type. -/
theorem powerVisWeightLaw_unramified {m : ℕ} (σ : FactorizationType)
    (hunr : ∀ p ∈ σ.data, p.1 = 1) : PowerVisWeightLaw m σ := by
  unfold PowerVisWeightLaw
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  rw [powerVisWeight_eq_zero_of_empty
    (powerSectorProperVis_eq_empty_unramified σ hunr M)]
  simp

/-- ★ **NEW FIRE of `PowerConvolutionDefectLaw`** — at mass `≤ 4` under the `< m`
value laws the defect is the whole table (PSL4 had only the unramified fire). -/
theorem powerConvolutionDefectLaw_of_mass_le_four {m : ℕ} (hm4 : m ≤ 4)
    (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    PowerConvolutionDefectLaw m σ :=
  powerConvolutionDefectLaw_of_powerVisCountLaw σ hDV
    (powerVisCountLaw_of_mass_le_four hm4 σ)

/-- ★ The split census `VisCountLaw` fires unconditionally at mass `≤ 3` (RCD's
emptiness, not fired as a `VisCountLaw` instance there). -/
theorem visCountLaw_of_mass_le_three {m : ℕ} (hm3 : m ≤ 3)
    (σ : FactorizationType) : VisCountLaw m σ := by
  unfold VisCountLaw
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  have h0 : Nat.card (splitSectorVis O π m σ M) = 0 := by
    rw [splitSectorVis_eq_empty_of_mass_le_three hπ hm3 σ M,
      Nat.card_coe_set_eq, Set.ncard_empty]
  show (0 : ℝ) = (Nat.card (splitSectorVis O π m σ M) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [h0]
  simp

/-- ★ The split census `VisCountLaw` fires unconditionally at every unramified type. -/
theorem visCountLaw_unramified {m : ℕ} (σ : FactorizationType)
    (hunr : ∀ p ∈ σ.data, p.1 = 1) : VisCountLaw m σ := by
  unfold VisCountLaw
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  have h0 : Nat.card (splitSectorVis O π m σ M) = 0 := by
    rw [splitSectorVis_eq_empty_unramified σ hunr M,
      Nat.card_coe_set_eq, Set.ncard_empty]
  show (0 : ℝ) = (Nat.card (splitSectorVis O π m σ M) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [h0]
  simp

end Fires

/-! ## §4 — ★★ THE UNIFICATION: one Vis-census Prop per residual genre -/

section Unification

/-- **The visible convolution-descent genres**: the two residual genres of RECUR's
trichotomy whose visible cells descend through the convolution table (the leaf genre
does not descend — a leaf cell's residual is irreducible, no mass drop — and the
full-span power genre descends through the fractional recentring instead;
`PowerFullSpanLaw` keeps it). -/
inductive VisGenre : Type
  | split
  | power

/-- **The genre-`g` visible cells** of the carrier: the visible split cells at
`.split`, the visible proper power cells at `.power` — two disjoint sub-genres of the
same visible decided carrier. -/
def visGenreSet (g : VisGenre) (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) : Set (Coeff O m (M + m)) :=
  match g with
  | .split => splitSectorVis O π m σ M
  | .power => powerSectorProperVis O π m σ M

/-- ★★ **THE UNIFIED VISIBLE-GENRE CENSUS at `(g, m, σ)`** — ONE Prop covering both
convolution-defect premises: the normalized count of the genre-`g` visible cells is a
uniform rational limit.  (A single union-count Prop would NOT recover the two defect
laws — a sum limit does not split — so the genre-INDEXED family is the honest joint
form.) -/
def VisCensusLaw (g : VisGenre) (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (Nat.card (visGenreSet g O π m σ M) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- The split instance IS RCD's `VisCountLaw` — definitionally. -/
theorem visCensusLaw_split_iff (m : ℕ) (σ : FactorizationType) :
    VisCensusLaw .split m σ ↔ VisCountLaw m σ := Iff.rfl

/-- The power instance IS `PowerVisCountLaw` — definitionally. -/
theorem visCensusLaw_power_iff (m : ℕ) (σ : FactorizationType) :
    VisCensusLaw .power m σ ↔ PowerVisCountLaw m σ := Iff.rfl

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The genres are disjoint** (RECUR's trichotomy at the visible cells): a visible
cell is a split cell or a proper power cell for at most one genre. -/
theorem visGenreSet_disjoint (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Disjoint (visGenreSet .split O π m σ M) (visGenreSet .power O π m σ M) := by
  have hd := (sectors_disjoint (O := O) (m := m) σ π M).1
  rw [Set.disjoint_left]
  intro c hcs hcp
  exact (Set.disjoint_left.mp hd) hcs.1 hcp.1.1

/-- ★★ The split defect law rests on the unified census (through RCD). -/
theorem splitConvolutionDefectLaw_of_visCensus {m : ℕ} (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (hVC : ∀ g, VisCensusLaw g m σ) : SplitConvolutionDefectLaw m σ :=
  splitConvolutionDefectLaw_of_visCountLaw σ hDV
    ((visCensusLaw_split_iff m σ).mp (hVC .split))

/-- ★★ The power defect law rests on the unified census (through §2's re-base). -/
theorem powerConvolutionDefectLaw_of_visCensus {m : ℕ} (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (hVC : ∀ g, VisCensusLaw g m σ) : PowerConvolutionDefectLaw m σ :=
  powerConvolutionDefectLaw_of_powerVisCountLaw σ hDV
    ((visCensusLaw_power_iff m σ).mp (hVC .power))

/-- ★ The unified census fires at mass `≤ 3` in BOTH genres, unconditionally. -/
theorem visCensusLaw_of_mass_le_three {m : ℕ} (hm3 : m ≤ 3) (σ : FactorizationType) :
    ∀ g, VisCensusLaw g m σ := by
  intro g
  cases g with
  | split => exact (visCensusLaw_split_iff m σ).mpr (visCountLaw_of_mass_le_three hm3 σ)
  | power =>
      exact (visCensusLaw_power_iff m σ).mpr (powerVisCountLaw_of_mass_le_four (by omega) σ)

/-- ★ The unified census fires at every unramified type in BOTH genres,
unconditionally. -/
theorem visCensusLaw_unramified {m : ℕ} (σ : FactorizationType)
    (hunr : ∀ p ∈ σ.data, p.1 = 1) : ∀ g, VisCensusLaw g m σ := by
  intro g
  cases g with
  | split => exact (visCensusLaw_split_iff m σ).mpr (visCountLaw_unramified σ hunr)
  | power => exact (visCensusLaw_power_iff m σ).mpr (powerVisCountLaw_unramified σ hunr)

end Unification

/-! ## §5 — ★★★ THE MASTER RECOMPUTED -/

section Masters

/-- ★★★ **THE CENSUS FRONT ON THE TWO CELL CENSUSES**: the all-degree decided slice
rests on {`VisCountLaw`, `PowerVisCountLaw`, `PowerFullSpanLaw`, `LeafSectorLaw`, the
five `e = 4` remainder laws} — BOTH convolution-defect premises replaced by their
visible-cell censuses. -/
theorem decidedSliceAt_all_of_visCounts
    (hV : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → VisCountLaw e σ)
    (hPV : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerVisCountLaw e σ)
    (hPF : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerFullSpanLaw e σ)
    (hLeaf : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → LeafSectorLaw e σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_defects
    (fun e he hsm σ hσ hwit hram =>
      splitConvolutionDefectLaw_of_visCountLaw σ hsm (hV e he hsm σ hσ hwit hram))
    (fun e he hsm σ hσ hwit hram =>
      powerConvolutionDefectLaw_of_powerVisCountLaw σ hsm (hPV e he hsm σ hσ hwit hram))
    hPF hLeaf hR4

/-- ★★★ **THE CENSUS FRONT ON THE UNIFIED CENSUS** — the master's TWO defect premises
fused into ONE genre-quantified Prop: the all-degree decided slice rests on
{`∀ g, VisCensusLaw g`, `PowerFullSpanLaw`, `LeafSectorLaw`, the five `e = 4`
remainder laws}. -/
theorem decidedSliceAt_all_of_visCensus
    (hVC : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ∀ g, VisCensusLaw g e σ)
    (hPF : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerFullSpanLaw e σ)
    (hLeaf : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → LeafSectorLaw e σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_visCounts
    (fun e he hsm σ hσ hwit hram =>
      (visCensusLaw_split_iff e σ).mp (hVC e he hsm σ hσ hwit hram .split))
    (fun e he hsm σ hσ hwit hram =>
      (visCensusLaw_power_iff e σ).mp (hVC e he hsm σ hσ hwit hram .power))
    hPF hLeaf hR4

end Masters

end Uniformity.Density.IFCG58

end

/-! ## AXCHECK FOOTER — the emptiness fires, the mass fires, the cite-free re-base,
and the unification consumers expect PURE Lean core `{propext, Classical.choice,
Quot.sound}`; the decomposition/casts/unramified route and the masters expect Lean
core + the owner-signed B.42 cite
`Uniformity.Density.Leaf.exists_slope_factorization` (inherited through
PSL4/SDL/IFCG33/IFCG35, never re-consumed).  C.33 and `AX_cellRecursion` must NOT
occur. -/
#print axioms Uniformity.Density.IFCG58.one_le_multCount_of_powerVis
#print axioms Uniformity.Density.IFCG58.convCount_eq_card_powerVis_add_totals
#print axioms Uniformity.Density.IFCG58.powerCollisionTotal_cast
#print axioms Uniformity.Density.IFCG58.powerStrayTotal_cast
#print axioms Uniformity.Density.IFCG58.zcURLim_powerCollision_of_visLaws
#print axioms Uniformity.Density.IFCG58.zcURLim_powerStray_of_visWeightLaw
#print axioms Uniformity.Density.IFCG58.powerConvolutionDefectLaw_of_powerVisCountLaw
#print axioms Uniformity.Density.IFCG58.powerSectorLaw_of_visCountLaw
#print axioms Uniformity.Density.IFCG58.powerSectorProper_eq_empty_of_mass_le_four
#print axioms Uniformity.Density.IFCG58.powerSectorProperVis_eq_empty_of_mass_le_four
#print axioms Uniformity.Density.IFCG58.powerSectorProperVis_eq_empty_unramified
#print axioms Uniformity.Density.IFCG58.powerVisCountLaw_of_mass_le_four
#print axioms Uniformity.Density.IFCG58.powerVisCountLaw_unramified
#print axioms Uniformity.Density.IFCG58.powerVisWeightLaw_of_mass_le_four
#print axioms Uniformity.Density.IFCG58.powerVisWeightLaw_unramified
#print axioms Uniformity.Density.IFCG58.powerConvolutionDefectLaw_of_mass_le_four
#print axioms Uniformity.Density.IFCG58.visCountLaw_of_mass_le_three
#print axioms Uniformity.Density.IFCG58.visCountLaw_unramified
#print axioms Uniformity.Density.IFCG58.visGenreSet_disjoint
#print axioms Uniformity.Density.IFCG58.splitConvolutionDefectLaw_of_visCensus
#print axioms Uniformity.Density.IFCG58.powerConvolutionDefectLaw_of_visCensus
#print axioms Uniformity.Density.IFCG58.visCensusLaw_of_mass_le_three
#print axioms Uniformity.Density.IFCG58.visCensusLaw_unramified
#print axioms Uniformity.Density.IFCG58.decidedSliceAt_all_of_visCounts
#print axioms Uniformity.Density.IFCG58.decidedSliceAt_all_of_visCensus
