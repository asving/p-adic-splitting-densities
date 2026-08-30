/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG38
import Uniformity.ChapI.IFCG43

/-!
# Uniformity.ChapI.IFCG44 — [PSL4 2026-08-30] the power sector fired: the
full-span/proper partition, the face-indexed assembly at the Eisenstein frame,
the recentring instruments, and `PowerSectorLaw` re-based on two named laws

Stage PSL4 of the cone census (design record `runs/wave-c/verdict_PSL4.md`).  PSL2/PSL3
(`IFCG39`/`IFCG43`) landed the power-sector instrument layer; RECUR (`IFCG35`) left
`PowerSectorLaw m σ` as one of the three endgame families.  This file lands the power
sector's DESCENT structure, PSL3's three remainder items in order:

* **§1 the full-span/proper partition** (item 1's frame).  The unique minimal face of a
  power-sector class spans either ALL of `[0, m]` (`e'·deg(residual) = m`, the class is
  PURE — the fractional-recentring territory, where NO `O`-level mass drop exists) or a
  proper top segment (`e'·deg < m` — the residual factor splits off and BOTH factors
  drop mass).  `powerSector = powerSectorFull ⊔ powerSectorProper`, exact at every level.
* **§2 the proper part descends at `O`** (the same convolution table as the split
  sector): a visible-corner proper class is a `mulClass` of two DECIDED classes of
  masses `e'·deg < m` and `m − e'·deg > 0` (B.42 through XHS with the TRIVIAL coprime
  pair `(ψ^k, 1)`), so `#properVis ≤ convCount`; the invisible-corner part is boxed by
  `q^((m−1)(M+m))`.
* **§3 ★ the face-indexed assembly** (item 1).  On the full-span part the lift IS the
  face factor — no factorization, CITE-FREE: the side pins (`sideMin = 0`,
  `sideDeg = D`, `H₀ = h·D`) and the raw purity lattice
  `π^(⌈h(m−j)/e'⌉) ∣ coeff j` fall out of `MinFaceAt` alone (`fullSpan_pins`,
  `fullSpan_raw_dvd`), and the minimal face is RECONSTRUCTED from the lattice + the
  exact corner (`minFaceAt_of_lattice`) — the two-way cell description.
* **§4 ★★ the deep-box cell reading at the Eisenstein frame `(h, d) = (1, 1)`**
  (items 1+2): `fullSpan_resPoly_iff_box` — a full-span class at face `(1, e')` has
  residual `(X − w̄)^D` IFF every lift's `eisKey`-transform lies in the deep recentred
  box over `O' = AdjoinRoot (eisKey π (−z) e')` (PSL3's transfer heart consumed at the
  sector); `fullSpan_image_alphaBox` — under `cellTransport` the structure cells land
  in the `α`-lattice box over `O'`, with the count preserved.
* **§5 the general-`(h, d)` axes** (item 2): the `(h, 1)` axis digit criterion
  (`xres_eq_pow_iff_digits_h` — the ring-free general-`h` replay) and the `(1, d)` axis
  consumption instrument (`zcURLim_compositum_value` — any uniform law instantiated at
  LEG 4's compositum ring keeps a rational pair, reindexed by `q ↦ q^d`).
* **§6 the recentred-mass induction wiring** (item 3): `recentred_decidedSeq_tendsto` —
  under the `< m` decided value laws the recentred decided sequence at the transported
  level `e'·(M + m)` converges to the SAME rational value at the BASE `q`, at every
  Eisenstein recentring ring and every uniformizer (the `Tendsto` reindexing through
  `eis_recentring_stack`).
* **§7 ★★ THE RE-BASE**: `PowerConvolutionDefectLaw m σ` (the proper part's overcount,
  pointwise ≥ 0) and `PowerFullSpanLaw m σ` (the full-span family) — the TWO named
  remaining Props; then `powerSectorLaw_of_rebase`: the two laws + the `< m` value laws
  ⟹ `PowerSectorLaw m σ`, and the census wrappers
  (`decidedSliceAt_all_of_rebased`, `decidedSliceAt_all_of_defects`) leaving the
  all-degree decided slice on the stated finite set of named laws.

## Honest scope

`PowerSectorLaw m σ` is FIRED conditionally on the two named laws, in the recursion's
own descent shape — exactly parallel to IFCG38's split-sector re-base.  What is NOT
in the corpus (and is the two Props' discharge territory): (a) the exact image
description of §2's proper refinement (finite-precision polygon factorization
uniqueness — the same converse IFCG38's defect names); (b) the DECISION transport
across the recentring (`DecidedAt` over `O` at a full-span pure class ⟺ `DecidedAt`
over `O'` of the transported class at the rescaled type — the OM tower step; C136's
territory).  §3–§6 land the complete supply the discharge unit consumes: the cell
description, the `O'`-transport with count preservation, and the smaller-mass
consumption instruments.  The general-`(h, d)` box criterion beyond the landed axes
remains open with the mixed case named in the verdict; nothing weakened;
`PowerSectorLaw`'s statement is IFCG35's, byte-untouched.

## Axiom fence

§1, §3, §4, §5, §6 and the two law DEFINITIONS are pure Lean core.  §2's refinement
and majorant consume exactly the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42) through XHS's
`wideFace_refinement_of_stratum`; §7's assembly and the census wrappers inherit it
(as IFCG35's front already does).  The C.33 cites must NOT occur.  Zero sorries at
landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG44

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG16 (tendsto_decidedSeq_comp)
open Uniformity.Density.IFCG17 (exists_decided_factors monicPoly_coeff_eq_self)
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply le_classNPSupport classNPSupport_le)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq npHgt_monicPoly_top)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_sum shallowSet
  mem_stratum_X_pow_iff pureFaceSet coneRemainderCount ConeRemainderLaw npHeight_coe
  card_setOf_le_resOrd card_pi_set)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains)
open Uniformity.Density.IFCG28 (sideSet_monicPoly_eq resPoly_monicPoly_eq)
open Uniformity.Density.IFCG30 (wideFace_refinement_of_stratum)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_support minFaceAt_min
  minFaceAt_attained_lt minFaceAt_unique exists_minFaceAt_of_shallow
  classResidualPoly classResidualPoly_eq classResidualPoly_natDegree_pos
  powerSector powerSectorCount PowerSectorLaw SplitSectorLaw LeafSectorLaw
  remainderCarrier coneRemainderLaw_of_sectorLaws sectorLaws_unramified
  coneRemainderLaw_ram5_of_sectorLaws decidedSliceAt_all_of_sectorLaws)
open Uniformity.Density.IFCG37 (xres resPoly_x_frame)
open Uniformity.Density.IFCG38 (CornerVisible convPairs convCount mulClassAt
  classResidualPoly_monic zcURLim_mul zcURLim_sub zcURLim_conv
  SplitConvolutionDefectLaw splitSectorLaw_of_defectLaw)
open Uniformity.Density.IFCG39 (powerSector_data powerSector_mass_drop
  eisKey eisKey_monic eisKey_natDegree eis_root_pow_dvd_mk_iff
  devT devT_coeff eis_residueCard)
open Uniformity.Density.IFCG43 (compositum_recentring_stack eis_root_irreducible
  devVec reassVec cellTransport cellTransport_apply cellTransport_symm_apply
  cellTransport_card_image card_coeff_eis eis_recentring_stack zcURLim_eis_value
  eisKey_neg eis_transfer_digits_iff xres_eq_pow_iff_digits resPoly_eq_pow_iff_box)

attribute [local instance] Classical.propDecidable

/-! ## §0 — kit (private replicas of the established supply) -/

section Kit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- B83Kit's membership unfolding for the Classical `sideSet` filter (private copy). -/
private theorem mem_sideSet_iff' {φ f : Polynomial O} {u ℓ j : ℕ} :
    j ∈ sideSet φ f u ℓ ↔ (j < f.natDegree + 1 ∧ OnSide φ f u ℓ j) := by
  classical
  constructor
  · intro hj
    have hj' : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj'
    exact ⟨Finset.mem_range.mp h1, h2⟩
  · intro ⟨h1, h2⟩
    have : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1, h2⟩
    exact this

variable [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The representation supply** (IFCG39's private block, replicated): on a minimal
face the canonical class residual IS every lift's side residual, with the side set,
finite support and height data exported. -/
private theorem resPoly_rep {π : O} (hπ : Irreducible π) {m K h e' : ℕ}
    {c : Coeff O m K} (hF : MinFaceAt c h e')
    {a : Fin m → O} (ha : proj O m K a = c) :
    ∃ (hne : (sideSet X (monicPoly a) h e').Nonempty) (H₀ : ℕ),
      npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) = (H₀ : ℕ∞)
      ∧ suppVal X (monicPoly a) h e' ≠ ⊤
      ∧ classResidualPoly π c h e' = resPoly π X (monicPoly a) h e' hne H₀ := by
  obtain ⟨hh1, hhe, hcop, hface, hAm, hvis⟩ := hF
  have he' : 0 < e' := by omega
  obtain ⟨i, j, hij, hAi, hAj⟩ := hface
  have hilt : i < m := lt_of_lt_of_le hij hAj.1
  obtain ⟨hOni, hsupp⟩ := onSide_monicPoly_of_npAttains hπ he' hvis hAi ha
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  have himem : i ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOni⟩
  have hne : (sideSet X (monicPoly a) h e').Nonempty := ⟨i, himem⟩
  have htop : suppVal X (monicPoly a) h e' ≠ ⊤ := by
    rw [hsupp]
    exact ENat.coe_ne_top _
  have hntop : npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) ≠ ⊤ :=
    npHgt_ne_top_of_onSide he' htop (onSide_of_mem_sideSet (Finset.min'_mem _ hne))
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hntop
  have hw' : ((w : ℕ) : ℕ∞)
      = npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) := hw
  exact ⟨hne, w, hw'.symm, htop,
    classResidualPoly_eq hπ he' hvis ha hne hw'.symm⟩

end Kit

/-! ## §1 — the full-span/proper partition of the power sector (item 1's frame) -/

section Partition

/-- **The FULL-SPAN part of the power sector**: the unique minimal face spans ALL of
`[0, m]` (`e'·deg(residual) = m`) — the class is pure of slope `h/e'`, no `O`-level
mass drop exists, and the fractional recentring is the ONLY descent. -/
def powerSectorFull (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Set (Coeff O m (M + m)) :=
  {c | c ∈ powerSector O π m σ M ∧ ∃ h e' : ℕ, MinFaceAt c h e'
    ∧ e' * (classResidualPoly π c h e').natDegree = m}

/-- **The PROPER part of the power sector**: the minimal face spans a proper top
segment (`e'·deg(residual) < m`) — the face factor splits off and BOTH factors drop
mass (the `O`-level convolution descent applies). -/
def powerSectorProper (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Set (Coeff O m (M + m)) :=
  {c | c ∈ powerSector O π m σ M ∧ ∃ h e' : ℕ, MinFaceAt c h e'
    ∧ e' * (classResidualPoly π c h e').natDegree < m}

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- The power sector partitions into the full-span and proper parts (the face's span
is `≤ m` by the degree bookkeeping, and the face is unique). -/
theorem powerSector_eq_full_union_proper {π : O} (hπ : Irreducible π) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) :
    powerSector O π m σ M
      = powerSectorFull O π m σ M ∪ powerSectorProper O π m σ M := by
  ext c
  constructor
  · intro hc
    obtain ⟨h, e', k, ψ, hF, he'2, hψm, hψirr, hψ0, hk, heq, hd1, hle⟩ :=
      powerSector_data σ hπ hc
    letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
    have hdeg : (classResidualPoly π c h e').natDegree = k * ψ.natDegree := by
      rw [heq, Polynomial.natDegree_pow]
    rcases Nat.lt_or_ge (e' * (classResidualPoly π c h e').natDegree) m with hlt | hge
    · exact Or.inr ⟨hc, h, e', hF, hlt⟩
    · refine Or.inl ⟨hc, h, e', hF, le_antisymm ?_ hge⟩
      rw [hdeg]
      exact hle
  · rintro (⟨hc, -⟩ | ⟨hc, -⟩) <;> exact hc

theorem full_proper_disjoint (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Disjoint (powerSectorFull O π m σ M) (powerSectorProper O π m σ M) := by
  rw [Set.disjoint_left]
  rintro c ⟨-, h₁, e₁, hF₁, hfull⟩ ⟨-, h₂, e₂, hF₂, hlt⟩
  obtain ⟨hh, he⟩ := minFaceAt_unique hF₁ hF₂
  subst hh
  subst he
  omega

/-- The visible-corner part of the proper power sector. -/
def powerSectorProperVis (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) : Set (Coeff O m (M + m)) :=
  powerSectorProper O π m σ M ∩ {c | CornerVisible c}

/-- The invisible-corner part of the proper power sector (the boxed remainder). -/
def powerSectorProperInv (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) : Set (Coeff O m (M + m)) :=
  powerSectorProper O π m σ M ∩ {c | ¬ CornerVisible c}

/-- ★ **THE POWER PARTITION** (count form, exact at every finite level): the power
count is full-span + visible-proper + invisible-proper. -/
theorem powerSectorCount_eq_partition {π : O} (hπ : Irreducible π) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) :
    powerSectorCount O π m σ M
      = Nat.card (powerSectorFull O π m σ M)
        + Nat.card (powerSectorProperVis O π m σ M)
        + Nat.card (powerSectorProperInv O π m σ M) := by
  classical
  haveI : Fintype (Coeff O m (M + m)) := Fintype.ofFinite _
  have hdvi : Disjoint (powerSectorProperVis O π m σ M)
      (powerSectorProperInv O π m σ M) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hv⟩ ⟨-, hnv⟩
    exact hnv hv
  have hprop : powerSectorProper O π m σ M
      = powerSectorProperVis O π m σ M ∪ powerSectorProperInv O π m σ M :=
    (Set.inter_union_compl (powerSectorProper O π m σ M) {c | CornerVisible c}).symm
  have hdfp := full_proper_disjoint π m σ M
  show Nat.card (powerSector O π m σ M : Set (Coeff O m (M + m))) = _
  rw [powerSector_eq_full_union_proper hπ m σ M, hprop, ← Set.union_assoc]
  have hd2 : Disjoint (powerSectorFull O π m σ M ∪ powerSectorProperVis O π m σ M)
      (powerSectorProperInv O π m σ M) := by
    refine Set.disjoint_union_left.mpr ⟨?_, hdvi⟩
    exact Set.disjoint_of_subset_right Set.inter_subset_left hdfp
  have hd1 : Disjoint (powerSectorFull O π m σ M) (powerSectorProperVis O π m σ M) :=
    Set.disjoint_of_subset_right Set.inter_subset_left hdfp
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_union_eq hd2 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq hd1 (Set.toFinite _) (Set.toFinite _)]

end Partition

/-! ## §2 — the proper part descends at `O` (the convolution majorant; B.42) -/

section Proper

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★ **The proper refinement (lift level)** — XHS fired at the power sector's minimal
face with the TRIVIAL coprime pair `(ψ^k, 1)`: every visible-corner proper class
carries face data `(h, e', ψ, k)`, and EVERY lift factors `monicPoly a = g · R` with
`g` monic `(h, e')`-pure of degree `e'·k·deg ψ` carrying residual EXACTLY `ψ^k`, and
`R` monic of the complementary positive degree.  Consumes B.42 through
`wideFace_refinement_of_stratum`. -/
theorem powerSectorProper_refines {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ powerSectorProper O π m σ M) (hvis0 : CornerVisible c) :
    ∃ (h e' k : ℕ) (ψ : Polynomial (resField (X : Polynomial O))),
      MinFaceAt c h e' ∧ 2 ≤ e' ∧ ψ.Monic ∧ Irreducible ψ ∧ 2 ≤ k
      ∧ classResidualPoly π c h e' = ψ ^ k
      ∧ 0 < e' * (k * ψ.natDegree) ∧ e' * (k * ψ.natDegree) < m
      ∧ ∀ a : Fin m → O, proj O m (M + m) a = c →
          ∃ g R : Polynomial O, g.Monic ∧ R.Monic ∧ monicPoly a = g * R
            ∧ g.natDegree = e' * (k * ψ.natDegree)
            ∧ IsPure X g h e'
            ∧ npHgt X g 0 = ((h * (k * ψ.natDegree) : ℕ) : ℕ∞)
            ∧ ∀ hg' : (sideSet X g h e').Nonempty,
                resPoly π X g h e' hg' (h * (k * ψ.natDegree)) = ψ ^ k := by
  obtain ⟨hcp, h₂, e₂, hF₂, hlt₂⟩ := hc
  obtain ⟨h, e', k, ψ, hF, he'2, hψm, hψirr, hψ0, hk, heq, hd1, -⟩ :=
    powerSector_data σ hπ hcp
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have hdegres : (classResidualPoly π c h e').natDegree = k * ψ.natDegree := by
    rw [heq, Polynomial.natDegree_pow]
  have hltm : e' * (k * ψ.natDegree) < m := by
    obtain ⟨hh, he⟩ := minFaceAt_unique hF hF₂
    subst hh
    subst he
    rw [← hdegres]
    exact hlt₂
  have hpos : 0 < e' * (k * ψ.natDegree) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) hd1)
  refine ⟨h, e', k, ψ, hF, he'2, hψm, hψirr, hk, heq, hpos, hltm, ?_⟩
  intro a ha
  obtain ⟨⟨⟨-, hstr⟩, -⟩, -⟩ := hcp.1
  have hu : 0 < h := hF.1
  have hhe : h < e' := hF.2.1
  have he' : 0 < e' := by omega
  have hcop : Nat.Coprime h e' := hF.2.2.1
  have hface : ClassNPFace c h e' := hF.2.2.2.1
  have hvis : NPVisibleAt c h e' := hF.2.2.2.2.2
  have hcorner : classCoeffVal c ⟨0, hm⟩ < M + m := hvis0 ⟨0, hm⟩ rfl
  obtain ⟨a₀, ha₀⟩ := proj_surjective O m (M + m) c
  obtain ⟨hne₀, H₀, hH₀, -, hcrp₀⟩ := resPoly_rep hπ hF ha₀
  have hres : resPoly π X (monicPoly a₀) h e' hne₀ H₀ = ψ ^ k * 1 := by
    rw [mul_one, ← hcrp₀]
    exact heq
  obtain ⟨g, one', R, hg, hone', hR, heqf, hgd, hod, hgp, -, hg0, -, hgres, -⟩ :=
    wideFace_refinement_of_stratum hπ hm hu he' hcop hstr hcorner hface hvis ha₀
      hne₀ hH₀ (hψm.pow k) Polynomial.monic_one (isCoprime_one_right) hres ha
  have hone1 : one' = 1 := by
    rw [Polynomial.natDegree_one, Nat.mul_zero] at hod
    exact (Polynomial.Monic.natDegree_eq_zero hone').mp hod
  rw [hone1, mul_one] at heqf
  have hdegpk : (ψ ^ k).natDegree = k * ψ.natDegree := Polynomial.natDegree_pow ψ k
  rw [hdegpk] at hgd hg0 hgres
  exact ⟨g, R, hg, hR, heqf, hgd, hgp, hg0, hgres⟩

/-- ★ **The proper refinement (class level, decided)**: a visible-corner proper class
IS a `mulClass` of two DECIDED classes of strictly smaller masses, at types summing
to `σ` (the pair determines the class). -/
theorem powerSectorProper_refines_decided {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 0 < m) {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ powerSectorProper O π m σ M) (hvis0 : CornerVisible c) :
    ∃ (n₁ n₂ : ℕ) (_ : 0 < n₁) (_ : 0 < n₂) (hsum : n₁ + n₂ = m)
      (σ₁ σ₂ : FactorizationType)
      (c₁ : Coeff O n₁ (M + m)) (c₂ : Coeff O n₂ (M + m)),
      DecidedAt O n₁ σ₁ (M + m) c₁ ∧ DecidedAt O n₂ σ₂ (M + m) c₂ ∧
      σ₁.data + σ₂.data = σ.data ∧ mulClass c₁ c₂ = hsum.symm ▸ c := by
  obtain ⟨h, e', k, ψ, hF, he'2, hψm, hψirr, hk, heq, hpos, hltm, hlift⟩ :=
    powerSectorProper_refines hπ hm hc hvis0
  have hdecc : DecidedAt O m σ (M + m) c := hc.1.1.1.1.1
  obtain ⟨a, ha⟩ := proj_surjective O m (M + m) c
  obtain ⟨g, R, hg, hR, heqf, hgd, -, -, -⟩ := hlift a ha
  have hn₁ : 0 < g.natDegree := by
    rw [hgd]
    exact hpos
  have hsum : g.natDegree + R.natDegree = m := by
    have h1 : (monicPoly a).natDegree = m := monicPoly_natDegree a
    rw [heqf, hg.natDegree_mul hR] at h1
    exact h1
  have hn₂ : 0 < R.natDegree := by
    rw [hgd] at hsum
    omega
  subst hsum
  have hmp₁ : monicPoly (fun i : Fin g.natDegree => g.coeff (i : ℕ)) = g :=
    monicPoly_coeff_eq_self hg rfl
  have hmp₂ : monicPoly (fun i : Fin R.natDegree => R.coeff (i : ℕ)) = R :=
    monicPoly_coeff_eq_self hR rfl
  have hkey : mulClass
      (proj O g.natDegree (M + (g.natDegree + R.natDegree))
        (fun i => g.coeff (i : ℕ)))
      (proj O R.natDegree (M + (g.natDegree + R.natDegree))
        (fun i => R.coeff (i : ℕ)))
      = c := by
    rw [← mulClass_proj, hmp₁, hmp₂, ← heqf, ← ha]
    congr 1
    funext i
    exact monicPoly_coeff_lt a i.isLt
  rw [← hkey] at hdecc
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hsumty⟩ := exists_decided_factors hdecc
  exact ⟨g.natDegree, R.natDegree, hn₁, hn₂, rfl, σ₁, σ₂, _, _, hσ₁, hσ₂,
    hsumty, hkey⟩

/-- ★ **THE PROPER MAJORANT**: the visible-corner proper power count injects into the
SAME convolution table as the split sector — at every finite level. -/
theorem card_powerSectorProperVis_le {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (M : ℕ) :
    Nat.card (powerSectorProperVis O π m σ M) ≤ convCount O m σ M := by
  classical
  set T : (ℕ × ℕ) × Multiset (ℕ × ℕ) → Set (Coeff O m (M + m)) := fun p =>
    if h : p.1.1 + p.1.2 = m then
      (fun q : Coeff O p.1.1 (M + m) × Coeff O p.1.2 (M + m) =>
          mulClassAt h q.1 q.2) ''
        ((decidedSet O p.1.1 ⟨p.2⟩ (M + m)) ×ˢ (decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m)))
    else ∅ with hT
  have hsub : powerSectorProperVis O π m σ M ⊆ ⋃ p ∈ convPairs m σ, T p := by
    intro c hc
    obtain ⟨hcs, hcv⟩ := hc
    obtain ⟨n₁, n₂, hn₁, hn₂, hsum, σ₁, σ₂, c₁, c₂, hd₁, hd₂, hsumty, hkey⟩ :=
      powerSectorProper_refines_decided hπ hm hcs hcv
    subst hsum
    refine Set.mem_biUnion
      (show ((n₁, n₂), σ₁.data) ∈ convPairs (n₁ + n₂) σ from ?_) ?_
    · rw [convPairs, Finset.mem_product, Finset.mem_filter, Finset.mem_product]
      dsimp only
      refine ⟨⟨⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩,
        rfl, hn₁, hn₂⟩, ?_⟩
      rw [Multiset.mem_toFinset, Multiset.mem_powerset]
      exact Multiset.le_iff_exists_add.mpr ⟨σ₂.data, hsumty.symm⟩
    · show c ∈ T ((n₁, n₂), σ₁.data)
      rw [hT]
      dsimp only
      rw [dif_pos rfl]
      refine ⟨(c₁, c₂), ⟨?_, ?_⟩, ?_⟩
      · exact (show (⟨σ₁.data⟩ : FactorizationType) = σ₁ from rfl) ▸ hd₁
      · have h6 : σ.data - σ₁.data = σ₂.data := by
          rw [← hsumty, add_tsub_cancel_left]
        rw [show (⟨σ.data - σ₁.data⟩ : FactorizationType) = σ₂ from
          FactorizationType.ext h6]
        exact hd₂
      · exact hkey
  calc Nat.card (powerSectorProperVis O π m σ M)
      = (powerSectorProperVis O π m σ M).ncard := Nat.card_coe_set_eq _
    _ ≤ (⋃ p ∈ convPairs m σ, T p).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ∑ p ∈ convPairs m σ, (T p).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ p ∈ convPairs m σ,
          decidedCount O p.1.1 ⟨p.2⟩ (M + m)
            * decidedCount O p.1.2 ⟨σ.data - p.2⟩ (M + m) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpm : p.1.1 + p.1.2 = m := by
          rw [convPairs, Finset.mem_product, Finset.mem_filter] at hp
          exact hp.1.2.1
        rw [hT]
        dsimp only
        rw [dif_pos hpm]
        calc ((fun q : Coeff O p.1.1 (M + m) × Coeff O p.1.2 (M + m) =>
                mulClassAt hpm q.1 q.2) ''
              ((decidedSet O p.1.1 ⟨p.2⟩ (M + m))
                ×ˢ (decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m)))).ncard
            ≤ ((decidedSet O p.1.1 ⟨p.2⟩ (M + m))
                ×ˢ (decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m))).ncard :=
              Set.ncard_image_le (Set.toFinite _)
          _ = (decidedSet O p.1.1 ⟨p.2⟩ (M + m)).ncard
                * (decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m)).ncard := Set.ncard_prod
          _ = decidedCount O p.1.1 ⟨p.2⟩ (M + m)
                * decidedCount O p.1.2 ⟨σ.data - p.2⟩ (M + m) := by
              rw [decidedCount, decidedCount, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    _ = convCount O m σ M := rfl

/-- **The invisible-corner box**: an invisible corner pins the constant coefficient to
the zero window, so the invisible part injects into the remaining `m − 1` coordinates. -/
theorem card_powerSectorProperInv_le (π : O) {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (M : ℕ) :
    Nat.card (powerSectorProperInv O π m σ M) ≤ residueCard O ^ ((m - 1) * (M + m)) := by
  classical
  have hzero : ∀ c ∈ powerSectorProperInv O π m σ M, c ⟨0, hm⟩ = 0 := by
    intro c hc
    obtain ⟨-, hnv⟩ := hc
    have hge : M + m ≤ resOrd (c ⟨0, hm⟩) := by
      by_contra hlt
      refine hnv fun i hi => ?_
      have h5 : i = ⟨0, hm⟩ := Fin.ext hi
      rw [h5]
      exact Nat.lt_of_not_le hlt
    have heq : resOrd (c ⟨0, hm⟩) = M + m :=
      le_antisymm (resOrd_le (c ⟨0, hm⟩)) hge
    exact (resOrd_eq_iff (c ⟨0, hm⟩)).mp heq
  have hinj : Function.Injective (fun c : powerSectorProperInv O π m σ M =>
      (fun j : Fin (m - 1) => c.1 ⟨(j : ℕ) + 1, by omega⟩ : Coeff O (m - 1) (M + m))) := by
    intro c c' hcc
    apply Subtype.ext
    funext j
    rcases j with ⟨jv, hj⟩
    cases jv with
    | zero =>
        exact (hzero c.1 c.2).trans (hzero c'.1 c'.2).symm
    | succ k =>
        have hk : k < m - 1 := by omega
        have := congrFun hcc ⟨k, hk⟩
        simpa using this
  calc Nat.card (powerSectorProperInv O π m σ M)
      ≤ Nat.card (Coeff O (m - 1) (M + m)) := Nat.card_le_card_of_injective _ hinj
    _ = residueCard O ^ ((m - 1) * (M + m)) := card_coeff (m - 1) (M + m)

end Proper

/-! ## §3 — ★ the face-indexed assembly, cite-free half: the full-span side pins,
the raw purity lattice, and the minimal-face reconstruction (item 1) -/

section FullSpanPins

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★ **THE FULL-SPAN SIDE PINS**: on a full-span minimal face the lift needs NO
factorization — `monicPoly a` itself carries the side pins `sideMin = 0`,
`sideDeg = deg(residual)`, pinned corner height `H₀ = h·D`, and the canonical residual
IS its side residual at that height.  (The ℕ∞ bookkeeping of PSL3's remainder item 1;
no cite.) -/
theorem fullSpan_pins {π : O} (hπ : Irreducible π) {m K h e' : ℕ}
    {c : Coeff O m K} (hF : MinFaceAt c h e')
    (hfull : e' * (classResidualPoly π c h e').natDegree = m)
    {a : Fin m → O} (ha : proj O m K a = c) :
    ∃ hne : (sideSet X (monicPoly a) h e').Nonempty,
      sideMin X (monicPoly a) h e' hne = 0
      ∧ sideDeg X (monicPoly a) h e' hne = (classResidualPoly π c h e').natDegree
      ∧ npHgt X (monicPoly a) 0
          = ((h * (classResidualPoly π c h e').natDegree : ℕ) : ℕ∞)
      ∧ classResidualPoly π c h e'
          = resPoly π X (monicPoly a) h e' hne
              (h * (classResidualPoly π c h e').natDegree) := by
  obtain ⟨hne, H₀, hH₀, htop, hcrp⟩ := resPoly_rep hπ hF ha
  obtain ⟨hh1, hhe, hcop, hface, hAm, hvis⟩ := hF
  have he' : 0 < e' := by omega
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  -- the residual degree is the side degree
  have hnd := natDegree_resPoly hπ isKey_X he' hcop htop hne hH₀
  have hsdeg : sideDeg X (monicPoly a) h e' hne
      = (classResidualPoly π c h e').natDegree := by
    rw [hcrp, hnd.1]
  set D : ℕ := (classResidualPoly π c h e').natDegree with hD
  -- the monic point is on the side, so `sideMax = m`
  obtain ⟨hOnm, hsuppm⟩ := onSide_monicPoly_of_npAttains hπ he' hvis hAm ha
  have hmmem : m ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOnm⟩
  have hmax : sideMax X (monicPoly a) h e' hne = m := by
    unfold sideMax
    refine le_antisymm ?_ (Finset.le_max' _ m hmmem)
    have h2 := Finset.max'_mem (sideSet X (monicPoly a) h e') hne
    obtain ⟨h3, -⟩ := mem_sideSet_iff'.mp h2
    omega
  have hminle : sideMin X (monicPoly a) h e' hne ≤ m := by
    unfold sideMin
    exact Finset.min'_le _ m hmmem
  -- the support value is `h·m` (read at the monic point)
  have hsupp_m : suppVal X (monicPoly a) h e' = ((h * m : ℕ) : ℕ∞) := by
    have h6 : e' • npHgt X (monicPoly a) m + ((h * m : ℕ) : ℕ∞)
        = suppVal X (monicPoly a) h e' := hOnm
    rw [npHgt_monicPoly_top, smul_zero, zero_add] at h6
    exact h6.symm
  -- the on-side equation at the left endpoint, extracted to ℕ
  have hOnmin : OnSide X (monicPoly a) h e' (sideMin X (monicPoly a) h e' hne) :=
    onSide_of_mem_sideSet (Finset.min'_mem _ hne)
  have h7 : e' • npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne)
      + ((h * sideMin X (monicPoly a) h e' hne : ℕ) : ℕ∞) = ((h * m : ℕ) : ℕ∞) := by
    rw [← hsupp_m]
    exact hOnmin
  rw [hH₀] at h7
  have h8 : e' * H₀ + h * sideMin X (monicPoly a) h e' hne = h * m := by
    have h9 : ((e' * H₀ + h * sideMin X (monicPoly a) h e' hne : ℕ) : ℕ∞)
        = ((h * m : ℕ) : ℕ∞) := by
      rw [← h7, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add]
    exact Nat.cast_inj.mp h9
  -- coprimality forces `e' ∣ m − sideMin`, and the exact span pins `sideMin = 0`
  have hdvd : e' ∣ h * (m - sideMin X (monicPoly a) h e' hne) := by
    refine ⟨H₀, ?_⟩
    have hsplit : h * (m - sideMin X (monicPoly a) h e' hne)
        + h * sideMin X (monicPoly a) h e' hne = h * m := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hminle]
    have h10 := hsplit.trans h8.symm
    exact Nat.add_right_cancel h10
  obtain ⟨t, ht⟩ : e' ∣ (m - sideMin X (monicPoly a) h e' hne) :=
    hcop.symm.dvd_of_dvd_mul_left hdvd
  have hsdeg_t : sideDeg X (monicPoly a) h e' hne = t := by
    unfold sideDeg
    rw [hmax, ht, Nat.mul_div_cancel_left t he']
  have htD : t = D := by
    rw [← hsdeg_t, hsdeg]
  have hmin0 : sideMin X (monicPoly a) h e' hne = 0 := by
    have h11 : m - sideMin X (monicPoly a) h e' hne = m := by
      rw [ht, htD]
      exact hfull
    omega
  -- the pinned height: `e'·H₀ = h·m = e'·(h·D)`
  have hH0D : H₀ = h * D := by
    rw [hmin0, Nat.mul_zero, Nat.add_zero] at h8
    have h12 : e' * H₀ = e' * (h * D) := by
      rw [h8, ← hfull]
      ring
    exact Nat.eq_of_mul_eq_mul_left he' h12
  refine ⟨hne, hmin0, hsdeg, ?_, ?_⟩
  · rw [← hmin0, hH₀, hH0D]
  · rw [← hH0D]
    exact hcrp

/-- ★ **THE RAW PURITY LATTICE** (cite-free): every lift of a minimal-face class sits
on or above the face line — `π^(⌈h·(m−j)/e'⌉) ∣ coeff j` for every `j < m` (at the
Eisenstein frame `h = 1`, `e'·D = m` this is EXACTLY `resPoly_eq_pow_iff_box`'s purity
hypothesis).  Slope minimality is the whole proof. -/
theorem fullSpan_raw_dvd {π : O} (hπ : Irreducible π) {m K h e' : ℕ}
    {c : Coeff O m K} (hF : MinFaceAt c h e')
    {a : Fin m → O} (ha : proj O m K a = c) :
    ∀ j, j < m → π ^ ((h * (m - j) + (e' - 1)) / e') ∣ (monicPoly a).coeff j := by
  intro j hj
  have he' : 0 < e' := by
    have h1 := hF.1
    have h2 := hF.2.1
    omega
  have hb := minFaceAt_min hF ⟨j, hj⟩
  simp only at hb
  -- the exponent clears the ceiling: `h(m−j) ≤ e'·w ⟹ ⌈h(m−j)/e'⌉ ≤ w`
  have hexp : (h * (m - j) + (e' - 1)) / e' ≤ resOrd (c ⟨j, hj⟩) := by
    have h1 : (h * (m - j) + (e' - 1)) / e' < resOrd (c ⟨j, hj⟩) + 1 := by
      rw [Nat.div_lt_iff_lt_mul he']
      have h2 : (resOrd (c ⟨j, hj⟩) + 1) * e' = e' * resOrd (c ⟨j, hj⟩) + e' := by ring
      rw [h2]
      generalize hA : h * (m - j) = A at hb
      generalize hB : e' * resOrd (c ⟨j, hj⟩) = B at hb ⊢
      omega
    omega
  have hn_le : (h * (m - j) + (e' - 1)) / e' ≤ K :=
    le_trans hexp (resOrd_le _)
  have hcj : c ⟨j, hj⟩ = Ideal.Quotient.mk ((maximalIdeal O) ^ K) (a ⟨j, hj⟩) := by
    rw [← ha]
    rfl
  rw [hcj] at hexp
  have hdvd : π ^ ((h * (m - j) + (e' - 1)) / e') ∣ a ⟨j, hj⟩ :=
    (resOrd_ge_iff hπ hn_le _).mp hexp
  rw [monicPoly_coeff_lt a hj]
  exact hdvd

/-- ★ **THE MINIMAL-FACE RECONSTRUCTION** (the ⟸ of the cell description): a class
whose coordinates sit on or above the full-span line of slope `h/e'` with the corner
EXACT (`resOrd(c₀) = h·D`, `e'·D = m`) has `(h, e')` as its minimal face.  (Slope
minimality, attainment at `0` and at the monic point, and visibility are all read off
the lattice.) -/
theorem minFaceAt_of_lattice {m K h e' D : ℕ} (hh1 : 1 ≤ h) (hhe : h < e')
    (hcop : Nat.Coprime h e') (hfull : e' * D = m) (hmK : m ≤ K)
    {c : Coeff O m K} (hm0 : 0 < m)
    (hlat : ∀ j : Fin m, h * (m - (j : ℕ)) ≤ e' * resOrd (c j))
    (hcorner : resOrd (c ⟨0, hm0⟩) = h * D) :
    MinFaceAt c h e' := by
  have hnpm : npHeight c m = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl m)]
  have hkey : ∀ i, i ≤ m → h * m ≤ e' * npHeight c i + h * i := by
    intro i him
    rcases Nat.lt_or_ge i m with hlt | hge
    · have hnp : npHeight c i = resOrd (c ⟨i, hlt⟩) := by
        have h5 := npHeight_coe c ⟨i, hlt⟩
        simpa using h5
      rw [hnp]
      have h8 := hlat ⟨i, hlt⟩
      simp only at h8
      calc h * m = h * (m - i) + h * i := by
            rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hlt)]
        _ ≤ e' * resOrd (c ⟨i, hlt⟩) + h * i := Nat.add_le_add_right h8 _
    · have him' : i = m := le_antisymm him hge
      subst him'
      rw [hnpm, Nat.mul_zero, Nat.zero_add]
  have hsup : classNPSupport c h e' = h * m := by
    refine le_antisymm (classNPSupport_le c h e') (le_classNPSupport hkey)
  have hnp0 : npHeight c 0 = h * D := by
    have h5 : npHeight c 0 = resOrd (c ⟨0, hm0⟩) := by
      simpa using npHeight_coe c ⟨0, hm0⟩
    rw [h5, hcorner]
  have hA0 : NPAttains c h e' 0 := by
    refine ⟨Nat.zero_le m, ?_⟩
    rw [hsup, hnp0, Nat.mul_zero, Nat.add_zero, ← hfull]
    ring
  have hAm : NPAttains c h e' m := by
    refine ⟨le_refl m, ?_⟩
    rw [hsup, hnpm, Nat.mul_zero, Nat.zero_add]
  have hvis : NPVisibleAt c h e' := by
    show classNPSupport c h e' < e' * K
    rw [hsup]
    calc h * m < e' * m := mul_lt_mul_of_pos_right hhe hm0
      _ ≤ e' * K := Nat.mul_le_mul (le_refl e') hmK
  exact ⟨hh1, hhe, hcop, ⟨0, m, hm0, hA0, hAm⟩, hAm, hvis⟩

/-- **The exact corner** (the forward half): on a full-span face the corner coordinate
has EXACT windowed valuation `h·D` (at or above by slope minimality; not deeper because
the lift's polygon height at `0` is pinned to `H₀ = h·D`). -/
theorem fullSpan_corner {π : O} (hπ : Irreducible π) {m K h e' : ℕ}
    {c : Coeff O m K} (hF : MinFaceAt c h e')
    (hfull : e' * (classResidualPoly π c h e').natDegree = m) (hmK : m ≤ K)
    (hm0 : 0 < m) :
    resOrd (c ⟨0, hm0⟩) = h * (classResidualPoly π c h e').natDegree := by
  obtain ⟨a, ha⟩ := proj_surjective O m K c
  obtain ⟨hne, hmin0, hsdeg, hnpz, hcrp⟩ := fullSpan_pins hπ hF hfull ha
  set D : ℕ := (classResidualPoly π c h e').natDegree
  have he' : 0 < e' := by
    have h1 := hF.1
    have h2 := hF.2.1
    omega
  have hhDm : h * D < m := by
    have h2 := hF.2.1
    calc h * D < e' * D := by
          refine Nat.mul_lt_mul_of_lt_of_le h2 (le_refl D) ?_
          have h3 := classResidualPoly_natDegree_pos hπ hF
          omega
      _ = m := hfull
  -- at or above: slope minimality at the corner
  have hge : h * D ≤ resOrd (c ⟨0, hm0⟩) := by
    have h8 := minFaceAt_min hF ⟨0, hm0⟩
    simp only [Nat.sub_zero] at h8
    have h9 : e' * (h * D) ≤ e' * resOrd (c ⟨0, hm0⟩) := by
      calc e' * (h * D) = h * (e' * D) := by ring
        _ = h * m := by rw [hfull]
        _ ≤ e' * resOrd (c ⟨0, hm0⟩) := h8
    exact Nat.le_of_mul_le_mul_left h9 he'
  -- not deeper: the lift's height at `0` is exactly `h·D`
  have hval : IsDiscreteValuationRing.addVal O ((monicPoly a).coeff 0)
      = ((h * D : ℕ) : ℕ∞) := by
    have h5 := hnpz
    rwa [npHgt_X] at h5
  have hnd : ¬ π ^ (h * D + 1) ∣ a ⟨0, hm0⟩ := by
    intro hdvd
    have h6 : (((h * D + 1 : ℕ) : ℕ∞))
        ≤ IsDiscreteValuationRing.addVal O (a ⟨0, hm0⟩) :=
      (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).mp hdvd
    have h7 : (monicPoly a).coeff 0 = a ⟨0, hm0⟩ := monicPoly_coeff_lt a hm0
    rw [h7] at hval
    rw [hval] at h6
    have h8 : h * D + 1 ≤ h * D := by exact_mod_cast h6
    omega
  have hle : resOrd (c ⟨0, hm0⟩) ≤ h * D := by
    by_contra hlt
    have h9 : h * D + 1 ≤ resOrd (c ⟨0, hm0⟩) := by omega
    have hc0 : c ⟨0, hm0⟩
        = Ideal.Quotient.mk ((maximalIdeal O) ^ K) (a ⟨0, hm0⟩) := by
      rw [← ha]
      rfl
    rw [hc0] at h9
    exact hnd ((resOrd_ge_iff hπ (by omega : h * D + 1 ≤ K) _).mp h9)
  exact le_antisymm hle hge

end FullSpanPins

/-! ## §4 — ★★ the deep-box cell reading at the Eisenstein frame `(h, d) = (1, 1)`
(items 1+2: PSL3's transfer heart consumed at the sector) -/

section FullSpanBox

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★★ **THE CELL READING** (the face-indexed assembly at the landed frame): a
full-span class at face `(1, e')` has canonical residual the `D`-th power of the
recentred linear `(X − z̄)` IF AND ONLY IF every lift's `eisKey`-adic transform lies in
the DEEP RECENTRED BOX over `O' = AdjoinRoot (eisKey π (−z) e')` — PSL3's
`resPoly_eq_pow_iff_box` fired on the sector's own data (pins + purity from §3),
uniform in `q, e', D, z`, every complete DVR. -/
theorem fullSpan_resPoly_iff_box {π : O} (hπ : Irreducible π) {z : O}
    (hz : IsLocalRing.residue O z ≠ 0) {m K e' D : ℕ} (he' : 2 ≤ e')
    {c : Coeff O m K} (hF : MinFaceAt c 1 e')
    (hDeq : (classResidualPoly π c 1 e').natDegree = D) (hfull : e' * D = m)
    {a : Fin m → O} (ha : proj O m K a = c) :
    classResidualPoly π c 1 e'
        = (Polynomial.X - Polynomial.C
            (resFieldXEquiv O (IsLocalRing.residue O z))) ^ D
      ↔ ∀ t, t < D → (AdjoinRoot.root (eisKey π (-z) e')) ^ (e' * (D - t) + 1)
          ∣ AdjoinRoot.mk (eisKey π (-z) e')
              (dev (eisKey π (-z) e') (monicPoly a) t) := by
  have hfull' : e' * (classResidualPoly π c 1 e').natDegree = m := by
    rw [hDeq]
    exact hfull
  obtain ⟨hne, hmin0, hsdeg, -, hcrp⟩ := fullSpan_pins hπ hF hfull' ha
  rw [hDeq] at hsdeg hcrp
  rw [one_mul] at hcrp
  have hGdeg : (monicPoly a).natDegree = e' * D := by
    rw [monicPoly_natDegree, ← hfull]
  have hpure : ∀ j, j < e' * D →
      π ^ ((e' * D - j + (e' - 1)) / e') ∣ (monicPoly a).coeff j := by
    intro j hj
    have hjm : j < m := by
      rw [hfull] at hj
      exact hj
    have h1 := fullSpan_raw_dvd hπ hF ha j hjm
    rw [one_mul] at h1
    have hexp : (e' * D - j + (e' - 1)) / e' = (m - j + (e' - 1)) / e' := by
      rw [hfull]
    rw [hexp]
    exact h1
  rw [hcrp]
  exact resPoly_eq_pow_iff_box hπ hz he' (monicPoly_monic a) hGdeg hpure hne hmin0 hsdeg

/-- **The `α`-lattice box over the recentring ring**: the transported classes whose
coordinates sit one `α`-notch strictly above the `e'`-scaled Eisenstein line — the
recentred image of the full-span residual-power cells. -/
def alphaBox (π w : O) (e' D N' : ℕ)
    [IsDomain (AdjoinRoot (eisKey π w e'))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey π w e'))] :
    Set (Coeff (AdjoinRoot (eisKey π w e')) D N') :=
  {b | ∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ resOrd (b t)}

variable {π w : O} {e' D : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π w e'))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π w e'))]
  [Finite (ResidueField (AdjoinRoot (eisKey π w e')))]

/-- ★ **THE TRANSPORT READING**: the transported class lies in the `α`-lattice box IFF
the lift's transform lies in the deep recentred box — `cellTransport` carries §4's cell
reading to the recentred coordinates (the windowed `α`-valuation reads the divisibility
exactly, one notch inside the window). -/
theorem cellTransport_mem_alphaBox_iff (hπ : Irreducible π)
    (hw : IsLocalRing.residue O w ≠ 0) (he' : 2 ≤ e') {N : ℕ} (hDN : D < N)
    (a : Fin (e' * D) → O) :
    cellTransport hπ hw he' D N (proj O (e' * D) N a) ∈ alphaBox π w e' D (e' * N)
      ↔ ∀ t, t < D → (AdjoinRoot.root (eisKey π w e')) ^ (e' * (D - t) + 1)
          ∣ AdjoinRoot.mk (eisKey π w e') (dev (eisKey π w e') (monicPoly a) t) := by
  have hα : Irreducible (AdjoinRoot.root (eisKey π w e')) :=
    eis_root_irreducible hπ hw he'
  have hside : ∀ t, t < D → e' * (D - t) + 1 ≤ e' * N := by
    intro t ht
    have h1 : e' * (D - t) ≤ e' * (N - 1) :=
      Nat.mul_le_mul (le_refl e') (by omega)
    have h2 : e' * (N - 1) + e' = e' * N := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    generalize hA : e' * (D - t) = A at h1
    generalize hB : e' * (N - 1) = B at h1 h2
    generalize hC : e' * N = C at h2 ⊢
    omega
  rw [cellTransport_apply]
  have hcoord : ∀ (t : ℕ) (ht : t < D),
      proj (AdjoinRoot (eisKey π w e')) D (e' * N) (devVec π w e' D a) ⟨t, ht⟩
        = Ideal.Quotient.mk
            ((maximalIdeal (AdjoinRoot (eisKey π w e'))) ^ (e' * N))
            (AdjoinRoot.mk (eisKey π w e') (dev (eisKey π w e') (monicPoly a) t)) := by
    intro t ht
    have h3 : devVec π w e' D a ⟨t, ht⟩
        = AdjoinRoot.mk (eisKey π w e') (dev (eisKey π w e') (monicPoly a) t) := by
      show (devT (eisKey π w e') D (monicPoly a)).coeff t = _
      exact devT_coeff (monicPoly a) (le_of_lt ht)
    rw [← h3]
    rfl
  constructor
  · intro hb t ht
    have h1 := hb ⟨t, ht⟩
    rw [hcoord t ht] at h1
    exact (resOrd_ge_iff hα (hside t ht) _).mp h1
  · intro hbox t
    rw [hcoord t.1 t.isLt]
    exact (resOrd_ge_iff hα (hside t.1 t.isLt) _).mpr (hbox t.1 t.isLt)

/-- ★ **The `α`-lattice box count is an exact `q`-power** (the free-coordinate supply
for the full-span discharge): coordinate `t` of the box ranges over a
depth-`e'(D−t)+1` sub-window of the level-`e'·N` window, at the BASE residue
cardinality (`eis_residueCard`). -/
theorem card_alphaBox (hπ : Irreducible π) (hw : IsLocalRing.residue O w ≠ 0)
    (he' : 2 ≤ e') {N : ℕ} (hDN : D < N) [Finite (ResidueField O)] :
    Nat.card (alphaBox π w e' D (e' * N))
      = residueCard O ^ (∑ t ∈ Finset.range D, (e' * N - (e' * (D - t) + 1))) := by
  have hside : ∀ t : Fin D, e' * (D - (t : ℕ)) + 1 ≤ e' * N := by
    intro t
    have ht := t.isLt
    have h1 : e' * (D - (t : ℕ)) ≤ e' * (N - 1) :=
      Nat.mul_le_mul (le_refl e') (by omega)
    have h2 : e' * (N - 1) + e' = e' * N := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    generalize hA : e' * (D - (t : ℕ)) = A at h1
    generalize hB : e' * (N - 1) = B at h1 h2
    generalize hC : e' * N = C at h2 ⊢
    omega
  have hset : (alphaBox π w e' D (e' * N))
      = {b : Coeff (AdjoinRoot (eisKey π w e')) D (e' * N) |
          ∀ t : Fin D, b t ∈ {x : Res (AdjoinRoot (eisKey π w e')) (e' * N) |
            e' * (D - (t : ℕ)) + 1 ≤ resOrd x}} := rfl
  rw [hset, card_pi_set]
  have hfac : ∀ t : Fin D,
      Nat.card ({x : Res (AdjoinRoot (eisKey π w e')) (e' * N) |
          e' * (D - (t : ℕ)) + 1 ≤ resOrd x}
        : Set (Res (AdjoinRoot (eisKey π w e')) (e' * N)))
        = residueCard (AdjoinRoot (eisKey π w e'))
            ^ (e' * N - (e' * (D - (t : ℕ)) + 1)) := fun t =>
    card_setOf_le_resOrd (hside t)
  rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_pow_eq_pow_sum,
    eis_residueCard hπ hw he']
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun t => e' * N - (e' * (D - t) + 1)) D

end FullSpanBox

/-! ## §5 — the general-`(h, d)` axes (item 2): the `(h, 1)` digit criterion and the
`(1, d)` compositum consumption instrument -/

section GeneralAxes

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The coefficient read of the x-frame residual under the side pins, at GENERAL slope
numerator `h` (the `(h, 1)`-axis replay of PSL3's private read). -/
private theorem xres_coeff_read_h {π : O} {h e' D : ℕ} {G : Polynomial O}
    (hne : (sideSet (Polynomial.X : Polynomial O) G h e').Nonempty)
    (hmin : sideMin (Polynomial.X : Polynomial O) G h e' hne = 0)
    (hdeg : sideDeg (Polynomial.X : Polynomial O) G h e' hne = D) (j : ℕ) :
    (xres π G h e' hne (h * D)).coeff j
      = if j < D + 1 then digAt π (h * (D - j)) (G.coeff (e' * j)) else 0 := by
  classical
  unfold xres
  rw [hdeg, hmin]
  simp only [zero_add]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (D + 1)) j
    (fun t => digAt π (h * D - h * t) (G.coeff (e' * t)))]
  have hsub : h * D - h * j = h * (D - j) := by
    rcases Nat.le_total j D with hle | hgt
    · obtain ⟨u, hu⟩ : ∃ u, D = j + u := ⟨D - j, by omega⟩
      subst hu
      rw [Nat.mul_add, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    · have h1 : h * D ≤ h * j := Nat.mul_le_mul (le_refl h) hgt
      have h2 : D - j = 0 := by omega
      rw [h2, Nat.mul_zero]
      omega
  rw [hsub]
  simp [Finset.mem_range]

/-- ★★ **THE `(h, 1)`-AXIS DIGIT CRITERION** (item 2, first axis; ring-free): under
the side pins at slope `h/e'` (`sideMin = 0`, `sideDeg = D`, height `H₀ = h·D`), the
x-frame residual is the recentred `D`-th power `(X − z̄)^D` IFF the `D` lattice digits
at heights `h·(D−t)` read the binomial expansion — the general-`h` replay of PSL3's
`xres_eq_pow_iff_digits` (whose `h = 1` instance it recovers).  The `O'`-ring
transport at `h > 1` is NOT claimed (the `h > 1` key ring is not a DVR — the honest
mixed-case remainder). -/
theorem xres_eq_pow_iff_digits_h {π : O} {z : O} {h e' D : ℕ}
    {G : Polynomial O} (hG : G.Monic) (hGdeg : G.natDegree = e' * D)
    (hne : (sideSet (Polynomial.X : Polynomial O) G h e').Nonempty)
    (hmin : sideMin (Polynomial.X : Polynomial O) G h e' hne = 0)
    (hdeg : sideDeg (Polynomial.X : Polynomial O) G h e' hne = D) :
    xres π G h e' hne (h * D)
        = (Polynomial.X - Polynomial.C (IsLocalRing.residue O z)) ^ D
      ↔ ∀ t, t < D → digAt π (h * (D - t)) (G.coeff (e' * t))
          = (D.choose t : IsLocalRing.ResidueField O)
              * (- IsLocalRing.residue O z) ^ (D - t) := by
  have hGtop : G.coeff (e' * D) = 1 := by
    rw [← hGdeg]
    exact hG.coeff_natDegree
  have hpc : ∀ j : ℕ,
      ((Polynomial.X - Polynomial.C (IsLocalRing.residue O z)) ^ D).coeff j
        = (D.choose j : IsLocalRing.ResidueField O)
            * (- IsLocalRing.residue O z) ^ (D - j) := by
    intro j
    rw [sub_eq_add_neg, ← map_neg, Polynomial.coeff_X_add_C_pow]
    ring
  constructor
  · intro heq t ht
    have h1 := congrArg (fun P => Polynomial.coeff P t) heq
    rw [xres_coeff_read_h hne hmin hdeg t] at h1
    rw [if_pos (by omega : t < D + 1), hpc t] at h1
    exact h1
  · intro hdig
    refine Polynomial.ext fun j => ?_
    rw [xres_coeff_read_h hne hmin hdeg j, hpc j]
    rcases Nat.lt_trichotomy j D with hj | hj | hj
    · rw [if_pos (by omega : j < D + 1)]
      exact hdig j hj
    · rw [if_pos (by omega : j < D + 1), hj, Nat.sub_self, Nat.mul_zero, digAt_zero,
        hGtop, map_one, Nat.choose_self, Nat.cast_one, pow_zero, mul_one]
    · rw [if_neg (by omega), Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, zero_mul]

/-- ★ **THE `(1, d)`-AXIS CONSUMPTION INSTRUMENT** (item 2, second axis): any uniform
law family instantiated at LEG 4's COMPOSITUM ring
`O₂ = AdjoinRoot (eisKey (algebraMap π) c₁ e')` over `O₁ = AdjoinRoot φ` keeps the
family's own rational pair, evaluated at `q^{deg φ}` — the unramified stage reindexes
the residue cardinality by `q ↦ q^d`, the Eisenstein stage leaves it fixed.  (So the
recentred limits at every general-`(1, d)` face stay inside ONE rational family in the
base `q`.) -/
theorem zcURLim_compositum_value
    {F : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ}
    (hF : ZcURLim F) :
    ∃ n d : Polynomial ℚ, d ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        ∀ {φ : Polynomial O}, IsKey φ → ∀ {π : O}, Irreducible π →
        ∀ [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)],
        ∀ {c₁ : AdjoinRoot φ}, IsLocalRing.residue (AdjoinRoot φ) c₁ ≠ 0 →
        ∀ {e' : ℕ}, 2 ≤ e' →
        ∀ [IsDomain (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))]
          [IsDiscreteValuationRing
            (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))]
          [IsAdicComplete
            (maximalIdeal (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')))
            (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))]
          [Finite (ResidueField
            (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')))],
        d.eval (((residueCard O ^ φ.natDegree : ℕ) : ℚ)) ≠ 0
        ∧ ∀ π₂ : AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'),
            Irreducible π₂ →
            Filter.Tendsto
              (F (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')) π₂)
              Filter.atTop
              (nhds ((n.eval ((residueCard O ^ φ.natDegree : ℕ) : ℚ)
                / d.eval ((residueCard O ^ φ.natDegree : ℕ) : ℚ) : ℚ) : ℝ)) := by
  obtain ⟨n, d, hd, hval⟩ := hF
  refine ⟨n, d, hd, ?_⟩
  intro O _ _ _ _ _ φ hφ π hπ _ _ c₁ hc₁ e' he' _ _ _ _
  have hcard : residueCard
      (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))
      = residueCard O ^ φ.natDegree := by
    obtain ⟨i1, i2, i3, i4, hAC, hcard', hK⟩ :=
      compositum_recentring_stack hφ hπ hc₁ he'
    exact hcard'
  obtain ⟨hne₂, hlim₂⟩ :=
    hval (AdjoinRoot (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e'))
  rw [hcard] at hne₂
  refine ⟨hne₂, ?_⟩
  intro π₂ hπ₂
  have h1 := hlim₂ π₂ hπ₂
  rwa [hcard] at h1

end GeneralAxes

/-! ## §6 — the recentred-mass induction wiring (item 3): the smaller-mass decided
sequences at the recentring ring, along the transported levels -/

section RecentredWiring

/-- ★ **THE RECENTRED CONSUMPTION INSTRUMENT** (item 3's `Tendsto` reindexing): a
decided value law at mass `k` yields ONE rational pair such that, at every complete
DVR `O`, every Eisenstein recentring ring `O' = AdjoinRoot (eisKey π w e')`, and every
level reindexing `φ` diverging to `∞` (e.g. the transport level `M ↦ e'·(M + m)`),
the recentred decided sequence `decidedSeq O' k τ (φ M)` converges to the value at the
BASE `q` — `q' = q` pays here (`eis_residueCard`), so the face-summed recentred counts
stay inside one rational family. -/
theorem recentred_decidedSeq_tendsto {k : ℕ} {τ : FactorizationType}
    (hDV : DecidedValueLaw k τ) :
    ∃ n d : Polynomial ℚ, d ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        d.eval ((residueCard O : ℕ) : ℚ) ≠ 0
        ∧ ∀ (π w : O), Irreducible π → IsLocalRing.residue O w ≠ 0 →
          ∀ {e' : ℕ}, 2 ≤ e' →
          ∀ [IsDomain (AdjoinRoot (eisKey π w e'))]
            [IsDiscreteValuationRing (AdjoinRoot (eisKey π w e'))]
            [IsAdicComplete (maximalIdeal (AdjoinRoot (eisKey π w e')))
              (AdjoinRoot (eisKey π w e'))]
            [Finite (ResidueField (AdjoinRoot (eisKey π w e')))],
          ∀ {φ : ℕ → ℕ}, Filter.Tendsto φ Filter.atTop Filter.atTop →
            Filter.Tendsto
              (fun M => decidedSeq (AdjoinRoot (eisKey π w e')) k τ (φ M))
              Filter.atTop
              (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
                / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)) := by
  obtain ⟨num, den, hden, hval⟩ := hDV
  refine ⟨num, den, hden, ?_⟩
  intro O _ _ _ _ _
  refine ⟨(hval O).1, ?_⟩
  intro π w hπ hw e' he' _ _ _ _ φ hφ
  obtain ⟨-, hdd⟩ := hval (AdjoinRoot (eisKey π w e'))
  have hcard : residueCard (AdjoinRoot (eisKey π w e')) = residueCard O :=
    eis_residueCard hπ hw he'
  rw [hcard] at hdd
  have ht := tendsto_decidedSeq_comp (O := AdjoinRoot (eisKey π w e')) hφ k τ
  rwa [hdd] at ht

/-- The transport-level reindexing diverges (the `e'·(M + m)` level map of item 3). -/
theorem tendsto_transport_level (e' m : ℕ) (he' : 1 ≤ e') :
    Filter.Tendsto (fun M => e' * (M + m)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono (fun M => ?_) Filter.tendsto_id
  calc (M : ℕ) = 1 * M := (Nat.one_mul M).symm
    _ ≤ e' * (M + m) := Nat.mul_le_mul he' (by omega)

end RecentredWiring

/-! ## §7 — ★★ THE RE-BASE: the power-sector law on the two named laws, and the
census wrappers -/

section ReBase

/-- **THE POWER CONVOLUTION DEFECT LAW at `(m, σ)`** — named remaining Prop 1 of the
power sector: the normalized overcount of the convolution table over the
visible-corner PROPER power cells (pointwise `≥ 0` by §2's majorant) is a uniform
rational limit.  Its discharge territory is the image description of §2's refinement
map — the same finite-precision polygon-factorization-uniqueness genre as IFCG38's
split defect (the two defects share one converse mechanism). -/
def PowerConvolutionDefectLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    ((convCount O m σ M : ℝ) - (Nat.card (powerSectorProperVis O π m σ M) : ℝ))
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- **THE POWER FULL-SPAN LAW at `(m, σ)`** — named remaining Prop 2, the fractional
recentring's residue: the normalized FULL-SPAN count is a uniform rational limit.
Its discharge territory is the DECISION transport across the recentring (the OM tower
step: `DecidedAt` at a full-span pure class over `O` ⟺ `DecidedAt` of the transported
class over `O'` at the `e'`-rescaled type), consumed against §4's two-way cell reading
(`fullSpan_resPoly_iff_box` + `cellTransport_mem_alphaBox_iff` + the count transport)
and §6's recentred smaller-mass instrument (`recentred_decidedSeq_tendsto` at masses
`≤ m/2` by `powerSector_mass_drop`, level `e'·(M+m)` by `tendsto_transport_level`,
summed by `ZcURLim_sum` over the finitely many divisor faces). -/
def PowerFullSpanLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (Nat.card (powerSectorFull O π m σ M) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The defect is pointwise nonnegative (§2's majorant — a genuine overcount, never a
signed fudge). -/
theorem powerDefect_nonneg {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (M : ℕ) :
    (0 : ℝ) ≤ ((convCount O m σ M : ℝ)
        - (Nat.card (powerSectorProperVis O π m σ M) : ℝ))
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)) := by
  apply div_nonneg
  · rw [sub_nonneg]
    exact_mod_cast card_powerSectorProperVis_le hπ hm σ M
  · positivity

/-- **The invisible-corner family vanishes**: squeezed against §2's box, the
normalized invisible-corner proper count is a `ZcURLim` family with value `0`. -/
theorem zcURLim_powerInv {m : ℕ} (hm : 0 < m) (σ : FactorizationType) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      (Nat.card (powerSectorProperInv O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
  refine ⟨0, 1, one_ne_zero, ?_⟩
  intro O _ _ _ _ _
  refine ⟨by simp, ?_⟩
  intro π hπ
  have hval : (((0 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
      / (1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by simp
  rw [hval]
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq1 : (1 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 < residueCard O)
  have hq0 : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := lt_trans one_pos hq1
  have h1 : Filter.Tendsto (fun k : ℕ => (1 / ((residueCard O : ℕ) : ℝ)) ^ k)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hq0).mpr hq1)
  refine squeeze_zero (g := fun M => (1 / ((residueCard O : ℕ) : ℝ)) ^ (M + m))
    (fun M => by positivity) (fun M => ?_) (h1.comp (Filter.tendsto_add_atTop_nat m))
  have hb : (Nat.card (powerSectorProperInv O π m σ M) : ℝ)
      ≤ ((residueCard O : ℕ) : ℝ) ^ ((m - 1) * (M + m)) := by
    exact_mod_cast card_powerSectorProperInv_le π hm σ M
  have hpow : ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      = ((residueCard O : ℕ) : ℝ) ^ ((m - 1) * (M + m))
        * ((residueCard O : ℕ) : ℝ) ^ (M + m) := by
    rw [← pow_add]
    congr 1
    have h5 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
    calc m * (M + m) = ((m - 1) + 1) * (M + m) := by rw [h5]
      _ = (m - 1) * (M + m) + (M + m) := by ring
  calc (Nat.card (powerSectorProperInv O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      ≤ ((residueCard O : ℕ) : ℝ) ^ ((m - 1) * (M + m))
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)) := by gcongr
    _ = (1 / ((residueCard O : ℕ) : ℝ)) ^ (M + m) := by
        rw [hpow, one_div, inv_pow]
        exact div_mul_cancel_left₀
          ((by positivity :
            (0 : ℝ) < ((residueCard O : ℕ) : ℝ) ^ ((m - 1) * (M + m))).ne') _

/-- ★ **Nonvacuity — the unramified instances fire** under the recursion's supply: at
every unramified type both power parts are EMPTY on the shallow stratum (UZL's
forcing), so the defect is the full convolution table (§4 of IFCG38's limit layer)
and the full-span family is `0`. -/
theorem powerLaws_unramified {m : ℕ} (σ : FactorizationType)
    (hunr : ∀ p ∈ σ.data, p.1 = 1)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    PowerConvolutionDefectLaw m σ ∧ PowerFullSpanLaw m σ := by
  have hcar : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (π : O) (M : ℕ),
      ∀ c : Coeff O m (M + m), c ∉ powerSector O π m σ M := by
    intro O _ _ _ _ _ π M c hc
    obtain ⟨⟨⟨hdec, hstr⟩, hsh⟩, -⟩ := hc.1
    exact Uniformity.Density.IFCG33.not_decidedAt_unramified_of_shallow
      (by omega : m ≤ M + m) hstr hsh hunr hdec
  constructor
  · refine (zcURLim_conv σ hDV).congr ?_
    intro O _ _ _ _ _ π hπ M
    have h0 : Nat.card (powerSectorProperVis O π m σ M) = 0 := by
      have hempty : powerSectorProperVis O π m σ M = (∅ : Set (Coeff O m (M + m))) := by
        ext c
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨hcp, -⟩, -⟩
        exact hcar O π M c hcp
      rw [hempty, Nat.card_coe_set_eq, Set.ncard_empty]
    show (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
        = ((convCount O m σ M : ℝ)
            - (Nat.card (powerSectorProperVis O π m σ M) : ℝ))
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    rw [h0]
    simp
  · refine ZcURLim_zero.congr ?_
    intro O _ _ _ _ _ π hπ M
    have h0 : Nat.card (powerSectorFull O π m σ M) = 0 := by
      have hempty : powerSectorFull O π m σ M = (∅ : Set (Coeff O m (M + m))) := by
        ext c
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨hcp, -⟩
        exact hcar O π M c hcp
      rw [hempty, Nat.card_coe_set_eq, Set.ncard_empty]
    show (0 : ℝ) = (Nat.card (powerSectorFull O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    rw [h0]
    simp

/-- ★★ **THE RE-BASE — `PowerSectorLaw` FIRED on the two named laws**, under the
recursion's own supply (the `< m` decided value laws):
`#power = #full + (conv − defect) + #inv`, the convolution family is a `ZcURLim`
(IFCG38 §4), the invisible part vanishes, and the two named laws carry the rest.
`PowerSectorLaw`'s statement is IFCG35's, byte-untouched. -/
theorem powerSectorLaw_of_rebase {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (hD : PowerConvolutionDefectLaw m σ) (hF : PowerFullSpanLaw m σ) :
    PowerSectorLaw m σ := by
  have hconv := zcURLim_conv σ hDV
  have hvis : ZcURLim (fun O _ _ _ _ _ π M =>
      (Nat.card (powerSectorProperVis O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
    refine (zcURLim_sub hconv hD).congr ?_
    intro O _ _ _ _ _ π hπ M
    ring
  refine ((hF.add hvis).add (zcURLim_powerInv hm σ)).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (Nat.card (powerSectorFull O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      + (Nat.card (powerSectorProperVis O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      + (Nat.card (powerSectorProperInv O π m σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = (powerSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [powerSectorCount_eq_partition hπ m σ M]
  push_cast
  ring

end ReBase

/-! ## §8 — ★★★ the census wrappers: the all-degree decided slice on the re-based set -/

section Wrappers

/-- ★★★ **THE CENSUS FRONT, POWER SECTOR RE-BASED**: the all-degree decided slice
rests on {split sector laws, power CONVOLUTION DEFECT laws, power FULL-SPAN laws,
leaf sector laws, the five `e = 4` remainder laws} — `PowerSectorLaw` is GONE from
the premise list, replaced by its two named residues. -/
theorem decidedSliceAt_all_of_rebased
    (hSplit : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → SplitSectorLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerConvolutionDefectLaw e σ)
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
  decidedSliceAt_all_of_sectorLaws hSplit
    (fun e he hsm σ hσ hwit hram =>
      powerSectorLaw_of_rebase (by omega : 0 < e) σ hsm
        (hPD e he hsm σ hσ hwit hram) (hPF e he hsm σ hσ hwit hram))
    hLeaf hR4

/-- ★★★ **THE CENSUS FRONT, BOTH CONVOLUTION SECTORS ON THEIR DEFECTS**: with IFCG38's
split re-base consumed as well, the all-degree decided slice rests on {the split
convolution defect laws, the power convolution defect laws, the power full-span laws,
the leaf sector laws, the five `e = 4` remainder laws}. -/
theorem decidedSliceAt_all_of_defects
    (hSD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → SplitConvolutionDefectLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerConvolutionDefectLaw e σ)
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
  decidedSliceAt_all_of_rebased
    (fun e he hsm σ hσ hwit hram =>
      splitSectorLaw_of_defectLaw (by omega : 0 < e) σ hsm
        (hSD e he hsm σ hσ hwit hram))
    hPD hPF hLeaf hR4

end Wrappers

end Uniformity.Density.IFCG44

end

/-! ## AXCHECK FOOTER — §1/§3/§4/§5/§6 and the two law definitions expect pure Lean
core `{propext, Classical.choice, Quot.sound}`; §2's refinement/majorant and
everything through the unramified forcing or IFCG35's front expects Lean core PLUS
exactly the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42).  The C.33 cites must NOT
occur anywhere. -/

section AxCheck
#print axioms Uniformity.Density.IFCG44.powerSector_eq_full_union_proper
#print axioms Uniformity.Density.IFCG44.full_proper_disjoint
#print axioms Uniformity.Density.IFCG44.powerSectorCount_eq_partition
#print axioms Uniformity.Density.IFCG44.powerSectorProper_refines
#print axioms Uniformity.Density.IFCG44.powerSectorProper_refines_decided
#print axioms Uniformity.Density.IFCG44.card_powerSectorProperVis_le
#print axioms Uniformity.Density.IFCG44.card_powerSectorProperInv_le
#print axioms Uniformity.Density.IFCG44.fullSpan_pins
#print axioms Uniformity.Density.IFCG44.fullSpan_raw_dvd
#print axioms Uniformity.Density.IFCG44.minFaceAt_of_lattice
#print axioms Uniformity.Density.IFCG44.fullSpan_corner
#print axioms Uniformity.Density.IFCG44.fullSpan_resPoly_iff_box
#print axioms Uniformity.Density.IFCG44.alphaBox
#print axioms Uniformity.Density.IFCG44.cellTransport_mem_alphaBox_iff
#print axioms Uniformity.Density.IFCG44.card_alphaBox
#print axioms Uniformity.Density.IFCG44.xres_eq_pow_iff_digits_h
#print axioms Uniformity.Density.IFCG44.zcURLim_compositum_value
#print axioms Uniformity.Density.IFCG44.recentred_decidedSeq_tendsto
#print axioms Uniformity.Density.IFCG44.tendsto_transport_level
#print axioms Uniformity.Density.IFCG44.PowerConvolutionDefectLaw
#print axioms Uniformity.Density.IFCG44.PowerFullSpanLaw
#print axioms Uniformity.Density.IFCG44.powerDefect_nonneg
#print axioms Uniformity.Density.IFCG44.zcURLim_powerInv
#print axioms Uniformity.Density.IFCG44.powerLaws_unramified
#print axioms Uniformity.Density.IFCG44.powerSectorLaw_of_rebase
#print axioms Uniformity.Density.IFCG44.decidedSliceAt_all_of_rebased
#print axioms Uniformity.Density.IFCG44.decidedSliceAt_all_of_defects
end AxCheck
