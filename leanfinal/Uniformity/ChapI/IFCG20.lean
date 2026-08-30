/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG18

/-!
# Uniformity.ChapI.IFCG20 — [DLC 2026-08-30] the deep-linear kernel: the boundary
annihilation and THE FRACTIONAL CELL

FP3 (`IFCG18.lean`) reduced the all-degree decided-slice theorem to TWO kernels; the
second, `DeepLinearClusterLaw`, asks for one uniform rational limit of the loop-corrected
`{(1, m)}` pattern cell `pcellCount / q^(m(M+m))`.  This file answers the unit's key
question — is that law derivable from the RECURSION structure itself? — with a proved
dichotomy:

* **The integer-recentering geometric series is already spent.**  IFCG14's fixed-point
  bridge sums the series `D = B + q^(1-T_m)·D`, and IFCG15's loop subtraction removes
  exactly the once-recentred image of the level-`M`-DECIDED boxes.  What the recursion
  structure still yields — and this file proves, unconditionally — is the annihilation of
  the BOUNDARY between uniform-`M` decidedness and mixed-precision decidedness:

* **§1 the full recentering range**: `fullLoopClassN` extends IFCG15's `loopClassN` from
  decided boxes to ALL mixed boxes (IFCG3's `loopMapN` needs no decidedness); it is
  injective and confined to the deep pattern cell.
* **§2 the mixed truncation** `mixedTruncN : Coeff O m (M+m) →+ MBoxN O m M` (coordinate
  `i` truncated to its natural precision `M + i`) and the pair hom `pairTruncN`, whose
  kernel has exactly `q^(T_m)` elements.
* **§3 ★ the lift correspondence** (`decided_of_mixedTruncN`): if the recentring of a
  mixed box is decided at level `M + m`, then EVERY uniform-`(M+m)` refinement of the box
  is decided — the recentering `f ↦ π^m f((X - γ̃)/π)` is a type-preserving bijection
  between the uniform lifts of the class and the mixed lifts of the box
  (`typeOf_shiftVecN` + `typeOf_scaleVecN`).
* **§4 the exact partition**: `pcellCount + q^(1+κ_m)·decidedCount(M) = #decidedPairs +
  fracCellCount`, where `decidedPairs` are the recentrations decided at the TARGET level
  and `fracCellCount` counts the deep-pattern decided classes in NO recentering range —
  the strictly-fractional-slope cell.  The counting squeeze:
  `q^(1+κ)·decidedCount(M) ≤ #decidedPairs ≤ q^(1-T)·decidedCount(M+m)·q^(m(M+m))`.
* **§5 the boundary annihilation**: normalized, the mismatch is squeezed between
  `q^(1-T)·decidedSeq(M)` and `q^(1-T)·decidedSeq(M+m)`, whose difference tends to `0` by
  the LANDED monotone convergence `decidedSeq_tendsto` alone — NO drainage, NO
  exhaustiveness.  Hence `tendsto_pcell_iff_frac`: the pcell family and the fractional
  family have the same limits.
* **§6 ★ THE EQUIVALENCE**: `DeepFractionalCellLaw` (the kernel's verbatim shape with
  `fracCellCount` in place of `pcellCount`) and
  `deepLinearClusterLaw_iff_fractionalCell : DeepLinearClusterLaw ↔ DeepFractionalCellLaw`
  — an IFF, so nothing is weakened — plus the composite headline
  `decidedSliceAt_all_of_singlePoint_fractional`.

## ⚠ Scoping disposition

`DeepLinearClusterLaw` does NOT fully close here, and cannot from the recursion
structure: the fractional cell has, by construction, NO self-similarity under integer
recentering (it is the complement of the full recentering range at every centre), so no
further geometric series is available.  Its residual content — the visibly-fractional
Newton-slope (denominator ≥ 2) deep clusters — is the same fractional-slope
Okutsu–Montes cone census as `SinglePointAggregateLaw`'s `e ≥ 2` blocks.  The census
front's remaining gap is therefore `SinglePointAggregateLaw` AND `DeepFractionalCellLaw`,
both instances of ONE open heart.

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); the C.33 cite does
not occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG20

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.IFCG1
open Uniformity.Density.IFCG3 (loopMapN loopVecN scaleVecN kappaLoop bigTLoop
  typeOf_scaleVecN mkBoxN_resOut_self map_residue_monicPoly_loopMapN loopMapN_inj
  bigTLoop_eq_kappaLoop_add kappaLoop_add_bigTLoop card_MBoxN_kappaLoop)
open Uniformity.Density.Induction
open Uniformity.Density.IFC7 (resOut mk_resOut)
open Uniformity.Density.IFCG15 (nonloopDecidedSet loopClassN LoopParamsN
  card_range_loopClassN loopImageSeq_eq loopClassN_mem_decidedSet)
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG17 (patternOf)
open Uniformity.Density.IFCG18 (pcellCount SinglePointAggregateLaw DeepLinearClusterLaw
  decidedSliceAt_all_of_singlePoint patternOf_addC_pow)

/-! ## §1 — the full recentering range -/

section FullLoop

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The recentering on ALL mixed boxes**: IFCG15's `loopClassN` without the decidedness
constraint on the box — a residue centre and an arbitrary mixed-precision box. -/
def fullLoopClassN (π : O) {m M : ℕ} (p : ResidueField O × MBoxN O m M) :
    Coeff O m (M + m) :=
  proj O m (M + m) (loopMapN p.1 π p.2)

/-- The full recentering is injective jointly in centre and box (IFCG3's generic loop
bijection, verbatim). -/
theorem fullLoopClassN_injective {π : O} (hπ : Irreducible π) {m M : ℕ} (hm : 0 < m) :
    Function.Injective (fullLoopClassN π (m := m) (M := M)) :=
  loopMapN_inj hπ hm

/-- The constrained loop image sits inside the full recentering range. -/
theorem range_loopClassN_subset_fullRange {π : O} {m M : ℕ} {σ : FactorizationType} :
    Set.range (loopClassN (O := O) (m := m) (M := M) (σ := σ) π)
      ⊆ Set.range (fullLoopClassN π (m := m) (M := M)) := by
  rintro _ ⟨p, rfl⟩
  exact ⟨(p.1, p.2.1), rfl⟩

/-- **The full-range confinement**: every recentred class — decided box or not — has the
deep-linear stratum label `(X + Cγ)^m`, hence pattern `{(1, m)}` (IFCG18 §6's confinement,
extended to the full range). -/
theorem patternOf_stratumPoly_fullLoopClassN {π : O} (hπ : Irreducible π)
    {m M : ℕ} (hm : 1 ≤ m) (p : ResidueField O × MBoxN O m M) :
    patternOf (stratumPoly O m (M + m) (fullLoopClassN π p))
      = ({(1, m)} : Multiset (ℕ × ℕ)) := by
  have hmem : fullLoopClassN π p ∈ levelZeroStratum O m (M + m) ((X + C p.1) ^ m) := by
    rw [mem_levelZeroStratum_iff (by omega)]
    exact ⟨loopMapN p.1 π p.2, rfl, map_residue_monicPoly_loopMapN hπ p.1 p.2⟩
  rw [stratumPoly_eq_of_mem hmem, patternOf_addC_pow p.1 hm]

end FullLoop

/-! ## §2 — the mixed truncation and the `q^(T_m)` fibre law -/

section MixedTrunc

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The mixed truncation**: a uniform level-`(M+m)` class truncated coordinate-wise to
the mixed box precisions `M + i` — the left inverse of refinement, as an additive
homomorphism (all fibres the same size). -/
def mixedTruncN (m M : ℕ) : Coeff O m (M + m) →+ MBoxN O m M :=
  AddMonoidHom.pi fun i =>
    ((resFactor (O := O) (Nat.add_le_add_left i.isLt.le M)).toAddMonoidHom).comp
      (Pi.evalAddMonoidHom (fun _ : Fin m => Res O (M + m)) i)

theorem mixedTruncN_apply (m M : ℕ) (e : Coeff O m (M + m)) (i : Fin m) :
    mixedTruncN (O := O) m M e i
      = resFactor (Nat.add_le_add_left i.isLt.le M) (e i) := rfl

/-- Compatibility: mixed-truncating the uniform class of a lift vector gives its mixed
record. -/
theorem mixedTruncN_proj (m M : ℕ) (b : Fin m → O) :
    mixedTruncN (O := O) m M (proj O m (M + m) b) = mkBoxN m M b := by
  funext i
  exact resFactor_mk (Nat.add_le_add_left i.isLt.le M) (b i)

theorem mixedTruncN_surjective (m M : ℕ) :
    Function.Surjective (mixedTruncN (O := O) m M) := by
  intro d
  obtain ⟨b, hb⟩ := mkBoxN_surjective (O := O) m M d
  exact ⟨proj O m (M + m) b, by rw [mixedTruncN_proj, hb]⟩

/-- The centre-and-class truncation, as one additive homomorphism on the pair. -/
def pairTruncN (m M : ℕ) :
    (ResidueField O × Coeff O m (M + m)) →+ (ResidueField O × MBoxN O m M) :=
  (AddMonoidHom.id (ResidueField O)).prodMap (mixedTruncN m M)

theorem pairTruncN_apply (m M : ℕ) (p : ResidueField O × Coeff O m (M + m)) :
    pairTruncN (O := O) m M p = (p.1, mixedTruncN m M p.2) := rfl

theorem pairTruncN_surjective (m M : ℕ) :
    Function.Surjective (pairTruncN (O := O) m M) := by
  rintro ⟨γ, d⟩
  obtain ⟨e, he⟩ := mixedTruncN_surjective (O := O) m M d
  exact ⟨(γ, e), by rw [pairTruncN_apply, he]⟩

/-- **The fibre exponent is exactly `T_m`**: the kernel of the pair truncation has
`q^(T_m)` elements — `T_m = m(m+1)/2` digits separate the uniform level `M + m` from the
mixed precisions `M + i`. -/
theorem card_ker_pairTruncN (m M : ℕ) :
    Nat.card (pairTruncN (O := O) m M).ker = residueCard O ^ bigTLoop m := by
  have h2 := card_preimage_of_surjective (pairTruncN (O := O) m M)
    (pairTruncN_surjective m M) Set.univ
  rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_coe_set_eq,
    Set.ncard_univ] at h2
  rw [Nat.card_prod, Nat.card_prod, card_coeff, card_MBoxN_kappaLoop] at h2
  have hRF : Nat.card (ResidueField O) = residueCard O := rfl
  rw [hRF] at h2
  have hq : 0 < residueCard O := residueCard_pos O
  have hpos : 0 < residueCard O * residueCard O ^ (m * M + kappaLoop m) :=
    Nat.mul_pos hq (pow_pos hq _)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [← h2]
  have hexp : bigTLoop m + (1 + (m * M + kappaLoop m)) = 1 + m * (M + m) := by
    have hκT := kappaLoop_add_bigTLoop m
    have hd : m * (M + m) = m * M + m * m := by ring
    omega
  symm
  calc residueCard O ^ bigTLoop m * (residueCard O * residueCard O ^ (m * M + kappaLoop m))
      = residueCard O ^ (bigTLoop m + (1 + (m * M + kappaLoop m))) := by ring
    _ = residueCard O ^ (1 + m * (M + m)) := by rw [hexp]
    _ = residueCard O * residueCard O ^ (m * (M + m)) := by
        rw [pow_add, pow_one]

end MixedTrunc

/-! ## §3 — ★ the lift correspondence -/

section LiftCorrespondence

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★ **The lift correspondence**: if the recentring of a mixed box `d` is `σ`-decided at
level `M + m`, then every uniform-`(M+m)` class refining `d` is `σ`-decided.  Every
uniform lift `c` of the refinement is a mixed lift of `d`; its recentring
`shiftVecN (scaleVecN π c) γ̃` is a uniform lift of the recentred class, hence of type
`σ`; and the recentering preserves `typeOf` (`typeOf_shiftVecN`, `typeOf_scaleVecN`).
This is the converse of IFCG3's `decidedAt_of_loopMapN` at the counting level: the
recentring is a type-preserving BIJECTION between the two lift families. -/
theorem decided_of_mixedTruncN {π : O} (hπ : Irreducible π) {m M : ℕ}
    {σ : FactorizationType} {γ : ResidueField O} {d : MBoxN O m M}
    (hdec : fullLoopClassN π (γ, d) ∈ decidedSet O m σ (M + m))
    {e : Coeff O m (M + m)} (he : mixedTruncN (O := O) m M e = d) :
    e ∈ decidedSet O m σ (M + m) := by
  obtain ⟨b, rfl⟩ := proj_surjective O m (M + m) e
  have hbox : mkBoxN (O := O) m M b = d := by
    rw [← mixedTruncN_proj]
    exact he
  show DecidedAt O m σ (M + m) (proj O m (M + m) b)
  refine decidedAt_of_congr hπ (fun c hc => ?_)
  -- `c` is a mixed lift of `d`
  have hcbox : mkBoxN (O := O) m M c = d := by
    rw [← hbox]
    exact ((mkBoxN_eq_iff_dvd hπ).2 (fun i =>
      (pow_dvd_pow π (Nat.add_le_add_left i.isLt.le M)).trans (hc i))).symm
  -- the recentring of `c` is a uniform lift of the recentred class
  have hbase : ∀ i : Fin m, π ^ (M + m) ∣ (scaleVecN π c i - loopVecN π d i) := by
    intro i
    have h1 : mkBoxN (O := O) m M (fun j => resOut (d j)) = mkBoxN m M c := by
      rw [mkBoxN_resOut_self, hcbox]
    have hcong : π ^ (M + (i : ℕ)) ∣ (c i - resOut (d i)) :=
      (mkBoxN_eq_iff_dvd hπ).1 h1 i
    have hval : scaleVecN π c i - loopVecN π d i
        = π ^ (m - (i : ℕ)) * (c i - resOut (d i)) := by
      show π ^ (m - (i : ℕ)) * c i - π ^ (m - (i : ℕ)) * resOut (d i) = _
      ring
    have hsplit : π ^ (M + m) = π ^ (m - (i : ℕ)) * π ^ (M + (i : ℕ)) := by
      rw [← pow_add]
      congr 1
      have := i.isLt
      omega
    rw [hval, hsplit]
    exact mul_dvd_mul_left _ hcong
  have hdvd : ∀ i : Fin m, π ^ (M + m) ∣
      (shiftVecN (scaleVecN π c) (resSect O γ) i - loopMapN γ π d i) :=
    dvd_shiftVecN_sub (resSect O γ) hbase
  have hkey : proj O m (M + m) (shiftVecN (scaleVecN π c) (resSect O γ))
      = fullLoopClassN π (γ, d) :=
    ((proj_eq_iff_dvd hπ (loopMapN γ π d)
      (shiftVecN (scaleVecN π c) (resSect O γ))).2 hdvd).symm
  have hty : typeOf (monicPoly (shiftVecN (scaleVecN π c) (resSect O γ))) = σ :=
    hdec _ hkey
  calc typeOf (monicPoly c)
      = typeOf (monicPoly (scaleVecN π c)) := (typeOf_scaleVecN hπ c).symm
    _ = typeOf (monicPoly (shiftVecN (scaleVecN π c) (resSect O γ))) :=
        (typeOf_shiftVecN _ _).symm
    _ = σ := hty

end LiftCorrespondence

/-! ## §4 — the counting layer: decided pairs, the fibre bound, the exact partition -/

section Counting

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The recentering parameters whose class is decided at the TARGET level `M + m` —
the loop parameters `LoopParamsN` demand decidedness of the truncation at level `M`;
these demand only the target. -/
def decidedPairs (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Set (ResidueField O × MBoxN O m M) :=
  {p | fullLoopClassN π p ∈ decidedSet O m σ (M + m)}

/-- **THE FRACTIONAL CELL**: the deep-pattern part of the non-loop decided set that lies
in NO recentering range — after removing every integral recentring, what remains carries
a visibly-fractional Newton slope at some centre.  This is the named remainder's
carrier. -/
def fracCellCount (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  Nat.card (((nonloopDecidedSet π m σ M
    ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
    \ Set.range (fullLoopClassN π (m := m) (M := M))) : Set (Coeff O m (M + m)))

private theorem pcellCount_eq_ncard (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    pcellCount O π m σ M ({(1, m)} : Multiset (ℕ × ℕ))
      = ((nonloopDecidedSet π m σ M
          ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
          : Set (Coeff O m (M + m))).ncard :=
  Nat.card_coe_set_eq _

private theorem fracCellCount_eq_ncard (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    fracCellCount O π m σ M
      = (((nonloopDecidedSet π m σ M
          ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
          \ Set.range (fullLoopClassN π (m := m) (M := M)))
          : Set (Coeff O m (M + m))).ncard :=
  Nat.card_coe_set_eq _

/-- The fractional cell is part of the pattern cell. -/
theorem fracCellCount_le_pcellCount (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    fracCellCount O π m σ M ≤ pcellCount O π m σ M ({(1, m)} : Multiset (ℕ × ℕ)) := by
  rw [fracCellCount_eq_ncard, pcellCount_eq_ncard]
  exact Set.ncard_le_ncard Set.sdiff_subset (Set.toFinite _)

/-- **The fibre bound**: each decided pair owns `q^(T_m)` distinct decided classes at the
target level (its refinements, decided by the lift correspondence), so
`#decidedPairs · q^(T_m) ≤ q · decidedCount(M + m)`. -/
theorem card_decidedPairs_mul_le {π : O} (hπ : Irreducible π)
    (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Nat.card (decidedPairs π m σ M) * residueCard O ^ bigTLoop m
      ≤ residueCard O * decidedCount O m σ (M + m) := by
  have h1 := card_preimage_of_surjective (pairTruncN (O := O) m M)
    (pairTruncN_surjective m M) (decidedPairs π m σ M)
  rw [card_ker_pairTruncN] at h1
  -- the preimage refines only decided classes (Lemma A)
  have hsub : (pairTruncN (O := O) m M) ⁻¹' (decidedPairs π m σ M)
      ⊆ {p : ResidueField O × Coeff O m (M + m) | p.2 ∈ decidedSet O m σ (M + m)} := by
    rintro ⟨γ, e⟩ hp
    exact decided_of_mixedTruncN hπ hp rfl
  have hle : Nat.card ((pairTruncN (O := O) m M) ⁻¹' (decidedPairs π m σ M))
      ≤ Nat.card {p : ResidueField O × Coeff O m (M + m) |
          p.2 ∈ decidedSet O m σ (M + m)} := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  -- the target set counts q · decidedCount
  have hcard2 : Nat.card {p : ResidueField O × Coeff O m (M + m) |
        p.2 ∈ decidedSet O m σ (M + m)}
      = residueCard O * decidedCount O m σ (M + m) := by
    have hset : {p : ResidueField O × Coeff O m (M + m) |
          p.2 ∈ decidedSet O m σ (M + m)}
        = (Set.univ ×ˢ decidedSet O m σ (M + m)) := by
      ext ⟨γ, e⟩
      simp [Set.mem_prod]
    rw [hset, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
    congr 1
    rw [Nat.card_coe_set_eq, Set.ncard_univ]
    rfl
  calc Nat.card (decidedPairs π m σ M) * residueCard O ^ bigTLoop m
      = residueCard O ^ bigTLoop m * Nat.card (decidedPairs π m σ M) :=
        Nat.mul_comm _ _
    _ = Nat.card ((pairTruncN (O := O) m M) ⁻¹' (decidedPairs π m σ M)) := h1.symm
    _ ≤ Nat.card {p : ResidueField O × Coeff O m (M + m) |
          p.2 ∈ decidedSet O m σ (M + m)} := hle
    _ = residueCard O * decidedCount O m σ (M + m) := hcard2

/-- **THE EXACT PARTITION** of the loop-corrected pattern cell: the pcell plus the loop
image equals the decided pairs plus the fractional cell — the mismatch
`#decidedPairs − q^(1+κ)·decidedCount(M)` is exactly the recentrations decided at the
target level but not at the base level (the "decides inside the window" boundary). -/
theorem pcell_partition {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 1 ≤ m)
    [IsAdicComplete (maximalIdeal O) O]
    (σ : FactorizationType) (M : ℕ) :
    pcellCount O π m σ M ({(1, m)} : Multiset (ℕ × ℕ))
        + residueCard O * decidedCount O m σ M * residueCard O ^ kappaLoop m
      = Nat.card (decidedPairs π m σ M) + fracCellCount O π m σ M := by
  -- (1) the pattern cell splits along the full recentering range
  have h1 := (Set.ncard_inter_add_ncard_sdiff_eq_ncard
    ((nonloopDecidedSet π m σ M
      ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
      : Set (Coeff O m (M + m)))
    (Set.range (fullLoopClassN π (m := m) (M := M))) (Set.toFinite _)).symm
  -- (2) the range part is (decided ∩ range) minus the loop image
  have h2 : ((nonloopDecidedSet π m σ M
        ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
        ∩ Set.range (fullLoopClassN π (m := m) (M := M)))
      = (decidedSet O m σ (M + m) ∩ Set.range (fullLoopClassN π (m := m) (M := M)))
        \ Set.range (loopClassN (O := O) (m := m) (M := M) (σ := σ) π) := by
    ext c
    simp only [nonloopDecidedSet, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨⟨hD, hnL⟩, -⟩, hF⟩
      exact ⟨⟨hD, hF⟩, hnL⟩
    · rintro ⟨⟨hD, hF⟩, hnL⟩
      obtain ⟨p, rfl⟩ := hF
      exact ⟨⟨⟨hD, hnL⟩, patternOf_stratumPoly_fullLoopClassN hπ hm p⟩, ⟨p, rfl⟩⟩
  -- (3) the loop image sits inside (decided ∩ range)
  have hLsub : Set.range (loopClassN (O := O) (m := m) (M := M) (σ := σ) π)
      ⊆ decidedSet O m σ (M + m) ∩ Set.range (fullLoopClassN π (m := m) (M := M)) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨loopClassN_mem_decidedSet hπ p, ⟨(p.1, p.2.1), rfl⟩⟩
  have h3 := Set.ncard_sdiff_add_ncard_of_subset hLsub
  -- (4) (decided ∩ range) is counted by the decided pairs
  have h4 : (decidedSet O m σ (M + m) ∩ Set.range (fullLoopClassN π (m := m) (M := M)))
      = fullLoopClassN π '' (decidedPairs π m σ M) := by
    ext c
    constructor
    · rintro ⟨hD, ⟨p, rfl⟩⟩
      exact ⟨p, hD, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp, ⟨p, rfl⟩⟩
  have h5 : (fullLoopClassN π '' (decidedPairs π m σ M)).ncard
      = Nat.card (decidedPairs π m σ M) := by
    rw [Set.ncard_image_of_injective _ (fullLoopClassN_injective hπ (by omega)),
      Nat.card_coe_set_eq]
  -- (5) the loop image count (IFCG15)
  have h6 : (Set.range (loopClassN (O := O) (m := m) (M := M) (σ := σ) π)).ncard
      = residueCard O * decidedCount O m σ M * residueCard O ^ kappaLoop m := by
    rw [← Nat.card_coe_set_eq]
    exact card_range_loopClassN hπ (by omega) σ M
  -- assemble
  have e2 : ((nonloopDecidedSet π m σ M
        ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
        ∩ Set.range (fullLoopClassN π (m := m) (M := M))).ncard
      = ((decidedSet O m σ (M + m) ∩ Set.range (fullLoopClassN π (m := m) (M := M)))
        \ Set.range (loopClassN (O := O) (m := m) (M := M) (σ := σ) π)).ncard := by
    rw [h2]
  have e4 : (decidedSet O m σ (M + m)
        ∩ Set.range (fullLoopClassN π (m := m) (M := M))).ncard
      = Nat.card (decidedPairs π m σ M) := by
    rw [h4]
    exact h5
  rw [pcellCount_eq_ncard, fracCellCount_eq_ncard]
  omega

end Counting

/-! ## §5 — the boundary annihilation (the ℝ squeeze) -/

section Squeeze

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **The boundary annihilation**: the normalized pattern-cell family and the
normalized fractional-cell family have exactly the same limits — the mismatch (the
window boundary) is squeezed between `q^(1−T)·decidedSeq(M)` and
`q^(1−T)·decidedSeq(M+m)`, and `decidedSeq` converges (LANDED `decidedSeq_tendsto`; NO
drainage input). -/
theorem tendsto_pcell_iff_frac {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 1 ≤ m)
    (σ : FactorizationType) (L : ℝ) :
    Filter.Tendsto (fun M => (fracCellCount O π m σ M : ℝ)
        / (residueCard O : ℝ) ^ (m * (M + m))) Filter.atTop (nhds L)
      ↔ Filter.Tendsto (fun M => (pcellCount O π m σ M ({(1, m)} : Multiset (ℕ × ℕ)) : ℝ)
        / (residueCard O : ℝ) ^ (m * (M + m))) Filter.atTop (nhds L) := by
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast residueCard_pos O
  have hT1 : 1 ≤ bigTLoop m := by
    have := bigTLoop_eq_kappaLoop_add m
    omega
  -- the pointwise identity: pcell-norm = frac-norm + boundary
  have hidentity : ∀ M : ℕ,
      (pcellCount O π m σ M ({(1, m)} : Multiset (ℕ × ℕ)) : ℝ)
          / (residueCard O : ℝ) ^ (m * (M + m))
        = (fracCellCount O π m σ M : ℝ) / (residueCard O : ℝ) ^ (m * (M + m))
          + ((Nat.card (decidedPairs π m σ M) : ℝ)
              / (residueCard O : ℝ) ^ (m * (M + m))
            - ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ M) := by
    intro M
    have hpart := pcell_partition (O := O) hπ hm σ M
    have hpartR : (pcellCount O π m σ M ({(1, m)} : Multiset (ℕ × ℕ)) : ℝ)
        + ((residueCard O * decidedCount O m σ M * residueCard O ^ kappaLoop m : ℕ) : ℝ)
        = (Nat.card (decidedPairs π m σ M) : ℝ) + (fracCellCount O π m σ M : ℝ) := by
      exact_mod_cast hpart
    have hloop : ((residueCard O * decidedCount O m σ M
          * residueCard O ^ kappaLoop m : ℕ) : ℝ)
          / (residueCard O : ℝ) ^ (m * (M + m))
        = ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ M := by
      rw [← card_range_loopClassN hπ (by omega) σ M]
      exact loopImageSeq_eq hπ (by omega) σ M
    have hdiv := congrArg
      (fun x : ℝ => x / (residueCard O : ℝ) ^ (m * (M + m))) hpartR
    simp only [add_div] at hdiv
    rw [hloop] at hdiv
    linarith
  -- the boundary is nonnegative
  have herr0 : ∀ M : ℕ, 0 ≤ (Nat.card (decidedPairs π m σ M) : ℝ)
      / (residueCard O : ℝ) ^ (m * (M + m))
      - ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ M := by
    intro M
    have hQ : (0 : ℝ) < (residueCard O : ℝ) ^ (m * (M + m)) := pow_pos hq0 _
    have hle : (fracCellCount O π m σ M : ℝ)
        ≤ (pcellCount O π m σ M ({(1, m)} : Multiset (ℕ × ℕ)) : ℝ) := by
      exact_mod_cast fracCellCount_le_pcellCount (O := O) π m σ M
    have hdivle : (fracCellCount O π m σ M : ℝ) / (residueCard O : ℝ) ^ (m * (M + m))
        ≤ (pcellCount O π m σ M ({(1, m)} : Multiset (ℕ × ℕ)) : ℝ)
          / (residueCard O : ℝ) ^ (m * (M + m)) := by
      gcongr
    have := hidentity M
    linarith
  -- the boundary's upper bound: the decided pairs are dominated by the target level
  have herrle : ∀ M : ℕ, (Nat.card (decidedPairs π m σ M) : ℝ)
      / (residueCard O : ℝ) ^ (m * (M + m))
      - ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ M
      ≤ ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ (M + m)
        - ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ M := by
    intro M
    have hQ : (0 : ℝ) < (residueCard O : ℝ) ^ (m * (M + m)) := pow_pos hq0 _
    have hd : (0 : ℝ) < (residueCard O : ℝ) ^ (bigTLoop m - 1) := pow_pos hq0 _
    -- the ℕ bound, with one q cancelled
    have hNat : Nat.card (decidedPairs π m σ M) * residueCard O ^ (bigTLoop m - 1)
        ≤ decidedCount O m σ (M + m) := by
      have hfull := card_decidedPairs_mul_le hπ m σ M
      have hsplit : residueCard O ^ bigTLoop m
          = residueCard O ^ (bigTLoop m - 1) * residueCard O := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hsplit, ← Nat.mul_assoc] at hfull
      have hq : 0 < residueCard O := residueCard_pos O
      refine Nat.le_of_mul_le_mul_right ?_ hq
      calc Nat.card (decidedPairs π m σ M) * residueCard O ^ (bigTLoop m - 1)
            * residueCard O
          ≤ residueCard O * decidedCount O m σ (M + m) := hfull
        _ = decidedCount O m σ (M + m) * residueCard O := by ring
    have hcast : (Nat.card (decidedPairs π m σ M) : ℝ)
        * (residueCard O : ℝ) ^ (bigTLoop m - 1)
        ≤ (decidedCount O m σ (M + m) : ℝ) := by
      exact_mod_cast hNat
    have hS : (Nat.card (decidedPairs π m σ M) : ℝ)
        / (residueCard O : ℝ) ^ (m * (M + m))
        ≤ ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ (M + m) := by
      unfold decidedSeq
      rw [div_le_iff₀ hQ]
      have hexp : ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹
          * ((decidedCount O m σ (M + m) : ℝ)
            / (residueCard O : ℝ) ^ (m * (M + m)))
          * (residueCard O : ℝ) ^ (m * (M + m))
          = (decidedCount O m σ (M + m) : ℝ)
            / (residueCard O : ℝ) ^ (bigTLoop m - 1) := by
        field_simp
      rw [hexp, le_div_iff₀ hd]
      linarith
    linarith
  -- the squeeze: the boundary tends to 0
  have hE : Filter.Tendsto (fun M => (Nat.card (decidedPairs π m σ M) : ℝ)
      / (residueCard O : ℝ) ^ (m * (M + m))
      - ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ M)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun M => decidedSeq O m σ (M + m)) Filter.atTop
        (nhds (decidedDensity O m σ)) :=
      (decidedSeq_tendsto (O := O) m σ).comp (Filter.tendsto_add_atTop_nat m)
    have hg := (h1.const_mul (((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹)).sub
      ((decidedSeq_tendsto (O := O) m σ).const_mul
        (((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹))
    rw [sub_self] at hg
    exact squeeze_zero herr0 herrle hg
  constructor
  · intro hf
    have hsum := hf.add hE
    rw [add_zero] at hsum
    refine hsum.congr fun M => ?_
    exact (hidentity M).symm
  · intro hp
    have hsub := hp.sub hE
    rw [sub_zero] at hsub
    refine hsub.congr fun M => ?_
    have := hidentity M
    linarith

end Squeeze

/-! ## §6 — ★ THE NAMED REMAINDER and THE EQUIVALENCE -/

section Laws

/-- ★ **THE FRACTIONAL CELL LAW** — the deep-linear kernel's residual content, in the
kernel's verbatim shape: the strictly-fractional deep cell (the `{(1, m)}` pattern cell
with EVERY integral recentring removed — decided-box recentrings by the loop
subtraction, the rest by the boundary annihilation) has ONE uniform rational limit,
given the smaller value laws.  Mathematically: the visibly-fractional Newton-slope
(denominator `≥ 2`) deep clusters — the same fractional-slope Okutsu–Montes cone census
as `SinglePointAggregateLaw`'s `e ≥ 2` blocks. -/
def DeepFractionalCellLaw : Prop :=
  ∀ m : ℕ, 4 ≤ m →
    (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
    ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
      ∃ n d : Polynomial ℚ, d ≠ 0 ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
          [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
          d.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
            ∀ π : O, Irreducible π →
              Filter.Tendsto
                (fun M => (fracCellCount O π m σ M : ℝ)
                  / (residueCard O : ℝ) ^ (m * (M + m)))
                Filter.atTop
                (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
                  / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))

/-- ★★ **THE EQUIVALENCE**: the deep-linear cluster kernel IS the fractional cell law —
an iff, so the reformulation weakens nothing.  The recursion structure's whole
contribution to the kernel is the boundary annihilation inside this proof; what remains
open is strictly the fractional-slope census. -/
theorem deepLinearClusterLaw_iff_fractionalCell :
    DeepLinearClusterLaw ↔ DeepFractionalCellLaw := by
  constructor
  · intro h m hm hsm σ hσ hwit
    obtain ⟨n, d, hd, hlaw⟩ := h m hm hsm σ hσ hwit
    refine ⟨n, d, hd, ?_⟩
    intro O _ _ _ _ _
    obtain ⟨hne, hlim⟩ := hlaw O
    exact ⟨hne, fun π hπ =>
      (tendsto_pcell_iff_frac hπ (by omega) σ _).2 (hlim π hπ)⟩
  · intro h m hm hsm σ hσ hwit
    obtain ⟨n, d, hd, hlaw⟩ := h m hm hsm σ hσ hwit
    refine ⟨n, d, hd, ?_⟩
    intro O _ _ _ _ _
    obtain ⟨hne, hlim⟩ := hlaw O
    exact ⟨hne, fun π hπ =>
      (tendsto_pcell_iff_frac hπ (by omega) σ _).1 (hlim π hπ)⟩

/-- ★★ **THE CAPSTONE REDUCTION, refined**: the single-point kernel and the FRACTIONAL
cell law fire the all-degree decided slice — IFCG18's reduction with the deep-linear
kernel replaced by its strictly smaller (and provably equivalent) fractional remainder. -/
theorem decidedSliceAt_all_of_singlePoint_fractional
    (hSP : SinglePointAggregateLaw) (hDF : DeepFractionalCellLaw) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_singlePoint hSP (deepLinearClusterLaw_iff_fractionalCell.mpr hDF)

end Laws

end Uniformity.Density.IFCG20

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}`
everywhere; the C.33 cite must NOT occur. -/

#print axioms Uniformity.Density.IFCG20.fullLoopClassN_injective
#print axioms Uniformity.Density.IFCG20.patternOf_stratumPoly_fullLoopClassN
#print axioms Uniformity.Density.IFCG20.card_ker_pairTruncN
#print axioms Uniformity.Density.IFCG20.decided_of_mixedTruncN
#print axioms Uniformity.Density.IFCG20.card_decidedPairs_mul_le
#print axioms Uniformity.Density.IFCG20.pcell_partition
#print axioms Uniformity.Density.IFCG20.tendsto_pcell_iff_frac
#print axioms Uniformity.Density.IFCG20.deepLinearClusterLaw_iff_fractionalCell
#print axioms Uniformity.Density.IFCG20.decidedSliceAt_all_of_singlePoint_fractional
