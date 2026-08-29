/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG14

/-!
# Uniformity.ChapI.IFCG15 — [FP0 2026-08-29] the counting-recurrence boundary

This file audits and advances IFCG14's last socket.  It proves the full generic loop-cell
count, identifies its members as decided classes, and isolates the exact remaining
non-loop statement as `RationalNonloopRemainderAt`.  The latter is canonically formulated:
its sequence is target density at level `M + m` minus the proved loop contribution at
level `M`, so no arbitrary auxiliary sequence can hide the finite-level counting gap.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFCG15

open IsLocalRing Polynomial
open Uniformity.Density.IFCG1 (MBoxN mtruncN)
open Uniformity.Density.IFCG3 (bigTLoop kappaLoop loopMapN)
open Uniformity.Density.IFCG14

/-! ## §1 — the loop cell: exact generic finite-level count -/

/-- Parameters for the mass-`m` loop contribution to the decided `σ` classes at level
`M + m`: a residue centre and a mixed-precision lift of a decided level-`M` class. -/
abbrev LoopParamsN (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (m : ℕ) (σ : FactorizationType) (M : ℕ) :=
  ResidueField O ×
    {d : MBoxN O m M // mtruncN (O := O) m M d ∈ decidedSet O m σ M}

/-- The loop parameter map into level-`M+m` coefficient classes. -/
def loopClassN {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] {m M : ℕ} (π : O) {σ : FactorizationType}
    (p : LoopParamsN O m σ M) : Coeff O m (M + m) :=
  proj O m (M + m) (loopMapN p.1 π p.2.1)

/-- The generic loop map is injective jointly in its centre and decided mixed-box
parameter. -/
theorem loopClassN_injective {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] {π : O} (hπ : Irreducible π)
    {m M : ℕ} (hm : 0 < m) {σ : FactorizationType} :
    Function.Injective (loopClassN (O := O) (m := m) (M := M) (σ := σ) π) := by
  rintro ⟨γ, ⟨d, hd⟩⟩ ⟨γ', ⟨d', hd'⟩⟩ h
  have hp : (γ, d) = (γ', d') :=
    IFCG3.loopMapN_inj hπ hm h
  cases hp
  rfl

/-- Every class in the loop image is decided at the same factorization label. -/
theorem loopClassN_mem_decidedSet {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π)
    {m M : ℕ} {σ : FactorizationType} (p : LoopParamsN O m σ M) :
    loopClassN π p ∈ decidedSet O m σ (M + m) := by
  exact IFCG3.decidedAt_of_loopMapN hπ p.2.2

/-- The loop image is a subset of the target decided set. -/
theorem range_loopClassN_subset_decidedSet {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π)
    {m M : ℕ} {σ : FactorizationType} :
    Set.range (loopClassN (O := O) (m := m) (M := M) (σ := σ) π) ⊆
      decidedSet O m σ (M + m) := by
  rintro _ ⟨p, rfl⟩
  exact loopClassN_mem_decidedSet hπ p

/-- Exact cardinality of the loop parameter space: one residue centre and the constant
`q^κ_m` mixed-box fibre over every decided level-`M` class. -/
theorem card_loopParamsN {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Nat.card (LoopParamsN O m σ M) =
      residueCard O * decidedCount O m σ M * residueCard O ^ kappaLoop m := by
  rw [Nat.card_prod]
  change residueCard O *
      Nat.card ((mtruncN (O := O) m M) ⁻¹' (decidedSet O m σ M)) = _
  rw [IFCG3.card_preimage_mtruncN_kappaLoop]
  unfold decidedCount
  ring

/-- Exact cardinality of the loop image. -/
theorem card_range_loopClassN {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] {π : O} (hπ : Irreducible π)
    {m : ℕ} (hm : 0 < m) (σ : FactorizationType) (M : ℕ) :
    Nat.card (Set.range (loopClassN (O := O) (m := m) (M := M) (σ := σ) π)) =
      residueCard O * decidedCount O m σ M * residueCard O ^ kappaLoop m := by
  rw [Nat.card_range_of_injective (loopClassN_injective hπ hm), card_loopParamsN]

/-- Subtraction-free form of the exact loop weight.  After normalizing the two levels,
this is precisely the factor `q^{-(T_m-1)}` in IFCG14's `LoopStepLaw`. -/
theorem loopClassN_weight {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] {π : O} (hπ : Irreducible π)
    {m : ℕ} (hm : 0 < m) (σ : FactorizationType) (M : ℕ) :
    Nat.card (Set.range (loopClassN (O := O) (m := m) (M := M) (σ := σ) π))
          * residueCard O ^ (bigTLoop m - 1) * residueCard O ^ (m * M)
      = decidedCount O m σ M * residueCard O ^ (m * (M + m)) := by
  rw [card_range_loopClassN hπ hm]
  have hT : 1 ≤ bigTLoop m := by
    rw [IFCG3.bigTLoop_eq_kappaLoop_add]
    omega
  have hexp : 1 + kappaLoop m + (bigTLoop m - 1) + m * M = m * (M + m) := by
    have hsq := IFCG3.kappaLoop_add_bigTLoop m
    calc
      1 + kappaLoop m + (bigTLoop m - 1) + m * M
          = kappaLoop m + bigTLoop m + m * M := by omega
      _ = m * m + m * M := by rw [hsq]
      _ = m * (M + m) := by ring
  have hpow : residueCard O * residueCard O ^ kappaLoop m
          * residueCard O ^ (bigTLoop m - 1) * residueCard O ^ (m * M)
      = residueCard O ^ (m * (M + m)) := by
    calc
      residueCard O * residueCard O ^ kappaLoop m
            * residueCard O ^ (bigTLoop m - 1) * residueCard O ^ (m * M)
          = residueCard O ^
              (1 + kappaLoop m + (bigTLoop m - 1) + m * M) := by
                simp only [pow_add, pow_one]
      _ = residueCard O ^ (m * (M + m)) := by rw [hexp]
  calc
    (residueCard O * decidedCount O m σ M * residueCard O ^ kappaLoop m)
          * residueCard O ^ (bigTLoop m - 1) * residueCard O ^ (m * M)
        = decidedCount O m σ M *
            (residueCard O * residueCard O ^ kappaLoop m
              * residueCard O ^ (bigTLoop m - 1) * residueCard O ^ (m * M)) := by ring
    _ = decidedCount O m σ M * residueCard O ^ (m * (M + m)) := by rw [hpow]

/-- Normalized exact loop contribution, in the literal scalar shape used by
`IFCG14.LoopStepLaw`. -/
theorem loopImageSeq_eq {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] {π : O} (hπ : Irreducible π)
    {m : ℕ} (hm : 0 < m) (σ : FactorizationType) (M : ℕ) :
    (Nat.card (Set.range
          (loopClassN (O := O) (m := m) (M := M) (σ := σ) π)) : ℝ)
        / (residueCard O : ℝ) ^ (m * (M + m))
      = ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ M := by
  have hq0 : (residueCard O : ℝ) ≠ 0 := by
    exact_mod_cast (residueCard_pos O).ne'
  have hcount := loopClassN_weight hπ hm σ M
  have hcountR :
      (Nat.card (Set.range
          (loopClassN (O := O) (m := m) (M := M) (σ := σ) π)) : ℝ)
            * (residueCard O : ℝ) ^ (bigTLoop m - 1)
            * (residueCard O : ℝ) ^ (m * M)
        = (decidedCount O m σ M : ℝ)
            * (residueCard O : ℝ) ^ (m * (M + m)) := by
    exact_mod_cast hcount
  unfold decidedSeq
  field_simp
  calc
    (Nat.card (Set.range
          (loopClassN (O := O) (m := m) (M := M) (σ := σ) π)) : ℝ)
          * (residueCard O : ℝ) ^ (bigTLoop m - 1)
          * (residueCard O : ℝ) ^ (m * M)
        = (decidedCount O m σ M : ℝ)
            * (residueCard O : ℝ) ^ (m * (M + m)) := hcountR
    _ = (residueCard O : ℝ) ^ (m * (M + m))
          * (decidedCount O m σ M : ℝ) := by ring

/-! ## §2 — the aggregate non-loop cell -/

/-- The exact complement of the proved loop image inside the target decided set.  This
is an aggregate finite-level cell; decomposing and counting it skeleton-by-skeleton is
the missing bridge from IFCG12/13. -/
def nonloopDecidedSet {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) : Set (Coeff O m (M + m)) :=
  decidedSet O m σ (M + m) \ Set.range
    (loopClassN (O := O) (m := m) (M := M) (σ := σ) π)

/-- The aggregate non-loop cell and the loop image partition the target decided set,
at the level of exact finite cardinalities. -/
theorem card_nonloop_add_loop {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π)
    (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Nat.card (nonloopDecidedSet π m σ M)
        + Nat.card (Set.range
          (loopClassN (O := O) (m := m) (M := M) (σ := σ) π))
      = decidedCount O m σ (M + m) := by
  unfold nonloopDecidedSet decidedCount
  simp only [Nat.card_coe_set_eq]
  exact Set.ncard_sdiff_add_ncard_of_subset
    (range_loopClassN_subset_decidedSet hπ)

/-- The normalized cardinality of the aggregate non-loop cell. -/
def nonloopCellSeq (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℝ :=
  (Nat.card (nonloopDecidedSet π m σ M) : ℝ)
    / (residueCard O : ℝ) ^ (m * (M + m))

/-! ## §3 — the canonical non-loop remainder -/

/-- The canonical base sequence after removing the exact loop weight from the target
level.  This definition makes IFCG14's affine equality tautological; its rational limit
is the genuine remaining mathematical content. -/
def nonloopBaseSeq (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℝ :=
  decidedSeq O m σ (M + m)
    - ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ M

/-- The canonical base sequence satisfies the exact affine step, by construction. -/
theorem nonloopBaseSeq_step {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    nonloopBaseSeq O m σ M
        + ((residueCard O : ℝ) ^ (bigTLoop m - 1))⁻¹ * decidedSeq O m σ M
      = decidedSeq O m σ (M + m) := by
  unfold nonloopBaseSeq
  ring

/-- The canonical base sequence is exactly the normalized cardinality of the aggregate
non-loop cell.  Thus the named remainder below is a genuine counting-limit statement,
not an arbitrary choice of auxiliary sequence. -/
theorem nonloopBaseSeq_eq_nonloopCellSeq {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π)
    {m : ℕ} (hm : 0 < m) (σ : FactorizationType) (M : ℕ) :
    nonloopBaseSeq O m σ M = nonloopCellSeq O π m σ M := by
  have hcard := card_nonloop_add_loop hπ m σ M
  have hcardR : (decidedCount O m σ (M + m) : ℝ)
      = (Nat.card (nonloopDecidedSet π m σ M) : ℝ)
        + (Nat.card (Set.range
          (loopClassN (O := O) (m := m) (M := M) (σ := σ) π)) : ℝ) := by
    exact_mod_cast hcard.symm
  have hloop := loopImageSeq_eq hπ hm σ M
  unfold nonloopBaseSeq nonloopCellSeq
  rw [show decidedSeq O m σ (M + m)
      = (decidedCount O m σ (M + m) : ℝ)
          / (residueCard O : ℝ) ^ (m * (M + m)) from rfl,
    hcardR, ← hloop]
  ring

/-- **Named FP0 remainder.**  Given all smaller value laws, the canonical NON-LOOP
contribution has one rational limit uniformly in the DVR.  A finite-level cell-counting
and split-measure theorem for the non-loop skeletons is intended to prove this statement;
no such theorem is currently exported by IFCG12/13. -/
def RationalNonloopRemainderAt (m : ℕ) : Prop :=
  (∀ k, k < m → ∀ σ : FactorizationType, σ.degree = k → DecidedValueLaw k σ) →
  ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          Filter.Tendsto (nonloopBaseSeq O m σ) Filter.atTop
            (nhds ((num.eval ((residueCard O : ℕ) : ℚ)
              / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))

/-- IFCG14's socket is exactly the canonical rational non-loop remainder. -/
theorem clusterRecursionAt_iff_rationalNonloopRemainderAt (m : ℕ) :
    ClusterRecursionAt m ↔ RationalNonloopRemainderAt m := by
  unfold ClusterRecursionAt RationalNonloopRemainderAt
  constructor
  · intro h hsmaller σ hσ hwit
    obtain ⟨num, den, hden, hlaw⟩ := h hsmaller σ hσ hwit
    refine ⟨num, den, hden, ?_⟩
    intro O _ _ _ _ _
    obtain ⟨hne, bs, hbs, hstep⟩ := hlaw O
    refine ⟨hne, ?_⟩
    have heq : nonloopBaseSeq O m σ = bs := by
      funext M
      unfold nonloopBaseSeq
      have hs := hstep M
      linarith
    rw [heq]
    exact hbs
  · intro h hsmaller σ hσ hwit
    obtain ⟨num, den, hden, hlaw⟩ := h hsmaller σ hσ hwit
    refine ⟨num, den, hden, ?_⟩
    intro O _ _ _ _ _
    obtain ⟨hne, hlim⟩ := hlaw O
    exact ⟨hne, nonloopBaseSeq O m σ, hlim, nonloopBaseSeq_step m σ⟩

/-- The uniform named remainder. -/
def UniformRationalNonloopRemainder : Prop :=
  ∀ m, 4 ≤ m → RationalNonloopRemainderAt m

/-- The campaign's socket is equivalent to the one uniform named non-loop remainder. -/
theorem uniformClusterRecursion_iff_nonloopRemainder :
    UniformClusterRecursion ↔ UniformRationalNonloopRemainder := by
  unfold UniformClusterRecursion UniformRationalNonloopRemainder
  constructor
  · intro h m hm
    exact (clusterRecursionAt_iff_rationalNonloopRemainderAt m).mp (h m hm)
  · intro h m hm
    exact (clusterRecursionAt_iff_rationalNonloopRemainderAt m).mpr (h m hm)

/-- Widest honest capstone supported by the landed interfaces: the exact non-loop
finite-level counting remainder fires the all-degree decided slice through IFCG14. -/
theorem decidedSliceAt_all_of_nonloopRemainder
    (h : UniformRationalNonloopRemainder) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  IFCG14.decidedSliceAt_all_of_recursion
    (uniformClusterRecursion_iff_nonloopRemainder.mpr h)

end Uniformity.Density.IFCG15

end

/-! ## AXCHECK FOOTER -/

#print axioms Uniformity.Density.IFCG15.loopClassN_injective
#print axioms Uniformity.Density.IFCG15.loopClassN_mem_decidedSet
#print axioms Uniformity.Density.IFCG15.range_loopClassN_subset_decidedSet
#print axioms Uniformity.Density.IFCG15.card_loopParamsN
#print axioms Uniformity.Density.IFCG15.card_range_loopClassN
#print axioms Uniformity.Density.IFCG15.loopClassN_weight
#print axioms Uniformity.Density.IFCG15.loopImageSeq_eq
#print axioms Uniformity.Density.IFCG15.card_nonloop_add_loop
#print axioms Uniformity.Density.IFCG15.nonloopBaseSeq_step
#print axioms Uniformity.Density.IFCG15.nonloopBaseSeq_eq_nonloopCellSeq
#print axioms Uniformity.Density.IFCG15.clusterRecursionAt_iff_rationalNonloopRemainderAt
#print axioms Uniformity.Density.IFCG15.uniformClusterRecursion_iff_nonloopRemainder
#print axioms Uniformity.Density.IFCG15.decidedSliceAt_all_of_nonloopRemainder
