/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C47
import Uniformity.ChapC.C131a
import Uniformity.ChapC.C131p

/-!
# Uniformity.ChapC.C131f — public lift fence and the composed-key floor

**Chapter C, NODES C.131f′–g′**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §2.4 and §5).

This file respects the private-export fence: no private C.46/C.47 declaration is named.
The reduced two-variable image is built directly from the public canonical digits, and its
floor uses only C.47's four public `composedKey_*` clauses together with C.131p's public
coefficient formula for `stageHeight`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131f

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131a Uniformity.Density.Tower.C131p

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## C.131f′ — the public degree pin -/

/-- **NODE C.131f′ (degree export).** Every element-at-height lift is reduced modulo the
frame key.  This is rederived from the public definition, without naming the private C.46
helper. -/
theorem KeyFrame.natDegree_stageLiftO_lt (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (M : ℕ) (c : F.stageField H₀ hpin) :
    (F.stageLiftO H₀ hpin M c).natDegree < F.e₁ * F.f₁ := by
  classical
  have hpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hbound : (F.stageLiftO H₀ hpin M c).natDegree ≤ F.e₁ * F.f₁ - 1 := by
    rw [KeyFrame.stageLiftO, KeyFrame.stageLiftIA]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
    have hs' : s < F.f₁ := Finset.mem_range.mp hs
    have hmul : F.e₁ * (s + 1) ≤ F.e₁ * F.f₁ := Nat.mul_le_mul_left F.e₁ hs'
    have hexp : F.e₁ * (s + 1) = F.e₁ * s + F.e₁ := by ring
    have hi : F.slotIdx M < F.e₁ := (F.slotIdx_spec M).1
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    omega
  omega

private theorem lift_slot_eq (F : KeyFrame O π) {M : ℕ}
    (hM : F.slotIdx M * F.h ≤ M) :
    F.slotIdx M * F.h + F.e₁ * ((M - F.slotIdx M * F.h) / F.e₁) = M := by
  have hdvd : F.e₁ ∣ M - F.slotIdx M * F.h :=
    (Nat.modEq_iff_dvd' hM).mp (F.slotIdx_spec M).2
  rw [Nat.mul_div_cancel' hdvd, Nat.add_sub_cancel' hM]

private theorem lift_window_data (F : KeyFrame O π) {M : ℕ}
    (hM : F.e₁ * F.f₁ * F.h < M) :
    F.slotIdx M * F.h + F.e₁ * ((M - F.slotIdx M * F.h) / F.e₁) = M ∧
      F.slotWindow M = Finset.range F.f₁ ∧
      ∀ s, s < F.f₁ → s * F.h ≤ (M - F.slotIdx M * F.h) / F.e₁ := by
  have hbelow : ∀ s, s < F.f₁ → (F.slotIdx M + F.e₁ * s) * F.h < M := by
    intro s hs
    have hi : F.slotIdx M < F.e₁ := (F.slotIdx_spec M).1
    have hmul : F.e₁ * (s + 1) ≤ F.e₁ * F.f₁ := Nat.mul_le_mul_left F.e₁ hs
    have hexp : F.e₁ * (s + 1) = F.e₁ * s + F.e₁ := by ring
    have hle : F.slotIdx M + F.e₁ * s ≤ F.e₁ * F.f₁ := by
      omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) hM
  have hile : F.slotIdx M * F.h ≤ M := by
    have h0 := hbelow 0 F.hf₁
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    omega
  have hMa := lift_slot_eq F hile
  refine ⟨hMa, ?_, ?_⟩
  · refine F.slotWindow_full_of_le M ?_
    have hsub : (F.e₁ * F.f₁ - 1) * F.h ≤ (F.e₁ * F.f₁) * F.h :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  · intro s hs
    have h1 := hbelow s hs
    have h2 : F.e₁ * (s * F.h) <
        F.e₁ * ((M - F.slotIdx M * F.h) / F.e₁) := by
      have hexp : (F.slotIdx M + F.e₁ * s) * F.h =
          F.slotIdx M * F.h + F.e₁ * (s * F.h) := by ring
      omega
    exact le_of_lt (Nat.lt_of_mul_lt_mul_left h2)

private theorem lift_coeff_at_slot (F : KeyFrame O π) {i a s : ℕ} (hs : s < F.f₁)
    (lift : ℕ → O) :
    (F.stageLiftIA (π := π) i a lift).coeff (i + F.e₁ * s) =
      lift s * π ^ (a - s * F.h) := by
  classical
  rw [KeyFrame.stageLiftIA, Polynomial.finsetSum_coeff, Finset.sum_eq_single s]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b hb hbs
    have hne : i + F.e₁ * s ≠ i + F.e₁ * b := by
      intro he
      exact hbs (Nat.eq_of_mul_eq_mul_left F.he₁ (by omega)).symm
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
  · exact fun hns => (hns (Finset.mem_range.mpr hs)).elim

private theorem lift_slotRes_formula (F : KeyFrame O π) (hπ : Irreducible π)
    (H₀ : ℕ) (hpin : F.Pin H₀) {a M : ℕ}
    (hM : F.slotIdx M * F.h + F.e₁ * a = M)
    (hfull : F.slotWindow M = Finset.range F.f₁)
    (hsa : ∀ s, s < F.f₁ → s * F.h ≤ a) (lift : ℕ → O) :
    F.slotRes H₀ hpin M (F.stageLiftIA (π := π) (F.slotIdx M) a lift) =
      ∑ s ∈ Finset.range F.f₁,
        algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
          (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
            (IsLocalRing.residue O (lift s))) * F.stageLetter H₀ hpin ^ s := by
  classical
  rw [KeyFrame.slotRes, hfull]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s < F.f₁ := Finset.mem_range.mp hs
  have hidx : (M - (F.slotIdx M + F.e₁ * s) * F.h) / F.e₁ = a - s * F.h := by
    have hsa' := hsa s hs'
    have heq : M - (F.slotIdx M + F.e₁ * s) * F.h = F.e₁ * (a - s * F.h) := by
      rw [Nat.mul_sub]
      have hexp : (F.slotIdx M + F.e₁ * s) * F.h =
          F.slotIdx M * F.h + F.e₁ * (s * F.h) := by ring
      omega
    rw [heq, Nat.mul_div_cancel_left _ F.he₁]
  rw [hidx, lift_coeff_at_slot F hs' lift,
    digAt_eq hπ (mul_comm (lift s) (π ^ (a - s * F.h)))]

/-- **NODE C.131f′ (residue export).** Above the full-window threshold, the public lift is
read back by `slotRes`. -/
theorem KeyFrame.slotRes_stageLiftO (F : KeyFrame O π) (hπ : Irreducible π)
    (H₀ : ℕ) (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M)
    (c : F.stageField H₀ hpin) :
    F.slotRes H₀ hpin M (F.stageLiftO H₀ hpin M c) = c := by
  obtain ⟨hMa, hfull, hsa⟩ := lift_window_data F hM
  rw [KeyFrame.stageLiftO, lift_slotRes_formula F hπ H₀ hpin hMa hfull hsa]
  refine Eq.trans (Finset.sum_congr rfl fun s hs => ?_) (F.sum_stageCoord H₀ hpin c)
  rw [resLift_spec]

private theorem lift_coeff_off_slots (F : KeyFrame O π) {i a n : ℕ} (lift : ℕ → O)
    (hn : ∀ s < F.f₁, n ≠ i + F.e₁ * s) :
    (F.stageLiftIA (π := π) i a lift).coeff n = 0 := by
  classical
  rw [KeyFrame.stageLiftIA, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    if_neg (hn s (Finset.mem_range.mp hs)), mul_zero]

private theorem lift_cost (F : KeyFrame O π) (hπ : Irreducible π) {i a M s : ℕ}
    (hs : s < F.f₁) (hsa : s * F.h ≤ a) (hM : i * F.h + F.e₁ * a = M)
    (lift : ℕ → O) :
    F.e₁ • addVal O ((F.stageLiftIA (π := π) i a lift).coeff (i + F.e₁ * s)) +
        (F.h * (i + F.e₁ * s) : ℕ∞) =
      F.e₁ • addVal O (lift s) + (M : ℕ∞) := by
  rw [lift_coeff_at_slot F hs lift, AddValuation.map_mul, hπ.addVal_pow, smul_add]
  have hnat : F.e₁ * (a - s * F.h) + F.h * (i + F.e₁ * s) = M := by
    have hsub : F.e₁ * (a - s * F.h) = F.e₁ * a - F.e₁ * (s * F.h) := by
      rw [Nat.mul_sub]
    have hle : F.e₁ * (s * F.h) ≤ F.e₁ * a := Nat.mul_le_mul_left _ hsa
    have hexp : F.h * (i + F.e₁ * s) = i * F.h + F.e₁ * (s * F.h) := by ring
    omega
  rw [add_assoc]
  congr 1
  simp only [nsmul_eq_mul]
  exact_mod_cast hnat

private theorem lift_isUnit_of_residue_ne_zero {x : O}
    (hx : IsLocalRing.residue O x ≠ 0) : IsUnit x := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff] at hx
  exact IsLocalRing.notMem_maximalIdeal.mp hx

private theorem lift_height_formula (F : KeyFrame O π) (hπ : Irreducible π)
    {i a M s₀ : ℕ} (hM : i * F.h + F.e₁ * a = M)
    (hsa : ∀ s, s < F.f₁ → s * F.h ≤ a) (lift : ℕ → O)
    (hs₀ : s₀ < F.f₁) (hu : IsUnit (lift s₀)) :
    F.stageHeight (F.stageLiftIA (π := π) i a lift) = (M : ℕ∞) := by
  classical
  set A := F.stageLiftIA (π := π) i a lift with hA
  have hcoeff₀ : A.coeff (i + F.e₁ * s₀) = lift s₀ * π ^ (a - s₀ * F.h) :=
    lift_coeff_at_slot F hs₀ lift
  have hne₀ : A.coeff (i + F.e₁ * s₀) ≠ 0 := by
    rw [hcoeff₀]
    exact mul_ne_zero hu.ne_zero (pow_ne_zero _ hπ.ne_zero)
  rw [stageHeight_eq_coeff_inf]
  apply le_antisymm
  · refine le_trans (Finset.inf_le (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hne₀)))) ?_
    simp only [Nat.cast_add, Nat.cast_mul]
    rw [hA, lift_cost F hπ hs₀ (hsa s₀ hs₀) hM lift,
      addVal_eq_zero_iff.mpr hu, smul_zero, zero_add]
  · refine Finset.le_inf fun j hj => ?_
    by_cases hex : ∃ s, s < F.f₁ ∧ j = i + F.e₁ * s
    · obtain ⟨s, hs, rfl⟩ := hex
      simp only [Nat.cast_add, Nat.cast_mul]
      rw [hA, lift_cost F hπ hs (hsa s hs) hM lift]
      exact le_add_self
    · have hz : A.coeff j = 0 :=
        lift_coeff_off_slots F lift (fun s hs he => hex ⟨s, hs, he⟩)
      rw [hz, addVal_zero, nsmul_eq_mul,
        ENat.mul_top (by exact_mod_cast F.he₁.ne'), top_add]
      exact le_top

/-- **NODE C.131f′ (height export).** A nonzero element lifts to exactly its prescribed
height once the full slot window is available. -/
theorem KeyFrame.stageHeight_stageLiftO (F : KeyFrame O π) (hπ : Irreducible π)
    (H₀ : ℕ) (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M)
    {c : F.stageField H₀ hpin} (hc : c ≠ 0) :
    F.stageHeight (F.stageLiftO H₀ hpin M c) = (M : ℕ∞) := by
  classical
  obtain ⟨hMa, hfull, hsa⟩ := lift_window_data F hM
  have hex : ∃ s, s < F.f₁ ∧ F.stageCoord H₀ hpin c s ≠ 0 := by
    by_contra hall
    refine hc (Eq.trans (F.sum_stageCoord H₀ hpin c).symm ?_)
    refine Finset.sum_eq_zero fun s hs => ?_
    have hzero : F.stageCoord H₀ hpin c s = 0 := by
      by_contra hd
      exact hall ⟨s, Finset.mem_range.mp hs, hd⟩
    rw [hzero, map_zero, map_zero, zero_mul]
  obtain ⟨s₀, hs₀, hd₀⟩ := hex
  rw [KeyFrame.stageLiftO]
  refine lift_height_formula F hπ hMa hsa _ hs₀ ?_
  apply lift_isUnit_of_residue_ne_zero
  rw [resLift_spec]
  exact hd₀

/-! ## C.131g′ — the canonical two-variable image -/

/-- The reduced `F.key`-development of the composed key, represented in a fresh outer
variable. -/
noncomputable def K_T (T : TowerDatum F H₀ hpin) :
    Polynomial (Polynomial O) :=
  ∑ b ∈ Finset.range (T.e₂ * T.f₂ + 1),
    Polynomial.monomial b (dev F.key (composedKey T) b)

/-- Coefficients of the reduced composed-key image are its canonical development digits. -/
theorem coeff_K_T (T : TowerDatum F H₀ hpin) {b : ℕ}
    (hb : b ≤ T.e₂ * T.f₂) :
    (K_T T).coeff b = dev F.key (composedKey T) b := by
  classical
  rw [K_T, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c hc hcb
    rw [if_neg hcb]
  · simp [hb]

/-- Every scalar monomial of a nonzero composed-key digit lies above `E₂`. -/
theorem composedKey_monomial_floor (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    {a b : ℕ} (hb : b ≤ T.e₂ * T.f₂)
    (ha : (dev F.key (composedKey T) b).coeff a ≠ 0) :
    (T.E₂ : ℕ∞) ≤
      wtCoeff T ((dev F.key (composedKey T) b).coeff a) a b := by
  by_cases htop : b = T.e₂ * T.f₂
  · subst b
    rw [composedKey_top_digit T] at ha ⊢
    have ha0 : a = 0 := by
      by_contra hne
      exact ha (by simp [Polynomial.coeff_one, hne])
    subst a
    simp [wtCoeff, TowerDatum.E₂]
  · have hblt : b < T.e₂ * T.f₂ := lt_of_le_of_ne hb htop
    by_cases hdiv : T.e₂ ∣ b
    · obtain ⟨t, rfl⟩ := hdiv
      have ht : t < T.f₂ := by
        have := Nat.lt_of_mul_lt_mul_left hblt
        exact this
      have hlabel : (towerLabel T).coeff t ≠ 0 := by
        intro hz
        rw [composedKey_zero_slot T hπ ht hz] at ha
        exact ha (Polynomial.coeff_zero _)
      have hheight := composedKey_slot_height T hπ ht hlabel
      have hmem : a ∈ Finset.range
          ((dev F.key (composedKey T) (T.e₂ * t)).natDegree + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero ha))
      have hcoeff := Finset.inf_le (f := fun j =>
          F.e₁ • addVal O ((dev F.key (composedKey T) (T.e₂ * t)).coeff j) +
            (F.h * j : ℕ∞)) hmem
      rw [← stageHeight_eq_coeff_inf F, hheight] at hcoeff
      unfold wtCoeff
      have hscaled := nsmul_le_nsmul_right hcoeff T.e₂
      simp only [nsmul_eq_mul, Nat.cast_mul] at hscaled ⊢
      push_cast at hscaled ⊢
      have hnat : T.e₂ * T.f₂ * T.u₂ =
          T.e₂ * ((T.f₂ - t) * T.u₂) + (T.e₂ * t) * T.u₂ := by
        have htle : t ≤ T.f₂ := Nat.le_of_lt ht
        calc
          T.e₂ * T.f₂ * T.u₂ = T.e₂ * ((T.f₂ - t + t) * T.u₂) := by
            rw [Nat.sub_add_cancel htle]
            ring
          _ = T.e₂ * ((T.f₂ - t) * T.u₂) + (T.e₂ * t) * T.u₂ := by ring
      calc
        ((T.E₂ : ℕ) : ℕ∞) =
            (T.e₂ : ℕ∞) * (((T.f₂ - t) * T.u₂ : ℕ) : ℕ∞) +
              (((T.e₂ * t) * T.u₂ : ℕ) : ℕ∞) := by
                simp only [TowerDatum.E₂]
                exact_mod_cast hnat
        _ ≤ (T.e₂ : ℕ∞) *
              (F.e₁ • addVal O ((dev F.key (composedKey T) (T.e₂ * t)).coeff a) +
                (F.h * a : ℕ∞)) + (((T.e₂ * t) * T.u₂ : ℕ) : ℕ∞) :=
          by simpa [add_comm] using
            add_le_add_right hscaled (((T.e₂ * t) * T.u₂ : ℕ) : ℕ∞)
        _ = (F.e₁ * T.e₂ : ℕ∞) *
              addVal O ((dev F.key (composedKey T) (T.e₂ * t)).coeff a) +
                (((a * (T.e₂ * F.h) + (T.e₂ * t) * T.u₂ : ℕ) : ℕ∞)) := by
          push_cast
          ring
    · rw [composedKey_offLattice_digit T hblt hdiv] at ha
      exact absurd (ha (Polynomial.coeff_zero _)) False.elim

/-- Every scalar monomial in the reduced two-variable image lies above `E₂`. -/
theorem K_T_monomial_floor (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    {a b : ℕ} (hb : b ∈ (K_T T).support)
    (ha : a ∈ ((K_T T).coeff b).support) :
    (T.E₂ : ℕ∞) ≤ wtCoeff T (((K_T T).coeff b).coeff a) a b := by
  have hbdeg : b ≤ T.e₂ * T.f₂ := by
    by_contra hnot
    have hbgt : T.e₂ * T.f₂ < b := Nat.lt_of_not_ge hnot
    have hzero : (K_T T).coeff b = 0 := by
      classical
      rw [K_T, Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [Polynomial.coeff_monomial]
      simp only [Finset.mem_range] at hc
      simp [show c ≠ b by omega]
    exact (Polynomial.mem_support_iff.mp hb) hzero
  rw [coeff_K_T T hbdeg] at ha ⊢
  exact composedKey_monomial_floor T hπ hbdeg (Polynomial.mem_support_iff.mp ha)

/-- **NODE C.131g′.** The reduced composed key has weight exactly `E₂`. -/
theorem WT_K_T (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    WT T (K_T T) = (T.E₂ : ℕ∞) := by
  apply le_antisymm
  · have hb : T.e₂ * T.f₂ ∈ (K_T T).support := by
      rw [Polynomial.mem_support_iff, coeff_K_T T le_rfl,
        composedKey_top_digit T]
      exact one_ne_zero
    have ha : 0 ∈ ((K_T T).coeff (T.e₂ * T.f₂)).support := by
      rw [coeff_K_T T le_rfl, composedKey_top_digit T]
      simp
    refine le_trans (WT_le_wtCoeff_of_mem T hb ha) ?_
    simp [coeff_K_T T le_rfl, composedKey_top_digit T, wtCoeff,
      TowerDatum.E₂]
  · simp only [WT, Finset.le_inf_iff]
    intro b hb a ha
    exact K_T_monomial_floor T hπ hb ha

end Uniformity.Density.Tower.C131f

/-! ## Public lift-pin fence

These aliases deliberately live in the frame namespace rather than the node namespace.  Later
files therefore consume a stable public API and cannot accidentally depend on C.46/C.47's
private implementation names. -/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- Public H.55(ii) lift-degree pin. -/
theorem KeyFrame.natDegree_stageLiftO_lt (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (M : ℕ) (c : F.stageField H₀ hpin) :
    (F.stageLiftO H₀ hpin M c).natDegree < F.e₁ * F.f₁ :=
  C131f.KeyFrame.natDegree_stageLiftO_lt F H₀ hpin M c

/-- Public H.56 lift-residue pin. -/
theorem KeyFrame.slotRes_stageLiftO (F : KeyFrame O π) (hπ : Irreducible π)
    (H₀ : ℕ) (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M)
    (c : F.stageField H₀ hpin) :
    F.slotRes H₀ hpin M (F.stageLiftO H₀ hpin M c) = c :=
  C131f.KeyFrame.slotRes_stageLiftO F hπ H₀ hpin hM c

/-- Public H.55(i) exact-height pin. -/
theorem KeyFrame.stageHeight_stageLiftO (F : KeyFrame O π) (hπ : Irreducible π)
    (H₀ : ℕ) (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M)
    {c : F.stageField H₀ hpin} (hc : c ≠ 0) :
    F.stageHeight (F.stageLiftO H₀ hpin M c) = (M : ℕ∞) :=
  C131f.KeyFrame.stageHeight_stageLiftO F hπ H₀ hpin hM hc

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131f.KeyFrame.natDegree_stageLiftO_lt
#print axioms Uniformity.Density.Tower.C131f.KeyFrame.slotRes_stageLiftO
#print axioms Uniformity.Density.Tower.C131f.KeyFrame.stageHeight_stageLiftO
#print axioms Uniformity.Density.Tower.C131f.K_T
#print axioms Uniformity.Density.Tower.C131f.coeff_K_T
#print axioms Uniformity.Density.Tower.C131f.composedKey_monomial_floor
#print axioms Uniformity.Density.Tower.C131f.K_T_monomial_floor
#print axioms Uniformity.Density.Tower.C131f.WT_K_T
#print axioms Uniformity.Density.Tower.KeyFrame.natDegree_stageLiftO_lt
#print axioms Uniformity.Density.Tower.KeyFrame.slotRes_stageLiftO
#print axioms Uniformity.Density.Tower.KeyFrame.stageHeight_stageLiftO

end AxCheck
