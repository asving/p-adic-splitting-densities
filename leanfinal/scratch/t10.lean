import Uniformity.ChapB.B82

namespace Uniformity.Density.Leaf
open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem npHgt_eq_top_of_gt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    {j : ℕ} (hj : μ < j) : npHgt φ f j = ⊤ :=
  npHgt_eq_top_iff.2 (dev_eq_zero_of_lt hφ hd f j (by
    rw [hdeg]; exact Nat.mul_lt_mul_of_lt_of_le hj (le_refl _) hd))

section TwoPoint

variable {φ f : Polynomial O} {μ : ℕ}

/-- The weight function of the polygon at the slope `(u,ℓ)`. -/
private theorem twoPoint_weight (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hf : f.Monic)
    (hdeg : f.natDegree = μ * φ.natDegree)
    (h0 : npHgt φ f 0 = 1) (hmid : ∀ j, 0 < j → j < μ → npHgt φ f j = ⊤)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (j : ℕ) :
    ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞)
      = if j = 0 then (ℓ : ℕ∞) else if j = μ then ((u * μ : ℕ) : ℕ∞) else ⊤ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [h0]
  rcases lt_trichotomy j μ with hlt | rfl | hgt
  · rw [hmid j hj hlt]; simp [hj.ne', hlt.ne, hℓ.ne']
  · rw [npHgt_top hφ hd hf hdeg]; simp [hj.ne']
  · rw [npHgt_eq_top_of_gt hφ hd hdeg hgt]; simp [hj.ne', hgt.ne', hℓ.ne']

theorem twoPoint_suppVal (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hf : f.Monic)
    (hdeg : f.natDegree = μ * φ.natDegree) (hμ : 0 < μ)
    (h0 : npHgt φ f 0 = 1) (hmid : ∀ j, 0 < j → j < μ → npHgt φ f j = ⊤)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) :
    suppVal φ f u ℓ = min (ℓ : ℕ∞) ((u * μ : ℕ) : ℕ∞) := by
  classical
  have hμle : μ ≤ f.natDegree := by
    rw [hdeg]; exact Nat.le_mul_of_pos_right μ hd
  have hW := twoPoint_weight hφ hd hf hdeg h0 hmid (u := u) hℓ
  rw [suppVal]
  refine le_antisymm (le_min ?_ ?_) (Finset.le_inf fun j _ => ?_)
  · have hmem : (0 : ℕ) ∈ Finset.range (f.natDegree + 1) :=
      Finset.mem_range.2 (Nat.succ_pos _)
    have := Finset.inf_le (f := fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞)) hmem
    rw [hW 0] at this
    simpa using this
  · have hmem : μ ∈ Finset.range (f.natDegree + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le hμle)
    have := Finset.inf_le (f := fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞)) hmem
    rw [hW μ, if_neg hμ.ne', if_pos rfl] at this
    exact this
  · rw [hW j]
    split_ifs with hj0 hjμ
    · exact min_le_left _ _
    · exact min_le_right _ _
    · exact le_top

theorem twoPoint_mem_sideSet (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hf : f.Monic)
    (hdeg : f.natDegree = μ * φ.natDegree) (hμ : 0 < μ)
    (h0 : npHgt φ f 0 = 1) (hmid : ∀ j, 0 < j → j < μ → npHgt φ f j = ⊤)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {j : ℕ} :
    j ∈ sideSet φ f u ℓ ↔ ((j = 0 ∧ ℓ ≤ u * μ) ∨ (j = μ ∧ u * μ ≤ ℓ)) := by
  classical
  have hμle : μ ≤ f.natDegree := by
    rw [hdeg]; exact Nat.le_mul_of_pos_right μ hd
  have hW := twoPoint_weight hφ hd hf hdeg h0 hmid (u := u) hℓ
  have hsupp := twoPoint_suppVal hφ hd hf hdeg hμ h0 hmid (u := u) hℓ
  constructor
  · intro hj
    have hjr : j ∈ Finset.range (f.natDegree + 1) :=
      Finset.mem_of_mem_filter (s := Finset.range (f.natDegree + 1)) j hj
    have hon : ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = suppVal φ f u ℓ :=
      onSide_of_mem_sideSet hj
    rw [hW j, hsupp] at hon
    split_ifs at hon with hj0 hjμ
    · exact Or.inl ⟨hj0, by
        have : (ℓ : ℕ∞) ≤ ((u * μ : ℕ) : ℕ∞) := hon.symm ▸ min_le_right _ _
        exact_mod_cast this⟩
    · exact Or.inr ⟨hjμ, by
        have : ((u * μ : ℕ) : ℕ∞) ≤ (ℓ : ℕ∞) := hon.symm ▸ min_le_left _ _
        exact_mod_cast this⟩
    · exact absurd hon (by
        refine fun hc => ?_
        rw [eq_comm, min_eq_top] at hc
        exact (ENat.coe_ne_top ℓ) hc.1)
  · rintro (⟨rfl, hle⟩ | ⟨hjm, hle⟩)
    · have hmem : (0 : ℕ) ∈ Finset.range (f.natDegree + 1) :=
        Finset.mem_range.2 (Nat.succ_pos _)
      refine Finset.mem_filter.2 ⟨hmem, ?_⟩
      show ℓ • npHgt φ f 0 + ((u * 0 : ℕ) : ℕ∞) = suppVal φ f u ℓ
      rw [hW 0, hsupp, if_pos rfl, min_eq_left (by exact_mod_cast hle)]
    · subst hjm
      have hmem : j ∈ Finset.range (f.natDegree + 1) :=
        Finset.mem_range.2 (Nat.lt_succ_of_le hμle)
      refine Finset.mem_filter.2 ⟨hmem, ?_⟩
      show ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = suppVal φ f u ℓ
      rw [hW j, hsupp, if_neg hμ.ne', if_pos rfl, min_eq_right (by exact_mod_cast hle)]

theorem twoPoint_sideSet_eq (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hf : f.Monic)
    (hdeg : f.natDegree = μ * φ.natDegree) (hμ : 0 < μ)
    (h0 : npHgt φ f 0 = 1) (hmid : ∀ j, 0 < j → j < μ → npHgt φ f j = ⊤)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (heq : ℓ = u * μ) :
    sideSet φ f u ℓ = {0, μ} := by
  classical
  ext j
  rw [twoPoint_mem_sideSet hφ hd hf hdeg hμ h0 hmid hℓ, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, le_of_eq heq⟩
    · exact Or.inr ⟨rfl, le_of_eq heq.symm⟩

theorem twoPoint_card_iff (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hf : f.Monic)
    (hdeg : f.natDegree = μ * φ.natDegree) (hμ : 0 < μ)
    (h0 : npHgt φ f 0 = 1) (hmid : ∀ j, 0 < j → j < μ → npHgt φ f j = ⊤)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) :
    1 < (sideSet φ f u ℓ).card ↔ ℓ = u * μ := by
  classical
  constructor
  · intro hc
    by_contra hne
    have hsub : sideSet φ f u ℓ ⊆ (if ℓ < u * μ then {0} else {μ}) := by
      intro j hj
      rcases (twoPoint_mem_sideSet hφ hd hf hdeg hμ h0 hmid hℓ).1 hj with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
      · rw [if_pos (by omega)]; simp
      · rw [if_neg (by omega)]; simp
    have := Finset.card_le_card hsub
    split_ifs at this <;> simp at this <;> omega
  · intro heq
    rw [twoPoint_sideSet_eq hφ hd hf hdeg hμ h0 hmid hℓ heq,
      Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    omega

theorem twoPoint_sideDeg (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hf : f.Monic)
    (hdeg : f.natDegree = μ * φ.natDegree) (hμ : 0 < μ)
    (h0 : npHgt φ f 0 = 1) (hmid : ∀ j, 0 < j → j < μ → npHgt φ f j = ⊤)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (heq : ℓ = u * μ)
    (hne : (sideSet φ f u ℓ).Nonempty) : sideDeg φ f u ℓ hne = 1 := by
  classical
  have hu : u = 1 := by
    have hdvd : u ∣ ℓ := ⟨μ, heq⟩
    have hg : Nat.gcd u ℓ = u := Nat.gcd_eq_left hdvd
    rw [Nat.Coprime] at hcop
    omega
  have hlμ : ℓ = μ := by rw [heq, hu, one_mul]
  have hss := twoPoint_sideSet_eq hφ hd hf hdeg hμ h0 hmid hℓ heq
  have hmin : sideMin φ f u ℓ hne = 0 := by
    have h0m : (0 : ℕ) ∈ sideSet φ f u ℓ := by rw [hss]; simp
    exact Nat.le_zero.1 (Finset.min'_le _ _ h0m)
  have hmax : sideMax φ f u ℓ hne = μ := by
    refine le_antisymm (Finset.max'_le _ _ _ fun j hj => ?_) (Finset.le_max' _ _ (by rw [hss]; simp))
    rw [hss] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · omega
    · exact le_refl _
  rw [sideDeg, hmin, hmax, Nat.sub_zero, hlμ, Nat.div_self hμ]

end TwoPoint

end Uniformity.Density.Leaf
