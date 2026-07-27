/-
Unit XA.6 lat1  [proved]
moves_ref: "strict-interior count (EH−E−H−d)/2 + 1, on-side non-vertex count d − 1"
at ℓ = 1. sketch: center-reflection involution + no on-segment points (coprime).
deps: Defs. difficulty: HARD.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem lat1 (s0 u0 e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hcop : Nat.Coprime e h) :
    2 * (p1Region s0 u0 e h 1).card = (e - 1) * (h - 1) := by
  -- The center reflection `(s,u) ↦ (2s₀+e-s, 2u₀+h-u)`.
  set σ : ℕ × ℕ → ℕ × ℕ := fun q => (2 * s0 + e - q.1, 2 * u0 + h - q.2) with hσ
  -- Membership in the region (ℓ = 1, shifted coords x = s - s₀, y = u - u₀).
  have hAmem : ∀ s u, (s, u) ∈ p1Region s0 u0 e h 1 ↔
      s0 < s ∧ s ≤ s0 + e ∧ u0 < u ∧ u ≤ u0 + h ∧
        h * (s - s0) + e * (u - u0) ≤ e * h := by
    intro s u
    simp only [p1Region, Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc, mul_one]
    tauto
  -- Membership in the open box `P = (s₀,s₀+e) × (u₀,u₀+h)`, of cardinality (e-1)(h-1).
  have hPmem : ∀ s u, (s, u) ∈ (Finset.Ioo s0 (s0 + e) ×ˢ Finset.Ioo u0 (u0 + h)) ↔
      s0 < s ∧ s < s0 + e ∧ u0 < u ∧ u < u0 + h := by
    intro s u
    simp only [Finset.mem_product, Finset.mem_Ioo]
    tauto
  -- The region sits inside the open box (no on-axis point survives the diagonal cut).
  have hsub : p1Region s0 u0 e h 1 ⊆ (Finset.Ioo s0 (s0 + e) ×ˢ Finset.Ioo u0 (u0 + h)) := by
    intro q hq
    obtain ⟨s, u⟩ := q
    rw [hAmem] at hq
    obtain ⟨hs1, hs2, hu1, hu2, hfilt⟩ := hq
    rw [hPmem]
    refine ⟨hs1, ?_, hu1, ?_⟩
    · rcases Nat.lt_or_ge s (s0 + e) with h' | h'
      · exact h'
      · exfalso
        have hx : s - s0 = e := by omega
        rw [hx] at hfilt
        have hpos : 0 < e * (u - u0) := Nat.mul_pos (by omega) (by omega)
        have hcm : h * e = e * h := Nat.mul_comm h e
        omega
    · rcases Nat.lt_or_ge u (u0 + h) with h' | h'
      · exact h'
      · exfalso
        have hy : u - u0 = h := by omega
        rw [hy] at hfilt
        have hpos : 0 < h * (s - s0) := Nat.mul_pos (by omega) (by omega)
        omega
  -- σ maps the region into (box \ region): the reflected point overshoots the diagonal.
  have hi : Set.MapsTo σ ↑(p1Region s0 u0 e h 1)
      ↑((Finset.Ioo s0 (s0 + e) ×ˢ Finset.Ioo u0 (u0 + h)) \ p1Region s0 u0 e h 1) := by
    intro q hq
    rw [Finset.mem_coe] at hq
    obtain ⟨s, u⟩ := q
    have hqP := hsub hq
    rw [hPmem] at hqP
    rw [hAmem] at hq
    obtain ⟨hs1, hs2, hu1, hu2, hfilt⟩ := hq
    obtain ⟨-, hsE, -, huH⟩ := hqP
    -- coprimality: the diagonal `hx + ey = eh` carries no interior lattice point.
    have hne : h * (s - s0) + e * (u - u0) ≠ e * h := by
      intro heq
      have hm2 : e * (h - (u - u0)) + e * (u - u0) = e * h := by
        have hsum : (h - (u - u0)) + (u - u0) = h := by omega
        rw [← mul_add, hsum]
      have hsplit : h * (s - s0) = e * (h - (u - u0)) := by omega
      have hdvd : e ∣ h * (s - s0) := ⟨h - (u - u0), hsplit⟩
      have hdvdx : e ∣ (s - s0) := hcop.dvd_of_dvd_mul_left hdvd
      have : e ≤ s - s0 := Nat.le_of_dvd (by omega) hdvdx
      omega
    have hlt : h * (s - s0) + e * (u - u0) < e * h := lt_of_le_of_ne hfilt hne
    rw [Finset.mem_coe, Finset.mem_sdiff]
    simp only [hσ]
    refine ⟨?_, ?_⟩
    · rw [hPmem]; omega
    · rw [hAmem]
      rintro ⟨_, _, _, _, hR⟩
      have hm1 : h * (2 * s0 + e - s - s0) + h * (s - s0) = h * e := by
        have hsum : (2 * s0 + e - s - s0) + (s - s0) = e := by omega
        rw [← mul_add, hsum]
      have hm2 : e * (2 * u0 + h - u - u0) + e * (u - u0) = e * h := by
        have hsum : (2 * u0 + h - u - u0) + (u - u0) = h := by omega
        rw [← mul_add, hsum]
      have hcm : h * e = e * h := Nat.mul_comm h e
      omega
  -- σ maps (box \ region) back into the region: the reflected point clears the diagonal.
  have hj : Set.MapsTo σ
      ↑((Finset.Ioo s0 (s0 + e) ×ˢ Finset.Ioo u0 (u0 + h)) \ p1Region s0 u0 e h 1)
      ↑(p1Region s0 u0 e h 1) := by
    intro q hq
    rw [Finset.mem_coe, Finset.mem_sdiff] at hq
    obtain ⟨s, u⟩ := q
    obtain ⟨hqP, hqA⟩ := hq
    rw [hPmem] at hqP
    obtain ⟨hs1, hsE, hu1, huH⟩ := hqP
    have hnf : ¬ (h * (s - s0) + e * (u - u0) ≤ e * h) := by
      intro hle
      exact hqA ((hAmem s u).2 ⟨hs1, by omega, hu1, by omega, hle⟩)
    rw [Finset.mem_coe]
    simp only [hσ]
    rw [hAmem]
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    have hm1 : h * (2 * s0 + e - s - s0) + h * (s - s0) = h * e := by
      have hsum : (2 * s0 + e - s - s0) + (s - s0) = e := by omega
      rw [← mul_add, hsum]
    have hm2 : e * (2 * u0 + h - u - u0) + e * (u - u0) = e * h := by
      have hsum : (2 * u0 + h - u - u0) + (u - u0) = h := by omega
      rw [← mul_add, hsum]
    have hcm : h * e = e * h := Nat.mul_comm h e
    omega
  -- σ is an involution on both the region and its complement in the box.
  have hleft : Set.LeftInvOn σ σ ↑(p1Region s0 u0 e h 1) := by
    intro q hq
    rw [Finset.mem_coe] at hq
    obtain ⟨s, u⟩ := q
    rw [hAmem] at hq
    obtain ⟨hs1, hs2, hu1, hu2, -⟩ := hq
    simp only [hσ, Prod.mk.injEq]
    exact ⟨by omega, by omega⟩
  have hright : Set.RightInvOn σ σ
      ↑((Finset.Ioo s0 (s0 + e) ×ˢ Finset.Ioo u0 (u0 + h)) \ p1Region s0 u0 e h 1) := by
    intro q hq
    rw [Finset.mem_coe, Finset.mem_sdiff] at hq
    obtain ⟨s, u⟩ := q
    obtain ⟨hqP, -⟩ := hq
    rw [hPmem] at hqP
    obtain ⟨hs1, hsE, hu1, huH⟩ := hqP
    simp only [hσ, Prod.mk.injEq]
    exact ⟨by omega, by omega⟩
  -- The involution equidistributes: |region| = |box \ region|.
  have hcardeq : (p1Region s0 u0 e h 1).card =
      ((Finset.Ioo s0 (s0 + e) ×ˢ Finset.Ioo u0 (u0 + h)) \ p1Region s0 u0 e h 1).card :=
    Finset.card_nbij' σ σ hi hj hleft hright
  have hsum := Finset.card_sdiff_add_card_eq_card hsub
  have hPcard : (Finset.Ioo s0 (s0 + e) ×ˢ Finset.Ioo u0 (u0 + h)).card = (e - 1) * (h - 1) := by
    rw [Finset.card_product, Nat.card_Ioo, Nat.card_Ioo]
    congr 1 <;> omega
  omega

end LeanUrat.MovesX
