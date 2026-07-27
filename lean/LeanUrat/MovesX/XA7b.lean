/-
Unit XA.7b latGen  [PROVED, fleet 2026-07-28]
moves_ref: "(IND) ind(S) = ½·ℓ·(ehℓ − e − h + 1)" + example anchors
(ℓ = 1 ↦ XA.6; e = h = ℓ = 1 ↦ 0). deps: XA.6, XA.7a. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA6
import LeanUrat.MovesX.XA7a

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The closed-form arithmetic step behind `latGen`: after the slice+doubling the count
is `ℓ·(e−1)(h−1) + eh·ℓ·(ℓ−1)`, which equals `ℓ·(ehℓ+1−e−h)`. Proved by clearing the
`ℕ`-truncated subtractions via `e = 1+a`, `h = 1+b`, `ℓ = 1+c`. -/
private lemma latGen_arith (e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 1 ≤ ell) :
    ell * ((e - 1) * (h - 1)) + e * h * (ell * (ell - 1))
      = ell * (e * h * ell + 1 - e - h) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le he
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hh
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hl
  have hinner : (1 + a) * (1 + b) * (1 + c) + 1 - (1 + a) - (1 + b)
      = c + a * b + a * c + b * c + a * b * c := by
    have e1 : (1 + a) * (1 + b) * (1 + c)
        = 1 + a + b + c + a * b + a * c + b * c + a * b * c := by ring
    omega
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, hinner]
  ring

theorem latGen (s0 u0 e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 1 ≤ ell)
    (hcop : Nat.Coprime e h) :
    2 * (p1Region s0 u0 e h ell).card = ell * (e * h * ell + 1 - e - h) := by
  -- reflection: ∑ (ℓ−1−k) over k = ∑ k
  have hgauss : ∑ k ∈ Finset.range ell, (ell - 1 - k) = ∑ k ∈ Finset.range ell, k :=
    Finset.sum_range_reflect (fun k => k) ell
  -- the second (rectangle-stride) block sums to eh·ℓ·(ℓ−1)
  have hsum2 : ∑ k ∈ Finset.range ell, 2 * (e * ((ell - 1 - k) * h))
      = e * h * (ell * (ell - 1)) := by
    have hterm : ∀ k ∈ Finset.range ell,
        2 * (e * ((ell - 1 - k) * h)) = 2 * e * h * (ell - 1 - k) := by
      intro k _; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hgauss,
      show 2 * e * h * (∑ k ∈ Finset.range ell, k)
          = e * h * ((∑ k ∈ Finset.range ell, k) * 2) from by ring,
      Finset.sum_range_id_mul_two]
  -- expand the region as column blocks (XA.7a), then double each block (XA.6)
  rw [latSlice s0 u0 e h ell he hh hl, Finset.mul_sum]
  have step : ∀ k ∈ Finset.range ell,
      2 * ((p1Region (s0 + k * e) (u0 + (ell - 1 - k) * h) e h 1).card
            + e * ((ell - 1 - k) * h))
        = (e - 1) * (h - 1) + 2 * (e * ((ell - 1 - k) * h)) := by
    intro k _
    rw [Nat.mul_add, lat1 (s0 + k * e) (u0 + (ell - 1 - k) * h) e h he hh hcop]
  rw [Finset.sum_congr rfl step, Finset.sum_add_distrib, hsum2, Finset.sum_const,
    Finset.card_range, smul_eq_mul]
  exact latGen_arith e h ell he hh hl

/-- anchor: at ℓ = 1 the display is XA.6's. -/
example (s0 u0 e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hcop : Nat.Coprime e h) :
    2 * (p1Region s0 u0 e h 1).card = (e - 1) * (h - 1) :=
  lat1 s0 u0 e h he hh hcop

/-- anchor: e = h = ℓ = 1 ↦ 0. -/
example (s0 u0 : ℕ) : 2 * (p1Region s0 u0 1 1 1).card = 0 := by
  simpa using latGen s0 u0 1 1 1 le_rfl le_rfl le_rfl (Nat.coprime_one_right 1)

end LeanUrat.MovesX
