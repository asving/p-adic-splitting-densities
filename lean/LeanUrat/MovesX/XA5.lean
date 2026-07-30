/-
Unit XA.5 t2Witness  [PROVED, fleet 2026-07-28]
moves_ref: T2 witness "(s+1, u+1) … gcd(e,h) = 1 excludes (2,2)".
deps: XA.1. difficulty: MEDIUM (EASY-MEDIUM band).
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem t2Witness {n : ℕ} (ν : XNode n) (h2 : rowOf ν = .T2) :
    (ν.s0 + 1, ν.u0 + 1) ∈ ν.region ∧ 2 ≤ (ν.e - 1) * (ν.h - 1) ∧
    2 ∣ (ν.e - 1) * (ν.h - 1) := by
  -- Extract the T2 characterization directly from the row classifier (XA.1).
  obtain ⟨hell, he, hh⟩ := ((rowTotal ν).2.2.1.mp h2).2
  -- Coprimality of `e, h` (both ≥ 2) forces at least one of them odd.
  have hodd : ¬ 2 ∣ ν.e ∨ ¬ 2 ∣ ν.h := by
    rw [← not_and_or]
    rintro ⟨he2, hh2⟩
    have hcop1 : Nat.gcd ν.e ν.h = 1 := ν.hcop
    have hd : (2 : ℕ) ∣ Nat.gcd ν.e ν.h := Nat.dvd_gcd he2 hh2
    rw [hcop1] at hd
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- (s0+1, u0+1) lies in the region: the on-or-below pin `e + h ≤ e*h` at ℓ = 1.
    have key : ν.h + ν.e ≤ ν.e * ν.h := by
      have := Nat.add_le_mul hh he
      rwa [Nat.mul_comm] at this
    simp only [XNode.region, p1Region, hell, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ioc, Nat.add_sub_cancel_left, mul_one]
    omega
  · -- 2 ≤ (e-1)(h-1): the odd one is ≥ 3, so its factor is ≥ 2.
    rcases hodd with hE | hH
    · have h3 : 2 ≤ ν.e - 1 := by omega
      have h1 : 1 ≤ ν.h - 1 := by omega
      calc (2 : ℕ) = 2 * 1 := by norm_num
        _ ≤ (ν.e - 1) * (ν.h - 1) := Nat.mul_le_mul h3 h1
    · have h3 : 2 ≤ ν.h - 1 := by omega
      have h1 : 1 ≤ ν.e - 1 := by omega
      calc (2 : ℕ) = 1 * 2 := by norm_num
        _ ≤ (ν.e - 1) * (ν.h - 1) := Nat.mul_le_mul h1 h3
  · -- 2 ∣ (e-1)(h-1): the odd one gives an even factor.
    rcases hodd with hE | hH
    · have hd : (2 : ℕ) ∣ (ν.e - 1) := by omega
      exact dvd_mul_of_dvd_left hd _
    · have hd : (2 : ℕ) ∣ (ν.h - 1) := by omega
      exact dvd_mul_of_dvd_right hd _

end LeanUrat.MovesX
