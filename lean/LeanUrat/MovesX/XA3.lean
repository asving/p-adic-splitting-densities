/-
Unit XA.3 t1Witness  [PROVED]
moves_ref: T1 witness "(s+e, u+(ℓ−1)h): ON S …" — the (P1) ON-OR-BELOW pin (§4 trap).
deps: XA.1. difficulty: EASY.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem t1Witness {n : ℕ} (ν : XNode n) (h1 : rowOf ν = .T1) :
    (ν.s0 + ν.e, ν.u0 + (ν.ell - 1) * ν.h) ∈ ν.region ∧ 1 ≤ ν.region.card := by
  -- From `rowOf ν = .T1` the row classifier (XA.1) forces `2 ≤ ν.ell`.
  have hell : 2 ≤ ν.ell := ((rowTotal ν).2.1.mp h1).2
  have epos := ν.epos
  have hpos := ν.hpos
  -- Write `ν.ell = m + 1` with `m ≥ 1` to eliminate the `ℓ - 1` subtraction.
  obtain ⟨m, hm⟩ : ∃ m, ν.ell = m + 1 := ⟨ν.ell - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  -- The witness point lies in the region: it is ON the segment (equality in the filter).
  have hmem : (ν.s0 + ν.e, ν.u0 + (ν.ell - 1) * ν.h) ∈ ν.region := by
    unfold XNode.region p1Region
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- first coordinate in `Ioc s0 (s0 + e*ℓ)`
      rw [Finset.mem_Ioc, hm]
      have hle : ν.e ≤ ν.e * (m + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    · -- second coordinate in `Ioc u0 (u0 + h*ℓ)`
      rw [Finset.mem_Ioc, hm]
      simp only [Nat.add_sub_cancel]
      have hpos2 : 0 < m * ν.h := Nat.mul_pos (by omega) (by omega)
      have hle2 : m * ν.h ≤ ν.h * (m + 1) := by nlinarith
      omega
    · -- filter predicate: on the segment, `h·e + e·(m·h) = e·h·(m+1)`
      rw [hm]
      simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
      have : ν.h * ν.e + ν.e * (m * ν.h) = ν.e * ν.h * (m + 1) := by ring
      omega
  exact ⟨hmem, Finset.one_le_card.mpr ⟨_, hmem⟩⟩

end LeanUrat.MovesX
