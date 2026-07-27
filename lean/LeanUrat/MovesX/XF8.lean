/-
Unit XF.8 tailZero — UNCONDITIONAL  [E-phase: stated, body sorry]
moves_ref: "→ 0 as D → ∞".
sketch: tailExp → ∞ linearly; geometric squeeze. deps: XF.7. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XF7

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Filter Topology in
theorem tailZero (p n : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) :
    Filter.Tendsto (fun D => (tailCount p n D : ℚ) / (p : ℚ) ^ (n * D))
      Filter.atTop (nhds 0) := by
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℚ) < p := by linarith
  have hd : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast h2
    linarith
  -- `tailExp p n D → ∞` linearly in `D` (ceiling of an affine map with positive slope)
  have hinner : Filter.Tendsto (fun D => tailExp p n D) Filter.atTop Filter.atTop := by
    unfold tailExp
    apply tendsto_ceil_atTop.comp
    apply Filter.Tendsto.atTop_div_const hd
    simp only [Int.cast_natCast, sub_eq_add_neg]
    exact tendsto_atTop_add_const_right Filter.atTop _ tendsto_natCast_atTop_atTop
  -- `(p:ℚ)^(-k) → 0` as `k → ∞`, via `((p:ℚ)^k)⁻¹` and `p^k → ∞`
  have htoNat : Filter.Tendsto Int.toNat Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro m
    exact ⟨(m : ℤ), fun k hk => by omega⟩
  have hzpos : Filter.Tendsto (fun k : ℤ => (p : ℚ) ^ k) Filter.atTop Filter.atTop := by
    have hnat := tendsto_pow_atTop_atTop_of_one_lt hp1
    refine (hnat.comp htoNat).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℤ)] with k hk
    rw [Function.comp_apply, ← zpow_natCast, Int.toNat_of_nonneg hk]
  have houter : Filter.Tendsto (fun k : ℤ => (p : ℚ) ^ (-k)) Filter.atTop (nhds 0) := by
    have h := hzpos.inv_tendsto_atTop
    simp only [zpow_neg]
    exact h
  -- compose to get the geometric upper bound `(n-1)·p^(-tailExp) → 0`
  have hcomp : Filter.Tendsto (fun D => (p : ℚ) ^ (-tailExp p n D)) Filter.atTop (nhds 0) :=
    houter.comp hinner
  have hupper : Filter.Tendsto (fun D => ((n : ℚ) - 1) * (p : ℚ) ^ (-tailExp p n D))
      Filter.atTop (nhds 0) := by
    have h := hcomp.const_mul ((n : ℚ) - 1)
    simpa using h
  -- squeeze `0 ≤ tailCount / p^(nD) ≤ (n-1)·p^(-tailExp)` (upper bound from XF.7)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper ?_ ?_
  · intro D; positivity
  · intro D
    show (tailCount p n D : ℚ) / (p : ℚ) ^ (n * D)
      ≤ ((n : ℚ) - 1) * (p : ℚ) ^ (-tailExp p n D)
    have hb := tailCountBound p n D h2
    have hPe : (0 : ℚ) < (p : ℚ) ^ (tailExp p n D) := zpow_pos hp0 _
    have hPN : (0 : ℚ) < (p : ℚ) ^ (n * D) := pow_pos hp0 _
    rw [zpow_natCast] at hb
    rw [zpow_neg, div_le_iff₀ hPN, mul_assoc,
      mul_comm (((p : ℚ) ^ (tailExp p n D))⁻¹) ((p : ℚ) ^ (n * D)),
      ← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ hPe]
    exact hb

end LeanUrat.MovesX
