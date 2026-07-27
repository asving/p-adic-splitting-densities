/-
Unit Sp.b4Derived — moves_ref: "(B4) … hence the Σ eᵢgᵢμᵢ-type constraint
e_r·g_r·μ_r·D_r ≤ e_r·ℓ_r·D_r = w′_r·D_r ≤ n."
sketch: g·μ ≤ ℓ (B4) scaled by e·D; w′ ≤ W ≤ n/D (B3) ⇒ w′·D ≤ n (Nat.div:
W ≤ n/D → W·D ≤ n via Nat.le_div_iff_mul_le, D ≥ 1). difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem egμD_le {n} {s : Species} (hc : Coherent s) (hb : Budget n s)
    {g μ : ℕ} (hsel : s.sel = some (g, μ)) : s.e * g * μ * s.D ≤ s.wraw * s.D ∧
    s.wraw * s.D ≤ n := by
  -- Coherence supplies D ≥ 1 (WellTyped); the rest of Coherent is unused here.
  obtain ⟨⟨hD1, _, _, _, _, _⟩, _, _, _, _, _⟩ := hc
  -- Budget supplies (B3) w′ ≤ W ≤ n/D and (B4) g·μ ≤ ℓ.
  obtain ⟨_, _, ⟨hs0w, _, _, hWnD⟩, hB4, _⟩ := hb
  have hgμ : g * μ ≤ s.ell := hB4 (g, μ) hsel
  refine ⟨?_, ?_⟩
  · -- (B4) scaled by e·D: e·g·μ·D = e·(g·μ)·D ≤ e·ℓ·D = w′·D.
    change s.e * g * μ * s.D ≤ s.e * s.ell * s.D
    calc s.e * g * μ * s.D = s.e * (g * μ) * s.D := by ring
      _ ≤ s.e * s.ell * s.D := by gcongr
  · -- (B3): w′ ≤ W and W ≤ n/D with D ≥ 1 ⇒ w′·D ≤ W·D ≤ n.
    have hD0 : 0 < s.D := hD1
    have hWD : s.W * s.D ≤ n := (Nat.le_div_iff_mul_le hD0).mp hWnD
    have hwrawW : s.wraw ≤ s.W := by omega
    calc s.wraw * s.D ≤ s.W * s.D := by gcongr
      _ ≤ n := hWD

end LeanUrat.MovesSp
