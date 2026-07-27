/-
Unit XD.4 x2hypAssembled  [proved]
moves_ref: "(X2-HYP) … DERIVED given (X2-AFF) ∧ (X2-CAP) … both prices in the ONE
currency Σ h_r, combined constant c₀⁺ := c₀ + c_cap".
deps: XD.1–XD.3. difficulty: MEDIUM. hyp_fields: X2AffP, X2CapP by name.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XD1
import LeanUrat.MovesX.XD2
import LeanUrat.MovesX.XD3

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem x2hypAssembled {n : ℕ} (X : XFamily n) (K : XConsts n)
    (AF : X2AffP n X K) (CP : X2CapP n X K)
    (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f)
    (hb : FourthPieceB (X.ctx p) b) (N : ℕ)
    (hN : N < (X.ctx p).threshold b + capHB (X.ctx p) b) :
    (N : ℚ) - 1 - K.ccap < (K.c0 + K.ccap) * ((dTotal ((X.ctx p).hist b) : ℚ) + 1) ^ 2 ∨
    (N : ℚ) - 1 - K.ccap < (K.c0 + K.ccap) * (maxH ((X.ctx p).hist b) : ℚ) ^ 2 := by
  -- (X2-AFF): thr(b) ≤ 1 + c₀·Σh
  have haff := AF p f b hb
  -- (X2-CAP) + cap 0-convention (XD.1): cap(b) ≤ c_cap·(1 + Σh) in BOTH detectability cases
  have hcap : ((capHB (X.ctx p) b : ℕ) : ℚ) ≤ K.ccap * (1 + (sumH ((X.ctx p).hist b) : ℚ)) := by
    rcases capTotal (X.ctx p) f b with ⟨hcap0, hcapD⟩
    by_cases hdet : (X.ctx p).capDetectable b
    · rw [hcapD hdet]
      exact CP p f b hb hdet
    · rw [hcap0 hdet]
      simp only [Nat.cast_zero]
      exact mul_nonneg K.ccapnonneg (by positivity)
  -- N < thr + cap, over ℚ
  have hNq : (N : ℚ) < ((X.ctx p).threshold b : ℚ) + (capHB (X.ctx p) b : ℚ) := by
    exact_mod_cast hN
  -- combine both prices in the ONE currency Σh, with combined constant c₀ + c_cap
  have hE : (N : ℚ) - 1 - K.ccap < (K.c0 + K.ccap) * (sumH ((X.ctx p).hist b) : ℚ) := by
    nlinarith [hNq, haff, hcap]
  -- (XD.2) x2hypCount: Σh ≤ (d_total + 1)·max h
  have hcount : (sumH ((X.ctx p).hist b) : ℚ) ≤
      ((dTotal ((X.ctx p).hist b) : ℚ) + 1) * (maxH ((X.ctx p).hist b) : ℚ) := by
    have h := x2hypCount ((X.ctx p).hist b) ((X.ctx p).wf b)
    exact_mod_cast h
  have hc0cc : (0 : ℚ) ≤ K.c0 + K.ccap := add_nonneg K.c0nonneg K.ccapnonneg
  have d1nn : (0 : ℚ) ≤ (dTotal ((X.ctx p).hist b) : ℚ) + 1 := by positivity
  have mnn : (0 : ℚ) ≤ (maxH ((X.ctx p).hist b) : ℚ) := by positivity
  -- the √-dichotomy (XD.3 style): split on max h ≤ d_total+1 vs. the reverse
  rcases le_total ((maxH ((X.ctx p).hist b) : ℚ)) ((dTotal ((X.ctx p).hist b) : ℚ) + 1) with hmd | hmd
  · left
    have hSbound : (sumH ((X.ctx p).hist b) : ℚ) ≤ ((dTotal ((X.ctx p).hist b) : ℚ) + 1) ^ 2 := by
      calc (sumH ((X.ctx p).hist b) : ℚ)
          ≤ ((dTotal ((X.ctx p).hist b) : ℚ) + 1) * (maxH ((X.ctx p).hist b) : ℚ) := hcount
        _ ≤ ((dTotal ((X.ctx p).hist b) : ℚ) + 1) * ((dTotal ((X.ctx p).hist b) : ℚ) + 1) :=
            mul_le_mul_of_nonneg_left hmd d1nn
        _ = ((dTotal ((X.ctx p).hist b) : ℚ) + 1) ^ 2 := by ring
    calc (N : ℚ) - 1 - K.ccap
        < (K.c0 + K.ccap) * (sumH ((X.ctx p).hist b) : ℚ) := hE
      _ ≤ (K.c0 + K.ccap) * ((dTotal ((X.ctx p).hist b) : ℚ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hSbound hc0cc
  · right
    have hSbound : (sumH ((X.ctx p).hist b) : ℚ) ≤ (maxH ((X.ctx p).hist b) : ℚ) ^ 2 := by
      calc (sumH ((X.ctx p).hist b) : ℚ)
          ≤ ((dTotal ((X.ctx p).hist b) : ℚ) + 1) * (maxH ((X.ctx p).hist b) : ℚ) := hcount
        _ ≤ (maxH ((X.ctx p).hist b) : ℚ) * (maxH ((X.ctx p).hist b) : ℚ) :=
            mul_le_mul_of_nonneg_right hmd mnn
        _ = (maxH ((X.ctx p).hist b) : ℚ) ^ 2 := by ring
    calc (N : ℚ) - 1 - K.ccap
        < (K.c0 + K.ccap) * (sumH ((X.ctx p).hist b) : ℚ) := hE
      _ ≤ (K.c0 + K.ccap) * (maxH ((X.ctx p).hist b) : ℚ) ^ 2 :=
          mul_le_mul_of_nonneg_left hSbound hc0cc

end LeanUrat.MovesX
