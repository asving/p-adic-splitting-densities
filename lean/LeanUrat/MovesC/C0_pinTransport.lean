/-
Unit C0.pinTransport — moves_ref: §C.0.5 pin-transport corollary: Θ*(E) is a digit system with
the same pins.
Constructive: D'.pinned := D.pinned; for a pinned coordinate i, D'.solve i f reads off the
transported equation.  Since Θ is unitriangular ((Θx)_i = x_i + corr_i(x_{<i})), the equation
"(Θx)_i = D.solve i (fun j => (Θx)_j)" is affine in x_i with unit coefficient, so it re-presents
as x_i = [D.solve i on the Θ-image of the earlier coordinates] − corr_i(x_{<i}).  The Θ-image of
a coordinate j < i is recovered from x_{<i} alone (unitriangularity: Θ at j sees only j' ≤ j),
here via the extension-by-zero of the partial assignment.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

variable {p : ℕ}

theorem C0_pinTransport {m : ℕ} (D : Locus p m) {Θ : (Fin m → ZMod p) → (Fin m → ZMod p)} (h : IsUnitriangular Θ) : ∃ D' : Locus p m, (∀ x, D'.IsSolution x ↔ D.IsSolution (Θ x)) ∧ ∀ j : Fin m, D'.pinned j = D.pinned j := by
  -- Extract the unitriangular correction functions.
  choose corr hcorr using h
  -- Θ at coordinate i depends only on coordinates ≤ i.
  have key : ∀ (i : Fin m) (g₁ g₂ : Fin m → ZMod p),
      (∀ k : Fin m, k ≤ i → g₁ k = g₂ k) → Θ g₁ i = Θ g₂ i := by
    intro i g₁ g₂ hag
    rw [hcorr i g₁, hcorr i g₂, hag i le_rfl]
    have harg : (fun j (_ : j < i) => g₁ j) = (fun j (_ : j < i) => g₂ j) := by
      funext k hk
      exact hag k hk.le
    rw [harg]
  refine ⟨⟨D.pinned,
      fun i f => D.solve i (fun j _ => Θ (fun k => if hk : k < i then f k hk else 0) j)
        - corr i f⟩, ?_, ?_⟩
  · intro x
    -- The extension-by-zero of x below i agrees with Θ x on coordinates < i.
    have argeq : ∀ i : Fin m,
        D.solve i (fun j (_ : j < i) => Θ (fun k => if hk : k < i then x k else 0) j)
        = D.solve i (fun j _ => Θ x j) := by
      intro i
      congr 1
      funext j hj
      apply key j
      intro k hk
      have hki : k < i := lt_of_le_of_lt hk hj
      simp only [dif_pos hki]
    -- corr on the full assignment is exactly (Θ x)_i − x_i.
    have correq : ∀ i : Fin m, corr i (fun j _ => x j) = Θ x i - x i := by
      intro i
      rw [hcorr i x]; ring
    constructor
    · intro hx i hpin
      have hxi : x i = D.solve i (fun j (_ : j < i) => Θ (fun k => if hk : k < i then x k else 0) j)
          - corr i (fun j _ => x j) := hx i hpin
      rw [argeq i, correq i] at hxi
      linear_combination hxi
    · intro hx i hpin
      have hxi : Θ x i = D.solve i (fun j _ => Θ x j) := hx i hpin
      show x i = D.solve i (fun j (_ : j < i) => Θ (fun k => if hk : k < i then x k else 0) j)
          - corr i (fun j _ => x j)
      rw [argeq i, correq i, hxi]; ring
  · intro j; rfl

end LeanUrat.MovesC
