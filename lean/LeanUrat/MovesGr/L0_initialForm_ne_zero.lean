import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem L0_initialForm_ne_zero (S : SideVal p) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) : S.initialForm f ≠ 0 := by
  intro h
  have h2 := congrArg (fun x : S.Gr => x (S.deg f)) h
  simp only [SideVal.initialForm, DirectSum.of_eq_same, DirectSum.zero_apply] at h2
  -- h2 : S.mkPiece f = 0
  simp only [SideVal.mkPiece, Submodule.Quotient.mk_eq_zero] at h2
  -- h2 : ⟨f, _⟩ ∈ S.gtIn (S.deg f)
  have hlt : (S.deg f : WithTop ℤ) < S.w f := h2
  rw [S.deg_eq hf] at hlt
  exact lt_irrefl _ hlt

#print axioms L0_initialForm_ne_zero
