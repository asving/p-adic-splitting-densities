/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.D3_carryDomain — products of nonzero homogeneous elements are nonzero

moves_ref: MOVES 1510–1511 "products of nonzero homogeneous elements nonzero
(c·c′·z̄^κ ≠ 0 in the field — the graded-domain property, irreducibility not
needed)". deps: D2. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- A nonzero homogeneous element is nonzero at its own coset (else it is `0`
everywhere). -/
private theorem homog_apply_ne_zero {F : Type*} [Field F] {e : ℕ}
    (w : CarryAlg F e) (τ : ZMod e) (hw : IsHomog w τ) (hw0 : w ≠ 0) : w τ ≠ 0 := by
  intro hcontra
  apply hw0
  funext ν
  by_cases hν : ν = τ
  · rw [hν]; exact hcontra
  · exact hw ν hν

/-- Unit D3: the graded-domain property of 𝒟. -/
theorem D3_carryDomain {F : Type*} [Field F] {e : ℕ} [NeZero e] {zbar : Fˣ}
    (P : CarryRingPack F e zbar) (x y : CarryAlg F e) (ρ σ : ZMod e)
    (hx : IsHomog x ρ) (hy : IsHomog y σ) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    (letI := P.ring; x * y) ≠ 0 := by
  -- The product is the twisted convolution; its `(ρ+σ)`-component is the single
  -- surviving term `x ρ · y σ · z̄^{carryExp ρ σ}`, a product of nonzeros in `F`.
  rw [P.mul_def x y]
  intro hcontra
  have hxρ : x ρ ≠ 0 := homog_apply_ne_zero x ρ hx hx0
  have hyσ : y σ ≠ 0 := homog_apply_ne_zero y σ hy hy0
  have hval : cmul zbar x y (ρ + σ) = x ρ * y σ * (zbar : F) ^ carryExp ρ σ := by
    simp only [cmul]
    rw [Finset.sum_eq_single ρ (fun b _ hb => by rw [hx b hb]; ring)
      (fun h => absurd (Finset.mem_univ ρ) h)]
    rw [add_sub_cancel_left]
  have hne : cmul zbar x y (ρ + σ) ≠ 0 := by
    rw [hval]
    exact mul_ne_zero (mul_ne_zero hxρ hyσ) (pow_ne_zero _ (Units.ne_zero zbar))
  rw [hcontra] at hne
  exact hne rfl

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D3_carryDomain
