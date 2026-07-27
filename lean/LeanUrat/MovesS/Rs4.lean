/-
Unit U-28 `rs4_rational_step` (medium) — RS.4 with the full inherited set (R2-19).
moves_ref: "(RS.4) Σ_σ R_σ = 1 identically in q … RS.4 inherits EVERY condition
of the block solve".  THE DISPLAYED INHERITED SET, all explicit in RS4Chain:
C.L (nine CL-5 inputs) · C.B (RS.1's set: xrb/CL-9, recursion_meas/CL-10+CL-8
provenance) · C.hns ((ns-null)) · C.pools_e0 + C.legs_reg (ESCAPE(E0)/CL-1, full
per-pool quantifier) · C.WshP/wsh_ok (denominator regularity; CL-17(ii)'s
PRODUCTION burden is the seam pin W17ii/S-8 — INHERITED AND OPEN via the typed
premise `h17 : C.wsh17_pin` (R57): the acceptance record MAY NOT be marked
unconditional while W17ii is open) · RB in (iv)-POLY form (CL-6) + XHD-s geoms +
INIT-RAT ιP + (J-RAT) jP · C.x3_total (X.3/CL-4, pinned W-4) · C.rs1_equates
(pinned W-1e) · C.rsh_interp (pinned W-1's shadow).
sketch: eval(Σ Rsh − 1) at p ∈ PrimePools = Σ Rval − decidedTotal = 0
(rsh_interp, rs1_equates, x3_total); prime infinitude + U-27.
-/
import LeanUrat.MovesS.Interfaces
import LeanUrat.MovesS.RatfuncEvalInfinite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem rs4_rational_step {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e} {F : ShapeFam T}
    (C : RS4Chain T M RB hdc hK F) (h17 : C.wsh17_pin) (hdet : DetHyp T RB hK) :
    (∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ) = 1 := by
  -- The difference is a rational function vanishing at every prime pool; RS.2 for
  -- R_σ is derived, so we show `(Σ_σ Rsh) − 1 = 0` in ℚ(q) via U-27.
  have key : (∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ) - 1 = 0 := by
    refine ratfunc_eval_infinite _ C.PrimePools ?_ ?_ ?_
    · -- PrimePools is infinite: it is the image of the infinitely many primes.
      refine Set.infinite_of_injective_forall_mem
        (f := fun p : Nat.Primes => ((p.val : ℕ) : ℚ)) ?_ ?_
      · exact Nat.cast_injective.comp Subtype.val_injective
      · intro a
        exact (C.prime_base _).mpr ⟨a.val, a.2, rfl⟩
    · -- Denominator regularity: the difference lies in the regular subring OKat x.
      intro x hx
      rw [← mem_OKat_iff]
      exact sub_mem (sum_mem (fun σ hσ => (C.rsh_interp σ hσ x hx hdet).choose)) (one_mem _)
    · -- Evaluation vanishes at each prime pool p: Σ_σ Rval − decidedTotal = 0.
      intro x hx
      have hok : ∀ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ ∈ OKat x :=
        fun σ hσ => (C.rsh_interp σ hσ x hx hdet).choose
      have hsum : (∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ) ∈ OKat x :=
        sum_mem hok
      have hmem : (∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ) - 1 ∈ OKat x :=
        sub_mem hsum (one_mem _)
      -- The sum evaluates to 1 at p (rsh_interp ↦ Rval, rs1_equates, x3_total).
      have hsplit :
          (⟨∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ, hsum⟩ : OKat x)
            = ∑ σ ∈ C.Sigmas.attach,
                (⟨Rsh T M RB hdc hK hdet F C.WshP σ.1, hok σ.1 σ.2⟩ : OKat x) := by
        apply Subtype.ext
        push_cast
        exact (Finset.sum_attach C.Sigmas
          (fun σ => Rsh T M RB hdc hK hdet F C.WshP σ)).symm
      have hstep : ∀ σ ∈ C.Sigmas.attach,
          ((evalAt x ⟨Rsh T M RB hdc hK hdet F C.WshP σ.1, hok σ.1 σ.2⟩ : ℚ) : ℝ)
            = C.Rval σ.1 x :=
        fun σ _ => (C.rsh_interp σ.1 σ.2 x hx hdet).choose_spec
      have hone :
          evalAt x ⟨∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ, hsum⟩ = 1 := by
        have hcast :
            ((evalAt x ⟨∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ, hsum⟩ : ℚ) : ℝ)
              = 1 := by
          rw [hsplit, map_sum]
          push_cast
          rw [Finset.sum_congr rfl hstep,
            Finset.sum_attach C.Sigmas (fun σ => C.Rval σ x),
            C.rs1_equates x hx, C.x3_total x hx]
        exact_mod_cast hcast
      -- Assemble: eval(Σ Rsh − 1) = eval(Σ Rsh) − 1 = 1 − 1 = 0.
      change evalAt x ⟨(∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ) - 1, hmem⟩ = 0
      rw [show (⟨(∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ) - 1, hmem⟩ : OKat x)
            = ⟨∑ σ ∈ C.Sigmas, Rsh T M RB hdc hK hdet F C.WshP σ, hsum⟩ - 1 from rfl,
        map_sub, map_one, hone, sub_self]
  exact sub_eq_zero.mp key

end LeanUrat.MovesS
