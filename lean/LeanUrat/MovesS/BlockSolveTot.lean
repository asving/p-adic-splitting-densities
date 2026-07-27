/-
Unit U-16c `blockSolveTot` (medium) — the σ′-FREE totalized triangular solve
(R2-17): `bTot(τ) := Σ_{term o} TG + Σ_{split o} J · ∏_j legTot` (halted legs 1,
continuing legs `powSubst δ (blockSolveTot …)`), and `blockSolveTot e :=
(1 - Kmat)⁻¹ *ᵥ bTot` — the exit-total vector the MARKED pairing consumes.
moves_ref: "the scalar output ι_e^T (I − K_e)^{−1} b_e" (ORIENTATION).
No hdet parameter (Mathlib `⁻¹` total — the R29 clarifier's convention).
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.BSplitDef

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

noncomputable def bTot (T : TableShape n) (M : MeasuredSide T)
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (e : ℕ) (he : e ∈ Finset.Icc 1 n) : T.State e → Qq :=
  sorry

noncomputable def blockSolveTot (T : TableShape n) (M : MeasuredSide T)
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (e : ℕ) (he : e ∈ Finset.Icc 1 n) : T.State e → Qq :=
  sorry

end LeanUrat.MovesS
