/-
Unit U-25 `marked_def` (easy) — the μ̂-typed MARKED-entrance total (aggregate
DEFINED, R2-17).  moves_ref: "(RS.1-MARKED) the pairing ι_e^T(I − K_e)^{−1}b_e is
the μ̂-typed MARKED-entrance total … NEVER summed into R_σ."  Identification with
`M.markedVal` = the PINNED W1m (seam; never claimed here).  No hdet parameter
(Mathlib `⁻¹` total — R29 clarifier; W1m's hdet binder is arity slack).
The no-Add/no-coercion fence is structural: `MuHat` carries no algebra.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.BlockSolveTot

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

variable {n : ℕ}

noncomputable def markedPairing (T : TableShape n) (M : MeasuredSide T)
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (e : ℕ) (he : e ∈ Finset.Icc 1 n) : MuHat :=
  ⟨RB.ι e ⬝ᵥ ((1 - Kmat T RB e (hK e he))⁻¹ *ᵥ bTot T M RB hdc hK e he)⟩

end LeanUrat.MovesS
