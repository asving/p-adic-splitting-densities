/-
Unit U-22 `rs3_det_symbolic` (medium) — E0 RE-SCOPED to all-active BASE pools
(R51, Codex#8-2): the note demands E0 at base pools + consumed legs (legs_reg),
NEVER at every prime-power pool.  moves_ref: "at all-active primes (cofinitely
many …) K_e(p) = A and ρ(A) < 1 gives det(I − A) ≠ 0; a rational function
vanishing at infinitely many prime evaluations is 0".  deps: U-19, U-20, U-21c,
U-22b, U-22c, U-27 (R58).  sketch: at an all-active base pool Act = univ
(act_spec + the locus); if det = 0 in Qq its evaluation vanishes there (U-20),
contradicting U-21c; U-22b/U-22c + prime infinitude give infinitely many
all-active base pools.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.EvalDet
import LeanUrat.MovesS.E0DetNeZero
import LeanUrat.MovesS.AllActivePrimes
import LeanUrat.MovesS.RatfuncEvalInfinite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem rs3_det_symbolic {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (hdc : DegCons T)
    (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (PP : Set ℚ) (hsub : PP ⊆ M.Pools)
    (hbase : ∀ q₀, q₀ ∈ PP ↔ ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ))
    (hact : ∀ e (he : e ∈ Finset.Icc 1 n), ∀ q₀ ∈ PP ∩ allActivePools M,
      Nonempty (PoolHyp T M RB e (hK e he) q₀)) :
    ∀ e (he : e ∈ Finset.Icc 1 n), (1 - Kmat T RB e (hK e he)).det ≠ 0 :=
  sorry

end LeanUrat.MovesS
