/-
Unit U-22c `allActive_cofinite_primes` (medium) — the base-prime face, chain
hypotheses EXPLICIT (R48 split; Codex#6-3's scope): "cofinitely many BASE primes
are all-active"; consumed by U-22 and U-24b's locus through prime_base/prime_sub.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.AllActiveCofinite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem allActive_cofinite_primes {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (PP : Set ℚ) (hsub : PP ⊆ M.Pools)
    (hbase : ∀ q₀, q₀ ∈ PP ↔ ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ)) :
    {q₀ ∈ PP | q₀ ∉ allActivePools M}.Finite :=
  sorry

end LeanUrat.MovesS
