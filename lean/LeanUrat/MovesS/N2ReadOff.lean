/-
Unit U-29d5 `n2_readoff` (medium) — inhabits `ReadOffBundle` with S := the
BASE-PRIME pools (scope CORRECTED, Codex#4-10) — exactly what U-29d2's legs_reg
packages cover (consumedDeltas = {1} at this instance), infinite, ⊆
allActivePools; the per-(e, q₀) packages are READ OFF U-29d2's construction
(cited, not rebuilt); AVAgree from the explicit reduced denominators (q²+q+1 and
q³ nonvanishing at every q₀ ≥ 2 supply hok; the active solve = the explicit
values; no split legs).
-/
import LeanUrat.MovesS.N2Beta
import LeanUrat.MovesS.N2Det
import LeanUrat.MovesS.N2Pools

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

def n2BasePrimes : Set ℚ := {q₀ | ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ)}

theorem n2_base_sub : n2BasePrimes ⊆ allActivePools n2M := sorry

theorem n2_base_infinite : n2BasePrimes.Infinite := sorry

noncomputable def n2_readoff : ReadOffBundle n2BasePrimes n2_base_sub n2B n2hdet :=
  sorry

end LeanUrat.MovesS
