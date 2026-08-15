/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3Drain3
import UniformityCheck.N3Exact

/-!
# UniformityCheck.N3Tie — the `n = 3` brackets, with the drainage slack REMOVED

Unit `UNIFORMITY-CHECK-N3C`, layer 5. `N3Exact.lean` §3 had to carry an explicit `+ 1/q²` on
every `n = 3` upper bound over THE density, because `n = 3` drainage was open there: all it had
was `genuineDensity_three_le` (`genuineDensity ≤ decidedDensity + 1/q²`). `N3Drain3.lean` closes
that gap — `genuineDensity_three_eq_decidedDensity` — so this file restates the transfer and the
two concrete gate brackets WITHOUT slack.

Nothing here is new mathematics; it is the audit trail of what the tie buys. The superseded
slacked statements (`genuine3_bracket_of_decided`, `gate_bracket3_padic_two_genuine`,
`gate_bracket3_padic_three_genuine`) are left standing in `N3Exact.lean`: they are still true, and
keeping them makes the improvement checkable side by side.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

section Tie

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The `n = 3` transfer, slack-free** (supersedes `genuine3_bracket_of_decided`): a certified
two-sided bracket on the inner density is a bracket on THE density, with the SAME upper end. -/
theorem genuine3_bracket_of_decided_tie {σ : FactorizationType} {l u : ℝ}
    (hl : l ≤ decidedDensity O 3 σ) (hu : decidedDensity O 3 σ ≤ u) :
    l ≤ genuineDensity O 3 σ ∧ genuineDensity O 3 σ ≤ u := by
  rw [genuineDensity_three_eq_decidedDensity]
  exact ⟨hl, hu⟩

end Tie

/-- **GATE BRACKET (n = 3), q = 2, over THE density, SLACK-FREE.** The `1/4` of
`gate_bracket3_padic_two_genuine` is gone: these are exactly the certified brackets of
`gate_bracket3_padic_two`, now valid for `genuineDensity`. The HMENU3 predicted values
`(4/93, 28/93, 8/31, 22/93, 5/31)` lie inside them (`gate_bracket3_hmenu3_two`). -/
theorem gate_bracket3_padic_two_tie :
    ((1 : ℝ) / 512 ≤ genuineDensity ℤ_[2] 3 c3split
        ∧ genuineDensity ℤ_[2] 3 c3split ≤ 3 / 8)
    ∧ ((1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 3 c3linInert
        ∧ genuineDensity ℤ_[2] 3 c3linInert ≤ 319 / 512)
    ∧ ((1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 3 c3inert
        ∧ genuineDensity ℤ_[2] 3 c3inert ≤ 319 / 512)
    ∧ ((1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 3 c3linRam
        ∧ genuineDensity ℤ_[2] 3 c3linRam ≤ 223 / 512)
    ∧ ((1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 3 c3ram
        ∧ genuineDensity ℤ_[2] 3 c3ram ≤ 223 / 512) := by
  simp only [genuineDensity_three_eq_decidedDensity]
  exact gate_bracket3_padic_two

/-- **GATE BRACKET (n = 3), q = 3, over THE density, SLACK-FREE.** The `1/9` is gone. Note the
`c3inert` bracket `[8/27, 5/9]` now pins THE density of the inert cubics between `0.29630` and
`0.5556`, with HMENU3's `36/121 = 0.29752` just above the lower end — the exact value proved in
`N3InertExact.lean`. -/
theorem gate_bracket3_padic_three_tie :
    ((1 : ℝ) / 27 ≤ genuineDensity ℤ_[3] 3 c3split
        ∧ genuineDensity ℤ_[3] 3 c3split ≤ 8 / 27)
    ∧ ((1 : ℝ) / 3 ≤ genuineDensity ℤ_[3] 3 c3linInert
        ∧ genuineDensity ℤ_[3] 3 c3linInert ≤ 16 / 27)
    ∧ ((8 : ℝ) / 27 ≤ genuineDensity ℤ_[3] 3 c3inert
        ∧ genuineDensity ℤ_[3] 3 c3inert ≤ 5 / 9)
    ∧ ((4 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 3 c3linRam
        ∧ genuineDensity ℤ_[3] 3 c3linRam ≤ 25 / 81)
    ∧ ((2 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 3 c3ram
        ∧ genuineDensity ℤ_[3] 3 c3ram ≤ 23 / 81) := by
  simp only [genuineDensity_three_eq_decidedDensity]
  exact gate_bracket3_padic_three

/-! ## Axiom census -/

section AxCheck

#print axioms UniformityCheck.genuine3_bracket_of_decided_tie
#print axioms UniformityCheck.gate_bracket3_padic_two_tie
#print axioms UniformityCheck.gate_bracket3_padic_three_tie

end AxCheck

end UniformityCheck
