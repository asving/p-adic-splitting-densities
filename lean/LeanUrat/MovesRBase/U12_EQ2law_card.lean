/-
Unit U12  (MovesR base layer)  [EQ2law_card]
moves_ref: "(EQ-2)'s displayed consequence '|𝔸_δ| = q_δ^a = |𝔸|^δ' on the pinned
domain" — PROVABLE from `card_eq` + hypothesized `EQ2law` by `pow_mul`.
deps: Defs (U1 + the U9–U11 supporting vocabulary), U5. difficulty: easy.
sketch: consumes h's DIMENSION conjunct only: `Nat.card (alpha δ x) = p ^ aDim δ x
= p ^ (δ · aDim 1 x) = (p^δ)^{aDim 1 x} = qq p δ ^ aDim 1 x`, and
`= (p ^ aDim 1 x)^δ = Nat.card (alpha 1 x) ^ δ` (pow arithmetic; `card_eq` at δ, 1).
-/
import Mathlib
import LeanUrat.MovesRBase.Defs
import LeanUrat.MovesRBase.U5_qq_mul

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace MovesRBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- U12: (EQ-2)'s displayed consequence `|𝔸_δ| = q_δ^a = |𝔸|^δ` on the pinned
(δ-stable) domain, conditional on the hypothesized `EQ2law`. -/
theorem EQ2law_card {Sp} (AD : AlphabetData p Sp) (h : EQ2law p AD) :
    ∀ (δ : ℕ+) (x : AD.Pos), AlphabetData.Stable p AD δ x →
      Nat.card (AD.alpha δ x) = qq p δ ^ AD.aDim 1 x ∧
      Nat.card (AD.alpha δ x) = Nat.card (AD.alpha 1 x) ^ (δ : ℕ) := sorry

end MovesRBase
