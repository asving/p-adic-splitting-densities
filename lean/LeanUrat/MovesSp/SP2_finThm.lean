/-
Unit Sp.finThm — moves_ref: "Theorem SP-FIN. 𝒮_n^raw is FINITE and INDEPENDENT
of p, with the explicit (crude) bound |𝒮_n^raw| ≤ (n+2)^{n² + 3n + 12}."
deps: Sp.memCoherent, Sp.encodeInj, Sp.encodeCard. sketch: SnRaw ⊆ the coherent-
admissible set; encode injective there; `Set.Finite.of_finite_image`/
`Nat.card_le_card_of_injective`.
p-INDEPENDENCE: discharged BY TYPING (blueprint §0) — `SnRaw : ℕ → Set Species`
mentions no prime ("no field of the datum ... mentions p — the same list serves
every prime"); recorded here as the faithfulness witness, no clause.
difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SP_FIN (n : ℕ) (hn : 1 ≤ n) : (SnRaw n).Finite ∧
    Nat.card (SnRaw n) ≤ (n+2)^(n^2 + 3*n + 12) := sorry

end LeanUrat.MovesSp
