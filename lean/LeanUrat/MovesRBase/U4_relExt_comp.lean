/-
Unit U4  (MovesR base layer)  [relExt_comp]
moves_ref: "'(O_δ)_{δ′} = O_{δδ′}' is bookkeeping inside W(F̄_p)" — the composition
law under the relExt convention (`rfl`/`mul_assoc`), plus `O_le_relExt`.
deps: Defs (U1), U3. difficulty: easy.
-/
import Mathlib
import LeanUrat.MovesRBase.Defs
import LeanUrat.MovesRBase.U3_O_le

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace MovesRBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- U4(i): the convention IS the identity — "never an identification up to
isomorphism". -/
theorem relExt_eq (m δ' : ℕ+) : relExt p m δ' = O p (m * δ') := rfl

/-- U4(ii): iterated base change composes by index multiplication (`mul_assoc`). -/
theorem relExt_relExt (m δ' δ'' : ℕ+) :
    relExt p (m * δ') δ'' = relExt p m (δ' * δ'') := by
  unfold relExt; rw [mul_assoc]

/-- U4(iii): the base sits inside its own base change (via U3). -/
theorem O_le_relExt (m δ' : ℕ+) : O p m ≤ relExt p m δ' := O_le p ⟨δ', rfl⟩

end MovesRBase
