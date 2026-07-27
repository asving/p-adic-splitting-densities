/-
Unit U41  (MovesR base layer)  [O_chain, SETTING-FREE RESTATEMENT — see DEVIATION]
moves_ref: "a branch of relative accumulated degree δ″ at ambient O_{δ_j} targets
O_{δ_j·δ″}, literally a subring chain in W(F̄_p)" (R23's ring-theoretic half;
family-closure is `SettingsFamily.desc*`, NOT this unit — finding 20).
deps: Defs (U1), U3. difficulty: easy.
sketch: two applications of `O_le` at the divisibility witnesses `⟨δrel, rfl⟩` and
`⟨δ'', rfl⟩`.
DEVIATION (recorded in MANIFEST): the blueprint states this over `S : Setting p` as
`O p S.δ ≤ O p S.δabs ∧ O p S.δabs ≤ O p (S.δabs * δ'')`. `Setting` is excluded from
this split-off by the base-layer charge, so the parameterization is replaced by
explicit `ℕ+` arguments via the DEFINITIONAL translation `m := S.δ`, `δrel := S.δrel`,
`S.δabs = S.δ * S.δrel = m * δrel` (`Setting.δabs` is literally `S.δ * S.δrel`).
Ring content unchanged; the `Setting`-typed form re-enters with the parked corpus.
-/
import Mathlib
import LeanUrat.MovesRBase.Defs
import LeanUrat.MovesRBase.U3_O_le

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace MovesRBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- U41: the recursion clause's ring-side witness — the literal subring chain
`O_m ≤ O_{m·δrel} ≤ O_{m·δrel·δ″}` in `W(F̄_p)` (with `m·δrel` the absolute
accumulated index `δ_j`). -/
theorem O_chain (m δrel δ'' : ℕ+) :
    O p m ≤ O p (m * δrel) ∧ O p (m * δrel) ≤ O p (m * δrel * δ'') :=
  ⟨O_le p ⟨δrel, rfl⟩, O_le p ⟨δ'', rfl⟩⟩

end MovesRBase
