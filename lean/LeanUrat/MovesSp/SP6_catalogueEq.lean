/-
Unit Sp.n3catalogueEq — moves_ref: "**Definition (the raw catalogue; rev 3 …)**
𝒮_n^raw := the least set …" + "[RE-VERIFIED against the rev-3 definition: …]".
deps: Sp.memCoherent, Sp.speciesEnumComplete, Sp.reflSucc, Sp.n3rootLetters,
Sp.n3closureStep, Sp.n3reachable. sketch: (→) induction on InCatalogue: root case
via n3rootLetters (s ∈ enum by speciesEnumComplete); step via n3closureStep. (←)
each letter: root case by rootAdmissibleB + refl lemmas; non-root via n3reachable
+ `.step`. difficulty: medium.
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SnRaw3_eq : ∀ s, InCatalogue 3 s ↔ s ∈ catalogue3 := sorry

end LeanUrat.MovesSp
