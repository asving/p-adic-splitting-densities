/-
Unit Sp.n3rootLetters [REV 2, F16 — ONE statement, the membership equivalence
the note asserts; multiplicity content carried by n3card53's Nodup, so duplicate
enum candidates (repeated equal λ-factors in the generator) are harmless] —
moves_ref: "GROUP R — ROOT, stage (D, w, W) = (1, 1, 3): 21 letters." + "per
stage, the (G1)–(G6)+(B1)–(B5corrected) letters are exactly the displayed rows".
deps: Sp.speciesEnumComplete, Sp.reflSucc (rootAdmissibleB_iff). sketch: (→)
RootAdmissible ⇒ Coherent ∧ Budget ⇒ s ∈ speciesEnum 3 (enumComplete), then
root3_enum_check reads off membership; (←) groupR_admissible + the reflection
iff. difficulty: medium (perf).
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- decide fact 1 [REV 4, Codex-6]. -/
theorem root3_enum_check : ((speciesEnum 3).all fun s =>
    rootAdmissibleB 3 s == groupR.contains s) = true := sorry

/-- decide fact 2. -/
theorem groupR_admissible : (groupR.all (rootAdmissibleB 3)) = true := sorry

theorem rootAdmissible3_iff (s : Species) :
    RootAdmissible 3 s ↔ s ∈ groupR := sorry

end LeanUrat.MovesSp
