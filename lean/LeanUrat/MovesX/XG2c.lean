/-
Unit XG.2c interTrichotomy — X.3(d)'s first half, DERIVED (finding 11)
[PROVED, fleet 2026-07-28]
moves_ref: "(d) … an f whose complete tree is undetected at EVERY level has an ns leaf
(TB-CAP's clause trichotomy — detection fails at all N only on the (τ-ns) class)".
sketch: f ∉ InfTree ⟹ Finite (Branch f); if every leaf ns-free, XG.2b exits f from some
Undec N — contradiction; so some leaf carries an ns node; `C.nsCover` places f in a
fiber. deps: XG.2b. difficulty: MEDIUM. hyp_fields: nsCover ((NS-c) input).
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XG2b

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem interTrichotomy {n p : ℕ} [Fact p.Prime] (C : XCtx n p) :
    (⋂ N, C.Undec N) ⊆ InfTree C ∪ (⋃ i, C.nsFiber i) := by
  intro f hf
  by_cases hfin : Finite (C.Branch f)
  · -- finite tree: either an ns leaf exists (fiber) or detection contradicts f ∈ ⋂ Undec
    by_cases hns : ∃ b : C.Branch f, C.children b = ∅ ∧ ∃ ν ∈ C.hist b, C.nsTrack ν
    · exact Or.inr (Set.mem_iUnion.2 (C.nsCover f hns))
    · exfalso
      have hleaves : ∀ b : C.Branch f, IsLeafB C b → ∀ ν ∈ C.hist b, ¬ C.nsTrack ν := by
        intro b hb ν hν hν'
        exact hns ⟨b, hb, ν, hν, hν'⟩
      obtain ⟨N, hN⟩ := detectJoin C f hfin hleaves
      exact hN (Set.mem_iInter.1 hf N)
  · exact Or.inl hfin

end LeanUrat.MovesX
