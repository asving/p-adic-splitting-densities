/-
Unit U29.gate_NP  (HC-2 campaign, E-phase — blueprint §5 Layer E)
moves_ref: the MovesD gate instance: for the worked shape P̂* (MovesD §3.3's gate row /
G1_gates `PhatStar`), the CONSTRUCTED system's largest equation level + 1 = 5 = Shape.NP
(the note's own derivation "NP(P̂*) = 1 + 4 = 5") — U14's arithmetic at one census-pinned
instance.  deps: U14, MovesD.G1_gates (`PhatStar`, `PhatStar_NPband` PROVED).
difficulty: easy-medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.MovesD.G1_gates

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The census-pinned NPband value (re-export of MovesD's PROVED gate: NP(P̂*) = 5). -/
theorem gate_NP_value : PhatStar.NPband 3 = 5 := PhatStar_NPband

/-- GATE: at N = 5 = NPband(P̂*), every constructed fresh support coordinate of a matched
coherent history fits below level 5 (U14's bound at the instance). -/
theorem gate_NP_fits {F : Type*} [Field F] [Finite F] {H : History 2 F}
    (hm : PhatStar.MatchesHist H) (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (hbox : InBox 3 H) {keys : ℕ → Polynomial ℤ_[2]}
    (S : PresentSeed 2 F H 3 5 keys) (vOf : VOf 2 (3 * 5)) :
    ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ cl ∈ (mkFresh H 3 5 S vOf i hi).clauses,
      ∀ c ∈ cl.support, (boxChart 3 5 c).1 + 1 ≤ 5 := by
  sorry

/-- GATE (attainment): the bound is EXACT — some constructed equation coordinate sits at
level 4 (the note's "largest pinned base level = 4, at c₀"; shape-side, the band point
(4,0) of `PhatStar_bandS1_iff`). -/
theorem gate_NP_attained {F : Type*} [Field F] [Finite F] {H : History 2 F}
    (hm : PhatStar.MatchesHist H) (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (hbox : InBox 3 H) {keys : ℕ → Polynomial ℤ_[2]}
    (S : PresentSeed 2 F H 3 5 keys) (vOf : VOf 2 (3 * 5)) :
    ∃ (i : ℕ) (hi : i < H.nodes.length),
      ∃ cl ∈ (mkFresh H 3 5 S vOf i hi).clauses,
        ∃ c ∈ cl.support, (boxChart 3 5 c).1 = 4 := by
  sorry

end LeanUrat.MovesJ
