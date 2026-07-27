/-
Unit Sp.n3entrancePatterns [REV 2, F17: full roster, no ellipses; REV 3, C2: the
▸(1,2) rosters corrected to their TRUE three members per group — the note's own
R6 row {(1,2),(1,1)}▸(1,2) is a root ▸(1,2) letter and its menu law "▸(1,2) → Q2
letters" is row-unrestricted; the entrance display's "[R4/R5 rows]" bracket is an
ERRATUM CANDIDATE, verified at blueprint §9 and NOT baked into any target] —
moves_ref: "ENTRANCE SUB-CATALOGUE {ε} at n = 3 (loops as depth slots): into the
μ=2 block: root▸(1,2) [R4/R5 rows], or root▸(1,3)·(Q3-loop)^d·▸(1,2); into the
μ=3 block: root▸(1,3); into each increment landing (D ≥ 2): the
▸(2,1)/▸(3,1)/e=2/e=3 rows of R, Q2, Q3 prefixed by their cascades — a finite
list, displayed by the same map." [the bracket read per §9's verified correction:
the ▸(1,2) rows of R4/R5/R6]
sketch: decide per conjunct (filters over 53/21; edge checks). difficulty: easy.
(the loop-power (Q3-loop)^d is witnessed by the ONE loop edge — depth d is a
parameter, not a letter: EntranceShape's depth slot, SP-DAG scope)
-/
import LeanUrat.MovesSp.DefsN3

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem entrance3_patterns :
    -- into the μ=2 block, direct: root▸(1,2) = the ▸(1,2) rows of R4/R5/R6
    -- (three members; §9 — the note's bracket omits R6's)
    (groupR.filter fun s => s.sel == some (1, 2)) =
      [rootR4sel12, rootR5sel12, rootR6sel12] ∧
    -- into the μ=2 block, via the μ=3 loop: root▸(1,3)·(Q3-loop)^d·▸(1,2)
    succStepB 3 rootR6sel13 loopQ3 = true ∧
    succStepB 3 loopQ3 loopQ3 = true ∧
    ((groupQ3.filter fun s => s.sel == some (1, 2)).all fun q =>
      succStepB 3 loopQ3 q) = true ∧
    ((groupQ3.filter fun s => s.sel == some (1, 2)).length = 3) ∧
    -- into the μ=3 block: root▸(1,3)
    rootR6sel13.sel = some (1, 3) ∧ rootR6sel13 ∈ groupR ∧
    -- into the increment landings (D ≥ 2): the ▸(2,1)/▸(3,1)/e=2/e=3 rows of
    -- R, Q2, Q3, each stepping into its I letter
    ((catalogue3.filter fun s => s.sel == some (2, 1)).all fun s =>
      succStepB 3 s letterI22) = true ∧
    ((catalogue3.filter fun s => s.sel == some (3, 1)).all fun s =>
      succStepB 3 s letterI33) = true ∧
    ((catalogue3.filter fun s => (s.e == 2) && !(s.sel == none)).all fun s =>
      succStepB 3 s letterI21) = true ∧
    ((catalogue3.filter fun s => (s.e == 3) && !(s.sel == none)).all fun s =>
      succStepB 3 s letterI31) = true ∧
    -- …and each such row lives in R, Q2, or Q3 (never I, Q1: those are terminal)
    ((catalogue3.filter fun s => s.sel == some (2, 1) || s.sel == some (3, 1) ||
      ((s.e == 2 || s.e == 3) && !(s.sel == none))).all fun s =>
      (groupR ++ groupQ2 ++ groupQ3).contains s) = true := by decide

end LeanUrat.MovesSp
