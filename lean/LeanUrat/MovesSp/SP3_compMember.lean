/-
Unit Sp.compMember — moves_ref: "For every n, every prime p, every f in the monic
degree-n coefficient box, every chain η ∈ T_can(f) …, and every read r of η's
CATALOGUE WORD …: the read's retained datum is a member of 𝒮_n^raw".
sketch: induction on r: r = 0 via `InCatalogue.root` (M.hRoot); r + 1 via
`InCatalogue.step` with SuccStep ASSEMBLED from M.hStage + M.hCoh at r + 1 —
the assembly is the derivation, not an assumption. difficulty: easy-medium.
hypothesis_fields (STANDING for group F): hRoot, hStage, hCoh, hHalt (SP-COMP
steps (1)/(2)/(3)/(3′)/(5) — §B2-DEF D.4/D.5/D.6/D.7/D.8/D.10 + §C DOM via §D4-R
L11 + §D4-R L2/L3/L5; owner HC-1/MovesD; OPEN, never proved here) and hVerdictPin
(THE D4R.0-K(c) RESIDUAL — the verdict pin, owner [3t] via VP; explicit per F7).
hVerdictPin is UNUSED by this unit's proof but part of the interface it quantifies
over [REV 3, G4: the field keeps the conditionality VISIBLE, not type-enforced —
a model discharges (verdict, hVerdictPin) trivially; WHICH verdict is VP-owned].
(hf/hdeg carry the note's "monic degree-n coefficient box" binder — unused
computationally, kept for quantifier fidelity.)
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SP_COMP (n p : ℕ) [Fact p.Prime] (f : Polynomial ℤ_[p])
    (hf : f.Monic) (hdeg : f.natDegree = n) (M : CanTreeModel n p f)
    (η : M.Branch) (r : ℕ) (hr : (r : ℕ∞) < M.len η) :
    InCatalogue n (M.datum η r) := sorry

end LeanUrat.MovesSp
