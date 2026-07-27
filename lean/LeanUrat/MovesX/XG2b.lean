/-
Unit XG.2b detectJoin — X.3(b), the finite-level detection, DERIVED (finding 11)
[E-phase: stated, body sorry]
moves_ref: "(b) DETECTION AT A FINITE LEVEL [derived from accepted sources]. Every f
whose tree is complete with all leaves (τ-irr)/(τ-hen) … exits Undec(N) at its finite
threshold thr(T): Thm 2.1 … joined over the tree's finitely many branches with TB-CAP's
per-clause caps".
sketch: N := max over the finitely many leaf branches of (threshold b + capHB b)
(Finite ⟹ the max exists); `C.detectBranch` detects each ns-free leaf at N;
`C.undec_spec` (the Undec DEFINITION) closes.
deps: Defs. difficulty: MEDIUM. hyp_fields: XCtx's detectBranch + undec_spec (accepted
LOCAL inputs, blueprint §4).
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem detectJoin {n p : ℕ} [Fact p.Prime] (C : XCtx n p) (f : MonicBox n p)
    (hfin : Finite (C.Branch f))
    (hleaves : ∀ b : C.Branch f, IsLeafB C b → ∀ ν ∈ C.hist b, ¬ C.nsTrack ν) :
    ∃ N, f ∉ C.Undec N := by
  sorry

end LeanUrat.MovesX
