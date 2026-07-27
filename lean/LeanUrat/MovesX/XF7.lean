/-
Unit XF.7 tailCountBound — (3b-LEAN), UNCONDITIONAL (Ruling 2 — no V argument)
[E-phase: stated, body sorry]
moves_ref: "(3b) μ{f monic deg n : v_p(disc f) ≥ D} ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉}"
(auditor-confirmed arithmetic: 4 and 1/4 at (2,2,0)/(2,2,4); 2/3, 2/9, 2/27 at
(3,3,5/7/9)).
sketch: fiber over aTail ∈ (ZMod p^D)^{n−1} (XF.1); INSIDE the proof,
`valExtOf (fTail n p _ aTail)` (fTail ≠ 0: lead coeff n ≠ 0 in char 0) discharges
XF.6's V; ≤ (n−1)·p^{D−tailExp.toNat} residues per fiber; trivial-face check at
tailExp ≤ 0. deps: XF.1, XF.6, XF.3. difficulty: MEDIUM-HARD (carries XF.3's
stuck-risk — by ruling, a STUCK report, not a rider).
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XF1
import LeanUrat.MovesX.XF3
import LeanUrat.MovesX.XF6

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem tailCountBound (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) :
    (tailCount p n D : ℚ) * (p : ℚ) ^ (tailExp p n D) ≤
      (n - 1 : ℚ) * (p : ℚ) ^ ((n * D : ℕ) : ℤ) := by
  sorry

end LeanUrat.MovesX
