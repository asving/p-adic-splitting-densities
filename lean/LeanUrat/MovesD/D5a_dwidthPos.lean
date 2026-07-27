/-
Unit D5a.Dwidth_pos  (MovesD campaign, E-phase)  [AUX]
informal: every read of a coherent history has positive frame width.
deps: MovesC.Defs.
sketch: induction on r — root `deg Φ₀ = 1` + `hDwidth`; step width chain
`D_{r+1} = e·g·D_r`, e, g ≥ 1.  difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Coherent histories have positive frame width at every read. -/
theorem Dwidth_pos {H : History p F} (hcoh : HistoryCoherent H) (r : ℕ)
    (hr : r < H.nodes.length) : 0 < (H.nodes[r]'hr).Dwidth := by
  induction r with
  | zero =>
    have h1 : (H.nodes[0]'hr).σ.Φ.natDegree = 1 := hcoh.1 hr
    have h2 : (H.nodes[0]'hr).Dwidth = (H.nodes[0]'hr).σ.Φ.natDegree := (H.nodes[0]'hr).hDwidth
    omega
  | succ n ih =>
    have hn : n < H.nodes.length := by omega
    have hstep := hcoh.2.2.2 n hr
    have hD : (H.nodes[n+1]'hr).Dwidth = (H.nodes[n]'hn).childWidth := hstep.2.2.2.2.2.1
    have ihn : 0 < (H.nodes[n]'hn).Dwidth := ih hn
    have he : 1 ≤ (H.nodes[n]'hn).e := (H.nodes[n]'hn).he
    have hg : 1 ≤ (H.nodes[n]'hn).g := (H.nodes[n]'hn).hg
    rw [hD, Node.childWidth]
    exact Nat.mul_pos (Nat.mul_pos he hg) ihn

end LeanUrat.MovesD
