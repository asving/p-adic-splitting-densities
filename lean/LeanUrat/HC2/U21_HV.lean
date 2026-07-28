/-
Unit U21.readsOf_HV  (HC-2 campaign, E-phase — blueprint §5 Layer D; escalation risk:
exponent bookkeeping across two conventions — the MovesC F10 index lesson applies)
moves_ref: §C C.0 (HV) "the data IDENTITY pattern lead of ν_{i+1} = vtx(ν_i) with the
FULL transported vertex value".
deps: D4 (incl. the NEW clause (vi), N-4), Moves L5_landVertexDigit{,_repair} +
L5_landTransport_R4 + LandingCylinderL (PROVED — D.8's two-sided landing with the vertex
unit).  difficulty: medium-hard bookkeeping (post-N-4).
sketch: the adjacent read's hinge digit is the transported vertex digit by D.8's (VERTEX)
clause; unfold `Node.vtx`'s scalar bookkeeping (`z̄^{a−μm̂}` — the anchor/normalization
exponents match `LandingCylinderL`'s `T(μ·m̂ − a)` unit literally).
hypothesis_fields: none.
N-4 RESTATEMENT (2026-07-28, sign-off round — §9 F-3 executed; STATEMENT byte-unchanged,
the restatement is the DERIVATION ROUTE): the layer-2 TERMINAL interface gap is closed
by `SideReads` clause (vi) (Defs) — the vertex read-off `σ.digPrime zbar (Bh μ) = vtx`
at the designated next key's development. U21 is now a DERIVATION: at the transition
i → i+1, `ReadsOf` gives the frame-(i+1) development B' of f with the recorded child key
= read i's Φnext (the pin), so clause (vi) at read i fires on B' giving
`σ_i.digPrime zbar_i (B' μ_i) = vtx(ν_i)`; SideReads(i+1) clause (ii) at the top stride
`k = wSide'/e'` (adjacency puts `s0'+wSide' = μ_i`) reads the recorded pattern lead off
`B' μ_i` as a frame-(i+1) residual; the cross-frame digit bookkeeping
(`TransitionCoreL.child_dig_frame` + L5's z̄-exponent identities) ties the two. The
clause records only the minimal un-derivable fact — never (HV) itself. PROOF QUEUED
(fleet; medium-hard bookkeeping). U31's clause-(vi) gate re-run is the mandatory
non-vacuity companion (queued there).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- (HV) for runs: at an adjacent consecutive read of a run, the pattern LEAD equals the
transported vertex value in `F` (the (HV) conjunct of `TransitionAdmissible`). -/
theorem readsOf_HV {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hadj : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide
      = (H.nodes[i]'(by omega)).μ) :
    (((H.nodes[i+1]'hi1).pat ((H.nodes[i+1]'hi1).wSide / (H.nodes[i+1]'hi1).e)
        : ↥(H.nodes[i+1]'hi1).σ.K) : F)
      = (H.nodes[i]'(by omega)).vtx := by
  sorry

end LeanUrat.MovesJ
