/-
Kernels/KD5 — BP4-c7 E-phase skeleton for unit KD5:
`x3aRoute_of_weightCharge_align` — WeightChargeFullP (via KD10's ladder-cap
route, or KD3 if a constant bound ever lands) + X1aAlignP at the inc state
⟹ X3aRouteP's RIGHT disjunct (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.D
+ §4 KD5, re-pointed from the TRACK-COUNT-only route per F3; adjudications
per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

RECORDED RESOLUTIONS (statement transcription):
· "X1aAlignP (inc state)" = the AlignState ⟨inc := true, recn := false⟩,
  VERBATIM the right disjunct of `MovesX.X3aRouteP`
  (MovesX/Defs.lean:424-426).
· The premises are the CONCLUSION Props of the feeding units (KD10 /
  KE8-territory ALIGN), not their internals — KD5 is pure route assembly
  (`Or.inr` + pairing), discharging cl2_route's SHAPE conditionally
  (`UpstreamTyped.cl2_route = MovesX.X3aRouteP`,
  MovesU/DefsLedger.lean:167).

deps: KD10 (or KD3) — as the WeightChargeFullP premise; the ALIGN state
feed (X1aAlignP ⟨true, false⟩) is KE8/ALIGN-inc territory, taken as a
premise.  Consumer: cl2_route → `x3Series` (XG4).
Sketch: exact Or.inr ⟨halign, hwc⟩.

Build: cd lean && lake build LeanUrat.Kernels.KD5
-/
import LeanUrat.MovesX.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

/-- KD5 (HEAD — blueprint-prescribed name `x3aRoute_of_weightCharge_align`):
the FULL weight charge + the inc-state alignment discharge X.3(a)'s route
disjunction through its right disjunct.  deps: KD10 (feeds `hwc`), the
ALIGN state (feeds `halign`).  Sketch: `Or.inr ⟨halign, hwc⟩`. -/
theorem x3aRoute_of_weightCharge_align {n : ℕ} (X : MovesX.XFamily n)
    (K : MovesX.XConsts n)
    (halign : MovesX.X1aAlignP n X ⟨true, false⟩)
    (hwc : MovesX.WeightChargeFullP n X K) :
    MovesX.X3aRouteP n X K := by
  sorry

end LeanUrat.Kernels
