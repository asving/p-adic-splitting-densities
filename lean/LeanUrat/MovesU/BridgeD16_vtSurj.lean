/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.Defs
import LeanUrat.MovesT.Defs

/-!
# IB-D16 — `vt_surj` (bridge campaign BP1, cluster c9)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†5)
("REALIZABILITY MUST BE IN THE CARRIER") / §4 group D (IB-D16).

INFORMAL STATEMENT: the COMPLETENESS direction of the (†5) carrier (the
`TreePin.vt_surj` field supply, DefsLedger.lean:361 — round-3 CRITICAL 3's
converse): every `MovesT.VTree` of typemult σ.1, threshold ≤ N, REALIZED at the
pinned level-N model/chart (0 < N), lies in the carrier's image — transfer DOWN
to the tree's own level `lvl V = max (V.thr n) 1` (†6) gives the carrier's
`RealizedSelf` membership datum, and `vt = Subtype.val` makes the preimage
explicit.

DEPS: IB-D5 (`TransferRow`).  TRANSCRIPTION RESOLUTION (recorded): IB-D3/IB-D5
are other clusters' units, not landed — the transfer row's `realizes_transfer`
enters as the binder `transfer` with (†6)'s verbatim type, and the (†5) carrier
`{V' // V'.typemult = σ.1 ∧ RealizedSelf V'}` is INLINED as an anonymous
subtype in the conclusion (`lvl` inlined as `max (V'.thr n) 1`, the BridgeD13
convention).  Once IB-D3 lands, its `Tree σ` is definitionally this subtype and
IB-D18 consumes the statement verbatim.  The transfer-down HALF is split out
(`bridge_realizedSelf_of_realizes`) because IB-D18's wiring consumes it
separately.

PROOF SKETCH (R, ~20): transfer-down = one `transfer` application (0 < lvl by
`le_max_right`, thr ≤ lvl by `le_max_left`); vt_surj = `⟨⟨V, htm, transfer-down⟩,
rfl⟩`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- TRANSFER DOWN to the tree's own level (†6 consumed once): realization at
    any positive N ≥ thr gives the (†5) carrier's `RealizedSelf` datum
    (realization at `max (V.thr n) 1`). -/
theorem bridge_realizedSelf_of_realizes {p : ℕ} [Fact p.Prime] {n : ℕ}
    {pol : MovesD.CanonPolicy p (ZMod p)}
    (Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol)
    (chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N))
    (transfer : ∀ (V : MovesT.VTree p (ZMod p)) (N N' : ℕ)
      (hN : 0 < N) (hN' : 0 < N'), V.thr n ≤ N → V.thr n ≤ N' →
      MovesT.Realizes (Tm N) (chart N hN) V →
      MovesT.Realizes (Tm N') (chart N' hN') V)
    (V : MovesT.VTree p (ZMod p)) (N : ℕ) (hN : 0 < N) (hthr : V.thr n ≤ N)
    (hreal : MovesT.Realizes (Tm N) (chart N hN) V) :
    MovesT.Realizes (Tm (max (V.thr n) 1))
      (chart (max (V.thr n) 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
      V := by
  sorry

/-- (†5) `vt_surj`, the COMPLETENESS direction at the inlined carrier (file
    header): a realized σ.1-typemult tree within threshold lies in the (†5)
    carrier's `Subtype.val` image.  THE `TreePin.vt_surj` FIELD SUPPLY
    (DefsLedger.lean:361) after IB-D18's repackaging at IB-D3's carrier. -/
theorem bridge_vt_surj {p : ℕ} [Fact p.Prime] {n : ℕ}
    {pol : MovesD.CanonPolicy p (ZMod p)}
    (Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol)
    (chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N))
    (transfer : ∀ (V : MovesT.VTree p (ZMod p)) (N N' : ℕ)
      (hN : 0 < N) (hN' : 0 < N'), V.thr n ≤ N → V.thr n ≤ N' →
      MovesT.Realizes (Tm N) (chart N hN) V →
      MovesT.Realizes (Tm N') (chart N' hN') V)
    (σ : SplittingType n) (V : MovesT.VTree p (ZMod p)) (N : ℕ) (hN : 0 < N)
    (htm : V.typemult = σ.1) (hthr : V.thr n ≤ N)
    (hreal : MovesT.Realizes (Tm N) (chart N hN) V) :
    ∃ T : {V' : MovesT.VTree p (ZMod p) // V'.typemult = σ.1 ∧
        MovesT.Realizes (Tm (max (V'.thr n) 1))
          (chart (max (V'.thr n) 1)
            (lt_of_lt_of_le zero_lt_one (le_max_right _ _))) V'},
      T.1 = V := by
  sorry

end LeanUrat.MovesU
