/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-!
# IB-D15 — `vt_real` FROM THE TRANSFER ROW (bridge campaign BP1, cluster c9)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4
(†5)/(†6) / §4 group D (IB-D15) / §5 R2.

INFORMAL STATEMENT: carrier realizability at the tree's own level transfers to
EVERY positive level ≥ threshold — the `TreePin.vt_real` field supply
(DefsLedger.lean:359): a tree realized at `lvl V = max (V.thr n) 1` (the (†5)
carrier's `RealizedSelf` membership datum) is realized at every N with
0 < N and thr ≤ N, by ONE application of the transfer row (†6).  R2's residual
duty rides here: realizability is IN the carrier, so `vt_real` REDUCES to the
transfer row — if even this version fails, the TransferRow is mis-scoped
(report, adjudication).

DEPS: IB-D3 (carrier), IB-D5 (`TransferRow` structure).  TRANSCRIPTION
RESOLUTION (recorded): both are other clusters' units, not landed — the
statement is CARRIER-FREE on the raw `MovesT.VTree` (`lvl` inlined as
`max (V.thr n) 1`, the BridgeD13 convention; the (†5) carrier's `vt` is
`Subtype.val` and `RealizedSelf` is exactly the `hself` premise, so IB-D18's
consumer only repackages the subtype), and the transfer row's
`realizes_transfer` field enters as the binder `transfer` with (†6)'s verbatim
type (the `fiber_transfer` field is NOT consumed here — it feeds IB-D8 only).

PROOF SKETCH (R, ~15): apply `transfer` from N₀ := max (V.thr n) 1 to N:
0 < N₀ by `le_max_right`, thr ≤ N₀ by `le_max_left`, thr ≤ N given, 0 < N
given, `hself` given.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (†5)/(†6) `vt_real`, carrier-free form (file header): self-realization at
    the tree's own level `max (V.thr n) 1` + the transfer row (†6,
    `realizes_transfer` — IB-D5's row, a binder here) give realization at every
    positive level ≥ threshold.  THE `TreePin.vt_real` FIELD SUPPLY
    (DefsLedger.lean:359) after IB-D18's subtype repackaging. -/
theorem bridge_vt_real {p : ℕ} [Fact p.Prime] {n : ℕ}
    {pol : MovesD.CanonPolicy p (ZMod p)}
    (Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol)
    (chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N))
    (transfer : ∀ (V : MovesT.VTree p (ZMod p)) (N N' : ℕ)
      (hN : 0 < N) (hN' : 0 < N'), V.thr n ≤ N → V.thr n ≤ N' →
      MovesT.Realizes (Tm N) (chart N hN) V →
      MovesT.Realizes (Tm N') (chart N' hN') V)
    (V : MovesT.VTree p (ZMod p))
    (hself : MovesT.Realizes (Tm (max (V.thr n) 1))
      (chart (max (V.thr n) 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
      V)
    (N : ℕ) (hN : 0 < N) (hthr : V.thr n ≤ N) :
    MovesT.Realizes (Tm N) (chart N hN) V := by
  exact transfer V (max (V.thr n) 1) N
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hN
    (le_max_left _ _) hthr hself

end LeanUrat.MovesU
