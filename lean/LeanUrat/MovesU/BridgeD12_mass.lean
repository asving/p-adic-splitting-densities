/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-D12 — `mass` DEF + SANITY (bridge campaign BP1, cluster c9)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†9) /
§4 group D (IB-D12).

INFORMAL STATEMENT: the tree mass, defined AT THE TREE'S OWN LEVEL as the
normalized fiber count (†9's "cleanest equivalent"):
`mass σ T := (Nat.card {x : MovesD.Box p (n·lvl T) // (vt σ T).fiberAt (Tm (lvl T)) (chart _ _) x}) / p^(n·lvl T)`
in ℝ≥0∞, at `lvl T := max (thr T) 1`.  Plus a `mass_ne_top`-style sanity law and
the lvl edge display at thr = 0 (mass reads the LEVEL-1 fiber).

DEPS: IB-D3 (`Tree σ` carrier + `lvl`).  TRANSCRIPTION RESOLUTION (recorded):
IB-D3 is another cluster's unit, not landed — the mass is stated CARRIER-FREE
on the raw `MovesT.VTree` (the (†5) carrier's `vt` is `Subtype.val`, so the
carrier mass IS this mass precomposed with `.val`; IB-D14's consumer performs
the subtype repackaging), with `lvl` INLINED as `max (V.thr n) 1` (the same
inlining BridgeD13_sliceFinite.lean's probe half already uses — no `lvl` def
here, avoiding a name collision with IB-D3's).  `Tm`/`chart` are binders per
the D-group's Tm-parametric discipline (blueprint §5 R7: only IB-D1 blocks on
the designer round).

PROOF SKETCH: def-only + two sanity lemmas (R, ~15).  `ne_top`: the numerator
is a cast ℕ (finite), the denominator `(p : ℝ≥0∞)^(n·lvl)` is nonzero (p ≥ 2)
and finite, so the ENNReal division is ≠ ⊤ (`ENNReal.div_eq_top` case split).
thr-0 edge: rewrite `max 0 1 = 1`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open scoped ENNReal

/-- (†9) THE TREE MASS at the tree's own level `lvl V = max (V.thr n) 1`
    (inlined — file header): the normalized count of the level-`lvl` fiber of
    `V` at the pinned model/chart.  Carrier-free form: at the (†5) carrier this
    is `mass σ := bridgeMass Tm chart ∘ Subtype.val` (IB-D14's repackaging). -/
noncomputable def bridgeMass {p : ℕ} [Fact p.Prime] {n : ℕ}
    {pol : MovesD.CanonPolicy p (ZMod p)}
    (Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol)
    (chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N))
    (V : MovesT.VTree p (ZMod p)) : ℝ≥0∞ :=
  (Nat.card {x : MovesD.Box p (n * max (V.thr n) 1) //
      V.fiberAt (Tm (max (V.thr n) 1))
        (chart (max (V.thr n) 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
        x} : ℝ≥0∞)
    / (p : ℝ≥0∞) ^ (n * max (V.thr n) 1)

/-- SANITY (`mass_ne_top`-style, †9): the mass is finite — cast-ℕ numerator
    over a nonzero finite denominator ((p : ℝ≥0∞) ≥ 2). -/
theorem bridgeMass_ne_top {p : ℕ} [Fact p.Prime] {n : ℕ}
    {pol : MovesD.CanonPolicy p (ZMod p)}
    (Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol)
    (chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N))
    (V : MovesT.VTree p (ZMod p)) :
    bridgeMass Tm chart V ≠ ⊤ := by
  sorry

/-- THE lvl EDGE (†9 tail): at threshold 0 the mass reads the LEVEL-1 fiber
    (lvl = max 0 1 = 1) — the same guard discipline as `TreePin.chart`
    (round-3 CRITICAL 1: no level-0 chart exists). -/
theorem bridgeMass_thr_zero {p : ℕ} [Fact p.Prime] {n : ℕ}
    {pol : MovesD.CanonPolicy p (ZMod p)}
    (Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol)
    (chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N))
    (V : MovesT.VTree p (ZMod p)) (h : V.thr n = 0) :
    bridgeMass Tm chart V
      = (Nat.card {x : MovesD.Box p (n * 1) //
          V.fiberAt (Tm 1) (chart 1 one_pos) x} : ℝ≥0∞)
        / (p : ℝ≥0∞) ^ (n * 1) := by
  sorry

end LeanUrat.MovesU
