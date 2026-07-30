/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-D18 — `bridgeTreePin` ASSEMBLY (bridge campaign BP1, cluster c9)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 / §4
group D (IB-D18: "pol/Tm/chart/chart_inj := chartWitness_inj/boxeq := A11/
boxeq_digits/vt*/canonical_pin/treeOf_pin").

INFORMAL STATEMENT: the full `TreePin n p X F seam` record (DefsLedger.lean:344,
the round-2 CRITICAL 2 named premise) assembled with the chart PINNED to the
digit-0 chart `chartWitness`/`chartWitness_inj` (the built non-vacuity witness,
DefsLedger.lean:299–307; IB-D2's semantics check pinned the choice) and every
remaining field wired from its D/A-group supplier.

DEPS: D1–D17 (+ A11 for `boxeq`/`boxeq_digits`).  TRANSCRIPTION RESOLUTION
(recorded): the suppliers live in other clusters (D1 pol/Tm; A11 boxeq +
digits law; D3/D4 carrier + vt laws; D15/D16 vt_real/vt_surj — THIS cluster,
carrier-free forms; D7 canonical_pin; D17 treeOf_pin — THIS cluster) — so the
assembly is PARAMETRIC: each field except `chart`/`chart_inj` is a binder with
the `TreePin` field's verbatim type AT `chart := chartWitness n`.  The unit's
content is the type-checked wiring: it fixes EXACTLY the obligation list
IB-F4's `mkUInstance` must discharge, with the chart pin compiled (no free
chart survives).  Assembly-only — no sorry.

PROOF SKETCH: record literal (R, ~15).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- THE TREE/CLASSIFIER PIN ASSEMBLY at the pinned digit-0 chart: every field
    of `TreePin` (DefsLedger.lean:344) from its supplier (binders — file
    header), with `chart := chartWitness n` and `chart_inj :=
    chartWitness_inj n` COMPILED (the round-3 CRITICAL 1 guarded chart, its
    non-vacuity already PROVED in DefsLedger). -/
noncomputable def bridgeTreePin (n p : ℕ) [Fact p.Prime]
    (X : ClassifierSpec n p) (F : FiberSeries n p X) (seam : TreeSeam n p X F)
    (pol : MovesD.CanonPolicy p (ZMod p))
    (Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol)
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N))
    (boxeq_digits : ∀ (N : ℕ) (f : Box p n N) (i : Fin n),
      f i = ∑ k : Fin N,
        ((boxeq N f (digitIdx n N i k)).val : ZMod (p ^ N))
          * (p : ZMod (p ^ N)) ^ (k : ℕ))
    (vt : ∀ σ : SplittingType n, F.Tree σ → MovesT.VTree p (ZMod p))
    (vt_inj : ∀ σ, Function.Injective (vt σ))
    (vt_typemult : ∀ (σ : SplittingType n) (T : F.Tree σ),
      (vt σ T).typemult = σ.1)
    (vt_thr : ∀ (σ : SplittingType n) (T : F.Tree σ),
      F.thr σ T = (vt σ T).thr n)
    (vt_real : ∀ (σ : SplittingType n) (T : F.Tree σ) (N : ℕ) (hN : 0 < N),
      F.thr σ T ≤ N →
      MovesT.Realizes (Tm N) (chartWitness n N hN) (vt σ T))
    (vt_surj : ∀ (σ : SplittingType n) (V : MovesT.VTree p (ZMod p)) (N : ℕ)
      (hN : 0 < N), V.typemult = σ.1 → V.thr n ≤ N →
      MovesT.Realizes (Tm N) (chartWitness n N hN) V →
      ∃ T : F.Tree σ, vt σ T = V)
    (canonical_pin : ∀ (N : ℕ) (hN : 0 < N) (f : Box p n N)
      (σ : SplittingType n),
      X.canonical N f = some σ ↔
        ∃ T : F.Tree σ, F.thr σ T ≤ N ∧
          (vt σ T).fiberAt (Tm N) (chartWitness n N hN) (boxeq N f))
    (treeOf_pin : ∀ (σ : SplittingType n) (N : ℕ) (hN : 0 < N)
      (f : {f : Box p n N // X.canonical N f = some σ}),
      (vt σ (seam.treeOf σ N f)).fiberAt (Tm N) (chartWitness n N hN)
        (boxeq N f.1)) :
    TreePin n p X F seam where
  pol := pol
  Tm := Tm
  chart := chartWitness n
  chart_inj := chartWitness_inj n
  boxeq := boxeq
  boxeq_digits := boxeq_digits
  vt := vt
  vt_inj := vt_inj
  vt_typemult := vt_typemult
  vt_thr := vt_thr
  vt_real := vt_real
  vt_surj := vt_surj
  canonical_pin := canonical_pin
  treeOf_pin := treeOf_pin

end LeanUrat.MovesU
