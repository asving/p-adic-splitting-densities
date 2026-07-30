/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-D17 — `bridgeTreeOf` / `thr_le` / `treeOf_pin` (bridge campaign BP1, cluster c9)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†9)
tail ("`treeOf σ N f := (canonical_pin ⇒ ∃ T…).choose` with `thr_le`/`treeOf_pin`
from choose_spec; single-valuedness by (†7u)") / §4 group D (IB-D17).

INFORMAL STATEMENT: the canonical-tree assignment of every decided-σ class —
`TreeSeam.treeOf`'s supply (DefsLedger.lean:232) — read off the canonical_pin
iff by choice; its threshold bound (`TreeSeam.thr_le`) and its fibering law
(`TreePin.treeOf_pin`, DefsLedger.lean:369) from `choose_spec`.

DEPS: IB-D7 (`bridgeCanonical` + `canonical_pin`).  TRANSCRIPTION RESOLUTION
(recorded): IB-D7 is another cluster's unit, not landed — the pin enters as the
binder `hpin` with `TreePin.canonical_pin`'s verbatim type
(DefsLedger.lean:365–368), stated over an abstract `X`/`F` (D7's construction
supplies `X.canonical` with the pin holding by (†7u)-uniqueness + dif
unfolding); the N = 0 leg needs `canonical 0 = none` (D7's dite yields it —
`hzero` binder here), since the pin itself is guarded to 0 < N and the
decided-σ subtype at level 0 must be seen empty.  IB-F4/IB-D18 instantiate
both binders at D7's outputs.

PROOF SKETCH (R, ~20): `bridgeTreeOf` = dite on 0 < N; positive leg
`((hpin N hN f.1 σ).mp f.2).choose`; zero leg `False.elim` from `hzero` vs
`f.2` (compiled below — definitional, no sorry).  `thr_le`/`treeOf_pin` =
`choose_spec`'s two conjuncts, dif_pos unfolding (sorried).  Single-valuedness
across choices is (†7u) = IB-D6 (not consumed here; needed only by uniqueness
consumers).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (†9) THE CANONICAL-TREE ASSIGNMENT `treeOf` — `TreeSeam.treeOf`'s supply:
    the fibering tree the canonical_pin's ∃ produces at a decided-σ class
    (choice); at N = 0 the decided-σ subtype is empty (`hzero`), closed by
    `False.elim`. -/
noncomputable def bridgeTreeOf {n p : ℕ} [Fact p.Prime] {X : ClassifierSpec n p}
    (F : FiberSeries n p X)
    {pol : MovesD.CanonPolicy p (ZMod p)}
    (Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol)
    (chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N))
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N))
    (vt : ∀ σ : SplittingType n, F.Tree σ → MovesT.VTree p (ZMod p))
    (hzero : ∀ f : Box p n 0, X.canonical 0 f = none)
    (hpin : ∀ (N : ℕ) (hN : 0 < N) (f : Box p n N) (σ : SplittingType n),
      X.canonical N f = some σ ↔
        ∃ T : F.Tree σ, F.thr σ T ≤ N ∧
          (vt σ T).fiberAt (Tm N) (chart N hN) (boxeq N f))
    (σ : SplittingType n) (N : ℕ)
    (f : {f : Box p n N // X.canonical N f = some σ}) : F.Tree σ :=
  if hN : 0 < N then ((hpin N hN f.1 σ).mp f.2).choose
  else
    False.elim (by
      have h0 : N = 0 := by omega
      subst h0
      have h2 := f.2
      rw [hzero f.1] at h2
      exact Option.some_ne_none σ h2.symm)

/-- (†9) `thr_le` — `TreeSeam.thr_le`'s supply: the assigned tree's threshold is
    within the deciding level (choose_spec, first conjunct). -/
theorem bridgeTreeOf_thr_le {n p : ℕ} [Fact p.Prime] {X : ClassifierSpec n p}
    (F : FiberSeries n p X)
    {pol : MovesD.CanonPolicy p (ZMod p)}
    (Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol)
    (chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N))
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N))
    (vt : ∀ σ : SplittingType n, F.Tree σ → MovesT.VTree p (ZMod p))
    (hzero : ∀ f : Box p n 0, X.canonical 0 f = none)
    (hpin : ∀ (N : ℕ) (hN : 0 < N) (f : Box p n N) (σ : SplittingType n),
      X.canonical N f = some σ ↔
        ∃ T : F.Tree σ, F.thr σ T ≤ N ∧
          (vt σ T).fiberAt (Tm N) (chart N hN) (boxeq N f))
    (σ : SplittingType n) (N : ℕ)
    (f : {f : Box p n N // X.canonical N f = some σ}) :
    F.thr σ (bridgeTreeOf F Tm chart boxeq vt hzero hpin σ N f) ≤ N := by
  sorry

/-- (†9) `treeOf_pin` — `TreePin.treeOf_pin`'s supply (DefsLedger.lean:369):
    the assigned tree FIBERS at the class (choose_spec, second conjunct). -/
theorem bridgeTreeOf_pin {n p : ℕ} [Fact p.Prime] {X : ClassifierSpec n p}
    (F : FiberSeries n p X)
    {pol : MovesD.CanonPolicy p (ZMod p)}
    (Tm : ∀ N : ℕ, MovesD.TreeModel p (ZMod p) n N (n * N) pol)
    (chart : ∀ N : ℕ, 0 < N → Fin n → Fin (n * N))
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N))
    (vt : ∀ σ : SplittingType n, F.Tree σ → MovesT.VTree p (ZMod p))
    (hzero : ∀ f : Box p n 0, X.canonical 0 f = none)
    (hpin : ∀ (N : ℕ) (hN : 0 < N) (f : Box p n N) (σ : SplittingType n),
      X.canonical N f = some σ ↔
        ∃ T : F.Tree σ, F.thr σ T ≤ N ∧
          (vt σ T).fiberAt (Tm N) (chart N hN) (boxeq N f))
    (σ : SplittingType n) (N : ℕ) (hN : 0 < N)
    (f : {f : Box p n N // X.canonical N f = some σ}) :
    (vt σ (bridgeTreeOf F Tm chart boxeq vt hzero hpin σ N f)).fiberAt
      (Tm N) (chart N hN) (boxeq N f.1) := by
  sorry

end LeanUrat.MovesU
