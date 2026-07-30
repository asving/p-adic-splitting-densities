/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-D10 — trueType N = 0 EDGE PROBE (bridge campaign BP1; gates IB-D9b)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†8,
ordering + fallback CORRECTED post-Codex finding 6) / §4 group D (IB-D10) / §5
R5.  This probe runs BEFORE the lift_true prover IB-D9b (the binding cross-area
countermodel-first rule).

SEALED PREDICTIONS (recorded before any proving):
(1) ∀-LIFT RE-VERIFICATION: `ZpReads` is the ∀-lift predicate
    (DefsLedger.lean:686–689) — an ∃-read would sink D9b's uniqueness route.
    COMPILED below as `zpReads_forall_lift := Iff.rfl` (a definitional read, no
    sorry): the re-verification the corrected †8 demands.
(2) THE LEVEL-0 EDGE: at N = 0 the box ring `ZMod (p^0) = ZMod 1` is trivial, so
    EVERY monic degree-n g lifts every f (`map_toZModPow_zero_eq_toPoly`), hence
    `ZpReads n p zf 0 f σ` pins zf's value on ALL monic degree-n polynomials at
    once — as soon as TWO monic degree-n lifts get DISTINCT zf values, NO σ is
    read at level 0 (`zpReads_level0_empty`).  Instance discharge duty (recorded
    OPEN, gated on IB-E11/Q2 — zfType is another cluster's unit): at the real
    `zfType`, the two witnesses are X^n (n factors X, each (e,f) = (1,1), value
    n·{(1,1)}) and the Eisenstein X^n − p (irreducible, totally ramified, value
    {(n,1)}), distinct for n ≥ 2 (the hn binder — R5).
(3) THE SINGLE-LIFT UNIQUENESS D9b ACTUALLY CONSUMES (the corrected fallback's
    display — sound at ALL N because of (1)): one lift g of f forces σ = σ' for
    any two σ's read at f.  COMPILED below (`zpReads_unique_of_lift`, real
    proof): (†8u)'s uniqueness rides ONE lift, supplied by `lift_exists` at
    every N including 0.

INSTANCE-LEVEL RESTATEMENT DEFERRED (transcription resolution, recorded): the
blueprint's display `bridgeTrueType 0 f = none` cannot be stated here —
`bridgeTrueType` is IB-D9a's def (another cluster, gated behind IB-E11's
zfType); once D9a lands, the edge follows from `zpReads_level0_empty` + the
witness distinctness by unfolding D9a's dite.  Per the corrected †8 tail, a
painful edge does NOT block D9b: (3) is what D9b consumes; the edge itself
stays a recorded-OPEN display until the E-group witnesses land.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Polynomial

/-- PREDICTION (1), COMPILED — the ∀-lift re-verification (corrected †8 tail):
    `ZpReads` IS the ∀-monic-lift predicate, definitionally.  If this ever fails
    `Iff.rfl`, D9b's uniqueness route is unsound — stop and report. -/
theorem zpReads_forall_lift {n p : ℕ} [Fact p.Prime]
    (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)) (N : ℕ)
    (f : Box p n N) (σ : SplittingType n) :
    ZpReads n p zf N f σ ↔
      ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
        g.map (PadicInt.toZModPow N) = f.toPoly → zf g = σ.1 :=
  Iff.rfl

/-- Level-0 lifting is AUTOMATIC: `ZMod (p^0) = ZMod 1` is trivial, so any two
    polynomials over it are equal (`Polynomial.ext` on subsingleton
    coefficients) — every g maps onto every level-0 box polynomial. -/
theorem map_toZModPow_zero_eq_toPoly {n p : ℕ} [Fact p.Prime]
    (g : Polynomial ℤ_[p]) (f : Box p n 0) :
    g.map (PadicInt.toZModPow 0) = f.toPoly := by
  haveI : Subsingleton (ZMod (p ^ 0)) := by
    rw [pow_zero]
    infer_instance
  exact Polynomial.ext fun k => Subsingleton.elim _ _

/-- PREDICTION (2) — THE LEVEL-0 EDGE, witness-parametric form: two monic
    degree-n polynomials with distinct zf values kill every level-0 read (both
    lift f by `map_toZModPow_zero_eq_toPoly`, so a read σ would force
    zf g₁ = σ.1 = zf g₂).  The concrete witnesses (X^n vs Eisenstein X^n − p at
    the real zfType) are the E-group's instance duty — see header. -/
theorem zpReads_level0_empty {n p : ℕ} [Fact p.Prime]
    (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ))
    (g₁ g₂ : Polynomial ℤ_[p]) (h₁m : g₁.Monic) (h₁d : g₁.natDegree = n)
    (h₂m : g₂.Monic) (h₂d : g₂.natDegree = n) (hne : zf g₁ ≠ zf g₂)
    (f : Box p n 0) (σ : SplittingType n) :
    ¬ ZpReads n p zf 0 f σ := by
  intro hread
  exact hne ((hread g₁ h₁m h₁d (map_toZModPow_zero_eq_toPoly g₁ f)).trans
    (hread g₂ h₂m h₂d (map_toZModPow_zero_eq_toPoly g₂ f)).symm)

/-- PREDICTION (3), COMPILED — the single-lift uniqueness derivation IB-D9b
    consumes ((†8u), sound at ALL N by `zpReads_forall_lift`): ONE monic
    degree-n lift of f already forces agreement of any two σ's read at f. -/
theorem zpReads_unique_of_lift {n p : ℕ} [Fact p.Prime]
    (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)) (N : ℕ) (f : Box p n N)
    (g : Polynomial ℤ_[p]) (hm : g.Monic) (hd : g.natDegree = n)
    (hmap : g.map (PadicInt.toZModPow N) = f.toPoly)
    {σ σ' : SplittingType n}
    (h : ZpReads n p zf N f σ) (h' : ZpReads n p zf N f σ') : σ = σ' :=
  Subtype.ext ((h g hm hd hmap).symm.trans (h' g hm hd hmap))

end LeanUrat.MovesU
