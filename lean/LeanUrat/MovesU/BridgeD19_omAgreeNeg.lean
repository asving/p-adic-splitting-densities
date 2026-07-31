/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeD19_omAgree
import LeanUrat.OM.ClassifierBridgeChildful

/-!
# IB-D19-NEG — the STALL-STRATUM COUNTERMODEL to `decCovers_typeOf5_n2`
(movesu-pair probe 1, 2026-07-31; closes the BridgeD19 census row)

THE ROW (REMAINING_CENSUS_2026-08-01.md §1 MovesU): `BridgeD19_omAgree.lean:90
decCovers_typeOf5_n2` — the sorried n = 2 covering claim for the Wave-5 menu
decoder — flagged SUSPECT at the stall stratum (typeOf5 → typeOf4 → none).
Charge: prove OR compile the stall-stratum countermodel in a leaf.

OUTCOME: **REFUTED AS STATED, at EVERY prime.**  The witness is the stall point
`g = X²` at level `N = 1`: all lower coefficients vanish, so the box-native
valuation support is the SINGLE dot `(2, 0)` — the Newton polygon degenerates to
one vertex with no side (`rootSide = none`), the order-0 root residual is `0`
(`dr = 0`), and `classify` emits the single-tuple stall shape `[(0, 2, 0)]`.
The decoder chain then falls through exactly as the census record suspected:
* `typeOf5`: `headOrd = 0 ≠ 2` — not a chain head, defer to `typeOf4`;
* `typeOf4`: `headOrd = 0 ≠ 1` — not a multi-slope head, defer to `typeOfW`;
* `typeOfW`: the tree is neither the separable head `[(0, 2, 2)]` nor a
  self-loop head `[(0, 2, dr)]` with `0 < dr < 2` (here `headDr = 0`) → `none`.
So `DecCoversClassify 2 p (typeOf5 2)` FAILS at `(N, g) = (1, X²)` — the stall
stratum is genuinely OUTSIDE `typeOf5`'s covering range, and no decoder keyed
off the emitted shape can cover it (the level-1 box cannot decide `X²`'s type:
its lifts realize several factorization types).  The honest repair shape for
IB-F7's covering hypothesis is a DECIDED-LOCUS guard (covering off the stall
strata), not a proof of the row as typed.

M1 COEXISTENCE (recorded): this leaf imports `BridgeD19_omAgree` for the named
Prop `DecCoversClassify` only; the sorried universal `decCovers_typeOf5_n2` in
the import cone is exactly the statement refuted here.  Per the standing
countermodel-not-force discipline the upstream sorry STANDS byte-unchanged (its
disposition is a fence event for Asvin); nothing in this module consumes it,
and every theorem below is Lean-core (`#print axioms` at EOF).

DEPS (all sorry-free): `ClassifierBridgeChildful.classify_eq_shapeOf` (the
classifier collapses to `shapeOf (fRootCtx …)`),
`ClassifierBridgeChildful.factorize_factors_empty_of_natDegree_zero`,
`NewtonPolygon.npVertices_length_le`, the ChainMenu/MultiSlopeMenu compat
lemmas `typeOf5_typeOf4_compat` / `typeOf4_typeOfW_compat`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open LeanUrat.OM Polynomial

/-! ## §1 the stall point: `X²` at level 1 -/

/-- The stall-stratum witness: `g = X²` in the level-1 monic box (all lower
coefficients vanish — the level-1 undecided cluster point). -/
noncomputable def stallBox (p : ℕ) [Fact p.Prime] :
    OM.QuotientBox.monicBox p 1 2 :=
  ⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, by
    haveI : Fact (1 < p ^ 1) := ⟨by simpa using (Fact.out (p := p.Prime)).one_lt⟩
    haveI : Nontrivial (OM.QuotientBox.ResidueRing p 1) := ZMod.nontrivial _
    exact Polynomial.natDegree_X_pow 2⟩

/-- `X²`'s support is the single index `{2}` (lower coefficients all vanish). -/
theorem stallBox_support (p : ℕ) [Fact p.Prime] :
    (stallBox p).1.support = {2} := by
  haveI : Fact (1 < p ^ 1) := ⟨by simpa using (Fact.out (p := p.Prime)).one_lt⟩
  haveI : Nontrivial (OM.QuotientBox.ResidueRing p 1) := ZMod.nontrivial _
  show (Polynomial.X ^ 2 : (OM.QuotientBox.ResidueRing p 1)[X]).support = {2}
  rw [Polynomial.X_pow_eq_monomial, Polynomial.support_monomial _ one_ne_zero]

/-- The box-native valuation support of the stall point is a SINGLE dot. -/
theorem boxValSupport_stallBox_card (p : ℕ) [Fact p.Prime] :
    (OM.B.boxValSupport p 1 (stallBox p)).card = 1 := by
  unfold OM.B.boxValSupport
  rw [stallBox_support p, Finset.image_singleton, Finset.card_singleton]

/-! ## §2 the degenerate polygon: one dot, no side, zero residual -/

/-- A one-dot support has NO polygon sides (the vertex list has length `≤ 1`,
so the consecutive-pair zip is empty). -/
theorem npSides_of_card_le_one (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    (h1 : S.card ≤ 1) : OM.NewtonPolygon.npSides S hS = [] := by
  have hlen : (OM.NewtonPolygon.npVertices S hS).length ≤ 1 :=
    (OM.NewtonPolygon.npVertices_length_le S hS).trans h1
  unfold OM.NewtonPolygon.npSides
  rcases hv : OM.NewtonPolygon.npVertices S hS with _ | ⟨a, tl⟩
  · rfl
  · rw [hv] at hlen
    have htl : tl = [] := by
      rw [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst htl
    rfl

/-- The stall point selects NO order-0 side. -/
theorem rootSide_stallBox (p : ℕ) [Fact p.Prime] :
    OM.B.rootSide p 1 one_pos (stallBox p) = none := by
  unfold OM.B.rootSide
  rw [npSides_of_card_le_one _ _ (le_of_eq (boxValSupport_stallBox_card p))]
  rfl

/-- Hence the order-0 root residual is `0` (the no-side branch). -/
theorem rootResidual_stallBox (p : ℕ) [Fact p.Prime] :
    OM.B.rootResidual p 1 one_pos (stallBox p) = 0 := by
  unfold OM.B.rootResidual
  rw [rootSide_stallBox p]

/-- Any OM context with a degree-0 residual has NO cells (the general form of
`ClassifierBridgeChildful.cells_childCtxOfSize`, at a free context). -/
theorem cells_eq_nil_of_natDegree_zero (T : OM.M5.OMType)
    (h : T.Rr.natDegree = 0) : OM.M5.cells T = [] := by
  rw [OM.M5.cells]
  apply List.eq_nil_of_length_eq_zero
  rw [List.length_map, List.length_mergeSort]
  have hfac : (Classical.choice (OM.M4.factorize_any T.Rr)).factors = ∅ :=
    OM.ClassifierBridgeChildful.factorize_factors_empty_of_natDegree_zero h _
  rw [Finset.length_toList, Finset.card_attach, hfac, Finset.card_empty]

/-! ## §3 the emitted stall shape `[(0, 2, 0)]` -/

/-- **The classifier emits the stall shape**: `classify p 2 1 X²` has the
single-tuple tree `[(0, 2, 0)]` — order-0 head, full budget 2, residual
degree 0. -/
theorem classify_stallBox_tree (p : ℕ) [Fact p.Prime] :
    (OM.B.classify p 2 1 (stallBox p)).tree = [(0, 2, 0)] := by
  rw [OM.ClassifierBridgeChildful.classify_eq_shapeOf one_pos (stallBox p)]
  show OM.M5.encodeTree (OM.B.fRootCtx p 1 one_pos (stallBox p)) = [(0, 2, 0)]
  have hRr : (OM.B.fRootCtx p 1 one_pos (stallBox p)).Rr = 0 :=
    rootResidual_stallBox p
  rw [OM.M5.encodeTree,
    cells_eq_nil_of_natDegree_zero _ (by rw [hRr, Polynomial.natDegree_zero]),
    List.flatMap_nil]
  show [(0, 2, (OM.B.rootResidual p 1 one_pos (stallBox p)).natDegree)]
    = [(0, 2, 0)]
  rw [rootResidual_stallBox p, Polynomial.natDegree_zero]

/-! ## §4 the decoder falls through: typeOf5 → typeOf4 → typeOfW → none -/

/-- **The Wave-5 decoder returns `none` on the stall shape** — the census
record's suspected fall-through, compiled. -/
theorem typeOf5_stallBox (p : ℕ) [Fact p.Prime] :
    OM.ChainMenu.typeOf5 2 (OM.B.classify p 2 1 (stallBox p)) = none := by
  have ht := classify_stallBox_tree p
  have hho : OM.MultiSlopeMenu.headOrd (OM.B.classify p 2 1 (stallBox p)) = 0 := by
    rw [OM.MultiSlopeMenu.headOrd, ht]; rfl
  have hhd : OM.WildMenu.headDr (OM.B.classify p 2 1 (stallBox p)) = 0 := by
    rw [OM.WildMenu.headDr, ht]; rfl
  rw [OM.ChainMenu.typeOf5_typeOf4_compat (by rw [hho]; omega),
    OM.MultiSlopeMenu.typeOf4_typeOfW_compat (by rw [hho]; omega),
    OM.WildMenu.typeOfW]
  rw [if_neg (by rw [ht]; simp), if_neg (by rw [hhd]; simp)]

/-! ## §5 the refutation -/

/-- **THE COUNTERMODEL (probe outcome): the covering claim FAILS at every
prime** — `typeOf5 2` does not cover `classify`'s range at `(2, p)`: the stall
point `X²` at level 1 decodes to `none`. -/
theorem decCovers_typeOf5_n2_false (p : ℕ) [Fact p.Prime] :
    ¬ DecCoversClassify 2 p (OM.ChainMenu.typeOf5 2) := by
  intro h
  obtain ⟨σft, hσ⟩ := h 1 one_pos (stallBox p)
  rw [typeOf5_stallBox p] at hσ
  exact Option.some_ne_none σft hσ.symm

/-- The census row `decCovers_typeOf5_n2` (BridgeD19_omAgree.lean:88), refuted
AS TYPED: its ∀-statement is false (already at `p = 2`). -/
theorem decCovers_typeOf5_n2_refuted :
    ¬ ∀ (p : ℕ) [Fact p.Prime], DecCoversClassify 2 p (OM.ChainMenu.typeOf5 2) :=
  fun h => decCovers_typeOf5_n2_false 2 (@h 2 ⟨Nat.prime_two⟩)

-- Footprint gates: Lean-core only (no sorryAx — the upstream sorry is NOT consumed).
#print axioms typeOf5_stallBox
#print axioms decCovers_typeOf5_n2_false
#print axioms decCovers_typeOf5_n2_refuted

end LeanUrat.MovesU
