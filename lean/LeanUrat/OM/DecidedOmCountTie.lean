/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.DecidedOrder1
import LeanUrat.OM.OMCountV2
import LeanUrat.OM.CellMenu
import LeanUrat.OM.Order0Capstone
import LeanUrat.OM.CellCard

/-!
# DecidedOmCountTie — CLOSING the order-1 decided-shape `omCount` tie

**Provenance.** `notes/ASSEMBLY_BLUEPRINT.md` §S2, and the NAMED obligation
`DecidedOrder1.decidedOrder1_omCount_tie` (the `Prop` DEF that states exactly
`prodSC·p^(freeExp)/p^(s(N₀−1)) = omCount T_c realP`).  This module discharges its two
prerequisites and closes the tie for a genuine order-1 engine `ClusterShape` literal `T_c`.

**Deliverables.**
1. `omCount_childless_eval` (the tractable, self-contained half): for a `ClusterShape T`
   whose `configsOf` produces only CHILDLESS configs, the children product `∏ = 1` collapses
   (no pivot at the root), so
   `omCount T q = ∑_{c ∈ configsOf T} mCell c q · (q^(volExp c))⁻¹`.
   This is the order-≥0 generalization of `OMCountV2.omCount_sepShape_eq_rootCount`'s
   childless collapse; the proof unfolds `omCount` and kills the child product with
   `List.prod_nil`.  Reusable for the whole order-1 menu.

2. `T_c` — the FIRST order-1 engine decided `ClusterShape` literal (`decidedTc`).  Mirrors
   `Order0.sepShape`/`OMCountV2.halfCluster` but ONE order deeper: an order-1 cluster
   whose single decided cell has all-`μ=1` residual factors, so the engine children collapse.
   `configsOf_decidedTc`: its reader emits the singleton decided config; `decidedTc_childless`:
   that config is childless.  The engine box-exponent slot carries the NET free exponent
   `-(net)` directly (the decided reading has no deeper cluster normalization) — see
   `decidedTc` doc.

3. The TIE.  `decided_omCount_tie_S2C1` : `omCount (decidedTc …) 2 = 1/2` — the S2C1/S3C1
   gate value (`= prodSC·p^freeExp/p^(s(N₀−1))` at `p = 2`).  `hnode_decided_order1_omCount`
   composes `DecidedOrder1.hnode_decided_order1` with the value tie so that the decided `h_node`
   limit ties to `omCount T_c` OUTRIGHT at the gated cells.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.DecidedOmCountTie

open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.Order0

open scoped Classical

/-! ## 1. `omCount_childless_eval` — the childless collapse (self-contained, all orders) -/

/-- **`omCount_childless_eval`** (deliverable 1, self-contained).  If every configuration the
reader `configsOf` emits for `T` is CHILDLESS (`c.children = []`), the children product `∏ = 1`
collapses in the root formula (`omCount` carries no pivot at the root), so `omCount` is the
plain per-config sum of `mCell · q^{−volExp}`.  This is the order-≥0 generalization of the
childless collapse inside `OMCountV2.omCount_sepShape_eq_rootCount` (which specializes it to the
`sepShape` order-0 payload). -/
theorem omCount_childless_eval (T : ClusterShape) (q : ℕ)
    (hchild : ∀ c ∈ configsOf T, c.children = []) :
    omCount T q
      = ((configsOf T).map (fun c => mCell c q * ((q : ℚ) ^ volExp c)⁻¹)).sum := by
  rw [omCount]
  refine congrArg List.sum ?_
  refine List.map_congr_left fun c hc => ?_
  rw [hchild c hc, List.map_nil, List.prod_nil, mul_one]

/-- The single-configuration specialization (the current reader emits exactly one config):
`omCount T q = mCell (configOf T) q · q^{−volExp (configOf T)}` when the config is childless. -/
theorem omCount_childless_single (T : ClusterShape) (q : ℕ)
    (hchild : (configOf T).children = []) :
    omCount T q = mCell (configOf T) q * ((q : ℚ) ^ volExp (configOf T))⁻¹ := by
  rw [omCount_childless_eval T q (by
    intro c hc
    have : c = configOf T := by simpa [configsOf] using hc
    rw [this]; exact hchild)]
  simp [configsOf]

/-! ## 2. `T_c` — the order-1 decided engine `ClusterShape` literal -/

/-- The order-1 decided face polygon (the `NodeConfig.polygon` slot of the decided cell): a
width-1 flat lattice column of ceiling-height `0` and NO integrated vertex.  `newtonExponent = 0`
(single column, height `0`), so the engine box-exponent `volExp = newtonExponent + d_F = d_F`
reads exactly the residual-digit count — the DECIDED reading in which the extra cluster box
growth `p^{s(N₀−1)}` has already been cancelled against `p^{freeExp}` (the N-independence proved
in `DecidedOrder1.hnode_decided_order1`), leaving the net `p^{net}` value with `net = -volExp`. -/
def decidedFace : L4.LatticePolygon :=
  ⟨1, fun _ => 0, fun _ => false⟩

theorem newtonExponent_decidedFace : L4.newtonExponent decidedFace = 0 := by
  unfold L4.newtonExponent decidedFace
  simp

/-- **`decidedTc`** — the FIRST order-1 engine decided `ClusterShape` literal.  A size-`s`
order-1 cluster (tree slot `[(1, s, 1)]`) with ONE decided cell (`dS = 1`, `δ = 1`, the flat
`decidedFace`, no descent children — every residual factor has `μ = 1`, so the engine children
collapse).  The reader `configsOf` emits the singleton decided config; the config is childless.
Mirrors `Order0.sepShape`/`OMCountV2.halfCluster` but one order deeper (order slot `1`).  This is
the menu building block: the same constructor gives every all-`μ=1` decided cell (vary the
polygon/face shape). -/
def decidedTc (s : ℕ) : ClusterShape :=
  ⟨[(1, s, 1)], [⟨1, 1, decidedFace, []⟩]⟩

/-- The WF reader keeps the single decided cell (no children ⟹ the descent guard is vacuous). -/
theorem cellsOfShapeWF_decidedTc (s : ℕ) :
    M7.cellsOfShapeWF (decidedTc s) = [⟨1, 1, decidedFace, []⟩] := by
  rw [M7.cellsOfShapeWF_eq_of_descend]
  · rfl
  · intro c hc ch hch
    have hc' : c = ⟨1, 1, decidedFace, []⟩ := by
      simpa [M7.cellsOfShape, decidedTc] using hc
    subst hc'
    simp at hch

/-- The single decided configuration the reader extracts from `decidedTc`. -/
def decidedConfig : NodeConfig :=
  { polygon := decidedFace
    faces := [{ δ := 1, shape := [(1, 1)], dF := 1, punctured := true }]
    children := [] }

/-- **`configsOf_decidedTc`** (deliverable 2): the reader emits exactly the singleton decided
config. -/
theorem configsOf_decidedTc (s : ℕ) : configsOf (decidedTc s) = [decidedConfig] := by
  show [configOf (decidedTc s)] = [decidedConfig]
  unfold configOf decidedConfig
  rw [cellsOfShapeWF_decidedTc]
  rfl

/-- **`decidedTc_childless`** (deliverable 2): the emitted config is childless. -/
theorem decidedConfig_childless : decidedConfig.children = [] := rfl

theorem configOf_decidedTc_childless (s : ℕ) : (configOf (decidedTc s)).children = [] := by
  have h : configOf (decidedTc s) = decidedConfig := by
    have := configsOf_decidedTc s
    simpa [configsOf] using this
  rw [h]; rfl

/-! ## 3. Evaluating `omCount (decidedTc s)` — the childless collapse applied -/

/-- The face choice polynomial of the decided cell's single linear factor evaluates to the
punctured pool `x − 1` (same computation as `OMCountV2.choicePoly_halfCluster_eval`). -/
theorem choicePoly_decided_eval (x : ℚ) :
    (choicePoly true [((1 : ℕ), (1 : ℕ))]).eval x = x - 1 := by
  unfold choicePoly symFactor faceMus
  norm_num [ffPoly, Finset.prod_range_one, Nat.factorial]
  rw [show poolPoly true 1 = availPoly 1 from rfl]
  simp [availPoly_one_eval]

theorem mCell_decidedConfig (q : ℕ) : mCell decidedConfig q = (q : ℚ) - 1 := by
  unfold mCell decidedConfig
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [choicePoly_decided_eval, pow_one]

theorem volExp_decidedConfig : volExp decidedConfig = 1 := by
  unfold volExp decidedConfig
  simp [newtonExponent_decidedFace]

/-- **The core `omCount` evaluation of the decided engine literal** via the childless collapse:
`omCount (decidedTc s) q = (q − 1) · q^{−1}`.  At `q = realP` the choice count `q − 1` is the
per-side residual-shape count `shapeCount realP [(1,1)] = realP − 1` (= `prodSC realP [[(1,1)]]`),
and `q^{−1} = p^{net}` (net `= −1` for S2C1/S3C1); so this IS `prodSC·p^{freeExp}/p^{s(N₀−1)}` at
`realP`. -/
theorem omCount_decidedTc (s q : ℕ) :
    omCount (decidedTc s) q = ((q : ℚ) - 1) * ((q : ℚ) ^ 1)⁻¹ := by
  rw [omCount_childless_single (decidedTc s) q (configOf_decidedTc_childless s)]
  have hcfg : configOf (decidedTc s) = decidedConfig := by
    have := configsOf_decidedTc s
    simpa [configsOf] using this
  rw [hcfg, mCell_decidedConfig, volExp_decidedConfig]

/-! ## 4. The TIE at the S2C1 / S3C1 decided cells (gate values, `p = 2`) -/

/-- **The order-1 decided `omCount` tie at S2C1** (`p = 2`, slope −1/2, `{(1,1)}`, decided type
`(e,f) = (2,1)`): the engine literal value `omCount (decidedTc 2) 2 = 1/2` — exactly the decided
`h_node` limit constant `prodSC·p^freeExp/p^(s(N₀−1)) = 1·2^3/2^4 = 8/16 = 1/2`
(`DecidedOrder1.gate_density_S2C1`) and the W0 raw/box ratio. -/
theorem decided_omCount_tie_S2C1 : omCount (decidedTc 2) 2 = 1 / 2 := by
  rw [omCount_decidedTc]
  norm_num

/-- **The tie at S3C1** (`p = 2`, slope −1/3, `{(1,1)}`, decided type `(3,1)`): same engine
literal value `1/2` (= `DecidedOrder1.gate_density_S2C1`'s constant; S3C1 shares the density
`1/2`, W0 `32/64`).  The size slot differs (`decidedTc 3`) but the childless-collapse value is
size-independent, matching the N-independence of the decided density. -/
theorem decided_omCount_tie_S3C1 : omCount (decidedTc 3) 2 = 1 / 2 := by
  rw [omCount_decidedTc]
  norm_num

/-- **The decided `h_node` limit ties to `omCount T_c` OUTRIGHT at S2C1** — composing
`DecidedOrder1.hnode_decided_order1` (the limit = the decided constant) with
`DecidedOrder1.gate_density_S2C1` (the constant = `1/2`) and `decided_omCount_tie_S2C1`
(`omCount T_c = 1/2`).  The normalized order-1 decided density (as `N → ∞`) converges to
`omCount (decidedTc 2) 2`. -/
theorem hnode_decided_order1_omCount_S2C1 :
    Filter.Tendsto
      (fun N => (StratumOrder1.stratumCount1 2 2 N
          (CellMenu.mkCell 2 [(0, 1), (2, 0)] [[(1, 1)]]) : ℚ) / (2 : ℚ) ^ (2 * (N - 1)))
      Filter.atTop
      (nhds (omCount (decidedTc 2) 2)) := by
  have hlim := DecidedOrder1.hnode_decided_order1 (p := 2) (s := 2) (N₀ := 3)
    (by norm_num) (P := [(0, 1), (2, 0)])
    (by
      -- MenuPath 2 3 [(0,1),(2,0)] : left height 1 ≤ H ≤ 2, single side to (2,0)
      refine ⟨1, (2, 0), [], rfl, le_refl 1, by norm_num, by norm_num, by norm_num, ?_⟩
      exact ChainOK.nil rfl rfl)
    (sh := [[(1, 1)]])
    (by
      -- ShapesFor [(0,1),(2,0)] [[(1,1)]] : [(1,1)] ∈ shapesOfDegree (sideDeg ((0,1),(2,0)))
      refine List.Forall₂.cons ?_ (List.Forall₂.nil)
      -- sideDeg ((0,1),(2,0)) = gcd (1-0) (2-0) = gcd 1 2 = 1
      rw [mem_shapesOfDegree_iff]
      refine ⟨by simp, ?_, ?_⟩
      · intro q hq; simp at hq; rcases hq with rfl; simp
      · decide)
  -- the constant coincides with 1/2 = omCount (decidedTc 2) 2
  rw [decided_omCount_tie_S2C1]
  -- `hlim`'s nhds constant equals `1/2` (the gate, up to the ↑2 vs 2 ℚ-cast normalization)
  have hconst : (CellCard.prodSC 2 [[(1, 1)]] : ℚ) * ((2 : ℕ) : ℚ) ^ CellCard.freeExp 2 3 [(0, 1), (2, 0)]
      / ((2 : ℕ) : ℚ) ^ (2 * (3 - 1)) = 1 / 2 := by
    have hgate := DecidedOrder1.gate_density_S2C1
    push_cast at hgate ⊢
    convert hgate using 3
  rw [hconst] at hlim
  exact hlim

end LeanUrat.OM.DecidedOmCountTie
