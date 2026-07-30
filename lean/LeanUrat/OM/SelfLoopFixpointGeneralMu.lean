/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.SelfLoopFixpoint
import LeanUrat.OM.SelfLoopResum
import LeanUrat.OM.OMCountV2

/-!
# SelfLoopFixpointGeneralMu — the general-`μ` self-loop fixpoint, `μ = 3` discharged

**Scope.**  `SelfLoopFixpoint` banks the ENGINE self-loop fixpoint `b = EFFSEED + r·b` and its
closure `b = EFFSEED·(countPivot s q)⁻¹`, general in `(depth0, s, q)`, and ties the `μ = 2` instance
to `omChildCount halfCluster 2 = 2/3`.  This module extends that to the GENERAL-`μ` structure and
DISCHARGES `μ = 3` (self-loop density `20/31` at `p = q = 2`).

**The general-`μ` structure (coupled-diagonal system).**  Across `μ` the recursion is
LOWER-TRIANGULAR-IN-`μ`: the size-`μ` self-loop cluster's seed `EFFSEED_μ` is ASSEMBLED from the
already-computed `β_{μ' < μ}` through the descent-child product
(`OMCountV2.omChildCount ch.shape (q^{δ·D})`, `OMCountV2.lean:267`), and the DIAGONAL block is the
scalar self-loop fixpoint `b_μ = EFFSEED_μ + slExposedRatio μ q · b_μ`, whose unique solution is
`EFFSEED_μ · (countPivot μ q)⁻¹` (`SelfLoopFixpoint.selfLoopFixpoint_unique`).  So the whole system
is a coupled-diagonal recursion with SCALAR-FIXPOINT diagonal blocks cross-fed by the child descent.

**`μ = 3` (the discharged instance, gated exact at `p = q = 2`).**  The size-3 self-loop cluster's
seed is `EFFSEED_3 = (q−1)(q²+1)/q³ = 5/8` (the `OMCountV2.configOf`-produced SHALLOW_3 const term,
cross-fed by the `β_2 = ((1,1),(2,1))` descent child; harness `phaseb_r0` C2, `results.txt`).  The
self-loop exposed ratio is `slExposedRatio 3 q = q^{−(3·4/2−1)} = q^{−5} = 1/32`, so
`countPivot 3 2 = 1 − 1/32 = 31/32` and the fixpoint closes to

    b_3 = EFFSEED_3 · (countPivot 3 2)⁻¹ = (5/8)·(32/31) = 20/31

(vs the naive pure-scalar seed `(q−1)/q` with `q^{−3}`, which gives `16/31` — REJECTED by Agent 1's
800k-sample MC at `z = +241`; `20/31` matches at `z = −0.01`).

**The genuine engine tie (cross-fed `omChildCount` at size 3).**  `shape3Half` is a size-3 cluster
whose single `configOf` config carries a NON-EMPTY descent child that is `halfCluster` itself (the
`β_2` self-loop cluster, `omChildCount halfCluster 2 = 2/3` = `gate3_cluster_q2`).  We evaluate
`omChildCount shape3Half 2` GENUINELY through the well-founded recursion — the child step discharges
to `gate3_cluster_q2` and the size-3 pivot is `countPivot 3 2 = 31/32` — landing the cross-fed value
`32/93` on the ACTUAL engine (numerator `(q−1)/q · β_2 = 1/3`).  This exercises exactly the
coupled-diagonal cross-feed the general-`μ` structure targets: the `μ = 3` diagonal solve consuming
the `μ = 2` value `β_2` through the recursive child `omChildCount ch.shape` call.

**Honesty.**  What is LANDED here: (1) the `μ = 3` fixpoint ALGEBRA + arithmetic (`20/31`), via the
banked `selfLoopFixpoint_unique`/`_eq` with `depth0 = EFFSEED_3`; (2) the general-`μ` closure
statement for arbitrary `(depth0, μ)`; (3) a GENUINE cross-fed size-3 `omChildCount` reaching the
recursion + `countPivot 3` + the recursive `halfCluster` child (`gate3_cluster_q2`).

What is NOT landed (the honest obstacle, inherited from `SelfLoopResum.REMAINING_OBLIGATION` item 2):
the `configOf` reader emits exactly ONE config per shape, but the engine `EFFSEED_3 = 5/8` is a
TWO-config sum `(q−1)/q + (q−1)/q³` (the SHALLOW strict term PLUS the cross-fed descent term).  So
the `depth0 = 5/8` fed to the fixpoint is the gated ENGINE seed (harness/PARI/MC), NOT reconstructed
through the current one-config reader; the genuine one-config `omChildCount shape3Half 2 = 32/93`
carries the cross-feed but at a different (single-config) seed.  A fully general-`μ` UNCONDITIONAL
theorem also needs the uniform-in-`(N,k)` per-depth census induction for `k ≥ 2`, which the numerics
confirm but which is unproven.  No `sorry`/`axiom`/`native_decide`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.SelfLoopFixpointGeneralMu

open scoped BigOperators
open Filter Topology
open LeanUrat LeanUrat.OM
open LeanUrat.OM.SelfLoopResum
open LeanUrat.OM.SelfLoopFixpoint
open LeanUrat.OM.Order0

/-! ## 1. The `μ = 3` self-loop arithmetic (gated exact at `p = q = 2`) -/

/-- **`slExposedRatio 3 2 = 1/32`.**  `selfLoopExponent 3 = 3·4/2 − 1 = 5`, so the size-3 self-loop
exposed ratio is `q^{−5} = 1/32`.  This is the `μ = 3` analogue of `slRatios_q2` (`slExposedRatio 2 2
= 1/4`); the geometric ratio of the size-3 self-loop tower. -/
theorem slExposedRatio_3_q2 : slExposedRatio 3 2 = 1 / 32 := by
  unfold slExposedRatio L5fix.selfLoopExponent
  norm_num

/-- **`countPivot 3 2 = 31/32`.**  `1 − slExposedRatio 3 2 = 1 − 1/32 = 31/32`; the size-3 pivot
denominator.  (`countPivot_eq_one_sub_slExposedRatio` gives `countPivot 3 q = 1 − slExposedRatio 3 q`
in general.) -/
theorem countPivot_3_q2 : MontesAxiom.countPivot 3 2 = 31 / 32 := by
  unfold MontesAxiom.countPivot L5fix.selfLoopExponent
  norm_num

/-! ## 2. The `μ = 3` engine seed `EFFSEED_3` (the SHALLOW_3 const term) -/

/-- **The `μ = 3` self-loop seed `EFFSEED_3 = (q−1)(q²+1)/q³`.**  The `OMCountV2.configOf`-produced
SHALLOW_3 const term of the size-3 self-loop cluster: the depth-0 shallow strict-polygon term
`(q−1)/q` PLUS the cross-fed `((1,1),(2,1)) = (q−1)/q³` `β_2` descent term
(`(q−1)/q + (q−1)/q³ = (q−1)(q²+1)/q³`).  This is the coupled-diagonal cross-feed: the `μ = 3` seed
assembled from the `μ = 2` `β`-descent.  Harness `phaseb_r0` C2 / PARI oracle gated. -/
noncomputable def EFFSEED3 (q : ℚ) : ℚ := (q - 1) * (q ^ 2 + 1) / q ^ 3

/-- **`EFFSEED_3` gate at `q = 2`: `= 5/8`.**  `(2−1)(4+1)/8 = 5/8`.  This is the MC-backed seed
(Agent 1's 800k-sample conditional MC `0.645156` vs `20/31 = 0.645161`, `z = −0.01`; the naive scalar
seed `16/31` REJECTED at `z = +241`). -/
theorem EFFSEED3_q2 : EFFSEED3 2 = 5 / 8 := by
  unfold EFFSEED3; norm_num

/-- **`EFFSEED_3` decomposes as the two-config cross-feed sum** `(q−1)/q + (q−1)/q³` (shallow strict
term + `β_2` descent term).  Records precisely why the single-config `configOf` reader cannot emit
`EFFSEED_3` on its own (the honest one-config obstacle). -/
theorem EFFSEED3_decomp (q : ℚ) (hq : q ≠ 0) :
    EFFSEED3 q = (q - 1) / q + (q - 1) / q ^ 3 := by
  unfold EFFSEED3
  field_simp

/-! ## 3. The `μ = 3` self-loop fixpoint value `b_3 = 20/31` -/

/-- **THE `μ = 3` SELF-LOOP FIXPOINT VALUE = `20/31`** (`p = q = 2`).  The banked closed value
`selfLoopFixpointValue EFFSEED_3 3 2 = EFFSEED_3 · (countPivot 3 2)⁻¹ = (5/8)·(32/31) = 20/31`.  This
is the settled, MC-backed size-3 self-loop density. -/
theorem selfLoopFixpointValue_mu3_q2 :
    selfLoopFixpointValue (EFFSEED3 2) 3 2 = 20 / 31 := by
  unfold selfLoopFixpointValue
  rw [EFFSEED3_q2, countPivot_3_q2]
  norm_num

/-- **THE `μ = 3` FIXPOINT EQUATION (†), landed.**  `b_3 = EFFSEED_3 + slExposedRatio 3 2 · b_3`,
i.e. `20/31 = 5/8 + (1/32)·(20/31)`.  Direct instance of the banked `selfLoopFixpoint_eq` at
`s = 3, q = 2, depth0 = EFFSEED_3`. -/
theorem selfLoopFixpoint_eq_mu3 :
    selfLoopFixpointValue (EFFSEED3 2) 3 2
      = EFFSEED3 2 + slExposedRatio 3 2 * selfLoopFixpointValue (EFFSEED3 2) 3 2 :=
  selfLoopFixpoint_eq (by norm_num) (by norm_num) (EFFSEED3 2)

/-- **The `μ = 3` fixpoint equation, fully concrete numerals.**  `20/31 = 5/8 + (1/32)·(20/31)`. -/
theorem selfLoopFixpoint_eq_mu3_value :
    (20 : ℚ) / 31 = 5 / 8 + (1 / 32) * (20 / 31) := by norm_num

/-- **UNIQUENESS of the `μ = 3` fixpoint.**  Any `b` solving `b = EFFSEED_3 + slExposedRatio 3 2 · b`
equals `20/31`.  Direct instance of the banked `selfLoopFixpoint_unique`. -/
theorem selfLoopFixpoint_unique_mu3 (b : ℚ)
    (hb : b = EFFSEED3 2 + slExposedRatio 3 2 * b) :
    b = 20 / 31 := by
  have h := selfLoopFixpoint_unique (s := 3) (q := 2) (by norm_num) (by norm_num) (EFFSEED3 2) b hb
  rwa [selfLoopFixpointValue_mu3_q2] at h

/-! ## 4. The general-`μ` self-loop fixpoint closure (coupled-diagonal diagonal block)

The DIAGONAL block of the coupled-diagonal system: for ANY `μ ≥ 2` and ANY seed `depth0` (the
`EFFSEED_μ` assembled from the `β_{μ' < μ}` cross-feed), the self-loop fixpoint
`b_μ = depth0 + slExposedRatio μ q · b_μ` closes UNIQUELY to `depth0 · (countPivot μ q)⁻¹`.  This is
the general-`μ` structure banked over arbitrary `(depth0, μ, q)`; `μ = 2` (`2/3`) and `μ = 3`
(`20/31`) are the two gated instances. -/

/-- **THE GENERAL-`μ` DIAGONAL FIXPOINT (closure).**  For every `μ ≥ 2`, `q ≥ 2`, and every seed
`depth0`, the size-`μ` self-loop fixpoint value `selfLoopFixpointValue depth0 μ q` is the UNIQUE
solution of `b = depth0 + slExposedRatio μ q · b`.  Packages `selfLoopFixpoint_eq` +
`selfLoopFixpoint_unique`: existence AND uniqueness of the diagonal block, general in `μ`. -/
theorem selfLoopFixpoint_general_closure {μ q : ℕ} (hq : 2 ≤ q) (hμ : 2 ≤ μ) (depth0 : ℚ) :
    selfLoopFixpointValue depth0 μ q
        = depth0 + slExposedRatio μ q * selfLoopFixpointValue depth0 μ q
      ∧ ∀ b : ℚ, b = depth0 + slExposedRatio μ q * b →
          b = selfLoopFixpointValue depth0 μ q :=
  ⟨selfLoopFixpoint_eq hq hμ depth0, selfLoopFixpoint_unique hq hμ depth0⟩

/-- **The general-`μ` closed form** `b_μ = EFFSEED_μ · (countPivot μ q)⁻¹`.  The definitional content
of the diagonal block: the self-loop density is the seed times the inverse pivot (the geometric
`(1 − slExposedRatio)⁻¹` resummation).  For any seed and any `μ`. -/
theorem selfLoopFixpoint_general_value (depth0 : ℚ) (μ q : ℕ) :
    selfLoopFixpointValue depth0 μ q = depth0 * (MontesAxiom.countPivot μ q)⁻¹ := rfl

/-! ## 5. The GENUINE cross-fed engine tie: a size-3 `omChildCount` with a `halfCluster` child

`shape3Half` is a size-3 cluster (tree slot `[(1, 3, 1)]`) whose single WF cell carries a NON-EMPTY
descent child that is `OMCountV2.halfCluster` itself — the `β_2` size-2 self-loop cluster with
`omChildCount halfCluster 2 = 2/3` (`gate3_cluster_q2`).  Evaluating `omChildCount shape3Half 2`
through the well-founded recursion discharges the child step to `gate3_cluster_q2` and applies the
size-3 pivot `countPivot 3 2 = 31/32`.  This is the coupled-diagonal cross-feed in the ACTUAL engine:
the `μ = 3` solve consuming the `μ = 2` value `β_2` via the recursive `omChildCount ch.shape` call. -/

/-- **The cross-fed size-3 cluster shape.**  Tree slot `[(1, 3, 1)]` (order 1, size 3); ONE
`ShapeCell` with `dS = 1`, `δ = 1`, the slope-`−1/2` face `halfFace`, and a NON-EMPTY child list
`[halfCluster]` — the `β_2` descent.  The child `halfCluster` has `nodeSizeOf = 2 < 3`, so the WF
descent guard keeps the cell. -/
def shape3Half : ClusterShape :=
  ⟨[(1, 3, 1)], [⟨1, 1, OMCountV2.halfFace, [OMCountV2.halfCluster]⟩]⟩

theorem treeSize_shape3Half : M6.treeSize shape3Half = 3 := rfl

/-- The WF cell list of `shape3Half`: the single cell survives (its `halfCluster` child descends
`nodeSizeOf halfCluster = 2 < 3 = nodeSizeOf shape3Half`). -/
theorem cellsOfShapeWF_shape3Half :
    M7.cellsOfShapeWF shape3Half
      = [⟨1, 1, OMCountV2.halfFace, [OMCountV2.halfCluster]⟩] := by
  rw [M7.cellsOfShapeWF_eq_of_descend]
  · rfl
  · intro c hc ch hch
    have hc' : c = ⟨1, 1, OMCountV2.halfFace, [OMCountV2.halfCluster]⟩ := by
      simpa [M7.cellsOfShape, shape3Half] using hc
    subst hc'
    have hch' : ch = OMCountV2.halfCluster := by simpa using hch
    subst hch'
    -- nodeSizeOf halfCluster = 2 < 3 = nodeSizeOf shape3Half.
    show M5.nodeSizeOf OMCountV2.halfCluster < M5.nodeSizeOf shape3Half
    have h1 : M5.nodeSizeOf OMCountV2.halfCluster = 2 := rfl
    have h2 : M5.nodeSizeOf shape3Half = 3 := rfl
    rw [h1, h2]; norm_num

/-- The single configuration `configOf` extracts from `shape3Half`: polygon `halfFace`, one
punctured face carrying the read-back shape `(dS, cellMult) = (1, 2)` (`cellMult = nodeSizeOf
halfCluster / dS = 2/1 = 2`) with `dF = cellResDeg = 2`, and one `ChildData ⟨halfCluster, 1, 1⟩`. -/
def config3Half : OMCountV2.NodeConfig :=
  { polygon := OMCountV2.halfFace
    faces := [{ δ := 1, shape := [(1, 2)], dF := 2, punctured := true }]
    children := [⟨OMCountV2.halfCluster, 1, 1⟩] }

theorem configsOf_shape3Half : OMCountV2.configsOf shape3Half = [config3Half] := by
  show [OMCountV2.configOf shape3Half] = [config3Half]
  unfold OMCountV2.configOf config3Half
  rw [cellsOfShapeWF_shape3Half]
  -- cellMult / cellResDeg of the single childful cell.
  have hmult : OMCountV2.cellMult (⟨1, 1, OMCountV2.halfFace, [OMCountV2.halfCluster]⟩ :
      MontesAxiom.CountCell) = 2 := by
    unfold OMCountV2.cellMult
    -- children = [halfCluster], nonempty; (Σ nodeSizeOf)/dS = 2/1 = 2.
    norm_num [M5.nodeSizeOf, OMCountV2.halfCluster]
  have hres : OMCountV2.cellResDeg (⟨1, 1, OMCountV2.halfFace, [OMCountV2.halfCluster]⟩ :
      MontesAxiom.CountCell) = 2 := by
    unfold OMCountV2.cellResDeg
    norm_num [M5.nodeSizeOf, OMCountV2.halfCluster]
  simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, hmult, hres]
  rfl

/-- The choice polynomial of the cross-fed face shape `[(1, 2)]` (ONE degree-1 factor of
multiplicity 2) is the punctured linear pool `x − 1`: `ff(availPoly 1, count = 1)/sym = availPoly 1`,
and the per-`μ` symmetry factor is `1` (a single factor).  Mirrors `choicePoly_halfCluster_eval`
(shape `[(1,1)]`), with the μ-slot `2` (not `1`) — the point of the childful read-back. -/
theorem choicePoly_config3Half_eval (x : ℚ) :
    (OMCountV2.choicePoly true [((1 : ℕ), (2 : ℕ))]).eval x = x - 1 := by
  unfold OMCountV2.choicePoly OMCountV2.symFactor OMCountV2.faceMus
  norm_num [ffPoly, Finset.prod_range_one, Nat.factorial]
  rw [show OMCountV2.poolPoly true 1 = availPoly 1 from rfl]
  simp [OMCountV2.availPoly_one_eval]

/-- `mCell` of the cross-fed config: the single punctured face has shape `[(1, 2)]`, so the choice
polynomial evaluated at `q^1 = q` is `q − 1`. -/
theorem mCell_config3Half (q : ℕ) : OMCountV2.mCell config3Half q = (q : ℚ) - 1 := by
  unfold OMCountV2.mCell config3Half
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [choicePoly_config3Half_eval, pow_one]

/-- `volExp` of the cross-fed config: `newtonExponent halfFace + dF = 2 + 2 = 4`. -/
theorem volExp_config3Half : OMCountV2.volExp config3Half = 4 := by
  unfold OMCountV2.volExp config3Half
  simp [OMCountV2.newtonExponent_halfFace]

/-- **THE GENUINE CROSS-FED SIZE-3 ENGINE VALUE.**  `omChildCount shape3Half 2 = 32/93`, computed
through the well-founded recursion: the single config contributes
`mCell · q^{−(volExp−3)} · (child product)`, the child product is the recursive
`omChildCount halfCluster (2^{δ·D}) = omChildCount halfCluster 2 = 2/3` (`gate3_cluster_q2` — the
`β_2` value cross-fed into the `μ = 3` node), and the whole is divided by the size-3 pivot
`countPivot 3 2 = 31/32`.  Numerator `(q−1)/q · β_2 = (1/2)·(2/3) = 1/3`; value
`(1/3)/(31/32) = 32/93`.  This is the coupled-diagonal cross-feed on the ACTUAL engine: the
recursive `omChildCount ch.shape` call drawing on `β_{μ' < μ}`. -/
theorem omChildCount_shape3Half_q2 :
    OMCountV2.omChildCount shape3Half 2 = 32 / 93 := by
  rw [OMCountV2.omChildCount_rec, configsOf_shape3Half]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    treeSize_shape3Half, mCell_config3Half, volExp_config3Half,
    show config3Half.children = [⟨OMCountV2.halfCluster, 1, 1⟩] from rfl,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  -- the recursive child: omChildCount halfCluster (2^(1*1)) = omChildCount halfCluster 2 = 2/3.
  rw [show (2 : ℕ) ^ ((1 : ℕ) * (1 : ℕ)) = 2 from rfl, OMCountV2.gate3_cluster_q2]
  -- the size-3 pivot.
  rw [countPivot_3_q2]
  norm_num

/-- **The cross-fed engine value ties the recursion to `gate3_cluster_q2`.**  Restates
`omChildCount_shape3Half_q2` exhibiting the `β_2 = 2/3` child value explicitly: the size-3 self-loop
`omChildCount` equals `((2−1)/2 · omChildCount halfCluster 2) / countPivot 3 2`, the coupled-diagonal
cross-feed identity. -/
theorem omChildCount_shape3Half_crossfeed :
    OMCountV2.omChildCount shape3Half 2
      = (((2 : ℚ) - 1) / 2 * OMCountV2.omChildCount OMCountV2.halfCluster 2)
        / MontesAxiom.countPivot 3 2 := by
  rw [omChildCount_shape3Half_q2, OMCountV2.gate3_cluster_q2, countPivot_3_q2]
  norm_num

#print axioms slExposedRatio_3_q2
#print axioms countPivot_3_q2
#print axioms EFFSEED3_q2
#print axioms EFFSEED3_decomp
#print axioms selfLoopFixpointValue_mu3_q2
#print axioms selfLoopFixpoint_eq_mu3
#print axioms selfLoopFixpoint_unique_mu3
#print axioms selfLoopFixpoint_general_closure
#print axioms selfLoopFixpoint_general_value
#print axioms omChildCount_shape3Half_q2
#print axioms omChildCount_shape3Half_crossfeed

end LeanUrat.OM.SelfLoopFixpointGeneralMu
