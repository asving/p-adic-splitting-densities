/-
Scratch module: CHILDFUL S3 constructor extension — the single-side path shape
carrying genuine μ ≥ 2 descent children.  Namespace LeanUrat.OM.PathShapeChildful.
Math-first, no sorry/axiom/native_decide.

This module extends PathShape.oneSideShape to inject non-empty ShapeCell.children
(one childShape (μ·D) per μ ≥ 2 factor with μ·D < s), exercising the NON-VACUOUS
WF-descent guard, the cellMult = μ face read, and the pivot self-loop factors.
-/
import Mathlib
import LeanUrat.OM.CellMenu
import LeanUrat.OM.OMCountV2
import LeanUrat.OM.CellPartition
import LeanUrat.Interface
import LeanUrat.OM.DecidedOmCountTie
import LeanUrat.OM.ShapeCountTie
import LeanUrat.OM.DecidedOrder1
import LeanUrat.OM.StratumOrder1
import LeanUrat.OM.PathShape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.PathShapeChildful

open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.DecidedOrder1
open LeanUrat.OM.PathShape
open LeanUrat.MontesAxiom (CountCell)

open scoped Classical

/-! ## 0. The childShape-collapse lemma (empty-payload child, KEEPING the pivot) -/

/-- **`omChildCount` on a `childShape`.**  `childShape sz = ⟨[(2, sz, 0)], []⟩` has an EMPTY
payload (`cells = []`), so its WF cell list is empty (the descent guard is vacuous, as in
`gate7_junk_value`).  The single configuration then has an empty face-shape (mCell `= 1`),
`volExp = 0`, and no descent children.  With `treeSize (childShape sz) = sz`, the cluster count
collapses to the bare pivot factor `1 / countPivot sz`.  This is the self-loop mass the finite
stratum density does NOT capture — the source of the pivot mismatch. -/
theorem omChildCount_childShape' (sz : ℕ) (q : ℕ) :
    OMCountV2.omChildCount (childShape sz) q = 1 / MontesAxiom.countPivot sz q := by
  -- WF cell list of the empty-payload child shape is empty.
  have hcs : M7.cellsOfShapeWF (childShape sz) = [] := by
    rw [M7.cellsOfShapeWF_eq_of_descend]
    · rfl
    · intro c hc
      simp [M7.cellsOfShape, childShape] at hc
  rw [omChildCount_rec]
  simp only [configsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hchild : (configOf (childShape sz)).children = [] := by
    unfold configOf
    rw [hcs]
    rfl
  have hm : mCell (configOf (childShape sz)) q = 1 := by
    unfold mCell configOf
    rw [hcs]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    unfold choicePoly
    simp
  have hv : volExp (configOf (childShape sz)) = 0 := by
    unfold volExp configOf
    rw [hcs]
    rfl
  have htree : M6.treeSize (childShape sz) = sz := rfl
  rw [hchild, hm, hv, htree]
  simp

#print axioms omChildCount_childShape'

/-- **`omChildCount` on a `childShape`** (the target statement, at a prime `p`).  Immediate from the
unconditional `omChildCount_childShape'`. -/
theorem omChildCount_childShape (sz : ℕ) (p : ℕ) [Fact p.Prime] :
    OMCountV2.omChildCount (childShape sz) p = 1 / MontesAxiom.countPivot sz p := by
  exact omChildCount_childShape' sz p

#print axioms omChildCount_childShape

/-! ## 1. The childful single-side path cluster shape -/

/-- **The childful single-side path cluster shape.**  A size-`s` order-1 cluster
(tree slot `[(1, s, 1)]`) carrying ONE `ShapeCell` PER FACTOR of `shape`: each `(D, μ)` part `q`
becomes a cell with `dS = q.1`, `δ = 1`, the shared side polygon `mkPoly s [pr.1, pr.2]`, and —
UNLIKE `oneSideShape` — a NON-EMPTY child list `[childShape (μ·D)]` exactly when `2 ≤ μ` and
`μ·D < s` (the descent-emission guard).  For an all-`μ=1` shape this reduces to `oneSideShape`. -/
def oneSideShapeChildful (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) : ClusterShape :=
  ⟨[(1, s, 1)],
    shape.map (fun q =>
      ⟨q.1, 1, mkPoly s [pr.1, pr.2],
        (if 2 ≤ q.2 ∧ q.2 * q.1 < s then [childShape (q.2 * q.1)] else [])⟩)⟩

/-- **Obligation 1 (NON-VACUOUS WF guard).**  The WF reader keeps every per-factor cell.  Unlike
`oneSideShape`, the descent premise is now genuine: an emitted child `childShape (μ·D)` must have
`M5.nodeSizeOf (childShape (μ·D)) = μ·D < s = M5.nodeSizeOf T`.  The size-`s` head slot of the
cluster tree `[(1, s, 1)]` gives `nodeSizeOf T = s`; `childShape (μ·D)`'s head slot `[(2, μ·D, 0)]`
gives `nodeSizeOf = μ·D`; the emission guard `μ·D < s` discharges the descent. -/
theorem cellsOfShapeWF_oneSideShapeChildful (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (shape : List (ℕ × ℕ)) (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) :
    M7.cellsOfShapeWF (oneSideShapeChildful s pr shape)
      = shape.map (fun q =>
          ({ dS := q.1, δ := 1, polygon := mkPoly s [pr.1, pr.2],
             children := (if 2 ≤ q.2 ∧ q.2 * q.1 < s then [childShape (q.2 * q.1)] else []) }
             : CountCell)) := by
  rw [M7.cellsOfShapeWF_eq_of_descend]
  · -- identity part: `cellsOfShape` erases the payload field-for-field.
    rw [M7.cellsOfShape, oneSideShapeChildful, List.map_map]
    rfl
  · -- descent premise: every emitted child strictly descends.
    intro c hc ch hch
    rw [M7.cellsOfShape, oneSideShapeChildful, List.map_map, List.mem_map] at hc
    obtain ⟨q, hq, rfl⟩ := hc
    -- nodeSizeOf T = s (head slot of the cluster tree).
    have hT : M5.nodeSizeOf (oneSideShapeChildful s pr shape) = s := rfl
    rw [hT]
    -- reduce the erasure composition on the children field.
    simp only [Function.comp_apply] at hch
    -- the child membership forces the guard true and ch = childShape (μ·D).
    by_cases hg : 2 ≤ q.2 ∧ q.2 * q.1 < s
    · rw [if_pos hg] at hch
      rw [List.mem_singleton] at hch
      subst hch
      -- nodeSizeOf (childShape (μ·D)) = μ·D (head slot of [(2, μ·D, 0)]).
      have hchsz : M5.nodeSizeOf (childShape (q.2 * q.1)) = q.2 * q.1 := rfl
      rw [hchsz]
      exact hg.2
    · rw [if_neg hg] at hch
      exact absurd hch List.not_mem_nil

#print axioms cellsOfShapeWF_oneSideShapeChildful

/-! ## 2. Helper reads on the childful WF cell list -/

/-- The per-factor childful `CountCell` (WF-list element) for one shape part `q`. -/
private def childCell (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (q : ℕ × ℕ) : CountCell :=
  { dS := q.1, δ := 1, polygon := mkPoly s [pr.1, pr.2],
    children := (if 2 ≤ q.2 ∧ q.2 * q.1 < s then [childShape (q.2 * q.1)] else []) }

/-- Under `hlt` (every μ ≥ 2 factor emits a child), the descent guard `2 ≤ q.2 ∧ q.2·q.1 < s`
holds iff `2 ≤ q.2`. -/
private theorem guard_iff (s : ℕ) (shape : List (ℕ × ℕ))
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) {q : ℕ × ℕ} (hq : q ∈ shape) :
    (2 ≤ q.2 ∧ q.2 * q.1 < s) ↔ 2 ≤ q.2 :=
  ⟨fun h => h.1, fun h => ⟨h, hlt q hq h⟩⟩

/-- **`cellMult` of every per-factor childful cell is the genuine `μ = q.2`** (positive degree),
using `cellMult = (Σ child sizes)/dS = μ·D/D = μ` on the emitted child, and `= 1 = μ` when `μ = 1`
(no child).  Requires `1 ≤ q.1` (so `D > 0` for the `μ·D/D = μ` division) and `hlt`. -/
private theorem cellMult_childful (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) {q : ℕ × ℕ} (hq : q ∈ shape) (hpos : 1 ≤ q.1)
    (hmpos : 1 ≤ q.2) :
    cellMult (childCell s pr q) = q.2 := by
  by_cases hμ : 2 ≤ q.2
  · have hch : (childCell s pr q).children = [childShape (q.2 * q.1)] := by
      show (if 2 ≤ q.2 ∧ q.2 * q.1 < s then [childShape (q.2 * q.1)] else []) = _
      rw [if_pos ((guard_iff s shape hlt hq).mpr hμ)]
    have hdS : (childCell s pr q).dS = q.1 := rfl
    unfold cellMult
    rw [hch, hdS]
    -- children = [childShape (μ·D)], nonempty; sum of nodeSizeOf = μ·D; /dS = μ·D/D = μ.
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    have hchsz : M5.nodeSizeOf (childShape (q.2 * q.1)) = q.2 * q.1 := rfl
    rw [hchsz]
    exact Nat.mul_div_cancel _ hpos
  · -- μ = 1 (positive but < 2): no child, cellMult = 1 = μ.
    have hch : (childCell s pr q).children = [] := by
      show (if 2 ≤ q.2 ∧ q.2 * q.1 < s then [childShape (q.2 * q.1)] else []) = _
      rw [if_neg (fun h => hμ h.1)]
    unfold cellMult
    rw [hch]
    simp only [List.isEmpty_nil, if_true]
    omega

/-- **`cellResDeg` of every per-factor childful cell is `μ·D = q.2·q.1`.** -/
private theorem cellResDeg_childful (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) {q : ℕ × ℕ} (hq : q ∈ shape) (hmpos : 1 ≤ q.2) :
    cellResDeg (childCell s pr q) = q.2 * q.1 := by
  by_cases hμ : 2 ≤ q.2
  · have hch : (childCell s pr q).children = [childShape (q.2 * q.1)] := by
      show (if 2 ≤ q.2 ∧ q.2 * q.1 < s then [childShape (q.2 * q.1)] else []) = _
      rw [if_pos ((guard_iff s shape hlt hq).mpr hμ)]
    unfold cellResDeg
    rw [hch]
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rfl
  · -- μ = 1: no child, cellResDeg = dS = q.1 = 1·q.1 = μ·q.1.
    have hch : (childCell s pr q).children = [] := by
      show (if 2 ≤ q.2 ∧ q.2 * q.1 < s then [childShape (q.2 * q.1)] else []) = _
      rw [if_neg (fun h => hμ h.1)]
    have hdS : (childCell s pr q).dS = q.1 := rfl
    unfold cellResDeg
    rw [hch, hdS]
    simp only [List.isEmpty_nil, if_true]
    have : q.2 = 1 := by omega
    rw [this, Nat.one_mul]

/-! ## 3. The face-shape and residual-degree reads on the childful config -/

/-- **The engine face-shape multiset is the GENUINE shape `shape`** (each part read back as
`(dS, cellMult) = (D, μ)`), thanks to `cellMult_childful`.  This is the point of the childful
constructor: unlike `oneSideShape` (which recodes to `(D, 1)`), the child payload lets the reader
recover the true `μ`. -/
private theorem faceShape_eqC (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) (hpos : ∀ q ∈ shape, 1 ≤ q.1)
    (hmpos : ∀ q ∈ shape, 1 ≤ q.2) :
    ((M7.cellsOfShapeWF (oneSideShapeChildful s pr shape)).map (fun c => (c.dS, cellMult c)))
      = shape := by
  rw [cellsOfShapeWF_oneSideShapeChildful s pr shape hlt, List.map_map]
  conv_rhs => rw [← List.map_id shape]
  apply List.map_congr_left
  intro q hq
  show ((childCell s pr q).dS, cellMult (childCell s pr q)) = id q
  rw [id]
  have h1 : (childCell s pr q).dS = q.1 := rfl
  rw [h1, cellMult_childful s pr shape hlt hq (hpos q hq) (hmpos q hq)]

/-- The reader's total residual degree is `Σ q.2·q.1 = Σ μ·D` over the shape. -/
private theorem faceDF_eqC (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) (hmpos : ∀ q ∈ shape, 1 ≤ q.2) :
    (((M7.cellsOfShapeWF (oneSideShapeChildful s pr shape)).map cellResDeg).sum)
      = (shape.map (fun q => q.2 * q.1)).sum := by
  rw [cellsOfShapeWF_oneSideShapeChildful s pr shape hlt, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  show cellResDeg (childCell s pr q) = q.2 * q.1
  exact cellResDeg_childful s pr shape hlt hq (hmpos q hq)

/-- The reader's node `δ` is `1` when `shape ≠ []` (head cell carries `δ = 1`). -/
private theorem nodeDelta_eqC (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) (hne : shape ≠ []) :
    Order0.nodeDelta (M7.cellsOfShapeWF (oneSideShapeChildful s pr shape)) = 1 := by
  rw [cellsOfShapeWF_oneSideShapeChildful s pr shape hlt]
  cases shape with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-- The reader's polygon slot is the shared side polygon when `shape ≠ []`. -/
private theorem polygon_eqC (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) (hne : shape ≠ []) :
    (((M7.cellsOfShapeWF (oneSideShapeChildful s pr shape)).head?).map CountCell.polygon).getD
        emptyPolygon
      = mkPoly s [pr.1, pr.2] := by
  rw [cellsOfShapeWF_oneSideShapeChildful s pr shape hlt]
  cases shape with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-! ## 4. The descent-child product on the childful config -/

/-- **The engine child-product of the childful config.**  The `configOf` children flatMap emits one
`ChildData ⟨childShape (μ·D), 1, D⟩` per μ ≥ 2 factor (guard true), each evaluated by the cluster
recursion at the base-changed variable `p^{δ·D} = p^{q.1}`.  By `omChildCount_childShape` each such
factor collapses to `1 / countPivot (μ·D) (p^{q.1})`.  The product over all children equals the
`filterMap` product over the emitting factors.

NOTE (the base-change subtlety, load-bearing): the pivot is evaluated at `p^{q.1}`, NOT at `p` — the
child is entered at the node's base-changed variable `q^{δ·D}` (`omChildCount`'s recursion argument).
For `D = q.1 = 1` (the recommended single-factor case) `p^{q.1} = p`, matching the schematic target;
for `D > 1` the faithful pivot argument is `p^{q.1}`.

Per-factor form with a FIXED node-δ `d` (the `d = 1` instance is what `configOf` uses). -/
private theorem childProd_fixedDelta (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (d : ℕ)
    (shape : List (ℕ × ℕ)) (p : ℕ) :
    ((shape.flatMap (fun q =>
        (childCell s pr q).children.map (fun ch =>
          ({ shape := ch, δ := d, D := q.1 } : ChildData)))).map
        (fun ch => omChildCount ch.shape (p ^ (ch.δ * ch.D)))).prod
      = (shape.filterMap (fun q =>
          if 2 ≤ q.2 ∧ q.2 * q.1 < s then
            some (1 / MontesAxiom.countPivot (q.2 * q.1) (p ^ (d * q.1))) else none)).prod := by
  induction shape with
  | nil => simp
  | cons a t ih =>
      simp only [List.flatMap_cons, List.map_append, List.prod_append, List.filterMap_cons]
      rw [ih]
      -- head factor: the guard on `a` decides.
      by_cases hg : 2 ≤ a.2 ∧ a.2 * a.1 < s
      · have hch : (childCell s pr a).children = [childShape (a.2 * a.1)] := by
          show (if 2 ≤ a.2 ∧ a.2 * a.1 < s then [childShape (a.2 * a.1)] else []) = _
          rw [if_pos hg]
        rw [hch]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, if_pos hg]
        -- omChildCount (childShape (μ·D)) (p^(d·D)) = 1 / countPivot (μ·D) (p^(d·D))
        rw [omChildCount_childShape' (a.2 * a.1) (p ^ (d * a.1))]
      · have hch : (childCell s pr a).children = [] := by
          show (if 2 ≤ a.2 ∧ a.2 * a.1 < s then [childShape (a.2 * a.1)] else []) = _
          rw [if_neg hg]
        rw [hch]
        simp only [List.map_nil, List.prod_nil, one_mul, if_neg hg]

/-- **The engine child-product of the childful config.**  Specializing `childProd_fixedDelta` to the
node-δ `= 1` (`nodeDelta_eqC`, `shape ≠ []`): each μ ≥ 2 factor contributes
`1 / countPivot (μ·D) (p^{q.1})`. -/
private theorem childProd_eqC (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) (hne : shape ≠ []) (p : ℕ) :
    ((configOf (oneSideShapeChildful s pr shape)).children.map
        (fun ch => omChildCount ch.shape (p ^ (ch.δ * ch.D)))).prod
      = (shape.filterMap (fun q =>
          if 2 ≤ q.2 ∧ q.2 * q.1 < s then
            some (1 / MontesAxiom.countPivot (q.2 * q.1) (p ^ q.1)) else none)).prod := by
  have hnd1 : Order0.nodeDelta (M7.cellsOfShapeWF (oneSideShapeChildful s pr shape)) = 1 :=
    nodeDelta_eqC s pr shape hlt hne
  have hchildren : (configOf (oneSideShapeChildful s pr shape)).children
      = (M7.cellsOfShapeWF (oneSideShapeChildful s pr shape)).flatMap (fun c =>
          c.children.map (fun ch =>
            ({ shape := ch,
               δ := Order0.nodeDelta (M7.cellsOfShapeWF (oneSideShapeChildful s pr shape)),
               D := c.dS } : ChildData))) := rfl
  rw [hchildren, hnd1, cellsOfShapeWF_oneSideShapeChildful s pr shape hlt, List.flatMap_map]
  -- the per-factor body is defeq to `childProd_fixedDelta`'s (childCell.dS = q.1 and .children).
  have hkey := childProd_fixedDelta s pr 1 shape p
  simp only [childCell, Nat.one_mul] at hkey
  exact hkey

/-! ## 5. The `mCell` and `volExp` of the childful config -/

/-- **`mCell` of the childful config is the residual-shape count `shapeCount p shape`.**  The single
face carries `δ = 1`, `punctured = true`, and the GENUINE face-shape `shape` (`faceShape_eqC`); the
choice polynomial evaluated at `p^1 = p` is the residual-shape count by `shapeCount_tie_general`
(the general-μ tie — this is where the childful cell's genuine `(D, μ)` shape is consumed). -/
private theorem mCell_configOf_childful (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) (hpos : ∀ q ∈ shape, 1 ≤ q.1)
    (hmpos : ∀ q ∈ shape, 1 ≤ q.2) (hne : shape ≠ []) (p : ℕ) [Fact p.Prime] :
    mCell (configOf (oneSideShapeChildful s pr shape)) p = (CellCard.shapeCount p shape : ℚ) := by
  unfold mCell configOf
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  -- the single face: δ = nodeDelta = 1, shape = faceShape = shape, punctured = true.
  rw [nodeDelta_eqC s pr shape hlt hne, faceShape_eqC s pr shape hlt hpos hmpos]
  simp only [pow_one]
  rw [ShapeCountTie.shapeCount_tie_general p shape hpos hmpos]

/-- **`volExp` of the childful config is `newtonExponent(mkPoly) + Σ μ·D`.** -/
private theorem volExp_configOf_childful (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) (hmpos : ∀ q ∈ shape, 1 ≤ q.2) (hne : shape ≠ []) :
    volExp (configOf (oneSideShapeChildful s pr shape))
      = L4.newtonExponent (mkPoly s [pr.1, pr.2]) + (shape.map (fun q => q.2 * q.1)).sum := by
  unfold volExp configOf
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  congr 1
  · -- polygon slot = mkPoly (head cell).
    rw [polygon_eqC s pr shape hlt hne]
  · -- single face dF = Σ cellResDeg = Σ μ·D.
    exact faceDF_eqC s pr shape hlt hmpos

/-! ## 6. TARGET — the childful `omCount` closed form -/

/-- **The closed form of `omCount` on the childful single-side path shape.**  On a size-`s`,
order-1 single-side path shape carrying a nonempty side shape `shape` (positive degrees `1 ≤ D`,
positive multiplicities `1 ≤ μ`, correct side degree `Σ D·μ = sideDeg pr`, and every μ ≥ 2 factor
emitting a descent child, `hlt`), the engine's `omCount` factorizes as the per-shape residual count
`shapeCount` times the box-volume factor `p^{−(newtonExponent + sideDeg)}` times the PRODUCT of the
self-loop pivot factors `1 / countPivot (μ·D) (p^{D})` over the μ ≥ 2 factors.

The pivot product is the genuine geometric self-loop resummation `∏ 1/(1 − p^{−D·w(μ·D)})` that the
childful descent children carry — the mass ABSENT from the finite decided-cell stratum density.

FAITHFULNESS NOTE: the pivot is evaluated at the base-changed variable `p^{D}` (= `p^{q.1}`), not at
`p`; these coincide exactly when `D = 1` (the recommended single-factor case, e.g. `shape = [(1,2)]`).
The `hmpos : 1 ≤ q.2` hypothesis (positive multiplicity) is genuinely needed here — see
`cellResDeg_childful` — and holds for every `ShapesFor` shape. -/
theorem omCount_oneSideShapeChildful_closed (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (shape : List (ℕ × ℕ)) (hpos : ∀ q ∈ shape, 1 ≤ q.1) (hmpos : ∀ q ∈ shape, 1 ≤ q.2)
    (hdeg : (shape.map (fun q => q.1 * q.2)).sum = sideDeg pr) (hne : shape ≠ [])
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) (p : ℕ) [Fact p.Prime] :
    OMCountV2.omCount (oneSideShapeChildful s pr shape) p
      = (CellCard.shapeCount p shape : ℚ)
          * ((p : ℚ) ^ (L4.newtonExponent (mkPoly s [pr.1, pr.2]) + sideDeg pr))⁻¹
          * (shape.filterMap (fun q =>
              if 2 ≤ q.2 ∧ q.2 * q.1 < s then
                some (1 / MontesAxiom.countPivot (q.2 * q.1) (p ^ q.1)) else none)).prod := by
  rw [omCount]
  simp only [configsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [mCell_configOf_childful s pr shape hlt hpos hmpos hne p,
      volExp_configOf_childful s pr shape hlt hmpos hne,
      childProd_eqC s pr shape hlt hne p]
  -- align Σ μ·D = Σ D·μ = sideDeg pr in the exponent.
  have hsum : (shape.map (fun q => q.2 * q.1)).sum = sideDeg pr := by
    rw [← hdeg]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q _
    exact Nat.mul_comm q.2 q.1
  rw [hsum]

#print axioms omCount_oneSideShapeChildful_closed

/-! ## 7. TARGET — the childful `h_node` (with the exact pivot relation) -/

/-- **The childful `h_node`.**  For a size-`s`, order-1 single-side path `P` (one side
`pr = sidePairs P`) carrying a nonempty side shape `shape` (positive degrees, positive
multiplicities, every μ ≥ 2 factor emitting a child), the genuine order-1 stratum density
`stratumCount1 s N (mkCell s P [shape]) / p^(s·N)` converges (as `N → ∞`) to the FINITE
decided-cell value `shapeCount p shape · p^{−(newtonExponent + sideDeg)}`.

DECISIVE PIVOT FINDING (resolving the pivot-mismatch risk).  The limit is the RAW finite value
`shapeCount·p^{−V}`, which is NOT the engine `omCount` on the childful shape.  By
`omCount_oneSideShapeChildful_closed`,
  `omCount (oneSideShapeChildful s pr shape) p = (limit) · ∏ 1/countPivot(μ·D)(p^{D})`,
so the density limit is the engine value with the self-loop pivot product DIVIDED OUT — the pivot
mass is exactly the self-loop resummation the single-decided-cell density does not capture.  Hence
the faithful h_node states `limit = shapeCount·p^{−V}` (option (a) of the risk analysis: the honest
stratum value), and the companion identity `pivot_relation` below records
`omCount = limit · ∏ pivot`.

The stratum-side Steps A–C are μ-agnostic and coincide verbatim with `hnode_oneSideShape`
(`hnode_decided_order1` + `mkCell_volExp_add_freeExp`, neither of which sees the cell's children). -/
theorem hnode_oneSideShapeChildful (s N₀ : ℕ) (hN₀ : 0 < N₀) (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (P : List (ℕ × ℕ)) (hP : MenuPath s N₀ P) (hsingle : sidePairs P = [pr])
    (shape : List (ℕ × ℕ)) (hsh : ShapesFor P [shape]) (hpos : ∀ q ∈ shape, 1 ≤ q.1)
    (hne : shape ≠ []) (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto (fun N => (stratumCount1 p s N (mkCell s P [shape]) : ℚ) / (p:ℚ)^(s*N))
      Filter.atTop
      (nhds ((CellCard.shapeCount p shape : ℚ)
              * ((p : ℚ) ^ (L4.newtonExponent (mkPoly s [pr.1, pr.2]) + sideDeg pr))⁻¹)) := by
  have hp0 : (p : ℚ) ≠ 0 := by
    have : p ≠ 0 := (Fact.out (p := p.Prime)).ne_zero
    exact_mod_cast this
  -- Step A: the `p^{s(N-1)}`-normalized decided-cell limit (μ-agnostic).
  have hbase := hnode_decided_order1 (p := p) hN₀ hP hsh
  -- Step B: multiply by the constant `(p^s)⁻¹`.
  have hmul := hbase.mul_const ((p : ℚ) ^ s)⁻¹
  -- Step C: rewrite the sequence to the full-box normalization (eventually, for `N ≥ 1`).
  have hseq : Filter.Tendsto
      (fun N => (stratumCount1 p s N (mkCell s P [shape]) : ℚ) / (p:ℚ)^(s*N))
      Filter.atTop
      (nhds (((CellCard.prodSC p [shape] : ℚ) * (p : ℚ) ^ CellCard.freeExp s N₀ P
                / (p : ℚ) ^ (s * (N₀ - 1))) * ((p : ℚ) ^ s)⁻¹)) := by
    refine hmul.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hexp : s * N = s * (N - 1) + s := by
      conv_lhs => rw [show N = (N - 1) + 1 from by omega]
      rw [Nat.mul_add, Nat.mul_one]
    rw [hexp, pow_add]
    field_simp
  -- Step D: identify the limit constant with the RAW value `shapeCount·p^{−V}`.
  have hPpair : P = [pr.1, pr.2] := by
    obtain ⟨H, p1, T, rfl, hH1, hH2, hp1a, hp1b, hc⟩ := hP
    rw [sidePairs_cons₂] at hsingle
    cases T with
    | nil =>
        simp only [sidePairs, List.tail_cons, List.zip_nil_right] at hsingle ⊢
        rw [List.cons_eq_cons] at hsingle
        obtain ⟨heq, _⟩ := hsingle
        rw [← heq]
    | cons q T' =>
        exfalso
        rw [sidePairs_cons₂] at hsingle
        simp only [List.cons_eq_cons] at hsingle
        exact absurd hsingle.2 (by simp)
  have hvolid : volExp (mkCell s P [shape]) + CellCard.freeExp s N₀ P = s * N₀ :=
    mkCell_volExp_add_freeExp s N₀ P hP [shape] hsh
  have hV : volExp (mkCell s P [shape])
      = L4.newtonExponent (mkPoly s [pr.1, pr.2]) + sideDeg pr := by
    rw [hPpair, volExp]
    congr 1
  set V := L4.newtonExponent (mkPoly s [pr.1, pr.2]) + sideDeg pr with hVdef
  have hconst : ((CellCard.prodSC p [shape] : ℚ) * (p : ℚ) ^ CellCard.freeExp s N₀ P
      / (p : ℚ) ^ (s * (N₀ - 1))) * ((p : ℚ) ^ s)⁻¹
      = (CellCard.shapeCount p shape : ℚ) * ((p : ℚ) ^ V)⁻¹ := by
    rw [show CellCard.prodSC p [shape] = CellCard.shapeCount p shape from by
      rw [CellCard.prodSC, List.map_singleton, List.prod_singleton]]
    have hden : (p : ℚ) ^ (s * (N₀ - 1)) * (p : ℚ) ^ s = (p : ℚ) ^ (s * N₀) := by
      rw [← pow_add]
      congr 1
      rw [show s * (N₀ - 1) + s = s * (N₀ - 1) + s * 1 from by rw [Nat.mul_one],
        ← Nat.mul_add, Nat.sub_add_cancel hN₀]
    have hnum : (p : ℚ) ^ (s * N₀) = (p : ℚ) ^ V * (p : ℚ) ^ CellCard.freeExp s N₀ P := by
      rw [← pow_add]
      congr 1
      omega
    have hcollect : (p : ℚ) ^ CellCard.freeExp s N₀ P / (p : ℚ) ^ (s * (N₀ - 1)) * ((p : ℚ) ^ s)⁻¹
        = (p : ℚ) ^ CellCard.freeExp s N₀ P * ((p : ℚ) ^ (s * N₀))⁻¹ := by
      rw [div_eq_mul_inv, mul_assoc, ← mul_inv, hden]
    rw [mul_div_assoc, mul_assoc, hcollect, hnum, mul_inv]
    rw [show (p : ℚ) ^ CellCard.freeExp s N₀ P
          * (((p : ℚ) ^ V)⁻¹ * ((p : ℚ) ^ CellCard.freeExp s N₀ P)⁻¹)
        = ((p : ℚ) ^ V)⁻¹ from by
      field_simp]
  rw [← hconst]
  exact hseq

#print axioms hnode_oneSideShapeChildful

/-! ## 8. The companion pivot relation (`omCount = limit · ∏ pivot`) -/

/-- **The exact pivot relation.**  The engine `omCount` of the childful shape equals the finite
stratum density limit (`hnode_oneSideShapeChildful`'s RHS) times the self-loop pivot product.  This
is the precise algebraic statement of the pivot mismatch: `omCount ≠ limit` (they differ by the
pivot product), so a childful h_node CANNOT be the clean `limit = omCount` identity that the
childless `hnode_oneSideShape` enjoys.  Immediate from `omCount_oneSideShapeChildful_closed`. -/
theorem omCount_eq_limit_mul_pivot (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hpos : ∀ q ∈ shape, 1 ≤ q.1) (hmpos : ∀ q ∈ shape, 1 ≤ q.2)
    (hdeg : (shape.map (fun q => q.1 * q.2)).sum = sideDeg pr) (hne : shape ≠ [])
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) (p : ℕ) [Fact p.Prime] :
    OMCountV2.omCount (oneSideShapeChildful s pr shape) p
      = ((CellCard.shapeCount p shape : ℚ)
          * ((p : ℚ) ^ (L4.newtonExponent (mkPoly s [pr.1, pr.2]) + sideDeg pr))⁻¹)
        * (shape.filterMap (fun q =>
            if 2 ≤ q.2 ∧ q.2 * q.1 < s then
              some (1 / MontesAxiom.countPivot (q.2 * q.1) (p ^ q.1)) else none)).prod :=
  omCount_oneSideShapeChildful_closed s pr shape hpos hmpos hdeg hne hlt p

#print axioms omCount_eq_limit_mul_pivot

end LeanUrat.OM.PathShapeChildful
