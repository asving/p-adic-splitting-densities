/-
Scratch module: FIRST S3 constructor increment — the single-side path shape.
Namespace LeanUrat.OM.PathShape.  Math-first, no sorry/axiom/native_decide.
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

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.PathShape

open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.DecidedOrder1
open LeanUrat.MontesAxiom (CountCell)

open scoped Classical

/-- **The single-side path cluster shape** (FIRST S3 constructor increment).  A size-`s`
order-1 cluster (tree slot `[(1, s, 1)]`) carrying ONE `ShapeCell` PER FACTOR of `shape`: each
`(D, μ)` part `q` becomes a childless cell with `dS = q.1`, `δ = 1`, the shared side polygon
`mkPoly s [pr.1, pr.2]`, and NO descent children.  All cells are childless (the all-`μ=1`
regime), so the engine children collapse — mirroring `DecidedOmCountTie.decidedTc` but with the
faithful per-factor cell list of the side residual shape. -/
def oneSideShape (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) : ClusterShape :=
  ⟨[(1, s, 1)], shape.map (fun q => ⟨q.1, 1, mkPoly s [pr.1, pr.2], []⟩)⟩

/-- **Obligation 1** — the WF reader keeps every per-factor cell (no children ⟹ the descent
guard is vacuous, mirroring `DecidedOmCountTie.cellsOfShapeWF_decidedTc`). -/
theorem cellsOfShapeWF_oneSideShape (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    M7.cellsOfShapeWF (oneSideShape s pr shape)
      = shape.map (fun q =>
          ({ dS := q.1, δ := 1, polygon := mkPoly s [pr.1, pr.2], children := [] } : CountCell)) := by
  rw [M7.cellsOfShapeWF_eq_of_descend]
  · -- identity part: `cellsOfShape` is the field-copy erasure of the payload.
    rw [M7.cellsOfShape, oneSideShape, List.map_map]
    rfl
  · -- descent premise is vacuous: every cell is childless.
    intro c hc ch hch
    rw [M7.cellsOfShape, oneSideShape, List.map_map, List.mem_map] at hc
    obtain ⟨q, _, rfl⟩ := hc
    exact absurd hch List.not_mem_nil

/-! ### Helper computations on the WF cell list of `oneSideShape`. -/

/-- Abbreviation for the WF cell list (obligation 1's RHS). -/
private def wfCells (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) : List CountCell :=
  shape.map (fun q =>
    ({ dS := q.1, δ := 1, polygon := mkPoly s [pr.1, pr.2], children := [] } : CountCell))

/-- `cellMult` of every per-factor cell is `1` (childless). -/
private theorem cellMult_wfCell (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (q : ℕ × ℕ) :
    cellMult ({ dS := q.1, δ := 1, polygon := mkPoly s [pr.1, pr.2], children := [] } : CountCell)
      = 1 := by
  rfl

/-- `cellResDeg` of every per-factor cell is `q.1` (childless ⟹ `= dS`). -/
private theorem cellResDeg_wfCell (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (q : ℕ × ℕ) :
    cellResDeg ({ dS := q.1, δ := 1, polygon := mkPoly s [pr.1, pr.2], children := [] } : CountCell)
      = q.1 := by
  rfl

/-- The face-shape multiset the reader builds is `shape` itself when every `μ = 1`. -/
private theorem faceShape_eq (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hμ : ∀ q ∈ shape, q.2 = 1) :
    ((M7.cellsOfShapeWF (oneSideShape s pr shape)).map (fun c => (c.dS, cellMult c)))
      = shape := by
  rw [cellsOfShapeWF_oneSideShape, List.map_map]
  -- the composite maps `q ↦ (q.1, 1)`; on an all-`μ=1` shape this is the identity.
  conv_rhs => rw [← List.map_id shape]
  apply List.map_congr_left
  intro q hq
  show (q.1, (1 : ℕ)) = id q
  rw [id]
  exact Prod.ext rfl (hμ q hq).symm

/-- The reader's total residual degree is `Σ q.1` over the shape. -/
private theorem faceDF_eq (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    (((M7.cellsOfShapeWF (oneSideShape s pr shape)).map cellResDeg).sum)
      = (shape.map Prod.fst).sum := by
  rw [cellsOfShapeWF_oneSideShape, List.map_map]
  rfl

/-- The reader's node `δ` is `1` when `shape ≠ []` (head cell carries `δ = 1`). -/
private theorem nodeDelta_eq (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hne : shape ≠ []) :
    Order0.nodeDelta (M7.cellsOfShapeWF (oneSideShape s pr shape)) = 1 := by
  rw [cellsOfShapeWF_oneSideShape]
  cases shape with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-- The reader's polygon slot is the shared side polygon when `shape ≠ []`. -/
private theorem polygon_eq (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hne : shape ≠ []) :
    (((M7.cellsOfShapeWF (oneSideShape s pr shape)).head?).map CountCell.polygon).getD emptyPolygon
      = mkPoly s [pr.1, pr.2] := by
  rw [cellsOfShapeWF_oneSideShape]
  cases shape with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-- The reader emits no descent children (every per-factor cell is childless). -/
private theorem children_eq (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    ((M7.cellsOfShapeWF (oneSideShape s pr shape)).flatMap (fun c =>
        c.children.map (fun ch =>
          ({ shape := ch, δ := Order0.nodeDelta (M7.cellsOfShapeWF (oneSideShape s pr shape)),
             D := c.dS } : ChildData))))
      = [] := by
  rw [cellsOfShapeWF_oneSideShape]
  rw [List.flatMap_eq_nil_iff]  -- every mapped list is nil
  intro c hc
  rw [List.mem_map] at hc
  obtain ⟨q, _, rfl⟩ := hc
  rfl

/-- The `cellChildren` of a single all-`μ=1` side shape is empty. -/
private theorem cellChildren_singleton_nil (s : ℕ) (shape : List (ℕ × ℕ))
    (hμ : ∀ q ∈ shape, q.2 = 1) :
    cellChildren s [shape] = [] := by
  rw [cellChildren]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.filterMap_eq_nil_iff]
  intro q hq
  rw [if_neg]
  rintro ⟨h2, _⟩
  rw [hμ q hq] at h2
  omega

/-- `sidePairs [pr.1, pr.2] = [pr]`. -/
private theorem sidePairs_pair (pr : (ℕ × ℕ) × (ℕ × ℕ)) :
    sidePairs [pr.1, pr.2] = [pr] := by
  rw [sidePairs]
  simp only [List.tail_cons, List.zip_cons_cons, List.zip_nil_right]

/-- **Obligation 2 (the bridge)** — on a single-side path with an all-`μ=1` shape of the correct
side degree (and nonempty), the reader's single configuration is exactly `mkCell`'s node.

Hypotheses (all load-bearing, none weaken the conclusion):
* `hμ  : ∀ q ∈ shape, q.2 = 1`  — all multiplicities `1`, so the engine children collapse
  (`cellChildren = []`) AND the reader's face-shape multiset `(dS, cellMult) = (q.1, 1)` is `shape`
  itself (not the coarser `(q.1, 1)` recoding of a genuine `μ ≥ 2` shape);
* `hdeg : (shape.map Prod.fst).sum = sideDeg pr`  — the reader's `dF = Σ dS` must equal `mkFace`'s
  `dF = sideDeg pr`; under `hμ` this is the `shapesOfDegree (sideDeg pr)` sum condition
  `Σ q.1·q.2 = sideDeg pr`;
* `hne : shape ≠ []`  — the reader reads its polygon and `δ` off the HEAD cell, so an empty shape
  would give `emptyPolygon`/`δ=1` instead of the side polygon. -/
theorem configsOf_oneSideShape (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hμ : ∀ q ∈ shape, q.2 = 1)
    (hdeg : (shape.map Prod.fst).sum = sideDeg pr)
    (hne : shape ≠ []) :
    configsOf (oneSideShape s pr shape) = [mkCell s [pr.1, pr.2] [shape]] := by
  show [configOf (oneSideShape s pr shape)] = [mkCell s [pr.1, pr.2] [shape]]
  congr 1
  -- compare `configOf` and `mkCell` field-by-field.
  unfold configOf mkCell
  rw [sidePairs_pair, cellChildren_singleton_nil s shape hμ]
  refine NodeConfig.mk.injEq .. ▸ ?_
  refine ⟨polygon_eq s pr shape hne, ?_, ?_⟩
  · -- the single face
    rw [nodeDelta_eq s pr shape hne, faceShape_eq s pr shape hμ, faceDF_eq s pr shape, hdeg]
    -- both sides are `[mkFace pr shape]`
    show _ = List.zipWith mkFace [pr] [shape]
    rw [List.zipWith_cons_cons, List.zipWith_nil_right, mkFace]
  · exact children_eq s pr shape

/-- **The closed form of `omCount` on the single-side path shape.**  On a size-`s`, order-1,
all-`μ=1` single-side path shape of the correct side degree (nonempty), the engine's `omCount`
collapses to the per-shape residual count `shapeCount` times the box-volume factor
`p^{−(newtonExponent + sideDeg)}` — the root box-volume exponent (no `− s`, no pivot: this is the
ROOT `omCount`, not the cluster-node `omChildCount`). -/
theorem omCount_oneSideShape_closed (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hpos : ∀ q ∈ shape, 1 ≤ q.1) (hμ : ∀ q ∈ shape, q.2 = 1)
    (hdeg : (shape.map Prod.fst).sum = sideDeg pr) (hne : shape ≠ [])
    (p : ℕ) [Fact p.Prime] :
    omCount (oneSideShape s pr shape) p
      = (CellCard.shapeCount p shape : ℚ)
          * ((p : ℚ) ^ (L4.newtonExponent (mkPoly s [pr.1, pr.2]) + sideDeg pr))⁻¹ := by
  -- Step 1: unfold `omCount` and reduce the config list to the single `mkCell` node.
  rw [omCount, configsOf_oneSideShape s pr shape hμ hdeg hne]
  -- the single config; its children are `cellChildren s [shape] = []` (all `μ = 1`).
  have hchildren : (mkCell s [pr.1, pr.2] [shape]).children = [] := by
    show cellChildren s [shape] = []
    exact cellChildren_singleton_nil s shape hμ
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    hchildren, List.map_nil, List.prod_nil, mul_one]
  -- Step 2: `mCell (mkCell s [pr.1,pr.2] [shape]) p = shapeCount p shape`.
  have hlen : ([shape] : List (List (ℕ × ℕ))).length = (sidePairs [pr.1, pr.2]).length := by
    rw [sidePairs_pair]
    rfl
  rw [CellCard.mCell_mkCell hlen p]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← ShapeCountTie.shapeCount_tie_general p shape hpos
      (fun q hq => by rw [hμ q hq])]
  -- Step 3: identify `volExp (mkCell s [pr.1,pr.2] [shape])`.
  have hvol : volExp (mkCell s [pr.1, pr.2] [shape])
      = L4.newtonExponent (mkPoly s [pr.1, pr.2]) + sideDeg pr := by
    rw [volExp]
    -- `(mkCell ..).polygon = mkPoly s [pr.1,pr.2]` and the single face's `dF = sideDeg pr`,
    -- both definitional (`sidePairs [pr.1,pr.2] = [pr]`, `(mkFace pr shape).dF = sideDeg pr`).
    congr 1
  rw [hvol]

#print axioms omCount_oneSideShape_closed

/-! ## RESULT 1 — the exponent identity `volExp + freeExp = s·N` -/

open CellCard

/-- `newtonExponent (mkPoly s P)` is the sum of the per-column ceilings over `Fin s`. -/
private theorem newtonExponent_mkPoly (s : ℕ) (P : List (ℕ × ℕ)) :
    L4.newtonExponent (mkPoly s P) = ∑ i ∈ Finset.range s, ceilAt P i := by
  rw [L4.newtonExponent, Finset.sum_range fun i => ceilAt P i]
  rfl

/-- A length-matched `zipWith` whose combiner ignores its second argument reduces to a `map` of the
first list.  The `dF ∘ mkFace` case: `FaceAssign.dF (mkFace pr shape) = sideDeg pr`. -/
private theorem zipWith_dF_mkFace_sum :
    ∀ (sp : List ((ℕ × ℕ) × (ℕ × ℕ))) (sh : List (List (ℕ × ℕ))),
      sh.length = sp.length →
      ((List.zipWith mkFace sp sh).map FaceAssign.dF).sum = (sp.map sideDeg).sum := by
  intro sp
  induction sp with
  | nil => intro sh _; simp
  | cons pr rest ih =>
      intro sh hlen
      cases sh with
      | nil => simp at hlen
      | cons a t =>
          simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons]
          rw [ih t (by simpa using hlen)]
          -- `FaceAssign.dF (mkFace pr a) = sideDeg pr` definitionally.
          rfl

private theorem faceDF_mkCell (s : ℕ) (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ)))
    (hlen : sh.length = (sidePairs P).length) :
    ((mkCell s P sh).faces.map FaceAssign.dF).sum
      = ((sidePairs P).map sideDeg).sum := by
  show ((List.zipWith mkFace (sidePairs P) sh).map FaceAssign.dF).sum = _
  exact zipWith_dF_mkFace_sum (sidePairs P) sh hlen

/-- **Telescoping of runs along a chain.**  The sum of side runs `Σ (pr.2.1 − pr.1.1)` over the
sides of `p1 :: T` equals `s − p1.1` (abscissas increase `p1.1 → s`). -/
private theorem chainOK_run_sum {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) :
    ((sidePairs (p1 :: T)).map (fun pr => pr.2.1 - pr.1.1)).sum = s - p1.1 := by
  induction h with
  | @nil p0 p1 h1 h2 =>
      -- single vertex list [p1]; no sides; s - p1.1 = 0 since p1.1 = s.
      simp only [sidePairs, List.tail_cons, List.zip_nil_right, List.map_nil, List.sum_nil]
      omega
  | @cons p0 p1 p2 T h1 h2 h3 h4 ih =>
      -- sides of (p1 :: p2 :: T) = (p1,p2) :: sides of (p2 :: T)
      rw [sidePairs_cons₂, List.map_cons, List.sum_cons, ih]
      simp only []  -- beta-reduce the head map application `(fun pr => ..) (p1, p2)`
      -- (p2.1 - p1.1) + (s - p2.1) = s - p1.1, using p1.1 < p2.1 ≤ s.
      have hp2s : p2.1 ≤ s := chainOK_le h4
      show (p2.1 - p1.1) + (s - p2.1) = s - p1.1
      omega

/-- The terminal vertex of a chain is `(s, 0)`; hence the last abscissa of `p1 :: T` is `s`. -/
private theorem chainOK_getLast? {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) : (p1 :: T).getLast? = some (s, 0) := by
  induction h with
  | @nil p0 p1 h1 h2 =>
      have hp : p1 = (s, 0) := Prod.ext h1 h2
      simp [hp]
  | @cons p0 p1 p2 T h1 h2 h3 h4 ih =>
      rw [List.getLast?_cons_cons]
      exact ih

/-- Pointwise `sideDeg ≤ run` lets `Σ sideDeg + Σ(run − sideDeg) = Σ run`. -/
private theorem sum_deg_add_free {sp : List ((ℕ × ℕ) × (ℕ × ℕ))}
    (hle : ∀ pr ∈ sp, sideDeg pr ≤ pr.2.1 - pr.1.1) :
    (sp.map sideDeg).sum + (sp.map (fun pr => pr.2.1 - pr.1.1 - sideDeg pr)).sum
      = (sp.map (fun pr => pr.2.1 - pr.1.1)).sum := by
  induction sp with
  | nil => rfl
  | cons pr rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have hpr : sideDeg pr ≤ pr.2.1 - pr.1.1 := hle pr List.mem_cons_self
      have ihr := ih (fun q hq => hle q (List.mem_cons_of_mem _ hq))
      omega

/-- **RESULT 1 — the exponent identity.**  On a menu path `P` (level `N`) with shapes `sh`, the
cell's root box-volume exponent and the free-digit exponent are complementary in `s·N`:
`volExp (mkCell s P sh) + freeExp s N P = s·N`.  Span `= s` holds (the abscissas run `0 → s`). -/
theorem mkCell_volExp_add_freeExp (s N : ℕ) (P : List (ℕ × ℕ)) (hP : MenuPath s N P)
    (sh : List (List (ℕ × ℕ))) (hsh : ShapesFor P sh) :
    volExp (mkCell s P sh) + CellCard.freeExp s N P = s * N := by
  have hlen : sh.length = (sidePairs P).length := hsh.length_eq
  -- `volExp (mkCell s P sh) = Σ_{i<s} ceilAt P i + Σ_{pr} sideDeg pr`
  have hvol : volExp (mkCell s P sh)
      = (∑ i ∈ Finset.range s, ceilAt P i) + ((sidePairs P).map sideDeg).sum := by
    rw [volExp]
    congr 1
    · -- polygon slot: `(mkCell s P sh).polygon = mkPoly s P` (defeq)
      rw [show (mkCell s P sh).polygon = mkPoly s P from rfl, newtonExponent_mkPoly]
    · exact faceDF_mkCell s P sh hlen
  rw [hvol, CellCard.freeExp, CellCard.chainFree]
  -- Ceiling piece: ceilAt P i ≤ N-1 for i < s.
  have hceil : ∀ i ∈ Finset.range s, ceilAt P i ≤ N - 1 := by
    intro i hi
    exact CellCard.menuPath_ceilAt_le hP (Finset.mem_range.mp hi)
  -- Run piece: sideDeg pr ≤ (pr.2.1 - pr.1.1) for every side.
  have hrun : ∀ pr ∈ sidePairs P, sideDeg pr ≤ pr.2.1 - pr.1.1 := by
    intro pr hpr
    obtain ⟨hw, _, _, _⟩ := menuPath_side_facts hP pr hpr
    have hdvd : sideDeg pr ∣ (pr.2.1 - pr.1.1) := Nat.gcd_dvd_right _ _
    exact Nat.le_of_dvd (by omega) hdvd
  -- Combine: (Σceil + ΣsideDeg) + (Σ(N-1-ceil) + Σ(run-sideDeg))
  --        = (Σceil + Σ(N-1-ceil)) + (ΣsideDeg + Σ(run-sideDeg))
  --        = s*(N-1) + Σrun = s*(N-1) + s = s*N.
  have hceilsum : (∑ i ∈ Finset.range s, ceilAt P i)
      + (∑ i ∈ Finset.range s, (N - 1 - ceilAt P i)) = s * (N - 1) := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun i hi => by
      have := hceil i hi; omega : ∀ i ∈ Finset.range s,
        ceilAt P i + (N - 1 - ceilAt P i) = N - 1)]
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
  have hrunsum : ((sidePairs P).map sideDeg).sum
      + ((sidePairs P).map (fun pr => pr.2.1 - pr.1.1 - sideDeg pr)).sum
      = ((sidePairs P).map (fun pr => pr.2.1 - pr.1.1)).sum :=
    sum_deg_add_free hrun
  -- Span: Σ run telescopes to (last abscissa − first abscissa) = s − 0 = s.
  have hspan : ((sidePairs P).map (fun pr => pr.2.1 - pr.1.1)).sum = s := by
    obtain ⟨H, p1, T, hPeq, hH1, hH2, hp1a, hp1b, hc⟩ := hP
    subst hPeq
    -- sides of (0,H) :: p1 :: T = ((0,H), p1) :: sides of (p1 :: T)
    rw [sidePairs_cons₂, List.map_cons, List.sum_cons, chainOK_run_sum hc]
    -- (p1.1 - 0) + (s - p1.1) = s, using 0 < p1.1 ≤ s.
    have hp1s : p1.1 ≤ s := chainOK_le hc
    show (p1.1 - (0 : ℕ)) + (s - p1.1) = s
    omega
  rw [show ((sidePairs P).map (fun pr => pr.2.1 - pr.1.1)) =
        (List.map (fun pr => pr.2.1 - pr.1.1) (sidePairs P)) from rfl] at hrunsum
  -- assemble.
  calc (∑ i ∈ Finset.range s, ceilAt P i) + ((sidePairs P).map sideDeg).sum
        + ((∑ i ∈ Finset.range s, (N - 1 - ceilAt P i))
            + ((sidePairs P).map (fun pr => pr.2.1 - pr.1.1 - sideDeg pr)).sum)
      = ((∑ i ∈ Finset.range s, ceilAt P i) + (∑ i ∈ Finset.range s, (N - 1 - ceilAt P i)))
        + (((sidePairs P).map sideDeg).sum
            + ((sidePairs P).map (fun pr => pr.2.1 - pr.1.1 - sideDeg pr)).sum) := by ring
    _ = s * (N - 1) + ((sidePairs P).map (fun pr => pr.2.1 - pr.1.1)).sum := by
          rw [hceilsum, hrunsum]
    _ = s * (N - 1) + s := by rw [hspan]
    _ = s * N := by
          -- N ≥ 1 from MenuPath (1 ≤ H ≤ N-1 ⟹ N ≥ 2)
          have hN1 : 1 ≤ N := by
            obtain ⟨H, p1, T, _, hH1, hH2, _, _, _⟩ := hP; omega
          rw [show s * (N - 1) + s = s * (N - 1) + s * 1 from by rw [Nat.mul_one],
            ← Nat.mul_add, Nat.sub_add_cancel hN1]

#print axioms mkCell_volExp_add_freeExp

/-! ## RESULT 2 — the first genuine cluster-shape `h_node` (single-side path) -/

/-- **RESULT 2 — the single-side `h_node`.**  For a size-`s`, order-1, all-`μ = 1` single-side path
`P` (exactly one side `pr = sidePairs P`) carrying a nonempty side shape `shape` of the right degree,
the genuine order-1 stratum density `stratumCount1 s N (mkCell s P [shape]) / p^(s·N)` — normalized by
the FULL box `p^{s·N}` — converges (as `N → ∞`) to the engine value `omCount (oneSideShape s pr shape) p`.

This is the first cluster-shape `h_node` that ties the density limit to a genuine engine
`ClusterShape` literal (`oneSideShape`), via RESULT 1's exponent identity `volExp + freeExp = s·N₀`.
Route: `hnode_decided_order1` gives the `p^{s(N−1)}`-normalized limit `C`; the extra `p^{−s}` factor
(from `s·N = s·(N−1) + s`) turns `C` into `C·p^{−s}`, and RESULT 1 identifies `C·p^{−s}` with
`omCount (oneSideShape …) p = shapeCount · p^{−volExp}`. -/
theorem hnode_oneSideShape (s N₀ : ℕ) (hN₀ : 0 < N₀) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (P : List (ℕ × ℕ))
    (hP : MenuPath s N₀ P) (hsingle : sidePairs P = [pr]) (shape : List (ℕ × ℕ))
    (hsh : ShapesFor P [shape]) (hpos : ∀ q ∈ shape, 1 ≤ q.1) (hμ : ∀ q ∈ shape, q.2 = 1)
    (hne : shape ≠ []) (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto (fun N => (stratumCount1 p s N (mkCell s P [shape]) : ℚ) / (p:ℚ)^(s*N))
      Filter.atTop (nhds (omCount (oneSideShape s pr shape) p)) := by
  have hp0 : (p : ℚ) ≠ 0 := by
    have : p ≠ 0 := (Fact.out (p := p.Prime)).ne_zero
    exact_mod_cast this
  -- the degree condition needed by `omCount_oneSideShape_closed`, derived from `hsh` + `hμ`.
  have hshape_mem : shape ∈ shapesOfDegree (sideDeg pr) := by
    rw [ShapesFor, hsingle] at hsh
    rw [List.forall₂_cons] at hsh
    exact hsh.1
  have hdeg : (shape.map Prod.fst).sum = sideDeg pr := by
    rw [mem_shapesOfDegree_iff] at hshape_mem
    rw [← hshape_mem.2.2]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    show q.1 = q.1 * q.2
    rw [hμ q hq, Nat.mul_one]
  -- Step A: the `p^{s(N-1)}`-normalized limit (the decided-cell `h_node`).
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
    -- p^(s*N) = p^(s*(N-1)) * p^s, so /p^(sN) = (/p^(s(N-1))) * (p^s)⁻¹.
    have hexp : s * N = s * (N - 1) + s := by
      conv_lhs => rw [show N = (N - 1) + 1 from by omega]
      rw [Nat.mul_add, Nat.mul_one]
    rw [hexp, pow_add]
    field_simp
  -- Step D: identify the limit constant with `omCount (oneSideShape s pr shape) p`.
  -- `sidePairs P = [pr]` pins `P = [pr.1, pr.2]` (a two-vertex path).
  have hPpair : P = [pr.1, pr.2] := by
    obtain ⟨H, p1, T, rfl, hH1, hH2, hp1a, hp1b, hc⟩ := hP
    rw [sidePairs_cons₂] at hsingle
    -- head side is ((0,H), p1); its tail (sides of p1::T) must be empty, forcing T = [].
    cases T with
    | nil =>
        simp only [sidePairs, List.tail_cons, List.zip_nil_right] at hsingle ⊢
        -- hsingle : ((0,H), p1) = pr
        rw [List.cons_eq_cons] at hsingle
        obtain ⟨heq, _⟩ := hsingle
        rw [← heq]
    | cons q T' =>
        exfalso
        rw [sidePairs_cons₂] at hsingle
        simp only [List.cons_eq_cons] at hsingle
        exact absurd hsingle.2 (by simp)
  -- the volume exponent identity (RESULT 1 at N₀) on the two-vertex path.
  have hvolid : volExp (mkCell s P [shape]) + CellCard.freeExp s N₀ P = s * N₀ :=
    mkCell_volExp_add_freeExp s N₀ P hP [shape] hsh
  have hV : volExp (mkCell s P [shape])
      = L4.newtonExponent (mkPoly s [pr.1, pr.2]) + sideDeg pr := by
    rw [hPpair, volExp]
    congr 1
  set V := L4.newtonExponent (mkPoly s [pr.1, pr.2]) + sideDeg pr with hVdef
  -- assemble the constant equality.
  have hconst : ((CellCard.prodSC p [shape] : ℚ) * (p : ℚ) ^ CellCard.freeExp s N₀ P
      / (p : ℚ) ^ (s * (N₀ - 1))) * ((p : ℚ) ^ s)⁻¹
      = omCount (oneSideShape s pr shape) p := by
    rw [omCount_oneSideShape_closed s pr shape hpos hμ hdeg hne p]
    -- prodSC p [shape] = shapeCount p shape.
    rw [show CellCard.prodSC p [shape] = CellCard.shapeCount p shape from by
      rw [CellCard.prodSC, List.map_singleton, List.prod_singleton]]
    -- combine denominators: p^(s(N₀-1)) · p^s = p^(s·N₀).
    have hden : (p : ℚ) ^ (s * (N₀ - 1)) * (p : ℚ) ^ s = (p : ℚ) ^ (s * N₀) := by
      rw [← pow_add]
      congr 1
      rw [show s * (N₀ - 1) + s = s * (N₀ - 1) + s * 1 from by rw [Nat.mul_one],
        ← Nat.mul_add, Nat.sub_add_cancel hN₀]
    -- s·N₀ = V + freeExp, so p^(s·N₀) = p^V · p^(freeExp).
    have hnum : (p : ℚ) ^ (s * N₀) = (p : ℚ) ^ V * (p : ℚ) ^ CellCard.freeExp s N₀ P := by
      rw [← pow_add]
      congr 1
      omega
    -- fold the RHS exponent to `V`.
    rw [← hVdef]
    have hfne : (p : ℚ) ^ CellCard.freeExp s N₀ P ≠ 0 := pow_ne_zero _ hp0
    -- rewrite `/ p^(s(N₀-1)) * (p^s)⁻¹` as `* (p^(sN₀))⁻¹` (combine the two denominators).
    have hcollect : (p : ℚ) ^ CellCard.freeExp s N₀ P / (p : ℚ) ^ (s * (N₀ - 1)) * ((p : ℚ) ^ s)⁻¹
        = (p : ℚ) ^ CellCard.freeExp s N₀ P * ((p : ℚ) ^ (s * N₀))⁻¹ := by
      rw [div_eq_mul_inv, mul_assoc, ← mul_inv, hden]
    rw [mul_div_assoc, mul_assoc, hcollect, hnum, mul_inv]
    -- shapeCount * (p^free * ((p^V)⁻¹ * (p^free)⁻¹)) = shapeCount * (p^V)⁻¹.
    rw [show (p : ℚ) ^ CellCard.freeExp s N₀ P
          * (((p : ℚ) ^ V)⁻¹ * ((p : ℚ) ^ CellCard.freeExp s N₀ P)⁻¹)
        = ((p : ℚ) ^ V)⁻¹ from by
      field_simp]
  rw [← hconst]
  exact hseq

#print axioms hnode_oneSideShape

end LeanUrat.OM.PathShape
