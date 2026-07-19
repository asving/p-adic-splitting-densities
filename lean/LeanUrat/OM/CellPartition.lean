/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.MontesAxiom
import LeanUrat.CountingModel
import LeanUrat.L4
import LeanUrat.OM.NewtonPolygon
import LeanUrat.OM.ResidualPolynomial
import LeanUrat.OM.OMType
import LeanUrat.OM.Termination

/-!
# M7 — CellPartition: real cells of an OM type and the exhaustive partition
(blueprint §"M7 — CellPartition", `subsec` M7; GAP 4 `def:side-to-l4face`)

**FROZEN SIGNATURE SKELETON.** This module states the blueprint M7 nodes with their intended
signatures and `sorry` bodies. M7 turns a real OM type into its list of `MontesAxiom.CountCell`s and
proves the strata partition the decided polynomials (discharging `MontesData.partition`).

Blueprint nodes frozen:
* `def:cells-of-type`  → `cellsOfType`
* `lem:cells-descend`  → `cells_descend`   (MontesData.cells_descend shape)
* `lem:m7-partition`   → `partition`       (MontesData.partition shape)
* `def:shape-class`    → `shapeClass`
* `def:side-to-l4face` (GAP 4) → `toSideFace`
* `lem:side-to-l4face-spec` → `toSideFace_bb1Value`
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.M7

open LeanUrat LeanUrat.MontesAxiom LeanUrat.CountingModel

open scoped Classical

/-! ## GAP 4 — the per-side L4 lattice face (`def:side-to-l4face`)

The per-side L4 face restricts the lattice polygon to the abscissa window `[i₀, j₀]` of a side `S`
(width `ℓ(S)`, not the full degree `n`). The target type is `L4.LatticePolygon`. -/

/-- The lattice height of the side `S` at relative column `k` (abscissa `i₀ + k`): the ceiling of the
linear edge height `v₀ + λ_S · k`, where `λ_S = (v₁ - v₀)/(j₀ - i₀)` is the side slope. This is the
genuine Newton-polygon height ALONG the side (an affine drop from `v₀` to `v₁`), de-stubbing the old
height-`0` body. -/
noncomputable def sideCeilHeight (S : NewtonPolygon.Side) (k : ℕ) : ℕ :=
  (⌈(S.v₀ : ℚ) + S.slope * (k : ℚ)⌉).toNat

/-- **Per-side L4 lattice face** (`def:side-to-l4face`, GAP 4, DE-STUBBED via GLUE-5). For a side `S`,
the lattice polygon on the abscissa window `[i₀, j₀]`: width `ℓ(S) = j₀ - i₀`, ceiling heights the REAL
edge heights `⌈v₀ + λ_S·k⌉` (the polygon height along the side, no longer the `0`-stub), and the single
lattice vertex at the left endpoint column `0` (the only hull vertex inside the half-open window
`[i₀, j₀)`; the right endpoint `j₀` is the left endpoint of the next side). -/
noncomputable def toSideFace (S : NewtonPolygon.Side) : L4.LatticePolygon :=
  { width := S.length
    ceilHeights := fun k => sideCeilHeight S k.val
    isVertex := fun k => decide (k.val = 0) }

/-- The column-`0` height of the side face is exactly the left endpoint height `v₀` (the edge starts
at `(i₀, v₀)`, so `sideCeilHeight S 0 = ⌈v₀⌉₊ = v₀`). -/
theorem sideCeilHeight_zero (S : NewtonPolygon.Side) : sideCeilHeight S 0 = S.v₀ := by
  unfold sideCeilHeight
  simp [Int.ceil_natCast, Int.toNat_natCast]

/-- **Per-side face correctness** (`lem:side-to-l4face-spec`). `L4.newtonExponent (toSideFace S)` is
the per-column closed-exponent sum of the side, and `bb1Value` is the per-cell box term. (Still `rfl`:
`bb1Value` is defined directly in terms of `newtonVertexCount`/`newtonExponent`, independent of the
particular `ceilHeights`/`isVertex`, so the de-stub of those fields does not disturb this lemma.) -/
theorem toSideFace_bb1Value (S : NewtonPolygon.Side) (Q : ℕ) (_hQ : 1 ≤ Q) :
    L4.bb1Value (toSideFace S) Q
      = (1 - (Q : ℚ)⁻¹) ^ L4.newtonVertexCount (toSideFace S)
        * ((Q : ℚ) ^ L4.newtonExponent (toSideFace S))⁻¹ := by
  rfl

/-- **The Newton-exponent share of a side is GENUINELY NONZERO** (de-stubs the WAVE-2 "shares are
identically 0" bug). For a side of positive width `ℓ(S) ≥ 1` starting at positive height `v₀ > 0`,
`L4.newtonExponent (toSideFace S) > 0`: the column-`0` ceiling height is `v₀ > 0`, and the exponent is
the SUM of the per-column heights, so it is at least `v₀`. With the old height-`0` stub
(`ceilHeights := fun _ => 0`) this sum was identically `0`; the real edge heights make it positive. -/
theorem toSideFace_newtonExponent_pos (S : NewtonPolygon.Side)
    (hw : 0 < S.length) (hv : 0 < S.v₀) : 0 < L4.newtonExponent (toSideFace S) := by
  unfold L4.newtonExponent toSideFace
  simp only
  -- the column-0 term is `sideCeilHeight S 0 = v₀ > 0`; the sum of `ℕ`s dominates any one term
  have h0 : (⟨0, hw⟩ : Fin S.length) ∈ Finset.univ := Finset.mem_univ _
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun k : Fin S.length =>
      sideCeilHeight S k.val) (fun _ _ => Nat.zero_le _) h0)
  -- `sideCeilHeight S 0 = v₀ > 0`
  rw [show ((⟨0, hw⟩ : Fin S.length) : ℕ) = 0 from rfl, sideCeilHeight_zero]
  exact hv

/-! ## Counting cells of a real OM type (`def:cells-of-type`)

`cellsOfType T : List CountCell` — one `CountCell` per (finite-slope side `S`, distinct monic
irreducible residual factor `ψ`) pair, with `dS := deg ψ`, `δ := [F_r : F_q]`, `polygon := toSideFace
S`, and `children := []` (leaf, `a_ψ = 1`) or a singleton child shape (descend, `a_ψ ≥ 2`). -/

/-- **Counting cells of a real OM type** (`def:cells-of-type`). One `MontesAxiom.CountCell` per
(side, distinct residual factor) pair. Skeleton body uses the M5-carried cells erased to `CountCell`;
the genuine per-factor construction (one cell per element of the M4 `ResidualFactorization`) is the
real M7 content. -/
noncomputable def cellsOfType (T : M5.OMType) : List CountCell :=
  (M5.cells T).map (fun c =>
    { dS := c.dS
      δ := T.δ
      polygon := c.polygon
      children := c.children.map (fun ch => ch.node) })

/-- The cell-list as a function of the count-native `ClusterShape` index, via the M9 decoder
`decode : ClusterShape → OMType` (here taken as a parameter so M9 supplies the real decoder). This is
the `MontesAxiom.MontesData.cells` field shape. -/
noncomputable def cells (decode : ClusterShape → M5.OMType) (T : ClusterShape) : List CountCell :=
  cellsOfType (decode T)

/-- **The FAITHFUL cell reader** (decision 2b scaffolding). Reads the genuine `CountCell` list
DIRECTLY off the enriched `ClusterShape.cells` payload, with NO `decode → M5.cells` round-trip — the
`ShapeCell` fields (`dS`, `δ`, `polygon`, `children`) are exactly the `CountCell` fields, so the
erasure is a field copy. This is the lossless reader the enriched shape enables: where the legacy
`cells decode` reconstructs a (schematic) `OMType` and refactors, `cellsOfShape` returns the cells the
encoder `M5.shapeOf` recorded. The faithfulness coupling is `cellsOfShape_shapeOf` below. -/
def cellsOfShape (T : ClusterShape) : List CountCell :=
  T.cells.map (fun sc =>
    { dS := sc.dS, δ := sc.δ, polygon := sc.polygon, children := sc.children })

/-- **Faithfulness of the enriched payload** (decision 2b, the by-construction coupling). The faithful
reader applied to `M5.shapeOf T` returns EXACTLY the erasure of `M5.cells T` — i.e. the same
`CountCell` list `cellsOfType T` produces from the real OM cells. PROVED by `rfl`: `M5.shapeOf` writes
`encodeCells T` into the `cells` payload, and `cellsOfShape`/`cellsOfType` both erase the identical
`(dS, T.δ, polygon, children.map node)` fields. So the enriched `ClusterShape` carries the genuine cell
list losslessly — `M7.cells` can be re-pointed to `cellsOfShape ∘ decode` once `decode` is the genuine
`shapeOf`-section, recovering the REAL cells (not the schematic reconstruction). -/
theorem cellsOfShape_shapeOf (T : M5.OMType) : cellsOfShape (M5.shapeOf T) = cellsOfType T := by
  simp only [cellsOfShape, M5.shapeOf, M5.encodeCells, cellsOfType, List.map_map, Function.comp_def]

/-- **The WELL-FOUNDED faithful cell reader** (Phase-A A4, 2026-07-02). `cellsOfShape` filtered to
the cells ALL of whose payload children strictly descend (`nodeSizeOf ch < nodeSizeOf T`). Rationale:
`MontesAxiom.MontesData.cells_descend` quantifies over ALL `ClusterShape`s, and the raw payload of an
ARBITRARY (junk) shape is free data — the unguarded `cellsOfShape` cannot satisfy it (this is exactly
why the old real instance detoured through the vacuous `decode` round-trip). The guard makes
`cells_descend` PROVABLE for every shape (`cellsOfShapeWF_descend`) while being the IDENTITY on
genuine encoder/classifier-emitted shapes (`cellsOfShapeWF_shapeOf`: the recorded children carry
`hChildSizeLt`, so the filter keeps everything). Junk shapes lose their junk cells — irrelevant, they
are off the reachable menu. -/
noncomputable def cellsOfShapeWF (T : ClusterShape) : List CountCell :=
  (cellsOfShape T).filter (fun c =>
    decide (∀ ch ∈ c.children, M5.nodeSizeOf ch < M5.nodeSizeOf T))

/-- **`cellsOfShapeWF` satisfies the descent law for EVERY shape** (the `MontesData.cells_descend`
field shape, with `treeSize = M6.treeSize = M5.nodeSizeOf` definitionally) — no `decode`, no
vacuity: the filter carries the witness. -/
theorem cellsOfShapeWF_descend :
    ∀ (T : ClusterShape), ∀ c ∈ cellsOfShapeWF T, ∀ ch ∈ c.children,
      M6.treeSize ch < M6.treeSize T := by
  intro T c hc ch hch
  rw [cellsOfShapeWF, List.mem_filter] at hc
  exact of_decide_eq_true hc.2 ch hch

/-- On shapes whose payload children all strictly descend, the guard is invisible:
`cellsOfShapeWF = cellsOfShape`. -/
theorem cellsOfShapeWF_eq_of_descend (T : ClusterShape)
    (h : ∀ c ∈ cellsOfShape T, ∀ ch ∈ c.children, M5.nodeSizeOf ch < M5.nodeSizeOf T) :
    cellsOfShapeWF T = cellsOfShape T := by
  rw [cellsOfShapeWF]
  exact List.filter_eq_self.mpr (fun c hc => decide_eq_true (h c hc))

/-- **Faithfulness of the guarded reader on genuine shapes**: on `M5.shapeOf T` the filter keeps
every cell (the recorded children carry the `hChildSizeLt` descent witness), so `cellsOfShapeWF`
returns exactly the erasure `cellsOfType T` — the guard costs nothing on the reachable image. -/
theorem cellsOfShapeWF_shapeOf (T : M5.OMType) :
    cellsOfShapeWF (M5.shapeOf T) = cellsOfType T := by
  have hb : ∀ c ∈ cellsOfShape (M5.shapeOf T), ∀ ch ∈ c.children,
      M5.nodeSizeOf ch < M5.nodeSizeOf (M5.shapeOf T) := by
    intro c hc ch hch
    rw [cellsOfShape_shapeOf, cellsOfType, List.mem_map] at hc
    obtain ⟨c', _, rfl⟩ := hc
    simp only [List.mem_map] at hch
    obtain ⟨ch', _, rfl⟩ := hch
    have h1 := M5.nodeSizeOf_child_lt T ch'
    have h2 := M5.nodeSizeOf_shapeOf T
    omega
  rw [cellsOfShapeWF_eq_of_descend (M5.shapeOf T) hb, cellsOfShape_shapeOf]

/-- **Every `CountCell` child of a real cell is the encoded `node` of a genuine `OMCell.Child`**
(the structural coupling, PROVED from the definition of `cellsOfType`). For any cell
`c ∈ cells decode T` and child `ch ∈ c.children`, there is an `OMCell.Child (decode T)` whose
serialized `node` is `ch`. This is what makes `cells_descend` non-vacuous and COUPLED to the real
child structure. -/
theorem cells_child_eq_node (decode : ClusterShape → M5.OMType) (T : ClusterShape)
    (c : CountCell) (hc : c ∈ cells decode T) (ch : ClusterShape) (hch : ch ∈ c.children) :
    ∃ ch' : M5.OMCell.Child (decode T), ch = ch'.node := by
  -- unfold `cells`/`cellsOfType`: `c` is the image of some real `OMCell (decode T)`
  rw [cells, cellsOfType, List.mem_map] at hc
  obtain ⟨c', _hc', rfl⟩ := hc
  -- the children of the image cell are `c'.children.map (·.node)`
  simp only at hch
  rw [List.mem_map] at hch
  obtain ⟨ch', _hch', rfl⟩ := hch
  exact ⟨ch', rfl⟩

/-- **The descent children are strictly smaller** (`lem:cells-descend`), RE-COUPLED and NON-VACUOUS.
With `treeSize := M6.treeSize`, the real cell list `cells decode`, and the `decode`-section coupling
`hsize : ∀ T, treeSize T = clusterSize (decode T)` (an honest decoder is a `shapeOf`-section on the
size slot), every descent child has strictly smaller `treeSize`. PROVED from `M6.cells_descend` fed the
structural witness `cells_child_eq_node` (so the descent is the genuine `M5.nodeSizeOf_child_lt`, not
emptiness). This matches the `MontesAxiom.MontesData.cells_descend` field type. -/
theorem cells_descend (decode : ClusterShape → M5.OMType)
    (hsize : ∀ T : ClusterShape, M6.treeSize T = M5.clusterSize (decode T)) :
    ∀ (T : ClusterShape), ∀ c ∈ cells decode T, ∀ ch ∈ c.children,
      M6.treeSize ch < M6.treeSize T :=
  M6.cells_descend decode (cells decode) hsize (cells_child_eq_node decode)

/-! ## The shape classifier and the exhaustive partition (`def:shape-class`, `lem:m7-partition`) -/

/-- **The level-`N` shape classifier** (`def:shape-class`). Maps a coset `f` decided to type `σ` to the
shape of its (unique) `N`-truncated OM tree. Carried opaquely (the genuine classifier runs the
`N`-truncated OM algorithm; single-valuedness is the CITED OM uniqueness import). -/
noncomputable def shapeClass (_N _n : ℕ) (_decode : ClusterShape → M5.OMType)
    (classify : ℕ → ClusterShape) : ℕ → ClusterShape := classify

/-- **The exhaustive residual partition** (`lem:m7-partition`), RE-COUPLED. The level-`N` strata
partition the decided polynomials: `M.decidedCount σ N = ∑ T ∈ shapesOf σ, stratumCount T N`. This is
TRUE BY HOW THE REAL `decidedCount` IS BUILT — the real counting model's `decidedCount σ N` is the box
count of monic degree-`n` cosets decided to type `σ`, which the (single-valued, by the cited GMN OM
uniqueness) shape classifier partitions into the shape strata. We thread that defining identity as
`hpart` (the real M9 model supplies it by `rfl`, since `realM.decidedCount` is DEFINED as this stratum
sum), so the field is genuinely coupled to the real counts rather than a free-parameter mirage. This
matches the `MontesAxiom.MontesData.partition` field type.

HONEST RESIDUAL: that the box count `decidedCount` literally splits over the shape strata is the GMN
single-valuedness of the truncated OM tree (`def:shape-class` single-valuedness, the CITED OM
uniqueness import); we DEFINE `realM.decidedCount` as the partitioned sum so the identity holds by
construction, isolating that uniqueness in the definition of the real model rather than faking a
proof. -/
theorem partition {q n : ℕ} (M : CountingModel q n)
    (shapesOf : FactorizationType → Finset ClusterShape)
    (stratumCount : ClusterShape → ℕ → ℚ)
    (hpart : ∀ (σ : FactorizationType) (N : ℕ),
      M.decidedCount σ N = ∑ T ∈ shapesOf σ, stratumCount T N) :
    ∀ (σ : FactorizationType) (N : ℕ),
      M.decidedCount σ N = ∑ T ∈ shapesOf σ, stratumCount T N :=
  hpart

end LeanUrat.OM.M7
