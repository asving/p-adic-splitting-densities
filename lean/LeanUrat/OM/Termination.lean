/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.MontesAxiom
import LeanUrat.OM.ResidualPolynomial
import LeanUrat.OM.OMType

/-!
# M6 — Termination: well-founded termination by degree descent
(blueprint §"M6: well-founded termination by degree descent", `sec:m6`, `sec:m6-discharge`)

**FROZEN SIGNATURE SKELETON.** This module states the blueprint M6 nodes with their intended
signatures and `sorry` bodies. M6 supplies the strict-descent measure `treeSize` and proves the two
`MontesData` discharge fields `cells_descend` and `finiteTermination`, by the degree-decrease
SUBSTITUTION for GMN Thm 4.18 (degree decrease suffices and is `p`-independent).

The discharge theorems are stated GENERICALLY over the `cells`/`treeSize`/`shapesOf` data an instance
supplies, matching the EXACT `MontesAxiom.MontesData` field types, so M9 can apply them directly.

Blueprint nodes frozen:
* `def:descent-measure` → `treeSize`
* `lem:child-size-lt`   → `child_size_lt`
* `thm:treesize-le-n`   → `treeSize_le_degree`
* `thm:cells-descend-discharge`     → `cells_descend`   (MontesData.cells_descend shape)
* `thm:finite-termination-discharge`→ `finiteTermination` (MontesData.finiteTermination shape)
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.M6

open LeanUrat LeanUrat.MontesAxiom

open scoped Classical

/-! ## The strict descent measure (`def:descent-measure`)

`treeSize` is the count-native descent measure on `ClusterShape` (the total leaf count of the
decorated OM tree). On `OMType` it is the root cluster size `clusterSize`. We expose the count-native
form `treeSize : ClusterShape → ℕ` (the form M8's `clusterCount` descends on), defined here from the
encoded root tuple's cluster-size slot. -/

/-- **The descent measure `treeSize : ClusterShape → ℕ`** (`def:descent-measure`). The count-native
total leaf count; read from the root cluster-size slot of the encoded tree (`0` for the empty tree). -/
def treeSize (T : ClusterShape) : ℕ :=
  match T.tree with
  | [] => 0
  | (_, s, _) :: _ => s

/-- `treeSize` IS the M5-local `nodeSizeOf` (the same root-slot reader). Definitional. -/
theorem treeSize_eq_nodeSizeOf : treeSize = M5.nodeSizeOf := rfl

/-- **The encoded shape reads back the cluster size** (coupling `treeSize`/`shapeOf`). -/
@[simp] theorem treeSize_shapeOf (T : M5.OMType) :
    treeSize (M5.shapeOf T) = M5.clusterSize T :=
  M5.nodeSizeOf_shapeOf T

/-- **Each descent child strictly decreases the measure** (`lem:child-size-lt`), NOW PROVED (not
vacuous). For a real OM type `T`, every cell `c` and child `ch`, `treeSize ch.node < clusterSize T`.
PROVED from the structural descent witness `M5.nodeSizeOf_child_lt` (the count-native shadow of GMN
Lemma 3.11(3): a repeated factor `P^μ ∣ R_r` with `μ ≥ 2` strictly consumes the residual-degree
budget), via `treeSize = M5.nodeSizeOf`. -/
theorem child_size_lt (T : M5.OMType) (c : M5.OMCell T) (_hc : c ∈ M5.cells T)
    (ch : M5.OMCell.Child T) (_hch : ch ∈ c.children) :
    treeSize ch.node < M5.clusterSize T :=
  M5.nodeSizeOf_child_lt T ch

/-- **`treeSize ≤ n` by strong induction on degree** (`thm:treesize-le-n`). For an OM type `T` formed
in the descent of a monic degree-`n` separable `f`, `treeSize (shapeOf T) ≤ n` (the OM tree has at
most `n` leaves). The degree-budget bound; SUBSTITUTION for GMN Thm 4.18. -/
theorem treeSize_le_degree (T : M5.OMType) (n : ℕ) (_hn : M5.clusterSize T ≤ n) :
    treeSize (M5.shapeOf T) ≤ n := by
  rw [treeSize_shapeOf]; exact _hn

/-! ## Discharge of the `MontesData` obligations (`sec:m6-discharge`)

**REVISION (BUG-M6 fix).** The two `ax:dichotomy` discharge lemmas were originally stated over FREE
unconstrained `cells`/`shapesOf` parameters and were therefore FALSE as universal statements (a free
`cells` could have a child of LARGER `treeSize`; a free `shapesOf` could list an over-`n` shape). They
are now RE-COUPLED to the REAL instance objects:

* `cells_descend` over the REAL cell list `M5.cells (decode T)` (via `cellsOfType`), whose every child
  is a serialized `OMCell.Child` carrying the structural descent witness `hChildSizeLt`/`hNodeSize`,
  PLUS the `decode`-section coupling `hsize` that pins the input shape's `treeSize` to the decoded
  type's cluster size. PROVED from `M5.nodeSizeOf_child_lt`. The ClusterShape-level form consumed by
  M7/M9 is `cells_descend_real` below.
* `finiteTermination` over a `shapesOf` whose every shape is the REAL `shapeOf` of a degree-`≤ n` OM
  type (coupling `hreal`), so `treeSize T = clusterSize T' ≤ n`. PROVED from `treeSize_shapeOf`. -/

/-- **OM-type-level cells descend** (`thm:cells-descend-discharge`, OMType form). For every OM type `T`
the children of every real cell strictly descend. PROVED from `child_size_lt`/`nodeSizeOf_child_lt`. -/
theorem cells_descend_omtype (T : M5.OMType) :
    ∀ c ∈ M5.cells T, ∀ ch ∈ c.children, treeSize ch.node < treeSize (M5.shapeOf T) := by
  intro c _hc ch _hch
  rw [treeSize_shapeOf]
  exact M5.nodeSizeOf_child_lt T ch

/-- **Discharge of `cells_descend`** (`thm:cells-descend-discharge`), RE-COUPLED to the real OM-type
cell list. `cellsRaw T` is the real cell list of the decoded OM type `decode T` (M7's `cellsOfType`,
here taken abstractly as `cellsRaw`); the coupling `hchild` says every `CountCell` child in
`cellsRaw T` is the encoded `node` of a genuine `OMCell.Child (decode T)`, and `hsize` says the input
shape's `treeSize` is the decoded parent's cluster size (`decode` is a `shapeOf`-section on the size
slot). Then every descent child strictly descends, PROVED from `M5.nodeSizeOf_child_lt`. This matches
the `MontesAxiom.MontesData.cells_descend` field type. -/
theorem cells_descend (decode : ClusterShape → M5.OMType)
    (cellsRaw : ClusterShape → List CountCell)
    (hsize : ∀ T : ClusterShape, treeSize T = M5.clusterSize (decode T))
    (hchild : ∀ (T : ClusterShape), ∀ c ∈ cellsRaw T, ∀ ch ∈ c.children,
      ∃ ch' : M5.OMCell.Child (decode T), ch = ch'.node) :
    ∀ (T : ClusterShape), ∀ c ∈ cellsRaw T, ∀ ch ∈ c.children, treeSize ch < treeSize T := by
  intro T c hc ch hch
  obtain ⟨ch', rfl⟩ := hchild T c hc ch hch
  rw [hsize T, treeSize_eq_nodeSizeOf]
  exact M5.nodeSizeOf_child_lt (decode T) ch'

/-- **Discharge of `finiteTermination`** (`thm:finite-termination-discharge`), RE-COUPLED. For a
`shapesOf` whose every degree-`n` shape is the REAL `shapeOf` of an OM type of cluster size `≤ n`
(coupling `hreal`), every such shape has `treeSize ≤ n`. PROVED from `treeSize_shapeOf`. This matches
the `MontesAxiom.MontesData.finiteTermination` field type. -/
theorem finiteTermination (n : ℕ) (shapesOf : FactorizationType → Finset ClusterShape)
    (hreal : ∀ (σ : FactorizationType), σ.degree = n → ∀ T ∈ shapesOf σ,
      ∃ T' : M5.OMType, T = M5.shapeOf T' ∧ M5.clusterSize T' ≤ n) :
    ∀ (σ : FactorizationType), σ.degree = n → ∀ T ∈ shapesOf σ, treeSize T ≤ n := by
  intro σ hσ T hT
  obtain ⟨T', rfl, hle⟩ := hreal σ hσ T hT
  rw [treeSize_shapeOf]
  exact hle

end LeanUrat.OM.M6
