/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.CountingModel
import LeanUrat.MontesAxiom
import LeanUrat.Decomposition
import LeanUrat.Goal
import LeanUrat.OM.ResidualPolynomial
import LeanUrat.OM.QuotientBox
import LeanUrat.OM.OMType
import LeanUrat.OM.Termination
import LeanUrat.OM.CellPartition
import LeanUrat.OM.LevelNCount
import LeanUrat.OM.Classifier
import LeanUrat.OM.LimitSpine

/-!
# M9 — RealInstance: shared real-instance primitives
(blueprint §"M9 — RealInstance", `subsec` M9; GAP 2 `def:decode`)

**ROLE CHANGE (2026-07-21, blueprint W4a).** This module used to assemble the old real
`CountingModel`/`MontesData`/`DensityFoundation` triple (`realM`/`realD`/`realF`) and fire the old
capstone `montes_unconditional` via the axiom `realDensity_tame_functionalEquation`. That chain was
VACUOUS (order-0 decode ≡ 0, σ-independent) and is RETIRED to
`quarantine/RealInstance_oldCapstone_2026-07-21.lean.txt`; the all-orders capstone is now
`RealInstanceV2.montes_unconditional` (`OM/RealInstanceV2.lean`), per
`notes/M9_REBASE_BLUEPRINT_2026-07-19.md` (see the in-file tombstone below for the full record).

What REMAINS here are the shared real-instance primitives consumed across the tree
(`ClassifierBridge*`, `ConditionalDensity`, `Order0*`, `RealInstanceV2Prep`, `RealInstanceV2`, ...):
* `realP` — the real residue prime (`2`) + its `Fact (Nat.Prime realP)` instance;
* `realClassify` — the genuine `N`-truncated OM shape classifier `B.classify realP n`;
* `rawCount` — the genuine `Nat.card` shape-fiber counts over M1's `monicBox`
  (`M8.shapeFiberCount realP n (realClassify n)`);
* `leafOMTypeOfSize`/`leafOMType` + the `Nonempty M5.OMType` instance;
* `decode`/`decode_treeSize` — retained only as the PROVED order-0 rebuild witness (the V2 chain
  reads per-shape payloads directly; see `decode`'s docstring).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.M9

open Polynomial LeanUrat LeanUrat.CountingModel LeanUrat.MontesAxiom

open scoped Classical

/-! ## Fixed parameters of the real instance

For a fixed `K/ℚ_p` with residue cardinality `q = p^{f_K}` and degree `n`. We carry `(q, n)` and the
hypothesis `2 ≤ q` as a section variable bundle. -/

variable (q n : ℕ) (hq : 2 ≤ q)

/-! ## GAP 2 — the decoder `decode : ClusterShape → OMType` (`def:decode`)

Rebuilds an OM type from the serialized tree. On the realizable image it is a genuine section of
`M5.shapeOf`; off it, junk. Carried opaquely for the skeleton. -/

/-- **A size-parameterized order-0 leaf `OMType` witness** (`def:decode`, the ORDER-0 leaf rebuild).
Built over the base/order-`r` residue field `ZMod 2` (a finite field), with the trivial Newton polygon
(width 0), zero residual polynomial, and ALL OM-order slots `0` EXCEPT the cluster size `cs := s`,
which is carried as the parameter. The two A0 ties hold INDEPENDENTLY of `s` (they constrain `δ`/`dr`,
not `cs`): `δ = 1 = finrank (ZMod 2) (ZMod 2)` (`Module.finrank_self`) and
`dr = 0 = (0 : (ZMod 2)[X]).natDegree` (`Polynomial.natDegree_zero`). This is the genuine ORDER-0 leaf
OM type of cluster size `s`: order `0` (no descent — the Newton polygon is trivial, the residual is
separable), so the OM tree is a single leaf, and its only nontrivial datum is the cluster size. -/
noncomputable def leafOMTypeOfSize (s : ℕ) : M5.OMType where
  order := 0
  F0 := ZMod 2
  Fr := ZMod 2
  δ := 1
  Nr := ⟨0, fun i => 0, fun i => false⟩
  Rr := 0
  dr := 0
  keyDeg := 0
  cs := s
  hResidueDeg := by simp [Module.finrank_self]
  hResidualDeg := by simp
  hDrLeCs := Nat.zero_le _

/-- **A concrete order-0 leaf `OMType` witness** (the inhabitedness of `M5.OMType`), the size-`0`
specialization `leafOMTypeOfSize 0`. DISCHARGES the `Nonempty M5.OMType` obligation with a genuine
concrete OM type (no `sorry`). -/
noncomputable def leafOMType : M5.OMType := leafOMTypeOfSize 0

/-- **`M5.OMType` is inhabited** (the concrete order-0 leaf `leafOMType` witnesses it). DISCHARGES the
`Nonempty M5.OMType` obligation that `decode` previously carried as a `sorry`. -/
instance : Nonempty M5.OMType := ⟨leafOMType⟩

/-- **The decoder** `decode : ClusterShape → OMType` (`def:decode`, GAP 2), the ORDER-0 PROTOTYPE.
Rebuilds an `OMType` from the serialized `ClusterShape.tree`. For the order-0 prototype the rebuild is
the ORDER-0 leaf OM type whose cluster size is the shape's root size slot `M6.treeSize T`
(`leafOMTypeOfSize (M6.treeSize T)`): an order-0 cluster shape IS a leaf (trivial Newton polygon /
separable residual, no descent), and the genuine decode rebuilds exactly that leaf OM type, carrying the
root cluster size across. This is no longer the OPAQUE `Classical.choice` placeholder: it is a CONCRETE,
treeSize-PRESERVING section on the order-0 (leaf) image, making the GAP-2 decode coupling
`decode_treeSize` a PROVED theorem (below). The genuine HIGHER-ORDER `rebuild` (parsing the full
decorated tree and re-attaching M4/M5 descent data for orders `≥ 1`) is the remaining GAP-2 content. -/
noncomputable def decode : ClusterShape → M5.OMType := fun T => leafOMTypeOfSize (M6.treeSize T)

/-- **The decoder is a `shapeOf`-section on the count-native size slot** (the GAP-2 decode coupling),
NOW PROVED for the ORDER-0 prototype. `M6.treeSize T = M5.clusterSize (decode T)`: the order-0 leaf
decoder rebuilds the leaf OM type whose cluster size IS the shape's root size slot, so `treeSize` is
preserved by construction. PROVED core-only: `M5.clusterSize (decode T) = (leafOMTypeOfSize (treeSize T)).cs
= treeSize T` definitionally (`M5.clusterSize T' = T'.cs`, `leafOMTypeOfSize s` has `cs := s`). This is
the well-foundedness coupling consumed by `M7.cells_descend`; it is the genuine GAP-2 decode-section
property, no longer a `sorry`. (For the higher-order genuine decoder the same identity is the leaf-size
preservation across the full tree rebuild.)

**(2026-07-21, W4a) Vestigial but PROVED.** The V2 capstone chain (`OM/RealInstanceV2.lean`) reads
per-shape payloads directly (`OMCountV2.omCount` over the σ-keyed `omMenu`) and does not consume
`decode`; `decode`/`decode_treeSize` are retained only as the order-0 rebuild witness. -/
theorem decode_treeSize : ∀ T : ClusterShape, M6.treeSize T = M5.clusterSize (decode T) :=
  fun _ => rfl

/-! ## The real raw counts (RE-COUPLED to the M1 box / M8 fiber count)

**REVISION (BUG-M9 fix).** The raw level-`N` counts are the GENUINE `Nat.card` shape-fiber counts
over M1's `monicBox(p, N, n)` (`M8.shapeFiberCount`), threaded through the genuine `N`-truncated
OM shape classifier `realClassify`. The V2 chain (`OM/RealInstanceV2.lean`) builds its decided counts
as menu-sums of these stratum counts, so its `partition` field holds by `rfl` — the count is
genuinely partitioned over the shape strata, not a free-parameter `0`. -/

/-- The residue characteristic `p` of the real instance (a fixed prime; `2` as a concrete witness so
the `Fact p.Prime` instance is discharged). The genuine instance fixes `p` from `K/ℚ_p`. -/
def realP : ℕ := 2

instance : Fact (Nat.Prime realP) := ⟨by unfold realP; norm_num⟩

/-- **The `N`-truncated OM shape classifier** (`def:shape-class`, the genuine M7 content). Maps a monic
degree-`n` coset mod `p^N` to the shape of its `N`-truncated OM tree. NOW THE GENUINE OM CLASSIFIER:
`B.classify realP n` (Classifier.lean:455), which runs the OM algorithm (`classifyAux`) on the lifted
root context and reads off the `N`-truncated tree shape. So `rawCount T N = M8.shapeFiberCount realP n
(realClassify n) T N = #{ f ∈ monicBox(realP,N,n) : B.classify realP n N f = T }` is the GENUINE box
fiber count (by `rfl`), no longer the constant `⟨[],[]⟩` stub. -/
noncomputable def realClassify : (N : ℕ) → QuotientBox.monicBox realP N n → ClusterShape :=
  B.classify realP n

/-- The raw per-shape level-`N` fiber count `#{ f ∈ monicBox(p,N,n) : classify f = T }` — the GENUINE
finite cardinality of the shape fiber over the M1 box (`M8.shapeFiberCount`), no longer a free `0`. -/
noncomputable def rawCount : ClusterShape → ℕ → ℕ :=
  M8.shapeFiberCount realP n (realClassify n)

/-! ## RETIRED: the old vacuous capstone chain (W4a, 2026-07-21)

The old menu/instance/capstone chain that lived here — `leafTypesUpTo`/`shapeMenu`/`shapesOf` (the
σ-discarding `if σ = σ₀` menu), the helper bank, `realM`/`realD`/`realF`, the `h_node` wiring
(`realStratum_tendsto_clusterCount`, `real_nodeMeasure_boxSum`, `real_h_node`), the AXIOM
`realDensity_tame_functionalEquation`, and the old capstone `montes_unconditional` — was VACUOUS
(order-0 decode ≡ 0, σ-independent; capstone conditional on false-for-the-instance hypotheses) and is
RETIRED, superseded by the corrected σ-keyed V2 chain in `LeanUrat/OM/RealInstanceV2.lean`
(`realM2`/`realD2`/`realF2`; capstones `montes_unconditional`/`montes_unconditional_exhaustive`) per
`notes/M9_REBASE_BLUEPRINT_2026-07-19.md` (W4; D4: the axiom is retired — the tame input is the V2
HYPOTHESIS `htameFE`, and the V2 capstone footprint is Lean core only). The excised source is
preserved verbatim in `quarantine/RealInstance_oldCapstone_2026-07-21.lean.txt`. -/

end LeanUrat.OM.M9
