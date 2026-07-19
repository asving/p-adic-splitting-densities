/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.MontesAxiom
import LeanUrat.L4
import LeanUrat.OM.NewtonPolygon
import LeanUrat.OM.ResidualPolynomial

/-!
# M5 — OMType: the order-`r` OM type, cluster size, cells, and the shape encoder
(blueprint §"M5: the order-`r` OM type", `sec:m5`; GAP 2 `def:shape-of-type`)

**FROZEN SIGNATURE SKELETON.** This module states the blueprint M5 nodes with their intended
signatures and `sorry`/`structure` bodies. The recursion of the OM tree is carried by the cell
children, which (matching `MontesAxiom.CountCell.children : List ClusterShape`, the count-native index
M7/M8 actually consume) are encoded `ClusterShape`s; the rich `OMType` carries the order-`r` residual
data with the A0 ties.

Blueprint nodes frozen:
* `def:residue-tower`   → `ResidueTower`
* `lem:card-Fr`         → `card_Fr`
* `def:om-type`         → `OMType` (the A0 ties `hResidueDeg`, `hResidualDeg` as proof fields)
* `def:cluster-size`    → `clusterSize`
* `def:om-cell-child`   → `OMCell.Child`
* `def:om-cell`         → `OMCell` (the leaf/descent dichotomy via `isLeaf`/`needsDescent`)
* `lem:descend-of-factors` → `descend_children_of_factors`
* `def:shape-of-type` (GAP 2) → `shapeOf` (+ `encodeTree`)
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.M5

open Polynomial LeanUrat LeanUrat.MontesAxiom

open scoped Classical

/-! ## The residue-field tower (`def:residue-tower`)

A finite residue tower with base `F₀ = F_q` and top `F_r`, the single base/top pair consumed
downstream (mirroring `PadicMeasure.OMShape.{baseField, Fr}`), with `δ := [F_r : F₀]`. -/

/-- **A finite residue tower** of order `r`: base field `F₀`, top field `F_r`, a genuine
`Algebra F₀ F_r`, both finite fields, with `δ := Module.finrank F₀ F_r`. -/
structure ResidueTower where
  /-- The OM order `r`. -/
  order : ℕ
  /-- The base residue field `F₀ = F_q`. -/
  F0 : Type
  /-- The top residue field `F_r`. -/
  Fr : Type
  [field_F0 : Field F0]
  [finite_F0 : Finite F0]
  [field_Fr : Field Fr]
  [finite_Fr : Finite Fr]
  [alg : Algebra F0 Fr]
  /-- The composite degree `δ = [F_r : F₀]`. -/
  δ : ℕ
  /-- A0 tie: `δ` is the genuine extension degree. -/
  hδ : δ = Module.finrank F0 Fr

attribute [instance] ResidueTower.field_F0 ResidueTower.finite_F0 ResidueTower.field_Fr
  ResidueTower.finite_Fr ResidueTower.alg

/-- **Residue-field cardinality is a `q`-power** (`lem:card-Fr`). For a tower with base of cardinality
`q` and `δ = [F_r : F₀]`, `Nat.card F_r = q^δ`. -/
theorem card_Fr (tw : ResidueTower) (q : ℕ) (hq : Nat.card tw.F0 = q) :
    Nat.card tw.Fr = q ^ tw.δ := by
  rw [Module.natCard_eq_pow_finrank (K := tw.F0) (V := tw.Fr), hq, tw.hδ]

/-! ## The order-`r` OM type (`def:om-type`)

`OMType` bundles the tower, the (degree of the) key polynomial `φ_r`, the order-`r` lattice Newton
polygon `N_r`, the residual `R_r ∈ F_r[Y]`, the degrees `δ, d_r`, and the cluster size `cs`, with the
A0 ties enforced as proof fields. The residue field `Fr` is carried as a structure field (a `Type`),
following `LeanUrat.OMType` in `Interface.lean`. -/

/-- **An order-`r` OM type.** Carries the residue tower data flattened in (base `F0`, top `Fr`,
`Algebra`), the order-`r` lattice Newton polygon `N_r`, the residual `R_r ∈ F_r[Y]`, the degrees
`δ, d_r`, the key-polynomial degree `keyDeg = m_r`, and the cluster size `cs`, with the two A0 ties. -/
structure OMType where
  /-- The OM order `r`. -/
  order : ℕ
  /-- The base residue field `F₀ = F_q`. -/
  F0 : Type
  /-- The order-`r` residue field `F_r`. -/
  Fr : Type
  [field_F0 : Field F0]
  [finite_F0 : Finite F0]
  [field_Fr : Field Fr]
  [finite_Fr : Finite Fr]
  [alg : Algebra F0 Fr]
  /-- The residue-extension degree `δ`. -/
  δ : ℕ
  /-- The order-`r` lattice Newton polygon `N_r` (reuses `L4.LatticePolygon`, the M3 bridge). -/
  Nr : L4.LatticePolygon
  /-- The order-`r` residual polynomial `R_r ∈ F_r[Y]`. -/
  Rr : Fr[X]
  /-- The residual degree `d_r`. -/
  dr : ℕ
  /-- The key-polynomial degree `m_r = m_{r-1} e_{r-1} f_{r-1}` (only its degree is used). -/
  keyDeg : ℕ
  /-- The cluster size `cs(T)` (the well-founded descent measure). -/
  cs : ℕ
  /-- **A0 tie `hResidueDeg`**: `δ = Module.finrank F₀ F_r`. -/
  hResidueDeg : δ = Module.finrank F0 Fr
  /-- **A0 tie `hResidualDeg`**: `d_r = R_r.natDegree`. -/
  hResidualDeg : dr = Rr.natDegree
  /-- **Size law `hDrLeCs` (Phase-A fix A1, 2026-07-02): `d_r ≤ cs`.**

  REPLACES the former STRICT field `hDrLtCs : 0 < dr → dr < cs`, which was SEMANTICALLY WRONG at the
  ROOT node: for a generic `f` (unit constant coefficient) the order-0 Newton polygon is the single
  flat side and the residual is `f̄` itself, so `d_r = n = cs` — the strict law FAILED exactly at the
  generic root, and forcing it is what created the `rootResidual` degree GUARD that zeroed the generic
  residual (the V1 vacuity chain, `notes/VACUITY_SIGMA_BLUEPRINT.md` §1.1-§1.2). The genuine GMN
  content is: the residual degree never exceeds the cluster size (`d_r ≤ cs`, this field), while
  STRICTNESS is a per-DESCENT-CHILD fact (GMN Lemma 3.11(3)) now carried where it belongs — as the
  `hChildSizeLt` witness of each emitted `OMCell.Child`, with the same-size refinement (the
  totally-clustered `ψ^μ` consuming the whole budget) EXCLUDED from the child list and absorbed into
  the self-loop pivot `countPivot` (the L5fix geometric resummation), exactly as the GLUE-1 self-loop
  split anticipates. Carried as a proof FIELD — a hypothesis the recursion maintains, GMN-content not
  Lean-proved — an honest footprint addition, NOT a free axiom or a conclusion. -/
  hDrLeCs : dr ≤ cs

attribute [instance] OMType.field_F0 OMType.finite_F0 OMType.field_Fr OMType.finite_Fr OMType.alg

/-- **Cluster size = residual multiplicity** (`def:cluster-size`). The cluster size of an `OMType` is
its carried `cs` field. -/
def clusterSize (T : OMType) : ℕ := T.cs

/-- **Count-native size of a `ClusterShape`** (the M5-local copy of the descent measure, identical to
`M6.treeSize`). Reads the root cluster-size slot of the encoded tree. Defined here so the OM-cell
children can carry their structural descent witness without forward-referencing M6. -/
def nodeSizeOf (T : ClusterShape) : ℕ :=
  match T.tree with
  | [] => 0
  | (_, s, _) :: _ => s

/-! ## The OM cell and its descent children (`def:om-cell`, `def:om-cell-child`)

An OM cell carries one Newton-polygon face × one residual stratum `S ∣ R_r`, with descent children.
The children are encoded `ClusterShape`s (the count-native index the recursion descends on, matching
`MontesAxiom.CountCell.children`); each carries its descent witness `(P, μ)` as data. -/

/-- **A descent child** of an `OMType` `T` (`def:om-cell-child`, GMN Lemma 3.11(3)): a repeated
residual factor `P^μ ∣ R_r` with `μ ≥ 2`, the child's encoded shape `node`, and the size tie
`cs(node) = μ` recorded against the count-native `treeSize`. -/
structure OMCell.Child (T : OMType) where
  /-- The child's count-native shape index. -/
  node : ClusterShape
  /-- The repeated residual factor `P ∈ F_r[Y]`. -/
  P : T.Fr[X]
  /-- The multiplicity `μ`. -/
  μ : ℕ
  /-- `2 ≤ μ` (descent fires only at multiplicity `≥ 2`). -/
  hμ : 2 ≤ μ
  /-- `P^μ ∣ R_r`. -/
  hdvd : P ^ μ ∣ T.Rr
  /-- The count-native size of the child, in DEGREE units (Phase-A decision A2, 2026-07-02):
  the child cluster consumes `μ·deg P` of the parent's degree budget. -/
  childSize : ℕ
  /-- `childSize = μ·deg P` (degree units — the convention under which the GLUE-2 degree-budget
  tiling `∑_c (δ·dS + ∑_ch childSize) = cs` can close; the former `childSize = μ` multiplicity-only
  convention could not tile for `deg ψ > 1`). -/
  hcs : childSize = μ * P.natDegree
  /-- **Count-native size tie**: the encoded child node's size slot IS `childSize`, so
  `nodeSizeOf node = childSize` (the child shape was serialized with its own cluster size in the root
  slot). -/
  hNodeSize : nodeSizeOf node = childSize
  /-- **STRUCTURAL STRICT DESCENT** (`lem:child-size-lt`, count shadow of `descend_size_lt`): the
  child's count-native size is strictly below the parent cluster size. This is the well-foundedness
  witness carried by every real descent child (GMN Lemma 3.11(3): a repeated factor `P^μ ∣ R_r` with
  `μ ≥ 2` consumes `μ·deg P ≤ d_r < clusterSize` of the residual degree budget). -/
  hChildSizeLt : childSize < clusterSize T

/-- **An OM cell** (`def:om-cell`): one order-`r` Newton-polygon face (`polygon`) carrying one residual
stratum `S ∣ R_r` of degree `dS`, together with its descent children. The leaf/descent dichotomy:
`children = []` for a multiplicity-1 (leaf) stratum, nonempty for a multiplicity-`≥2` (descend)
stratum. -/
structure OMCell (T : OMType) where
  /-- The order-`r` Newton-polygon face (the M3 lattice face). -/
  polygon : L4.LatticePolygon
  /-- The residual stratum `S ∣ R_r`. -/
  S : T.Fr[X]
  /-- `S ∣ R_r` (cells are strata OF the real residual). -/
  hSdvd : S ∣ T.Rr
  /-- The residual-stratum degree `d_S`. -/
  dS : ℕ
  /-- `d_S = S.natDegree`. -/
  hdS : dS = S.natDegree
  /-- The descent children of this cell. -/
  children : List (OMCell.Child T)

/-- **The genuine cells of an OM type** (`def:om-cell`, the KEYSTONE body, resolution (i) of the
single-face structural gap). The cells of `T` are computed from `T` ALONE (the upstream `classifyAux`
already selected the side `S`, set `T.Nr := toSideFace S` and `T.Rr := residualPoly (boxCoeffData… S)`,
so `M5.cells` factors that ONE residual): one cell per distinct monic-irreducible factor `ψ` of `T.Rr`,
using `T.Nr` directly as the (already-side-selected) cell polygon, with the leaf/descend dichotomy
`children = []` for a multiplicity-1 (separable) factor and a single descent `Child` for a
multiplicity-`≥2` (repeated) factor that consumes STRICTLY LESS than the whole cluster budget
(`μ·deg ψ < cs` — the `if` guard IS the well-foundedness witness `hChildSizeLt`); the full-budget
repeated factor (`μ·deg ψ = cs`, the totally-clustered case) is the SELF-LOOP, deliberately not a
child, absorbed into `countPivot` (Phase-A A2 — replaces the old route through the deleted strict
root law `hDrLtCs`). NEITHER `boxCoeffData` NOR `f` appears: they build `T.Rr`/`T.Nr` upstream (B.3). -/
noncomputable def cells (T : OMType) : List (OMCell T) :=
  let fact : M4.ResidualFactorization T.Rr := Classical.choice (M4.factorize_any T.Rr)
  -- (Phase-A A5 canonicalization, 2026-07-02) the factor list is SORTED by factor degree before the
  -- cell map: `Finset.toList` order is representative-dependent, so without the sort two polynomials
  -- with the SAME factor-degree pattern λ could emit payload/tree lists in different orders and land
  -- in DIFFERENT `ClusterShape`s, fragmenting the λ-stratum (menu shapes must depend only on λ).
  -- After erasure, same-degree separable cells are EQUAL, so degree-sorting fully canonicalizes the
  -- Phase-A (separable/leaf) payloads; ties among non-separable same-degree cells with distinct
  -- children are the documented Phase-B canonicalization obligation. `clusterCount` sums are
  -- order-invariant, so coefficients are unaffected.
  ((fact.factors.attach.toList.mergeSort
      (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map (fun ⟨ψ, hψf⟩ =>
    let μ : ℕ := fact.mult ψ
    have hψμR : ψ ^ fact.mult ψ ∣ T.Rr := by
      have hdvdprod : ψ ^ fact.mult ψ ∣ ∏ φ ∈ fact.factors, φ ^ fact.mult φ :=
        Finset.dvd_prod_of_mem (fun φ => φ ^ fact.mult φ) hψf
      exact (hdvdprod.mul_left _).trans (dvd_of_eq fact.prod_eq.symm)
    have hψR : ψ ∣ T.Rr :=
      dvd_trans (dvd_pow_self ψ (by have := fact.mult_pos ψ hψf; omega)) hψμR
    { polygon := T.Nr
      S := ψ
      hSdvd := hψR
      dS := ψ.natDegree
      hdS := rfl
      children :=
        -- (Phase-A A2, 2026-07-02) SELF-LOOP-AWARE descent: a repeated factor (`μ ≥ 2`) emits a
        -- descent child ONLY when it consumes strictly less than the whole cluster budget
        -- (`μ·deg ψ < cs`); the same-size refinement (`μ·deg ψ = cs`, the totally-clustered case,
        -- e.g. `R_r = ψ^μ` a full-budget prime power) is the SELF-LOOP — deliberately NOT a child,
        -- absorbed into the geometric pivot `countPivot (treeSize T)` (L5fix resummation; this is
        -- the same-size order-increase chain the GLUE-1 self-loop term models). Note
        -- `μ·deg ψ ≤ ∑ mult·deg = d_r ≤ cs` (`degree_budget` + `hDrLeCs`), so the only excluded
        -- case IS the full-budget one; strict descent for emitted children is the `if` guard
        -- itself (no longer routed through the deleted strict root law `hDrLtCs`).
        if hμ : 2 ≤ μ then
          if hlt : fact.mult ψ * ψ.natDegree < clusterSize T then
            [{ node := ⟨[(T.order + 1, fact.mult ψ * ψ.natDegree, 0)], []⟩
               P := ψ, μ := μ, hμ := hμ, hdvd := hψμR
               childSize := fact.mult ψ * ψ.natDegree, hcs := rfl
               hNodeSize := by simp [nodeSizeOf]
               hChildSizeLt := hlt }]
          else []
        else [] }))

/-- **Descent children carry repeated factors (projection)** (`lem:descend-of-factors`). For every
`T`, every cell `c ∈ cells T` and every child `ch ∈ c.children` there exist `P` and `μ` with `2 ≤ μ`,
`P^μ ∣ R_r`, and `ch.childSize = μ·deg P` (degree units, Phase-A A2).

⚠ **HONEST SCOPE (audit F3a, 2026-07-03).** This is a mere FIELD PROJECTION out of the
`OMCell.Child` data (`⟨ch.P, ch.μ, ch.hμ, ch.hdvd, ch.hcs⟩`): it certifies that every child that
WAS emitted carries a genuine repeated-factor witness. It is NOT an emission certificate — it does
NOT say that every repeated factor `ψ^μ ∣ R_r` with `μ ≥ 2` IS emitted as a child. Under the A2
self-loop split, `cells` deliberately emits NO child for a full-budget repeated factor
(`μ·deg ψ = cs`, absorbed into `countPivot`). The budget dichotomy making that exclusion exhaustive
is `mult_deg_le_clusterSize` / `not_emitted_imp_eq_cs` below: a factor NOT passing the emission
guard `μ·deg ψ < cs` necessarily has `μ·deg ψ = cs` — there is no third case. -/
theorem descend_children_of_factors (T : OMType) (c : OMCell T) (_hc : c ∈ cells T)
    (ch : OMCell.Child T) (_hch : ch ∈ c.children) :
    ∃ (P : T.Fr[X]) (μ : ℕ), 2 ≤ μ ∧ P ^ μ ∣ T.Rr ∧ ch.childSize = μ * P.natDegree :=
  ⟨ch.P, ch.μ, ch.hμ, ch.hdvd, ch.hcs⟩

/-- **The per-factor degree budget** (audit F3a; the inline pattern of
`LevelNCount.perNode_tiling_of_zeroResidual` promoted to a named lemma). For ANY factorization
`fact` of `T.Rr` (in particular the `Classical.choice (M4.factorize_any T.Rr)` chosen inside
`cells`) and any factor `ψ ∈ fact.factors`, the factor's budget consumption is bounded by the
cluster size: `fact.mult ψ * ψ.natDegree ≤ clusterSize T`. Chain: `Finset.single_le_sum` into the
factorization's `degree_budget` (`∑ mult·deg = Rr.natDegree`), then the A0 tie `hResidualDeg`
(`dr = Rr.natDegree`) and the Phase-A size law `hDrLeCs` (`dr ≤ cs`). PROVED, no axiom. -/
theorem mult_deg_le_clusterSize (T : OMType) (fact : M4.ResidualFactorization T.Rr)
    (ψ : T.Fr[X]) (hψ : ψ ∈ fact.factors) :
    fact.mult ψ * ψ.natDegree ≤ clusterSize T :=
  calc fact.mult ψ * ψ.natDegree
      ≤ ∑ φ ∈ fact.factors, fact.mult φ * φ.natDegree :=
        Finset.single_le_sum (f := fun φ => fact.mult φ * φ.natDegree)
          (fun _ _ => Nat.zero_le _) hψ
    _ = T.Rr.natDegree := fact.degree_budget
    _ = T.dr := T.hResidualDeg.symm
    _ ≤ clusterSize T := T.hDrLeCs

/-- **The not-emitted dichotomy** (audit F3a, corollary). A factor NOT emitted as a descent child —
i.e. one failing the `μ·deg ψ < cs` emission guard of `cells` — consumes EXACTLY the whole budget:
`fact.mult ψ * ψ.natDegree = clusterSize T`. This is the precise sense in which the A2 self-loop
exclusion is exhaustive: a `μ ≥ 2` factor is either a genuine strictly-descending emitted child or
the full-budget self-loop (`μ·deg ψ = cs`, the totally-clustered case absorbed into `countPivot`) —
no third case. (The `2 ≤ μ` hypothesis is not needed for the arithmetic, which holds for every
factor; the `μ ≥ 2` reading is where the guard is actually consulted in `cells`.) PROVED, no
axiom. -/
theorem not_emitted_imp_eq_cs (T : OMType) (fact : M4.ResidualFactorization T.Rr)
    (ψ : T.Fr[X]) (hψ : ψ ∈ fact.factors)
    (hnot : ¬ fact.mult ψ * ψ.natDegree < clusterSize T) :
    fact.mult ψ * ψ.natDegree = clusterSize T :=
  Nat.le_antisymm (mult_deg_le_clusterSize T fact ψ hψ) (Nat.le_of_not_lt hnot)

/-- **Per-child strict descent of the count-native size** (`lem:child-size-lt`, COUPLED). For every
descent child `ch` of an OM type `T`, the child node's count-native size is strictly below the parent
cluster size: `nodeSizeOf ch.node < clusterSize T`. PROVED from the structural witnesses
`hNodeSize` (`nodeSizeOf node = childSize`) and `hChildSizeLt` (`childSize < clusterSize T`). This is
the genuine well-foundedness fact, no longer vacuous. -/
theorem nodeSizeOf_child_lt (T : OMType) (ch : OMCell.Child T) :
    nodeSizeOf ch.node < clusterSize T := by
  rw [ch.hNodeSize]; exact ch.hChildSizeLt

/-! ## GAP 2: the shape encoder `shapeOf : OMType → ClusterShape` (`def:shape-of-type`)

Serializes a real OM type into the opaque count-native index `ClusterShape` (`tree : List (ℕ×ℕ×ℕ)`),
the pre-order traversal of the decorated OM tree: the root contributes `(order, clusterSize, dr)`,
followed by the encoded child subtrees. -/

/-- The pre-order encoding of an OM type's decorated tree (`def:shape-of-type`). Root tuple
`(order, clusterSize, dr)` followed by the concatenated child subtrees. For the skeleton the child
recursion (whose well-foundedness is by `clusterSize` descent) is encoded via the already-serialized
child `node` shapes. -/
noncomputable def encodeTree (T : OMType) : List (ℕ × ℕ × ℕ) :=
  (T.order, clusterSize T, T.dr) ::
    ((cells T).flatMap (fun c => c.children.flatMap (fun ch => ch.node.tree)))

/-- **The faithful per-node cell payload of an OM type** (decision 2b). Erases each genuine
`OMCell T` to a `ShapeCell` carrying its residual-stratum degree `dS`, the residue-extension degree
`δ` (= `T.δ`), the lattice Newton-polygon face `polygon`, and the descent children as their
already-serialized `node` shapes. This is exactly the data `M7.cellsOfType` reads back into a genuine
`MontesAxiom.CountCell`, so `shapeOf` is lossless: the enriched `cells` field IS the cell list. -/
noncomputable def encodeCells (T : OMType) : List ShapeCell :=
  (cells T).map (fun c =>
    ({ dS := c.dS, δ := T.δ, polygon := c.polygon,
       children := c.children.map (fun ch => ch.node) } : ShapeCell))

/-- **The shape encoder** `shapeOf : OMType → ClusterShape` (`def:shape-of-type`, GAP 2). Serializes
the decorated OM tree into the count-native index, populating BOTH the count-native `tree` slot list
(unchanged, for the descent-measure read-back) AND the faithful per-node cell payload `encodeCells T`
(decision 2b), so reconstruction is lossless. -/
noncomputable def shapeOf (T : OMType) : ClusterShape :=
  { tree := encodeTree T, cells := encodeCells T }

/-- **The encoded shape reads back the cluster size** (the coupling between `shapeOf` and the
count-native `nodeSizeOf`/`treeSize`). By construction `encodeTree T` has root tuple
`(order, clusterSize T, dr)`, so `nodeSizeOf (shapeOf T) = clusterSize T`. -/
@[simp] theorem nodeSizeOf_shapeOf (T : OMType) : nodeSizeOf (shapeOf T) = clusterSize T := by
  rfl

end LeanUrat.OM.M5
