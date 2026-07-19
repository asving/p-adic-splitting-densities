/-
Scratch module (S3, CHILDFUL FIBER BRIDGE): the childful analogue of
`ClassifierBridgeFiber2.classify_eq_selfloop_iff` — the fiber characterization of the genuine
order-0 classifier `B.classify` against `InCell` on the single-side, hlt-regime, μ ≥ 2 locus, PLUS
the omCount bridge tying the respell `TselfloopChildful` to `PathShapeChildful.oneSideShapeChildful`.

Namespace LeanUrat.OM.ClassifierBridgeChildful.  Math-first, no sorry/axiom/native_decide.

SCOPE (option (a) only): the fiber iff `B.classify f = TselfloopChildful ↔ InCell (childful mkCell)`
and the `stratumCount_childful_R` discharge.  We deliberately STOP before any density theorem (the
pivot-as-deeper-resummation obstacle, `MontesAllOrders.montes_allorders_of_hnode` requires
`limit = omCount`, which the childful shape violates: `limit = omCount / ∏ pivot`).

Key structural facts driving the build (see thread SCOPE):
* The classifier emits, per μ ≥ 2 factor passing the strict-descent guard `μ·deg < cs`, ONE
  `OMCell.Child` with node `⟨[(order+1, μ·deg, 0)], []⟩ = ⟨[(1, μ·D, 0)], []⟩` (root order 0);
  `encodeCells` records that node in the cell's `children`.  So the raw classify shape is
  `⟨(0,n,dr) :: (per-emitted-child [(1,μD,0)]), encodeCells⟩`.
* The child ctx `childCtxOfSize` has `Rr = 0`, whose ANY factorization has empty factors
  (`factorize_zero_factors_empty`), so its cells are empty ⇒ the child is CHILDLESS ⇒ the recursion
  terminates in ONE descent step (`classifyAux_of_single_descent`).
* `treeSize`/`nodeSizeOf` read the SIZE slot (slot 2), NOT the order slot; so the classifier child
  node `⟨[(1,μD,0)],[]⟩` and `PathShapeChildful.childShape = ⟨[(2,μD,0)],[]⟩` have identical
  `omChildCount` — the order-slot mismatch (RISK 3) is invisible to `omCount`.
* `hlt` regime (every μ ≥ 2 factor strictly descends, `μ·D < s`): no full-budget self-loop factor
  exists at order 1, so every μ ≥ 2 factor IS emitted ⇒ the emission is bijective (RISK 2 mitigation).
-/
import LeanUrat.OM.ClassifierBridgeFiber2
import LeanUrat.OM.ClassifierBridgeFiber
import LeanUrat.OM.ClassifierBridge
import LeanUrat.OM.PathShapeChildful
import LeanUrat.OM.Order0Classify
import LeanUrat.OM.Order0Alpha

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.ClassifierBridgeChildful

open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.PathShape
open LeanUrat.MontesAxiom (CountCell)

open scoped Classical

/-! ## 0. The `Rr = 0` child context is childless. -/

/-- **Any factorization of a zero-degree residual has empty factors.**  If `T.Rr.natDegree = 0`,
its `degree_budget` is `∑ mult·deg = 0`; every member has `mult ≥ 1` and (irreducible ⟹) `deg ≥ 1`,
so `mult·deg ≥ 1`; a nonempty factor set would force the sum `≥ 1`. -/
theorem factorize_factors_empty_of_natDegree_zero {kS : Type*} [Field kS] [Finite kS]
    {R : Polynomial kS} (hR : R.natDegree = 0) (fact : M4.ResidualFactorization R) :
    fact.factors = ∅ := by
  by_contra hne
  obtain ⟨ψ, hψ⟩ := Finset.nonempty_of_ne_empty hne
  have hbudget : ∑ φ ∈ fact.factors, fact.mult φ * φ.natDegree = R.natDegree :=
    fact.degree_budget
  rw [hR] at hbudget
  -- each term ≥ 1 for members ⟹ sum ≥ 1
  have hdegpos : 1 ≤ ψ.natDegree := by
    have hirr := fact.factors_irreducible ψ hψ
    have : ψ.natDegree ≠ 0 := by
      intro h0
      exact hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree hirr.ne_zero, h0]; rfl))
    omega
  have htermpos : 1 ≤ fact.mult ψ * ψ.natDegree :=
    Nat.one_le_iff_ne_zero.mpr (by
      have := fact.mult_pos ψ hψ
      positivity)
  have hle : fact.mult ψ * ψ.natDegree ≤ ∑ φ ∈ fact.factors, fact.mult φ * φ.natDegree :=
    Finset.single_le_sum (f := fun φ => fact.mult φ * φ.natDegree) (fun _ _ => Nat.zero_le _) hψ
  omega

/-- **The `Rr = 0` context has no cells.**  The `mergeSort`ed factor list of `M5.cells` is a `.map`
over `fact.factors.attach.toList`, which is `[]` because `fact.factors = ∅`
(`factorize_factors_empty_of_natDegree_zero`, `(childCtxOfSize).Rr = 0` has natDegree `0`).  We read
this off the LENGTH (avoiding a dependent-motive rewrite of `fact` inside the OMCell type). -/
theorem cells_childCtxOfSize (r s : ℕ) : M5.cells (B.childCtxOfSize r s) = [] := by
  rw [M5.cells]
  apply List.eq_nil_of_length_eq_zero
  rw [List.length_map, List.length_mergeSort]
  have hfac : (Classical.choice (M4.factorize_any (B.childCtxOfSize r s).Rr)).factors = ∅ :=
    factorize_factors_empty_of_natDegree_zero (by rfl) _
  rw [Finset.length_toList, Finset.card_attach, hfac, Finset.card_empty]

/-- The `Rr = 0` child context serializes to the single-tuple childless tree `⟨[(r, s, 0)], []⟩`. -/
theorem classifyAux_childCtxOfSize {p : ℕ} [Fact p.Prime] {N n : ℕ}
    (f : QuotientBox.monicBox p N n) (r s : ℕ) :
    B.classifyAux p N n s f (B.childCtxOfSize r s) rfl
      = ⟨[(r, s, 0)], M5.encodeCells (B.childCtxOfSize r s)⟩ := by
  rw [Order0.classifyAux_of_childless p N n s f (B.childCtxOfSize r s) rfl
      (fun c hc => absurd (by rw [cells_childCtxOfSize] at hc; exact hc) (List.not_mem_nil))]
  -- head tuple (order, clusterSize, dr) = (r, s, 0)
  rfl

/-- **The M5-emitted child node is `⟨[(order+1, childSize, 0)], []⟩`.**  Every descent child of every
cell of `M5.cells T` is emitted with node tree `[(T.order+1, μ·deg, 0)]` and `childSize = μ·deg`
(the `M5.cells` emission), so `ch.node.tree = [(T.order+1, ch.childSize, 0)]`.  Extracted by
unfolding `M5.cells` and inspecting the `dite`-guarded singleton child list. -/
theorem cells_child_node_tree (T : M5.OMType) (c : M5.OMCell T) (hc : c ∈ M5.cells T)
    (ch : M5.OMCell.Child T) (hch : ch ∈ c.children) :
    ch.node.tree = [(T.order + 1, ch.childSize, 0)] := by
  -- unfold membership: c is one of the mapped cells, its children is the dite-guarded singleton.
  rw [M5.cells, List.mem_map] at hc
  obtain ⟨⟨ψ, hψf⟩, _hmem, rfl⟩ := hc
  -- c.children is `if 2 ≤ μ then if μ·deg<cs then [child] else [] else []`.
  simp only at hch
  set μ := (Classical.choice (M4.factorize_any T.Rr)).mult ψ with hμdef
  by_cases hμ : 2 ≤ μ
  · by_cases hlt : (Classical.choice (M4.factorize_any T.Rr)).mult ψ * ψ.natDegree < M5.clusterSize T
    · rw [dif_pos hμ, dif_pos hlt, List.mem_singleton] at hch
      subst hch
      rfl
    · rw [dif_pos hμ, dif_neg hlt] at hch
      exact absurd hch (List.not_mem_nil)
  · rw [dif_neg hμ] at hch
    exact absurd hch (List.not_mem_nil)

/-! ## 1. `classifyAux_of_single_descent` — the ONE-step-recursion tree. -/

/-- **The single-descent recursion.**  When every child of every cell of `T` is a genuine descent
child whose sub-recursion terminates immediately (the child ctx `childCtxOfSize` has `Rr = 0` and is
childless, `classifyAux_childCtxOfSize`), `classifyAux` at `T` serializes to `shapeOf T =
⟨encodeTree T, encodeCells T⟩`: each child subtree `(classifyAux ch.childSize (childCtxOfSize
(order+1) ch.childSize)).tree` collapses to `[(order+1, ch.childSize, 0)] = ch.node.tree` (the M5
child node), so the tree flatMap is EXACTLY `encodeTree`'s tail.  No squarefree/childless-cell
hypothesis is needed — the descent is one step deep for ANY residual, because the child context is
`Rr = 0`. -/
theorem classifyAux_of_single_descent {p : ℕ} [Fact p.Prime] {N n : ℕ} (budget : ℕ)
    (f : QuotientBox.monicBox p N n) (T : M5.OMType) (hT : M5.clusterSize T = budget) :
    B.classifyAux p N n budget f T hT = ⟨M5.encodeTree T, M5.encodeCells T⟩ := by
  rw [Order0.classifyAux_unfold]
  -- reduce the children flatMap to `encodeTree`'s tail.
  congr 1
  rw [M5.encodeTree]
  congr 1
  -- omStep = M5.cells; per child, subtree.tree = [(order+1, childSize, 0)] = ch.node.tree
  show (B.omStep p N n f T).flatMap (fun c =>
        c.children.flatMap (fun ch =>
          (B.classifyAux p N n ch.childSize f
            (B.childCtxOfSize (T.order + 1) ch.childSize) rfl).tree))
    = (M5.cells T).flatMap (fun c => c.children.flatMap (fun ch => ch.node.tree))
  rw [show B.omStep p N n f T = M5.cells T from rfl]
  apply List.flatMap_congr
  intro c hc
  apply List.flatMap_congr
  intro ch hch
  rw [classifyAux_childCtxOfSize f (T.order + 1) ch.childSize]
  -- (classifyAux …).tree = [(order+1, childSize, 0)] = ch.node.tree
  show ([((T.order + 1), ch.childSize, 0)] : List (ℕ × ℕ × ℕ)) = ch.node.tree
  rw [cells_child_node_tree T c hc ch hch]

/-- **`classify f = shapeOf (fRootCtx f)`.**  Dispatch `classify → classifyAux` at `fRootCtx`, then
`classifyAux_of_single_descent` (the child ctx is `Rr = 0`, so the recursion is one step deep for
ANY residual).  This is the RAW shape of the genuine classifier, before any respell. -/
theorem classify_eq_shapeOf {p : ℕ} [Fact p.Prime] {n N : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) :
    B.classify p n N f = M5.shapeOf (B.fRootCtx p N hN f) := by
  have hdisp : B.classify p n N f
      = B.classifyAux p N n n f (B.fRootCtx p N hN f) (B.clusterSize_fRootCtx p N hN f) :=
    Order0.classifyAux_congr_ctx p N n n f (dif_pos hN)
      (B.clusterSize_rootCtx p N f) (B.clusterSize_fRootCtx p N hN f)
  rw [hdisp, classifyAux_of_single_descent n f (B.fRootCtx p N hN f)
      (B.clusterSize_fRootCtx p N hN f)]
  rfl

/-! ## 2. The respelled childful self-loop shape `TselfloopChildful`. -/

/-- **The M5 classifier child node** for one shape part `q = (D, μ)`: `⟨[(1, μ·D, 0)], []⟩` (root
order 0 ⇒ child order slot `1`).  This is what `M5.cells`/`encodeCells` records in the emitted cell's
`children` for a μ ≥ 2 strictly-descending factor — DISTINCT from `PathShapeChildful.childShape`
(order slot `2`), but with the SAME size slot `μ·D`, so `omChildCount`-invisible. -/
def childNode (sz : ℕ) : ClusterShape := ⟨[(1, sz, 0)], []⟩

/-- **`T★` respelled, CHILDFUL** — the genuine `B.classify` output on the single-side, hlt-regime
μ ≥ 2 locus: an ORDER-0 head `(0, s, Σ D)` whose serialized tree appends one child subtree
`[(1, μ·D, 0)]` per emitted (μ ≥ 2, `μ·D < s`) factor, and whose payload is one per-factor cell
carrying the classifier's own side face `toSideFace (mkSide pr)` and the child node `childNode (μ·D)`
under the same emission guard.  The tree slot is spelled to match `encodeTree (fRootCtx)` EXACTLY. -/
noncomputable def TselfloopChildful (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    ClusterShape :=
  ⟨(0, s, (shape.map (fun q => q.1 * q.2)).sum) ::
      (shape.flatMap (fun q =>
        if 2 ≤ q.2 ∧ q.2 * q.1 < s then [((1 : ℕ), q.2 * q.1, (0 : ℕ))] else [])),
    shape.map (fun q =>
      ⟨q.1, 1, M7.toSideFace (mkSide pr),
        (if 2 ≤ q.2 ∧ q.2 * q.1 < s then [childNode (q.2 * q.1)] else [])⟩)⟩

/-! ## 3. The childful `encodeCells` payload lemma (prime-power / general-μ). -/

/-- **The classifier's sorted factor pair-list.**  The degree-`mergeSort`ed factor list of `T.Rr`,
mapped to `(natDegree ψ, mult ψ)` pairs — the classifier's own emission order of the residual shape.
The forward raw-shape equality holds precisely when this list IS `shape`. -/
noncomputable def sortedFactorPairs (T : M5.OMType) : List (ℕ × ℕ) :=
  (((Classical.choice (M4.factorize_any T.Rr)).factors.attach.toList.mergeSort
      (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map
    (fun a => (a.1.natDegree, (Classical.choice (M4.factorize_any T.Rr)).mult a.1)))

/-- **`encodeCells` as a per-pair map** (general μ).  Erasing `M5.cells T` cell-by-cell gives, per
sorted factor `ψ` (degree `D`, mult `μ`), the childful `ShapeCell` `⟨D, T.δ, T.Nr, if 2≤μ∧μ·D<cs then
[childNode (μ·D)] else []⟩`.  This is the general-μ analogue of `encodeCells_of_squarefree` KEEPING
the descent branch (the child node is the M5-emitted `⟨[(order+1, μ·D, 0)], []⟩`; here `order+1 = 1`
requires `T.order = 0`, supplied by `hord`). -/
theorem encodeCells_childful_pairmap (T : M5.OMType) (hord : T.order = 0) :
    M5.encodeCells T
      = (sortedFactorPairs T).map (fun q =>
          (⟨q.1, T.δ, T.Nr,
            (if 2 ≤ q.2 ∧ q.2 * q.1 < M5.clusterSize T then [childNode (q.2 * q.1)] else [])⟩
            : ShapeCell)) := by
  rw [M5.encodeCells, M5.cells, sortedFactorPairs, List.map_map, List.map_map]
  apply List.map_congr_left
  rintro ⟨ψ, hψ⟩ _hmem
  set μ := (Classical.choice (M4.factorize_any T.Rr)).mult ψ with hμdef
  -- LHS: erase the emitted OMCell; RHS: the per-pair childful cell.
  show (⟨ψ.natDegree, T.δ, T.Nr,
      (if hμ : 2 ≤ μ then
        if hlt : μ * ψ.natDegree < M5.clusterSize T then
          [(⟨⟨[(T.order + 1, μ * ψ.natDegree, 0)], []⟩, ψ, μ, hμ, _, μ * ψ.natDegree, rfl, by simp [M5.nodeSizeOf], hlt⟩ : M5.OMCell.Child T)]
        else []
      else []).map (fun ch => ch.node)⟩ : ShapeCell)
    = ⟨ψ.natDegree, T.δ, T.Nr,
        (if 2 ≤ μ ∧ μ * ψ.natDegree < M5.clusterSize T then [childNode (μ * ψ.natDegree)] else [])⟩
  congr 1
  by_cases hμ : 2 ≤ μ
  · by_cases hlt : μ * ψ.natDegree < M5.clusterSize T
    · rw [dif_pos hμ, dif_pos hlt, if_pos ⟨hμ, hlt⟩]
      show [(⟨[(T.order + 1, μ * ψ.natDegree, 0)], []⟩ : ClusterShape)] = [childNode (μ * ψ.natDegree)]
      rw [childNode, hord]
    · rw [dif_pos hμ, dif_neg hlt, if_neg (fun h => hlt h.2)]
      rfl
  · rw [dif_neg hμ, if_neg (fun h => hμ h.1)]
    rfl

/-- **`encodeCells (fRootCtx f) = (TselfloopChildful s pr shape).cells`** (childful payload).  With
the classifier's sorted factor pair-list equal to `shape` (`hfshape`), `δ = 1` (fRootCtx),
`Nr = toSideFace (mkSide pr)` (`hNr`), and `clusterSize = s` (fRootCtx budget), the per-pair childful
cell map IS `TselfloopChildful`'s cell list. -/
theorem encodeCells_fRootCtx_childful {p : ℕ} [Fact p.Prime] {n N : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hNr : (B.fRootCtx p N hN f).Nr = M7.toSideFace (mkSide pr))
    (hfshape : sortedFactorPairs (B.fRootCtx p N hN f) = shape) :
    M5.encodeCells (B.fRootCtx p N hN f) = (TselfloopChildful n pr shape).cells := by
  rw [encodeCells_childful_pairmap (B.fRootCtx p N hN f) rfl, hfshape]
  show (shape.map (fun q =>
      (⟨q.1, (B.fRootCtx p N hN f).δ, (B.fRootCtx p N hN f).Nr,
        (if 2 ≤ q.2 ∧ q.2 * q.1 < M5.clusterSize (B.fRootCtx p N hN f) then
          [childNode (q.2 * q.1)] else [])⟩ : ShapeCell)))
    = shape.map (fun q =>
        ⟨q.1, 1, M7.toSideFace (mkSide pr),
          (if 2 ≤ q.2 ∧ q.2 * q.1 < n then [childNode (q.2 * q.1)] else [])⟩)
  apply List.map_congr_left
  intro q _
  rw [hNr]
  show (⟨q.1, (B.fRootCtx p N hN f).δ, M7.toSideFace (mkSide pr),
      (if 2 ≤ q.2 ∧ q.2 * q.1 < M5.clusterSize (B.fRootCtx p N hN f) then
        [childNode (q.2 * q.1)] else [])⟩ : ShapeCell)
    = ⟨q.1, 1, M7.toSideFace (mkSide pr),
        (if 2 ≤ q.2 ∧ q.2 * q.1 < n then [childNode (q.2 * q.1)] else [])⟩
  rw [show (B.fRootCtx p N hN f).δ = 1 from rfl,
      show M5.clusterSize (B.fRootCtx p N hN f) = n from rfl]

/-- **`encodeTree`'s child tail as a per-pair flatMap.**  The children flatMap of `encodeTree T`
(over `M5.cells T`, then over each cell's children's `node.tree`) equals the per-pair flatMap
emitting `[(order+1, μ·D, 0)]` for each μ ≥ 2 strictly-descending factor.  Uses
`cells_child_node_tree` (each child node tree is `[(order+1, childSize, 0)]`) and the same dite
structure as `encodeCells_childful_pairmap`. -/
theorem encodeTree_tail_pairmap (T : M5.OMType) :
    (M5.cells T).flatMap (fun c => c.children.flatMap (fun ch => ch.node.tree))
      = (sortedFactorPairs T).flatMap (fun q =>
          if 2 ≤ q.2 ∧ q.2 * q.1 < M5.clusterSize T then
            [(T.order + 1, q.2 * q.1, (0 : ℕ))] else []) := by
  rw [M5.cells, sortedFactorPairs, List.flatMap_map, List.flatMap_map]
  apply List.flatMap_congr
  rintro ⟨ψ, hψ⟩ _hmem
  set μ := (Classical.choice (M4.factorize_any T.Rr)).mult ψ with hμdef
  -- LHS: c.children.flatMap node.tree; RHS: the dite-guarded singleton tuple list.
  show ((if hμ : 2 ≤ μ then
          if hlt : μ * ψ.natDegree < M5.clusterSize T then
            [(⟨⟨[(T.order + 1, μ * ψ.natDegree, 0)], []⟩, ψ, μ, hμ, _, μ * ψ.natDegree, rfl, by simp [M5.nodeSizeOf], hlt⟩ : M5.OMCell.Child T)]
          else []
        else []).flatMap (fun ch => ch.node.tree))
    = (if 2 ≤ μ ∧ μ * ψ.natDegree < M5.clusterSize T then
        [(T.order + 1, μ * ψ.natDegree, (0 : ℕ))] else [])
  by_cases hμ : 2 ≤ μ
  · by_cases hlt : μ * ψ.natDegree < M5.clusterSize T
    · rw [dif_pos hμ, dif_pos hlt, if_pos ⟨hμ, hlt⟩]
      rfl
    · rw [dif_pos hμ, dif_neg hlt, if_neg (fun h => hlt h.2)]
      rfl
  · rw [dif_neg hμ, if_neg (fun h => hμ h.1)]
    rfl

/-- **The head `dr` of `fRootCtx` in the hlt regime equals `Σ D·μ`.**  `fRootCtx.dr =
rootResidual.natDegree = Σ mult·deg` over the factors = `Σ q.1·q.2` over `sortedFactorPairs = shape`.
Derived from `degree_budget` (over the factor Finset) transported to the sorted pair list. -/
theorem fRootCtx_dr_childful {p : ℕ} [Fact p.Prime] {n N : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) (shape : List (ℕ × ℕ))
    (hfshape : sortedFactorPairs (B.fRootCtx p N hN f) = shape) :
    (B.fRootCtx p N hN f).dr = (shape.map (fun q => q.1 * q.2)).sum := by
  set T := B.fRootCtx p N hN f with hTdef
  set fact := Classical.choice (M4.factorize_any T.Rr) with hfactdef
  -- dr = Rr.natDegree = ∑_{ψ∈factors} mult·deg  (degree_budget)
  have hdr : T.dr = T.Rr.natDegree := rfl
  have hbudget : ∑ ψ ∈ fact.factors, fact.mult ψ * ψ.natDegree = T.Rr.natDegree :=
    fact.degree_budget
  -- Σ over the sorted pair list (deg·mult) = Σ over factors.attach = Σ over factors (mult·deg).
  have hlist : (shape.map (fun q => q.1 * q.2)).sum
      = ∑ ψ ∈ fact.factors, fact.mult ψ * ψ.natDegree := by
    rw [← hfshape, sortedFactorPairs, List.map_map]
    rw [show (fun (q : ℕ × ℕ) => q.1 * q.2) ∘
          (fun a : {x // x ∈ fact.factors} => ((a.1.natDegree, fact.mult a.1) : ℕ × ℕ))
        = (fun a : {x // x ∈ fact.factors} => a.1.natDegree * fact.mult a.1) from rfl]
    -- convert RHS Finset sum to sum over attach.toList
    rw [← Finset.sum_attach fact.factors (fun ψ => fact.mult ψ * ψ.natDegree)]
    -- ∑ a ∈ factors.attach, mult·deg  →  (attach.toList.map (mult·deg)).sum  (Finset.sum_map_toList)
    rw [← Finset.sum_map_toList fact.factors.attach (fun a => fact.mult a.1 * a.1.natDegree)]
    -- now both are List.sum; the LHS is over the mergeSort'd list, a permutation of attach.toList
    apply List.Perm.sum_eq
    refine ((List.mergeSort_perm _ _).map _).trans ?_
    -- map (a => deg·mult) vs map (a => mult·deg): pointwise-equal maps
    rw [show (fun a : {x // x ∈ fact.factors} => a.1.natDegree * fact.mult a.1)
        = (fun a : {x // x ∈ fact.factors} => fact.mult a.1 * a.1.natDegree) from by
      funext a; rw [Nat.mul_comm]]
  rw [hdr, ← hbudget, hlist]

/-! ## 3b. The multiset bridge `sortedFactorPairs ↔ polyShape`. -/

/-- **`F.mult ψ = (normalizedFactors R).count ψ`** for a monic-irreducible factor `ψ` of a nonzero
`R`.  The ψ-adic valuation of `R = C(lc)·∏ φ^(mult φ)` is exactly `mult ψ`: `ψ^(mult ψ) ∣ R`
(`pow_mult_dvd`) while `ψ^(mult ψ + 1) ∤ R` (else `ψ` divides the ψ-coprime cofactor
`C(lc)·∏_{φ≠ψ} φ^(mult φ)`).  `count_normalizedFactors_eq` then reads the count. -/
theorem mult_eq_count {kS : Type*} [Field kS] [Finite kS] {R : Polynomial kS} (hR : R ≠ 0)
    (F : M4.ResidualFactorization R) {ψ : Polynomial kS} (hψ : ψ ∈ F.factors) :
    F.mult ψ = (UniqueFactorizationMonoid.normalizedFactors R).count ψ := by
  classical
  have hirr : Irreducible ψ := F.factors_irreducible ψ hψ
  have hmon : ψ.Monic := F.factors_monic ψ hψ
  -- cofactor: R = ψ^(mult ψ) · G where ψ is coprime to G.
  set μ := F.mult ψ with hμdef
  set G := Polynomial.C R.leadingCoeff * ∏ φ ∈ F.factors.erase ψ, φ ^ F.mult φ with hGdef
  have hsplit : R = ψ ^ μ * G := by
    have hprod : ∏ φ ∈ F.factors, φ ^ F.mult φ
        = ψ ^ F.mult ψ * ∏ φ ∈ F.factors.erase ψ, φ ^ F.mult φ :=
      (Finset.mul_prod_erase F.factors (fun φ => φ ^ F.mult φ) hψ).symm
    calc R = Polynomial.C R.leadingCoeff * ∏ φ ∈ F.factors, φ ^ F.mult φ := F.prod_eq
      _ = Polynomial.C R.leadingCoeff
            * (ψ ^ F.mult ψ * ∏ φ ∈ F.factors.erase ψ, φ ^ F.mult φ) := by rw [hprod]
      _ = ψ ^ μ * G := by rw [hGdef, hμdef]; ring
  -- ψ coprime to G
  have hcopG : IsCoprime ψ G := by
    rw [hGdef]
    apply IsCoprime.mul_right
    · -- ψ coprime to the unit `C lc`
      have hlc : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR
      obtain ⟨u, hu⟩ := (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlc))
      exact ⟨0, (↑u⁻¹ : Polynomial kS), by rw [← hu]; simp⟩
    · apply IsCoprime.prod_right
      intro φ hφ
      have hφne : φ ≠ ψ := (Finset.mem_erase.mp hφ).1
      have hφmem : φ ∈ F.factors := (Finset.mem_erase.mp hφ).2
      exact (F.pairwise_coprime ψ hψ φ hφmem (Ne.symm hφne)).pow_right
  -- ψ^μ ∣ R (pow_mult_dvd) and ψ^(μ+1) ∤ R
  have hle : ψ ^ μ ∣ R := Order0.pow_mult_dvd F hψ
  have hlt : ¬ ψ ^ (μ + 1) ∣ R := by
    intro hdvd
    rw [hsplit] at hdvd
    -- ψ^(μ+1) ∣ ψ^μ · G ⟹ ψ ∣ G (cancel ψ^μ), contradicting coprimality
    rw [pow_succ] at hdvd
    have hψne : ψ ≠ 0 := hirr.ne_zero
    have hcancel : ψ ∣ G := by
      have hpow_ne : ψ ^ μ ≠ 0 := pow_ne_zero _ hψne
      exact (mul_dvd_mul_iff_left hpow_ne).mp hdvd
    exact hirr.not_isUnit (hcopG.isUnit_of_dvd' (dvd_refl ψ) hcancel)
  rw [hμdef]
  exact (UniqueFactorizationMonoid.count_normalizedFactors_eq hirr
    (Polynomial.Monic.normalize_eq_self hmon) hle hlt).symm

/-- **`sortedFactorPairs` as a multiset IS `polyShape`.**  The degree-sorted `(deg, mult)` pair list
of the fRootCtx factorization of `Rr = R`, as a multiset, equals the canonical `polyShape R` (the
`(deg, count)` map over the distinct normalized factors), using the factor-set canonicity
(`factors_eq_normalizedFactors_toFinset`) and `mult = count` (`mult_eq_count`). -/
theorem sortedFactorPairs_multiset_eq_polyShape {p : ℕ} [Fact p.Prime] {n N : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) (R : Polynomial (ZMod p)) (hR : R ≠ 0)
    (hRr : (B.fRootCtx p N hN f).Rr = R) :
    (↑(sortedFactorPairs (B.fRootCtx p N hN f)) : Multiset (ℕ × ℕ)) = polyShape p R := by
  letI := Classical.decEq (Polynomial (ZMod p))
  set T := B.fRootCtx p N hN f with hTdef
  set fact := Classical.choice (M4.factorize_any T.Rr) with hfactdef
  rw [sortedFactorPairs]
  -- multiset of the sorted list = factors.val.map (deg, mult)
  have hms : (↑(((fact.factors.attach.toList.mergeSort
        (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map
          (fun a => (a.1.natDegree, fact.mult a.1)))) : Multiset (ℕ × ℕ))
      = fact.factors.val.map (fun ψ => (ψ.natDegree, fact.mult ψ)) := by
    calc (↑(((fact.factors.attach.toList.mergeSort
          (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map
            (fun a => (a.1.natDegree, fact.mult a.1)))) : Multiset (ℕ × ℕ))
        = (↑((fact.factors.attach.toList).map
            (fun a => (a.1.natDegree, fact.mult a.1))) : Multiset (ℕ × ℕ)) :=
          Multiset.coe_eq_coe.mpr ((List.mergeSort_perm _ _).map _)
      _ = Multiset.map (fun (a : {x // x ∈ fact.factors}) => (a.1.natDegree, fact.mult a.1))
            ((fact.factors.attach.toList : List _) : Multiset _) := (Multiset.map_coe _ _).symm
      _ = Multiset.map (fun (a : {x // x ∈ fact.factors}) => (a.1.natDegree, fact.mult a.1))
            fact.factors.attach.val := congrArg (Multiset.map _) (Finset.coe_toList _)
      _ = fact.factors.val.map (fun ψ => (ψ.natDegree, fact.mult ψ)) := by
          rw [show fact.factors.attach.val = fact.factors.val.attach from rfl]
          exact Multiset.attach_map_val' fact.factors.val (fun ψ => (ψ.natDegree, fact.mult ψ))
  rw [hms]
  -- factors.val.map (deg, mult) = polyShape (deg, count) over the SAME nodup support
  have hRr0 : T.Rr ≠ 0 := by rw [hRr]; exact hR
  have hfac_eq : fact.factors = (UniqueFactorizationMonoid.normalizedFactors T.Rr).toFinset :=
    Order0.factors_eq_normalizedFactors_toFinset T.Rr hRr0 fact
  have hval : fact.factors.val = (UniqueFactorizationMonoid.normalizedFactors T.Rr).toFinset.val := by
    rw [hfac_eq]
  -- Prove the goal by comparing the two multisets element-wise over the shared nodup support (T.Rr).
  have hgoal : Multiset.map (fun ψ => (ψ.natDegree, fact.mult ψ)) fact.factors.val
      = (UniqueFactorizationMonoid.normalizedFactors T.Rr).toFinset.val.map
          (fun ψ => (ψ.natDegree, (UniqueFactorizationMonoid.normalizedFactors T.Rr).count ψ)) := by
    rw [hval]
    apply Multiset.map_congr rfl
    intro ψ hψ
    have hψf : ψ ∈ fact.factors := by rw [hfac_eq]; exact Finset.mem_val.mp hψ
    rw [mult_eq_count hRr0 fact hψf]
  rw [hgoal]
  -- close against `polyShape p R` by transporting through `polyShape p T.Rr` (defeq to the (deg,count)
  -- map by `unfold`) via `hRr : T.Rr = R` (a clean `congrArg`, no instance surgery under binders).
  -- `polyShape p R` unfolds to the (deg, count) map; polyShape's monoid uses `ZMod.decidableEq p`
  -- while `hgoal`'s uses `Classical.propDecidable` — aligned by `normalizedFactors_decEq_irrel`.
  have hpolyR : polyShape p R
      = (UniqueFactorizationMonoid.normalizedFactors R).toFinset.val.map
          (fun ψ => (ψ.natDegree, (UniqueFactorizationMonoid.normalizedFactors R).count ψ)) := by
    conv_lhs => unfold polyShape
  rw [hpolyR]
  -- both sides are `nf(·).toFinset.val.map (deg,count)`; fold T.Rr→R via hRr and align the
  -- `normalizedFactors` NormalizationMonoid flavor (subsingleton).
  have key : (UniqueFactorizationMonoid.normalizedFactors T.Rr)
      = (UniqueFactorizationMonoid.normalizedFactors R) := by
    rw [hRr]
    exact ClassifierBridgeFiber2.normalizedFactors_decEq_irrel
      (fun a b => Classical.propDecidable (a = b)) (ZMod.decidableEq p) R
  rw [key]
  -- residual: only the `Multiset.count`/`toFinset` `DecidableEq (Polynomial (ZMod p))` differs
  -- (LHS `Polynomial.instDecidableEq`, RHS `Classical.decEq`); a subsingleton, so `convert`.
  refine Multiset.map_congr ?_ (fun ψ _ => ?_)
  · exact congrArg (fun (i : DecidableEq (Polynomial (ZMod p))) =>
      (@Multiset.toFinset _ i (UniqueFactorizationMonoid.normalizedFactors R)).val)
      (Subsingleton.elim _ _)
  · exact congrArg (fun (i : DecidableEq (Polynomial (ZMod p))) =>
      (ψ.natDegree, @Multiset.count _ i ψ (UniqueFactorizationMonoid.normalizedFactors R)))
      (Subsingleton.elim _ _)

/-! ## 3c. The list equality `sortedFactorPairs = shape` (distinct-degree regime). -/

/-- **`sortedFactorPairs` is degree-`≤`-sorted.**  The `mergeSort` by the degree-`≤` key produces a
list `Pairwise (fst ≤ fst)`. -/
theorem sortedFactorPairs_pairwise_deg (T : M5.OMType) :
    (sortedFactorPairs T).Pairwise (fun a b => a.1 ≤ b.1) := by
  rw [sortedFactorPairs, List.pairwise_map]
  have hpairB := List.pairwise_mergeSort
    (le := fun a b : {x // x ∈ (Classical.choice (M4.factorize_any T.Rr)).factors} =>
      decide (a.1.natDegree ≤ b.1.natDegree))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (Classical.choice (M4.factorize_any T.Rr)).factors.attach.toList
  exact hpairB.imp (fun h => of_decide_eq_true h)

/-- **The list equality `sortedFactorPairs (fRootCtx f) = shape`** in the DISTINCT-DEGREE regime.
`sortedFactorPairs` is degree-`≤`-sorted and, with distinct degrees, hence `shapeLE`-sorted (first
disjunct); `shape` is `shapeLE`-sorted (`ShapesFor`); the two are `shapeLE`-permutations (both equal
`polyShape` as multisets — `sortedFactorPairs_multiset_eq_polyShape` + the locus `polyShape = shape`);
`Perm.eq_of_pairwise'` (with the `shapeLE` `Std.Antisymm` instance) then forces equality.

The distinct-degree hypothesis `hnodup` is the honest scope boundary: for degree-tied factors with
distinct multiplicities the classifier's degree-only `mergeSort` order is NOT `shapeLE`-determined
(the documented Phase-B canonicalization ambiguity), so the RAW shape equality can fail there. -/
theorem sortedFactorPairs_eq_shape {p : ℕ} [Fact p.Prime] {n N : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) (R : Polynomial (ZMod p)) (hR : R ≠ 0)
    (hRr : (B.fRootCtx p N hN f).Rr = R) (shape : List (ℕ × ℕ))
    (hshape : polyShape p R = (shape : Multiset (ℕ × ℕ)))
    (hpw : shape.Pairwise shapeLE)
    (hnodup : (shape.map Prod.fst).Nodup) :
    sortedFactorPairs (B.fRootCtx p N hN f) = shape := by
  -- perm: both equal polyShape as multisets.
  have hperm : List.Perm (sortedFactorPairs (B.fRootCtx p N hN f)) shape := by
    have h1 := sortedFactorPairs_multiset_eq_polyShape hN f R hR hRr
    rw [hshape] at h1
    exact Multiset.coe_eq_coe.mp h1
  -- sortedFactorPairs is shapeLE-sorted: degree-≤-sorted + distinct degrees (via the perm) ⟹ shapeLE.
  have hdegpw := sortedFactorPairs_pairwise_deg (B.fRootCtx p N hN f)
  -- distinct degrees transfer along the perm.
  have hnodupS : ((sortedFactorPairs (B.fRootCtx p N hN f)).map Prod.fst).Nodup := by
    rw [(hperm.map Prod.fst).nodup_iff]
    exact hnodup
  have hpwS : (sortedFactorPairs (B.fRootCtx p N hN f)).Pairwise shapeLE := by
    -- degree-≤-sorted + distinct degrees ⟹ degrees strictly increase ⟹ shapeLE (first disjunct).
    have hnepw : (sortedFactorPairs (B.fRootCtx p N hN f)).Pairwise (fun a b => a.1 ≠ b.1) := by
      have hnp : List.Pairwise (· ≠ ·) ((sortedFactorPairs (B.fRootCtx p N hN f)).map Prod.fst) :=
        hnodupS
      rw [List.pairwise_map] at hnp
      exact hnp
    have hstrict : (sortedFactorPairs (B.fRootCtx p N hN f)).Pairwise (fun a b => a.1 < b.1) :=
      (hdegpw.and hnepw).imp (fun ⟨hle, hne⟩ => lt_of_le_of_ne hle hne)
    exact hstrict.imp (fun h => Or.inl h)
  exact hperm.eq_of_pairwise' hpwS hpw

/-- **`shapeOf (fRootCtx f) = TselfloopChildful n pr shape`** given the classifier pair-list
`hfshape` and the side-face `hNr`.  The cells match by `encodeCells_fRootCtx_childful`; the tree
head is `(0, n, Σ D·μ)` (`fRootCtx_dr_childful`) and the tail is the per-emitted-child flatMap
(`encodeTree_tail_pairmap`, order slot `T.order + 1 = 1`). -/
theorem classify_eq_TselfloopChildful_of_pairs {p : ℕ} [Fact p.Prime] {n N : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hNr : (B.fRootCtx p N hN f).Nr = M7.toSideFace (mkSide pr))
    (hfshape : sortedFactorPairs (B.fRootCtx p N hN f) = shape) :
    B.classify p n N f = TselfloopChildful n pr shape := by
  rw [classify_eq_shapeOf hN f, M5.shapeOf]
  -- cells
  have hcells : M5.encodeCells (B.fRootCtx p N hN f) = (TselfloopChildful n pr shape).cells :=
    encodeCells_fRootCtx_childful hN f pr shape hNr hfshape
  -- tree
  have htree : M5.encodeTree (B.fRootCtx p N hN f) = (TselfloopChildful n pr shape).tree := by
    rw [M5.encodeTree, encodeTree_tail_pairmap, hfshape,
        show M5.clusterSize (B.fRootCtx p N hN f) = n from rfl,
        show (B.fRootCtx p N hN f).order = 0 from rfl]
    show ((B.fRootCtx p N hN f).order, M5.clusterSize (B.fRootCtx p N hN f), (B.fRootCtx p N hN f).dr)
        :: (shape.flatMap (fun q =>
              if 2 ≤ q.2 ∧ q.2 * q.1 < n then [((0 : ℕ) + 1, q.2 * q.1, (0 : ℕ))] else []))
      = (TselfloopChildful n pr shape).tree
    rw [show ((B.fRootCtx p N hN f).order, M5.clusterSize (B.fRootCtx p N hN f), (B.fRootCtx p N hN f).dr)
        = ((0 : ℕ), n, (shape.map (fun q => q.1 * q.2)).sum) from by
      rw [fRootCtx_dr_childful hN f shape hfshape]; rfl]
    rfl
  show (⟨M5.encodeTree (B.fRootCtx p N hN f), M5.encodeCells (B.fRootCtx p N hN f)⟩ : ClusterShape)
    = TselfloopChildful n pr shape
  rw [hcells, htree]
  rfl


/-! ## 5b. The backward-direction helpers (all-childful regime). -/

/-- **The childful cell erasure `g q = (q.1, if guard then [childNode (μ·D)] else [])` is injective**
on positive-degree pairs where the guard is TRUE (`2 ≤ μ ∧ μ·D < n`): `q.1 = D` from the first slot,
and `childNode (μ·D)` (size slot) with `D > 0` recovers `μ`. -/
theorem childful_erase_inj_guardTrue {n : ℕ} {q q' : ℕ × ℕ} (hpos : 1 ≤ q.1)
    (hg : 2 ≤ q.2 ∧ q.2 * q.1 < n) (hg' : 2 ≤ q'.2 ∧ q'.2 * q'.1 < n)
    (h : (q.1, (if 2 ≤ q.2 ∧ q.2 * q.1 < n then [childNode (q.2 * q.1)] else []))
       = (q'.1, (if 2 ≤ q'.2 ∧ q'.2 * q'.1 < n then [childNode (q'.2 * q'.1)] else []))) :
    q = q' := by
  rw [Prod.mk.injEq] at h
  obtain ⟨hD, hch⟩ := h
  rw [if_pos hg, if_pos hg'] at hch
  have hcn : childNode (q.2 * q.1) = childNode (q'.2 * q'.1) := (List.cons.injEq _ _ _ _).mp hch |>.1
  have hsz : q.2 * q.1 = q'.2 * q'.1 := by
    have := congrArg (fun (c : ClusterShape) => c.tree) hcn
    simp only [childNode] at this
    have h2 := congrArg (fun l => l.head?) this
    simp only [List.head?_cons, Option.some.injEq] at h2
    exact congrArg (fun t => t.2.1) h2
  rw [hD] at hsz
  exact Prod.ext hD (Nat.eq_of_mul_eq_mul_right (by omega) hsz)

/-- **List equality from a guard-true erasure identity.**  If `l₁.map g = l₂.map g` for the childful
erasure `g` and every element of BOTH lists is positive-degree and guard-true, then `l₁ = l₂`
(pointwise `g`-injectivity `childful_erase_inj_guardTrue` + `List.map` cancellation). -/
theorem list_eq_of_erase_eq {n : ℕ} {l₁ l₂ : List (ℕ × ℕ)}
    (hpos₁ : ∀ q ∈ l₁, 1 ≤ q.1) (hg₁ : ∀ q ∈ l₁, 2 ≤ q.2 ∧ q.2 * q.1 < n)
    (hg₂ : ∀ q ∈ l₂, 2 ≤ q.2 ∧ q.2 * q.1 < n)
    (h : l₁.map (fun q => (q.1, (if 2 ≤ q.2 ∧ q.2 * q.1 < n then [childNode (q.2 * q.1)] else [])))
       = l₂.map (fun q => (q.1, (if 2 ≤ q.2 ∧ q.2 * q.1 < n then [childNode (q.2 * q.1)] else [])))) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons b t => simp at h
  | cons a t ih =>
      cases l₂ with
      | nil => simp at h
      | cons b t' =>
          rw [List.map_cons, List.map_cons, List.cons.injEq] at h
          have hab : a = b := childful_erase_inj_guardTrue
            (hpos₁ a (by simp)) (hg₁ a (by simp)) (hg₂ b (by simp)) h.1
          subst hab
          rw [ih (fun q hq => hpos₁ q (by simp [hq])) (fun q hq => hg₁ q (by simp [hq]))
            (fun q hq => hg₂ q (by simp [hq])) h.2]

/-! ## 6. Forward fiber direction `classify_eq_childful_of_inCell`.

The full iff `classify = TselfloopChildful ↔ InCell` splits into the FORWARD direction (LANDED here)
and the BACKWARD direction (precise obstacle documented at the end of the file).  The forward is the
childful analogue of `ClassifierBridgeFiber.classify_eq_selfloop_of_inCell`. -/

/-- **FORWARD (childful): `InCell → classify = TselfloopChildful`.**  On the single-side,
distinct-degree, hlt-regime locus, membership in the order-1 cell `mkCell n P [shape]` forces the
genuine order-0 classifier to emit the respelled childful shape `TselfloopChildful n pr shape`.

Chain: extract the menu/residual data from `InCell` (Steps 2/3 of `ClassifierBridgeFiber`,
μ-agnostic — `rootResidual = residualOf f pr`, `rootFace = toSideFace (mkSide pr)`, `polyShape
(residualOf f pr) = shape`); `sortedFactorPairs_eq_shape` (distinct degrees) pins the classifier's own
degree-sorted `(deg, mult)` emission list to `shape`; `classify_eq_TselfloopChildful_of_pairs`
assembles the raw tree + payload. -/
theorem classify_eq_childful_of_inCell {p : ℕ} [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (P : List (ℕ × ℕ)) (hPmenu : MenuPath n N P) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (hsingle : sidePairs P = [pr])
    (shape : List (ℕ × ℕ)) (hSF : ShapesFor P [shape]) (hnodup : (shape.map Prod.fst).Nodup)
    (f : QuotientBox.monicBox p N n)
    (hInCell : InCell p f (mkCell n P [shape])) :
    B.classify p n N f = TselfloopChildful n pr shape := by
  obtain ⟨H, hPeq, hpreq, hH1, hH2⟩ := ClassifierBridgeFiber.menuPath_single_side hPmenu hsingle
  subst hpreq
  subst hPeq
  obtain ⟨P', sh', hP', hsh', heq, hM0⟩ := hInCell
  obtain ⟨rfl, rfl⟩ := mkCell_injective hPmenu hP' hSF hsh' heq
  have hM : Matches p f ([((0:ℕ),H),((n:ℕ),(0:ℕ))] : List (ℕ × ℕ)) [shape] := hM0
  have hexact : ∀ q ∈ ([((0:ℕ), H), ((n:ℕ), (0:ℕ))] : List (ℕ × ℕ)), vOf p f q.1 = q.2 := hM.1
  have hv0 : vOf p f 0 = H := hexact (0, H) (by simp)
  have hHN : H < N := by omega
  have hside : SideAbove p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) := by
    have hsa := matches_sideAbove p hM
    rw [hsingle] at hsa
    exact hsa (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (by simp)
  have hRr : B.rootResidual p N hN f = residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) :=
    ClassifierBridgeFiber.rootResidual_eq_residualOf p hn hN f hPmenu hexact hsingle hv0 hHN hside
  have hFace : B.rootFace p N hN f = M7.toSideFace (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) := by
    rw [B.rootFace, ClassifierBridgeFiber.rootSide_eq_of_inCell p hn hN f hv0 hHN hside]
  have hpr_mem : (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ sidePairs
      ([((0:ℕ), H), ((n:ℕ), (0:ℕ))] : List (ℕ × ℕ)) := by rw [hsingle]; simp
  obtain ⟨hRne, _⟩ := residual_facts p hN hPmenu hexact hpr_mem
  have hshapeM : polyShape p (residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))
      = (shape : Multiset (ℕ × ℕ)) := by
    have hSM := hM.2
    rw [hsingle] at hSM
    cases hSM with
    | cons hhead _ => exact hhead.2
  have hpw : (shape : List (ℕ × ℕ)).Pairwise shapeLE := by
    have := hsh'; rw [ShapesFor, hsingle] at this
    cases this with
    | cons hh _ => exact (mem_shapesOfDegree_iff.mp hh).1
  have hRrEq : (B.fRootCtx p N hN f).Rr = residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) := hRr
  have hraw : sortedFactorPairs (B.fRootCtx p N hN f) = shape :=
    sortedFactorPairs_eq_shape hN f _ hRne hRrEq shape hshapeM hpw hnodup
  have hNr : (B.fRootCtx p N hN f).Nr = M7.toSideFace (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) := hFace
  exact classify_eq_TselfloopChildful_of_pairs hN f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape hNr hraw

#print axioms classify_eq_childful_of_inCell

/-! ## 7. The MAIN childful fiber iff `classify_eq_childful_iff`.

The full iff holds in the ALL-CHILDFUL, distinct-degree, hlt regime: every shape factor is genuinely
repeated (`2 ≤ μ`), strictly descending (`μ·D < n`), and the degrees are distinct.  The all-childful
hypothesis `hallμ` is ESSENTIAL for the backward direction: a shape with a `μ = 1` (or full-budget
`μ·D = n`) entry erases to a CHILDLESS cell, which the classifier ALSO emits for a full-budget
prime-power factor — so `classify = TselfloopChildful shape` would not pin the InCell residual (the
guard-false cells cannot distinguish `μ = 1` from a full-budget `μ ≥ 2` self-loop).  With every entry
guard-TRUE, the child data pins the genuine `μ` (`childful_erase_inj_guardTrue`), closing the fiber. -/
theorem classify_eq_childful_iff {p : ℕ} [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (P : List (ℕ × ℕ)) (hPmenu : MenuPath n N P) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (hsingle : sidePairs P = [pr])
    (shape : List (ℕ × ℕ)) (hSF : ShapesFor P [shape]) (hne : shape ≠ [])
    (hnodup : (shape.map Prod.fst).Nodup)
    (hallμ : ∀ q ∈ shape, 2 ≤ q.2) (hlt : ∀ q ∈ shape, q.2 * q.1 < n)
    (f : QuotientBox.monicBox p N n) :
    B.classify p n N f = TselfloopChildful n pr shape
      ↔ InCell p f (mkCell n P [shape]) := by
  obtain ⟨H, hPeq, hpreq, hH1, hH2⟩ := ClassifierBridgeFiber.menuPath_single_side hPmenu hsingle
  subst hpreq
  subst hPeq
  -- shape positivity from ShapesFor.
  have hpospair : ∀ q ∈ shape, 1 ≤ q.1 ∧ 1 ≤ q.2 := by
    have := hSF; rw [ShapesFor, hsingle] at this
    cases this with
    | cons hh _ => exact (mem_shapesOfDegree_iff.mp hh).2.1
  -- every shape entry is guard-true (2 ≤ μ ∧ μ·D < n).
  have hgshape : ∀ q ∈ shape, 2 ≤ q.2 ∧ q.2 * q.1 < n := fun q hq => ⟨hallμ q hq, hlt q hq⟩
  constructor
  · -- backward: classify = TselfloopChildful → InCell.
    intro hcl
    have hHN : H < N := by omega
    have hH0 : 0 < H := by omega
    -- Step A(i): rootFace = toSideFace (mkSide pr) off the emitted head cell polygon.
    have hface : B.rootFace p N hN f
        = M7.toSideFace (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) := by
      have hcells : M5.encodeCells (B.fRootCtx p N hN f)
          = (TselfloopChildful n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape).cells := by
        rw [← ClassifierBridgeFiber2.classify_cells hN f, hcl]
      cases shape with
      | nil => exact absurd rfl hne
      | cons a t =>
          have hheadmem : (⟨a.1, 1, M7.toSideFace (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))),
              (if 2 ≤ a.2 ∧ a.2 * a.1 < n then [childNode (a.2 * a.1)] else [])⟩ : ShapeCell)
              ∈ M5.encodeCells (B.fRootCtx p N hN f) := by
            rw [hcells]
            show _ ∈ (List.cons a t).map (fun q =>
              (⟨q.1, 1, M7.toSideFace (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))),
                (if 2 ≤ q.2 ∧ q.2 * q.1 < n then [childNode (q.2 * q.1)] else [])⟩ : ShapeCell))
            rw [List.map_cons]; exact List.mem_cons_self
          have hpoly := ClassifierBridgeFiber2.encodeCells_polygon (B.fRootCtx p N hN f) _ hheadmem
          exact hpoly.symm
    -- Step A(ii): rootSide = some (mkSide pr) — the μ-agnostic hull inversion of `ClassifierBridgeFiber2`.
    have hrs : B.rootSide p N hN f = some (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) := by
      set S := B.boxValSupport p N f with hSdef
      set hS := B.boxValSupport_nonempty p N hN f with hShyp
      have hRHSwidth : (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))).length = n := by
        show n - 0 = n; omega
      rw [B.rootFace] at hface
      cases hrs' : B.rootSide p N hN f with
      | none =>
          rw [hrs'] at hface
          have hw : (0 : ℕ) = (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))).length :=
            congrArg L4.LatticePolygon.width hface
          rw [hRHSwidth] at hw; omega
      | some Sm =>
          rw [hrs'] at hface
          have hlen : Sm.length = n := by
            have := ClassifierBridgeFiber2.toSideFace_length_eq hface
            rw [hRHSwidth] at this; exact this
          have hlenpos : 0 < Sm.length := by rw [hlen]; exact hn
          have hv0S : Sm.v₀ = H := by
            have := ClassifierBridgeFiber2.toSideFace_v0_eq hface hlenpos
            show Sm.v₀ = H; rw [this]; rfl
          rw [B.rootSide] at hrs'
          have hverts : ∃ v1 rest, NewtonPolygon.npVertices S hS
              = (Sm.i₀, Sm.v₀) :: (Sm.j₀, v1) :: rest ∧ Sm.v₁ = v1 := by
            unfold NewtonPolygon.npSides at hrs'
            cases hv : NewtonPolygon.npVertices S hS with
            | nil => rw [hv] at hrs'; simp at hrs'
            | cons a t =>
                cases t with
                | nil => rw [hv] at hrs'; simp at hrs'
                | cons b rest =>
                    rw [hv] at hrs'
                    simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.head?_cons,
                      Option.some.injEq] at hrs'
                    have hi : a.1 = Sm.i₀ := congrArg NewtonPolygon.Side.i₀ hrs'
                    have hj : b.1 = Sm.j₀ := congrArg NewtonPolygon.Side.j₀ hrs'
                    have hvv0 : a.2 = Sm.v₀ := congrArg NewtonPolygon.Side.v₀ hrs'
                    have hvv1 : b.2 = Sm.v₁ := congrArg NewtonPolygon.Side.v₁ hrs'
                    refine ⟨b.2, rest, ?_, hvv1.symm⟩
                    rw [show a = (Sm.i₀, Sm.v₀) from Prod.ext hi hvv0,
                        show b = (Sm.j₀, b.2) from Prod.ext hj rfl]
          obtain ⟨v1, rest, hV, hv1eq⟩ := hverts
          have hmemR : (Sm.j₀, v1) ∈ NewtonPolygon.npVertices S hS := by rw [hV]; simp
          have hSmemR : (Sm.j₀, v1) ∈ S :=
            ClassifierBridgeFiber.mem_S_of_mem_npVertices p f hS hmemR
          obtain ⟨_, hneR⟩ := ClassifierBridgeFiber.boxValSupport_eq_dot p f hSmemR
          have hjle : Sm.j₀ ≤ n :=
            ClassifierBridgeFiber.support_le_deg p f (Polynomial.mem_support_iff.mpr hneR)
          have hwidth : Sm.j₀ - Sm.i₀ = n := hlen
          have hi0 : Sm.i₀ = 0 := by omega
          have hj0 : Sm.j₀ = n := by omega
          have hv1 : v1 = 0 := by
            have honhull : ((v1 : ℕ) : ℚ) = NewtonPolygon.npHeight S hS ((Sm.j₀ : ℕ) : ℚ) := by
              have := NewtonPolygon.npVertices_on_hull S hS hmemR; simpa using this
            rw [hj0] at honhull
            have hnmem : (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) ∈ S :=
              ClassifierBridgeFiber.mem_boxValSupport_right p hN f
            have hle : NewtonPolygon.npHeight S hS ((n : ℕ) : ℚ) ≤ ((0 : ℕ) : ℚ) :=
              NewtonPolygon.npHeight_le S hS hnmem
            rw [← honhull] at hle
            have : (v1 : ℚ) ≤ 0 := by simpa using hle
            have hv1z : (v1 : ℚ) = 0 := le_antisymm this (by positivity)
            exact_mod_cast hv1z
          have hSmeq : Sm = mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) := by
            have hv1S : Sm.v₁ = 0 := by rw [hv1eq]; exact hv1
            show Sm = ⟨0, n, H, 0⟩
            cases Sm with
            | mk i j vv0 vv1 => simp only at hi0 hj0 hv0S hv1S; subst hi0 hj0 hv0S hv1S; rfl
          rw [hSmeq]
    -- npVertices = [(0,H),(n,0)]; Step B: SideAbove + vertex exactness.
    have hverts := ClassifierBridgeFiber.npVertices_of_rootSide p hn hN f hrs
    obtain ⟨hside, hv0, hvn⟩ := ClassifierBridgeFiber2.sideAbove_of_npVertices p hn hN hH0 hHN f hverts
    have hexact : ∀ q ∈ ([((0 : ℕ), H), ((n : ℕ), (0 : ℕ))] : List (ℕ × ℕ)), vOf p f q.1 = q.2 := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq2
      · simpa using hv0
      · rcases List.mem_cons.mp hq2 with rfl | hq3
        · simpa using hvn
        · simp at hq3
    have hRr : B.rootResidual p N hN f = residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) :=
      ClassifierBridgeFiber.rootResidual_eq_residualOf p hn hN f hPmenu hexact hsingle hv0 hHN hside
    have hRne : residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ≠ 0 := by
      have hpr_mem : (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ sidePairs ([((0:ℕ),H),((n:ℕ),(0:ℕ))] : List (ℕ × ℕ)) := by rw [hsingle]; simp
      exact (residual_facts p hN hPmenu hexact hpr_mem).1
    have hRrEq : (B.fRootCtx p N hN f).Rr = residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) := hRr
    have hbridge := sortedFactorPairs_multiset_eq_polyShape hN f
      (residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) hRne hRrEq
    -- raw list identity: the emitted cells' (dS, children) equals shape's; both guard-true.
    have hgeq : (sortedFactorPairs (B.fRootCtx p N hN f)).map
          (fun q => (q.1, (if 2 ≤ q.2 ∧ q.2 * q.1 < n then [childNode (q.2 * q.1)] else [])))
        = shape.map
          (fun q => (q.1, (if 2 ≤ q.2 ∧ q.2 * q.1 < n then [childNode (q.2 * q.1)] else []))) := by
      have hcellseq : M5.encodeCells (B.fRootCtx p N hN f)
          = (TselfloopChildful n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape).cells := by
        rw [← ClassifierBridgeFiber2.classify_cells hN f, hcl]
      rw [encodeCells_childful_pairmap (B.fRootCtx p N hN f) rfl,
          show M5.clusterSize (B.fRootCtx p N hN f) = n from rfl] at hcellseq
      rw [show (TselfloopChildful n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape).cells
          = shape.map (fun q =>
              (⟨q.1, 1, M7.toSideFace (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))),
                (if 2 ≤ q.2 ∧ q.2 * q.1 < n then [childNode (q.2 * q.1)] else [])⟩ : ShapeCell))
          from rfl] at hcellseq
      have h := congrArg (List.map (fun (c : ShapeCell) => (c.dS, c.children))) hcellseq
      rw [List.map_map, List.map_map] at h
      exact h
    -- sortedFactorPairs positivity + guard-true (its entries match shape's guard-true entries).
    have hsfpos : ∀ q ∈ sortedFactorPairs (B.fRootCtx p N hN f), 1 ≤ q.1 ∧ 1 ≤ q.2 := fun q hq =>
      polyShape_pos p hRne q (by rw [← hbridge]; exact hq)
    have hsfg : ∀ q ∈ sortedFactorPairs (B.fRootCtx p N hN f), 2 ≤ q.2 ∧ q.2 * q.1 < n := by
      -- each sfp entry's g-image is in shape.map g (hgeq), i.e. equals some shape entry's g-image;
      -- shape entries are guard-true, so the g-image has a NONEMPTY child ⇒ sfp entry guard true.
      intro q hq
      have hqimg : (q.1, (if 2 ≤ q.2 ∧ q.2 * q.1 < n then [childNode (q.2 * q.1)] else []))
          ∈ shape.map (fun q => (q.1, (if 2 ≤ q.2 ∧ q.2 * q.1 < n then [childNode (q.2 * q.1)] else []))) := by
        rw [← hgeq, List.mem_map]; exact ⟨q, hq, rfl⟩
      rw [List.mem_map] at hqimg
      obtain ⟨q', hq', hqq'⟩ := hqimg
      -- q' is a shape entry (guard-true), so its g-image has a nonempty child; hence q's does too.
      rw [if_pos (hgshape q' hq')] at hqq'
      have hchild := congrArg Prod.snd hqq'
      simp only at hchild
      by_contra hg
      rw [if_neg hg] at hchild
      exact absurd hchild.symm (by simp)
    have hraw : sortedFactorPairs (B.fRootCtx p N hN f) = shape :=
      list_eq_of_erase_eq (fun q hq => (hsfpos q hq).1) hsfg hgshape hgeq
    have hpsh : polyShape p (residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))
        = (shape : Multiset (ℕ × ℕ)) := by rw [← hbridge, hraw]
    rw [inCell_mkCell_iff p hPmenu hSF]
    refine ⟨hexact, ?_⟩
    rw [hsingle]
    exact List.Forall₂.cons ⟨hside, hpsh⟩ List.Forall₂.nil
  · -- forward: InCell → classify = TselfloopChildful (LANDED).
    intro hInCell
    exact classify_eq_childful_of_inCell n N hN hn ([((0:ℕ),H),((n:ℕ),(0:ℕ))] : List (ℕ × ℕ))
      hPmenu (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) hsingle shape hSF hnodup f hInCell

#print axioms classify_eq_childful_iff

/-! ## 8. The `omCount` bridge `TselfloopChildful ↔ oneSideShapeChildful`.

`omCount` reads a shape only through `configOf`: the polygon slot via `newtonExponent` (bridged for
`toSideFace (mkSide pr)` vs `mkPoly` by `ClassifierBridgeFiber.newtonExponent_toSideFace_eq_mkPoly`),
the faces via `dS`/`cellMult`/`cellResDeg` (SIZE slot only), and the children via `omChildCount`
(pivots on `treeSize` = SIZE slot).  The classifier child node `childNode (μ·D) = ⟨[(1,μD,0)],[]⟩`
and `PathShapeChildful.childShape (μ·D) = ⟨[(2,μD,0)],[]⟩` differ ONLY in the order slot (1 vs 2),
which every `omCount` reader ignores — so the two shapes have equal `omChildCount` and equal
`omCount`. -/

/-- **`omChildCount` on the classifier child node** `childNode sz = ⟨[(1, sz, 0)], []⟩`.  Identical
to `PathShapeChildful.omChildCount_childShape'` (order slot `1` vs `2` invisible): empty payload ⇒
empty WF cell list ⇒ `mCell = 1`, `volExp = 0`, no children, `treeSize = sz` ⇒ collapses to the bare
pivot `1 / countPivot sz`. -/
theorem omChildCount_childNode (sz : ℕ) (q : ℕ) :
    OMCountV2.omChildCount (childNode sz) q = 1 / MontesAxiom.countPivot sz q := by
  have hcs : M7.cellsOfShapeWF (childNode sz) = [] := by
    rw [M7.cellsOfShapeWF_eq_of_descend]
    · rfl
    · intro c hc; simp [M7.cellsOfShape, childNode] at hc
  rw [omChildCount_rec]
  simp only [configsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hchild : (configOf (childNode sz)).children = [] := by unfold configOf; rw [hcs]; rfl
  have hm : mCell (configOf (childNode sz)) q = 1 := by
    unfold mCell configOf; rw [hcs]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    unfold choicePoly; simp
  have hv : volExp (configOf (childNode sz)) = 0 := by unfold volExp configOf; rw [hcs]; rfl
  have htree : M6.treeSize (childNode sz) = sz := rfl
  rw [hchild, hm, hv, htree]; simp

/-- **`omChildCount (childNode sz) = omChildCount (childShape sz)`.**  Both collapse to
`1 / countPivot sz`, the order-slot mismatch (1 vs 2) being invisible to every `omCount` reader. -/
theorem omChildCount_childNode_eq_childShape (sz q : ℕ) :
    OMCountV2.omChildCount (childNode sz) q = OMCountV2.omChildCount (childShape sz) q := by
  rw [omChildCount_childNode, PathShapeChildful.omChildCount_childShape']

/-- **The WF cell list of `TselfloopChildful`** (hlt regime).  Mirror of
`PathShapeChildful.cellsOfShapeWF_oneSideShapeChildful`: every per-factor cell is kept, and the
emitted `childNode (μ·D)` strictly descends (`nodeSizeOf = μ·D < s` under `hlt`). -/
theorem cellsOfShapeWF_TselfloopChildful (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (shape : List (ℕ × ℕ)) (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) :
    M7.cellsOfShapeWF (TselfloopChildful s pr shape)
      = shape.map (fun q =>
          ({ dS := q.1, δ := 1, polygon := M7.toSideFace (mkSide pr),
             children := (if 2 ≤ q.2 ∧ q.2 * q.1 < s then [childNode (q.2 * q.1)] else []) }
             : CountCell)) := by
  rw [M7.cellsOfShapeWF_eq_of_descend]
  · rw [M7.cellsOfShape, TselfloopChildful, List.map_map]; rfl
  · intro c hc ch hch
    rw [M7.cellsOfShape, TselfloopChildful, List.map_map, List.mem_map] at hc
    obtain ⟨q, hq, rfl⟩ := hc
    have hT : M5.nodeSizeOf (TselfloopChildful s pr shape) = s := rfl
    rw [hT]
    simp only [Function.comp_apply] at hch
    by_cases hg : 2 ≤ q.2 ∧ q.2 * q.1 < s
    · rw [if_pos hg, List.mem_singleton] at hch
      subst hch
      have hchsz : M5.nodeSizeOf (childNode (q.2 * q.1)) = q.2 * q.1 := rfl
      rw [hchsz]; exact hg.2
    · rw [if_neg hg] at hch; exact absurd hch List.not_mem_nil

/-- **`omCount_TselfloopChildful_eq`.**  On a self-loop side `pr = ((0,H),(s,0))`, the respelled
childful shape `TselfloopChildful` and the stylized `PathShapeChildful.oneSideShapeChildful` evaluate
to the SAME `omCount` (any `q`).  `omCount` reads only through `configOf`: the polygon `newtonExponent`
agrees (`newtonExponent_toSideFace_eq_mkPoly`), the single face (`nodeDelta`/`dS`/`cellMult`/`dF`)
reads only the size slot and child SIZES — identical for `childNode (μ·D)` vs `childShape (μ·D)` — and
the descent-child `omChildCount`s agree (`omChildCount_childNode_eq_childShape`).  This transports
`PathShapeChildful.omCount_oneSideShapeChildful_closed` to the respelled shape. -/
theorem omCount_TselfloopChildful_eq {H s : ℕ} (shape : List (ℕ × ℕ)) (hne : shape ≠ [])
    (hlt : ∀ q ∈ shape, 2 ≤ q.2 → q.2 * q.1 < s) (q : ℕ) :
    OMCountV2.omCount (TselfloopChildful s (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape) q
      = OMCountV2.omCount (PathShapeChildful.oneSideShapeChildful s
          (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape) q := by
  set pr := (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) with hpr
  rw [omCount, omCount]
  simp only [configsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  -- both WF cell lists (childful, hlt).
  have hcwfT := cellsOfShapeWF_TselfloopChildful s pr shape hlt
  have hcwfO := PathShapeChildful.cellsOfShapeWF_oneSideShapeChildful s pr shape hlt
  -- mCell: faces read (nodeDelta, (dS, cellMult), Σ cellResDeg) — cellMult/cellResDeg read child
  -- SIZES; childNode/childShape share size μ·D, so faces AGREE.
  -- the single FaceAssign agrees: nodeDelta (head δ=1), faceShape (dS, cellMult), dF (Σ cellResDeg).
  have hnodeDelta : Order0.nodeDelta (M7.cellsOfShapeWF (TselfloopChildful s pr shape))
      = Order0.nodeDelta (M7.cellsOfShapeWF (PathShapeChildful.oneSideShapeChildful s pr shape)) := by
    rw [hcwfT, hcwfO]
    cases shape with
    | nil => exact absurd rfl hne
    | cons a t => rfl
  have hfaceShape : (M7.cellsOfShapeWF (TselfloopChildful s pr shape)).map (fun c => (c.dS, cellMult c))
      = (M7.cellsOfShapeWF (PathShapeChildful.oneSideShapeChildful s pr shape)).map
          (fun c => (c.dS, cellMult c)) := by
    rw [hcwfT, hcwfO, List.map_map, List.map_map]
    apply List.map_congr_left
    intro q _
    -- the two per-factor cells differ only in polygon and child node (childNode vs childShape);
    -- both have the SAME child SIZE μ·D, so `cellMult` (= children.map nodeSizeOf) agrees.
    show ((_ : CountCell).dS, cellMult _) = ((_ : CountCell).dS, cellMult _)
    by_cases hg : 2 ≤ q.2 ∧ q.2 * q.1 < s
    · simp only [cellMult, if_pos hg, List.isEmpty_cons, Bool.false_eq_true, if_false,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rfl
    · simp only [cellMult, if_neg hg, List.isEmpty_nil, if_true]
  have hdF : ((M7.cellsOfShapeWF (TselfloopChildful s pr shape)).map cellResDeg).sum
      = ((M7.cellsOfShapeWF (PathShapeChildful.oneSideShapeChildful s pr shape)).map cellResDeg).sum := by
    rw [hcwfT, hcwfO, List.map_map, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q _
    show cellResDeg _ = cellResDeg _
    by_cases hg : 2 ≤ q.2 ∧ q.2 * q.1 < s
    · simp only [cellResDeg, if_pos hg, List.isEmpty_cons, Bool.false_eq_true, if_false,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rfl
    · simp only [cellResDeg, if_neg hg, List.isEmpty_nil, if_true]
  have hfaces : (configOf (TselfloopChildful s pr shape)).faces
      = (configOf (PathShapeChildful.oneSideShapeChildful s pr shape)).faces := by
    unfold configOf
    simp only []
    rw [hnodeDelta, hfaceShape, hdF]
  -- volExp: newtonExponent(polygon) + dF; polygon bridged, dF equal (hfaces).
  have hvol : volExp (configOf (TselfloopChildful s pr shape))
      = volExp (configOf (PathShapeChildful.oneSideShapeChildful s pr shape)) := by
    rw [volExp, volExp, hfaces]
    congr 1
    unfold configOf
    rw [hcwfT, hcwfO]
    cases shape with
    | nil => exact absurd rfl hne
    | cons a t =>
        simp only [List.map_cons, List.head?_cons, Option.map_some, Option.getD_some]
        exact ClassifierBridgeFiber.newtonExponent_toSideFace_eq_mkPoly
  -- children product: per emitted child, omChildCount (childNode μD) = omChildCount (childShape μD).
  have hchild : (configOf (TselfloopChildful s pr shape)).children.map
        (fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D)))
      = (configOf (PathShapeChildful.oneSideShapeChildful s pr shape)).children.map
        (fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D))) := by
    -- nodeDelta agrees on both WF lists.
    have hndT : Order0.nodeDelta (M7.cellsOfShapeWF (TselfloopChildful s pr shape)) = 1 := by
      rw [hcwfT]; cases shape with | nil => exact absurd rfl hne | cons a t => rfl
    have hndO : Order0.nodeDelta (M7.cellsOfShapeWF (PathShapeChildful.oneSideShapeChildful s pr shape)) = 1 := by
      rw [hcwfO]; cases shape with | nil => exact absurd rfl hne | cons a t => rfl
    -- configOf.children = cellsWF.flatMap (children.map childData); reduce both to shape.flatMap.
    unfold configOf
    simp only []
    rw [hndT, hndO, hcwfT, hcwfO, List.flatMap_map, List.flatMap_map, List.map_flatMap, List.map_flatMap]
    apply List.flatMap_congr
    intro qq _
    -- per shape element: the (childNode vs childShape) child maps to equal omChildCount.
    by_cases hg : 2 ≤ qq.2 ∧ qq.2 * qq.1 < s
    · simp only [Function.comp_apply, if_pos hg, List.map_cons, List.map_nil]
      rw [omChildCount_childNode_eq_childShape]
    · simp only [Function.comp_apply, if_neg hg, List.map_nil]
  rw [mCell, mCell, hfaces, hvol, hchild]

#print axioms omCount_TselfloopChildful_eq

/-! ## 9. The `stratumCount_childful_R` discharge (pivot-free). -/

/-- **`stratumCount_childful_R`.**  The schematic `M8.stratumCount (M9.rawCount n)` count of the
respelled childful shape `TselfloopChildful n pr shape` equals the genuine order-1 stratum count
`stratumCount1 realP n N (mkCell n P [shape])` (cast to ℚ), on the all-childful, distinct-degree,
hlt locus.  Analogue of `ClassifierBridgeFiber2.stratumCount_selfloop_R`: `rfl`-unfold of the
schematic count to the `Nat.card` classify fiber, `stratumCount1_eq_cellCard`, then `Nat.card_congr`
on `classify_eq_childful_iff` at `realP`.  PIVOT-FREE — no density/limit statement is involved. -/
theorem stratumCount_childful_R (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (P : List (ℕ × ℕ)) (hPmenu : MenuPath n N P) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (hsingle : sidePairs P = [pr])
    (shape : List (ℕ × ℕ)) (hSF : ShapesFor P [shape]) (hne : shape ≠ [])
    (hnodup : (shape.map Prod.fst).Nodup)
    (hallμ : ∀ q ∈ shape, 2 ≤ q.2) (hlt : ∀ q ∈ shape, q.2 * q.1 < n) :
    M8.stratumCount (M9.rawCount n) (TselfloopChildful n pr shape) N
      = ((StratumOrder1.stratumCount1 M9.realP n N (mkCell n P [shape]) : ℕ) : ℚ) := by
  show ((M9.rawCount n (TselfloopChildful n pr shape) N : ℕ) : ℚ) = _
  rw [show M9.rawCount n (TselfloopChildful n pr shape) N
      = Nat.card {f : QuotientBox.monicBox M9.realP N n //
          B.classify M9.realP n N f = TselfloopChildful n pr shape} from rfl]
  rw [StratumOrder1.stratumCount1_eq_cellCard]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight
    (fun f => classify_eq_childful_iff n N hN hn P hPmenu pr hsingle shape hSF hne hnodup hallμ hlt f))

#print axioms stratumCount_childful_R

end LeanUrat.OM.ClassifierBridgeChildful
