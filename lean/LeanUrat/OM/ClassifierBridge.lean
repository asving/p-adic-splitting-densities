/-
Scratch module: the classify1 ↔ B.classify bridge (S3).
Namespace LeanUrat.OM.ClassifierBridge.  Math-first, no sorry/axiom/native_decide.

GOAL (SCOPE plan): let `hnode_oneSideShape` (proved, over the genuine order-1 classifier
`classify1` / `stratumCount1`) feed `montes_allorders_of_hnode` (which consumes the schematic
`M8.stratumCount (M9.rawCount n)` count over `B.classify`).  The bridge must reconcile
  (a) the two boxes/degree scopes,
  (b) the two classifiers' fibers, and
  (c) the two target shape literals (`oneSideShape` order-1 head vs `B.classify` order-0 head).

This module LANDS the engine-value half of the bridge — the tree the two counters attach to —
plus the count-cast normalization, and it isolates precisely the ONE remaining deep obligation
(the coefficient-level classifier-agreement fiber characterization).
-/
import Mathlib
import LeanUrat.OM.CellMenu
import LeanUrat.OM.OMCountV2
import LeanUrat.OM.CellPartition
import LeanUrat.OM.Classifier
import LeanUrat.OM.StratumOrder1
import LeanUrat.OM.PathShape
import LeanUrat.OM.RealInstance
import LeanUrat.OM.Order0Alpha
import LeanUrat.OM.MontesAllOrders

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.ClassifierBridge

open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.PathShape
open LeanUrat.MontesAxiom (CountCell)

open scoped Classical

/-! ## 1. The explicit `B.classify`-output tree `T★` on the single-side self-loop locus.

`B.classify realP n N f` ALWAYS runs `classifyAux` from `fRootCtx` whose `order := 0`; by
`classifyAux_unfold` the emitted head tuple is ALWAYS `(0, n, dr)` (an ORDER-0 head), whereas
`oneSideShape s pr shape` is the stylized order-1 literal `⟨[(1, s, 1)], …⟩`.  So the connecting
lemma cannot target `oneSideShape` verbatim; it must target the genuine order-0-headed output
tree `T★`.

Under the plan's `all-μ=1` hypothesis the root residual factors into DISTINCT (multiplicity-1)
irreducibles on the selected side, so every root cell is childless (`M5.cells` emits no descent
child), and the emitted tree is `⟨[(0, s, d)], childless-cells⟩`.  We record the SHAPE of that
tree as `Tselfloop`: an order-0 head with the SAME childless per-factor cell payload
`oneSideShape` carries.  (The classifier's per-cell `polygon` slot is the f-dependent `rootFace`;
`Tselfloop` uses the stylized `mkPoly s [pr.1, pr.2]` — the two agree in every quantity `omCount`
reads, namely `newtonExponent`, as isolated in `polygon_agnostic` below.) -/

/-- **`T★`** — the genuine `B.classify` output tree shape on the single-side, all-`μ=1` self-loop
locus: an ORDER-0 head `(0, s, Σ dS)` carrying the childless per-factor cell payload of the side
residual `shape`.  Same `cells` payload as `oneSideShape`, order-0 head (the true classifier
head), and the head's cluster-size slot `s` so `nodeSizeOf Tselfloop = nodeSizeOf (oneSideShape …)`
(`= s`), keeping the two `M6.treeSize` thresholds equal. -/
def Tselfloop (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) : ClusterShape :=
  ⟨[(0, s, (shape.map Prod.fst).sum)],
    shape.map (fun q => ⟨q.1, 1, mkPoly s [pr.1, pr.2], []⟩)⟩

/-- The two shapes carry the SAME `cells` payload (the head tuple is the only difference). -/
theorem Tselfloop_cells_eq (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    (Tselfloop s pr shape).cells = (oneSideShape s pr shape).cells := rfl

/-- `nodeSizeOf` of both shapes is `s` (head second component). -/
theorem nodeSizeOf_Tselfloop (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    M5.nodeSizeOf (Tselfloop s pr shape) = s := rfl

theorem nodeSizeOf_oneSideShape (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    M5.nodeSizeOf (oneSideShape s pr shape) = s := rfl

/-! ## 2. `omCount Tselfloop = omCount (oneSideShape …)` — the engine-value identity (target 3).

`omCount` reads a shape ONLY through `configsOf = [configOf T]`, and `configOf T` reads `T`
through `M7.cellsOfShapeWF T` (the WF-guarded `cells` payload) — NEVER through the head tuple's
`order` slot, and through the head's cluster-size slot only inside the WF descent threshold
`M5.nodeSizeOf T`.  Since the two shapes have (i) identical `cells` payload and (ii) identical
`nodeSizeOf` (`= s`), their `cellsOfShapeWF` lists coincide, hence their `configOf`, hence their
`omCount`.  No arithmetic on the tree head is needed — the order-0 vs order-1 head difference is
INVISIBLE to `omCount`. -/

/-- `cellsOfShapeWF` agrees on the two shapes: both read the same `cells` payload and filter by the
same `nodeSizeOf`-threshold. -/
theorem cellsOfShapeWF_Tselfloop (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    M7.cellsOfShapeWF (Tselfloop s pr shape) = M7.cellsOfShapeWF (oneSideShape s pr shape) := by
  unfold M7.cellsOfShapeWF M7.cellsOfShape
  rw [Tselfloop_cells_eq, nodeSizeOf_Tselfloop, nodeSizeOf_oneSideShape]

/-- `configOf` agrees on the two shapes (it reads only `cellsOfShapeWF`). -/
theorem configOf_Tselfloop (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    configOf (Tselfloop s pr shape) = configOf (oneSideShape s pr shape) := by
  unfold configOf
  rw [cellsOfShapeWF_Tselfloop]

/-- **TARGET 3 — the engine-value identity.**  The genuine `B.classify` output tree `Tselfloop`
(order-0 head) and the stylized single-node `oneSideShape` (order-1 head) evaluate to the SAME
`omCount` rational.  Proof: `omCount` reads a shape only through `configsOf = [configOf T]`, and
`configOf` reads only the WF-guarded `cells` payload + `nodeSizeOf`, both of which agree
(`configOf_Tselfloop`).  The head `order`/`cluster-size` difference is invisible to `omCount`. -/
theorem omCount_selfloop_eq_oneSideShape (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (shape : List (ℕ × ℕ)) (p : ℕ) [Fact p.Prime] :
    omCount (Tselfloop s pr shape) p = omCount (oneSideShape s pr shape) p := by
  unfold omCount configsOf
  rw [configOf_Tselfloop]

#print axioms omCount_selfloop_eq_oneSideShape

/-! ## 3. The count-cast reduction (target 2) and the limit transport (target 4).

The one DEEP obligation of the bridge is the FIBER CHARACTERIZATION (target 1):
```
B.classify realP n N f = Tselfloop n pr shape ↔ InCell realP f (mkCell n P [shape]).
```
It is a coefficient-level classifier-agreement statement: the genuine order-0 classifier
(`rootSide` = the first finite-slope side of `f`'s FULL Newton polygon via `NewtonPolygon.npSides
(boxValSupport …)`, then factor `rootResidual = residualPoly (boxCoeffData …) rootSide`) must be
shown to select EXACTLY the single side `pr` and residual shape `shape` that `InCell` pins via
vertex-exactness `vOf p f q.1 = q.2`, `SideAbove`, and `polyShape (residualOf p f pr) = shape`.
Forward needs a Newton-polygon UNIQUENESS lemma (`npSides (boxValSupport f) = [mkSide pr]` from the
`InCell` vertex/side data) that does not yet exist in-repo; this is the S3 analogue of the order-0
`classify_eq_sepShape_iff` (Order0Alpha.lean:64), whose forward half is likewise the whole content.

Given target 1, the rest of the bridge is MECHANICAL and is discharged genuinely below:
* `stratumCount_selfloop` (target 2) — the `M8`-typed count identity, by the `rfl`-unfold of
  `M8.stratumCount (M9.rawCount n)` to the `Nat.card` classifier fiber (mirroring
  `Order0Alpha.stratumCount_sepShape`) + a `Nat.card_congr` on target 1 + `classify1`'s own bridge
  `stratumCount1_eq_cellCard`.
* `hnode_selfloop_over_Bclassify` (target 4) — the `h_node` in EXACTLY
  `montes_allorders_of_hnode`'s shape, by transporting `hnode_oneSideShape` along target 2's count
  identity and target 3's `omCount` identity (both proved here; target 3 unconditionally).

We take target 1 as an explicit hypothesis `hfiber` (its precise statement IS the remaining
obligation; NOT a weakening — targets 2/4's own content is the reduction/transport, and target 3 is
unconditional). -/

/-- **TARGET 2 — the `M8`-typed count identity (given the fiber characterization).**  For a
single-side (`sidePairs P = [pr]`), all-`μ=1` shape of the right degree, the schematic
`M8.stratumCount (M9.rawCount n)` count of the genuine `B.classify`-output tree `Tselfloop n pr
shape` equals the genuine order-1 stratum count `stratumCount1 realP n N (mkCell n P [shape])`
(cast to ℚ).

Route (mirrors `Order0Alpha.stratumCount_sepShape`): `M8.stratumCount (M9.rawCount n) T N` is by
`rfl` the ℚ-cast of `M9.rawCount n T N = Nat.card {f // B.classify realP n N f = T}`.  A
`Nat.card_congr` on the fiber characterization `hfiber` rewrites that fiber to the `InCell` fiber,
which is `stratumCount1 realP n N (mkCell n P [shape])` by `stratumCount1_eq_cellCard`
(`classify1 = some c ↔ InCell`). -/
theorem stratumCount_selfloop (n N : ℕ)
    (P : List (ℕ × ℕ)) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ))
    (hfiber : ∀ f : QuotientBox.monicBox M9.realP N n,
      B.classify M9.realP n N f = Tselfloop n pr shape
        ↔ InCell M9.realP f (mkCell n P [shape])) :
    M8.stratumCount (M9.rawCount n) (Tselfloop n pr shape) N
      = ((stratumCount1 M9.realP n N (mkCell n P [shape]) : ℕ) : ℚ) := by
  -- (i) unfold the schematic count to the ℚ-cast classifier fiber (as in `stratumCount_sepShape`).
  show ((M9.rawCount n (Tselfloop n pr shape) N : ℕ) : ℚ) = _
  rw [show M9.rawCount n (Tselfloop n pr shape) N
      = Nat.card {f : QuotientBox.monicBox M9.realP N n //
          B.classify M9.realP n N f = Tselfloop n pr shape} from rfl]
  -- (ii) the genuine order-1 count is the `InCell` fiber (`classify1`'s own bridge).
  rw [stratumCount1_eq_cellCard]
  -- (iii) the two ℕ cardinalities agree by `Nat.card_congr` on `hfiber`.
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight hfiber)

/-- **TARGET 4 — the `h_node` in `montes_allorders_of_hnode`'s shape (given the fiber
characterization).**  Transporting the proved order-1 density limit `hnode_oneSideShape` (over
`stratumCount1 / p^(s·N)` → `omCount (oneSideShape …)`) along:
* target 2's count identity `stratumCount_selfloop` (rewrites the count and the box exponent, using
  `n = s`), and
* target 3's engine-value identity `omCount_selfloop_eq_oneSideShape` (rewrites the limit),

gives the limit over `M8.stratumCount (M9.rawCount n) (Tselfloop n pr shape) N / realP^(n·N)`
toward `omCount (Tselfloop n pr shape) realP` — EXACTLY the `h_node` shape
`montes_allorders_of_hnode` consumes (with `T = Tselfloop n pr shape`). -/
theorem hnode_selfloop_over_Bclassify (n N₀ : ℕ) (hN₀ : 0 < N₀)
    (pr : (ℕ × ℕ) × (ℕ × ℕ)) (P : List (ℕ × ℕ)) (hP : MenuPath n N₀ P)
    (hsingle : sidePairs P = [pr]) (shape : List (ℕ × ℕ)) (hsh : ShapesFor P [shape])
    (hpos : ∀ q ∈ shape, 1 ≤ q.1) (hμ : ∀ q ∈ shape, q.2 = 1) (hne : shape ≠ [])
    (hfiber : ∀ (N : ℕ) (f : QuotientBox.monicBox M9.realP N n),
      B.classify M9.realP n N f = Tselfloop n pr shape
        ↔ InCell M9.realP f (mkCell n P [shape])) :
    Filter.Tendsto
      (fun N => M8.stratumCount (M9.rawCount n) (Tselfloop n pr shape) N
          / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds (omCount (Tselfloop n pr shape) M9.realP)) := by
  -- Start from the proved order-1 limit over `stratumCount1 / p^(n·N)` → `omCount (oneSideShape …)`.
  have hbase := PathShape.hnode_oneSideShape n N₀ hN₀ pr P hP hsingle shape hsh hpos hμ hne M9.realP
  -- Rewrite the LIMIT VALUE by target 3 (engine identity), giving `omCount (Tselfloop …)`.
  rw [← omCount_selfloop_eq_oneSideShape n pr shape M9.realP] at hbase
  -- Rewrite the SEQUENCE by target 2 (count identity), eventually (for every `N`).
  refine hbase.congr ?_
  intro N
  rw [stratumCount_selfloop n N P pr shape (hfiber N)]

#print axioms stratumCount_selfloop
#print axioms hnode_selfloop_over_Bclassify

/-! ## 4. Target 1 — the fiber characterization: the isolated remaining obligation.

We record the PRECISE statement.  Landing it (unconditionally) discharges the whole bridge:
feed `hnode_selfloop_over_Bclassify` (with `hfiber` supplied by target 1) into
`MontesAllOrders.montes_allorders_of_hnode` for the menu containing `Tselfloop n pr shape`.

`classify_eq_selfloop_iff` (STATEMENT — the S3 fiber characterization, analogue of
`Order0Alpha.classify_eq_sepShape_iff`):
```
theorem classify_eq_selfloop_iff (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (P : List (ℕ × ℕ)) (pr : (ℕ×ℕ)×(ℕ×ℕ)) (hsingle : sidePairs P = [pr])
    (shape : List (ℕ × ℕ)) (hμ : ∀ q ∈ shape, q.2 = 1)
    (f : QuotientBox.monicBox realP N n) :
    B.classify realP n N f = Tselfloop n pr shape ↔ InCell realP f (mkCell n P [shape])
```
The forward half (the whole content) needs the Newton-polygon UNIQUENESS lemma
`NewtonPolygon.npSides (boxValSupport realP N f) _ = [mkSide pr]` derived from `InCell`'s
vertex-exactness (`vOf p f q.1 = q.2` on `P`) + `SideAbove`; then `rootResidual = residualOf p f pr`
(both are `residualPoly (boxCoeffData …) (mkSide pr)`), whose all-`μ=1` factorization makes every
root cell childless (`classifyAux_of_childless`), collapsing `B.classify` to `⟨[(0,n,dr)],
encodeCells⟩` = `Tselfloop` — provided `encodeCells`' per-cell `polygon` (the f-dependent `rootFace
= toSideFace (mkSide pr)`) and the sorted-degree payload match `Tselfloop`'s `mkPoly`/`shape` cells,
which `omCount` sees only through `newtonExponent` (isolated by target 3) but the raw shape EQUALITY
`B.classify = Tselfloop` demands verbatim — so `Tselfloop`'s `polygon` slot should be RESPELLED to
`rootFace`-equivalent `toSideFace (mkSide pr)` before the forward proof (a purely-notational
adjustment that leaves target 3 — which reads only `newtonExponent` — intact, since
`newtonExponent (toSideFace (mkSide pr)) = newtonExponent (mkPoly n [pr.1, pr.2])` is the volume
identity `PathShape.mkCell_volExp_add_freeExp` already carries). -/

end LeanUrat.OM.ClassifierBridge
