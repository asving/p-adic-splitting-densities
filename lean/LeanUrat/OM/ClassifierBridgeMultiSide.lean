/-
Scratch module (S3, MULTI-SIDE FIBER BRIDGE): the multi-side `B.classify` fiber characterization
and its tie to the product-of-`omCount`s stratum density.  Namespace
`LeanUrat.OM.ClassifierBridgeMultiSide`.  Math-first, no sorry/axiom/native_decide.

DECISIVE SEMANTIC FINDING (this module records + formalizes it).  `B.classify` does NOT split a
multi-side polynomial into per-slope branches at the root node.  `rootSide`
(`Classifier.lean:159-161`) is literally `NewtonPolygon.npSides(boxValSupport …).head?` — it selects
the FIRST finite-slope side ONLY.  `fRootCtx` sets `Nr := toSideFace(that one side)`,
`Rr := rootResidual(that one side)`; `M5.cells` factors that ONE residual into one cell per distinct
irreducible factor, and EVERY cell carries the SAME polygon `T.Nr` (the single first-side face).  So
the classifier's per-node output is a SINGLE-SIDE-headed shape (`ClassifierBridgeFiber.Tselfloop`),
and the multi-slope factorization ("theorem of the product") is Hensel content living in a SEPARATE
layer (`ProductTheorem`/block-product), never inside one `B.classify` node.

CONSEQUENCE.  For a MULTI-side `mkCell n P sh` (`P` with ≥ 2 sides), `B.classify f` reads back ONLY
the first side `pr₀`.  A `classify = Tselfloop n pr₀ shape₀`-style equality can therefore characterize
only the FIRST-SIDE projection of `Matches` — `SideAbove f pr₀ ∧ polyShape(residualOf f pr₀) = shape₀`
— NOT the full multi-side `InCell` (which is vertex-exactness ∧ `Forall₂ SideMatch` over ALL sides,
`CellMenu.lean:1259-1267`).  So there is NO singleton `B.classify` menu whose fiber equals the
multi-side `InCell` fiber, and the multi-side density CANNOT be delivered by instantiating
`montes_allorders_of_hnode` at a singleton menu the way `montes_order1_selfloop_density` does.

CORRECT FRAMING.  The stratum side is ALREADY done via `InCell`, bypassing `B.classify` entirely:
`stratumCount1 p s N c = #{f | InCell p f c}` (`StratumOrder1`), and
`PathShapeMultiSideTree.hnode_multiSideProduct` already proves
`stratumCount1 p s N (mkCell s P sh)/p^{sN} → ∏_side omCount(sideSubShape pr shape)` for all-`μ=1`
nonempty multi-side paths.  The product tie `prod_omCount_eq_blockCardinality` is also proven.  What
is NOT closed is wiring this into `omDensityV2` (a `Finset`-sum of single-shape `omCount`s): the
product is not a single `omCount` summand, so it must be assembled by the `ProductTheorem`
block-cardinality layer whose ⊆ half is `obligation_hensel_surjective` — a NAMED OBLIGATION, not a
theorem.

DELIVERABLES (this module):
  STEP 1  `classify_multiSide_firstSide_projection` — the POSITIVE first-side-projection lemma:
          `classify f = Tselfloop n ((0,H),(n,0)) shape₀` implies the first-side match
          `SideAbove f ((0,H),(n,0)) ∧ polyShape(residualOf f ((0,H),(n,0))) = shape₀`.  This is the
          genuine content of a (multi-side) classifier node, reusing the first-side-only Steps A/B/C
          of `ClassifierBridgeFiber2` verbatim.
  STEP 2  `inCell_multiSide_imp_classify_firstSide` — the strict-refinement / framing theorem:
          multi-side `InCell f (mkCell n P sh)` is FINER than any single `B.classify` fiber (it
          implies the first-side `SideMatch`, but the classifier does not read sides 2..k).  The
          converse is a DOCUMENTED non-implication (no theorem stated).
  STEP 3  `hnode_multiSideProduct_reexport` + `prod_omCount_eq_blockCardinality_reexport` — the
          product-density tie, re-exported UNCONDITIONALLY from `PathShapeMultiSideTree`.
  STEP 4  `omDensityMultiSide_of_sides` — DOCUMENTED OPEN, NOT a theorem (blocked on
          `ProductTheorem.obligation_hensel_surjective`); stated only as a docstring target.
-/
import LeanUrat.OM.ClassifierBridgeFiber2
import LeanUrat.OM.PathShapeMultiSideTree

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.ClassifierBridgeMultiSide

open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.PathShape
open LeanUrat.OM.PathShapeMultiSide
open LeanUrat.OM.PathShapeMultiSideTree

open scoped Classical

/-! ## STEP 1 — the POSITIVE first-side-projection of a `B.classify` node.

For a full-width self-loop side `pr₀ = ((0,H),(n,0))` with `1 ≤ H` and `H < N`, if the genuine
classifier collapses to the respelled `Tselfloop n pr₀ shape₀`, then `f` matches `pr₀` on the first
side: it is on/above the side (`SideAbove`) and its side-`pr₀` residual has factorization shape
`shape₀`.  This is EXACTLY the content that a (multi-side) `B.classify` node exposes — the head side
read — and it reuses the first-side-only Steps A/B/C of `ClassifierBridgeFiber2` verbatim.

`pr₀` here is the classifier's OWN first-side read (`rootSide`), which the emitted `Tselfloop`
determines to be `((0,H),(n,0))`; nothing about downstream sides 2..k of any multi-side menu enters.
The hypotheses `0 < H`, `H < N` are the level-`N` menu-path constraints on the head side (always true
on the density locus); they let us build the local single-side hull menu path the classifier's read
realizes. -/
theorem classify_multiSide_firstSide_projection
    {p : ℕ} [Fact p.Prime] {n N H : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hH0 : 0 < H) (hHN : H < N)
    (shape : List (ℕ × ℕ)) (hpos : ∀ q ∈ shape, 1 ≤ q.1) (hmu : ∀ q ∈ shape, q.2 = 1)
    (hne : shape ≠ [])
    (f : QuotientBox.monicBox p N n)
    (hcl : B.classify p n N f
      = ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape) :
    SideAbove p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
      ∧ polyShape p (residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))
          = (shape : Multiset (ℕ × ℕ)) := by
  -- Step A: rootSide = some (mkSide ((0,H),(n,0))) — reads ONLY npSides.head?.
  have hrs : B.rootSide p N hN f = some (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) :=
    ClassifierBridgeFiber2.rootSide_eq_of_classify hn hN f shape hcl hne
  -- npVertices = [(0,H),(n,0)]  (the single-side hull the classifier's read realizes).
  have hverts := ClassifierBridgeFiber.npVertices_of_rootSide p hn hN f hrs
  -- Step B: SideAbove + vertex-exactness off the two-vertex hull.
  obtain ⟨hside, hv0, hvn⟩ :=
    ClassifierBridgeFiber2.sideAbove_of_npVertices p hn hN hH0 hHN f hverts
  refine ⟨hside, ?_⟩
  -- Build the LOCAL single-side menu path the classifier's read realizes (from H, hH0, hHN);
  -- this is `f`'s own head-side hull, NOT any ambient multi-side menu.
  set P0 : List (ℕ × ℕ) := [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))] with hP0def
  have hP0 : MenuPath n N P0 := by
    refine ⟨H, ((n : ℕ), (0 : ℕ)), [], rfl, hH0, by omega, hn, by omega, ChainOK.nil rfl rfl⟩
  have hsingle : sidePairs P0 = [(((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))] := rfl
  -- vertex-exactness for P0 (from hv0, hvn).
  have hexact : ∀ q ∈ P0, vOf p f q.1 = q.2 := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq2
    · simpa using hv0
    · rcases List.mem_cons.mp hq2 with rfl | hq3
      · simpa using hvn
      · simp at hq3
  -- rootResidual = residualOf f pr₀  (via the LOCAL single-side path P0).
  have hRr : B.rootResidual p N hN f = residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) :=
    ClassifierBridgeFiber.rootResidual_eq_residualOf p hn hN f hP0 hexact hsingle hv0 hHN hside
  have hRne : residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ≠ 0 := by
    have hpr_mem : (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ sidePairs P0 := by rw [hsingle]; simp
    exact (residual_facts p hN hP0 hexact hpr_mem).1
  -- Step C: polyShape (residualOf f pr₀) = shape (first-side residual read).
  obtain ⟨hpsh, _⟩ :=
    ClassifierBridgeFiber2.polyShape_residual_of_classify hN f
      (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape hcl hRr hRne hpos hmu
  exact hpsh

#print axioms classify_multiSide_firstSide_projection

/-! ## STEP 2 — the NEGATIVE characterization / strict-refinement framing theorem.

The multi-side `InCell` fiber is strictly FINER than any single `B.classify` fiber.  Concretely,
`InCell f (mkCell n P sh)` implies the first-side `SideMatch` (`SideAbove f pr₀` and
`polyShape(residualOf f pr₀) = sh₀`), which is exactly the datum a `B.classify` node exposes (STEP 1).
But the classifier reads back ONLY `pr₀`; it never sees sides 2..k of a multi-side `P`.  Hence the
first-side projection does NOT recover the full `Matches` (which additionally requires vertex-exactness
at EVERY vertex and a `SideMatch` on EVERY side).  This is the formal statement that the multi-side
density must NOT route through a `B.classify` singleton menu.

The forward implication below is a clean theorem.  The converse (first-side projection ⟹ full
multi-side `InCell`) is a DOCUMENTED NON-implication — it is FALSE whenever `P` has ≥ 2 sides (a
witness `f` can match `pr₀` on the head side while violating a downstream side's `SideMatch` or a
downstream vertex-exactness) — and is deliberately NOT stated as a theorem. -/
theorem inCell_multiSide_imp_firstSide_sideMatch
    {p : ℕ} [Fact p.Prime] {n N : ℕ} {P : List (ℕ × ℕ)} {sh : List (List (ℕ × ℕ))}
    {pr₀ : (ℕ × ℕ) × (ℕ × ℕ)} {prTail : List ((ℕ × ℕ) × (ℕ × ℕ))} {sh₀ : List (ℕ × ℕ)}
    {shTail : List (List (ℕ × ℕ))}
    (hP : MenuPath n N P) (hsh : ShapesFor P sh)
    (hsp : sidePairs P = pr₀ :: prTail) (hsheq : sh = sh₀ :: shTail)
    (f : QuotientBox.monicBox p N n)
    (hIn : InCell p f (mkCell n P sh)) :
    SideAbove p f pr₀
      ∧ polyShape p (residualOf p f pr₀) = (sh₀ : Multiset (ℕ × ℕ)) := by
  -- InCell ↔ Matches at (P, sh); extract the head `SideMatch` off the `Forall₂`.
  rw [inCell_mkCell_iff p hP hsh] at hIn
  have hF := hIn.2
  rw [hsheq, hsp] at hF
  -- hF : Forall₂ SideMatch (sh₀ :: shTail) (pr₀ :: prTail); take the head.
  cases hF with
  | cons hhead _ => exact ⟨hhead.1, hhead.2⟩

#print axioms inCell_multiSide_imp_firstSide_sideMatch

/-- **STEP 2, packaged (TARGET 2).**  On a multi-side menu path whose head side is the full-width
self-loop `pr₀ = ((0,H),(n,0))`, the multi-side `InCell` fiber refines the `B.classify` first-side
read: `InCell f (mkCell n P sh)` implies the SAME first-side projection that STEP 1 reads off a
`classify = Tselfloop n pr₀ sh₀` node.  Thus the two fibers agree ONLY on the first side; the
classifier cannot see sides 2..k, so no singleton `B.classify` menu has the multi-side `InCell` as
its fiber (the density must NOT route through such a menu — see the STEP 4 docstring). -/
theorem inCell_multiSide_imp_classify_firstSide
    {p : ℕ} [Fact p.Prime] {n N H : ℕ} {P : List (ℕ × ℕ)} {sh : List (List (ℕ × ℕ))}
    {prTail : List ((ℕ × ℕ) × (ℕ × ℕ))} {sh₀ : List (ℕ × ℕ)} {shTail : List (List (ℕ × ℕ))}
    (hP : MenuPath n N P) (hsh : ShapesFor P sh)
    (hsp : sidePairs P = (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) :: prTail)
    (hsheq : sh = sh₀ :: shTail)
    (f : QuotientBox.monicBox p N n)
    (hIn : InCell p f (mkCell n P sh)) :
    SideAbove p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
      ∧ polyShape p (residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))
          = (sh₀ : Multiset (ℕ × ℕ)) :=
  inCell_multiSide_imp_firstSide_sideMatch hP hsh hsp hsheq f hIn

#print axioms inCell_multiSide_imp_classify_firstSide

/-! ## STEP 3 — the product-density tie, re-exported UNCONDITIONALLY from `PathShapeMultiSideTree`.

The genuine stratum density `stratumCount1 p s N (mkCell s P sh)/p^{sN}` (defined THROUGH `InCell`,
bypassing `B.classify`) converges to the PRODUCT over sides of the re-scoped single-side engine
literals `omCount (sideSubShape pr shape) p`.  Distinct Newton-slope branches MULTIPLY, so the limit
is a product of single-`ClusterShape` `omCount`s — NOT a single `omCount` (candidate (c) is FALSE) —
which is exactly the counting-side witness the `ProductTheorem` block-product layer consumes.  Both
re-exports below are copy-through of PROVEN results. -/

/-- **STEP 3 (TARGET 3) — the multi-side stratum limit as a PRODUCT of single-side `omCount`s.**
Unconditional re-export of `PathShapeMultiSideTree.hnode_multiSideProduct`. -/
theorem hnode_multiSideProduct_reexport (s N₀ : ℕ) (hN₀ : 0 < N₀) (P : List (ℕ × ℕ))
    (hP : MenuPath s N₀ P) (sh : List (List (ℕ × ℕ))) (hsh : ShapesFor P sh)
    (hμ : AllMuOne sh) (hne : AllNonempty sh) (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto (fun N => (stratumCount1 p s N (mkCell s P sh) : ℚ) / (p : ℚ) ^ (s * N))
      Filter.atTop
      (nhds ((List.zipWith (fun pr shape => omCount (sideSubShape pr shape) p)
        (sidePairs P) sh).prod)) :=
  hnode_multiSideProduct s N₀ hN₀ P hP sh hsh hμ hne p

#print axioms hnode_multiSideProduct_reexport

/-- **STEP 3 (TARGET 4) — the block-cardinality witness the `ProductTheorem` consumes.**  The product
over sides of the single-side `omCount`s equals `prodSC p sh` (the block-product cardinality,
`= ∏_side shapeCount`) times the single box-volume factor
`p^{−(newtonExponent(mkPoly s P) + Σ sideDeg)}`.  Unconditional re-export of
`PathShapeMultiSideTree.prod_omCount_eq_blockCardinality`. -/
theorem prod_omCount_eq_blockCardinality_reexport
    {s N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    (sh : List (List (ℕ × ℕ))) (hsh : ShapesFor P sh)
    (hμ : AllMuOne sh) (hne : AllNonempty sh) (p : ℕ) [Fact p.Prime] :
    (List.zipWith (fun pr shape => omCount (sideSubShape pr shape) p) (sidePairs P) sh).prod
      = (CellCard.prodSC p sh : ℚ)
          * ((p : ℚ) ^ (L4.newtonExponent (mkPoly s P) + ((sidePairs P).map sideDeg).sum))⁻¹ :=
  prod_omCount_eq_blockCardinality hP sh hsh hμ hne p

#print axioms prod_omCount_eq_blockCardinality_reexport

/-! ## Smallest genuine 2-side witness: `menuPath_s3c = [(0,2),(1,1),(3,0)]`.

The concrete 2-side instance the SCOPE names (`s = 3`, two sides `((0,2),(1,1))`, `((1,1),(3,0))`).
The witnesses below are compile-time checks that the multi-side product-density re-export applies
verbatim to this 2-side path with the concrete all-`μ=1` shapes `shapes_s3c = [[(1,1)],[(1,1)]]`. -/

theorem s3c_AllMuOne : AllMuOne [[((1 : ℕ), (1 : ℕ))], [((1 : ℕ), (1 : ℕ))]] := by
  intro shape hshape q hq
  fin_cases hshape <;> (fin_cases hq; rfl)

theorem s3c_AllNonempty : AllNonempty [[((1 : ℕ), (1 : ℕ))], [((1 : ℕ), (1 : ℕ))]] := by
  intro shape hshape
  fin_cases hshape <;> simp

/-- The 2-side product-density witness at `menuPath_s3c` (any prime `p`).  Instantiates STEP 3. -/
theorem s3c_product_density (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto
      (fun N => (stratumCount1 p 3 N
          (mkCell 3 [(0, 2), (1, 1), (3, 0)] [[((1 : ℕ), (1 : ℕ))], [((1 : ℕ), (1 : ℕ))]]) : ℚ)
          / (p : ℚ) ^ (3 * N))
      Filter.atTop
      (nhds ((List.zipWith (fun pr shape => omCount (sideSubShape pr shape) p)
        (sidePairs [(0, 2), (1, 1), (3, 0)]) [[((1 : ℕ), (1 : ℕ))], [((1 : ℕ), (1 : ℕ))]]).prod)) :=
  hnode_multiSideProduct_reexport 3 3 (by norm_num) [(0, 2), (1, 1), (3, 0)]
    CellCard.menuPath_s3c [[((1 : ℕ), (1 : ℕ))], [((1 : ℕ), (1 : ℕ))]] CellCard.shapes_s3c
    s3c_AllMuOne s3c_AllNonempty p

#print axioms s3c_product_density

/-! ## STEP 4 — the `omDensityV2` assembly.  DOCUMENTED OPEN (NOT a theorem).

`omDensityMultiSide_of_sides` (target shape): the multi-side contribution to `omDensityV2 n σ q`
factors as

    ∏_{(pr, shape) over sides} omCount (sideSubShape pr shape) q .

Why it is NOT stated as a theorem here.

* There is NO single menu shape `T ∈ omMenu n σ` with `omCount T q = ∏_side omCount (sideSubShape …)`
  — that is candidate (c), refuted in the module header (`configOf` emits ONE concatenated face,
  reading ONE polygon off the head; `shapeCount` is multiplicative only over DISTINCT factor-degrees,
  not over side concatenation; STEP 2 shows `B.classify` reads back only the FIRST side).  So the
  product CANNOT be a single `omCount` summand of `omDensityV2`, and the density CANNOT be delivered
  by instantiating `MontesAllOrders.montes_allorders_of_hnode` at a singleton menu the way
  `ClassifierBridgeFiber2.montes_order1_selfloop_density` does on the single-side locus.

* The honest route is the `ProductTheorem` polynomial-concatenation / block-product-cardinality layer:
  the block-product cardinality `∏_block card = card(∏ blocks)` is what makes the density FACTOR over
  sides.  Its ⊆-surjectivity half is `ProductTheorem.obligation_hensel_surjective` — a NAMED
  OBLIGATION, not a theorem (blocked on the θ-graded Hensel margin `W4d2′`) — with a CONDITIONAL
  variant `ProductTheorem.fiber_node_identity_of_image_eq` gated on an image-equality hypothesis.
  Stating `omDensityMultiSide_of_sides` as a theorem would force asserting
  `obligation_hensel_surjective`, violating the no-sorry / no-false-theorem discipline of the whole
  development.  It is therefore left as this docstring target only.

What IS closed here (unconditionally):

  * STEP 1  the POSITIVE first-side projection of a `B.classify` node
            (`classify_multiSide_firstSide_projection`);
  * STEP 2  the strict-refinement framing theorem
            (`inCell_multiSide_imp_classify_firstSide`) — the multi-side `InCell` fiber is finer than
            any single `B.classify` fiber; the converse is the documented non-implication above;
  * STEP 3  the product-density tie (`hnode_multiSideProduct_reexport`) and its block-cardinality
            witness (`prod_omCount_eq_blockCardinality_reexport`) — the exact counting-side data the
            `ProductTheorem` block-product layer consumes.

The remaining wiring `omDensityV2 = ∏_side omCount(sideSubShape …)` is the `ProductTheorem`
surjectivity half, downstream of this module's scope; forcing it through a single `omCount` would be
FALSE (STEP 2).  Optionally, a CONDITIONAL version gated on
`ProductTheorem.fiber_node_identity_of_image_eq`'s image-equality hypothesis could be stated once that
hypothesis is available; it is intentionally omitted here rather than asserted unproven.
-/

end LeanUrat.OM.ClassifierBridgeMultiSide
