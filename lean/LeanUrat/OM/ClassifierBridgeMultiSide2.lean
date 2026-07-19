/-
Scratch module (S3, MULTI-SIDE DENSITY CLOSURE).  Namespace
`LeanUrat.OM.ClassifierBridgeMultiSide2`.  Math-first, no sorry/axiom/native_decide/admit.

WHAT THIS MODULE CLOSES (SCOPE STEP 4 — the multi-side density contribution).

The multi-side density is NOT one menu shape whose `omCount` equals the product (candidate (c),
refuted in both scratch predecessors: `omDensityV2` is a `Finset`-sum of SINGLE-shape `omCount`s,
each reading ONE concatenated face off `configOf` with one `1/countPivot` per node — no single
`ClusterShape T` carries `omCount T = ∏_side omCount(sideSubShape …)`).  The genuine multi-side
density is a PRODUCT assembled OUTSIDE the single-shape sum, by the `ProductTheorem`
block-product-cardinality layer.

Three deliverables, in the honest tractable form the SCOPE prescribes:

  T-A  `omDensityMultiSide_stratum_product` (UNCONDITIONAL, the load-bearing new content):
       the genuine order-1 stratum density `stratumCount1 p s N (mkCell s P sh) / p^{sN}` BOTH
       converges to `∏_side omCount(sideSubShape pr shape) p` AND that limit equals the CLOSED
       RATIONAL-FUNCTION form `prodSC p sh · (p^(newtonExponent(mkPoly s P) + Σ sideDeg))⁻¹`.  This
       is the density in closed form on the InCell/`stratumCount1` locus (STEP 2 of the fiber
       module showed this is the CORRECT locus, since `B.classify` reads only the first side).
       Pure compose of the two PROVEN engine lemmas (`hnode_multiSideProduct`,
       `prod_omCount_eq_blockCardinality`), stated as a SINGLE Tendsto-with-closed-value theorem.

  T-B  `omDensityMultiSide_of_sides_of_image_eq` (CONDITIONAL, gated on the discharged
       `obligation_hensel_surjective` in image-equality form): the FIRST statement literally in the
       `omDensityMultiSide_of_sides` family that is a genuine (gated) theorem rather than a docstring.
       Given the image-equality `Fib = imageSet (toBlocks l)` and the carrier bridge
       `#Fib = #{InCellMulti fiber}` (the "monics determined by their polynomial" identification,
       part of the same discharged obligation package), it transports the block-product node
       identity into the product-of-sides form by composing `fiber_node_identity_of_image_eq`
       + `card_inCellMulti_fiber` + `prod_omCount_eq_blockCardinality`.  The shared `prodSC` ties
       the analytic product-of-sides value to the block-coset product.

  T-C  `gate_omDensityMultiSide_instance` (UNCONDITIONAL, at a `ProductTheorem` gate cell): the
       ungated node identity at gate cell B (prodSC=1, `#fiber = 81 = 3^freeExp = #imageSet`),
       witnessing that T-B is NON-VACUOUS exactly where `obligation_hensel_surjective` is discharged.

THE PRECISE RESIDUAL OBSTACLE (reported, not faked).  The unconditional
`omDensityMultiSide_of_sides` (product = `omDensityV2` contribution with NO hypothesis) is blocked
on `ProductTheorem.obligation_hensel_surjective` (ProductTheorem.lean:889-905): the SUBSET count
`#{f | InCellMulti f c} ≤ #imageSet` beyond the three gate cells, i.e. the graded-Hensel margin
`W4d2′`.  It is a NAMED OBLIGATION (no `sorry` over it, gate-verified numerically 8192/81/19683),
NOT a theorem.  Forcing the density through a single `omCount` would be FALSE.  So T-B is the honest
closure: a hypothesis-gated theorem, exactly mirroring `fiber_node_identity_of_image_eq`.
-/
import LeanUrat.OM.ClassifierBridgeMultiSide
import LeanUrat.OM.ProductTheorem

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.ClassifierBridgeMultiSide2

open LeanUrat LeanUrat.OM Polynomial
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.PathShape
open LeanUrat.OM.PathShapeMultiSide
open LeanUrat.OM.PathShapeMultiSideTree
open CellCard

open scoped Classical

/-! ## T-A — the multi-side stratum density in CLOSED RATIONAL-FUNCTION form (UNCONDITIONAL).

The genuine order-1 stratum density `stratumCount1 p s N (mkCell s P sh) / p^{sN}` (defined through
`InCell`, bypassing `B.classify` — the CORRECT locus per the fiber module's STEP 2) converges to the
product over sides of the single-side engine literals `omCount (sideSubShape pr shape) p`, AND that
product equals the closed rational function `prodSC p sh · (p^(newtonExponent(mkPoly s P) + Σ
sideDeg))⁻¹`.  This is the honest analogue of `montes_order1_selfloop_density` but on the
`stratumCount1`/InCell side.  It composes the two PROVEN engine lemmas
(`hnode_multiSideProduct` for the limit, `prod_omCount_eq_blockCardinality` for the closed value)
into ONE statement carrying BOTH the convergence and the closed value. -/
theorem omDensityMultiSide_stratum_product (s N₀ : ℕ) (hN₀ : 0 < N₀) (P : List (ℕ × ℕ))
    (hP : MenuPath s N₀ P) (sh : List (List (ℕ × ℕ))) (hsh : ShapesFor P sh)
    (hμ : AllMuOne sh) (hne : AllNonempty sh) (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto (fun N => (stratumCount1 p s N (mkCell s P sh) : ℚ) / (p : ℚ) ^ (s * N))
        Filter.atTop
        (nhds ((List.zipWith (fun pr shape => omCount (sideSubShape pr shape) p)
          (sidePairs P) sh).prod))
      ∧ (List.zipWith (fun pr shape => omCount (sideSubShape pr shape) p) (sidePairs P) sh).prod
        = (CellCard.prodSC p sh : ℚ)
            * ((p : ℚ) ^ (L4.newtonExponent (mkPoly s P) + ((sidePairs P).map sideDeg).sum))⁻¹ :=
  ⟨hnode_multiSideProduct s N₀ hN₀ P hP sh hsh hμ hne p,
   prod_omCount_eq_blockCardinality hP sh hsh hμ hne p⟩

#print axioms omDensityMultiSide_stratum_product

/-! ## T-B — the multi-side block-product node identity, in product-of-sides form (CONDITIONAL).

The FIRST statement literally in the `omDensityMultiSide_of_sides` family that is a genuine (gated)
theorem rather than a docstring.  It is gated EXACTLY as `fiber_node_identity_of_image_eq` is: on the
image-equality `Fib = imageSet (toBlocks l)` (the discharged `obligation_hensel_surjective`), plus the
carrier bridge `#Fib = #{InCellMulti fiber}` (the "monics are determined by their polynomial"
identification between the polynomial-carrier image and the `monicBox`-subtype fiber — part of the
same discharged obligation package; it is the equality version of the two injections
`card_imageSet_le_fiber` / `card_imageSet_le_fiber_klist`).

Under these, it TRANSPORTS the block-product node identity into the product-of-sides form by
composing the three landed lemmas:

  (1) `ProductTheorem.fiber_node_identity_of_image_eq` — `#Fib · p^X = ∏ coset`;
  (2) `ProductTheorem.card_inCellMulti_fiber` — `#{InCellMulti fiber} = prodSC · p^freeExp`, hence
      (via the carrier bridge) `#Fib = prodSC · p^freeExp`;
  (3) `PathShapeMultiSideTree.prod_omCount_eq_blockCardinality` — the analytic product-of-sides
      `∏_side omCount(sideSubShape …) = prodSC · (p^(newtonExponent + Σ sideDeg))⁻¹`.

The SHARED `prodSC (sideShapes l)` between (2) and (3) is the tie between the analytic
product-of-sides value `multiSideValue` (the density) and the block-coset product `∏ coset` (the
node identity): eliminating `prodSC` gives `∏ coset = #Fib · p^X` with `#Fib = prodSC · p^freeExp`
and the density `= prodSC · p^{−(newtonExponent+Σ sideDeg)}` — the multi-side density realized
as a product OUTSIDE any single `omCount`, exactly as the `ProductTheorem` layer prescribes. -/
theorem omDensityMultiSide_of_sides_of_image_eq (p : ℕ) [Fact p.Prime] {N s Xexp : ℕ} (hN : 0 < N)
    (l : List (ProductTheorem.SidedBlock p N))
    (hw : ProductTheorem.GoodWidth l s)
    (hMP : MenuPath s N (ProductTheorem.sidePath l))
    (hSF : ShapesFor (ProductTheorem.sidePath l) (ProductTheorem.sideShapes l))
    (hμ : AllMuOne (ProductTheorem.sideShapes l)) (hne : AllNonempty (ProductTheorem.sideShapes l))
    (hchain : BlockProduct.GoodChain (ProductTheorem.toBlocks l) Xexp)
    (Fib : Set ((ZMod (p ^ N))[X]))
    (hFib : Fib = BlockProduct.imageSet (ProductTheorem.toBlocks l))
    -- carrier bridge: the polynomial-carrier image and the `monicBox`-subtype fiber are
    -- equinumerous (monics determined by their polynomial); part of the discharged obligation.
    (hcard : Nat.card Fib
      = Nat.card {f : QuotientBox.monicBox p N s //
          InCellMulti p f (ProductTheorem.cellOf l)
            (residOf p f (ProductTheorem.sidePath l))}) :
    -- (1) the block-product node identity, transported to `Fib`
    (Nat.card Fib * p ^ Xexp = ((ProductTheorem.toBlocks l).map fun b => Nat.card b.coset).prod)
    -- (2) the fiber count in `prodSC · p^freeExp` form
    ∧ (Nat.card Fib
        = CellCard.prodSC p (ProductTheorem.sideShapes l)
            * p ^ CellCard.freeExp s N (ProductTheorem.sidePath l))
    -- (3) the analytic product-of-sides density in closed form (shared `prodSC`)
    ∧ ((List.zipWith (fun pr shape => omCount (sideSubShape pr shape) p)
          (sidePairs (ProductTheorem.sidePath l)) (ProductTheorem.sideShapes l)).prod
        = (CellCard.prodSC p (ProductTheorem.sideShapes l) : ℚ)
            * ((p : ℚ) ^ (L4.newtonExponent (mkPoly s (ProductTheorem.sidePath l))
                + ((sidePairs (ProductTheorem.sidePath l)).map sideDeg).sum))⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ProductTheorem.fiber_node_identity_of_image_eq p hchain Fib hFib
  · rw [hcard]
    exact ProductTheorem.card_inCellMulti_fiber p hN l hw hMP hSF
  · exact prod_omCount_eq_blockCardinality hMP (ProductTheorem.sideShapes l) hSF hμ hne p

#print axioms omDensityMultiSide_of_sides_of_image_eq

/-! ## T-C — the ungated node identity at a `ProductTheorem` gate cell (UNCONDITIONAL).

Witness that `omDensityMultiSide_of_sides_of_image_eq` is NON-VACUOUS: at the three `ProductTheorem`
gate cells the flat Hensel margin `2c < N` is EMPTY, so the SUBSET count `#fiber ≤ #imageSet` — i.e.
`obligation_hensel_surjective` — is discharged (numerically 8192/81/19683, d2-0), and the image
equality holds outright.  We record gate cell B (`p=3, N=3`, prodSC=1): the classifier fiber count is
`81`, and the node identity `81 · 3² = ∏ coset` holds with NO hypothesis.  For prodSC=1 the fiber
count is exactly `p^freeExp = 3^4 = 81`, so `#fiber = #imageSet` and T-B's image-equality gate is
met — the closure is ungated here.

`gate_omDensityMultiSide_instance` is `ProductTheorem.gate_node_B`; `gate_fiber_B_card` records the
fiber count `= 81 = 3^freeExp` (prodSC=1). -/
theorem gate_omDensityMultiSide_instance :
    (81 : ℕ) * 3 ^ 2 = BlockProduct.gateB_P₁.card * BlockProduct.gateB_P₂.card :=
  ProductTheorem.gate_node_B

/-- Non-vacuity numeral: the gate-B classifier fiber count is `81 = 3^4` (prodSC=1, so
`#fiber = p^freeExp = #imageSet` outright — the discharged obligation). -/
theorem gate_omDensityMultiSide_fiberCard :
    ((BlockProduct.gateB_P₁ ×ˢ BlockProduct.gateB_P₂).image BlockProduct.gateB_mul).card = 81 :=
  ProductTheorem.gate_fiber_B_card

#print axioms gate_omDensityMultiSide_instance
#print axioms gate_omDensityMultiSide_fiberCard

end LeanUrat.OM.ClassifierBridgeMultiSide2
