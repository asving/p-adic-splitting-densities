/-
Scratch module: MULTI-SIDE → omDensityV2 connection.  Namespace
`LeanUrat.OM.PathShapeMultiSideTree`.  Math-first, no sorry/axiom/native_decide.

DECISIVE SEMANTIC FINDING (this module realizes it).  A multi-side degree-`s` polynomial
SPLITS: distinct Newton slopes = distinct irreducible factors, so the stratum density is a
PRODUCT of independent per-side residual-count factors, NOT a single `omCount`.

  (c) FALSE — one multi-side `ClusterShape` cannot carry `omCount = multiSideValue`: `configOf`
      emits ONE face (concatenation of all cells' `(dS,cellMult)`), reading ONE polygon off the
      head, whereas `mkCell` has one face PER side; and even at the value level `shapeCount` is
      multiplicative only over DISTINCT factor-degrees, not over side concatenation.
  (a) FALSE — children-per-side injects spurious `1/countPivot` self-loop divisors that
      `multiSideValue` (which has no pivot factors) does not carry.
  (b) CORRECT with a fixable exponent obstacle — resolved HERE.

The FLAT single-side polygon `mkPoly s [pr.1, pr.2]` OVER-COUNTS (its full-width-`s` Newton sum
extends the endpoint heights as constants across ALL columns).  The honest per-side engine value
uses the TRUNCATED `sideCeilSum P pr` (each column owned by ONE side).  The fix (Step 1) is to
RE-SCOPE the single-side engine literal to the side's OWN sub-width `span = pr.2.1 - pr.1.1`, with
the side translated to 0-based abscissa (heights unchanged): on that sub-scale the FLAT single-side
Newton exponent equals exactly the truncated `sideCeilSum P pr`, because `ceilSide` is covariant
under abscissa translation and `ceilAt` on the side's window is `ceilSide`.  Then:

  Step 1  `omCount_sideSubShape_eq_sideFactor` : the re-scoped per-side engine literal `= sideFactor`.
  Step 2  `multiSideValue_eq_prod_omCount`     : `multiSideValue = ∏_side omCount (sideSubShape …)`.
  Step 3  `hnode_multiSideProduct`             : the whole-path stratum limit AS a product of
           single-side `omCount`s (composes `hnode_multiSideShape` with Step 2).

The product structure lives in the ProductTheorem layer (`montes_allorders_of_hnode` consumes a
SINGLE `omCount` per menu shape; the product is assembled outside a single `omCount`).
-/
import Mathlib
import LeanUrat.OM.PathShapeMultiSide

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.PathShapeMultiSideTree

open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.PathShape
open LeanUrat.OM.PathShapeMultiSide
open CellCard

open scoped Classical

/-! ## Step 1.  The honest re-scoped per-side single `ClusterShape`. -/

/-- **The side, re-scoped to its own 0-based sub-width.**  Abscissa translated so the left endpoint
sits at `0` (the run `pr.2.1 - pr.1.1` becomes the sub-width); heights are UNCHANGED.  This is the
key fix: on this sub-scale the FLAT single-side Newton exponent
`newtonExponent (mkPoly span [subPr.1, subPr.2])` equals the TRUNCATED `sideCeilSum P pr`. -/
def subPr (pr : (ℕ × ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((0, pr.1.2), (pr.2.1 - pr.1.1, pr.2.2))

/-- **The re-scoped per-side single-shape cluster.**  `oneSideShape` at the side's OWN sub-width,
carrying the residual shape `shape`.  Unlike `oneSideShape s pr shape` (which uses the full width
`s` and over-counts on columns outside the side), this literal reconciles per-column with the
whole-path stratum. -/
def sideSubShape (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) : ClusterShape :=
  oneSideShape (pr.2.1 - pr.1.1) (subPr pr) shape

/-- `sideDeg` is translation-invariant: `sideDeg (subPr pr) = sideDeg pr`.  Both are
`gcd (v₀ − v₁) (run)` — the abscissa translation subtracts `pr.1.1` from both endpoints, leaving
the run and the drop unchanged. -/
theorem sideDeg_subPr (pr : (ℕ × ℕ) × (ℕ × ℕ)) : sideDeg (subPr pr) = sideDeg pr := by
  -- sideDeg pr = gcd (pr.1.2 - pr.2.2) (pr.2.1 - pr.1.1)
  -- sideDeg (subPr pr) = gcd (pr.1.2 - pr.2.2) ((pr.2.1 - pr.1.1) - 0)
  show Nat.gcd (pr.1.2 - pr.2.2) ((pr.2.1 - pr.1.1) - 0) = Nat.gcd (pr.1.2 - pr.2.2) (pr.2.1 - pr.1.1)
  rw [Nat.sub_zero]

/-- **`ceilAt` on a bare two-vertex list equals that side's `ceilSide` formula, on the window.**
Direct from the `ceilAt` definition (no chain needed): the sub-side endpoint height need not be `0`,
so `chainOK_ceilAt_window` does not apply, but the two-vertex ceilAt is exactly the middle branch. -/
theorem ceilAt_pair (q0 q1 : ℕ × ℕ) (_hw : q0.1 < q1.1) {i : ℕ} (h2 : i ≤ q1.1) :
    ceilAt [q0, q1] i = CellCard.ceilSide (q0, q1) i := by
  simp only [ceilAt, CellCard.ceilSide]
  by_cases hi0 : i ≤ q0.1
  · rw [if_pos hi0]
    -- i ≤ q0.1 ⟹ i - q0.1 = 0 ⟹ ceilSide = q0.2 - 0 = q0.2
    have hz : i - q0.1 = 0 := by omega
    rw [hz]
    simp
  · rw [if_neg hi0, if_pos h2]

/-- **`ceilSide` is covariant under abscissa translation.**  `ceilSide (subPr pr) i =
ceilSide pr (pr.1.1 + i)`: the translation adds `pr.1.1` back to the abscissa, and `ceilSide`
depends on `i` only through `i − left`, which is invariant. -/
theorem ceilSide_subPr (pr : (ℕ × ℕ) × (ℕ × ℕ)) (i : ℕ) :
    CellCard.ceilSide (subPr pr) i = CellCard.ceilSide pr (pr.1.1 + i) := by
  -- ceilSide (subPr pr) i = subPr.1.2 - (subPr.1.2 - subPr.2.2)*(i - subPr.1.1)/(subPr.2.1 - subPr.1.1)
  --                       = pr.1.2 - (pr.1.2 - pr.2.2)*(i - 0)/((pr.2.1 - pr.1.1) - 0)
  -- ceilSide pr (pr.1.1 + i) = pr.1.2 - (pr.1.2 - pr.2.2)*((pr.1.1 + i) - pr.1.1)/(pr.2.1 - pr.1.1)
  show pr.1.2 - (pr.1.2 - pr.2.2) * (i - 0) / ((pr.2.1 - pr.1.1) - 0)
      = pr.1.2 - (pr.1.2 - pr.2.2) * ((pr.1.1 + i) - pr.1.1) / (pr.2.1 - pr.1.1)
  rw [Nat.sub_zero, Nat.sub_zero, Nat.add_sub_cancel_left]

/-- `newtonExponent (mkPoly span P') = Σ_{i ∈ range span} ceilAt P' i`. -/
theorem newtonExponent_mkPoly_range (span : ℕ) (P' : List (ℕ × ℕ)) :
    L4.newtonExponent (mkPoly span P') = ∑ i ∈ Finset.range span, ceilAt P' i := by
  rw [L4.newtonExponent, Finset.sum_range fun i => ceilAt P' i]
  rfl

/-- **THE EXPONENT MATCH (Step 1 core).**  The re-scoped side's FLAT single-side Newton exponent
equals the TRUNCATED whole-path column contribution `sideCeilSum P pr`.  The over-count of the flat
full-width form is removed precisely by re-scoping to the side's own sub-width. -/
theorem newtonExponent_sideSub_eq_sideCeilSum
    {s N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hpr : pr ∈ sidePairs P) :
    L4.newtonExponent (mkPoly (pr.2.1 - pr.1.1) [(subPr pr).1, (subPr pr).2])
      = sideCeilSum P pr := by
  obtain ⟨hw, hh, _, _⟩ := menuPath_side_facts hP pr hpr
  -- newtonExponent = Σ_{i ∈ range span} ceilAt [subPr.1, subPr.2] i
  rw [newtonExponent_mkPoly_range]
  -- On the window i ≤ span, ceilAt of the two-vertex list is ceilSide (subPr pr).
  have hwsub : (subPr pr).1.1 < (subPr pr).2.1 := by
    show (0 : ℕ) < pr.2.1 - pr.1.1
    omega
  have hstep1 : ∀ i ∈ Finset.range (pr.2.1 - pr.1.1),
      ceilAt [(subPr pr).1, (subPr pr).2] i = CellCard.ceilSide (subPr pr) i := by
    intro i hi
    have hile : i ≤ (subPr pr).2.1 := by
      rw [Finset.mem_range] at hi
      show i ≤ pr.2.1 - pr.1.1
      omega
    have := ceilAt_pair (subPr pr).1 (subPr pr).2 hwsub hile
    -- (subPr pr).1, (subPr pr).2 as a pair is subPr pr itself.
    simpa using this
  rw [Finset.sum_congr rfl hstep1]
  -- ceilSide (subPr pr) i = ceilSide pr (pr.1.1 + i)
  rw [Finset.sum_congr rfl (fun i _ => ceilSide_subPr pr i)]
  -- reindex Σ_{i ∈ range span} ceilSide pr (pr.1.1 + i) = Σ_{k ∈ Ico pr.1.1 pr.2.1} ceilSide pr k
  rw [sideCeilSum]
  -- sideCeilSum uses ceilAt P; rewrite it to ceilSide pr on the window first.
  have hceil : ∀ k ∈ Finset.Ico pr.1.1 pr.2.1, ceilAt P k = CellCard.ceilSide pr k := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact menuPath_ceilAt_window hP hpr hk.1 (by omega)
  rw [Finset.sum_congr rfl hceil]
  -- Σ_{k ∈ Ico pr.1.1 pr.2.1} ceilSide pr k = Σ_{i ∈ range (pr.2.1 - pr.1.1)} ceilSide pr (pr.1.1 + i)
  rw [Finset.sum_Ico_eq_sum_range]

/-- **Step 1 (TARGET 1).**  The re-scoped per-side engine literal equals the truncated per-side
factor: `omCount (sideSubShape pr shape) p = sideFactor P p pr shape`.  Combines
`omCount_oneSideShape_closed` (the single-side closed form at the sub-width) with the exponent match
`newtonExponent_sideSub_eq_sideCeilSum` and `sideDeg_subPr`. -/
theorem omCount_sideSubShape_eq_sideFactor
    {s N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hpr : pr ∈ sidePairs P)
    (shape : List (ℕ × ℕ))
    (hpos : ∀ q ∈ shape, 1 ≤ q.1) (hμ : ∀ q ∈ shape, q.2 = 1)
    (hdeg : (shape.map Prod.fst).sum = sideDeg pr) (hne : shape ≠ [])
    (p : ℕ) [Fact p.Prime] :
    omCount (sideSubShape pr shape) p = sideFactor P p pr shape := by
  -- degree condition on the re-scoped side pr' = subPr pr: sideDeg (subPr pr) = sideDeg pr.
  have hdeg' : (shape.map Prod.fst).sum = sideDeg (subPr pr) := by
    rw [sideDeg_subPr]; exact hdeg
  -- match exponents: newtonExponent (mkPoly span [subPr.1, subPr.2]) + sideDeg (subPr pr)
  --                 = sideCeilSum P pr + sideDeg pr
  rw [sideSubShape,
    omCount_oneSideShape_closed (pr.2.1 - pr.1.1) (subPr pr) shape hpos hμ hdeg' hne p,
    sideFactor, newtonExponent_sideSub_eq_sideCeilSum hP hpr, sideDeg_subPr]

#print axioms omCount_sideSubShape_eq_sideFactor

/-! ## Step 2.  The product form of `multiSideValue`. -/

/-- **All-`μ=1` per side.**  The residual shapes on every side carry only simple parts (`μ = 1`);
this is the order-1 all-`μ=1` regime (the same regime `oneSideShape`'s closed form lives in — a
`μ ≥ 2` part would introduce a descent child).  Under this the per-side engine literal
`sideSubShape` has the childless closed form, so the product tie holds. -/
def AllMuOne (sh : List (List (ℕ × ℕ))) : Prop :=
  ∀ shape ∈ sh, ∀ q ∈ shape, q.2 = 1

/-- **Nonempty per side.**  Every side's residual shape is nonempty (the reader reads polygon/`δ`
off the head cell — an empty shape would give the wrong data). -/
def AllNonempty (sh : List (List (ℕ × ℕ))) : Prop :=
  ∀ shape ∈ sh, shape ≠ []

/-- **Per-side factor = re-scoped `omCount`, over a sublist of `sidePairs P` (induction core).**
For any `sp` all of whose members are sides of `P`, matched by `sh` via `ShapesFor`-style
`Forall₂`, all-`μ=1` and nonempty, the zipped product of `sideFactor` equals the zipped product of
`omCount (sideSubShape …)`.  Proof is a `Forall₂` induction using Step 1 pointwise. -/
theorem prod_sideFactor_eq_prod_omCount
    {s N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N P) (p : ℕ) [Fact p.Prime]
    (sp : List ((ℕ × ℕ) × (ℕ × ℕ))) (sh : List (List (ℕ × ℕ)))
    (hsub : ∀ pr ∈ sp, pr ∈ sidePairs P)
    (hF : List.Forall₂ (fun l pr => l ∈ shapesOfDegree (sideDeg pr)) sh sp)
    (hμ : AllMuOne sh) (hne : AllNonempty sh) :
    (List.zipWith (sideFactor P p) sp sh).prod
      = (List.zipWith (fun pr shape => omCount (sideSubShape pr shape) p) sp sh).prod := by
  induction hF with
  | nil => rfl
  | @cons shape pr shTail spTail hhead htail ih =>
      -- head: sideFactor P p pr shape = omCount (sideSubShape pr shape) p (Step 1)
      have hprmem : pr ∈ sidePairs P := hsub pr List.mem_cons_self
      have hmem := mem_shapesOfDegree_iff.mp hhead
      have hpos : ∀ q ∈ shape, 1 ≤ q.1 := fun q hq => (hmem.2.1 q hq).1
      have hμhead : ∀ q ∈ shape, q.2 = 1 := hμ shape List.mem_cons_self
      have hnehead : shape ≠ [] := hne shape List.mem_cons_self
      -- degree condition: Σ q.1 = sideDeg pr, from Σ q.1*q.2 = sideDeg pr under μ = 1.
      have hdeg : (shape.map Prod.fst).sum = sideDeg pr := by
        rw [← hmem.2.2]
        apply congrArg List.sum
        apply List.map_congr_left
        intro q hq
        show q.1 = q.1 * q.2
        rw [hμhead q hq, Nat.mul_one]
      have hhead' : sideFactor P p pr shape = omCount (sideSubShape pr shape) p :=
        (omCount_sideSubShape_eq_sideFactor hP hprmem shape hpos hμhead hdeg hnehead p).symm
      simp only [List.zipWith_cons_cons, List.prod_cons]
      rw [hhead']
      -- tail: apply the IH with the restricted hypotheses.
      rw [ih (fun pr' hpr' => hsub pr' (List.mem_cons_of_mem _ hpr'))
        (fun shape' hshape' => hμ shape' (List.mem_cons_of_mem _ hshape'))
        (fun shape' hshape' => hne shape' (List.mem_cons_of_mem _ hshape'))]

/-- **Step 2 (TARGET 2).**  `multiSideValue s P sh p` is the PRODUCT over sides of the re-scoped
per-side engine literal `omCount (sideSubShape pr shape) p`.  Immediate from the `zipWith` definition
of `multiSideValue` (= product of `sideFactor`) once Step 1 holds pointwise. -/
theorem multiSideValue_eq_prod_omCount
    {s N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    (sh : List (List (ℕ × ℕ))) (hsh : ShapesFor P sh)
    (hμ : AllMuOne sh) (hne : AllNonempty sh)
    (p : ℕ) [Fact p.Prime] :
    multiSideValue s P sh p
      = (List.zipWith (fun pr shape => omCount (sideSubShape pr shape) p) (sidePairs P) sh).prod := by
  rw [multiSideValue]
  -- multiSideValue = prod of sideFactor over (sidePairs P, sh); swap zip argument order to match.
  exact prod_sideFactor_eq_prod_omCount hP p (sidePairs P) sh (fun _ h => h) hsh hμ hne

#print axioms multiSideValue_eq_prod_omCount

/-! ## Step 3.  The multi-side `h_node` AS an explicit product of single-side `omCount`s. -/

/-- **Step 3 (TARGET 3) — the multi-side stratum limit as a PRODUCT of single-side `omCount`s.**
For an all-`μ=1`, nonempty, order-1 multi-side menu path `P` carrying per-side shapes `sh`, the
genuine order-1 stratum density `stratumCount1 s N (mkCell s P sh) / p^{s·N}` converges to the
PRODUCT over sides of the re-scoped single-side engine literal `omCount (sideSubShape pr shape) p`.

Distinct Newton-slope branches MULTIPLY (independent OM branches), so the limit is a product of
single-`ClusterShape` `omCount`s — exactly the counting-side witness the ProductTheorem's
block-product cardinality layer consumes.  Composes `hnode_multiSideShape` (limit = `multiSideValue`)
with `multiSideValue_eq_prod_omCount` (= the product).  This does NOT force the density through a
single `omCount` (candidate (c) is FALSE): the product structure lives outside any one `omCount`. -/
theorem hnode_multiSideProduct (s N₀ : ℕ) (hN₀ : 0 < N₀) (P : List (ℕ × ℕ))
    (hP : MenuPath s N₀ P) (sh : List (List (ℕ × ℕ))) (hsh : ShapesFor P sh)
    (hμ : AllMuOne sh) (hne : AllNonempty sh) (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto (fun N => (stratumCount1 p s N (mkCell s P sh) : ℚ) / (p:ℚ)^(s*N))
      Filter.atTop
      (nhds ((List.zipWith (fun pr shape => omCount (sideSubShape pr shape) p)
        (sidePairs P) sh).prod)) := by
  have hbase := hnode_multiSideShape s N₀ hN₀ P hP sh hsh p
  rwa [multiSideValue_eq_prod_omCount hP sh hsh hμ hne p] at hbase

#print axioms hnode_multiSideProduct

/-! ## Smallest genuine 2-side witness: `menuPath_s3c = [(0,2),(1,1),(3,0)]`.

The concrete 2-side instance the SCOPE names.  `s = 3`, two sides `((0,2),(1,1))` and `((1,1),(3,0))`.
The flat single-side Newton sums are `2 + 1 + 1 = 4` (side 1) and `1 + 1 + 1 = 3` (side 2) — total `7`
— whereas the whole-path `newtonExponent (mkPoly 3 P) = 2 + 1 + 1 = 4`, so the FLAT reconciliation
FAILS (7 ≠ 4).  The re-scoped `sideSubShape` fixes this per side: side 1 has run `1`, so its sub-width
sum is `2` (just column `0`); side 2 has run `2`, sub-width sum `1 + 1 = 2` (columns `1,2`); total
`2 + 2 = 4 = newtonExponent (mkPoly 3 P)`.  The instantiation below is a compile-time witness that the
product-form `h_node` applies verbatim to this 2-side path (with any valid all-`μ=1` `sh`). -/
example (sh : List (List (ℕ × ℕ)))
    (hsh : ShapesFor [(0, 2), (1, 1), (3, 0)] sh)
    (hμ : AllMuOne sh) (hne : AllNonempty sh) (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto
      (fun N => (stratumCount1 p 3 N (mkCell 3 [(0, 2), (1, 1), (3, 0)] sh) : ℚ) / (p:ℚ)^(3*N))
      Filter.atTop
      (nhds ((List.zipWith (fun pr shape => omCount (sideSubShape pr shape) p)
        (sidePairs [(0, 2), (1, 1), (3, 0)]) sh).prod)) :=
  hnode_multiSideProduct 3 3 (by norm_num) [(0, 2), (1, 1), (3, 0)] menuPath_s3c sh hsh hμ hne p

/-! ## (Optional bridge, TARGET 4) — the product-of-`omCount`s as the block-cardinality witness.

The ProductTheorem realizes the multi-side density as a product over sides via the
block-product cardinality `∏_block card = card (∏ blocks)`.  The counting-side witness for that
factorization is precisely: the product over sides of the single-side `omCount`s equals the joint
residual count `prodSC p sh` (= `∏_side shapeCount`, the block-product cardinality) times a single
box-volume factor `p^{−(newtonExponent (mkPoly s P) + Σ sideDeg)}`.  This is exactly the reciprocal
of `p^{volExp (mkCell s P sh)}`.  We prove it here as an algebraic identity (compose Step 2 with
`omCount_multiSide_closed`), which is the tractable, unconditional half. -/
theorem prod_omCount_eq_blockCardinality
    {s N : ℕ} {P : List (ℕ × ℕ)} (hP : MenuPath s N P)
    (sh : List (List (ℕ × ℕ))) (hsh : ShapesFor P sh)
    (hμ : AllMuOne sh) (hne : AllNonempty sh) (p : ℕ) [Fact p.Prime] :
    (List.zipWith (fun pr shape => omCount (sideSubShape pr shape) p) (sidePairs P) sh).prod
      = (CellCard.prodSC p sh : ℚ)
          * ((p : ℚ) ^ (L4.newtonExponent (mkPoly s P) + ((sidePairs P).map sideDeg).sum))⁻¹ := by
  rw [← multiSideValue_eq_prod_omCount hP sh hsh hμ hne p]
  exact omCount_multiSide_closed s N P hP sh hsh p

#print axioms prod_omCount_eq_blockCardinality

/-
DOCUMENTED OPEN (NOT a declaration — the analytic half is out of this module's scope).

  omDensityProduct_of_sides (target shape):
    the multi-side contribution to `omDensityV2 n σ q` factors as
      ∏_{side pr, shape} omCount (sideSubShape pr shape) q .

  Why it is NOT stated as a theorem here.  There is NO single menu shape `T ∈ omMenu n σ` with
  `omCount T q = ∏_side omCount (sideSubShape …)` — that is candidate (c), refuted in the module
  header (`configOf` emits ONE concatenated face; `shapeCount` is multiplicative only over DISTINCT
  factor-degrees, not over side concatenation).  So the product CANNOT be a single `omCount`
  summand of `omDensityV2`.  The honest route is the ProductTheorem's polynomial-concatenation /
  block-product-cardinality layer (`imageSet_subset_concatCell`, `blocks_card`): the block-product
  cardinality `∏_block card = card (∏ blocks)` is what makes the density FACTOR over sides, and its
  ⊆-surjectivity half (Hensel factorization) is only CONDITIONALLY closed in that layer.  That layer
  is downstream of this module's import chain (`ProductTheorem`, `MontesAllOrders` are not imported
  by `PathShapeMultiSide`), and forcing the density through a single `omCount` would be FALSE.

  What IS closed here is the algebraic counting-side witness the ProductTheorem consumes:
  `prod_omCount_eq_blockCardinality` — the product of single-side `omCount`s equals
  `prodSC · p^{−(newtonExponent + Σ sideDeg)}`, i.e. the block-product cardinality times the single
  box factor.  Wiring this into `omDensityV2` = product is left to the ProductTheorem layer, whose
  surjectivity half exceeds this scratch module's scope.
-/

end LeanUrat.OM.PathShapeMultiSideTree
