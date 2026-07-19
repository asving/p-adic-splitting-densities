/-
Scratch module: MULTI-SIDE S3 extension — the product-over-sides engine value and its
`h_node`.  Namespace LeanUrat.OM.PathShapeMultiSide.  Math-first, no sorry/axiom/native_decide.

DECISIVE ENCODING FINDING (refines the SCOPE's step-3 recommendation):

  The FLAT per-side polygon `mkPoly s [pr.1, pr.2]` used by `PathShape.oneSideShape`
  OVER-COUNTS: `newtonExponent (mkPoly s [pr.1,pr.2]) = Σ_{i<s} ceilAt [pr.1,pr.2] i`
  is a FULL-WIDTH-`s` sum, so on the columns OUTSIDE the side `pr`'s own abscissa range
  it extends the endpoint heights as constants.  Summed over all sides this is strictly
  larger than `newtonExponent (mkPoly s P)`.  Concretely, `menuPath_s3c = [(0,2),(1,1),(3,0)]`
  (s=3): the flat side sums are 4 (side ((0,2),(1,1))) + 3 (side ((1,1),(3,0))) = 7, whereas
  `newtonExponent (mkPoly 3 P) = 2+1+1 = 4`.  So the FLAT reconciliation
  `Σ_i newtonExponent (mkPoly s [pr_i]) = newtonExponent (mkPoly s P)` is FALSE for ≥2 sides.

  Hence the honest multi-side engine value that reconciles with the whole-path stratum limit
  (RESULT 1: `volExp (mkCell s P sh) = newtonExponent (mkPoly s P) + Σ sideDeg`) is the product
  over sides of the per-side count `shapeCount` times the TRUNCATED column contribution
  `sideCeilSum P pr = Σ_{i ∈ Ico pr.1.1 pr.2.1} ceilAt P i` (each column in exactly ONE side).
  This is what the SCOPE flagged as the "width-truncated per-side polygon" fallback; the
  numerics above make it MANDATORY, not optional.  We define `multiSideValue` with the truncated
  exponent, prove the CLEAN reconciliation `Σ sideCeilSum = newtonExponent (mkPoly s P)`
  (telescoping over the chain via `Finset.sum_Ico_consecutive`), and land a genuine
  `hnode_multiSideShape` tying the whole-path stratum density to that product value.
-/
import Mathlib
import LeanUrat.OM.PathShape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.PathShapeMultiSide

open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.DecidedOrder1
open LeanUrat.OM.PathShape
open CellCard

open scoped Classical

/-! ## 1. The truncated per-side column contribution and the reconciliation lemma -/

/-- **The truncated column contribution of one side.**  The Newton exponent that the WHOLE-PATH
polygon `mkPoly s P` assigns to the columns owned by the side `pr`: the abscissa half-open range
`[pr.1.1, pr.2.1)`.  Unlike `newtonExponent (mkPoly s [pr.1,pr.2])` (a full-width-`s` sum that
extends the side's endpoint heights as constants across ALL columns), this counts ONLY the side's
own columns, so summing over the sides partitions `[0,s)` exactly. -/
def sideCeilSum (P : List (ℕ × ℕ)) (pr : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  ∑ i ∈ Finset.Ico pr.1.1 pr.2.1, ceilAt P i

/-- **Telescoping of consecutive `Ico` ranges along a chain (arbitrary summand).**  For any
`f : ℕ → ℕ`, the sum of `Σ_{i ∈ Ico pr.1.1 pr.2.1} f i` over the sides of `p1 :: T` equals
`Σ_{i ∈ Ico p1.1 s} f i` (abscissas increase `p1.1 → s`).  This is the clean per-column partition
that the flat per-side polygon fails to provide.  Proof mirrors `PathShape.chainOK_run_sum` but
telescopes `Finset.Ico` via `Finset.sum_Ico_consecutive` instead of natural subtraction. -/
private theorem chainOK_ceilSum_gen {s : ℕ} {T : List (ℕ × ℕ)} {p0 p1 : ℕ × ℕ}
    (h : ChainOK s p0 p1 T) (f : ℕ → ℕ) :
    ((sidePairs (p1 :: T)).map (fun pr => ∑ i ∈ Finset.Ico pr.1.1 pr.2.1, f i)).sum
      = ∑ i ∈ Finset.Ico p1.1 s, f i := by
  induction h with
  | @nil p0 p1 h1 h2 =>
      -- single vertex list [p1]; no sides; p1.1 = s ⟹ Ico p1.1 s = ∅.
      simp only [sidePairs, List.tail_cons, List.zip_nil_right, List.map_nil, List.sum_nil]
      rw [h1, Finset.Ico_self, Finset.sum_empty]
  | @cons p0 p1 p2 T h1 h2 h3 h4 ih =>
      -- sides of (p1 :: p2 :: T) = (p1,p2) :: sides of (p2 :: T)
      rw [sidePairs_cons₂, List.map_cons, List.sum_cons, ih]
      -- head term is Σ_{Ico p1.1 p2.1} f, tail is Σ_{Ico p2.1 s} f; splice.
      have hp1p2 : p1.1 ≤ p2.1 := le_of_lt h1
      have hp2s : p2.1 ≤ s := chainOK_le h4
      show (∑ i ∈ Finset.Ico p1.1 p2.1, f i) + (∑ i ∈ Finset.Ico p2.1 s, f i)
        = ∑ i ∈ Finset.Ico p1.1 s, f i
      exact Finset.sum_Ico_consecutive f hp1p2 hp2s

/-- **THE RECONCILIATION LEMMA (truncated form).**  The whole-path Newton exponent decomposes as a
sum over the sides of the truncated per-side column contribution:
`Σ_{pr ∈ sidePairs P} sideCeilSum P pr = newtonExponent (mkPoly s P)`.

This is the honest exponent identity for the multi-side product engine value — it telescopes
CLEANLY because each column `i ∈ [0,s)` is owned by exactly ONE side.  (The FLAT analogue
`Σ_{pr} newtonExponent (mkPoly s [pr.1,pr.2]) = newtonExponent (mkPoly s P)` is FALSE for ≥2 sides,
see the module header.) -/
theorem sideCeilSum_sum (s N : ℕ) (P : List (ℕ × ℕ)) (hP : MenuPath s N P) :
    ((sidePairs P).map (sideCeilSum P)).sum = L4.newtonExponent (mkPoly s P) := by
  obtain ⟨H, p1, T, rfl, hH1, hH2, hp1a, hp1b, hc⟩ := hP
  -- newtonExponent (mkPoly s P) = Σ_{i<s} ceilAt P i = Σ_{i ∈ Ico 0 s} ceilAt P i.
  rw [show L4.newtonExponent (mkPoly s ((0, H) :: p1 :: T))
        = ∑ i ∈ Finset.range s, ceilAt ((0, H) :: p1 :: T) i from by
    rw [L4.newtonExponent]; rw [Finset.sum_range fun i => ceilAt ((0, H) :: p1 :: T) i]; rfl]
  rw [← Nat.Ico_zero_eq_range]
  -- sides of (0,H) :: p1 :: T = ((0,H), p1) :: sides of (p1 :: T)
  rw [sidePairs_cons₂, List.map_cons, List.sum_cons]
  -- head truncated contribution: Ico 0 p1.1; tail: telescopes to Ico p1.1 s.
  have hp1s : p1.1 ≤ s := chainOK_le hc
  rw [show ((sidePairs (p1 :: T)).map (sideCeilSum ((0, H) :: p1 :: T))).sum
        = ∑ i ∈ Finset.Ico p1.1 s, ceilAt ((0, H) :: p1 :: T) i from
    chainOK_ceilSum_gen hc (ceilAt ((0, H) :: p1 :: T))]
  -- head = Σ_{Ico 0 p1.1}; splice Ico 0 p1.1 ∪ Ico p1.1 s = Ico 0 s.
  show (∑ i ∈ Finset.Ico ((0 : ℕ)) p1.1, ceilAt ((0, H) :: p1 :: T) i)
      + (∑ i ∈ Finset.Ico p1.1 s, ceilAt ((0, H) :: p1 :: T) i)
    = ∑ i ∈ Finset.Ico 0 s, ceilAt ((0, H) :: p1 :: T) i
  exact Finset.sum_Ico_consecutive (ceilAt ((0, H) :: p1 :: T)) (Nat.zero_le _) hp1s

#print axioms sideCeilSum_sum

/-! ## 2. The multi-side engine value (product over sides) and its closed form -/

/-- **The honest per-side engine factor.**  The single-side order-1 cluster contribution of one
side `pr` carrying residual shape `shape`, using the TRUNCATED whole-path column contribution
`sideCeilSum P pr` (NOT the flat `newtonExponent (mkPoly s [pr.1,pr.2])`, which over-counts — see
the module header).  Shape identical to `omCount (oneSideShape s pr shape) p` EXCEPT the box-volume
exponent is the truncated `sideCeilSum P pr` in place of the flat `newtonExponent (mkPoly s [·])`;
this is the version that reconciles per-column with the whole-path stratum. -/
noncomputable def sideFactor (P : List (ℕ × ℕ)) (p : ℕ) [Fact p.Prime] (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (shape : List (ℕ × ℕ)) : ℚ :=
  (CellCard.shapeCount p shape : ℚ)
    * ((p : ℚ) ^ (sideCeilSum P pr + sideDeg pr))⁻¹

/-- **THE MULTI-SIDE ENGINE VALUE.**  Distinct Newton-slope branches MULTIPLY (they are independent
OM branches, not children of a shared node — see the SCOPE's classifier analysis), so the honest
engine value on a multi-side path `P` with per-side shapes `sh` is the PRODUCT over the zipped
(side, shape) of the per-side factor.  A `List`-product value, not a single `ClusterShape`. -/
noncomputable def multiSideValue (s : ℕ) (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ)))
    (p : ℕ) [Fact p.Prime] : ℚ :=
  (List.zipWith (sideFactor P p) (sidePairs P) sh).prod

/-- `prodSC` on a cons splits off the head `shapeCount`. -/
private theorem prodSC_cons (p : ℕ) [Fact p.Prime] (a : List (ℕ × ℕ)) (t : List (List (ℕ × ℕ))) :
    CellCard.prodSC p (a :: t)
      = CellCard.shapeCount p a * CellCard.prodSC p t := by
  show ((a :: t).map (CellCard.shapeCount p)).prod
    = CellCard.shapeCount p a * (t.map (CellCard.shapeCount p)).prod
  rw [List.map_cons, List.prod_cons]

/-- `prodSC` on nil is `1`. -/
private theorem prodSC_nil (p : ℕ) [Fact p.Prime] :
    CellCard.prodSC p [] = 1 := by
  show (([] : List (List (ℕ × ℕ))).map (CellCard.shapeCount p)).prod = 1
  rw [List.map_nil, List.prod_nil]

/-- **Core factorization (single induction).**  The product over the zipped (side, shape) list of
`shapeCount · p^{-(sideCeilSum + sideDeg)}` splits into `prodSC` times a single telescoped box
factor `p^{-(Σ sideCeilSum + Σ sideDeg)}`.  One induction on the side list, generalizing `sh`. -/
private theorem multiSide_factor_zip (P : List (ℕ × ℕ)) (p : ℕ) [Fact p.Prime]
    (sp : List ((ℕ × ℕ) × (ℕ × ℕ))) (sh : List (List (ℕ × ℕ))) (hlen : sh.length = sp.length) :
    (List.zipWith (sideFactor P p) sp sh).prod
      = (CellCard.prodSC p sh : ℚ)
          * ((p : ℚ) ^ ((sp.map (sideCeilSum P)).sum + (sp.map sideDeg).sum))⁻¹ := by
  induction sp generalizing sh with
  | nil =>
      cases sh with
      | nil => rw [prodSC_nil]; simp
      | cons a t => simp at hlen
  | cons pr rest ih =>
      cases sh with
      | nil => simp at hlen
      | cons a t =>
          simp only [List.zipWith_cons_cons, List.prod_cons, List.map_cons, List.sum_cons]
          rw [ih t (by simpa using hlen)]
          rw [prodSC_cons, sideFactor]
          rw [show (sideCeilSum P pr + (rest.map (sideCeilSum P)).sum)
                + (sideDeg pr + (rest.map sideDeg).sum)
              = (sideCeilSum P pr + sideDeg pr)
                + ((rest.map (sideCeilSum P)).sum + (rest.map sideDeg).sum) from by ring]
          rw [pow_add, mul_inv]
          push_cast [Nat.cast_mul]
          ring

/-- **The closed form of `multiSideValue`** (`ShapesFor` length-match; MenuPath for the
reconciliation).  The product over sides factors into the joint residual count `prodSC p sh` times a
single box-volume factor `p^{-(newtonExponent (mkPoly s P) + Σ_{pr} sideDeg pr)}` — EXACTLY the
reciprocal of `p^{volExp (mkCell s P sh)}` (RESULT 1: `volExp (mkCell s P sh) =
newtonExponent (mkPoly s P) + Σ sideDeg`).  The Newton piece is the RECONCILED (truncated) sum, via
`sideCeilSum_sum`. -/
theorem omCount_multiSide_closed (s N : ℕ) (P : List (ℕ × ℕ)) (hP : MenuPath s N P)
    (sh : List (List (ℕ × ℕ))) (hsh : ShapesFor P sh) (p : ℕ) [Fact p.Prime] :
    multiSideValue s P sh p
      = (CellCard.prodSC p sh : ℚ)
          * ((p : ℚ) ^ (L4.newtonExponent (mkPoly s P) + ((sidePairs P).map sideDeg).sum))⁻¹ := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).ne_zero
  have hlen : sh.length = (sidePairs P).length := hsh.length_eq
  rw [multiSideValue]
  rw [multiSide_factor_zip P p (sidePairs P) sh hlen]
  -- reconcile the truncated per-side ceiling sum with the whole-path Newton exponent.
  rw [sideCeilSum_sum s N P hP]

#print axioms omCount_multiSide_closed

/-! ## 3. The multi-side `h_node` (product-of-sides stratum limit) -/

/-- `volExp` of a menu cell, standalone: `newtonExponent (mkPoly s P) + Σ_{pr} sideDeg pr`.  Extracted
from the `hvol` step of `PathShape.mkCell_volExp_add_freeExp`; the polygon slot is `mkPoly s P` and
the face degrees sum to `Σ sideDeg` (via `PathShape.faceDF_mkCell`, both def-transparent here). -/
private theorem zipWith_dF_sum (sp : List ((ℕ × ℕ) × (ℕ × ℕ))) (sh : List (List (ℕ × ℕ)))
    (hlen : sh.length = sp.length) :
    ((List.zipWith mkFace sp sh).map FaceAssign.dF).sum = (sp.map sideDeg).sum := by
  induction sp generalizing sh with
  | nil => simp
  | cons pr rest ih =>
      cases sh with
      | nil => simp at hlen
      | cons a t =>
          simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons]
          rw [ih t (by simpa using hlen)]
          rfl

private theorem volExp_mkCell (s : ℕ) (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ)))
    (hsh : ShapesFor P sh) :
    volExp (mkCell s P sh)
      = L4.newtonExponent (mkPoly s P) + ((sidePairs P).map sideDeg).sum := by
  have hlen : sh.length = (sidePairs P).length := hsh.length_eq
  rw [volExp]
  congr 1
  -- (mkCell s P sh).faces = zipWith mkFace (sidePairs P) sh; its dF-sum is Σ sideDeg.
  show ((List.zipWith mkFace (sidePairs P) sh).map FaceAssign.dF).sum = _
  exact zipWith_dF_sum (sidePairs P) sh hlen

/-- **RESULT 3 — the multi-side `h_node`.**  For a size-`s`, order-1, all-`μ = 1` MULTI-side menu
path `P` (any number of sides) carrying per-side shapes `sh` of the right degrees (`ShapesFor`), the
genuine order-1 stratum density `stratumCount1 s N (mkCell s P sh) / p^(s·N)` — normalized by the FULL
box `p^{s·N}` — converges (as `N → ∞`) to the PRODUCT-over-sides engine value
`multiSideValue s P sh p`.

Distinct Newton-slope branches MULTIPLY (independent OM branches, not children of a shared node), so
the limit is a product, not a single-node value.  The stratum side transfers VERBATIM from
`PathShape.hnode_oneSideShape` (RESULT 1 `mkCell_volExp_add_freeExp` is already proven for general
multi-side `P`, and `hnode_decided_order1` is multi-side-agnostic); only Step D's constant
identification changes — `prodSC · p^{-volExp}` is now identified with `multiSideValue` via
`omCount_multiSide_closed` + the standalone `volExp_mkCell`. -/
theorem hnode_multiSideShape (s N₀ : ℕ) (hN₀ : 0 < N₀) (P : List (ℕ × ℕ))
    (hP : MenuPath s N₀ P) (sh : List (List (ℕ × ℕ))) (hsh : ShapesFor P sh)
    (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto (fun N => (stratumCount1 p s N (mkCell s P sh) : ℚ) / (p:ℚ)^(s*N))
      Filter.atTop (nhds (multiSideValue s P sh p)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).ne_zero
  -- Step A: the p^{s(N-1)}-normalized limit (the decided-cell h_node), multi-side-agnostic.
  have hbase := hnode_decided_order1 (p := p) hN₀ hP hsh
  -- Step B: multiply by the constant (p^s)⁻¹.
  have hmul := hbase.mul_const ((p : ℚ) ^ s)⁻¹
  -- Step C: rewrite the sequence to the full-box normalization (eventually, N ≥ 1).
  have hseq : Filter.Tendsto
      (fun N => (stratumCount1 p s N (mkCell s P sh) : ℚ) / (p:ℚ)^(s*N))
      Filter.atTop
      (nhds (((CellCard.prodSC p sh : ℚ) * (p : ℚ) ^ CellCard.freeExp s N₀ P
                / (p : ℚ) ^ (s * (N₀ - 1))) * ((p : ℚ) ^ s)⁻¹)) := by
    refine hmul.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hexp : s * N = s * (N - 1) + s := by
      conv_lhs => rw [show N = (N - 1) + 1 from by omega]
      rw [Nat.mul_add, Nat.mul_one]
    rw [hexp, pow_add]
    field_simp
  -- Step D: identify the limit constant with `multiSideValue s P sh p`.
  have hvol : volExp (mkCell s P sh)
      = L4.newtonExponent (mkPoly s P) + ((sidePairs P).map sideDeg).sum :=
    volExp_mkCell s P sh hsh
  set V := L4.newtonExponent (mkPoly s P) + ((sidePairs P).map sideDeg).sum with hVdef
  -- RESULT 1 at N₀: volExp + freeExp = s·N₀, i.e. V + freeExp = s·N₀.
  have hvolid : V + CellCard.freeExp s N₀ P = s * N₀ := by
    rw [← hvol]; exact mkCell_volExp_add_freeExp s N₀ P hP sh hsh
  have hconst : ((CellCard.prodSC p sh : ℚ) * (p : ℚ) ^ CellCard.freeExp s N₀ P
      / (p : ℚ) ^ (s * (N₀ - 1))) * ((p : ℚ) ^ s)⁻¹
      = multiSideValue s P sh p := by
    rw [omCount_multiSide_closed s N₀ P hP sh hsh p, ← hVdef]
    -- combine denominators: p^(s(N₀-1)) · p^s = p^(s·N₀).
    have hden : (p : ℚ) ^ (s * (N₀ - 1)) * (p : ℚ) ^ s = (p : ℚ) ^ (s * N₀) := by
      rw [← pow_add]
      congr 1
      rw [show s * (N₀ - 1) + s = s * (N₀ - 1) + s * 1 from by rw [Nat.mul_one],
        ← Nat.mul_add, Nat.sub_add_cancel hN₀]
    -- s·N₀ = V + freeExp, so p^(s·N₀) = p^V · p^(freeExp).
    have hnum : (p : ℚ) ^ (s * N₀) = (p : ℚ) ^ V * (p : ℚ) ^ CellCard.freeExp s N₀ P := by
      rw [← pow_add]; congr 1; omega
    have hcollect : (p : ℚ) ^ CellCard.freeExp s N₀ P / (p : ℚ) ^ (s * (N₀ - 1)) * ((p : ℚ) ^ s)⁻¹
        = (p : ℚ) ^ CellCard.freeExp s N₀ P * ((p : ℚ) ^ (s * N₀))⁻¹ := by
      rw [div_eq_mul_inv, mul_assoc, ← mul_inv, hden]
    rw [mul_div_assoc, mul_assoc, hcollect, hnum, mul_inv]
    rw [show (p : ℚ) ^ CellCard.freeExp s N₀ P
          * (((p : ℚ) ^ V)⁻¹ * ((p : ℚ) ^ CellCard.freeExp s N₀ P)⁻¹)
        = ((p : ℚ) ^ V)⁻¹ from by field_simp]
  rw [← hconst]
  exact hseq

#print axioms hnode_multiSideShape

end LeanUrat.OM.PathShapeMultiSide
