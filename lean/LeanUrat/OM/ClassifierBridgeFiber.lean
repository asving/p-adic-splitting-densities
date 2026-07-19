/-
Scratch module (S3): the fiber characterization `classify_eq_selfloop_iff`.
Namespace LeanUrat.OM.ClassifierBridgeFiber.  Math-first, no sorry/axiom/native_decide.

This module BUILDS the single-side, all-μ=1 fiber characterization of the genuine order-0
classifier `B.classify` against the order-1 `InCell` membership predicate, the S3 analogue of
`Order0Alpha.classify_eq_sepShape_iff`.  It follows the SCOPE plan:

* STEP 0 (respell): `Tselfloop` is respelled to carry the classifier's own per-cell polygon
  `toSideFace (mkSide pr)` (not the stylized `mkPoly`), so the raw shape equality
  `B.classify = Tselfloop` can hold verbatim.  `omCount_selfloop_eq_oneSideShape` is re-proved
  through the `newtonExponent` bridge `newtonExponent (toSideFace (mkSide pr))
  = newtonExponent (mkPoly n [pr.1, pr.2])`.
* STEP 1 (head/payload skeleton): mirrors `Order0Classify.classify_eq_sepShape`.
* STEP 2 (residual identification): `rootResidual = residualOf p f pr` on the locus.
* STEP 3 (hull uniqueness): `B.rootSide = some (mkSide pr)` from the `InCell` data.
* STEP 4/5: backward direction + discharge.
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
import LeanUrat.OM.Order0Classify
import LeanUrat.OM.MontesAllOrders
import LeanUrat.OM.ClassifierBridge

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.ClassifierBridgeFiber

open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.PathShape
open LeanUrat.MontesAxiom (CountCell)

open scoped Classical

/-! ## STEP 0. The RESPELLED self-loop shape `Tselfloop`.

The genuine `B.classify` emits, per sorted factor, a `ShapeCell` whose `polygon` slot is
`c.polygon = T.Nr = rootFace = toSideFace (mkSide pr)` (`Classifier.rootFace`, `M5.cells`
`polygon := T.Nr`).  So for the raw shape equality `B.classify = Tselfloop` to hold verbatim we
respell the polygon slot of `Tselfloop` to `toSideFace (mkSide pr)`. -/

/-- **`T★` respelled** — the genuine `B.classify` output tree shape on the single-side, all-`μ=1`
self-loop locus: an ORDER-0 head `(0, s, Σ dS)` carrying one childless per-factor cell whose
polygon is the classifier's own side face `toSideFace (mkSide pr)`. -/
noncomputable def Tselfloop (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) : ClusterShape :=
  ⟨[(0, s, (shape.map Prod.fst).sum)],
    shape.map (fun q => ⟨q.1, 1, M7.toSideFace (mkSide pr), []⟩)⟩

/-! ### The `newtonExponent` bridge for the respell.

`omCount` reads a shape's polygon slot ONLY through `L4.newtonExponent` (inside `volExp`).  So to
transport the engine-value identity from the stylized `oneSideShape` (polygon `mkPoly s [pr.1,pr.2]`)
to the respelled `Tselfloop` (polygon `toSideFace (mkSide pr)`) it suffices to show the two polygons
have EQUAL `newtonExponent` on a single side `pr = ((0,H),(s,0))`. -/

/-- **The respell arithmetic core.**  For `H k s : ℕ` with `0 < s`, the rational ceiling of the
chord value `H − H·k/s` equals the natural-number floor-division expression `H − (H·k)/s`.  Since
`H` is an integer, `⌈H − H·k/s⌉ = H − ⌊H·k/s⌋`, and `⌊(H·k)/s⌋ = (H·k)/s` in ℕ. -/
theorem ceil_chord_eq (H k s : ℕ) :
    (⌈(H : ℚ) - ((H : ℚ) * (k : ℚ)) / (s : ℚ)⌉).toNat = H - (H * k) / s := by
  have hcast : (H : ℚ) * (k : ℚ) / (s : ℚ) = ((H * k : ℕ) : ℚ) / ((s : ℕ) : ℚ) := by
    push_cast; ring
  rw [hcast, show (H : ℚ) - ((H * k : ℕ) : ℚ) / ((s : ℕ) : ℚ)
        = (H : ℚ) + (-(((H * k : ℕ) : ℚ) / ((s : ℕ) : ℚ))) by ring,
    Int.ceil_natCast_add, Int.ceil_neg, Int.floor_div_natCast, Int.floor_natCast]
  rw [show ((H * k : ℕ) : ℤ) / ((s : ℕ) : ℤ) = (((H * k) / s : ℕ) : ℤ) from by exact_mod_cast rfl]
  omega

/-- On a self-loop side `pr = ((0,H),(s,0))`, the side's slope is `-H/s` and its left height is `H`. -/
theorem mkSide_selfloop_slope {H s : ℕ} :
    (mkSide (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ))).slope = -(H : ℚ) / (s : ℚ) := by
  show ((0 : ℚ) - (H : ℚ)) / ((s : ℚ) - (0 : ℚ)) = -(H : ℚ) / (s : ℚ)
  rw [sub_zero, zero_sub]

/-- The per-column ceiling height of the self-loop side face equals the chord `H − H·k/s`. -/
theorem sideCeilHeight_selfloop {H s : ℕ} (k : ℕ) :
    M7.sideCeilHeight (mkSide (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) k
      = (⌈(H : ℚ) - ((H : ℚ) * (k : ℚ)) / (s : ℚ)⌉).toNat := by
  unfold M7.sideCeilHeight
  rw [mkSide_selfloop_slope]
  congr 2
  show ((mkSide (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ))).v₀ : ℚ) + (-(H : ℚ) / (s : ℚ)) * (k : ℚ)
      = (H : ℚ) - (H : ℚ) * (k : ℚ) / (s : ℚ)
  show (H : ℚ) + (-(H : ℚ) / (s : ℚ)) * (k : ℚ) = (H : ℚ) - (H : ℚ) * (k : ℚ) / (s : ℚ)
  ring

/-- The path-`ceilAt` of the two-vertex self-loop path at an interior column `k < s`. -/
theorem ceilAt_selfloop {H s : ℕ} {k : ℕ} (hk : k < s) :
    ceilAt [((0 : ℕ), H), ((s : ℕ), (0 : ℕ))] k = H - (H * k) / s := by
  cases k with
  | zero =>
      show ceilAt [((0 : ℕ), H), ((s : ℕ), (0 : ℕ))] 0 = H - (H * 0) / s
      unfold ceilAt
      rw [if_pos (le_refl 0)]
      simp
  | succ m =>
      show ceilAt [((0 : ℕ), H), ((s : ℕ), (0 : ℕ))] (m + 1) = H - (H * (m + 1)) / s
      unfold ceilAt
      rw [if_neg (by omega : ¬ (m + 1 ≤ (0 : ℕ))), if_pos (by omega : m + 1 ≤ s)]
      show H - (H - 0) * (m + 1 - 0) / (s - 0) = H - H * (m + 1) / s
      simp

/-- **The `newtonExponent` bridge for the respell.**  On a self-loop side `pr = ((0,H),(s,0))`, the
classifier's side face `toSideFace (mkSide pr)` and the stylized path polygon `mkPoly s [pr.1,pr.2]`
have EQUAL Newton exponents: both sum the identical per-column ceiling `H − (H·k)/s` over the `s`
columns.  This is the ONLY quantity `omCount` reads off the polygon slot, so the respell leaves the
engine value invariant. -/
theorem newtonExponent_toSideFace_eq_mkPoly {H s : ℕ} :
    L4.newtonExponent (M7.toSideFace (mkSide (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ))))
      = L4.newtonExponent (mkPoly s [((0 : ℕ), H), ((s : ℕ), (0 : ℕ))]) := by
  -- width of the side face is `(mkSide pr).length = pr.2.1 - pr.1.1 = s`.
  have hwidth : (mkSide (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ))).length = s := by
    show (s : ℕ) - (0 : ℕ) = s; omega
  -- Both are `∑ k ∈ range s, (H − (H·k)/s)`, column-wise equal.
  have hlhs : L4.newtonExponent (M7.toSideFace (mkSide (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ))))
      = ∑ k ∈ Finset.range s,
          M7.sideCeilHeight (mkSide (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) k := by
    rw [L4.newtonExponent, ← Fin.sum_congr'
      (fun i : Fin (M7.toSideFace (mkSide (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))).width =>
        (M7.toSideFace (mkSide (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))).ceilHeights i)
      hwidth.symm]
    rw [Finset.sum_range
      (fun k => M7.sideCeilHeight (mkSide (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) k)]
    rfl
  have hrhs : L4.newtonExponent (mkPoly s [((0 : ℕ), H), ((s : ℕ), (0 : ℕ))])
      = ∑ k ∈ Finset.range s, ceilAt [((0 : ℕ), H), ((s : ℕ), (0 : ℕ))] k := by
    rw [L4.newtonExponent, Finset.sum_range (fun k => ceilAt [((0 : ℕ), H), ((s : ℕ), (0 : ℕ))] k)]
    rfl
  rw [hlhs, hrhs]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  rw [sideCeilHeight_selfloop, ceil_chord_eq, ceilAt_selfloop hk]

/-! ### STEP 0, target 3 — the engine-value identity, RE-PROVED after the respell.

`omCount` reads a shape ONLY through `configsOf = [configOf T]`, and `configOf` reads only the
WF-guarded `cells` payload; through the polygon slot it feeds `omCount` ONLY via `volExp`'s
`newtonExponent`.  The respelled `Tselfloop` and the stylized `oneSideShape` carry the SAME childless
per-factor payload except for the polygon (`toSideFace (mkSide pr)` vs `mkPoly s [pr.1,pr.2]`), whose
`newtonExponent`s agree by `newtonExponent_toSideFace_eq_mkPoly`. -/

/-- The WF cell list of the respelled `Tselfloop`: one childless per-factor cell carrying the side
face polygon.  Mirror of `PathShape.cellsOfShapeWF_oneSideShape`. -/
theorem cellsOfShapeWF_Tselfloop (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    M7.cellsOfShapeWF (Tselfloop s pr shape)
      = shape.map (fun q =>
          ({ dS := q.1, δ := 1, polygon := M7.toSideFace (mkSide pr), children := [] } : CountCell)) := by
  rw [M7.cellsOfShapeWF_eq_of_descend]
  · rw [M7.cellsOfShape, Tselfloop, List.map_map]
    rfl
  · intro c hc ch hch
    rw [M7.cellsOfShape, Tselfloop, List.map_map, List.mem_map] at hc
    obtain ⟨q, _, rfl⟩ := hc
    exact absurd hch List.not_mem_nil

/-- The `mCell` (face-choice count) of `configOf` is invariant under the polygon respell: `mCell`
reads only the faces, and the two `configOf` faces agree because the face readers
(`nodeDelta`/`cellMult`/`cellResDeg`) ignore the cell `polygon`. -/
theorem faces_configOf_Tselfloop (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    (configOf (Tselfloop s pr shape)).faces = (configOf (oneSideShape s pr shape)).faces := by
  unfold configOf
  rw [cellsOfShapeWF_Tselfloop, PathShape.cellsOfShapeWF_oneSideShape]
  -- element-wise: the single FaceAssign has all three data fields equal (readers ignore polygon).
  simp only [Order0.nodeDelta, List.map_map]
  cases shape with
  | nil => rfl
  | cons a t => rfl

/-- The descent children of `configOf` are `[]` for both shapes (every per-factor cell is
childless), so they agree. -/
theorem children_configOf_Tselfloop (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    (configOf (Tselfloop s pr shape)).children = (configOf (oneSideShape s pr shape)).children := by
  unfold configOf
  rw [cellsOfShapeWF_Tselfloop, PathShape.cellsOfShapeWF_oneSideShape]
  rw [List.flatMap_eq_nil_iff.mpr, List.flatMap_eq_nil_iff.mpr]
  · intro c hc
    rw [List.mem_map] at hc
    obtain ⟨q, _, rfl⟩ := hc
    rfl
  · intro c hc
    rw [List.mem_map] at hc
    obtain ⟨q, _, rfl⟩ := hc
    rfl

/-- `volExp (configOf Tselfloop) = volExp (configOf oneSideShape)`: the faces' `dF` agree, and the
head-cell polygon's `newtonExponent` agrees by `newtonExponent_toSideFace_eq_mkPoly` on the
self-loop side `pr = ((0,H),(s,0))`. -/
theorem volExp_configOf_Tselfloop (s H : ℕ) (shape : List (ℕ × ℕ)) (hne : shape ≠ []) :
    volExp (configOf (Tselfloop s (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape))
      = volExp (configOf (oneSideShape s (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape)) := by
  rw [volExp, volExp, faces_configOf_Tselfloop s _ shape]
  congr 1
  -- polygon slots: head? of the two WF cell lists.
  rw [configOf, configOf]
  rw [cellsOfShapeWF_Tselfloop, PathShape.cellsOfShapeWF_oneSideShape]
  cases shape with
  | nil => exact absurd rfl hne
  | cons a t =>
      simp only [List.map_cons, List.head?_cons, Option.map_some, Option.getD_some]
      exact newtonExponent_toSideFace_eq_mkPoly

/-- **TARGET 3 — the engine-value identity (RE-PROVED after the respell).**  The respelled
`Tselfloop` (order-0 head, per-cell polygon `toSideFace (mkSide pr)`) and the stylized
`oneSideShape` (order-1 head, polygon `mkPoly s [pr.1,pr.2]`) evaluate to the SAME `omCount`
rational.  Proof: `omCount` reads a shape only through `configsOf = [configOf T]`; the single
summand is `mCell (configOf) · (p^volExp)⁻¹ · (children-prod)`.  `mCell` reads only the faces
(`faces_configOf_Tselfloop`), the children agree (`children_configOf_Tselfloop`), and `volExp` reads
the polygon only through `newtonExponent`, which agrees by `volExp_configOf_Tselfloop`. -/
theorem omCount_selfloop_eq_oneSideShape (s H : ℕ) (shape : List (ℕ × ℕ)) (hne : shape ≠ [])
    (p : ℕ) [Fact p.Prime] :
    omCount (Tselfloop s (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape) p
      = omCount (oneSideShape s (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape) p := by
  rw [omCount, omCount]
  unfold configsOf
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [show mCell (configOf (Tselfloop s (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape)) p
        = mCell (configOf (oneSideShape s (((0, H), (s, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape)) p from by
      unfold mCell; rw [faces_configOf_Tselfloop s _ shape],
    volExp_configOf_Tselfloop s H shape hne, children_configOf_Tselfloop s _ shape]

/-! ## STEP 3 preamble — the single-side path is a two-vertex path `[(0,H),(n,0)]`.

A `MenuPath` with exactly one side (`sidePairs P = [pr]`) is the two-vertex path from the readable
left endpoint `(0, H)` straight down to `(n, 0)`; the single side is `pr = ((0,H),(n,0))`. -/

/-- A single-side menu path is `[(0,H),(n,0)]` and its side is `pr = ((0,H),(n,0))` with
`1 ≤ H ≤ N−1`. -/
theorem menuPath_single_side {n N : ℕ} {P : List (ℕ × ℕ)} {pr : (ℕ × ℕ) × (ℕ × ℕ)}
    (hP : MenuPath n N P) (hsingle : sidePairs P = [pr]) :
    ∃ H, P = [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))] ∧ pr = (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
      ∧ 1 ≤ H ∧ H ≤ N - 1 := by
  obtain ⟨H, p1, T, hPeq, hH1, hH2, hp1a, hp1b, hc⟩ := hP
  subst hPeq
  -- sidePairs ((0,H) :: p1 :: T) = ((0,H), p1) :: sidePairs (p1 :: T)
  rw [sidePairs_cons₂] at hsingle
  -- single element ⟹ sidePairs (p1 :: T) = [] ⟹ T = []
  have hpr : pr = (((0, H), p1) : (ℕ × ℕ) × (ℕ × ℕ)) := by
    have := List.head_eq_of_cons_eq hsingle
    exact this.symm
  have hnil : sidePairs (p1 :: T) = [] := by
    have := List.tail_eq_of_cons_eq hsingle
    simpa using this
  -- sidePairs (p1 :: T) = (p1 :: T).zip T ; = [] ⟹ T = []
  have hT : T = [] := by
    cases T with
    | nil => rfl
    | cons b t => simp [sidePairs] at hnil
  subst hT
  -- ChainOK n (0,H) p1 [] ⟹ p1 = (n, 0)
  have hp1 : p1 = ((n : ℕ), (0 : ℕ)) := by
    cases hc with
    | nil h1 h2 => exact Prod.ext h1 h2
  subst hp1
  exact ⟨H, rfl, hpr, hH1, hH2⟩

/-! ### `dropCollinear` of a set of collinear points.

If every point of the list lies on a single affine line (all triples collinear) and the abscissae
strictly increase, `dropCollinear` returns exactly the first and last points — the single-side hull
has just its two corner vertices. -/

/-- `Q` lies exactly on the integer line through `A` and `B` (cross-multiplied, no division):
`(B.1 − A.1)·(Q.2 − A.2) = (Q.1 − A.1)·(B.2 − A.2)`. -/
def OnLineℤ (A B Q : ℕ × ℕ) : Prop :=
  ((B.1 : ℤ) - A.1) * ((Q.2 : ℤ) - A.2) = ((Q.1 : ℤ) - A.1) * ((B.2 : ℤ) - A.2)

/-- Three points `a`, `Bp`, `C` all lying on the line through `A`,`B` (with nonzero direction
`A.1 < B.1`) are collinear w.r.t. anchor `a`: `collinear₃ a Bp C` holds. (All three displacements
from `A` are parallel to the fixed direction, so the cross product `(Bp − a) × (C − a)` vanishes;
cancel the common nonzero factor `B.1 − A.1`.) -/
theorem collinear₃_of_onLine {A B a Bp C : ℕ × ℕ}
    (hAB : (A.1 : ℤ) < (B.1 : ℤ))
    (ha : OnLineℤ A B a) (hBp : OnLineℤ A B Bp) (hC : OnLineℤ A B C) :
    NewtonPolygon.collinear₃ a Bp C = true := by
  unfold NewtonPolygon.collinear₃ OnLineℤ at *
  rw [beq_iff_eq]
  have hd : ((B.1 : ℤ) - A.1) ≠ 0 := by omega
  -- Cancel the common nonzero factor (B.1 − A.1); the identity is polynomial in the three OnLine eqns.
  refine mul_left_cancel₀ hd ?_
  nlinarith [ha, hBp, hC, sq_nonneg ((B.1 : ℤ) - A.1)]

/-- **`dropCollinear` collapse.**  A list `a :: b :: rest` all of whose points lie on the line
through `A`,`B` (nonzero direction `A.1 < B.1`) collapses under `dropCollinear` to just its first
and last points: `dropCollinear (a :: b :: rest) = [a, (b :: rest).getLast _]`.  Proof by induction
on `rest`: the base `[a,b]` is `dropCollinear`-fixed; in the step the recursive tail collapses (IH)
to `[b, last]`, and `collinear₃ a b last` fires (`collinear₃_of_onLine`), dropping the interior. -/
theorem dropCollinear_collapse {A B : ℕ × ℕ} (hAB : (A.1 : ℤ) < (B.1 : ℤ)) :
    ∀ (a b : ℕ × ℕ) (rest : List (ℕ × ℕ)),
      (∀ Q ∈ a :: b :: rest, OnLineℤ A B Q) →
      NewtonPolygon.dropCollinear (a :: b :: rest)
        = [a, (b :: rest).getLast (by simp)] := by
  intro a b rest
  induction rest generalizing a b with
  | nil =>
      intro _
      show NewtonPolygon.dropCollinear [a, b] = [a, ([b]).getLast (by simp)]
      rw [NewtonPolygon.dropCollinear]
      rfl
  | cons c t ih =>
      intro hon
      -- recursion: dropCollinear (a :: b :: c :: t) via dropCollinear (b :: c :: t)
      rw [NewtonPolygon.dropCollinear_cons3]
      have hon' : ∀ Q ∈ b :: c :: t, OnLineℤ A B Q := fun Q hQ =>
        hon Q (List.mem_cons_of_mem a hQ)
      rw [ih b c hon']
      -- tail collapsed to `[b, last]`; the match hits `b' = b, c' = last, rest' = []`.
      simp only
      -- `collinear₃ a b last` holds: a, b, last all on the line A,B.
      have haOn : OnLineℤ A B a := hon a (by simp)
      have hbOn : OnLineℤ A B b := hon b (by simp)
      have hlastOn : OnLineℤ A B ((c :: t).getLast (by simp)) := by
        apply hon
        exact List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.getLast_mem _))
      rw [if_pos (collinear₃_of_onLine hAB haOn hbOn hlastOn)]
      rw [show (b :: c :: t).getLast (by simp) = (c :: t).getLast (by simp) from
        List.getLast_cons (by simp)]


/-! ### List head/last extremal lemmas (for the sorted vertex abscissae). -/

/-- In a strictly-increasing (`<`-pairwise) list of naturals containing `0`, the head is `0`. -/
theorem head_eq_zero_of_pairwise {L : List ℕ} (hp : L.Pairwise (· < ·)) (h0 : 0 ∈ L) :
    L.head? = some 0 := by
  cases L with
  | nil => simp at h0
  | cons a t =>
      rw [List.pairwise_cons] at hp
      rcases List.mem_cons.mp h0 with rfl | h0'
      · rfl
      · exact absurd (hp.1 0 h0') (by omega)

/-- In a `<`-pairwise list of naturals all `≤ n` and containing `n`, the last element is `n`. -/
theorem getLast_eq_of_pairwise {L : List ℕ} (hp : L.Pairwise (· < ·))
    (hle : ∀ x ∈ L, x ≤ n) (hn : n ∈ L) (hne : L ≠ []) :
    L.getLast hne = n := by
  induction L with
  | nil => exact absurd rfl hne
  | cons a t ih =>
      rw [List.pairwise_cons] at hp
      cases t with
      | nil =>
          have : a = n := by
            rcases List.mem_cons.mp hn with rfl | hn'
            · rfl
            · simp at hn'
          simpa using this
      | cons b s =>
          rw [List.getLast_cons (by simp)]
          have hnmem : n ∈ b :: s := by
            rcases List.mem_cons.mp hn with rfl | hn'
            · exact absurd (hp.1 b (by simp)) (by have := hle b (by simp); omega)
            · exact hn'
          exact ih hp.2 (fun x hx => hle x (List.mem_cons_of_mem a hx)) hnmem (by simp)

/-! ## STEP 3 — the Newton-polygon UNIQUENESS lemma (the hull geometry).

The heart of the forward direction: from the `InCell` data on a single side `pr = ((0,H),(n,0))`
(vertex exactness `vOf f 0 = H`, `vOf f n = 0`; and `SideAbove`: every window dot on/above the
chord) we show `B.rootSide realP N f = some (mkSide pr)`, i.e. `npSides (boxValSupport f) = [mkSide
pr]`.  Route: the chord `((0,H),(n,0))` is a VALID supporting line (all dots on/above it, both
endpoints on it), so `npHeight = chord` on `[0,n]`; the two endpoints are on the hull; every other
support dot lies on-or-above, and the hull is the single chord line, so after `dropCollinear` exactly
the two corner vertices remain. -/

section HullUniqueness

variable (p : ℕ) [Fact p.Prime]

open NewtonPolygon

/-- The Newton-polygon chord through the two dots `(0,H)` and `(n,0)` coincides with the CellMenu
side line `lineAt ((0,H),(n,0))`. -/
theorem pairLine_eq_lineAt (H n : ℕ) (x : ℚ) :
    pairLine ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) x
      = lineAt (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) x := by
  unfold pairLine pairSlope lineAt slopeQ
  push_cast
  ring

/-- Every support index of a monic degree-`n` box element is `≤ n`. -/
theorem support_le_deg {N n : ℕ} (f : QuotientBox.monicBox p N n) {i : ℕ}
    (hi : i ∈ (f.1).support) : i ≤ n := by
  have hle : i ≤ (f.1).natDegree := Polynomial.le_natDegree_of_mem_supp i hi
  rwa [f.2.2] at hle

/-- A support dot of the box element, decorated, lies in `boxValSupport`. -/
theorem mem_boxValSupport {N n : ℕ} (f : QuotientBox.monicBox p N n) {i : ℕ}
    (hi : (f.1).coeff i ≠ 0) :
    (i, vOf p f i) ∈ B.boxValSupport p N f := by
  rw [B.boxValSupport, Finset.mem_image]
  exact ⟨i, Polynomial.mem_support_iff.mpr hi, rfl⟩

/-- Every dot of `boxValSupport` is `(i, vOf f i)` for some support index `i`. -/
theorem boxValSupport_eq_dot {N n : ℕ} (f : QuotientBox.monicBox p N n) {Q : ℕ × ℕ}
    (hQ : Q ∈ B.boxValSupport p N f) : Q.2 = vOf p f Q.1 ∧ (f.1).coeff Q.1 ≠ 0 := by
  rw [B.boxValSupport, Finset.mem_image] at hQ
  obtain ⟨i, hi, rfl⟩ := hQ
  exact ⟨rfl, Polynomial.mem_support_iff.mp hi⟩

/-- **All support dots lie on or above the chord** (the `SideAbove` extension to the full support).
Given the `InCell` side condition `SideAbove f pr` on `pr = ((0,H),(n,0))`, every support dot
`(i, vOf f i)` (all with `i ≤ n`) satisfies `pairLine (0,H)(n,0) i ≤ vOf f i`. -/
theorem allDotsAbove {N n H : ℕ} (f : QuotientBox.monicBox p N n)
    (hside : SideAbove p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) :
    ∀ Q ∈ B.boxValSupport p N f,
      pairLine ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) (Q.1 : ℚ) ≤ (Q.2 : ℚ) := by
  intro Q hQ
  obtain ⟨hv, hne⟩ := boxValSupport_eq_dot p f hQ
  have hle : Q.1 ≤ n := support_le_deg p f (Polynomial.mem_support_iff.mpr hne)
  rw [pairLine_eq_lineAt, hv]
  exact hside Q.1 (Nat.zero_le _) hle

/-- **The chord is a valid supporting line.**  `((0,H),(n,0)) ∈ validLines (boxValSupport f)`:
every support dot lies on/above it (`allDotsAbove`), which is exactly the validity condition. -/
theorem chord_validLine {N n H : ℕ} (f : QuotientBox.monicBox p N n)
    (hside : SideAbove p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))
    (h0 : (((0 : ℕ), H) : ℕ × ℕ) ∈ B.boxValSupport p N f)
    (hn : (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) ∈ B.boxValSupport p N f) :
    (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ validLines (B.boxValSupport p N f) := by
  rw [validLines, Finset.mem_filter]
  refine ⟨Finset.mem_product.2 ⟨h0, hn⟩, ?_⟩
  intro Q hQ
  exact allDotsAbove p f hside Q hQ

/-- The left endpoint `(0,H)` is a support dot: `vOf f 0 = H < N` forces `f.coeff 0 ≠ 0`. -/
theorem mem_boxValSupport_left {N n H : ℕ} (_hN : 0 < N) (f : QuotientBox.monicBox p N n)
    (hv0 : vOf p f 0 = H) (hHN : H < N) :
    (((0 : ℕ), H) : ℕ × ℕ) ∈ B.boxValSupport p N f := by
  have hne : (f.1).coeff 0 ≠ 0 := by
    intro h0
    rw [vOf, h0, PadicLift.zmodValuation_zero] at hv0
    omega
  have := mem_boxValSupport p f hne
  rwa [hv0] at this

/-- The right endpoint `(n,0)` is a support dot (the monic leading coefficient). -/
theorem mem_boxValSupport_right {N n : ℕ} (hN : 0 < N) (f : QuotientBox.monicBox p N n) :
    (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) ∈ B.boxValSupport p N f := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' (Fact.out (p := p.Prime)).one_lt⟩
  have hc : (f.1).coeff n = 1 := by
    have hcn : (f.1).coeff ((f.1).natDegree) = 1 := f.2.1.coeff_natDegree
    rwa [f.2.2] at hcn
  have hne : (f.1).coeff n ≠ 0 := by rw [hc]; exact one_ne_zero
  have hv : vOf p f n = 0 := vOf_leading p hN f
  have := mem_boxValSupport p f hne
  rwa [hv] at this

/-- **`npHeight` equals the chord on the window `[0,n]`** (chord attainment on the validLine). -/
theorem npHeight_eq_chord {N n H : ℕ} (f : QuotientBox.monicBox p N n)
    (hS : (B.boxValSupport p N f).Nonempty)
    (hval : (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ validLines (B.boxValSupport p N f))
    {x : ℚ} (hx : x ∈ Set.Icc ((0 : ℕ) : ℚ) ((n : ℕ) : ℚ)) :
    npHeight (B.boxValSupport p N f) hS x = pairLine ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) x :=
  npHeight_eq_pairLine_of_validLine (B.boxValSupport p N f) hS hval hx

/-- An on-hull support dot lies on the integer chord line through `(0,H)` and `(n,0)`. -/
theorem onHull_onLine {N n H : ℕ} (hn0 : 0 < n) (f : QuotientBox.monicBox p N n)
    (hS : (B.boxValSupport p N f).Nonempty)
    (hval : (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ validLines (B.boxValSupport p N f))
    {Q : ℕ × ℕ} (hQmem : Q ∈ B.boxValSupport p N f) (hQhull : OnHull (B.boxValSupport p N f) hS Q) :
    OnLineℤ (((0 : ℕ), H) : ℕ × ℕ) (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) Q := by
  obtain ⟨_, hne⟩ := boxValSupport_eq_dot p f hQmem
  have hle : Q.1 ≤ n := support_le_deg p f (Polynomial.mem_support_iff.mpr hne)
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn0
  -- OnHull: (Q.2 : ℚ) = npHeight Q.1 = chord Q.1
  have hchord : (Q.2 : ℚ) = pairLine ((0 : ℕ), H) ((n : ℕ), (0 : ℕ)) (Q.1 : ℚ) := by
    rw [OnHull] at hQhull
    rw [hQhull]
    exact npHeight_eq_chord p f hS hval ⟨by positivity, by exact_mod_cast hle⟩
  rw [pairLine, pairSlope] at hchord
  simp only [Nat.cast_zero, sub_zero] at hchord
  unfold OnLineℤ
  have hchord' : (Q.2 : ℚ) * (n : ℚ) = (H : ℚ) * (n : ℚ) + (0 - (H : ℚ)) * (Q.1 : ℚ) := by
    field_simp at hchord
    linarith [hchord]
  have hZ : (Q.2 : ℤ) * (n : ℤ) = (H : ℤ) * (n : ℤ) + (0 - (H : ℤ)) * (Q.1 : ℤ) := by
    exact_mod_cast hchord'
  have : ((n : ℤ) - 0) * ((Q.2 : ℤ) - H) = ((Q.1 : ℤ) - 0) * (0 - H) := by
    nlinarith [hZ]
  simpa using this

/-- Both endpoints lie on the hull (`npHeight` attains their heights via chord attainment). -/
theorem onHull_endpoints {N n H : ℕ} (hn0 : 0 < n) (f : QuotientBox.monicBox p N n)
    (hS : (B.boxValSupport p N f).Nonempty)
    (hval : (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ validLines (B.boxValSupport p N f)) :
    OnHull (B.boxValSupport p N f) hS (((0 : ℕ), H) : ℕ × ℕ)
    ∧ OnHull (B.boxValSupport p N f) hS (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn0
  constructor
  · show ((H : ℕ) : ℚ) = npHeight (B.boxValSupport p N f) hS ((0 : ℕ) : ℚ)
    rw [npHeight_eq_chord p f hS hval ⟨le_refl _, by positivity⟩]
    rw [pairLine_left]
  · show ((0 : ℕ) : ℚ) = npHeight (B.boxValSupport p N f) hS ((n : ℕ) : ℚ)
    rw [npHeight_eq_chord p f hS hval ⟨by positivity, le_refl _⟩]
    have hne : (((0 : ℕ), H) : ℕ × ℕ).1 ≠ (((n : ℕ), (0 : ℕ)) : ℕ × ℕ).1 := by
      simp only; omega
    rw [pairLine_right _ _ (by exact_mod_cast hne)]

/-- **STEP 3 — the hull uniqueness lemma.**  On the single-side `InCell` locus, the genuine
lower Newton polygon of `f` has EXACTLY the vertices `[(0,H),(n,0)]`: every support dot lies on/above
the chord (a valid supporting line), both endpoints are on the hull, and every other on-hull dot is
collinear with them (on the same chord), so `dropCollinear` leaves just the two corners. -/
theorem npVertices_eq_selfloop {N n H : ℕ} (hn0 : 0 < n) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n)
    (hv0 : vOf p f 0 = H) (hHN : H < N)
    (hside : SideAbove p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) :
    NewtonPolygon.npVertices (B.boxValSupport p N f) (B.boxValSupport_nonempty p N hN f)
      = [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))] := by
  set S := B.boxValSupport p N f with hSdef
  set hS := B.boxValSupport_nonempty p N hN f with hShyp
  have h0mem : (((0 : ℕ), H) : ℕ × ℕ) ∈ S := mem_boxValSupport_left p hN f hv0 hHN
  have hnmem : (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) ∈ S := mem_boxValSupport_right p hN f
  have hval : (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ NewtonPolygon.validLines S :=
    chord_validLine p f hside h0mem hnmem
  obtain ⟨hhull0, hhulln⟩ := onHull_endpoints p hn0 f hS hval
  -- `V := npVerticesFull S hS`; its abscissa list is `hullAbscissae`.
  set V := NewtonPolygon.npVerticesFull S hS with hVdef
  have hfst : V.map Prod.fst = NewtonPolygon.hullAbscissae S hS := NewtonPolygon.npVerticesFull_fst S hS
  have hpair : (V.map Prod.fst).Pairwise (· < ·) := NewtonPolygon.npVerticesFull_sorted S hS
  -- `0` and `n` are hull abscissae; all abscissae `≤ n`.
  have h0abs : (0 : ℕ) ∈ V.map Prod.fst := by
    rw [hfst, NewtonPolygon.mem_hullAbscissae_iff]
    exact ⟨H, h0mem, by rw [← hhull0]⟩
  have hnabs : (n : ℕ) ∈ V.map Prod.fst := by
    rw [hfst, NewtonPolygon.mem_hullAbscissae_iff]
    exact ⟨0, hnmem, by rw [← hhulln]⟩
  -- every vertex of `V` is a support dot of `S`.
  have hVsub : ∀ Q ∈ V, Q ∈ S := by
    intro Q hQV
    have habs : Q.1 ∈ NewtonPolygon.hullAbscissae S hS := by
      rw [← hfst, List.mem_map]; exact ⟨Q, hQV, rfl⟩
    rw [NewtonPolygon.mem_hullAbscissae_iff] at habs
    obtain ⟨v, hvmem, hvon⟩ := habs
    -- Q is on-hull with abscissa Q.1, so Q.2 = npHeight Q.1 = v
    have hQon : (Q.2 : ℚ) = npHeight S hS (Q.1 : ℚ) := NewtonPolygon.npVerticesFull_on_hull S hS hQV
    have hQ2 : Q.2 = v := by
      have : (Q.2 : ℚ) = (v : ℚ) := by rw [hQon, ← hvon]
      exact_mod_cast this
    have : Q = (Q.1, v) := by rw [← hQ2]
    rw [this]; exact hvmem
  have hallabs : ∀ x ∈ V.map Prod.fst, x ≤ n := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨Q, hQV, rfl⟩ := hx
    obtain ⟨_, hne⟩ := boxValSupport_eq_dot p f (hVsub Q hQV)
    exact support_le_deg p f (Polynomial.mem_support_iff.mpr hne)
  -- head abscissa is 0, last abscissa is n.
  have hheadabs : (V.map Prod.fst).head? = some 0 := head_eq_zero_of_pairwise hpair h0abs
  have hVne : V ≠ [] := by
    intro hnil; rw [hnil] at h0abs; simp at h0abs
  have hlastabs : (V.map Prod.fst).getLast (by
      intro hnil; exact hVne (List.map_eq_nil_iff.mp hnil)) = n :=
    getLast_eq_of_pairwise hpair hallabs hnabs _
  -- V's head is (0,H) and last is (n,0), using on-hull.
  have hVheadeq : V.head hVne = (((0 : ℕ), H) : ℕ × ℕ) := by
    have habs0 : (V.head hVne).1 = 0 := by
      have := hheadabs
      rw [List.head?_map, List.head?_eq_some_head hVne, Option.map_some, Option.some.injEq] at this
      exact this
    -- on-hull with abscissa 0 ⟹ height = chord 0 = H
    have hmem : V.head hVne ∈ V := List.head_mem hVne
    have hSmem : V.head hVne ∈ S := hVsub _ hmem
    have hon : ((V.head hVne).2 : ℚ) = npHeight S hS ((V.head hVne).1 : ℚ) :=
      NewtonPolygon.npVerticesFull_on_hull S hS hmem
    have : (V.head hVne).2 = H := by
      have hh : ((V.head hVne).2 : ℚ) = (H : ℚ) := by
        rw [hon, habs0]
        rw [show ((0 : ℕ) : ℚ) = (((0 : ℕ), H) : ℕ × ℕ).1 from by simp,
          ← Eq.symm hhull0]
      exact_mod_cast hh
    exact Prod.ext habs0 this
  have hVlasteq : V.getLast hVne = (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) := by
    have habsn : (V.getLast hVne).1 = n := by
      have hml : (V.map Prod.fst).getLast (by
          intro hnil; exact hVne (List.map_eq_nil_iff.mp hnil)) = (V.getLast hVne).1 := by
        rw [List.getLast_map]
      rw [← hml]; exact hlastabs
    have hmem : V.getLast hVne ∈ V := List.getLast_mem hVne
    have hon : ((V.getLast hVne).2 : ℚ) = npHeight S hS ((V.getLast hVne).1 : ℚ) :=
      NewtonPolygon.npVerticesFull_on_hull S hS hmem
    have : (V.getLast hVne).2 = 0 := by
      have hh : ((V.getLast hVne).2 : ℚ) = ((0 : ℕ) : ℚ) := by
        rw [hon, habsn]
        rw [show ((n : ℕ) : ℚ) = (((n : ℕ), (0 : ℕ)) : ℕ × ℕ).1 from by simp,
          ← Eq.symm hhulln]
      exact_mod_cast hh
    exact Prod.ext habsn this
  -- All vertices are on the chord line `OnLineℤ (0,H) (n,0)`.
  have hVline : ∀ Q ∈ V, OnLineℤ (((0 : ℕ), H) : ℕ × ℕ) (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) Q := by
    intro Q hQV
    exact onHull_onLine p hn0 f hS hval (hVsub Q hQV)
      (NewtonPolygon.npVerticesFull_on_hull S hS hQV)
  -- V has at least two elements: head (0,H) and last (n,0) differ (distinct abscissae 0 ≠ n).
  rw [NewtonPolygon.npVertices]
  show NewtonPolygon.dropCollinear V = _
  -- destructure V; it cannot be [] (hVne) nor a singleton (head ≠ last).
  match hVeq : V with
  | [] => exact absurd hVeq hVne
  | [a] =>
      -- singleton: head = last = a, but (0,H) ≠ (n,0).
      exfalso
      have hha : a = (((0 : ℕ), H) : ℕ × ℕ) := by
        rw [← hVheadeq]
        have : V.head hVne = ([a] : List (ℕ × ℕ)).head (by simp) := by congr 1
        rw [this]; rfl
      have hla : a = (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) := by
        rw [← hVlasteq]
        have : V.getLast hVne = ([a] : List (ℕ × ℕ)).getLast (by simp) := by congr 1
        rw [this]; rfl
      rw [hha] at hla
      have : (0 : ℕ) = n := congrArg Prod.fst hla
      omega
  | a :: b :: rest =>
      -- apply the collinear-collapse; head = a = (0,H), last = (n,0).
      have hAB : ((((0 : ℕ), H) : ℕ × ℕ).1 : ℤ) < ((((n : ℕ), (0 : ℕ)) : ℕ × ℕ).1 : ℤ) := by
        simp only; exact_mod_cast hn0
      have honall : ∀ Q ∈ a :: b :: rest, OnLineℤ (((0 : ℕ), H) : ℕ × ℕ) (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) Q := by
        intro Q hQ; exact hVline Q (by rw [hVeq]; exact hQ)
      rw [dropCollinear_collapse hAB a b rest honall]
      -- a = V.head = (0,H); (b :: rest).getLast = V.getLast = (n,0).
      have hae : a = (((0 : ℕ), H) : ℕ × ℕ) := by
        rw [← hVheadeq]
        have : V.head hVne = (a :: b :: rest).head (by simp) := by congr 1
        rw [this]; rfl
      have hle : (b :: rest).getLast (by simp) = (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) := by
        have h1 : (a :: b :: rest).getLast (by simp) = (b :: rest).getLast (by simp) :=
          List.getLast_cons (by simp)
        have h2 : V.getLast hVne = (a :: b :: rest).getLast (by simp) := by
          congr 1
        rw [← h1, ← h2, hVlasteq]
      rw [hae, hle]

/-- **`rootSide_eq_of_inCell`** — the classifier's selected side is `mkSide pr`.  From the hull
uniqueness lemma `npVertices = [(0,H),(n,0)]`, the side list is the single side
`[⟨0,n,H,0⟩] = [mkSide ((0,H),(n,0))]`, whose head is the root side. -/
theorem rootSide_eq_of_inCell {N n H : ℕ} (hn0 : 0 < n) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n)
    (hv0 : vOf p f 0 = H) (hHN : H < N)
    (hside : SideAbove p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) :
    B.rootSide p N hN f = some (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) := by
  rw [B.rootSide]
  rw [NewtonPolygon.npSides, npVertices_eq_selfloop p hn0 hN f hv0 hHN hside]
  -- zip [(0,H),(n,0)] [(n,0)] = [((0,H),(n,0))], mapped to the single Side.
  show (List.map (fun (pr : (ℕ × ℕ) × (ℕ × ℕ)) => (⟨pr.1.1, pr.2.1, pr.1.2, pr.2.2⟩ : NewtonPolygon.Side))
      (([((0 : ℕ), H), ((n : ℕ), (0 : ℕ))]).zip ([((0 : ℕ), H), ((n : ℕ), (0 : ℕ))]).tail)).head?
    = some (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))
  rfl

/-- **`rootResidual_eq_residualOf`** — the classifier's root residual is the order-1 side residual.
Once `rootSide = some (mkSide pr)`, `rootResidual` is the guarded `residualPoly (boxCoeffData
(mkSide pr) f) (mkSide pr)`, which is literally `residualOf f pr`; the `≤ n` guard never fires
because `(residualOf f pr).natDegree = sideDeg pr ≤ n` (`residual_facts`). -/
theorem rootResidual_eq_residualOf {N n H : ℕ} (hn0 : 0 < n) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n)
    {P : List (ℕ × ℕ)} (hP : MenuPath n N P)
    (hexact : ∀ q ∈ P, vOf p f q.1 = q.2)
    (hsingle : sidePairs P = [(((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))])
    (hv0 : vOf p f 0 = H) (hHN : H < N)
    (hside : SideAbove p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) :
    B.rootResidual p N hN f = residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) := by
  rw [B.rootResidual, rootSide_eq_of_inCell p hn0 hN f hv0 hHN hside]
  -- degree of the residual is sideDeg pr ≤ n, so the guard passes.
  have hpr : (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ sidePairs P := by
    rw [hsingle]; simp
  obtain ⟨_, hdeg⟩ := residual_facts p hN hP hexact hpr
  have hsd : sideDeg (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ≤ n := by
    have hdvd : sideDeg (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∣ n := by
      show Nat.gcd (H - 0) (n - 0) ∣ n
      have := Nat.gcd_dvd_right (H - 0) (n - 0)
      simpa using this
    exact Nat.le_of_dvd hn0 hdvd
  have hle : (residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))).natDegree ≤ n := by
    rw [hdeg]; exact hsd
  simp only [residualOf] at hle ⊢
  rw [if_pos hle]

/-! ### Squarefreeness of the residual from the all-μ=1 shape. -/

/-- If `polyShape R` (a multiset of `(degree, multiplicity)`) equals the assigned `shape` and every
assigned multiplicity is `1`, then every factor of `R` occurs with multiplicity `1` — i.e. the
`normalizedFactors` are `Nodup` — so `R` is squarefree (`R ≠ 0`). -/
theorem squarefree_of_polyShape {N n : ℕ} (f : QuotientBox.monicBox p N n)
    {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hne : residualOf p f pr ≠ 0)
    {shape : List (ℕ × ℕ)} (hshape : polyShape p (residualOf p f pr) = (shape : Multiset (ℕ × ℕ)))
    (hmu : ∀ q ∈ shape, q.2 = 1) :
    Squarefree (residualOf p f pr) := by
  letI := Classical.decEq (Polynomial (ZMod p))
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hne,
    Multiset.nodup_iff_count_le_one]
  intro ψ
  by_cases hmem : ψ ∈ UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr)
  · -- the pair (deg ψ, count ψ) ∈ polyShape = shape, so count ψ = 1.
    have hpair : (ψ.natDegree,
        (UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr)).count ψ)
        ∈ polyShape p (residualOf p f pr) := by
      unfold polyShape
      rw [Multiset.mem_map]
      exact ⟨ψ, by rw [Finset.mem_val, Multiset.mem_toFinset]; exact hmem, rfl⟩
    rw [hshape, Multiset.mem_coe] at hpair
    have hq := hmu _ hpair
    simp only at hq
    omega
  · rw [Multiset.count_eq_zero.mpr hmem]; omega

/-- **The factor-degree multiset equals `shape.map fst`.**  For a squarefree residual with
`polyShape = shape` and all μ=1, the canonical factor-degree multiset `normalizedFactors.map
natDegree` equals `shape.map Prod.fst`. -/
theorem factorDegrees_eq_shape {N n : ℕ} (f : QuotientBox.monicBox p N n)
    {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hne : residualOf p f pr ≠ 0)
    {shape : List (ℕ × ℕ)} (hshape : polyShape p (residualOf p f pr) = (shape : Multiset (ℕ × ℕ)))
    (hsq : Squarefree (residualOf p f pr)) :
    (UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr)).map Polynomial.natDegree
      = (shape.map Prod.fst : Multiset ℕ) := by
  letI := Classical.decEq (Polynomial (ZMod p))
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr)).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hne).mp hsq
  -- polyShape = normalizedFactors.map (fun ψ => (deg ψ, 1)) since μ=1 (nodup) and toFinset.val = itself
  have htf : (UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr)).toFinset.val
      = UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr) := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  have hpoly : polyShape p (residualOf p f pr)
      = (UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr)).map
          (fun ψ => (ψ.natDegree, 1)) := by
    unfold polyShape
    rw [htf]
    apply Multiset.map_congr rfl
    intro ψ hψ
    have hc : (UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr)).count ψ = 1 :=
      Multiset.count_eq_one_of_mem hnodup hψ
    rw [hc]
  -- shape (as multiset) = normalizedFactors.map (deg, 1); take fst
  rw [hpoly] at hshape
  -- map Prod.fst on both sides
  have := congrArg (Multiset.map Prod.fst) hshape
  rw [Multiset.map_map] at this
  simp only [Function.comp, Multiset.map_coe] at this
  rw [this]

/-- A `shapeLE`-sorted all-μ=1 shape has a `≤`-sorted degree list: `shape.map Prod.fst` is
`Pairwise (· ≤ ·)`. -/
theorem shape_fst_sorted {shape : List (ℕ × ℕ)} (hpw : shape.Pairwise shapeLE)
    (_hmu : ∀ q ∈ shape, q.2 = 1) : (shape.map Prod.fst).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  refine hpw.imp_of_mem ?_
  intro a b ha hb hab
  unfold shapeLE at hab
  omega

/-- The `≤`-sort of the degree multiset returns `shape.map Prod.fst` when the latter is already
`≤`-sorted. -/
theorem sort_shape_fst {shape : List (ℕ × ℕ)} (hpw : shape.Pairwise shapeLE)
    (hmu : ∀ q ∈ shape, q.2 = 1) :
    (shape.map Prod.fst : Multiset ℕ).sort (· ≤ ·) = shape.map Prod.fst := by
  have hsorted := shape_fst_sorted hpw hmu
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (by simpa using hsorted)

/-- The sum of the shape degrees equals the residual's degree (`polyShape_sum` with all μ=1). -/
theorem shape_fst_sum {N n : ℕ} (f : QuotientBox.monicBox p N n)
    {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hne : residualOf p f pr ≠ 0)
    {shape : List (ℕ × ℕ)} (hshape : polyShape p (residualOf p f pr) = (shape : Multiset (ℕ × ℕ)))
    (hmu : ∀ q ∈ shape, q.2 = 1) :
    (shape.map Prod.fst).sum = (residualOf p f pr).natDegree := by
  have hsum := polyShape_sum p hne
  rw [hshape, Multiset.map_coe, Multiset.sum_coe] at hsum
  rw [← hsum]
  -- Σ q.1 = Σ (q.1 * q.2) when all q.2 = 1 — pure list fact.
  have hlist : (shape.map Prod.fst).sum = (shape.map fun q => q.1 * q.2).sum := by
    clear hsum hshape hne
    induction shape with
    | nil => simp
    | cons a t ih =>
        rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
          ih (fun q hq => hmu q (List.mem_cons_of_mem a hq)), hmu a (by simp), Nat.mul_one]
  rw [hlist]

/-- The classifier's `factors.val` degree multiset equals `shape.map Prod.fst` (squarefree residual:
`factors.val = normalizedFactors` on the nose, and `factorDegrees_eq_shape`). -/
theorem classifierFactors_deg_eq_shape {N n : ℕ} (f : QuotientBox.monicBox p N n)
    {pr : (ℕ × ℕ) × (ℕ × ℕ)} (hne : residualOf p f pr ≠ 0)
    {shape : List (ℕ × ℕ)} (hshape : polyShape p (residualOf p f pr) = (shape : Multiset (ℕ × ℕ)))
    (hsq : Squarefree (residualOf p f pr)) :
    (Classical.choice (M4.factorize_any (residualOf p f pr))).factors.val.map Polynomial.natDegree
      = (↑(shape.map Prod.fst) : Multiset ℕ) := by
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr)).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hne).mp hsq
  have hfset := Order0.factors_eq_normalizedFactors_toFinset (residualOf p f pr) hne
    (Classical.choice (M4.factorize_any (residualOf p f pr)))
  -- `factors.val = normalizedFactors` (dedup of a nodup multiset), aligning the DecidableEq
  -- subsingleton flavor via `convert` (the leftover instance goals close by `Subsingleton.elim`).
  have hval : (Classical.choice (M4.factorize_any (residualOf p f pr))).factors.val
      = UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr) := by
    rw [hfset]
    -- `s.toFinset.val = s.dedup = s`; discharge the subsingleton `NormalizationMonoid` /
    -- `DecidableEq (Polynomial …)` instance mismatches via `Subsingleton.elim` inside `convert`.
    have key : ∀ (I : DecidableEq (Polynomial (ZMod p)))
        (t s : Multiset (Polynomial (ZMod p))),
        t = s → s.Nodup → (@Multiset.toFinset _ I t).val = s := by
      intro I t s hts hnd
      subst hts
      rw [Multiset.toFinset_val]; exact (@Multiset.dedup_eq_self _ I _).mpr hnd
    refine key _ _ (UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr)) ?_ hnodup
    -- the two `normalizedFactors` differ only in the subsingleton `DecidableEq (ZMod p)` baked deep
    -- in the `NormalizationMonoid`; a single `congr` on that instance closes it.
    have hde : (fun a b => Classical.propDecidable (a = b) : DecidableEq (ZMod p))
        = ZMod.decidableEq p := Subsingleton.elim _ _
    congr 1
    rw [hde]
  have hmapeq : (Classical.choice (M4.factorize_any (residualOf p f pr))).factors.val.map
        Polynomial.natDegree
      = (UniqueFactorizationMonoid.normalizedFactors (residualOf p f pr)).map Polynomial.natDegree :=
    congrArg (Multiset.map Polynomial.natDegree) hval
  rw [hmapeq, factorDegrees_eq_shape p f hne hshape hsq]

/-- **The classifier payload matches `Tselfloop`'s cells.**  On the single-side, all-μ=1 locus,
`encodeCells (fRootCtx f)` (the sorted per-factor childless payload with polygon `rootFace =
toSideFace (mkSide pr)`) equals `(Tselfloop n pr shape).cells`. -/
theorem encodeCells_fRootCtx_eq {N n H : ℕ} (hN : 0 < N)
    (f : QuotientBox.monicBox p N n)
    (hne : residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ≠ 0)
    (hrootRes : B.rootResidual p N hN f = residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))
    (hrootFace : B.rootFace p N hN f = M7.toSideFace (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))))
    {shape : List (ℕ × ℕ)}
    (hshape : polyShape p (residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) = (shape : Multiset (ℕ × ℕ)))
    (hpw : shape.Pairwise shapeLE) (hmu : ∀ q ∈ shape, q.2 = 1)
    (hsq : Squarefree (residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))) :
    M5.encodeCells (B.fRootCtx p N hN f)
      = (Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape).cells := by
  set pr := (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) with hpr
  -- fRootCtx.Rr = residualOf f pr
  have hRrEq : (B.fRootCtx p N hN f).Rr = residualOf p f pr := hrootRes
  -- the partition of `(residualOf f pr).natDegree` from the shape degrees.
  have hpos : ∀ {d : ℕ}, d ∈ (shape.map Prod.fst : Multiset ℕ) → 0 < d := by
    intro d hd
    rw [Multiset.mem_coe, List.mem_map] at hd
    obtain ⟨q, hq, rfl⟩ := hd
    exact (polyShape_pos p hne q (by rw [hshape]; exact hq)).1
  have hsum : ((shape.map Prod.fst : List ℕ) : Multiset ℕ).sum = (residualOf p f pr).natDegree := by
    rw [Multiset.sum_coe]
    exact shape_fst_sum p f hne hshape hmu
  set lam : Nat.Partition (residualOf p f pr).natDegree :=
    ⟨((shape.map Prod.fst : List ℕ) : Multiset ℕ), hpos, hsum⟩ with hlamdef
  -- factors degree list = lam.parts
  have hsqT : Squarefree (B.fRootCtx p N hN f).Rr := by rw [hRrEq]; exact hsq
  have hfac : (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors.val.map
        Polynomial.natDegree = lam.parts := by
    rw [hRrEq, hlamdef]
    exact classifierFactors_deg_eq_shape p f hne hshape hsq
  rw [Order0.encodeCells_of_squarefree (B.fRootCtx p N hN f) hsqT lam hfac]
  -- lam.parts.sort = shape.map fst (already sorted); δ = 1; Nr = toSideFace (mkSide pr)
  have hδ : (B.fRootCtx p N hN f).δ = 1 := rfl
  have hNr : (B.fRootCtx p N hN f).Nr = M7.toSideFace (mkSide pr) := hrootFace
  rw [hδ, hNr]
  have hsortEq : lam.parts.sort (· ≤ ·) = shape.map Prod.fst := sort_shape_fst hpw hmu
  rw [hsortEq]
  -- (shape.map fst).map (fun d => ⟨d,1,Nr,[]⟩) = shape.map (fun q => ⟨q.1,1,Nr,[]⟩)
  show (shape.map Prod.fst).map (fun d => (⟨d, 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell))
      = shape.map (fun q => (⟨q.1, 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell))
  rw [List.map_map]
  rfl

/-! ## STEP 1+4 — the fiber characterization `classify_eq_selfloop_iff`. -/

/-- **Forward direction (STEP 1).**  On the single-side, all-μ=1 `InCell` locus, the genuine
classifier collapses to the respelled `Tselfloop`.  Dispatch `classify → classifyAux` at `fRootCtx`
(`Order0.classifyAux_congr_ctx`); the residual `fRootCtx.Rr = residualOf f pr` is squarefree, so
every cell is childless (`Order0.classifyAux_of_childless`); the head is `(0, n, dr)` with
`dr = (residualOf f pr).natDegree = Σ shape.map fst`, and the payload is `Tselfloop`'s cells
(`encodeCells_fRootCtx_eq`). -/
theorem classify_eq_selfloop_of_inCell (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (P : List (ℕ × ℕ)) (hPmenu : MenuPath n N P) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (hsingle : sidePairs P = [pr])
    (shape : List (ℕ × ℕ)) (hSF : ShapesFor P [shape]) (hmu : ∀ q ∈ shape, q.2 = 1)
    (f : QuotientBox.monicBox p N n)
    (hInCell : InCell p f (mkCell n P [shape])) :
    B.classify p n N f = Tselfloop n pr shape := by
  -- Extract the menu data; `mkCell` injectivity pins the witness path/shapes to `(P, [shape])`.
  obtain ⟨P', sh', hP', hsh', heq, hM0⟩ := hInCell
  obtain ⟨rfl, rfl⟩ := mkCell_injective hPmenu hP' hSF hsh' heq
  have hP' : MenuPath n N P := hPmenu
  have hsh' : ShapesFor P [shape] := hSF
  have hM : Matches p f P [shape] := hM0
  -- Now hP' : MenuPath n N P, hsh' : ShapesFor P [shape], hM : Matches p f P [shape].
  obtain ⟨H, hPeq, hpreq, hH1, hH2⟩ := menuPath_single_side hP' hsingle
  subst hpreq
  subst hPeq
  -- vertex exactness and SideAbove from Matches
  have hexact : ∀ q ∈ ([((0:ℕ), H), ((n:ℕ), (0:ℕ))] : List (ℕ × ℕ)), vOf p f q.1 = q.2 := hM.1
  have hv0 : vOf p f 0 = H := hexact (0, H) (by simp)
  have hHN : H < N := by omega
  have hside : SideAbove p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) := by
    have hsa := matches_sideAbove p hM
    rw [hsingle] at hsa
    exact hsa (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (by simp)
  -- residual data
  have hRr : B.rootResidual p N hN f = residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) :=
    rootResidual_eq_residualOf p hn hN f hP' hexact hsingle hv0 hHN hside
  have hFace : B.rootFace p N hN f = M7.toSideFace (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) := by
    rw [B.rootFace, rootSide_eq_of_inCell p hn hN f hv0 hHN hside]
  -- polyShape and squarefree/nonzero
  have hpr_mem : (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ sidePairs
      ([((0:ℕ), H), ((n:ℕ), (0:ℕ))] : List (ℕ × ℕ)) := by rw [hsingle]; simp
  obtain ⟨hRne, _⟩ := residual_facts p hN hP' hexact hpr_mem
  have hshapeM : polyShape p (residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))
      = (shape : Multiset (ℕ × ℕ)) := by
    have hSM := hM.2
    -- Forall₂ (SideMatch) [shape] [pr]; extract the single SideMatch.
    rw [hsingle] at hSM
    cases hSM with
    | cons hhead _ => exact hhead.2
  have hpw : (shape : List (ℕ × ℕ)).Pairwise shapeLE := by
    have := hsh'
    rw [ShapesFor] at this
    rw [hsingle] at this
    cases this with
    | cons hh _ => exact (mem_shapesOfDegree_iff.mp hh).1
  have hsq : Squarefree (residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) :=
    squarefree_of_polyShape p f hRne hshapeM hmu
  -- Dispatch classify → classifyAux at fRootCtx, then childless collapse.
  have hRrT : (B.fRootCtx p N hN f).Rr = residualOf p f (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) := hRr
  have hsqT : Squarefree (B.fRootCtx p N hN f).Rr := by rw [hRrT]; exact hsq
  have hR0T : (B.fRootCtx p N hN f).Rr ≠ 0 := by rw [hRrT]; exact hRne
  have hdisp : B.classify p n N f
      = B.classifyAux p N n n f (B.fRootCtx p N hN f) (B.clusterSize_fRootCtx p N hN f) :=
    Order0.classifyAux_congr_ctx p N n n f (dif_pos hN)
      (B.clusterSize_rootCtx p N f) (B.clusterSize_fRootCtx p N hN f)
  rw [hdisp, Order0.classifyAux_of_childless p N n n f (B.fRootCtx p N hN f)
      (B.clusterSize_fRootCtx p N hN f)
      (Order0.cells_childless_of_squarefree (B.fRootCtx p N hN f) hsqT hR0T)]
  -- The collapsed shape `⟨[(0, n, dr)], encodeCells⟩` matches `Tselfloop`.
  have hhead : [((B.fRootCtx p N hN f).order, M5.clusterSize (B.fRootCtx p N hN f),
        (B.fRootCtx p N hN f).dr)]
      = [((0 : ℕ), n, (shape.map Prod.fst).sum)] := by
    have horder : (B.fRootCtx p N hN f).order = 0 := rfl
    have hcs : M5.clusterSize (B.fRootCtx p N hN f) = n := rfl
    have hdr : (B.fRootCtx p N hN f).dr = (shape.map Prod.fst).sum := by
      show (B.rootResidual p N hN f).natDegree = (shape.map Prod.fst).sum
      rw [hRr, shape_fst_sum p f hRne hshapeM hmu]
    rw [horder, hcs, hdr]
  have hcells : M5.encodeCells (B.fRootCtx p N hN f)
      = (Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape).cells :=
    encodeCells_fRootCtx_eq p hN f hRne hRr hFace hshapeM hpw hmu hsq
  -- assemble the ClusterShape.
  show (⟨[((B.fRootCtx p N hN f).order, M5.clusterSize (B.fRootCtx p N hN f),
      (B.fRootCtx p N hN f).dr)], M5.encodeCells (B.fRootCtx p N hN f)⟩ : ClusterShape)
    = Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape
  rw [hcells, hhead]
  rfl

/-! ### STEP 4 building blocks — reading vertex-exactness back off the hull. -/

/-- If the first Newton side is `mkSide pr` for a FULL-WIDTH self-loop `pr = ((0,H),(n,0))`, then
`npVertices = [(0,H),(n,0)]`: the first side reaches abscissa `n` (the maximal on-hull abscissa,
since all support indices are `≤ n`), so there is no further vertex. -/
theorem npVertices_of_rootSide {N n H : ℕ} (_hn0 : 0 < n) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n)
    (hrs : B.rootSide p N hN f = some (mkSide (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))) :
    NewtonPolygon.npVertices (B.boxValSupport p N f) (B.boxValSupport_nonempty p N hN f)
      = [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))] := by
  set S := B.boxValSupport p N f with hSdef
  set hS := B.boxValSupport_nonempty p N hN f with hShyp
  -- rootSide = npSides.head? = some (mkSide pr) forces npVertices = (0,H)::(n,0)::rest.
  rw [B.rootSide] at hrs
  -- unfold npSides.head?
  have hverts : ∃ rest, NewtonPolygon.npVertices S hS
      = ((0 : ℕ), H) :: ((n : ℕ), (0 : ℕ)) :: rest := by
    unfold NewtonPolygon.npSides at hrs
    -- head? of a map/zip; a `some` forces the first two vertices.
    cases hv : NewtonPolygon.npVertices S hS with
    | nil => rw [hv] at hrs; simp at hrs
    | cons a t =>
        cases t with
        | nil => rw [hv] at hrs; simp at hrs
        | cons b rest =>
            rw [hv] at hrs
            simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.head?_cons,
              Option.some.injEq] at hrs
            -- hrs : ⟨a.1, b.1, a.2, b.2⟩ = mkSide pr
            have ha : a = (((0 : ℕ), H) : ℕ × ℕ) := by
              have h1 : a.1 = 0 := congrArg NewtonPolygon.Side.i₀ hrs
              have h2 : a.2 = H := congrArg NewtonPolygon.Side.v₀ hrs
              exact Prod.ext h1 h2
            have hb : b = (((n : ℕ), (0 : ℕ)) : ℕ × ℕ) := by
              have h1 : b.1 = n := congrArg NewtonPolygon.Side.j₀ hrs
              have h2 : b.2 = 0 := congrArg NewtonPolygon.Side.v₁ hrs
              exact Prod.ext h1 h2
            exact ⟨rest, by rw [ha, hb]⟩
  obtain ⟨rest, hV⟩ := hverts
  -- (n,0) is on hull with abscissa n = max; strictly-increasing abscissae force rest = [].
  rcases rest.eq_nil_or_concat with hrest | ⟨l, c, hrest⟩
  · rw [hV, hrest]
  · exfalso
    -- the last element c has abscissa > n, impossible (all on-hull abscissae ≤ n).
    have hsorted : ((NewtonPolygon.npVertices S hS).map Prod.fst).Pairwise (· < ·) :=
      NewtonPolygon.npVertices_sorted S hS
    rw [hV, hrest] at hsorted
    -- abscissae: 0 < n < ... < c.1 ; but c ∈ npVertices ⊆ on-hull ⊆ support, so c.1 ≤ n.
    have hcmem : c ∈ NewtonPolygon.npVertices S hS := by
      rw [hV, hrest]; simp
    have hcOnHull : (c.2 : ℚ) = NewtonPolygon.npHeight S hS (c.1 : ℚ) :=
      NewtonPolygon.npVertices_on_hull S hS hcmem
    -- c ∈ npVertices ⊆ npVerticesFull; via hullAbscissae membership, c.1 is a support abscissa ≤ n.
    have hcabs : c.1 ∈ (NewtonPolygon.npVertices S hS).map Prod.fst := by
      rw [List.mem_map]; exact ⟨c, hcmem, rfl⟩
    have hcfull : c ∈ NewtonPolygon.npVerticesFull S hS :=
      (NewtonPolygon.dropCollinear_sublist _).subset hcmem
    have hc1abs : c.1 ∈ NewtonPolygon.hullAbscissae S hS := by
      rw [← NewtonPolygon.npVerticesFull_fst S hS, List.mem_map]; exact ⟨c, hcfull, rfl⟩
    rw [NewtonPolygon.mem_hullAbscissae_iff] at hc1abs
    obtain ⟨v, hvmem, _⟩ := hc1abs
    obtain ⟨_, hvne⟩ := boxValSupport_eq_dot p f hvmem
    have hcle : c.1 ≤ n := support_le_deg p f (Polynomial.mem_support_iff.mpr hvne)
    -- but sorted: n < c.1 (n is second, c is after the concat)
    simp only [List.map_cons] at hsorted
    -- hsorted : Pairwise (· < ·) [0, n] ++ (map fst l) ++ [c.1]
    have hnc : n < c.1 := by
      -- n is at index 1; c.1 is the very last; pairwise gives n < c.1
      have := hsorted
      rw [List.pairwise_cons] at this
      have h2 := this.2
      rw [List.pairwise_cons] at h2
      exact h2.1 c.1 (by simp)
    omega

/-- Every genuine Newton vertex is a support dot of `S = boxValSupport f`. -/
theorem mem_S_of_mem_npVertices {N n : ℕ} (f : QuotientBox.monicBox p N n)
    (hS : (B.boxValSupport p N f).Nonempty) {Q : ℕ × ℕ}
    (hQ : Q ∈ NewtonPolygon.npVertices (B.boxValSupport p N f) hS) :
    Q ∈ B.boxValSupport p N f := by
  set S := B.boxValSupport p N f
  have hfull : Q ∈ NewtonPolygon.npVerticesFull S hS :=
    (NewtonPolygon.dropCollinear_sublist _).subset hQ
  have habs : Q.1 ∈ NewtonPolygon.hullAbscissae S hS := by
    rw [← NewtonPolygon.npVerticesFull_fst S hS, List.mem_map]; exact ⟨Q, hfull, rfl⟩
  rw [NewtonPolygon.mem_hullAbscissae_iff] at habs
  obtain ⟨v, hvmem, hvon⟩ := habs
  have hQon : (Q.2 : ℚ) = NewtonPolygon.npHeight S hS (Q.1 : ℚ) :=
    NewtonPolygon.npVerticesFull_on_hull S hS hfull
  have hQ2 : Q.2 = v := by
    have : (Q.2 : ℚ) = (v : ℚ) := by rw [hQon, ← hvon]
    exact_mod_cast this
  have : Q = (Q.1, v) := by rw [← hQ2]
  rw [this]; exact hvmem

end HullUniqueness

/-! ## STEP 4 — the backward direction (OPEN, precise obstacle).

The forward direction `classify_eq_selfloop_of_inCell` is LANDED (above).  The full fiber
characterization is the iff

```
classify_eq_selfloop_iff (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (P : List (ℕ × ℕ)) (hPmenu : MenuPath n N P) (pr : (ℕ×ℕ)×(ℕ×ℕ)) (hsingle : sidePairs P = [pr])
    (shape : List (ℕ × ℕ)) (hSF : ShapesFor P [shape]) (hmu : ∀ q ∈ shape, q.2 = 1) (hne : shape ≠ [])
    (f : QuotientBox.monicBox p N n) :
    B.classify p n N f = Tselfloop n pr shape ↔ InCell p f (mkCell n P [shape])
```

The `←` (backward) direction is the ONLY remaining obligation.  Its INVERSE-of-STEP-3 skeleton is
partly LANDED here:

* `npVertices_of_rootSide` (LANDED) — from `rootSide = some (mkSide pr)` (full-width self-loop
  `pr = ((0,H),(n,0))`) recover `npVertices (boxValSupport f) = [(0,H),(n,0)]` (the first side spans
  the whole width `[0,n]`, and `n` is the maximal on-hull abscissa, so there is no further vertex).
* `mem_S_of_mem_npVertices` (LANDED) — every genuine Newton vertex is a support dot; combined with
  `boxValSupport_eq_dot` this reads the vertex-exactness `vOf f 0 = H`, `vOf f n = 0` straight off
  the two on-hull vertices.

Two pieces remain to assemble the full `←`:

1.  MISSING LEMMA A (`rootFace`/`rootSide` inversion): from `classify f = Tselfloop n pr shape`
    (with `shape ≠ []`) read `rootFace p N hN f = toSideFace (mkSide pr)` off the emitted per-cell
    polygon, then invert `toSideFace` to `rootSide p N hN f = some (mkSide pr)` (a
    `toSideFace`-injectivity fact: `width = j₀−i₀`, column-0 height `= v₀`, slope from the last
    column — TRUE, unformalized).  Then `npVertices_of_rootSide` fires.
2.  MISSING LEMMA B (`SideAbove` from the single-vertex hull): with `npVertices = [(0,H),(n,0)]`,
    the lower hull IS the single chord, so `npHeight = chord` on `[0,n]`; since `npHeight ≤ vOf`
    (minorant `npHeight_le`) this gives `SideAbove f pr`.  The missing sub-step is the
    npVertices→npHeight direction (`npHeight` equals the interpolation of its two vertices), the
    reverse of the forward `npHeight_eq_chord`; the rest (`Matches` ⟹ `InCell` via
    `inCell_mkCell_iff`, and the residual shape via `classify`'s payload) is mechanical.

Both are TRUE and reuse the STEP-3 infrastructure in the opposite direction.  The forward direction
(`classify_eq_selfloop_of_inCell`) and all of STEP 0/2/3 are proved and axiom-clean. -/

end LeanUrat.OM.ClassifierBridgeFiber
