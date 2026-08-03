/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.CU2tKp0
import LeanUrat.Scaffold.HDischarge.H6.TerminalRead

/-!
# Scaffold/DictIII/BasePolyLength — `BasePolygonLengthLaw` PROVED

Unit: synthesis pass-6 F2 ("BasePolygonLengthLaw: a genuine self-contained
unit"), the named open numerical row of `CU2tKp0.lean` — the OM base length
law at the corpus carrier:

For monic `f : ℤ_[p][X]` with `f(0) ≠ 0` and `p ∣ f(0)` (the decided,
finite-slope, saturated perimeter — both legs countermodel-forced by
`Kp0GateA`/`Kp0GateB`):
* (i) NONDEGENERACY — every principal side of the corpus base read has
  `1 ≤ e` and `1 ≤ ℓ`;
* (ii) LENGTH TIE — the total horizontal length `Σ e·ℓ` of `principalData f`
  equals the exact multiplicity `j₀ = ord_X(f̄)` of `X` in the mod-`p`
  reduction, with `1 ≤ j₀`.

PROOF ROUTE (the docstring route, executed).  Everything is measured against
the PROVED convex-lower-hull kernels of `OM/NewtonPolygon.lean`
(`npHeight_le`, `npHeight_convexOn`, `npVertices_sorted`,
`npVertices_on_hull`, `dropCollinear_cons_head`) and the support kernel
`M2.valSupport_facts`:

1. **Height sign law.**  `npHeight ≥ 0` always (horizontal line through a
   lowest dot); `npHeight = 0` on `[j₀, n]` (two height-0 anchor dots +
   convexity); `npHeight > 0` strictly left of `j₀` (NEW: the flattest
   descending chord into `(j₀, 0)` from the left-dot finset is a valid
   supporting line, positive left of `j₀`).  Here `j₀` is the least index
   with a unit coefficient — `(f̄).natTrailingDegree` — and `n = natDegree`.
2. **Endpoint pins.**  The hull is anchored at `(0, v₀)` (leftmost dot on
   the hull, NEW: steepest-chord valid line) and `(n, 0)`
   (`valSupport_facts`, monic); `dropCollinear` keeps head AND last (NEW:
   `dropCollinear_getLast?`).
3. **No vertex side straddles `j₀`** (NEW, the negative-prefix mechanism):
   `dropCollinear` only merges genuinely collinear dots — every full-vertex
   between two surviving consecutive vertices is collinear with them
   (`dropCollinear_between`); `(j₀, 0)` is a kink of the hull (height drop
   to 0 with the left height ≥ 1), so no surviving consecutive pair jumps
   over `j₀`.
4. **Sign ⟺ position.**  A vertex side has negative slope iff its left
   abscissa is `< j₀` (height sign law + `npHeight_convexOn`
   `slope_mono_adjacent`).
5. **Negative-prefix telescoping** (NEW): summing lengths of the filtered
   consecutive-pair list telescopes to `j₀ − 0`.
6. **Per-side arithmetic**: `e ∣ length` (`Rat.den_dvd` on the slope in
   lowest terms), so `e·ℓ = e·(length/e) = length` and `1 ≤ ℓ`.

The abstract §1 core `npSides_neg_length_sum` is stated over a bare support
`Finset` — exactly the negative-prefix hull machinery the OL5-adjacent work
(and the banked `npVertices_stable_of_hull_preserved` sorry) sits next to.

Fence (unchanged from the row): the −∞ corner (`f(0) = 0`) stays a
separately-priced open leg — the perimeter here excludes it.

Consumer fired: `terminalPolySem_kp0_unconditional` below — the first
UNCONDITIONAL `TerminalPolySem` supplier at a 𝐇°-keyed k′ = 0 seam
(`terminalPolySem_kp0_of_law` + this law; no per-instance polygon
computation consumed).

Unit record: `lean/notes/openmath/BPLL_2026-08-08.md`.
-/

namespace LeanUrat.Scaffold.DictIII

namespace BPLL

open Polynomial LeanUrat.OM LeanUrat.OM.NewtonPolygon

/-! ## §0 — Generic list kernels (abscissa-sorted point lists) -/

/-- Consecutive pairs of a strictly-abscissa-sorted point list increase. -/
lemma zip_fst_lt : ∀ (V : List (ℕ × ℕ)),
    (V.map Prod.fst).Pairwise (· < ·) →
    ∀ pr ∈ V.zip V.tail, pr.1.1 < pr.2.1
  | [], _, pr, hpr => by simp at hpr
  | [_], _, pr, hpr => by simp at hpr
  | a :: b :: t, hs, pr, hpr => by
      rw [List.map_cons, List.pairwise_cons] at hs
      obtain ⟨ha, hs'⟩ := hs
      rw [show (a :: b :: t).tail = b :: t from rfl, List.zip_cons_cons,
        List.mem_cons] at hpr
      rcases hpr with rfl | hpr
      · exact ha b.1 (by simp)
      · exact zip_fst_lt (b :: t) hs' pr hpr

/-- A strictly-sorted list containing `0` starts with `0`. -/
lemma sorted_head_zero {l : List ℕ} (hs : l.Pairwise (· < ·))
    (h0 : (0 : ℕ) ∈ l) : ∃ t, l = 0 :: t := by
  cases l with
  | nil => simp at h0
  | cons a t =>
      rcases List.mem_cons.mp h0 with h | h
      · exact ⟨t, by rw [← h]⟩
      · exact absurd ((List.pairwise_cons.mp hs).1 0 h) (by omega)

/-- A strictly-sorted list containing an upper bound `n` ends at `n`. -/
lemma sorted_getLast?_eq {l : List ℕ} (hs : l.Pairwise (· < ·)) {n : ℕ}
    (hn : n ∈ l) (hub : ∀ x ∈ l, x ≤ n) : l.getLast? = some n := by
  induction l with
  | nil => simp at hn
  | cons a t ih =>
      cases t with
      | nil =>
          rw [List.mem_singleton] at hn
          simp [hn]
      | cons b t' =>
          rw [List.getLast?_cons_cons]
          have hs' := (List.pairwise_cons.mp hs).2
          have hmem : n ∈ b :: t' := by
            rcases List.mem_cons.mp hn with rfl | h
            · have hab := (List.pairwise_cons.mp hs).1 b (by simp)
              have hb := hub b (by simp [List.mem_cons])
              exact absurd hab (by omega)
            · exact h
          exact ih hs' hmem (fun x hx => hub x (List.mem_cons_of_mem a hx))

/-- Membership from `getLast?` (defensive local helper). -/
lemma mem_of_getLast?_eq : ∀ {l : List (ℕ × ℕ)} {a : ℕ × ℕ},
    l.getLast? = some a → a ∈ l
  | [], _, h => by simp at h
  | [b], a, h => by
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      simp [h]
  | b :: c :: t, a, h => by
      rw [List.getLast?_cons_cons] at h
      exact List.mem_cons_of_mem _ (mem_of_getLast?_eq h)

/-- `dropCollinear` keeps the last entry. -/
lemma dropCollinear_getLast? : ∀ (l : List (ℕ × ℕ)),
    (dropCollinear l).getLast? = l.getLast?
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: rest => by
      obtain ⟨u, hu, -⟩ := dropCollinear_cons_head b (c :: rest)
      have ih : (dropCollinear (b :: c :: rest)).getLast?
          = (b :: c :: rest).getLast? := dropCollinear_getLast? (b :: c :: rest)
      rw [dropCollinear_cons3, hu]
      rw [hu] at ih
      cases u with
      | nil =>
          show (a :: b :: ([] : List (ℕ × ℕ))).getLast? = (a :: b :: c :: rest).getLast?
          simp only [List.getLast?_cons_cons] at ih ⊢
          exact ih
      | cons c' u' =>
          by_cases hcol : collinear₃ a b c'
          · show (if collinear₃ a b c' = true then a :: c' :: u'
                else a :: b :: c' :: u').getLast? = (a :: b :: c :: rest).getLast?
            rw [if_pos hcol]
            simp only [List.getLast?_cons_cons] at ih ⊢
            exact ih
          · show (if collinear₃ a b c' = true then a :: c' :: u'
                else a :: b :: c' :: u').getLast? = (a :: b :: c :: rest).getLast?
            rw [if_neg hcol]
            simp only [List.getLast?_cons_cons] at ih ⊢
            exact ih

/-- Integer cross-product collinearity is transitive along increasing
    abscissae: if `b` lies on chord `a–c` and `z` lies on chord `b–c`, then
    `z` lies on chord `a–c`.  (Identity pre-verified numerically:
    `G·(c₁−b₁) = (c₁−z₁)·e₁ + (c₁−a₁)·e₂`.) -/
lemma collinear₃_trans {a b z c : ℕ × ℕ} (hbc : b.1 < c.1)
    (h₁ : collinear₃ a b c = true) (h₂ : collinear₃ b z c = true) :
    collinear₃ a z c = true := by
  simp only [collinear₃, beq_iff_eq] at h₁ h₂ ⊢
  have hcb : ((c.1 : ℤ) - (b.1 : ℤ)) ≠ 0 := by
    have : (b.1 : ℤ) < (c.1 : ℤ) := by exact_mod_cast hbc
    omega
  refine mul_right_cancel₀ hcb ?_
  linear_combination ((c.1 : ℤ) - (z.1 : ℤ)) * h₁ + ((c.1 : ℤ) - (a.1 : ℤ)) * h₂

/-- **The `dropCollinear` merge invariant** (the straddle killer): on a
    strictly-abscissa-sorted list, every ORIGINAL point whose abscissa lies
    strictly between two CONSECUTIVE surviving points is collinear with
    them — `dropCollinear` only ever merges collinear runs. -/
lemma dropCollinear_between : ∀ (l : List (ℕ × ℕ)),
    (l.map Prod.fst).Pairwise (· < ·) →
    ∀ pr ∈ (dropCollinear l).zip (dropCollinear l).tail,
    ∀ z ∈ l, pr.1.1 < z.1 → z.1 < pr.2.1 → collinear₃ pr.1 z pr.2 = true
  | [], _, pr, hpr, _, _, _, _ => by simp [dropCollinear] at hpr
  | [a], _, pr, hpr, _, _, _, _ => by simp [dropCollinear] at hpr
  | [a, b], hs, pr, hpr, z, hz, h1, h2 => by
      have hpr' : pr ∈ (a :: b :: ([] : List (ℕ × ℕ))).zip (b :: []) := hpr
      rw [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hpr'
      subst hpr'
      have h1' : a.1 < z.1 := h1
      have h2' : z.1 < b.1 := h2
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact absurd h1' (lt_irrefl _)
      · rw [List.mem_singleton] at hz'
        subst hz'
        exact absurd h2' (lt_irrefl _)
  | a :: b :: c :: rest, hs, pr, hpr, z, hz, h1, h2 => by
      obtain ⟨u, hu, husub⟩ := dropCollinear_cons_head b (c :: rest)
      have hs' : ((b :: c :: rest).map Prod.fst).Pairwise (· < ·) := by
        rw [List.map_cons, List.pairwise_cons] at hs
        exact hs.2
      have hafst : ∀ x ∈ (b :: c :: rest).map Prod.fst, a.1 < x := by
        rw [List.map_cons, List.pairwise_cons] at hs
        exact hs.1
      have hbfst : ∀ x ∈ (c :: rest).map Prod.fst, b.1 < x := by
        rw [List.map_cons, List.pairwise_cons] at hs'
        exact hs'.1
      have ih := dropCollinear_between (b :: c :: rest) hs'
      rw [hu] at ih
      have hdctmem : ∀ P ∈ b :: u, P ∈ b :: c :: rest := by
        intro P hP
        rcases List.mem_cons.mp hP with rfl | hP'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (husub.subset hP')
      rw [dropCollinear_cons3, hu] at hpr
      cases u with
      | nil =>
          have hpr2 : pr ∈ (a :: b :: ([] : List (ℕ × ℕ))).zip
              ((a :: b :: ([] : List (ℕ × ℕ))).tail) := hpr
          rw [show (a :: b :: ([] : List (ℕ × ℕ))).tail = b :: [] from rfl,
            List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hpr2
          subst hpr2
          have h1' : a.1 < z.1 := h1
          have h2' : z.1 < b.1 := h2
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact absurd h1' (lt_irrefl _)
          · rcases List.mem_cons.mp hz' with rfl | hz''
            · exact absurd h2' (lt_irrefl _)
            · have := hbfst z.1 (List.mem_map_of_mem hz'')
              exact absurd h2' (by omega)
      | cons c' u' =>
          have hbc' : b.1 < c'.1 := hbfst c'.1
            (List.mem_map_of_mem (husub.subset List.mem_cons_self))
          have hpr2 : pr ∈ ((if collinear₃ a b c' then a :: c' :: u'
              else a :: b :: c' :: u').zip
                ((if collinear₃ a b c' then a :: c' :: u'
                  else a :: b :: c' :: u').tail)) := hpr
          by_cases hcol : collinear₃ a b c'
          · rw [if_pos hcol] at hpr2
            rw [show (a :: c' :: u').tail = c' :: u' from rfl,
              List.zip_cons_cons, List.mem_cons] at hpr2
            rcases hpr2 with rfl | hpr3
            · -- pr = (a, c')
              rcases List.mem_cons.mp hz with rfl | hz'
              · exact absurd h1 (lt_irrefl _)
              · rcases List.mem_cons.mp hz' with rfl | hz''
                · exact hcol
                · have hbz : b.1 < z.1 := hbfst z.1 (List.mem_map_of_mem hz'')
                  have hcolz : collinear₃ b z c' = true := by
                    apply ih (b, c')
                    · rw [show (b :: c' :: u').tail = c' :: u' from rfl,
                        List.zip_cons_cons]
                      exact List.mem_cons_self
                    · exact hz'
                    · exact hbz
                    · exact h2
                  exact collinear₃_trans hbc' hcol hcolz
            · -- pr among the deeper dct pairs
              have hprdct : pr ∈ (b :: c' :: u').zip ((b :: c' :: u').tail) := by
                rw [show (b :: c' :: u').tail = c' :: u' from rfl,
                  List.zip_cons_cons]
                exact List.mem_cons_of_mem _ hpr3
              rcases List.mem_cons.mp hz with rfl | hz'
              · have hpr1 : pr.1 ∈ c' :: u' := (List.of_mem_zip hpr3).1
                have hmem : pr.1 ∈ b :: c :: rest :=
                  hdctmem pr.1 (List.mem_cons_of_mem _ hpr1)
                have := hafst pr.1.1 (List.mem_map_of_mem hmem)
                exact absurd h1 (by omega)
              · exact ih pr hprdct z hz' h1 h2
          · rw [if_neg hcol] at hpr2
            rw [show (a :: b :: c' :: u').tail = b :: c' :: u' from rfl,
              List.zip_cons_cons, List.mem_cons] at hpr2
            rcases hpr2 with rfl | hpr3
            · -- pr = (a, b): nothing fits strictly between
              have h1' : a.1 < z.1 := h1
              have h2' : z.1 < b.1 := h2
              rcases List.mem_cons.mp hz with rfl | hz'
              · exact absurd h1' (lt_irrefl _)
              · rcases List.mem_cons.mp hz' with rfl | hz''
                · exact absurd h2' (lt_irrefl _)
                · have := hbfst z.1 (List.mem_map_of_mem hz'')
                  exact absurd h2' (by omega)
            · have hprdct : pr ∈ (b :: c' :: u').zip ((b :: c' :: u').tail) := by
                rw [show (b :: c' :: u').tail = c' :: u' from rfl]
                exact hpr3
              rcases List.mem_cons.mp hz with rfl | hz'
              · have hpr1 : pr.1 ∈ b :: c' :: u' := (List.of_mem_zip hprdct).1
                have hmem : pr.1 ∈ b :: c :: rest := hdctmem pr.1 hpr1
                have := hafst pr.1.1 (List.mem_map_of_mem hmem)
                exact absurd h1 (by omega)
              · exact ih pr hprdct z hz' h1 h2

/-- **Negative-prefix telescoping.**  Over a strictly-sorted vertex list
    starting at `P`, if consecutive pairs never jump over `j` (left `< j`
    forces right `≤ j`), `P.1 ≤ j`, and some vertex reaches `≥ j`, then the
    total horizontal length of the pairs with left abscissa `< j`
    telescopes to `j − P.1`. -/
lemma telescope_sum (j : ℕ) : ∀ (V : List (ℕ × ℕ)) (P : ℕ × ℕ),
    (((P :: V).map Prod.fst).Pairwise (· < ·)) →
    (∀ pr ∈ (P :: V).zip V, pr.1.1 < j → pr.2.1 ≤ j) →
    P.1 ≤ j → (∃ Q ∈ P :: V, j ≤ Q.1) →
    ((((P :: V).zip V).filter (fun pr => decide (pr.1.1 < j))).map
      (fun pr => pr.2.1 - pr.1.1)).sum = j - P.1
  | [], P, _, _, hPle, hex => by
      obtain ⟨Q, hQ, hjQ⟩ := hex
      rw [List.mem_singleton] at hQ
      subst hQ
      simp only [List.zip_nil_right, List.filter_nil, List.map_nil, List.sum_nil]
      omega
  | R :: rest, P, hs, hnj, hPle, hex => by
      have hs' : ((R :: rest).map Prod.fst).Pairwise (· < ·) := by
        rw [List.map_cons, List.pairwise_cons] at hs
        exact hs.2
      have hPfst : ∀ x ∈ (R :: rest).map Prod.fst, P.1 < x := by
        rw [List.map_cons, List.pairwise_cons] at hs
        exact hs.1
      rw [show ((P :: R :: rest).zip (R :: rest))
          = (P, R) :: ((R :: rest).zip rest) from rfl]
      by_cases hPj : P.1 < j
      · have hRle : R.1 ≤ j := hnj (P, R)
          (by rw [show ((P :: R :: rest).zip (R :: rest))
              = (P, R) :: ((R :: rest).zip rest) from rfl]
              exact List.mem_cons_self) hPj
        have hPR : P.1 < R.1 := hPfst R.1 (List.mem_map_of_mem List.mem_cons_self)
        have hnj' : ∀ pr ∈ (R :: rest).zip rest, pr.1.1 < j → pr.2.1 ≤ j := by
          intro pr hpr
          exact hnj pr (by
            rw [show ((P :: R :: rest).zip (R :: rest))
                = (P, R) :: ((R :: rest).zip rest) from rfl]
            exact List.mem_cons_of_mem _ hpr)
        have hex' : ∃ Q ∈ R :: rest, j ≤ Q.1 := by
          obtain ⟨Q, hQ, hjQ⟩ := hex
          rcases List.mem_cons.mp hQ with rfl | hQ'
          · exact absurd hjQ (by omega)
          · exact ⟨Q, hQ', hjQ⟩
        have ih := telescope_sum j rest R hs' hnj' hRle hex'
        rw [List.filter_cons_of_pos (by simpa using hPj), List.map_cons,
          List.sum_cons, ih]
        show R.1 - P.1 + (j - R.1) = j - P.1
        omega
      · have hPeq : P.1 = j := le_antisymm hPle (not_lt.mp hPj)
        rw [List.filter_cons_of_neg (by simpa using hPj)]
        have hnil : ((R :: rest).zip rest).filter
            (fun pr => decide (pr.1.1 < j)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro pr hpr
          have hpr1 : pr.1 ∈ R :: rest := (List.of_mem_zip hpr).1
          have := hPfst pr.1.1 (List.mem_map_of_mem hpr1)
          simp only [decide_eq_true_eq]
          omega
        rw [hnil]
        simp only [List.map_nil, List.sum_nil]
        omega

/-! ## §1 — Hull height sign kernels (abstract support `Finset`) -/

variable (S : Finset (ℕ × ℕ))

/-- The lower Newton hull is everywhere nonnegative (heights are naturals:
    the horizontal valid line through a lowest dot minorizes it). -/
lemma npHeight_nonneg (hS : S.Nonempty) (x : ℚ) : 0 ≤ npHeight S hS x := by
  classical
  obtain ⟨P₀, hP₀mem, hP₀min⟩ := S.exists_min_image (fun Q => Q.2) hS
  have hmem : (P₀, P₀) ∈ validLines S := by
    rw [validLines, Finset.mem_filter]
    exact ⟨Finset.mem_product.2 ⟨hP₀mem, hP₀mem⟩, fun Q hQ =>
      (pairLine_diag_const P₀.1 P₀.2 _).trans_le (by exact_mod_cast hP₀min Q hQ)⟩
  calc (0 : ℚ) ≤ (P₀.2 : ℚ) := Nat.cast_nonneg _
    _ = pairLine P₀ P₀ x := by
        rw [show P₀ = (P₀.1, P₀.2) from rfl, pairLine_diag_const]
    _ ≤ npHeight S hS x :=
        Finset.le_sup' (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 x) hmem

/-- Between two height-0 support dots the hull is identically 0. -/
lemma npHeight_eq_zero_on (hS : S.Nonempty) {a b : ℕ}
    (ha : (a, 0) ∈ S) (hb : (b, 0) ∈ S) {x : ℚ}
    (hax : (a : ℚ) ≤ x) (hxb : x ≤ (b : ℚ)) : npHeight S hS x = 0 := by
  refine le_antisymm ?_ (npHeight_nonneg S hS x)
  have hab : (a : ℚ) ≤ (b : ℚ) := le_trans hax hxb
  have hconv := npHeight_convexOn S hS (b : ℚ)
  have haIcc : (a : ℚ) ∈ Set.Icc (0 : ℚ) (b : ℚ) := ⟨Nat.cast_nonneg _, hab⟩
  have hbIcc : (b : ℚ) ∈ Set.Icc (0 : ℚ) (b : ℚ) := ⟨Nat.cast_nonneg _, le_refl _⟩
  have hseg : x ∈ segment ℚ (a : ℚ) (b : ℚ) := by
    rw [segment_eq_Icc hab]
    exact ⟨hax, hxb⟩
  have hbound := hconv.le_on_segment haIcc hbIcc hseg
  have hga : npHeight S hS (a : ℚ) ≤ 0 := by
    have := npHeight_le S hS ha
    simpa using this
  have hgb : npHeight S hS (b : ℚ) ≤ 0 := by
    have := npHeight_le S hS hb
    simpa using this
  exact le_trans hbound (max_le hga hgb)

/-- `pairLine` re-based at its RIGHT anchor (needs distinct abscissae). -/
lemma pairLine_right_form (P R : ℕ × ℕ) (h : (P.1 : ℚ) ≠ (R.1 : ℚ)) (x : ℚ) :
    pairLine P R x = (R.2 : ℚ) + pairSlope P R * (x - (R.1 : ℚ)) := by
  have h2 := pairLine_right P R h
  simp only [pairLine] at h2 ⊢
  linear_combination h2

/-- **Strict positivity left of a saturated zero-anchor** (the NEW hull
    geometry): if `(j, 0) ∈ S`, every dot strictly left of `j` has height
    `≥ 1`, and at least one such dot exists, then the hull is strictly
    positive at every abscissa `< j`.  Witness: the flattest descending
    chord into `(j, 0)` from the left-dot finset is a valid supporting
    line. -/
lemma npHeight_pos_left (hS : S.Nonempty) {j : ℕ} (hj : (j, 0) ∈ S)
    (hleft : ∀ P ∈ S, P.1 < j → 1 ≤ P.2)
    (hex : ∃ P ∈ S, P.1 < j) :
    ∀ x : ℚ, x < (j : ℚ) → 0 < npHeight S hS x := by
  classical
  obtain ⟨P₁, hP₁S, hP₁j⟩ := hex
  have hTne : (S.filter (fun P => P.1 < j)).Nonempty :=
    ⟨P₁, Finset.mem_filter.2 ⟨hP₁S, hP₁j⟩⟩
  obtain ⟨Pm, hPmT, hPmmax⟩ :=
    (S.filter (fun P => P.1 < j)).exists_max_image
      (fun P => pairSlope P (j, 0)) hTne
  have hPmS : Pm ∈ S := (Finset.mem_filter.mp hPmT).1
  have hPmj : Pm.1 < j := by
    have := (Finset.mem_filter.mp hPmT).2
    simpa using this
  have hPmv : 1 ≤ Pm.2 := hleft Pm hPmS hPmj
  have hjq : (Pm.1 : ℚ) < (j : ℚ) := by exact_mod_cast hPmj
  have hne : (Pm.1 : ℚ) ≠ (((j, 0) : ℕ × ℕ).1 : ℚ) := ne_of_lt hjq
  have hslope : pairSlope Pm ((j : ℕ), (0 : ℕ)) < 0 := by
    rw [pairSlope]
    apply div_neg_of_neg_of_pos
    · have : (1 : ℚ) ≤ (Pm.2 : ℚ) := by exact_mod_cast hPmv
      push_cast
      linarith
    · push_cast
      linarith
  have hform : ∀ y : ℚ, pairLine Pm ((j : ℕ), (0 : ℕ)) y
      = pairSlope Pm ((j : ℕ), (0 : ℕ)) * (y - (j : ℚ)) := by
    intro y
    rw [pairLine_right_form Pm ((j : ℕ), (0 : ℕ)) hne]
    show ((0 : ℕ) : ℚ) + _ * (y - ((j : ℕ) : ℚ)) = _
    push_cast
    ring
  have hval : (Pm, ((j : ℕ), (0 : ℕ))) ∈ validLines S := by
    rw [validLines, Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨hPmS, hj⟩, ?_⟩
    intro Q hQ
    rw [hform (Q.1 : ℚ)]
    rcases Nat.lt_or_ge Q.1 j with hQj | hQj
    · -- left dot: the max-slope choice dominates
      have hQT : Q ∈ S.filter (fun P => P.1 < j) := Finset.mem_filter.2 ⟨hQ, hQj⟩
      have hle := hPmmax Q hQT
      have hQden : (0 : ℚ) < (j : ℚ) - (Q.1 : ℚ) := by
        have : (Q.1 : ℚ) < (j : ℚ) := by exact_mod_cast hQj
        linarith
      have hkey : pairSlope Q ((j : ℕ), (0 : ℕ)) * ((Q.1 : ℚ) - (j : ℚ))
          = (Q.2 : ℚ) := by
        rw [pairSlope]
        show (((0 : ℕ) : ℚ) - (Q.2 : ℚ)) / (((j : ℕ) : ℚ) - (Q.1 : ℚ)) * _ = _
        push_cast
        field_simp
        ring
      have hmul : pairSlope Pm ((j : ℕ), (0 : ℕ)) * ((Q.1 : ℚ) - (j : ℚ))
          ≤ pairSlope Q ((j : ℕ), (0 : ℕ)) * ((Q.1 : ℚ) - (j : ℚ)) :=
        mul_le_mul_of_nonpos_right hle (by linarith)
      linarith
    · -- at or right of the anchor: nonpositive value under a natural height
      have hstep : (0 : ℚ) ≤ (Q.1 : ℚ) - (j : ℚ) := by
        have : (j : ℚ) ≤ (Q.1 : ℚ) := by exact_mod_cast hQj
        linarith
      have hnp : pairSlope Pm ((j : ℕ), (0 : ℕ)) * ((Q.1 : ℚ) - (j : ℚ)) ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨le_of_lt hslope, hstep⟩)
      have hQ2 : (0 : ℚ) ≤ (Q.2 : ℚ) := Nat.cast_nonneg _
      linarith
  intro x hx
  have hle := Finset.le_sup'
    (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 x) hval
  have hpos : 0 < pairLine Pm ((j : ℕ), (0 : ℕ)) x := by
    rw [hform x]
    exact mul_pos_of_neg_of_neg hslope (by linarith)
  exact lt_of_lt_of_le hpos hle

/-- **The leftmost dot is on the hull** (left endpoint pin): if `(0, v₀)`
    is the unique dot at abscissa `0`, the hull value there is `v₀`.
    Witness: the steepest descending chord out of `(0, v₀)` is a valid
    supporting line. -/
lemma npHeight_at_zero (hS : S.Nonempty) {v₀ : ℕ} (h0 : (0, v₀) ∈ S)
    (huniq : ∀ P ∈ S, P.1 = 0 → P.2 = v₀) :
    npHeight S hS 0 = (v₀ : ℚ) := by
  classical
  refine le_antisymm ?_ ?_
  · have := npHeight_le S hS h0
    simpa using this
  · rcases (S.filter (fun P => 0 < P.1)).eq_empty_or_nonempty with hT | hTne
    · -- all dots at abscissa 0: the horizontal diagonal line through (0, v₀)
      have hval : (((0 : ℕ), v₀), ((0 : ℕ), v₀)) ∈ validLines S := by
        rw [validLines, Finset.mem_filter]
        refine ⟨Finset.mem_product.2 ⟨h0, h0⟩, ?_⟩
        intro Q hQ
        have hQ1 : Q.1 = 0 := by
          by_contra hne
          have : Q ∈ S.filter (fun P => 0 < P.1) :=
            Finset.mem_filter.2 ⟨hQ, Nat.pos_of_ne_zero hne⟩
          rw [hT] at this
          exact absurd this (Finset.notMem_empty _)
        have hQ2 : Q.2 = v₀ := huniq Q hQ hQ1
        rw [pairLine_diag_const, hQ2]
      have hle := Finset.le_sup'
        (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 0) hval
      calc (v₀ : ℚ) = pairLine ((0 : ℕ), v₀) ((0 : ℕ), v₀) 0 :=
            (pairLine_diag_const _ _ _).symm
        _ ≤ npHeight S hS 0 := hle
    · -- steepest chord out of (0, v₀)
      obtain ⟨Qm, hQmT, hQmmin⟩ :=
        (S.filter (fun P => 0 < P.1)).exists_min_image
          (fun Q => pairSlope ((0 : ℕ), v₀) Q) hTne
      have hQmS : Qm ∈ S := (Finset.mem_filter.mp hQmT).1
      have hQmpos : 0 < Qm.1 := by
        have := (Finset.mem_filter.mp hQmT).2
        simpa using this
      have hval : (((0 : ℕ), v₀), Qm) ∈ validLines S := by
        rw [validLines, Finset.mem_filter]
        refine ⟨Finset.mem_product.2 ⟨h0, hQmS⟩, ?_⟩
        intro Q hQ
        rcases Nat.eq_zero_or_pos Q.1 with hQ1 | hQ1
        · have hQ2 : Q.2 = v₀ := huniq Q hQ hQ1
          have hcast : ((Q.1 : ℕ) : ℚ) = ((((0 : ℕ), v₀) : ℕ × ℕ).1 : ℚ) := by
            rw [hQ1]
          rw [hcast, pairLine_left, hQ2]
        · have hQT : Q ∈ S.filter (fun P => 0 < P.1) :=
            Finset.mem_filter.2 ⟨hQ, hQ1⟩
          have hge := hQmmin Q hQT
          have hQq : (0 : ℚ) < (Q.1 : ℚ) := by exact_mod_cast hQ1
          have hkey : (v₀ : ℚ) + pairSlope ((0 : ℕ), v₀) Q * (Q.1 : ℚ)
              = (Q.2 : ℚ) := by
            rw [pairSlope]
            push_cast
            rw [sub_zero, div_mul_cancel₀ _ (ne_of_gt hQq)]
            ring
          have hexp : pairLine ((0 : ℕ), v₀) Qm ((Q.1 : ℕ) : ℚ)
              = (v₀ : ℚ) + pairSlope ((0 : ℕ), v₀) Qm * (Q.1 : ℚ) := by
            rw [pairLine]
            push_cast
            ring
          rw [hexp]
          have hmul : pairSlope ((0 : ℕ), v₀) Qm * (Q.1 : ℚ)
              ≤ pairSlope ((0 : ℕ), v₀) Q * (Q.1 : ℚ) :=
            mul_le_mul_of_nonneg_right hge (le_of_lt hQq)
          linarith
      have hle := Finset.le_sup'
        (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 0) hval
      have hat0 : pairLine ((0 : ℕ), v₀) Qm 0 = (v₀ : ℚ) := by
        have := pairLine_left ((0 : ℕ), v₀) Qm
        simpa using this
      rw [← hat0]
      exact hle

/-! ## §2 — Side arithmetic kernels -/

/-- The slope denominator divides the horizontal length (`Rat.den_dvd` on
    the reduced slope fraction). -/
lemma side_e_dvd_length (s : Side) (hlt : s.i₀ < s.j₀) : s.e ∣ s.length := by
  have hslope : s.slope
      = (((s.v₁ : ℤ) - (s.v₀ : ℤ) : ℤ) : ℚ) / (((s.j₀ : ℤ) - (s.i₀ : ℤ) : ℤ) : ℚ) := by
    rw [Side.slope]
    push_cast
    ring
  have hdvd : ((s.slope.den : ℤ)) ∣ ((s.j₀ : ℤ) - (s.i₀ : ℤ)) := by
    rw [hslope, ← Rat.divInt_eq_div]
    exact Rat.den_dvd _ _
  have hlen : ((s.length : ℕ) : ℤ) = (s.j₀ : ℤ) - (s.i₀ : ℤ) := by
    rw [Side.length]
    omega
  rw [Side.e]
  have : ((s.slope.den : ℤ)) ∣ ((s.length : ℕ) : ℤ) := by
    rw [hlen]
    exact hdvd
  exact_mod_cast this

/-- `e · ℓ = length` on any side with increasing abscissae. -/
lemma side_e_mul_residualDeg (s : Side) (hlt : s.i₀ < s.j₀) :
    s.e * M4.residualDeg s = s.length := by
  rw [M4.residualDeg]
  exact Nat.mul_div_cancel' (side_e_dvd_length s hlt)

/-- Side nondegeneracy: `1 ≤ e` and `1 ≤ ℓ` on any side with increasing
    abscissae. -/
lemma side_nondeg (s : Side) (hlt : s.i₀ < s.j₀) :
    1 ≤ s.e ∧ 1 ≤ M4.residualDeg s := by
  have hepos : 0 < s.e := s.slope.den_pos
  refine ⟨hepos, ?_⟩
  have hlenpos : 0 < s.length := by
    rw [Side.length]
    omega
  have hle : s.e ≤ s.length := Nat.le_of_dvd hlenpos (side_e_dvd_length s hlt)
  rw [M4.residualDeg]
  exact (Nat.one_le_div_iff hepos).mpr hle

/-- Slope sign reads off the height drop: `h < 0 ↔ v₁ < v₀`. -/
lemma side_h_neg_iff (s : Side) (hlt : s.i₀ < s.j₀) :
    s.h < 0 ↔ s.v₁ < s.v₀ := by
  have hden : (0 : ℚ) < (s.j₀ : ℚ) - (s.i₀ : ℚ) := by
    have : (s.i₀ : ℚ) < (s.j₀ : ℚ) := by exact_mod_cast hlt
    linarith
  rw [Side.h, Rat.num_neg, Side.slope, div_neg_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact absurd hden (by linarith)
    · exact_mod_cast (by linarith : (s.v₁ : ℚ) < (s.v₀ : ℚ))
  · intro h
    right
    have : (s.v₁ : ℚ) < (s.v₀ : ℚ) := by exact_mod_cast h
    exact ⟨by linarith, hden⟩


/-! ## §1.5 — THE ABSTRACT CORE: the negative-prefix length law on a hull -/

/-- **The abstract negative-prefix length law.**  On a support with a
    (unique) left anchor `(0, v₀)`, a saturated left block (all dots left of
    `j` at height ≥ 1), a zero-anchor `(j, 0)` and a right anchor `(n, 0)`
    bounding all abscissae, every polygon side has increasing abscissae and
    the total horizontal length of the NEGATIVE-slope sides is exactly `j`. -/
theorem npSides_neg_length_sum (hS : S.Nonempty) {v₀ j n : ℕ}
    (hdot0 : (0, v₀) ∈ S) (hdotj : (j, 0) ∈ S) (hdotn : (n, 0) ∈ S)
    (hjpos : 1 ≤ j) (hjn : j ≤ n)
    (huniq0 : ∀ P ∈ S, P.1 = 0 → P.2 = v₀)
    (hleft : ∀ P ∈ S, P.1 < j → 1 ≤ P.2)
    (hub : ∀ P ∈ S, P.1 ≤ n) :
    (∀ s ∈ npSides S hS, s.i₀ < s.j₀) ∧
    (((npSides S hS).filter (fun s => decide (s.h < 0))).map
      (fun s => s.length)).sum = j := by
  classical
  -- ===== the height sign law =====
  have H0 : npHeight S hS 0 = (v₀ : ℚ) := npHeight_at_zero S hS hdot0 huniq0
  have Hpos : ∀ x : ℚ, x < (j : ℚ) → 0 < npHeight S hS x :=
    npHeight_pos_left S hS hdotj hleft ⟨(0, v₀), hdot0, hjpos⟩
  have Hzero : ∀ x : ℚ, (j : ℚ) ≤ x → x ≤ (n : ℚ) → npHeight S hS x = 0 :=
    fun x h1 h2 => npHeight_eq_zero_on S hS hdotj hdotn h1 h2
  have Hj : npHeight S hS (j : ℚ) = 0 := Hzero _ le_rfl (by exact_mod_cast hjn)
  have Hn : npHeight S hS (n : ℚ) = 0 :=
    Hzero _ (by exact_mod_cast hjn) le_rfl
  -- ===== sortedness =====
  have hsortFull : ((npVerticesFull S hS).map Prod.fst).Pairwise (· < ·) :=
    npVerticesFull_sorted S hS
  have hsortV : ((npVertices S hS).map Prod.fst).Pairwise (· < ·) :=
    npVertices_sorted S hS
  have hsortabs : (hullAbscissae S hS).Pairwise (· < ·) := by
    have := npVerticesFull_sorted S hS
    rwa [npVerticesFull_fst S hS] at this
  -- ===== abscissa bound on full vertices =====
  have habsFull : ∀ P ∈ npVerticesFull S hS, P.1 ≤ n := by
    intro P hP
    have hPa : P.1 ∈ hullAbscissae S hS := by
      rw [← npVerticesFull_fst S hS]
      exact List.mem_map_of_mem hP
    obtain ⟨v, hvS, -⟩ := (mem_hullAbscissae_iff S hS).mp hPa
    exact hub (P.1, v) hvS
  have hVsubFull : ∀ P ∈ npVertices S hS, P ∈ npVerticesFull S hS :=
    fun P hP => (dropCollinear_sublist _).subset hP
  -- ===== vertex height dichotomy =====
  have honhull : ∀ P ∈ npVertices S hS, (P.2 : ℚ) = npHeight S hS (P.1 : ℚ) :=
    fun P hP => npVertices_on_hull S hS hP
  have hposV : ∀ P ∈ npVertices S hS, P.1 < j → 1 ≤ P.2 := by
    intro P hP hPj
    have h := Hpos (P.1 : ℚ) (by exact_mod_cast hPj)
    rw [← honhull P hP] at h
    exact_mod_cast h
  have hzeroV : ∀ P ∈ npVertices S hS, j ≤ P.1 → P.2 = 0 := by
    intro P hP hPj
    have h := Hzero (P.1 : ℚ) (by exact_mod_cast hPj)
      (by exact_mod_cast habsFull P (hVsubFull P hP))
    rw [← honhull P hP] at h
    exact_mod_cast h
  -- ===== (j, 0) is a full vertex =====
  have honj : ((0 : ℕ) : ℚ) = npHeight S hS ((j : ℕ) : ℚ) := by
    rw [Hj]
    norm_num
  have hjabs : j ∈ hullAbscissae S hS :=
    (mem_hullAbscissae_iff S hS).mpr ⟨0, hdotj, honj⟩
  have hdj : hullDotAt S hS j = ((j : ℕ), (0 : ℕ)) := by
    unfold hullDotAt
    rw [hullHeightAt_of_onHull S hS hdotj honj]
  have hjFull : ((j : ℕ), (0 : ℕ)) ∈ npVerticesFull S hS := by
    rw [npVerticesFull, ← hdj]
    exact List.mem_map_of_mem hjabs
  -- ===== head pin: npVertices = (0, v₀) :: u =====
  have hon0 : ((v₀ : ℕ) : ℚ) = npHeight S hS ((0 : ℕ) : ℚ) := by
    rw [show (((0 : ℕ) : ℚ)) = (0 : ℚ) from by norm_num, H0]
  have h0abs : (0 : ℕ) ∈ hullAbscissae S hS :=
    (mem_hullAbscissae_iff S hS).mpr ⟨v₀, hdot0, hon0⟩
  obtain ⟨tA, htA⟩ := sorted_head_zero hsortabs h0abs
  have hd0 : hullDotAt S hS 0 = ((0 : ℕ), v₀) := by
    unfold hullDotAt
    rw [hullHeightAt_of_onHull S hS hdot0 hon0]
  have hFullhead : npVerticesFull S hS
      = ((0 : ℕ), v₀) :: tA.map (hullDotAt S hS) := by
    rw [npVerticesFull, htA, List.map_cons, hd0]
  obtain ⟨u, hu, -⟩ :=
    dropCollinear_cons_head ((0 : ℕ), v₀) (tA.map (hullDotAt S hS))
  have hVhead : npVertices S hS = ((0 : ℕ), v₀) :: u := by
    rw [npVertices, hFullhead, hu]
  -- ===== last pin: (n, 0) ∈ npVertices =====
  have honn : ((0 : ℕ) : ℚ) = npHeight S hS ((n : ℕ) : ℚ) := by
    rw [Hn]
    norm_num
  have hlastabs : (hullAbscissae S hS).getLast? = some n := by
    apply sorted_getLast?_eq hsortabs
    · exact (mem_hullAbscissae_iff S hS).mpr ⟨0, hdotn, honn⟩
    · intro x hx
      obtain ⟨v, hvS, -⟩ := (mem_hullAbscissae_iff S hS).mp hx
      exact hub (x, v) hvS
  have hdn : hullDotAt S hS n = ((n : ℕ), (0 : ℕ)) := by
    unfold hullDotAt
    rw [hullHeightAt_of_onHull S hS hdotn honn]
  have hlastV : (npVertices S hS).getLast? = some ((n : ℕ), (0 : ℕ)) := by
    rw [npVertices, dropCollinear_getLast?, npVerticesFull, List.getLast?_map,
      hlastabs, Option.map_some, hdn]
  have hnV : ((n : ℕ), (0 : ℕ)) ∈ npVertices S hS := mem_of_getLast?_eq hlastV
  -- ===== no-jump across j =====
  have hnojump : ∀ pr ∈ (npVertices S hS).zip (npVertices S hS).tail,
      pr.1.1 < j → pr.2.1 ≤ j := by
    intro pr hpr hlt
    by_contra hgt
    push_neg at hgt
    have hpr1V : pr.1 ∈ npVertices S hS := (List.of_mem_zip hpr).1
    have hpr2V : pr.2 ∈ npVertices S hS :=
      List.mem_of_mem_tail (List.of_mem_zip hpr).2
    have hcol : collinear₃ pr.1 ((j : ℕ), (0 : ℕ)) pr.2 = true := by
      apply dropCollinear_between (npVerticesFull S hS) hsortFull pr
        (by rw [← npVertices]; exact hpr) _ hjFull hlt hgt
    have h1v : 1 ≤ pr.1.2 := hposV pr.1 hpr1V hlt
    have h2v : pr.2.2 = 0 := hzeroV pr.2 hpr2V (le_of_lt hgt)
    rw [collinear₃, beq_iff_eq, h2v] at hcol
    push_cast at hcol
    have hcancel : ((j : ℤ) - (pr.1.1 : ℤ)) = ((pr.2.1 : ℤ) - (pr.1.1 : ℤ)) := by
      have hne : ((0 : ℤ) - (pr.1.2 : ℤ)) ≠ 0 := by
        have : (1 : ℤ) ≤ (pr.1.2 : ℤ) := by exact_mod_cast h1v
        omega
      apply mul_right_cancel₀ hne
      linarith [hcol]
    omega
  -- ===== sign ⟺ position =====
  have hsign : ∀ pr ∈ (npVertices S hS).zip (npVertices S hS).tail,
      (decide ((⟨pr.1.1, pr.2.1, pr.1.2, pr.2.2⟩ : Side).h < 0)
        = decide (pr.1.1 < j)) := by
    intro pr hpr
    have hab : pr.1.1 < pr.2.1 := zip_fst_lt _ hsortV pr hpr
    have hpr1V : pr.1 ∈ npVertices S hS := (List.of_mem_zip hpr).1
    have hpr2V : pr.2 ∈ npVertices S hS :=
      List.mem_of_mem_tail (List.of_mem_zip hpr).2
    rw [decide_eq_decide]
    rw [side_h_neg_iff _ hab]
    show pr.2.2 < pr.1.2 ↔ pr.1.1 < j
    constructor
    · intro hdrop
      by_contra hge
      push_neg at hge
      have h1 : pr.1.2 = 0 := hzeroV pr.1 hpr1V hge
      omega
    · intro hlt
      have hv1 : 1 ≤ pr.1.2 := hposV pr.1 hpr1V hlt
      have hble : pr.2.1 ≤ j := hnojump pr hpr hlt
      rcases eq_or_lt_of_le hble with heq | hltb
      · have h2 : pr.2.2 = 0 := hzeroV pr.2 hpr2V (le_of_eq heq.symm)
        omega
      · -- both endpoints strictly left of j: convex secant comparison
        have hHa : ((pr.1.2 : ℕ) : ℚ) = npHeight S hS (pr.1.1 : ℚ) :=
          honhull pr.1 hpr1V
        have hHb : ((pr.2.2 : ℕ) : ℚ) = npHeight S hS (pr.2.1 : ℚ) :=
          honhull pr.2 hpr2V
        have hcvx := npHeight_convexOn S hS (j : ℚ)
        have hxIcc : ((pr.1.1 : ℕ) : ℚ) ∈ Set.Icc (0 : ℚ) (j : ℚ) :=
          ⟨Nat.cast_nonneg _, by exact_mod_cast le_of_lt hlt⟩
        have hzIcc : ((j : ℕ) : ℚ) ∈ Set.Icc (0 : ℚ) (j : ℚ) :=
          ⟨Nat.cast_nonneg _, le_rfl⟩
        have hxy : ((pr.1.1 : ℕ) : ℚ) < ((pr.2.1 : ℕ) : ℚ) := by
          exact_mod_cast hab
        have hyz : ((pr.2.1 : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hltb
        have hkey := hcvx.slope_mono_adjacent hxIcc hzIcc hxy hyz
        rw [← hHa, ← hHb, Hj] at hkey
        have hbpos : (0 : ℚ) < ((pr.2.2 : ℕ) : ℚ) := by
          have := Hpos (pr.2.1 : ℚ) (by exact_mod_cast hltb)
          rwa [← hHb] at this
        by_contra hnd
        push_neg at hnd
        have hnum : (0 : ℚ) ≤ ((pr.2.2 : ℕ) : ℚ) - ((pr.1.2 : ℕ) : ℚ) := by
          have : ((pr.1.2 : ℕ) : ℚ) ≤ ((pr.2.2 : ℕ) : ℚ) := by exact_mod_cast hnd
          linarith
        have hdenab : (0 : ℚ) < ((pr.2.1 : ℕ) : ℚ) - ((pr.1.1 : ℕ) : ℚ) := by
          linarith
        have hlhs : (0 : ℚ)
            ≤ (((pr.2.2 : ℕ) : ℚ) - ((pr.1.2 : ℕ) : ℚ))
              / (((pr.2.1 : ℕ) : ℚ) - ((pr.1.1 : ℕ) : ℚ)) :=
          div_nonneg hnum (le_of_lt hdenab)
        have hrhs : ((0 : ℚ) - ((pr.2.2 : ℕ) : ℚ))
            / (((j : ℕ) : ℚ) - ((pr.2.1 : ℕ) : ℚ)) < 0 :=
          div_neg_of_neg_of_pos (by linarith) (by linarith)
        linarith [le_trans hlhs hkey]
  -- ===== assembly =====
  constructor
  · -- every side has increasing abscissae
    intro s hs
    rw [npSides] at hs
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hs
    exact zip_fst_lt _ hsortV pr hpr
  · -- the length sum telescopes to j
    rw [npSides, List.filter_map, List.map_map]
    have hpred : ((npVertices S hS).zip (npVertices S hS).tail).filter
          ((fun s => decide (s.h < 0)) ∘
            (fun pr : (ℕ × ℕ) × (ℕ × ℕ) => (⟨pr.1.1, pr.2.1, pr.1.2, pr.2.2⟩ : Side)))
        = ((npVertices S hS).zip (npVertices S hS).tail).filter
            (fun pr => decide (pr.1.1 < j)) :=
      List.filter_congr hsign
    rw [hpred]
    have hlen : (((npVertices S hS).zip (npVertices S hS).tail).filter
          (fun pr => decide (pr.1.1 < j))).map
            ((fun s : Side => s.length) ∘
              (fun pr : (ℕ × ℕ) × (ℕ × ℕ) => (⟨pr.1.1, pr.2.1, pr.1.2, pr.2.2⟩ : Side)))
        = (((npVertices S hS).zip (npVertices S hS).tail).filter
            (fun pr => decide (pr.1.1 < j))).map (fun pr => pr.2.1 - pr.1.1) := rfl
    rw [hlen]
    rw [hVhead, List.tail_cons]
    have hres := telescope_sum j u ((0 : ℕ), v₀)
      (by rw [← hVhead]; exact hsortV)
      (by
        intro pr hpr
        exact hnojump pr (by rw [hVhead, List.tail_cons]; exact hpr))
      (Nat.zero_le j)
      ⟨((n : ℕ), (0 : ℕ)), by rw [← hVhead]; exact hnV, hjn⟩
    rw [hres]
    rfl

/-! ## §3 — p-adic residue kernels -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- Reduction mod `p` detects divisibility (kernel of `toZMod`). -/
lemma toZMod_eq_zero_iff (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

/-- `p ∣ x ↔ 1 ≤ v(x)` on nonzero `x`. -/
lemma p_dvd_iff_one_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) :
    (p : ℤ_[p]) ∣ x ↔ 1 ≤ x.valuation := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by
      intro h
      exact hx (by rw [h, mul_zero])
    have hval := PadicInt.valuation_p_pow_mul 1 y hy
    rw [pow_one] at hval
    rw [hval]
    omega
  · intro hv
    have hspec := PadicInt.unitCoeff_spec hx
    rw [hspec]
    exact Dvd.dvd.mul_left
      (dvd_pow_self _ (by omega : x.valuation ≠ 0)) _

/-- The mod-`p` coefficient is nonzero iff the `ℤ_[p]` coefficient is a
    unit (nonzero of valuation 0). -/
lemma coeff_map_toZMod_ne_zero_iff (f : Polynomial ℤ_[p]) (i : ℕ) :
    (f.map PadicInt.toZMod).coeff i ≠ 0 ↔
      f.coeff i ≠ 0 ∧ (f.coeff i).valuation = 0 := by
  rw [Polynomial.coeff_map, Ne, toZMod_eq_zero_iff]
  constructor
  · intro h
    have hne : f.coeff i ≠ 0 := by
      intro h0
      exact h (h0 ▸ dvd_zero _)
    refine ⟨hne, ?_⟩
    by_contra hv
    exact h ((p_dvd_iff_one_le_valuation _ hne).mpr (by omega))
  · rintro ⟨hne, hv⟩ hdvd
    have := (p_dvd_iff_one_le_valuation _ hne).mp hdvd
    omega

end BPLL

/-! ## §4 — THE LAW -/

open Polynomial LeanUrat.OM LeanUrat.OM.NewtonPolygon BPLL in
/-- **`BasePolygonLengthLaw p` HOLDS** (synthesis pass-6 F2; the named open
    row of `CU2tKp0.lean`, now supplied).  On the decided finite-slope
    saturated perimeter, the corpus principal polygon is nondegenerate and
    its total horizontal length `Σ e·ℓ` equals `ord_X(f̄) ≥ 1`. -/
theorem basePolygonLengthLaw_proved (p : ℕ) [Fact p.Prime] :
    BasePolygonLengthLaw p := by
  intro f hf hc0 hsat
  classical
  -- ===== residue-side data: j₀ = natTrailingDegree of the reduction =====
  have hfbarm : (f.map PadicInt.toZMod).Monic := hf.map _
  have hfbarne : f.map PadicInt.toZMod ≠ 0 := hfbarm.ne_zero
  set j₀ : ℕ := (f.map PadicInt.toZMod).natTrailingDegree with hj₀def
  have hcoeffj₀ : (f.map PadicInt.toZMod).coeff j₀ ≠ 0 := by
    rw [hj₀def]
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hfbarne
  have hcoefflt : ∀ i < j₀, (f.map PadicInt.toZMod).coeff i = 0 := fun i hi =>
    Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi
  have hXdvd : (Polynomial.X : Polynomial (ZMod p)) ^ j₀ ∣ f.map PadicInt.toZMod :=
    Polynomial.X_pow_dvd_iff.mpr fun d hd => hcoefflt d hd
  have hXndvd :
      ¬ (Polynomial.X : Polynomial (ZMod p)) ^ (j₀ + 1) ∣ f.map PadicInt.toZMod :=
    fun h => hcoeffj₀ (Polynomial.X_pow_dvd_iff.mp h j₀ (Nat.lt_succ_self _))
  have hbar0 : (f.map PadicInt.toZMod).coeff 0 = 0 := by
    rw [Polynomial.coeff_map]
    exact (BPLL.toZMod_eq_zero_iff _).mpr hsat
  have hj₀pos : 1 ≤ j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · exact absurd hbar0 (h ▸ hcoeffj₀)
    · exact h
  have hnbar : (f.map PadicInt.toZMod).natDegree = f.natDegree :=
    hf.natDegree_map _
  have hj₀n : j₀ ≤ f.natDegree := by
    rw [← hnbar]
    exact Polynomial.natTrailingDegree_le_natDegree _
  -- ===== support-side data =====
  have hS : (M2.valSupport p f).Nonempty := M2.valSupport_nonempty_of_monic p hf
  have hchar := (M2.valSupport_facts p f).1
  have hdotj₀ : ((j₀ : ℕ), (0 : ℕ)) ∈ M2.valSupport p f := by
    obtain ⟨hne, hv⟩ := (BPLL.coeff_map_toZMod_ne_zero_iff f j₀).mp hcoeffj₀
    exact (hchar j₀ 0).mpr ⟨hne, by rw [M2.coeffVal_def, hv]⟩
  have hdotn : ((f.natDegree : ℕ), (0 : ℕ)) ∈ M2.valSupport p f :=
    (M2.valSupport_facts p f).2 hf
  have hdot0 : ((0 : ℕ), M2.coeffVal p f 0) ∈ M2.valSupport p f :=
    (hchar 0 (M2.coeffVal p f 0)).mpr ⟨hc0, rfl⟩
  have huniq0 : ∀ P ∈ M2.valSupport p f, P.1 = 0 → P.2 = M2.coeffVal p f 0 := by
    rintro ⟨i, v⟩ hP h0
    obtain ⟨-, hveq⟩ := (hchar i v).mp hP
    subst h0
    exact hveq
  have hleftv : ∀ P ∈ M2.valSupport p f, P.1 < j₀ → 1 ≤ P.2 := by
    rintro ⟨i, v⟩ hP hi
    obtain ⟨hne, hveq⟩ := (hchar i v).mp hP
    by_contra h
    push_neg at h
    have hv0 : (f.coeff i).valuation = 0 := by
      rw [M2.coeffVal_def] at hveq
      omega
    have : (f.map PadicInt.toZMod).coeff i ≠ 0 :=
      (BPLL.coeff_map_toZMod_ne_zero_iff f i).mpr ⟨hne, hv0⟩
    exact this (hcoefflt i hi)
  have habsle : ∀ P ∈ M2.valSupport p f, P.1 ≤ f.natDegree := by
    rintro ⟨i, v⟩ hP
    exact Polynomial.le_natDegree_of_ne_zero ((hchar i v).mp hP).1
  -- ===== the abstract core =====
  obtain ⟨hincr, hsum⟩ := BPLL.npSides_neg_length_sum (M2.valSupport p f) hS
    hdot0 hdotj₀ hdotn hj₀pos hj₀n huniq0 hleftv habsle
  -- ===== membership plumbing =====
  have hsl : sideList f = NewtonPolygon.npSides (M2.valSupport p f) hS := by
    rw [sideList, dif_pos hS]
  have hmemincr : ∀ s ∈ principalSideList f, s.i₀ < s.j₀ := by
    intro s hs
    rw [principalSideList, hsl] at hs
    exact hincr s (List.mem_of_mem_filter hs)
  -- ===== nondegeneracy leg =====
  have hnondeg : ∀ Sd ∈ principalData f, 1 ≤ Sd.e ∧ 1 ≤ Sd.ℓ := by
    intro Sd hSd
    rw [principalData] at hSd
    obtain ⟨s, hsmem, rfl⟩ := List.mem_map.mp hSd
    obtain ⟨he, hℓ⟩ := BPLL.side_nondeg s (hmemincr s hsmem)
    exact ⟨he, hℓ⟩
  -- ===== the length-tie leg =====
  refine ⟨hnondeg, j₀, hj₀pos, hXdvd, hXndvd, ?_⟩
  rw [principalData, List.map_map]
  have hvals : (principalSideList f).map
        ((fun Sd => Sd.e * Sd.ℓ) ∘ sideToDatum)
      = (principalSideList f).map (fun s => s.length) := by
    apply List.map_congr_left
    intro s hs
    show s.e * M4.residualDeg s = s.length
    exact BPLL.side_e_mul_residualDeg s (hmemincr s hs)
  rw [hvals, principalSideList, hsl]
  exact hsum

/-! ## §5 — Instance gate (falsifier-style statement check) -/

namespace BPLLGate

open Polynomial LeanUrat.OM LeanUrat.Scaffold.HDischarge.H6

/-- Gate H (Hensel family): at the Hensel configuration (`v(f₀) ≥ 1`,
    `f₁` a unit) the law's length-tie is EXACTLY the compiled unique-side
    read — `Σ e·ℓ = 1·1 = 1 = j₀`.  Checks the statement against the
    landed `principalData_hensel_a0_one` INDEPENDENTLY of the §4 proof. -/
theorem gate_hensel {p : ℕ} [Fact p.Prime] (f : Polynomial ℤ_[p])
    (hc0 : f.coeff 0 ≠ 0) (hv0 : 1 ≤ (f.coeff 0).valuation)
    (hc1 : f.coeff 1 ≠ 0) (hv1 : (f.coeff 1).valuation = 0) :
    ((principalData f).map fun S => S.e * S.ℓ).sum = 1 := by
  rw [principalData_hensel_a0_one f hc0 hv0 hc1 hv1]
  rfl

/-- Gate E (Eisenstein `e = 2` instance): `f = X² + 2` over `ℤ_[2]` — the
    law fires at a genuinely RAMIFIED base read (single slope −1/2 side):
    total horizontal length `Σ e·ℓ = 2 = j₀` with `f̄ = X²`, exercising the
    `e ∣ length` and telescoping legs at `e = 2` (j₀ pinned independently
    by the exact-multiplicity clauses). -/
theorem gate_eisenstein_sum :
    ((principalData ((X : Polynomial ℤ_[2]) ^ 2 + C 2)).map
      fun S => S.e * S.ℓ).sum = 2 := by
  set f : Polynomial ℤ_[2] := X ^ 2 + C 2 with hfdef
  have hmon : f.Monic := monic_X_pow_add_C _ (by norm_num)
  have hc0v : f.coeff 0 = 2 := by
    rw [hfdef]
    rw [coeff_add, coeff_X_pow, coeff_C]
    norm_num
  have hc0 : f.coeff 0 ≠ 0 := by
    rw [hc0v]
    exact two_ne_zero
  have hsat : ((2 : ℕ) : ℤ_[2]) ∣ f.coeff 0 := by
    rw [hc0v]
    exact ⟨1, by norm_num⟩
  obtain ⟨-, j₀, -, hdvd, hndvd, hsum⟩ :=
    basePolygonLengthLaw_proved 2 f hmon hc0 hsat
  have hmap : f.map PadicInt.toZMod = (X : Polynomial (ZMod 2)) ^ 2 := by
    rw [hfdef, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    have h2 : (PadicInt.toZMod (2 : ℤ_[2]) : ZMod 2) = 0 := by
      rw [map_ofNat PadicInt.toZMod 2]
      decide
    rw [h2, Polynomial.C_0, add_zero]
  rw [hmap] at hdvd hndvd
  have hX2ne : (X : Polynomial (ZMod 2)) ^ 2 ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hj2 : j₀ = 2 := by
    have hle : j₀ ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd hX2ne
      simpa [Polynomial.natDegree_X_pow] using this
    have hge : 2 ≤ j₀ := by
      by_contra h
      push_neg at h
      exact hndvd (pow_dvd_pow _ (by omega))
    omega
  rw [hsum, hj2]

end BPLLGate

/-! ## §6 — CONSUMER FIRED: `terminalPolySem_kp0_of_law`, unconditional -/

open Polynomial in
/-- **THE CONSUMER, UNCONDITIONAL** (the F2 charter's value clause): with
    `BasePolygonLengthLaw` proved, the k′ = 0 face fires at the positive-gate
    instance with NO per-instance polygon computation — `TerminalPolySem`
    holds at the real ι-certified read of `X + 2` purely from the seam
    perimeter (monic, `f(0) = 2 ≠ 0`, `2 ∣ f(0)`). -/
theorem terminalPolySem_kp0_unconditional :
    TerminalPolySem Kp0Gate.fkp0 Hkp0 Kp0Gate.Dkp0 := by
  have hc0 : Kp0Gate.fkp0.coeff 0 ≠ 0 := by
    rw [Kp0Gate.fkp0]
    simp only [coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
    exact two_ne_zero
  have hsat : ((2 : ℕ) : ℤ_[2]) ∣ Kp0Gate.fkp0.coeff 0 := by
    rw [Kp0Gate.fkp0]
    simp only [coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
    exact ⟨1, by norm_num⟩
  exact terminalPolySem_kp0_of_law (basePolygonLengthLaw_proved 2)
    Kp0Gate.fkp0 Hkp0 Kp0Gate.Dkp0 (monic_X_add_C _) rfl
    Kp0Gate.readThroughIota_kp0 hc0 hsat

end LeanUrat.Scaffold.DictIII
