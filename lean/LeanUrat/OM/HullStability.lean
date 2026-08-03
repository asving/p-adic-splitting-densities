import Mathlib
import LeanUrat.OM.NewtonPolygon

/-!
# OM/HullStability — the repaired hull-invariance lemma (banked-sorry attempt unit)

TARGET: `Classifier.npVertices_stable_of_hull_preserved` (the campaign's ONE banked
`sorry`, off the capstone path).  This file proves the abstract three-hypothesis
hull-invariance statement

  `hpres` (S'-vertices ⊆ S, same decorated points) + `habove` (S-dots weakly above the
  S'-hull) + `habs` (S-abscissae ⊆ S'-abscissae)  ⇒  `npVertices S = npVertices S'`

as `npVertices_stable_of_hull_preserved_core` at the bottom, against Mathlib + the
proved `OM/NewtonPolygon.lean` kernels only.

PROOF ROUTE (unit 2026-08-08 #10, BPLL fold-in; numerically falsifier-tested 0/4000):
1. §A — the BPLL §0 list kernels (`Scaffold/DictIII/BasePolyLength.lean`), copied
   VERBATIM with attribution: `Classifier` sits on the capstone import path, so this
   file stays import-minimal (Mathlib + NewtonPolygon) instead of dragging the
   183-module Scaffold closure under the OM tree.  Key kernel: `dropCollinear_between`
   (the straddle killer).
2. §B — new sorted-list kernels: head/last pins, no-dot-between-consecutive,
   interior-neighbor existence, bracket covers, and `sorted_eq_of_mem_iff`
   (strictly-sorted lists with the same members are equal).
3. §C — collinearity/affine arithmetic: slope transfer between coincident affine
   evaluations, `collinear₃` from equal adjacent slopes, and the junction transitivity
   `collinear₃_trans'` (the two-lines-through-two-points argument).
4. §D — `dropCollinear_corner`: the SURVIVOR-CORNER law — on a strictly-sorted input,
   `dropCollinear` leaves NO collinear consecutive triple (converse of
   `dropCollinear_between`; the fact that forces the target's truth).
5. §E — hull kernels: valid-line endpoints are on the hull; slope monotonicity at a
   hull dot; extreme abscissae are hull abscissae; consecutive FULL vertices span
   valid chords (flattest-chord argmin construction); the glue induction lifting
   chord attainment from consecutive full vertices to consecutive GENUINE vertices.
6. §F — the master assembly: the two hulls agree on the common abscissa range, the
   vertex head/last pins transfer, and each side's vertex membership is forced by the
   other side's survivor-corner law through slope transfer.
-/

namespace LeanUrat.OM.NewtonPolygon

open scoped Classical
open Finset

/-! ## §A — BPLL §0 kernels, copied VERBATIM from
`LeanUrat/Scaffold/DictIII/BasePolyLength.lean` (namespace `Scaffold.DictIII.BPLL`,
proved 2026-08-08) for import hygiene; see the header note. -/

/-- Consecutive pairs of a strictly-abscissa-sorted point list increase.
(BPLL `zip_fst_lt`, verbatim.) -/
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

/-- A strictly-sorted list containing an upper bound `n` ends at `n`.
(BPLL `sorted_getLast?_eq`, verbatim.) -/
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

/-- Membership from `getLast?`.  (BPLL `mem_of_getLast?_eq`, verbatim.) -/
lemma mem_of_getLast?_eq : ∀ {l : List (ℕ × ℕ)} {a : ℕ × ℕ},
    l.getLast? = some a → a ∈ l
  | [], _, h => by simp at h
  | [b], a, h => by
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      simp [h]
  | b :: c :: t, a, h => by
      rw [List.getLast?_cons_cons] at h
      exact List.mem_cons_of_mem _ (mem_of_getLast?_eq h)

/-- `dropCollinear` keeps the last entry.  (BPLL `dropCollinear_getLast?`, verbatim.) -/
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

/-- Integer cross-product collinearity is transitive along increasing abscissae.
(BPLL `collinear₃_trans`, verbatim.) -/
lemma collinear₃_trans {a b z c : ℕ × ℕ} (hbc : b.1 < c.1)
    (h₁ : collinear₃ a b c = true) (h₂ : collinear₃ b z c = true) :
    collinear₃ a z c = true := by
  simp only [collinear₃, beq_iff_eq] at h₁ h₂ ⊢
  have hcb : ((c.1 : ℤ) - (b.1 : ℤ)) ≠ 0 := by
    have : (b.1 : ℤ) < (c.1 : ℤ) := by exact_mod_cast hbc
    omega
  refine mul_right_cancel₀ hcb ?_
  linear_combination ((c.1 : ℤ) - (z.1 : ℤ)) * h₁ + ((c.1 : ℤ) - (a.1 : ℤ)) * h₂

/-- **The `dropCollinear` merge invariant** (the straddle killer): every ORIGINAL point
whose abscissa lies strictly between two CONSECUTIVE surviving points is collinear with
them.  (BPLL `dropCollinear_between`, verbatim.) -/
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

/-- `pairLine` re-based at its RIGHT anchor.  (BPLL `pairLine_right_form`, verbatim.) -/
lemma pairLine_right_form (P R : ℕ × ℕ) (h : (P.1 : ℚ) ≠ (R.1 : ℚ)) (x : ℚ) :
    pairLine P R x = (R.2 : ℚ) + pairSlope P R * (x - (R.1 : ℚ)) := by
  have h2 := pairLine_right P R h
  simp only [pairLine] at h2 ⊢
  linear_combination h2

/-! ## §B — new sorted-list kernels -/

/-- A strictly-sorted `ℕ`-list containing a lower bound `m` starts at `m`. -/
lemma sorted_head_min {l : List ℕ} (hs : l.Pairwise (· < ·)) {m : ℕ}
    (hm : m ∈ l) (hlb : ∀ x ∈ l, m ≤ x) : ∃ t, l = m :: t := by
  cases l with
  | nil => simp at hm
  | cons a t =>
      rcases List.mem_cons.mp hm with h | h
      · exact ⟨t, by rw [← h]⟩
      · have h1 := (List.pairwise_cons.mp hs).1 m h
        have h2 := hlb a List.mem_cons_self
        omega

/-- In a strictly-abscissa-sorted point list, everything is `≤` the last abscissa. -/
lemma sorted_le_getLast? : ∀ {l : List (ℕ × ℕ)},
    (l.map Prod.fst).Pairwise (· < ·) → ∀ {L : ℕ × ℕ}, l.getLast? = some L →
    ∀ z ∈ l, z.1 ≤ L.1
  | [], _, _, hL, _, hz => by simp at hz
  | [a], _, L, hL, z, hz => by
      simp only [List.getLast?_singleton, Option.some.injEq] at hL
      rw [List.mem_singleton] at hz
      subst hL; subst hz; exact le_refl _
  | a :: b :: t, hs, L, hL, z, hz => by
      rw [List.getLast?_cons_cons] at hL
      have hs' : ((b :: t).map Prod.fst).Pairwise (· < ·) := by
        rw [List.map_cons, List.pairwise_cons] at hs
        exact hs.2
      have hafst : ∀ x ∈ (b :: t).map Prod.fst, a.1 < x := by
        rw [List.map_cons, List.pairwise_cons] at hs
        exact hs.1
      rcases List.mem_cons.mp hz with rfl | hz'
      · have hLmem : L ∈ b :: t := mem_of_getLast?_eq hL
        exact le_of_lt (hafst L.1 (List.mem_map_of_mem hLmem))
      · exact sorted_le_getLast? hs' hL z hz'

/-- Strictly-abscissa-sorted lists have injective abscissae. -/
lemma fst_inj_of_sorted : ∀ {l : List (ℕ × ℕ)},
    (l.map Prod.fst).Pairwise (· < ·) →
    ∀ P ∈ l, ∀ Q ∈ l, P.1 = Q.1 → P = Q
  | [], _, P, hP, _, _, _ => by simp at hP
  | a :: t, hs, P, hP, Q, hQ, heq => by
      have hs' : (t.map Prod.fst).Pairwise (· < ·) := by
        rw [List.map_cons, List.pairwise_cons] at hs
        exact hs.2
      have hafst : ∀ x ∈ t.map Prod.fst, a.1 < x := by
        rw [List.map_cons, List.pairwise_cons] at hs
        exact hs.1
      rcases List.mem_cons.mp hP with rfl | hP'
      · rcases List.mem_cons.mp hQ with rfl | hQ'
        · rfl
        · exact absurd heq (by have := hafst Q.1 (List.mem_map_of_mem hQ'); omega)
      · rcases List.mem_cons.mp hQ with rfl | hQ'
        · exact absurd heq (by have := hafst P.1 (List.mem_map_of_mem hP'); omega)
        · exact fst_inj_of_sorted hs' P hP' Q hQ' heq

/-- No list entry lies strictly between a consecutive pair of a strictly-sorted
`ℕ`-list. -/
lemma no_between_nat : ∀ (l : List ℕ), l.Pairwise (· < ·) →
    ∀ pr ∈ l.zip l.tail, ∀ z ∈ l, pr.1 < z → z < pr.2 → False
  | [], _, pr, hpr, _, _, _, _ => by simp at hpr
  | [a], _, pr, hpr, _, _, _, _ => by simp at hpr
  | a :: b :: t, hs, pr, hpr, z, hz, h1, h2 => by
      have hs' : (b :: t).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
      have ha : ∀ x ∈ b :: t, a < x := (List.pairwise_cons.mp hs).1
      have hb : ∀ x ∈ t, b < x := (List.pairwise_cons.mp hs').1
      rw [show (a :: b :: t).tail = b :: t from rfl, List.zip_cons_cons,
        List.mem_cons] at hpr
      rcases hpr with rfl | hpr'
      · -- pr = (a, b)
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact absurd h1 (lt_irrefl _)
        · rcases List.mem_cons.mp hz' with rfl | hz''
          · exact absurd h2 (lt_irrefl _)
          · exact absurd h2 (by have := hb z hz''; omega)
      · rcases List.mem_cons.mp hz with rfl | hz'
        · have hpr1 : pr.1 ∈ b :: t := (List.of_mem_zip hpr').1
          exact absurd h1 (by have := ha pr.1 hpr1; omega)
        · exact no_between_nat (b :: t) hs' pr hpr' z hz' h1 h2

/-- A consecutive pair of a point list projects to a consecutive pair of the abscissa
list. -/
lemma zip_pair_map_fst : ∀ {l : List (ℕ × ℕ)} {pr : (ℕ × ℕ) × (ℕ × ℕ)},
    pr ∈ l.zip l.tail →
    (pr.1.1, pr.2.1) ∈ (l.map Prod.fst).zip ((l.map Prod.fst).tail)
  | [], pr, hpr => by simp at hpr
  | [a], pr, hpr => by simp at hpr
  | a :: b :: t, pr, hpr => by
      rw [show (a :: b :: t).tail = b :: t from rfl, List.zip_cons_cons,
        List.mem_cons] at hpr
      rw [List.map_cons, List.map_cons,
        show (a.1 :: b.1 :: t.map Prod.fst).tail = b.1 :: t.map Prod.fst from rfl,
        List.zip_cons_cons, List.mem_cons]
      rcases hpr with rfl | hpr'
      · exact Or.inl rfl
      · exact Or.inr (zip_pair_map_fst hpr')

/-- A non-last entry has an immediate successor pair. -/
lemma exists_zip_right : ∀ (l : List (ℕ × ℕ)) {P : ℕ × ℕ}, P ∈ l →
    l.getLast? ≠ some P → ∃ z, (P, z) ∈ l.zip l.tail
  | [], P, hP, _ => by simp at hP
  | [a], P, hP, hlast => by
      rw [List.mem_singleton] at hP
      subst hP
      simp at hlast
  | a :: b :: t, P, hP, hlast => by
      rcases List.mem_cons.mp hP with rfl | hP'
      · exact ⟨b, by rw [show (P :: b :: t).tail = b :: t from rfl,
          List.zip_cons_cons]; exact List.mem_cons_self⟩
      · rw [List.getLast?_cons_cons] at hlast
        obtain ⟨z, hz⟩ := exists_zip_right (b :: t) hP' hlast
        exact ⟨z, by rw [show (a :: b :: t).tail = b :: t from rfl,
          List.zip_cons_cons]; exact List.mem_cons_of_mem _ hz⟩

/-- A non-head entry has an immediate predecessor pair. -/
lemma exists_zip_left : ∀ (l : List (ℕ × ℕ)) {P : ℕ × ℕ}, P ∈ l →
    l.head? ≠ some P → ∃ x, (x, P) ∈ l.zip l.tail
  | [], P, hP, _ => by simp at hP
  | a :: t, P, hP, hhead => by
      have hPa : P ≠ a := by
        intro h
        subst h
        simp at hhead
      have hP' : P ∈ t := by
        rcases List.mem_cons.mp hP with h | h
        · exact absurd h hPa
        · exact h
      cases t with
      | nil => simp at hP'
      | cons b t' =>
          by_cases hPb : P = b
          · subst hPb
            exact ⟨a, by
              rw [show (a :: P :: t').tail = P :: t' from rfl, List.zip_cons_cons]
              exact List.mem_cons_self⟩
          · have hP'' : P ∈ t' := by
              rcases List.mem_cons.mp hP' with h | h
              · exact absurd h hPb
              · exact h
            obtain ⟨x, hx⟩ := exists_zip_left (b :: t')
              (List.mem_cons_of_mem b hP'') (by
                simp only [List.head?_cons, ne_eq, Option.some.injEq]
                intro h
                exact hPb h.symm)
            exact ⟨x, by
              rw [show (a :: b :: t').tail = b :: t' from rfl, List.zip_cons_cons]
              exact List.mem_cons_of_mem _ hx⟩

/-- **Bracket (strict/weak):** from a head strictly left of `c` and any entry at or
right of `c`, some consecutive pair straddles `c` (left strictly, right weakly). -/
lemma zip_bracket : ∀ (V : List (ℕ × ℕ)) (P : ℕ × ℕ) {c : ℕ}, P.1 < c →
    (∃ Q ∈ P :: V, c ≤ Q.1) →
    ∃ pr ∈ (P :: V).zip V, pr.1.1 < c ∧ c ≤ pr.2.1
  | [], P, c, hPc, hex => by
      obtain ⟨Q, hQ, hcQ⟩ := hex
      rw [List.mem_singleton] at hQ
      subst hQ
      omega
  | R :: rest, P, c, hPc, hex => by
      by_cases hcR : c ≤ R.1
      · exact ⟨(P, R), by rw [List.zip_cons_cons]; exact List.mem_cons_self, hPc, hcR⟩
      · push_neg at hcR
        have hex' : ∃ Q ∈ R :: rest, c ≤ Q.1 := by
          obtain ⟨Q, hQ, hcQ⟩ := hex
          rcases List.mem_cons.mp hQ with rfl | hQ'
          · omega
          · exact ⟨Q, hQ', hcQ⟩
        obtain ⟨pr, hpr, h1, h2⟩ := zip_bracket rest R hcR hex'
        exact ⟨pr, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hpr,
          h1, h2⟩

/-- **Bracket cover (`ℚ`, weak/weak):** a rational point of `[head, last]` is covered
by some consecutive pair. -/
lemma bracket_cover : ∀ (V : List (ℕ × ℕ)) (P L : ℕ × ℕ) {x : ℚ},
    (P :: V).getLast? = some L → ((P.1 : ℚ)) ≤ x → x ≤ ((L.1 : ℚ)) → V ≠ [] →
    ∃ pr ∈ (P :: V).zip V, ((pr.1.1 : ℚ)) ≤ x ∧ x ≤ ((pr.2.1 : ℚ))
  | [], _, _, _, _, _, _, hne => absurd rfl hne
  | R :: rest, P, L, x, hlast, hPx, hxL, _ => by
      by_cases hxR : x ≤ ((R.1 : ℚ))
      · exact ⟨(P, R), by rw [List.zip_cons_cons]; exact List.mem_cons_self, hPx, hxR⟩
      · push_neg at hxR
        cases rest with
        | nil =>
            rw [List.getLast?_cons_cons, List.getLast?_singleton,
              Option.some.injEq] at hlast
            subst hlast
            exact absurd hxL (by push_neg; exact hxR)
        | cons c t =>
            rw [List.getLast?_cons_cons] at hlast
            obtain ⟨pr, hpr, h1, h2⟩ :=
              bracket_cover (c :: t) R L hlast (le_of_lt hxR) hxL (by simp)
            exact ⟨pr, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hpr,
              h1, h2⟩

/-- Two strictly-abscissa-sorted point lists with the same members are EQUAL. -/
lemma sorted_eq_of_mem_iff : ∀ {l₁ l₂ : List (ℕ × ℕ)},
    (l₁.map Prod.fst).Pairwise (· < ·) → (l₂.map Prod.fst).Pairwise (· < ·) →
    (∀ P, P ∈ l₁ ↔ P ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: t₂, _, _, hmem => absurd ((hmem b).mpr List.mem_cons_self) (by simp)
  | a :: t₁, [], _, _, hmem => absurd ((hmem a).mp List.mem_cons_self) (by simp)
  | a :: t₁, b :: t₂, hs₁, hs₂, hmem => by
      have hafst : ∀ x ∈ t₁.map Prod.fst, a.1 < x := by
        rw [List.map_cons, List.pairwise_cons] at hs₁
        exact hs₁.1
      have hbfst : ∀ x ∈ t₂.map Prod.fst, b.1 < x := by
        rw [List.map_cons, List.pairwise_cons] at hs₂
        exact hs₂.1
      have hs₁' : (t₁.map Prod.fst).Pairwise (· < ·) := by
        rw [List.map_cons, List.pairwise_cons] at hs₁
        exact hs₁.2
      have hs₂' : (t₂.map Prod.fst).Pairwise (· < ·) := by
        rw [List.map_cons, List.pairwise_cons] at hs₂
        exact hs₂.2
      have hab : a = b := by
        rcases List.mem_cons.mp ((hmem a).mp List.mem_cons_self) with h | h
        · exact h
        · rcases List.mem_cons.mp ((hmem b).mpr List.mem_cons_self) with h' | h'
          · exact h'.symm
          · have h1 := hbfst a.1 (List.mem_map_of_mem h)
            have h2 := hafst b.1 (List.mem_map_of_mem h')
            omega
      subst hab
      have htail : ∀ P, P ∈ t₁ ↔ P ∈ t₂ := by
        intro P
        constructor
        · intro hP
          rcases List.mem_cons.mp ((hmem P).mp (List.mem_cons_of_mem a hP)) with h | h
          · subst h
            exact absurd (hafst P.1 (List.mem_map_of_mem hP)) (lt_irrefl _)
          · exact h
        · intro hP
          rcases List.mem_cons.mp ((hmem P).mpr (List.mem_cons_of_mem a hP)) with h | h
          · subst h
            exact absurd (hbfst P.1 (List.mem_map_of_mem hP)) (lt_irrefl _)
          · exact h
      rw [sorted_eq_of_mem_iff hs₁' hs₂' htail]

/-! ## §C — collinearity / affine-line arithmetic -/

/-- The affine evaluation identity: `pairLine` at `x` from its value at `y`. -/
lemma pairLine_eval_shift (A B : ℕ × ℕ) (x y : ℚ) :
    pairLine A B x = pairLine A B y + pairSlope A B * (x - y) := by
  simp only [pairLine]
  ring

/-- Two candidate lines agreeing at two distinct abscissae have equal slopes. -/
lemma pairSlope_eq_of_eval₂ {A B C D : ℕ × ℕ} {x₁ x₂ : ℚ} (hne : x₁ ≠ x₂)
    (h₁ : pairLine A B x₁ = pairLine C D x₁) (h₂ : pairLine A B x₂ = pairLine C D x₂) :
    pairSlope A B = pairSlope C D := by
  have hAB := pairLine_eval_shift A B x₂ x₁
  have hCD := pairLine_eval_shift C D x₂ x₁
  have hsub : x₂ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hkey : pairSlope A B * (x₂ - x₁) = pairSlope C D * (x₂ - x₁) := by
    rw [h₁, h₂] at hAB
    linarith [hAB, hCD]
  exact mul_right_cancel₀ hsub hkey

/-- Two candidate lines agreeing at two distinct abscissae agree everywhere. -/
lemma pairLine_eq_of_eval₂ {A B C D : ℕ × ℕ} {x₁ x₂ : ℚ} (hne : x₁ ≠ x₂)
    (h₁ : pairLine A B x₁ = pairLine C D x₁) (h₂ : pairLine A B x₂ = pairLine C D x₂) :
    ∀ y, pairLine A B y = pairLine C D y := by
  intro y
  have hs := pairSlope_eq_of_eval₂ hne h₁ h₂
  rw [pairLine_eval_shift A B y x₁, pairLine_eval_shift C D y x₁, h₁, hs]

/-- The chord through `A` and a point ON the line `A–R` is the line `A–R` itself. -/
lemma pairLine_eq_of_through {A B R : ℕ × ℕ} (hab : A.1 < B.1)
    (hB : (B.2 : ℚ) = pairLine A R (B.1 : ℚ)) :
    ∀ y, pairLine A B y = pairLine A R y := by
  have h₁ : pairLine A B ((A.1 : ℚ)) = pairLine A R ((A.1 : ℚ)) := by
    rw [pairLine_left, pairLine_left]
  have h₂ : pairLine A B ((B.1 : ℚ)) = pairLine A R ((B.1 : ℚ)) := by
    rw [pairLine_right A B (by exact_mod_cast Nat.ne_of_lt hab), ← hB]
  exact pairLine_eq_of_eval₂ (by
    have : ((A.1 : ℚ)) < ((B.1 : ℚ)) := by exact_mod_cast hab
    exact ne_of_lt this) h₁ h₂

/-- Integer collinearity evaluates the chord: if `collinear₃ A C B` and `A.1 < B.1`,
the chord `A–B` passes through `C`. -/
lemma pairLine_eq_of_collinear₃ {A C B : ℕ × ℕ} (h : collinear₃ A C B = true)
    (hab : A.1 < B.1) : pairLine A B ((C.1 : ℚ)) = (C.2 : ℚ) := by
  simp only [collinear₃, beq_iff_eq] at h
  have hq : (((C.1 : ℤ) : ℚ) - ((A.1 : ℤ) : ℚ)) * (((B.2 : ℤ) : ℚ) - ((A.2 : ℤ) : ℚ))
      = (((B.1 : ℤ) : ℚ) - ((A.1 : ℤ) : ℚ)) * (((C.2 : ℤ) : ℚ) - ((A.2 : ℤ) : ℚ)) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  have hba : ((B.1 : ℚ)) - ((A.1 : ℚ)) ≠ 0 := by
    have : ((A.1 : ℚ)) < ((B.1 : ℚ)) := by exact_mod_cast hab
    intro hzero
    linarith
  simp only [pairLine, pairSlope]
  field_simp
  linarith [hq]

/-- Equal adjacent slopes give integer collinearity. -/
lemma collinear₃_of_pairSlope_eq {x y z : ℕ × ℕ} (h1 : x.1 < y.1) (h2 : y.1 < z.1)
    (h : pairSlope x y = pairSlope y z) : collinear₃ x y z = true := by
  have hyx : ((y.1 : ℚ)) - ((x.1 : ℚ)) ≠ 0 := by
    have : ((x.1 : ℚ)) < ((y.1 : ℚ)) := by exact_mod_cast h1
    intro hzero; linarith
  have hzy : ((z.1 : ℚ)) - ((y.1 : ℚ)) ≠ 0 := by
    have : ((y.1 : ℚ)) < ((z.1 : ℚ)) := by exact_mod_cast h2
    intro hzero; linarith
  rw [pairSlope, pairSlope, div_eq_div_iff hyx hzy] at h
  -- h : (y.2 − x.2)(z.1 − y.1) = (z.2 − y.2)(y.1 − x.1)   (over ℚ)
  simp only [collinear₃, beq_iff_eq]
  have hgoal : (((y.1 : ℚ)) - ((x.1 : ℚ))) * (((z.2 : ℚ)) - ((x.2 : ℚ)))
      = (((z.1 : ℚ)) - ((x.1 : ℚ))) * (((y.2 : ℚ)) - ((x.2 : ℚ))) := by
    linear_combination -h
  exact_mod_cast hgoal

/-- **Junction transitivity** (the two-lines-through-two-points argument): if `b` lies
on chord `a–c` and `c` lies on chord `a–z`, then `z` lies on chord `b–c`'s line, i.e.
`collinear₃ b c z`.  Needs only `a.1 < c.1` for the cancellation. -/
lemma collinear₃_trans' {a b c z : ℕ × ℕ} (hac : a.1 < c.1)
    (h₁ : collinear₃ a b c = true) (h₂ : collinear₃ a c z = true) :
    collinear₃ b c z = true := by
  simp only [collinear₃, beq_iff_eq] at h₁ h₂ ⊢
  have hca : ((c.1 : ℤ) - (a.1 : ℤ)) ≠ 0 := by
    have : (a.1 : ℤ) < (c.1 : ℤ) := by exact_mod_cast hac
    omega
  refine mul_right_cancel₀ hca ?_
  linear_combination ((c.1 : ℤ) - (z.1 : ℤ)) * h₁ + ((c.1 : ℤ) - (b.1 : ℤ)) * h₂

/-- Affine domination transfers from the endpoints of a bracket to its interior. -/
lemma affine_le_on_Icc {A B C D : ℕ × ℕ} {a b x : ℚ} (hab : a < b)
    (hx₁ : a ≤ x) (hx₂ : x ≤ b)
    (h₁ : pairLine A B a ≤ pairLine C D a) (h₂ : pairLine A B b ≤ pairLine C D b) :
    pairLine A B x ≤ pairLine C D x := by
  have hinterp : ∀ (P R : ℕ × ℕ),
      pairLine P R x * (b - a) = pairLine P R a * (b - x) + pairLine P R b * (x - a) := by
    intro P R
    simp only [pairLine]
    ring
  have hba : (0 : ℚ) < b - a := by linarith
  have h1 := hinterp A B
  have h2 := hinterp C D
  nlinarith [mul_le_mul_of_nonneg_right h₁ (by linarith : (0:ℚ) ≤ b - x),
    mul_le_mul_of_nonneg_right h₂ (by linarith : (0:ℚ) ≤ x - a)]

/-! ## §D — the SURVIVOR-CORNER law

`dropCollinear` on a strictly-sorted list leaves no collinear consecutive triple: if
`(x, y)` and `(y, z)` are both consecutive pairs of the output, then `x, y, z` are NOT
collinear.  This is the converse companion of `dropCollinear_between` and the fact
that forces the truth of the repaired hull-invariance statement (a genuine vertex of
`S'` must be a genuine CORNER, so it cannot be dropped from the `S`-hull).  Falsifier:
0 violations / 4000 random sorted lists (unit record). -/

lemma dropCollinear_corner : ∀ (l : List (ℕ × ℕ)),
    (l.map Prod.fst).Pairwise (· < ·) →
    ∀ pq ∈ (dropCollinear l).zip (dropCollinear l).tail,
    ∀ qr ∈ (dropCollinear l).zip (dropCollinear l).tail,
    pq.2 = qr.1 → collinear₃ pq.1 qr.1 qr.2 = true → False
  | [], _, pq, hpq, _, _, _, _ => by simp [dropCollinear] at hpq
  | [a], _, pq, hpq, _, _, _, _ => by simp [dropCollinear] at hpq
  | [a, b], hs, pq, hpq, qr, hqr, hshare, hcol3 => by
      have hab : a.1 < b.1 := by
        rw [List.map_cons, List.pairwise_cons] at hs
        exact hs.1 b.1 (by simp)
      have hpq' : pq ∈ (a :: b :: ([] : List (ℕ × ℕ))).zip (b :: []) := hpq
      have hqr' : qr ∈ (a :: b :: ([] : List (ℕ × ℕ))).zip (b :: []) := hqr
      rw [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hpq' hqr'
      subst hpq'; subst hqr'
      have hba : b = a := hshare
      rw [hba] at hab
      exact absurd hab (lt_irrefl _)
  | a :: b :: c :: rest, hs, pq, hpq, qr, hqr, hshare, hcol3 => by
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
      have hab : a.1 < b.1 := hafst b.1 (by simp)
      have ih := dropCollinear_corner (b :: c :: rest) hs'
      rw [hu] at ih
      have husub' : ∀ x ∈ u, x ∈ c :: rest := fun x hx => husub.subset hx
      rw [dropCollinear_cons3, hu] at hpq hqr
      cases u with
      | nil =>
          have hpq2 : pq ∈ (a :: b :: ([] : List (ℕ × ℕ))).zip
              ((a :: b :: ([] : List (ℕ × ℕ))).tail) := hpq
          have hqr2 : qr ∈ (a :: b :: ([] : List (ℕ × ℕ))).zip
              ((a :: b :: ([] : List (ℕ × ℕ))).tail) := hqr
          rw [show (a :: b :: ([] : List (ℕ × ℕ))).tail = b :: [] from rfl,
            List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hpq2 hqr2
          subst hpq2; subst hqr2
          have hba : b = a := hshare
          rw [hba] at hab
          exact absurd hab (lt_irrefl _)
      | cons c' u' =>
          have hbc' : b.1 < c'.1 := hbfst c'.1
            (List.mem_map_of_mem (husub' c' List.mem_cons_self))
          have hac' : a.1 < c'.1 := lt_trans hab hbc'
          have hu'mem : ∀ x ∈ u', x ∈ c :: rest :=
            fun x hx => husub' x (List.mem_cons_of_mem c' hx)
          have hpq2 : pq ∈ ((if collinear₃ a b c' then a :: c' :: u'
              else a :: b :: c' :: u').zip
                ((if collinear₃ a b c' then a :: c' :: u'
                  else a :: b :: c' :: u').tail)) := hpq
          have hqr2 : qr ∈ ((if collinear₃ a b c' then a :: c' :: u'
              else a :: b :: c' :: u').zip
                ((if collinear₃ a b c' then a :: c' :: u'
                  else a :: b :: c' :: u').tail)) := hqr
          by_cases hcol : collinear₃ a b c'
          · rw [if_pos hcol] at hpq2 hqr2
            rw [show (a :: c' :: u').tail = c' :: u' from rfl,
              List.zip_cons_cons, List.mem_cons] at hpq2 hqr2
            rcases hpq2 with rfl | hpqDeep
            · rcases hqr2 with rfl | hqrDeep
              · -- pq = qr = (a, c'): shared middle forces c' = a
                have hca2 : c' = a := hshare
                rw [hca2] at hac'
                exact absurd hac' (lt_irrefl _)
              · -- pq = (a, c'), qr a deeper pair starting at c'
                have hqrK : qr ∈ (b :: c' :: u').zip ((b :: c' :: u').tail) := by
                  rw [show (b :: c' :: u').tail = c' :: u' from rfl,
                    List.zip_cons_cons]
                  exact List.mem_cons_of_mem _ hqrDeep
                have hbcK : ((b, c') : (ℕ × ℕ) × (ℕ × ℕ))
                    ∈ (b :: c' :: u').zip ((b :: c' :: u').tail) := by
                  rw [show (b :: c' :: u').tail = c' :: u' from rfl,
                    List.zip_cons_cons]
                  exact List.mem_cons_self
                have hshare' : c' = qr.1 := hshare
                have hcol3' : collinear₃ a c' qr.2 = true := by
                  rw [← hshare'] at hcol3
                  exact hcol3
                have htrans : collinear₃ b c' qr.2 = true :=
                  collinear₃_trans' hac' hcol hcol3'
                refine ih (b, c') hbcK qr hqrK hshare' ?_
                rw [← hshare']
                exact htrans
            · rcases hqr2 with rfl | hqrDeep
              · -- qr = (a, c') with pq deeper: pq.2 = a is impossible
                have hpq1 : pq.2 ∈ u' := (List.of_mem_zip hpqDeep).2
                have hlt := hbfst pq.2.1 (List.mem_map_of_mem (hu'mem pq.2 hpq1))
                have h' : pq.2 = a := hshare
                rw [h'] at hlt
                omega
              · -- both deep: both are pairs of the recursive output
                have hpqK : pq ∈ (b :: c' :: u').zip ((b :: c' :: u').tail) := by
                  rw [show (b :: c' :: u').tail = c' :: u' from rfl,
                    List.zip_cons_cons]
                  exact List.mem_cons_of_mem _ hpqDeep
                have hqrK : qr ∈ (b :: c' :: u').zip ((b :: c' :: u').tail) := by
                  rw [show (b :: c' :: u').tail = c' :: u' from rfl,
                    List.zip_cons_cons]
                  exact List.mem_cons_of_mem _ hqrDeep
                exact ih pq hpqK qr hqrK hshare hcol3
          · rw [if_neg hcol] at hpq2 hqr2
            rw [show (a :: b :: c' :: u').tail = b :: c' :: u' from rfl,
              List.zip_cons_cons, List.mem_cons] at hpq2 hqr2
            rcases hpq2 with rfl | hpqK
            · rcases hqr2 with rfl | hqrK
              · -- pq = qr = (a, b): shared middle forces b = a
                have hba : b = a := hshare
                rw [hba] at hab
                exact absurd hab (lt_irrefl _)
              · -- pq = (a, b), qr ∈ zip of the kept tail: qr.1 = b forces qr = (b, c')
                have hqrK2 : qr ∈ ((b, c') : (ℕ × ℕ) × (ℕ × ℕ))
                    :: (c' :: u').zip u' := by
                  rw [show (c' :: u') = (b :: c' :: u').tail from rfl,
                    ← List.zip_cons_cons]
                  exact hqrK
                rcases List.mem_cons.mp hqrK2 with rfl | hqrDeep
                · -- qr = (b, c'): the triple (a, b, c') is the non-collinear branch
                  exact hcol (by
                    have hcol3' : collinear₃ a b c' = true := hcol3
                    exact hcol3')
                · -- qr deeper: qr.1 ∈ c' :: u' has abscissa > b.1 = qr.1.1
                  have hqr1 : qr.1 ∈ c' :: u' := (List.of_mem_zip hqrDeep).1
                  have hgt : b.1 < qr.1.1 := by
                    rcases List.mem_cons.mp hqr1 with rfl' | hqr1'
                    · rw [rfl']
                      exact hbc'
                    · exact hbfst qr.1.1 (List.mem_map_of_mem (hu'mem qr.1 hqr1'))
                  have h' : b = qr.1 := hshare
                  rw [← h'] at hgt
                  exact absurd hgt (lt_irrefl _)
            · rcases hqr2 with rfl | hqrK
              · -- qr = (a, b), pq deep: pq.2 = a impossible
                have hpq1 : pq.2 ∈ c' :: u' := (List.of_mem_zip hpqK).2
                have hgt : b.1 < pq.2.1 := by
                  rcases List.mem_cons.mp hpq1 with h | hpq1'
                  · rw [h]
                    exact hbc'
                  · exact hbfst pq.2.1 (List.mem_map_of_mem (hu'mem pq.2 hpq1'))
                have h' : pq.2 = a := hshare
                rw [h'] at hgt
                omega
              · -- both are pairs of the kept tail
                have hpqK' : pq ∈ (b :: c' :: u').zip ((b :: c' :: u').tail) := hpqK
                have hqrK' : qr ∈ (b :: c' :: u').zip ((b :: c' :: u').tail) := hqrK
                exact ih pq hpqK' qr hqrK' hshare hcol3

/-! ## §E — hull kernels -/

variable (S : Finset (ℕ × ℕ))

/-- Every full vertex is a support dot (local copy of `Classifier.npVerticesFull_mem`,
which cannot be imported here — `Classifier` is downstream). -/
lemma full_mem (hS : S.Nonempty) {P : ℕ × ℕ}
    (hP : P ∈ npVerticesFull S hS) : P ∈ S := by
  unfold npVerticesFull at hP
  rw [List.mem_map] at hP
  obtain ⟨i, hi, hPi⟩ := hP
  rw [mem_hullAbscissae_iff] at hi
  obtain ⟨v, hiv, hon⟩ := hi
  have hd : hullDotAt S hS i = (i, v) := by
    unfold hullDotAt
    rw [hullHeightAt_of_onHull S hS hiv hon]
  rw [hd] at hPi
  rw [← hPi]
  exact hiv

/-- Every genuine vertex is a support dot. -/
lemma vert_mem (hS : S.Nonempty) {P : ℕ × ℕ}
    (hP : P ∈ npVertices S hS) : P ∈ S :=
  full_mem S hS ((dropCollinear_sublist _).subset hP)

/-- The right endpoint of a valid line with distinct abscissae is ON the hull. -/
lemma valid_right_on_hull (hS : S.Nonempty) {A B : ℕ × ℕ}
    (hval : (A, B) ∈ validLines S) (hne : ((A.1 : ℚ)) ≠ ((B.1 : ℚ))) :
    (B.2 : ℚ) = npHeight S hS ((B.1 : ℚ)) := by
  have hBS : B ∈ S := validLines_mem_right S hval
  refine le_antisymm ?_ (npHeight_le S hS (show (B.1, B.2) ∈ S by simpa using hBS))
  calc (B.2 : ℚ) = pairLine A B ((B.1 : ℚ)) := (pairLine_right A B hne).symm
    _ ≤ npHeight S hS ((B.1 : ℚ)) :=
        Finset.le_sup' (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 ((B.1 : ℚ))) hval

/-- **Slope monotonicity at a hull dot**: chords from the left into a hull dot are no
steeper than chords out of it to the right. -/
lemma hull_slope_mono (hS : S.Nonempty) {Q A R : ℕ × ℕ} (hQ : Q ∈ S) (hR : R ∈ S)
    (hA : (A.2 : ℚ) = npHeight S hS ((A.1 : ℚ))) (hQA : Q.1 < A.1) (hAR : A.1 < R.1) :
    pairSlope Q A ≤ pairSlope A R := by
  have hQA' : ((Q.1 : ℚ)) < ((A.1 : ℚ)) := by exact_mod_cast hQA
  have hAR' : ((A.1 : ℚ)) < ((R.1 : ℚ)) := by exact_mod_cast hAR
  have hgQ : npHeight S hS ((Q.1 : ℚ)) ≤ (Q.2 : ℚ) :=
    npHeight_le S hS (show (Q.1, Q.2) ∈ S by simpa using hQ)
  have hgR : npHeight S hS ((R.1 : ℚ)) ≤ (R.2 : ℚ) :=
    npHeight_le S hS (show (R.1, R.2) ∈ S by simpa using hR)
  have hslope := (npHeight_convexOn S hS ((R.1 : ℚ))).slope_mono_adjacent
    (x := ((Q.1 : ℚ))) (y := ((A.1 : ℚ))) (z := ((R.1 : ℚ)))
    ⟨Nat.cast_nonneg _, by linarith⟩ ⟨Nat.cast_nonneg _, le_refl _⟩ hQA' hAR'
  rw [← hA] at hslope
  have haq : (0 : ℚ) < ((A.1 : ℚ)) - ((Q.1 : ℚ)) := by linarith
  have hra : (0 : ℚ) < ((R.1 : ℚ)) - ((A.1 : ℚ)) := by linarith
  rw [div_le_div_iff₀ haq hra] at hslope
  rw [pairSlope, pairSlope, div_le_div_iff₀ haq hra]
  have hm1 := mul_le_mul_of_nonneg_right
    (sub_le_sub_left hgQ ((A.2 : ℚ))) (le_of_lt hra)
  have hm2 := mul_le_mul_of_nonneg_right
    (sub_le_sub_right hgR ((A.2 : ℚ))) (le_of_lt haq)
  linarith [hslope, hm1, hm2]

/-- **The minimal abscissa is a hull abscissa** (leftmost pin): the lowest dot at the
minimal abscissa is on the hull, witnessed by its flattest rightward chord (or the
horizontal diagonal when no dot lies to the right). -/
lemma mem_hullAbscissae_min (hS : S.Nonempty) {m : ℕ}
    (hlb : ∀ P ∈ S, m ≤ P.1) (hmem : ∃ v, (m, v) ∈ S) :
    m ∈ hullAbscissae S hS := by
  classical
  obtain ⟨v1, hv1⟩ := hmem
  have hTne : (S.filter (fun P => P.1 = m)).Nonempty :=
    ⟨(m, v1), Finset.mem_filter.2 ⟨hv1, rfl⟩⟩
  obtain ⟨A, hAT, hAmin⟩ :=
    (S.filter (fun P => P.1 = m)).exists_min_image (fun P => P.2) hTne
  have hAS : A ∈ S := (Finset.mem_filter.mp hAT).1
  have hA1 : A.1 = m := (Finset.mem_filter.mp hAT).2
  have hup : npHeight S hS ((m : ℚ)) ≤ (A.2 : ℚ) := by
    have := npHeight_le S hS (show (A.1, A.2) ∈ S by simpa using hAS)
    rwa [hA1] at this
  have hdown : (A.2 : ℚ) ≤ npHeight S hS ((m : ℚ)) := by
    rcases (S.filter (fun P => m < P.1)).eq_empty_or_nonempty with hT | hTne'
    · -- all dots at abscissa m: the horizontal diagonal through A is valid
      have hval : ((A, A) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ validLines S := by
        rw [validLines, Finset.mem_filter]
        refine ⟨Finset.mem_product.2 ⟨hAS, hAS⟩, ?_⟩
        intro Q hQ
        have hQ1 : Q.1 = m := by
          have h1 := hlb Q hQ
          by_contra hne
          have : Q ∈ S.filter (fun P => m < P.1) :=
            Finset.mem_filter.2 ⟨hQ, by omega⟩
          rw [hT] at this
          exact absurd this (Finset.notMem_empty _)
        have hQ2 : A.2 ≤ Q.2 := hAmin Q (Finset.mem_filter.2 ⟨hQ, hQ1⟩)
        change pairLine A A ((Q.1 : ℚ)) ≤ (Q.2 : ℚ)
        rw [show A = (A.1, A.2) from rfl, pairLine_diag_const]
        exact_mod_cast hQ2
      have hle := Finset.le_sup'
        (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 ((m : ℚ))) hval
      calc (A.2 : ℚ) = pairLine A A ((m : ℚ)) := by
            rw [show A = (A.1, A.2) from rfl, pairLine_diag_const]
        _ ≤ npHeight S hS ((m : ℚ)) := hle
    · -- flattest rightward chord out of A
      obtain ⟨Qm, hQmT, hQmmin⟩ :=
        (S.filter (fun P => m < P.1)).exists_min_image
          (fun Q => pairSlope A Q) hTne'
      have hQmS : Qm ∈ S := (Finset.mem_filter.mp hQmT).1
      have hmQm : m < Qm.1 := by
        have := (Finset.mem_filter.mp hQmT).2
        simpa using this
      have hval : ((A, Qm) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ validLines S := by
        rw [validLines, Finset.mem_filter]
        refine ⟨Finset.mem_product.2 ⟨hAS, hQmS⟩, ?_⟩
        intro Q hQ
        change pairLine A Qm ((Q.1 : ℚ)) ≤ (Q.2 : ℚ)
        rcases Nat.lt_or_ge m Q.1 with hQgt | hQle
        · have hle := hQmmin Q (Finset.mem_filter.2 ⟨hQ, hQgt⟩)
          have hQA' : ((A.1 : ℚ)) < ((Q.1 : ℚ)) := by
            rw [hA1]; exact_mod_cast hQgt
          have hne : ((Q.1 : ℚ)) - ((A.1 : ℚ)) ≠ 0 := by
            intro h0; linarith
          have hkey : (A.2 : ℚ) + pairSlope A Q * (((Q.1 : ℚ)) - ((A.1 : ℚ)))
              = (Q.2 : ℚ) := by
            rw [pairSlope]
            field_simp
            ring
          have hmul := mul_le_mul_of_nonneg_right hle (by linarith :
            (0 : ℚ) ≤ ((Q.1 : ℚ)) - ((A.1 : ℚ)))
          rw [pairLine]
          linarith
        · have hQ1 : Q.1 = m := le_antisymm hQle (hlb Q hQ)
          have hQ1' : ((Q.1 : ℚ)) = ((A.1 : ℚ)) := by
            rw [hQ1, hA1]
          rw [hQ1', pairLine_left]
          exact_mod_cast hAmin Q (Finset.mem_filter.2 ⟨hQ, hQ1⟩)
      have hle := Finset.le_sup'
        (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 ((m : ℚ))) hval
      have hatm : pairLine A Qm ((m : ℚ)) = (A.2 : ℚ) := by
        have : ((m : ℚ)) = ((A.1 : ℚ)) := by rw [hA1]
        rw [this, pairLine_left]
      rw [← hatm]
      exact hle
  have honA : ((A.2 : ℕ) : ℚ) = npHeight S hS ((m : ℚ)) := le_antisymm hdown hup
  rw [mem_hullAbscissae_iff]
  exact ⟨A.2, by rw [← hA1]; simpa using hAS, honA⟩

/-- **The maximal abscissa is a hull abscissa** (rightmost pin): mirror of
`mem_hullAbscissae_min` via the steepest leftward chord. -/
lemma mem_hullAbscissae_max (hS : S.Nonempty) {M : ℕ}
    (hub : ∀ P ∈ S, P.1 ≤ M) (hmem : ∃ v, (M, v) ∈ S) :
    M ∈ hullAbscissae S hS := by
  classical
  obtain ⟨v1, hv1⟩ := hmem
  have hTne : (S.filter (fun P => P.1 = M)).Nonempty :=
    ⟨(M, v1), Finset.mem_filter.2 ⟨hv1, rfl⟩⟩
  obtain ⟨A, hAT, hAmin⟩ :=
    (S.filter (fun P => P.1 = M)).exists_min_image (fun P => P.2) hTne
  have hAS : A ∈ S := (Finset.mem_filter.mp hAT).1
  have hA1 : A.1 = M := (Finset.mem_filter.mp hAT).2
  have hup : npHeight S hS ((M : ℚ)) ≤ (A.2 : ℚ) := by
    have := npHeight_le S hS (show (A.1, A.2) ∈ S by simpa using hAS)
    rwa [hA1] at this
  have hdown : (A.2 : ℚ) ≤ npHeight S hS ((M : ℚ)) := by
    rcases (S.filter (fun P => P.1 < M)).eq_empty_or_nonempty with hT | hTne'
    · have hval : ((A, A) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ validLines S := by
        rw [validLines, Finset.mem_filter]
        refine ⟨Finset.mem_product.2 ⟨hAS, hAS⟩, ?_⟩
        intro Q hQ
        have hQ1 : Q.1 = M := by
          have h1 := hub Q hQ
          by_contra hne
          have : Q ∈ S.filter (fun P => P.1 < M) :=
            Finset.mem_filter.2 ⟨hQ, by omega⟩
          rw [hT] at this
          exact absurd this (Finset.notMem_empty _)
        have hQ2 : A.2 ≤ Q.2 := hAmin Q (Finset.mem_filter.2 ⟨hQ, hQ1⟩)
        change pairLine A A ((Q.1 : ℚ)) ≤ (Q.2 : ℚ)
        rw [show A = (A.1, A.2) from rfl, pairLine_diag_const]
        exact_mod_cast hQ2
      have hle := Finset.le_sup'
        (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 ((M : ℚ))) hval
      calc (A.2 : ℚ) = pairLine A A ((M : ℚ)) := by
            rw [show A = (A.1, A.2) from rfl, pairLine_diag_const]
        _ ≤ npHeight S hS ((M : ℚ)) := hle
    · -- steepest leftward chord into A
      obtain ⟨Qm, hQmT, hQmmax⟩ :=
        (S.filter (fun P => P.1 < M)).exists_max_image
          (fun Q => pairSlope Q A) hTne'
      have hQmS : Qm ∈ S := (Finset.mem_filter.mp hQmT).1
      have hQmM : Qm.1 < M := by
        have := (Finset.mem_filter.mp hQmT).2
        simpa using this
      have hQmA : ((Qm.1 : ℚ)) ≠ ((A.1 : ℚ)) := by
        rw [hA1]
        have : ((Qm.1 : ℚ)) < ((M : ℚ)) := by exact_mod_cast hQmM
        exact ne_of_lt this
      have hval : ((Qm, A) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ validLines S := by
        rw [validLines, Finset.mem_filter]
        refine ⟨Finset.mem_product.2 ⟨hQmS, hAS⟩, ?_⟩
        intro Q hQ
        change pairLine Qm A ((Q.1 : ℚ)) ≤ (Q.2 : ℚ)
        rw [pairLine_right_form Qm A hQmA]
        rcases Nat.lt_or_ge Q.1 M with hQlt | hQge
        · have hge := hQmmax Q (Finset.mem_filter.2 ⟨hQ, hQlt⟩)
          have hQA' : ((Q.1 : ℚ)) < ((A.1 : ℚ)) := by
            rw [hA1]; exact_mod_cast hQlt
          have hne : ((A.1 : ℚ)) - ((Q.1 : ℚ)) ≠ 0 := by
            intro h0; linarith
          have hkey : (A.2 : ℚ) + pairSlope Q A * (((Q.1 : ℚ)) - ((A.1 : ℚ)))
              = (Q.2 : ℚ) := by
            rw [pairSlope]
            field_simp
            ring
          have hmul := mul_le_mul_of_nonpos_right hge (by linarith :
            ((Q.1 : ℚ)) - ((A.1 : ℚ)) ≤ 0)
          linarith
        · have hQ1 : Q.1 = M := le_antisymm (hub Q hQ) hQge
          have hQ1' : ((Q.1 : ℚ)) = ((A.1 : ℚ)) := by
            rw [hQ1, hA1]
          rw [hQ1']
          simp only [sub_self, mul_zero, add_zero]
          exact_mod_cast hAmin Q (Finset.mem_filter.2 ⟨hQ, hQ1⟩)
      have hle := Finset.le_sup'
        (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 ((M : ℚ))) hval
      have hatM : pairLine Qm A ((M : ℚ)) = (A.2 : ℚ) := by
        have : ((M : ℚ)) = ((A.1 : ℚ)) := by rw [hA1]
        rw [this, pairLine_right Qm A hQmA]
      rw [← hatM]
      exact hle
  have honA : ((A.2 : ℕ) : ℚ) = npHeight S hS ((M : ℚ)) := le_antisymm hdown hup
  rw [mem_hullAbscissae_iff]
  exact ⟨A.2, by rw [← hA1]; simpa using hAS, honA⟩

/-- **Consecutive full vertices span a VALID chord** (the flattest-chord transfer).
The heart: the flattest chord out of the left endpoint is valid, its right endpoint is
a hull dot, which cannot lie strictly between consecutive hull abscissae — so the
chord to the NEXT full vertex rides the same line. -/
lemma full_zip_valid (hS : S.Nonempty) {A B : ℕ × ℕ}
    (hpr : ((A, B) : (ℕ × ℕ) × (ℕ × ℕ))
      ∈ (npVerticesFull S hS).zip (npVerticesFull S hS).tail) :
    ((A, B) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ validLines S := by
  classical
  have hAF : A ∈ npVerticesFull S hS := (List.of_mem_zip hpr).1
  have hBF : B ∈ npVerticesFull S hS := List.mem_of_mem_tail (List.of_mem_zip hpr).2
  have hAS : A ∈ S := full_mem S hS hAF
  have hBS : B ∈ S := full_mem S hS hBF
  have hAhull : (A.2 : ℚ) = npHeight S hS ((A.1 : ℚ)) := npVerticesFull_on_hull S hS hAF
  have hBhull : (B.2 : ℚ) = npHeight S hS ((B.1 : ℚ)) := npVerticesFull_on_hull S hS hBF
  have hsortF := npVerticesFull_sorted S hS
  have hAB : A.1 < B.1 := zip_fst_lt _ hsortF (A, B) hpr
  have hsortabs : (hullAbscissae S hS).Pairwise (· < ·) := by
    have := npVerticesFull_sorted S hS
    rwa [npVerticesFull_fst S hS] at this
  have hpairabs := zip_pair_map_fst hpr
  rw [npVerticesFull_fst S hS] at hpairabs
  have hnomid : ∀ c ∈ hullAbscissae S hS, A.1 < c → c < B.1 → False :=
    fun c hc h1 h2 => no_between_nat _ hsortabs _ hpairabs c hc h1 h2
  have hTne : (S.filter (fun Q => A.1 < Q.1)).Nonempty :=
    ⟨B, Finset.mem_filter.2 ⟨hBS, hAB⟩⟩
  obtain ⟨Qm, hQmT, hQmmin⟩ :=
    (S.filter (fun Q => A.1 < Q.1)).exists_min_image (fun Q => pairSlope A Q) hTne
  have hQmS : Qm ∈ S := (Finset.mem_filter.mp hQmT).1
  have hAQm : A.1 < Qm.1 := by
    have := (Finset.mem_filter.mp hQmT).2
    simpa using this
  have hAQm' : ((A.1 : ℚ)) < ((Qm.1 : ℚ)) := by exact_mod_cast hAQm
  have hval : ((A, Qm) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ validLines S := by
    rw [validLines, Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨hAS, hQmS⟩, ?_⟩
    intro Q hQ
    change pairLine A Qm ((Q.1 : ℚ)) ≤ (Q.2 : ℚ)
    rcases Nat.lt_trichotomy Q.1 A.1 with hQA | hQA | hQA
    · have hsl : pairSlope Q A ≤ pairSlope A Qm :=
        hull_slope_mono S hS hQ hQmS hAhull hQA hAQm
      have hQA' : ((Q.1 : ℚ)) < ((A.1 : ℚ)) := by exact_mod_cast hQA
      have hne : ((A.1 : ℚ)) - ((Q.1 : ℚ)) ≠ 0 := by intro h0; linarith
      have hkey : (A.2 : ℚ) + pairSlope Q A * (((Q.1 : ℚ)) - ((A.1 : ℚ)))
          = (Q.2 : ℚ) := by
        rw [pairSlope]
        field_simp
        ring
      have hmul := mul_le_mul_of_nonpos_right hsl (by linarith :
        ((Q.1 : ℚ)) - ((A.1 : ℚ)) ≤ 0)
      rw [pairLine]
      linarith
    · have hQ1' : ((Q.1 : ℚ)) = ((A.1 : ℚ)) := by exact_mod_cast hQA
      rw [hQ1', pairLine_left]
      have hgQ : npHeight S hS ((Q.1 : ℚ)) ≤ (Q.2 : ℚ) :=
        npHeight_le S hS (show (Q.1, Q.2) ∈ S by simpa using hQ)
      rw [hQ1'] at hgQ
      rw [hAhull]
      exact hgQ
    · have hle := hQmmin Q (Finset.mem_filter.2 ⟨hQ, hQA⟩)
      have hQA' : ((A.1 : ℚ)) < ((Q.1 : ℚ)) := by exact_mod_cast hQA
      have hne : ((Q.1 : ℚ)) - ((A.1 : ℚ)) ≠ 0 := by intro h0; linarith
      have hkey : (A.2 : ℚ) + pairSlope A Q * (((Q.1 : ℚ)) - ((A.1 : ℚ)))
          = (Q.2 : ℚ) := by
        rw [pairSlope]
        field_simp
        ring
      have hmul := mul_le_mul_of_nonneg_right hle (by linarith :
        (0 : ℚ) ≤ ((Q.1 : ℚ)) - ((A.1 : ℚ)))
      rw [pairLine]
      linarith
  have hQmhull : (Qm.2 : ℚ) = npHeight S hS ((Qm.1 : ℚ)) :=
    valid_right_on_hull S hS hval (ne_of_lt hAQm')
  have hQmabs : Qm.1 ∈ hullAbscissae S hS :=
    (mem_hullAbscissae_iff S hS).mpr ⟨Qm.2, by simpa using hQmS, hQmhull⟩
  have hBQm : B.1 ≤ Qm.1 := by
    by_contra hlt
    push_neg at hlt
    exact hnomid Qm.1 hQmabs hAQm hlt
  have hattain : npHeight S hS ((B.1 : ℚ)) = pairLine A Qm ((B.1 : ℚ)) :=
    npHeight_eq_pairLine_of_validLine S hS hval
      ⟨by exact_mod_cast le_of_lt hAB, by exact_mod_cast hBQm⟩
  have hBon : (B.2 : ℚ) = pairLine A Qm ((B.1 : ℚ)) := by
    rw [hBhull]
    exact hattain
  have hlines := pairLine_eq_of_through hAB hBon
  rw [validLines, Finset.mem_filter]
  refine ⟨Finset.mem_product.2 ⟨hAS, hBS⟩, ?_⟩
  intro Q hQ
  change pairLine A B ((Q.1 : ℚ)) ≤ (Q.2 : ℚ)
  rw [hlines]
  exact (Finset.mem_filter.mp hval).2 Q hQ

/-- Chord attainment on consecutive FULL vertices. -/
lemma full_zip_attain (hS : S.Nonempty) {A B : ℕ × ℕ}
    (hpr : ((A, B) : (ℕ × ℕ) × (ℕ × ℕ))
      ∈ (npVerticesFull S hS).zip (npVerticesFull S hS).tail)
    {x : ℚ} (hx1 : ((A.1 : ℚ)) ≤ x) (hx2 : x ≤ ((B.1 : ℚ))) :
    npHeight S hS x = pairLine A B x :=
  npHeight_eq_pairLine_of_validLine S hS (full_zip_valid S hS hpr) ⟨hx1, hx2⟩

/-- The glue induction: chord attainment transfers from consecutive full vertices to
consecutive GENUINE vertices (every full vertex between two consecutive survivors is
collinear with them — `dropCollinear_between` — so the per-full-bracket chords all
ride the survivors' chord). -/
lemma glue_aux (hS : S.Nonempty) {A B : ℕ × ℕ}
    (hzipD : ((A, B) : (ℕ × ℕ) × (ℕ × ℕ))
      ∈ (npVertices S hS).zip (npVertices S hS).tail) (hAB : A.1 < B.1) :
    ∀ (k : ℕ) (C : ℕ × ℕ), C ∈ npVerticesFull S hS → A.1 ≤ C.1 → C.1 < B.1 →
      pairLine A B ((C.1 : ℚ)) = (C.2 : ℚ) → B.1 - C.1 ≤ k →
      ∀ x : ℚ, ((C.1 : ℚ)) ≤ x → x ≤ ((B.1 : ℚ)) → npHeight S hS x = pairLine A B x := by
  have hzipDC : ((A, B) : (ℕ × ℕ) × (ℕ × ℕ))
      ∈ (dropCollinear (npVerticesFull S hS)).zip
        (dropCollinear (npVerticesFull S hS)).tail := hzipD
  have hsortF := npVerticesFull_sorted S hS
  have hBD : B ∈ npVertices S hS := List.mem_of_mem_tail (List.of_mem_zip hzipD).2
  have hBF : B ∈ npVerticesFull S hS := (dropCollinear_sublist _).subset hBD
  intro k
  induction k with
  | zero =>
      intro C _ _ hCB _ hk
      exact absurd hk (by omega)
  | succ k ih =>
      intro C hCF hAC hCB hCon hk x hx1 hx2
      have hlastne : (npVerticesFull S hS).getLast? ≠ some C := by
        intro hlast
        have := sorted_le_getLast? hsortF hlast B hBF
        omega
      obtain ⟨D, hCD⟩ := exists_zip_right _ hCF hlastne
      have hCDlt : C.1 < D.1 := zip_fst_lt _ hsortF (C, D) hCD
      have hDF : D ∈ npVerticesFull S hS :=
        List.mem_of_mem_tail (List.of_mem_zip hCD).2
      have hDB : D.1 ≤ B.1 := by
        by_contra hgt
        push_neg at hgt
        have hpairabs := zip_pair_map_fst hCD
        rw [npVerticesFull_fst S hS] at hpairabs
        have hsortabs : (hullAbscissae S hS).Pairwise (· < ·) := by
          have := npVerticesFull_sorted S hS
          rwa [npVerticesFull_fst S hS] at this
        have hBabs : B.1 ∈ hullAbscissae S hS := by
          rw [← npVerticesFull_fst S hS]
          exact List.mem_map_of_mem hBF
        exact no_between_nat _ hsortabs _ hpairabs B.1 hBabs hCB hgt
      have hABne : ((A.1 : ℚ)) ≠ ((B.1 : ℚ)) := by
        have : ((A.1 : ℚ)) < ((B.1 : ℚ)) := by exact_mod_cast hAB
        exact ne_of_lt this
      have hDon : pairLine A B ((D.1 : ℚ)) = (D.2 : ℚ) := by
        rcases eq_or_lt_of_le hDB with heq | hlt
        · have hDBeq : D = B := fst_inj_of_sorted hsortF D hDF B hBF heq
          rw [hDBeq]
          exact pairLine_right A B hABne
        · have hADlt : A.1 < D.1 := lt_of_le_of_lt hAC hCDlt
          have hcol : collinear₃ A D B = true :=
            dropCollinear_between (npVerticesFull S hS) hsortF (A, B) hzipDC
              D hDF hADlt hlt
          exact pairLine_eq_of_collinear₃ hcol hAB
      have hCDne : ((C.1 : ℚ)) ≠ ((D.1 : ℚ)) := by
        have : ((C.1 : ℚ)) < ((D.1 : ℚ)) := by exact_mod_cast hCDlt
        exact ne_of_lt this
      have hCon' : pairLine C D ((C.1 : ℚ)) = pairLine A B ((C.1 : ℚ)) := by
        rw [pairLine_left, hCon]
      have hDon' : pairLine C D ((D.1 : ℚ)) = pairLine A B ((D.1 : ℚ)) := by
        rw [pairLine_right C D hCDne, hDon]
      have hlineseq := pairLine_eq_of_eval₂ hCDne hCon' hDon'
      by_cases hxD : x ≤ ((D.1 : ℚ))
      · have hattain := full_zip_attain S hS hCD hx1 hxD
        rw [hattain]
        exact hlineseq x
      · push_neg at hxD
        have hDB' : D.1 < B.1 := by
          rcases eq_or_lt_of_le hDB with heq | hlt
          · exfalso
            have : ((D.1 : ℚ)) = ((B.1 : ℚ)) := by exact_mod_cast heq
            rw [this] at hxD
            linarith
          · exact hlt
        exact ih D hDF (le_of_lt (lt_of_le_of_lt hAC hCDlt)) hDB' hDon
          (by omega) x (le_of_lt hxD) hx2

/-- **Chord attainment on consecutive GENUINE vertices.** -/
lemma vert_zip_attain (hS : S.Nonempty) {A B : ℕ × ℕ}
    (hpr : ((A, B) : (ℕ × ℕ) × (ℕ × ℕ))
      ∈ (npVertices S hS).zip (npVertices S hS).tail)
    {x : ℚ} (hx1 : ((A.1 : ℚ)) ≤ x) (hx2 : x ≤ ((B.1 : ℚ))) :
    npHeight S hS x = pairLine A B x := by
  have hAB : A.1 < B.1 := zip_fst_lt _ (npVertices_sorted S hS) (A, B) hpr
  have hAD : A ∈ npVertices S hS := (List.of_mem_zip hpr).1
  have hAF : A ∈ npVerticesFull S hS := (dropCollinear_sublist _).subset hAD
  exact glue_aux S hS hpr hAB B.1 A hAF (le_refl _) hAB (pairLine_left A B)
    (by omega) x hx1 hx2

/-- Chord validity from on-hull endpoints + chord-dominated interior (the
`consecutive_chord_valid` engine with the empty-interior hypothesis generalized to
chord domination). -/
lemma chord_valid_of_between_le (hS : S.Nonempty)
    {A B : ℕ × ℕ} (hAmem : A ∈ S) (hBmem : B ∈ S)
    (hA : OnHull S hS A) (hB : OnHull S hS B) (hAB : A.1 < B.1)
    (hmid : ∀ C ∈ S, A.1 < C.1 → C.1 < B.1 → pairLine A B ((C.1 : ℚ)) ≤ (C.2 : ℚ)) :
    (A, B) ∈ validLines S := by
  rw [validLines, Finset.mem_filter]
  refine ⟨Finset.mem_product.2 ⟨hAmem, hBmem⟩, ?_⟩
  intro Q hQ
  change pairLine A B ((Q.1 : ℚ)) ≤ ((Q.2 : ℚ))
  have hgA : npHeight S hS ((A.1 : ℚ)) = (A.2 : ℚ) := Eq.symm hA
  have hgB : npHeight S hS ((B.1 : ℚ)) = (B.2 : ℚ) := Eq.symm hB
  have hgQ : npHeight S hS ((Q.1 : ℚ)) ≤ (Q.2 : ℚ) :=
    npHeight_le S hS (show (Q.1, Q.2) ∈ S by simpa using hQ)
  have hab : ((A.1 : ℚ)) < ((B.1 : ℚ)) := by exact_mod_cast hAB
  have hba : (0 : ℚ) < ((B.1 : ℚ)) - ((A.1 : ℚ)) := by linarith
  have hexp : pairLine A B ((Q.1 : ℚ))
      = (A.2 : ℚ) + ((B.2 : ℚ) - (A.2 : ℚ)) * (((Q.1 : ℚ)) - ((A.1 : ℚ)))
        / (((B.1 : ℚ)) - ((A.1 : ℚ))) := by
    simp only [pairLine, pairSlope]
    ring
  have hred : ((B.2 : ℚ) - (A.2 : ℚ)) * (((Q.1 : ℚ)) - ((A.1 : ℚ)))
        ≤ (((Q.2 : ℚ)) - (A.2 : ℚ)) * (((B.1 : ℚ)) - ((A.1 : ℚ))) →
      pairLine A B ((Q.1 : ℚ)) ≤ ((Q.2 : ℚ)) := by
    intro hcross
    have h2 : ((B.2 : ℚ) - (A.2 : ℚ)) * (((Q.1 : ℚ)) - ((A.1 : ℚ)))
        / (((B.1 : ℚ)) - ((A.1 : ℚ))) ≤ ((Q.2 : ℚ)) - (A.2 : ℚ) := by
      rw [div_le_iff₀ hba]
      exact hcross
    rw [hexp]
    linarith
  rcases Nat.lt_trichotomy Q.1 A.1 with hqa | hqa | hqa
  · have hqa' : ((Q.1 : ℚ)) < ((A.1 : ℚ)) := by exact_mod_cast hqa
    have haq : (0 : ℚ) < ((A.1 : ℚ)) - ((Q.1 : ℚ)) := by linarith
    have hslope := (npHeight_convexOn S hS ((B.1 : ℚ))).slope_mono_adjacent
      (x := ((Q.1 : ℚ))) (y := ((A.1 : ℚ))) (z := ((B.1 : ℚ)))
      ⟨Nat.cast_nonneg _, by linarith⟩ ⟨Nat.cast_nonneg _, le_refl _⟩ hqa' hab
    rw [hgA, hgB, div_le_div_iff₀ haq hba] at hslope
    refine hred ?_
    have hmul : (npHeight S hS ((Q.1 : ℚ)) - (A.2 : ℚ)) * (((B.1 : ℚ)) - ((A.1 : ℚ)))
        ≤ (((Q.2 : ℚ)) - (A.2 : ℚ)) * (((B.1 : ℚ)) - ((A.1 : ℚ))) :=
      mul_le_mul_of_nonneg_right (by linarith) hba.le
    nlinarith [hslope, hmul]
  · have hq : ((Q.1 : ℚ)) = ((A.1 : ℚ)) := by exact_mod_cast hqa
    rw [hq, pairLine_left]
    rw [hq, hgA] at hgQ
    exact hgQ
  · rcases Nat.lt_trichotomy Q.1 B.1 with hqb | hqb | hqb
    · exact hmid Q hQ hqa hqb
    · have hq : ((Q.1 : ℚ)) = ((B.1 : ℚ)) := by exact_mod_cast hqb
      rw [hq, pairLine_right A B (ne_of_lt hab)]
      rw [hq, hgB] at hgQ
      exact hgQ
    · have hqb' : ((B.1 : ℚ)) < ((Q.1 : ℚ)) := by exact_mod_cast hqb
      have hbq : (0 : ℚ) < ((Q.1 : ℚ)) - ((B.1 : ℚ)) := by linarith
      have hslope := (npHeight_convexOn S hS ((Q.1 : ℚ))).slope_mono_adjacent
        (x := ((A.1 : ℚ))) (y := ((B.1 : ℚ))) (z := ((Q.1 : ℚ)))
        ⟨Nat.cast_nonneg _, by linarith⟩ ⟨Nat.cast_nonneg _, le_refl _⟩ hab hqb'
      rw [hgA, hgB, div_le_div_iff₀ hba hbq] at hslope
      refine hred ?_
      have hmul : (npHeight S hS ((Q.1 : ℚ)) - (A.2 : ℚ)) * (((B.1 : ℚ)) - ((A.1 : ℚ)))
          ≤ (((Q.2 : ℚ)) - (A.2 : ℚ)) * (((B.1 : ℚ)) - ((A.1 : ℚ))) :=
        mul_le_mul_of_nonneg_right (by linarith) hba.le
      nlinarith [hslope, hmul]

/-- **Consecutive genuine vertices span a VALID chord.** -/
lemma vert_zip_valid (hS : S.Nonempty) {A B : ℕ × ℕ}
    (hpr : ((A, B) : (ℕ × ℕ) × (ℕ × ℕ))
      ∈ (npVertices S hS).zip (npVertices S hS).tail) :
    (A, B) ∈ validLines S := by
  have hAD : A ∈ npVertices S hS := (List.of_mem_zip hpr).1
  have hBD : B ∈ npVertices S hS := List.mem_of_mem_tail (List.of_mem_zip hpr).2
  have hAB : A.1 < B.1 := zip_fst_lt _ (npVertices_sorted S hS) (A, B) hpr
  refine chord_valid_of_between_le S hS (vert_mem S hS hAD) (vert_mem S hS hBD)
    (npVertices_on_hull S hS hAD) (npVertices_on_hull S hS hBD) hAB ?_
  intro C hC h1 h2
  have h1' : ((A.1 : ℚ)) ≤ ((C.1 : ℚ)) := by exact_mod_cast le_of_lt h1
  have h2' : ((C.1 : ℚ)) ≤ ((B.1 : ℚ)) := by exact_mod_cast le_of_lt h2
  have hattain := vert_zip_attain S hS hpr h1' h2'
  rw [← hattain]
  exact npHeight_le S hS (show (C.1, C.2) ∈ S by simpa using hC)

/-! ## §F — the master assembly -/

/-- **The repaired hull-invariance law** (the `Classifier` banked-sorry contract, proved).
If every genuine vertex of `S'` is a dot of `S` (`hpres`), every dot of `S` lies weakly
above the `S'`-hull (`habove`), and every `S`-abscissa is an `S'`-abscissa (`habs`),
then the genuine vertex lists coincide. -/
theorem npVertices_stable_of_hull_preserved_core
    (S S' : Finset (ℕ × ℕ)) (hS : S.Nonempty) (hS' : S'.Nonempty)
    (hpres : ∀ P ∈ npVertices S' hS', P ∈ S)
    (habove : ∀ P ∈ S, npHeight S' hS' ((P.1 : ℚ)) ≤ ((P.2 : ℚ)))
    (habs : ∀ P ∈ S, ∃ Q ∈ S', Q.1 = P.1) :
    npVertices S hS = npVertices S' hS' := by
  classical
  -- ===== extreme abscissae of S' =====
  obtain ⟨Pm, hPmS', hPmmin⟩ := S'.exists_min_image (fun P => P.1) hS'
  obtain ⟨PM, hPMS', hPMmax⟩ := S'.exists_max_image (fun P => P.1) hS'
  set m' := Pm.1 with hm'def
  set M' := PM.1 with hM'def
  have hmM : m' ≤ M' := hPmmin PM hPMS'
  -- ===== S'-side hull pins =====
  have hminabs' : m' ∈ hullAbscissae S' hS' :=
    mem_hullAbscissae_min S' hS' (fun P hP => hPmmin P hP) ⟨Pm.2, by simpa using hPmS'⟩
  have hmaxabs' : M' ∈ hullAbscissae S' hS' :=
    mem_hullAbscissae_max S' hS' (fun P hP => hPMmax P hP) ⟨PM.2, by simpa using hPMS'⟩
  have hsortabs' : (hullAbscissae S' hS').Pairwise (· < ·) := by
    have := npVerticesFull_sorted S' hS'
    rwa [npVerticesFull_fst S' hS'] at this
  have habs_lb' : ∀ x ∈ hullAbscissae S' hS', m' ≤ x := by
    intro x hx
    obtain ⟨v, hvS', -⟩ := (mem_hullAbscissae_iff S' hS').mp hx
    exact hPmmin (x, v) hvS'
  obtain ⟨tA', htA'⟩ := sorted_head_min hsortabs' hminabs' habs_lb'
  obtain ⟨v0, hv0S', hv0on⟩ := (mem_hullAbscissae_iff S' hS').mp hminabs'
  obtain ⟨vK, hvKS', hvKon⟩ := (mem_hullAbscissae_iff S' hS').mp hmaxabs'
  have hd0' : hullDotAt S' hS' m' = (m', v0) := by
    unfold hullDotAt
    rw [hullHeightAt_of_onHull S' hS' hv0S' hv0on]
  have hdK' : hullDotAt S' hS' M' = (M', vK) := by
    unfold hullDotAt
    rw [hullHeightAt_of_onHull S' hS' hvKS' hvKon]
  have hFhead' : npVerticesFull S' hS' = (m', v0) :: tA'.map (hullDotAt S' hS') := by
    rw [npVerticesFull, htA', List.map_cons, hd0']
  obtain ⟨u', hu', -⟩ := dropCollinear_cons_head ((m' : ℕ), v0) (tA'.map (hullDotAt S' hS'))
  have hVhead' : npVertices S' hS' = (m', v0) :: u' := by
    rw [npVertices, hFhead', hu']
  have hlastabs' : (hullAbscissae S' hS').getLast? = some M' := by
    apply sorted_getLast?_eq hsortabs' hmaxabs'
    intro x hx
    obtain ⟨v, hvS', -⟩ := (mem_hullAbscissae_iff S' hS').mp hx
    exact hPMmax (x, v) hvS'
  have hlastV' : (npVertices S' hS').getLast? = some (M', vK) := by
    rw [npVertices, dropCollinear_getLast?, npVerticesFull, List.getLast?_map,
      hlastabs', Option.map_some, hdK']
  have hW0V' : ((m' : ℕ), v0) ∈ npVertices S' hS' := by
    rw [hVhead']
    exact List.mem_cons_self
  have hWkV' : ((M' : ℕ), vK) ∈ npVertices S' hS' := mem_of_getLast?_eq hlastV'
  have hW0S : ((m' : ℕ), v0) ∈ S := hpres _ hW0V'
  have hWkS : ((M' : ℕ), vK) ∈ S := hpres _ hWkV'
  have hsing : u' = [] → M' = m' ∧ vK = v0 := by
    intro hnil
    have h1 : (npVertices S' hS').getLast? = some ((m' : ℕ), v0) := by
      rw [hVhead', hnil]
      simp
    have h2 := hlastV'
    rw [h1] at h2
    injection h2 with h3
    exact ⟨(congrArg Prod.fst h3).symm, (congrArg Prod.snd h3).symm⟩
  -- ===== abscissa range of S =====
  have hrange : ∀ P ∈ S, m' ≤ P.1 ∧ P.1 ≤ M' := by
    intro P hP
    obtain ⟨Q, hQ, hQ1⟩ := habs P hP
    exact ⟨hQ1 ▸ hPmmin Q hQ, hQ1 ▸ hPMmax Q hQ⟩
  have hsortV' : ((npVertices S' hS').map Prod.fst).Pairwise (· < ·) :=
    npVertices_sorted S' hS'
  have hsortV : ((npVertices S hS).map Prod.fst).Pairwise (· < ·) :=
    npVertices_sorted S hS
  -- ===== the two hulls agree on [m', M'] =====
  have hg_le : ∀ x : ℚ, ((m' : ℚ)) ≤ x → x ≤ ((M' : ℚ)) →
      npHeight S hS x ≤ npHeight S' hS' x := by
    intro x hx1 hx2
    rw [npHeight]
    refine Finset.sup'_le _ _ (fun PR hPR => ?_)
    by_cases hu'nil : u' = []
    · obtain ⟨hMm, hvKv0⟩ := hsing hu'nil
      rw [hMm] at hx2
      have hxeq : x = ((m' : ℚ)) := le_antisymm hx2 hx1
      rw [hxeq]
      calc pairLine PR.1 PR.2 ((m' : ℚ)) ≤ ((v0 : ℚ)) := pairLine_le_of_valid S hPR hW0S
        _ = npHeight S' hS' ((m' : ℚ)) := hv0on
    · obtain ⟨⟨Wi, Wj⟩, hprV'0, hb1, hb2⟩ := bracket_cover u' ((m' : ℕ), v0) ((M' : ℕ), vK)
        (by rw [← hVhead']; exact hlastV') hx1 hx2 hu'nil
      have hprV'2 : ((Wi, Wj) : (ℕ × ℕ) × (ℕ × ℕ))
          ∈ (npVertices S' hS').zip (npVertices S' hS').tail := by
        rw [hVhead']
        exact hprV'0
      have hb1' : ((Wi.1 : ℚ)) ≤ x := hb1
      have hb2' : x ≤ ((Wj.1 : ℚ)) := hb2
      have hWiS : Wi ∈ S := hpres Wi (List.of_mem_zip hprV'2).1
      have hWjS : Wj ∈ S := hpres Wj (List.mem_of_mem_tail (List.of_mem_zip hprV'2).2)
      have hWij : Wi.1 < Wj.1 := zip_fst_lt _ hsortV' (Wi, Wj) hprV'2
      have hWij' : ((Wi.1 : ℚ)) < ((Wj.1 : ℚ)) := by exact_mod_cast hWij
      have h1 : pairLine PR.1 PR.2 ((Wi.1 : ℚ)) ≤ pairLine Wi Wj ((Wi.1 : ℚ)) := by
        rw [pairLine_left]
        exact pairLine_le_of_valid S hPR (show (Wi.1, Wi.2) ∈ S by simpa using hWiS)
      have h2 : pairLine PR.1 PR.2 ((Wj.1 : ℚ)) ≤ pairLine Wi Wj ((Wj.1 : ℚ)) := by
        rw [pairLine_right Wi Wj (ne_of_lt hWij')]
        exact pairLine_le_of_valid S hPR (show (Wj.1, Wj.2) ∈ S by simpa using hWjS)
      have hdom := affine_le_on_Icc hWij' hb1' hb2' h1 h2
      have hatt := vert_zip_attain S' hS' hprV'2 hb1' hb2'
      rw [hatt]
      exact hdom
  have hg_ge : ∀ x : ℚ, ((m' : ℚ)) ≤ x → x ≤ ((M' : ℚ)) →
      npHeight S' hS' x ≤ npHeight S hS x := by
    intro x hx1 hx2
    by_cases hu'nil : u' = []
    · obtain ⟨hMm, hvKv0⟩ := hsing hu'nil
      rw [hMm] at hx2
      have hxeq : x = ((m' : ℚ)) := le_antisymm hx2 hx1
      have hval : ((((m' : ℕ), v0), ((m' : ℕ), v0)) : (ℕ × ℕ) × (ℕ × ℕ))
          ∈ validLines S := by
        rw [validLines, Finset.mem_filter]
        refine ⟨Finset.mem_product.2 ⟨hW0S, hW0S⟩, ?_⟩
        intro Q hQ
        change pairLine ((m' : ℕ), v0) ((m' : ℕ), v0) ((Q.1 : ℚ)) ≤ ((Q.2 : ℚ))
        rw [pairLine_diag_const]
        have hQ2 := (hrange Q hQ).2
        rw [hMm] at hQ2
        have hQ1 : Q.1 = m' := le_antisymm hQ2 (hrange Q hQ).1
        have hab := habove Q hQ
        rw [hQ1] at hab
        calc ((v0 : ℚ)) = npHeight S' hS' ((m' : ℚ)) := hv0on
          _ ≤ ((Q.2 : ℚ)) := hab
      rw [hxeq, ← hv0on]
      calc ((v0 : ℚ)) = pairLine ((m' : ℕ), v0) ((m' : ℕ), v0) ((m' : ℚ)) :=
            (pairLine_diag_const _ _ _).symm
        _ ≤ npHeight S hS ((m' : ℚ)) := Finset.le_sup'
            (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 ((m' : ℚ))) hval
    · obtain ⟨⟨Wi, Wj⟩, hprV'0, hb1, hb2⟩ := bracket_cover u' ((m' : ℕ), v0) ((M' : ℕ), vK)
        (by rw [← hVhead']; exact hlastV') hx1 hx2 hu'nil
      have hprV'2 : ((Wi, Wj) : (ℕ × ℕ) × (ℕ × ℕ))
          ∈ (npVertices S' hS').zip (npVertices S' hS').tail := by
        rw [hVhead']
        exact hprV'0
      have hb1' : ((Wi.1 : ℚ)) ≤ x := hb1
      have hb2' : x ≤ ((Wj.1 : ℚ)) := hb2
      have hWiS : Wi ∈ S := hpres Wi (List.of_mem_zip hprV'2).1
      have hWjS : Wj ∈ S := hpres Wj (List.mem_of_mem_tail (List.of_mem_zip hprV'2).2)
      have hvalid' := vert_zip_valid S' hS' hprV'2
      have hSvalid : ((Wi, Wj) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ validLines S := by
        rw [validLines, Finset.mem_filter]
        refine ⟨Finset.mem_product.2 ⟨hWiS, hWjS⟩, ?_⟩
        intro Q hQ
        change pairLine Wi Wj ((Q.1 : ℚ)) ≤ ((Q.2 : ℚ))
        have hchord_le : pairLine Wi Wj ((Q.1 : ℚ)) ≤ npHeight S' hS' ((Q.1 : ℚ)) :=
          Finset.le_sup'
            (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 ((Q.1 : ℚ))) hvalid'
        exact le_trans hchord_le (habove Q hQ)
      have hatt := vert_zip_attain S' hS' hprV'2 hb1' hb2'
      rw [hatt]
      exact Finset.le_sup'
        (fun PR : (ℕ × ℕ) × (ℕ × ℕ) => pairLine PR.1 PR.2 x) hSvalid
  have hgg : ∀ x : ℚ, ((m' : ℚ)) ≤ x → x ≤ ((M' : ℚ)) →
      npHeight S hS x = npHeight S' hS' x :=
    fun x h1 h2 => le_antisymm (hg_le x h1 h2) (hg_ge x h1 h2)
  -- ===== S-side head and last pins =====
  have hminabsS : m' ∈ hullAbscissae S hS :=
    mem_hullAbscissae_min S hS (fun P hP => (hrange P hP).1) ⟨v0, hW0S⟩
  have hmaxabsS : M' ∈ hullAbscissae S hS :=
    mem_hullAbscissae_max S hS (fun P hP => (hrange P hP).2) ⟨vK, hWkS⟩
  have hon0S : ((v0 : ℕ) : ℚ) = npHeight S hS ((m' : ℚ)) := by
    rw [hgg ((m' : ℚ)) (le_refl _) (by exact_mod_cast hmM)]
    exact hv0on
  have honKS : ((vK : ℕ) : ℚ) = npHeight S hS ((M' : ℚ)) := by
    rw [hgg ((M' : ℚ)) (by exact_mod_cast hmM) (le_refl _)]
    exact hvKon
  have hd0S : hullDotAt S hS m' = (m', v0) := by
    unfold hullDotAt
    rw [hullHeightAt_of_onHull S hS hW0S hon0S]
  have hdKS : hullDotAt S hS M' = (M', vK) := by
    unfold hullDotAt
    rw [hullHeightAt_of_onHull S hS hWkS honKS]
  have hsortabsS : (hullAbscissae S hS).Pairwise (· < ·) := by
    have := npVerticesFull_sorted S hS
    rwa [npVerticesFull_fst S hS] at this
  have habs_lbS : ∀ x ∈ hullAbscissae S hS, m' ≤ x := by
    intro x hx
    obtain ⟨v, hvS, -⟩ := (mem_hullAbscissae_iff S hS).mp hx
    exact (hrange (x, v) hvS).1
  obtain ⟨tAS, htAS⟩ := sorted_head_min hsortabsS hminabsS habs_lbS
  have hFheadS : npVerticesFull S hS = (m', v0) :: tAS.map (hullDotAt S hS) := by
    rw [npVerticesFull, htAS, List.map_cons, hd0S]
  obtain ⟨uS, huS, -⟩ := dropCollinear_cons_head ((m' : ℕ), v0) (tAS.map (hullDotAt S hS))
  have hVheadS : npVertices S hS = (m', v0) :: uS := by
    rw [npVertices, hFheadS, huS]
  have hlastabsS : (hullAbscissae S hS).getLast? = some M' := by
    apply sorted_getLast?_eq hsortabsS hmaxabsS
    intro x hx
    obtain ⟨v, hvS, -⟩ := (mem_hullAbscissae_iff S hS).mp hx
    exact (hrange (x, v) hvS).2
  have hlastVS : (npVertices S hS).getLast? = some (M', vK) := by
    rw [npVertices, dropCollinear_getLast?, npVerticesFull, List.getLast?_map,
      hlastabsS, Option.map_some, hdKS]
  have hW0VS : ((m' : ℕ), v0) ∈ npVertices S hS := by
    rw [hVheadS]
    exact List.mem_cons_self
  have hWkVS : ((M' : ℕ), vK) ∈ npVertices S hS := mem_of_getLast?_eq hlastVS
  have hsortFS := npVerticesFull_sorted S hS
  -- ===== membership: V' ⊆ V =====
  have hmemA : ∀ W ∈ npVertices S' hS', W ∈ npVertices S hS := by
    intro W hW
    have hWS' : W ∈ S' := vert_mem S' hS' hW
    have hWS : W ∈ S := hpres W hW
    have hWm : m' ≤ W.1 := hPmmin W hWS'
    have hWM : W.1 ≤ M' := hPMmax W hWS'
    have hWon' : ((W.2 : ℚ)) = npHeight S' hS' ((W.1 : ℚ)) := npVertices_on_hull S' hS' hW
    have hWonS : ((W.2 : ℚ)) = npHeight S hS ((W.1 : ℚ)) := by
      rw [hgg ((W.1 : ℚ)) (by exact_mod_cast hWm) (by exact_mod_cast hWM)]
      exact hWon'
    have hWabsS : W.1 ∈ hullAbscissae S hS :=
      (mem_hullAbscissae_iff S hS).mpr ⟨W.2, by simpa using hWS, hWonS⟩
    have hdW : hullDotAt S hS W.1 = W := by
      unfold hullDotAt
      rw [hullHeightAt_of_onHull S hS (show (W.1, W.2) ∈ S by simpa using hWS) hWonS]
    have hWF : W ∈ npVerticesFull S hS := by
      rw [npVerticesFull, List.mem_map]
      exact ⟨W.1, hWabsS, hdW⟩
    by_contra hWnot
    have hWne0 : W ≠ ((m' : ℕ), v0) := fun h => hWnot (h ▸ hW0VS)
    have hWneK : W ≠ ((M' : ℕ), vK) := fun h => hWnot (h ▸ hWkVS)
    have hW0F : ((m' : ℕ), v0) ∈ npVerticesFull S hS := by
      rw [hFheadS]
      exact List.mem_cons_self
    have hWkF : ((M' : ℕ), vK) ∈ npVerticesFull S hS :=
      (dropCollinear_sublist _).subset hWkVS
    have hWm' : m' < W.1 := by
      rcases eq_or_lt_of_le hWm with heq | h
      · exact absurd (fst_inj_of_sorted hsortFS W hWF _ hW0F heq.symm) hWne0
      · exact h
    have hWM' : W.1 < M' := by
      rcases eq_or_lt_of_le hWM with heq | h
      · exact absurd (fst_inj_of_sorted hsortFS W hWF _ hWkF heq) hWneK
      · exact h
    -- W is interior in V': both neighbors exist
    have hWneHead' : (npVertices S' hS').head? ≠ some W := by
      rw [hVhead']
      simp only [List.head?_cons, ne_eq, Option.some.injEq]
      intro h
      exact hWne0 h.symm
    have hWneLast' : (npVertices S' hS').getLast? ≠ some W := by
      rw [hlastV']
      simp only [ne_eq, Option.some.injEq]
      intro h
      exact hWneK h.symm
    obtain ⟨Wp, hWpzip⟩ := exists_zip_left _ hW hWneHead'
    obtain ⟨Wn, hWnzip⟩ := exists_zip_right _ hW hWneLast'
    -- bracket W in the S-side vertex list
    obtain ⟨⟨uu, vv⟩, hprS0, huuW0, hWvv0⟩ := zip_bracket uS ((m' : ℕ), v0) hWm'
      ⟨((M' : ℕ), vK), by rw [← hVheadS]; exact hWkVS, hWM'.le⟩
    have hprS : ((uu, vv) : (ℕ × ℕ) × (ℕ × ℕ))
        ∈ (npVertices S hS).zip (npVertices S hS).tail := by
      rw [hVheadS]
      exact hprS0
    have huuW : uu.1 < W.1 := huuW0
    have hWvv : W.1 ≤ vv.1 := hWvv0
    have hvvV : vv ∈ npVertices S hS := List.mem_of_mem_tail (List.of_mem_zip hprS).2
    have huuV : uu ∈ npVertices S hS := (List.of_mem_zip hprS).1
    have hWvv' : W.1 < vv.1 := by
      rcases eq_or_lt_of_le hWvv with heq | h
      · exfalso
        have hvvF : vv ∈ npVerticesFull S hS := (dropCollinear_sublist _).subset hvvV
        exact hWnot ((fst_inj_of_sorted hsortFS W hWF vv hvvF heq) ▸ hvvV)
      · exact h
    have huuR := hrange uu (vert_mem S hS huuV)
    have hvvR := hrange vv (vert_mem S hS hvvV)
    have hWpW : Wp.1 < W.1 := zip_fst_lt _ hsortV' (Wp, W) hWpzip
    have hWWn : W.1 < Wn.1 := zip_fst_lt _ hsortV' (W, Wn) hWnzip
    -- LEFT slope transfer at x₁ = max(uu.1, Wp.1) and W.1
    set x₁ : ℚ := max ((uu.1 : ℚ)) ((Wp.1 : ℚ)) with hx₁def
    have hx₁lt : x₁ < ((W.1 : ℚ)) :=
      max_lt (by exact_mod_cast huuW) (by exact_mod_cast hWpW)
    have hx₁m : ((m' : ℚ)) ≤ x₁ :=
      le_trans (by exact_mod_cast huuR.1) (le_max_left _ _)
    have hWQm : ((m' : ℚ)) ≤ ((W.1 : ℚ)) := by exact_mod_cast hWm
    have hWQM : ((W.1 : ℚ)) ≤ ((M' : ℚ)) := by exact_mod_cast hWM
    have hx₁M : x₁ ≤ ((M' : ℚ)) := le_of_lt (lt_of_lt_of_le hx₁lt hWQM)
    have hWvvQ : ((W.1 : ℚ)) ≤ ((vv.1 : ℚ)) := by exact_mod_cast hWvv'.le
    have huv1 : npHeight S hS x₁ = pairLine uu vv x₁ :=
      vert_zip_attain S hS hprS (le_max_left _ _)
        (le_of_lt (lt_of_lt_of_le hx₁lt hWvvQ))
    have huv2 : npHeight S hS ((W.1 : ℚ)) = pairLine uu vv ((W.1 : ℚ)) :=
      vert_zip_attain S hS hprS (by exact_mod_cast huuW.le) hWvvQ
    have hpW1 : npHeight S' hS' x₁ = pairLine Wp W x₁ :=
      vert_zip_attain S' hS' hWpzip (le_max_right _ _) (le_of_lt hx₁lt)
    have hpW2 : npHeight S' hS' ((W.1 : ℚ)) = pairLine Wp W ((W.1 : ℚ)) :=
      vert_zip_attain S' hS' hWpzip (by exact_mod_cast hWpW.le) (le_refl _)
    have he1 : pairLine uu vv x₁ = pairLine Wp W x₁ := by
      rw [← huv1, ← hpW1]
      exact hgg x₁ hx₁m hx₁M
    have he2 : pairLine uu vv ((W.1 : ℚ)) = pairLine Wp W ((W.1 : ℚ)) := by
      rw [← huv2, ← hpW2]
      exact hgg _ hWQm hWQM
    have hslopeL : pairSlope uu vv = pairSlope Wp W :=
      pairSlope_eq_of_eval₂ (ne_of_lt hx₁lt) he1 he2
    -- RIGHT slope transfer at W.1 and x₄ = min(vv.1, Wn.1)
    set x₄ : ℚ := min ((vv.1 : ℚ)) ((Wn.1 : ℚ)) with hx₄def
    have hx₄gt : ((W.1 : ℚ)) < x₄ :=
      lt_min (by exact_mod_cast hWvv') (by exact_mod_cast hWWn)
    have hx₄M : x₄ ≤ ((M' : ℚ)) := le_trans (min_le_left _ _) (by exact_mod_cast hvvR.2)
    have hx₄m : ((m' : ℚ)) ≤ x₄ := le_of_lt (lt_of_le_of_lt hWQm hx₄gt)
    have huv3 : npHeight S hS x₄ = pairLine uu vv x₄ :=
      vert_zip_attain S hS hprS
        (le_trans (by exact_mod_cast huuW.le) (le_of_lt hx₄gt)) (min_le_left _ _)
    have hWn1 : npHeight S' hS' ((W.1 : ℚ)) = pairLine W Wn ((W.1 : ℚ)) :=
      vert_zip_attain S' hS' hWnzip (le_refl _) (by exact_mod_cast hWWn.le)
    have hWn2 : npHeight S' hS' x₄ = pairLine W Wn x₄ :=
      vert_zip_attain S' hS' hWnzip (le_of_lt hx₄gt) (min_le_right _ _)
    have he3 : pairLine uu vv ((W.1 : ℚ)) = pairLine W Wn ((W.1 : ℚ)) := by
      rw [← huv2, ← hWn1]
      exact hgg _ hWQm hWQM
    have he4 : pairLine uu vv x₄ = pairLine W Wn x₄ := by
      rw [← huv3, ← hWn2]
      exact hgg x₄ hx₄m hx₄M
    have hslopeR : pairSlope uu vv = pairSlope W Wn :=
      pairSlope_eq_of_eval₂ (ne_of_lt hx₄gt) he3 he4
    -- W would not be a corner of V' — contradiction with the survivor-corner law
    have hcol : collinear₃ Wp W Wn = true :=
      collinear₃_of_pairSlope_eq hWpW hWWn (hslopeL.symm.trans hslopeR)
    have hWpzipD : ((Wp, W) : (ℕ × ℕ) × (ℕ × ℕ))
        ∈ (dropCollinear (npVerticesFull S' hS')).zip
          (dropCollinear (npVerticesFull S' hS')).tail := hWpzip
    have hWnzipD : ((W, Wn) : (ℕ × ℕ) × (ℕ × ℕ))
        ∈ (dropCollinear (npVerticesFull S' hS')).zip
          (dropCollinear (npVerticesFull S' hS')).tail := hWnzip
    exact dropCollinear_corner (npVerticesFull S' hS') (npVerticesFull_sorted S' hS')
      (Wp, W) hWpzipD (W, Wn) hWnzipD rfl hcol
  -- ===== membership: V ⊆ V' =====
  have hmemB : ∀ P ∈ npVertices S hS, P ∈ npVertices S' hS' := by
    intro P hP
    by_cases hPvert : ∃ W ∈ npVertices S' hS', W.1 = P.1
    · obtain ⟨W, hWV', hWeq⟩ := hPvert
      have hWVS : W ∈ npVertices S hS := hmemA W hWV'
      have hPF : P ∈ npVerticesFull S hS := (dropCollinear_sublist _).subset hP
      have hWF : W ∈ npVerticesFull S hS := (dropCollinear_sublist _).subset hWVS
      have hPW := fst_inj_of_sorted hsortFS P hPF W hWF hWeq.symm
      rw [hPW]
      exact hWV'
    · push_neg at hPvert
      exfalso
      have hPS : P ∈ S := vert_mem S hS hP
      have hPm : m' < P.1 := by
        rcases eq_or_lt_of_le (hrange P hPS).1 with heq | h
        · exact absurd heq (hPvert ((m' : ℕ), v0) hW0V')
        · exact h
      have hPM : P.1 < M' := by
        rcases eq_or_lt_of_le (hrange P hPS).2 with heq | h
        · exact absurd heq.symm (hPvert ((M' : ℕ), vK) hWkV')
        · exact h
      have hu'nil : u' ≠ [] := by
        intro hnil
        obtain ⟨hMm, -⟩ := hsing hnil
        omega
      obtain ⟨⟨Wi, Wj⟩, hpr0, hb10, hb20⟩ := zip_bracket u' ((m' : ℕ), v0) hPm
        ⟨((M' : ℕ), vK), by rw [← hVhead']; exact hWkV', hPM.le⟩
      have hprV'2 : ((Wi, Wj) : (ℕ × ℕ) × (ℕ × ℕ))
          ∈ (npVertices S' hS').zip (npVertices S' hS').tail := by
        rw [hVhead']
        exact hpr0
      have hb1 : Wi.1 < P.1 := hb10
      have hb2 : P.1 ≤ Wj.1 := hb20
      have hWiV' : Wi ∈ npVertices S' hS' := (List.of_mem_zip hprV'2).1
      have hWjV' : Wj ∈ npVertices S' hS' :=
        List.mem_of_mem_tail (List.of_mem_zip hprV'2).2
      have hb2' : P.1 < Wj.1 := by
        rcases eq_or_lt_of_le hb2 with heq | h
        · exact absurd heq.symm (hPvert Wj hWjV')
        · exact h
      have hWiVS : Wi ∈ npVertices S hS := hmemA Wi hWiV'
      have hWjVS : Wj ∈ npVertices S hS := hmemA Wj hWjV'
      have hPneHead : (npVertices S hS).head? ≠ some P := by
        rw [hVheadS]
        simp only [List.head?_cons, ne_eq, Option.some.injEq]
        intro h
        rw [← h] at hPm
        exact absurd hPm (lt_irrefl _)
      have hPneLast : (npVertices S hS).getLast? ≠ some P := by
        rw [hlastVS]
        simp only [ne_eq, Option.some.injEq]
        intro h
        rw [← h] at hPM
        exact absurd hPM (lt_irrefl _)
      obtain ⟨xL, hxLzip⟩ := exists_zip_left _ hP hPneHead
      obtain ⟨zR, hzRzip⟩ := exists_zip_right _ hP hPneLast
      have hxLV : xL ∈ npVertices S hS := (List.of_mem_zip hxLzip).1
      have hzRV : zR ∈ npVertices S hS :=
        List.mem_of_mem_tail (List.of_mem_zip hzRzip).2
      have hxLP : xL.1 < P.1 := zip_fst_lt _ hsortV (xL, P) hxLzip
      have hPzR : P.1 < zR.1 := zip_fst_lt _ hsortV (P, zR) hzRzip
      have hWile : Wi.1 ≤ xL.1 := by
        by_contra hlt
        push_neg at hlt
        have hpairabs := zip_pair_map_fst hxLzip
        have hWiabs : Wi.1 ∈ (npVertices S hS).map Prod.fst :=
          List.mem_map_of_mem hWiVS
        exact no_between_nat _ hsortV _ hpairabs Wi.1 hWiabs hlt hb1
      have hWjge : zR.1 ≤ Wj.1 := by
        by_contra hlt
        push_neg at hlt
        have hpairabs := zip_pair_map_fst hzRzip
        have hWjabs : Wj.1 ∈ (npVertices S hS).map Prod.fst :=
          List.mem_map_of_mem hWjVS
        exact no_between_nat _ hsortV _ hpairabs Wj.1 hWjabs hb2' hlt
      have hxLR := hrange xL (vert_mem S hS hxLV)
      have hzRR := hrange zR (vert_mem S hS hzRV)
      have hPR := hrange P hPS
      have c_xL : ((Wi.1 : ℚ)) ≤ ((xL.1 : ℚ)) := by exact_mod_cast hWile
      have c_P2 : ((P.1 : ℚ)) ≤ ((Wj.1 : ℚ)) := by exact_mod_cast hb2'.le
      have c_xLP : ((xL.1 : ℚ)) < ((P.1 : ℚ)) := by exact_mod_cast hxLP
      have hA1 : npHeight S hS ((xL.1 : ℚ)) = pairLine xL P ((xL.1 : ℚ)) :=
        vert_zip_attain S hS hxLzip (le_refl _) (le_of_lt c_xLP)
      have hA2 : npHeight S hS ((P.1 : ℚ)) = pairLine xL P ((P.1 : ℚ)) :=
        vert_zip_attain S hS hxLzip (le_of_lt c_xLP) (le_refl _)
      have hB1 : npHeight S' hS' ((xL.1 : ℚ)) = pairLine Wi Wj ((xL.1 : ℚ)) :=
        vert_zip_attain S' hS' hprV'2 c_xL (le_trans (le_of_lt c_xLP) c_P2)
      have hB2 : npHeight S' hS' ((P.1 : ℚ)) = pairLine Wi Wj ((P.1 : ℚ)) :=
        vert_zip_attain S' hS' hprV'2 (le_trans c_xL (le_of_lt c_xLP)) c_P2
      have hgg1 : npHeight S hS ((xL.1 : ℚ)) = npHeight S' hS' ((xL.1 : ℚ)) :=
        hgg _ (by exact_mod_cast hxLR.1) (by exact_mod_cast hxLR.2)
      have hgg2 : npHeight S hS ((P.1 : ℚ)) = npHeight S' hS' ((P.1 : ℚ)) :=
        hgg _ (by exact_mod_cast hPR.1) (by exact_mod_cast hPR.2)
      have heL1 : pairLine xL P ((xL.1 : ℚ)) = pairLine Wi Wj ((xL.1 : ℚ)) := by
        rw [← hA1, ← hB1]
        exact hgg1
      have heL2 : pairLine xL P ((P.1 : ℚ)) = pairLine Wi Wj ((P.1 : ℚ)) := by
        rw [← hA2, ← hB2]
        exact hgg2
      have hslopeL : pairSlope xL P = pairSlope Wi Wj :=
        pairSlope_eq_of_eval₂ (ne_of_lt c_xLP) heL1 heL2
      have c_PzR : ((P.1 : ℚ)) < ((zR.1 : ℚ)) := by exact_mod_cast hPzR
      have c_zR : ((zR.1 : ℚ)) ≤ ((Wj.1 : ℚ)) := by exact_mod_cast hWjge
      have c_WiP : ((Wi.1 : ℚ)) ≤ ((P.1 : ℚ)) := by exact_mod_cast hb1.le
      have hC1 : npHeight S hS ((zR.1 : ℚ)) = pairLine P zR ((zR.1 : ℚ)) :=
        vert_zip_attain S hS hzRzip (le_of_lt c_PzR) (le_refl _)
      have hC2 : npHeight S hS ((P.1 : ℚ)) = pairLine P zR ((P.1 : ℚ)) :=
        vert_zip_attain S hS hzRzip (le_refl _) (le_of_lt c_PzR)
      have hD1 : npHeight S' hS' ((zR.1 : ℚ)) = pairLine Wi Wj ((zR.1 : ℚ)) :=
        vert_zip_attain S' hS' hprV'2 (le_trans c_WiP (le_of_lt c_PzR)) c_zR
      have hgg3 : npHeight S hS ((zR.1 : ℚ)) = npHeight S' hS' ((zR.1 : ℚ)) :=
        hgg _ (by exact_mod_cast hzRR.1) (by exact_mod_cast hzRR.2)
      have heR1 : pairLine P zR ((P.1 : ℚ)) = pairLine Wi Wj ((P.1 : ℚ)) := by
        rw [← hC2, ← hB2]
        exact hgg2
      have heR2 : pairLine P zR ((zR.1 : ℚ)) = pairLine Wi Wj ((zR.1 : ℚ)) := by
        rw [← hC1, ← hD1]
        exact hgg3
      have hslopeR : pairSlope P zR = pairSlope Wi Wj :=
        pairSlope_eq_of_eval₂ (ne_of_lt c_PzR) heR1 heR2
      have hcol : collinear₃ xL P zR = true :=
        collinear₃_of_pairSlope_eq hxLP hPzR (hslopeL.trans hslopeR.symm)
      have hxLzipD : ((xL, P) : (ℕ × ℕ) × (ℕ × ℕ))
          ∈ (dropCollinear (npVerticesFull S hS)).zip
            (dropCollinear (npVerticesFull S hS)).tail := hxLzip
      have hzRzipD : ((P, zR) : (ℕ × ℕ) × (ℕ × ℕ))
          ∈ (dropCollinear (npVerticesFull S hS)).zip
            (dropCollinear (npVerticesFull S hS)).tail := hzRzip
      exact dropCollinear_corner (npVerticesFull S hS) hsortFS
        (xL, P) hxLzipD (P, zR) hzRzipD rfl hcol
  -- ===== same members + strictly sorted ⇒ equal lists =====
  exact sorted_eq_of_mem_iff hsortV hsortV'
    (fun P => ⟨fun h => hmemB P h, fun h => hmemA P h⟩)

end LeanUrat.OM.NewtonPolygon
