/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Scaffold/O12/PolygonData — face-kind sequences [unit II-P1]

E-phase transcription of `lean/blueprints/BP_II.md` §1.6, unit II-P1: the
`FaceKind` structure (verbatim) and the `FaceKind.x` / `FaceKind.d`
definitions (signatures verbatim; bodies realize the docstring's defining
clauses `x_1 = 0, x_{j+1} = x_j + L_j` and `d_j = L_j / b_j`).
Math source of record: `lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`
§3 (the L6 setting). Later units II-P2..II-P8 (`SlopeTuple`, `heights`,
L6b, L4(ii) arithmetic) extend this file.

Indexing convention (recorded for downstream units): faces are 0-indexed in
Lean (`j = 0` is the blueprint's `j = 1`), so `x 0 = 0` and
`x (j+1) = x j + L_j` for `j < k`; `x` saturates at `e` for `j ≥ k`, and
`d j = 0` out of range. The defining equations are certified below
(`x_zero`, `x_succ_of_lt`, `x_length`, `d_of_lt`).
-/

set_option linter.style.longLine false

namespace LeanUrat.Scaffold

variable {e : ℕ}

/-- A face-kind sequence κ = (L_j, b_j)_{j=1..k} on width e (brief §3, L6): L_j ≥ 1,
Σ L_j = e, b_j ∣ L_j, b_k ≥ 2. d_j := L_j/b_j; x_1 = 0, x_{j+1} = x_j + L_j. -/
structure FaceKind (e : ℕ) where
  faces    : List (ℕ+ × ℕ+)                    -- (L_j, b_j), left to right
  hsum     : (faces.map (·.1.val)).sum = e
  hdvd     : ∀ f ∈ faces, (f.2 : ℕ) ∣ (f.1 : ℕ)
  hlast    : ∀ h : faces ≠ [], 2 ≤ ((faces.getLast h).2 : ℕ)

/-- Vertex abscissas: `x j = L_0 + ⋯ + L_{j-1}` (so `x 0 = 0`,
`x (j+1) = x j + L_j` while `j < k`, saturating at `e` for `j ≥ k`). -/
def FaceKind.x (κ : FaceKind e) (j : ℕ) : ℕ :=
  ((κ.faces.take j).map (·.1.val)).sum

/-- Residual degrees `d_j = L_j / b_j` (an exact division by `hdvd`);
`0` out of range. -/
def FaceKind.d (κ : FaceKind e) (j : ℕ) : ℕ :=
  match κ.faces[j]? with
  | some f => (f.1 : ℕ) / (f.2 : ℕ)
  | none   => 0

namespace FaceKind

@[simp] theorem x_zero (κ : FaceKind e) : κ.x 0 = 0 := rfl

/-- The defining recurrence `x_{j+1} = x_j + L_j` (0-indexed, in range). -/
theorem x_succ_of_lt (κ : FaceKind e) {j : ℕ} (hj : j < κ.faces.length) :
    κ.x (j + 1) = κ.x j + (κ.faces[j].1 : ℕ) := by
  simp only [FaceKind.x, List.take_add_one, List.getElem?_eq_getElem hj,
    Option.toList_some, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- The rightmost vertex abscissa is the full width `e`. -/
theorem x_length (κ : FaceKind e) : κ.x κ.faces.length = e := by
  simpa [FaceKind.x] using κ.hsum

/-- The defining clause `d_j = L_j / b_j` (0-indexed, in range). -/
theorem d_of_lt (κ : FaceKind e) {j : ℕ} (hj : j < κ.faces.length) :
    κ.d j = (κ.faces[j].1 : ℕ) / ((κ.faces[j].2 : ℕ)) := by
  simp [FaceKind.d, List.getElem?_eq_getElem hj]

end FaceKind

/-! ## Unit II-P2: `SlopeTuple`, `heights`, `vertexHeight_int`

Blueprint §1.6 pseudo-notation realized: `slope j := (a j : ℚ) / (b j : ℚ)` is
inlined at its two use sites (`hdesc`, `hlt1`); `last` is the index
`κ.faces.length - 1` (well-defined under `h : κ.faces ≠ []`). -/

/-- An admissible slope tuple: numerators a_j ≥ 1, gcd(a_j, b_j) = 1, s_1 > ⋯ > s_k,
s_k ∈ (0,1) (i.e. a_k < b_k). -/
structure SlopeTuple (κ : FaceKind e) where
  a       : Fin κ.faces.length → ℕ+
  hcop    : ∀ j, Nat.Coprime (a j) (κ.faces.get j).2
  hdesc   : ∀ j j' : Fin κ.faces.length, j < j' →
    ((a j' : ℕ) : ℚ) / (((κ.faces.get j').2 : ℕ) : ℚ) <
      ((a j : ℕ) : ℚ) / (((κ.faces.get j).2 : ℕ) : ℚ)
  hlt1    : ∀ h : κ.faces ≠ [],
    ((a ⟨κ.faces.length - 1,
        Nat.sub_lt (List.length_pos_of_ne_nil h) Nat.one_pos⟩ : ℕ) : ℚ) /
      (((κ.faces.getLast h).2 : ℕ) : ℚ) < 1

/-- Heights h_i := P(i) ∈ ℚ (right-anchored: h_e = 0); vertex heights are integers
h_{x_j} = Σ_{j′≥j} a_{j′}·d_{j′} (each face drops a_j·d_j ∈ ℤ).

Realization: h_i sums, over each face j, the slope a_j/b_j times the width of the
part of face j lying to the right of the abscissa i (so `heights` is the
piecewise-linear polygon read right-anchored from h_e = 0). -/
noncomputable def heights (κ : FaceKind e) (s : SlopeTuple κ) (i : ℕ) : ℚ :=
  ∑ j : Fin κ.faces.length,
    ((s.a j : ℕ) : ℚ) / (((κ.faces.get j).2 : ℕ) : ℚ) *
      ((max (κ.x ((j : ℕ) + 1)) i - max (κ.x (j : ℕ)) i : ℕ) : ℚ)

/-- Vertex heights are integers: h_{x_j} = ((Σ_{j′ ≥ j} a_{j′}·d_{j′} : ℕ) : ℚ) —
each face drops a_j·d_j ∈ ℤ. -/
theorem vertexHeight_int (κ : FaceKind e) (s : SlopeTuple κ) (j : ℕ) :
    heights κ s (κ.x j) =
      ((∑ j' ∈ Finset.univ.filter (fun j' : Fin κ.faces.length => j ≤ (j' : ℕ)),
          (s.a j' : ℕ) * κ.d (j' : ℕ) : ℕ) : ℚ) := by
  have hmono : Monotone κ.x := by
    apply monotone_nat_of_le_succ
    intro m
    by_cases hm : m < κ.faces.length
    · rw [κ.x_succ_of_lt hm]; omega
    · unfold FaceKind.x
      rw [List.take_of_length_le (Nat.le_of_not_lt hm),
        List.take_of_length_le (by omega)]
  rw [heights, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j' _ => ?_
  by_cases hj : j ≤ (j' : ℕ)
  · rw [if_pos hj]
    have h1 : κ.x j ≤ κ.x (j' : ℕ) := hmono hj
    have h2 : κ.x j ≤ κ.x ((j' : ℕ) + 1) := hmono (by omega)
    rw [max_eq_left h2, max_eq_left h1, κ.x_succ_of_lt j'.isLt,
      Nat.add_sub_cancel_left, κ.d_of_lt j'.isLt]
    have hdvd : ((κ.faces.get j').2 : ℕ) ∣ ((κ.faces.get j').1 : ℕ) :=
      κ.hdvd _ (κ.faces.get_mem j')
    have hb : (((κ.faces.get j').2 : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (κ.faces.get j').2.ne_zero
    simp only [List.get_eq_getElem] at hdvd hb ⊢
    rw [Nat.cast_mul, Nat.cast_div hdvd hb]
    field_simp
  · rw [if_neg hj]
    have h1 : κ.x ((j' : ℕ) + 1) ≤ κ.x j := hmono (by omega)
    have h2 : κ.x (j' : ℕ) ≤ κ.x j := hmono (by omega)
    rw [max_eq_right h1, max_eq_right h2]
    simp

end LeanUrat.Scaffold
