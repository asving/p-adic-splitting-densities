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
  simp [FaceKind.x, List.take_succ, List.getElem?_eq_getElem hj]

/-- The rightmost vertex abscissa is the full width `e`. -/
theorem x_length (κ : FaceKind e) : κ.x κ.faces.length = e := by
  simpa [FaceKind.x] using κ.hsum

/-- The defining clause `d_j = L_j / b_j` (0-indexed, in range). -/
theorem d_of_lt (κ : FaceKind e) {j : ℕ} (hj : j < κ.faces.length) :
    κ.d j = (κ.faces[j].1 : ℕ) / ((κ.faces[j].2 : ℕ)) := by
  simp [FaceKind.d, List.getElem?_eq_getElem hj]

end FaceKind

end LeanUrat.Scaffold
