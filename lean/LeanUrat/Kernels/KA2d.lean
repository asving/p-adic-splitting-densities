/-
Kernels/KA2d — BP4-c2 GATE unit KA2d [CM-first twin of KA2c; SEQUENCED BEFORE
the KA2c prover, REV 2 F5] (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §4 KA2d,
§3.A route (1b), risk R2, disposition F4).

SEALED PREDICTION (the gate's record, stated before any prover runs): BOTH
hypotheses of KA2c (`escapeE0_of_noClosedClass`: nonneg + substochastic +
every-state-reaches-a-strict-deficit-row ⟹ EscapeE0) are needed —
 · witness A = !![0, 2; 1/2, 0] (ℚ): nonneg; row 1 sums to 1/2 (strict
   deficit) and is reachable from row 0 in one step (entry 2 > 0) — the
   reachability hypothesis is RETAINED; NOT substochastic (row 0 sums to 2);
   A² = 1, hence A^{2k}𝟙 = 𝟙 ↛ 0 — no escape.
 · witness B = !![1] (ℚ): nonneg, substochastic; but the single class is
   CLOSED (every row sums to exactly 1, so no strict-deficit row exists to
   reach) — the reachability hypothesis is DROPPED; B^k𝟙 = 𝟙 — no escape.
(REV 2, F4 disposition: the pre-revision [[2]] witness FAILED its own
premises — its single row sums to 2, so no strict-deficit row exists and the
reachability premise was violated rather than retained.  The corrected pair
above is F4's.)

RECORDED RESOLUTION (file placement): the blueprint's §4 KA header assigns KA
units to Kernels/E0Matrix.lean; that file's defs (`SubStochastic`,
`NoClosedClass`, the escape theorems KA1/KA2a-c/KA3/KA5) belong to a sibling
cluster, so this gate lives in its own probe file and states the two
hypothesis sides in RAW row-sum/entry form against the built
`MovesS.EscapeE0` (MovesS/Defs.lean:524).  When E0Matrix.lean lands, the raw
forms instantiate its named Props definitionally — no restatement needed.

deps: — (gate; KA2c depends on THIS).
Build: cd lean && lake build LeanUrat.Kernels.KA2d
-/
import Mathlib
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.Kernels

open Matrix

/-- KA2d (witness A data): drops substochasticity, KEEPS reachability.
A = !![0, 2; 1/2, 0] over ℚ. -/
def ka2dA : Matrix (Fin 2) (Fin 2) ℚ := !![0, 2; 1/2, 0]

/-- KA2d (witness B data): drops reachability, KEEPS substochasticity.
B = !![1] over ℚ. -/
def ka2dB : Matrix (Fin 1) (Fin 1) ℚ := !![1]

/-- KA2d. Witness A is entrywise nonneg.  Sketch: decide/norm_num on the
four entries (`Matrix.cons_val` simp set + Fin.cases). -/
theorem ka2dA_nonneg : ∀ i j, 0 ≤ ka2dA i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [ka2dA]

/-- KA2d (reachability retained, deficit leg). Row 1 of witness A is a
STRICT-DEFICIT row: it sums to 1/2 < 1.  Sketch: `Fin.sum_univ_two` +
norm_num. -/
theorem ka2dA_deficit_row : ∑ j, ka2dA 1 j < 1 := by
  rw [Fin.sum_univ_two]
  norm_num [ka2dA]

/-- KA2d (reachability retained, path leg). The strict-deficit row 1 is
reachable from state 0 in one step: entry A₀₁ = 2 > 0.  (With
`ka2dA_deficit_row` this is exactly KA2c's reachability hypothesis at both
states — state 1 reaches itself in 0 steps.) -/
theorem ka2dA_reach : 0 < ka2dA 0 1 := by
  norm_num [ka2dA]

/-- KA2d (the dropped hypothesis). Witness A is NOT substochastic:
row 0 sums to 2 > 1. -/
theorem ka2dA_not_substochastic : ¬ ∀ i, ∑ j, ka2dA i j ≤ 1 := by
  intro h
  have h0 := h 0
  rw [Fin.sum_univ_two] at h0
  norm_num [ka2dA] at h0

/-- KA2d (mechanism). A² = 1.  Sketch: decide-adjacent
(`Matrix.mul_fin_two` / entrywise norm_num). -/
theorem ka2dA_sq : ka2dA ^ 2 = 1 := by
  ext i j
  rw [pow_two]
  fin_cases i <;> fin_cases j <;>
    simp [ka2dA, Matrix.mul_apply]

/-- KA2d (mechanism, displayed). A^{2k}·𝟙 = 𝟙 — the even subsequence is
constant, so no convergence to 0 is possible.  Sketch: `pow_mul` +
`ka2dA_sq` + `one_pow`. -/
theorem ka2dA_pow_even (k : ℕ) :
    (ka2dA ^ (2 * k)) *ᵥ (fun _ => (1 : ℚ)) = fun _ => (1 : ℚ) := by
  rw [pow_mul, ka2dA_sq, one_pow, Matrix.one_mulVec]

/-- KA2d — GATE, substochasticity leg: witness A admits NO escape.
Dropping substochasticity from KA2c (while retaining nonneg + reachability,
`ka2dA_nonneg`/`ka2dA_deficit_row`/`ka2dA_reach`) breaks the conclusion.
Sketch: `ka2dA_pow_even` pins the even subsequence at 𝟙; Tendsto to 0 would
force 𝟙 → 0 along it (`Filter.Tendsto.comp` with k ↦ 2k, atTop) —
contradiction at any entry. -/
theorem ka2dA_not_escape : ¬ MovesS.EscapeE0 ka2dA := by
  intro h
  have hmono : Filter.Tendsto (fun k : ℕ => 2 * k) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop_of_monotone (fun a b hab => by omega)
      (fun b => ⟨b, by omega⟩)
  have hsub := h.escape.comp hmono
  have hconst : ((fun k => (ka2dA ^ k) *ᵥ (fun _ => (1 : ℚ))) ∘ (fun k : ℕ => 2 * k))
      = fun _ => (fun _ => (1 : ℚ)) := by
    funext k
    exact ka2dA_pow_even k
  rw [hconst] at hsub
  have h10 : (0 : Fin 2 → ℚ) = fun _ => (1 : ℚ) :=
    tendsto_nhds_unique hsub tendsto_const_nhds
  have h01 := congrFun h10 0
  norm_num [Pi.zero_apply] at h01

/-- KA2d. Witness B is entrywise nonneg. -/
theorem ka2dB_nonneg : ∀ i j, 0 ≤ ka2dB i j := by
  intro i j
  fin_cases i; fin_cases j; norm_num [ka2dB]

/-- KA2d (the retained hypothesis). Witness B IS substochastic: the single
row sums to exactly 1. -/
theorem ka2dB_substochastic : ∀ i, ∑ j, ka2dB i j ≤ 1 := by
  intro i
  fin_cases i; simp [ka2dB]

/-- KA2d (the dropped hypothesis). Witness B's single class is CLOSED —
every row sums to EXACTLY 1, so no strict-deficit row exists and KA2c's
reachability hypothesis fails (there is nothing to reach). -/
theorem ka2dB_closed : ∀ i, ∑ j, ka2dB i j = 1 := by
  intro i
  fin_cases i; simp [ka2dB]

/-- KA2d — GATE, reachability leg: witness B admits no escape.
Sketch: B = 1 (the identity matrix), so B^k·𝟙 = 𝟙 for all k. -/
theorem ka2dB_not_escape : ¬ MovesS.EscapeE0 ka2dB := by
  intro h
  have hB : ka2dB = 1 := by
    ext i j
    fin_cases i; fin_cases j; simp [ka2dB]
  have hesc := h.escape
  rw [hB] at hesc
  simp only [one_pow, Matrix.one_mulVec] at hesc
  have h10 : (0 : Fin 1 → ℚ) = fun _ => (1 : ℚ) :=
    tendsto_nhds_unique hesc tendsto_const_nhds
  have h01 := congrFun h10 0
  norm_num [Pi.zero_apply] at h01

end LeanUrat.Kernels
