/-
Unit U-21c `e0_det_ne_zero` (medium) — `EscapeE0 A → (1 - A).det ≠ 0`; the EMPTY
case is `Matrix.det_isEmpty` (det = 1 ≠ 0 — an empty active block is vacuously
nonsingular, matching "realized states only"); the nonempty case uses U-21a/b.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.PowFixedVector
import LeanUrat.MovesS.MulVecAbsBound

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

theorem e0_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} (h : EscapeE0 A) : (1 - A).det ≠ 0 := by
  rcases isEmpty_or_nonempty ι with hemp | hne
  · -- EMPTY case: det of an empty matrix is 1 (vacuously nonsingular).
    haveI := hemp
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  · -- NONEMPTY case: if det = 0 there is a nonzero fixed vector of A, which
    -- U-21a/U-21b then force to 0 via the escaping mass.
    haveI := hne
    intro hdet
    obtain ⟨v, hv0, hvker⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hAv : A *ᵥ v = v := by
      have h1 := hvker
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
      exact (sub_eq_zero.1 h1).symm
    have hAvk : ∀ k : ℕ, (A ^ k) *ᵥ v = v := pow_fixed_vector hAv
    have hvzero : ∀ i, v i = 0 := by
      intro i
      have hb : ∀ k : ℕ, |v i| ≤
          (Finset.univ.sup' Finset.univ_nonempty fun j => |v j|) *
            ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i := by
        intro k
        have h1 := mulVec_abs_bound h.nonneg v k i
        rwa [congrFun (hAvk k) i] at h1
      have hcomp : Filter.Tendsto
          (fun k => ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i) Filter.atTop (nhds 0) := by
        simpa only [Pi.zero_apply] using (tendsto_pi_nhds.1 h.escape) i
      have htend : Filter.Tendsto
          (fun k => (Finset.univ.sup' Finset.univ_nonempty fun j => |v j|) *
            ((A ^ k) *ᵥ (fun _ => (1 : ℚ))) i) Filter.atTop (nhds 0) := by
        simpa only [mul_zero] using hcomp.const_mul
          (Finset.univ.sup' Finset.univ_nonempty fun j => |v j|)
      have hle : |v i| ≤ 0 := ge_of_tendsto' htend hb
      exact abs_nonpos_iff.1 hle
    exact hv0 (funext hvzero)

end LeanUrat.MovesS
