/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3Drain

/-!
# UniformityCheck.N3Exact — what is EXACT at `n = 3`, and the concrete `q = 2, 3` rungs

Two exactness results, both honest about what they are not.

## 1. The level-1 inert census is EXHAUSTIVE

`inert3_decided` says a class whose residue cubic has no root is `{(1,3)}`-decided at level 1.
The converse holds too (`inert3_decided_iff`): if the residue cubic HAS a root `ρ̄`, the class
also has a REDUCIBLE lift — namely `(X − ρ)(X² + β₁X + β₀)` with `(β₀, β₁)` any lift of the
residue peel — whose type contains the part `(1,1)` and so is not `{(1,3)}`. Hence

    decidedSet O 3 c3inert 1  =  liftRes1 '' { v | NoRootCubic v }     (`decidedSet_inert3_one`)
    3·decidedCount O 3 c3inert 1 + q  =  q³                            (`decidedCount_inert3_one`)
    decidedSeq O 3 c3inert 1  =  (q³ − q) / (3q³)                      (`decidedSeq_inert3_one`)

— an EXACT level-1 count, in the `three_mul_card_noRootCubic` form.

**This is NOT the density, and nothing here claims it is.** `genuineDensity O 3 c3inert` is a
supremum over ALL levels, so the level-1 value is only a lower bound for it; the theorems below
say nothing more. ⚠ The following comparison is NOT proved here and is recorded only as
orientation: the informal corpus predicts the density `q³(q+1)/(3Φ)` with `Φ = q⁴+q³+q²+q+1`,
i.e. `8/31 ≈ 0.2581` at `q = 2` against the level-1 `1/4` and `36/121 ≈ 0.29752` at `q = 3`
against `8/27 ≈ 0.29630`; deeper strata (cubics that are inert but residually a perfect cube —
`X³ + 4X + 8` over `ℤ_[2]` is the standard example) would carry the difference, and
`verification/n3_family_check.py` §6c sees exactly that numerically. Neither the predicted
formula nor the strictness of the gap is a theorem of this file. What IS a theorem is that the
level-1 count cannot be improved AT LEVEL 1.

## 2. The `1/q²` bracket at the two wild primes

`upperDensity_three_padic_two/_three`: at `q = 2` the possible density exceeds the certified
density by at most `1/4`; at `q = 3`, by at most `1/9`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

section Exhaustive

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- The coefficient vector of `(X − ρ)(X² + B₁X + B₀)`. -/
def linQuadCoeff (ρ B₀ B₁ : O) : Fin 3 → O := ![-(ρ * B₀), B₀ - ρ * B₁, B₁ - ρ]

theorem monicPoly_linQuadCoeff (ρ B₀ B₁ : O) :
    monicPoly (linQuadCoeff ρ B₀ B₁) = (X - C ρ) * monicPoly ![B₀, B₁] := by
  rw [cubic_expand, monicPoly_two_expand]
  simp only [linQuadCoeff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, map_neg, map_sub, map_mul]
  ring

/-- **The level-1 `{(1,3)}` certificate is exhaustive.** A level-1 class is `{(1,3)}`-decided
**iff** its residue cubic has no root. -/
theorem inert3_decided_iff {v : Fin 3 → ResidueField O} :
    DecidedAt O 3 c3inert 1 (liftRes1 v) ↔ NoRootCubic v := by
  refine ⟨fun hdec => fun ρbar hρ => ?_, inert3_decided⟩
  -- a residual root gives a REDUCIBLE lift of the same class, of a different type
  obtain ⟨ρ, hρlift⟩ := IsLocalRing.residue_surjective (R := O) ρbar
  obtain ⟨B₀, hB₀⟩ := IsLocalRing.residue_surjective (R := O) (v 1 + v 2 * ρbar + ρbar ^ 2)
  obtain ⟨B₁, hB₁⟩ := IsLocalRing.residue_surjective (R := O) (v 2 + ρbar)
  have hres : resVec (linQuadCoeff ρ B₀ B₁) = v := by
    funext i
    fin_cases i
    · show residue O (-(ρ * B₀)) = v 0
      rw [map_neg, map_mul, hρlift, hB₀]
      linear_combination -hρ
    · show residue O (B₀ - ρ * B₁) = v 1
      rw [map_sub, map_mul, hρlift, hB₀, hB₁]
      ring
    · show residue O (B₁ - ρ) = v 2
      rw [map_sub, hρlift, hB₁]
      ring
  have hproj : proj O 3 1 (linQuadCoeff ρ B₀ B₁) = liftRes1 v := by
    rw [proj_one_eq_liftRes1, hres]
  have htype := hdec (linQuadCoeff ρ B₀ B₁) hproj
  have hmem : ((1 : ℕ), (1 : ℕ)) ∈ c3inert.data := by
    rw [← htype, monicPoly_linQuadCoeff, typeOf_linear_mul (monicPoly_monic ![B₀, B₁]) ρ]
    exact Multiset.mem_cons_self _ _
  simp [c3inert] at hmem

/-- The `{(1,3)}`-decided level-1 classes are exactly the residually rootless ones. -/
theorem decidedSet_inert3_one :
    decidedSet O 3 c3inert 1 = liftRes1 '' {v : Fin 3 → ResidueField O | NoRootCubic v} := by
  ext c
  constructor
  · intro hc
    obtain ⟨a, ha⟩ := proj_surjective O 3 1 c
    have hc' : DecidedAt O 3 c3inert 1 (liftRes1 (resVec a)) := by
      rw [← proj_one_eq_liftRes1, ha]; exact hc
    exact ⟨resVec a, inert3_decided_iff.1 hc', by rw [← proj_one_eq_liftRes1, ha]⟩
  · rintro ⟨v, hv, rfl⟩
    exact inert3_decided hv

/-- **The EXACT level-1 `{(1,3)}` count**, in the `three_mul_card_noRootCubic` form:
`3·#{(1,3)}-decided level-1 classes + q = q³`. -/
theorem decidedCount_inert3_one :
    3 * decidedCount O 3 c3inert 1 + residueCard O = residueCard O ^ 3 := by
  classical
  have hcard : decidedCount O 3 c3inert 1
      = Nat.card {v : Fin 3 → ResidueField O // NoRootCubic v} := by
    rw [decidedCount, decidedSet_inert3_one, Nat.card_coe_set_eq,
      Set.ncard_image_of_injective _ liftRes1_injective, ← Nat.card_coe_set_eq]
    rfl
  rw [hcard]
  simpa [residueCard] using three_mul_card_noRootCubic (ResidueField O)

/-- **The level-1 certified proportion of `{(1,3)}` is EXACTLY `(q³ − q)/(3q³)`** — the lower
bound `gate_inert3_lower` is sharp at level 1 (but not as a density: see the file header). -/
theorem decidedSeq_inert3_one :
    decidedSeq O 3 c3inert 1
      = ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3) := by
  have h := decidedCount_inert3_one (O := O)
  have hc : (3 : ℝ) * (decidedCount O 3 c3inert 1 : ℝ) + (residueCard O : ℝ)
      = (residueCard O : ℝ) ^ 3 := by exact_mod_cast h
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  rw [decidedSeq, show (3 : ℕ) * 1 = 3 from rfl]
  field_simp
  linarith

end Exhaustive

/-! ## The concrete `q = 2` and `q = 3` rungs of the `1/q²` bracket -/

section Padic

/-- **`q = 2`.** Over `ℤ_[2]` the `n = 3` possible density exceeds the certified density by at
most `1/4`, for every splitting type. -/
theorem upperDensity_three_padic_two (σ : FactorizationType) :
    upperDensity ℤ_[2] 3 σ ≤ genuineDensity ℤ_[2] 3 σ + 1 / 4 := by
  have h := upperDensity_three_le (O := ℤ_[2]) σ
  rw [residueCard_padicInt 2] at h
  norm_num at h
  exact h

/-- **`q = 3`.** Over `ℤ_[3]` the gap is at most `1/9`. -/
theorem upperDensity_three_padic_three (σ : FactorizationType) :
    upperDensity ℤ_[3] 3 σ ≤ genuineDensity ℤ_[3] 3 σ + 1 / 9 := by
  have h := upperDensity_three_le (O := ℤ_[3]) σ
  rw [residueCard_padicInt 3] at h
  norm_num at h
  exact h

/-- **`q = 2`, exact level-1 inert census:** `1/4` of the level-1 classes are `{(1,3)}`-decided
and no more. (HMENU3 predicts the DENSITY `8/31 ≈ 0.2581`, strictly larger — the difference is
deep mass.) -/
theorem decidedSeq_inert3_one_padic_two : decidedSeq ℤ_[2] 3 c3inert 1 = 1 / 4 := by
  rw [decidedSeq_inert3_one, residueCard_padicInt 2]
  norm_num

/-- **`q = 3`, exact level-1 inert census:** `8/27`. (HMENU3's density is `36/121 ≈ 0.29752`.) -/
theorem decidedSeq_inert3_one_padic_three : decidedSeq ℤ_[3] 3 c3inert 1 = 8 / 27 := by
  rw [decidedSeq_inert3_one, residueCard_padicInt 3]
  norm_num

end Padic

#print axioms UniformityCheck.inert3_decided_iff
#print axioms UniformityCheck.decidedSet_inert3_one
#print axioms UniformityCheck.decidedCount_inert3_one
#print axioms UniformityCheck.decidedSeq_inert3_one
#print axioms UniformityCheck.upperDensity_three_padic_two
#print axioms UniformityCheck.upperDensity_three_padic_three

end UniformityCheck
