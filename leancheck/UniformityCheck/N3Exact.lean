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

**This is NOT the density, and nothing here claims it is.** `decidedDensity O 3 c3inert` is a
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

`genuineDensity_three_padic_two/_three`: at `q = 2` the possible density exceeds the certified
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
theorem genuineDensity_three_padic_two (σ : FactorizationType) :
    genuineDensity ℤ_[2] 3 σ ≤ decidedDensity ℤ_[2] 3 σ + 1 / 4 := by
  have h := genuineDensity_three_le (O := ℤ_[2]) σ
  rw [residueCard_padicInt 2] at h
  norm_num at h
  exact h

/-- **`q = 3`.** Over `ℤ_[3]` the gap is at most `1/9`. -/
theorem genuineDensity_three_padic_three (σ : FactorizationType) :
    genuineDensity ℤ_[3] 3 σ ≤ decidedDensity ℤ_[3] 3 σ + 1 / 9 := by
  have h := genuineDensity_three_le (O := ℤ_[3]) σ
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

/-! ## 3. `n = 3` over THE density: what transfers, and what does NOT

At `n = 2` drainage is a theorem, so every certified statement transfers verbatim to THE
density `genuineDensity`. **At `n = 3` drainage is OPEN**, and this section says exactly how
much survives without it.

* **Lower bounds transfer for free, unconditionally.** `decidedDensity ≤ genuineDensity` is a
  theorem for every `n`, so every certified lower bound of `N3Gates.lean` is also a lower bound
  on THE density (`lowers_three_genuine`). Nothing is lost.
* **Upper bounds do NOT transfer.** They come from `sum_decidedDensity_le_one`, which is a
  statement about the *inner* density only; over the outer density the analogous sum bound is
  false in general. What IS available is the `n = 3` partial-drainage theorem
  `genuineDensity_three_le` (`N3Drain.lean`): `genuineDensity O 3 σ ≤ decidedDensity O 3 σ + 1/q²`.
  So a certified upper bound `u` on `decidedDensity` yields the honest upper bound `u + 1/q²`
  on THE density — the brackets widen by `1/q²` and no more.

The `n = 3` brackets over THE density are therefore stated with that explicit `1/q²` slack. The
HMENU3 predicted values still sit inside all ten of them (`gate_bracket3_hmenu3_two_genuine`,
`_three_genuine`) — a weaker but honest check. Closing the slack is exactly the open `n = 3`
drainage problem; do not quietly drop the `+ 1/q²`. -/

section GenuineThree

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The `n = 3` transfer, with its honest slack.** A certified two-sided bracket on
`decidedDensity` becomes a bracket on THE density with the upper end raised by `1/q²`. -/
theorem genuine3_bracket_of_decided {σ : FactorizationType} {l u : ℝ}
    (hl : l ≤ decidedDensity O 3 σ) (hu : decidedDensity O 3 σ ≤ u) :
    l ≤ genuineDensity O 3 σ ∧ genuineDensity O 3 σ ≤ u + 1 / (residueCard O : ℝ) ^ 2 := by
  refine ⟨hl.trans (decidedDensity_le_genuineDensity 3 σ), ?_⟩
  have h := genuineDensity_three_le (O := O) σ
  linarith

/-- **THE FIVE `n = 3` LOWER BOUNDS, over THE density**, general `O`, unconditional: a lower
bound on the inner density is a lower bound on the outer one. -/
theorem lowers_three_genuine :
    1 / (residueCard O : ℝ) ^ 9 ≤ genuineDensity O 3 c3split
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ) ^ 2) / (2 * (residueCard O : ℝ) ^ 3)
        ≤ genuineDensity O 3 c3linInert
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
        ≤ genuineDensity O 3 c3inert
    ∧ ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 4 ≤ genuineDensity O 3 c3linRam
    ∧ ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4 ≤ genuineDensity O 3 c3ram := by
  obtain ⟨hs, hi, hc, hr, ht⟩ := lowers_three (O := O)
  exact ⟨hs.trans (decidedDensity_le_genuineDensity 3 _),
    hi.trans (decidedDensity_le_genuineDensity 3 _),
    hc.trans (decidedDensity_le_genuineDensity 3 _),
    hr.trans (decidedDensity_le_genuineDensity 3 _),
    ht.trans (decidedDensity_le_genuineDensity 3 _)⟩

end GenuineThree

/-- **GATE BRACKET (n = 3), q = 2, over THE density.** Same lower bounds as
`gate_bracket3_padic_two`; each upper bound is the certified one plus the `1/4` drainage slack
of `genuineDensity_three_padic_two`. -/
theorem gate_bracket3_padic_two_genuine :
    ((1 : ℝ) / 512 ≤ genuineDensity ℤ_[2] 3 c3split
        ∧ genuineDensity ℤ_[2] 3 c3split ≤ 5 / 8)
    ∧ ((1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 3 c3linInert
        ∧ genuineDensity ℤ_[2] 3 c3linInert ≤ 447 / 512)
    ∧ ((1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 3 c3inert
        ∧ genuineDensity ℤ_[2] 3 c3inert ≤ 447 / 512)
    ∧ ((1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 3 c3linRam
        ∧ genuineDensity ℤ_[2] 3 c3linRam ≤ 351 / 512)
    ∧ ((1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 3 c3ram
        ∧ genuineDensity ℤ_[2] 3 c3ram ≤ 351 / 512) := by
  obtain ⟨⟨ls, us⟩, ⟨li, ui⟩, ⟨lc, uc⟩, ⟨lr, ur⟩, ⟨lt, ut⟩⟩ := gate_bracket3_padic_two
  have hs := genuineDensity_three_padic_two c3split
  have hi := genuineDensity_three_padic_two c3linInert
  have hc := genuineDensity_three_padic_two c3inert
  have hr := genuineDensity_three_padic_two c3linRam
  have ht := genuineDensity_three_padic_two c3ram
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    first
      | linarith [decidedDensity_le_genuineDensity (O := ℤ_[2]) 3 c3split]
      | linarith [decidedDensity_le_genuineDensity (O := ℤ_[2]) 3 c3linInert]
      | linarith [decidedDensity_le_genuineDensity (O := ℤ_[2]) 3 c3inert]
      | linarith [decidedDensity_le_genuineDensity (O := ℤ_[2]) 3 c3linRam]
      | linarith [decidedDensity_le_genuineDensity (O := ℤ_[2]) 3 c3ram]

/-- **GATE BRACKET (n = 3), q = 3, over THE density.** Upper bounds raised by the `1/9` slack of
`genuineDensity_three_padic_three`. -/
theorem gate_bracket3_padic_three_genuine :
    ((1 : ℝ) / 27 ≤ genuineDensity ℤ_[3] 3 c3split
        ∧ genuineDensity ℤ_[3] 3 c3split ≤ 11 / 27)
    ∧ ((1 : ℝ) / 3 ≤ genuineDensity ℤ_[3] 3 c3linInert
        ∧ genuineDensity ℤ_[3] 3 c3linInert ≤ 19 / 27)
    ∧ ((8 : ℝ) / 27 ≤ genuineDensity ℤ_[3] 3 c3inert
        ∧ genuineDensity ℤ_[3] 3 c3inert ≤ 2 / 3)
    ∧ ((4 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 3 c3linRam
        ∧ genuineDensity ℤ_[3] 3 c3linRam ≤ 34 / 81)
    ∧ ((2 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 3 c3ram
        ∧ genuineDensity ℤ_[3] 3 c3ram ≤ 32 / 81) := by
  obtain ⟨⟨ls, us⟩, ⟨li, ui⟩, ⟨lc, uc⟩, ⟨lr, ur⟩, ⟨lt, ut⟩⟩ := gate_bracket3_padic_three
  have hs := genuineDensity_three_padic_three c3split
  have hi := genuineDensity_three_padic_three c3linInert
  have hc := genuineDensity_three_padic_three c3inert
  have hr := genuineDensity_three_padic_three c3linRam
  have ht := genuineDensity_three_padic_three c3ram
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    first
      | linarith [decidedDensity_le_genuineDensity (O := ℤ_[3]) 3 c3split]
      | linarith [decidedDensity_le_genuineDensity (O := ℤ_[3]) 3 c3linInert]
      | linarith [decidedDensity_le_genuineDensity (O := ℤ_[3]) 3 c3inert]
      | linarith [decidedDensity_le_genuineDensity (O := ℤ_[3]) 3 c3linRam]
      | linarith [decidedDensity_le_genuineDensity (O := ℤ_[3]) 3 c3ram]

/-- **HMENU3 containment in the widened brackets, q = 2.** The corpus's predicted cubic
densities `(4/93, 28/93, 8/31, 22/93, 5/31)` still lie inside the `n = 3` brackets over THE
density. -/
theorem gate_bracket3_hmenu3_two_genuine :
    ((1 : ℝ) / 512 ≤ 4 / 93 ∧ (4 : ℝ) / 93 ≤ 5 / 8)
    ∧ ((1 : ℝ) / 4 ≤ 28 / 93 ∧ (28 : ℝ) / 93 ≤ 447 / 512)
    ∧ ((1 : ℝ) / 4 ≤ 8 / 31 ∧ (8 : ℝ) / 31 ≤ 447 / 512)
    ∧ ((1 : ℝ) / 16 ≤ 22 / 93 ∧ (22 : ℝ) / 93 ≤ 351 / 512)
    ∧ ((1 : ℝ) / 16 ≤ 5 / 31 ∧ (5 : ℝ) / 31 ≤ 351 / 512) := by
  norm_num

/-- **HMENU3 containment in the widened brackets, q = 3.** -/
theorem gate_bracket3_hmenu3_three_genuine :
    ((1 : ℝ) / 27 ≤ 63 / 968 ∧ (63 : ℝ) / 968 ≤ 11 / 27)
    ∧ ((1 : ℝ) / 3 ≤ 351 / 968 ∧ (351 : ℝ) / 968 ≤ 19 / 27)
    ∧ ((8 : ℝ) / 27 ≤ 36 / 121 ∧ (36 : ℝ) / 121 ≤ 2 / 3)
    ∧ ((4 : ℝ) / 81 ≤ 93 / 484 ∧ (93 : ℝ) / 484 ≤ 34 / 81)
    ∧ ((2 : ℝ) / 81 ≤ 10 / 121 ∧ (10 : ℝ) / 121 ≤ 32 / 81) := by
  norm_num

#print axioms UniformityCheck.inert3_decided_iff
#print axioms UniformityCheck.decidedSet_inert3_one
#print axioms UniformityCheck.decidedCount_inert3_one
#print axioms UniformityCheck.decidedSeq_inert3_one
#print axioms UniformityCheck.genuineDensity_three_padic_two
#print axioms UniformityCheck.genuineDensity_three_padic_three
-- unit UNIFORMITY-P4 (2026-08-13): the honest `n = 3` re-key over THE density
#print axioms UniformityCheck.genuine3_bracket_of_decided
#print axioms UniformityCheck.lowers_three_genuine
#print axioms UniformityCheck.gate_bracket3_padic_two_genuine
#print axioms UniformityCheck.gate_bracket3_padic_three_genuine
#print axioms UniformityCheck.gate_bracket3_hmenu3_two_genuine
#print axioms UniformityCheck.gate_bracket3_hmenu3_three_genuine

end UniformityCheck
