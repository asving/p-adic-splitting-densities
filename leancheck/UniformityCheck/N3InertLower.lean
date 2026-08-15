/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3MBox
import UniformityCheck.N3Exact

/-!
# UniformityCheck.N3InertLower — the self-similar LOWER bound for the inert density

Unit `UNIFORMITY-CHECK-N3C`, layer 7 (`notes/N3_CHECK_2026-08-13.md` §13.5, the lower half). The
`{(1,3)}`-decided classes at level `M + 3` contain two disjoint families:

* the classes whose residue cubic is IRREDUCIBLE — the level-1 certificate, refined; there are
  `((q³−q)/3)·q^(3M+6)` of them (`decidedCount_inert3_one` plus the refinement count);
* the reconstructions `boxClass π M (γ̄, x)` of `{(1,3)}`-decided level-`M` classes through the
  triple-root extraction — `q⁴ · decidedCount O 3 c3inert M` of them (`card_boxImage`: `q` centres
  times the `q³` mixed-box fibre).

They are disjoint because the first family is residually rootless while the second is residually a
perfect cube, and `(X − γ̄)³` has the root `γ̄`. Hence

    decidedSeq (M+3)  ≥  (q³−q)/(3q³)  +  q^(-5) · decidedSeq M ,

which is `decidedSeq_inert_step`. The matching upper bound (over `possibleSeq`) and the limit are
in `N3InertExact.lean`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

section Lower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-! ## 1. The reconstruction, packaged for counting -/

/-- The chosen coefficient-vector lift of a mixed-box element. -/
noncomputable def boxLift (M : ℕ) (x : MBox O M) : Fin 3 → O :=
  ![resQLift M x.1, resQLift (M + 1) x.2.1, resQLift (M + 2) x.2.2]

/-- The level-`M` class of the chosen lift is the mixed box's truncation. -/
theorem proj_boxLift (M : ℕ) (x : MBox O M) : proj O 3 M (boxLift M x) = mtrunc M x := by
  funext i
  fin_cases i
  · exact mk_resQLift M x.1
  · show Ideal.Quotient.mk ((maximalIdeal O) ^ M) (resQLift (M + 1) x.2.1)
      = resFactor (by omega : M ≤ M + 1) x.2.1
    conv_rhs => rw [← mk_resQLift (M + 1) x.2.1]
    exact (resFactor_mk _ _).symm
  · show Ideal.Quotient.mk ((maximalIdeal O) ^ M) (resQLift (M + 2) x.2.2)
      = resFactor (by omega : M ≤ M + 2) x.2.2
    conv_rhs => rw [← mk_resQLift (M + 2) x.2.2]
    exact (resFactor_mk _ _).symm

theorem boxVec_eq_boxLift (π : O) (M : ℕ) (x : MBox O M) :
    boxVec π M x = ![π ^ 3 * boxLift M x 0, π ^ 2 * boxLift M x 1, π * boxLift M x 2] := by
  funext i
  fin_cases i <;> rfl

/-- Recentring the reconstruction at its own centre returns `boxVec`. -/
theorem shiftVec_boxClass (π : O) (M : ℕ) (p : ResidueField O × MBox O M) :
    shiftVec (shiftVec (boxVec π M p.2) (-(resSect O p.1))) (resSect O p.1) = boxVec π M p.2 := by
  have h := shiftVec_shiftVec_neg (boxVec π M p.2) (-(resSect O p.1))
  rwa [neg_neg] at h

/-- **The reconstruction of a `σ`-decided level-`M` class is `σ`-decided at level `M + 3`.** -/
theorem boxClass_mem_decidedSet {π : O} (hπ : Irreducible π) {M : ℕ} {σ : FactorizationType}
    (p : ResidueField O × MBox O M) (hp : mtrunc M p.2 ∈ decidedSet O 3 σ M) :
    boxClass π M p ∈ decidedSet O 3 σ (M + 3) := by
  have hs := shiftVec_boxClass π M p
  have hb := boxVec_eq_boxLift π M p.2
  show DecidedAt O 3 σ (M + 3)
    (proj O 3 (M + 3) (shiftVec (boxVec π M p.2) (-(resSect O p.1))))
  refine decidedAt_of_extract hπ (γ := resSect O p.1) (d := boxLift M p.2) ?_ ?_ ?_ ?_
  · rw [hs, hb]; rfl
  · rw [hs, hb]; rfl
  · rw [hs, hb]; rfl
  · rw [proj_boxLift]; exact hp

/-- The image of the reconstruction over the level-`M` classes lying in `S`. Written as a
`Set.range` over `ResidueField O × ↥(mtrunc ⁻¹' S)` so that its cardinality is a product. -/
noncomputable def boxImage (π : O) (M : ℕ) (S : Set (Coeff O 3 M)) : Set (Coeff O 3 (M + 3)) :=
  Set.range fun p : ResidueField O × ((mtrunc (O := O) M) ⁻¹' S) =>
    boxClass π M (p.1, (p.2 : MBox O M))

theorem mem_boxImage {π : O} {M : ℕ} {S : Set (Coeff O 3 M)} {c : Coeff O 3 (M + 3)} :
    c ∈ boxImage π M S ↔
      ∃ p : ResidueField O × MBox O M, mtrunc M p.2 ∈ S ∧ boxClass π M p = c := by
  constructor
  · rintro ⟨⟨g, x, hx⟩, rfl⟩
    exact ⟨(g, x), hx, rfl⟩
  · rintro ⟨⟨g, x⟩, hS, rfl⟩
    exact ⟨(g, ⟨x, hS⟩), rfl⟩

/-- **`#(boxImage) = q⁴ · #S`** — `q` residual centres times the sharp mixed-box fibre `q³`. -/
theorem card_boxImage {π : O} (hπ : Irreducible π) (M : ℕ) (S : Set (Coeff O 3 M)) :
    Nat.card (boxImage (O := O) π M S) = residueCard O ^ 4 * Nat.card S := by
  classical
  -- (a) the parametrisation is injective, so the image count is the parameter count
  have hinj : Function.Injective
      (fun p : ResidueField O × ((mtrunc (O := O) M) ⁻¹' S) =>
        boxClass π M (p.1, (p.2 : MBox O M))) := by
    intro p q hpq
    have h := boxClass_injective hπ M hpq
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Subtype.ext h.2)
  have hcard : Nat.card (boxImage (O := O) π M S)
      = Nat.card (ResidueField O × ((mtrunc (O := O) M) ⁻¹' S)) :=
    Nat.card_range_of_injective hinj
  -- (b) the sharp mixed-box fibre: `#(mtrunc⁻¹ S) = q³ · #S`
  have hfib : Nat.card ((mtrunc (O := O) M) ⁻¹' S) = residueCard O ^ 3 * Nat.card S := by
    have h := card_preimage_mtrunc (O := O) M S
    rw [card_coeff, card_mbox] at h
    refine Nat.eq_of_mul_eq_mul_right (pow_pos (residueCard_pos O) (3 * M)) ?_
    calc Nat.card ((mtrunc (O := O) M) ⁻¹' S) * residueCard O ^ (3 * M)
        = Nat.card S * residueCard O ^ (3 * M + 3) := h
      _ = residueCard O ^ 3 * Nat.card S * residueCard O ^ (3 * M) := by ring
  rw [hcard, Nat.card_prod, hfib, show Nat.card (ResidueField O) = residueCard O from rfl]
  ring

/-! ## 2. Disjointness from the level-1 family -/

/-- A perfect cube has a root: `(X − γ)³` vanishes at `γ`. -/
theorem not_noRootCubic_cubeCoeff {K : Type*} [Field K] (g : K) : ¬ NoRootCubic (cubeCoeff g) := by
  intro h
  refine h g ?_
  simp only [cubeCoeff_zero, cubeCoeff_one, cubeCoeff_two]
  ring

/-- **The two families are disjoint.** A reconstruction is residually a perfect cube, hence
residually rooted, hence not in the (residually rootless) level-1 inert family. -/
theorem boxClass_notMem_level1 {π : O} (hπ : Irreducible π) {M : ℕ}
    (p : ResidueField O × MBox O M) :
    boxClass π M p ∉
      (coeffFactor (O := O) 3 (show 1 ≤ M + 3 by omega)) ⁻¹' (decidedSet O 3 c3inert 1) := by
  intro hmem
  -- the residue vector of the recentred reconstruction is the perfect cube `(X − γ̄)³`
  have hmemB : ∀ i, boxVec π M p.2 i ∈ maximalIdeal O := by
    intro i
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
    fin_cases i
    · exact dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
    · exact dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
    · exact dvd_mul_right π _
  have hres : resVec (shiftVec (boxVec π M p.2) (-(resSect O p.1))) = cubeCoeff p.1 := by
    have h1 : ∀ i, shiftVec (shiftVec (boxVec π M p.2) (-(resSect O p.1))) (resSect O p.1) i
        ∈ maximalIdeal O := by
      intro i
      rw [shiftVec_boxClass π M p]
      exact hmemB i
    have h2 := (shiftVec_mem_iff (shiftVec (boxVec π M p.2) (-(resSect O p.1)))
      (resSect O p.1)).1 h1
    rwa [residue_resSect] at h2
  -- level-1 `{(1,3)}`-decidedness would force the residue cubic to be rootless
  have hdec : DecidedAt O 3 c3inert 1
      (liftRes1 (resVec (shiftVec (boxVec π M p.2) (-(resSect O p.1))))) := by
    have h3 : proj O 3 1 (shiftVec (boxVec π M p.2) (-(resSect O p.1)))
        ∈ decidedSet O 3 c3inert 1 := by
      rw [← coeffFactor_proj (O := O) 3 (show 1 ≤ M + 3 by omega)
        (shiftVec (boxVec π M p.2) (-(resSect O p.1)))]
      exact hmem
    rwa [proj_one_eq_liftRes1] at h3
  exact not_noRootCubic_cubeCoeff p.1 (by rw [← hres]; exact inert3_decided_iff.1 hdec)

/-! ## 3. The level-1 family's count, and the step -/

/-- **The refined level-1 inert family's count**, subtraction-free:
`3·#{classes residually irreducible at level M+3} + q·q^(3M+6) = q³·q^(3M+6)`. -/
theorem card_level1_inert_preimage (M : ℕ) :
    3 * Nat.card ((coeffFactor (O := O) 3 (show 1 ≤ M + 3 by omega)) ⁻¹'
        (decidedSet O 3 c3inert 1))
        + residueCard O * residueCard O ^ (3 * M + 6)
      = residueCard O ^ 3 * residueCard O ^ (3 * M + 6) := by
  have hcp := card_preimage_coeffFactor (O := O) 3 (show 1 ≤ M + 3 by omega)
    (decidedSet O 3 c3inert 1)
  rw [card_coeff, card_coeff] at hcp
  -- hcp : #(preimage) * q ^ (3 * 1) = #(decided at 1) * q ^ (3 * (M + 3))
  have hd : 3 * Nat.card (decidedSet O 3 c3inert 1) + residueCard O = residueCard O ^ 3 :=
    decidedCount_inert3_one
  refine Nat.eq_of_mul_eq_mul_right (pow_pos (residueCard_pos O) 3) ?_
  calc (3 * Nat.card ((coeffFactor (O := O) 3 (show 1 ≤ M + 3 by omega)) ⁻¹'
          (decidedSet O 3 c3inert 1))
        + residueCard O * residueCard O ^ (3 * M + 6)) * residueCard O ^ 3
      = 3 * (Nat.card ((coeffFactor (O := O) 3 (show 1 ≤ M + 3 by omega)) ⁻¹'
            (decidedSet O 3 c3inert 1)) * residueCard O ^ (3 * 1))
          + residueCard O * residueCard O ^ (3 * M + 6) * residueCard O ^ 3 := by ring
    _ = 3 * (Nat.card (decidedSet O 3 c3inert 1) * residueCard O ^ (3 * (M + 3)))
          + residueCard O * residueCard O ^ (3 * M + 6) * residueCard O ^ 3 := by rw [hcp]
    _ = (3 * Nat.card (decidedSet O 3 c3inert 1) + residueCard O)
          * (residueCard O ^ (3 * M + 6) * residueCard O ^ 3) := by ring
    _ = residueCard O ^ 3 * (residueCard O ^ (3 * M + 6) * residueCard O ^ 3) := by rw [hd]
    _ = residueCard O ^ 3 * residueCard O ^ (3 * M + 6) * residueCard O ^ 3 := by ring

/-- **THE SELF-SIMILAR LOWER BOUND.** `decidedSeq (M+3) ≥ (q³−q)/(3q³) + q^(-5)·decidedSeq M`:
the level-1 inert census plus the reconstruction of the deep inert mass, with the SHARP constant
`q^(-5)` of `N3_CHECK` §9.4. -/
theorem decidedSeq_inert_step (M : ℕ) :
    ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
        + (1 / (residueCard O : ℝ) ^ 5) * decidedSeq O 3 c3inert M
      ≤ decidedSeq O 3 c3inert (M + 3) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set A : Set (Coeff O 3 (M + 3)) :=
    (coeffFactor (O := O) 3 (show 1 ≤ M + 3 by omega)) ⁻¹' (decidedSet O 3 c3inert 1) with hAdef
  set B : Set (Coeff O 3 (M + 3)) := boxImage (O := O) π M (decidedSet O 3 c3inert M) with hBdef
  -- (1) both families are `{(1,3)}`-decided at level `M + 3`
  have hsubA : A ⊆ decidedSet O 3 c3inert (M + 3) := preimage_decidedSet_subset _
  have hsubB : B ⊆ decidedSet O 3 c3inert (M + 3) := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := mem_boxImage.1 hc
    exact boxClass_mem_decidedSet hπ p hp
  -- (2) they are disjoint: the reconstruction is residually a perfect cube
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_right]
    intro c hcB hcA
    obtain ⟨p, hp, rfl⟩ := mem_boxImage.1 hcB
    exact boxClass_notMem_level1 hπ p hcA
  -- (3) so the decided count at `M + 3` dominates the sum of the two counts
  have hcount : Nat.card A + Nat.card B ≤ decidedCount O 3 c3inert (M + 3) := by
    have h1 : Nat.card (A ∪ B : Set (Coeff O 3 (M + 3))) ≤ decidedCount O 3 c3inert (M + 3) :=
      Nat.card_le_card_of_injective (Set.inclusion (Set.union_subset hsubA hsubB))
        (Set.inclusion_injective _)
    have h2 : Nat.card (A ∪ B : Set (Coeff O 3 (M + 3))) = Nat.card A + Nat.card B := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    omega
  -- (4) the two counts, cast to `ℝ`
  have hAcard : 3 * Nat.card A + residueCard O * residueCard O ^ (3 * M + 6)
      = residueCard O ^ 3 * residueCard O ^ (3 * M + 6) := card_level1_inert_preimage (O := O) M
  have hBcard : Nat.card B = residueCard O ^ 4 * decidedCount O 3 c3inert M :=
    card_boxImage hπ M (decidedSet O 3 c3inert M)
  have f1R : 3 * (Nat.card A : ℝ)
      + (residueCard O : ℝ) * (residueCard O : ℝ) ^ (3 * M + 6)
      = (residueCard O : ℝ) ^ 3 * (residueCard O : ℝ) ^ (3 * M + 6) := by exact_mod_cast hAcard
  have f2R : (Nat.card B : ℝ)
      = (residueCard O : ℝ) ^ 4 * (decidedCount O 3 c3inert M : ℝ) := by exact_mod_cast hBcard
  -- (5) rewrite both summands over the common denominator `q ^ (3M + 9)` and compare counts
  rw [decidedSeq, decidedSeq, show 3 * (M + 3) = 3 * M + 9 from by ring]
  have hQ0 : (residueCard O : ℝ) ≠ 0 := ne_of_gt qR_pos
  have e1 : ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
      = (Nat.card A : ℝ) / (residueCard O : ℝ) ^ (3 * M + 9) := by
    rw [div_eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero 3 hQ0))
      (pow_ne_zero (3 * M + 9) hQ0)]
    linear_combination (-((residueCard O : ℝ) ^ 3)) * f1R
  have e2 : (1 / (residueCard O : ℝ) ^ 5)
        * ((decidedCount O 3 c3inert M : ℝ) / (residueCard O : ℝ) ^ (3 * M))
      = (Nat.card B : ℝ) / (residueCard O : ℝ) ^ (3 * M + 9) := by
    rw [f2R, div_mul_div_comm, div_eq_div_iff
      (mul_ne_zero (pow_ne_zero 5 hQ0) (pow_ne_zero (3 * M) hQ0))
      (pow_ne_zero (3 * M + 9) hQ0)]
    ring
  rw [e1, e2, ← add_div]
  gcongr
  exact_mod_cast hcount

end Lower

/-! ## Axiom census -/

section AxCheck

#print axioms UniformityCheck.proj_boxLift
#print axioms UniformityCheck.boxClass_mem_decidedSet
#print axioms UniformityCheck.card_boxImage
#print axioms UniformityCheck.boxClass_notMem_level1
#print axioms UniformityCheck.card_level1_inert_preimage
#print axioms UniformityCheck.decidedSeq_inert_step

end AxCheck

end UniformityCheck
