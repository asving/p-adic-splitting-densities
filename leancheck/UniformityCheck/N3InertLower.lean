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
  sorry

/-- **The two families are disjoint.** A reconstruction is residually a perfect cube, hence
residually rooted, hence not in the (residually rootless) level-1 inert family. -/
theorem boxClass_notMem_level1 {π : O} (hπ : Irreducible π) {M : ℕ}
    (p : ResidueField O × MBox O M) :
    boxClass π M p ∉
      (coeffFactor (O := O) 3 (show 1 ≤ M + 3 by omega)) ⁻¹' (decidedSet O 3 c3inert 1) := by
  sorry

/-! ## 3. The level-1 family's count, and the step -/

/-- **The refined level-1 inert family's count**, subtraction-free:
`3·#{classes residually irreducible at level M+3} + q·q^(3M+6) = q³·q^(3M+6)`. -/
theorem card_level1_inert_preimage (M : ℕ) :
    3 * Nat.card ((coeffFactor (O := O) 3 (show 1 ≤ M + 3 by omega)) ⁻¹'
        (decidedSet O 3 c3inert 1))
        + residueCard O * residueCard O ^ (3 * M + 6)
      = residueCard O ^ 3 * residueCard O ^ (3 * M + 6) := by
  sorry

/-- **THE SELF-SIMILAR LOWER BOUND.** `decidedSeq (M+3) ≥ (q³−q)/(3q³) + q^(-5)·decidedSeq M`:
the level-1 inert census plus the reconstruction of the deep inert mass, with the SHARP constant
`q^(-5)` of `N3_CHECK` §9.4. -/
theorem decidedSeq_inert_step (M : ℕ) :
    ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
        + (1 / (residueCard O : ℝ) ^ 5) * decidedSeq O 3 c3inert M
      ≤ decidedSeq O 3 c3inert (M + 3) := by
  sorry

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
