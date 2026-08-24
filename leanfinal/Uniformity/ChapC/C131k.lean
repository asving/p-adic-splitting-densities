/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B05
import Uniformity.ChapB.B06
import Uniformity.ChapC.C71

/-!
# Uniformity.ChapC.C131k — structural normal forms for the dv-engine

**Chapter C, NODES C.131k′–l′** (`DV_GRADED_ENGINE_V2_2026-08-24.md` §2.6 and §5).

This file supplies the two structural normal forms used by the v2 dv-engine.  The inner
normal form `xNF` is built from a quotient tower recursive in a natural number and a finite
reconstruction sum.  Its reconstruction and uniqueness are B.05 and B.06.  The outer normal
form applies `xNF` coefficientwise to C.71's structurally recursive `devQ` digit.

There is no reduction relation and no polynomial-dependent termination measure here: all
recursion is on a syntactic natural number, and all assembly is by `Finset.range`.

## Status

Sorry-free and axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower.C131k

open Polynomial
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A frame key has positive degree, directly from its signed degree formula and positive
ramification and residual degrees. -/
private theorem key_natDegree_pos {π : O} (F : KeyFrame O π) : 0 < F.key.natDegree := by
  rw [F.hdeg]
  exact Nat.mul_pos F.he₁ F.hf₁

/-! ## C.131k′ — the structural x-normal form -/

/-- The quotient tower at `φ`, structurally recursive in its depth. -/
noncomputable def xQuot (φ : Polynomial O) : Polynomial O → ℕ → Polynomial O
  | A, 0 => A
  | A, n + 1 => xQuot φ (A /ₘ φ) n

/-- The digit at depth `n` of the structural quotient tower. -/
noncomputable def xDigit (φ : Polynomial O) (A : Polynomial O) (n : ℕ) : Polynomial O :=
  xQuot φ A n %ₘ φ

/-- The x-normal form: the finite polynomial whose outer coefficients are the successive
`F.key`-adic digits of `A`. -/
noncomputable def xNF {π : O} (F : KeyFrame O π) (A : Polynomial O) :
    Polynomial (Polynomial O) :=
  ∑ b ∈ Finset.range (A.natDegree + 1), C (xDigit F.key A b) * X ^ b

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The structural digit agrees with B.02's canonical development coefficient. -/
theorem xDigit_eq_dev (φ A : Polynomial O) (n : ℕ) :
    xDigit φ A n = dev φ A n := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih => exact ih (A /ₘ φ)

/-- Every coefficient of `xNF` is the corresponding structural digit, including beyond the
assembly range, where both sides vanish. -/
theorem xNF_coeff {π : O} (F : KeyFrame O π) (A : Polynomial O) (b : ℕ) :
    (xNF F A).coeff b = xDigit F.key A b := by
  classical
  rw [xNF, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (A.natDegree + 1)) b
    (fun b' => xDigit F.key A b')]
  by_cases hb : b ∈ Finset.range (A.natDegree + 1)
  · rw [if_pos hb]
  · rw [if_neg hb, xDigit_eq_dev]
    rw [Finset.mem_range, not_lt] at hb
    refine (dev_eq_zero_of_lt F.hmonic (key_natDegree_pos F) A b ?_).symm
    calc
      A.natDegree < b := by omega
      _ = b * 1 := (Nat.mul_one b).symm
      _ ≤ b * F.key.natDegree := Nat.mul_le_mul_left b (key_natDegree_pos F)

/-- Every x-normal-form digit is reduced modulo `F.key`. -/
theorem xNF_coeff_degree_lt {π : O} (F : KeyFrame O π) (A : Polynomial O) (b : ℕ) :
    ((xNF F A).coeff b).degree < F.key.degree := by
  rw [xNF_coeff, xDigit_eq_dev]
  exact degree_dev_lt F.hmonic (key_natDegree_pos F) A b

/-- Reconstruction: evaluating the outer variable of `xNF F A` at `F.key` returns `A`. -/
theorem xNF_eval {π : O} (F : KeyFrame O π) (A : Polynomial O) :
    Polynomial.eval F.key (xNF F A) = A := by
  rw [xNF, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X, xDigit_eq_dev]
  refine sum_dev_eq F.hmonic (key_natDegree_pos F) A ?_
  calc
    A.natDegree < A.natDegree + 1 := by omega
    _ = (A.natDegree + 1) * 1 := by ring
    _ ≤ (A.natDegree + 1) * F.key.natDegree :=
      Nat.mul_le_mul_left _ (key_natDegree_pos F)

/-- Uniqueness of the x-normal-form digits: any reduced family reconstructing `A` over a
finite range is the structural digit family on that range. -/
theorem xNF_unique {π : O} (F : KeyFrame O π) {A : Polynomial O}
    {a : ℕ → Polynomial O} {k : ℕ}
    (hdeg : ∀ b, (a b).degree < F.key.degree)
    (hreconstruct : ∑ b ∈ Finset.range k, a b * F.key ^ b = A) :
    ∀ b < k, a b = xDigit F.key A b := by
  intro b hb
  rw [xDigit_eq_dev]
  exact dev_unique F.hmonic (key_natDegree_pos F) hdeg hreconstruct b hb

/-! ## C.131l′ — the structural outer normal form -/

/-- Apply the structural x-normal form to every coefficient of a polynomial. -/
noncomputable def coeffwiseXNF {π : O} (F : KeyFrame O π)
    (S : Polynomial (Polynomial O)) : Polynomial (Polynomial (Polynomial O)) :=
  ∑ b ∈ Finset.range (S.natDegree + 1), C (xNF F (S.coeff b)) * X ^ b

/-- Coefficients of the coefficientwise normal form are exactly the corresponding `xNF`s. -/
theorem coeffwiseXNF_coeff {π : O} (F : KeyFrame O π)
    (S : Polynomial (Polynomial O)) (b : ℕ) :
    (coeffwiseXNF F S).coeff b = xNF F (S.coeff b) := by
  classical
  rw [coeffwiseXNF, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (S.natDegree + 1)) b
    (fun b' => xNF F (S.coeff b'))]
  by_cases hb : b ∈ Finset.range (S.natDegree + 1)
  · rw [if_pos hb]
  · rw [if_neg hb]
    rw [Finset.mem_range, not_lt] at hb
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [xNF, xDigit, xQuot]

/-- The structural outer normal form at coordinate `j`: first take the `devQ` digit at the
outer key, then x-normalize each of that digit's coefficients. -/
noncomputable def outerNF {π : O} (F : KeyFrame O π)
    (K : Polynomial (Polynomial O)) (A : Polynomial O) (j : ℕ) :
    Polynomial (Polynomial (Polynomial O)) :=
  coeffwiseXNF F (devQ K (xNF F A) j)

/-- The coefficient formula for the structural outer normal form. -/
theorem outerNF_coeff {π : O} (F : KeyFrame O π)
    (K : Polynomial (Polynomial O)) (A : Polynomial O) (j b : ℕ) :
    (outerNF F K A j).coeff b = xNF F ((devQ K (xNF F A) j).coeff b) := by
  exact coeffwiseXNF_coeff F _ b

/-- Coefficientwise x-reconstruction collapses the outer normal form back to its `devQ`
digit. -/
theorem outerNF_reconstruct {π : O} (F : KeyFrame O π)
    (K : Polynomial (Polynomial O)) (A : Polynomial O) (j : ℕ) :
    (outerNF F K A j).map (Polynomial.evalRingHom F.key) = devQ K (xNF F A) j := by
  apply Polynomial.ext
  intro b
  rw [coeff_map, outerNF_coeff]
  exact xNF_eval F _

end Uniformity.Density.Tower.C131k

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131k.xNF
#print axioms Uniformity.Density.Tower.C131k.xNF_eval
#print axioms Uniformity.Density.Tower.C131k.xNF_unique
#print axioms Uniformity.Density.Tower.C131k.outerNF
#print axioms Uniformity.Density.Tower.C131k.outerNF_reconstruct

end AxCheck
