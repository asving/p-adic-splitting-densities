/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C131d
import Uniformity.ChapC.C131k

/-!
# Uniformity.ChapC.C131m — tagged paid-branch recursion

**Chapter C, NODE C.131m′**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §2.6 and §5).

This file enriches the structural normal forms of C.131k with a natural `paid` tag.  A
`TaggedTerm R` is one contribution to a finite sum in `R`; `eraseTagged` forgets the tags.
The inner recursion is structural in the quotient depth, exactly as `xQuot` is.  Its term at
depth `b` carries tag `b`, recording the number of paid `Y` branches.  Coefficientwise outer
assembly transports this tag unchanged through C.71's `devQ` coordinate.

The main erasure theorem says that forgetting every tag in `taggedOuterNF` gives C.131k's
`outerNF` on the nose.  The two-term `xCarryStep` pins the operational meaning of the tag:
the tail branch has tag zero and satisfies `xCarry_tail_floor`, while the `Y` branch has tag
one and has the exact extra-margin weight from `xCarry_branch_WT_exact`.

All recursions below are on a syntactic natural number and all outputs are finite lists.  No
polynomial-dependent termination measure or nondeterministic rewrite relation is used.

## Status

Sorry-free and axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131m

open Polynomial
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131a Uniformity.Density.Tower.C131k

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A summand together with the number of paid branches used to produce it. -/
structure TaggedTerm (R : Type*) where
  paid : ℕ
  term : R

/-- Forget all branch tags and add the underlying finite family of terms. -/
def eraseTagged {R : Type*} [AddMonoid R] : List (TaggedTerm R) → R
  | [] => 0
  | t :: ts => t.term + eraseTagged ts

/-- Increment the paid count without changing the underlying contribution. -/
def pay {R : Type*} (t : TaggedTerm R) : TaggedTerm R :=
  ⟨t.paid + 1, t.term⟩

/-- Multiplication by a tail contribution preserves the paid count. -/
def preserve {R : Type*} [Mul R] (r : R) (t : TaggedTerm R) : TaggedTerm R :=
  ⟨t.paid, r * t.term⟩

@[simp] theorem eraseTagged_append {R : Type*} [AddMonoid R]
    (xs ys : List (TaggedTerm R)) :
    eraseTagged (xs ++ ys) = eraseTagged xs + eraseTagged ys := by
  induction xs with
  | nil => simp [eraseTagged]
  | cons x xs ih => simp [eraseTagged, ih, add_assoc]

@[simp] theorem eraseTagged_map_pay {R : Type*} [AddMonoid R]
    (xs : List (TaggedTerm R)) :
    eraseTagged (xs.map pay) = eraseTagged xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [eraseTagged, pay, ih]

@[simp] theorem eraseTagged_map_preserve {R : Type*} [Semiring R]
    (r : R) (xs : List (TaggedTerm R)) :
    eraseTagged (xs.map (preserve r)) = r * eraseTagged xs := by
  induction xs with
  | nil => simp [eraseTagged]
  | cons x xs ih => simp [eraseTagged, preserve, ih, mul_add]

/-! ## The one-step paid branch -/

/-- The tag-preserving tail contribution in a single `x`-carry. -/
noncomputable def xCarryTail {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (_T : TowerDatum F H₀ hpin) (a₀ b : ℕ) :
    TaggedTerm (Polynomial (Polynomial O)) :=
  ⟨0, Polynomial.C ((Polynomial.X ^ (F.e₁ * F.f₁) - F.key) * Polynomial.X ^ a₀) *
    Polynomial.X ^ b⟩

/-- The tag-one outer-variable contribution in a single `x`-carry. -/
noncomputable def xCarryPaid {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (_T : TowerDatum F H₀ hpin) (a₀ b : ℕ) :
    TaggedTerm (Polynomial (Polynomial O)) :=
  ⟨1, Polynomial.C (Polynomial.X ^ a₀) * Polynomial.X ^ (b + 1)⟩

/-- The two branches of one `x`-carry.  The tail branch preserves the tag; the outer-variable
branch is the unique contribution tagged as paid. -/
noncomputable def xCarryStep {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (_T : TowerDatum F H₀ hpin) (a₀ b : ℕ) :
    List (TaggedTerm (Polynomial (Polynomial O))) :=
  [xCarryTail _T a₀ b, xCarryPaid _T a₀ b]

/-- The one-step recursion consists exactly of its tag-preserving and paid contributions. -/
theorem xCarryStep_eq {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (a₀ b : ℕ) :
    xCarryStep T a₀ b = [xCarryTail T a₀ b, xCarryPaid T a₀ b] := rfl

/-- The branch constructors expose the promised zero/one paid tags. -/
theorem xCarryStep_tags {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (a₀ b : ℕ) :
    (xCarryTail T a₀ b).paid = 0 ∧ (xCarryPaid T a₀ b).paid = 1 := by
  exact ⟨rfl, rfl⟩

/-- The preserved branch has the key-side floor proved in C.131e′. -/
theorem xCarryStep_tail_floor {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (a₀ b : ℕ) :
    ((((F.e₁ * F.f₁) * T.e₂ * F.h + a₀ * (T.e₂ * F.h) + b * T.u₂ : ℕ) : ℕ∞)) ≤
      WT T (xCarryTail T a₀ b).term := by
  exact xCarry_tail_floor T a₀ b

/-- The tag-one branch has exactly the old side price plus `T.margin`. -/
theorem xCarryStep_paid_WT {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (a₀ b : ℕ) :
    WT T (xCarryPaid T a₀ b).term =
      (((a₀ * (T.e₂ * F.h) + b * T.u₂ +
        (T.e₂ * ((F.e₁ * F.f₁) * F.h) + T.margin) : ℕ) : ℕ∞)) := by
  exact xCarry_branch_WT_exact T a₀ b

/-! ## Structurally tagged inner normal form -/

/-- The first `n` terms of the tagged key-adic normal form.  The recursive call is made at
the syntactic predecessor `n`; the new quotient digit receives tag `n`. -/
noncomputable def taggedXNFUpTo {π : O} (F : KeyFrame O π) (A : Polynomial O) :
    ℕ → List (TaggedTerm (Polynomial (Polynomial O)))
  | 0 => []
  | n + 1 => taggedXNFUpTo F A n ++
      [⟨n, Polynomial.C (xDigit F.key A n) * Polynomial.X ^ n⟩]

/-- The finite tagged inner normal form, with the same reconstruction range as `xNF`. -/
noncomputable def taggedXNF {π : O} (F : KeyFrame O π) (A : Polynomial O) :
    List (TaggedTerm (Polynomial (Polynomial O))) :=
  taggedXNFUpTo F A (A.natDegree + 1)

/-- Erasing the first `n` tagged digits produces the corresponding finite reconstruction sum. -/
theorem eraseTagged_taggedXNFUpTo {π : O} (F : KeyFrame O π) (A : Polynomial O) (n : ℕ) :
    eraseTagged (taggedXNFUpTo F A n) =
      ∑ b ∈ Finset.range n, Polynomial.C (xDigit F.key A b) * Polynomial.X ^ b := by
  induction n with
  | zero => simp [taggedXNFUpTo, eraseTagged]
  | succ n ih =>
      simp [taggedXNFUpTo, eraseTagged, ih, Finset.sum_range_succ]

/-- **Inner erasure theorem.**  Forgetting the paid counts gives C.131k's `xNF`. -/
theorem taggedXNF_erasure {π : O} (F : KeyFrame O π) (A : Polynomial O) :
    eraseTagged (taggedXNF F A) = xNF F A := by
  rw [taggedXNF, eraseTagged_taggedXNFUpTo]
  rfl

/-! ## Tag transport through the outer quotient tower -/

/-- Place an inner tagged contribution at outer coefficient `b`, preserving its paid count. -/
noncomputable def atOuter {R : Type*} [Semiring R] (b : ℕ)
    (t : TaggedTerm (Polynomial R)) : TaggedTerm (Polynomial (Polynomial R)) :=
  ⟨t.paid, Polynomial.C t.term * Polynomial.X ^ b⟩

/-- Erasure commutes with transporting a finite tagged sum to an outer coefficient. -/
theorem eraseTagged_map_atOuter {R : Type*} [Semiring R]
    (b : ℕ) (xs : List (TaggedTerm (Polynomial R))) :
    eraseTagged (xs.map (atOuter b)) =
      Polynomial.C (eraseTagged xs) * Polynomial.X ^ b := by
  induction xs with
  | nil => simp [eraseTagged]
  | cons x xs ih =>
      simp [eraseTagged, atOuter, ih, add_mul]

/-- The first `n` outer coefficients, each expanded by the tagged inner recursion. -/
noncomputable def taggedCoeffwiseUpTo {π : O} (F : KeyFrame O π)
    (S : Polynomial (Polynomial O)) :
    ℕ → List (TaggedTerm (Polynomial (Polynomial (Polynomial O))))
  | 0 => []
  | n + 1 => taggedCoeffwiseUpTo F S n ++
      (taggedXNF F (S.coeff n)).map (atOuter n)

/-- Apply the tagged inner normal form coefficientwise over the finite outer range. -/
noncomputable def taggedCoeffwiseXNF {π : O} (F : KeyFrame O π)
    (S : Polynomial (Polynomial O)) :
    List (TaggedTerm (Polynomial (Polynomial (Polynomial O)))) :=
  taggedCoeffwiseUpTo F S (S.natDegree + 1)

/-- Erasure of the coefficientwise recursion is the corresponding finite assembly sum. -/
theorem eraseTagged_taggedCoeffwiseUpTo {π : O} (F : KeyFrame O π)
    (S : Polynomial (Polynomial O)) (n : ℕ) :
    eraseTagged (taggedCoeffwiseUpTo F S n) =
      ∑ b ∈ Finset.range n, Polynomial.C (xNF F (S.coeff b)) * Polynomial.X ^ b := by
  induction n with
  | zero => simp [taggedCoeffwiseUpTo, eraseTagged]
  | succ n ih =>
      simp [taggedCoeffwiseUpTo, ih, eraseTagged_map_atOuter, taggedXNF_erasure,
        Finset.sum_range_succ]

/-- Erasing the full coefficientwise tagged form gives C.131k's `coeffwiseXNF`. -/
theorem taggedCoeffwiseXNF_erasure {π : O} (F : KeyFrame O π)
    (S : Polynomial (Polynomial O)) :
    eraseTagged (taggedCoeffwiseXNF F S) = coeffwiseXNF F S := by
  rw [taggedCoeffwiseXNF, eraseTagged_taggedCoeffwiseUpTo]
  rfl

/-- The tagged outer normal form at coordinate `j`.  C.71's structurally recursive `devQ`
selects the coordinate; coefficientwise assembly transports every paid count unchanged. -/
noncomputable def taggedOuterNF {π : O} (F : KeyFrame O π)
    (K : Polynomial (Polynomial O)) (A : Polynomial O) (j : ℕ) :
    List (TaggedTerm (Polynomial (Polynomial (Polynomial O)))) :=
  taggedCoeffwiseXNF F (devQ K (xNF F A) j)

/-- **C.131m′ erasure theorem.**  Erasing paid-branch tags gives the preceding structural
outer normal form exactly. -/
theorem taggedOuterNF_erasure {π : O} (F : KeyFrame O π)
    (K : Polynomial (Polynomial O)) (A : Polynomial O) (j : ℕ) :
    eraseTagged (taggedOuterNF F K A j) = outerNF F K A j := by
  exact taggedCoeffwiseXNF_erasure F _

end Uniformity.Density.Tower.C131m

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131m.TaggedTerm
#print axioms Uniformity.Density.Tower.C131m.eraseTagged
#print axioms Uniformity.Density.Tower.C131m.pay
#print axioms Uniformity.Density.Tower.C131m.preserve
#print axioms Uniformity.Density.Tower.C131m.eraseTagged_append
#print axioms Uniformity.Density.Tower.C131m.eraseTagged_map_pay
#print axioms Uniformity.Density.Tower.C131m.eraseTagged_map_preserve
#print axioms Uniformity.Density.Tower.C131m.xCarryTail
#print axioms Uniformity.Density.Tower.C131m.xCarryPaid
#print axioms Uniformity.Density.Tower.C131m.xCarryStep
#print axioms Uniformity.Density.Tower.C131m.xCarryStep_eq
#print axioms Uniformity.Density.Tower.C131m.xCarryStep_tags
#print axioms Uniformity.Density.Tower.C131m.xCarryStep_tail_floor
#print axioms Uniformity.Density.Tower.C131m.xCarryStep_paid_WT
#print axioms Uniformity.Density.Tower.C131m.taggedXNFUpTo
#print axioms Uniformity.Density.Tower.C131m.taggedXNF
#print axioms Uniformity.Density.Tower.C131m.eraseTagged_taggedXNFUpTo
#print axioms Uniformity.Density.Tower.C131m.taggedXNF_erasure
#print axioms Uniformity.Density.Tower.C131m.atOuter
#print axioms Uniformity.Density.Tower.C131m.eraseTagged_map_atOuter
#print axioms Uniformity.Density.Tower.C131m.taggedCoeffwiseUpTo
#print axioms Uniformity.Density.Tower.C131m.taggedCoeffwiseXNF
#print axioms Uniformity.Density.Tower.C131m.eraseTagged_taggedCoeffwiseUpTo
#print axioms Uniformity.Density.Tower.C131m.taggedCoeffwiseXNF_erasure
#print axioms Uniformity.Density.Tower.C131m.taggedOuterNF
#print axioms Uniformity.Density.Tower.C131m.taggedOuterNF_erasure

end AxCheck
