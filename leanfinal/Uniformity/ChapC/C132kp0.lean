/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp8

/-!
# Uniformity.ChapC.C132kp0 — the μ₃ initial-form predicates

**[M3-KP0, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6): define
initial equivalence, μ-divisibility, μ-minimality, μ-irreducibility, and key-polynomialhood
for the landed μ₃ value `s2Hgt₃`, and port the elementary equivalence, grade-transport, and
divisibility laws from `C130kp0`.

The similarly named declarations in `C130kp0` are not duplicates: they are anchored to
`s2Hgt₂`.  In particular, their use in `C132nv3` is the inner μ₂ argument certifying the
carried polynomial `Φ₂`; the declarations below are the next-level predicates anchored to
`s2Hgt₃`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132kp0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp8
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## The five μ₃ predicates -/

/-- Initial-form equivalence for the landed μ₃ value. -/
def S2Mu3InitialEquiv (g h : Polynomial O) : Prop :=
  (s2Hgt₃ h2 hq (g - h) > s2Hgt₃ h2 hq g ∧ s2Hgt₃ h2 hq g = s2Hgt₃ h2 hq h)
    ∨ (g = 0 ∧ h = 0)

/-- Divisibility of μ₃-initial forms. -/
def S2Mu3Dvd (φ g : Polynomial O) : Prop :=
  ∃ q : Polynomial O, S2Mu3InitialEquiv h2 hq g (φ * q)

/-- μ₃-minimality, including the positive-degree clause of FGMN Definition 1.2. -/
def S2Mu3Minimal (φ : Polynomial O) : Prop :=
  0 < φ.natDegree ∧
    ∀ g : Polynomial O, g ≠ 0 → g.natDegree < φ.natDegree → ¬ S2Mu3Dvd h2 hq φ g

/-- μ₃-irreducibility rendered through initial-form divisibility. -/
def S2Mu3Irreducible (φ : Polynomial O) : Prop :=
  φ ≠ 0 ∧ ¬ S2Mu3Dvd h2 hq φ 1 ∧
    ∀ g h : Polynomial O,
      S2Mu3Dvd h2 hq φ (g * h) → S2Mu3Dvd h2 hq φ g ∨ S2Mu3Dvd h2 hq φ h

/-- Key-polynomialhood for μ₃. -/
def S2Mu3KeyPoly (φ : Polynomial O) : Prop :=
  φ.Monic ∧ S2Mu3Minimal h2 hq φ ∧ S2Mu3Irreducible h2 hq φ

/-- Field-shape pin for the future μ₃ source-data `initialEquiv` field. -/
example : Polynomial O → Polynomial O → Prop := S2Mu3InitialEquiv h2 hq

/-- Field-shape pin for the future μ₃ source-data `keyPolynomial` field. -/
example : Polynomial O → Prop := S2Mu3KeyPoly h2 hq

/-! ## Value and equivalence laws -/

/-- The μ₃ value is invariant under negation. -/
theorem s2Hgt₃_neg (A : Polynomial O) : s2Hgt₃ h2 hq (-A) = s2Hgt₃ h2 hq A := by
  rw [s2Hgt₃_eq_dv2Supp, s2Hgt₃_eq_dv2Supp,
    dv2Supp_neg _ (s2Φ₂_monic h2 hq)]

/-- A polynomial has infinite μ₃ value exactly when it is zero. -/
theorem s2Hgt₃_eq_top_iff {A : Polynomial O} : s2Hgt₃ h2 hq A = ⊤ ↔ A = 0 := by
  constructor
  · intro htop
    by_contra hne
    exact s2Hgt₃_ne_top h2 hq hne htop
  · rintro rfl
    exact s2Hgt₃_zero h2 hq

/-- μ₃-initial equivalence is reflexive. -/
theorem S2Mu3InitialEquiv_refl (g : Polynomial O) : S2Mu3InitialEquiv h2 hq g g := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact Or.inr ⟨rfl, rfl⟩
  · refine Or.inl ⟨?_, rfl⟩
    rw [sub_self, s2Hgt₃_zero h2 hq]
    exact lt_top_iff_ne_top.mpr (s2Hgt₃_ne_top h2 hq hg)

/-- μ₃-initial equivalence is symmetric. -/
theorem S2Mu3InitialEquiv_symm {g h : Polynomial O}
    (hgh : S2Mu3InitialEquiv h2 hq g h) : S2Mu3InitialEquiv h2 hq h g := by
  rcases hgh with ⟨hlt, heq⟩ | ⟨hg0, hh0⟩
  · refine Or.inl ⟨?_, heq.symm⟩
    rw [show h - g = -(g - h) from (neg_sub g h).symm, s2Hgt₃_neg h2 hq, ← heq]
    exact hlt
  · exact Or.inr ⟨hh0, hg0⟩

/-- μ₃-initial equivalence is transitive. -/
theorem S2Mu3InitialEquiv_trans {g h k : Polynomial O}
    (hgh : S2Mu3InitialEquiv h2 hq g h) (hhk : S2Mu3InitialEquiv h2 hq h k) :
    S2Mu3InitialEquiv h2 hq g k := by
  rcases hgh with ⟨hlt1, heq1⟩ | ⟨hg0, hh0⟩
  · rcases hhk with ⟨hlt2, heq2⟩ | ⟨hh0, hk0⟩
    · refine Or.inl ⟨?_, heq1.trans heq2⟩
      have hdecomp : g - k = (g - h) + (h - k) := by ring
      have hmin := s2Hgt₃_add_ge h2 hq (g - h) (h - k)
      rw [← hdecomp] at hmin
      refine lt_of_lt_of_le (lt_min hlt1 ?_) hmin
      rw [heq1]
      exact hlt2
    · have hg0 : g = 0 := by
        rw [← s2Hgt₃_eq_top_iff h2 hq, heq1, hh0, s2Hgt₃_zero h2 hq]
      exact Or.inr ⟨hg0, hk0⟩
  · subst hh0
    rcases hhk with ⟨hlt2, -⟩ | ⟨-, hk0⟩
    · rw [s2Hgt₃_zero h2 hq] at hlt2
      exact absurd hlt2 not_top_lt
    · exact Or.inr ⟨hg0, hk0⟩

/-- The packaged equivalence relation. -/
theorem S2Mu3InitialEquiv_equivalence :
    Equivalence (S2Mu3InitialEquiv h2 hq (O := O)) :=
  ⟨S2Mu3InitialEquiv_refl h2 hq, S2Mu3InitialEquiv_symm h2 hq,
    S2Mu3InitialEquiv_trans h2 hq⟩

/-- Initial equivalence preserves μ₃ value. -/
theorem S2Mu3InitialEquiv_hgt_eq {g h : Polynomial O}
    (hgh : S2Mu3InitialEquiv h2 hq g h) : s2Hgt₃ h2 hq g = s2Hgt₃ h2 hq h := by
  rcases hgh with ⟨-, heq⟩ | ⟨rfl, rfl⟩
  · exact heq
  · rfl

/-- Zero is μ₃-initial-equivalent only to zero. -/
theorem S2Mu3InitialEquiv_zero_left {h : Polynomial O} :
    S2Mu3InitialEquiv h2 hq 0 h ↔ h = 0 := by
  constructor
  · intro hh
    rcases hh with ⟨hlt, -⟩ | ⟨-, hh0⟩
    · rw [s2Hgt₃_zero h2 hq] at hlt
      exact absurd hlt not_top_lt
    · exact hh0
  · rintro rfl
    exact S2Mu3InitialEquiv_refl h2 hq 0

/-- Right-hand zero law for μ₃-initial equivalence. -/
theorem S2Mu3InitialEquiv_zero_right {g : Polynomial O} :
    S2Mu3InitialEquiv h2 hq g 0 ↔ g = 0 := by
  constructor
  · intro hg
    exact (S2Mu3InitialEquiv_zero_left h2 hq).mp (S2Mu3InitialEquiv_symm h2 hq hg)
  · rintro rfl
    exact S2Mu3InitialEquiv_refl h2 hq 0

/-! ## Grade transport -/

/-- Initial equivalence transports an exact μ₃ grade. -/
theorem S2Mu3ExactGrade_of_initialEquiv {β : ℕ} {g h : Polynomial O}
    (hg : S2Mu3ExactGrade h2 hq β g) (hgh : S2Mu3InitialEquiv h2 hq g h) :
    S2Mu3ExactGrade h2 hq β h := by
  show s2Hgt₃ h2 hq h = (β : WithTop ℤ)
  rw [← S2Mu3InitialEquiv_hgt_eq h2 hq hgh]
  exact hg

/-- Initial equivalence preserves the total extracted μ₃ grade. -/
theorem s2Mu3GradeOf_eq_of_initialEquiv {g h : Polynomial O}
    (hgh : S2Mu3InitialEquiv h2 hq g h) :
    s2Mu3GradeOf h2 hq g = s2Mu3GradeOf h2 hq h := by
  have heq := S2Mu3InitialEquiv_hgt_eq h2 hq hgh
  rw [s2Hgt₃_eq_dv2Supp, s2Hgt₃_eq_dv2Supp] at heq
  unfold s2Mu3GradeOf
  exact congrArg ENat.toNat (toZ_inj heq)

/-! ## Elementary μ₃-divisibility laws -/

/-- Ordinary divisibility implies μ₃-divisibility. -/
theorem S2Mu3Dvd_of_dvd {φ g : Polynomial O} (hdvd : φ ∣ g) : S2Mu3Dvd h2 hq φ g := by
  obtain ⟨q, rfl⟩ := hdvd
  exact ⟨q, S2Mu3InitialEquiv_refl h2 hq _⟩

/-- Every polynomial μ₃-divides itself. -/
theorem S2Mu3Dvd_self (φ : Polynomial O) : S2Mu3Dvd h2 hq φ φ :=
  S2Mu3Dvd_of_dvd h2 hq dvd_rfl

/-- Every polynomial μ₃-divides zero. -/
theorem S2Mu3Dvd_zero (φ : Polynomial O) : S2Mu3Dvd h2 hq φ 0 :=
  S2Mu3Dvd_of_dvd h2 hq (dvd_zero φ)

/-- μ₃-divisibility is invariant under initial equivalence in the dividend. -/
theorem S2Mu3Dvd_congr_right {φ g g' : Polynomial O}
    (hgg' : S2Mu3InitialEquiv h2 hq g g') :
    S2Mu3Dvd h2 hq φ g ↔ S2Mu3Dvd h2 hq φ g' := by
  constructor
  · rintro ⟨q, hq'⟩
    exact ⟨q, S2Mu3InitialEquiv_trans h2 hq (S2Mu3InitialEquiv_symm h2 hq hgg') hq'⟩
  · rintro ⟨q, hq'⟩
    exact ⟨q, S2Mu3InitialEquiv_trans h2 hq hgg' hq'⟩

end S2

end Uniformity.Density.Tower.C132kp0

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132kp0.S2Mu3InitialEquiv
#print axioms Uniformity.Density.Tower.C132kp0.S2Mu3Dvd
#print axioms Uniformity.Density.Tower.C132kp0.S2Mu3Minimal
#print axioms Uniformity.Density.Tower.C132kp0.S2Mu3Irreducible
#print axioms Uniformity.Density.Tower.C132kp0.S2Mu3KeyPoly
#print axioms Uniformity.Density.Tower.C132kp0.S2Mu3InitialEquiv_equivalence
#print axioms Uniformity.Density.Tower.C132kp0.S2Mu3ExactGrade_of_initialEquiv
#print axioms Uniformity.Density.Tower.C132kp0.s2Mu3GradeOf_eq_of_initialEquiv
#print axioms Uniformity.Density.Tower.C132kp0.S2Mu3Dvd_congr_right

end AxCheck
