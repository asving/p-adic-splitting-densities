/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136d2

/-!
# Uniformity.ChapC.C136d3 — the μ₄ key layer and THE μ₄ CALCULUS [D3D 2026-08-28]

**Unit D3D** of the deep-witness campaign
(`docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.2, rows D3-15..D3-19): the μ₄
stack's CLOSER.  Everything below is the one-level-up port of the μ₃ key campaign
(`C132kp0`–`C132kp6b`) against the landed μ₄ operator bank (`C136d0`/`C136d1`/`C136d2`),
followed by the source records and the calculus packaging.

* **D3-15 — key predicates and residual divisibility** (models `C132kp0`, `C132kp1`).
  The five μ₄ predicates anchored to `s2Hgt₄` (`S2Mu4InitialEquiv`/`Dvd`/`Minimal`/
  `Irreducible`/`KeyPoly`), the equivalence/grade-transport/divisibility law bank, and
  `S2Mu4Dvd_iff_mu4NormRes_dvd` — the honest monic degree-`≤ 16` nonunit-residual scope
  (the μ₄ remainder fence is `16 = 2·deg g₈`).
* **D3-16 — criterion, irreducibility, and the `g16` key theorem** (models `C132kp2`,
  `C132kp3`, `C132kp5`).  `s2Mu4_key_criterion` in the literal `FGMNSourceLaws` field
  shape at the depth-three recipe degree `2·1·deg(keyAt 3) = 16`;
  `s2Mu4_key_irreducible`; ★ `s2Mu4KeyPoly_g16` — D3-14's landed monic degree-16
  `g16 = g₈² − 2⁸Φ₂` with residual `X + 1` IS a μ₄ key polynomial.
* **D3-17 — the carried key and the initial-iff-residual** (models `C132kp4`,
  `C132kp6b`).  ★ `s2Mu4KeyPoly_g8`: the carried depth-three key `g₈ = keyAt 3` is a μ₄
  key (residual `1` is the landed `s2Mu4NormRes_key`; keyhood via the odd-by-odd carry
  and the slot-zero gate, NOT via the nonunit-residual criterion).  The μ₄ key-structure
  bank: ★ `s2Mu4Minimal_natDegree_eight_dvd` (`8 ∣ deg`, refuter `g₈^(m+1) /ₘ g` with the
  seven inner cleared μ₃ digit bounds `c₁..c₇ = 4, 10, 14, 21, 25, 31, 35`; worst pair
  `2·(21 + 21) = 84 < 85`, tight at `r = 4`), ★ `s2Mu4Minimal_exactGrade`
  (`μ₄(g) = 85·(deg g/8)`), ★ `s2Mu4KeyPoly_slotZero`, the degree dictionary
  `deg g/8 = 1 ∨ deg g/8 = 2·deg R₅(g)`, and ★★ `s2Mu4_residual_to_initial` — the
  converse (published Prop 5.6's (2)→(3), two levels up).
* **D3-18 — the source records** (model `C132fd0`).  `s2SourceDataThree` packages the
  SEVEN landed μ₄ operators as
  `FGMNSourceData (s2DepthThree h2 hq) (s2DepthThreeKeyChain h2 hq) 2 1 85`, every
  projection pinned by `rfl`; ★★ `s2SourceLawsThree` discharges ALL THIRTEEN laws
  UNCONDITIONALLY (no `hex`/`hconv` hypotheses remain — D3-14 landed `s2Mu4_hex`, D3-17
  lands the converse here).  The `normalized_recipe` field is discharged by the μ₄ twin
  of RP-9's parity vacuity (`s2Mu4_recipe_grade_eighty_five_vacuous`: no polynomial of
  degree `< 8` has the odd exact μ₄ grade `85`) — the printed field's odd grade numeral,
  not the realization, is at fault, exactly as recorded one level down.
* **D3-19 — ★★★ THE μ₄ CALCULUS AND `keyAt 4`.**
  `s2Mu4_calculus_nonempty : Nonempty (FGMNCalculus (s2DepthThree h2 hq) 2 1 85)` — the
  UNCONDITIONAL depth-three calculus, via `fgmn_model_calculus_nonempty` (the campaign's
  μ₄ milestone).  `s2DepthFourKeyChain : KeyChain (s2DepthFour h2 hq)` extends the T2
  chain with `keyAt 4 = g16` (monic, degree `16 = Dcum 4`), and
  `s2Mu5_chainNormBelow_four_one_seventy_one_chain` completes C136t's T5 deferred half:
  the chain-level `hkey : I.keyAt = (s2DepthFourKeyChain h2 hq).keyAt` restatement of
  `chainNormBelow 4 171 = Λ = 2·x·Φ′·Φ₂·g₈`.

## Status

Zero `sorry`; Lean-core axiom footprint for every declaration (AxCheck footer).  No landed
statement is touched.  Verdict: `runs/wave-c/verdict_D3D.md`.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace Uniformity.Density.Tower.C136d3

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130rp0 Uniformity.Density.Tower.C130rp1
open Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C131v Uniformity.Density.Tower.C131y
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv5
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp6 Uniformity.Density.Tower.C132rp7
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C132rp10
open Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C132kp0 Uniformity.Density.Tower.C132kp1
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3ad
open Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## D3-15 Part 0 — the five μ₄ predicates (model `C132kp0`) -/

/-- Initial-form equivalence for the landed μ₄ value. -/
def S2Mu4InitialEquiv (g h : Polynomial O) : Prop :=
  (s2Hgt₄ h2 hq (g - h) > s2Hgt₄ h2 hq g ∧ s2Hgt₄ h2 hq g = s2Hgt₄ h2 hq h)
    ∨ (g = 0 ∧ h = 0)

/-- Divisibility of μ₄-initial forms. -/
def S2Mu4Dvd (φ g : Polynomial O) : Prop :=
  ∃ q : Polynomial O, S2Mu4InitialEquiv h2 hq g (φ * q)

/-- μ₄-minimality, including the positive-degree clause of FGMN Definition 1.2. -/
def S2Mu4Minimal (φ : Polynomial O) : Prop :=
  0 < φ.natDegree ∧
    ∀ g : Polynomial O, g ≠ 0 → g.natDegree < φ.natDegree → ¬ S2Mu4Dvd h2 hq φ g

/-- μ₄-irreducibility rendered through initial-form divisibility. -/
def S2Mu4Irreducible (φ : Polynomial O) : Prop :=
  φ ≠ 0 ∧ ¬ S2Mu4Dvd h2 hq φ 1 ∧
    ∀ g h : Polynomial O,
      S2Mu4Dvd h2 hq φ (g * h) → S2Mu4Dvd h2 hq φ g ∨ S2Mu4Dvd h2 hq φ h

/-- Key-polynomialhood for μ₄. -/
def S2Mu4KeyPoly (φ : Polynomial O) : Prop :=
  φ.Monic ∧ S2Mu4Minimal h2 hq φ ∧ S2Mu4Irreducible h2 hq φ

/-- Field-shape pin for the μ₄ source-data `initialEquiv` field. -/
example : Polynomial O → Polynomial O → Prop := S2Mu4InitialEquiv h2 hq

/-- Field-shape pin for the μ₄ source-data `keyPolynomial` field. -/
example : Polynomial O → Prop := S2Mu4KeyPoly h2 hq

/-! ## D3-15 Part 1 — value and equivalence laws (model `C132kp0`) -/

/-- The μ₄ value is invariant under negation. -/
theorem s2Hgt₄_neg (A : Polynomial O) : s2Hgt₄ h2 hq (-A) = s2Hgt₄ h2 hq A := by
  rw [s2Hgt₄_eq_dv3Supp, s2Hgt₄_eq_dv3Supp,
    dv3Supp_neg _ (s2Φ₂_monic h2 hq) 21 2 (s2g8_monic h2 hq) A 85 2]

/-- A polynomial has infinite μ₄ value exactly when it is zero. -/
theorem s2Hgt₄_eq_top_iff {A : Polynomial O} : s2Hgt₄ h2 hq A = ⊤ ↔ A = 0 := by
  constructor
  · intro htop
    by_contra hne
    exact s2Hgt₄_ne_top h2 hq hne htop
  · rintro rfl
    exact s2Hgt₄_zero h2 hq

/-- μ₄-initial equivalence is reflexive. -/
theorem S2Mu4InitialEquiv_refl (g : Polynomial O) : S2Mu4InitialEquiv h2 hq g g := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact Or.inr ⟨rfl, rfl⟩
  · refine Or.inl ⟨?_, rfl⟩
    rw [sub_self, s2Hgt₄_zero h2 hq]
    exact lt_top_iff_ne_top.mpr (s2Hgt₄_ne_top h2 hq hg)

/-- μ₄-initial equivalence is symmetric. -/
theorem S2Mu4InitialEquiv_symm {g h : Polynomial O}
    (hgh : S2Mu4InitialEquiv h2 hq g h) : S2Mu4InitialEquiv h2 hq h g := by
  rcases hgh with ⟨hlt, heq⟩ | ⟨hg0, hh0⟩
  · refine Or.inl ⟨?_, heq.symm⟩
    rw [show h - g = -(g - h) from (neg_sub g h).symm, s2Hgt₄_neg h2 hq, ← heq]
    exact hlt
  · exact Or.inr ⟨hh0, hg0⟩

/-- μ₄-initial equivalence is transitive. -/
theorem S2Mu4InitialEquiv_trans {g h k : Polynomial O}
    (hgh : S2Mu4InitialEquiv h2 hq g h) (hhk : S2Mu4InitialEquiv h2 hq h k) :
    S2Mu4InitialEquiv h2 hq g k := by
  rcases hgh with ⟨hlt1, heq1⟩ | ⟨hg0, hh0⟩
  · rcases hhk with ⟨hlt2, heq2⟩ | ⟨hh0, hk0⟩
    · refine Or.inl ⟨?_, heq1.trans heq2⟩
      have hdecomp : g - k = (g - h) + (h - k) := by ring
      have hmin := s2Hgt₄_add_ge h2 hq (g - h) (h - k)
      rw [← hdecomp] at hmin
      refine lt_of_lt_of_le (lt_min hlt1 ?_) hmin
      rw [heq1]
      exact hlt2
    · have hg0 : g = 0 := by
        rw [← s2Hgt₄_eq_top_iff h2 hq, heq1, hh0, s2Hgt₄_zero h2 hq]
      exact Or.inr ⟨hg0, hk0⟩
  · subst hh0
    rcases hhk with ⟨hlt2, -⟩ | ⟨-, hk0⟩
    · rw [s2Hgt₄_zero h2 hq] at hlt2
      exact absurd hlt2 not_top_lt
    · exact Or.inr ⟨hg0, hk0⟩

/-- The packaged equivalence relation. -/
theorem S2Mu4InitialEquiv_equivalence :
    Equivalence (S2Mu4InitialEquiv h2 hq (O := O)) :=
  ⟨S2Mu4InitialEquiv_refl h2 hq, S2Mu4InitialEquiv_symm h2 hq,
    S2Mu4InitialEquiv_trans h2 hq⟩

/-- Initial equivalence preserves μ₄ value. -/
theorem S2Mu4InitialEquiv_hgt_eq {g h : Polynomial O}
    (hgh : S2Mu4InitialEquiv h2 hq g h) : s2Hgt₄ h2 hq g = s2Hgt₄ h2 hq h := by
  rcases hgh with ⟨-, heq⟩ | ⟨rfl, rfl⟩
  · exact heq
  · rfl

/-- Zero is μ₄-initial-equivalent only to zero. -/
theorem S2Mu4InitialEquiv_zero_left {h : Polynomial O} :
    S2Mu4InitialEquiv h2 hq 0 h ↔ h = 0 := by
  constructor
  · intro hh
    rcases hh with ⟨hlt, -⟩ | ⟨-, hh0⟩
    · rw [s2Hgt₄_zero h2 hq] at hlt
      exact absurd hlt not_top_lt
    · exact hh0
  · rintro rfl
    exact S2Mu4InitialEquiv_refl h2 hq 0

/-- Right-hand zero law for μ₄-initial equivalence. -/
theorem S2Mu4InitialEquiv_zero_right {g : Polynomial O} :
    S2Mu4InitialEquiv h2 hq g 0 ↔ g = 0 := by
  constructor
  · intro hg
    exact (S2Mu4InitialEquiv_zero_left h2 hq).mp (S2Mu4InitialEquiv_symm h2 hq hg)
  · rintro rfl
    exact S2Mu4InitialEquiv_refl h2 hq 0

/-! ## D3-15 Part 2 — grade transport (model `C132kp0`) -/

/-- Initial equivalence transports an exact μ₄ grade. -/
theorem S2Mu4ExactGrade_of_initialEquiv {β : ℕ} {g h : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hgh : S2Mu4InitialEquiv h2 hq g h) :
    S2Mu4ExactGrade h2 hq β h := by
  show s2Hgt₄ h2 hq h = (β : WithTop ℤ)
  rw [← S2Mu4InitialEquiv_hgt_eq h2 hq hgh]
  exact hg

/-- Initial equivalence preserves the total extracted μ₄ grade. -/
theorem s2Mu4GradeOf_eq_of_initialEquiv {g h : Polynomial O}
    (hgh : S2Mu4InitialEquiv h2 hq g h) :
    s2Mu4GradeOf h2 hq g = s2Mu4GradeOf h2 hq h := by
  have heq := S2Mu4InitialEquiv_hgt_eq h2 hq hgh
  rw [s2Hgt₄_eq_dv3Supp, s2Hgt₄_eq_dv3Supp] at heq
  unfold s2Mu4GradeOf
  exact congrArg ENat.toNat (toZ_inj heq)

/-! ## D3-15 Part 3 — elementary μ₄-divisibility laws (model `C132kp0`) -/

/-- Ordinary divisibility implies μ₄-divisibility. -/
theorem S2Mu4Dvd_of_dvd {φ g : Polynomial O} (hdvd : φ ∣ g) : S2Mu4Dvd h2 hq φ g := by
  obtain ⟨q, rfl⟩ := hdvd
  exact ⟨q, S2Mu4InitialEquiv_refl h2 hq _⟩

/-- Every polynomial μ₄-divides itself. -/
theorem S2Mu4Dvd_self (φ : Polynomial O) : S2Mu4Dvd h2 hq φ φ :=
  S2Mu4Dvd_of_dvd h2 hq dvd_rfl

/-- Every polynomial μ₄-divides zero. -/
theorem S2Mu4Dvd_zero (φ : Polynomial O) : S2Mu4Dvd h2 hq φ 0 :=
  S2Mu4Dvd_of_dvd h2 hq (dvd_zero φ)

/-- μ₄-divisibility is invariant under initial equivalence in the dividend. -/
theorem S2Mu4Dvd_congr_right {φ g g' : Polynomial O}
    (hgg' : S2Mu4InitialEquiv h2 hq g g') :
    S2Mu4Dvd h2 hq φ g ↔ S2Mu4Dvd h2 hq φ g' := by
  constructor
  · rintro ⟨q, hq'⟩
    exact ⟨q, S2Mu4InitialEquiv_trans h2 hq (S2Mu4InitialEquiv_symm h2 hq hgg') hq'⟩
  · rintro ⟨q, hq'⟩
    exact ⟨q, S2Mu4InitialEquiv_trans h2 hq hgg' hq'⟩

/-! ## D3-15 Part 4 — initial-equivalence residual transport (model `C132kp1`) -/

/-- Initial equivalence preserves the normalized μ₄ residual. -/
theorem s2Mu4NormRes_eq_of_initialEquiv {g h : Polynomial O}
    (hgh : S2Mu4InitialEquiv h2 hq g h) :
    s2Mu4NormRes h2 hq g = s2Mu4NormRes h2 hq h := by
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [(S2Mu4InitialEquiv_zero_left h2 hq).mp hgh]
  · have hg := S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hg0
    have hh := S2Mu4ExactGrade_of_initialEquiv h2 hq hg hgh
    rcases hgh with ⟨hlt, -⟩ | ⟨hgzero, -⟩
    · have habove : S2Mu4AboveGrade h2 hq (s2Mu4GradeOf h2 hq g) (g - h) := by
        show ((s2Mu4GradeOf h2 hq g : ℕ) : WithTop ℤ) < s2Hgt₄ h2 hq (g - h)
        rw [← hg]
        exact hlt
      have hdecomp : g = h + (g - h) := by ring
      have hadd := s2Mu4GradedRes_add_of_le h2 hq
        (le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hh).symm)
        (le_of_lt ((S2Mu4AboveGrade_iff_dv3Supp h2 hq).mp habove))
      rw [← hdecomp, s2Mu4GradedRes_zero_of_above h2 hq habove, add_zero] at hadd
      rw [s2Mu4NormRes_of_exact h2 hq hg, s2Mu4NormRes_of_exact h2 hq hh, hadd]
    · exact absurd hgzero hg0

/-! ## D3-15 Part 5 — forward translation and low-degree residuals (model `C132kp1`) -/

/-- μ₄-divisibility universally implies divisibility of normalized μ₄ residuals. -/
theorem mu4NormRes_dvd_of_S2Mu4Dvd {g a : Polynomial O} (h : S2Mu4Dvd h2 hq g a) :
    s2Mu4NormRes h2 hq g ∣ s2Mu4NormRes h2 hq a := by
  obtain ⟨q, hq'⟩ := h
  have heq := s2Mu4NormRes_eq_of_initialEquiv h2 hq hq'
  rw [s2Mu4NormRes_mul h2 hq] at heq
  exact ⟨s2Mu4NormRes h2 hq q, heq⟩

/-- Below twice the degree-eight development key, every μ₄ graded residual is constant. -/
theorem s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen {g : Polynomial O}
    (hdeg : g.natDegree < 16) (β : ℕ) :
    s2Mu4GradedRes h2 hq β g =
      Polynomial.C ((s2Mu4GradedRes h2 hq β g).coeff 0) := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 => rw [Polynomial.coeff_C_zero]
  | t + 1 =>
    rw [Polynomial.coeff_C_of_ne_zero (Nat.succ_ne_zero t), s2Mu4GradedRes_coeff]
    refine s2Mu4Coeff_eq_zero_of_dv3Pin_top h2 hq ?_
    rw [dv3Pin, dev_eq_zero_of_lt (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num) g _
      (by rw [s2g8_natDegree h2 hq]; omega)]
    exact dv3Hgt_zero _ _ _ (by norm_num)

/-- A nonzero polynomial of degree below sixteen has unit normalized μ₄ residual. -/
theorem s2Mu4NormRes_isUnit_of_natDegree_lt_sixteen {g : Polynomial O} (hg : g ≠ 0)
    (hdeg : g.natDegree < 16) : IsUnit (s2Mu4NormRes h2 hq g) := by
  have hex := S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hg
  have hC := s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hdeg
    (s2Mu4GradeOf h2 hq g)
  have hne := s2Mu4GradedRes_ne_zero_of_exact h2 hq hex
  have hγ : (s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq g) g).coeff 0 ≠ 0 := by
    intro h0
    rw [hC, h0, map_zero] at hne
    exact hne rfl
  rw [s2Mu4NormRes_of_exact h2 hq hex, hC, Polynomial.natTrailingDegree_C,
    Function.iterate_zero_apply]
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hγ)

/-- Extracted μ₄ grades add on nonzero products. -/
private theorem s2Mu4GradeOf_mul {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    s2Mu4GradeOf h2 hq (g * z) = s2Mu4GradeOf h2 hq g + s2Mu4GradeOf h2 hq z := by
  exact s2Mu4GradeOf_eq_of_exact h2 hq
    (S2Mu4ExactGrade_mul h2 hq
      (S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hg)
      (S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hz))

/-! ## D3-15 Part 6 — backward translation and the packaged iff (model `C132kp1`) -/

/-- In the monic degree-`≤ 16`, nonunit-residual scope, residual divisibility implies
μ₄-divisibility. -/
theorem S2Mu4Dvd_of_mu4NormRes_dvd {g a : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 16) (hnu : ¬ IsUnit (s2Mu4NormRes h2 hq g))
    (hdvd : s2Mu4NormRes h2 hq g ∣ s2Mu4NormRes h2 hq a) :
    S2Mu4Dvd h2 hq g a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact S2Mu4Dvd_zero h2 hq g
  have hmod : a %ₘ g + g * (a /ₘ g) = a := Polynomial.modByMonic_add_div a g
  rcases eq_or_ne (a %ₘ g) 0 with hr0 | hr0
  · exact S2Mu4Dvd_of_dvd h2 hq ((Polynomial.modByMonic_eq_zero_iff_dvd hmon).mp hr0)
  rcases eq_or_ne (a /ₘ g) 0 with hw0 | hw0
  · exfalso
    have ha : a %ₘ g = a := by
      rw [hw0, mul_zero, add_zero] at hmod
      exact hmod
    have hdega : a.natDegree < 16 := by
      have h1 := Polynomial.natDegree_lt_natDegree hr0
        (Polynomial.degree_modByMonic_lt a hmon)
      rw [ha] at h1
      omega
    exact hnu (isUnit_of_dvd_unit hdvd
      (s2Mu4NormRes_isUnit_of_natDegree_lt_sixteen h2 hq ha0 hdega))
  have hgw0 : g * (a /ₘ g) ≠ 0 := mul_ne_zero hmon.ne_zero hw0
  have hexr := S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hr0
  have hexgw := S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hgw0
  have hvr : s2Hgt₄ h2 hq (a %ₘ g)
      = ((s2Mu4GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ) := hexr
  have hvgw : s2Hgt₄ h2 hq (g * (a /ₘ g))
      = ((s2Mu4GradeOf h2 hq (g * (a /ₘ g)) : ℕ) : WithTop ℤ) := hexgw
  rcases Nat.lt_or_ge (s2Mu4GradeOf h2 hq (g * (a /ₘ g)))
      (s2Mu4GradeOf h2 hq (a %ₘ g)) with hlt | hge
  · have hltv : s2Hgt₄ h2 hq (g * (a /ₘ g)) < s2Hgt₄ h2 hq (a %ₘ g) := by
      rw [hvr, hvgw]
      exact_mod_cast hlt
    have hadd := s2Hgt₄_add_eq h2 hq (a %ₘ g) (g * (a /ₘ g)) (ne_of_gt hltv)
    rw [hmod] at hadd
    have hva : s2Hgt₄ h2 hq a = s2Hgt₄ h2 hq (g * (a /ₘ g)) := by
      rw [hadd]
      exact min_eq_right (le_of_lt hltv)
    refine ⟨a /ₘ g, Or.inl ⟨?_, hva⟩⟩
    rw [show a - g * (a /ₘ g) = a %ₘ g from sub_eq_of_eq_add hmod.symm, hva]
    exact hltv
  · exfalso
    have hψg : s2Mu4NormRes h2 hq g
        ∣ s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq (a %ₘ g)) (g * (a /ₘ g)) := by
      rcases (ge_iff_le.mp hge).lt_or_eq with hlt' | heq'
      · rw [s2Mu4GradedRes_zero_of_above h2 hq
          (show ((s2Mu4GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ)
              < s2Hgt₄ h2 hq (g * (a /ₘ g)) from by rw [hvgw]; exact_mod_cast hlt')]
        exact dvd_zero _
      · have hmul := s2Mu4GradedRes_mul_of_exact h2 hq
          (S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hmon.ne_zero)
          (S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hw0)
        have hsum := s2Mu4GradeOf_mul h2 hq hmon.ne_zero hw0
        rw [heq', hsum, hmul]
        have hrec : s2Mu4NormRes h2 hq g
            ∣ s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq g) g :=
          ⟨Polynomial.X ^
              (s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq g) g).natTrailingDegree,
            (s2Mu4NormRes_mul_X_pow_of_exact h2 hq
              (S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hmon.ne_zero)).symm⟩
        exact Dvd.dvd.mul_left (hrec.mul_right _) _
    have hβr_le_a : ((s2Mu4GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ)
        ≤ s2Hgt₄ h2 hq a := by
      have hmin := s2Hgt₄_add_ge h2 hq (a %ₘ g) (g * (a /ₘ g))
      rw [hmod] at hmin
      refine le_trans ?_ hmin
      rw [hvr, hvgw]
      exact le_min le_rfl (by exact_mod_cast hge)
    have hψa : s2Mu4NormRes h2 hq g
        ∣ s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq (a %ₘ g)) a := by
      rcases hβr_le_a.lt_or_eq with hlt' | heq'
      · rw [s2Mu4GradedRes_zero_of_above h2 hq hlt']
        exact dvd_zero _
      · exact dvd_trans hdvd
          ⟨Polynomial.X ^
              (s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq (a %ₘ g)) a).natTrailingDegree,
            (s2Mu4NormRes_mul_X_pow_of_exact h2 hq heq'.symm).symm⟩
    have h1 : ((s2Mu4GradeOf h2 hq (a %ₘ g) : ℕ) : ℕ∞)
        ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) (g * (a /ₘ g)) 85 2 := by
      rw [(S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hexgw]
      exact_mod_cast hge
    have haddres := s2Mu4GradedRes_add_of_le h2 hq
      (le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hexr).symm) h1
    rw [hmod] at haddres
    have hψr : s2Mu4NormRes h2 hq g
        ∣ s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq (a %ₘ g)) (a %ₘ g) := by
      have hsub : s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq (a %ₘ g)) (a %ₘ g)
          = s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq (a %ₘ g)) a
            - s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq (a %ₘ g)) (g * (a /ₘ g)) := by
        rw [haddres]
        ring
      rw [hsub]
      exact dvd_sub hψa hψg
    have hdegr : (a %ₘ g).natDegree < 16 := by
      have h2' := Polynomial.natDegree_lt_natDegree hr0
        (Polynomial.degree_modByMonic_lt a hmon)
      omega
    have hC := s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hdegr
      (s2Mu4GradeOf h2 hq (a %ₘ g))
    have hne := s2Mu4GradedRes_ne_zero_of_exact h2 hq hexr
    have hγ :
        (s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq (a %ₘ g)) (a %ₘ g)).coeff 0 ≠ 0 := by
      intro h0
      rw [hC, h0, map_zero] at hne
      exact hne rfl
    rw [hC] at hψr
    exact hnu (isUnit_of_dvd_unit hψr
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hγ)))

/-- ★ **D3-15 — the μ₄-divisibility/residual-divisibility equivalence** in its honest
monic degree-`≤ 16` scope (model `C132kp1.S2Mu3Dvd_iff_mu3NormRes_dvd`, one level up). -/
theorem S2Mu4Dvd_iff_mu4NormRes_dvd {g a : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 16) (hnu : ¬ IsUnit (s2Mu4NormRes h2 hq g)) :
    S2Mu4Dvd h2 hq g a ↔ s2Mu4NormRes h2 hq g ∣ s2Mu4NormRes h2 hq a :=
  ⟨mu4NormRes_dvd_of_S2Mu4Dvd h2 hq,
    S2Mu4Dvd_of_mu4NormRes_dvd h2 hq hmon hdeg hnu⟩

/-! ## D3-16 Part 0 — residual primality and minimality (model `C132kp2`) -/

/-- An irreducible normalized μ₄ residual makes the initial form μ₄-irreducible in the
monic degree-`≤ 16` scope. -/
theorem s2Mu4Irreducible_of_irreducible_normRes {g : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 16) (hirr : Irreducible (s2Mu4NormRes h2 hq g)) :
    S2Mu4Irreducible h2 hq g := by
  refine ⟨hmon.ne_zero, ?_, ?_⟩
  · intro hone
    have hd := mu4NormRes_dvd_of_S2Mu4Dvd h2 hq hone
    rw [s2Mu4NormRes_one h2 hq] at hd
    exact hirr.not_isUnit (isUnit_of_dvd_one hd)
  · intro x y hxy
    have hd := mu4NormRes_dvd_of_S2Mu4Dvd h2 hq hxy
    rw [s2Mu4NormRes_mul h2 hq] at hd
    have hprime : Prime (s2Mu4NormRes h2 hq g) :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
    rcases hprime.2.2 _ _ hd with hdx | hdy
    · exact Or.inl (S2Mu4Dvd_of_mu4NormRes_dvd h2 hq hmon hdeg hirr.not_isUnit hdx)
    · exact Or.inr (S2Mu4Dvd_of_mu4NormRes_dvd h2 hq hmon hdeg hirr.not_isUnit hdy)

/-- A positive-degree polynomial of degree at most sixteen whose normalized μ₄ residual is
not a unit is μ₄-minimal. -/
theorem s2Mu4Minimal_of_not_isUnit_normRes {g : Polynomial O}
    (hpos : 0 < g.natDegree) (hdeg : g.natDegree ≤ 16)
    (hnu : ¬ IsUnit (s2Mu4NormRes h2 hq g)) :
    S2Mu4Minimal h2 hq g :=
  ⟨hpos, fun f hf0 hdegf hdvd =>
    hnu (isUnit_of_dvd_unit (mu4NormRes_dvd_of_S2Mu4Dvd h2 hq hdvd)
      (s2Mu4NormRes_isUnit_of_natDegree_lt_sixteen h2 hq hf0 (by omega)))⟩

/-- At the degree-sixteen μ₄ recipe size, irreducible normalized residual implies
μ₄-minimality. -/
theorem s2Mu4Minimal_of_irreducible_normRes {g : Polynomial O}
    (hdeg : g.natDegree = 16) (hirr : Irreducible (s2Mu4NormRes h2 hq g)) :
    S2Mu4Minimal h2 hq g :=
  s2Mu4Minimal_of_not_isUnit_normRes h2 hq (by omega) (le_of_eq hdeg) hirr.not_isUnit

/-! ## D3-16 Part 1 — the μ₄ key criterion, field shape (model `C132kp3`) -/

/-- ★ **D3-16 — the literal μ₄ `key_criterion`** (the `FGMNSourceLaws.key_criterion`
field shape at `(e', f', u') = (2, 1, 85)`, `r = 3`): at the depth-three recipe degree
`2·1·deg(keyAt 3) = 16`, monicity, residual irreducibility, residual degree one, and a
nonzero residual scalar assemble μ₄-minimality and μ₄-irreducibility into
key-polynomialhood. -/
theorem s2Mu4_key_criterion :
    ∀ g : Polynomial O, g.Monic →
      g.natDegree = 2 * 1 * ((s2DepthThreeKeyChain h2 hq).keyAt 3).natDegree →
      Irreducible (s2Mu4NormRes h2 hq g) →
      (s2Mu4NormRes h2 hq g).natDegree = 1 →
      (s2Mu4NormRes h2 hq g).coeff 0 ≠ 0 →
      S2Mu4KeyPoly h2 hq g := by
  intro g hmon hdeg hirr _ _
  have hkd : ((s2DepthThreeKeyChain h2 hq).keyAt 3).natDegree = 8 :=
    s2DepthThreeKeyAt_natDegree_three h2 hq
  have hdeg16 : g.natDegree = 16 := by
    rw [hdeg, hkd]
  refine ⟨hmon, s2Mu4Minimal_of_irreducible_normRes h2 hq hdeg16 hirr, ?_⟩
  exact s2Mu4Irreducible_of_irreducible_normRes h2 hq hmon (by omega) hirr

/-! ## D3-16 Part 2 — irreducibility of μ₄ key polynomials (model `C132kp5`) -/

/-- ★ **D3-16 — every μ₄ key polynomial is irreducible over `O`** (model
`C132kp5.s2Mu3_key_irreducible`: μ₄-primality splits a factorization, μ₄-minimality
excludes either strictly smaller factor). -/
theorem s2Mu4_key_irreducible {g : Polynomial O} (hkey : S2Mu4KeyPoly h2 hq g) :
    Irreducible g := by
  obtain ⟨hmon, hmin, hirr⟩ := hkey
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have hzero := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hpos := hmin.1
    omega
  · by_contra hcon
    have hua : ¬ IsUnit a := fun ha => hcon (Or.inl ha)
    have hub : ¬ IsUnit b := fun hb => hcon (Or.inr hb)
    have hg0 : g ≠ 0 := hmon.ne_zero
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hg0 (by rw [hab, zero_mul])
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hg0 (by rw [hab, mul_zero])
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hab]
      exact hmon.leadingCoeff
    have hdega : 0 < a.natDegree := by
      rcases Nat.eq_zero_or_pos a.natDegree with hzero | hpos
      · exfalso
        refine hua ?_
        have hCa : a = Polynomial.C (a.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero hzero
        rw [hCa] at hlc
        rw [Polynomial.leadingCoeff_C] at hlc
        rw [hCa]
        exact Polynomial.isUnit_C.mpr (.of_mul_eq_one _ hlc)
      · exact hpos
    have hdegb : 0 < b.natDegree := by
      rcases Nat.eq_zero_or_pos b.natDegree with hzero | hpos
      · exfalso
        refine hub ?_
        have hCb : b = Polynomial.C (b.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero hzero
        rw [hCb] at hlc
        rw [Polynomial.leadingCoeff_C] at hlc
        rw [hCb]
        exact Polynomial.isUnit_C.mpr (.of_mul_eq_one _ (by rw [mul_comm]; exact hlc))
      · exact hpos
    have hdeg : a.natDegree + b.natDegree = g.natDegree := by
      rw [hab, Polynomial.natDegree_mul ha0 hb0]
    have hself : S2Mu4Dvd h2 hq g (a * b) :=
      S2Mu4Dvd_of_dvd h2 hq (dvd_of_eq hab)
    rcases hirr.2.2 a b hself with hdvd | hdvd
    · exact hmin.2 a ha0 (by omega) hdvd
    · exact hmin.2 b hb0 (by omega) hdvd

/-! ## D3-16 Part 3 — ★ the `g16` key theorem -/

/-- ★ **D3-16 — `g16` is a μ₄ key polynomial**: D3-14's landed monic degree-16
`g16 = g₈² − 2⁸Φ₂` with normalized μ₄ residual `X + 1` (irreducible, degree one, nonzero
constant) satisfies the criterion (model `C136t.s2Mu3KeyPoly_g8`, one level up). -/
theorem s2Mu4KeyPoly_g16 : S2Mu4KeyPoly h2 hq (g16 h2 hq) := by
  refine s2Mu4_key_criterion h2 hq (g16 h2 hq) (g16_monic h2 hq) ?_ ?_ ?_ ?_
  · rw [show ((s2DepthThreeKeyChain h2 hq).keyAt 3).natDegree = 8 from
      s2DepthThreeKeyAt_natDegree_three h2 hq]
    exact g16_natDegree h2 hq
  · rw [s2Mu4NormRes_g16 h2 hq]
    exact s2Mu3_X_add_one_irreducible h2 hq
  · rw [s2Mu4NormRes_g16 h2 hq, ← Polynomial.C_1, Polynomial.natDegree_X_add_C]
  · rw [s2Mu4NormRes_g16 h2 hq]
    simp

/-! ## D3-17 Part 0 — initial forms through the μ₄ graded piece (model `C132kp4`) -/

/-- The S2-specialized μ₄ term bound (wrapper over `C136d0.dv3Supp_le_term`). -/
private theorem dv3Supp_le_term_s2 (f : Polynomial O) (j : ℕ) :
    dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
        f 85 2
      ≤ 2 • dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) f j + (85 * j : ℕ∞) :=
  C136d0.dv3Supp_le_term ((s2Tower h2 hq).levelDatum h2) (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) 21 (by norm_num) f 85 (by norm_num) j

private theorem s2Mu4GradedRes_neg_of_le {β : ℕ} {g : Polynomial O}
    (hg : (β : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g 85 2) :
    s2Mu4GradedRes h2 hq β (-g) = -s2Mu4GradedRes h2 hq β g := by
  have hneg : (β : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) (-g) 85 2 := by
    rw [dv3Supp_neg _ (s2Φ₂_monic h2 hq) 21 2 (s2g8_monic h2 hq) g 85 2]
    exact hg
  have hsum := s2Mu4GradedRes_add_of_le h2 hq hg hneg
  rw [add_neg_cancel, s2Mu4GradedRes_zero] at hsum
  linear_combination hsum.symm

private theorem mu4_initialEquiv_iff_gradedRes {β : ℕ} {g h : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hh : S2Mu4ExactGrade h2 hq β h) :
    S2Mu4InitialEquiv h2 hq g h ↔
      s2Mu4GradedRes h2 hq β g = s2Mu4GradedRes h2 hq β h := by
  have hvg : s2Hgt₄ h2 hq g = (β : WithTop ℤ) := hg
  have hvh : s2Hgt₄ h2 hq h = (β : WithTop ℤ) := hh
  constructor
  · intro hgh
    rcases hgh with ⟨hlt, -⟩ | ⟨hg0, -⟩
    · have habove : S2Mu4AboveGrade h2 hq β (g - h) := by
        show (β : WithTop ℤ) < s2Hgt₄ h2 hq (g - h)
        rw [← hvg]
        exact hlt
      have hdecomp : g = h + (g - h) := by ring
      have hadd := s2Mu4GradedRes_add_of_le h2 hq
        (le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hh).symm)
        (le_of_lt ((S2Mu4AboveGrade_iff_dv3Supp h2 hq).mp habove))
      rw [← hdecomp, s2Mu4GradedRes_zero_of_above h2 hq habove, add_zero] at hadd
      exact hadd
    · exact absurd hg0 (S2Mu4ExactGrade_not_zero h2 hq hg)
  · intro hres
    rcases eq_or_ne (g - h) 0 with hgh0 | hgh0
    · rw [sub_eq_zero.mp hgh0]
      exact S2Mu4InitialEquiv_refl h2 hq h
    · have hnegh : S2Mu4ExactGrade h2 hq β (-h) := by
        rw [S2Mu4ExactGrade_iff_dv3Supp,
          dv3Supp_neg _ (s2Φ₂_monic h2 hq) 21 2 (s2g8_monic h2 hq) h 85 2]
        exact (S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hh
      have hvneg : s2Hgt₄ h2 hq (-h) = (β : WithTop ℤ) := hnegh
      have hge : (β : WithTop ℤ) ≤ s2Hgt₄ h2 hq (g - h) := by
        have hmin := s2Hgt₄_add_ge h2 hq g (-h)
        rw [← sub_eq_add_neg, hvg, hvneg, min_self] at hmin
        exact hmin
      rcases hge.lt_or_eq with hlt | heqv
      · refine Or.inl ⟨?_, hvg.trans hvh.symm⟩
        rw [hvg]
        exact hlt
      · have hexact : S2Mu4ExactGrade h2 hq β (g - h) := heqv.symm
        have hne := s2Mu4GradedRes_ne_zero_of_exact h2 hq hexact
        have hadd := s2Mu4GradedRes_add_of_le h2 hq
          (le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hg).symm)
          (le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hnegh).symm)
        rw [← sub_eq_add_neg,
          s2Mu4GradedRes_neg_of_le h2 hq
            (le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hh).symm),
          hres, add_neg_cancel] at hadd
        exact absurd hadd hne

/-! ## D3-17 Part 1 — the odd-carry obstruction and minimality (model `C132kp4`) -/

private theorem not_mu4Dvd_g8_of_even_grade {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (heven : 2 ∣ β)
    (hc : (s2Mu4GradedRes h2 hq β g).coeff 0 ≠ 0) :
    ¬ S2Mu4Dvd h2 hq (g8 h2 hq) g := by
  rintro ⟨q, hq'⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero] at hq'
    exact S2Mu4ExactGrade_not_zero h2 hq hg
      ((S2Mu4InitialEquiv_zero_right h2 hq).mp hq')
  · obtain ⟨β', hβ'⟩ := S2Mu4ExactGrade_exists h2 hq hq0
    have hkq : S2Mu4ExactGrade h2 hq (85 + β')
        ((g8 h2 hq : Polynomial O) * q) :=
      S2Mu4ExactGrade_mul h2 hq (tooth_g8 h2 hq) hβ'
    have hgkq : S2Mu4ExactGrade h2 hq β
        ((g8 h2 hq : Polynomial O) * q) :=
      S2Mu4ExactGrade_of_initialEquiv h2 hq hg hq'
    have hβeq : β = 85 + β' := S2Mu4ExactGrade_unique h2 hq hgkq hkq
    subst hβeq
    have hres := (mu4_initialEquiv_iff_gradedRes h2 hq hg hgkq).mp hq'
    have hmul := s2Mu4GradedRes_mul_of_exact h2 hq (tooth_g8 h2 hq) hβ'
    rw [s2Mu4GradedRes_key h2 hq, one_mul,
      show 85 % 2 * (β' % 2) = 1 by omega, pow_one] at hmul
    rw [hmul] at hres
    apply hc
    rw [hres, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]

/-- **the μ₄ parity fence**: an exact μ₄ grade of a polynomial of degree below the
development key's `8` is even (slot 0 is the only live slot; the grade line reads
`2m + 85·0`).  This is also the engine of the D3-18 recipe vacuity. -/
theorem s2Mu4ExactGrade_even_of_natDegree_lt_eight {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hdeg : g.natDegree < 8) : 2 ∣ β := by
  obtain ⟨s, hgate⟩ := exists_mu4SlotOnGrade_of_exact h2 hq hg
  have hs0 : s = 0 := by
    by_contra hs
    obtain ⟨m, hm, -⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp hgate
    have hdev : dev (g8 h2 hq) g s = 0 :=
      dev_eq_zero_of_lt (s2g8_monic h2 hq)
        (by rw [s2g8_natDegree h2 hq]; norm_num) g s
        (by rw [s2g8_natDegree h2 hq]; omega)
    have htop : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) g s = ⊤ := by
      rw [dv3Pin, hdev]
      exact dv3Hgt_zero _ _ _ (by norm_num)
    rw [htop] at hm
    exact WithTop.top_ne_coe hm
  subst hs0
  obtain ⟨m, -, hline⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp hgate
  exact ⟨m, by omega⟩

private theorem mu4Minimal_g8 : S2Mu4Minimal h2 hq (g8 h2 hq) := by
  refine ⟨by rw [s2g8_natDegree h2 hq]; omega, fun g hg0 hdeg hdvd => ?_⟩
  rw [s2g8_natDegree h2 hq] at hdeg
  obtain ⟨β, hβ⟩ := S2Mu4ExactGrade_exists h2 hq hg0
  exact not_mu4Dvd_g8_of_even_grade h2 hq hβ
    (s2Mu4ExactGrade_even_of_natDegree_lt_eight h2 hq hβ hdeg)
    (s2Mu4GradedRes_coeff_zero_ne_zero_of_exact h2 hq hβ hdeg) hdvd

private theorem not_mu4Dvd_g8_one :
    ¬ S2Mu4Dvd h2 hq (g8 h2 hq) (1 : Polynomial O) :=
  (mu4Minimal_g8 h2 hq).2 1 one_ne_zero
    (by rw [Polynomial.natDegree_one, s2g8_natDegree h2 hq]; omega)

/-! ## D3-17 Part 2 — the slot-zero test and primality (model `C132kp4`) -/

private theorem mu4Coeff_ne_zero_of_slot {β s : ℕ} {g : Polynomial O}
    (hgate : S2Mu4SlotOnGrade h2 hq β g s) :
    s2Mu4Coeff h2 hq β g (s / 2) ≠ 0 := by
  have hinner : S2Mu3ExactGrade h2 hq ((β - 85 * s) / 2) (dev (g8 h2 hq) g s) :=
    s2Mu4SlotOnGrade_inner_exact h2 hq hgate
  have hdeg : (dev (g8 h2 hq) g s).natDegree < 8 := by
    rcases eq_or_ne (dev (g8 h2 hq) g s) 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      norm_num
    · have h := Polynomial.natDegree_lt_natDegree h0
        (degree_dev_lt (s2g8_monic h2 hq)
          (by rw [s2g8_natDegree h2 hq]; norm_num) g s)
      rwa [s2g8_natDegree h2 hq] at h
  have hcoeff := s2Mu4Coeff_slot h2 hq hgate
  rw [s2Mu4Eps_eq_one, one_mul,
    eval_one_s2Mu3GradedRes_eq_coeff_zero h2 hq hdeg] at hcoeff
  rw [hcoeff]
  intro hc0
  have hzero : s2Mu3GradedRes h2 hq ((β - 85 * s) / 2) (dev (g8 h2 hq) g s) = 0 := by
    rw [s2Mu3GradedRes_eq_C_of_natDegree_lt_eight h2 hq hdeg, hc0, Polynomial.C_0]
  exact C132rp8.s2Mu3GradedRes_ne_zero_of_exact h2 hq hinner hzero

private theorem not_mu4Dvd_g8_of_slotZero {β : ℕ} {f : Polynomial O}
    (hf : S2Mu4ExactGrade h2 hq β f) (hgate : S2Mu4SlotOnGrade h2 hq β f 0) :
    ¬ S2Mu4Dvd h2 hq (g8 h2 hq) f := by
  obtain ⟨m, -, hline⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp hgate
  have heven : 2 ∣ β := ⟨m, by omega⟩
  have hc : (s2Mu4GradedRes h2 hq β f).coeff 0 ≠ 0 := by
    rw [s2Mu4GradedRes_coeff]
    simpa using (mu4Coeff_ne_zero_of_slot (O := O) h2 hq
      (β := β) (s := 0) (g := f) hgate)
  exact not_mu4Dvd_g8_of_even_grade h2 hq hf heven hc

private theorem mu4Dvd_g8_of_not_slotZero {β : ℕ} {f : Polynomial O}
    (hf : S2Mu4ExactGrade h2 hq β f) (hgate : ¬ S2Mu4SlotOnGrade h2 hq β f 0) :
    S2Mu4Dvd h2 hq (g8 h2 hq) f := by
  have hmon : (g8 h2 hq : Polynomial O).Monic := s2g8_monic h2 hq
  have hmod : f %ₘ (g8 h2 hq) + (g8 h2 hq) * (f /ₘ (g8 h2 hq)) = f :=
    Polynomial.modByMonic_add_div f (g8 h2 hq)
  rcases eq_or_ne (f %ₘ (g8 h2 hq)) 0 with hr0 | hr0
  · exact S2Mu4Dvd_of_dvd h2 hq ((Polynomial.modByMonic_eq_zero_iff_dvd hmon).mp hr0)
  have hdegr : (f %ₘ (g8 h2 hq)).natDegree < 8 := by
    have h := Polynomial.natDegree_lt_natDegree hr0 (Polynomial.degree_modByMonic_lt f hmon)
    rwa [s2g8_natDegree h2 hq] at h
  have hdevr : dev (g8 h2 hq) (f %ₘ (g8 h2 hq)) 0 = f %ₘ (g8 h2 hq) := by
    rw [dev_zero_pin]
    exact (Polynomial.modByMonic_eq_self_iff hmon).mpr (Polynomial.degree_modByMonic_lt f hmon)
  have hsupp_r : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) (f %ₘ (g8 h2 hq)) 85 2 =
      2 • dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) f 0 := by
    rw [dv3Supp_eq_inf_range ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21
      (by norm_num) (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) _ (M := 8) hdegr,
      show Finset.range 8 = {0, 1, 2, 3, 4, 5, 6, 7} by decide,
      Finset.inf_insert, Finset.inf_insert, Finset.inf_insert, Finset.inf_insert,
      Finset.inf_insert, Finset.inf_insert, Finset.inf_insert, Finset.inf_singleton]
    have hpin (j : ℕ) (hj : 0 < j) :
        dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) (f %ₘ (g8 h2 hq)) j = ⊤ := by
      rw [dv3Pin, dev_eq_zero_of_lt hmon
        (by rw [s2g8_natDegree h2 hq]; norm_num) _ j
        (by rw [s2g8_natDegree h2 hq]; omega)]
      exact dv3Hgt_zero _ _ _ (by norm_num)
    simp only [hpin 1 (by norm_num), hpin 2 (by norm_num), hpin 3 (by norm_num),
      hpin 4 (by norm_num), hpin 5 (by norm_num), hpin 6 (by norm_num),
      hpin 7 (by norm_num),
      C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add,
      Nat.cast_zero, mul_zero, add_zero]
    simp only [min_eq_left le_top]
    rw [show dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) (f %ₘ (g8 h2 hq)) 0 =
        dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) f 0 by
      rw [dv3Pin, hdevr, dv3Pin, dev_zero_pin]]
  have hle : (β : ℕ∞) ≤ 2 • dv3Pin ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) f 0 := by
    have hterm := dv3Supp_le_term_s2 h2 hq f 0
    rw [(S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hf] at hterm
    simpa using hterm
  have hne : 2 • dv3Pin ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) f 0 ≠ (β : ℕ∞) := by
    intro heq
    have hfin : dv3Pin ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) f 0 ≠ ⊤ := by
      intro htop
      rw [htop, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2)] at heq
      exact WithTop.top_ne_coe heq
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    refine hgate ((s2Mu4SlotOnGrade_iff h2 hq).mpr ⟨m, hm.symm, ?_⟩)
    rw [← hm, nsmul_eq_mul] at heq
    have h2m : (2 * m : ℕ) = β := by exact_mod_cast heq
    omega
  have hltE : (β : ℕ∞) < 2 • dv3Pin ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) f 0 :=
    lt_of_le_of_ne hle (Ne.symm hne)
  have hgt : s2Hgt₄ h2 hq f < s2Hgt₄ h2 hq (f %ₘ (g8 h2 hq)) := by
    have hvf : s2Hgt₄ h2 hq f = (β : WithTop ℤ) := hf
    rw [hvf, s2Hgt₄_eq_dv3Supp, hsupp_r,
      show (β : WithTop ℤ) = C130s6.toZ (β : ℕ∞) by norm_cast]
    exact toZ_lt_toZ_iff.mpr hltE
  have hkw : (g8 h2 hq) * (f /ₘ (g8 h2 hq)) = f - f %ₘ (g8 h2 hq) :=
    (sub_eq_of_eq_add' hmod.symm).symm
  have hval_kw : s2Hgt₄ h2 hq ((g8 h2 hq) * (f /ₘ (g8 h2 hq))) = s2Hgt₄ h2 hq f := by
    rw [hkw, sub_eq_add_neg,
      s2Hgt₄_add_eq h2 hq _ _ (by rw [s2Hgt₄_neg h2 hq]; exact ne_of_lt hgt),
      s2Hgt₄_neg h2 hq]
    exact min_eq_left (le_of_lt hgt)
  refine ⟨f /ₘ (g8 h2 hq), Or.inl ⟨?_, hval_kw.symm⟩⟩
  rw [show f - (g8 h2 hq) * (f /ₘ (g8 h2 hq)) = f %ₘ (g8 h2 hq) by rw [hkw]; ring]
  exact hgt

private theorem mu4Dvd_g8_of_odd_grade {β : ℕ} {f : Polynomial O}
    (hf : S2Mu4ExactGrade h2 hq β f) (hodd : β % 2 = 1) :
    S2Mu4Dvd h2 hq (g8 h2 hq) f :=
  mu4Dvd_g8_of_not_slotZero h2 hq hf fun hgate => by
    obtain ⟨m, -, hline⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp hgate
    omega

private theorem mu4Dvd_g8_or (a b : Polynomial O)
    (hdvd : S2Mu4Dvd h2 hq (g8 h2 hq) (a * b)) :
    S2Mu4Dvd h2 hq (g8 h2 hq) a ∨ S2Mu4Dvd h2 hq (g8 h2 hq) b := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inl (S2Mu4Dvd_zero h2 hq _)
  rcases eq_or_ne b 0 with rfl | hb0
  · exact Or.inr (S2Mu4Dvd_zero h2 hq _)
  have hexa := S2Mu4ExactGrade_s2Mu4GradeOf h2 hq ha0
  have hexb := S2Mu4ExactGrade_s2Mu4GradeOf h2 hq hb0
  rcases Nat.mod_two_eq_zero_or_one (s2Mu4GradeOf h2 hq a) with hpa | hpa
  swap
  · exact Or.inl (mu4Dvd_g8_of_odd_grade h2 hq hexa hpa)
  rcases Nat.mod_two_eq_zero_or_one (s2Mu4GradeOf h2 hq b) with hpb | hpb
  swap
  · exact Or.inr (mu4Dvd_g8_of_odd_grade h2 hq hexb hpb)
  by_cases hga : S2Mu4SlotOnGrade h2 hq (s2Mu4GradeOf h2 hq a) a 0
  swap
  · exact Or.inl (mu4Dvd_g8_of_not_slotZero h2 hq hexa hga)
  by_cases hgb : S2Mu4SlotOnGrade h2 hq (s2Mu4GradeOf h2 hq b) b 0
  swap
  · exact Or.inr (mu4Dvd_g8_of_not_slotZero h2 hq hexb hgb)
  exfalso
  have hexab := S2Mu4ExactGrade_mul h2 hq hexa hexb
  have heven : 2 ∣ s2Mu4GradeOf h2 hq a + s2Mu4GradeOf h2 hq b := by omega
  have hca : (s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq a) a).coeff 0 ≠ 0 := by
    rw [s2Mu4GradedRes_coeff]
    simpa using (mu4Coeff_ne_zero_of_slot (O := O) h2 hq
      (β := s2Mu4GradeOf h2 hq a) (s := 0) (g := a) hga)
  have hcb : (s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq b) b).coeff 0 ≠ 0 := by
    rw [s2Mu4GradedRes_coeff]
    simpa using (mu4Coeff_ne_zero_of_slot (O := O) h2 hq
      (β := s2Mu4GradeOf h2 hq b) (s := 0) (g := b) hgb)
  have hcab :
      (s2Mu4GradedRes h2 hq (s2Mu4GradeOf h2 hq a + s2Mu4GradeOf h2 hq b)
        (a * b)).coeff 0 ≠ 0 := by
    rw [s2Mu4GradedRes_mul_of_exact h2 hq hexa hexb, hpa, hpb,
      show (0 * 0 : ℕ) = 0 from rfl, pow_zero, one_mul, Polynomial.mul_coeff_zero]
    exact mul_ne_zero hca hcb
  exact not_mu4Dvd_g8_of_even_grade h2 hq hexab heven hcab hdvd

/-! ## D3-17 Part 3 — ★ the carried key -/

/-- ★ **D3-17 — the carried depth-three key `g₈ = keyAt 3` is a μ₄ key polynomial**
(published Prop 1.7(4)'s occurrence, model `C132kp4.s2Mu3KeyPoly_Φ₂` one level up:
minimality and primality via the odd-by-odd carry and the slot-zero gate — the
nonunit-residual criterion is intentionally inapplicable, `R₅(g₈) = 1`). -/
theorem s2Mu4KeyPoly_g8 : S2Mu4KeyPoly h2 hq (g8 h2 hq) := by
  refine ⟨s2g8_monic h2 hq, mu4Minimal_g8 h2 hq, ?_⟩
  exact ⟨(s2g8_monic h2 hq).ne_zero, not_mu4Dvd_g8_one h2 hq,
    fun a b hab => mu4Dvd_g8_or h2 hq a b hab⟩

/-- **D3-17 — the carried key's normalized μ₄ residual is `1`** (alias of the landed
`C136d2.s2Mu4NormRes_key`, restated under the D3-17 name). -/
theorem s2Mu4NormRes_g8 :
    s2Mu4NormRes h2 hq (g8 h2 hq : Polynomial O) = 1 :=
  s2Mu4NormRes_key h2 hq

/-- Regression tooth: the same carried polynomial reads as `1` at μ₄ but as `X + 1` at
μ₃ (model `C132kp4.tooth_Φ₂_mu3_vs_mu2`, one level up). -/
theorem tooth_g8_mu4_vs_mu3 :
    s2Mu4NormRes h2 hq (g8 h2 hq : Polynomial O) = 1 ∧
      s2Mu3NormRes h2 hq (g8 h2 hq : Polynomial O) = Polynomial.X + 1 :=
  ⟨s2Mu4NormRes_g8 h2 hq, s2Mu3NormRes_g8 h2 hq⟩

/-! ## D3-17 Part 4 — the inner monic-digit bounds (model `C132kp6b` Part 0, one level up)

The μ₂-level bounds `c₁, c₂, c₃ = 2, 5, 7` are `C132kp6b`'s file-local copies, repeated
verbatim (they are private there).  On top of them, the SEVEN μ₃-level cleared bounds for
monic digits of degree `1..7` — the inner ledger of the μ₄ divisibility pin:
`c′₁..c′₇ = 4, 10, 14, 21, 25, 31, 35` (`c′_{4a+b} = 2·c_b + 21·a`). -/

private theorem key_natDegree_two :
    ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
  rw [key_eq h2 hq]
  exact s2Key_natDegree

/-- private copy of C132kp6b's `stageHeight_one`. -/
private theorem stageHeight_one : (s2Frame h2 hq).stageHeight (1 : Polynomial O) = 0 := by
  rw [show (1 : Polynomial O) = Polynomial.C 1 by rw [map_one], sh_C h2 hq]
  simp

/-- private copy of C132kp6b's monic-linear stage bound. -/
private theorem stageHeight_le_one_of_monic_linear {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 1) : (s2Frame h2 hq).stageHeight A ≤ 1 := by
  rw [KeyFrame.stageHeight_eq_inf]
  refine le_trans (Finset.inf_le (Finset.mem_range.mpr (show 1 < A.natDegree + 1 by omega))) ?_
  have hc : A.coeff 1 = 1 := by rw [← hdeg]; exact hA.coeff_natDegree
  rw [hc]
  simp only [e1_eq h2 hq, h_eq h2 hq, gaussVal_C, AddValuation.map_one, smul_zero, zero_add]
  simp

/-- private copy of C132kp6b's degree-1 inner μ₂ bound (`c₁ = 2`). -/
private theorem dvSupp_le_of_monic_deg1 {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 1) : dvSupp (s2Frame h2 hq) A 5 2 ≤ (2 : ℕ∞) := by
  have hself : dev (s2Frame h2 hq).key A 0 = A := by
    rw [dev_zero_pin]
    refine (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr ?_
    rw [Polynomial.degree_eq_natDegree hA.ne_zero,
      Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero,
      key_natDegree_two h2 hq, hdeg]
    exact_mod_cast (by omega : 1 < 2)
  have hhgt : dvHgt (s2Frame h2 hq) A 0 ≤ (1 : ℕ∞) := by
    rw [dvHgt, hself]
    exact stageHeight_le_one_of_monic_linear h2 hq hA hdeg
  refine le_trans (dvSupp_le_term (s2Frame h2 hq) A 5 (by norm_num : (0 : ℕ) < 2) 0) ?_
  simp only [Nat.cast_zero, mul_zero, add_zero]
  rw [two_nsmul]
  calc dvHgt (s2Frame h2 hq) A 0 + dvHgt (s2Frame h2 hq) A 0
      ≤ (1 : ℕ∞) + (1 : ℕ∞) := add_le_add hhgt hhgt
    _ = 2 := one_add_one_eq_two

/-- private copy of C132kp6b's degree-2 inner μ₂ bound (`c₂ = 5`). -/
private theorem dvSupp_le_of_monic_deg2 {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 2) : dvSupp (s2Frame h2 hq) A 5 2 ≤ (5 : ℕ∞) := by
  have htop : dev (s2Frame h2 hq).key A 1 = 1 :=
    dev_top_eq_one (s2Frame h2 hq).hmonic (s2Frame h2 hq).natDegree_key_pos 1 A hA
      (by rw [key_natDegree_two h2 hq]; omega)
  have hhgt : dvHgt (s2Frame h2 hq) A 1 = 0 := by
    rw [dvHgt, htop]
    exact stageHeight_one h2 hq
  refine le_trans (dvSupp_le_term (s2Frame h2 hq) A 5 (by norm_num : (0 : ℕ) < 2) 1) ?_
  rw [hhgt, smul_zero, zero_add]
  simp only [Nat.cast_ofNat, Nat.cast_one, mul_one]
  exact le_rfl

/-- private copy of C132kp6b's degree-3 inner μ₂ bound (`c₃ = 7`). -/
private theorem dvSupp_le_of_monic_deg3 {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 3) : dvSupp (s2Frame h2 hq) A 5 2 ≤ (7 : ℕ∞) := by
  have hdle : ((s2Frame h2 hq).key : Polynomial O).degree ≤ A.degree := by
    rw [Polynomial.degree_eq_natDegree hA.ne_zero,
      Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero,
      key_natDegree_two h2 hq, hdeg]
    exact_mod_cast (by omega : 2 ≤ 3)
  have hQm : (A /ₘ (s2Frame h2 hq).key).Monic :=
    monic_divByMonic hA (s2Frame h2 hq).hmonic hdle
  have hQd : (A /ₘ (s2Frame h2 hq).key).natDegree = 1 := by
    rw [Polynomial.natDegree_divByMonic A (s2Frame h2 hq).hmonic,
      key_natDegree_two h2 hq, hdeg]
  have hd1 : dev (s2Frame h2 hq).key A 1 = A /ₘ (s2Frame h2 hq).key := by
    rw [show dev (s2Frame h2 hq).key A 1
        = dev (s2Frame h2 hq).key (A /ₘ (s2Frame h2 hq).key) 0 from rfl, dev_zero_pin]
    refine (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr ?_
    rw [Polynomial.degree_eq_natDegree hQm.ne_zero,
      Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero,
      key_natDegree_two h2 hq, hQd]
    exact_mod_cast (by omega : 1 < 2)
  have hhgt : dvHgt (s2Frame h2 hq) A 1 ≤ (1 : ℕ∞) := by
    rw [dvHgt, hd1]
    exact stageHeight_le_one_of_monic_linear h2 hq hQm hQd
  refine le_trans (dvSupp_le_term (s2Frame h2 hq) A 5 (by norm_num : (0 : ℕ) < 2) 1) ?_
  simp only [Nat.cast_ofNat, Nat.cast_one, mul_one]
  rw [two_nsmul]
  calc dvHgt (s2Frame h2 hq) A 1 + dvHgt (s2Frame h2 hq) A 1 + (5 : ℕ∞)
      ≤ (1 : ℕ∞) + (1 : ℕ∞) + (5 : ℕ∞) := add_le_add (add_le_add hhgt hhgt) le_rfl
    _ = 7 := by norm_num

/-- private copy of C132kp6b's `dvSupp_one_eq_zero` (the digit `1` at the frame). -/
private theorem dvSupp_one_eq_zero : dvSupp (s2Frame h2 hq) (1 : Polynomial O) 5 2 = 0 := by
  have hhgt : dvHgt (s2Frame h2 hq) (1 : Polynomial O) 0 = 0 := by
    rw [dvHgt, dev_zero_pin]
    have hself : (1 : Polynomial O) %ₘ (s2Frame h2 hq).key = 1 := by
      refine (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr ?_
      rw [Polynomial.degree_eq_natDegree (one_ne_zero : (1 : Polynomial O) ≠ 0),
        Polynomial.degree_eq_natDegree (s2Frame h2 hq).hmonic.ne_zero,
        Polynomial.natDegree_one, key_natDegree_two h2 hq]
      exact_mod_cast (by omega : 0 < 2)
    rw [hself]
    exact stageHeight_one h2 hq
  refine le_antisymm ?_ _root_.zero_le
  refine le_trans (dvSupp_le_term (s2Frame h2 hq) 1 5 (by norm_num : (0 : ℕ) < 2) 0) ?_
  rw [hhgt, smul_zero, zero_add]
  simp

/-- private copy of C132kp6b's `dev_phi2_top_monic` (the μ₃ top digit at fractional
degree): a monic polynomial of degree `4m + r` (`1 ≤ r ≤ 3`) has monic degree-`r` top
`Φ₂`-digit. -/
private theorem dev_phi2_top_monic :
    ∀ (m : ℕ) (A : Polynomial O) (r : ℕ), 1 ≤ r → r ≤ 3 → A.Monic →
      A.natDegree = 4 * m + r →
      (dev (s2DepthTwoKeyAt h2 hq 2) A m).Monic ∧
        (dev (s2DepthTwoKeyAt h2 hq 2) A m).natDegree = r := by
  intro m
  induction m with
  | zero =>
    intro A r hr1 hr3 hA hdeg
    have hself : dev (s2DepthTwoKeyAt h2 hq 2) A 0 = A := by
      rw [dev_zero_pin]
      refine (Polynomial.modByMonic_eq_self_iff (s2Φ₂_monic h2 hq)).mpr ?_
      rw [Polynomial.degree_eq_natDegree hA.ne_zero,
        Polynomial.degree_eq_natDegree (s2Φ₂_monic h2 hq).ne_zero,
        s2Φ₂_natDegree h2 hq, hdeg]
      exact_mod_cast (by omega : 4 * 0 + r < 4)
    rw [hself]
    exact ⟨hA, by omega⟩
  | succ m ih =>
    intro A r hr1 hr3 hA hdeg
    rw [show dev (s2DepthTwoKeyAt h2 hq 2) A (m + 1)
        = dev (s2DepthTwoKeyAt h2 hq 2) (A /ₘ (s2DepthTwoKeyAt h2 hq 2)) m from rfl]
    have hdle : ((s2DepthTwoKeyAt h2 hq 2) : Polynomial O).degree ≤ A.degree := by
      rw [Polynomial.degree_eq_natDegree hA.ne_zero,
        Polynomial.degree_eq_natDegree (s2Φ₂_monic h2 hq).ne_zero,
        s2Φ₂_natDegree h2 hq, hdeg]
      exact_mod_cast (by omega : 4 ≤ 4 * (m + 1) + r)
    refine ih _ r hr1 hr3 (monic_divByMonic hA (s2Φ₂_monic h2 hq) hdle) ?_
    rw [Polynomial.natDegree_divByMonic A (s2Φ₂_monic h2 hq), s2Φ₂_natDegree h2 hq, hdeg]
    omega

/-! ### The seven μ₃-level digit bounds `c′₁..c′₇ = 4, 10, 14, 21, 25, 31, 35` -/

/-- the μ₃ weight bound from a single pin bound (ℕ∞ level). -/
private theorem dv2Supp_le_weight_of_pin_le {A : Polynomial O} {j c : ℕ}
    (hpin : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A j
      ≤ (c : ℕ∞)) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2
      ≤ ((2 * c + 21 * j : ℕ) : ℕ∞) := by
  refine le_trans (C132nv2.dv2Supp_le_term ((s2Tower h2 hq).levelDatum h2)
    (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num) A 21
    (by norm_num : (0 : ℕ) < 2) j) ?_
  have h2c : (2 : ℕ) • dv2Pin ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) A j ≤ ((2 * c : ℕ) : ℕ∞) := by
    rw [two_nsmul]
    calc dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A j
          + dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A j
        ≤ (c : ℕ∞) + (c : ℕ∞) := add_le_add hpin hpin
      _ = ((2 * c : ℕ) : ℕ∞) := by push_cast; ring
  calc (2 : ℕ) • dv2Pin ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) A j + (21 * j : ℕ∞)
      ≤ ((2 * c : ℕ) : ℕ∞) + ((21 * j : ℕ) : ℕ∞) := by
        refine add_le_add h2c (le_of_eq ?_)
        push_cast
        ring
    _ = ((2 * c + 21 * j : ℕ) : ℕ∞) := by push_cast; ring

/-- slot-0 self-development below the μ₃ key degree. -/
private theorem dv2Pin_zero_self {A : Polynomial O} (hdeg : A.natDegree < 4) (hA : A ≠ 0) :
    dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 0
      = dvSupp (s2Frame h2 hq) A 5 2 := by
  have hself : dev (s2DepthTwoKeyAt h2 hq 2) A 0 = A := by
    rw [dev_zero_pin]
    refine (Polynomial.modByMonic_eq_self_iff (s2Φ₂_monic h2 hq)).mpr ?_
    rw [Polynomial.degree_eq_natDegree hA,
      Polynomial.degree_eq_natDegree (s2Φ₂_monic h2 hq).ne_zero,
      s2Φ₂_natDegree h2 hq]
    exact_mod_cast hdeg
  rw [dv2Pin, hself, dv2Hgt_eq_dvSupp h2 hq]

/-- `c′₁ = 4`. -/
private theorem dv2Supp_le_of_monic_deg1' {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 1) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2
      ≤ (4 : ℕ∞) := by
  have hpin : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 0
      ≤ ((2 : ℕ) : ℕ∞) := by
    rw [dv2Pin_zero_self h2 hq (by omega) hA.ne_zero]
    exact_mod_cast dvSupp_le_of_monic_deg1 h2 hq hA hdeg
  have h := dv2Supp_le_weight_of_pin_le h2 hq hpin
  exact_mod_cast h

/-- `c′₂ = 10`. -/
private theorem dv2Supp_le_of_monic_deg2' {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 2) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2
      ≤ (10 : ℕ∞) := by
  have hpin : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 0
      ≤ ((5 : ℕ) : ℕ∞) := by
    rw [dv2Pin_zero_self h2 hq (by omega) hA.ne_zero]
    exact_mod_cast dvSupp_le_of_monic_deg2 h2 hq hA hdeg
  have h := dv2Supp_le_weight_of_pin_le h2 hq hpin
  exact_mod_cast h

/-- `c′₃ = 14`. -/
private theorem dv2Supp_le_of_monic_deg3' {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 3) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2
      ≤ (14 : ℕ∞) := by
  have hpin : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 0
      ≤ ((7 : ℕ) : ℕ∞) := by
    rw [dv2Pin_zero_self h2 hq (by omega) hA.ne_zero]
    exact_mod_cast dvSupp_le_of_monic_deg3 h2 hq hA hdeg
  have h := dv2Supp_le_weight_of_pin_le h2 hq hpin
  exact_mod_cast h

/-- `c′₄ = 21` (the top digit of a monic quartic is `1`). -/
private theorem dv2Supp_le_of_monic_deg4' {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 4) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2
      ≤ (21 : ℕ∞) := by
  have htop : dev (s2DepthTwoKeyAt h2 hq 2) A 1 = 1 :=
    dev_top_eq_one (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num) 1 A hA
      (by rw [s2Φ₂_natDegree h2 hq]; omega)
  have hpin : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 1
      ≤ ((0 : ℕ) : ℕ∞) := by
    rw [dv2Pin, htop, dv2Hgt_eq_dvSupp h2 hq, dvSupp_one_eq_zero h2 hq]
    norm_num
  have h := dv2Supp_le_weight_of_pin_le h2 hq hpin
  exact_mod_cast h

/-- the slot-1 bound for monic degree `4 + b` (`1 ≤ b ≤ 3`) digits, shared engine of
`c′₅..c′₇` (the degree fence lives in the top-digit bound `hbound` itself). -/
private theorem dv2Supp_le_of_monic_deg4b' {A : Polynomial O} {c : ℕ}
    (hbound : dvSupp (s2Frame h2 hq) (dev (s2DepthTwoKeyAt h2 hq 2) A 1) 5 2
      ≤ (c : ℕ∞)) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2
      ≤ ((2 * c + 21 : ℕ) : ℕ∞) := by
  have hpin : dv2Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 1
      ≤ (c : ℕ∞) := by
    rw [dv2Pin, dv2Hgt_eq_dvSupp h2 hq]
    exact hbound
  have h := dv2Supp_le_weight_of_pin_le h2 hq hpin
  exact_mod_cast h

/-- `c′₅ = 25`. -/
private theorem dv2Supp_le_of_monic_deg5' {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 5) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2
      ≤ (25 : ℕ∞) := by
  obtain ⟨hm, hd⟩ := dev_phi2_top_monic h2 hq 1 A 1 (by omega) (by omega) hA (by omega)
  have h := dv2Supp_le_of_monic_deg4b' h2 hq (c := 2)
    (by exact_mod_cast dvSupp_le_of_monic_deg1 h2 hq hm hd)
  exact_mod_cast h

/-- `c′₆ = 31`. -/
private theorem dv2Supp_le_of_monic_deg6' {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 6) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2
      ≤ (31 : ℕ∞) := by
  obtain ⟨hm, hd⟩ := dev_phi2_top_monic h2 hq 1 A 2 (by omega) (by omega) hA (by omega)
  have h := dv2Supp_le_of_monic_deg4b' h2 hq (c := 5)
    (by exact_mod_cast dvSupp_le_of_monic_deg2 h2 hq hm hd)
  exact_mod_cast h

/-- `c′₇ = 35`. -/
private theorem dv2Supp_le_of_monic_deg7' {A : Polynomial O} (hA : A.Monic)
    (hdeg : A.natDegree = 7) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) A 21 2
      ≤ (35 : ℕ∞) := by
  obtain ⟨hm, hd⟩ := dev_phi2_top_monic h2 hq 1 A 3 (by omega) (by omega) hA (by omega)
  have h := dv2Supp_le_of_monic_deg4b' h2 hq (c := 7)
    (by exact_mod_cast dvSupp_le_of_monic_deg3 h2 hq hm hd)
  exact_mod_cast h

/-! ## D3-17 Part 5 — the μ₄ term bound in ℕ, top digits, and the top-slot pin
(model `C132kp6b` Part 1, one level up) -/

/-- **the μ₄ term bound in ℕ**: an exact μ₄ grade is at most `2c + 85j` for any
slot-`j` pin bound `c`. -/
private theorem mu4_grade_le_of_pin_le {β c j : ℕ} {g : Polynomial O}
    (hβ : S2Mu4ExactGrade h2 hq β g)
    (hc : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) g j ≤ (c : ℕ∞)) :
    β ≤ 2 * c + 85 * j := by
  have hterm := dv3Supp_le_term_s2 h2 hq g j
  rw [(S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hβ] at hterm
  have h2c : (2 : ℕ) • dv3Pin ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g j ≤ ((2 * c : ℕ) : ℕ∞) := by
    rw [two_nsmul]
    calc dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) g j
          + dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
            (g8 h2 hq) g j
        ≤ (c : ℕ∞) + (c : ℕ∞) := add_le_add hc hc
      _ = ((2 * c : ℕ) : ℕ∞) := by push_cast; ring
  have hle : ((β : ℕ) : ℕ∞) ≤ ((2 * c + 85 * j : ℕ) : ℕ∞) := by
    calc ((β : ℕ) : ℕ∞)
        ≤ 2 • dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
            (g8 h2 hq) g j + ((85 * j : ℕ) : ℕ∞) := by
          refine hterm.trans (le_of_eq ?_)
          push_cast
          ring
      _ ≤ ((2 * c : ℕ) : ℕ∞) + ((85 * j : ℕ) : ℕ∞) := add_le_add h2c le_rfl
      _ = ((2 * c + 85 * j : ℕ) : ℕ∞) := by push_cast; ring
  exact_mod_cast hle

/-- **the μ₄ top digit at fractional degree**: a monic polynomial of degree `8m + r`
(`1 ≤ r ≤ 7`) has monic degree-`r` top `g₈`-digit. -/
private theorem dev_g8_top_monic :
    ∀ (m : ℕ) (A : Polynomial O) (r : ℕ), 1 ≤ r → r ≤ 7 → A.Monic →
      A.natDegree = 8 * m + r →
      (dev (g8 h2 hq) A m).Monic ∧ (dev (g8 h2 hq) A m).natDegree = r := by
  intro m
  induction m with
  | zero =>
    intro A r hr1 hr7 hA hdeg
    have hself : dev (g8 h2 hq) A 0 = A := by
      rw [dev_zero_pin]
      refine (Polynomial.modByMonic_eq_self_iff (s2g8_monic h2 hq)).mpr ?_
      rw [Polynomial.degree_eq_natDegree hA.ne_zero,
        Polynomial.degree_eq_natDegree (s2g8_monic h2 hq).ne_zero,
        s2g8_natDegree h2 hq, hdeg]
      exact_mod_cast (by omega : 8 * 0 + r < 8)
    rw [hself]
    exact ⟨hA, by omega⟩
  | succ m ih =>
    intro A r hr1 hr7 hA hdeg
    rw [show dev (g8 h2 hq) A (m + 1) = dev (g8 h2 hq) (A /ₘ (g8 h2 hq)) m from rfl]
    have hdle : (g8 h2 hq : Polynomial O).degree ≤ A.degree := by
      rw [Polynomial.degree_eq_natDegree hA.ne_zero,
        Polynomial.degree_eq_natDegree (s2g8_monic h2 hq).ne_zero,
        s2g8_natDegree h2 hq, hdeg]
      exact_mod_cast (by omega : 8 ≤ 8 * (m + 1) + r)
    refine ih _ r hr1 hr7 (monic_divByMonic hA (s2g8_monic h2 hq) hdle) ?_
    rw [Polynomial.natDegree_divByMonic A (s2g8_monic h2 hq), s2g8_natDegree h2 hq, hdeg]
    omega

/-- the inner μ₃ cleared value of the digit `1` is `0`. -/
private theorem dv2Supp_one_eq_zero :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
      (1 : Polynomial O) 21 2 = 0 := by
  apply C130s6.toZ_inj
  rw [← s2Hgt₃_eq_dv2Supp h2 hq, s2Hgt₃_one_eq_zero h2 hq]
  rfl

/-- **the top pin at full degree**: monic of degree `8m` has slot-`m` pin `0` (the top
digit is `1`). -/
private theorem dv3Pin_top_of_monic_mul_eight {g : Polynomial O} {m : ℕ} (hmon : g.Monic)
    (hd : g.natDegree = 8 * m) :
    dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) g m = 0 := by
  rw [dv3Pin, dev_top_eq_one (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num) m g hmon
      (by rw [s2g8_natDegree h2 hq]; omega),
    dv3Hgt, dv2Supp_one_eq_zero h2 hq]

/-- **the top slot is on its own line**: monic of degree `8m` has slot `m` on the
grade-`85m` line. -/
private theorem slot_top_of_monic_mul_eight {g : Polynomial O} {m : ℕ} (hmon : g.Monic)
    (hd : g.natDegree = 8 * m) : S2Mu4SlotOnGrade h2 hq (85 * m) g m :=
  (s2Mu4SlotOnGrade_iff h2 hq).mpr
    ⟨0, by rw [dv3Pin_top_of_monic_mul_eight h2 hq hmon hd]; norm_num, by omega⟩

/-! ## D3-17 Part 6 — ★ the divisibility pin (model `C132kp6b` Part 2, one level up)

μ₄-minimality forces `8 ∣ deg`.  For `deg g = 8m + r` (`1 ≤ r ≤ 7`), the refuter is
`f := g·Q − g₈^(m+1)` with `Q := g₈^(m+1) /ₘ g`: the division identity gives
`f = −(g₈^(m+1) %ₘ g)` of degree `< deg g`, while the grade comparison
`μ₄(g·Q) ≤ 85m + 2(c′_r + c′_{8−r}) ≤ 85m + 84 < 85(m+1) = μ₄(g₈^(m+1))` makes
`f ∼μ₄ g·Q` — so `g ∣μ₄ f`, violating minimality.  The worst pair is `r = 4`:
`2(21 + 21) = 84`, tight against the floor `84 < 85`. -/

/-- ★ **the divisibility pin**: a monic μ₄-minimal polynomial has degree divisible
by 8. -/
theorem s2Mu4Minimal_natDegree_eight_dvd {g : Polynomial O} (hmon : g.Monic)
    (hmin : S2Mu4Minimal h2 hq g) : 8 ∣ g.natDegree := by
  by_contra hndvd
  obtain ⟨m, r, hr1, hr7, hd⟩ : ∃ m r, 1 ≤ r ∧ r ≤ 7 ∧ g.natDegree = 8 * m + r :=
    ⟨g.natDegree / 8, g.natDegree % 8, by omega, by omega, by omega⟩
  obtain ⟨hAmon, hAdeg⟩ := dev_g8_top_monic h2 hq m g r hr1 hr7 hmon hd
  -- the divisor and its complement
  have hg8pmon : ((g8 h2 hq : Polynomial O) ^ (m + 1)).Monic :=
    (s2g8_monic h2 hq).pow _
  have hg8pdeg : ((g8 h2 hq : Polynomial O) ^ (m + 1)).natDegree = 8 * (m + 1) := by
    rw [Polynomial.natDegree_pow, s2g8_natDegree h2 hq]
    ring
  have hdle : g.degree ≤ ((g8 h2 hq : Polynomial O) ^ (m + 1)).degree := by
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero,
      Polynomial.degree_eq_natDegree hg8pmon.ne_zero, hg8pdeg, hd]
    exact_mod_cast (by omega : 8 * m + r ≤ 8 * (m + 1))
  set Q := (g8 h2 hq : Polynomial O) ^ (m + 1) /ₘ g with hQdef
  have hQmon : Q.Monic := monic_divByMonic hg8pmon hmon hdle
  have hQdeg : Q.natDegree = 8 - r := by
    rw [hQdef, Polynomial.natDegree_divByMonic _ hmon, hg8pdeg, hd]
    omega
  have hQself : Q %ₘ (g8 h2 hq) = Q :=
    (Polynomial.modByMonic_eq_self_iff (s2g8_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by rw [s2g8_natDegree h2 hq, hQdeg]; omega))
  -- the two pin bounds, per residue
  obtain ⟨cg, cQ, hsum, hpg, hpQ⟩ : ∃ cg cQ : ℕ, cg + cQ ≤ 42 ∧
      dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) g m ≤ (cg : ℕ∞) ∧
      dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) Q 0 ≤ (cQ : ℕ∞) := by
    have hpg_eq : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) g m
        = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
            (dev (g8 h2 hq) g m) 21 2 := by
      rw [dv3Pin, dv3Hgt_eq_dv2Supp]
    have hpQ_eq : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) Q 0
        = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) Q 21 2 := by
      rw [dv3Pin, dev_zero_pin, hQself, dv3Hgt_eq_dv2Supp]
    rw [hpg_eq, hpQ_eq]
    interval_cases r
    · exact ⟨4, 35, by norm_num, dv2Supp_le_of_monic_deg1' h2 hq hAmon hAdeg,
        dv2Supp_le_of_monic_deg7' h2 hq hQmon (by omega)⟩
    · exact ⟨10, 31, by norm_num, dv2Supp_le_of_monic_deg2' h2 hq hAmon hAdeg,
        dv2Supp_le_of_monic_deg6' h2 hq hQmon (by omega)⟩
    · exact ⟨14, 25, by norm_num, dv2Supp_le_of_monic_deg3' h2 hq hAmon hAdeg,
        dv2Supp_le_of_monic_deg5' h2 hq hQmon (by omega)⟩
    · exact ⟨21, 21, by norm_num, dv2Supp_le_of_monic_deg4' h2 hq hAmon hAdeg,
        dv2Supp_le_of_monic_deg4' h2 hq hQmon (by omega)⟩
    · exact ⟨25, 14, by norm_num, dv2Supp_le_of_monic_deg5' h2 hq hAmon hAdeg,
        dv2Supp_le_of_monic_deg3' h2 hq hQmon (by omega)⟩
    · exact ⟨31, 10, by norm_num, dv2Supp_le_of_monic_deg6' h2 hq hAmon hAdeg,
        dv2Supp_le_of_monic_deg2' h2 hq hQmon (by omega)⟩
    · exact ⟨35, 4, by norm_num, dv2Supp_le_of_monic_deg7' h2 hq hAmon hAdeg,
        dv2Supp_le_of_monic_deg1' h2 hq hQmon (by omega)⟩
  -- grades
  obtain ⟨β, hβ⟩ := S2Mu4ExactGrade_exists h2 hq hmon.ne_zero
  obtain ⟨γ, hγ⟩ := S2Mu4ExactGrade_exists h2 hq hQmon.ne_zero
  have hβle : β ≤ 2 * cg + 85 * m := mu4_grade_le_of_pin_le h2 hq hβ hpg
  have hγle : γ ≤ 2 * cQ + 85 * 0 := mu4_grade_le_of_pin_le h2 hq hγ hpQ
  have hgQ : S2Mu4ExactGrade h2 hq (β + γ) (g * Q) := S2Mu4ExactGrade_mul h2 hq hβ hγ
  have hkp : S2Mu4ExactGrade h2 hq (85 * (m + 1))
      ((g8 h2 hq : Polynomial O) ^ (m + 1)) :=
    S2Mu4ExactGrade_key_pow h2 hq (m + 1)
  have hlt : β + γ < 85 * (m + 1) := by omega
  -- the perturbation carries the product's initial form
  have hltc : ((β + γ : ℕ) : WithTop ℤ) < ((85 * (m + 1) : ℕ) : WithTop ℤ) := by
    exact_mod_cast hlt
  have hvgq : s2Hgt₄ h2 hq (g * Q) = ((β + γ : ℕ) : WithTop ℤ) := hgQ
  have hvkp : s2Hgt₄ h2 hq ((g8 h2 hq : Polynomial O) ^ (m + 1))
      = ((85 * (m + 1) : ℕ) : WithTop ℤ) := hkp
  have hvf : s2Hgt₄ h2 hq (g * Q - (g8 h2 hq : Polynomial O) ^ (m + 1))
      = ((β + γ : ℕ) : WithTop ℤ) := by
    rw [sub_eq_add_neg, s2Hgt₄_add_eq h2 hq _ _ (by
        rw [s2Hgt₄_neg h2 hq, hvgq, hvkp]; exact hltc.ne), s2Hgt₄_neg h2 hq, hvgq, hvkp]
    exact min_eq_left hltc.le
  have hf_exact : S2Mu4ExactGrade h2 hq (β + γ)
      (g * Q - (g8 h2 hq : Polynomial O) ^ (m + 1)) := hvf
  have hf0 : g * Q - (g8 h2 hq : Polynomial O) ^ (m + 1) ≠ 0 :=
    S2Mu4ExactGrade_not_zero h2 hq hf_exact
  have hequiv : S2Mu4InitialEquiv h2 hq
      (g * Q - (g8 h2 hq : Polynomial O) ^ (m + 1)) (g * Q) := by
    refine Or.inl ⟨?_, ?_⟩
    · rw [show (g * Q - (g8 h2 hq : Polynomial O) ^ (m + 1)) - g * Q
          = -((g8 h2 hq : Polynomial O) ^ (m + 1)) from by ring,
        s2Hgt₄_neg h2 hq, hvkp, hvf]
      exact hltc
    · rw [hvf, hvgq]
  have hdvd : S2Mu4Dvd h2 hq g
      (g * Q - (g8 h2 hq : Polynomial O) ^ (m + 1)) := ⟨Q, hequiv⟩
  -- the degree collapse: the difference is minus the remainder
  have hmodid : (g8 h2 hq : Polynomial O) ^ (m + 1) %ₘ g + g * Q
      = (g8 h2 hq : Polynomial O) ^ (m + 1) :=
    Polynomial.modByMonic_add_div ((g8 h2 hq : Polynomial O) ^ (m + 1)) g
  have hfeq : g * Q - (g8 h2 hq : Polynomial O) ^ (m + 1)
      = -((g8 h2 hq : Polynomial O) ^ (m + 1) %ₘ g) := by
    linear_combination hmodid
  have hfdeg : (g * Q - (g8 h2 hq : Polynomial O) ^ (m + 1)).natDegree
      < g.natDegree := by
    have hR0 : (g8 h2 hq : Polynomial O) ^ (m + 1) %ₘ g ≠ 0 := by
      intro h0
      rw [hfeq, h0, neg_zero] at hf0
      exact hf0 rfl
    rw [hfeq, Polynomial.natDegree_neg]
    exact Polynomial.natDegree_lt_natDegree hR0 (Polynomial.degree_modByMonic_lt _ hmon)
  exact hmin.2 _ hf0 hfdeg hdvd

/-! ## D3-17 Part 7 — ★ the grade pin (model `C132kp6b` Part 3, one level up) -/

/-- ★ **the grade pin**: a monic μ₄-minimal polynomial has exact grade
`85·(deg g/8)`. -/
theorem s2Mu4Minimal_exactGrade {g : Polynomial O} (hmon : g.Monic)
    (hmin : S2Mu4Minimal h2 hq g) :
    S2Mu4ExactGrade h2 hq (85 * (g.natDegree / 8)) g := by
  have h8 := s2Mu4Minimal_natDegree_eight_dvd h2 hq hmon hmin
  set m := g.natDegree / 8 with hm
  have hd : g.natDegree = 8 * m := by omega
  obtain ⟨β, hβ⟩ := S2Mu4ExactGrade_exists h2 hq hmon.ne_zero
  have hle : β ≤ 2 * 0 + 85 * m :=
    mu4_grade_le_of_pin_le h2 hq hβ
      (le_of_eq (dv3Pin_top_of_monic_mul_eight h2 hq hmon hd))
  rcases (show β ≤ 85 * m from by omega).lt_or_eq with hlt | heq
  · -- strictly below the top term: the truncation `g − g₈^m` refutes minimality
    exfalso
    have hkp : S2Mu4ExactGrade h2 hq (85 * m) ((g8 h2 hq : Polynomial O) ^ m) :=
      S2Mu4ExactGrade_key_pow h2 hq m
    rcases eq_or_ne (g - (g8 h2 hq : Polynomial O) ^ m) 0 with hf0 | hf0
    · have hg : g = (g8 h2 hq : Polynomial O) ^ m := sub_eq_zero.mp hf0
      rw [hg] at hβ
      exact absurd (S2Mu4ExactGrade_unique h2 hq hβ hkp) (by omega)
    · have hltc : ((β : ℕ) : WithTop ℤ) < ((85 * m : ℕ) : WithTop ℤ) := by
        exact_mod_cast hlt
      have hvg : s2Hgt₄ h2 hq g = ((β : ℕ) : WithTop ℤ) := hβ
      have hvk : s2Hgt₄ h2 hq ((g8 h2 hq : Polynomial O) ^ m)
          = ((85 * m : ℕ) : WithTop ℤ) := hkp
      have hvf : s2Hgt₄ h2 hq (g - (g8 h2 hq : Polynomial O) ^ m)
          = ((β : ℕ) : WithTop ℤ) := by
        rw [sub_eq_add_neg, s2Hgt₄_add_eq h2 hq _ _ (by
            rw [s2Hgt₄_neg h2 hq, hvg, hvk]; exact hltc.ne), s2Hgt₄_neg h2 hq, hvg, hvk]
        exact min_eq_left hltc.le
      have hequiv : S2Mu4InitialEquiv h2 hq
          (g - (g8 h2 hq : Polynomial O) ^ m) g := by
        refine Or.inl ⟨?_, ?_⟩
        · rw [show (g - (g8 h2 hq : Polynomial O) ^ m) - g
              = -((g8 h2 hq : Polynomial O) ^ m) from by ring,
            s2Hgt₄_neg h2 hq, hvk, hvf]
          exact hltc
        · rw [hvf, hvg]
      have hdvd : S2Mu4Dvd h2 hq g (g - (g8 h2 hq : Polynomial O) ^ m) :=
        ⟨1, by rw [mul_one]; exact hequiv⟩
      have hkm : ((g8 h2 hq : Polynomial O) ^ m).Monic :=
        (s2g8_monic h2 hq).pow m
      have hdeg_eq : g.degree = ((g8 h2 hq : Polynomial O) ^ m).degree := by
        rw [Polynomial.degree_eq_natDegree hmon.ne_zero,
          Polynomial.degree_eq_natDegree hkm.ne_zero, Polynomial.natDegree_pow,
          s2g8_natDegree h2 hq, hd, Nat.mul_comm]
      have hdlt := Polynomial.degree_sub_lt hdeg_eq hmon.ne_zero
        (by rw [hmon.leadingCoeff, hkm.leadingCoeff])
      exact hmin.2 _ hf0 (Polynomial.natDegree_lt_natDegree hf0 hdlt) hdvd
  · rw [← heq]
    exact hβ

/-! ## D3-17 Part 8 — ★ the slot-0 pin (model `C132kp6b` Part 7, one level up)

A μ₄ key of degree `> 8` has slot 0 ON the grade line — one-step deflation: an off-line
slot 0 factors the initial form as `g₈·q`; primality forces `g ∣μ₄ g₈` (killed by
minimality, `deg g₈ = 8 < deg g`) or `g ∣μ₄ q` (killed by the grade ledger:
`β = 85 + γ` and `γ = β + γ′` cannot both hold in ℕ). -/

/-- ★ **the slot-0 pin**: a μ₄ key polynomial of degree `> 8` has slot 0 on its grade
line. -/
theorem s2Mu4KeyPoly_slotZero {g : Polynomial O} {β : ℕ} (hkey : S2Mu4KeyPoly h2 hq g)
    (hβ : S2Mu4ExactGrade h2 hq β g) (hdeg : 8 < g.natDegree) :
    S2Mu4SlotOnGrade h2 hq β g 0 := by
  obtain ⟨hmon, hmin, -, -, hprime⟩ := hkey
  by_contra hgate
  obtain ⟨q, hq'⟩ := mu4Dvd_g8_of_not_slotZero h2 hq hβ hgate
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq'
    exact hmon.ne_zero ((S2Mu4InitialEquiv_zero_right h2 hq).mp hq')
  have hprod : S2Mu4Dvd h2 hq g ((g8 h2 hq : Polynomial O) * q) :=
    ⟨1, by rw [mul_one]; exact S2Mu4InitialEquiv_symm h2 hq hq'⟩
  rcases hprime _ _ hprod with hL | hR
  · -- `g ∣μ₄ g₈` refutes minimality
    exact hmin.2 _ (s2g8_monic h2 hq).ne_zero
      (by rw [s2g8_natDegree h2 hq]; omega) hL
  · -- `g ∣μ₄ q` refutes the grade ledger
    obtain ⟨q', hq''⟩ := hR
    have hq'0 : q' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq''
      exact hq0 ((S2Mu4InitialEquiv_zero_right h2 hq).mp hq'')
    obtain ⟨γ, hγ⟩ := S2Mu4ExactGrade_exists h2 hq hq0
    obtain ⟨γ', hγ'⟩ := S2Mu4ExactGrade_exists h2 hq hq'0
    have hkq : S2Mu4ExactGrade h2 hq (85 + γ)
        ((g8 h2 hq : Polynomial O) * q) :=
      S2Mu4ExactGrade_mul h2 hq (tooth_g8 h2 hq) hγ
    have hkqβ : S2Mu4ExactGrade h2 hq β
        ((g8 h2 hq : Polynomial O) * q) :=
      S2Mu4ExactGrade_of_initialEquiv h2 hq hβ hq'
    have h1 : β = 85 + γ := S2Mu4ExactGrade_unique h2 hq hkqβ hkq
    have hgq' : S2Mu4ExactGrade h2 hq (β + γ') (g * q') :=
      S2Mu4ExactGrade_mul h2 hq hβ hγ'
    have hq2 : S2Mu4ExactGrade h2 hq (β + γ') q :=
      S2Mu4ExactGrade_of_initialEquiv h2 hq hgq' (S2Mu4InitialEquiv_symm h2 hq hq'')
    have h2' : γ = β + γ' := S2Mu4ExactGrade_unique h2 hq hγ hq2
    omega

/-! ## D3-17 Part 9 — the key-structure master and the bank (model `C132kp6b` Part 8) -/

private theorem key_master {g : Polynomial O} (hkey : S2Mu4KeyPoly h2 hq g) :
    8 ∣ g.natDegree
    ∧ S2Mu4ExactGrade h2 hq (85 * (g.natDegree / 8)) g
    ∧ S2Mu4SlotOnGrade h2 hq (85 * (g.natDegree / 8)) g (g.natDegree / 8 % 2)
    ∧ (g.natDegree / 8 = 1 ∨ 2 ∣ g.natDegree / 8) := by
  obtain ⟨hmon, hmin, hirr⟩ := hkey
  have h8 := s2Mu4Minimal_natDegree_eight_dvd h2 hq hmon hmin
  have hβ := s2Mu4Minimal_exactGrade h2 hq hmon hmin
  have hpos : 0 < g.natDegree := hmin.1
  rcases Nat.lt_or_ge 8 g.natDegree with hbig | hsmall
  · -- `deg g > 8`: the slot-0 pin fires, the grade is even
    have h0 := s2Mu4KeyPoly_slotZero h2 hq ⟨hmon, hmin, hirr⟩ hβ hbig
    have hm2 : 2 ∣ g.natDegree / 8 := by
      obtain ⟨c, -, hc⟩ := (s2Mu4SlotOnGrade_iff h2 hq).mp h0
      omega
    refine ⟨h8, hβ, ?_, Or.inr hm2⟩
    rw [show g.natDegree / 8 % 2 = 0 from by omega]
    exact h0
  · -- `deg g = 8`: the top slot IS the parity slot (grade 85, odd)
    have hd8 : g.natDegree = 8 := by omega
    have htop := slot_top_of_monic_mul_eight h2 hq hmon (m := 1) (by omega)
    refine ⟨h8, hβ, ?_, Or.inl (by omega)⟩
    rw [show g.natDegree / 8 = 1 from by omega]
    exact htop

/-- **the grade of a μ₄ key polynomial**: `μ₄(g) = 85·(deg g/8)`. -/
theorem s2Mu4KeyPoly_exactGrade {g : Polynomial O} (hkey : S2Mu4KeyPoly h2 hq g) :
    S2Mu4ExactGrade h2 hq (85 * (g.natDegree / 8)) g :=
  (key_master h2 hq hkey).2.1

/-- **the residual scalar of a μ₄ key polynomial is nonzero** (the lowest `y`-coefficient
lives). -/
theorem s2Mu4KeyPoly_gradedRes_coeff_zero_ne_zero {g : Polynomial O}
    (hkey : S2Mu4KeyPoly h2 hq g) :
    (s2Mu4GradedRes h2 hq (85 * (g.natDegree / 8)) g).coeff 0 ≠ 0 := by
  obtain ⟨-, -, hlow, -⟩ := key_master h2 hq hkey
  have h := mu4Coeff_ne_zero_of_slot h2 hq hlow
  rw [show g.natDegree / 8 % 2 / 2 = 0 from by omega] at h
  rw [s2Mu4GradedRes_coeff]
  exact h

/-- ★ **the strip is trivial on μ₄ keys**: the normalized residual of a key polynomial IS
its graded residual at the pinned grade — the trailing `y`-power is `0`. -/
theorem s2Mu4KeyPoly_normRes_eq_gradedRes {g : Polynomial O}
    (hkey : S2Mu4KeyPoly h2 hq g) :
    s2Mu4NormRes h2 hq g = s2Mu4GradedRes h2 hq (85 * (g.natDegree / 8)) g := by
  have hβ := s2Mu4KeyPoly_exactGrade h2 hq hkey
  have hntd : (s2Mu4GradedRes h2 hq (85 * (g.natDegree / 8)) g).natTrailingDegree = 0 :=
    Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero
      (s2Mu4KeyPoly_gradedRes_coeff_zero_ne_zero h2 hq hkey))
  rw [s2Mu4NormRes_of_exact h2 hq hβ, hntd]
  exact Function.iterate_zero_apply _ _

/-- **the residual degree of a μ₄ key polynomial**: `deg R₅(g) = deg g/16` (published
Corollary 4.4's `s′ − s = e·deg R` at `s = 0`, `e = 2`, with `deg g = 8s′`). -/
theorem s2Mu4KeyPoly_normRes_natDegree {g : Polynomial O}
    (hkey : S2Mu4KeyPoly h2 hq g) :
    (s2Mu4NormRes h2 hq g).natDegree = g.natDegree / 16 := by
  have h8 := (key_master h2 hq hkey).1
  rw [s2Mu4KeyPoly_normRes_eq_gradedRes h2 hq hkey]
  refine le_antisymm ?_ ?_
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    rw [s2Mu4GradedRes_coeff]
    refine s2Mu4Coeff_eq_zero_of_dv3Pin_top h2 hq ?_
    rw [dv3Pin, dev_eq_zero_of_lt (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num)]
    · exact dv3Hgt_zero _ _ _ (by norm_num)
    · rw [s2g8_natDegree h2 hq]
      omega
  · have htop := slot_top_of_monic_mul_eight h2 hq hkey.1
      (m := g.natDegree / 8) (by omega)
    have h := mu4Coeff_ne_zero_of_slot h2 hq htop
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [s2Mu4GradedRes_coeff, show g.natDegree / 16 = g.natDegree / 8 / 2 from by omega]
    exact h

/-- ★ **the μ₄ degree dictionary**: a μ₄ key polynomial's degree is determined by its
normalized residual — `deg g/8 = 1` (the `∼ g₈` fiber) or
`deg g/8 = 2·deg R₅(g)` (equivalently `deg g = 16·deg R₅(g)`). -/
theorem s2Mu4KeyPoly_natDegree_pin {g : Polynomial O} (hkey : S2Mu4KeyPoly h2 hq g) :
    g.natDegree / 8 = 1 ∨ g.natDegree / 8 = 2 * (s2Mu4NormRes h2 hq g).natDegree := by
  obtain ⟨h8, -, -, hpar⟩ := key_master h2 hq hkey
  have hdeg := s2Mu4KeyPoly_normRes_natDegree h2 hq hkey
  rcases hpar with h1 | h2'
  · exact Or.inl h1
  · right
    rw [hdeg]
    omega

/-! ## D3-17 Part 10 — ★★ the converse and the assembled Prop-5.6 field -/

/-- ★★ **D3-17, the converse** (published Prop 5.6's (2)→(3), the hard direction, at the
μ₄ operators; model `C132kp6b.s2Mu3_residual_to_initial` one level up): residual equality
forces initial equivalence for μ₄ key polynomials.  The dictionary forces equal degrees,
hence equal grades `85·(deg/8)`; the trivial strip turns residual equality into graded
equality at the common exact grade; the graded-piece IFF fires backward. -/
theorem s2Mu4_residual_to_initial {g h : Polynomial O} (hkg : S2Mu4KeyPoly h2 hq g)
    (hkh : S2Mu4KeyPoly h2 hq h) (hres : s2Mu4NormRes h2 hq g = s2Mu4NormRes h2 hq h) :
    S2Mu4InitialEquiv h2 hq g h := by
  have hpin_g := s2Mu4KeyPoly_natDegree_pin h2 hq hkg
  have hpin_h := s2Mu4KeyPoly_natDegree_pin h2 hq hkh
  have hdg := s2Mu4KeyPoly_normRes_natDegree h2 hq hkg
  have hdh := s2Mu4KeyPoly_normRes_natDegree h2 hq hkh
  have h8g := (key_master h2 hq hkg).1
  have h8h := (key_master h2 hq hkh).1
  have hpos_g : 0 < g.natDegree := hkg.2.1.1
  have hpos_h : 0 < h.natDegree := hkh.2.1.1
  rw [hres] at hpin_g hdg
  have hd : g.natDegree = h.natDegree := by
    rcases hpin_g with h1g | h2g <;> rcases hpin_h with h1h | h2h <;> omega
  have hβg := s2Mu4KeyPoly_exactGrade h2 hq hkg
  have heqg := s2Mu4KeyPoly_normRes_eq_gradedRes h2 hq hkg
  rw [hd] at hβg heqg
  exact (mu4_initialEquiv_iff_gradedRes h2 hq hβg (s2Mu4KeyPoly_exactGrade h2 hq hkh)).mpr
    (by rw [← heqg, ← s2Mu4KeyPoly_normRes_eq_gradedRes h2 hq hkh, hres])

/-- ★★ **D3-17 — the assembled Proposition-5.6 field at μ₄** (both directions; forward is
D3-15's universal `s2Mu4NormRes_eq_of_initialEquiv`). -/
theorem s2Mu4_initial_iff_residual :
    ∀ g h : Polynomial O, S2Mu4KeyPoly h2 hq g → S2Mu4KeyPoly h2 hq h →
      (S2Mu4InitialEquiv h2 hq g h ↔ s2Mu4NormRes h2 hq g = s2Mu4NormRes h2 hq h) :=
  fun _ _ hkg hkh =>
    ⟨s2Mu4NormRes_eq_of_initialEquiv h2 hq, s2Mu4_residual_to_initial h2 hq hkg hkh⟩

/-! ## D3-18 Part 0 — the μ₄ recipe field, discharged by parity vacuity (model `C132rp9`)

The printed field's grade numeral `(f′ − t)·u′ = 85` is ODD, while every exact μ₄ grade
below the development-key degree `8` is EVEN (`s2Mu4ExactGrade_even_of_natDegree_lt_eight`
— slot 0 is the only live slot).  Exactly the recorded μ₃ defect
(`C132rp9.s2Mu3_recipe_grade_twenty_one_vacuous`), one level up: the field's numerals,
not the realization, are at fault. -/

/-- **BLOCKED-BECAUSE certificate.** No polynomial of degree below the current key degree
`8` can have the odd exact μ₄ grade `85`. -/
theorem s2Mu4_recipe_grade_eighty_five_vacuous {g : Polynomial O}
    (hdeg : g.natDegree < 8) : ¬ S2Mu4ExactGrade h2 hq 85 g := by
  intro hg
  have heven := s2Mu4ExactGrade_even_of_natDegree_lt_eight h2 hq hg hdeg
  omega

/-- The literal `(e', f', u') = (2, 1, 85)` normalized-recipe display.  It elaborates and
is logically true, but only because its required `khat 0` premise is impossible. -/
theorem s2Mu4_normalized_recipe (khat : ℕ → Polynomial O)
    (hkhat : ∀ t, t < 1 → S2Mu4ExactGrade h2 hq ((1 - t) * 85) (khat t))
    (hdeg : ∀ t, t < 1 → (khat t).natDegree <
      ((s2DepthThreeKeyChain h2 hq).keyAt 3 : Polynomial O).natDegree) :
    s2Mu4NormRes h2 hq
        (((s2DepthThreeKeyChain h2 hq).keyAt 3 : Polynomial O) ^ (2 * 1) -
          ∑ t ∈ Finset.range 1,
            khat t * ((s2DepthThreeKeyChain h2 hq).keyAt 3 : Polynomial O) ^ (2 * t)) =
      Polynomial.X ^ 1 -
        ∑ t ∈ Finset.range 1,
          Polynomial.C ((s2Mu4GradedRes h2 hq ((1 - t) * 85) (khat t)).coeff 0) *
            Polynomial.X ^ t := by
  exfalso
  apply s2Mu4_recipe_grade_eighty_five_vacuous h2 hq
    (by rw [show ((s2DepthThreeKeyChain h2 hq).keyAt 3 : Polynomial O).natDegree = 8 from
      s2DepthThreeKeyAt_natDegree_three h2 hq] at hdeg; exact hdeg 0 (by omega))
  simpa using hkhat 0 (by omega)

/-! ## D3-18 Part 1 — the depth-three letter (model `C130np6.s2Letter`, depth-3 typed) -/

/-- **the `FGMNSourceData.letter` field at depth three**: the constant `1` — the unique
nonzero value of the 2-element residue tower field, depth-3 typed; junk (never read by
`letter_ne_zero`) off the live range `1 ≤ i ≤ 3`. -/
noncomputable def s2LetterThree : ℕ → (s2DepthThree h2 hq).fld 3 := fun _ => 1

/-- the `letter_ne_zero` field, exact shape at `r = 3`. -/
theorem s2LetterThree_ne_zero : ∀ i, 1 ≤ i → i ≤ 3 → s2LetterThree h2 hq i ≠ 0 :=
  fun _ _ _ => one_ne_zero

/-! ## D3-18 Part 2 — ★★ the source records (model `C132fd0`, one level up) -/

/-- ★★ **D3-18, the DATA record**: the seven landed μ₄ operators at the depth-3 triple
`(2, 1, 85)`, over the T2 chain `Φ′/Φ₂/g₈`. -/
noncomputable def s2SourceDataThree :
    FGMNSourceData (s2DepthThree h2 hq) (s2DepthThreeKeyChain h2 hq) 2 1 85 where
  nextValue := s2Hgt₄ h2 hq
  gradedResidual := s2Mu4GradedRes h2 hq
  normalizedResidual := s2Mu4NormRes h2 hq
  PrevGrade := S2Mu4PrevGrade
  keyPolynomial := S2Mu4KeyPoly h2 hq
  initialEquiv := S2Mu4InitialEquiv h2 hq
  letter := s2LetterThree h2 hq

/-- read pin: `nextValue` is the μ₄ table `s2Hgt₄`. -/
theorem s2SourceDataThree_nextValue :
    (s2SourceDataThree h2 hq).nextValue = s2Hgt₄ h2 hq := rfl

/-- read pin: `gradedResidual` is `s2Mu4GradedRes`. -/
theorem s2SourceDataThree_gradedResidual :
    (s2SourceDataThree h2 hq).gradedResidual = s2Mu4GradedRes h2 hq := rfl

/-- read pin: `normalizedResidual` is `s2Mu4NormRes`. -/
theorem s2SourceDataThree_normalizedResidual :
    (s2SourceDataThree h2 hq).normalizedResidual = s2Mu4NormRes h2 hq := rfl

/-- read pin: `PrevGrade` is the evenness predicate `S2Mu4PrevGrade`. -/
theorem s2SourceDataThree_PrevGrade :
    (s2SourceDataThree h2 hq).PrevGrade = S2Mu4PrevGrade := rfl

/-- read pin: `keyPolynomial` is `S2Mu4KeyPoly`. -/
theorem s2SourceDataThree_keyPolynomial :
    (s2SourceDataThree h2 hq).keyPolynomial = S2Mu4KeyPoly h2 hq := rfl

/-- read pin: `initialEquiv` is `S2Mu4InitialEquiv`. -/
theorem s2SourceDataThree_initialEquiv :
    (s2SourceDataThree h2 hq).initialEquiv = S2Mu4InitialEquiv h2 hq := rfl

/-- read pin: `letter` is the forced constant-`1` `s2LetterThree` (depth-3 typed). -/
theorem s2SourceDataThree_letter :
    (s2SourceDataThree h2 hq).letter = s2LetterThree h2 hq := rfl

set_option maxHeartbeats 1600000 in
/-- ★★ **D3-18, the LAWS record — UNCONDITIONAL** (unlike the depth-2
`C132fd0.s2SourceLawsTwo_of`, which carried the then-open `hex`/`hconv` hypotheses: the
μ₄ `hex` landed at D3-14 (`C136d2.s2Mu4_hex`) and the μ₄ converse landed above at D3-17).
All thirteen projections are discharged by named landed theorems. -/
theorem s2SourceLawsThree :
    FGMNSourceLaws (s2DepthThree h2 hq) (s2DepthThreeKeyChain h2 hq) 2 1 85
      (s2SourceDataThree h2 hq) where
  graded_zero_of_above := fun _ _ h => s2Mu4GradedRes_zero_of_above h2 hq h
  graded_add := fun _ _ _ hg hh hgh => s2Mu4GradedRes_add h2 hq hg hh hgh
  graded_mul := s2Mu4_graded_mul h2 hq
  graded_scalar_nonzero := s2Mu4_graded_scalar_nonzero h2 hq
  normalized_mul := fun g h => s2Mu4NormRes_mul h2 hq g h
  normalized_recipe := fun khat hgr hdeg => s2Mu4_normalized_recipe h2 hq khat hgr hdeg
  normalized_exists := fun _ ψ hm hirr hd hc => s2Mu4_hex h2 hq ψ hm hirr hd hc
  key_criterion := s2Mu4_key_criterion h2 hq
  key_irreducible := fun _ hkp _ => s2Mu4_key_irreducible h2 hq hkp
  carried_key_is_key := fun _ => s2Mu4KeyPoly_g8 h2 hq
  carried_key_residual := fun _ => s2Mu4NormRes_g8 h2 hq
  initial_iff_residual := fun g h hg hh => s2Mu4_initial_iff_residual h2 hq g h hg hh
  letter_ne_zero := fun i h1 hr => s2LetterThree_ne_zero h2 hq i h1 hr

/-! ## D3-19 Part 0 — ★★★ THE μ₄ CALCULUS -/

/-- ★★★ **D3-19 — THE UNCONDITIONAL DEPTH-THREE (μ₄) CALCULUS**: the packaging theorem
`C130pk.fgmn_model_calculus_nonempty` fired at the D3-18 records — the deep-witness
campaign's μ₄ milestone.  Lean-core footprint; no hypothesis remains. -/
theorem s2Mu4_calculus_nonempty :
    Nonempty (FGMNCalculus (s2DepthThree h2 hq) 2 1 85) :=
  fgmn_model_calculus_nonempty (s2DepthThreeKeyChain h2 hq) (s2SourceDataThree h2 hq)
    (s2SourceLawsThree h2 hq)

/-! ## D3-19 Part 1 — the depth-four key function `keyAt 4 = g16` -/

/-- **the depth-four key function**: the T1/T2 depth-three keys at levels `≤ 3`
(`Φ′ / Φ₂ / g₈`), the D3-16 μ₄ key `g16 = g₈² − 2⁸Φ₂` at every higher index (only level
`4` is ever read — `KeyChain`'s laws are `StageLive`-fenced). -/
noncomputable def s2DepthFourKeyAt (i : ℕ) : Polynomial O :=
  if i ≤ 3 then s2DepthThreeKeyAt h2 hq i else g16 h2 hq

/-- on the depth-three live range the depth-four key function restricts to the T1 keys. -/
theorem s2DepthFourKeyAt_of_le {i : ℕ} (hi : i ≤ 3) :
    s2DepthFourKeyAt h2 hq i = s2DepthThreeKeyAt h2 hq i := by
  show (if i ≤ 3 then s2DepthThreeKeyAt h2 hq i else g16 h2 hq)
    = s2DepthThreeKeyAt h2 hq i
  rw [if_pos hi]

/-- Level 1 of the depth-four key function is the frame key `Φ′`. -/
theorem s2DepthFourKeyAt_one :
    s2DepthFourKeyAt h2 hq 1 = (s2Frame h2 hq).key := by
  rw [s2DepthFourKeyAt_of_le h2 hq (by omega)]
  exact s2DepthThreeKeyAt_one h2 hq

/-- **`keyAt 4 = g16`** — the campaign's depth-four key assignment (T5's deferred
carrier). -/
theorem s2DepthFourKeyAt_four :
    s2DepthFourKeyAt h2 hq 4 = g16 h2 hq := by
  show (if (4 : ℕ) ≤ 3 then s2DepthThreeKeyAt h2 hq 4 else g16 h2 hq) = g16 h2 hq
  rw [if_neg (by norm_num)]

/-! ## D3-19 Part 2 — the depth-four cumulative degrees -/

/-- `D₁ = 2` at the depth-four occurrence. -/
theorem s2DepthFour_Dcum_one : (s2DepthFour h2 hq).Dcum 1 = 2 := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 1 : Finset ℕ) = {1} by decide,
    Finset.prod_singleton]
  rfl

/-- `D₂ = 4` at the depth-four occurrence. -/
theorem s2DepthFour_Dcum_two : (s2DepthFour h2 hq).Dcum 2 = 4 := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide,
    Finset.prod_insert (by decide), Finset.prod_singleton]
  rfl

/-- `D₃ = 8` at the depth-four occurrence. -/
theorem s2DepthFour_Dcum_three : (s2DepthFour h2 hq).Dcum 3 = 8 := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  rfl

/-- `D₄ = 16` at the depth-four occurrence (T3's landed pin at the unique frame pin). -/
theorem s2DepthFour_Dcum_four : (s2DepthFour h2 hq).Dcum 4 = 16 :=
  s2WitnessFour_Dcum_four h2 hq 1 (s2Frame_pin h2 hq)

/-! ## D3-19 Part 3 — ★★ the depth-four `KeyChain` -/

/-- ★★ **D3-19 — the depth-four S2 `KeyChain`**: `Φ′ / Φ₂ / g₈ / g16` over
`s2DepthFour`, every C.130k field discharged from the T1/T2 pins and the D3-14/16 `g16`
bank.  This is the carrier T5's deferred chain-level normalizer row consumes, and the
entry point of the μ₅ refinement stack (D4). -/
noncomputable def s2DepthFourKeyChain : KeyChain (s2DepthFour h2 hq) where
  keyAt := s2DepthFourKeyAt h2 hq
  keyAt_one := s2DepthFourKeyAt_one h2 hq
  keyAt_monic := by
    intro i hi
    obtain ⟨hi1, hi4⟩ := hi
    interval_cases i
    · rw [s2DepthFourKeyAt_of_le h2 hq (by omega)]
      exact s2DepthThreeKeyAt_monic_one h2 hq
    · rw [s2DepthFourKeyAt_of_le h2 hq (by omega)]
      exact s2DepthThreeKeyAt_monic_two h2 hq
    · rw [s2DepthFourKeyAt_of_le h2 hq (by omega)]
      exact s2DepthThreeKeyAt_monic_three h2 hq
    · rw [s2DepthFourKeyAt_four h2 hq]
      exact g16_monic h2 hq
  keyAt_degree := by
    intro i hi
    obtain ⟨hi1, hi4⟩ := hi
    interval_cases i
    · rw [s2DepthFourKeyAt_of_le h2 hq (by omega),
        s2DepthThreeKeyAt_natDegree_one h2 hq, s2DepthFour_Dcum_one h2 hq]
    · rw [s2DepthFourKeyAt_of_le h2 hq (by omega),
        s2DepthThreeKeyAt_natDegree_two h2 hq, s2DepthFour_Dcum_two h2 hq]
    · rw [s2DepthFourKeyAt_of_le h2 hq (by omega),
        s2DepthThreeKeyAt_natDegree_three h2 hq, s2DepthFour_Dcum_three h2 hq]
    · rw [s2DepthFourKeyAt_four h2 hq, g16_natDegree h2 hq,
        s2DepthFour_Dcum_four h2 hq]

/-- chain read pin: `keyAt 4` of the depth-four chain IS `g16`. -/
theorem s2DepthFourKeyChain_keyAt_four :
    (s2DepthFourKeyChain h2 hq).keyAt 4 = g16 h2 hq :=
  s2DepthFourKeyAt_four h2 hq

/-- chain read pin: on the depth-three live range the depth-four chain restricts to the
T2 chain. -/
theorem s2DepthFourKeyChain_keyAt_of_le {i : ℕ} (hi : i ≤ 3) :
    (s2DepthFourKeyChain h2 hq).keyAt i = (s2DepthThreeKeyChain h2 hq).keyAt i :=
  s2DepthFourKeyAt_of_le h2 hq hi

/-! ## D3-19 Part 4 — T5's deferred half: the chain-level `Λ` restatement -/

/-- ★ **T5's deferred polynomial pin, COMPLETED** (`C136t`'s recorded split): at the
depth-four occurrence, any calculus carrying the depth-four chain (one `hkey`, no
pointwise premises) computes `chainNormBelow 4 171 = Λ = 2·x·Φ′·Φ₂·g₈`.  Only keys
`1..3` occur in `chainNorm 3`, so the restatement factors through the chain's
depth-three restriction pins. -/
theorem s2Mu5_chainNormBelow_four_one_seventy_one_chain
    (I : FGMNCalculus (s2DepthFour h2 hq) 1 1 171)
    (hkey : I.keyAt = (s2DepthFourKeyChain h2 hq).keyAt) :
    I.chainNormBelow 4 171 = s2Mu5Lambda h2 hq := by
  refine s2Mu5_chainNormBelow_four_one_seventy_one h2 hq I ?_ ?_ ?_
  · rw [hkey]
    exact s2DepthFourKeyAt_of_le h2 hq (i := 1) (by omega)
  · rw [hkey]
    exact s2DepthFourKeyAt_of_le h2 hq (i := 2) (by omega)
  · rw [hkey]
    exact s2DepthFourKeyAt_of_le h2 hq (i := 3) (by omega)

end S2

end Uniformity.Density.Tower.C136d3

/-! ## Axiom footprint -/

section AxCheck

-- D3-15: the predicates and the residual-divisibility equivalence
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4InitialEquiv
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4Dvd
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4Minimal
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4Irreducible
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4KeyPoly
#print axioms Uniformity.Density.Tower.C136d3.s2Hgt₄_neg
#print axioms Uniformity.Density.Tower.C136d3.s2Hgt₄_eq_top_iff
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4InitialEquiv_equivalence
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4InitialEquiv_hgt_eq
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4InitialEquiv_zero_left
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4InitialEquiv_zero_right
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4ExactGrade_of_initialEquiv
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4GradeOf_eq_of_initialEquiv
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4Dvd_of_dvd
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4Dvd_self
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4Dvd_zero
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4Dvd_congr_right
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4NormRes_eq_of_initialEquiv
#print axioms Uniformity.Density.Tower.C136d3.mu4NormRes_dvd_of_S2Mu4Dvd
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4NormRes_isUnit_of_natDegree_lt_sixteen
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4Dvd_of_mu4NormRes_dvd
#print axioms Uniformity.Density.Tower.C136d3.S2Mu4Dvd_iff_mu4NormRes_dvd
-- D3-16: criterion, irreducibility, and the g16 key theorem
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4Irreducible_of_irreducible_normRes
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4Minimal_of_not_isUnit_normRes
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4Minimal_of_irreducible_normRes
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4_key_criterion
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4_key_irreducible
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4KeyPoly_g16
-- D3-17: the carried key, the key-structure bank, and the converse
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4ExactGrade_even_of_natDegree_lt_eight
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4KeyPoly_g8
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4NormRes_g8
#print axioms Uniformity.Density.Tower.C136d3.tooth_g8_mu4_vs_mu3
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4Minimal_natDegree_eight_dvd
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4Minimal_exactGrade
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4KeyPoly_slotZero
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4KeyPoly_exactGrade
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4KeyPoly_gradedRes_coeff_zero_ne_zero
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4KeyPoly_normRes_eq_gradedRes
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4KeyPoly_normRes_natDegree
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4KeyPoly_natDegree_pin
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4_residual_to_initial
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4_initial_iff_residual
-- D3-18: the recipe vacuity, the letter, and the source records
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4_recipe_grade_eighty_five_vacuous
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4_normalized_recipe
#print axioms Uniformity.Density.Tower.C136d3.s2LetterThree
#print axioms Uniformity.Density.Tower.C136d3.s2LetterThree_ne_zero
#print axioms Uniformity.Density.Tower.C136d3.s2SourceDataThree
#print axioms Uniformity.Density.Tower.C136d3.s2SourceDataThree_nextValue
#print axioms Uniformity.Density.Tower.C136d3.s2SourceDataThree_gradedResidual
#print axioms Uniformity.Density.Tower.C136d3.s2SourceDataThree_normalizedResidual
#print axioms Uniformity.Density.Tower.C136d3.s2SourceDataThree_PrevGrade
#print axioms Uniformity.Density.Tower.C136d3.s2SourceDataThree_keyPolynomial
#print axioms Uniformity.Density.Tower.C136d3.s2SourceDataThree_initialEquiv
#print axioms Uniformity.Density.Tower.C136d3.s2SourceDataThree_letter
#print axioms Uniformity.Density.Tower.C136d3.s2SourceLawsThree
-- D3-19: ★★★ the μ₄ calculus, the depth-four chain, and T5's completed pin
#print axioms Uniformity.Density.Tower.C136d3.s2Mu4_calculus_nonempty
#print axioms Uniformity.Density.Tower.C136d3.s2DepthFourKeyAt
#print axioms Uniformity.Density.Tower.C136d3.s2DepthFourKeyAt_of_le
#print axioms Uniformity.Density.Tower.C136d3.s2DepthFourKeyAt_one
#print axioms Uniformity.Density.Tower.C136d3.s2DepthFourKeyAt_four
#print axioms Uniformity.Density.Tower.C136d3.s2DepthFour_Dcum_one
#print axioms Uniformity.Density.Tower.C136d3.s2DepthFour_Dcum_two
#print axioms Uniformity.Density.Tower.C136d3.s2DepthFour_Dcum_three
#print axioms Uniformity.Density.Tower.C136d3.s2DepthFour_Dcum_four
#print axioms Uniformity.Density.Tower.C136d3.s2DepthFourKeyChain
#print axioms Uniformity.Density.Tower.C136d3.s2DepthFourKeyChain_keyAt_four
#print axioms Uniformity.Density.Tower.C136d3.s2DepthFourKeyChain_keyAt_of_le
#print axioms Uniformity.Density.Tower.C136d3.s2Mu5_chainNormBelow_four_one_seventy_one_chain

end AxCheck
