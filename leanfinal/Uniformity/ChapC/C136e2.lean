/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136e1
import Uniformity.ChapC.C130lb

/-!
# Uniformity.ChapC.C136e2 — the μ₅ refinement stack's CLOSER: D4-13..D4-18 [D4C 2026-08-28]

**Unit D4C** of the deep-witness campaign
(`docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.3, rows D4-13..D4-18): the μ₅
stack's closer, against the landed μ₅ operator bank (`C136e0`/`C136e1`), mirroring the μ₄
closer `C136d3` one level up at the [G5F]-adjudicated refinement triple
`(e', f', u') = (1, 1, 171)` over the landed depth-four tower/chain (`C136d3` D3-19).

* **D4-13 — key predicates and residual divisibility** (mirror of `C136d3` D3-15).
  The five μ₅ predicates anchored to `s2Hgt₅` (`S2Mu5InitialEquiv`/`Dvd`/`Minimal`/
  `Irreducible`/`KeyPoly`), the equivalence/grade-transport/divisibility law bank, and
  `S2Mu5Dvd_iff_mu5NormRes_dvd` — the honest monic degree-`≤ 16` nonunit-residual scope
  (the μ₅ remainder fence is `16 = deg g16` itself: at `e' = 1` the backward translation
  is the ONE-SLOT remainder mechanism, no parity split anywhere).
* **D4-14 — criterion, the leaf key, and the carried key** (mirror of `C136d3` D3-16 +
  D3-17 Parts 0–3).  `s2Mu5_key_criterion` in the literal `FGMNSourceLaws` field shape at
  the depth-four recipe degree `1·1·deg(keyAt 4) = 16`; ★ `S2Mu5KeyPoly_leaf` (D4-12's
  landed leaf `keyAt4 − Λ` with residual `X + 1` is a μ₅ key); ★ `S2Mu5KeyPoly_g16` — the
  carried depth-four key IS a μ₅ key.  RECORDED DEVIATION from the μ₄ pattern: the odd-carry
  parity obstruction has NO μ₅ analogue (`S2Mu5PrevGrade` is ALL grades); the carried key's
  minimality/primality are instead proved by the GRADE-COMPARISON route — the landed
  `s2Mu5GradedRes_key = X` kills the scalar coefficient of anything `g16` μ₅-divides
  (`not_mu5Dvd_g16_of_coeff_zero_ne`), while D4-08's scalar-nonzero law protects every
  polynomial of degree `< 16`; primality is the slot-zero dichotomy with NO parity case.
* **D4-15 — irreducibility over `O` and fraction-map coprimality**.
  `s2Mu5_key_irreducible` (mirror of `s2Mu4_key_irreducible`), applied to both keys;
  `s2Mu5Leaf_ne_g16` (Λ ≠ 0); the Gauss transports
  (`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`, forward direction) and
  ★ `s2Mu5_leafSq_keyAt4_coprime_fractionMap` — `leaf²` and `keyAt 4` are coprime in
  `K[x]` for every fraction field `K` of `O`.
* **D4-16 — the initial-iff-residual converse** (mirror of `C136d3` D3-17 Parts 6–10,
  MUCH lighter): the μ₅ key-structure bank WITHOUT any digit-bound ledger — the pair bound
  `μ₄(A) + μ₄(B) ≤ 170` for monic digits with `deg A + deg B = 16` is the VALUATION
  MULTIPLICATIVITY (`S2Mu4ExactGrade_mul`) plus ONE top-slot read on the monic degree-16
  product (`dev_top_eq_one`), tight against the [G5F] floor `170 < 171`.  Then the
  divisibility pin `16 ∣ deg`, the grade pin `μ₅(g) = 171·(deg g/16)`, the top-slot
  pin `deg R(g) = deg g/16`, the trailing dichotomy (a key's residual strip is trivial
  UNLESS the key is in the `∼ g16` fiber: `normRes = 1`, `deg = 16`, `gradedRes = X`),
  ★★ `s2Mu5_residual_to_initial`, and `s2Mu5_initial_iff_residual`; plus the concrete
  `not_S2Mu5InitialEquiv_leaf_g16` (`X + 1 ≠ 1`).
* **D4-17 — the source records** (mirror of `C136d3` D3-18).  `s2LetterFour`;
  ★★ `s2SourceDataFour : FGMNSourceData (s2DepthFour h2 hq) (s2DepthFourKeyChain h2 hq)
  1 1 171` (seven `rfl` read pins) and ★★ `s2SourceLawsFour` — ALL THIRTEEN laws
  UNCONDITIONAL, with the `normalized_recipe` field GENUINELY NON-VACUOUS (the μ₅ recipe
  is the exact-evaluation computation D4-11 landed, not a parity vacuity: at `e' = 1`
  every grade is realizable) and `normalized_exists` discharged by the landed leaf.
* **D4-18 — ★★★ THE μ₅ CALCULUS.**  `s2Mu5_calculus_nonempty :
  Nonempty (FGMNCalculus (s2DepthFour h2 hq) 1 1 171)` via
  `fgmn_model_calculus_nonempty` — the deep-witness campaign's key-tail closer at
  `(1, 1, 171)`.  No depth-five `keyAt`/`KeyChain` is built (out of scope by the row).

## Status

Zero `sorry`; Lean-core axiom footprint for every declaration (AxCheck footer).  No landed
statement is touched.  Verdict: `runs/wave-c/verdict_D4C.md`.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace Uniformity.Density.Tower.C136e2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130nv2 (weight_read dev_zero_pin)
open Uniformity.Density.Tower.C132rp5 (dev_mul_conv_split_monic)
open Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv2 (dv2Hgt_zero)
open Uniformity.Density.Tower.C132nv5
open Uniformity.Density.Tower.C131v
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C132rp10
open Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136d3ad Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136e0 Uniformity.Density.Tower.C136e1
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## D4-13 Part 0 — the five μ₅ predicates (mirror of `C136d3` D3-15 Part 0) -/

/-- Initial-form equivalence for the landed μ₅ value. -/
def S2Mu5InitialEquiv (g h : Polynomial O) : Prop :=
  (s2Hgt₅ h2 hq (g - h) > s2Hgt₅ h2 hq g ∧ s2Hgt₅ h2 hq g = s2Hgt₅ h2 hq h)
    ∨ (g = 0 ∧ h = 0)

/-- Divisibility of μ₅-initial forms. -/
def S2Mu5Dvd (φ g : Polynomial O) : Prop :=
  ∃ q : Polynomial O, S2Mu5InitialEquiv h2 hq g (φ * q)

/-- μ₅-minimality, including the positive-degree clause of FGMN Definition 1.2. -/
def S2Mu5Minimal (φ : Polynomial O) : Prop :=
  0 < φ.natDegree ∧
    ∀ g : Polynomial O, g ≠ 0 → g.natDegree < φ.natDegree → ¬ S2Mu5Dvd h2 hq φ g

/-- μ₅-irreducibility rendered through initial-form divisibility. -/
def S2Mu5Irreducible (φ : Polynomial O) : Prop :=
  φ ≠ 0 ∧ ¬ S2Mu5Dvd h2 hq φ 1 ∧
    ∀ g h : Polynomial O,
      S2Mu5Dvd h2 hq φ (g * h) → S2Mu5Dvd h2 hq φ g ∨ S2Mu5Dvd h2 hq φ h

/-- Key-polynomialhood for μ₅. -/
def S2Mu5KeyPoly (φ : Polynomial O) : Prop :=
  φ.Monic ∧ S2Mu5Minimal h2 hq φ ∧ S2Mu5Irreducible h2 hq φ

/-- Field-shape pin for the μ₅ source-data `initialEquiv` field. -/
example : Polynomial O → Polynomial O → Prop := S2Mu5InitialEquiv h2 hq

/-- Field-shape pin for the μ₅ source-data `keyPolynomial` field. -/
example : Polynomial O → Prop := S2Mu5KeyPoly h2 hq

/-! ## D4-13 Part 1 — value and equivalence laws (mirror of `C136d3` D3-15 Part 1) -/

/-- The μ₅ value is invariant under negation. -/
theorem s2Hgt₅_neg (A : Polynomial O) : s2Hgt₅ h2 hq (-A) = s2Hgt₅ h2 hq A := by
  rw [s2Hgt₅_eq_dv4Supp, s2Hgt₅_eq_dv4Supp,
    dv4Supp_neg _ (s2Φ₂_monic h2 hq) 21 2 (s2g8_monic h2 hq) 85 2 (g16_monic h2 hq) A 171 1]

/-- A polynomial has infinite μ₅ value exactly when it is zero. -/
theorem s2Hgt₅_eq_top_iff {A : Polynomial O} : s2Hgt₅ h2 hq A = ⊤ ↔ A = 0 := by
  constructor
  · intro htop
    by_contra hne
    exact s2Hgt₅_ne_top h2 hq hne htop
  · rintro rfl
    exact s2Hgt₅_zero h2 hq

/-- μ₅-initial equivalence is reflexive. -/
theorem S2Mu5InitialEquiv_refl (g : Polynomial O) : S2Mu5InitialEquiv h2 hq g g := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact Or.inr ⟨rfl, rfl⟩
  · refine Or.inl ⟨?_, rfl⟩
    rw [sub_self, s2Hgt₅_zero h2 hq]
    exact lt_top_iff_ne_top.mpr (s2Hgt₅_ne_top h2 hq hg)

/-- μ₅-initial equivalence is symmetric. -/
theorem S2Mu5InitialEquiv_symm {g h : Polynomial O}
    (hgh : S2Mu5InitialEquiv h2 hq g h) : S2Mu5InitialEquiv h2 hq h g := by
  rcases hgh with ⟨hlt, heq⟩ | ⟨hg0, hh0⟩
  · refine Or.inl ⟨?_, heq.symm⟩
    rw [show h - g = -(g - h) from (neg_sub g h).symm, s2Hgt₅_neg h2 hq, ← heq]
    exact hlt
  · exact Or.inr ⟨hh0, hg0⟩

/-- μ₅-initial equivalence is transitive. -/
theorem S2Mu5InitialEquiv_trans {g h k : Polynomial O}
    (hgh : S2Mu5InitialEquiv h2 hq g h) (hhk : S2Mu5InitialEquiv h2 hq h k) :
    S2Mu5InitialEquiv h2 hq g k := by
  rcases hgh with ⟨hlt1, heq1⟩ | ⟨hg0, hh0⟩
  · rcases hhk with ⟨hlt2, heq2⟩ | ⟨hh0, hk0⟩
    · refine Or.inl ⟨?_, heq1.trans heq2⟩
      have hdecomp : g - k = (g - h) + (h - k) := by ring
      have hmin := s2Hgt₅_add_ge h2 hq (g - h) (h - k)
      rw [← hdecomp] at hmin
      refine lt_of_lt_of_le (lt_min hlt1 ?_) hmin
      rw [heq1]
      exact hlt2
    · have hg0 : g = 0 := by
        rw [← s2Hgt₅_eq_top_iff h2 hq, heq1, hh0, s2Hgt₅_zero h2 hq]
      exact Or.inr ⟨hg0, hk0⟩
  · subst hh0
    rcases hhk with ⟨hlt2, -⟩ | ⟨-, hk0⟩
    · rw [s2Hgt₅_zero h2 hq] at hlt2
      exact absurd hlt2 not_top_lt
    · exact Or.inr ⟨hg0, hk0⟩

/-- The packaged equivalence relation. -/
theorem S2Mu5InitialEquiv_equivalence :
    Equivalence (S2Mu5InitialEquiv h2 hq (O := O)) :=
  ⟨S2Mu5InitialEquiv_refl h2 hq, S2Mu5InitialEquiv_symm h2 hq,
    S2Mu5InitialEquiv_trans h2 hq⟩

/-- Initial equivalence preserves μ₅ value. -/
theorem S2Mu5InitialEquiv_hgt_eq {g h : Polynomial O}
    (hgh : S2Mu5InitialEquiv h2 hq g h) : s2Hgt₅ h2 hq g = s2Hgt₅ h2 hq h := by
  rcases hgh with ⟨-, heq⟩ | ⟨rfl, rfl⟩
  · exact heq
  · rfl

/-- Zero is μ₅-initial-equivalent only to zero. -/
theorem S2Mu5InitialEquiv_zero_left {h : Polynomial O} :
    S2Mu5InitialEquiv h2 hq 0 h ↔ h = 0 := by
  constructor
  · intro hh
    rcases hh with ⟨hlt, -⟩ | ⟨-, hh0⟩
    · rw [s2Hgt₅_zero h2 hq] at hlt
      exact absurd hlt not_top_lt
    · exact hh0
  · rintro rfl
    exact S2Mu5InitialEquiv_refl h2 hq 0

/-- Right-hand zero law for μ₅-initial equivalence. -/
theorem S2Mu5InitialEquiv_zero_right {g : Polynomial O} :
    S2Mu5InitialEquiv h2 hq g 0 ↔ g = 0 := by
  constructor
  · intro hg
    exact (S2Mu5InitialEquiv_zero_left h2 hq).mp (S2Mu5InitialEquiv_symm h2 hq hg)
  · rintro rfl
    exact S2Mu5InitialEquiv_refl h2 hq 0

/-! ## D4-13 Part 2 — grade transport (mirror of `C136d3` D3-15 Part 2) -/

/-- Initial equivalence transports an exact μ₅ grade. -/
theorem S2Mu5ExactGrade_of_initialEquiv {β : ℕ} {g h : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) (hgh : S2Mu5InitialEquiv h2 hq g h) :
    S2Mu5ExactGrade h2 hq β h := by
  show s2Hgt₅ h2 hq h = (β : WithTop ℤ)
  rw [← S2Mu5InitialEquiv_hgt_eq h2 hq hgh]
  exact hg

/-- Initial equivalence preserves the total extracted μ₅ grade. -/
theorem s2Mu5GradeOf_eq_of_initialEquiv {g h : Polynomial O}
    (hgh : S2Mu5InitialEquiv h2 hq g h) :
    s2Mu5GradeOf h2 hq g = s2Mu5GradeOf h2 hq h := by
  have heq := S2Mu5InitialEquiv_hgt_eq h2 hq hgh
  rw [s2Hgt₅_eq_dv4Supp, s2Hgt₅_eq_dv4Supp] at heq
  unfold s2Mu5GradeOf
  exact congrArg ENat.toNat (toZ_inj heq)

/-! ## D4-13 Part 3 — elementary μ₅-divisibility laws (mirror of `C136d3` D3-15 Part 3) -/

/-- Ordinary divisibility implies μ₅-divisibility. -/
theorem S2Mu5Dvd_of_dvd {φ g : Polynomial O} (hdvd : φ ∣ g) : S2Mu5Dvd h2 hq φ g := by
  obtain ⟨q, rfl⟩ := hdvd
  exact ⟨q, S2Mu5InitialEquiv_refl h2 hq _⟩

/-- Every polynomial μ₅-divides itself. -/
theorem S2Mu5Dvd_self (φ : Polynomial O) : S2Mu5Dvd h2 hq φ φ :=
  S2Mu5Dvd_of_dvd h2 hq dvd_rfl

/-- Every polynomial μ₅-divides zero. -/
theorem S2Mu5Dvd_zero (φ : Polynomial O) : S2Mu5Dvd h2 hq φ 0 :=
  S2Mu5Dvd_of_dvd h2 hq (dvd_zero φ)

/-- μ₅-divisibility is invariant under initial equivalence in the dividend. -/
theorem S2Mu5Dvd_congr_right {φ g g' : Polynomial O}
    (hgg' : S2Mu5InitialEquiv h2 hq g g') :
    S2Mu5Dvd h2 hq φ g ↔ S2Mu5Dvd h2 hq φ g' := by
  constructor
  · rintro ⟨q, hq'⟩
    exact ⟨q, S2Mu5InitialEquiv_trans h2 hq (S2Mu5InitialEquiv_symm h2 hq hgg') hq'⟩
  · rintro ⟨q, hq'⟩
    exact ⟨q, S2Mu5InitialEquiv_trans h2 hq hgg' hq'⟩

/-! ## D4-13 Part 4 — initial-equivalence residual transport (mirror of D3-15 Part 4) -/

/-- Initial equivalence preserves the normalized μ₅ residual. -/
theorem s2Mu5NormRes_eq_of_initialEquiv {g h : Polynomial O}
    (hgh : S2Mu5InitialEquiv h2 hq g h) :
    s2Mu5NormRes h2 hq g = s2Mu5NormRes h2 hq h := by
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [(S2Mu5InitialEquiv_zero_left h2 hq).mp hgh]
  · have hg := S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hg0
    have hh := S2Mu5ExactGrade_of_initialEquiv h2 hq hg hgh
    rcases hgh with ⟨hlt, -⟩ | ⟨hgzero, -⟩
    · have habove : S2Mu5AboveGrade h2 hq (s2Mu5GradeOf h2 hq g) (g - h) := by
        show ((s2Mu5GradeOf h2 hq g : ℕ) : WithTop ℤ) < s2Hgt₅ h2 hq (g - h)
        rw [← hg]
        exact hlt
      have hdecomp : g = h + (g - h) := by ring
      have hadd := s2Mu5GradedRes_add_of_le h2 hq
        (le_of_eq ((S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hh).symm)
        (le_of_lt ((S2Mu5AboveGrade_iff_dv4Supp h2 hq).mp habove))
      rw [← hdecomp, s2Mu5GradedRes_zero_of_above h2 hq habove, add_zero] at hadd
      rw [s2Mu5NormRes_of_exact h2 hq hg, s2Mu5NormRes_of_exact h2 hq hh, hadd]
    · exact absurd hgzero hg0

/-! ## D4-13 Part 5 — forward translation and low-degree residuals (mirror of D3-15 Part 5) -/

/-- μ₅-divisibility universally implies divisibility of normalized μ₅ residuals. -/
theorem mu5NormRes_dvd_of_S2Mu5Dvd {g a : Polynomial O} (h : S2Mu5Dvd h2 hq g a) :
    s2Mu5NormRes h2 hq g ∣ s2Mu5NormRes h2 hq a := by
  obtain ⟨q, hq'⟩ := h
  have heq := s2Mu5NormRes_eq_of_initialEquiv h2 hq hq'
  rw [s2Mu5NormRes_mul h2 hq] at heq
  exact ⟨s2Mu5NormRes h2 hq q, heq⟩

/-- Below the degree-sixteen development key, every μ₅ graded residual is constant
(the μ₅ fence is `deg g16 = 16` itself, not a doubled fence, since `e' = 1`). -/
theorem s2Mu5GradedRes_eq_C_of_natDegree_lt_sixteen {g : Polynomial O}
    (hdeg : g.natDegree < 16) (β : ℕ) :
    s2Mu5GradedRes h2 hq β g =
      Polynomial.C ((s2Mu5GradedRes h2 hq β g).coeff 0) := by
  refine Polynomial.ext fun t => ?_
  match t with
  | 0 => rw [Polynomial.coeff_C_zero]
  | t + 1 =>
    rw [Polynomial.coeff_C_of_ne_zero (Nat.succ_ne_zero t), s2Mu5GradedRes_coeff]
    refine s2Mu5Coeff_eq_zero_of_dv4Pin_top h2 hq ?_
    rw [dv4Pin, dev_eq_zero_of_lt (g16_monic h2 hq)
      (by rw [g16_natDegree h2 hq]; norm_num) g _
      (by rw [g16_natDegree h2 hq]; omega)]
    exact dv4Hgt_zero ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21
      (by norm_num) (g8 h2 hq) 85 (by norm_num)

/-- A nonzero polynomial of degree below sixteen has unit normalized μ₅ residual. -/
theorem s2Mu5NormRes_isUnit_of_natDegree_lt_sixteen {g : Polynomial O} (hg : g ≠ 0)
    (hdeg : g.natDegree < 16) : IsUnit (s2Mu5NormRes h2 hq g) := by
  have hex := S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hg
  have hC := s2Mu5GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hdeg
    (s2Mu5GradeOf h2 hq g)
  have hne := s2Mu5GradedRes_ne_zero_of_exact h2 hq hex
  have hγ : (s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq g) g).coeff 0 ≠ 0 := by
    intro h0
    rw [hC, h0, map_zero] at hne
    exact hne rfl
  rw [s2Mu5NormRes_of_exact h2 hq hex, hC, Polynomial.natTrailingDegree_C,
    Function.iterate_zero_apply]
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hγ)

/-- Extracted μ₅ grades add on nonzero products. -/
private theorem s2Mu5GradeOf_mul {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    s2Mu5GradeOf h2 hq (g * z) = s2Mu5GradeOf h2 hq g + s2Mu5GradeOf h2 hq z := by
  exact s2Mu5GradeOf_eq_of_exact h2 hq
    (S2Mu5ExactGrade_mul h2 hq
      (S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hg)
      (S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hz))

/-! ## D4-13 Part 6 — backward translation and the packaged iff (mirror of D3-15 Part 6)

At `e' = 1` this is the ONE-SLOT remainder mechanism: the remainder `a %ₘ g` has degree
below the development key `g16`, so its μ₅ graded residual is a SCALAR (Part 5's collapse)
— no parity case-split occurs anywhere, unlike the μ₄ mirror's two-slot fence. -/

/-- In the monic degree-`≤ 16`, nonunit-residual scope, residual divisibility implies
μ₅-divisibility. -/
theorem S2Mu5Dvd_of_mu5NormRes_dvd {g a : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 16) (hnu : ¬ IsUnit (s2Mu5NormRes h2 hq g))
    (hdvd : s2Mu5NormRes h2 hq g ∣ s2Mu5NormRes h2 hq a) :
    S2Mu5Dvd h2 hq g a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact S2Mu5Dvd_zero h2 hq g
  have hmod : a %ₘ g + g * (a /ₘ g) = a := Polynomial.modByMonic_add_div a g
  rcases eq_or_ne (a %ₘ g) 0 with hr0 | hr0
  · exact S2Mu5Dvd_of_dvd h2 hq ((Polynomial.modByMonic_eq_zero_iff_dvd hmon).mp hr0)
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
      (s2Mu5NormRes_isUnit_of_natDegree_lt_sixteen h2 hq ha0 hdega))
  have hgw0 : g * (a /ₘ g) ≠ 0 := mul_ne_zero hmon.ne_zero hw0
  have hexr := S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hr0
  have hexgw := S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hgw0
  have hvr : s2Hgt₅ h2 hq (a %ₘ g)
      = ((s2Mu5GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ) := hexr
  have hvgw : s2Hgt₅ h2 hq (g * (a /ₘ g))
      = ((s2Mu5GradeOf h2 hq (g * (a /ₘ g)) : ℕ) : WithTop ℤ) := hexgw
  rcases Nat.lt_or_ge (s2Mu5GradeOf h2 hq (g * (a /ₘ g)))
      (s2Mu5GradeOf h2 hq (a %ₘ g)) with hlt | hge
  · have hltv : s2Hgt₅ h2 hq (g * (a /ₘ g)) < s2Hgt₅ h2 hq (a %ₘ g) := by
      rw [hvr, hvgw]
      exact_mod_cast hlt
    have hadd := s2Hgt₅_add_eq h2 hq (a %ₘ g) (g * (a /ₘ g)) (ne_of_gt hltv)
    rw [hmod] at hadd
    have hva : s2Hgt₅ h2 hq a = s2Hgt₅ h2 hq (g * (a /ₘ g)) := by
      rw [hadd]
      exact min_eq_right (le_of_lt hltv)
    refine ⟨a /ₘ g, Or.inl ⟨?_, hva⟩⟩
    rw [show a - g * (a /ₘ g) = a %ₘ g from sub_eq_of_eq_add hmod.symm, hva]
    exact hltv
  · exfalso
    have hψg : s2Mu5NormRes h2 hq g
        ∣ s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq (a %ₘ g)) (g * (a /ₘ g)) := by
      rcases (ge_iff_le.mp hge).lt_or_eq with hlt' | heq'
      · rw [s2Mu5GradedRes_zero_of_above h2 hq
          (show ((s2Mu5GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ)
              < s2Hgt₅ h2 hq (g * (a /ₘ g)) from by rw [hvgw]; exact_mod_cast hlt')]
        exact dvd_zero _
      · have hmul := s2Mu5GradedRes_mul h2 hq
          (S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hmon.ne_zero)
          (S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hw0)
        have hsum := s2Mu5GradeOf_mul h2 hq hmon.ne_zero hw0
        rw [heq', hsum, hmul]
        have hrec : s2Mu5NormRes h2 hq g
            ∣ s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq g) g :=
          ⟨Polynomial.X ^
              (s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq g) g).natTrailingDegree,
            (s2Mu5NormRes_mul_X_pow_of_exact h2 hq
              (S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hmon.ne_zero)).symm⟩
        exact hrec.mul_right _
    have hβr_le_a : ((s2Mu5GradeOf h2 hq (a %ₘ g) : ℕ) : WithTop ℤ)
        ≤ s2Hgt₅ h2 hq a := by
      have hmin := s2Hgt₅_add_ge h2 hq (a %ₘ g) (g * (a /ₘ g))
      rw [hmod] at hmin
      refine le_trans ?_ hmin
      rw [hvr, hvgw]
      exact le_min le_rfl (by exact_mod_cast hge)
    have hψa : s2Mu5NormRes h2 hq g
        ∣ s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq (a %ₘ g)) a := by
      rcases hβr_le_a.lt_or_eq with hlt' | heq'
      · rw [s2Mu5GradedRes_zero_of_above h2 hq hlt']
        exact dvd_zero _
      · exact dvd_trans hdvd
          ⟨Polynomial.X ^
              (s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq (a %ₘ g)) a).natTrailingDegree,
            (s2Mu5NormRes_mul_X_pow_of_exact h2 hq heq'.symm).symm⟩
    have h1 : ((s2Mu5GradeOf h2 hq (a %ₘ g) : ℕ) : ℕ∞)
        ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) 85 2 (g16 h2 hq) (g * (a /ₘ g)) 171 1 := by
      rw [(S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hexgw]
      exact_mod_cast hge
    have haddres := s2Mu5GradedRes_add_of_le h2 hq
      (le_of_eq ((S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hexr).symm) h1
    rw [hmod] at haddres
    have hψr : s2Mu5NormRes h2 hq g
        ∣ s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq (a %ₘ g)) (a %ₘ g) := by
      have hsub : s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq (a %ₘ g)) (a %ₘ g)
          = s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq (a %ₘ g)) a
            - s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq (a %ₘ g)) (g * (a /ₘ g)) := by
        rw [haddres]
        ring
      rw [hsub]
      exact dvd_sub hψa hψg
    have hdegr : (a %ₘ g).natDegree < 16 := by
      have h2' := Polynomial.natDegree_lt_natDegree hr0
        (Polynomial.degree_modByMonic_lt a hmon)
      omega
    have hC := s2Mu5GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hdegr
      (s2Mu5GradeOf h2 hq (a %ₘ g))
    have hne := s2Mu5GradedRes_ne_zero_of_exact h2 hq hexr
    have hγ :
        (s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq (a %ₘ g)) (a %ₘ g)).coeff 0 ≠ 0 := by
      intro h0
      rw [hC, h0, map_zero] at hne
      exact hne rfl
    rw [hC] at hψr
    exact hnu (isUnit_of_dvd_unit hψr
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hγ)))

/-- ★ **D4-13 — the μ₅-divisibility/residual-divisibility equivalence** in its honest
monic degree-`≤ 16` scope (mirror of `C136d3.S2Mu4Dvd_iff_mu4NormRes_dvd`, one level up;
the fence `16 = deg g16` is the `e' = 1` one-slot remainder fence). -/
theorem S2Mu5Dvd_iff_mu5NormRes_dvd {g a : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 16) (hnu : ¬ IsUnit (s2Mu5NormRes h2 hq g)) :
    S2Mu5Dvd h2 hq g a ↔ s2Mu5NormRes h2 hq g ∣ s2Mu5NormRes h2 hq a :=
  ⟨mu5NormRes_dvd_of_S2Mu5Dvd h2 hq,
    S2Mu5Dvd_of_mu5NormRes_dvd h2 hq hmon hdeg hnu⟩

/-! ## D4-14 Part 0 — residual primality and minimality (mirror of `C136d3` D3-16 Part 0) -/

/-- An irreducible normalized μ₅ residual makes the initial form μ₅-irreducible in the
monic degree-`≤ 16` scope. -/
theorem s2Mu5Irreducible_of_irreducible_normRes {g : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 16) (hirr : Irreducible (s2Mu5NormRes h2 hq g)) :
    S2Mu5Irreducible h2 hq g := by
  refine ⟨hmon.ne_zero, ?_, ?_⟩
  · intro hone
    have hd := mu5NormRes_dvd_of_S2Mu5Dvd h2 hq hone
    rw [s2Mu5NormRes_one h2 hq] at hd
    exact hirr.not_isUnit (isUnit_of_dvd_one hd)
  · intro x y hxy
    have hd := mu5NormRes_dvd_of_S2Mu5Dvd h2 hq hxy
    rw [s2Mu5NormRes_mul h2 hq] at hd
    have hprime : Prime (s2Mu5NormRes h2 hq g) :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
    rcases hprime.2.2 _ _ hd with hdx | hdy
    · exact Or.inl (S2Mu5Dvd_of_mu5NormRes_dvd h2 hq hmon hdeg hirr.not_isUnit hdx)
    · exact Or.inr (S2Mu5Dvd_of_mu5NormRes_dvd h2 hq hmon hdeg hirr.not_isUnit hdy)

/-- A positive-degree polynomial of degree at most sixteen whose normalized μ₅ residual is
not a unit is μ₅-minimal. -/
theorem s2Mu5Minimal_of_not_isUnit_normRes {g : Polynomial O}
    (hpos : 0 < g.natDegree) (hdeg : g.natDegree ≤ 16)
    (hnu : ¬ IsUnit (s2Mu5NormRes h2 hq g)) :
    S2Mu5Minimal h2 hq g :=
  ⟨hpos, fun f hf0 hdegf hdvd =>
    hnu (isUnit_of_dvd_unit (mu5NormRes_dvd_of_S2Mu5Dvd h2 hq hdvd)
      (s2Mu5NormRes_isUnit_of_natDegree_lt_sixteen h2 hq hf0 (by omega)))⟩

/-- At the degree-sixteen μ₅ recipe size, irreducible normalized residual implies
μ₅-minimality. -/
theorem s2Mu5Minimal_of_irreducible_normRes {g : Polynomial O}
    (hdeg : g.natDegree = 16) (hirr : Irreducible (s2Mu5NormRes h2 hq g)) :
    S2Mu5Minimal h2 hq g :=
  s2Mu5Minimal_of_not_isUnit_normRes h2 hq (by omega) (le_of_eq hdeg) hirr.not_isUnit

/-! ## D4-14 Part 1 — the μ₅ key criterion, field shape (mirror of `C136d3` D3-16 Part 1) -/

/-- ★ **D4-14 — the literal μ₅ `key_criterion`** (the `FGMNSourceLaws.key_criterion`
field shape at `(e', f', u') = (1, 1, 171)`, `r = 4`): at the depth-four recipe degree
`1·1·deg(keyAt 4) = 16`, monicity, residual irreducibility, residual degree one, and a
nonzero residual scalar assemble μ₅-minimality and μ₅-irreducibility into
key-polynomialhood. -/
theorem s2Mu5_key_criterion :
    ∀ g : Polynomial O, g.Monic →
      g.natDegree = 1 * 1 * ((s2DepthFourKeyChain h2 hq).keyAt 4).natDegree →
      Irreducible (s2Mu5NormRes h2 hq g) →
      (s2Mu5NormRes h2 hq g).natDegree = 1 →
      (s2Mu5NormRes h2 hq g).coeff 0 ≠ 0 →
      S2Mu5KeyPoly h2 hq g := by
  intro g hmon hdeg hirr _ _
  have hkd : ((s2DepthFourKeyChain h2 hq).keyAt 4).natDegree = 16 := by
    rw [s2DepthFourKeyChain_keyAt_four, g16_natDegree h2 hq]
  have hdeg16 : g.natDegree = 16 := by
    rw [hdeg, hkd]
  refine ⟨hmon, s2Mu5Minimal_of_irreducible_normRes h2 hq hdeg16 hirr, ?_⟩
  exact s2Mu5Irreducible_of_irreducible_normRes h2 hq hmon (by omega) hirr

/-! ## D4-14 Part 2 — ★ the leaf key theorem -/

/-- ★ **D4-14 — the leaf `keyAt4 − Λ` is a μ₅ key polynomial**: D4-12's landed monic
degree-16 leaf with normalized μ₅ residual `X + 1` (irreducible, degree one, nonzero
constant) satisfies the criterion (mirror of `C136d3.s2Mu4KeyPoly_g16`, one level up). -/
theorem S2Mu5KeyPoly_leaf : S2Mu5KeyPoly h2 hq (s2Mu5Leaf h2 hq) := by
  refine s2Mu5_key_criterion h2 hq (s2Mu5Leaf h2 hq) (s2Mu5Leaf_monic h2 hq) ?_ ?_ ?_ ?_
  · rw [s2DepthFourKeyChain_keyAt_four, g16_natDegree h2 hq, s2Mu5Leaf_natDegree h2 hq]
  · rw [s2Mu5NormRes_leaf h2 hq]
    exact s2Mu3_X_add_one_irreducible h2 hq
  · rw [s2Mu5NormRes_leaf h2 hq, ← Polynomial.C_1, Polynomial.natDegree_X_add_C]
  · rw [s2Mu5NormRes_leaf h2 hq]
    simp

/-! ## D4-14 Part 3 — initial forms through the μ₅ graded piece (mirror of D3-17 Part 0) -/

/-- The S2-specialized μ₅ term bound (wrapper over `C136e0.dv4Supp_le_term`). -/
private theorem dv4Supp_le_term_s2 (f : Polynomial O) (j : ℕ) :
    dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
        85 2 (g16 h2 hq) f 171 1
      ≤ 1 • dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) 85 2 (g16 h2 hq) f j + (171 * j : ℕ∞) :=
  dv4Supp_le_term (Ψ₂ := s2DepthTwoKeyAt h2 hq 2) (Ψ₃ := g8 h2 hq) (ℓ₂ := 2) (ℓ₃ := 2)
    (ℓ₄ := 1) ((s2Tower h2 hq).levelDatum h2) (g16_monic h2 hq)
    (by rw [g16_natDegree h2 hq]; norm_num) 21 (by norm_num) 85 (by norm_num) f 171
    (by norm_num) j

private theorem s2Mu5GradedRes_neg_of_le {β : ℕ} {g : Polynomial O}
    (hg : (β : ℕ∞) ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2 (g16 h2 hq) g 171 1) :
    s2Mu5GradedRes h2 hq β (-g) = -s2Mu5GradedRes h2 hq β g := by
  have hneg : (β : ℕ∞) ≤ dv4Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2 (g16 h2 hq) (-g) 171 1 := by
    rw [dv4Supp_neg _ (s2Φ₂_monic h2 hq) 21 2 (s2g8_monic h2 hq) 85 2
      (g16_monic h2 hq) g 171 1]
    exact hg
  have hsum := s2Mu5GradedRes_add_of_le h2 hq hg hneg
  rw [add_neg_cancel, s2Mu5GradedRes_zero h2 hq] at hsum
  linear_combination hsum.symm

private theorem mu5_initialEquiv_iff_gradedRes {β : ℕ} {g h : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g) (hh : S2Mu5ExactGrade h2 hq β h) :
    S2Mu5InitialEquiv h2 hq g h ↔
      s2Mu5GradedRes h2 hq β g = s2Mu5GradedRes h2 hq β h := by
  have hvg : s2Hgt₅ h2 hq g = (β : WithTop ℤ) := hg
  have hvh : s2Hgt₅ h2 hq h = (β : WithTop ℤ) := hh
  constructor
  · intro hgh
    rcases hgh with ⟨hlt, -⟩ | ⟨hg0, -⟩
    · have habove : S2Mu5AboveGrade h2 hq β (g - h) := by
        show (β : WithTop ℤ) < s2Hgt₅ h2 hq (g - h)
        rw [← hvg]
        exact hlt
      have hdecomp : g = h + (g - h) := by ring
      have hadd := s2Mu5GradedRes_add_of_le h2 hq
        (le_of_eq ((S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hh).symm)
        (le_of_lt ((S2Mu5AboveGrade_iff_dv4Supp h2 hq).mp habove))
      rw [← hdecomp, s2Mu5GradedRes_zero_of_above h2 hq habove, add_zero] at hadd
      exact hadd
    · exact absurd hg0 (S2Mu5ExactGrade_not_zero h2 hq hg)
  · intro hres
    rcases eq_or_ne (g - h) 0 with hgh0 | hgh0
    · rw [sub_eq_zero.mp hgh0]
      exact S2Mu5InitialEquiv_refl h2 hq h
    · have hnegh : S2Mu5ExactGrade h2 hq β (-h) := by
        rw [S2Mu5ExactGrade_iff_dv4Supp h2 hq,
          dv4Supp_neg _ (s2Φ₂_monic h2 hq) 21 2 (s2g8_monic h2 hq) 85 2
            (g16_monic h2 hq) h 171 1]
        exact (S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hh
      have hvneg : s2Hgt₅ h2 hq (-h) = (β : WithTop ℤ) := hnegh
      have hge : (β : WithTop ℤ) ≤ s2Hgt₅ h2 hq (g - h) := by
        have hmin := s2Hgt₅_add_ge h2 hq g (-h)
        rw [← sub_eq_add_neg, hvg, hvneg, min_self] at hmin
        exact hmin
      rcases hge.lt_or_eq with hlt | heqv
      · refine Or.inl ⟨?_, hvg.trans hvh.symm⟩
        rw [hvg]
        exact hlt
      · have hexact : S2Mu5ExactGrade h2 hq β (g - h) := heqv.symm
        have hne := s2Mu5GradedRes_ne_zero_of_exact h2 hq hexact
        have hadd := s2Mu5GradedRes_add_of_le h2 hq
          (le_of_eq ((S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hg).symm)
          (le_of_eq ((S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hnegh).symm)
        rw [← sub_eq_add_neg,
          s2Mu5GradedRes_neg_of_le h2 hq
            (le_of_eq ((S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hh).symm),
          hres, add_neg_cancel] at hadd
        exact absurd hadd hne

/-! ## D4-14 Part 4 — the grade-comparison obstruction and minimality of `g16`

RECORDED DEVIATION from the D3-17 pattern: at μ₄ the carried key's minimality rode the
PARITY of exact grades below the development degree (`ℓ₄ = 2`).  At μ₅ there is no parity
gate (`S2Mu5PrevGrade` is ALL grades) — but there is a STRONGER mechanism: the carried
key's own μ₅ graded residual is `X` (D4-09's landed `s2Mu5GradedRes_key`, NOT `1` as at
`e' = 2`), so anything `g16` μ₅-divides has VANISHING residual scalar, while everything
of degree `< 16` has NONVANISHING scalar (D4-08).  No case split on grade classes at
all. -/

private theorem not_mu5Dvd_g16_of_coeff_zero_ne {β : ℕ} {g : Polynomial O}
    (hg : S2Mu5ExactGrade h2 hq β g)
    (hc : (s2Mu5GradedRes h2 hq β g).coeff 0 ≠ 0) :
    ¬ S2Mu5Dvd h2 hq (g16 h2 hq) g := by
  rintro ⟨q, hq'⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero] at hq'
    exact S2Mu5ExactGrade_not_zero h2 hq hg
      ((S2Mu5InitialEquiv_zero_right h2 hq).mp hq')
  · obtain ⟨β', hβ'⟩ := S2Mu5ExactGrade_exists h2 hq hq0
    have hkq : S2Mu5ExactGrade h2 hq (171 + β')
        ((g16 h2 hq : Polynomial O) * q) :=
      S2Mu5ExactGrade_mul h2 hq (tooth_g16 h2 hq) hβ'
    have hgkq : S2Mu5ExactGrade h2 hq β
        ((g16 h2 hq : Polynomial O) * q) :=
      S2Mu5ExactGrade_of_initialEquiv h2 hq hg hq'
    have hβeq : β = 171 + β' := S2Mu5ExactGrade_unique h2 hq hgkq hkq
    subst hβeq
    have hres := (mu5_initialEquiv_iff_gradedRes h2 hq hg hgkq).mp hq'
    have hmul := s2Mu5GradedRes_mul h2 hq (tooth_g16 h2 hq) hβ'
    rw [s2Mu5GradedRes_key h2 hq] at hmul
    rw [hmul] at hres
    apply hc
    rw [hres, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]

private theorem mu5Minimal_g16 : S2Mu5Minimal h2 hq (g16 h2 hq) := by
  refine ⟨by rw [g16_natDegree h2 hq]; omega, fun g hg0 hdeg hdvd => ?_⟩
  rw [g16_natDegree h2 hq] at hdeg
  obtain ⟨β, hβ⟩ := S2Mu5ExactGrade_exists h2 hq hg0
  exact not_mu5Dvd_g16_of_coeff_zero_ne h2 hq hβ
    (s2Mu5GradedRes_coeff_zero_ne_zero_of_exact h2 hq hβ hdeg) hdvd

private theorem not_mu5Dvd_g16_one :
    ¬ S2Mu5Dvd h2 hq (g16 h2 hq) (1 : Polynomial O) :=
  (mu5Minimal_g16 h2 hq).2 1 one_ne_zero
    (by rw [Polynomial.natDegree_one, g16_natDegree h2 hq]; omega)

/-! ## D4-14 Part 5 — the slot-zero test and primality (mirror of D3-17 Part 2, no parity) -/

private theorem mu5Coeff_ne_zero_of_slot {β s : ℕ} {g : Polynomial O}
    (hgate : S2Mu5SlotOnGrade h2 hq β g s) :
    s2Mu5Coeff h2 hq β g s ≠ 0 := by
  have hinner : S2Mu4ExactGrade h2 hq (β - 171 * s) (dev (g16 h2 hq) g s) :=
    s2Mu5SlotOnGrade_inner_exact h2 hq hgate
  have hdeg : (dev (g16 h2 hq) g s).natDegree < 16 := by
    rcases eq_or_ne (dev (g16 h2 hq) g s) 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      norm_num
    · have h := Polynomial.natDegree_lt_natDegree h0
        (degree_dev_lt (g16_monic h2 hq)
          (by rw [g16_natDegree h2 hq]; norm_num) g s)
      rwa [g16_natDegree h2 hq] at h
  have hcoeff := s2Mu5Coeff_slot h2 hq hgate
  rw [s2Mu5Eps_eq_one, one_mul] at hcoeff
  have heval : Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2)
      (s2Mu4GradedRes h2 hq (β - 171 * s) (dev (g16 h2 hq) g s))
      = (s2Mu4GradedRes h2 hq (β - 171 * s) (dev (g16 h2 hq) g s)).coeff 0 := by
    conv_lhs => rw [s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hdeg (β - 171 * s)]
    exact Polynomial.eval_C
  rw [hcoeff, heval]
  intro hc0
  have hzero : s2Mu4GradedRes h2 hq (β - 171 * s) (dev (g16 h2 hq) g s) = 0 := by
    rw [s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hdeg (β - 171 * s), hc0,
      Polynomial.C_0]
  exact s2Mu4GradedRes_ne_zero_of_exact h2 hq hinner hzero

private theorem not_mu5Dvd_g16_of_slotZero {β : ℕ} {f : Polynomial O}
    (hf : S2Mu5ExactGrade h2 hq β f) (hgate : S2Mu5SlotOnGrade h2 hq β f 0) :
    ¬ S2Mu5Dvd h2 hq (g16 h2 hq) f := by
  have hc : (s2Mu5GradedRes h2 hq β f).coeff 0 ≠ 0 := by
    rw [s2Mu5GradedRes_coeff]
    exact mu5Coeff_ne_zero_of_slot h2 hq hgate
  exact not_mu5Dvd_g16_of_coeff_zero_ne h2 hq hf hc

/-- Off the slot-zero gate, the initial form of `f` IS `g16` times the monic quotient —
the concrete witness form (consumed with its explicit quotient by D4-16's dichotomy). -/
private theorem mu5_equiv_keyMulDiv_of_not_slotZero {β : ℕ} {f : Polynomial O}
    (hf : S2Mu5ExactGrade h2 hq β f) (hgate : ¬ S2Mu5SlotOnGrade h2 hq β f 0) :
    S2Mu5InitialEquiv h2 hq f ((g16 h2 hq : Polynomial O) * (f /ₘ g16 h2 hq)) := by
  have hmon : (g16 h2 hq : Polynomial O).Monic := g16_monic h2 hq
  have hmod : f %ₘ g16 h2 hq + g16 h2 hq * (f /ₘ g16 h2 hq) = f :=
    Polynomial.modByMonic_add_div f (g16 h2 hq)
  rcases eq_or_ne (f %ₘ g16 h2 hq) 0 with hr0 | hr0
  · have hfeq : (g16 h2 hq : Polynomial O) * (f /ₘ g16 h2 hq) = f := by
      rw [hr0, zero_add] at hmod
      exact hmod
    rw [hfeq]
    exact S2Mu5InitialEquiv_refl h2 hq f
  · have hdegr : (f %ₘ g16 h2 hq).natDegree < 16 := by
      have h := Polynomial.natDegree_lt_natDegree hr0
        (Polynomial.degree_modByMonic_lt f hmon)
      rwa [g16_natDegree h2 hq] at h
    have hdevr : dev (g16 h2 hq) (f %ₘ g16 h2 hq) 0 = f %ₘ g16 h2 hq := by
      rw [dev_zero_pin]
      exact (Polynomial.modByMonic_eq_self_iff hmon).mpr
        (Polynomial.degree_modByMonic_lt f hmon)
    have hpin0 : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 (g16 h2 hq) (f %ₘ g16 h2 hq) 0
        = dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) 85 2 (g16 h2 hq) f 0 := by
      rw [dv4Pin, hdevr, dv4Pin, dev_zero_pin]
    have hsupp_r : dv4Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) 85 2 (g16 h2 hq) (f %ₘ g16 h2 hq) 171 1
        = 1 • dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) 85 2 (g16 h2 hq) f 0 := by
      refine le_antisymm ?_ ?_
      · have h := dv4Supp_le_term_s2 h2 hq (f %ₘ g16 h2 hq) 0
        rw [hpin0] at h
        simpa using h
      · rw [dv4Supp]
        refine Finset.le_inf fun j _ => ?_
        match j with
        | 0 =>
          rw [hpin0]
          simp
        | j + 1 =>
          have hpin_top : dv4Pin ((s2Tower h2 hq).levelDatum h2)
              (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2 (g16 h2 hq)
              (f %ₘ g16 h2 hq) (j + 1) = ⊤ := by
            rw [dv4Pin, dev_eq_zero_of_lt (g16_monic h2 hq)
              (by rw [g16_natDegree h2 hq]; norm_num) (f %ₘ g16 h2 hq) (j + 1)
              (by rw [g16_natDegree h2 hq]; omega)]
            exact dv4Hgt_zero ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2)
              21 (by norm_num) (g8 h2 hq) 85 (by norm_num)
          rw [hpin_top, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 1), top_add]
          exact le_top
    have hle : (β : ℕ∞) ≤ 1 • dv4Pin ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2 (g16 h2 hq) f 0 := by
      have hterm := dv4Supp_le_term_s2 h2 hq f 0
      rw [(S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hf] at hterm
      simpa using hterm
    have hne : 1 • dv4Pin ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2 (g16 h2 hq) f 0 ≠ (β : ℕ∞) := by
      intro heq
      have hfin : dv4Pin ((s2Tower h2 hq).levelDatum h2)
          (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2 (g16 h2 hq) f 0 ≠ ⊤ := by
        intro htop
        rw [htop, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 1)] at heq
        exact WithTop.top_ne_coe heq
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
      refine hgate ((s2Mu5SlotOnGrade_iff h2 hq).mpr ⟨m, hm.symm, ?_⟩)
      rw [← hm, nsmul_eq_mul] at heq
      have h1m : (1 * m : ℕ) = β := by exact_mod_cast heq
      omega
    have hltE : (β : ℕ∞) < 1 • dv4Pin ((s2Tower h2 hq).levelDatum h2)
        (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2 (g16 h2 hq) f 0 :=
      lt_of_le_of_ne hle (Ne.symm hne)
    have hgt : s2Hgt₅ h2 hq f < s2Hgt₅ h2 hq (f %ₘ g16 h2 hq) := by
      have hvf : s2Hgt₅ h2 hq f = (β : WithTop ℤ) := hf
      rw [hvf, s2Hgt₅_eq_dv4Supp h2 hq, hsupp_r,
        show (β : WithTop ℤ) = C130s6.toZ (β : ℕ∞) by norm_cast]
      exact toZ_lt_toZ_iff.mpr hltE
    have hkw : (g16 h2 hq : Polynomial O) * (f /ₘ g16 h2 hq) = f - f %ₘ g16 h2 hq :=
      (sub_eq_of_eq_add' hmod.symm).symm
    have hval_kw : s2Hgt₅ h2 hq ((g16 h2 hq : Polynomial O) * (f /ₘ g16 h2 hq))
        = s2Hgt₅ h2 hq f := by
      rw [hkw, sub_eq_add_neg,
        s2Hgt₅_add_eq h2 hq _ _ (by rw [s2Hgt₅_neg h2 hq]; exact ne_of_lt hgt),
        s2Hgt₅_neg h2 hq]
      exact min_eq_left (le_of_lt hgt)
    refine Or.inl ⟨?_, hval_kw.symm⟩
    rw [show f - (g16 h2 hq : Polynomial O) * (f /ₘ g16 h2 hq) = f %ₘ g16 h2 hq
      from by rw [hkw]; ring]
    exact hgt

private theorem mu5Dvd_g16_of_not_slotZero {β : ℕ} {f : Polynomial O}
    (hf : S2Mu5ExactGrade h2 hq β f) (hgate : ¬ S2Mu5SlotOnGrade h2 hq β f 0) :
    S2Mu5Dvd h2 hq (g16 h2 hq) f :=
  ⟨f /ₘ g16 h2 hq, mu5_equiv_keyMulDiv_of_not_slotZero h2 hq hf hgate⟩

private theorem mu5Dvd_g16_or (a b : Polynomial O)
    (hdvd : S2Mu5Dvd h2 hq (g16 h2 hq) (a * b)) :
    S2Mu5Dvd h2 hq (g16 h2 hq) a ∨ S2Mu5Dvd h2 hq (g16 h2 hq) b := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inl (S2Mu5Dvd_zero h2 hq _)
  rcases eq_or_ne b 0 with rfl | hb0
  · exact Or.inr (S2Mu5Dvd_zero h2 hq _)
  have hexa := S2Mu5ExactGrade_s2Mu5GradeOf h2 hq ha0
  have hexb := S2Mu5ExactGrade_s2Mu5GradeOf h2 hq hb0
  by_cases hga : S2Mu5SlotOnGrade h2 hq (s2Mu5GradeOf h2 hq a) a 0
  swap
  · exact Or.inl (mu5Dvd_g16_of_not_slotZero h2 hq hexa hga)
  by_cases hgb : S2Mu5SlotOnGrade h2 hq (s2Mu5GradeOf h2 hq b) b 0
  swap
  · exact Or.inr (mu5Dvd_g16_of_not_slotZero h2 hq hexb hgb)
  exfalso
  have hexab := S2Mu5ExactGrade_mul h2 hq hexa hexb
  have hca : (s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq a) a).coeff 0 ≠ 0 := by
    rw [s2Mu5GradedRes_coeff]
    exact mu5Coeff_ne_zero_of_slot h2 hq hga
  have hcb : (s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq b) b).coeff 0 ≠ 0 := by
    rw [s2Mu5GradedRes_coeff]
    exact mu5Coeff_ne_zero_of_slot h2 hq hgb
  have hcab :
      (s2Mu5GradedRes h2 hq (s2Mu5GradeOf h2 hq a + s2Mu5GradeOf h2 hq b)
        (a * b)).coeff 0 ≠ 0 := by
    rw [s2Mu5GradedRes_mul h2 hq hexa hexb, Polynomial.mul_coeff_zero]
    exact mul_ne_zero hca hcb
  exact not_mu5Dvd_g16_of_coeff_zero_ne h2 hq hexab hcab hdvd

/-! ## D4-14 Part 6 — ★ the carried key -/

/-- ★ **D4-14 — the carried depth-four key `g16 = keyAt 4` is a μ₅ key polynomial**
(published Prop 1.7(4)'s occurrence, mirror of `C136d3.s2Mu4KeyPoly_g8` one level up:
minimality and primality via the grade-comparison obstruction and the slot-zero gate —
the nonunit-residual criterion is intentionally inapplicable, `R₆(g16) = 1`). -/
theorem S2Mu5KeyPoly_g16 : S2Mu5KeyPoly h2 hq (g16 h2 hq) := by
  refine ⟨g16_monic h2 hq, mu5Minimal_g16 h2 hq, ?_⟩
  exact ⟨(g16_monic h2 hq).ne_zero, not_mu5Dvd_g16_one h2 hq,
    fun a b hab => mu5Dvd_g16_or h2 hq a b hab⟩

/-- **D4-14 — the carried key's normalized μ₅ residual is `1`** (alias of the landed
`C136e1.s2Mu5NormRes_key`, restated under the D4-14 name). -/
theorem s2Mu5NormRes_g16 :
    s2Mu5NormRes h2 hq (g16 h2 hq : Polynomial O) = 1 :=
  s2Mu5NormRes_key h2 hq

/-- Regression tooth: the same carried polynomial reads as `1` at μ₅ but as `X + 1` at
μ₄ (mirror of `C136d3.tooth_g8_mu4_vs_mu3`, one level up). -/
theorem tooth_g16_mu5_vs_mu4 :
    s2Mu5NormRes h2 hq (g16 h2 hq : Polynomial O) = 1 ∧
      s2Mu4NormRes h2 hq (g16 h2 hq : Polynomial O) = Polynomial.X + 1 :=
  ⟨s2Mu5NormRes_g16 h2 hq, s2Mu4NormRes_g16 h2 hq⟩

/-! ## D4-15 Part 0 — irreducibility of μ₅ key polynomials (mirror of D3-16 Part 2) -/

/-- ★ **D4-15 — every μ₅ key polynomial is irreducible over `O`** (mirror of
`C136d3.s2Mu4_key_irreducible`: μ₅-primality splits a factorization, μ₅-minimality
excludes either strictly smaller factor). -/
theorem s2Mu5_key_irreducible {g : Polynomial O} (hkey : S2Mu5KeyPoly h2 hq g) :
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
    have hself : S2Mu5Dvd h2 hq g (a * b) :=
      S2Mu5Dvd_of_dvd h2 hq (dvd_of_eq hab)
    rcases hirr.2.2 a b hself with hdvd | hdvd
    · exact hmin.2 a ha0 (by omega) hdvd
    · exact hmin.2 b hb0 (by omega) hdvd

/-! ## D4-15 Part 1 — both μ₅ keys are irreducible over `O` -/

/-- ★ the leaf `keyAt4 − Λ` is irreducible in `O[x]`. -/
theorem s2Mu5Leaf_irreducible : Irreducible (s2Mu5Leaf h2 hq) :=
  s2Mu5_key_irreducible h2 hq (S2Mu5KeyPoly_leaf h2 hq)

/-- ★ the carried key `g16 = keyAt 4` is irreducible in `O[x]` (through its μ₅
keyhood — the μ₄ residual criterion route is inapplicable at residual `1`). -/
theorem s2_g16_irreducible : Irreducible (g16 h2 hq : Polynomial O) :=
  s2Mu5_key_irreducible h2 hq (S2Mu5KeyPoly_g16 h2 hq)

/-! ## D4-15 Part 2 — the two keys are distinct monics (`Λ ≠ 0`) -/

/-- The leaf and the carried key differ, since `Λ ≠ 0` (C136t). -/
theorem s2Mu5Leaf_ne_g16 : s2Mu5Leaf h2 hq ≠ (g16 h2 hq : Polynomial O) := by
  intro heq
  have hLeaf : s2Mu5Leaf h2 hq = (g16 h2 hq : Polynomial O) - s2Mu5Lambda h2 hq := by
    rw [s2Mu5Leaf_eq_keyAt_sub h2 hq, s2DepthFourKeyChain_keyAt_four]
  rw [hLeaf] at heq
  exact s2Mu5Lambda_ne_zero h2 hq (sub_eq_self.mp heq)

/-! ## D4-15 Part 3 — fraction-map irreducibility (the Gauss transport, forward
direction of `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` — the
direction OPPOSITE to `C130lb.irreducible_of_fraction_map_irreducible`). -/

/-- The leaf's image in `K[x]` is irreducible, for any fraction field `K` of `O`. -/
theorem s2Mu5Leaf_map_irreducible {K : Type*} [Field K] [Algebra O K]
    [IsFractionRing O K] :
    Irreducible ((s2Mu5Leaf h2 hq).map (algebraMap O K)) :=
  ((s2Mu5Leaf_monic h2 hq).irreducible_iff_irreducible_map_fraction_map).mp
    (s2Mu5Leaf_irreducible h2 hq)

/-- The carried key's image in `K[x]` is irreducible, for any fraction field `K` of
`O`. -/
theorem s2_g16_map_irreducible {K : Type*} [Field K] [Algebra O K]
    [IsFractionRing O K] :
    Irreducible ((g16 h2 hq : Polynomial O).map (algebraMap O K)) :=
  ((g16_monic h2 hq).irreducible_iff_irreducible_map_fraction_map).mp
    (s2_g16_irreducible h2 hq)

/-! ## D4-15 Part 4 — ★ fraction-map coprimality of the leaf (and its square) with
`keyAt 4`.  Two non-associated monic irreducibles in the Bézout domain `K[x]` are
coprime; non-association descends along the injective fraction map to `Λ ≠ 0`. -/

/-- ★ the leaf and the carried key `keyAt 4 = g16` are coprime in `K[x]`. -/
theorem s2Mu5_leaf_keyAt4_coprime_fractionMap {K : Type*} [Field K] [Algebra O K]
    [IsFractionRing O K] :
    IsCoprime ((s2Mu5Leaf h2 hq).map (algebraMap O K))
      ((g16 h2 hq : Polynomial O).map (algebraMap O K)) := by
  refine ((s2Mu5Leaf_map_irreducible h2 hq).coprime_iff_not_dvd).mpr ?_
  intro hdvd
  have hassoc := (s2Mu5Leaf_map_irreducible h2 hq).associated_of_dvd
    (s2_g16_map_irreducible h2 hq) hdvd
  have heq := Polynomial.eq_of_monic_of_associated
    ((s2Mu5Leaf_monic h2 hq).map (algebraMap O K))
    ((g16_monic h2 hq).map (algebraMap O K)) hassoc
  exact s2Mu5Leaf_ne_g16 h2 hq
    (Polynomial.map_injective (algebraMap O K) (IsFractionRing.injective O K) heq)

/-- ★★ **D4-15 — the row's ask**: `leaf²` and `keyAt 4` are coprime in `K[x]`, for any
fraction field `K` of `O`. -/
theorem s2Mu5_leafSq_keyAt4_coprime_fractionMap {K : Type*} [Field K] [Algebra O K]
    [IsFractionRing O K] :
    IsCoprime ((s2Mu5Leaf h2 hq ^ 2).map (algebraMap O K))
      ((g16 h2 hq : Polynomial O).map (algebraMap O K)) := by
  rw [Polynomial.map_pow]
  exact (s2Mu5_leaf_keyAt4_coprime_fractionMap h2 hq).pow_left

/-! ## D4-16 Part 0 — top-slot tools (the μ₅ key-structure bank's inner reads)

RECORDED DEVIATION from the D3-17 pattern (Parts 4–5's seven-digit ledger): at μ₅ the
divisibility pin's pair bound is the VALUATION MULTIPLICATIVITY — for monic digits `A`,
`Q` with `deg A + deg Q = 16`, `μ₄(A) + μ₄(Q) = μ₄(A·Q) ≤ 2·0 + 85·2 = 170` by ONE
top-slot read on the monic degree-16 product (`dev_top_eq_one` at slot 2 of the
`g₈`-development).  No monic-digit bound bank is needed; the bound is tight against the
[G5F] floor `170 < 171`. -/

omit [Finite (ResidueField O)] in
/-- The `Ψ`-adic TOP digit of a monic polynomial of degree `m·deg Ψ + r` (`r < deg Ψ`)
is monic of degree `r` (the general-`r` companion of `C131v.dev_top_eq_one`). -/
private theorem dev_top_monic {φ : Polynomial O} (hφ : φ.Monic) (_hd : 0 < φ.natDegree) :
    ∀ (m : ℕ) (A : Polynomial O) (r : ℕ), A.Monic → r < φ.natDegree →
      A.natDegree = m * φ.natDegree + r →
      (dev φ A m).Monic ∧ (dev φ A m).natDegree = r := by
  intro m
  induction m with
  | zero =>
      intro A r hA hr hdeg
      rw [zero_mul, zero_add] at hdeg
      have hself : dev φ A 0 = A := by
        rw [dev_zero_pin]
        exact (Polynomial.modByMonic_eq_self_iff hφ).mpr
          (Polynomial.degree_lt_degree (by omega))
      rw [hself]
      exact ⟨hA, hdeg⟩
  | succ m ih =>
      intro A r hA hr hdeg
      show (dev φ (A /ₘ φ) m).Monic ∧ (dev φ (A /ₘ φ) m).natDegree = r
      have hdle : φ.degree ≤ A.degree := by
        rw [Polynomial.degree_eq_natDegree hφ.ne_zero,
          Polynomial.degree_eq_natDegree hA.ne_zero, hdeg]
        exact_mod_cast Nat.le_add_right_of_le
          (Nat.le_mul_of_pos_left φ.natDegree (Nat.succ_pos m))
      refine ih (A /ₘ φ) r (monic_divByMonic hA hφ hdle) hr ?_
      rw [Polynomial.natDegree_divByMonic A hφ, hdeg, Nat.succ_mul]
      omega

/-- the inner μ₄ read of the digit `1` is `0` (D3-05's `s2Hgt₄ 1 = 0` transported across
the `s2Hgt₄_eq_dv3Supp` anti-drift pin — file-local copy of e0/e1's private shim). -/
private theorem s2_dv4Hgt_one :
    dv4Hgt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2
      (1 : Polynomial O) = (0 : ℕ∞) := by
  apply C130s6.toZ_inj
  rw [dv4Hgt, ← s2Hgt₄_eq_dv3Supp h2 hq, s2Hgt₄_one_eq_zero h2 hq]
  rfl

/-- the inner μ₃ read of the digit `1` is `0` (the μ₃ twin, one level down: C132nv5's
`s2Hgt₃ 1 = 0` across `s2Hgt₃_eq_dv2Supp`). -/
private theorem s2_dv3Hgt_one :
    dv3Hgt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (1 : Polynomial O) = (0 : ℕ∞) := by
  apply C130s6.toZ_inj
  rw [dv3Hgt_eq_dv2Supp, ← s2Hgt₃_eq_dv2Supp h2 hq, s2Hgt₃_one_eq_zero h2 hq]
  rfl

/-- The S2-specialized μ₄ term bound (wrapper over `C136d0.dv3Supp_le_term`; file-local
copy of C136d3's private shim). -/
private theorem dv3Supp_le_term_s2 (f : Polynomial O) (j : ℕ) :
    dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq)
        f 85 2
      ≤ 2 • dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) f j + (85 * j : ℕ∞) :=
  C136d0.dv3Supp_le_term ((s2Tower h2 hq).levelDatum h2) (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) 21 (by norm_num) f 85 (by norm_num) j

/-- Any pin bound at any abscissa bounds the exact μ₄ grade along the weight line. -/
private theorem mu4_grade_le_of_pin_le {β c j : ℕ} {g : Polynomial O}
    (hβ : S2Mu4ExactGrade h2 hq β g)
    (hpin : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) g j ≤ (c : ℕ∞)) :
    β ≤ 2 * c + 85 * j := by
  have hterm := dv3Supp_le_term_s2 h2 hq g j
  rw [(S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hβ] at hterm
  have hle2 : (β : ℕ∞) ≤ 2 • (c : ℕ∞) + (85 * j : ℕ∞) :=
    le_trans hterm (add_le_add (nsmul_le_nsmul_right hpin 2) le_rfl)
  rw [nsmul_eq_mul] at hle2
  exact_mod_cast hle2

/-- Any pin bound at any abscissa bounds the exact μ₅ grade along the weight line. -/
private theorem mu5_grade_le_of_pin_le {β c j : ℕ} {g : Polynomial O}
    (hβ : S2Mu5ExactGrade h2 hq β g)
    (hpin : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) g j ≤ (c : ℕ∞)) :
    β ≤ 1 * c + 171 * j := by
  have hterm := dv4Supp_le_term_s2 h2 hq g j
  rw [(S2Mu5ExactGrade_iff_dv4Supp h2 hq).mp hβ] at hterm
  have hle2 : (β : ℕ∞) ≤ 1 • (c : ℕ∞) + (171 * j : ℕ∞) :=
    le_trans hterm (add_le_add (nsmul_le_nsmul_right hpin 1) le_rfl)
  rw [nsmul_eq_mul] at hle2
  exact_mod_cast hle2

/-- ★ **the μ₄ pair bound via valuation multiplicativity** — the [G5F] tight floor:
monic digits of complementary degrees `r + (16 − r) = 16` carry total μ₄ grade at most
`170 < 171`, read off ONE top slot of the monic degree-16 product. -/
private theorem mu4_pair_grade_le {A B : Polynomial O} {α β : ℕ}
    (hA : A.Monic) (hB : B.Monic) (hd : A.natDegree + B.natDegree = 16)
    (hα : S2Mu4ExactGrade h2 hq α A) (hβ : S2Mu4ExactGrade h2 hq β B) :
    α + β ≤ 170 := by
  have hAB : S2Mu4ExactGrade h2 hq (α + β) (A * B) := S2Mu4ExactGrade_mul h2 hq hα hβ
  have hABmon : (A * B).Monic := hA.mul hB
  have hABdeg : (A * B).natDegree = 16 := by
    rw [Polynomial.natDegree_mul hA.ne_zero hB.ne_zero, hd]
  have hdev : dev (g8 h2 hq) (A * B) 2 = 1 :=
    dev_top_eq_one (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num) 2 (A * B) hABmon
      (by rw [s2g8_natDegree h2 hq, hABdeg])
  have hpin : dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) (A * B) 2 ≤ ((0 : ℕ) : ℕ∞) := by
    rw [dv3Pin, hdev, s2_dv3Hgt_one h2 hq]
    simp
  have := mu4_grade_le_of_pin_le h2 hq hAB hpin
  omega

/-! ## D4-16 Part 1 — ★ the divisibility pin (mirror of D3-17 Part 6, digit-ledger-free) -/

/-- ★ **the μ₅ divisibility pin**: a monic μ₅-minimal polynomial has degree divisible
by 16.  For `deg g = 16m + r` (`1 ≤ r ≤ 15`) the refuter is `g·Q − g16^(m+1)` with
`Q := g16^(m+1) /ₘ g`; the grade comparison `μ₅(g·Q) ≤ (cA + cQ) + 171m ≤ 170 + 171m
< 171(m+1) = μ₅(g16^(m+1))` rides the multiplicativity pair bound. -/
theorem s2Mu5Minimal_natDegree_sixteen_dvd {g : Polynomial O} (hmon : g.Monic)
    (hmin : S2Mu5Minimal h2 hq g) : 16 ∣ g.natDegree := by
  by_contra hndvd
  obtain ⟨m, r, hr1, hr15, hd⟩ : ∃ m r, 1 ≤ r ∧ r ≤ 15 ∧ g.natDegree = 16 * m + r :=
    ⟨g.natDegree / 16, g.natDegree % 16, by omega, by omega, by omega⟩
  obtain ⟨hAmon, hAdeg⟩ := dev_top_monic (g16_monic h2 hq)
    (by rw [g16_natDegree h2 hq]; norm_num) m g r hmon
    (by rw [g16_natDegree h2 hq]; omega) (by rw [g16_natDegree h2 hq]; omega)
  -- the divisor and its complement
  have hg16pmon : ((g16 h2 hq : Polynomial O) ^ (m + 1)).Monic :=
    (g16_monic h2 hq).pow _
  have hg16pdeg : ((g16 h2 hq : Polynomial O) ^ (m + 1)).natDegree = 16 * (m + 1) := by
    rw [Polynomial.natDegree_pow, g16_natDegree h2 hq]
    ring
  have hdle : g.degree ≤ ((g16 h2 hq : Polynomial O) ^ (m + 1)).degree := by
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero,
      Polynomial.degree_eq_natDegree hg16pmon.ne_zero, hg16pdeg, hd]
    exact_mod_cast (by omega : 16 * m + r ≤ 16 * (m + 1))
  set Q := (g16 h2 hq : Polynomial O) ^ (m + 1) /ₘ g with hQdef
  have hQmon : Q.Monic := monic_divByMonic hg16pmon hmon hdle
  have hQdeg : Q.natDegree = 16 - r := by
    rw [hQdef, Polynomial.natDegree_divByMonic _ hmon, hg16pdeg, hd]
    omega
  have hQself : Q %ₘ (g16 h2 hq) = Q :=
    (Polynomial.modByMonic_eq_self_iff (g16_monic h2 hq)).mpr
      (Polynomial.degree_lt_degree (by rw [g16_natDegree h2 hq, hQdeg]; omega))
  -- the two pin reads as exact μ₄ grades
  obtain ⟨cA, hcA⟩ := S2Mu4ExactGrade_exists h2 hq hAmon.ne_zero
  obtain ⟨cQ, hcQ⟩ := S2Mu4ExactGrade_exists h2 hq hQmon.ne_zero
  have hpg : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) g m ≤ (cA : ℕ∞) := by
    rw [dv4Pin, dv4Hgt_eq_dv3Supp]
    exact le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hcA)
  have hpQ : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) Q 0 ≤ (cQ : ℕ∞) := by
    rw [dv4Pin, dev_zero_pin, hQself, dv4Hgt_eq_dv3Supp]
    exact le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hcQ)
  -- the pair bound (NO digit ledger)
  have hsum : cA + cQ ≤ 170 :=
    mu4_pair_grade_le h2 hq hAmon hQmon (by omega) hcA hcQ
  -- grades
  obtain ⟨β, hβ⟩ := S2Mu5ExactGrade_exists h2 hq hmon.ne_zero
  obtain ⟨γ, hγ⟩ := S2Mu5ExactGrade_exists h2 hq hQmon.ne_zero
  have hβle : β ≤ 1 * cA + 171 * m := mu5_grade_le_of_pin_le h2 hq hβ hpg
  have hγle : γ ≤ 1 * cQ + 171 * 0 := mu5_grade_le_of_pin_le h2 hq hγ hpQ
  have hgQ : S2Mu5ExactGrade h2 hq (β + γ) (g * Q) := S2Mu5ExactGrade_mul h2 hq hβ hγ
  have hkp : S2Mu5ExactGrade h2 hq (171 * (m + 1))
      ((g16 h2 hq : Polynomial O) ^ (m + 1)) :=
    S2Mu5ExactGrade_key_pow h2 hq (m + 1)
  have hlt : β + γ < 171 * (m + 1) := by omega
  -- the perturbation carries the product's initial form
  have hltc : ((β + γ : ℕ) : WithTop ℤ) < ((171 * (m + 1) : ℕ) : WithTop ℤ) := by
    exact_mod_cast hlt
  have hvgq : s2Hgt₅ h2 hq (g * Q) = ((β + γ : ℕ) : WithTop ℤ) := hgQ
  have hvkp : s2Hgt₅ h2 hq ((g16 h2 hq : Polynomial O) ^ (m + 1))
      = ((171 * (m + 1) : ℕ) : WithTop ℤ) := hkp
  have hvf : s2Hgt₅ h2 hq (g * Q - (g16 h2 hq : Polynomial O) ^ (m + 1))
      = ((β + γ : ℕ) : WithTop ℤ) := by
    rw [sub_eq_add_neg, s2Hgt₅_add_eq h2 hq _ _ (by
        rw [s2Hgt₅_neg h2 hq, hvgq, hvkp]; exact hltc.ne), s2Hgt₅_neg h2 hq, hvgq, hvkp]
    exact min_eq_left hltc.le
  have hf_exact : S2Mu5ExactGrade h2 hq (β + γ)
      (g * Q - (g16 h2 hq : Polynomial O) ^ (m + 1)) := hvf
  have hf0 : g * Q - (g16 h2 hq : Polynomial O) ^ (m + 1) ≠ 0 :=
    S2Mu5ExactGrade_not_zero h2 hq hf_exact
  have hequiv : S2Mu5InitialEquiv h2 hq
      (g * Q - (g16 h2 hq : Polynomial O) ^ (m + 1)) (g * Q) := by
    refine Or.inl ⟨?_, ?_⟩
    · rw [show (g * Q - (g16 h2 hq : Polynomial O) ^ (m + 1)) - g * Q
          = -((g16 h2 hq : Polynomial O) ^ (m + 1)) from by ring,
        s2Hgt₅_neg h2 hq, hvkp, hvf]
      exact hltc
    · rw [hvf, hvgq]
  have hdvd : S2Mu5Dvd h2 hq g
      (g * Q - (g16 h2 hq : Polynomial O) ^ (m + 1)) := ⟨Q, hequiv⟩
  -- the degree collapse: the difference is minus the remainder
  have hmodid : (g16 h2 hq : Polynomial O) ^ (m + 1) %ₘ g + g * Q
      = (g16 h2 hq : Polynomial O) ^ (m + 1) :=
    Polynomial.modByMonic_add_div ((g16 h2 hq : Polynomial O) ^ (m + 1)) g
  have hfeq : g * Q - (g16 h2 hq : Polynomial O) ^ (m + 1)
      = -((g16 h2 hq : Polynomial O) ^ (m + 1) %ₘ g) := by
    linear_combination hmodid
  have hfdeg : (g * Q - (g16 h2 hq : Polynomial O) ^ (m + 1)).natDegree
      < g.natDegree := by
    have hR0 : (g16 h2 hq : Polynomial O) ^ (m + 1) %ₘ g ≠ 0 := by
      intro h0
      rw [hfeq, h0, neg_zero] at hf0
      exact hf0 rfl
    rw [hfeq, Polynomial.natDegree_neg]
    exact Polynomial.natDegree_lt_natDegree hR0 (Polynomial.degree_modByMonic_lt _ hmon)
  exact hmin.2 _ hf0 hfdeg hdvd

/-! ## D4-16 Part 2 — ★ the grade pin (mirror of D3-17 Part 7) -/

/-- ★ **the μ₅ grade pin**: a monic μ₅-minimal polynomial has exact grade
`171·(deg g/16)`. -/
theorem s2Mu5Minimal_exactGrade {g : Polynomial O} (hmon : g.Monic)
    (hmin : S2Mu5Minimal h2 hq g) :
    S2Mu5ExactGrade h2 hq (171 * (g.natDegree / 16)) g := by
  have h16 := s2Mu5Minimal_natDegree_sixteen_dvd h2 hq hmon hmin
  set m := g.natDegree / 16 with hm
  have hd : g.natDegree = 16 * m := by omega
  obtain ⟨β, hβ⟩ := S2Mu5ExactGrade_exists h2 hq hmon.ne_zero
  have hdevtop : dev (g16 h2 hq) g m = 1 :=
    dev_top_eq_one (g16_monic h2 hq) (by rw [g16_natDegree h2 hq]; norm_num) m g hmon
      (by rw [g16_natDegree h2 hq]; omega)
  have hpin : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) g m ≤ ((0 : ℕ) : ℕ∞) := by
    rw [dv4Pin, hdevtop, s2_dv4Hgt_one h2 hq]
    simp
  have hle : β ≤ 1 * 0 + 171 * m := mu5_grade_le_of_pin_le h2 hq hβ hpin
  rcases (show β ≤ 171 * m from by omega).lt_or_eq with hlt | heq
  · -- strictly below the top term: the truncation `g − g16^m` refutes minimality
    exfalso
    have hkp : S2Mu5ExactGrade h2 hq (171 * m) ((g16 h2 hq : Polynomial O) ^ m) :=
      S2Mu5ExactGrade_key_pow h2 hq m
    rcases eq_or_ne (g - (g16 h2 hq : Polynomial O) ^ m) 0 with hf0 | hf0
    · have hg : g = (g16 h2 hq : Polynomial O) ^ m := sub_eq_zero.mp hf0
      rw [hg] at hβ
      exact absurd (S2Mu5ExactGrade_unique h2 hq hβ hkp) (by omega)
    · have hltc : ((β : ℕ) : WithTop ℤ) < ((171 * m : ℕ) : WithTop ℤ) := by
        exact_mod_cast hlt
      have hvg : s2Hgt₅ h2 hq g = ((β : ℕ) : WithTop ℤ) := hβ
      have hvk : s2Hgt₅ h2 hq ((g16 h2 hq : Polynomial O) ^ m)
          = ((171 * m : ℕ) : WithTop ℤ) := hkp
      have hvf : s2Hgt₅ h2 hq (g - (g16 h2 hq : Polynomial O) ^ m)
          = ((β : ℕ) : WithTop ℤ) := by
        rw [sub_eq_add_neg, s2Hgt₅_add_eq h2 hq _ _ (by
            rw [s2Hgt₅_neg h2 hq, hvg, hvk]; exact hltc.ne), s2Hgt₅_neg h2 hq, hvg, hvk]
        exact min_eq_left hltc.le
      have hequiv : S2Mu5InitialEquiv h2 hq
          (g - (g16 h2 hq : Polynomial O) ^ m) g := by
        refine Or.inl ⟨?_, ?_⟩
        · rw [show (g - (g16 h2 hq : Polynomial O) ^ m) - g
              = -((g16 h2 hq : Polynomial O) ^ m) from by ring,
            s2Hgt₅_neg h2 hq, hvk, hvf]
          exact hltc
        · rw [hvf, hvg]
      have hdvd : S2Mu5Dvd h2 hq g (g - (g16 h2 hq : Polynomial O) ^ m) :=
        ⟨1, by rw [mul_one]; exact hequiv⟩
      have hkm : ((g16 h2 hq : Polynomial O) ^ m).Monic := (g16_monic h2 hq).pow m
      have hdeg_eq : g.degree = ((g16 h2 hq : Polynomial O) ^ m).degree := by
        rw [Polynomial.degree_eq_natDegree hmon.ne_zero,
          Polynomial.degree_eq_natDegree hkm.ne_zero, Polynomial.natDegree_pow,
          g16_natDegree h2 hq, hd, Nat.mul_comm]
      have hdlt := Polynomial.degree_sub_lt hdeg_eq hmon.ne_zero
        (by rw [hmon.leadingCoeff, hkm.leadingCoeff])
      exact hmin.2 _ hf0 (Polynomial.natDegree_lt_natDegree hf0 hdlt) hdvd
  · rw [← heq]
    exact hβ

/-! ## D4-16 Part 3 — the top slot lives (the μ₅ residual-degree pin) -/

/-- the top slot `m = deg g/16` of a monic exact-grade-`171m` polynomial reads `1`. -/
private theorem key_gradedRes_coeff_top {m : ℕ} {g : Polynomial O} (hmon : g.Monic)
    (hd : g.natDegree = 16 * m) :
    (s2Mu5GradedRes h2 hq (171 * m) g).coeff m = 1 := by
  have hdevtop : dev (g16 h2 hq) g m = 1 :=
    dev_top_eq_one (g16_monic h2 hq) (by rw [g16_natDegree h2 hq]; norm_num) m g hmon
      (by rw [g16_natDegree h2 hq]; omega)
  have hpin : dv4Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 (g16 h2 hq) g m = (0 : ℕ∞) := by
    rw [dv4Pin, hdevtop, s2_dv4Hgt_one h2 hq]
  have hgate : S2Mu5SlotOnGrade h2 hq (171 * m) g m :=
    (s2Mu5SlotOnGrade_iff h2 hq).mpr ⟨0, by simpa using hpin, by omega⟩
  have hslot := s2Mu5Coeff_slot h2 hq hgate
  rw [show 171 * m - 171 * m = 0 from by omega, hdevtop, s2Mu5Eps_eq_one, one_mul,
    s2Mu4GradedRes_one h2 hq, Polynomial.eval_one] at hslot
  rw [s2Mu5GradedRes_coeff]
  exact hslot

/-- the μ₅ graded residual of a monic exact-grade-`171m` degree-`16m` polynomial has
degree exactly `m`. -/
private theorem key_gradedRes_natDegree {m : ℕ} {g : Polynomial O} (hmon : g.Monic)
    (hd : g.natDegree = 16 * m) :
    (s2Mu5GradedRes h2 hq (171 * m) g).natDegree = m := by
  refine le_antisymm ?_ ?_
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    rw [s2Mu5GradedRes_coeff]
    refine s2Mu5Coeff_eq_zero_of_dv4Pin_top h2 hq ?_
    rw [dv4Pin, dev_eq_zero_of_lt (g16_monic h2 hq)
      (by rw [g16_natDegree h2 hq]; norm_num) g N
      (by rw [g16_natDegree h2 hq]; omega)]
    exact dv4Hgt_zero ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21
      (by norm_num) (g8 h2 hq) 85 (by norm_num)
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [key_gradedRes_coeff_top h2 hq hmon hd]
    exact one_ne_zero

/-! ## D4-16 Part 4 — the assembled key-structure facts -/

/-- **the μ₅ key degree pin**: `16 ∣ deg g` for every μ₅ key polynomial. -/
theorem s2Mu5KeyPoly_natDegree_sixteen_dvd {g : Polynomial O}
    (hkey : S2Mu5KeyPoly h2 hq g) : 16 ∣ g.natDegree :=
  s2Mu5Minimal_natDegree_sixteen_dvd h2 hq hkey.1 hkey.2.1

/-- **the grade of a μ₅ key polynomial**: `μ₅(g) = 171·(deg g/16)`. -/
theorem s2Mu5KeyPoly_exactGrade {g : Polynomial O} (hkey : S2Mu5KeyPoly h2 hq g) :
    S2Mu5ExactGrade h2 hq (171 * (g.natDegree / 16)) g :=
  s2Mu5Minimal_exactGrade h2 hq hkey.1 hkey.2.1

/-- **the graded-residual degree of a μ₅ key polynomial** is `deg g/16` (the top slot
lives; higher slots are past the degree). -/
theorem s2Mu5KeyPoly_gradedRes_natDegree {g : Polynomial O}
    (hkey : S2Mu5KeyPoly h2 hq g) :
    (s2Mu5GradedRes h2 hq (171 * (g.natDegree / 16)) g).natDegree
      = g.natDegree / 16 := by
  have h16 := s2Mu5KeyPoly_natDegree_sixteen_dvd h2 hq hkey
  exact key_gradedRes_natDegree h2 hq hkey.1 (by omega)

/-- **the μ₅ trailing/residual ledger**: `ntd + deg R(g) = deg g/16`. -/
private theorem key_ntd_add_normRes_natDegree {g : Polynomial O}
    (hkey : S2Mu5KeyPoly h2 hq g) :
    (s2Mu5GradedRes h2 hq (171 * (g.natDegree / 16)) g).natTrailingDegree
      + (s2Mu5NormRes h2 hq g).natDegree = g.natDegree / 16 := by
  have hex := s2Mu5KeyPoly_exactGrade h2 hq hkey
  have hfac := s2Mu5NormRes_mul_X_pow_of_exact h2 hq hex
  have hN0 : s2Mu5NormRes h2 hq g ≠ 0 := s2Mu5NormRes_ne_zero h2 hq hkey.1.ne_zero
  have hdeg := s2Mu5KeyPoly_gradedRes_natDegree h2 hq hkey
  rw [← hfac, Polynomial.natDegree_mul hN0 (pow_ne_zero _ Polynomial.X_ne_zero),
    Polynomial.natDegree_X_pow] at hdeg
  omega

/-! ## D4-16 Part 5 — ★ the trailing dichotomy (the `∼ g16` fiber is the ONLY
nontrivial strip).  One-step deflation: an off-line slot 0 factors the initial form as
`g16·q`; μ₅-primality forces `g ∣μ₅ g16` (grades pin `deg g = 16`, residual-dvd pins
`R(g) = 1`) or `g ∣μ₅ Q` (killed by minimality, `deg Q = deg g − 16 < deg g`). -/

private theorem key_trailing_dichotomy {g : Polynomial O} (hkey : S2Mu5KeyPoly h2 hq g) :
    (s2Mu5GradedRes h2 hq (171 * (g.natDegree / 16)) g).natTrailingDegree = 0
      ∨ (g.natDegree = 16 ∧ s2Mu5NormRes h2 hq g = 1) := by
  set β := 171 * (g.natDegree / 16) with hβdef
  have hex := s2Mu5KeyPoly_exactGrade h2 hq hkey
  rcases Nat.eq_zero_or_pos (s2Mu5GradedRes h2 hq β g).natTrailingDegree with h0 | hpos
  · exact Or.inl h0
  · right
    have h16 := s2Mu5KeyPoly_natDegree_sixteen_dvd h2 hq hkey
    have hpos_deg : 0 < g.natDegree := hkey.2.1.1
    -- coeff 0 vanishes ⇒ slot 0 off the gate ⇒ g ~ g16·(g /ₘ g16)
    have hc0 : (s2Mu5GradedRes h2 hq β g).coeff 0 = 0 :=
      Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hpos
    have hcoeff0 : s2Mu5Coeff h2 hq β g 0 = 0 := by
      rw [← s2Mu5GradedRes_coeff h2 hq β g 0]
      exact hc0
    have hgate : ¬ S2Mu5SlotOnGrade h2 hq β g 0 :=
      fun hgate => mu5Coeff_ne_zero_of_slot h2 hq hgate hcoeff0
    set Q := g /ₘ g16 h2 hq with hQdef
    have hequiv := mu5_equiv_keyMulDiv_of_not_slotZero h2 hq hex hgate
    have hQmon : Q.Monic := monic_divByMonic hkey.1 (g16_monic h2 hq)
      (by
        rw [Polynomial.degree_eq_natDegree (g16_monic h2 hq).ne_zero,
          Polynomial.degree_eq_natDegree hkey.1.ne_zero, g16_natDegree h2 hq]
        exact_mod_cast (by omega : 16 ≤ g.natDegree))
    have hQdeg : Q.natDegree = g.natDegree - 16 := by
      rw [hQdef, Polynomial.natDegree_divByMonic _ (g16_monic h2 hq),
        g16_natDegree h2 hq]
    -- self-divisibility transported, then primality splits
    have hprod : S2Mu5Dvd h2 hq g ((g16 h2 hq : Polynomial O) * Q) :=
      ⟨1, by rw [mul_one]; exact S2Mu5InitialEquiv_symm h2 hq hequiv⟩
    rcases hkey.2.2.2.2 _ _ hprod with hL | hR
    · -- `g ∣μ₅ g16`: grade pins `deg g = 16`; residual-dvd pins `R(g) = 1`
      obtain ⟨p, hp⟩ := hL
      have hp0 : p ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hp
        exact (g16_monic h2 hq).ne_zero ((S2Mu5InitialEquiv_zero_right h2 hq).mp hp)
      obtain ⟨δ, hδ⟩ := S2Mu5ExactGrade_exists h2 hq hp0
      have hgp : S2Mu5ExactGrade h2 hq (β + δ) (g * p) :=
        S2Mu5ExactGrade_mul h2 hq hex hδ
      have hg16grade : S2Mu5ExactGrade h2 hq (β + δ) (g16 h2 hq : Polynomial O) :=
        S2Mu5ExactGrade_of_initialEquiv h2 hq hgp (S2Mu5InitialEquiv_symm h2 hq hp)
      have h171 : (171 : ℕ) = β + δ :=
        S2Mu5ExactGrade_unique h2 hq (tooth_g16 h2 hq) hg16grade
      have hdeg16 : g.natDegree = 16 := by
        rw [hβdef] at h171
        omega
      have hdvdres := mu5NormRes_dvd_of_S2Mu5Dvd h2 hq ⟨p, hp⟩
      rw [s2Mu5NormRes_g16 h2 hq] at hdvdres
      have hunit : IsUnit (s2Mu5NormRes h2 hq g) := isUnit_of_dvd_one hdvdres
      have hNdeg : (s2Mu5NormRes h2 hq g).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit hunit
      have hNC : s2Mu5NormRes h2 hq g
          = Polynomial.C ((s2Mu5NormRes h2 hq g).coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hNdeg
      have hc0N : (s2Mu5NormRes h2 hq g).coeff 0 ≠ 0 :=
        s2Mu5NormRes_coeff_zero_ne_zero h2 hq hkey.1.ne_zero
      refine ⟨hdeg16, ?_⟩
      rw [hNC, C132rp1.s2Fld₂_eq_one_of_ne_zero h2 hq hc0N, Polynomial.C_1]
    · -- `g ∣μ₅ Q` refutes minimality
      exfalso
      have hQlt : Q.natDegree < g.natDegree := by omega
      exact hkey.2.1.2 Q hQmon.ne_zero hQlt hR

/-! ## D4-16 Part 6 — ★★ the converse and the assembled Prop-5.6 field -/

/-- ★★ **D4-16, the converse** (published Prop 5.6's (2)→(3), the hard direction, at the
μ₅ operators; mirror of `C136d3.s2Mu4_residual_to_initial` one level up, from the
digit-ledger-free bank): residual equality forces initial equivalence for μ₅ key
polynomials.  The trailing dichotomy pins equal strips; the ledger pins equal degrees,
hence equal grades `171·(deg/16)`; the graded-piece IFF fires backward. -/
theorem s2Mu5_residual_to_initial {g h : Polynomial O} (hkg : S2Mu5KeyPoly h2 hq g)
    (hkh : S2Mu5KeyPoly h2 hq h) (hres : s2Mu5NormRes h2 hq g = s2Mu5NormRes h2 hq h) :
    S2Mu5InitialEquiv h2 hq g h := by
  have hexg := s2Mu5KeyPoly_exactGrade h2 hq hkg
  have hexh := s2Mu5KeyPoly_exactGrade h2 hq hkh
  have hledg := key_ntd_add_normRes_natDegree h2 hq hkg
  have hledh := key_ntd_add_normRes_natDegree h2 hq hkh
  have h16g := s2Mu5KeyPoly_natDegree_sixteen_dvd h2 hq hkg
  have h16h := s2Mu5KeyPoly_natDegree_sixteen_dvd h2 hq hkh
  have hposg : 0 < g.natDegree := hkg.2.1.1
  have hposh : 0 < h.natDegree := hkh.2.1.1
  have hntd_eq : (s2Mu5GradedRes h2 hq (171 * (g.natDegree / 16)) g).natTrailingDegree
      = (s2Mu5GradedRes h2 hq (171 * (h.natDegree / 16)) h).natTrailingDegree := by
    rcases key_trailing_dichotomy h2 hq hkg with hg0 | ⟨hgd, hgN⟩ <;>
      rcases key_trailing_dichotomy h2 hq hkh with hh0 | ⟨hhd, hhN⟩
    · rw [hg0, hh0]
    · exfalso
      rw [hg0, hres, hhN, Polynomial.natDegree_one] at hledg
      omega
    · exfalso
      rw [hh0, ← hres, hgN, Polynomial.natDegree_one] at hledh
      omega
    · have hg1 : (s2Mu5GradedRes h2 hq
          (171 * (g.natDegree / 16)) g).natTrailingDegree = 1 := by
        rw [hgN, Polynomial.natDegree_one] at hledg
        omega
      have hh1 : (s2Mu5GradedRes h2 hq
          (171 * (h.natDegree / 16)) h).natTrailingDegree = 1 := by
        rw [hhN, Polynomial.natDegree_one] at hledh
        omega
      rw [hg1, hh1]
  have hdeg_eq : g.natDegree = h.natDegree := by
    rw [hres] at hledg
    omega
  have hexh' : S2Mu5ExactGrade h2 hq (171 * (g.natDegree / 16)) h := by
    rw [hdeg_eq]
    exact hexh
  refine (mu5_initialEquiv_iff_gradedRes h2 hq hexg hexh').mpr ?_
  calc s2Mu5GradedRes h2 hq (171 * (g.natDegree / 16)) g
      = s2Mu5NormRes h2 hq g * Polynomial.X
          ^ (s2Mu5GradedRes h2 hq (171 * (g.natDegree / 16)) g).natTrailingDegree :=
        (s2Mu5NormRes_mul_X_pow_of_exact h2 hq hexg).symm
    _ = s2Mu5NormRes h2 hq h * Polynomial.X
          ^ (s2Mu5GradedRes h2 hq (171 * (h.natDegree / 16)) h).natTrailingDegree := by
        rw [hres, hntd_eq]
    _ = s2Mu5GradedRes h2 hq (171 * (h.natDegree / 16)) h :=
        s2Mu5NormRes_mul_X_pow_of_exact h2 hq hexh
    _ = s2Mu5GradedRes h2 hq (171 * (g.natDegree / 16)) h := by
        rw [hdeg_eq]

/-- ★★ **D4-16 — the assembled Proposition-5.6 field at μ₅** (both directions; forward
is D4-13's universal `s2Mu5NormRes_eq_of_initialEquiv`). -/
theorem s2Mu5_initial_iff_residual :
    ∀ g h : Polynomial O, S2Mu5KeyPoly h2 hq g → S2Mu5KeyPoly h2 hq h →
      (S2Mu5InitialEquiv h2 hq g h ↔ s2Mu5NormRes h2 hq g = s2Mu5NormRes h2 hq h) :=
  fun _ _ hkg hkh =>
    ⟨s2Mu5NormRes_eq_of_initialEquiv h2 hq, s2Mu5_residual_to_initial h2 hq hkg hkh⟩

/-- **D4-16's concrete tangent fact**: the leaf and the carried key are NOT
μ₅-initial-equivalent (their residuals `X + 1` and `1` differ) — the two μ₅ key fibers
are genuinely distinct. -/
theorem not_S2Mu5InitialEquiv_leaf_g16 :
    ¬ S2Mu5InitialEquiv h2 hq (s2Mu5Leaf h2 hq) (g16 h2 hq : Polynomial O) := by
  intro hequiv
  have hres := s2Mu5NormRes_eq_of_initialEquiv h2 hq hequiv
  rw [s2Mu5NormRes_leaf h2 hq, s2Mu5NormRes_g16 h2 hq] at hres
  have hdeg := congrArg Polynomial.natDegree hres
  rw [Polynomial.natDegree_one, ← Polynomial.C_1, Polynomial.natDegree_X_add_C] at hdeg
  exact one_ne_zero hdeg

/-! ## D4-17 Part 0 — the `normalized_exists` witness (mirror of `C136d2.s2Mu4_hex`) -/

/-- ★ **the μ₅ `normalized_exists` field** at `(e', f', u') = (1, 1, 171)`: every
admissible monic irreducible degree-one residual collapses to `X + 1` over the 2-element
stage field (`C132rp10.s2Mu3_unique_admissible_linear` — field-generic, no
level-dependence), and D4-12's landed leaf realizes it. -/
theorem s2Mu5_hex :
    ∀ ψ : Polynomial ((s2DepthTwo h2 hq).fld 2),
      ψ.Monic → Irreducible ψ → ψ.natDegree = 1 → ψ.coeff 0 ≠ 0 →
        ∃ g : Polynomial O, g.Monic ∧
          g.natDegree = 1 * 1 * (((s2DepthFourKeyChain h2 hq).keyAt 4).natDegree) ∧
          s2Mu5NormRes h2 hq g = ψ := by
  intro ψ hm _ hd hc
  have hψ : ψ = Polynomial.X + 1 :=
    C132rp10.s2Mu3_unique_admissible_linear h2 hq ψ hm hd hc
  refine ⟨s2Mu5Leaf h2 hq, s2Mu5Leaf_monic h2 hq, ?_, ?_⟩
  · rw [s2DepthFourKeyChain_keyAt_four, g16_natDegree h2 hq,
      show (1 : ℕ) * 1 * 16 = 16 from by norm_num]
    exact s2Mu5Leaf_natDegree h2 hq
  · rw [hψ]
    exact s2Mu5NormRes_leaf h2 hq

/-! ## D4-17 Part 1 — the `normalized_recipe` field in the μ₅-graded display

GENUINELY NON-VACUOUS, unlike the μ₄ mirror (`C136d3.s2Mu4_normalized_recipe`, discharged
by parity vacuity): at `e' = 1` every grade is realizable (`S2Mu5PrevGrade_all`), the
premise fires (e.g. at `khat 0 := Λ`), and the display is D4-11's landed exact-evaluation
computation.  D4-11's landed statement reads the scalar slot through the INNER μ₄ graded
operator; the `FGMNSourceLaws` field reads it through the μ₅ one — both scalar reads are
the unit `1` of the 2-element field, so the displays agree. -/

/-- the literal `FGMNSourceLaws.normalized_recipe` field shape at `(1, 1, 171)`, with the
scalar slot read through `s2Mu5GradedRes`. -/
theorem s2Mu5_normalized_recipe_field (khat : ℕ → Polynomial O)
    (hkhat : ∀ t, t < 1 → S2Mu5ExactGrade h2 hq ((1 - t) * 171) (khat t))
    (hdeg : ∀ t, t < 1 → (khat t).natDegree <
      ((s2DepthFourKeyChain h2 hq).keyAt 4 : Polynomial O).natDegree) :
    s2Mu5NormRes h2 hq
        (((s2DepthFourKeyChain h2 hq).keyAt 4 : Polynomial O) ^ (1 * 1) -
          ∑ t ∈ Finset.range 1,
            khat t * ((s2DepthFourKeyChain h2 hq).keyAt 4 : Polynomial O) ^ (1 * t)) =
      Polynomial.X ^ 1 -
        ∑ t ∈ Finset.range 1,
          Polynomial.C ((s2Mu5GradedRes h2 hq ((1 - t) * 171) (khat t)).coeff 0) *
            Polynomial.X ^ t := by
  have hμ4 := s2Mu5_normalized_recipe h2 hq khat hkhat hdeg
  rw [hμ4]
  have hk0grade : S2Mu5ExactGrade h2 hq 171 (khat 0) := by
    have h := hkhat 0 (by omega)
    simpa using h
  have hk0deg : (khat 0).natDegree < 16 := by
    have h := hdeg 0 (by omega)
    rwa [s2DepthFourKeyChain_keyAt_four, g16_natDegree h2 hq] at h
  have hΛ'mu4 : S2Mu4ExactGrade h2 hq 171 (khat 0) :=
    s2Mu4ExactGrade_of_s2Mu5ExactGrade_natDegree_lt h2 hq hk0grade hk0deg
  have hcollapse4 := s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen h2 hq hk0deg 171
  have hne4 : s2Mu4GradedRes h2 hq 171 (khat 0) ≠ 0 :=
    s2Mu4GradedRes_ne_zero_of_exact h2 hq hΛ'mu4
  have hc4 : (s2Mu4GradedRes h2 hq 171 (khat 0)).coeff 0 ≠ 0 :=
    fun h0 => hne4 (by rw [hcollapse4, h0, Polynomial.C_0])
  have hc5 : (s2Mu5GradedRes h2 hq 171 (khat 0)).coeff 0 ≠ 0 :=
    s2Mu5GradedRes_coeff_zero_ne_zero_of_exact h2 hq hk0grade hk0deg
  simp only [Finset.sum_range_one, Nat.sub_zero, one_mul, pow_zero, mul_one]
  rw [C132rp1.s2Fld₂_eq_one_of_ne_zero h2 hq hc4,
    C132rp1.s2Fld₂_eq_one_of_ne_zero h2 hq hc5]

/-! ## D4-17 Part 2 — the `graded_scalar_nonzero` field shape and the carried-key pins -/

/-- the `FGMNSourceLaws.graded_scalar_nonzero` field, exact shape at `r = 4` (thin
wrapper over D4-08's landed scalar law, mirroring `C136d2.s2Mu4_graded_scalar_nonzero`). -/
theorem s2Mu5_graded_scalar_nonzero :
    ∀ β (g : Polynomial O),
      S2Mu5ExactGrade h2 hq β g →
      g.natDegree < ((s2DepthFourKeyChain h2 hq).keyAt 4).natDegree →
      g ≠ 0 →
      (s2Mu5GradedRes h2 hq β g).coeff 0 ≠ 0 := by
  intro β g hg hdeg _
  rw [s2DepthFourKeyChain_keyAt_four, g16_natDegree h2 hq] at hdeg
  exact s2Mu5GradedRes_coeff_zero_ne_zero_of_exact h2 hq hg hdeg

/-- the carried key theorem, read at the chain slot `keyAt 4`. -/
theorem S2Mu5KeyPoly_keyAt_four :
    S2Mu5KeyPoly h2 hq ((s2DepthFourKeyChain h2 hq).keyAt 4) := by
  rw [s2DepthFourKeyChain_keyAt_four]
  exact S2Mu5KeyPoly_g16 h2 hq

/-- the carried key's residual, read at the chain slot `keyAt 4`. -/
theorem s2Mu5NormRes_keyAt_four :
    s2Mu5NormRes h2 hq ((s2DepthFourKeyChain h2 hq).keyAt 4) = 1 := by
  rw [s2DepthFourKeyChain_keyAt_four]
  exact s2Mu5NormRes_g16 h2 hq

/-! ## D4-17 Part 3 — the depth-four letter (mirror of `C136d3.s2LetterThree`) -/

/-- **the `FGMNSourceData.letter` field at depth four**: the constant `1` — the unique
nonzero value of the 2-element residue tower field; junk (never read by
`letter_ne_zero`) off the live range `1 ≤ i ≤ 4`. -/
noncomputable def s2LetterFour : ℕ → (s2DepthTwo h2 hq).fld 2 := fun _ => 1

/-- the `letter_ne_zero` field, exact shape at `r = 4`. -/
theorem s2LetterFour_ne_zero : ∀ i, 1 ≤ i → i ≤ 4 → s2LetterFour h2 hq i ≠ 0 :=
  fun _ _ _ => one_ne_zero

/-! ## D4-17 Part 4 — ★★ the source records (mirror of `C136d3` D3-18 Part 2) -/

set_option maxHeartbeats 1600000 in
/-- ★★ **D4-17, the DATA record**: the seven landed μ₅ operators at the depth-four
refinement triple `(1, 1, 171)`, over the landed depth-four chain `Φ′/Φ₂/g₈/g16`. -/
noncomputable def s2SourceDataFour :
    FGMNSourceData (s2DepthFour h2 hq) (s2DepthFourKeyChain h2 hq) 1 1 171 where
  nextValue := s2Hgt₅ h2 hq
  gradedResidual := s2Mu5GradedRes h2 hq
  normalizedResidual := s2Mu5NormRes h2 hq
  PrevGrade := S2Mu5PrevGrade
  keyPolynomial := S2Mu5KeyPoly h2 hq
  initialEquiv := S2Mu5InitialEquiv h2 hq
  letter := s2LetterFour h2 hq

/-- read pin: `nextValue` is the μ₅ table `s2Hgt₅`. -/
theorem s2SourceDataFour_nextValue :
    (s2SourceDataFour h2 hq).nextValue = s2Hgt₅ h2 hq := rfl

/-- read pin: `gradedResidual` is `s2Mu5GradedRes`. -/
theorem s2SourceDataFour_gradedResidual :
    (s2SourceDataFour h2 hq).gradedResidual = s2Mu5GradedRes h2 hq := rfl

/-- read pin: `normalizedResidual` is `s2Mu5NormRes`. -/
theorem s2SourceDataFour_normalizedResidual :
    (s2SourceDataFour h2 hq).normalizedResidual = s2Mu5NormRes h2 hq := rfl

/-- read pin: `PrevGrade` is the ALL-grades predicate `S2Mu5PrevGrade`. -/
theorem s2SourceDataFour_PrevGrade :
    (s2SourceDataFour h2 hq).PrevGrade = S2Mu5PrevGrade := rfl

/-- read pin: `keyPolynomial` is `S2Mu5KeyPoly`. -/
theorem s2SourceDataFour_keyPolynomial :
    (s2SourceDataFour h2 hq).keyPolynomial = S2Mu5KeyPoly h2 hq := rfl

/-- read pin: `initialEquiv` is `S2Mu5InitialEquiv`. -/
theorem s2SourceDataFour_initialEquiv :
    (s2SourceDataFour h2 hq).initialEquiv = S2Mu5InitialEquiv h2 hq := rfl

/-- read pin: `letter` is the forced constant-`1` `s2LetterFour`. -/
theorem s2SourceDataFour_letter :
    (s2SourceDataFour h2 hq).letter = s2LetterFour h2 hq := rfl

set_option maxHeartbeats 1600000 in
/-- ★★ **D4-17, the LAWS record — UNCONDITIONAL** (mirror of
`C136d3.s2SourceLawsThree`, one level up; all thirteen projections are discharged by
named landed theorems).  Unlike every `e' = 2` predecessor, the `normalized_recipe`
field here is GENUINELY NON-VACUOUS (D4-11's exact-evaluation computation, premise
realizable at `khat 0 := Λ`), and `normalized_exists` is realized by the landed leaf. -/
theorem s2SourceLawsFour :
    FGMNSourceLaws (s2DepthFour h2 hq) (s2DepthFourKeyChain h2 hq) 1 1 171
      (s2SourceDataFour h2 hq) where
  graded_zero_of_above := fun _ _ h => s2Mu5GradedRes_zero_of_above h2 hq h
  graded_add := fun _ _ _ hg hh hgh => s2Mu5GradedRes_add h2 hq hg hh hgh
  graded_mul := fun β β' g h hg hh _ => s2Mu5_graded_mul h2 hq β β' g h hg hh
  graded_scalar_nonzero := s2Mu5_graded_scalar_nonzero h2 hq
  normalized_mul := fun g h => s2Mu5NormRes_mul h2 hq g h
  normalized_recipe := fun khat hgr hdeg =>
    s2Mu5_normalized_recipe_field h2 hq khat hgr hdeg
  normalized_exists := fun _ ψ hm hirr hd hc => s2Mu5_hex h2 hq ψ hm hirr hd hc
  key_criterion := s2Mu5_key_criterion h2 hq
  key_irreducible := fun _ hkp _ => s2Mu5_key_irreducible h2 hq hkp
  carried_key_is_key := fun _ => S2Mu5KeyPoly_keyAt_four h2 hq
  carried_key_residual := fun _ => s2Mu5NormRes_keyAt_four h2 hq
  initial_iff_residual := fun g h hg hh => s2Mu5_initial_iff_residual h2 hq g h hg hh
  letter_ne_zero := fun i h1 hr => s2LetterFour_ne_zero h2 hq i h1 hr

/-! ## D4-18 — ★★★ THE μ₅ CALCULUS -/

set_option maxHeartbeats 1600000 in
/-- ★★★ **D4-18 — THE UNCONDITIONAL μ₅ (REFINEMENT) CALCULUS at `(1, 1, 171)`**: the
packaging theorem `C130pk.fgmn_model_calculus_nonempty` fired at the D4-17 records —
the deep-witness campaign's key-tail closer over the landed depth-four tower.
Lean-core footprint; no hypothesis remains.  (No depth-five `keyAt`/`KeyChain` is built
— the `(1,1,171)` triple is OPERATOR data over `s2DepthFour`, per the [G5F] record.) -/
theorem s2Mu5_calculus_nonempty :
    Nonempty (FGMNCalculus (s2DepthFour h2 hq) 1 1 171) :=
  fgmn_model_calculus_nonempty (s2DepthFourKeyChain h2 hq) (s2SourceDataFour h2 hq)
    (s2SourceLawsFour h2 hq)

/-! ## D4-15 addendum ([DWR] §11.1, optional) — the `h := keyAt4 + 1` coprimality legs

The blueprint's [DWR] revision flags `h := g16 + 1` as the real downstream input
candidate.  The four legs: monic degree 16; Bézout-coprime with `g16` over `O[x]`
itself; `g16` and the leaf coprime (Part 4 above); the leaf and `h` coprime in `K[x]`
(a monic same-degree divisibility collapse plus `deg Λ = 15 ≠ 0`). -/

/-- [DWR] leg: `g16 + 1` is monic. -/
theorem s2_g16_add_one_monic : ((g16 h2 hq : Polynomial O) + 1).Monic :=
  (g16_monic h2 hq).add_of_left
    (Polynomial.degree_lt_degree
      (by rw [Polynomial.natDegree_one, g16_natDegree h2 hq]; omega))

/-- [DWR] leg: `g16 + 1` has degree 16. -/
theorem s2_g16_add_one_natDegree : ((g16 h2 hq : Polynomial O) + 1).natDegree = 16 := by
  rw [← Polynomial.C_1, Polynomial.natDegree_add_C, g16_natDegree h2 hq]

/-- [DWR] leg: `g16 + 1` and `g16` are coprime over `O[x]` itself — the literal Bézout
witness `1·(g16 + 1) + (−1)·g16 = 1` (no fraction field needed). -/
theorem s2_g16_add_one_coprime_g16 :
    IsCoprime ((g16 h2 hq : Polynomial O) + 1) (g16 h2 hq : Polynomial O) :=
  ⟨1, -1, by ring⟩

/-- [DWR] leg: the leaf and `g16 + 1` are coprime in `K[x]`: a common divisor would make
the two monic degree-16 polynomials EQUAL (the leaf's image is irreducible), forcing
`Λ = −1` against `deg Λ = 15`. -/
theorem s2Mu5_leaf_g16_add_one_coprime_fractionMap {K : Type*} [Field K] [Algebra O K]
    [IsFractionRing O K] :
    IsCoprime ((s2Mu5Leaf h2 hq).map (algebraMap O K))
      (((g16 h2 hq : Polynomial O) + 1).map (algebraMap O K)) := by
  refine ((s2Mu5Leaf_map_irreducible h2 hq).coprime_iff_not_dvd).mpr ?_
  intro hdvd
  have hhmon : ((((g16 h2 hq : Polynomial O) + 1)).map (algebraMap O K)).Monic :=
    (s2_g16_add_one_monic h2 hq).map _
  have hlmon : ((s2Mu5Leaf h2 hq).map (algebraMap O K)).Monic :=
    (s2Mu5Leaf_monic h2 hq).map _
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact hhmon.ne_zero hc
  have hcdeg : c.natDegree = 0 := by
    have hdegs := congrArg Polynomial.natDegree hc
    rw [Polynomial.natDegree_mul hlmon.ne_zero hc0,
      (s2Mu5Leaf_monic h2 hq).natDegree_map, s2Mu5Leaf_natDegree h2 hq,
      (s2_g16_add_one_monic h2 hq).natDegree_map, s2_g16_add_one_natDegree h2 hq]
      at hdegs
    omega
  have hcC : c = Polynomial.C (c.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hcdeg
  have hlc : c.leadingCoeff = 1 := by
    have hlead := congrArg Polynomial.leadingCoeff hc
    rw [Polynomial.leadingCoeff_mul, hlmon.leadingCoeff, hhmon.leadingCoeff,
      one_mul] at hlead
    exact hlead.symm
  have hc1 : c = 1 := by
    rw [hcC] at hlc ⊢
    rw [Polynomial.leadingCoeff_C] at hlc
    rw [hlc, Polynomial.C_1]
  rw [hc1, mul_one] at hc
  have heqO : (g16 h2 hq : Polynomial O) + 1 = s2Mu5Leaf h2 hq :=
    Polynomial.map_injective (algebraMap O K) (IsFractionRing.injective O K) hc
  have hLeaf : s2Mu5Leaf h2 hq = (g16 h2 hq : Polynomial O) - s2Mu5Lambda h2 hq := by
    rw [s2Mu5Leaf_eq_keyAt_sub h2 hq, s2DepthFourKeyChain_keyAt_four]
  rw [hLeaf] at heqO
  have hΛ : s2Mu5Lambda h2 hq = -1 := by linear_combination heqO
  have hdeg15 := s2Mu5Lambda_natDegree h2 hq
  rw [hΛ, Polynomial.natDegree_neg, Polynomial.natDegree_one] at hdeg15
  omega

end S2

end Uniformity.Density.Tower.C136e2

/-! ## Axiom footprint -/

section AxCheck

-- D4-13: the predicates and the residual-divisibility equivalence
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5InitialEquiv
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5Dvd
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5Minimal
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5Irreducible
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5KeyPoly
#print axioms Uniformity.Density.Tower.C136e2.s2Hgt₅_neg
#print axioms Uniformity.Density.Tower.C136e2.s2Hgt₅_eq_top_iff
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5InitialEquiv_equivalence
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5InitialEquiv_hgt_eq
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5InitialEquiv_zero_left
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5InitialEquiv_zero_right
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5ExactGrade_of_initialEquiv
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5GradeOf_eq_of_initialEquiv
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5Dvd_of_dvd
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5Dvd_self
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5Dvd_zero
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5Dvd_congr_right
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5NormRes_eq_of_initialEquiv
#print axioms Uniformity.Density.Tower.C136e2.mu5NormRes_dvd_of_S2Mu5Dvd
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5GradedRes_eq_C_of_natDegree_lt_sixteen
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5NormRes_isUnit_of_natDegree_lt_sixteen
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5Dvd_of_mu5NormRes_dvd
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5Dvd_iff_mu5NormRes_dvd
-- D4-14: criterion, the leaf key, and the carried key
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5Irreducible_of_irreducible_normRes
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5Minimal_of_not_isUnit_normRes
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5Minimal_of_irreducible_normRes
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5_key_criterion
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5KeyPoly_leaf
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5KeyPoly_g16
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5NormRes_g16
#print axioms Uniformity.Density.Tower.C136e2.tooth_g16_mu5_vs_mu4
-- D4-15: irreducibility over `O`, distinctness, and fraction-map coprimality
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5_key_irreducible
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5Leaf_irreducible
#print axioms Uniformity.Density.Tower.C136e2.s2_g16_irreducible
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5Leaf_ne_g16
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5Leaf_map_irreducible
#print axioms Uniformity.Density.Tower.C136e2.s2_g16_map_irreducible
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5_leaf_keyAt4_coprime_fractionMap
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5_leafSq_keyAt4_coprime_fractionMap
-- D4-15 addendum ([DWR] §11.1): the `g16 + 1` legs
#print axioms Uniformity.Density.Tower.C136e2.s2_g16_add_one_monic
#print axioms Uniformity.Density.Tower.C136e2.s2_g16_add_one_natDegree
#print axioms Uniformity.Density.Tower.C136e2.s2_g16_add_one_coprime_g16
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5_leaf_g16_add_one_coprime_fractionMap
-- D4-16: the key-structure bank and the converse
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5Minimal_natDegree_sixteen_dvd
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5Minimal_exactGrade
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5KeyPoly_natDegree_sixteen_dvd
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5KeyPoly_exactGrade
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5KeyPoly_gradedRes_natDegree
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5_residual_to_initial
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5_initial_iff_residual
#print axioms Uniformity.Density.Tower.C136e2.not_S2Mu5InitialEquiv_leaf_g16
-- D4-17: the hex/recipe/scalar fields, the letter, and the source records
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5_hex
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5_normalized_recipe_field
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5_graded_scalar_nonzero
#print axioms Uniformity.Density.Tower.C136e2.S2Mu5KeyPoly_keyAt_four
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5NormRes_keyAt_four
#print axioms Uniformity.Density.Tower.C136e2.s2LetterFour
#print axioms Uniformity.Density.Tower.C136e2.s2LetterFour_ne_zero
#print axioms Uniformity.Density.Tower.C136e2.s2SourceDataFour
#print axioms Uniformity.Density.Tower.C136e2.s2SourceDataFour_nextValue
#print axioms Uniformity.Density.Tower.C136e2.s2SourceDataFour_gradedResidual
#print axioms Uniformity.Density.Tower.C136e2.s2SourceDataFour_normalizedResidual
#print axioms Uniformity.Density.Tower.C136e2.s2SourceDataFour_PrevGrade
#print axioms Uniformity.Density.Tower.C136e2.s2SourceDataFour_keyPolynomial
#print axioms Uniformity.Density.Tower.C136e2.s2SourceDataFour_initialEquiv
#print axioms Uniformity.Density.Tower.C136e2.s2SourceDataFour_letter
#print axioms Uniformity.Density.Tower.C136e2.s2SourceLawsFour
-- D4-18: ★★★ the μ₅ calculus
#print axioms Uniformity.Density.Tower.C136e2.s2Mu5_calculus_nonempty

end AxCheck
