/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.MovesGr.L0_pmul_mk
import LeanUrat.MovesGr.L0_initialForm_zero
import LeanUrat.MovesGr.L0_initialForm_ne_zero
import LeanUrat.MovesGr.L0_deg_add

/-!
# HC1.T6_carrierLaws — the real carrier satisfies the four GradedCarrier laws

moves_ref: MOVES 3799–3801 ("the class map is additive and kills weight > δ′ —
D.1") + D.1(b). deps: DefsCar; MovesGr `L0_pmul_mk`, `L0_initialForm_*`,
`L0_deg_add` (proved). First leg: `HasSide` (the side-valuation bundle exists —
the constant-weight nonnegativity rides the spine induction). Second leg: the four
laws through the ⌊strTop·γ⌋ reindexing (C-1 re-thread); off-lattice clauses vacuous
by D3's convention. difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesGr

open scoped Classical

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## Arithmetic helpers for the ⌊strTop·γ⌋ reindexing -/

/-- The frame stretch `strTop = e₀·…·e_K` is a positive natural (each `e ≥ 1`). -/
private lemma strTop_pos (T : Tower p F) : 0 < T.strTop := by
  have haux : ∀ n : ℕ, 0 < T.strAux n := by
    intro n
    induction n with
    | zero => norm_num [Tower.strAux]
    | succ k ih =>
      rw [Tower.strAux]
      apply Nat.mul_pos ih
      split
      · exact (T.stg _).he
      · exact Nat.one_pos
  rw [Tower.strTop, Tower.str]
  exact Nat.mul_pos (haux _) (T.stg (Fin.last T.K)).he

/-- Dividing by a positive rational is strictly monotone; lifted to `WithTop`. -/
private lemma map_div_strictMono (S : ℚ) (hS : 0 < S) :
    StrictMono (WithTop.map (fun n : ℤ => (n : ℚ) / S)) := by
  have hg : StrictMono (fun n : ℤ => (n : ℚ) / S) := by
    intro a b hab
    simp only
    have : (a : ℚ) < (b : ℚ) := by exact_mod_cast hab
    gcongr
  intro x y hxy
  cases x with
  | top => exact absurd hxy (by simp)
  | coe a =>
    cases y with
    | top => simp [WithTop.map_coe, WithTop.map_top]
    | coe b =>
      rw [WithTop.map_coe, WithTop.map_coe]
      exact WithTop.coe_lt_coe.mpr (hg (WithTop.coe_lt_coe.mp hxy))

/-- On the lattice, the coerced weight `γ` is the divided image of the floor `⌊strTop·γ⌋`. -/
private lemma coe_gamma_eq (T : Tower p F) {γ : ℚ} (honL : T.onLattice γ) :
    (↑γ : WithTop ℚ)
      = WithTop.map (fun n : ℤ => (n : ℚ) / (T.strTop : ℚ))
          (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) := by
  have hSne : (T.strTop : ℚ) ≠ 0 := ne_of_gt (by exact_mod_cast strTop_pos T)
  have hoL : (↑(⌊(T.strTop : ℚ) * γ⌋) : ℚ) = (T.strTop : ℚ) * γ := honL
  have hfa : (↑(⌊(T.strTop : ℚ) * γ⌋) : ℚ) / (T.strTop : ℚ) = γ := by
    rw [hoL]; field_simp
  rw [WithTop.map_coe, hfa]

/-- On the lattice, `γ ≤ wQ f` iff `⌊strTop·γ⌋ ≤ side.w f`. -/
private lemma wQ_ge_iff (T : Tower p F) {γ : ℚ} (honL : T.onLattice γ) (f : Polynomial ℤ_[p]) :
    (↑γ : WithTop ℚ) ≤ T.wQ f
      ↔ (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w f := by
  have hSpos : (0 : ℚ) < (T.strTop : ℚ) := by exact_mod_cast strTop_pos T
  rw [coe_gamma_eq T honL]
  simp only [Tower.wQ]
  exact (map_div_strictMono (T.strTop : ℚ) hSpos).le_iff_le

/-- On the lattice, `γ < wQ f` iff `⌊strTop·γ⌋ < side.w f`. -/
private lemma wQ_gt_iff (T : Tower p F) {γ : ℚ} (honL : T.onLattice γ) (f : Polynomial ℤ_[p]) :
    (↑γ : WithTop ℚ) < T.wQ f
      ↔ (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) < T.side.w f := by
  have hSpos : (0 : ℚ) < (T.strTop : ℚ) := by exact_mod_cast strTop_pos T
  rw [coe_gamma_eq T honL]
  simp only [Tower.wQ]
  exact (map_div_strictMono (T.strTop : ℚ) hSpos).lt_iff_lt

/-- Off the lattice, `inGr γ` is identically `0` (D3's recorded convention). -/
private lemma inGr_off (T : Tower p F) {γ : ℚ} (honL : ¬ T.onLattice γ)
    (f : Polynomial ℤ_[p]) : T.inGr γ f = 0 := by
  rw [Tower.inGr, dif_neg (fun h => honL h.1)]

/-- On the lattice and at or above weight `⌊strTop·γ⌋`, `inGr γ f` is the class `[f]`. -/
private lemma inGr_on (T : Tower p F) {γ : ℚ} (honL : T.onLattice γ) (f : Polynomial ℤ_[p])
    (hf : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w f) :
    T.inGr γ f = Submodule.Quotient.mk (⟨f, hf⟩ : T.side.ge (⌊(T.strTop : ℚ) * γ⌋)) := by
  rw [Tower.inGr, dif_pos ⟨honL, hf⟩]

/-- The class `[f]` in the degree-`m` piece vanishes iff `f` has strictly higher weight. -/
private lemma mk_eq_zero_iff (T : Tower p F) (m : ℤ) (f : Polynomial ℤ_[p])
    (hf : f ∈ T.side.ge m) :
    (Submodule.Quotient.mk (⟨f, hf⟩ : T.side.ge m) : T.side.grPiece m) = 0
      ↔ (↑m : WithTop ℤ) < T.side.w f := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/-! ## The spine induction: constant weights are nonnegative -/

/-- **Constant-weight nonnegativity** (the spine induction behind `SideVal.w_smul`):
every tower stage's valuation is `≥ 0` on nonzero constants.  Base: the Gauss
valuation of a `ℤ_[p]`-constant is `≥ 0`; increment: `w = e·w_prev` with `w_prev`
the parent's `w`; recentering: `w` is unchanged. -/
private lemma stage_wC_nonneg (T : Tower p F) (c : ℤ_[p]) (hc : c ≠ 0) :
    ∀ k : Fin (T.K + 1), 0 ≤ (T.stg k).w (Polynomial.C c) := by
  have hCcne : (Polynomial.C c) ≠ 0 := Polynomial.C_ne_zero.mpr hc
  have hinC : ∀ σ : Stage p F, inC σ.Φ (Polynomial.C c) := by
    intro σ
    have h1 : (Polynomial.C c).degree ≤ 0 := Polynomial.degree_C_le
    have h2 : (0 : WithBot ℕ) < σ.Φ.degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp (by have := σ.hdeg; omega)
    exact lt_of_le_of_lt h1 h2
  intro k
  induction k using Fin.induction with
  | zero =>
    rw [(T.stg 0).hStretch (Polynomial.C c) hCcne (hinC _),
        T.base.1.1 (Polynomial.C c) hCcne]
    apply mul_nonneg (Nat.cast_nonneg _)
    simp only [gaussVal]
    rw [dif_pos (Polynomial.support_nonempty.mpr hCcne)]
    apply Finset.le_inf'
    intro i _
    positivity
  | succ i ih =>
    rcases T.move i with ⟨ψ, g, Φhat, e', h', zbar, hyp, core⟩ | ⟨cc, tt, core⟩
    · rw [(T.stg i.succ).hStretch (Polynomial.C c) hCcne (hinC _),
          core.base.child_wPrev (Polynomial.C c)]
      exact mul_nonneg (Nat.cast_nonneg _) ih
    · obtain ⟨_, _, _, _, _, _, _, _, hweq, _⟩ := core.base
      rw [hweq (Polynomial.C c)]
      exact ih

/-! ## Leg 1: the side-valuation bundle exists -/

/-- **`HasSide`**: extend the top stage's valuation `σ.w` by `0 ↦ ⊤`; the ultrametric,
submultiplicative and unit laws come from the stage's `hwmul`/`hwult`, and the
scalar law `w_smul` from `stage_wC_nonneg`. -/
private lemma hasSide (T : Tower p F) : T.HasSide := by
  have hw1 : (T.topStage).w 1 = 0 := by
    have h := (T.topStage).hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    omega
  have hCn1 : (Polynomial.C (-1 : ℤ_[p])) ≠ 0 := by
    rw [Polynomial.C_ne_zero]; norm_num
  have hw_neg1 : (T.topStage).w (Polynomial.C (-1 : ℤ_[p])) = 0 := by
    have h := (T.topStage).hwmul (Polynomial.C (-1)) (Polynomial.C (-1)) hCn1 hCn1
    rw [← Polynomial.C_mul] at h
    have he : ((-1 : ℤ_[p]) * (-1)) = 1 := by ring
    rw [he, Polynomial.C_1, hw1] at h
    omega
  have hconst : ∀ c : ℤ_[p], c ≠ 0 → 0 ≤ (T.topStage).w (Polynomial.C c) :=
    fun c hc => stage_wC_nonneg T c hc (Fin.last T.K)
  refine ⟨{ w := fun f => if f = 0 then (⊤ : WithTop ℤ) else ((T.topStage).w f : WithTop ℤ)
            w_zero := if_pos rfl
            w_ne_top := by intro f hf; simp only [if_neg hf]; exact WithTop.coe_ne_top
            w_neg := by
              intro f
              by_cases hf : f = 0
              · subst hf; simp
              · have hnf : -f ≠ 0 := neg_ne_zero.mpr hf
                simp only [if_neg hf, if_neg hnf]
                congr 1
                have hcf : (Polynomial.C (-1 : ℤ_[p])) * f = -f := by
                  rw [Polynomial.C_neg, Polynomial.C_1, neg_one_mul]
                rw [← hcf, (T.topStage).hwmul (Polynomial.C (-1)) f hCn1 hf, hw_neg1, zero_add]
            w_add := by
              intro f g
              by_cases hf : f = 0
              · subst hf; rw [zero_add]; exact min_le_right _ _
              · by_cases hg : g = 0
                · subst hg; rw [add_zero]; exact min_le_left _ _
                · by_cases hfg : f + g = 0
                  · simp only [if_neg hf, if_neg hg, if_pos hfg]; exact le_top
                  · simp only [if_neg hf, if_neg hg, if_neg hfg]
                    rw [← WithTop.coe_min, WithTop.coe_le_coe]
                    exact (T.topStage).hwult f g hf hg hfg
            w_smul := by
              intro c f
              by_cases hcf : Polynomial.C c * f = 0
              · simp only [if_pos hcf]; exact le_top
              · have hc : Polynomial.C c ≠ 0 := left_ne_zero_of_mul hcf
                have hf : f ≠ 0 := right_ne_zero_of_mul hcf
                have hc0 : c ≠ 0 := Polynomial.C_ne_zero.mp hc
                simp only [if_neg hf, if_neg hcf]
                rw [(T.topStage).hwmul (Polynomial.C c) f hc hf, WithTop.coe_le_coe]
                have := hconst c hc0
                omega
            w_mul := by
              intro f g
              by_cases hf : f = 0
              · subst hf; simp
              · by_cases hg : g = 0
                · subst hg; simp
                · have hfg : f * g ≠ 0 := mul_ne_zero hf hg
                  simp only [if_neg hf, if_neg hg, if_neg hfg]
                  rw [(T.topStage).hwmul f g hf hg, ← WithTop.coe_add]
            w_one := by
              simp only [if_neg (one_ne_zero), hw1]; exact WithTop.coe_zero }, ?_⟩
  intro f hf
  simp only [if_neg hf]

/-! ## Leg 2: the four GradedCarrier laws -/

/-- **`CarrierLaws`**: `w_add` is the ultrametric pushed through the monotone
`⌊strTop··⌋⁻¹` reindexing; the three initial-form laws are quotient facts, vacuous
off the lattice. -/
private lemma carrierLaws (T : Tower p F) : T.CarrierLaws := by
  have hSpos : (0 : ℚ) < (T.strTop : ℚ) := by exact_mod_cast strTop_pos T
  have hmono : Monotone (WithTop.map (fun n : ℤ => (n : ℚ) / (T.strTop : ℚ))) :=
    (map_div_strictMono (T.strTop : ℚ) hSpos).monotone
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- w_add
    intro B B'
    simp only [Tower.wQ]
    rw [← Monotone.map_min hmono]
    exact hmono (T.side.w_add _ _)
  · -- inγ_add
    intro γ B B' hB hB'
    by_cases honL : T.onLattice γ
    · have hmB := (wQ_ge_iff T honL (↑B)).mp hB
      have hmB' := (wQ_ge_iff T honL (↑B')).mp hB'
      have hmadd : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ)
          ≤ T.side.w ((↑B : Polynomial ℤ_[p]) + ↑B') :=
        (T.side.ge _).add_mem hmB hmB'
      rw [inGr_on T honL _ hmadd, inGr_on T honL _ hmB, inGr_on T honL _ hmB']
      exact Submodule.Quotient.mk_add (T.side.gtIn (⌊(T.strTop : ℚ) * γ⌋))
        (x := ⟨(↑B : Polynomial ℤ_[p]), hmB⟩) (y := ⟨(↑B' : Polynomial ℤ_[p]), hmB'⟩)
    · rw [inGr_off T honL, inGr_off T honL, inGr_off T honL, add_zero]
  · -- inγ_kills
    intro γ B hlt
    by_cases honL : T.onLattice γ
    · have hm := (wQ_gt_iff T honL (↑B)).mp hlt
      rw [inGr_on T honL _ (le_of_lt hm)]
      exact (mk_eq_zero_iff T (⌊(T.strTop : ℚ) * γ⌋) (↑B) (le_of_lt hm)).mpr hm
    · exact inGr_off T honL _
  · -- inγ_detects
    intro γ B heq
    cases hw : T.side.w (↑B : Polynomial ℤ_[p]) with
    | top =>
      exfalso
      simp only [Tower.wQ, hw, WithTop.map_top] at heq
      exact (by simp : (⊤ : WithTop ℚ) ≠ ↑γ) heq
    | coe k =>
      simp only [Tower.wQ, hw, WithTop.map_coe] at heq
      have hSne : (T.strTop : ℚ) ≠ 0 := ne_of_gt hSpos
      have hkg : (k : ℚ) / (T.strTop : ℚ) = γ := by exact_mod_cast heq
      have hstg : (T.strTop : ℚ) * γ = (k : ℚ) := by rw [← hkg]; field_simp
      have hfloor : ⌊(T.strTop : ℚ) * γ⌋ = k := by rw [hstg]; exact Int.floor_intCast k
      have honL : T.onLattice γ := by
        show (↑(⌊(T.strTop : ℚ) * γ⌋) : ℚ) = (T.strTop : ℚ) * γ
        rw [hfloor, hstg]
      have hle : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w (↑B : Polynomial ℤ_[p]) := by
        rw [hfloor, hw]
      rw [inGr_on T honL _ hle]
      intro hzero
      have hlt : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) < T.side.w (↑B : Polynomial ℤ_[p]) :=
        (mk_eq_zero_iff T (⌊(T.strTop : ℚ) * γ⌋) (↑B) hle).mp hzero
      rw [hfloor, hw] at hlt
      exact absurd hlt (lt_irrefl _)

/-- Unit T6: the tower's side bundle exists and the concrete carrier data satisfy
the four GradedCarrier laws (`Tower.carrier` packages them). -/
theorem T6_carrierLaws {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) : T.HasSide ∧ T.CarrierLaws :=
  ⟨hasSide T, carrierLaws T⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T6_carrierLaws
