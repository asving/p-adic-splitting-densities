/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L4_TRANSiii_R3
import LeanUrat.Moves.L2_psiNotDvd_R3
import LeanUrat.Moves.L3_digPrime_nonzero
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L0_FactB_unique
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.ResVal

/-!
# HC1.S5_childValuation — D.7(iii): childW multiplicative, child value group ℤ

moves_ref: MOVES 2343–2352 (D.7(iii), incl. the F5 "nothing is renormalized"
clause: the un-rescaled form — coefficient weights e′·w(Ĉ) + h′ with
gcd(e′,h′) = 1). deps: S3, S4; Moves `L4_TRANSiii_R3`, `L2_psiNotDvd_R3`,
`L3_digPrime_nonzero` (clean). difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

section Helpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `childW` reads the attained slot-minimum on every development: it satisfies
`IsSlotMinWeight`. The well-definedness (the choice-existence predicate) is settled
per nonzero `f` by Fact A (a development exists) + Fact B (developments are unique
slotwise, so the attained minimum over one development is the minimum over all). -/
private lemma childW_isSlotMin (σ : Stage p F) (Φhat : Polynomial ℤ_[p])
    (hmon : Φhat.Monic) (e' h' : ℕ) :
    IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w := by
  classical
  intro f B N hf hdev
  have hex : ∃ m : ℤ, ∀ (B' : ℕ → Polynomial ℤ_[p]) (N' : ℕ),
      IsDevelopment Φhat f B' N' →
      SlotMinAttained m N' (fun j => (e' : ℤ) * σ.w (B' j) + (j : ℤ) * (h' : ℤ))
        (fun j => B' j ≠ 0) := by
    set S : Finset ℕ := (Finset.range N).filter (fun j => B j ≠ 0) with hSdef
    have hSne : S.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      apply hf
      rw [hdev.2.2]
      apply Finset.sum_eq_zero
      intro j hj
      have hbj : B j = 0 := by
        by_contra hbj
        have hjS : j ∈ S := Finset.mem_filter.mpr ⟨hj, hbj⟩
        rw [hemp] at hjS
        simp at hjS
      rw [hbj, zero_mul]
    obtain ⟨j1, hj1S, hj1min⟩ :=
      S.exists_min_image (fun j => (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)) hSne
    refine ⟨(e' : ℤ) * σ.w (B j1) + (j1 : ℤ) * (h' : ℤ), ?_⟩
    intro B' N' hdev'
    have huniq : ∀ j, B' j = B j := L0_FactB_unique Φhat hmon f hdev' hdev
    refine ⟨?_, ?_⟩
    · intro j hjN' hnz'
      have hbj : B j ≠ 0 := by rw [← huniq j]; exact hnz'
      have hjN : j < N := by
        by_contra hc; exact hbj (hdev.2.1 j (not_lt.mp hc))
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN, hbj⟩
      have hle := hj1min j hjS
      show (e' : ℤ) * σ.w (B j1) + (j1 : ℤ) * (h' : ℤ)
        ≤ (e' : ℤ) * σ.w (B' j) + (j : ℤ) * (h' : ℤ)
      rw [huniq j]
      exact hle
    · refine ⟨j1, ?_, ?_, ?_⟩
      · have hbj1 : B j1 ≠ 0 := (Finset.mem_filter.mp hj1S).2
        by_contra hc
        exact (show B' j1 ≠ 0 by rw [huniq j1]; exact hbj1) (hdev'.2.1 j1 (not_lt.mp hc))
      · show B' j1 ≠ 0
        rw [huniq j1]; exact (Finset.mem_filter.mp hj1S).2
      · show (e' : ℤ) * σ.w (B j1) + (j1 : ℤ) * (h' : ℤ)
          = (e' : ℤ) * σ.w (B' j1) + (j1 : ℤ) * (h' : ℤ)
        rw [huniq j1]
  have hchild : childW σ Φhat e' h' f = hex.choose := by
    unfold childW
    exact dif_pos hex
  rw [hchild]
  exact hex.choose_spec B N hdev

/- [SYN2-S1 SWEEP-1, 2026-07-31] private ResVal.w_one DELETED (= ResVal.w_one). -/

/-- On a nonzero coefficient (`deg < deg Φ̂`) the child weight is the single-slot value
`e′·w(B)` (its `Φ̂`-development is `B·Φ̂⁰`). -/
private lemma childW_coeff (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (hmon : Φhat.Monic)
    (e' h' : ℕ) (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBc : inC Φhat B) :
    childW σ Φhat e' h' B = (e' : ℤ) * σ.w B := by
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  have hSMW := childW_isSlotMin σ Φhat hmon e' h'
  have hdev : IsDevelopment Φhat B (fun j => if j = 0 then B else 0) 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = 0
      · simp only [hj, if_pos]; exact hBc
      · simp only [if_neg hj]
        rw [Polynomial.degree_zero]
        exact bot_lt_iff_ne_bot.mpr (mt Polynomial.degree_eq_bot.mp hΦne)
    · intro j hj
      have : j ≠ 0 := by omega
      simp only [if_neg this]
    · simp
  have hsm := hSMW B (fun j => if j = 0 then B else 0) 1 hB hdev
  obtain ⟨-, j0, hj0lt, -, hj0eq⟩ := hsm
  have hj0z : j0 = 0 := by omega
  subst hj0z
  simpa using hj0eq

/-- `childW 1 = 0`. -/
private lemma childW_one (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (hmon : Φhat.Monic)
    (hdeg : 1 ≤ Φhat.natDegree) (e' h' : ℕ) :
    childW σ Φhat e' h' 1 = 0 := by
  have hc : inC Φhat (1 : Polynomial ℤ_[p]) := by
    show (1 : Polynomial ℤ_[p]).degree < Φhat.degree
    rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hmon.ne_zero]
    exact_mod_cast hdeg
  rw [childW_coeff σ Φhat hmon e' h' 1 one_ne_zero hc, ResVal.w_one, mul_zero]

/-- `childW Φ̂ = h′`: the key's own development is `1·Φ̂¹`, slot `1`, value `h′`. -/
private lemma childW_key (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (hmon : Φhat.Monic)
    (hdeg : 1 ≤ Φhat.natDegree) (e' h' : ℕ) :
    childW σ Φhat e' h' Φhat = (h' : ℤ) := by
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  have hSMW := childW_isSlotMin σ Φhat hmon e' h'
  have hdev : IsDevelopment Φhat Φhat (fun j => if j = 1 then 1 else 0) 2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = 1
      · simp only [hj, if_pos]
        rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hΦne]
        exact_mod_cast hdeg
      · simp only [if_neg hj]
        rw [Polynomial.degree_zero]
        exact bot_lt_iff_ne_bot.mpr (mt Polynomial.degree_eq_bot.mp hΦne)
    · intro j hj
      have : j ≠ 1 := by omega
      simp only [if_neg this]
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      simp
  have hsm := hSMW Φhat (fun j => if j = 1 then 1 else 0) 2 hΦne hdev
  obtain ⟨-, j0, hj0lt, hj0nz, hj0eq⟩ := hsm
  have hj01 : j0 = 1 := by
    by_contra hc
    apply hj0nz
    simp only [if_neg hc]
  subst hj01
  rw [hj0eq]
  show (e' : ℤ) * σ.w (if (1 : ℕ) = 1 then (1 : Polynomial ℤ_[p]) else 0)
      + ((1 : ℕ) : ℤ) * (h' : ℤ) = (h' : ℤ)
  rw [if_pos rfl, ResVal.w_one]
  push_cast; ring

end Helpers

/-- Unit S5: `childW` is multiplicative on nonzeros and its value group is ℤ (the
generated-subgroup form, Stage's own `hvalgrp` shape). -/
theorem S5_childValuation {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) :
    (∀ f f' : Polynomial ℤ_[p], f ≠ 0 → f' ≠ 0 →
      childW σ Φhat e' h' (f * f')
        = childW σ Φhat e' h' f + childW σ Φhat e' h' f') ∧
    AddSubgroup.closure {n : ℤ | ∃ f f' : Polynomial ℤ_[p], f ≠ 0 ∧ f' ≠ 0 ∧
      childW σ Φhat e' h' f - childW σ Φhat e' h' f' = n} = ⊤ := by
  classical
  obtain ⟨hΦmon, hΦdeg⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hΦne : Φhat ≠ 0 := hΦmon.ne_zero
  have hdpos : 0 < σ.e * g * σ.Φ.natDegree :=
    Nat.mul_pos (Nat.mul_pos σ.he th.hg) σ.hdeg
  have hΦdeg1 : 1 ≤ Φhat.natDegree := by rw [hΦdeg]; omega
  have hSMW : IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w :=
    childW_isSlotMin σ Φhat hΦmon e' h'
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rwa [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap F F).comp σ.K.subtype = σ.K.subtype from by ext x; simp] at h
  -- degree comparison `deg σ.Φ ≤ deg Φ̂`
  have hdegle : σ.Φ.degree ≤ Φhat.degree := by
    rw [Polynomial.degree_eq_natDegree σ.hmonic.ne_zero,
      Polynomial.degree_eq_natDegree hΦne, hΦdeg]
    have : σ.Φ.natDegree ≤ σ.e * g * σ.Φ.natDegree := by
      calc σ.Φ.natDegree = 1 * σ.Φ.natDegree := (one_mul _).symm
        _ ≤ (σ.e * g) * σ.Φ.natDegree :=
            Nat.mul_le_mul_right _ (by nlinarith [σ.he, th.hg])
        _ = σ.e * g * σ.Φ.natDegree := by ring
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · -- multiplicativity: the proved engine L4_TRANSiii at `w' := childW`
    intro f f' hf hf'
    exact L4_TRANSiii σ ψ g Φhat th.hlift th.hirr th.hne_z hΦmon zbar hzbar e' h'
      th.hcop (childW σ Φhat e' h') hSMW th.hiaug f f' hf hf' (mul_ne_zero hf hf')
  · -- value group = ℤ (generated-subgroup form)
    set G : AddSubgroup ℤ := AddSubgroup.closure {n : ℤ | ∃ f f' : Polynomial ℤ_[p],
      f ≠ 0 ∧ f' ≠ 0 ∧ childW σ Φhat e' h' f - childW σ Φhat e' h' f' = n} with hGdef
    -- integer scalar multiples stay inside a subgroup
    have mem_mul : ∀ (n x : ℤ), x ∈ G → n * x ∈ G := by
      intro n x hx
      have hzs := zsmul_mem hx n
      rwa [zsmul_eq_mul, Int.cast_id] at hzs
    -- `h′ ∈ G` from `Φ̂` vs `1`
    have hhG : (h' : ℤ) ∈ G := by
      apply AddSubgroup.subset_closure
      refine ⟨Φhat, 1, hΦne, one_ne_zero, ?_⟩
      rw [childW_key σ Φhat hΦmon hΦdeg1 e' h', childW_one σ Φhat hΦmon hΦdeg1 e' h']
      ring
    -- `e′·e ∈ G` from two S6b-coefficients of consecutive parent weights
    have hee : (e' : ℤ) * (σ.e : ℤ) ∈ G := by
      obtain ⟨B1, hB1ne, hB1c, hB1w, -⟩ :=
        σ.hS6b (σ.wPrev σ.Φ + 1) 1 (by linarith)
      obtain ⟨B2, hB2ne, hB2c, hB2w, -⟩ :=
        σ.hS6b (σ.wPrev σ.Φ + 2) 1 (by linarith)
      have hB1cΦ : inC Φhat B1 := lt_of_lt_of_le hB1c hdegle
      have hB2cΦ : inC Φhat B2 := lt_of_lt_of_le hB2c hdegle
      apply AddSubgroup.subset_closure
      refine ⟨B2, B1, hB2ne, hB1ne, ?_⟩
      rw [childW_coeff σ Φhat hΦmon e' h' B2 hB2ne hB2cΦ,
        childW_coeff σ Φhat hΦmon e' h' B1 hB1ne hB1cΦ,
        σ.hStretch B2 hB2ne hB2c, σ.hStretch B1 hB1ne hB1c, hB1w, hB2w]
      ring
    -- `e′ ∈ G`
    have he'G : (e' : ℤ) ∈ G := by
      rcases eq_or_lt_of_le σ.he with he1 | he2
      · -- σ.e = 1
        rwa [show (σ.e : ℤ) = 1 by exact_mod_cast he1.symm, mul_one] at hee
      · -- σ.e ≥ 2: σ.Φ is a coefficient of Φ̂, giving `e′·h ∈ G`
        have hΦcoeff : inC Φhat σ.Φ := by
          show σ.Φ.degree < Φhat.degree
          rw [Polynomial.degree_eq_natDegree σ.hmonic.ne_zero,
            Polynomial.degree_eq_natDegree hΦne, hΦdeg]
          have he2' : 2 ≤ σ.e := he2
          have heg : 1 < σ.e * g := by
            have := Nat.mul_le_mul he2' th.hg
            omega
          have hlt : σ.Φ.natDegree < σ.e * g * σ.Φ.natDegree := by
            calc σ.Φ.natDegree = 1 * σ.Φ.natDegree := (one_mul _).symm
              _ < σ.e * g * σ.Φ.natDegree := (Nat.mul_lt_mul_right σ.hdeg).mpr heg
          exact_mod_cast hlt
        have heh : (e' : ℤ) * (σ.h : ℤ) ∈ G := by
          apply AddSubgroup.subset_closure
          refine ⟨σ.Φ, 1, σ.hmonic.ne_zero, one_ne_zero, ?_⟩
          rw [childW_coeff σ Φhat hΦmon e' h' σ.Φ σ.hmonic.ne_zero hΦcoeff,
            childW_one σ Φhat hΦmon hΦdeg1 e' h', σ.hwΦ]
          ring
        obtain ⟨a, b, hab⟩ := (Nat.Coprime.isCoprime σ.hcop)
        have hval : a * ((e' : ℤ) * (σ.e : ℤ)) + b * ((e' : ℤ) * (σ.h : ℤ)) = (e' : ℤ) := by
          linear_combination (e' : ℤ) * hab
        rw [← hval]
        exact G.add_mem (mem_mul a _ hee) (mem_mul b _ heh)
    -- `1 ∈ G` from Bézout `gcd(e′,h′) = 1`
    obtain ⟨x, y, hxy⟩ := (Nat.Coprime.isCoprime th.hcop)
    have hone : (1 : ℤ) ∈ G := by
      have : (1 : ℤ) = x * (e' : ℤ) + y * (h' : ℤ) := hxy.symm
      rw [this]
      exact G.add_mem (mem_mul x _ he'G) (mem_mul y _ hhG)
    -- a subgroup of ℤ containing `1` is `⊤`
    rw [AddSubgroup.eq_top_iff']
    intro z
    simpa using zsmul_mem hone z

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S5_childValuation
