/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.K1_vertexPin
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.S3_childK1
import LeanUrat.HC1.S5_childValuation
import LeanUrat.HC1.S9a_stageLiteral
import LeanUrat.HC1.S9w_residualLaws
import LeanUrat.HC1.V7_stripDischarge
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L4_TRANSii
import LeanUrat.Moves.L4_TRANSviii_b_R4

/-!
# HC1.S9b_childWeightSet — the (S6′) legs: weightSet := 𝒜′, cumulative over S9a

S9 DECOMPOSITION unit (blueprint §9.5): "S9b: weightSet := 𝒜′ + hS6a/hS6b via the
TRANSviii finals." The `hS6a`/`hS6b` realizer laws are `Stage` fields of the
literal; this unit's statement content is that the literal can be built with its
`weightSet` PINNED to 𝒜′ (`childWeightSet` — the parent-scale coefficient weight
set, read against `σ'.wPrev = σ.w`), cumulatively over S9a's conjuncts.

**RESTATED (2026-07-28, mechanical-closer round — the S9a precedent + adjudication
applied verbatim): the increment guard `e·g > 1`.** The unguarded statement is
refuted at the `σ.e * g = 1` corner by EXACTLY S9a's kernel argument: S9b's ∃ is
S9a's ∃ strengthened by the `weightSet` conjunct, so any witness for it witnesses
the refuted S9a shape — `TransitionData.child_reps` puts the outgoing key `σ.Φ`
on the child list, `hreps` forces it into `C_Φ̂`, and at `e·g = 1` the degrees
collide (`S9b_ungated_corner_refuted` below, the in-file machine-checked kernel,
delegating to `S9a_ungated_corner_refuted`). ADJUDICATION (S9a's, verbatim): the
note's LST tower-induction step carries the guard EXPLICITLY — MOVES 3755–3757:
"STEP at an INCREMENT ν_{i+1} (stage data (e_{i+1}, h_{i+1}), **e·g > 1**)" — and
the `e·g = 1` corner is the note's OTHER species, MOVES 3766–3767 (RECENTERING,
`Φ̂ ↦ Φ̂ + t`), handled by the PROVED S10_recStage, not by S9. The statement gains
the hypothesis `hEG : 1 < σ.e * g`; the refutation corner fails the guard by
`S9a_corner_fails_guard` (proved in S9a's file; the arithmetic is
statement-independent, so it is cited as-is rather than duplicated).

**PROVED (same round): the guarded literal.** The S9a_final construction re-runs
verbatim — Bézout split, the S9w lawful carrier, the S2/S3/S5 childW plumbing,
the in-file hwult (slotwise development addition), hS6b′ + the above-threshold
half of hS6a′ via `L4_TRANSviii_b` + the carrier pin, and the BELOW-THRESHOLD
strip via `V7_stripDischarge` (σ′-free; the blueprint's original "TRANSviii_a
conjunct 2 verbatim" route was found CIRCULAR at S9a_final — TRANSviii_a consumes
a full child Stage — so this file's (S6a′)/(S6b′) come through the S9a route,
superseding the E-phase header's "via the TRANSviii finals" plan). The assembled
literal already pins `weightSet := childWeightSet σ Φ̂` (S9a's own `hWS` field
reads against it), so the new fourth conjunct closes by `rfl`.
difficulty: HARD (assembly). hyp: hEG (the adjudicated note guard).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **The refutation kernel, machine-checked** (the corner the restated guard
excludes; the S9a kernel transported): at `σ.e * g = 1` — the recentering
species, `deg Φ̂ = deg σ.Φ` — NO child stage can carry the S9b record, since the
S9b record contains the (refuted) S9a record: `TransitionData.child_reps` puts
the outgoing key on the child list, `hreps` forces it into `C_Φ̂`, and the
degrees collide. -/
theorem S9b_ungated_corner_refuted {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hcorner : σ.e * g = 1) :
    ¬ ∃ σ' : Stage p F,
        TransitionData σ σ' Φhat e' h' zbar ∧
        VertexPin σ σ' Φhat zbar ∧
        (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) ∧
        σ'.weightSet = childWeightSet σ Φhat := by
  rintro ⟨σ', td, pin, hw, -⟩
  exact S9a_ungated_corner_refuted σ th hcorner ⟨σ', td, pin, hw⟩

/-- Unit S9b (RESTATED 2026-07-28 with the adjudicated note guard `e·g > 1`,
MOVES 3755–3757, per the S9a precedent — see the header): at every INCREMENT
read (`1 < σ.e * g`), the S9a literal can be assembled with its `weightSet`
pinned to the child parent-scale coefficient weight set 𝒜′. -/
theorem S9b_childWeightSet {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hEG : 1 < σ.e * g) :
    ∃ σ' : Stage p F,
      TransitionData σ σ' Φhat e' h' zbar ∧
      VertexPin σ σ' Φhat zbar ∧
      (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) ∧
      σ'.weightSet = childWeightSet σ Φhat := by
  classical
  -- ## Lift facts (L3) and the guard's degree consequence (the S9a_final body)
  obtain ⟨hmonΦ, hdegΦ⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hΦne : Φhat ≠ 0 := hmonΦ.ne_zero
  have hdeg1 : 1 ≤ Φhat.natDegree := by
    rw [hdegΦ]
    exact Nat.mul_pos (by omega : 0 < σ.e * g) σ.hdeg
  have hΦnatlt : σ.Φ.natDegree < Φhat.natDegree := by
    rw [hdegΦ]
    calc σ.Φ.natDegree = 1 * σ.Φ.natDegree := (one_mul _).symm
      _ < (σ.e * g) * σ.Φ.natDegree := by
          have h0 : 0 < σ.Φ.natDegree := σ.hdeg
          exact Nat.mul_lt_mul_of_lt_of_le hEG (le_refl _) h0
  have hΦlt : σ.Φ.degree < Φhat.degree := by
    rw [Polynomial.degree_eq_natDegree σ.hmonic.ne_zero,
      Polynomial.degree_eq_natDegree hΦne]
    exact_mod_cast hΦnatlt
  -- ## The child Bézout pair, P2-pinned at e′ = 1 (the (vii) split)
  obtain ⟨s', t', hbez', ht'0⟩ :
      ∃ s' t' : ℤ, (e' : ℤ) * s' + (h' : ℤ) * t' = 1 ∧ (e' = 1 → t' = 0) := by
    by_cases he1 : e' = 1
    · exact ⟨1, 0, by rw [he1]; push_cast; ring, fun _ => rfl⟩
    · refine ⟨Nat.gcdA e' h', Nat.gcdB e' h', ?_, fun h => absurd h he1⟩
      have hg := Nat.gcd_eq_gcd_ab e' h'
      rw [th.hcop] at hg
      exact_mod_cast hg.symm
  -- ## The lawful D.7(vi)-normalized residual carrier (S9w)
  obtain ⟨hexD, hwstrict⟩ := S9w_residualLaws σ hσ th s' t' hbez' ht'0
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := hexD.choose_spec
  -- ## The childW plumbing (S2/S3/S5) + parent basics
  obtain ⟨hdevMin, hSMW⟩ := S2_childW σ Φhat hmonΦ hdeg1 e' h'
  have hw1 : σ.w 1 = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    omega
  obtain ⟨hwPhi, hK1c⟩ := S3_childK1 σ Φhat hmonΦ hdeg1 e' h' th.he' th.hh' hw1
  obtain ⟨hwmulc, hvalgrpc⟩ := S5_childValuation σ hσ th
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
    exact h
  -- ## The child ultrametric law (developments add slotwise; parent hwult per slot)
  have hwult : ∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
      min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g') ≤
        childW σ Φhat e' h' (f + g') := by
    intro f g' hf hg' hfg
    obtain ⟨Bf, Nf, hdf, hmf⟩ := hdevMin f hf
    obtain ⟨Bg, Ng, hdg, hmg⟩ := hdevMin g' hg'
    set N := max Nf Ng with hN
    -- the slotwise sum is a development of f + g' at length N
    have hsub_f : Finset.range Nf ⊆ Finset.range N := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_left _ _))
    have hsub_g : Finset.range Ng ⊆ Finset.range N := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_right _ _))
    have hsum_f : f = ∑ j ∈ Finset.range N, Bf j * Φhat ^ j := by
      rw [hdf.2.2]
      refine Finset.sum_subset hsub_f ?_
      intro j hjN hjNf
      rw [hdf.2.1 j (by simpa using hjNf), zero_mul]
    have hsum_g : g' = ∑ j ∈ Finset.range N, Bg j * Φhat ^ j := by
      rw [hdg.2.2]
      refine Finset.sum_subset hsub_g ?_
      intro j hjN hjNg
      rw [hdg.2.1 j (by simpa using hjNg), zero_mul]
    have hdevS : IsDevelopment Φhat (f + g') (fun j => Bf j + Bg j) N := by
      refine ⟨?_, ?_, ?_⟩
      · intro j
        exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt (hdf.1 j) (hdg.1 j))
      · intro j hj
        show Bf j + Bg j = 0
        rw [hdf.2.1 j (le_trans (le_max_left _ _) hj),
          hdg.2.1 j (le_trans (le_max_right _ _) hj), add_zero]
      · rw [hsum_f, hsum_g, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => (add_mul (Bf j) (Bg j) (Φhat ^ j)).symm
    obtain ⟨hlow, jS, hjSN, hjSnz, hjSeq⟩ := hSMW (f + g') _ N hfg hdevS
    rw [hjSeq]
    -- per-slot case split on which side is present
    by_cases hBf : Bf jS = 0
    · have hBg : Bg jS ≠ 0 := by
        intro hBg
        exact hjSnz (by rw [hBf, hBg, add_zero])
      have hjNg : jS < Ng := by
        by_contra hge
        exact hBg (hdg.2.1 jS (le_of_not_gt hge))
      have hle := (hmg.1) jS hjNg hBg
      have hval : σ.w (Bf jS + Bg jS) = σ.w (Bg jS) := by rw [hBf, zero_add]
      calc min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g')
          ≤ childW σ Φhat e' h' g' := min_le_right _ _
        _ ≤ (e' : ℤ) * σ.w (Bg jS) + (jS : ℤ) * (h' : ℤ) := hle
        _ = (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by rw [hval]
    · by_cases hBg : Bg jS = 0
      · have hjNf : jS < Nf := by
          by_contra hge
          exact hBf (hdf.2.1 jS (le_of_not_gt hge))
        have hle := (hmf.1) jS hjNf hBf
        have hval : σ.w (Bf jS + Bg jS) = σ.w (Bf jS) := by rw [hBg, add_zero]
        calc min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g')
            ≤ childW σ Φhat e' h' f := min_le_left _ _
          _ ≤ (e' : ℤ) * σ.w (Bf jS) + (jS : ℤ) * (h' : ℤ) := hle
          _ = (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by rw [hval]
      · -- both slots present: the parent ultrametric law
        have hjNf : jS < Nf := by
          by_contra hge
          exact hBf (hdf.2.1 jS (le_of_not_gt hge))
        have hjNg : jS < Ng := by
          by_contra hge
          exact hBg (hdg.2.1 jS (le_of_not_gt hge))
        have hult := σ.hwult (Bf jS) (Bg jS) hBf hBg hjSnz
        have hlef := (hmf.1) jS hjNf hBf
        have hleg := (hmg.1) jS hjNg hBg
        have he'nn : (0 : ℤ) ≤ (e' : ℤ) := Int.natCast_nonneg e'
        rcases min_cases (σ.w (Bf jS)) (σ.w (Bg jS)) with ⟨hmin, hcmp⟩ | ⟨hmin, hcmp⟩
        · have : childW σ Φhat e' h' f ≤ (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by
            have h2 : σ.w (Bf jS) ≤ σ.w (Bf jS + Bg jS) := by rw [← hmin]; exact hult
            have h3 := mul_le_mul_of_nonneg_left h2 he'nn
            linarith
          exact le_trans (min_le_left _ _) this
        · have : childW σ Φhat e' h' g' ≤ (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by
            have h2 : σ.w (Bg jS) ≤ σ.w (Bf jS + Bg jS) := by rw [← hmin]; exact hult
            have h3 := mul_le_mul_of_nonneg_left h2 he'nn
            linarith
          exact le_trans (min_le_right _ _) this
  -- ## (S6b′): full scalars above the key weight, via the Moves final `L4_TRANSviii_b`
  have hS6b' : ∀ (ν : ℤ) (a : (↥(σ.nextField zbar))ˣ), σ.w Φhat < ν →
      ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
        hexD.choose.Rc B = LaurentPolynomial.C ((a : ↥(σ.nextField zbar))) *
          LaurentPolynomial.T (- t' * ν) := by
    intro ν a hν
    obtain ⟨B, hBc, hdig, hnz⟩ := L4_TRANSviii_b σ hσ.core ψ g th.hdeg th.hmonic th.hirr
      th.hne_z Φhat th.hlift zbar hzbar ν hν ((a : ↥(σ.nextField zbar)) : F)
      (SetLike.coe_mem _)
    have hane : ((a : ↥(σ.nextField zbar)) : F) ≠ 0 := by
      have := a.ne_zero
      exact fun h => this (Subtype.ext h)
    obtain ⟨hB0, hBw⟩ := hnz hane
    obtain ⟨c', hc'R, hc'F⟩ := hexD.choose.hS5' B hB0 hBc
    have hcs : (c' : ↥(σ.nextField zbar)) = (a : ↥(σ.nextField zbar)) := by
      apply Subtype.ext
      rw [hc'F, hdig]
    refine ⟨B, hB0, hBc, hBw, ?_⟩
    rw [hc'R, hcs, hBw]
  -- ## (S6a′): the coset-orbit realizers (V5 fixed-point coset form, blueprint §10
  -- Key Finding 2).  Above the threshold: hS6b′ with base b = 1 (exact scalars).
  -- Below (the strip): the V7 discharge, exactly as in S9a_final (σ′-free).
  have hS6a' : ∀ ν ∈ childWeightSet σ Φhat, ∃ b : (↥(σ.nextField zbar))ˣ,
      ∀ c : (↥(σ.nextField zbar))ˣ,
      ((c : ↥(σ.nextField zbar)) : F) ∈ σ.FQ →
      ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
        hexD.choose.Rc B
          = LaurentPolynomial.C ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) *
            LaurentPolynomial.T (- t' * ν) := by
    intro ν hν
    rcases lt_or_ge (σ.w Φhat) ν with hgt | hle
    · exact ⟨1, fun c _ => by rw [mul_one]; exact hS6b' ν c hgt⟩
    · -- BELOW-THRESHOLD STRIP (ν ≤ σ.w Φ̂): the V7 discharge (S9a_final's route,
      -- 2026-07-28) — σ′-free: the parent (S6a) coset realizer ridden up the K1
      -- minimizing slot, pinned into Rc through the carrier's own hS5' (raw
      -- digPrime, mfun ≡ 0). Same kernel in Moves-lemma form: `Moves.L4_TRANSviii_c`.
      exact V7_stripDischarge σ hσ th s' t' hbez' ht'0 hexD.choose hexD.choose_spec ν hν
  -- ## The literal (weightSet := childWeightSet — this unit's pinned field)
  refine ⟨{
      e := e', h := h', s := s', t := t',
      he := th.he', hh := th.hh', hcop := th.hcop, hbez := hbez', he1t := ht'0,
      Φ := Φhat, hmonic := hmonΦ, hdeg := hdeg1,
      w := childW σ Φhat e' h',
      wPrev := σ.w,
      K := σ.nextField zbar, FQ := σ.FQ,
      hFQ_le := le_trans σ.hFQ_le (σ.le_nextField zbar),
      R := hexD.choose.Rc,
      hwmul := hwmulc,
      hwult := hwult,
      hvalgrp := hvalgrpc,
      hwΦ := hwPhi,
      hStretch := fun B hB hBc => L4_TRANSii σ Φhat e' h' _ hSMW B hB hBc,
      hR0 := hR0, hRne := hRne, hRmul := hRmul, hRadd := hRadd, hRlt := hRlt,
      hRΦ := hexD.choose.hRPhi,
      hK1 := by rw [hwPhi]; exact hK1c,
      hS5 := fun B hB hBc =>
        ⟨(hexD.choose.hS5' B hB hBc).choose, (hexD.choose.hS5' B hB hBc).choose_spec.1⟩,
      reps := σ.reps ++ [σ.Φ],
      hreps := fun ũ hũ => by
        rcases List.mem_append.mp hũ with h | h
        · exact ⟨(σ.hreps ũ h).1, lt_trans (σ.hreps ũ h).2 hΦlt⟩
        · rw [List.mem_singleton] at h
          subst h
          exact ⟨σ.hmonic.ne_zero, hΦlt⟩,
      Tvec := σ.Tvec.map (fun q => (q.1, s' * q.2)) ++ [(σ.Φ, s' * σ.t)],
      hTvec := by
        rw [List.map_append, List.map_map]
        simp only [Function.comp_def, List.map_cons, List.map_nil]
        rw [σ.hTvec],
      weightSet := childWeightSet σ Φhat,
      hWS := fun B hB hBc => ⟨B, hB, hBc, rfl⟩,
      hS6a := hS6a',
      hS6b := hS6b' }, ?_, ?_, ?_, ?_⟩
  · -- TransitionData: the construction records, all definitional on the literal
    exact { child_key := rfl, child_e := rfl, child_h := rfl,
            child_field := rfl, field_grow := σ.le_nextField zbar,
            child_base := rfl, child_wPrev := fun f => rfl, threshold := rfl,
            child_slotmin := hSMW, child_reps := rfl }
  · -- VertexPin: exactly the carrier's S5′ pinned shape (mfun ≡ 0)
    exact hexD.choose.hS5'
  · -- the childW tie: definitional on the literal
    exact fun f _ => rfl
  · -- S9b's own conjunct: weightSet = 𝒜′, definitional on the literal
    rfl

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9b_childWeightSet
#print axioms LeanUrat.HC1.S9b_ungated_corner_refuted
