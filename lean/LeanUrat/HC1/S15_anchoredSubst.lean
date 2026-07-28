/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.HC1.D8_digD_recenter
import LeanUrat.Moves.L5_recSubst_R4
import LeanUrat.Moves.L5_recRSland_R4
import LeanUrat.Moves.L0_GRg

/-!
# HC1.S15_anchoredSubst — the anchored substitution display (e_birth/e_read rerun, D6)

moves_ref: MOVES 2644–2653 (the anchored display + "Case J pinned a > 0 at
level 1"); 1488–1497 (the pass-7 e_birth/e_read demand). deps: S10, S14, D8; Moves
`L5_recSubst_R4` (clean). On the stratum `R(f) = z^a·(z − c̃)^μ·h(z)` (ψ′-order μ,
anchor a ≥ 0 by S14), the primed data are `a' = μ` and
`R'_anch(z') = (z' + c̃)^a·h(z' + c̃)` — with the D8 𝒟-leg: the birth cosets ride
as spectators (the digD data of the coefficients transform trivially). difficulty:
medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **Anchor existence**: every nonzero Laurent polynomial over a field has a `z`-anchor
`x = T a · toLaurent Ranch` with `Ranch.coeff 0 ≠ 0` (`a = ord_z x`, the trailing degree).
The explicit `Ranch` is the window sum of `L0_GRg`; its constant term is the trailing
coefficient of `x`, which is nonzero because the trailing degree lies in the support. -/
private lemma anchor_exists {K : Type*} [Field K] {x : LaurentPolynomial K} (hx : x ≠ 0) :
    ∃ (a : ℤ) (Ranch : Polynomial K), HasAnchorK x a Ranch := by
  have hne : x.support.Nonempty := Finsupp.support_nonempty_iff.mpr hx
  set a := x.support.min' hne with ha_def
  set M := x.support.max' hne with hM_def
  set g := (M - a).toNat + 1 with hg_def
  have hg1 : 1 ≤ g := by omega
  have hamem : a ∈ x.support := Finset.min'_mem _ hne
  have hxane : x.coeff a ≠ 0 := Finsupp.mem_support_iff.mp hamem
  have hsupp : ∀ k ∈ x.support, a ≤ k ∧ k < a + (g : ℤ) := by
    intro k hk
    refine ⟨Finset.min'_le _ k hk, ?_⟩
    have h1 : k ≤ M := Finset.le_max' _ k hk
    have h2 : a ≤ M := Finset.min'_le _ M (Finset.max'_mem _ hne)
    omega
  refine ⟨a, ∑ i ∈ Finset.range g, Polynomial.C (x.coeff (a + (i : ℤ))) * Polynomial.X ^ i,
    ?_, ?_⟩
  · -- `Ranch.coeff 0 = x.coeff a ≠ 0`
    have hc0 : (∑ i ∈ Finset.range g, Polynomial.C (x.coeff (a + (i : ℤ))) * Polynomial.X ^ i).coeff 0
        = x.coeff a := by
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 0
        (fun i _ hi0 => by rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)])
        (fun h => absurd (Finset.mem_range.mpr (by omega : 0 < g)) h)]
      simp
    rw [hc0]; exact hxane
  · -- the anchored identity `x = T a · toLaurent Ranch` (window-sum expansion, cf. `L0_GRg`)
    have key : LaurentPolynomial.T a *
          Polynomial.toLaurent (∑ i ∈ Finset.range g,
            Polynomial.C (x.coeff (a + (i : ℤ))) * Polynomial.X ^ i)
        = ∑ i ∈ Finset.range g,
            LaurentPolynomial.C (x.coeff (a + (i : ℤ))) * LaurentPolynomial.T (a + (i : ℤ)) := by
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.toLaurent_C_mul_X_pow, LaurentPolynomial.T_add]
      ring
    rw [key]
    have hx_repr : x = ∑ k ∈ x.support, LaurentPolynomial.C (x.coeff k) * LaurentPolynomial.T k := by
      conv_lhs => rw [← Finsupp.sum_single x]
      rw [Finsupp.sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      rfl
    conv_lhs => rw [hx_repr]
    let e : ℕ ↪ ℤ := ⟨fun i => a + (i : ℤ), fun i j h => by simpa using h⟩
    have hsub : x.support ⊆ (Finset.range g).map e := by
      intro k hk
      obtain ⟨hle, hlt⟩ := hsupp k hk
      rw [Finset.mem_map]
      exact ⟨(k - a).toNat, Finset.mem_range.mpr (by omega),
        by simp only [e, Function.Embedding.coeFn_mk]; omega⟩
    have hzero : ∀ k ∈ (Finset.range g).map e, k ∉ x.support →
        LaurentPolynomial.C (x.coeff k) * LaurentPolynomial.T k = 0 := by
      intro k hkS hknot
      rw [Finsupp.notMem_support_iff] at hknot
      rw [show x.coeff k = 0 from hknot, map_zero, zero_mul]
    rw [Finset.sum_subset hsub hzero, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [e, Function.Embedding.coeFn_mk]

/-- Unit S15: the anchored substitution display through a recentering, plus the
𝒟-form spectator clause. -/
theorem S15_anchoredSubst {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (hσ : StageCoreL σ) (he1 : σ.e = 1)
    (cc : ↥σ.K) (hcc : cc ≠ 0) (tt : Polynomial ℤ_[p])
    (hrec : IsRecenteringCore σ σ' cc tt) (hsub : RecenterSubstCore σ σ' cc)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0)
    (a : ℤ) (ha : 0 ≤ a) (μ : ℕ) (hpoly : Polynomial ↥σ.K)
    (hanch : HasAnchorK (σ.R f) a ((Polynomial.X - Polynomial.C cc) ^ μ * hpoly))
    (hnd : ¬ (Polynomial.X - Polynomial.C cc) ∣ hpoly)
    (zbar : Fˣ) (e_b : ℕ) [NeZero e_b] :
    (∃ Ranch' : Polynomial ↥σ'.K,
      HasAnchorK (σ'.R f) (μ : ℤ) Ranch' ∧
      Ranch'.map σ'.K.subtype
        = (Polynomial.X + Polynomial.C ((cc : ↥σ.K) : F)) ^ a.toNat *
          (hpoly.map σ.K.subtype).comp
            (Polynomial.X + Polynomial.C ((cc : ↥σ.K) : F))) ∧
    (∀ B : Polynomial ℤ_[p], B ≠ 0 → inC σ.Φ B →
      σ'.digD zbar e_b B = σ.digD zbar e_b B) := by
  refine ⟨?_, fun B hB hBc => D8_digD_recenter σ σ' cc tt hrec zbar e_b B hB hBc⟩
  -- ## Part 1: the anchored substitution display.
  -- an anchor for the primed residual (which is nonzero since `f ≠ 0`)
  obtain ⟨a', Ranch', hanch'⟩ := anchor_exists (σ'.hRne f hf)
  -- the ψ'-order of the stratum is exactly `μ` (the anchor clause `¬ ψ' ∣ h`)
  have hord : OrdPsiPoly (Polynomial.X - Polynomial.C cc)
      ((Polynomial.X - Polynomial.C cc) ^ μ * hpoly) μ := by
    refine ⟨dvd_mul_right _ _, ?_⟩
    intro hdvd
    rw [pow_succ] at hdvd
    have hne0 : ((Polynomial.X - Polynomial.C cc) ^ μ : Polynomial ↥σ.K) ≠ 0 :=
      pow_ne_zero _ (Polynomial.X_sub_C_ne_zero cc)
    exact hnd ((mul_dvd_mul_iff_left hne0).mp hdvd)
  -- the RS-landing theorem pins `a' = μ` and gives the substitution identity in `RatFunc F`
  obtain ⟨hiff, hmapeq⟩ := L5_recRSland σ σ' cc hcc tt hrec hsub μ f hf a
    ((Polynomial.X - Polynomial.C cc) ^ μ * hpoly) hanch a' Ranch' hanch'
  have ha' : a' = (μ : ℤ) := hiff.mp hord
  subst ha'
  refine ⟨Ranch', hanch', ?_⟩
  -- ### recentre the anchored residual: `((X − c̃)^μ·h)∘(X + c̃) = X^μ · h∘(X + c̃)`
  have hcomp : (((Polynomial.X - Polynomial.C cc) ^ μ * hpoly).map σ.K.subtype).comp
        (Polynomial.X + Polynomial.C ((cc : ↥σ.K) : F))
      = Polynomial.X ^ μ *
          (hpoly.map σ.K.subtype).comp (Polynomial.X + Polynomial.C ((cc : ↥σ.K) : F)) := by
    have hcoe : (σ.K.subtype cc) = ((cc : ↥σ.K) : F) := rfl
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, hcoe, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp,
      Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_right]
  rw [hcomp] at hmapeq
  -- ### unit powers → field powers (`a' = μ ≥ 0`, `a ≥ 0`)
  have hu1 : ((ratX F ^ (μ : ℤ) : (RatFunc F)ˣ) : RatFunc F) = (RatFunc.X : RatFunc F) ^ μ := by
    rw [Units.val_zpow_eq_zpow_val, ratX, Units.val_mk0, zpow_natCast]
  have hu2 : ((ratXShift ((cc : ↥σ.K) : F) ^ a : (RatFunc F)ˣ) : RatFunc F)
      = (RatFunc.X + RatFunc.C ((cc : ↥σ.K) : F) : RatFunc F) ^ a.toNat := by
    rw [Units.val_zpow_eq_zpow_val, ratXShift, Units.val_mk0,
      ← zpow_natCast (RatFunc.X + RatFunc.C ((cc : ↥σ.K) : F) : RatFunc F) a.toNat,
      Int.toNat_of_nonneg ha]
  rw [hu1, hu2] at hmapeq
  -- ### cancel `X^μ` and pull back through the injective `F[X] → RatFunc F`
  have hXμ : (RatFunc.X : RatFunc F) ^ μ ≠ 0 := pow_ne_zero μ RatFunc.X_ne_zero
  apply RatFunc.algebraMap_injective F
  apply mul_left_cancel₀ hXμ
  rw [hmapeq]
  simp only [map_mul, map_pow, map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  ring

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S15_anchoredSubst
