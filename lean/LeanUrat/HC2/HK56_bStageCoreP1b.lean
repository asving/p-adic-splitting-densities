/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC2.HK13_bStageCoreP1a
import LeanUrat.Moves.ResVal

/-!
# HC2.HK56_bStageCoreP1b — HK-56: `StageCoreL` at the gate base stage, part 1b

Bridge campaign BP2 (`lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md`, Block G, unit HK-56 —
NEW unit at REVISION 2, split out of HK-13, Codex finding 16).  E-PHASE SKELETON:
statements with `sorry` bodies; P-phase proves (hard-fable, est. ~70 lines).

**Unit HK-56** — blueprint statement: "`StageCoreL bStage` part 1b — SlotDecomp +
CoeffFieldLawCore at bStage (the two law groups with their own decomposition machinery)."

CARRIER RESOLUTION: stated at `bStageP` (the HK-13 base-pin re-dress of `U31.bStage`),
per the transcription finding recorded in `HK13_bStageCoreP1a.lean`'s module header
(`StageCoreL` at the literal `U31.bStage` is refutable: empty `reps`, refuted
`prevIaug`).  Both law groups here read only `w`/`R`/`wPrev`-on-`C_X`/`t = 0` data, on
which `bStageP` and `U31.bStage` agree — the U31 NF (normal-form) machinery is the
proof supply.

Statement shapes = `StageCore`'s `slot`/`coeff` field types at `σ := bStageP` (HK-16's
assembly is a constructor application).

deps: HK-13 (carrier lemmas).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves

/-- HK-56 (part 1b, `StageCore.slot` shape): **(S3) genuine slot decomposition** at the
gate base stage — `R` is additive across equal-weight slots of a weight-flat development,
and `Y = [Φ]` is degreewise transcendental over the coefficient classes (a one-graded-
piece `Σ_j R(B_j)·(R Φ)^j = 0` vanishes termwise).  At `bStageP`: `Φ = X`, `w = bw`,
`R = bR` — concrete θ/NF arithmetic (2-adic normal forms; the U31 600-line-build
precedent).  [Blueprint BP2 HK-56; deps: HK-13.] -/
theorem bStageP_slotDecomp : SlotDecomp bStageP := by
  constructor
  · -- DECOMPOSITION: within a graded piece, R is additive across slots (NF argument)
    intro B N γ htail hw hne hwsum
    classical
    have hw' : ∀ j, j < N → B j ≠ 0 →
        U31.bw (B j * (X : Polynomial ℤ_[2]) ^ j) = γ := hw
    have hne' : (∑ j ∈ Finset.range N, B j * (X : Polynomial ℤ_[2]) ^ j) ≠ 0 := hne
    have hwsum' : U31.bw (∑ j ∈ Finset.range N, B j * (X : Polynomial ℤ_[2]) ^ j) = γ :=
      hwsum
    show U31.bR (∑ j ∈ Finset.range N, B j * (X : Polynomial ℤ_[2]) ^ j)
        = ∑ j ∈ Finset.range N, U31.bR (B j * (X : Polynomial ℤ_[2]) ^ j)
    set S : Finset ℕ := (Finset.range N).filter (fun j => B j ≠ 0) with hS
    have haj : ∀ j ∈ S, B j * (X : Polynomial ℤ_[2]) ^ j ≠ 0 := by
      intro j hj
      rw [hS, Finset.mem_filter] at hj
      exact mul_ne_zero hj.2 (pow_ne_zero _ X_ne_zero)
    have hSne : S.Nonempty := by
      by_contra hSe
      rw [Finset.not_nonempty_iff_eq_empty] at hSe
      apply hne'
      refine Finset.sum_eq_zero (fun j hj => ?_)
      by_cases hBj : B j = 0
      · rw [hBj, zero_mul]
      · exact absurd (hSe ▸ (Finset.mem_filter.mpr ⟨hj, hBj⟩) : j ∈ (∅ : Finset ℕ))
          (Finset.notMem_empty j)
    obtain ⟨j₀, hj₀⟩ := hSne
    have hγ0 : 0 ≤ γ := by
      have hj₀' := hj₀
      rw [hS, Finset.mem_filter, Finset.mem_range] at hj₀'
      obtain ⟨m, Q, hQ⟩ := HK13R.NF_exists (HK13R.θ_ne_zero (haj j₀ hj₀))
      have hm := hw' j₀ hj₀'.1 hj₀'.2
      rw [U31.bw_eq hQ] at hm
      omega
    -- per-slot NF cofactors at the common exponent γ.toNat
    have hex : ∀ j, ∃ Q, j ∈ S →
        U31.NF (U31.θ (B j * (X : Polynomial ℤ_[2]) ^ j)) γ.toNat Q := by
      intro j
      by_cases hj : j ∈ S
      · obtain ⟨m, Q, hQ⟩ := HK13R.NF_exists (HK13R.θ_ne_zero (haj j hj))
        have hj' := hj
        rw [hS, Finset.mem_filter, Finset.mem_range] at hj'
        have hm : (m : ℤ) = γ := by
          rw [← U31.bw_eq hQ]
          exact hw' j hj'.1 hj'.2
        have hmt : m = γ.toNat := by omega
        exact ⟨Q, fun _ => hmt ▸ hQ⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose Q hQ using hex
    have hsplitθ : (∑ j ∈ Finset.range N, U31.θ (B j * (X : Polynomial ℤ_[2]) ^ j))
        = ∑ j ∈ S, U31.θ (B j * (X : Polynomial ℤ_[2]) ^ j) := by
      rw [hS]
      exact (Finset.sum_filter_of_ne (p := fun j => B j ≠ 0) (fun j _ hne0 hBj =>
        hne0 (by rw [hBj, zero_mul, map_zero]))).symm
    have hθsum : U31.θ (∑ j ∈ Finset.range N, B j * (X : Polynomial ℤ_[2]) ^ j)
        = (Polynomial.C 2) ^ γ.toNat * ∑ j ∈ S, Q j := by
      rw [map_sum, hsplitθ, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => (hQ j hj).1)
    have hSQne : (∑ j ∈ S, Q j).map U31.ρ ≠ 0 := by
      intro h0
      rcases eq_or_ne (∑ j ∈ S, Q j) 0 with hz | hz
      · apply HK13R.θ_ne_zero hne'
        rw [hθsum, hz, mul_zero]
      · obtain ⟨S', hS'⟩ := (HK13R.map_ρ_eq_zero_iff _).mp h0
        have hNF' : U31.θ (∑ j ∈ Finset.range N, B j * (X : Polynomial ℤ_[2]) ^ j)
            = (Polynomial.C 2) ^ (γ.toNat + 1) * S' := by
          rw [hθsum, hS', pow_succ]
          ring
        obtain ⟨m', Q', hQ'⟩ := HK13R.NF_exists (HK13R.θ_ne_zero hne')
        have hdom := HK13R.NF_dominates hQ' hNF'
        have hm' : (m' : ℤ) = γ := by
          rw [← U31.bw_eq hQ']
          exact hwsum'
        omega
    have hNFsum : U31.NF (U31.θ (∑ j ∈ Finset.range N, B j * (X : Polynomial ℤ_[2]) ^ j))
        γ.toNat (∑ j ∈ S, Q j) := ⟨hθsum, hSQne⟩
    rw [HK13R.bR_eq hNFsum]
    have hrhs : (∑ j ∈ Finset.range N, U31.bR (B j * (X : Polynomial ℤ_[2]) ^ j))
        = ∑ j ∈ S, U31.bR (B j * (X : Polynomial ℤ_[2]) ^ j) := by
      rw [hS]
      exact (Finset.sum_filter_of_ne (p := fun j => B j ≠ 0) (fun j _ hne0 hBj =>
        hne0 (by rw [hBj, zero_mul, HK13R.bR_zero]))).symm
    rw [hrhs]
    calc ((∑ j ∈ S, Q j).map U31.ρ).toLaurent
        = Polynomial.toLaurent ((Polynomial.mapRingHom U31.ρ) (∑ j ∈ S, Q j)) := rfl
      _ = ∑ j ∈ S, Polynomial.toLaurent ((Polynomial.mapRingHom U31.ρ) (Q j)) := by
          rw [map_sum, map_sum]
      _ = ∑ j ∈ S, U31.bR (B j * (X : Polynomial ℤ_[2]) ^ j) :=
          Finset.sum_congr rfl (fun j hj => ((HK13R.bR_eq (hQ j hj)).symm : _))
  · -- INDEPENDENCE: a vanishing one-graded-piece Y-combination vanishes termwise
    intro B N γ hB hzero j hjN
    by_contra hBj
    have hzero' : (∑ l ∈ Finset.range N,
        U31.bR (B l) * (U31.bR (X : Polynomial ℤ_[2])) ^ l) = 0 := hzero
    have hRl : ∀ l, l < N → B l ≠ 0 → U31.bR (B l) = 1 := by
      intro l hl hBl
      have hin : inC (X : Polynomial ℤ_[2]) (B l) := (hB l hl hBl).1
      have hc : B l = Polynomial.C ((B l).coeff 0) := U31.is_const hin
      have hb : (B l).coeff 0 ≠ 0 := fun h => hBl (by rw [hc, h, map_zero])
      rw [hc]
      exact HK13R.bR_const hb
    have happ : (∑ l ∈ Finset.range N,
        U31.bR (B l) * (U31.bR (X : Polynomial ℤ_[2])) ^ l) ((j : ℤ)) = 0 := by
      rw [hzero']
      rfl
    rw [ResVal.sum_apply'] at happ
    have hother : ∀ l ∈ Finset.range N, l ≠ j →
        (U31.bR (B l) * (U31.bR (X : Polynomial ℤ_[2])) ^ l) ((j : ℤ)) = 0 := by
      intro l hl hlj
      by_cases hBl : B l = 0
      · rw [hBl, HK13R.bR_zero, zero_mul]
        rfl
      · rw [hRl l (Finset.mem_range.mp hl) hBl, one_mul, HK13R.bR_X,
          LaurentPolynomial.T_pow, mul_one]
        have hone : (LaurentPolynomial.T ((l : ℤ)) : LaurentPolynomial ↥U31.K2)
            = LaurentPolynomial.C 1 * LaurentPolynomial.T ((l : ℤ)) := by
          rw [map_one, one_mul]
        rw [hone, ResVal.CT_apply, if_neg (by exact_mod_cast hlj)]
    have hjval : (U31.bR (B j) * (U31.bR (X : Polynomial ℤ_[2])) ^ j) ((j : ℤ)) = 1 := by
      rw [hRl j hjN hBj, one_mul, HK13R.bR_X, LaurentPolynomial.T_pow, mul_one]
      have hone : (LaurentPolynomial.T ((j : ℤ)) : LaurentPolynomial ↥U31.K2)
          = LaurentPolynomial.C 1 * LaurentPolynomial.T ((j : ℤ)) := by
        rw [map_one, one_mul]
      rw [hone, ResVal.CT_apply, if_pos rfl]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hjN) hother, hjval] at happ
    exact one_ne_zero happ

/-- HK-56 (part 1b, `StageCore.coeff` shape): **(S4) core** at the gate base stage — every
`K₂ˣ` scalar realized as a coefficient digit at its forced position (`t = 0` ⇒ position 0;
scalars are all 1 in `K₂ ≅ 𝔽₂`), equal-weight coefficient-products have `K`-constant
residual ratio, and the degree-0 exponent group of the `L`-monomials is `ℤ = ⟨z⟩`.
[Blueprint BP2 HK-56; deps: HK-13.] -/
theorem bStageP_coeffFieldLawCore : CoeffFieldLawCore bStageP := by
  refine ⟨?_, ?_, ?_⟩
  · -- (L^coeff)₀ ⊇ K: every unit scalar realized (at the sole scalar 1 of K₂)
    intro c
    refine ⟨1, 0, one_ne_zero, ?_, HK13R.gaussVal_one, ?_⟩
    · show (1 : Polynomial ℤ_[2]).degree < bStageP.Φ.degree
      rw [bStageP_Phi_def, Polynomial.degree_one, Polynomial.degree_X]
      norm_num
    · rw [bStageP_unit_eq_one c]
      have hR : bStageP.R (1 : Polynomial ℤ_[2]) = 1 := HK13R.bR_one
      rw [hR, map_one, bStageP_t_def, neg_zero, zero_mul, LaurentPolynomial.T_zero,
        one_mul]
  · -- (L^coeff)₀ ⊆ K: coefficient products are constants of residual 1
    intro f g hf hg hfne hgne _
    refine ⟨1, ?_⟩
    obtain ⟨lf, hlf, hfeq⟩ := hf
    obtain ⟨lg, hlg, hgeq⟩ := hg
    have hprod : ∀ (l : List (Polynomial ℤ_[2])),
        (∀ u ∈ l, u ≠ 0 ∧ inC (X : Polynomial ℤ_[2]) u) → l.prod ≠ 0 →
        U31.bR l.prod = 1 := by
      intro l
      induction l with
      | nil =>
          intro _ _
          rw [List.prod_nil]
          exact HK13R.bR_one
      | cons a t ih =>
          intro h hne0
          rw [List.prod_cons] at hne0 ⊢
          have hane : a ≠ 0 := fun h0 => hne0 (by rw [h0, zero_mul])
          have htne : t.prod ≠ 0 := fun h0 => hne0 (by rw [h0, mul_zero])
          rw [HK13R.bR_mul a t.prod hane htne,
            ih (fun u hu => h u (List.mem_cons_of_mem a hu)) htne, mul_one]
          have ha := h a List.mem_cons_self
          have hac : a = Polynomial.C (a.coeff 0) := U31.is_const ha.2
          have hb : a.coeff 0 ≠ 0 := fun h0 => hane (by rw [hac, h0, map_zero])
          rw [hac]
          exact HK13R.bR_const hb
    have hRf : bStageP.R f = 1 := by
      rw [hfeq]
      exact hprod lf (fun u hu => hlf u hu) (hfeq ▸ hfne)
    have hRg : bStageP.R g = 1 := by
      rw [hgeq]
      exact hprod lg (fun u hu => hlg u hu) (hgeq ▸ hgne)
    rw [hRf, hRg, map_one, one_mul]
  · -- the degree-0 exponent group is ℤ = ⟨z⟩: (X, C 2) realizes position difference 1
    rw [eq_top_iff]
    intro n _
    have h1 : (1 : ℤ) ∈ {n : ℤ | ∃ (f g : Polynomial ℤ_[2]) (c c' : ↥bStageP.K) (k k' : ℤ),
        IsUnitMonProd bStageP f ∧ IsUnitMonProd bStageP g ∧ f ≠ 0 ∧ g ≠ 0 ∧
        bStageP.w f = bStageP.w g ∧
        bStageP.R f = LaurentPolynomial.C c * LaurentPolynomial.T k ∧
        bStageP.R g = LaurentPolynomial.C c' * LaurentPolynomial.T k' ∧ n = k - k'} := by
      refine ⟨X, Polynomial.C 2, 1, 1, 1, 0, ?_, ?_, X_ne_zero,
        Polynomial.C_ne_zero.mpr HK13R.two_ne_zero', ?_, ?_, ?_, by ring⟩
      · exact ⟨[], 1, fun u hu => absurd hu (List.not_mem_nil),
          by rw [List.prod_nil, one_mul, bStageP_Phi_def, pow_one]⟩
      · refine ⟨[Polynomial.C 2], 0, ?_, by simp⟩
        intro u hu
        rw [List.mem_singleton] at hu
        subst hu
        exact ⟨Polynomial.C_ne_zero.mpr HK13R.two_ne_zero', HK13R.inC_C⟩
      · exact HK13R.bw_X.trans HK13R.bw_C2.symm
      · have hR : bStageP.R (X : Polynomial ℤ_[2]) = LaurentPolynomial.T 1 := HK13R.bR_X
        rw [hR, map_one, one_mul]
      · have hR : bStageP.R (Polynomial.C (2 : ℤ_[2])) = 1 := HK13R.bR_C2
        rw [hR, map_one, one_mul, LaurentPolynomial.T_zero]
    rw [show n = n • (1 : ℤ) by simp]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure h1) n

end LeanUrat.MovesJ
