/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.L3_liftResidual
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L2_widthBound
import LeanUrat.Moves.LaurentOrd
import LeanUrat.Moves.ResVal

/-!
# Moves/L5_landVertex — D.8 (VERTEX): the pinned child vertex (MOVES ~2323-2338)

On the descend stratum at `ψ` with multiplicity `μ`, i.e. `f` with `ord_ψ R(f) = μ` (read on the
`z`-anchored `Ranch`, `R(f) = z^a·Ranch`, `ψ^μ ∥ Ranch`), the `Φ̂`-development of `f` has slot
`μ` MINIMIZING and nonzero: `w(B_μ) + μ·(ehg) = w(f)` and `B_μ ≠ 0`.

## Proof structure (fully closed — no `sorry`)

* **The residual-sum machine** (`residual_sum_machine`): for terms of a common weight `m` whose
  residuals can never satisfy `R(a_j) = u·Σ_{l∈T} R(a_l)` (`u² = 1`), every sub-sum is nonzero of
  weight `m` with residual the sum of residuals.  The cancellation cases are killed by an ε-trick:
  if `w(a_j + S) > m` (or `a_j + S = 0`) then `hRlt` applied to `-S` and `a_j + S` (resp. `R` of
  `a_j = -S`) forces `R(a_j) = R(-1)·R(S)` with `R(-1)² = R(1) = 1` — exactly the excluded shape.
* **ψ-freeness of slot residuals** (`psiNotDvd`): `deg B < deg Φ̂ = eg·deg Φ` puts the
  support of `R(B)` in a window of width `< g` (`L2_widthBound`), so its `z`-anchored polynomial
  has degree `< g = deg ψ`; a `toLaurent`-divisibility transfer (`toLaurent_pow_dvd_transfer`,
  using `ψ` prime in `K[z]` and `ψ ∤ z`) then forbids `ψ ∣ R(B)`.
* **Order pinning**: `R(f) = Σ_{minimizing j} (R(B_j)·z^{jm̂})·ψ^j`, terms of pairwise-distinct
  ψ-order (each cofactor ψ-free); factoring out `ψ^{min}` GRf-style gives `ord_ψ R(f) = ` least
  minimizing slot; the anchored hypothesis pins it to `μ`, so slot `μ` is minimizing and nonzero.

The separation hypothesis of the machine is itself discharged by the ψ-order comparison, so the
whole argument is self-contained over the `Stage` axioms plus the shared engine.

## SYN-M2 record (2026-07-30, C1 cluster)

The file-private engine block (w_one' … R_pow', w_sum_ge', residual_sum_machine, the Laurent
toolkit, psiNotDvd_local, liftWeight_local — BYTE-IDENTICAL to `L5_landVertexDigit`'s block,
golf Moves#7's mirrored-edits drift risk now RETIRED) is deleted in favor of
`Moves/LaurentOrd.lean` + `Moves/ResVal.lean` (SYN-E0 concordance:
`lean/notes/SYN_E0_CONCORDANCE_2026-07-30.md`). Per-conjunct equivalences: all statements
identical per the table (primed names α-renamed) except (a) `psiNotDvd_local` →
`ResVal.psiNotDvd`, which drops the redundant `hg1` hypothesis (derivable; supplied no longer —
call sites drop the argument, SYN-E0 §3 VAR-H); (b) `liftWeight_local` → `ResVal.w_Phat`
(pure rename; this also RESOLVES the historical Class-D `L3_liftWeight` duplication note —
the shared module is now the single proof source). Public statement `L5_landVertex`
byte-identical.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Moves

open Polynomial LaurentOrd ResVal


theorem L5_landVertex {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ) (Ranch : Polynomial ↥σ.K) (hanch : HasAnchorK (σ.R f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N) : σ.w (B μ) + (μ : ℤ) * ((σ.e : ℤ) * σ.h * g) = σ.w f ∧ B μ ≠ 0 := by
  classical
  -- `g ≥ 1` from irreducibility
  have hg1 : 1 ≤ g := by
    rw [← hg]
    exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hψ)
  -- lift facts
  obtain ⟨hΦhatmon, hΦhatdeg⟩ := L3_liftMonic σ ψ g hg1 Φhat hlift
  have hΦhatne : Φhat ≠ 0 := hΦhatmon.ne_zero
  have hwhat : σ.w Φhat = (σ.e : ℤ) * σ.h * g := w_Phat σ ψ g hg1 Φhat hlift hΦhatne
  have hΨne : (Polynomial.toLaurent ψ : LaurentPolynomial ↥σ.K) ≠ 0 := fun h =>
    hψ.ne_zero (Polynomial.toLaurent_injective (by rw [map_zero]; exact h))
  obtain ⟨hdevdeg, hdevzero, hdevsum⟩ := hdev
  -- the nonzero slots
  have hfsupp : f = ∑ j ∈ (Finset.range N).filter (fun j => B j ≠ 0), B j * Φhat ^ j := by
    rw [hdevsum]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro j hj hne hBj
    exact hne (by rw [hBj, zero_mul])
  have hsuppne : ((Finset.range N).filter (fun j => B j ≠ 0)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    exact hf (by rw [hfsupp, hemp, Finset.sum_empty])
  have hsuppB : ∀ j ∈ (Finset.range N).filter (fun j => B j ≠ 0), B j ≠ 0 :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have ha'ne : ∀ j ∈ (Finset.range N).filter (fun j => B j ≠ 0), B j * Φhat ^ j ≠ 0 :=
    fun j hj => mul_ne_zero (hsuppB j hj) (pow_ne_zero j hΦhatne)
  have ha'w : ∀ j ∈ (Finset.range N).filter (fun j => B j ≠ 0),
      σ.w (B j * Φhat ^ j) = σ.w (B j) + (j : ℤ) * ((σ.e : ℤ) * σ.h * g) := by
    intro j hj
    rw [σ.hwmul _ _ (hsuppB j hj) (pow_ne_zero j hΦhatne), w_pow σ Φhat hΦhatne j, hwhat]
  -- the attained minimum over nonzero slots
  obtain ⟨jmin, hjminmem, hjminle⟩ :=
    Finset.exists_min_image ((Finset.range N).filter (fun j => B j ≠ 0))
      (fun j => σ.w (B j * Φhat ^ j)) hsuppne
  -- the minimizing set M
  have hMsub : ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin))
      ⊆ (Finset.range N).filter (fun j => B j ≠ 0) := Finset.filter_subset _ _
  have hMne : (((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin))).Nonempty :=
    ⟨jmin, Finset.mem_filter.mpr ⟨hjminmem, rfl⟩⟩
  -- residual normal form of the slot terms
  have hRterm : ∀ j ∈ (Finset.range N).filter (fun j => B j ≠ 0),
      σ.R (B j * Φhat ^ j)
        = (σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j) *
            (Polynomial.toLaurent ψ) ^ j := by
    intro j hj
    rw [σ.hRmul _ _ (hsuppB j hj) (pow_ne_zero j hΦhatne), R_pow σ Φhat hΦhatne j,
      L3_liftResidual σ ψ g Φhat hlift, mul_pow]
    ring
  -- ψ-freeness of the slot cofactors
  have hcne : ∀ j ∈ (Finset.range N).filter (fun j => B j ≠ 0),
      (σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j) ≠ 0 ∧
        ¬ (Polynomial.toLaurent ψ ∣
            σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j) := by
    intro j hj
    have hBj : B j ≠ 0 := hsuppB j hj
    have hRBne : σ.R (B j) ≠ 0 := σ.hRne _ hBj
    have hTu : ((LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ)) :
        LaurentPolynomial ↥σ.K)) ^ j ≠ 0 :=
      ((LaurentPolynomial.isUnit_T _).pow j).ne_zero
    refine ⟨mul_ne_zero hRBne hTu, fun hdvd => ?_⟩
    rw [LaurentPolynomial.T_pow] at hdvd
    have hdvd2 : Polynomial.toLaurent ψ ∣ σ.R (B j) :=
      dvd_of_dvd_mul_T _ _ _ hdvd
    have hBdeg : (B j).natDegree < σ.e * g * σ.Φ.natDegree := by
      have h1 := Polynomial.natDegree_lt_natDegree hBj (hdevdeg j)
      omega
    exact psiNotDvd σ ψ g hg hmon hψ hψz (B j) hBj hBdeg hdvd2
  -- separation: distinct ψ-orders forbid `R(a_j) = u·Σ R(a_l)`
  have hsep : ∀ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
      ∀ T ⊆ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
      T.Nonempty → j ∉ T → ∀ u : LaurentPolynomial ↥σ.K, u * u = 1 →
        σ.R (B j * Φhat ^ j) ≠ u * ∑ l ∈ T, σ.R (B l * Φhat ^ l) := by
    intro j hjM T hTM hTne hjT u hu2 heq
    have hjsupp : j ∈ (Finset.range N).filter (fun j => B j ≠ 0) := hMsub hjM
    have hTsupp : ∀ l ∈ T, l ∈ (Finset.range N).filter (fun j => B j ≠ 0) :=
      fun l hl => hMsub (hTM hl)
    have hune : u ≠ 0 := left_ne_zero_of_mul_eq_one hu2
    have hRHS : u * ∑ l ∈ T, σ.R (B l * Φhat ^ l)
        = ∑ l ∈ T, (u * (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)) *
            (Polynomial.toLaurent ψ) ^ l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      rw [hRterm l (hTsupp l hl)]
      ring
    have hcond : ∀ l ∈ T,
        (u * (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)) ≠ 0 ∧
          ¬ (Polynomial.toLaurent ψ ∣
            u * (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)) := by
      intro l hl
      obtain ⟨h1, h2⟩ := hcne l (hTsupp l hl)
      refine ⟨mul_ne_zero hune h1, fun hdvd => h2 ?_⟩
      have h3 := hdvd.mul_left u
      rwa [← mul_assoc, hu2, one_mul] at h3
    have horderT := psi_order_of_sum (Polynomial.toLaurent ψ) hΨne
      (fun l => u * (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l))
      T hTne hcond
    have hLHS : σ.R (B j * Φhat ^ j)
        = (σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j) *
            (Polynomial.toLaurent ψ) ^ j := hRterm j hjsupp
    have hLup : (Polynomial.toLaurent ψ) ^ j ∣ σ.R (B j * Φhat ^ j) := by
      rw [hLHS]
      exact dvd_mul_left _ _
    have hLdown : ¬ (Polynomial.toLaurent ψ) ^ (j + 1) ∣ σ.R (B j * Φhat ^ j) := by
      rw [hLHS]
      intro hdvd
      rw [pow_succ] at hdvd
      have h4 : (Polynomial.toLaurent ψ) ^ j * (Polynomial.toLaurent ψ) ∣
          (Polynomial.toLaurent ψ) ^ j *
            (σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j) := by
        rwa [mul_comm ((Polynomial.toLaurent ψ) ^ j)
          (σ.R (B j) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ j)]
      exact (hcne j hjsupp).2 ((mul_dvd_mul_iff_left (pow_ne_zero j hΨne)).mp h4)
    rw [heq, hRHS] at hLup hLdown
    have hj_eq : j = T.min' hTne :=
      pow_order_unique (Polynomial.toLaurent ψ) _ j (T.min' hTne)
        hLup hLdown horderT.1 horderT.2
    exact hjT (hj_eq ▸ T.min'_mem hTne)
  -- the machine on the minimizing set
  obtain ⟨hMsum_ne, hMsum_w, hMsum_R⟩ :=
    residual_sum_machine σ (σ.w (B jmin * Φhat ^ jmin)) (fun j => B j * Φhat ^ j)
      (((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)))
      (fun j hj => ha'ne j (hMsub hj))
      (fun j hj => (Finset.mem_filter.mp hj).2)
      hsep _ Finset.Subset.rfl hMne
  -- split off the strictly heavier slots and conclude `w f = m`, `R f = Σ_M R`
  have hsplitsum :
      (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
          (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
        + (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
          (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
        = ∑ j ∈ (Finset.range N).filter (fun j => B j ≠ 0), B j * Φhat ^ j :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hwf_and_Rf : σ.w f = σ.w (B jmin * Φhat ^ jmin) ∧
      σ.R f = ∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
          σ.R (B j * Φhat ^ j) := by
    by_cases hrest0 : (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j) = 0
    · have hfeq : f = ∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
          (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j := by
        rw [hfsupp, ← hsplitsum, hrest0, add_zero]
      rw [hfeq]
      exact ⟨hMsum_w, hMsum_R⟩
    · have hrest_ge : σ.w (B jmin * Φhat ^ jmin) + 1 ≤
          σ.w (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j) := by
        refine w_sum_ge σ _ _ _ (fun j hj _ => ?_) hrest0
        obtain ⟨hjsupp, hjne⟩ := Finset.mem_filter.mp hj
        have := hjminle j hjsupp
        omega
      have hfeq : f = (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
          + (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j) := by
        rw [hfsupp, hsplitsum]
      have hfne' : (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
          + (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
          ≠ 0 := by rw [← hfeq]; exact hf
      constructor
      · -- weight
        have hlow := σ.hwult _ _ hMsum_ne hrest0 hfne'
        rw [hMsum_w] at hlow
        have hup : σ.w f ≤ σ.w (B jmin * Φhat ^ jmin) := by
          by_contra hgt
          rw [not_le] at hgt
          have hne2 : -(∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
                B j * Φhat ^ j) ≠ 0 := neg_ne_zero.mpr hrest0
          have heq2 : f + -(∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
              = ∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
                (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
                  B j * Φhat ^ j := by
            rw [hfeq]; ring
          have h5 := σ.hwult f _ hf hne2 (by rw [heq2]; exact hMsum_ne)
          rw [heq2, hMsum_w, w_neg σ _ hrest0] at h5
          rcases min_choice (σ.w f)
            (σ.w (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
                B j * Φhat ^ j)) with hc | hc <;> rw [hc] at h5 <;> omega
        have hlow2 : σ.w (B jmin * Φhat ^ jmin) ≤ σ.w f := by
          have h6 : min (σ.w (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
                (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)), B j * Φhat ^ j))
              (σ.w (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
                (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
                  B j * Φhat ^ j)) ≤ σ.w f := by
            have h7 := σ.hwult _ _ hMsum_ne hrest0 hfne'
            rw [← hfeq] at h7
            exact h7
          rw [hMsum_w] at h6
          rcases min_choice (σ.w (B jmin * Φhat ^ jmin))
            (σ.w (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
                B j * Φhat ^ j)) with hc | hc <;> rw [hc] at h6 <;> omega
        omega
      · -- residual
        have h7 := σ.hRlt _ _ hMsum_ne hrest0 hfne' (by rw [hMsum_w]; omega)
        rw [← hfeq] at h7
        rw [h7, hMsum_R]
  obtain ⟨hwfm, hRf⟩ := hwf_and_Rf
  -- `R f` in `c·Ψ^order` normal form over M
  have hRf2 : σ.R f = ∑ l ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)),
        (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l) *
          (Polynomial.toLaurent ψ) ^ l := by
    rw [hRf]
    exact Finset.sum_congr rfl (fun l hl => hRterm l (hMsub hl))
  have horder := psi_order_of_sum (Polynomial.toLaurent ψ) hΨne
    (fun l => σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
    _ hMne (fun l hl => hcne l (hMsub hl))
  rw [← hRf2] at horder
  -- the anchored ψ-order reading: exactly μ
  obtain ⟨hRanch0, hanch_eq⟩ := hanch
  obtain ⟨horddvd, hordndvd⟩ := hord
  have hμup : (Polynomial.toLaurent ψ) ^ μ ∣ σ.R f := by
    rw [hanch_eq]
    have h8 := map_dvd (Polynomial.toLaurent (R := ↥σ.K)) horddvd
    rw [map_pow] at h8
    exact h8.mul_left _
  have hμdown : ¬ (Polynomial.toLaurent ψ) ^ (μ + 1) ∣ σ.R f := by
    intro hdvd
    rw [hanch_eq] at hdvd
    have h9 : (Polynomial.toLaurent ψ) ^ (μ + 1) ∣ Polynomial.toLaurent Ranch :=
      dvd_of_dvd_T_mul _ _ _ hdvd
    exact hordndvd (toLaurent_pow_dvd_transfer ψ hmon hψ hψz (μ + 1) Ranch h9)
  -- pin μ = least minimizing slot
  have hj0μ : (((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin))).min' hMne = μ :=
    pow_order_unique (Polynomial.toLaurent ψ) (σ.R f) _ μ horder.1 horder.2 hμup hμdown
  have hμM : μ ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)) :=
    hj0μ ▸ Finset.min'_mem _ hMne
  obtain ⟨hμsupp, hμmin⟩ := Finset.mem_filter.mp hμM
  have hμne : B μ ≠ 0 := (Finset.mem_filter.mp hμsupp).2
  refine ⟨?_, hμne⟩
  have h10 := ha'w μ hμsupp
  rw [hμmin] at h10
  omega

end LeanUrat.Moves
