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
# Moves/L5_landVertexDigit — the VERTEX explicit digit (§B2-DEF D.8, pass-10 finding 2)

`R(f) = ψ^μ·q` with `ψ ∤ q` (the ψ-free part), and the pinned VERTEX digit carries its
EXPLICIT normalization unit `z̄^{−μm̂} = z̄^{μthg}` (m̂ = −thg):

  `dig'(B_μ) = z̄^{μthg}·(q mod ψ)`.

## Status of the three parts — ALL PROVEN (sorry-free)

* **Part 1** (`R f = ψ^μ·q`) — the z-anchored ψ-order read-off. From
  `HasAnchorK (R f) a Ranch` and `OrdPsiPoly ψ Ranch μ` we get `Ranch = ψ^μ·R'`, `ψ ∤ R'`,
  and `q := T a · toLaurent R'`.
* **Part 2** (`ψ ∤ q`) — the toLaurent-divisibility transfer of `L2_psiNotDvd`
  (cancel the unit `T a`, clear `X`-denominators via `exists_T_pow`, reflect to `↥K[X]` by
  `toLaurent_injective`; `ψ` prime and `ψ ∤ X` since `ψ ≠ X` monic irreducible).
* **Part 3** (the explicit-unit digit identity) — via the private core `vertexCongruence`,
  now DISCHARGED in-file (the formerly honest `sorry`, closed per MANIFEST_REPAIR
  `L5.landVertexDigit`; proof ported verbatim from the verified
  `L5_landVertexDigit_repair.lean`): the K1 minimizing-slot congruence
  `q ≡ z^{μm̂}·R(B_μ) (mod ψ)` in `↥K[z^{±1}]`, `m̂ = −thg`.  Given the congruence, the
  evaluation layer: `eval₂` at the root `z̄` kills the `ψ`-multiple (`hzbar`),
  `eval₂(T μm̂) = z̄^{−μthg}` (mathlib `LaurentPolynomial.eval₂_T`), and the unit
  cancellation `z̄^{μthg}·z̄^{−μthg} = 1` produces exactly the pinned digit with its explicit
  normalization unit — pass-10 finding 2, NOT dropped.

## The discharge of the private core (formerly "the honest gap")

`vertexCongruence` is the residual minimizing-slot content of the deps `L5.landVertex` +
`L3.K1` (D.8 VERTEX / D.5 K1): `R(f) = Σ_{minimizing j} T^{jm̂}·R(B_j)·ψ^j` with pairwise
distinct ψ-orders, `μ` = least minimizing slot, so dividing by `ψ^μ` leaves
`T^a·R' = T^{μm̂}·R(B_μ) + ψ·r`.  Both dep units `L3.K1` and `L5.landVertex` are CLEAN
(sorry-free) on disk (2026-07-26 census §5); their residual minimizing-slot engine —
the residual-sum machine, the ψ-freeness of slot residuals via `L2_widthBound`, and the
GRf-style ψ-order reading — is carried as private helpers below (`L3_liftWeight`
reproduced verbatim as `w_Phat` — historical rationale: the original's `.olean`
was not yet built when this unit was written; it NOW builds (verified 2026-07-30 verify-2
fold-in: `L3_liftWeight.olean` on disk, full build green), the import remains un-taken for
historical reasons, and the duplication is tracked as Class-D).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

open Polynomial LeanUrat.Moves.LaurentOrd LeanUrat.Moves.ResVal

namespace LeanUrat.Moves

/-- The VERTEX ψ-congruence.  Deps `L3.K1` + `L5.landVertex` are CLEAN (sorry-free) on disk;
their residual minimizing-slot engine is cribbed above as private helpers.  From
`R(f) = Σ_{minimizing l} R(B l)·z^{lm̂}·ψ^l` (`m̂ = −t·h·g`) with `μ` the LEAST minimizing
slot (ψ-order read-off), dividing by `ψ^μ` isolates the μ-slot mod `ψ`. -/
private theorem vertexCongruence {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic)
    (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p])
    (hlift : IsStandardLift σ ψ g Φhat) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ)
    (Ranch : Polynomial ↥σ.K) (hanch : HasAnchorK (σ.R f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N)
    (R' : Polynomial ↥σ.K) (hR' : Ranch = ψ ^ μ * R') :
    ∃ r : LaurentPolynomial ↥σ.K,
      LaurentPolynomial.T a * Polynomial.toLaurent R' =
        LaurentPolynomial.T ((μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ))) * σ.R (B μ) +
          Polynomial.toLaurent ψ * r := by
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
  -- μ is the LEAST minimizing slot; divide the resSum decomposition `hRf2` by ψ^μ
  set M := ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => σ.w (B j * Φhat ^ j) = σ.w (B jmin * Φhat ^ jmin)) with hMdef
  have hge : ∀ l ∈ M, μ ≤ l := by
    intro l hl; rw [← hj0μ]; exact Finset.min'_le M l hl
  refine ⟨∑ l ∈ M.erase μ,
      (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
        * (Polynomial.toLaurent ψ) ^ (l - μ - 1), ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero μ hΨne)
  have hLHS : (Polynomial.toLaurent ψ) ^ μ
        * (LaurentPolynomial.T a * Polynomial.toLaurent R') = σ.R f := by
    rw [hanch_eq, hR', map_mul, map_pow]; ring
  have hRHS : (Polynomial.toLaurent ψ) ^ μ *
      (LaurentPolynomial.T ((μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ))) * σ.R (B μ)
        + Polynomial.toLaurent ψ *
            ∑ l ∈ M.erase μ,
              (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
                * (Polynomial.toLaurent ψ) ^ (l - μ - 1)) = σ.R f := by
    rw [mul_add]
    have hterm : (Polynomial.toLaurent ψ) ^ μ
          * (LaurentPolynomial.T ((μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ))) * σ.R (B μ))
        = (σ.R (B μ) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ μ)
            * (Polynomial.toLaurent ψ) ^ μ := by
      rw [LaurentPolynomial.T_pow]; ring
    have htail : (Polynomial.toLaurent ψ) ^ μ *
          (Polynomial.toLaurent ψ *
            ∑ l ∈ M.erase μ,
              (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
                * (Polynomial.toLaurent ψ) ^ (l - μ - 1))
        = ∑ l ∈ M.erase μ,
            (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
              * (Polynomial.toLaurent ψ) ^ l := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      have hlgt : μ < l := by
        have hlM := Finset.mem_of_mem_erase hl
        have hlne := Finset.ne_of_mem_erase hl
        have := hge l hlM; omega
      rw [show (Polynomial.toLaurent ψ) ^ μ *
              (Polynomial.toLaurent ψ *
                ((σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
                  * (Polynomial.toLaurent ψ) ^ (l - μ - 1)))
            = (σ.R (B l) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ l)
                * ((Polynomial.toLaurent ψ) ^ μ * (Polynomial.toLaurent ψ) ^ 1
                  * (Polynomial.toLaurent ψ) ^ (l - μ - 1)) from by rw [pow_one]; ring,
          ← pow_add, ← pow_add, show μ + 1 + (l - μ - 1) = l from by omega]
    rw [hterm, htail]
    refine Eq.trans ?_ hRf2.symm
    exact Finset.add_sum_erase M
      (fun x => σ.R (B x) * (LaurentPolynomial.T (- σ.t * (σ.h : ℤ) * (g : ℤ))) ^ x
        * (Polynomial.toLaurent ψ) ^ x) hμM
  rw [hLHS, hRHS]
theorem L5_landVertexDigit {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ) (Ranch : Polynomial ↥σ.K) (hanch : HasAnchorK (σ.R f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N) : ∃ q : LaurentPolynomial ↥σ.K, σ.R f = (Polynomial.toLaurent ψ) ^ μ * q ∧ ¬ (Polynomial.toLaurent ψ ∣ q) ∧ σ.digPrime zbar (B μ) = ((zbar ^ ((μ : ℤ) * σ.t * (σ.h : ℤ) * (g : ℤ)) : Fˣ) : F) * LaurentPolynomial.eval₂ σ.K.subtype zbar q := by
  classical
  -- the z-anchored ψ-order factorization `Ranch = ψ^μ · R'`, `ψ ∤ R'`
  obtain ⟨R', hR'⟩ := hord.1
  have hR'notdvd : ¬ (ψ ∣ R') := by
    intro ⟨R'', hR''⟩
    exact hord.2 ⟨R'', by rw [hR', hR'', pow_succ]; ring⟩
  -- the witness: the ψ-free part `q = T a · toLaurent R'`
  refine ⟨LaurentPolynomial.T a * Polynomial.toLaurent R', ?_, ?_, ?_⟩
  · -- Part 1: `R f = ψ^μ · q`
    rw [hanch.2, hR', map_mul, map_pow]; ring
  · -- Part 2: `ψ ∤ q`  (toLaurent-divisibility transfer, cf. L2_psiNotDvd)
    intro hdvd
    -- divide out the unit `T a`, then reflect to `↥K[X]` via the transfer helper
    have hdvdR : Polynomial.toLaurent ψ ∣ Polynomial.toLaurent R' :=
      dvd_of_dvd_T_mul _ _ _ hdvd
    have h := toLaurent_pow_dvd_transfer ψ hmon hψ hψz 1 R' (by rwa [pow_one])
    rw [pow_one] at h
    exact hR'notdvd h
  · -- Part 3: the explicit-unit VERTEX digit identity, from the private congruence core:
    -- evaluate `T^a·R' = T^{μm̂}·R(B_μ) + ψ·r` at the root `z̄` and cancel the unit.
    obtain ⟨r, hcong⟩ := vertexCongruence σ ψ g hg hmon hψ hψz Φhat hlift f hf μ a Ranch
      hanch hord B N hdev R' hR'
    -- the root kills the ψ-multiple
    have hψ0 : LaurentPolynomial.eval₂ σ.K.subtype zbar (Polynomial.toLaurent ψ) = 0 := by
      rw [LaurentPolynomial.eval₂_toLaurent]; exact hzbar
    -- evaluate the congruence: `eval(q) = z̄^{μm̂}·dig'(B_μ)`, `m̂ = −thg`
    have heval : LaurentPolynomial.eval₂ σ.K.subtype zbar
        (LaurentPolynomial.T a * Polynomial.toLaurent R') =
        ((zbar ^ ((μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ))) : Fˣ) : F) *
          σ.digPrime zbar (B μ) := by
      rw [hcong, map_add, map_mul, map_mul, hψ0, zero_mul, add_zero,
        LaurentPolynomial.eval₂_T, Stage.digPrime]
    -- the explicit normalization unit: `z̄^{μthg} · z̄^{−μthg} = 1`
    have hunit : zbar ^ ((μ : ℤ) * σ.t * (σ.h : ℤ) * (g : ℤ)) *
        zbar ^ ((μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ))) = 1 := by
      rw [← zpow_add,
        show (μ : ℤ) * σ.t * (σ.h : ℤ) * (g : ℤ) +
          (μ : ℤ) * (- σ.t * (σ.h : ℤ) * (g : ℤ)) = 0 by ring, zpow_zero]
    rw [heval, ← mul_assoc, ← Units.val_mul, hunit, Units.val_one, one_mul]
end LeanUrat.Moves
