/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.V3_readLift

/-!
# HC1.V4_readLanding — (BOX)+(VERTEX) at the ReadFrame (blueprint §10, V4)

V'-KERNEL unit (blueprint §10.1): for `f ≠ 0` with anchored RV-data of ψ-order `μ`,
the Φ̂-development satisfies (VERTEX) `wV(B_μ) + μ·e★h★g = wV(f)` with `B_μ ≠ 0`;
(BOX) `wV(B_m) + m·e★h★g > wV(f)` for every `m < μ` with `B_m ≠ 0`; and the vertex
digit with its explicit unit `z̄^{μ·t★·h★·g}`.

moves_ref: D.8 (BOX)/(VERTEX) VERBATIM (MOVES 2469–2490).  The Lean pattern
`L5_landVertex`/`L5_landBox`/`L5_landVertexDigit` transplanted to the ReadFrame pack:
the D.5 lift facts (`wV(Φ̂)`, `RV(Φ̂)=T(−t★h★g)·ψ`) come from `V3_readLift`; the
no-cancellation core is `v3_minsum_facts`/`v3_key_no_cancel`, the width/ψ-freeness is
`v3_psiNotDvd`, all re-derived here as private lemmas (verbatim copies of the V3-kernel
closure, which is file-private in V3) plus the field-generic ψ-order helpers from
`Moves/L5_landVertex`.  ALL THREE legs run off ONE shared minimizing-slot decomposition.

**FENCE (per §10.1): the (TRANSPORT) leg is NOT needed by any of the three discharges —
it is fenced OUT of this unit.**  Consumes NOTHING beyond the ReadFrame pack; no axioms,
no `native_decide`, no `sorry`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesJ
open LeanUrat.Moves.LaurentOrd


/-- Unit V4: the D.8 landing at the ReadFrame — (VERTEX), (BOX), and the vertex digit
with its explicit unit `z̄^{μ·t★·h★·g}`, transposing `L5_landVertex`/`L5_landBox`/
`L5_landVertexDigit` to the regrade pack.  The (TRANSPORT) leg is fenced OUT (see header). -/
theorem V4_readLanding {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar)
    (V : ReadFrame σ estar hstar sstar tstar)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hdeg : ψ.natDegree = g) (hmon : ψ.Monic)
    (hirr : Irreducible ψ) (hne : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g estar hstar Φhat)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ)
    (Ranch : Polynomial ↥σ.K)
    (hanch : HasAnchorK (V.D.Rv f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N) :
    (B μ ≠ 0 ∧
      childW σ σ.Φ estar hstar (B μ)
          + (μ : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))
        = childW σ σ.Φ estar hstar f) ∧
    (∀ m, m < μ → B m ≠ 0 →
      childW σ σ.Φ estar hstar f
        < childW σ σ.Φ estar hstar (B m)
            + (m : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ))) ∧
    (∀ zbar : Fˣ, Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 →
      ∃ q : LaurentPolynomial ↥σ.K,
        V.D.Rv f = (Polynomial.toLaurent ψ) ^ μ * q ∧
        ¬ (Polynomial.toLaurent ψ ∣ q) ∧
        LaurentPolynomial.eval₂ σ.K.subtype (zbar : Fˣ) (V.D.Rv (B μ))
          = ((zbar ^ ((μ : ℤ) * tstar * (hstar : ℤ) * (g : ℤ)) : Fˣ) : F) *
            LaurentPolynomial.eval₂ σ.K.subtype (zbar : Fˣ) q) := by
  classical
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := V.laws
  have hee : 1 ≤ estar := hrp.1
  have hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 := hrp.2.2.2.1
  have hg1 : 1 ≤ g := by rw [← hdeg]; exact hirr.natDegree_pos
  obtain ⟨-, hwhat, hRhat, -⟩ :=
    V3_readLift σ hσ estar hstar sstar tstar hrp V ψ g hmon hirr hne hdeg Φhat hlift
  obtain ⟨hΦmon, hΦdeg⟩ := v3_lift_monic hee ψ g hg1 Φhat hlift
  have hΦne : Φhat ≠ 0 := hΦmon.ne_zero
  have hΨne : (Polynomial.toLaurent ψ : LaurentPolynomial ↥σ.K) ≠ 0 := fun h =>
    hirr.ne_zero (Polynomial.toLaurent_injective (by rw [map_zero]; exact h))
  obtain ⟨hdegdev, hzerodev, hsumdev⟩ := hdev
  -- slot weight law
  have hwa : ∀ j, B j ≠ 0 →
      childW σ σ.Φ estar hstar (B j * Φhat ^ j)
        = childW σ σ.Φ estar hstar (B j) + (j : ℤ) * ((estar : ℤ) * (hstar : ℤ) * (g : ℤ)) := by
    intro j hBj
    rw [V.hwmul _ _ hBj (pow_ne_zero j hΦne), v3_wv_pow V Φhat hΦne j, hwhat]
  -- slot residual normal form  RV(B_j Φ̂^j) = (RV(B_j)·T(m̂)^j)·ψ^j,  m̂ = −t★h★g
  have hRterm : ∀ j, B j ≠ 0 →
      V.D.Rv (B j * Φhat ^ j)
        = (V.D.Rv (B j) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ j)
            * (Polynomial.toLaurent ψ) ^ j := by
    intro j hBj
    rw [hRmul _ _ hBj (pow_ne_zero j hΦne), v3_rv_pow V Φhat hΦne j, hRhat, mul_pow]; ring
  -- ψ-freeness of each slot cofactor
  have hcne : ∀ j, B j ≠ 0 →
      (V.D.Rv (B j) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ j) ≠ 0 ∧
        ¬ (Polynomial.toLaurent ψ ∣
            V.D.Rv (B j) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ j) := by
    intro j hBj
    have hRBne : V.D.Rv (B j) ≠ 0 := hRne _ hBj
    have hTu : ((LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) :
        LaurentPolynomial ↥σ.K)) ^ j ≠ 0 :=
      ((LaurentPolynomial.isUnit_T _).pow j).ne_zero
    refine ⟨mul_ne_zero hRBne hTu, fun hdvd => ?_⟩
    rw [LaurentPolynomial.T_pow] at hdvd
    have hdvd2 : Polynomial.toLaurent ψ ∣ V.D.Rv (B j) := dvd_of_dvd_mul_T _ _ _ hdvd
    have hBdeg : (B j).natDegree < estar * g * σ.Φ.natDegree := by
      have h1 := Polynomial.natDegree_lt_natDegree hBj (hdegdev j)
      rw [hΦdeg] at h1; exact h1
    exact v3_psiNotDvd V hee hbez ψ g hdeg hmon hirr hne (B j) hBj hBdeg hdvd2
  -- === shared minimizing-slot core ===
  have hfsupp : f = ∑ j ∈ (Finset.range N).filter (fun j => B j ≠ 0), B j * Φhat ^ j := by
    rw [hsumdev]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro j hj hne' hBj; exact hne' (by rw [hBj, zero_mul])
  have hsuppne : ((Finset.range N).filter (fun j => B j ≠ 0)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hemp
    exact hf (by rw [hfsupp, hemp, Finset.sum_empty])
  have hsuppB : ∀ j ∈ (Finset.range N).filter (fun j => B j ≠ 0), B j ≠ 0 :=
    fun j hj => (Finset.mem_filter.mp hj).2
  obtain ⟨jmin, hjminmem, hjminle⟩ :=
    Finset.exists_min_image ((Finset.range N).filter (fun j => B j ≠ 0))
      (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)) hsuppne
  have hMsub : ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
        = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin))
      ⊆ (Finset.range N).filter (fun j => B j ≠ 0) := Finset.filter_subset _ _
  have hMne : (((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
        = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin))).Nonempty :=
    ⟨jmin, Finset.mem_filter.mpr ⟨hjminmem, rfl⟩⟩
  have hMB : ∀ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
        = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j ≠ 0 :=
    fun j hj => hsuppB j (hMsub hj)
  have hMw : ∀ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
        = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)),
      childW σ σ.Φ estar hstar (B j * Φhat ^ j)
        = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin) :=
    fun j hj => (Finset.mem_filter.mp hj).2
  obtain ⟨hMsum_ne, hMsum_w, hMsum_R⟩ :=
    v3_minsum_facts V hee hbez ψ g hdeg hmon hirr hne Φhat hΦne hRhat hΦdeg B hdegdev
      (childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin))
      (((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
          = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)))
      hMB hMw hMne
  have hsplitsum :
      (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
          (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
            = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
        + (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
          (fun j => ¬ childW σ σ.Φ estar hstar (B j * Φhat ^ j)
            = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
        = ∑ j ∈ (Finset.range N).filter (fun j => B j ≠ 0), B j * Φhat ^ j :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hwf_and_Rf : childW σ σ.Φ estar hstar f
        = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin) ∧
      V.D.Rv f = ∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
          = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)),
          V.D.Rv (B j * Φhat ^ j) := by
    by_cases hrest0 : (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
        (fun j => ¬ childW σ σ.Φ estar hstar (B j * Φhat ^ j)
          = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j) = 0
    · have hfeq : f = ∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
          (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
            = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j := by
        rw [hfsupp, ← hsplitsum, hrest0, add_zero]
      rw [hfeq]; exact ⟨hMsum_w, hMsum_R⟩
    · have hrest_ge : childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin) + 1 ≤
          childW σ σ.Φ estar hstar (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => ¬ childW σ σ.Φ estar hstar (B j * Φhat ^ j)
              = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j) := by
        refine v3_wv_sum_ge V _ _ _ (fun j hj _ => ?_) hrest0
        obtain ⟨hjsupp, hjne⟩ := Finset.mem_filter.mp hj
        have := hjminle j hjsupp
        omega
      have hfeq : f = (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
              = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
          + (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => ¬ childW σ σ.Φ estar hstar (B j * Φhat ^ j)
              = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j) := by
        rw [hfsupp, hsplitsum]
      have hfne' : (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
              = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
          + (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => ¬ childW σ σ.Φ estar hstar (B j * Φhat ^ j)
              = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j) ≠ 0 := by
        rw [← hfeq]; exact hf
      refine ⟨?_, ?_⟩
      · have hlow := V.hwult _ _ hMsum_ne hrest0 hfne'
        rw [hMsum_w] at hlow
        have hup : childW σ σ.Φ estar hstar f
            ≤ childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin) := by
          by_contra hgt
          rw [not_le] at hgt
          have hne2 : -(∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ childW σ σ.Φ estar hstar (B j * Φhat ^ j)
                = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)),
                B j * Φhat ^ j) ≠ 0 := neg_ne_zero.mpr hrest0
          have heq2 : f + -(∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ childW σ σ.Φ estar hstar (B j * Φhat ^ j)
                = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j)
              = ∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
                (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
                  = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j := by
            rw [hfeq]; ring
          have h5 := V.hwult f _ hf hne2 (by rw [heq2]; exact hMsum_ne)
          rw [heq2, hMsum_w, v3_wv_neg V _ hrest0] at h5
          rcases min_choice (childW σ σ.Φ estar hstar f)
            (childW σ σ.Φ estar hstar (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ childW σ σ.Φ estar hstar (B j * Φhat ^ j)
                = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)),
                B j * Φhat ^ j)) with hc | hc <;> rw [hc] at h5 <;> omega
        have hlow2 : childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)
            ≤ childW σ σ.Φ estar hstar f := by
          have h6 : min (childW σ σ.Φ estar hstar
                (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
                  (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
                    = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j))
              (childW σ σ.Φ estar hstar
                (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
                  (fun j => ¬ childW σ σ.Φ estar hstar (B j * Φhat ^ j)
                    = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)),
                    B j * Φhat ^ j)) ≤ childW σ σ.Φ estar hstar f := by
            have h7 := V.hwult _ _ hMsum_ne hrest0 hfne'
            rw [← hfeq] at h7
            exact h7
          rw [hMsum_w] at h6
          rcases min_choice (childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin))
            (childW σ σ.Φ estar hstar
              (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
                (fun j => ¬ childW σ σ.Φ estar hstar (B j * Φhat ^ j)
                  = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)),
                  B j * Φhat ^ j)) with hc | hc <;> rw [hc] at h6 <;> omega
        omega
      · have h7 := V.hwult _ _ hMsum_ne hrest0 hfne'
        rw [hMsum_w] at h7
        have h8 : childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)
            < childW σ σ.Φ estar hstar (∑ j ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
              (fun j => ¬ childW σ σ.Φ estar hstar (B j * Φhat ^ j)
                = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), B j * Φhat ^ j) := by
          omega
        have hR := hRlt _ _ hMsum_ne hrest0 hfne' (by rw [hMsum_w]; exact h8)
        rw [← hfeq] at hR
        rw [hR, hMsum_R]
  obtain ⟨hwfm, hRf⟩ := hwf_and_Rf
  -- RV f in the c·Ψ^order normal form over the minimizing set
  have hRf2 : V.D.Rv f = ∑ l ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
        = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)),
        (V.D.Rv (B l) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ l)
          * (Polynomial.toLaurent ψ) ^ l := by
    rw [hRf]
    exact Finset.sum_congr rfl (fun l hl => hRterm l (hMB l hl))
  have horder := psi_order_of_sum (Polynomial.toLaurent ψ) hΨne
    (fun l => V.D.Rv (B l) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ l)
    _ hMne (fun l hl => hcne l (hMB l hl))
  rw [← hRf2] at horder
  -- anchored ψ-order reading: exactly μ
  obtain ⟨hRanch0, hanch_eq⟩ := hanch
  obtain ⟨horddvd, hordndvd⟩ := hord
  have hμup : (Polynomial.toLaurent ψ) ^ μ ∣ V.D.Rv f := by
    rw [hanch_eq]
    have h8 := map_dvd (Polynomial.toLaurent (R := ↥σ.K)) horddvd
    rw [map_pow] at h8
    exact h8.mul_left _
  have hμdown : ¬ (Polynomial.toLaurent ψ) ^ (μ + 1) ∣ V.D.Rv f := by
    intro hdvd
    rw [hanch_eq] at hdvd
    have h9 : (Polynomial.toLaurent ψ) ^ (μ + 1) ∣ Polynomial.toLaurent Ranch :=
      dvd_of_dvd_T_mul _ _ _ hdvd
    exact hordndvd (toLaurent_pow_dvd_transfer ψ hmon hirr hne (μ + 1) Ranch h9)
  have hj0μ : (((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
        = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin))).min' hMne = μ :=
    pow_order_unique (Polynomial.toLaurent ψ) (V.D.Rv f) _ μ horder.1 horder.2 hμup hμdown
  have hμM : μ ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
      (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
        = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)) :=
    hj0μ ▸ Finset.min'_mem _ hMne
  obtain ⟨hμsupp, hμmin⟩ := Finset.mem_filter.mp hμM
  have hμne : B μ ≠ 0 := (Finset.mem_filter.mp hμsupp).2
  -- === the three legs ===
  refine ⟨⟨hμne, ?_⟩, ?_, ?_⟩
  · -- (VERTEX)
    rw [← hwa μ hμne, hμmin, ← hwfm]
  · -- (BOX)
    intro m' hm'μ hBm'
    have hm'N : m' < N := by
      by_contra h; exact hBm' (hzerodev m' (not_lt.mp h))
    have hm'SN : m' ∈ (Finset.range N).filter (fun j => B j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm'N, hBm'⟩
    have hle := hjminle m' hm'SN
    rw [hwa m' hBm'] at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [hwfm]; exact hlt
    · exfalso
      have hm'M : m' ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
          (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
            = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)) :=
        Finset.mem_filter.mpr ⟨hm'SN, by rw [hwa m' hBm']; exact heq.symm⟩
      have hcontra := Finset.min'_le _ m' hm'M
      rw [hj0μ] at hcontra
      omega
  · -- (VERTEX DIGIT)
    intro zbar hzbar
    obtain ⟨R', hR'⟩ := horddvd
    have hR'notdvd : ¬ (ψ ∣ R') := by
      rintro ⟨R'', hR''⟩
      exact hordndvd ⟨R'', by rw [hR', hR'', pow_succ]; ring⟩
    refine ⟨LaurentPolynomial.T a * Polynomial.toLaurent R', ?_, ?_, ?_⟩
    · rw [hanch_eq, hR', map_mul, map_pow]; ring
    · intro hdvd
      have hdvdR : Polynomial.toLaurent ψ ∣ Polynomial.toLaurent R' := by
        have h := hdvd.mul_left (LaurentPolynomial.T (-a))
        rwa [← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel,
          LaurentPolynomial.T_zero, one_mul] at h
      obtain ⟨qq, hq⟩ := hdvdR
      obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow qq
      have hkey : R' * Polynomial.X ^ n = ψ * f' := by
        apply Polynomial.toLaurent_injective
        rw [map_mul, map_mul, Polynomial.toLaurent_X_pow, hq, mul_assoc, ← hf']
      have hdiv : ψ ∣ R' * Polynomial.X ^ n := ⟨f', hkey⟩
      have hprime : Prime ψ := hirr.prime
      have hnotdvdX : ¬ (ψ ∣ Polynomial.X) := fun hdX =>
        hne (Polynomial.eq_of_monic_of_associated hmon Polynomial.monic_X
          (hirr.associated_of_dvd Polynomial.irreducible_X hdX))
      rcases hprime.dvd_or_dvd hdiv with h1 | h2
      · exact hR'notdvd h1
      · exact hnotdvdX (hprime.dvd_of_dvd_pow h2)
    · -- the explicit-unit digit identity via the minimizing-slot congruence
      have hTp : ∀ n : ℕ,
          (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ)) : LaurentPolynomial ↥σ.K) ^ n
            = LaurentPolynomial.T ((n : ℤ) * (- tstar * (hstar : ℤ) * (g : ℤ))) := by
        intro n
        induction n with
        | zero => simp
        | succ k ih => rw [pow_succ, ih, ← LaurentPolynomial.T_add]; congr 1; push_cast; ring
      have hge : ∀ l ∈ ((Finset.range N).filter (fun j => B j ≠ 0)).filter
          (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
            = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin)), μ ≤ l := by
        intro l hl; rw [← hj0μ]; exact Finset.min'_le _ l hl
      obtain ⟨r, hcong⟩ : ∃ r : LaurentPolynomial ↥σ.K,
          LaurentPolynomial.T a * Polynomial.toLaurent R' =
            LaurentPolynomial.T ((μ : ℤ) * (- tstar * (hstar : ℤ) * (g : ℤ))) * V.D.Rv (B μ) +
              Polynomial.toLaurent ψ * r := by
        refine ⟨∑ l ∈ (((Finset.range N).filter (fun j => B j ≠ 0)).filter
            (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
              = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin))).erase μ,
            (V.D.Rv (B l) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ l)
              * (Polynomial.toLaurent ψ) ^ (l - μ - 1), ?_⟩
        apply mul_left_cancel₀ (pow_ne_zero μ hΨne)
        have hLHS : (Polynomial.toLaurent ψ) ^ μ
              * (LaurentPolynomial.T a * Polynomial.toLaurent R') = V.D.Rv f := by
          rw [hanch_eq, hR', map_mul, map_pow]; ring
        have hRHS : (Polynomial.toLaurent ψ) ^ μ *
            (LaurentPolynomial.T ((μ : ℤ) * (- tstar * (hstar : ℤ) * (g : ℤ))) * V.D.Rv (B μ)
              + Polynomial.toLaurent ψ *
                  ∑ l ∈ (((Finset.range N).filter (fun j => B j ≠ 0)).filter
                    (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
                      = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin))).erase μ,
                    (V.D.Rv (B l) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ l)
                      * (Polynomial.toLaurent ψ) ^ (l - μ - 1)) = V.D.Rv f := by
          rw [mul_add]
          have hterm : (Polynomial.toLaurent ψ) ^ μ
                * (LaurentPolynomial.T ((μ : ℤ) * (- tstar * (hstar : ℤ) * (g : ℤ))) * V.D.Rv (B μ))
              = (V.D.Rv (B μ) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ μ)
                  * (Polynomial.toLaurent ψ) ^ μ := by
            rw [hTp μ]; ring
          have htail : (Polynomial.toLaurent ψ) ^ μ *
                (Polynomial.toLaurent ψ *
                  ∑ l ∈ (((Finset.range N).filter (fun j => B j ≠ 0)).filter
                    (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
                      = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin))).erase μ,
                    (V.D.Rv (B l) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ l)
                      * (Polynomial.toLaurent ψ) ^ (l - μ - 1))
              = ∑ l ∈ (((Finset.range N).filter (fun j => B j ≠ 0)).filter
                  (fun j => childW σ σ.Φ estar hstar (B j * Φhat ^ j)
                    = childW σ σ.Φ estar hstar (B jmin * Φhat ^ jmin))).erase μ,
                  (V.D.Rv (B l) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ l)
                    * (Polynomial.toLaurent ψ) ^ l := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun l hl => ?_)
            have hlgt : μ < l := by
              have hlM := Finset.mem_of_mem_erase hl
              have hlne := Finset.ne_of_mem_erase hl
              have := hge l hlM; omega
            rw [show (Polynomial.toLaurent ψ) ^ μ *
                    (Polynomial.toLaurent ψ *
                      ((V.D.Rv (B l) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ l)
                        * (Polynomial.toLaurent ψ) ^ (l - μ - 1)))
                  = (V.D.Rv (B l) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ l)
                      * ((Polynomial.toLaurent ψ) ^ μ * (Polynomial.toLaurent ψ) ^ 1
                        * (Polynomial.toLaurent ψ) ^ (l - μ - 1)) from by rw [pow_one]; ring,
                ← pow_add, ← pow_add, show μ + 1 + (l - μ - 1) = l from by omega]
          rw [hterm, htail]
          refine Eq.trans ?_ hRf2.symm
          exact Finset.add_sum_erase _
            (fun x => V.D.Rv (B x) * (LaurentPolynomial.T (- tstar * (hstar : ℤ) * (g : ℤ))) ^ x
              * (Polynomial.toLaurent ψ) ^ x) hμM
        rw [hLHS, hRHS]
      have hψ0 : LaurentPolynomial.eval₂ σ.K.subtype zbar (Polynomial.toLaurent ψ) = 0 := by
        rw [LaurentPolynomial.eval₂_toLaurent]; exact hzbar
      have heval : LaurentPolynomial.eval₂ σ.K.subtype zbar
          (LaurentPolynomial.T a * Polynomial.toLaurent R') =
          ((zbar ^ ((μ : ℤ) * (- tstar * (hstar : ℤ) * (g : ℤ))) : Fˣ) : F) *
            LaurentPolynomial.eval₂ σ.K.subtype zbar (V.D.Rv (B μ)) := by
        rw [hcong, map_add, map_mul, map_mul, hψ0, zero_mul, add_zero,
          LaurentPolynomial.eval₂_T]
      have hunit : zbar ^ ((μ : ℤ) * tstar * (hstar : ℤ) * (g : ℤ)) *
          zbar ^ ((μ : ℤ) * (- tstar * (hstar : ℤ) * (g : ℤ))) = 1 := by
        rw [← zpow_add,
          show (μ : ℤ) * tstar * (hstar : ℤ) * (g : ℤ) +
            (μ : ℤ) * (- tstar * (hstar : ℤ) * (g : ℤ)) = 0 by ring, zpow_zero]
      rw [heval, ← mul_assoc, ← Units.val_mul, hunit, Units.val_one, one_mul]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V4_readLanding
