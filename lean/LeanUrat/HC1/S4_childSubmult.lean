/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L3_DIV
import LeanUrat.Moves.L4_TRANSi_R3
import LeanUrat.Moves.L0_FactB_unique
import LeanUrat.Moves.L3_liftMonic

/-!
# HC1.S4_childSubmult — D.7(i): childW is submultiplicative

moves_ref: MOVES 2331–2337 (D.7(i), the slot-(j+k+1) Q-part strictly deeper by
(I-aug)). deps: S2; Moves `L3_DIV`, `L4_TRANSi_R3` (clean). sketch: re-develop
products; the ultrametric assembly is L4_TRANSi's content instantiated at childW.
difficulty: medium. hyp: none (the read's legality bundled as `TransHyp`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- `childW σ Φhat e' h'` satisfies the slot-minimum-weight law (the D.7-head reading
`w'(Σ B_j Φ̂^j) = min_j (e'·w(B_j) + j·h')`).  This is exactly `IsSlotMinWeight` for the
`childW` FUNCTION — S2's content, proved here self-contained from the monic Φ̂-development
existence/uniqueness (Fact A already used in defining the class; Fact B `L0_FactB_unique`
pins the uniform slot-min value across developments).  Kept private so S4 is axiom-clean
(no dependency on the still-open S2 unit). -/
private lemma childW_isSlotMinWeight {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (hmon : Φhat.Monic) (e' h' : ℕ) :
    IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w := by
  classical
  intro f B N hf hdev
  -- the nonzero-slot set of the development is nonempty (else f = 0)
  have hSne : ((Finset.range N).filter (fun j => B j ≠ 0)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    apply hf
    rw [hdev.2.2]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    by_cases hbj : B j = 0
    · rw [hbj, zero_mul]
    · have hmem : j ∈ (Finset.range N).filter (fun j => B j ≠ 0) :=
        Finset.mem_filter.mpr ⟨hj, hbj⟩
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty j)
  -- the attained slot minimum over the given development
  obtain ⟨j₀, hj₀S, hj₀min⟩ :=
    ((Finset.range N).filter (fun j => B j ≠ 0)).exists_min_image
      (fun j => (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)) hSne
  rw [Finset.mem_filter, Finset.mem_range] at hj₀S
  -- the uniform slot-min value works for EVERY development (Fact B: developments agree)
  have hex : ∃ m : ℤ, ∀ (B' : ℕ → Polynomial ℤ_[p]) (N' : ℕ), IsDevelopment Φhat f B' N' →
      SlotMinAttained m N' (fun j => (e' : ℤ) * σ.w (B' j) + (j : ℤ) * (h' : ℤ))
        (fun j => B' j ≠ 0) := by
    refine ⟨(e' : ℤ) * σ.w (B j₀) + (j₀ : ℤ) * (h' : ℤ), fun B' N' hdev' => ⟨?_, ?_⟩⟩
    · intro j hjN' hbj'
      have hBB : B' j = B j := L0_FactB_unique Φhat hmon f hdev' hdev j
      have hbj : B j ≠ 0 := hBB ▸ hbj'
      have hjN : j < N := by
        by_contra hge; exact hbj (hdev.2.1 j (not_lt.mp hge))
      have hmem : j ∈ (Finset.range N).filter (fun j => B j ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN, hbj⟩
      simpa [hBB] using hj₀min j hmem
    · refine ⟨j₀, ?_, ?_, ?_⟩
      · by_contra hge
        have hBB : B' j₀ = B j₀ := L0_FactB_unique Φhat hmon f hdev' hdev j₀
        exact hj₀S.2 (hBB ▸ hdev'.2.1 j₀ (not_lt.mp hge))
      · have hBB : B' j₀ = B j₀ := L0_FactB_unique Φhat hmon f hdev' hdev j₀
        simpa [hBB] using hj₀S.2
      · have hBB : B' j₀ = B j₀ := L0_FactB_unique Φhat hmon f hdev' hdev j₀
        simp [hBB]
  -- childW picks that value (it is in the `dif_pos` branch), so the given development attains it
  have hcw : childW σ Φhat e' h' f = hex.choose := by
    simp only [childW]; rw [dif_pos hex]
  rw [hcw]
  exact hex.choose_spec B N hdev

/-- Unit S4: `childW (f·g) ≥ childW f + childW g` (via DIV(i) on coefficient
products + the (I-aug) strict depth of Q-terms). -/
theorem S4_childSubmult {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (f f' : Polynomial ℤ_[p]) (hf : f ≠ 0) (hf' : f' ≠ 0) :
    childW σ Φhat e' h' f + childW σ Φhat e' h' f'
      ≤ childW σ Φhat e' h' (f * f') := by
  have hmon : Φhat.Monic := (L3_liftMonic σ ψ g th.hg Φhat th.hlift).1
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    rw [← Polynomial.eval_map]
    simpa [Polynomial.aeval_def] using th.hroot
  exact L4_TRANSi σ ψ g Φhat th.hlift th.hirr th.hne_z zbar hzbar e' h'
    (childW σ Φhat e' h') (childW_isSlotMinWeight σ Φhat hmon e' h') th.hiaug
    f f' hf hf' (mul_ne_zero hf hf')

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S4_childSubmult
