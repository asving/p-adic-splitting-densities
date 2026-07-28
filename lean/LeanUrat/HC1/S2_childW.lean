/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L0_FactB_unique

/-!
# HC1.S2_childW — the child valuation function is well-defined

moves_ref: MOVES 2329 "w′(Σ_j B_j Φ̂^j) := min_j (e′·w(B_j) + j·h′)". deps:
DefsSpine; Moves `L0_FactA_exists`, `L0_FactB_unique` (clean). difficulty: HARD
(the function-level development + attained min is real plumbing; pre-split: S2a
development function; S2b the IsSlotMinWeight law). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S2: for f ≠ 0 the Φ̂-development exists and is unique, the min is attained
at `childW`'s value, and `IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w`
holds. -/
theorem S2_childW {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (hmon : Φhat.Monic)
    (hdeg : 1 ≤ Φhat.natDegree) (e' h' : ℕ) :
    (∀ f : Polynomial ℤ_[p], f ≠ 0 →
      ∃ (B : ℕ → Polynomial ℤ_[p]) (N : ℕ), IsDevelopment Φhat f B N ∧
        SlotMinAttained (childW σ Φhat e' h' f) N
          (fun j => (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)) (fun j => B j ≠ 0)) ∧
    IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w := by
  classical
  -- (S2a) The `childW` predicate is inhabited for every nonzero `f`: the slot minimum of
  -- the (unique, by Fact B) Φ̂-development is attained on the finite nonzero-slot set.
  have key : ∀ f : Polynomial ℤ_[p], f ≠ 0 →
      ∃ m : ℤ, ∀ (B : ℕ → Polynomial ℤ_[p]) (N : ℕ), IsDevelopment Φhat f B N →
        SlotMinAttained m N (fun j => (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ))
          (fun j => B j ≠ 0) := by
    intro f hf
    obtain ⟨B₀, N₀, hdev₀⟩ := L0_FactA_exists Φhat hmon hdeg f
    -- The nonzero-slot set is nonempty (else `f = Σ 0 = 0`).
    have hSne : ((Finset.range N₀).filter (fun j => B₀ j ≠ 0)).Nonempty := by
      rw [Finset.filter_nonempty_iff]
      by_contra hcon
      push_neg at hcon
      apply hf
      rw [hdev₀.2.2]
      apply Finset.sum_eq_zero
      intro j hj
      rw [hcon j hj, zero_mul]
    -- Attained minimum of the slot weights over the nonzero-slot set.
    obtain ⟨j₀, hj₀mem, hj₀min⟩ :=
      ((Finset.range N₀).filter (fun j => B₀ j ≠ 0)).exists_min_image
        (fun j => (e' : ℤ) * σ.w (B₀ j) + (j : ℤ) * (h' : ℤ)) hSne
    rw [Finset.mem_filter, Finset.mem_range] at hj₀mem
    refine ⟨(e' : ℤ) * σ.w (B₀ j₀) + (j₀ : ℤ) * (h' : ℤ), ?_⟩
    intro B N hdev
    -- Every development agrees with `B₀` (Fact B), so the slot data is the fixed one.
    have hBeq : ∀ j, B j = B₀ j := L0_FactB_unique Φhat hmon f hdev hdev₀
    refine ⟨?_, ?_⟩
    · -- lower bound: the fixed minimum bounds every nonzero slot
      intro j _ hBj
      have hB0j : B₀ j ≠ 0 := by rw [← hBeq j]; exact hBj
      have hjN0 : j < N₀ := by
        by_contra hge
        push_neg at hge
        exact hB0j (hdev₀.2.1 j hge)
      have hjmem : j ∈ (Finset.range N₀).filter (fun j => B₀ j ≠ 0) := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hjN0, hB0j⟩
      have hle := hj₀min j hjmem
      simpa only [hBeq] using hle
    · -- attained: the minimizer `j₀` lies in the range of every development
      refine ⟨j₀, ?_, ?_, ?_⟩
      · by_contra hge
        push_neg at hge
        have : B₀ j₀ = 0 := by rw [← hBeq j₀]; exact hdev.2.1 j₀ hge
        exact hj₀mem.2 this
      · show B j₀ ≠ 0
        rw [hBeq j₀]; exact hj₀mem.2
      · simp only [hBeq]
  -- (S2b) Evaluate `childW` at its choice witness, then assemble both conclusions.
  have main : ∀ (f : Polynomial ℤ_[p]), f ≠ 0 → ∀ (B : ℕ → Polynomial ℤ_[p]) (N : ℕ),
      IsDevelopment Φhat f B N →
      SlotMinAttained (childW σ Φhat e' h' f) N
        (fun j => (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)) (fun j => B j ≠ 0) := by
    intro f hf B N hdev
    have hP := key f hf
    have hval : childW σ Φhat e' h' f = hP.choose := by
      unfold childW
      exact dif_pos hP
    rw [hval]
    exact hP.choose_spec B N hdev
  refine ⟨?_, ?_⟩
  · intro f hf
    obtain ⟨B, N, hdev⟩ := L0_FactA_exists Φhat hmon hdeg f
    exact ⟨B, N, hdev, main f hf B N hdev⟩
  · intro f B N hf hdev
    exact main f hf B N hdev

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S2_childW
