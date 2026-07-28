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
# HC1.S3_childK1 — K1(Φ̂/w′) is definitional

moves_ref: MOVES 2338–2340 "(ii) K1(Φ̂/w′) is definitional (the accepted pass-4
observation)". deps: S2. sketch: unfold; the development of f at Φ̂ IS the defining
data; w′(Φ̂) = h′. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Transport a `SlotMinAttained` witness along a slot-weight function that agrees on the
nonzero slots (the predicate only ever reads `sw` at slots where `nz` holds). -/
private lemma slotMin_congr_slots {m : ℤ} {N : ℕ} {sw sw' : ℕ → ℤ} {nz : ℕ → Prop}
    (h : ∀ j, nz j → sw j = sw' j) (H : SlotMinAttained m N sw nz) :
    SlotMinAttained m N sw' nz := by
  obtain ⟨hle, j, hjN, hnz, heq⟩ := H
  exact ⟨fun i hiN hnzi => (h i hnzi) ▸ hle i hiN hnzi,
         j, hjN, hnz, heq.trans (h j hnz)⟩

/-- Core well-definedness (the S2 slot-minimum law, re-derived in-unit from Fact A/B):
`childW` reads the side `(e', h')` over `σ.w` at the child key `Φ̂` — every `Φ̂`-development's
weight is the attained slot-minimum `min_j (e'·σ.w(B_j) + j·h')`. -/
private lemma childW_isSlotMin (σ : Stage p F) (Φhat : Polynomial ℤ_[p])
    (hmon : Φhat.Monic) (e' h' : ℕ) :
    IsSlotMinWeight (childW σ Φhat e' h') Φhat e' h' σ.w := by
  intro f B N hf hdev
  classical
  -- nonzero-slot set for this development
  set S : Finset ℕ := (Finset.range N).filter (fun j => B j ≠ 0) with hSdef
  have hSne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with hemp | hne
    · exfalso; apply hf
      rw [hdev.2.2]
      apply Finset.sum_eq_zero
      intro j hj
      have hbj : B j = 0 := by
        by_contra hb
        have hmem : j ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨hj, hb⟩
        rw [hemp] at hmem; simp at hmem
      rw [hbj, zero_mul]
    · exact hne
  obtain ⟨j0, hj0S, hj0min⟩ :=
    S.exists_min_image (fun j => (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)) hSne
  have hbj0 : B j0 ≠ 0 := by
    have h := hj0S; rw [hSdef, Finset.mem_filter] at h; exact h.2
  -- the universal slot-min value: same for every development by Fact B uniqueness
  have hQ : ∃ m : ℤ, ∀ (B'' : ℕ → Polynomial ℤ_[p]) (N'' : ℕ), IsDevelopment Φhat f B'' N'' →
      SlotMinAttained m N'' (fun j => (e' : ℤ) * σ.w (B'' j) + (j : ℤ) * (h' : ℤ))
        (fun j => B'' j ≠ 0) := by
    refine ⟨(e' : ℤ) * σ.w (B j0) + (j0 : ℤ) * (h' : ℤ), ?_⟩
    intro B'' N'' hdev''
    have huniq : ∀ j, B'' j = B j := fun j => L0_FactB_unique Φhat hmon f hdev'' hdev j
    refine ⟨fun j hjN'' hb''j => ?_, j0, ?_, ?_, ?_⟩
    · -- ∀ part
      show (e' : ℤ) * σ.w (B j0) + (j0 : ℤ) * (h' : ℤ)
            ≤ (e' : ℤ) * σ.w (B'' j) + (j : ℤ) * (h' : ℤ)
      have hbj : B j ≠ 0 := by rw [← huniq j]; exact hb''j
      have hjN : j < N := by
        by_contra hge; exact hbj (hdev.2.1 j (not_lt.mp hge))
      have hjS : j ∈ S := by
        rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr hjN, hbj⟩
      rw [huniq j]
      exact hj0min j hjS
    · -- j0 < N''
      show j0 < N''
      by_contra hge
      have h0 : B'' j0 = 0 := hdev''.2.1 j0 (not_lt.mp hge)
      rw [huniq j0] at h0; exact hbj0 h0
    · -- nz j0
      show B'' j0 ≠ 0
      rw [huniq j0]; exact hbj0
    · -- m = slot weight at j0
      show (e' : ℤ) * σ.w (B j0) + (j0 : ℤ) * (h' : ℤ)
            = (e' : ℤ) * σ.w (B'' j0) + (j0 : ℤ) * (h' : ℤ)
      rw [huniq j0]
  -- childW picks that value
  have hchoose : childW σ Φhat e' h' f = hQ.choose := by
    unfold childW; rw [dif_pos hQ]
  rw [hchoose]
  exact hQ.choose_spec B N hdev

/-- For a nonzero coefficient `g` (degree below the child key), `childW` reads its stretched
parent weight `e'·σ.w(g)` (the constant slot, `j = 0`). -/
private lemma childW_lowDeg (σ : Stage p F) (Φhat : Polynomial ℤ_[p])
    (hmon : Φhat.Monic) (e' h' : ℕ) (g : Polynomial ℤ_[p]) (hg : g ≠ 0)
    (hgdeg : g.degree < Φhat.degree) :
    childW σ Φhat e' h' g = (e' : ℤ) * σ.w g := by
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  have hdev : IsDevelopment Φhat g (fun j => if j = 0 then g else 0) 1 := by
    refine ⟨fun j => ?_, fun j hj1 => ?_, ?_⟩
    · show (if j = 0 then g else 0).degree < Φhat.degree
      split_ifs with hj
      · exact hgdeg
      · rw [Polynomial.degree_zero]
        exact bot_lt_iff_ne_bot.mpr (fun h => hΦne (Polynomial.degree_eq_bot.mp h))
    · show (if j = 0 then g else 0) = 0
      rw [if_neg (by omega : j ≠ 0)]
    · rw [Finset.sum_range_one]; simp
  have hslot := childW_isSlotMin σ Φhat hmon e' h' g _ 1 hg hdev
  obtain ⟨hle, j, hjN, hnz, heq⟩ := hslot
  have hj0 : j = 0 := by omega
  subst hj0
  rw [heq]; simp

/-- Unit S3: the child key's own weight is h′ and Lemma K1 holds at the child's own
key for the child valuation. -/
theorem S3_childK1 {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (hmon : Φhat.Monic)
    (hdeg : 1 ≤ Φhat.natDegree) (e' h' : ℕ) (he' : 1 ≤ e') (hh' : 1 ≤ h')
    (hw1 : σ.w 1 = 0) :
    childW σ Φhat e' h' Φhat = (h' : ℤ) ∧
    K1At (childW σ Φhat e' h') Φhat ((h' : ℤ)) := by
  have hΦne : Φhat ≠ 0 := hmon.ne_zero
  refine ⟨?_, ?_⟩
  · -- childW Φhat = h′ : the development of Φ̂ at Φ̂ is 1·Φ̂¹
    have hstdev : IsDevelopment Φhat Φhat
        (fun j => if j = 1 then (1 : Polynomial ℤ_[p]) else 0) 2 := by
      refine ⟨fun j => ?_, fun j hj2 => ?_, ?_⟩
      · show (if j = 1 then (1 : Polynomial ℤ_[p]) else 0).degree < Φhat.degree
        split_ifs with hj
        · rw [Polynomial.degree_one]
          exact Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)
        · rw [Polynomial.degree_zero]
          exact bot_lt_iff_ne_bot.mpr (fun h => hΦne (Polynomial.degree_eq_bot.mp h))
      · show (if j = 1 then (1 : Polynomial ℤ_[p]) else 0) = 0
        rw [if_neg (by omega : j ≠ 1)]
      · rw [Finset.sum_range_succ, Finset.sum_range_one]; simp
    have hslot := childW_isSlotMin σ Φhat hmon e' h' Φhat _ 2 hΦne hstdev
    obtain ⟨hle, j, hjN, hnz, heq⟩ := hslot
    have hj1 : j = 1 := by
      by_contra hne
      apply hnz
      show (if j = 1 then (1 : Polynomial ℤ_[p]) else 0) = 0
      exact if_neg hne
    subst hj1
    rw [heq]; simp [hw1]
  · -- K1 at the child key: the K1 slot weights (childW(B_j) + j·h′) match the defining ones
    intro f B N hf hdev
    refine slotMin_congr_slots (fun j hbj => ?_)
      (childW_isSlotMin σ Φhat hmon e' h' f B N hf hdev)
    rw [childW_lowDeg σ Φhat hmon e' h' (B j) hbj (hdev.1 j)]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S3_childK1
