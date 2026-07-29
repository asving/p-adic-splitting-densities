/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.L0_FactA_exists
import LeanUrat.Moves.L2_P6ii_R3
import LeanUrat.Moves.L3_liftMonic

/-!
# Moves/L6_measureExact_R4 — the per-move measure ledger (D.11, MOVES ~2489-2519)

CONDITIONAL on the supplied jet-coordinate presentations (audit #4); not the full D.11 endpoint.

Counting endpoint: a stratum cut by `k` unitriangular digit equations has cardinality
`p^{D·N−k}`, so its measure `card/p^{D·N} = 1/p^k` is level-independent.  PROVED here:
the transport stratum ↔ digit-solution set at each level, the `p^{D·n−k}` count (L2.P6ii),
the ratio arithmetic, AND the exact-length-`Nslots` development of every nonzero `f` with
`natDegree f < D = natDegree Φ̂ · Nslots` (Fact A + a degree-bound truncation, inlined below).
REMAINING GAP (one explicit `sorry`):
* `L5_landTwoSided_missing` — the dep `L5.landTwoSided` has no file on disk: the descend
  stratum (`StratumData`) is exactly the landing cylinder (`LandingCylinder`) of the
  exact-length development.  Inlined as a private placeholder with the precise statement.
  MISSING-DEP bridge, out of one-unit scope (MANIFEST_REPAIR.json:86); note the recorded
  ANOMALY there: this placeholder is stated over `DefsCore.LandingCylinder`/`StratumData`
  whereas the real `L5_landTwoSided` proves the `DefsL.LandingCylinderL` form — a future
  bridge unit must reconcile the two cylinder objects (or re-point `measureExact`).

CLOSED (was the round-3 zero-coordinate FLAG): the leg where `E.IsSolution` at `Θ (code 0)`
was unpinned — no hypothesis ruled out the digit system accepting the zero polynomial's
coordinate, and a model making it true would break the count by one.  Discharged by the
SCOPING-AUTHORITY amendment adding the named typed hypotheses `hzsolN`/`hzsolM`
(`∀ f, f.natDegree < D → f = 0 → ¬ E.IsSolution (Θ (code f))`) to `L6_measureExact`, a
genuine presentation-faithfulness hypothesis symmetric to the pre-existing `hzN`/`hzM` on
the stratum side.  Warrant + exact statement: `MANIFEST_REPAIR.json:80`; the fence change is
pre-recorded for semantic audit at `MANIFEST_REPAIR.json:158`
(`fence_changes_needing_audit`: "L6.measureExact (+hzsolN/hzsolM)").  FLAGGED for orchestrator
ratification (semantic-guardian audit pass still owed).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

open Polynomial

namespace LeanUrat.Moves

/-- **Truncation of a Φ-adic development to the exact length `L`** forced by the degree bound
`natDegree f < natDegree Φ · L`: any development (Fact A gives some length `N'`) already has
all slots `≥ L` zero — a nonzero top slot `m ≥ L` would force `natDegree f ≥ m·natDegree Φ`. -/
private lemma development_truncate {p : ℕ} [Fact p.Prime] (Φ : Polynomial ℤ_[p])
    (hmon : Φ.Monic) (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]) (N' L : ℕ)
    (hdev : IsDevelopment Φ f B N') (hdeg : f.natDegree < Φ.natDegree * L) :
    IsDevelopment Φ f B L := by
  classical
  obtain ⟨hBdeg, hBzero, hBsum⟩ := hdev
  have hzL : ∀ j, L ≤ j → B j = 0 := by
    intro j hjL
    by_contra hBj
    have hjN' : j < N' := by
      by_contra hge
      exact hBj (hBzero j (by omega))
    set s : Finset ℕ := (Finset.range N').filter (fun i => B i ≠ 0) with hs
    have hjs : j ∈ s := by
      simp only [hs, Finset.mem_filter, Finset.mem_range]
      exact ⟨hjN', hBj⟩
    have hsne : s.Nonempty := ⟨j, hjs⟩
    set m := s.max' hsne with hm
    have hms : m ∈ s := s.max'_mem hsne
    have hmN' : m < N' := Finset.mem_range.mp (Finset.mem_filter.mp hms).1
    have hBm : B m ≠ 0 := (Finset.mem_filter.mp hms).2
    have hjm : j ≤ m := s.le_max' j hjs
    have hT_ne : B m * Φ ^ m ≠ 0 := mul_ne_zero hBm (hmon.pow m).ne_zero
    have hT_deg : m * Φ.natDegree ≤ (B m * Φ ^ m).natDegree := by
      rw [Polynomial.natDegree_mul hBm (hmon.pow m).ne_zero, Polynomial.natDegree_pow]
      omega
    have hTbot : (⊥ : WithBot ℕ) < (B m * Φ ^ m).degree := by
      rw [bot_lt_iff_ne_bot]
      intro h
      exact hT_ne (Polynomial.degree_eq_bot.mp h)
    have hsplit : f = (∑ i ∈ (Finset.range N').erase m, B i * Φ ^ i) + B m * Φ ^ m := by
      rw [hBsum]
      exact (Finset.sum_erase_add _ _ (Finset.mem_range.mpr hmN')).symm
    have hSdeg : (∑ i ∈ (Finset.range N').erase m, B i * Φ ^ i).degree
        < (B m * Φ ^ m).degree := by
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff hTbot]
      intro i hi
      rcases eq_or_ne (B i) 0 with h0 | h0
      · rw [h0, zero_mul, Polynomial.degree_zero]
        exact hTbot
      · have hiN' : i < N' := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
        have him : i ≠ m := Finset.ne_of_mem_erase hi
        have his : i ∈ s := by
          simp only [hs, Finset.mem_filter, Finset.mem_range]
          exact ⟨hiN', h0⟩
        have hilt : i < m := lt_of_le_of_ne (s.le_max' i his) him
        apply Polynomial.degree_lt_degree
        rw [Polynomial.natDegree_mul h0 (hmon.pow i).ne_zero,
          Polynomial.natDegree_mul hBm (hmon.pow m).ne_zero,
          Polynomial.natDegree_pow, Polynomial.natDegree_pow]
        have hBi : (B i).natDegree < Φ.natDegree :=
          Polynomial.natDegree_lt_natDegree h0 (hBdeg i)
        have hmul : i * Φ.natDegree + Φ.natDegree ≤ m * Φ.natDegree := by
          have h2 : (i + 1) * Φ.natDegree ≤ m * Φ.natDegree :=
            Nat.mul_le_mul (by omega) (le_refl _)
          rwa [add_one_mul] at h2
        omega
    have hfdeg2 : f.degree = (B m * Φ ^ m).degree := by
      rw [hsplit]
      exact Polynomial.degree_add_eq_right_of_degree_lt hSdeg
    have hfnat : f.natDegree = (B m * Φ ^ m).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq hfdeg2
    have hLm : Φ.natDegree * L ≤ Φ.natDegree * m := Nat.mul_le_mul (le_refl _) (by omega)
    have hcomm : Φ.natDegree * m = m * Φ.natDegree := Nat.mul_comm _ _
    omega
  refine ⟨hBdeg, hzL, ?_⟩
  rcases le_total L N' with h | h
  · have hsub : Finset.range L ⊆ Finset.range N' := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    rw [hBsum]
    symm
    refine Finset.sum_subset hsub ?_
    intro i _ hiL
    rw [hzL i (by simpa using hiL), zero_mul]
  · have hsub : Finset.range N' ⊆ Finset.range L := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    rw [hBsum]
    refine Finset.sum_subset hsub ?_
    intro i _ hiN
    rw [hBzero i (by simpa using hiN), zero_mul]

/-- **The missing dep `L5.landTwoSided` (no file on disk; audit #4)**: the descend stratum
with pinned pattern (`StratumData`) holds iff the exact-length development lands in the
cylinder (`LandingCylinder`).  Forward = BOX/VERTEX/TRANSPORT (L5_landBox, L5_landVertex,
L5_landVertexDigit assemble the carry recursion); backward = the transport converse
(L5_landTransport).  Out of one-unit scope; inlined as the precise statement consumed. -/
private lemma L5_landTwoSided_missing {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hcore : StageCore σ) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hgpos : 1 ≤ g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (μ : ℕ) (a : ℤ)
    (Cdig : ℕ → Polynomial ↥σ.K) (Nslots : ℕ) (hμN : μ < Nslots)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (B : ℕ → Polynomial ℤ_[p])
    (hdev : IsDevelopment Φhat f B Nslots) :
    StratumData σ ψ μ a Cdig Nslots f ↔ LandingCylinder σ ψ g μ a Cdig B Nslots := by
  sorry

theorem L6_measureExact {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (hcore : StageCore σ) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hgpos : 1 ≤ g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (μ : ℕ) (a : ℤ) (Cdig : ℕ → Polynomial ↥σ.K) (Nslots : ℕ) (hμN : μ < Nslots) (D k : ℕ) (hD : D = Φhat.natDegree * Nslots) (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) (hkN : k ≤ D * N) (hkM : k ≤ D * M) (stratN : (Fin (D * N) → ZMod p) → Prop) (stratM : (Fin (D * M) → ZMod p) → Prop) (codeN : Polynomial ℤ_[p] → (Fin (D * N) → ZMod p)) (codeM : Polynomial ℤ_[p] → (Fin (D * M) → ZMod p)) (hcodeN : ∀ x, ∃ f, f.natDegree < D ∧ codeN f = x) (hcodeM : ∀ x, ∃ f, f.natDegree < D ∧ codeM f = x) (hstratN : ∀ f : Polynomial ℤ_[p], f.natDegree < D → (stratN (codeN f) ↔ (f ≠ 0 ∧ StratumData σ ψ μ a Cdig Nslots f))) (hstratM : ∀ f : Polynomial ℤ_[p], f.natDegree < D → (stratM (codeM f) ↔ (f ≠ 0 ∧ StratumData σ ψ μ a Cdig Nslots f))) (ΘN : (Fin (D * N) → ZMod p) ≃ (Fin (D * N) → ZMod p)) (ΘM : (Fin (D * M) → ZMod p) ≃ (Fin (D * M) → ZMod p)) (EN : DigitSystem (D * N) (ZMod p)) (EM : DigitSystem (D * M) (ZMod p)) (hENk : EN.numPinned = k) (hEMk : EM.numPinned = k) (hcylN : ∀ (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]), f.natDegree < D → f ≠ 0 → IsDevelopment Φhat f B Nslots → (EN.IsSolution (ΘN (codeN f)) ↔ LandingCylinder σ ψ g μ a Cdig B Nslots)) (hcylM : ∀ (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]), f.natDegree < D → f ≠ 0 → IsDevelopment Φhat f B Nslots → (EM.IsSolution (ΘM (codeM f)) ↔ LandingCylinder σ ψ g μ a Cdig B Nslots)) (hzN : ∀ f : Polynomial ℤ_[p], f.natDegree < D → f = 0 → ¬ stratN (codeN f)) (hzM : ∀ f : Polynomial ℤ_[p], f.natDegree < D → f = 0 → ¬ stratM (codeM f)) (hzsolN : ∀ f : Polynomial ℤ_[p], f.natDegree < D → f = 0 → ¬ EN.IsSolution (ΘN (codeN f))) (hzsolM : ∀ f : Polynomial ℤ_[p], f.natDegree < D → f = 0 → ¬ EM.IsSolution (ΘM (codeM f))) : (Nat.card {x // stratN x} : ℚ) / (p : ℚ) ^ (D * N) = (Nat.card {x // stratM x} : ℚ) / (p : ℚ) ^ (D * M) := by
  classical
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hz : Nat.card (ZMod p) = p := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨hΦmon, hΦdeg⟩ := L3_liftMonic σ ψ g hgpos Φhat hlift
  -- Generic counting endpoint at a level `n`: transport the stratum locus to the
  -- digit-system solution set (jet-coordinate presentation), then P6ii counts it.
  have hcard : ∀ (n : ℕ)
      (strat : (Fin (D * n) → ZMod p) → Prop)
      (code : Polynomial ℤ_[p] → (Fin (D * n) → ZMod p))
      (Θ : (Fin (D * n) → ZMod p) ≃ (Fin (D * n) → ZMod p))
      (E : DigitSystem (D * n) (ZMod p)),
      (∀ x, ∃ f, f.natDegree < D ∧ code f = x) →
      (∀ f : Polynomial ℤ_[p], f.natDegree < D →
        (strat (code f) ↔ (f ≠ 0 ∧ StratumData σ ψ μ a Cdig Nslots f))) →
      (∀ (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]), f.natDegree < D → f ≠ 0 →
        IsDevelopment Φhat f B Nslots →
          (E.IsSolution (Θ (code f)) ↔ LandingCylinder σ ψ g μ a Cdig B Nslots)) →
      (∀ f : Polynomial ℤ_[p], f.natDegree < D → f = 0 → ¬ E.IsSolution (Θ (code f))) →
      E.numPinned = k →
      Nat.card {x // strat x} = p ^ (D * n - k) := by
    intro n strat code Θ E hcode hstrat hcyl hzsol hEk
    -- `D ≥ 1` (the coordinate space is inhabited and surjected onto), so `natDegree Φ̂ ≥ 1`
    obtain ⟨f₀, hf₀, -⟩ := hcode (fun _ => 0)
    have hΦd1 : 1 ≤ Φhat.natDegree := by
      rcases Nat.eq_zero_or_pos Φhat.natDegree with h | h
      · exfalso
        rw [h, zero_mul] at hD
        omega
      · exact h
    have hiff : ∀ x, strat x ↔ E.IsSolution (Θ x) := by
      intro x
      obtain ⟨f, hfdeg, rfl⟩ := hcode x
      rw [hstrat f hfdeg]
      by_cases hf0 : f = 0
      · subst hf0
        constructor
        · rintro ⟨hne, _⟩
          exact absurd rfl hne
        · intro hsol
          -- CLOSED (was the round-3 FLAG): the zero-coordinate leg is discharged by the
          -- presentation-faithfulness hypothesis `hzsol` — the digit system rejects the
          -- zero polynomial's coordinate `Θ (code 0)`, symmetric to `hzN`/`hzM` on the
          -- stratum side.  Threaded from `L6_measureExact`'s new `hzsolN`/`hzsolM`
          -- (MANIFEST_REPAIR.json:80,158 fence_changes_needing_audit: "+hzsolN/hzsolM").
          exact absurd hsol (hzsol 0 hfdeg rfl)
      · -- exact-length development: Fact A + the degree-bound truncation (PROVED)
        obtain ⟨B, N', hdev'⟩ := L0_FactA_exists Φhat hΦmon hΦd1 f
        have hdev : IsDevelopment Φhat f B Nslots :=
          development_truncate Φhat hΦmon f B N' Nslots hdev' (by rw [← hD]; exact hfdeg)
        have hlts := L5_landTwoSided_missing σ hcore ψ g hg hgpos hmon hψ hψz Φhat hlift
          μ a Cdig Nslots hμN f hf0 B hdev
        constructor
        · rintro ⟨_, hst⟩
          exact (hcyl f B hfdeg hf0 hdev).mpr (hlts.mp hst)
        · intro hsol
          exact ⟨hf0, hlts.mpr ((hcyl f B hfdeg hf0 hdev).mp hsol)⟩
    have e : {x // strat x} ≃ {x // E.IsSolution x} := Equiv.subtypeEquiv Θ hiff
    rw [Nat.card_congr e, LeanUrat.Moves.L2_P6ii (D * n) E, hEk, hz]
  have cardN := hcard N stratN codeN ΘN EN hcodeN hstratN hcylN hzsolN hENk
  have cardM := hcard M stratM codeM ΘM EM hcodeM hstratM hcylM hzsolM hEMk
  rw [cardN, cardM]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).pos.ne'
  have key : ∀ m : ℕ, k ≤ m → ((p ^ (m - k) : ℕ) : ℚ) / (p : ℚ) ^ m = 1 / (p : ℚ) ^ k := by
    intro m hm
    rw [Nat.cast_pow, div_eq_div_iff (pow_ne_zero m hp0) (pow_ne_zero k hp0), one_mul,
      ← pow_add, Nat.sub_add_cancel hm]
  rw [key (D * N) hkN, key (D * M) hkM]

end LeanUrat.Moves
