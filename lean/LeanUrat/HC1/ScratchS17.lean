/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L6_ledgerCount
import LeanUrat.Moves.L6_moveReduceCommute_R4
import LeanUrat.Moves.L6_measureExact_R4
import LeanUrat.Moves.L5_landTwoSided_repair

/-!
# HC1/ScratchS17 — SUFFICIENCY CERTIFICATE for S17's two missing hypotheses
(escalation prover, 2026-07-28; NOT a unit — scratch evidence for adjudication)

`S17_levelMeasureExact` as fenced is NOT provable sorry/axiom-free (see the
escalation report): (A) nothing pins `E.IsSolution (Θ (code 0))` when `0` is the
only deg-<D preimage — the L6_measureExact_R4:189 gap, blueprint §4.6(b), the
"+hzsol" spec of bfdfb5e; (B) `L5_landTwoSided` (the only StratumData ↔
LandingCylinderL bridge) needs `StageCore (T.stg k.castSucc)`, which S17 does not
carry and the Tower does not propagate (S11_towerSpine's machine-confirmed
obstruction, 2026-07-27).

THIS FILE proves: adding EXACTLY the two hypotheses
  `hcore : StageCore (T.stg k.castSucc)`  and
  `hzsol : ¬ E.IsSolution (Θ (code 0))`
closes S17 with zero sorry (footprint: Lean core only). So {A, B} is the EXACT
obstruction set — necessary (countermodels) and sufficient (this proof).
`development_truncate` is copied verbatim from L6_measureExact_R4 (private there).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

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

/-- S17's fenced statement PLUS the two missing hypotheses `hcore`/`hzsol`
(everything else verbatim): provable, zero sorry. -/
theorem S17_scratch_with_hcore_hzsol {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] (T : Tower p F) (k : Fin T.K) (lm : LevelMove T k)
    (hcore : StageCore (T.stg k.castSucc))
    (hg : lm.ψ.natDegree = lm.g) (hgpos : 1 ≤ lm.g) (hmon : lm.ψ.Monic)
    (hψ : Irreducible lm.ψ) (hψz : lm.ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p])
    (hlift : IsStandardLift (T.stg k.castSucc) lm.ψ lm.g Φhat)
    (hμN : lm.μ < lm.N)
    (hexact : ¬ Polynomial.X ∣ ∑ j ∈ Finset.range lm.N, lm.Cdig j * lm.ψ ^ j)
    (D ktot N : ℕ) (hD : D = Φhat.natDegree * lm.N) (hN : 1 ≤ N)
    (hkN : ktot ≤ D * N)
    (strat : (Fin (D * N) → ZMod p) → Prop)
    (code : Polynomial ℤ_[p] → (Fin (D * N) → ZMod p))
    (hcode : ∀ x, ∃ f : Polynomial ℤ_[p], f.natDegree < D ∧ code f = x)
    (hstrat : ∀ f : Polynomial ℤ_[p], f.natDegree < D →
      (strat (code f) ↔
        (f ≠ 0 ∧ StratumData (T.stg k.castSucc) lm.ψ lm.μ lm.a lm.Cdig lm.N f)))
    (hz : ∀ f : Polynomial ℤ_[p], f.natDegree < D → f = 0 → ¬ strat (code f))
    (Θ : (Fin (D * N) → ZMod p) ≃ (Fin (D * N) → ZMod p))
    (hΘ : LeanUrat.MovesC.IsUnitriangular fun x => Θ x)
    (E : DigitSystem (D * N) (ZMod p)) (hEk : E.numPinned = ktot)
    (hzsol : ¬ E.IsSolution (Θ (code 0)))
    (hcyl : ∀ (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]),
      f.natDegree < D → f ≠ 0 → IsDevelopment Φhat f B lm.N →
      (E.IsSolution (Θ (code f)) ↔
        LandingCylinderL (T.stg k.castSucc) lm.ψ lm.g lm.μ lm.a lm.Cdig B lm.N)) :
    Nat.card {x : Fin (D * N) → ZMod p // strat x} * p ^ ktot = p ^ (D * N) := by
  classical
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hzc : Nat.card (ZMod p) = p := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨hΦmon, hΦdeg⟩ := L3_liftMonic (T.stg k.castSucc) lm.ψ lm.g hgpos Φhat hlift
  -- D ≥ 1, hence natDegree Φ̂ ≥ 1 (the coordinate space is surjected onto)
  obtain ⟨f₀, hf₀, -⟩ := hcode (fun _ => 0)
  have hΦd1 : 1 ≤ Φhat.natDegree := by
    rcases Nat.eq_zero_or_pos Φhat.natDegree with h | h
    · rw [h, zero_mul] at hD; omega
    · exact h
  -- the pointwise transport iff (the L6 hcard skeleton, both legs now supplied)
  have hiff : ∀ x, strat x ↔ E.IsSolution (Θ x) := by
    intro x
    obtain ⟨f, hfdeg, rfl⟩ := hcode x
    rw [hstrat f hfdeg]
    by_cases hf0 : f = 0
    · subst hf0
      constructor
      · rintro ⟨hne, -⟩; exact absurd rfl hne
      · intro hsol; exact absurd hsol hzsol
    · obtain ⟨B, N', hdev'⟩ := L0_FactA_exists Φhat hΦmon hΦd1 f
      have hdev : IsDevelopment Φhat f B lm.N :=
        development_truncate Φhat hΦmon f B N' lm.N hdev' (by rw [← hD]; exact hfdeg)
      have hlts := L5_landTwoSided (T.stg k.castSucc) hcore lm.ψ lm.g hg hgpos hmon
        hψ hψz Φhat hlift lm.μ f hf0 B lm.N hμN hdev lm.a lm.Cdig hexact
      constructor
      · rintro ⟨-, hst⟩
        exact (hcyl f B hfdeg hf0 hdev).mpr (hlts.mp hst)
      · intro hsol
        exact ⟨hf0, hlts.mpr ((hcyl f B hfdeg hf0 hdev).mp hsol)⟩
  have e : {x // strat x} ≃ {x // E.IsSolution x} := Equiv.subtypeEquiv Θ hiff
  rw [Nat.card_congr e, LeanUrat.Moves.L2_P6ii (D * N) E, hEk, hzc,
    ← pow_add, Nat.sub_add_cancel hkN]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S17_scratch_with_hcore_hzsol
