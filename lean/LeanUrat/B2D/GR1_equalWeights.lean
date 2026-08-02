/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.GRDefs
import LeanUrat.Scaffold.HDischarge.H1.Order1

/-!
# B2D/GR1_equalWeights — (K1) at the parent stage  [B2DEF_LEAN unit GR-1; wave 2a]

Blueprint §5 GR-1. moves_ref: §B2-DEF D.5 EQUAL WEIGHTS (MOVES :2266–2270).
deps: E1, GR-0 (residue displayed). difficulty: medium.
REUSE: `H1.stage_w_pow`, `H1.stage_degree_pos`, `Stage.hK1` (S2),
`DictIII.devCoeff_eq_of_isDevelopment` (Fact A uniqueness).

**PROVED (wave 2a, 2026-08-02), at the frozen statements, GENERAL `ν.e`** — the
k-freeness of the slot totals is exactly `ReadHyps.hscale` (the R1-C2 fold), and the
attained slot-minimum (`Stage.hK1`) then pins the lift weight without any `e = 1`
collapse: the development of `Φ′` in `σ.Φ` has support on the stride lattice
`{e·k : k ≤ g}`, every nonzero slot totals `e·g·w(σ.Φ)`, and the min is attained at
a nonzero slot (the monic top is always present). N-GR1 run record: blueprint §7
(the harness confirms the frame-face equal-weights law holds iff the read is level —
which is what `hscale` carries; run 2026-08-02, ALL CHECKS PASSED).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.Scaffold.HDischarge.H1

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **GR-1 slot display (D.5 EQUAL WEIGHTS, per slot)**: each present slot's total
weight `w(t_κ·Φ^{e·κ}) = ν.h·(g−κ) + e·κ·w(Φ)` is the k-free value
`e·g·w(σ.Φ)` — the k-freeness is EXACTLY `ReadHyps.hscale` (R1-C2 fold). -/
theorem GR1_slotWeights (ν : Node p F) (R : ReadHyps ν)
    (tt : ℕ → Polynomial ℤ_[p]) (κ : ℕ) (hκ : κ < ν.g)
    (htt0 : tt κ ≠ 0)
    (httw : ν.σ.w (tt κ) = (ν.h : ℤ) * ((ν.g : ℤ) - (κ : ℤ))) :
    ν.σ.w (tt κ * ν.σ.Φ ^ (ν.e * κ)) = (ν.e : ℤ) * (ν.g : ℤ) * ν.σ.w ν.σ.Φ := by
  rw [ν.σ.hwmul _ _ htt0 (pow_ne_zero _ ν.σ.hmonic.ne_zero),
    stage_w_pow ν.σ ν.σ.Φ ν.σ.hmonic.ne_zero, httw, R.hscale]
  push_cast
  ring

/-- The stride-lattice coefficient family of an `IsNodeLift` key: slot `e·k` carries
`tt k` (`k < g`), slot `e·g` carries the monic top `1`, all other slots `0`. -/
private noncomputable def liftBB (ν : Node p F) (tt : ℕ → Polynomial ℤ_[p]) :
    ℕ → Polynomial ℤ_[p] :=
  fun j =>
    if j = ν.e * ν.g then 1
    else if h : ν.e ∣ j ∧ j / ν.e < ν.g then tt (j / ν.e) else 0

/-- The `IsNodeLift` key IS the `liftBB` development (support on the stride lattice,
reindexed through `k ↦ e·k`). -/
private theorem liftBB_isDev (ν : Node p F) (Φ' : Polynomial ℤ_[p])
    (hlift : IsNodeLift ν Φ') :
    ∃ tt : ℕ → Polynomial ℤ_[p],
      (∀ k, ν.ψ.coeff k = 0 → tt k = 0) ∧
      (∀ k, k < ν.g → ν.ψ.coeff k ≠ 0 →
          tt k ≠ 0 ∧ inC ν.σ.Φ (tt k) ∧
            ν.σ.w (tt k) = (ν.h : ℤ) * ((ν.g : ℤ) - (k : ℤ)) ∧
            ν.σ.R (tt k) = LaurentPolynomial.C (ν.ψ.coeff k) *
              LaurentPolynomial.T (- ν.σ.t * ν.σ.wPrev (tt k))) ∧
      IsDevelopment ν.σ.Φ Φ' (liftBB ν tt) (ν.e * ν.g + 1) := by
  classical
  obtain ⟨tt, h0, hcl, heq⟩ := hlift
  have hepos : 0 < ν.e := ν.he
  have hΦdeg : (0 : WithBot ℕ) < ν.σ.Φ.degree := stage_degree_pos ν.σ
  refine ⟨tt, h0, hcl, ?_, ?_, ?_⟩
  · -- degrees: every slot is a coefficient
    intro j
    unfold liftBB
    by_cases hjtop : j = ν.e * ν.g
    · simpa [hjtop, Polynomial.degree_one] using hΦdeg
    · simp only [if_neg hjtop]
      by_cases hj : ν.e ∣ j ∧ j / ν.e < ν.g
      · simp only [dif_pos hj]
        by_cases htt : tt (j / ν.e) = 0
        · rw [htt]; simpa using lt_of_le_of_lt bot_le hΦdeg
        · have hψ : ν.ψ.coeff (j / ν.e) ≠ 0 := fun h => htt (h0 _ h)
          exact (hcl _ hj.2 hψ).2.1
      · simp only [dif_neg hj]
        simpa using lt_of_le_of_lt bot_le hΦdeg
  · -- vanishing beyond the window
    intro j hj
    unfold liftBB
    have hjtop : j ≠ ν.e * ν.g := by omega
    have hj' : ¬ (ν.e ∣ j ∧ j / ν.e < ν.g) := by
      rintro ⟨⟨c, rfl⟩, hlt⟩
      rw [Nat.mul_div_cancel_left c hepos] at hlt
      have : ν.e * c < ν.e * ν.g := (Nat.mul_lt_mul_left hepos).mpr hlt
      omega
    simp [hjtop, hj']
  · -- the sum: reindex the stride lattice
    rw [heq]
    have himg : ∀ j ∈ Finset.range (ν.e * ν.g + 1),
        j ∉ (Finset.range (ν.g + 1)).image (fun k => ν.e * k) →
        liftBB ν tt j * ν.σ.Φ ^ j = 0 := by
      intro j _ hj
      have hjtop : j ≠ ν.e * ν.g := by
        intro h
        exact hj (Finset.mem_image.mpr ⟨ν.g, Finset.mem_range.mpr (by omega), h.symm⟩)
      have hj' : ¬ (ν.e ∣ j ∧ j / ν.e < ν.g) := by
        rintro ⟨⟨c, rfl⟩, hlt⟩
        rw [Nat.mul_div_cancel_left c hepos] at hlt
        exact hj (Finset.mem_image.mpr ⟨c, Finset.mem_range.mpr (by omega), rfl⟩)
      unfold liftBB
      simp [hjtop, hj']
    have hsub : (Finset.range (ν.g + 1)).image (fun k => ν.e * k) ⊆
        Finset.range (ν.e * ν.g + 1) := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      have := Finset.mem_range.mp hk
      exact Finset.mem_range.mpr (by
        have : ν.e * k ≤ ν.e * ν.g := Nat.mul_le_mul_left _ (by omega)
        omega)
    rw [← Finset.sum_subset hsub himg,
      Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hepos h),
      Finset.sum_range_succ]
    have htopBB : liftBB ν tt (ν.e * ν.g) = 1 := by unfold liftBB; simp
    have hmidBB : ∀ k < ν.g, liftBB ν tt (ν.e * k) = tt k := by
      intro k hk
      have hne : ν.e * k ≠ ν.e * ν.g := by
        intro h
        exact absurd (Nat.eq_of_mul_eq_mul_left hepos h) (by omega)
      have hdvd : ν.e ∣ ν.e * k ∧ (ν.e * k) / ν.e < ν.g := by
        constructor
        · exact Dvd.intro k rfl
        · rw [Nat.mul_div_cancel_left k hepos]; exact hk
      unfold liftBB
      rw [if_neg hne, dif_pos hdvd, Nat.mul_div_cancel_left k hepos]
    rw [htopBB, one_mul, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by
      rw [hmidBB k (Finset.mem_range.mp hk)]

/-- An `IsNodeLift` key is nonzero (its monic-top development slot is `1`; Fact A
uniqueness). Consumed by GR-1/GR-4 (the `f ≠ 0` guard of `hK1`/`discharge`). -/
theorem nodeLift_ne_zero (ν : Node p F) (Φ' : Polynomial ℤ_[p])
    (hlift : IsNodeLift ν Φ') : Φ' ≠ 0 := by
  classical
  obtain ⟨tt, h0, hcl, hdev⟩ := liftBB_isDev ν Φ' hlift
  intro habs
  have huniq := LeanUrat.Scaffold.DictIII.devCoeff_eq_of_isDevelopment
    ν.σ.hmonic (ν.e * ν.g + 1) Φ' (liftBB ν tt) hdev (ν.e * ν.g)
  rw [habs] at huniq
  simp only [LeanUrat.Scaffold.DictIII.devCoeff_zero_left] at huniq
  have : liftBB ν tt (ν.e * ν.g) = 1 := by unfold liftBB; simp
  rw [this] at huniq
  simp at huniq

/-- **GR-1 (K1), the key weight at the parent**: `w(Φ′) = e·g·w(σ.Φ)` for any
`IsNodeLift` key — the first `graded_read` clause (blueprint §4). -/
theorem GR1_equalWeights (ν : Node p F) (Φ' : Polynomial ℤ_[p])
    (hlift : IsNodeLift ν Φ') (R : ReadHyps ν) :
    ν.σ.w Φ' = (ν.e : ℤ) * (ν.g : ℤ) * ν.σ.w ν.σ.Φ := by
  classical
  obtain ⟨tt, h0, hcl, hdev⟩ := liftBB_isDev ν Φ' hlift
  have hne : Φ' ≠ 0 := nodeLift_ne_zero ν Φ' hlift
  have hepos : 0 < ν.e := ν.he
  -- every nonzero slot totals e·g·w(Φ)
  have hslot : ∀ j, liftBB ν tt j ≠ 0 →
      ν.σ.w (liftBB ν tt j) + (j : ℤ) * ν.σ.w ν.σ.Φ
        = (ν.e : ℤ) * (ν.g : ℤ) * ν.σ.w ν.σ.Φ := by
    intro j hj
    by_cases hjtop : j = ν.e * ν.g
    · have hBB : liftBB ν tt j = 1 := by unfold liftBB; simp [hjtop]
      have hw1 : ν.σ.w 1 = 0 := by
        have h := ν.σ.hwmul 1 1 one_ne_zero one_ne_zero
        rw [mul_one] at h
        omega
      rw [hBB, hw1, hjtop]
      push_cast
      ring
    · have hj' : ν.e ∣ j ∧ j / ν.e < ν.g := by
        by_contra h
        apply hj
        unfold liftBB
        simp [hjtop, h]
      have hBB : liftBB ν tt j = tt (j / ν.e) := by
        unfold liftBB
        rw [if_neg hjtop, dif_pos hj']
      obtain ⟨c, rfl⟩ := hj'.1
      have hc : (ν.e * c) / ν.e = c := Nat.mul_div_cancel_left c hepos
      rw [hc] at hBB
      have hclt : c < ν.g := by have h2 := hj'.2; rwa [hc] at h2
      have httc : tt c ≠ 0 := by rwa [hBB] at hj
      have hψc : ν.ψ.coeff c ≠ 0 := fun h => httc (h0 _ h)
      obtain ⟨-, -, hw, -⟩ := hcl c hclt hψc
      rw [hBB, hw, R.hscale]
      push_cast
      ring
  -- the slot minimum is attained (hK1) at a nonzero slot, whose total is the k-free value
  obtain ⟨-, j, hjlt, hjnz, hjeq⟩ := ν.σ.hK1 Φ' (liftBB ν tt) (ν.e * ν.g + 1) hne hdev
  rw [hjeq]
  exact hslot j hjnz

end LeanUrat.B2D

#print axioms LeanUrat.B2D.GR1_slotWeights
#print axioms LeanUrat.B2D.nodeLift_ne_zero
#print axioms LeanUrat.B2D.GR1_equalWeights
