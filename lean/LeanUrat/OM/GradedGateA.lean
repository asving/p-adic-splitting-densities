/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.GradedHensel
import LeanUrat.OM.GradedMargin
import LeanUrat.OM.LinearFiber
import LeanUrat.OM.SparseResultant

/-!
# GradedGateA — the case-A (p=2, N=5) concrete deep-wild graded gate

ONE concrete gate (case A, p=2, N=5); an honest non-vacuous instance of the graded margin M0,
NOT the general census — general M0 stays the numerically-gated obligation
`ProductTheorem.obligation_hensel_surjective`.

This is the case-A analogue of `GradedHensel.caseB_upgrade`/`caseB_ker_card`.  The gate blocks
are `(e, m) = (1, 2)` and `(2, 4)`, cross-shares `S = (2, 1)`, `c = 4`, `N = 5`.  It is the gate
whose FLAT margin `gate_margin_A` is empty (`¬(2·4 < 5)`), so the GRADED margin is what carries it.

The pattern cosets are x-slot boxes around the polygon centers `A₀ = (X-2)² = X²-4X+4`
(monic quadratic) and `B₀ = (X²-2)² = X⁴-4X²+4` (monic quartic), at the graded floors
`floA = (3, 2)`, `floB = (3, 2, 2, 1)`; the pinned graded kernel depths are `depA = (3, 2)`,
`depB = (4, 4, 3, 3)` (`GradedHensel.gate_margin_graded_A`).

`caseA_upgrade` discharges the pointwise graded margin at EVERY cell point by hand Gaussian
elimination: the triangular `X²,…,X⁵` rows eliminate the quartic increment `β` (unit pivots),
leaving a reduced `2×2` α-system whose diagonal is `2²·unit`; four annihilator rounds
(`LinearFiber.exists_mul_pow_of_pow_mul_eq_zero`) drive `α` to depth `(3, 3)`, whence `β` inherits
`(4, 4, 3, 3)` by back-substitution.  No `decide` on the linearization; no `native_decide`.
`caseA_ker_card` counts the polynomial kernel (`2⁴ = p^c`).

Discipline: no `sorry`/`axiom`/`native_decide`; core-only footprints; no existing module touched.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace LeanUrat.OM.GradedGateA

open Polynomial
open LeanUrat.OM
open LeanUrat.OM.HenselCount
open LeanUrat.OM.BlockProduct
open LeanUrat.OM.GradedHensel

private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

private instance : Fact (1 < 2 ^ 5) := ⟨by norm_num⟩

/-! ## Scalar helpers over `ZMod 32` -/

private theorem h32 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 5 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

/-! ### Small-degree coefficient helpers over `ZMod 32` -/

private theorem coeff_lin₀ (u v : (ZMod (2 ^ 5))) : (C u + C v * X).coeff 0 = u := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]

private theorem coeff_lin₁ (u v : (ZMod (2 ^ 5))) : (C u + C v * X).coeff 1 = v := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]

private theorem coeff_lin_top (u v : (ZMod (2 ^ 5))) {i : ℕ} (hi : 2 ≤ i) :
    (C u + C v * X).coeff i = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), Polynomial.coeff_C_mul,
    Polynomial.coeff_X, if_neg (by omega), mul_zero, add_zero]

private theorem eq_lin {α : (ZMod (2 ^ 5))[X]} (htop : ∀ i, 2 ≤ i → α.coeff i = 0) :
    α = C (α.coeff 0) + C (α.coeff 1) * X := by
  ext i
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · rw [coeff_lin₀]
    · rw [coeff_lin₁]
  · rw [htop i hi, coeff_lin_top _ _ hi]

private theorem coeff_quad₀ (u v : (ZMod (2 ^ 5))) : (X ^ 2 + (C u + C v * X)).coeff 0 = u := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_lin₀, zero_add]

private theorem coeff_quad₁ (u v : (ZMod (2 ^ 5))) : (X ^ 2 + (C u + C v * X)).coeff 1 = v := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_lin₁, zero_add]

private theorem coeff_quad₂ (u v : (ZMod (2 ^ 5))) : (X ^ 2 + (C u + C v * X)).coeff 2 = 1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl, coeff_lin_top _ _ le_rfl, add_zero]

private theorem coeff_quad_top (u v : (ZMod (2 ^ 5))) {i : ℕ} (hi : 3 ≤ i) :
    (X ^ 2 + (C u + C v * X)).coeff i = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega),
    coeff_lin_top _ _ (by omega), add_zero]

private theorem eq_quad {A : (ZMod (2 ^ 5))[X]} (h2 : A.coeff 2 = 1)
    (h3 : ∀ i, 3 ≤ i → A.coeff i = 0) :
    A = X ^ 2 + (C (A.coeff 0) + C (A.coeff 1) * X) := by
  ext i
  rcases Nat.lt_or_ge i 3 with hi | hi
  · interval_cases i
    · rw [coeff_quad₀]
    · rw [coeff_quad₁]
    · rw [coeff_quad₂, h2]
  · rw [h3 i hi, coeff_quad_top _ _ hi]

private theorem coeff_cub₀ (c0 c1 c2 c3 : (ZMod (2 ^ 5))) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).coeff 0 = c0 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub₁ (c0 c1 c2 c3 : (ZMod (2 ^ 5))) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).coeff 1 = c1 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub₂ (c0 c1 c2 c3 : (ZMod (2 ^ 5))) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).coeff 2 = c2 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub₃ (c0 c1 c2 c3 : (ZMod (2 ^ 5))) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).coeff 3 = c3 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_cub_top (c0 c1 c2 c3 : (ZMod (2 ^ 5))) {i : ℕ} (hi : 4 ≤ i) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3).coeff i = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_C, if_neg (by omega),
    Polynomial.coeff_C_mul, Polynomial.coeff_X, if_neg (by omega),
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega),
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
  ring

private theorem eq_cub {β : (ZMod (2 ^ 5))[X]} (htop : ∀ i, 4 ≤ i → β.coeff i = 0) :
    β = C (β.coeff 0) + C (β.coeff 1) * X + C (β.coeff 2) * X ^ 2 + C (β.coeff 3) * X ^ 3 := by
  ext i
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · rw [coeff_cub₀]
    · rw [coeff_cub₁]
    · rw [coeff_cub₂]
    · rw [coeff_cub₃]
  · rw [htop i hi, coeff_cub_top _ _ _ _ hi]

private theorem coeff_quar₀ (b0 b1 b2 b3 : (ZMod (2 ^ 5))) :
    (X ^ 4 + (C b0 + C b1 * X + C b2 * X ^ 2 + C b3 * X ^ 3)).coeff 0 = b0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_cub₀, zero_add]

private theorem coeff_quar₁ (b0 b1 b2 b3 : (ZMod (2 ^ 5))) :
    (X ^ 4 + (C b0 + C b1 * X + C b2 * X ^ 2 + C b3 * X ^ 3)).coeff 1 = b1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_cub₁, zero_add]

private theorem coeff_quar₂ (b0 b1 b2 b3 : (ZMod (2 ^ 5))) :
    (X ^ 4 + (C b0 + C b1 * X + C b2 * X ^ 2 + C b3 * X ^ 3)).coeff 2 = b2 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_cub₂, zero_add]

private theorem coeff_quar₃ (b0 b1 b2 b3 : (ZMod (2 ^ 5))) :
    (X ^ 4 + (C b0 + C b1 * X + C b2 * X ^ 2 + C b3 * X ^ 3)).coeff 3 = b3 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), coeff_cub₃, zero_add]

private theorem coeff_quar₄ (b0 b1 b2 b3 : (ZMod (2 ^ 5))) :
    (X ^ 4 + (C b0 + C b1 * X + C b2 * X ^ 2 + C b3 * X ^ 3)).coeff 4 = 1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl, coeff_cub_top _ _ _ _ le_rfl, add_zero]

private theorem coeff_quar_top (b0 b1 b2 b3 : (ZMod (2 ^ 5))) {i : ℕ} (hi : 5 ≤ i) :
    (X ^ 4 + (C b0 + C b1 * X + C b2 * X ^ 2 + C b3 * X ^ 3)).coeff i = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega),
    coeff_cub_top _ _ _ _ (by omega), add_zero]

private theorem eq_quar {B : (ZMod (2 ^ 5))[X]} (h4 : B.coeff 4 = 1)
    (h5 : ∀ i, 5 ≤ i → B.coeff i = 0) :
    B = X ^ 4 + (C (B.coeff 0) + C (B.coeff 1) * X + C (B.coeff 2) * X ^ 2 + C (B.coeff 3) * X ^ 3) := by
  ext i
  rcases Nat.lt_or_ge i 5 with hi | hi
  · interval_cases i
    · rw [coeff_quar₀]
    · rw [coeff_quar₁]
    · rw [coeff_quar₂]
    · rw [coeff_quar₃]
    · rw [coeff_quar₄, h4]
  · rw [h5 i hi, coeff_quar_top _ _ _ _ hi]

/-! ### Quintic normal-form coefficient extractors -/

private theorem coeff_quint₀ (c0 c1 c2 c3 c4 c5 : (ZMod (2 ^ 5))) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 + C c5 * X ^ 5).coeff 0 = c0 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint₁ (c0 c1 c2 c3 c4 c5 : (ZMod (2 ^ 5))) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 + C c5 * X ^ 5).coeff 1 = c1 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint₂ (c0 c1 c2 c3 c4 c5 : (ZMod (2 ^ 5))) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 + C c5 * X ^ 5).coeff 2 = c2 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint₃ (c0 c1 c2 c3 c4 c5 : (ZMod (2 ^ 5))) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 + C c5 * X ^ 5).coeff 3 = c3 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint₄ (c0 c1 c2 c3 c4 c5 : (ZMod (2 ^ 5))) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 + C c5 * X ^ 5).coeff 4 = c4 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint₅ (c0 c1 c2 c3 c4 c5 : (ZMod (2 ^ 5))) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 + C c5 * X ^ 5).coeff 5 = c5 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]

private theorem coeff_quint_top (c0 c1 c2 c3 c4 c5 : (ZMod (2 ^ 5))) {i : ℕ} (hi : 6 ≤ i) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 + C c5 * X ^ 5).coeff i = 0 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]
  ring

/-- **The quadratic×quartic linearization identity**: `B·α + A·β` in quintic normal form. -/
private theorem combo_eq {A B α β : (ZMod (2 ^ 5))[X]}
    (hA2 : A.coeff 2 = 1) (hA3 : ∀ i, 3 ≤ i → A.coeff i = 0)
    (hB4 : B.coeff 4 = 1) (hB5 : ∀ i, 5 ≤ i → B.coeff i = 0)
    (hαtop : ∀ i, 2 ≤ i → α.coeff i = 0) (hβtop : ∀ i, 4 ≤ i → β.coeff i = 0) :
    B * α + A * β
      = C ((A.coeff 0)*(β.coeff 0) + (α.coeff 0)*(B.coeff 0))
        + C ((A.coeff 0)*(β.coeff 1) + (A.coeff 1)*(β.coeff 0) + (α.coeff 0)*(B.coeff 1) + (α.coeff 1)*(B.coeff 0)) * X
        + C ((A.coeff 0)*(β.coeff 2) + (A.coeff 1)*(β.coeff 1) + (α.coeff 0)*(B.coeff 2) + (α.coeff 1)*(B.coeff 1) + (β.coeff 0)) * X ^ 2
        + C ((A.coeff 0)*(β.coeff 3) + (A.coeff 1)*(β.coeff 2) + (α.coeff 0)*(B.coeff 3) + (α.coeff 1)*(B.coeff 2) + (β.coeff 1)) * X ^ 3
        + C ((A.coeff 1)*(β.coeff 3) + (α.coeff 0) + (α.coeff 1)*(B.coeff 3) + (β.coeff 2)) * X ^ 4
        + C ((α.coeff 1) + (β.coeff 3)) * X ^ 5
        := by
  conv_lhs => rw [eq_quad hA2 hA3, eq_quar hB4 hB5, eq_lin hαtop, eq_cub hβtop]
  simp only [map_add, map_mul]
  ring


/-! ### The case-A cell data (p = 2, N = 5) -/

/-- Case-A first center `A₀ = (X-2)² = X² - 4X + 4` over `ZMod 32` (monic quadratic). -/
noncomputable def aA₀ : (ZMod (2 ^ 5))[X] := X ^ 2 + (C (4 : ZMod (2 ^ 5)) + C (-4) * X)

/-- Case-A second center `B₀ = (X²-2)² = X⁴ - 4X² + 4` over `ZMod 32` (monic quartic). -/
noncomputable def aB₀ : (ZMod (2 ^ 5))[X] :=
  X ^ 4 + (C (4 : ZMod (2 ^ 5)) + C 0 * X + C (-4) * X ^ 2 + C 0 * X ^ 3)

/-- The pinned case-A block-A x-slot floors `(3, 2)`. -/
def aFloA : ℕ → ℕ := sideFloor 1 2

/-- The pinned case-A block-B x-slot floors `(3, 2, 2, 1)`. -/
def aFloB : ℕ → ℕ := sideFloor 2 4

/-- The pinned case-A block-A graded kernel depths `(3, 2)` (`S = 2`). -/
def aDepA : ℕ → ℕ := sideDepth 1 2 5

/-- The pinned case-A block-B graded kernel depths `(4, 4, 3, 3)` (`S = 1`). -/
def aDepB : ℕ → ℕ := sideDepth 2 1 5

/-- The pinned case-A conv floor `(6, 5, 4, 4, 3)` (padded by `N = 5` beyond the support). -/
def aQb : ℕ → ℕ := fun r =>
  if r = 0 then 6 else if r = 1 then 5 else if r = 2 then 4 else if r = 3 then 4
  else if r = 4 then 3 else 5

/-- The case-A pattern coset of the first decided block (quadratic), an x-slot box. -/
noncomputable def aSA : Set ((ZMod (2 ^ 5))[X]) := patternCell (p := 2) (N := 5) aA₀ 2 aFloA

/-- The case-A pattern coset of the second decided block (quartic). -/
noncomputable def aSB : Set ((ZMod (2 ^ 5))[X]) := patternCell (p := 2) (N := 5) aB₀ 4 aFloB

private theorem hM1A : ∀ i, aFloA i ≤ aDepA i := by
  intro i
  simp only [aFloA, aDepA, sideFloor, sideDepth, cdiv]
  omega

private theorem hM1B : ∀ i, aFloB i ≤ aDepB i := by
  intro i
  simp only [aFloB, aDepB, sideFloor, sideDepth, cdiv]
  have hdi : i / 2 ≤ i := Nat.div_le_self i 2
  have hdi2 : 2 * (i / 2) ≤ i := Nat.mul_div_le i 2
  omega

private theorem hM2A : ∀ s t : ℕ, s < 2 → t < 4 → 5 ≤ aDepA s + aDepB t := by
  intro s t hs ht
  simp only [aDepA, aDepB, sideDepth]
  interval_cases s <;> interval_cases t <;> decide

private theorem hqbA : ∀ s t : ℕ, s < 2 → t < 4 → aQb (s + t) ≤ aFloA s + aFloB t := by
  intro s t hs ht
  simp only [aQb, aFloA, aFloB, sideFloor, cdiv]
  interval_cases s <;> interval_cases t <;> decide


/-! ### Membership facts for the case-A cosets -/

/-- Membership facts for the block-A (quadratic) coset around center `X² - 4X + 4`. -/
private theorem aSA_facts {A : (ZMod (2 ^ 5))[X]} (hA : A ∈ aSA) :
    A.coeff 2 = 1 ∧ (∀ i, 3 ≤ i → A.coeff i = 0)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ A.coeff 0 - 4)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ A.coeff 1 + 4) := by
  obtain ⟨hmon, hdeg, hdvd⟩ := hA
  have h2 : A.coeff 2 = 1 := by
    have h := hmon.coeff_natDegree; rw [hdeg] at h; exact h
  have h3 : ∀ i, 3 ≤ i → A.coeff i = 0 := fun i hi =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
  refine ⟨h2, h3, ?_, ?_⟩
  · have h := hdvd 0
    rw [Polynomial.coeff_sub] at h
    have hc : (aA₀).coeff 0 = 4 := by
      simp only [aA₀]; rw [coeff_quad₀]
    rw [hc] at h
    have hf : aFloA 0 = 3 := by decide
    rwa [hf] at h
  · have h := hdvd 1
    rw [Polynomial.coeff_sub] at h
    have hc : (aA₀).coeff 1 = -4 := by
      simp only [aA₀]; rw [coeff_quad₁]
    rw [hc] at h
    have hf : aFloA 1 = 2 := by decide
    rw [hf] at h
    rwa [sub_neg_eq_add] at h

/-- Membership facts for the block-B (quartic) coset around center `X⁴ - 4X² + 4`. -/
private theorem aSB_facts {B : (ZMod (2 ^ 5))[X]} (hB : B ∈ aSB) :
    B.coeff 4 = 1 ∧ (∀ i, 5 ≤ i → B.coeff i = 0)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ B.coeff 0 - 4)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 1)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 2 + 4)
      ∧ (((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ B.coeff 3) := by
  obtain ⟨hmon, hdeg, hdvd⟩ := hB
  have h4 : B.coeff 4 = 1 := by
    have h := hmon.coeff_natDegree; rw [hdeg] at h; exact h
  have h5 : ∀ i, 5 ≤ i → B.coeff i = 0 := fun i hi =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
  have hc0 : (aB₀).coeff 0 = 4 := by simp only [aB₀]; rw [coeff_quar₀]
  have hc1 : (aB₀).coeff 1 = 0 := by simp only [aB₀]; rw [coeff_quar₁]
  have hc2 : (aB₀).coeff 2 = -4 := by simp only [aB₀]; rw [coeff_quar₂]
  have hc3 : (aB₀).coeff 3 = 0 := by simp only [aB₀]; rw [coeff_quar₃]
  refine ⟨h4, h5, ?_, ?_, ?_, ?_⟩
  · have h := hdvd 0
    rw [Polynomial.coeff_sub, hc0, show aFloB 0 = 3 from by decide] at h
    exact h
  · have h := hdvd 1
    rw [Polynomial.coeff_sub, hc1, sub_zero, show aFloB 1 = 2 from by decide] at h
    exact h
  · have h := hdvd 2
    rw [Polynomial.coeff_sub, hc2, show aFloB 2 = 2 from by decide] at h
    rwa [sub_neg_eq_add] at h
  · have h := hdvd 3
    rw [Polynomial.coeff_sub, hc3, sub_zero, show aFloB 3 = 1 from by decide] at h
    exact h


/-! ### Scalar divisibility helpers over `ZMod 32` -/

/-- `x·y = 0` in `ZMod 32` when the valuations sum to `≥ 5`. -/
private theorem mul_kill {x y : ZMod (2 ^ 5)} {i j : ℕ} (hij : 5 ≤ i + j)
    (hx : ((2 : ℕ) : ZMod (2 ^ 5)) ^ i ∣ x) (hy : ((2 : ℕ) : ZMod (2 ^ 5)) ^ j ∣ y) :
    x * y = 0 := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  rw [hu, hv]
  have hz : ((2 : ℕ) : ZMod (2 ^ 5)) ^ (i + j) = 0 := by
    rw [← Nat.sub_add_cancel hij, pow_add, h32, mul_zero]
  calc ((2 : ℕ) : ZMod (2 ^ 5)) ^ i * u * (((2 : ℕ) : ZMod (2 ^ 5)) ^ j * v)
      = ((2 : ℕ) : ZMod (2 ^ 5)) ^ (i + j) * (u * v) := by rw [pow_add]; ring
    _ = 0 := by rw [hz, zero_mul]

/-- `1 + 2·k` is a unit of `ZMod 32`. -/
private theorem isUnit_one_add_two_mul (k : ZMod (2 ^ 5)) :
    IsUnit (1 + ((2 : ℕ) : ZMod (2 ^ 5)) * k) := by
  have hnil : IsNilpotent (((2 : ℕ) : ZMod (2 ^ 5)) * k) :=
    ⟨5, by rw [mul_pow, h32, zero_mul]⟩
  exact hnil.isUnit_add_left_of_commute isUnit_one (Commute.all _ _)

/-- `2^k ∣ x·y` when the valuations sum to `≥ k`. -/
private theorem mul_dvd_pow {x y : ZMod (2 ^ 5)} {i j k : ℕ} (hk : k ≤ i + j)
    (hx : ((2 : ℕ) : ZMod (2 ^ 5)) ^ i ∣ x) (hy : ((2 : ℕ) : ZMod (2 ^ 5)) ^ j ∣ y) :
    ((2 : ℕ) : ZMod (2 ^ 5)) ^ k ∣ x * y := by
  have := mul_dvd_mul hx hy
  rw [← pow_add] at this
  exact dvd_trans (pow_dvd_pow _ hk) this

/-- Divisibility transfers across multiplication by a unit. -/
private theorem dvd_of_isUnit_mul {w x d : ZMod (2 ^ 5)} (hw : IsUnit w)
    (h : d ∣ w * x) : d ∣ x := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(hw.unit⁻¹ : (ZMod (2 ^ 5))ˣ) * c, ?_⟩
  calc x = (hw.unit⁻¹ : (ZMod (2 ^ 5))ˣ) * ((hw.unit : ZMod (2 ^ 5)) * x) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = (hw.unit⁻¹ : (ZMod (2 ^ 5))ˣ) * (w * x) := by rw [IsUnit.unit_spec]
    _ = d * ((hw.unit⁻¹ : (ZMod (2 ^ 5))ˣ) * c) := by rw [hc]; ring

/-! ### The pointwise graded margin at every case-A cell point -/

/-- **Case-A pointwise graded upgrade** (the certificate bootstrap, at EVERY point of the
quadratic and quartic pattern cosets): the triangular `X²,…,X⁵` rows eliminate the quartic
increment `β` (unit pivots), leaving a reduced `2×2` α-system with diagonal `2²·unit`; four
annihilator rounds drive `α` to depth `(3, 3)`, whence `β` inherits `(4, 4, 3, 3)`.  No `decide`. -/
private theorem caseA_pointwise : ∀ A ∈ aSA, ∀ B ∈ aSB,
    ∀ α β Y : (ZMod (2 ^ 5))[X], (∀ i, 2 ≤ i → α.coeff i = 0) → (∀ i, 4 ≤ i → β.coeff i = 0) →
      B * α + A * β = Y → (∀ i, ((2 : ℕ) : ZMod (2 ^ 5)) ^ aQb i ∣ Y.coeff i) →
      ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ α.coeff 0 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ α.coeff 1
        ∧ ∀ i, ((2 : ℕ) : ZMod (2 ^ 5)) ^ aDepB i ∣ β.coeff i := by
  intro A hA B hB α β Y hαtop hβtop hcombo hY
  obtain ⟨hA2, hA3, hA0, hA1⟩ := aSA_facts hA
  obtain ⟨hB4, hB5, hB0, hB1, hB2, hB3⟩ := aSB_facts hB
  rw [combo_eq hA2 hA3 hB4 hB5 hαtop hβtop] at hcombo
  -- the six coefficient equations
  have e0 : (A.coeff 0)*(β.coeff 0) + (α.coeff 0)*(B.coeff 0) = Y.coeff 0 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 0) hcombo
    rwa [coeff_quint₀] at h
  have e1 : (A.coeff 0)*(β.coeff 1) + (A.coeff 1)*(β.coeff 0) + (α.coeff 0)*(B.coeff 1) + (α.coeff 1)*(B.coeff 0) = Y.coeff 1 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 1) hcombo
    rwa [coeff_quint₁] at h
  have e2 : (A.coeff 0)*(β.coeff 2) + (A.coeff 1)*(β.coeff 1) + (α.coeff 0)*(B.coeff 2) + (α.coeff 1)*(B.coeff 1) + (β.coeff 0) = Y.coeff 2 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 2) hcombo
    rwa [coeff_quint₂] at h
  have e3 : (A.coeff 0)*(β.coeff 3) + (A.coeff 1)*(β.coeff 2) + (α.coeff 0)*(B.coeff 3) + (α.coeff 1)*(B.coeff 2) + (β.coeff 1) = Y.coeff 3 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 3) hcombo
    rwa [coeff_quint₃] at h
  have e4 : (A.coeff 1)*(β.coeff 3) + (α.coeff 0) + (α.coeff 1)*(B.coeff 3) + (β.coeff 2) = Y.coeff 4 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 4) hcombo
    rwa [coeff_quint₄] at h
  have e5 : (α.coeff 1) + (β.coeff 3) = Y.coeff 5 := by
    have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 5) hcombo
    rwa [coeff_quint₅] at h
  -- conv-floor RHS facts
  have hy0 : Y.coeff 0 = 0 := by
    have h := hY 0; rw [show aQb 0 = 6 by decide] at h
    obtain ⟨z, hz⟩ := h
    rw [hz, show ((2 : ℕ) : ZMod (2 ^ 5)) ^ 6 = ((2 : ℕ) : ZMod (2 ^ 5)) ^ 5 * ((2 : ℕ) : ZMod (2 ^ 5)) from by ring, h32, zero_mul, zero_mul]
  have hy1 : Y.coeff 1 = 0 := by
    have h := hY 1; rw [show aQb 1 = 5 by decide] at h
    obtain ⟨z, hz⟩ := h; rw [hz, h32, zero_mul]
  have hy5 : Y.coeff 5 = 0 := by
    have h := hY 5; rw [show aQb 5 = 5 by decide] at h
    obtain ⟨z, hz⟩ := h; rw [hz, h32, zero_mul]
  have hy2 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ Y.coeff 2 := by
    have h := hY 2; rwa [show aQb 2 = 4 by decide] at h
  have hy3 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ Y.coeff 3 := by
    have h := hY 3; rwa [show aQb 3 = 4 by decide] at h
  have hy4 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ Y.coeff 4 := by
    have h := hY 4; rwa [show aQb 4 = 3 by decide] at h
  rw [hy0] at e0; rw [hy1] at e1; rw [hy5] at e5
  -- base coefficient divisibilities
  have hda0 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ A.coeff 0 := by
    have : A.coeff 0 = (A.coeff 0 - 4) + 4 := by ring
    rw [this]; exact dvd_add (dvd_trans (pow_dvd_pow _ (by norm_num)) hA0) ⟨1, by norm_num⟩
  have hda1 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ A.coeff 1 := by
    have : A.coeff 1 = (A.coeff 1 + 4) - 4 := by ring
    rw [this]; exact dvd_sub hA1 ⟨1, by norm_num⟩
  have hdb0 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 0 := by
    have : B.coeff 0 = (B.coeff 0 - 4) + 4 := by ring
    rw [this]; exact dvd_add (dvd_trans (pow_dvd_pow _ (by norm_num)) hB0) ⟨1, by norm_num⟩
  have hdb1 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 1 := hB1
  have hdb2 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ B.coeff 2 := by
    have : B.coeff 2 = (B.coeff 2 + 4) - 4 := by ring
    rw [this]; exact dvd_sub hB2 ⟨1, by norm_num⟩
  have hdb3 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 1 ∣ B.coeff 3 := hB3
  -- derived power divisibilities for the reduced matrix entries
  have hda0sq : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ (A.coeff 0)^2 := by
    rw [sq]; have := mul_dvd_mul hda0 hda0; rwa [← pow_add] at this
  -- reduced RHS vanish (R0y = 0, R1y = 0)
  have hk_a0Y2 : (A.coeff 0) * Y.coeff 2 = 0 := mul_kill (by norm_num) hda0 hy2
  have hk_a0Y3 : (A.coeff 0) * Y.coeff 3 = 0 := mul_kill (by norm_num) hda0 hy3
  have hk_a1Y2 : (A.coeff 1) * Y.coeff 2 = 0 := mul_kill (by norm_num) hda1 hy2
  have hk_a1Y3 : (A.coeff 1) * Y.coeff 3 = 0 := mul_kill (by norm_num) hda1 hy3
  have hk_a0sqY4 : (A.coeff 0)^2 * Y.coeff 4 = 0 := mul_kill (by norm_num) hda0sq hy4
  have hk_a0a1Y3 : (A.coeff 0) * (A.coeff 1) * Y.coeff 3 = 0 := by
    have h : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ (A.coeff 0) * (A.coeff 1) := by
      have := mul_dvd_mul hda0 hda1; rwa [← pow_add] at this
    exact mul_kill (by norm_num) h hy3
  have hk_a0a1sqY4 : (A.coeff 0) * (A.coeff 1)^2 * Y.coeff 4 = 0 := by
    have h : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 6 ∣ (A.coeff 0) * (A.coeff 1)^2 := by
      have h2 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ (A.coeff 1)^2 := by
        rw [sq]; have := mul_dvd_mul hda1 hda1; rwa [← pow_add] at this
      have := mul_dvd_mul hda0 h2; rwa [← pow_add] at this
    exact mul_kill (by norm_num) h hy4
  have hk_a1cubeY4 : (A.coeff 1)^3 * Y.coeff 4 = 0 := by
    have h : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 6 ∣ (A.coeff 1)^3 := by
      have heq : ((A.coeff 1))^3 = (A.coeff 1) * (A.coeff 1) * (A.coeff 1) := by ring
      rw [heq]
      have h2 := mul_dvd_mul (mul_dvd_mul hda1 hda1) hda1
      rwa [← pow_add, ← pow_add] at h2
    exact mul_kill (by norm_num) h hy4
  have hk_a1sqY3 : (A.coeff 1)^2 * Y.coeff 3 = 0 := by
    have h : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ (A.coeff 1)^2 := by
      rw [sq]; have := mul_dvd_mul hda1 hda1; rwa [← pow_add] at this
    exact mul_kill (by norm_num) h hy3
  have hk_a0a1Y4 : (A.coeff 0) * (A.coeff 1) * Y.coeff 4 = 0 := by
    have h : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ (A.coeff 0) * (A.coeff 1) := by
      have := mul_dvd_mul hda0 hda1; rwa [← pow_add] at this
    exact mul_kill (by norm_num) h hy4
  -- the reduced (β-eliminated) 2×2 α-system, homogeneous (deep RHS vanished)
  have hE0raw : ((A.coeff 0)^2 - (A.coeff 0)*(A.coeff 1)^2 + (A.coeff 0)*(A.coeff 1)*(B.coeff 3) - (A.coeff 0)*(B.coeff 2) + (B.coeff 0)) * (α.coeff 0)
      + (-2*(A.coeff 0)^2*(A.coeff 1) + (A.coeff 0)^2*(B.coeff 3) + (A.coeff 0)*(A.coeff 1)^3 - (A.coeff 0)*(A.coeff 1)^2*(B.coeff 3) + (A.coeff 0)*(A.coeff 1)*(B.coeff 2) - (A.coeff 0)*(B.coeff 1)) * (α.coeff 1) = 0 := by
    linear_combination e0 + (-(A.coeff 0))*e2 + ((A.coeff 0)*(A.coeff 1))*e3
      + ((A.coeff 0)^2 - (A.coeff 0)*(A.coeff 1)^2)*e4
      + (-2*(A.coeff 0)^2*(A.coeff 1) + (A.coeff 0)*(A.coeff 1)^3)*e5
      + hk_a0sqY4 - hk_a0a1sqY4 + hk_a0a1Y3 - hk_a0Y2
  have hE1raw : (2*(A.coeff 0)*(A.coeff 1) - (A.coeff 0)*(B.coeff 3) - (A.coeff 1)^3 + (A.coeff 1)^2*(B.coeff 3) - (A.coeff 1)*(B.coeff 2) + (B.coeff 1)) * (α.coeff 0)
      + ((A.coeff 0)^2 - 3*(A.coeff 0)*(A.coeff 1)^2 + 2*(A.coeff 0)*(A.coeff 1)*(B.coeff 3) - (A.coeff 0)*(B.coeff 2) + (A.coeff 1)^4 - (A.coeff 1)^3*(B.coeff 3) + (A.coeff 1)^2*(B.coeff 2) - (A.coeff 1)*(B.coeff 1) + (B.coeff 0)) * (α.coeff 1) = 0 := by
    linear_combination e1 + (-(A.coeff 1))*e2 + (-(A.coeff 0) + (A.coeff 1)^2)*e3
      + (2*(A.coeff 0)*(A.coeff 1) - (A.coeff 1)^3)*e4
      + ((A.coeff 0)^2 - 3*(A.coeff 0)*(A.coeff 1)^2 + (A.coeff 1)^4)*e5
      + 2*hk_a0a1Y4 - hk_a0Y3 - hk_a1cubeY4 + hk_a1sqY3 - hk_a1Y2
  -- reduced-matrix 2-power structure (Dvd facts; witnesses in the decomposition)
  obtain ⟨s, hs⟩ := id hA0
  obtain ⟨ap, hap⟩ := id hA1
  obtain ⟨t, ht⟩ := id hB0
  obtain ⟨q1, hq1⟩ := id hB1
  obtain ⟨q2, hq2⟩ := id hB2
  obtain ⟨q3, hq3⟩ := id hB3
  -- M00 - 4 = 2³·w0
  have hDM00 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣
      ((A.coeff 0)^2 - (A.coeff 0)*(A.coeff 1)^2 + (A.coeff 0)*(A.coeff 1)*(B.coeff 3) - (A.coeff 0)*(B.coeff 2) + (B.coeff 0)) - 4 := by
    refine ⟨(-16*ap^2*s - 8*ap^2 + 8*ap*q3*s + 4*ap*q3 + 32*ap*s + 16*ap - 4*q2*s - 2*q2 - 8*q3*s - 4*q3 + 8*s^2 - 4*s + t - 4), ?_⟩
    linear_combination ((A.coeff 0) - (A.coeff 1)^2 + (A.coeff 1)*(B.coeff 3) - (B.coeff 2) + 8*s + 4)*hs + (-8*(A.coeff 1)*s - 4*(A.coeff 1) - 32*ap*s - 16*ap + 8*(B.coeff 3)*s + 4*(B.coeff 3) + 32*s + 16)*hap + (1:ZMod (2^5))*ht + (-8*s - 4)*hq2 + (32*ap*s + 16*ap - 32*s - 16)*hq3
  have hDM11 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣
      ((A.coeff 0)^2 - 3*(A.coeff 0)*(A.coeff 1)^2 + 2*(A.coeff 0)*(A.coeff 1)*(B.coeff 3) - (A.coeff 0)*(B.coeff 2) + (A.coeff 1)^4 - (A.coeff 1)^3*(B.coeff 3) + (A.coeff 1)^2*(B.coeff 2) - (A.coeff 1)*(B.coeff 1) + (B.coeff 0)) - 4 := by
    refine ⟨(32*ap^4 - 16*ap^3*q3 - 128*ap^3 + 8*ap^2*q2 + 48*ap^2*q3 - 48*ap^2*s + 160*ap^2 - 2*ap*q1 - 16*ap*q2 + 16*ap*q3*s - 40*ap*q3 + 96*ap*s - 64*ap + 2*q1 - 4*q2*s + 6*q2 - 16*q3*s + 8*q3 + 8*s^2 - 36*s + t + 4), ?_⟩
    linear_combination ((A.coeff 0) - 3*(A.coeff 1)^2 + 2*(A.coeff 1)*(B.coeff 3) - (B.coeff 2) + 8*s + 4)*hs + ((A.coeff 1)^3 + 4*(A.coeff 1)^2*ap - (A.coeff 1)^2*(B.coeff 3) - 4*(A.coeff 1)^2 + 16*(A.coeff 1)*ap^2 - 4*(A.coeff 1)*ap*(B.coeff 3) - 32*(A.coeff 1)*ap + (A.coeff 1)*(B.coeff 2) + 4*(A.coeff 1)*(B.coeff 3) - 24*(A.coeff 1)*s + 4*(A.coeff 1) + 64*ap^3 - 16*ap^2*(B.coeff 3) - 192*ap^2 + 4*ap*(B.coeff 2) + 32*ap*(B.coeff 3) - 96*ap*s + 144*ap - (B.coeff 1) - 4*(B.coeff 2) + 16*(B.coeff 3)*s - 8*(B.coeff 3) + 96*s - 16)*hap + (1:ZMod (2^5))*ht + (4 - 4*ap)*hq1 + (16*ap^2 - 32*ap - 8*s + 12)*hq2 + (-64*ap^3 + 192*ap^2 + 64*ap*s - 160*ap - 64*s + 32)*hq3
  have hDM01 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣
      (-2*(A.coeff 0)^2*(A.coeff 1) + (A.coeff 0)^2*(B.coeff 3) + (A.coeff 0)*(A.coeff 1)^3 - (A.coeff 0)*(A.coeff 1)^2*(B.coeff 3) + (A.coeff 0)*(A.coeff 1)*(B.coeff 2) - (A.coeff 0)*(B.coeff 1)) := by
    refine ⟨(32*ap^3*s + 16*ap^3 - 16*ap^2*q3*s - 8*ap^2*q3 - 96*ap^2*s - 48*ap^2 + 8*ap*q2*s + 4*ap*q2 + 32*ap*q3*s + 16*ap*q3 - 32*ap*s^2 + 56*ap*s + 36*ap - 2*q1*s - q1 - 8*q2*s - 4*q2 + 8*q3*s^2 - 8*q3*s - 6*q3 + 32*s^2 + 8*s - 4), ?_⟩
    linear_combination (-2*(A.coeff 0)*(A.coeff 1) + (A.coeff 0)*(B.coeff 3) + (A.coeff 1)^3 - (A.coeff 1)^2*(B.coeff 3) + (A.coeff 1)*(B.coeff 2) - 16*(A.coeff 1)*s - 8*(A.coeff 1) - (B.coeff 1) + 8*(B.coeff 3)*s + 4*(B.coeff 3))*hs + (8*(A.coeff 1)^2*s + 4*(A.coeff 1)^2 + 32*(A.coeff 1)*ap*s + 16*(A.coeff 1)*ap - 8*(A.coeff 1)*(B.coeff 3)*s - 4*(A.coeff 1)*(B.coeff 3) - 32*(A.coeff 1)*s - 16*(A.coeff 1) + 128*ap^2*s + 64*ap^2 - 32*ap*(B.coeff 3)*s - 16*ap*(B.coeff 3) - 256*ap*s - 128*ap + 8*(B.coeff 2)*s + 4*(B.coeff 2) + 32*(B.coeff 3)*s + 16*(B.coeff 3) - 128*s^2 + 32)*hap + (-8*s - 4)*hq1 + (32*ap*s + 16*ap - 32*s - 16)*hq2 + (-128*ap^2*s - 64*ap^2 + 256*ap*s + 128*ap + 64*s^2 - 64*s - 48)*hq3
  have hDM10 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣
      (2*(A.coeff 0)*(A.coeff 1) - (A.coeff 0)*(B.coeff 3) - (A.coeff 1)^3 + (A.coeff 1)^2*(B.coeff 3) - (A.coeff 1)*(B.coeff 2) + (B.coeff 1)) := by
    refine ⟨(-16*ap^3 + 8*ap^2*q3 + 48*ap^2 - 4*ap*q2 - 16*ap*q3 + 16*ap*s - 36*ap + q1 + 4*q2 - 4*q3*s + 6*q3 - 16*s + 4), ?_⟩
    linear_combination (2*(A.coeff 1) - (B.coeff 3))*hs + (-(A.coeff 1)^2 - 4*(A.coeff 1)*ap + (A.coeff 1)*(B.coeff 3) + 4*(A.coeff 1) - 16*ap^2 + 4*ap*(B.coeff 3) + 32*ap - (B.coeff 2) - 4*(B.coeff 3) + 16*s - 8)*hap + (1:ZMod (2^5))*hq1 + (4 - 4*ap)*hq2 + (16*ap^2 - 32*ap - 8*s + 12)*hq3
  -- expose units and off-diagonal scalings
  obtain ⟨w0, hw0⟩ := hDM00
  obtain ⟨w1, hw1⟩ := hDM11
  obtain ⟨mM01, hmM01⟩ := hDM01
  obtain ⟨mM10, hmM10⟩ := hDM10
  set u0 : ZMod (2 ^ 5) := 1 + ((2 : ℕ) : ZMod (2 ^ 5)) * w0 with hu0def
  set u1 : ZMod (2 ^ 5) := 1 + ((2 : ℕ) : ZMod (2 ^ 5)) * w1 with hu1def
  have hu0 : IsUnit u0 := isUnit_one_add_two_mul w0
  have hu1 : IsUnit u1 := isUnit_one_add_two_mul w1
  -- M00 = 4·u0, M11 = 4·u1  (from hw0/hw1: M00 - 4 = 2³·w0)
  -- the reduced equations become 4·(u0·α0 + 4·mM01·α1) = 0 and 4·(mM10·α0 + u1·α1) = 0
  have hA' : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 * (u0 * α.coeff 0 + ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 * (mM01 * α.coeff 1)) = 0 := by
    rw [hu0def]; linear_combination hE0raw - (α.coeff 0) * hw0 - (α.coeff 1) * hmM01
  have hB' : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 * (mM10 * α.coeff 0 + u1 * α.coeff 1) = 0 := by
    rw [hu1def]; linear_combination hE1raw - (α.coeff 0) * hmM10 - (α.coeff 1) * hw1
  -- extract the two round witnesses
  obtain ⟨zA, hzA⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (p := 2) (N := 5) (by norm_num) hA'
  obtain ⟨zB, hzB⟩ := LinearFiber.exists_mul_pow_of_pow_mul_eq_zero (p := 2) (N := 5) (by norm_num) hB'
  -- hzA : u0*α0 + 4*mM01*α1 = 2^3 * zA ; hzB : mM10*α0 + u1*α1 = 2^3 * zB
  -- Round A: 2² | α0
  have hα0d2 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ α.coeff 0 := by
    refine dvd_of_isUnit_mul hu0 ⟨((2 : ℕ) : ZMod (2 ^ 5)) * zA - mM01 * α.coeff 1, ?_⟩
    linear_combination hzA
  -- Round B: 2² | α1
  obtain ⟨cA, hcA⟩ := hα0d2
  have hα1d2 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ α.coeff 1 := by
    refine dvd_of_isUnit_mul hu1 ⟨((2 : ℕ) : ZMod (2 ^ 5)) * zB - mM10 * cA, ?_⟩
    linear_combination hzB - mM10 * hcA
  -- Round C: 2³ | α0
  obtain ⟨cB, hcB⟩ := hα1d2
  have hα0 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ α.coeff 0 := by
    refine dvd_of_isUnit_mul hu0 ⟨zA - ((2 : ℕ) : ZMod (2 ^ 5)) * (mM01 * cB), ?_⟩
    linear_combination hzA - ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 * mM01 * hcB
  -- Round D: 2³ | α1
  obtain ⟨cC, hcC⟩ := id hα0
  have hα1 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ α.coeff 1 := by
    refine dvd_of_isUnit_mul hu1 ⟨zB - mM10 * cC, ?_⟩
    linear_combination hzB - mM10 * hcC
  -- β back-substitution: β3 = -α1, β2 = ..., β1 = ..., β0 = ...  (depths (4,4,3,3))
  have hβ3 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ β.coeff 3 := by
    have he : β.coeff 3 = -(α.coeff 1) := by linear_combination e5
    rw [he]; exact (dvd_neg).mpr hα1
  have hβ2 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ β.coeff 2 := by
    -- β2 = Y4 - α0 - α1·B.coeff3 - A.coeff1·β3
    have he : β.coeff 2 = Y.coeff 4 - α.coeff 0 - (α.coeff 1)*(B.coeff 3) - (A.coeff 1)*(β.coeff 3) := by
      linear_combination e4
    rw [he]
    refine dvd_sub (dvd_sub (dvd_sub hy4 hα0) ?_) ?_
    · exact mul_dvd_pow (i := 3) (j := 0) (by norm_num) hα1 (one_dvd _)
    · exact mul_dvd_pow (i := 2) (j := 3) (by norm_num) hda1 hβ3
  have hβ1 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ β.coeff 1 := by
    -- β1 = Y3 - A.coeff0·β3 - A.coeff1·β2 - α0·B.coeff3 - α1·B.coeff2
    have he : β.coeff 1 = Y.coeff 3 - (A.coeff 0)*(β.coeff 3) - (A.coeff 1)*(β.coeff 2) - (α.coeff 0)*(B.coeff 3) - (α.coeff 1)*(B.coeff 2) := by
      linear_combination e3
    rw [he]
    refine dvd_sub (dvd_sub (dvd_sub (dvd_sub hy3 ?_) ?_) ?_) ?_
    · exact mul_dvd_pow (i := 2) (j := 3) (by norm_num) hda0 hβ3
    · exact mul_dvd_pow (i := 2) (j := 3) (by norm_num) hda1 hβ2
    · exact mul_dvd_pow (i := 3) (j := 1) (by norm_num) hα0 hdb3
    · exact mul_dvd_pow (i := 3) (j := 2) (by norm_num) hα1 hdb2
  have hβ0 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ β.coeff 0 := by
    -- β0 = Y2 - A.coeff1·β1 - A.coeff0·β2 - α0·B.coeff2 - α1·B.coeff1
    have he : β.coeff 0 = Y.coeff 2 - (A.coeff 1)*(β.coeff 1) - (A.coeff 0)*(β.coeff 2) - (α.coeff 0)*(B.coeff 2) - (α.coeff 1)*(B.coeff 1) := by
      linear_combination e2
    rw [he]
    refine dvd_sub (dvd_sub (dvd_sub (dvd_sub hy2 ?_) ?_) ?_) ?_
    · exact mul_dvd_pow (i := 2) (j := 4) (by norm_num) hda1 hβ1
    · exact mul_dvd_pow (i := 2) (j := 3) (by norm_num) hda0 hβ2
    · exact mul_dvd_pow (i := 3) (j := 2) (by norm_num) hα0 hdb2
    · exact mul_dvd_pow (i := 3) (j := 2) (by norm_num) hα1 hdb1
  -- assemble the strong per-slot conclusion (α at depth (3,3); β at (4,4,3,3))
  refine ⟨hα0, hα1, fun i => ?_⟩
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · show ((2 : ℕ) : ZMod (2 ^ 5)) ^ (aDepB 0) ∣ β.coeff 0
      rw [show aDepB 0 = 4 by decide]; exact hβ0
    · show ((2 : ℕ) : ZMod (2 ^ 5)) ^ (aDepB 1) ∣ β.coeff 1
      rw [show aDepB 1 = 4 by decide]; exact hβ1
    · show ((2 : ℕ) : ZMod (2 ^ 5)) ^ (aDepB 2) ∣ β.coeff 2
      rw [show aDepB 2 = 3 by decide]; exact hβ2
    · show ((2 : ℕ) : ZMod (2 ^ 5)) ^ (aDepB 3) ∣ β.coeff 3
      rw [show aDepB 3 = 3 by decide]; exact hβ3
  · rw [hβtop i hi]; exact dvd_zero _

/-- **Case-A pointwise graded upgrade** at every cell point — the required deliverable, at the
pinned depths `aDepA = (3, 2)`, `aDepB = (4, 4, 3, 3)`.  A thin weakening of `caseA_pointwise`
(which proves the tight `α` depth `(3, 3)`). -/
theorem caseA_upgrade : ∀ A ∈ aSA, ∀ B ∈ aSB,
    GradedUpgradeAt (p := 2) (N := 5) A B 2 4 aDepA aDepB aQb := by
  intro A hA B hB α β Y hαtop hβtop hcombo hY
  obtain ⟨hα0, hα1, hβ⟩ := caseA_pointwise A hA B hB α β Y hαtop hβtop hcombo hY
  refine ⟨fun i => ?_, hβ⟩
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · show ((2 : ℕ) : ZMod (2 ^ 5)) ^ (aDepA 0) ∣ α.coeff 0
      rw [show aDepA 0 = 3 by decide]; exact hα0
    · show ((2 : ℕ) : ZMod (2 ^ 5)) ^ (aDepA 1) ∣ α.coeff 1
      rw [show aDepA 1 = 2 by decide]; exact dvd_trans (pow_dvd_pow _ (by norm_num)) hα1
  · rw [hαtop i hi]; exact dvd_zero _


/-! ### Kernel count -/

private theorem dvd8_iff_val (x : ZMod (2 ^ 5)) :
    ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ x ↔ x.val % 8 = 0 := by
  rw [RestartEquiv.pow_dvd_iff_dvd_val 2 5 (by norm_num) x]
  norm_num [Nat.dvd_iff_mod_eq_zero]

set_option maxRecDepth 40000 in
private theorem caseA_box_card :
    Nat.card {z : ZMod (2 ^ 5) × ZMod (2 ^ 5) //
      ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.2} = 2 ^ 4 := by
  have he : ∀ z : ZMod (2 ^ 5) × ZMod (2 ^ 5),
      (((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.2)
        ↔ (z.1.val % 8 = 0 ∧ z.2.val % 8 = 0) := by
    intro z; rw [dvd8_iff_val, dvd8_iff_val]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

/-- **Case-A kernel count** (the gate's torsor): at EVERY point of the two cosets the
polynomial kernel has exactly `2⁴ = p^c` elements — the graph of the explicit linear section
`(α₀, α₁) ↦ β` over the depth-`(3, 3)` box `{2³ ∣ z₁ ∧ 2³ ∣ z₂}`. -/
theorem caseA_ker_card : ∀ A ∈ aSA, ∀ B ∈ aSB,
    Nat.card {q : (ZMod (2 ^ 5))[X] × (ZMod (2 ^ 5))[X] //
      q ∈ polyKer (p := 2) (N := 5) A B 2 4} = 2 ^ 4 := by
  intro A hA B hB
  obtain ⟨hA2, hA3, hA0, hA1⟩ := aSA_facts hA
  obtain ⟨hB4, hB5, hB0, hB1, hB2, hB3⟩ := aSB_facts hB
  obtain ⟨s, hs⟩ := id hA0
  obtain ⟨ap, hap⟩ := id hA1
  obtain ⟨t, ht⟩ := id hB0
  obtain ⟨q1, hq1⟩ := id hB1
  obtain ⟨q2, hq2⟩ := id hB2
  obtain ⟨q3, hq3⟩ := id hB3
  have hDM00 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ ((A.coeff 0)^2 - (A.coeff 0)*(A.coeff 1)^2 + (A.coeff 0)*(A.coeff 1)*(B.coeff 3) - (A.coeff 0)*(B.coeff 2) + (B.coeff 0)) := by
    refine ⟨-32*ap^2*s - 16*ap^2 + 16*ap*q3*s + 8*ap*q3 + 64*ap*s + 32*ap - 8*q2*s - 4*q2 - 16*q3*s - 8*q3 + 16*s^2 - 8*s + 2*t - 7, ?_⟩
    linear_combination ((A.coeff 0) - (A.coeff 1)^2 + (A.coeff 1)*(B.coeff 3) - (B.coeff 2) + 8*s + 4)*hs + (-8*(A.coeff 1)*s - 4*(A.coeff 1) - 32*ap*s - 16*ap + 8*(B.coeff 3)*s + 4*(B.coeff 3) + 32*s + 16)*hap + (1)*ht + (-8*s - 4)*hq2 + (32*ap*s + 16*ap - 32*s - 16)*hq3
  have hDM01 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 4 ∣ (-2*(A.coeff 0)^2*(A.coeff 1) + (A.coeff 0)^2*(B.coeff 3) + (A.coeff 0)*(A.coeff 1)^3 - (A.coeff 0)*(A.coeff 1)^2*(B.coeff 3) + (A.coeff 0)*(A.coeff 1)*(B.coeff 2) - (A.coeff 0)*(B.coeff 1)) := by
    refine ⟨32*ap^3*s + 16*ap^3 - 16*ap^2*q3*s - 8*ap^2*q3 - 96*ap^2*s - 48*ap^2 + 8*ap*q2*s + 4*ap*q2 + 32*ap*q3*s + 16*ap*q3 - 32*ap*s^2 + 56*ap*s + 36*ap - 2*q1*s - q1 - 8*q2*s - 4*q2 + 8*q3*s^2 - 8*q3*s - 6*q3 + 32*s^2 + 8*s - 4, ?_⟩
    linear_combination (-2*(A.coeff 0)*(A.coeff 1) + (A.coeff 0)*(B.coeff 3) + (A.coeff 1)^3 - (A.coeff 1)^2*(B.coeff 3) + (A.coeff 1)*(B.coeff 2) - 16*(A.coeff 1)*s - 8*(A.coeff 1) - (B.coeff 1) + 8*(B.coeff 3)*s + 4*(B.coeff 3))*hs + (8*(A.coeff 1)^2*s + 4*(A.coeff 1)^2 + 32*(A.coeff 1)*ap*s + 16*(A.coeff 1)*ap - 8*(A.coeff 1)*(B.coeff 3)*s - 4*(A.coeff 1)*(B.coeff 3) - 32*(A.coeff 1)*s - 16*(A.coeff 1) + 128*ap^2*s + 64*ap^2 - 32*ap*(B.coeff 3)*s - 16*ap*(B.coeff 3) - 256*ap*s - 128*ap + 8*(B.coeff 2)*s + 4*(B.coeff 2) + 32*(B.coeff 3)*s + 16*(B.coeff 3) - 128*s^2 + 32)*hap + (-8*s - 4)*hq1 + (32*ap*s + 16*ap - 32*s - 16)*hq2 + (-128*ap^2*s - 64*ap^2 + 256*ap*s + 128*ap + 64*s^2 - 64*s - 48)*hq3
  have hDM10 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ (2*(A.coeff 0)*(A.coeff 1) - (A.coeff 0)*(B.coeff 3) - (A.coeff 1)^3 + (A.coeff 1)^2*(B.coeff 3) - (A.coeff 1)*(B.coeff 2) + (B.coeff 1)) := by
    refine ⟨-16*ap^3 + 8*ap^2*q3 + 48*ap^2 - 4*ap*q2 - 16*ap*q3 + 16*ap*s - 36*ap + q1 + 4*q2 - 4*q3*s + 6*q3 - 16*s + 4, ?_⟩
    linear_combination (2*(A.coeff 1) - (B.coeff 3))*hs + (-(A.coeff 1)^2 - 4*(A.coeff 1)*ap + (A.coeff 1)*(B.coeff 3) + 4*(A.coeff 1) - 16*ap^2 + 4*ap*(B.coeff 3) + 32*ap - (B.coeff 2) - 4*(B.coeff 3) + 16*s - 8)*hap + (1)*hq1 + (4 - 4*ap)*hq2 + (16*ap^2 - 32*ap - 8*s + 12)*hq3
  have hDM11 : ((2 : ℕ) : ZMod (2 ^ 5)) ^ 2 ∣ ((A.coeff 0)^2 - 3*(A.coeff 0)*(A.coeff 1)^2 + 2*(A.coeff 0)*(A.coeff 1)*(B.coeff 3) - (A.coeff 0)*(B.coeff 2) + (A.coeff 1)^4 - (A.coeff 1)^3*(B.coeff 3) + (A.coeff 1)^2*(B.coeff 2) - (A.coeff 1)*(B.coeff 1) + (B.coeff 0)) := by
    refine ⟨64*ap^4 - 32*ap^3*q3 - 256*ap^3 + 16*ap^2*q2 + 96*ap^2*q3 - 96*ap^2*s + 320*ap^2 - 4*ap*q1 - 32*ap*q2 + 32*ap*q3*s - 80*ap*q3 + 192*ap*s - 128*ap + 4*q1 - 8*q2*s + 12*q2 - 32*q3*s + 16*q3 + 16*s^2 - 72*s + 2*t + 9, ?_⟩
    linear_combination ((A.coeff 0) - 3*(A.coeff 1)^2 + 2*(A.coeff 1)*(B.coeff 3) - (B.coeff 2) + 8*s + 4)*hs + ((A.coeff 1)^3 + 4*(A.coeff 1)^2*ap - (A.coeff 1)^2*(B.coeff 3) - 4*(A.coeff 1)^2 + 16*(A.coeff 1)*ap^2 - 4*(A.coeff 1)*ap*(B.coeff 3) - 32*(A.coeff 1)*ap + (A.coeff 1)*(B.coeff 2) + 4*(A.coeff 1)*(B.coeff 3) - 24*(A.coeff 1)*s + 4*(A.coeff 1) + 64*ap^3 - 16*ap^2*(B.coeff 3) - 192*ap^2 + 4*ap*(B.coeff 2) + 32*ap*(B.coeff 3) - 96*ap*s + 144*ap - (B.coeff 1) - 4*(B.coeff 2) + 16*(B.coeff 3)*s - 8*(B.coeff 3) + 96*s - 16)*hap + (1)*ht + (4 - 4*ap)*hq1 + (16*ap^2 - 32*ap - 8*s + 12)*hq2 + (-64*ap^3 + 192*ap^2 + 64*ap*s - 160*ap - 64*s + 32)*hq3
  -- c0 = M00·z1 + M01·z2 and c1 = M10·z1 + M11·z2 vanish given 2³|z1, 2³|z2
  have e : {q : (ZMod (2 ^ 5))[X] × (ZMod (2 ^ 5))[X] //
        q ∈ polyKer (p := 2) (N := 5) A B 2 4}
      ≃ {z : ZMod (2 ^ 5) × ZMod (2 ^ 5) //
          ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.1 ∧ ((2 : ℕ) : ZMod (2 ^ 5)) ^ 3 ∣ z.2} :=
    { toFun := fun q => ⟨(q.1.1.coeff 0, q.1.1.coeff 1), by
        obtain ⟨hq1, hq2, hq3⟩ := q.2
        have h := caseA_pointwise A hA B hB q.1.1 q.1.2 0 hq1 hq2 hq3
          (fun i => by rw [Polynomial.coeff_zero]; exact dvd_zero _)
        exact ⟨h.1, h.2.1⟩⟩
      invFun := fun z => ⟨(C z.1.1 + C z.1.2 * X,
        C (-2*(A.coeff 0)*(A.coeff 1)*z.1.2 + (A.coeff 0)*(B.coeff 3)*z.1.2 + (A.coeff 0)*z.1.1 + (A.coeff 1)^3*z.1.2 - (A.coeff 1)^2*(B.coeff 3)*z.1.2 - (A.coeff 1)^2*z.1.1 + (A.coeff 1)*(B.coeff 2)*z.1.2 + (A.coeff 1)*(B.coeff 3)*z.1.1 - (B.coeff 1)*z.1.2 - (B.coeff 2)*z.1.1)
          + C ((A.coeff 0)*z.1.2 - (A.coeff 1)^2*z.1.2 + (A.coeff 1)*(B.coeff 3)*z.1.2 + (A.coeff 1)*z.1.1 - (B.coeff 2)*z.1.2 - (B.coeff 3)*z.1.1) * X
          + C ((A.coeff 1)*z.1.2 - (B.coeff 3)*z.1.2 - z.1.1) * X ^ 2
          + C (-z.1.2) * X ^ 3), by
        obtain ⟨hz1, hz2⟩ := z.2
        have hc0 : ((A.coeff 0)^2 - (A.coeff 0)*(A.coeff 1)^2 + (A.coeff 0)*(A.coeff 1)*(B.coeff 3) - (A.coeff 0)*(B.coeff 2) + (B.coeff 0)) * z.1.1
            + (-2*(A.coeff 0)^2*(A.coeff 1) + (A.coeff 0)^2*(B.coeff 3) + (A.coeff 0)*(A.coeff 1)^3 - (A.coeff 0)*(A.coeff 1)^2*(B.coeff 3) + (A.coeff 0)*(A.coeff 1)*(B.coeff 2) - (A.coeff 0)*(B.coeff 1)) * z.1.2 = 0 := by
          rw [mul_kill (i := 2) (j := 3) (by norm_num) hDM00 hz1,
            mul_kill (i := 4) (j := 3) (by norm_num) hDM01 hz2, add_zero]
        have hc1 : (2*(A.coeff 0)*(A.coeff 1) - (A.coeff 0)*(B.coeff 3) - (A.coeff 1)^3 + (A.coeff 1)^2*(B.coeff 3) - (A.coeff 1)*(B.coeff 2) + (B.coeff 1)) * z.1.1
            + ((A.coeff 0)^2 - 3*(A.coeff 0)*(A.coeff 1)^2 + 2*(A.coeff 0)*(A.coeff 1)*(B.coeff 3) - (A.coeff 0)*(B.coeff 2) + (A.coeff 1)^4 - (A.coeff 1)^3*(B.coeff 3) + (A.coeff 1)^2*(B.coeff 2) - (A.coeff 1)*(B.coeff 1) + (B.coeff 0)) * z.1.2 = 0 := by
          rw [mul_kill (i := 2) (j := 3) (by norm_num) hDM10 hz1,
            mul_kill (i := 2) (j := 3) (by norm_num) hDM11 hz2, add_zero]
        refine ⟨fun i hi => coeff_lin_top _ _ hi, fun i hi => coeff_cub_top _ _ _ _ hi, ?_⟩
        rw [combo_eq hA2 hA3 hB4 hB5 (fun i hi => coeff_lin_top _ _ hi)
          (fun i hi => coeff_cub_top _ _ _ _ hi)]
        ext k
        rcases Nat.lt_or_ge k 6 with hk | hk
        · interval_cases k
          · rw [coeff_quint₀, Polynomial.coeff_zero]
            simp only [coeff_lin₀, coeff_lin₁, coeff_cub₀, coeff_cub₁, coeff_cub₂, coeff_cub₃]
            linear_combination hc0
          · rw [coeff_quint₁, Polynomial.coeff_zero]
            simp only [coeff_lin₀, coeff_lin₁, coeff_cub₀, coeff_cub₁, coeff_cub₂, coeff_cub₃]
            linear_combination hc1
          · rw [coeff_quint₂, Polynomial.coeff_zero]
            simp only [coeff_lin₀, coeff_lin₁, coeff_cub₀, coeff_cub₁, coeff_cub₂, coeff_cub₃]
            ring
          · rw [coeff_quint₃, Polynomial.coeff_zero]
            simp only [coeff_lin₀, coeff_lin₁, coeff_cub₀, coeff_cub₁, coeff_cub₂, coeff_cub₃]
            ring
          · rw [coeff_quint₄, Polynomial.coeff_zero]
            simp only [coeff_lin₀, coeff_lin₁, coeff_cub₀, coeff_cub₁, coeff_cub₂, coeff_cub₃]
            ring
          · rw [coeff_quint₅, Polynomial.coeff_zero]
            simp only [coeff_lin₀, coeff_lin₁, coeff_cub₀, coeff_cub₁, coeff_cub₂, coeff_cub₃]
            ring
        · rw [coeff_quint_top _ _ _ _ _ _ hk, Polynomial.coeff_zero]⟩
      left_inv := by
        rintro ⟨⟨α, β⟩, hq1, hq2, hq3⟩
        apply Subtype.ext
        dsimp only
        rw [combo_eq hA2 hA3 hB4 hB5 hq1 hq2] at hq3
        have e5z : α.coeff 1 + β.coeff 3 = 0 := by
          have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 5) hq3
          rwa [coeff_quint₅, Polynomial.coeff_zero] at h
        have e4z : (A.coeff 1)*(β.coeff 3) + α.coeff 0 + (α.coeff 1)*(B.coeff 3) + β.coeff 2 = 0 := by
          have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 4) hq3
          rwa [coeff_quint₄, Polynomial.coeff_zero] at h
        have e3z : (A.coeff 0)*(β.coeff 3) + (A.coeff 1)*(β.coeff 2) + (α.coeff 0)*(B.coeff 3) + (α.coeff 1)*(B.coeff 2) + β.coeff 1 = 0 := by
          have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 3) hq3
          rwa [coeff_quint₃, Polynomial.coeff_zero] at h
        have e2z : (A.coeff 0)*(β.coeff 2) + (A.coeff 1)*(β.coeff 1) + (α.coeff 0)*(B.coeff 2) + (α.coeff 1)*(B.coeff 1) + β.coeff 0 = 0 := by
          have h := congrArg (fun P : (ZMod (2 ^ 5))[X] => P.coeff 2) hq3
          rwa [coeff_quint₂, Polynomial.coeff_zero] at h
        have hβ3 : β.coeff 3 = -(α.coeff 1) := by linear_combination e5z
        have hβ2 : β.coeff 2 = (A.coeff 1)*(α.coeff 1) - (B.coeff 3)*(α.coeff 1) - (α.coeff 0) := by
          linear_combination e4z - (A.coeff 1)*hβ3
        have hβ1 : β.coeff 1 = (A.coeff 0)*(α.coeff 1) - (A.coeff 1)^2*(α.coeff 1) + (A.coeff 1)*(B.coeff 3)*(α.coeff 1) + (A.coeff 1)*(α.coeff 0) - (B.coeff 2)*(α.coeff 1) - (B.coeff 3)*(α.coeff 0) := by
          linear_combination e3z - (A.coeff 1)*hβ2 - (A.coeff 0)*hβ3
        have hβ0 : β.coeff 0 = -2*(A.coeff 0)*(A.coeff 1)*(α.coeff 1) + (A.coeff 0)*(B.coeff 3)*(α.coeff 1) + (A.coeff 0)*(α.coeff 0) + (A.coeff 1)^3*(α.coeff 1) - (A.coeff 1)^2*(B.coeff 3)*(α.coeff 1) - (A.coeff 1)^2*(α.coeff 0) + (A.coeff 1)*(B.coeff 2)*(α.coeff 1) + (A.coeff 1)*(B.coeff 3)*(α.coeff 0) - (B.coeff 1)*(α.coeff 1) - (B.coeff 2)*(α.coeff 0) := by
          linear_combination e2z - (A.coeff 0)*hβ2 - (A.coeff 1)*hβ1
        have hαr : C (α.coeff 0) + C (α.coeff 1) * X = α := (eq_lin hq1).symm
        have hβr : C (β.coeff 0) + C (β.coeff 1) * X + C (β.coeff 2) * X ^ 2 + C (β.coeff 3) * X ^ 3 = β := (eq_cub hq2).symm
        rw [hβ0, hβ1, hβ2, hβ3] at hβr
        rw [hαr, hβr]
      right_inv := fun z => by
        apply Subtype.ext; dsimp only; rw [coeff_lin₀, coeff_lin₁] }
  rw [Nat.card_congr e]
  exact caseA_box_card

-- Footprint checks: must be ⊆ [propext, Classical.choice, Quot.sound].
#print axioms caseA_upgrade
#print axioms caseA_ker_card

end LeanUrat.OM.GradedGateA
