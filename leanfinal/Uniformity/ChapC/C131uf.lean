/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C80
import Uniformity.ChapC.C131ag
import Uniformity.ChapC.C53b
import Uniformity.ChapB.B35a
import Uniformity.ChapB.B04

/-!
# Uniformity.ChapC.C131uf — unit U-FEED (af′ plan) + the C.53 wiring

**Part 1 (U-FEED, `docs/in-progress/AF_REVERSE_PLAN_2026-08-25.md` §3/§4).** The plan's
final node: a concrete non-drain locus member at `s2Tower`, `μ₂ = 3` —
`f₀ = Φ₂³ + π⁶xΦ′` — landed via `mem_towerLocus_of_budget` (C.131ae) fed an explicit
`hbud`, with its `j = 0` composed-key digit's level-two height computed exactly (`31`).
This feeds `runs/wave-b/verdict_C123R.md`'s named gap ("no such `f` and no such `hbud` are
landed anywhere in the corpus"): the witness and the `hbud` are now supplied.  Per the
plan's own §4 finding, the FAM-B BAND window is provably EMPTY at both landed (margin-1)
towers — this file lands only the budget/locus facts (membership + the exact digit
height), not any live-band-window claim.

**Part 2 (the C.53 wiring, `runs/wave-b/verdict_RB1.md`'s blocked row).** RB1 found
`towerLocus_fibration_of_leg1` (C53b) needs `h1 : TowerBudgetIff T μ₂`, whose reverse half
(`budget_of_mem_towerLocus`, C.131af′) was not yet landed at the time.  It now is (landed by
unit U-ASSEMBLE, `C131ag.lean`), alongside the already-landed forward half
(`mem_towerLocus_of_budget`, C.131ae).  `TowerBudgetIff T μ₂` is exactly
`Uniformity.Density.Tower.towerLocus_iff_budget`'s statement, so it assembles directly, and
the unconditional signed-shape theorem (`towerLocus_fibration`, matching leanspec
`ChapC.lean:2048-2055`'s hypothesis list byte-for-byte) follows.

## Cite footprint (disclosed up front)

`mem_towerLocus_of_budget` (hence everything built from it: the witness's membership, and
`towerLocus_iff_budget`'s `←` direction, hence `TowerBudgetIff` and `towerLocus_fibration`)
carries the DECLARED literature cite `fgmn_dv_exact_mul` (C66b, allowlist member 7),
inherited via `composedKey_pow_mem_towerLocus` — reported per declaration below, not a new
axiom.  The digit-height computation (`s2Witness_digit_height`) and all pure digit/degree
bookkeeping are Lean-core only.

## Status

Sorry-free, no new axiom.  `lake env lean` run at the bottom (AxCheck footer).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131uf

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C131a Uniformity.Density.Tower.C131k Uniformity.Density.Tower.C131t
open Uniformity.Density.Tower.C131w (dev_zero' le_WT_of_forall_wtCoeff)
open Uniformity.Density.Tower.C131ag (budgetFloor_le_addVal_of_wtCoeff)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-! ## 1. The witness `f₀ = Φ₂³ + π⁶xΦ′` at `s2Tower` -/

/-- The correction term `π⁶xΦ′` (`π = 2`, `Φ′ = (s2Frame h2 hq).key`). -/
noncomputable def s2Extra (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    Polynomial O :=
  Polynomial.C ((2 : O) ^ 6) * Polynomial.X * (s2Frame h2 hq).key

/-- **The AF-7a witness**: `f₀ = Φ₂³ + π⁶xΦ′` at `s2Tower`. -/
noncomputable def s2Witness (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    Polynomial O :=
  composedKey (s2Tower h2 hq) ^ 3 + s2Extra h2 hq

/-! ### Degree bookkeeping -/

theorem s2_key_natDegree (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    (s2Frame h2 hq).key.natDegree = 2 := by
  rw [(s2Frame h2 hq).hdeg, (s2Frame_data h2 hq).1, (s2Frame_data h2 hq).2.1]

theorem s2_composedKey_natDegree (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    (composedKey (s2Tower h2 hq)).natDegree = 4 := by
  rw [composedKey_natDegree_D₂ (s2Tower h2 hq) h2, (s2Tower_data h2 hq).2.2.2.1]

theorem s2Extra_natDegree_lt (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    (s2Extra h2 hq).natDegree < 4 := by
  have hx : (Polynomial.C ((2 : O) ^ 6) * Polynomial.X : Polynomial O).natDegree ≤ 1 := by
    calc (Polynomial.C ((2 : O) ^ 6) * Polynomial.X : Polynomial O).natDegree
        ≤ (Polynomial.C ((2 : O) ^ 6) : Polynomial O).natDegree
            + (Polynomial.X : Polynomial O).natDegree := Polynomial.natDegree_mul_le
      _ = 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
  have hle : (s2Extra h2 hq).natDegree ≤ 3 :=
    Polynomial.natDegree_mul_le_of_le hx (le_of_eq (s2_key_natDegree h2 hq))
  omega

/-! ### The inner (`Φ′`) development of `s2Extra` -/

private theorem s2Extra_shape (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    s2Extra h2 hq
      = (Polynomial.C ((2 : O) ^ 6) * Polynomial.X) * (s2Frame h2 hq).key ^ 1 := by
  rw [s2Extra, pow_one]

theorem s2Extra_dev_zero (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    dev (s2Frame h2 hq).key (s2Extra h2 hq) 0 = 0 := by
  rw [s2Extra_shape h2 hq]
  exact dev_mul_pow_of_lt (s2Frame h2 hq).hmonic 1 _ 0 (by norm_num)

theorem s2Extra_dev_one (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    dev (s2Frame h2 hq).key (s2Extra h2 hq) 1 = Polynomial.C ((2 : O) ^ 6) * Polynomial.X := by
  have hstep := dev_mul_pow (s2Frame h2 hq).hmonic 1 (Polynomial.C ((2 : O) ^ 6) * Polynomial.X) 0
  rw [Nat.add_zero] at hstep
  rw [s2Extra_shape h2 hq, hstep]
  show (Polynomial.C ((2 : O) ^ 6) * Polynomial.X) %ₘ (s2Frame h2 hq).key
    = Polynomial.C ((2 : O) ^ 6) * Polynomial.X
  refine (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr ?_
  refine Polynomial.degree_lt_degree ?_
  rw [s2_key_natDegree h2 hq]
  calc (Polynomial.C ((2 : O) ^ 6) * Polynomial.X : Polynomial O).natDegree
      ≤ (Polynomial.C ((2 : O) ^ 6) : Polynomial O).natDegree
          + (Polynomial.X : Polynomial O).natDegree := Polynomial.natDegree_mul_le
    _ = 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
    _ < 2 := by norm_num

theorem s2Extra_dev_ge_two (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    ∀ b, 2 ≤ b → dev (s2Frame h2 hq).key (s2Extra h2 hq) b = 0 := by
  intro b hb
  have hlt := s2Extra_natDegree_lt h2 hq
  refine dev_eq_zero_of_lt (s2Frame h2 hq).hmonic ?_ (s2Extra h2 hq) b ?_
  · rw [s2_key_natDegree h2 hq]; norm_num
  · rw [s2_key_natDegree h2 hq]
    omega

/-! ### The outer (`Φ₂`) development of `s2Witness` -/

private theorem s2_composedKey_pos (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    0 < (composedKey (s2Tower h2 hq)).natDegree := by
  rw [s2_composedKey_natDegree h2 hq]; norm_num

theorem s2Witness_dev_zero (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    dev (composedKey (s2Tower h2 hq)) (s2Witness h2 hq) 0 = s2Extra h2 hq := by
  have hadd := dev_add_of_monic (composedKey_monic (s2Tower h2 hq))
    (composedKey (s2Tower h2 hq) ^ 3) (s2Extra h2 hq) 0
  have hpow : dev (composedKey (s2Tower h2 hq)) (composedKey (s2Tower h2 hq) ^ 3) 0 = 0 := by
    rw [dev_pow_self (composedKey_monic (s2Tower h2 hq)) (s2_composedKey_pos h2 hq) 3 0,
      if_neg (by norm_num)]
  have hextra : dev (composedKey (s2Tower h2 hq)) (s2Extra h2 hq) 0 = s2Extra h2 hq := by
    change (s2Extra h2 hq) %ₘ (composedKey (s2Tower h2 hq)) = s2Extra h2 hq
    refine (Polynomial.modByMonic_eq_self_iff (composedKey_monic (s2Tower h2 hq))).mpr ?_
    refine Polynomial.degree_lt_degree ?_
    rw [s2_composedKey_natDegree h2 hq]
    exact s2Extra_natDegree_lt h2 hq
  rw [s2Witness, hadd, hpow, hextra, zero_add]

theorem s2Witness_dev_one (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    dev (composedKey (s2Tower h2 hq)) (s2Witness h2 hq) 1 = 0 := by
  have hadd := dev_add_of_monic (composedKey_monic (s2Tower h2 hq))
    (composedKey (s2Tower h2 hq) ^ 3) (s2Extra h2 hq) 1
  have hpow : dev (composedKey (s2Tower h2 hq)) (composedKey (s2Tower h2 hq) ^ 3) 1 = 0 := by
    rw [dev_pow_self (composedKey_monic (s2Tower h2 hq)) (s2_composedKey_pos h2 hq) 3 1,
      if_neg (by norm_num)]
  have hextra : dev (composedKey (s2Tower h2 hq)) (s2Extra h2 hq) 1 = 0 := by
    refine dev_eq_zero_of_lt (composedKey_monic (s2Tower h2 hq)) (s2_composedKey_pos h2 hq)
      (s2Extra h2 hq) 1 ?_
    rw [one_mul, s2_composedKey_natDegree h2 hq]
    exact s2Extra_natDegree_lt h2 hq
  rw [s2Witness, hadd, hpow, hextra, zero_add]

theorem s2Witness_dev_two (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    dev (composedKey (s2Tower h2 hq)) (s2Witness h2 hq) 2 = 0 := by
  have hadd := dev_add_of_monic (composedKey_monic (s2Tower h2 hq))
    (composedKey (s2Tower h2 hq) ^ 3) (s2Extra h2 hq) 2
  have hpow : dev (composedKey (s2Tower h2 hq)) (composedKey (s2Tower h2 hq) ^ 3) 2 = 0 := by
    rw [dev_pow_self (composedKey_monic (s2Tower h2 hq)) (s2_composedKey_pos h2 hq) 3 2,
      if_neg (by norm_num)]
  have hextra : dev (composedKey (s2Tower h2 hq)) (s2Extra h2 hq) 2 = 0 := by
    refine dev_eq_zero_of_lt (composedKey_monic (s2Tower h2 hq)) (s2_composedKey_pos h2 hq)
      (s2Extra h2 hq) 2 ?_
    rw [s2_composedKey_natDegree h2 hq]
    have hlt := s2Extra_natDegree_lt h2 hq
    omega
  rw [s2Witness, hadd, hpow, hextra, zero_add]

/-! ### `s2Witness` is monic of the right degree -/

private theorem s2Extra_degree_lt_pow (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    (s2Extra h2 hq).degree < (composedKey (s2Tower h2 hq) ^ 3).degree := by
  refine Polynomial.degree_lt_degree ?_
  rw [Polynomial.natDegree_pow, s2_composedKey_natDegree h2 hq]
  have hlt := s2Extra_natDegree_lt h2 hq
  omega

theorem s2Witness_monic (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    (s2Witness h2 hq).Monic := by
  rw [s2Witness]
  exact ((composedKey_monic (s2Tower h2 hq)).pow 3).add_of_left (s2Extra_degree_lt_pow h2 hq)

theorem s2Witness_natDegree (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    (s2Witness h2 hq).natDegree = 3 * (s2Tower h2 hq).D₂ := by
  have hdeg : (s2Witness h2 hq).natDegree = (composedKey (s2Tower h2 hq) ^ 3).natDegree := by
    rw [s2Witness]
    exact Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_add_eq_left_of_degree_lt (s2Extra_degree_lt_pow h2 hq))
  rw [hdeg, Polynomial.natDegree_pow, s2_composedKey_natDegree h2 hq,
    (s2Tower_data h2 hq).2.2.2.1]

/-! ## 2. The `hbud` row and membership -/

/-- The numeral bridge for the one live slot `(j, a, b) = (0, 1, 1)`: `wtCoeff = 31`, tight
against the strict floor `(3 − 0)·E₂ + 1 = 31`. -/
private theorem s2_wtCoeff_31 (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    wtCoeff (s2Tower h2 hq) ((2 : O) ^ 6) 1 1 = (31 : ℕ∞) := by
  have he1 : (s2Frame h2 hq).e₁ = 2 := (s2Frame_data h2 hq).1
  have he2 : (s2Tower h2 hq).e₂ = 2 := (s2Tower_data h2 hq).1
  have hh : (s2Frame h2 hq).h = 1 := (s2Frame_data h2 hq).2.2.1
  have hu2 : (s2Tower h2 hq).u₂ = 5 := (s2Tower_data h2 hq).2.2.1
  have haddval : addVal O ((2 : O) ^ 6) = (6 : ℕ∞) := h2.addVal_pow 6
  rw [wtCoeff, haddval, he1, he2, hh, hu2]
  norm_num [nsmul_eq_mul]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] in
private theorem s2_coeff_one (c : O) :
    (Polynomial.C c * Polynomial.X).coeff 1 = c := by simp

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] in
private theorem s2_coeff_zero (c : O) :
    (Polynomial.C c * Polynomial.X).coeff 0 = 0 := by simp

theorem s2Witness_hbud (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    ∀ j a b : ℕ, j < 3 → a < (s2Frame h2 hq).e₁ * (s2Frame h2 hq).f₁ →
      b < (s2Tower h2 hq).e₂ * (s2Tower h2 hq).f₂ →
      (budgetFloor (s2Tower h2 hq) 3 j a b : ℕ∞) ≤
        addVal O ((dev (s2Frame h2 hq).key
          (dev (composedKey (s2Tower h2 hq)) (s2Witness h2 hq) j) b).coeff a) := by
  intro j a b hj ha hb
  rw [(s2Frame_data h2 hq).1, (s2Frame_data h2 hq).2.1] at ha
  rw [(s2Tower_data h2 hq).1, (s2Tower_data h2 hq).2.1] at hb
  norm_num at ha hb
  interval_cases j
  · rw [s2Witness_dev_zero h2 hq]
    interval_cases b
    · rw [s2Extra_dev_zero h2 hq, Polynomial.coeff_zero, addVal_zero]
      exact le_top
    · rw [s2Extra_dev_one h2 hq]
      interval_cases a
      · rw [s2_coeff_zero, addVal_zero]
        exact le_top
      · rw [s2_coeff_one]
        refine budgetFloor_le_addVal_of_wtCoeff (s2Tower h2 hq) ?_
        rw [s2_wtCoeff_31 h2 hq, (s2Tower_data h2 hq).2.2.2.2]
        norm_num
  · rw [s2Witness_dev_one h2 hq, dev_zero', Polynomial.coeff_zero, addVal_zero]
    exact le_top
  · rw [s2Witness_dev_two h2 hq, dev_zero', Polynomial.coeff_zero, addVal_zero]
    exact le_top

/-- **AF-7a — the witness's membership**, disposing `verdict_C123R.md`'s named gap: a
locus member with a non-drain sub-top digit, via `mem_towerLocus_of_budget` (C.131ae) fed
the explicit `hbud` above.  Carries the declared cite `fgmn_dv_exact_mul` (C66b), inherited
through `mem_towerLocus_of_budget`. -/
theorem s2Witness_mem (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    s2Witness h2 hq ∈ towerLocus (s2Tower h2 hq) 3 :=
  mem_towerLocus_of_budget (s2Tower h2 hq) h2 (le_refl 1) (by norm_num)
    (s2Witness_monic h2 hq) (s2Witness_natDegree h2 hq) (s2Witness_hbud h2 hq)

/-! ## 3. The non-drain digit height (AF-7b) -/

/-- **AF-7b — the witness's `j = 0` digit is non-drain, exact height `31`.** The first
landed locus member with a FINITE sub-top composed-key digit (`composedKey T ^ μ₂` itself
is drain everywhere below `μ₂`, `C123r.lean`'s honest disclosure): `dv2Hgt` of the `j = 0`
digit is exactly `Θ_0 = (3 − 0)·E₂ + 1 = 31`, the strict af′ floor realized with equality. -/
theorem s2Witness_digit_height (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    dv2Hgt ((s2Tower h2 hq).levelDatum h2)
      (dev (composedKey (s2Tower h2 hq)) (s2Witness h2 hq) 0) = (31 : ℕ∞) := by
  rw [s2Witness_dev_zero h2 hq, dv2Hgt_eq_WT_phiNF (s2Tower h2 hq) h2]
  apply le_antisymm
  · have hb := WT_le_wtCoeff (s2Tower h2 hq) (xNF (s2Frame h2 hq) (s2Extra h2 hq)) 1 1
    rw [xNF_coeff, xDigit_eq_dev, s2Extra_dev_one h2 hq, s2_coeff_one,
      s2_wtCoeff_31 h2 hq] at hb
    exact hb
  · apply le_WT_of_forall_wtCoeff
    intro a b
    by_cases hcase : a = 1 ∧ b = 1
    · obtain ⟨ha1, hb1⟩ := hcase
      subst ha1; subst hb1
      rw [xNF_coeff, xDigit_eq_dev, s2Extra_dev_one h2 hq, s2_coeff_one, s2_wtCoeff_31 h2 hq]
    · have hz : ((xNF (s2Frame h2 hq) (s2Extra h2 hq)).coeff b).coeff a = 0 := by
        rw [xNF_coeff, xDigit_eq_dev]
        rcases b with _ | _ | b'
        · rw [s2Extra_dev_zero h2 hq, Polynomial.coeff_zero]
        · rw [s2Extra_dev_one h2 hq]
          have ha1 : a ≠ 1 := fun h => hcase ⟨h, rfl⟩
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X, if_neg (Ne.symm ha1), mul_zero]
        · rw [s2Extra_dev_ge_two h2 hq (b' + 2) (by omega), Polynomial.coeff_zero]
      rw [hz, wtCoeff_zero]
      exact le_top

end Uniformity.Density.Tower.C131uf

/-! ## 4. Part 2 — the C.53 wiring: `TowerBudgetIff` assembled, `towerLocus_fibration` landed -/

/-- **`TowerBudgetIff T μ₂`, assembled from both landed halves.** The forward half
(`budget_of_mem_towerLocus`, C.131af′, landed by unit U-ASSEMBLE in `C131ag.lean`) and the
reverse half (`mem_towerLocus_of_budget`, C.131ae) together are exactly
`Uniformity.Density.Tower.towerLocus_iff_budget`'s statement, applied at each monic `f` of
the right degree — precisely `C53.lean`'s `TowerBudgetIff` unfolded. -/
theorem Uniformity.Density.Tower.towerBudgetIff_of_iff
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (IsLocalRing.ResidueField O)] {μ₂ : ℕ} (hμ₂ : 0 < μ₂) :
    TowerBudgetIff T μ₂ :=
  fun _f hf hdeg => towerLocus_iff_budget T hπ hh hμ₂ hf hdeg

/-- **`towerLocus_fibration` (C.53), unconditional** — the signed shape, hypothesis list
byte-identical to leanspec `ChapC.lean:2048-2055` (`axiom → theorem`): `RB1`'s blocked row
(`runs/wave-b/verdict_RB1.md`) needed `h1 : TowerBudgetIff T μ₂` for
`towerLocus_fibration_of_leg1` (C53b); it is now constructed above from both landed
halves, so the wrap is unconditional, with `hh` consumed (through `towerLocus_iff_budget`)
and `[IsAdicComplete …]` genuinely unused (as `towerLocus_fibration_of_leg1` itself never
needs it — the same finding `towerLocus_fibration_of_frontier`'s docstring already records
for `hh`/`hμ₂`). Carries the declared cite `fgmn_dv_exact_mul` (C66b), inherited through
`mem_towerLocus_of_budget`. -/
theorem Uniformity.Density.Tower.towerLocus_fibration
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (μ₂ N : ℕ) (hμ₂ : 0 < μ₂) :
    Nat.card {c : Coeff O (μ₂ * T.D₂) N //
        ∃ a : Fin (μ₂ * T.D₂) → O,
          proj O (μ₂ * T.D₂) N a = c ∧ monicPoly a ∈ towerLocus T μ₂}
      = residueCard O ^ towerFreeCount T μ₂ N :=
  towerLocus_fibration_of_leg1 hπ T hμ₂ N (towerBudgetIff_of_iff T hπ hh hμ₂)

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131uf.s2_key_natDegree
#print axioms Uniformity.Density.Tower.C131uf.s2_composedKey_natDegree
#print axioms Uniformity.Density.Tower.C131uf.s2Extra_natDegree_lt
#print axioms Uniformity.Density.Tower.C131uf.s2Extra_dev_zero
#print axioms Uniformity.Density.Tower.C131uf.s2Extra_dev_one
#print axioms Uniformity.Density.Tower.C131uf.s2Extra_dev_ge_two
#print axioms Uniformity.Density.Tower.C131uf.s2Witness_dev_zero
#print axioms Uniformity.Density.Tower.C131uf.s2Witness_dev_one
#print axioms Uniformity.Density.Tower.C131uf.s2Witness_dev_two
#print axioms Uniformity.Density.Tower.C131uf.s2Witness_monic
#print axioms Uniformity.Density.Tower.C131uf.s2Witness_natDegree
#print axioms Uniformity.Density.Tower.C131uf.s2Witness_hbud
#print axioms Uniformity.Density.Tower.C131uf.s2Witness_mem
#print axioms Uniformity.Density.Tower.C131uf.s2Witness_digit_height
#print axioms Uniformity.Density.Tower.towerBudgetIff_of_iff
#print axioms Uniformity.Density.Tower.towerLocus_fibration

end AxCheck
