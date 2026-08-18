/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Codex 5.6
-/
import Uniformity.ChapC.C128

/-!
# Uniformity.ChapC.C128b2 — C.128 (B2): top-coordinate census and heights

This module transcribes the fully specified census and height calculations of §§4–5 of
`LAWBS2_PROOF_2026-08-16.md` using the vocabulary landed in `Uniformity.ChapC.C128`.

## BLOCKED boundary

The exact three-branch chain census, three slot values, unit-height calculations, bottom-slot
arithmetic, congruence swap, signed top index, and top threshold are landed below.  Turning this
census into `lawBS2_pair_or_triple` still requires B1's identity identifying the actual
`shadowDev` discrepancy with `red (R_j(T̂))`.  The source gives no exact non-binomial `T̂`
formula (see `C128b1.lean`), so this module does not assume that identity or manufacture a
capstone from it.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf Polynomial

/-! ## The three surviving branches (§4) -/

section TopChain

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The pair, triple, and quad seeds after the wrap-depth filter from B1.  `A`, `B`, and `Q`
include their multinomial digits and coefficient powers; the triple's `x-κ₁` factor is likewise
part of `B`. -/
noncomputable def topSeeds (μ : ℕ) (A B Q : R) : Polynomial R :=
  Polynomial.C A * Polynomial.X ^ (2 * μ - 1) +
    Polynomial.C B * Polynomial.X ^ (2 * μ - 2) +
    Polynomial.C Q * Polynomial.X ^ (2 * μ - 2)

/-- **§4, chain census.**  LEMMA 4 turns the three surviving seeds into the pair quotient
`A·(Y-(μ-1)P)` and the constant triple/quad deposits. -/
theorem devQ_topSeeds (P c0 A B Q : R) {μ : ℕ} (hμ : 2 ≤ μ) :
    devQ (triKey P c0) (topSeeds μ A B Q) (μ - 1) =
      Polynomial.C A *
          (Polynomial.X - Polynomial.C (((μ - 1 : ℕ) : R) * P)) +
        Polynomial.C B + Polynomial.C Q := by
  have heven : 2 * μ - 2 = 2 * (μ - 1) := by omega
  have hodd : 2 * μ - 1 = 2 * (μ - 1) + 1 := by omega
  simp only [topSeeds]
  rw [devQ_add (triKey_monic P c0), devQ_add (triKey_monic P c0)]
  rw [hodd, devQ_C_mul (triKey_monic P c0), devQ_triKey_X_pow_odd]
  rw [heven, devQ_C_mul (triKey_monic P c0), devQ_triKey_X_pow_even, mul_one]
  rw [devQ_C_mul (triKey_monic P c0), devQ_triKey_X_pow_even, mul_one]

end TopChain

/-! ## Exact slot values (§4) -/

section Census

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The PAIR digit in slot `(0,1)`. -/
def pairDigit (μ : ℕ) (c₂ π : O) (v₂ : ℕ) : O :=
  (Nat.choose μ 2 : O) * c₂ ^ 2 * π ^ (2 * v₂)

/-- The integer coefficient which merges the PAIR quotient deposit with the TRIPLE deposit. -/
def mixedBase (μ : ℕ) : O :=
  (Nat.choose μ 3 : O) - ((μ - 1 : ℕ) : O) * (Nat.choose μ 2 : O)

/-- The mixed PAIR/TRIPLE digit in slot `(1,0)`:
`(b₃-(μ-1)b₂) ĉ₂³ π^(3v₂)`. -/
def mixedDigit (μ : ℕ) (c₂ π : O) (v₂ : ℕ) : O :=
  mixedBase μ * c₂ ^ 3 * π ^ (3 * v₂)

/-- The merged QUAD/`κ₁`-TRIPLE digit in slot `(0,0)`. -/
def bottomDigit (μ : ℕ) (κ₁ c₂ π : O) (v₂ : ℕ) : O :=
  (Nat.choose μ 4 : O) * c₂ ^ 4 * π ^ (4 * v₂) -
    κ₁ * (Nat.choose μ 3 : O) * c₂ ^ 3 * π ^ (3 * v₂)

/-- The exact three-slot polynomial displayed in §4.  Powers of `Φ′` encode the second slot
coordinate, and powers of `x` encode the first. -/
noncomputable def topCensus (Φ : Polynomial O) (μ : ℕ) (κ₁ c₂ π : O) (v₂ : ℕ) :
    Polynomial O :=
  Polynomial.C (pairDigit μ c₂ π v₂) * Φ +
    Polynomial.C (mixedDigit μ c₂ π v₂) * Polynomial.X +
    Polynomial.C (bottomDigit μ κ₁ c₂ π v₂)

/-- The `Φ′`-adic coefficient at slot-coordinate `b=0` contains exactly the `(1,0)` and `(0,0)`
values from the census. -/
theorem dev_topCensus_zero (F : KeyFrame O π) (he₁ : F.e₁ = 2) (hf₁ : F.f₁ = 1)
    (μ : ℕ) (κ₁ c₂ : O) (v₂ : ℕ) :
    dev F.key (topCensus F.key μ κ₁ c₂ π v₂) 0 =
      Polynomial.C (mixedDigit μ c₂ π v₂) * Polynomial.X +
        Polynomial.C (bottomDigit μ κ₁ c₂ π v₂) := by
  have hdeg : F.key.natDegree = 2 := by rw [F.hdeg, he₁, hf₁]
  let R : Polynomial O := Polynomial.C (mixedDigit μ c₂ π v₂) * Polynomial.X +
    Polynomial.C (bottomDigit μ κ₁ c₂ π v₂)
  have hRnat : R.natDegree ≤ 1 := by
    simp only [R]
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans natDegree_mul_le (by simp)
    · simp
  have hRdeg : R.degree < F.key.degree :=
    degree_lt_degree (lt_of_le_of_lt hRnat (by rw [hdeg]; omega))
  rw [← devQ_eq_dev]
  have hcensus : topCensus F.key μ κ₁ c₂ π v₂ =
      Polynomial.C (pairDigit μ c₂ π v₂) * F.key ^ 1 + R := by
    simp [topCensus, R]
    ring
  rw [hcensus, devQ_add F.hmonic]
  rw [devQ_mul_pow_of_lt F.hmonic 1 _ 0 (by omega), zero_add,
    devQ_zero_of_degree_lt F.hmonic hRdeg]

/-- The `Φ′`-adic coefficient at slot-coordinate `b=1` is exactly the PAIR digit. -/
theorem dev_topCensus_one (F : KeyFrame O π) (he₁ : F.e₁ = 2) (hf₁ : F.f₁ = 1)
    (μ : ℕ) (κ₁ c₂ : O) (v₂ : ℕ) :
    dev F.key (topCensus F.key μ κ₁ c₂ π v₂) 1 = Polynomial.C (pairDigit μ c₂ π v₂) := by
  have hdeg : F.key.natDegree = 2 := by rw [F.hdeg, he₁, hf₁]
  let R : Polynomial O := Polynomial.C (mixedDigit μ c₂ π v₂) * Polynomial.X +
    Polynomial.C (bottomDigit μ κ₁ c₂ π v₂)
  have hRnat : R.natDegree ≤ 1 := by
    simp only [R]
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans natDegree_mul_le (by simp)
    · simp
  have hRlt : R.natDegree < F.key.natDegree := by omega
  have hCdeg : (Polynomial.C (pairDigit μ c₂ π v₂) : Polynomial O).degree < F.key.degree :=
    degree_lt_degree (by rw [natDegree_C, hdeg]; omega)
  rw [← devQ_eq_dev]
  have hcensus : topCensus F.key μ κ₁ c₂ π v₂ =
      Polynomial.C (pairDigit μ c₂ π v₂) * F.key ^ 1 + R := by
    simp [topCensus, R]
    ring
  rw [hcensus, devQ_add F.hmonic]
  have hp := devQ_mul_pow F.hmonic 1 (Polynomial.C (pairDigit μ c₂ π v₂)) 0
  simp only [Nat.add_zero] at hp
  rw [hp, devQ_zero_of_degree_lt F.hmonic hCdeg,
    devQ_eq_zero_of_lt F.hmonic R 1 (by simpa [hdeg] using hRlt), add_zero]

/-! ## Slot heights (§5) -/

/-- The PAIR coefficient has normalized level-one height `4v₂` when its binomial digit is a
unit.  Adding its level-two slot offset `u₂` gives the first height in §5. -/
theorem stageHeight_pairDigit (F : KeyFrame O π) (hπ : Irreducible π) (he₁ : F.e₁ = 2)
    {μ v₂ : ℕ} {c₂ : O} (hc₂ : IsUnit c₂) (hb₂ : IsUnit ((Nat.choose μ 2 : ℕ) : O)) :
    F.stageHeight (Polynomial.C (pairDigit μ c₂ π v₂) * Polynomial.X ^ 0) =
      ((4 * v₂ : ℕ) : ℕ∞) := by
  have hu : IsUnit (((Nat.choose μ 2 : ℕ) : O) * c₂ ^ 2) := hb₂.mul (hc₂.pow 2)
  have hdigit : pairDigit μ c₂ π v₂ =
      (((Nat.choose μ 2 : ℕ) : O) * c₂ ^ 2) * π ^ (2 * v₂) := by
    simp [pairDigit]
  rw [stageHeight_C_mul_X_pow, hdigit, gaussVal_C_unit_mul_pow hπ hu, he₁]
  norm_num [nsmul_eq_mul]
  norm_cast
  omega

/-- The mixed coefficient has normalized level-one height `6v₂+h` when its merged integer
digit is a unit. -/
theorem stageHeight_mixedDigit (F : KeyFrame O π) (hπ : Irreducible π) (he₁ : F.e₁ = 2)
    {μ v₂ : ℕ} {c₂ : O} (hc₂ : IsUnit c₂) (hM : IsUnit (mixedBase (O := O) μ)) :
    F.stageHeight (Polynomial.C (mixedDigit μ c₂ π v₂) * Polynomial.X ^ 1) =
      ((6 * v₂ + F.h : ℕ) : ℕ∞) := by
  have hu : IsUnit (mixedBase (O := O) μ * c₂ ^ 3) := hM.mul (hc₂.pow 3)
  have hdigit : mixedDigit μ c₂ π v₂ =
      (mixedBase (O := O) μ * c₂ ^ 3) * π ^ (3 * v₂) := by
    simp [mixedDigit]
  rw [stageHeight_C_mul_X_pow, hdigit, gaussVal_C_unit_mul_pow hπ hu, he₁]
  norm_num [nsmul_eq_mul]
  norm_cast
  omega

/-- The two elementary on-side identities used to identify the PAIR and mixed heights with
`Θ_(μ-1)=3u₂-2h`. -/
theorem pair_mixed_height_eq_theta {h u₂ v₂ : ℕ} (hu : u₂ = 2 * v₂ + h)
    (hmargin : 2 * h ≤ u₂) :
    4 * v₂ + u₂ = 3 * u₂ - 2 * h ∧ 6 * v₂ + h = 3 * u₂ - 2 * h := by
  omega

/-- The undecorated QUAD deposit lies at `Θ+δ`, while the `κ₁`-decorated TRIPLE deposit has
base height `Θ-h`; adding the coefficient contribution `2v(κ₁)` gives
`Θ+(2v(κ₁)-h)`. -/
theorem bottom_deposit_height_arithmetic {h u₂ v₂ : ℕ} (hu : u₂ = 2 * v₂ + h)
    (hmargin : 2 * h ≤ u₂) :
    8 * v₂ = (3 * u₂ - 2 * h) + (u₂ - 2 * h) ∧
      6 * v₂ = (3 * u₂ - 2 * h) - h := by
  omega

/-- Consequently both possible `(0,0)` deposits, and hence their nonarchimedean sum, are at
least one grade above `Θ` once `δ≥1` and `2v(κ₁)-h≥1`. -/
theorem bottom_height_min_above_theta {Θ δ τ vb₄ vb₃ : ℕ} (hδ : 1 ≤ δ) (hτ : 1 ≤ τ) :
    Θ + 1 ≤ min (Θ + δ + 2 * vb₄) (Θ + τ + 2 * vb₃) := by
  omega

end Census

/-! ## The congruence swap (§5) -/

/-- If `p` divides the pair digit, then it divides the mixed integer
`b₃-(μ-1)b₂` exactly when it divides `b₃`. -/
theorem dvd_mixed_iff_of_dvd_pair (p μ : ℕ) (hp : p ∣ Nat.choose μ 2) :
    ((p : ℤ) ∣ (Nat.choose μ 3 : ℤ) - (μ - 1 : ℤ) * (Nat.choose μ 2 : ℤ)) ↔
      p ∣ Nat.choose μ 3 := by
  have hpZ : (p : ℤ) ∣ (Nat.choose μ 2 : ℤ) := Int.natCast_dvd_natCast.mpr hp
  have hprod : (p : ℤ) ∣ (μ - 1 : ℤ) * (Nat.choose μ 2 : ℤ) :=
    dvd_mul_of_dvd_right hpZ _
  constructor
  · intro hm
    exact Int.natCast_dvd_natCast.mp (by simpa using hm.add hprod)
  · intro hb₃
    have hb₃Z : (p : ℤ) ∣ (Nat.choose μ 3 : ℤ) := Int.natCast_dvd_natCast.mpr hb₃
    exact hb₃Z.sub hprod

/-- The verdict may therefore replace the mixed digit by the TRIPLE binomial digit. -/
theorem pair_or_mixed_iff_pair_or_triple (p μ : ℕ) :
    (¬ p ∣ Nat.choose μ 2 ∨
        ¬ ((p : ℤ) ∣ (Nat.choose μ 3 : ℤ) - (μ - 1 : ℤ) * (Nat.choose μ 2 : ℤ))) ↔
      (¬ p ∣ Nat.choose μ 2 ∨ ¬ p ∣ Nat.choose μ 3) := by
  by_cases hp : p ∣ Nat.choose μ 2
  · simp [hp, dvd_mixed_iff_of_dvd_pair p μ hp]
  · simp [hp]

/-! ## The signed top coordinate and its floor (§5) -/

section Geography

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- At the re-signed C.128 geography the cascade equation forces `e₂=1` and `t*=1`; hence the
stub's displayed coordinate is literally `μ₂-1`. -/
theorem cascade_top_coordinate {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hf₂ : T.f₂ = 2) {tstar μ₂ : ℕ}
    (hμ₂ : 2 ≤ μ₂) (hcasc : T.e₂ * (T.f₂ - tstar) = 1) :
    T.e₂ = 1 ∧ tstar = 1 ∧
      (μ₂ - 2) + (2 * T.e₂ * tstar + 1) / (T.e₂ * T.f₂) = μ₂ - 1 := by
  have he₂ : T.e₂ = 1 := Nat.eq_one_of_dvd_one ⟨T.f₂ - tstar, hcasc.symm⟩
  have hsub : T.f₂ - tstar = 1 :=
    Nat.eq_one_of_dvd_one ⟨T.e₂, by rw [mul_comm]; exact hcasc.symm⟩
  have ht : tstar = 1 := by omega
  refine ⟨he₂, ht, ?_⟩
  have hdiv : (2 * T.e₂ * tstar + 1) / (T.e₂ * T.f₂) = 1 := by
    norm_num [he₂, ht, hf₂]
  rw [hdiv]
  omega

/-- At that top coordinate the C.71 threshold is `E₂+δ = 3u₂-2h`. -/
theorem theta_top_eq {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hf₁ : F.f₁ = 1) (he₁ : F.e₁ = 2)
    (hf₂ : T.f₂ = 2) (he₂ : T.e₂ = 1) {μ₂ : ℕ} (hμ₂ : 1 ≤ μ₂) :
    T.theta μ₂ (μ₂ - 1) = 3 * T.u₂ - 2 * F.h := by
  have hfl : 2 * F.h < T.u₂ := by
    have h := T.hfloor
    rw [he₂, he₁, hf₁, one_mul, mul_one] at h
    exact h
  have hμsub : μ₂ - (μ₂ - 1) = 1 := by omega
  simp only [TowerDatum.theta, TowerDatum.E₂, TowerDatum.margin, he₂, hf₂, he₁, hf₁,
    one_mul, mul_one, hμsub]
  omega

end Geography

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.topSeeds
#print axioms Uniformity.Density.Tower.devQ_topSeeds
#print axioms Uniformity.Density.Tower.pairDigit
#print axioms Uniformity.Density.Tower.mixedBase
#print axioms Uniformity.Density.Tower.mixedDigit
#print axioms Uniformity.Density.Tower.bottomDigit
#print axioms Uniformity.Density.Tower.topCensus
#print axioms Uniformity.Density.Tower.dev_topCensus_zero
#print axioms Uniformity.Density.Tower.dev_topCensus_one
#print axioms Uniformity.Density.Tower.stageHeight_pairDigit
#print axioms Uniformity.Density.Tower.stageHeight_mixedDigit
#print axioms Uniformity.Density.Tower.pair_mixed_height_eq_theta
#print axioms Uniformity.Density.Tower.bottom_deposit_height_arithmetic
#print axioms Uniformity.Density.Tower.bottom_height_min_above_theta
#print axioms Uniformity.Density.Tower.dvd_mixed_iff_of_dvd_pair
#print axioms Uniformity.Density.Tower.pair_or_mixed_iff_pair_or_triple
#print axioms Uniformity.Density.Tower.cascade_top_coordinate
#print axioms Uniformity.Density.Tower.theta_top_eq

end AxCheck
