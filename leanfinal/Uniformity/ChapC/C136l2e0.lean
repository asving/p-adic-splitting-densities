/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C134dv2g
import Uniformity.ChapC.C134f13a

/-!
# Uniformity.ChapC.C136l2e0 — L2E-00--02: the shared level-2 multiplicative root

This file opens the shared level-2 multiplicative engine of DWC §11.7.  It is rooted at an
arbitrary `LevelDatum`: no S2 datum or numeral occurs in the declarations.

* L2E-00 locks the slot-carry and cocycle-twist statement shapes.
* L2E-01 defines the fence-free level-2 coefficient read and proves its additive laws.
* L2E-02 proves that a level-2 test key has the exact seam height and that its full residual
  symbol dies at `AdjoinRoot.root L.r`.

The full read is the one-level-up twin of `C133mh3` Part 10's private `fullRead`.  Its
polynomial before `AdjoinRoot.mk L.r` keeps every aligned coefficient; `dvResPoly` is the
side-window truncation of the same coefficient recipe at an attained exact height.

New statement shapes and definitions in this file are trust-boundary declarations and are
flagged for human review.  No assertion is made merely by either `...Statement` definition.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136l2e0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C132nv2
open Uniformity.Density.Tower.C134dv2g

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

private theorem find?_range_eq_some_zero {p : ℕ → Bool} (hp : p 0 = true) {n : ℕ}
    (hn : 0 < n) : List.find? p (List.range n) = some 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  induction m with
  | zero => simp [hp]
  | succ m ih =>
      rw [List.range_succ, List.find?_append]
      rw [ih (Nat.succ_pos _)]
      rfl

/-- A multiple of the level denominator has shift zero. -/
private theorem shift_eq_zero_of_dvd (L : LevelDatum F H₀ hpin) {m : ℕ}
    (hm : L.ℓ ∣ m) : L.shift m = 0 := by
  rw [LevelDatum.shift]
  rw [find?_range_eq_some_zero (hn := L.hℓ) (by simp [Nat.mod_eq_zero_of_dvd hm])]
  rfl

/-- The height-zero read of the unit polynomial is one, including at the formally allowed
degenerate frame height. -/
private theorem twistRead_zero_one (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) :
    F.twistRead H₀ hpin 0 (1 : Polynomial O) = 1 := by
  classical
  have hi0 : F.slotIdx 0 = 0 := by
    symm
    exact F.slotIdx_unique F.he₁ (by
      simpa using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD F.e₁]))
  have hq0 : F.twistExp 0 = 0 := by simp [KeyFrame.twistExp, hi0]
  rw [KeyFrame.twistRead, hq0, pow_zero, one_mul, KeyFrame.slotRes]
  rw [Finset.sum_eq_single 0]
  · simp [hi0, digAt_zero]
  · intro t ht ht0
    have hidx : 0 < F.slotIdx 0 + F.e₁ * t := by
      rw [hi0, zero_add]
      exact Nat.mul_pos F.he₁ (Nat.pos_of_ne_zero ht0)
    have hc : (1 : Polynomial O).coeff (F.slotIdx 0 + F.e₁ * t) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hidx)
    simp [hc, digAt_zero]
  · simp [KeyFrame.slotWindow, hi0, F.hf₁]

/-! ## L2E-00 — reviewed generic statement shapes -/

/-- ★ **L2E-00 shape lock, slot-carry form.**  At exact finite inner heights, the
slot-zero coefficient of a reduced product reads as the product of the two coefficient
reads times the root raised to the explicit shift carry.  The key, its exact grade, and
the outer floor are hypotheses of the shared engine rather than S2-special data. -/
def Dv2SlotCarryLawStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ (L : LevelDatum F H₀ hpin) (Ψ : Polynomial O), IsMuKey L Ψ →
  ∀ (KΨ : ℕ), dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞) →
  ∀ (u₂ ℓ₂ : ℕ), 0 < ℓ₂ → ℓ₂ * KΨ < u₂ →
  ∀ a b : Polynomial O, a.natDegree < Ψ.natDegree → b.natDegree < Ψ.natDegree →
  ∀ ka kb δ : ℕ, dv2Hgt L a = (ka : ℕ∞) → dv2Hgt L b = (kb : ℕ∞) →
    L.shift ka + L.shift kb = L.shift (ka + kb) + L.ℓ * δ →
    dv2Res L (dev Ψ (a * b) 0)
      = AdjoinRoot.root L.r ^ δ * (dv2Res L a * dv2Res L b)

/-- ★ **L2E-00 shape lock, cocycle form.**  This is the consumer-facing version of the
slot-carry law: the explicit carry is the landed normalizer cocycle `L.cocycle ka kb`.
It is generic enough to instantiate both the F1 test-key context and the D3 coefficient
engine; in particular its declaration contains no S2 numeral. -/
def Dv2TwistProductLawStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ (L : LevelDatum F H₀ hpin) (Ψ : Polynomial O), IsMuKey L Ψ →
  ∀ (KΨ : ℕ), dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞) →
  ∀ (u₂ ℓ₂ : ℕ), 0 < ℓ₂ → ℓ₂ * KΨ < u₂ →
  ∀ a b : Polynomial O, a.natDegree < Ψ.natDegree → b.natDegree < Ψ.natDegree →
  ∀ ka kb : ℕ, dv2Hgt L a = (ka : ℕ∞) → dv2Hgt L b = (kb : ℕ∞) →
    dv2Res L (dev Ψ (a * b) 0)
      = AdjoinRoot.root L.r ^ L.cocycle ka kb * (dv2Res L a * dv2Res L b)

/-! ## L2E-01 — the full level-2 coefficient read -/

/-- The fence-free residual polynomial at inner height `k`.  Its indices are precisely
`j = L.shift k + L.ℓ*t` below the line `j*L.u ≤ k`; unlike `dvResPoly`, the range is not
truncated at a chosen side degree. -/
noncomputable def dv2FullReadPoly (L : LevelDatum F H₀ hpin) (k : ℕ)
    (P : Polynomial O) : Polynomial (F.stageField H₀ hpin) :=
  open Classical in
  ((Finset.range (k + 1)).filter
      (fun t => (L.shift k + L.ℓ * t) * L.u ≤ k)).sum fun t =>
    Polynomial.C
        (F.twistRead H₀ hpin ((k - (L.shift k + L.ℓ * t) * L.u) / L.ℓ)
          (dev F.key P (L.shift k + L.ℓ * t)))
      * Polynomial.X ^ t

/-- The full level-2 coefficient read, obtained by evaluating the fence-free polynomial
at the level letter `AdjoinRoot.root L.r` through `AdjoinRoot.mk L.r`. -/
noncomputable def dv2FullRead (L : LevelDatum F H₀ hpin) (k : ℕ)
    (P : Polynomial O) : AdjoinRoot L.r :=
  AdjoinRoot.mk L.r (dv2FullReadPoly L k P)

/-- A full-read index below the height-`k` line is read at a depth below every polynomial
whose level value is at least `k`. -/
private theorem fullRead_depth_le (L : LevelDatum F H₀ hpin) {P : Polynomial O}
    {k t : ℕ} (hP : (k : ℕ∞) ≤ dv2Hgt L P)
    (_ht : (L.shift k + L.ℓ * t) * L.u ≤ k) :
    (((k - (L.shift k + L.ℓ * t) * L.u) / L.ℓ : ℕ) : ℕ∞)
      ≤ F.stageHeight (dev F.key P (L.shift k + L.ℓ * t)) := by
  let j := L.shift k + L.ℓ * t
  change (k : ℕ∞) ≤ dvSupp F P L.u L.ℓ at hP
  have hterm : (k : ℕ∞) ≤ L.ℓ • dvHgt F P j + (L.u * j : ℕ∞) :=
    hP.trans (C131y.dvSupp_le_term F P L.u L.hℓ j)
  change (((k - j * L.u) / L.ℓ : ℕ) : ℕ∞)
    ≤ F.stageHeight (dev F.key P j)
  rcases eq_or_ne (F.stageHeight (dev F.key P j)) ⊤ with htop | hfin
  · rw [htop]
    exact le_top
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hfin
    have hv' : dvHgt F P j = (v : ℕ∞) := hv.symm
    rw [hv', nsmul_eq_mul] at hterm
    have hnat : k ≤ L.ℓ * v + L.u * j := by exact_mod_cast hterm
    have hsub : k - j * L.u ≤ L.ℓ * v := by
      rw [Nat.mul_comm L.u j] at hnat
      omega
    rw [← hv]
    exact_mod_cast Nat.div_le_of_le_mul hsub

/-- Strictly below the polynomial's level pin, every full-read coefficient is read below
its digit height. -/
private theorem fullRead_depth_lt (L : LevelDatum F H₀ hpin) {P : Polynomial O}
    {k t : ℕ} (hP : (k : ℕ∞) < dv2Hgt L P)
    (ht : (L.shift k + L.ℓ * t) * L.u ≤ k) :
    (((k - (L.shift k + L.ℓ * t) * L.u) / L.ℓ : ℕ) : ℕ∞)
      < F.stageHeight (dev F.key P (L.shift k + L.ℓ * t)) := by
  let j := L.shift k + L.ℓ * t
  have hj : j * L.u ≤ k := by simpa [j] using ht
  change (k : ℕ∞) < dvSupp F P L.u L.ℓ at hP
  have hterm : (k : ℕ∞) < L.ℓ • dvHgt F P j + (L.u * j : ℕ∞) :=
    hP.trans_le (C131y.dvSupp_le_term F P L.u L.hℓ j)
  change (((k - j * L.u) / L.ℓ : ℕ) : ℕ∞)
    < F.stageHeight (dev F.key P j)
  rcases eq_or_ne (F.stageHeight (dev F.key P j)) ⊤ with htop | hfin
  · rw [htop]
    exact ENat.coe_lt_top _
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hfin
    have hv' : dvHgt F P j = (v : ℕ∞) := hv.symm
    rw [hv', nsmul_eq_mul] at hterm
    have hnat : k < L.ℓ * v + L.u * j := by exact_mod_cast hterm
    have hsub : k - j * L.u < L.ℓ * v := by
      rw [Nat.mul_comm L.u j] at hnat
      omega
    rw [← hv]
    exact_mod_cast (Nat.div_lt_of_lt_mul hsub)

/-- The full read is additive at a common inner-height floor. -/
theorem dv2FullRead_add_of_le (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {A B : Polynomial O} {k : ℕ}
    (hA : (k : ℕ∞) ≤ dv2Hgt L A) (hB : (k : ℕ∞) ≤ dv2Hgt L B) :
    dv2FullRead L k (A + B) = dv2FullRead L k A + dv2FullRead L k B := by
  classical
  rw [dv2FullRead, dv2FullRead, dv2FullRead, ← map_add, dv2FullReadPoly,
    dv2FullReadPoly, dv2FullReadPoly, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  have hline := (Finset.mem_filter.mp ht).2
  have hdA := fullRead_depth_le L hA hline
  have hdB := fullRead_depth_le L hB hline
  rw [dev_add_of_monic F.hmonic,
    C130rp2.twistRead_add_of_le F hπ H₀ hpin hdA hdB, Polynomial.C_add, add_mul]

/-- A coefficient read strictly below the inner pin vanishes. -/
theorem dv2FullRead_eq_zero_of_lt (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {A : Polynomial O} {k : ℕ} (hk : (k : ℕ∞) < dv2Hgt L A) :
    dv2FullRead L k A = 0 := by
  classical
  rw [dv2FullRead, dv2FullReadPoly]
  have hsum : ∑ t ∈ (Finset.range (k + 1)).filter
      (fun t => (L.shift k + L.ℓ * t) * L.u ≤ k),
      Polynomial.C
          (F.twistRead H₀ hpin ((k - (L.shift k + L.ℓ * t) * L.u) / L.ℓ)
            (dev F.key A (L.shift k + L.ℓ * t)))
        * Polynomial.X ^ t = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have hline := (Finset.mem_filter.mp ht).2
    rw [C130rp2.twistRead_eq_zero_of_lt F hπ H₀ hpin
      (fullRead_depth_lt L hk hline), Polynomial.C_0, zero_mul]
  rw [hsum, map_zero]

/-! ## L2E-02 — the level-2 key root and exact carry height -/

/-- The exact key height used by every later carry exponent. -/
theorem dv2Hgt_testKey (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨ : IsTestKey L Ψ) :
    dv2Hgt L Ψ = ((L.ℓ * L.seam : ℕ) : ℕ∞) := by
  exact C134f13a.dvSupp_testKey L hΨ

/-- ★ **The level-2 key-root law.**  At its exact seam height, the full residual symbol
of a test key is `AdjoinRoot.mk L.r L.r`, hence dies at `AdjoinRoot.root L.r`.
This is the one-level-up twin of `C133mh3.fullRead_key`. -/
theorem dv2FullRead_testKey (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) :
    dv2FullRead L (L.ℓ * L.seam) Ψ = 0 := by
  classical
  rcases hΨ with ⟨hmonic, hdeg, htop, hoff, hslots⟩
  have hu : 0 < L.u := by
    have := L.hκ
    omega
  have hshift : L.shift (L.ℓ * L.seam) = 0 :=
    shift_eq_zero_of_dvd L ⟨L.seam, rfl⟩
  have hset : (Finset.range (L.ℓ * L.seam + 1)).filter
      (fun t => (L.shift (L.ℓ * L.seam) + L.ℓ * t) * L.u ≤ L.ℓ * L.seam)
      = Finset.range (L.r.natDegree + 1) := by
    ext t
    rw [hshift]
    simp only [Finset.mem_filter, Finset.mem_range, zero_add]
    constructor
    · rintro ⟨-, ht⟩
      have ht' : (L.ℓ * L.u) * t ≤ (L.ℓ * L.u) * L.r.natDegree := by
        rw [LevelDatum.seam] at ht
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht
      exact Nat.lt_succ_of_le
        (Nat.le_of_mul_le_mul_left ht' (Nat.mul_pos L.hℓ hu))
    · intro ht
      have htle : t ≤ L.r.natDegree := Nat.lt_succ_iff.mp ht
      have hdeg_le : L.r.natDegree ≤ L.ℓ * L.seam := by
        rw [LevelDatum.seam]
        calc
          L.r.natDegree = 1 * L.r.natDegree := by rw [one_mul]
          _ ≤ L.ℓ * L.r.natDegree :=
            Nat.mul_le_mul (Nat.one_le_iff_ne_zero.mpr L.hℓ.ne') le_rfl
          _ = (L.ℓ * L.r.natDegree) * 1 := by rw [mul_one]
          _ ≤ (L.ℓ * L.r.natDegree) * L.u :=
            Nat.mul_le_mul le_rfl (Nat.one_le_iff_ne_zero.mpr hu.ne')
          _ = L.ℓ * (L.r.natDegree * L.u) := by simp only [Nat.mul_assoc]
      refine ⟨Nat.lt_succ_of_le (htle.trans hdeg_le), ?_⟩
      rw [LevelDatum.seam]
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        (Nat.mul_le_mul_left (L.ℓ * L.u) htle)
  rw [dv2FullRead, dv2FullReadPoly, hset]
  have hpoly : ∑ t ∈ Finset.range (L.r.natDegree + 1),
      Polynomial.C
          (F.twistRead H₀ hpin
            ((L.ℓ * L.seam -
                (L.shift (L.ℓ * L.seam) + L.ℓ * t) * L.u) / L.ℓ)
            (dev F.key Ψ (L.shift (L.ℓ * L.seam) + L.ℓ * t)))
        * Polynomial.X ^ t = L.r := by
    conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow L.r]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht_le : t ≤ L.r.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have hdepth :
        (L.ℓ * L.seam - (L.shift (L.ℓ * L.seam) + L.ℓ * t) * L.u) / L.ℓ
          = (L.r.natDegree - t) * L.u := by
      rw [hshift, zero_add, LevelDatum.seam]
      have hsub : L.ℓ * (L.r.natDegree * L.u) - L.ℓ * t * L.u
          = L.ℓ * ((L.r.natDegree - t) * L.u) := by
        calc
          L.ℓ * (L.r.natDegree * L.u) - L.ℓ * t * L.u
              = (L.ℓ * L.r.natDegree - L.ℓ * t) * L.u := by
                  simp only [Nat.sub_mul, Nat.mul_assoc]
          _ = (L.ℓ * (L.r.natDegree - t)) * L.u := by
                rw [Nat.mul_sub_left_distrib]
          _ = L.ℓ * ((L.r.natDegree - t) * L.u) := by simp only [Nat.mul_assoc]
      rw [hsub, Nat.mul_div_cancel_left _ L.hℓ]
    rw [hdepth, hshift, zero_add]
    rcases eq_or_lt_of_le ht_le with rfl | ht_lt
    · rw [Nat.sub_self, zero_mul, htop, twistRead_zero_one F H₀ hpin,
        L.hrmonic.coeff_natDegree]
    · by_cases hc : L.r.coeff t = 0
      · rw [(hslots t ht_lt).1 hc, C130rp2.twistRead_zero F hπ H₀ hpin, hc]
      · rw [((hslots t ht_lt).2 hc).2]
  rw [hpoly, AdjoinRoot.mk_self]

end Uniformity.Density.Tower.C136l2e0

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136l2e0.Dv2SlotCarryLawStatement
#print axioms Uniformity.Density.Tower.C136l2e0.Dv2TwistProductLawStatement
#print axioms Uniformity.Density.Tower.C136l2e0.dv2FullReadPoly
#print axioms Uniformity.Density.Tower.C136l2e0.dv2FullRead
#print axioms Uniformity.Density.Tower.C136l2e0.dv2FullRead_add_of_le
#print axioms Uniformity.Density.Tower.C136l2e0.dv2FullRead_eq_zero_of_lt
#print axioms Uniformity.Density.Tower.C136l2e0.dv2Hgt_testKey
#print axioms Uniformity.Density.Tower.C136l2e0.dv2FullRead_testKey

end AxCheck
