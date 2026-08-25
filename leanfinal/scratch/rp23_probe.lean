import Uniformity.ChapC.C130rp1

/-! Probe for unit RP23: the risky steps, before composing C130rp2.lean. -/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.RP23Probe

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130nv3 Uniformity.Density.Tower.C131y

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

-- A. the letter is 1 at S2 (card-2 collapse)
private theorem eq_one_of_card_two {K : Type} [Field K] (hcard : Nat.card K = 2)
    {z : K} (hz : z ≠ 0) : z = 1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hcard]
  haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hz.isUnit.unit = 1 := Subsingleton.elim _ _
  calc z = ((hz.isUnit.unit : Kˣ) : K) := (hz.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

theorem s2_stageLetter_eq_one :
    (s2Frame h2 hq).stageLetter 1 (s2Frame_pin h2 hq) = 1 := by
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  exact eq_one_of_card_two (C80.card_K₁ h2 hq)
    ((s2Frame h2 hq).stageLetter_ne_zero h2 1 (s2Frame_pin h2 hq))

-- B. the twist is trivial at S2
theorem s2_twistRead_eq_slotRes (k : ℕ) (A : Polynomial O) :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) k A
      = (s2Frame h2 hq).slotRes 1 (s2Frame_pin h2 hq) k A := by
  letI : Field ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq)) :=
    s2StageFieldInst h2 hq 1 (s2Frame_pin h2 hq)
  show ((s2Frame h2 hq).stageLetter 1 (s2Frame_pin h2 hq))⁻¹ ^ ((s2Frame h2 hq).twistExp k)
      * (s2Frame h2 hq).slotRes 1 (s2Frame_pin h2 hq) k A
    = (s2Frame h2 hq).slotRes 1 (s2Frame_pin h2 hq) k A
  rw [s2_stageLetter_eq_one h2 hq, inv_one, one_pow, one_mul]

-- C. slot arithmetic at variable k
theorem slotIdx_eq (k : ℕ) : (s2Frame h2 hq).slotIdx k = k % 2 := by
  change ((List.range 2).find? (fun i => (i * 1) % 2 == k % 2)).getD 0 = k % 2
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp only [h] <;> rfl

theorem twistExp_eq (k : ℕ) : (s2Frame h2 hq).twistExp k = k / 2 := by
  rw [KeyFrame.twistExp, slotIdx_one h2 hq, slotIdx_eq h2 hq k, e1_eq h2 hq, one_mul]
  omega

theorem slotWindow_eq (k : ℕ) : (s2Frame h2 hq).slotWindow k = {0} := by
  rw [KeyFrame.slotWindow]
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
    f1_eq h2 hq, e1_eq h2 hq, h_eq h2 hq, slotIdx_eq h2 hq k]
  omega

-- D. the read normal form
theorem s2_slotRes_eq_digAt (k : ℕ) (A : Polynomial O) :
    (s2Frame h2 hq).slotRes 1 (s2Frame_pin h2 hq) k A
      = algebraMap (resField (Polynomial.X : Polynomial O))
          ((s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq))
          (algebraMap (IsLocalRing.ResidueField O) (resField (Polynomial.X : Polynomial O))
            (digAt (2 : O) (k / 2) (A.coeff (k % 2)))) := by
  rw [KeyFrame.slotRes, slotWindow_eq h2 hq k, Finset.sum_singleton]
  have hidx : (s2Frame h2 hq).slotIdx k + (s2Frame h2 hq).e₁ * 0 = k % 2 := by
    rw [slotIdx_eq h2 hq k, e1_eq h2 hq]
    omega
  rw [hidx]
  have hdig : (k - k % 2 * (s2Frame h2 hq).h) / (s2Frame h2 hq).e₁ = k / 2 := by
    rw [h_eq h2 hq, e1_eq h2 hq]
    omega
  rw [hdig, pow_zero, mul_one]

-- E. twistRead_add_deep applies at the S2 pin
example {A B : Polynomial O} {k : ℕ}
    (hk : (k : ℕ∞) < (s2Frame h2 hq).stageHeight B) :
    (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) k (A + B)
      = (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) k A :=
  C131y.twistRead_add_deep (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq) hk

-- F. twistRead of the zero polynomial (digAt of 0 at every height)
include h2 in
theorem twistRead_zero' (F : KeyFrame O (2 : O)) (H₀ : ℕ) (hpin : F.Pin H₀) (k : ℕ) :
    F.twistRead H₀ hpin k (0 : Polynomial O) = 0 := by
  have hzero : F.slotRes H₀ hpin k (0 : Polynomial O) = 0 := by
    rw [KeyFrame.slotRes]
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Polynomial.coeff_zero,
      digAt_eq h2 (show (0 : O) = 2 ^ ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁) * 0 by
        rw [mul_zero]),
      map_zero, map_zero, map_zero, zero_mul]
  rw [KeyFrame.twistRead, hzero, mul_zero]

-- G. one parity case of the survival core at the digit level (odd × odd, the carry)
example {m n : ℕ} {a0 a1 b0 b1 : O}
    (ha0 : (2 : O) ^ (m + 1) ∣ a0) (hb0 : (2 : O) ^ (n + 1) ∣ b0)
    (ha1 : (2 : O) ^ m ∣ a1) (hb1 : (2 : O) ^ n ∣ b1) :
    digAt (2 : O) (m + n + 1) (a0 * b0 + 2 * (a1 * b1))
      = digAt (2 : O) m a1 * digAt (2 : O) n b1 := by
  obtain ⟨a', ha'⟩ := ha0
  obtain ⟨b', hb'⟩ := hb0
  obtain ⟨a'', ha''⟩ := ha1
  obtain ⟨b'', hb''⟩ := hb1
  have hcongr : digAt (2 : O) (m + n + 1) (a0 * b0 + 2 * (a1 * b1))
      = digAt (2 : O) (m + n + 1) (2 * (a1 * b1)) := by
    refine (Uniformity.Density.Tower.C109asm.digAt_congr h2 ?_).symm
    exact ⟨a' * b', by rw [ha', hb']; ring⟩
  rw [hcongr,
    digAt_eq h2 (show 2 * (a1 * b1) = (2 : O) ^ (m + n + 1) * (a'' * b'') by
      rw [ha'', hb'']; ring),
    digAt_eq h2 ha'', digAt_eq h2 hb'', map_mul]

-- H. the ℕ∞ floor extraction helpers
private theorem coe_le_of_le_two_smul {a : ℕ} {x : ℕ∞} (h : (a : ℕ∞) ≤ 2 • x) :
    (((a + 1) / 2 : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hx
  rw [← hc] at h ⊢
  rw [show (2 : ℕ) • ((c : ℕ) : ℕ∞) = ((2 * c : ℕ) : ℕ∞) by rw [nsmul_eq_mul]; push_cast; ring]
    at h
  have hnat : a ≤ 2 * c := by exact_mod_cast h
  exact_mod_cast (by omega : (a + 1) / 2 ≤ c)

private theorem coe_le_of_le_two_smul_add_one {a : ℕ} {x : ℕ∞} (h : (a : ℕ∞) ≤ 2 • x + 1) :
    ((a / 2 : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hx
  rw [← hc] at h ⊢
  rw [show (2 : ℕ) • ((c : ℕ) : ℕ∞) + 1 = ((2 * c + 1 : ℕ) : ℕ∞) by
    rw [nsmul_eq_mul]; push_cast; ring] at h
  have hnat : a ≤ 2 * c + 1 := by exact_mod_cast h
  exact_mod_cast (by omega : a / 2 ≤ c)

-- I. the generic weight extraction (RP-2's slot floor)
omit [Finite (ResidueField O)] in
theorem le_dvHgt_of_le_dvSupp {F : KeyFrame O (2 : O)} {f : Polynomial O} {u ℓ β m j : ℕ}
    (hℓ : 0 < ℓ) (hβ : (β : ℕ∞) ≤ dvSupp F f u ℓ) (hm : ℓ * m + u * j = β) :
    (m : ℕ∞) ≤ dvHgt F f j := by
  have hterm := C131y.dvSupp_le_term F f u hℓ j
  have h : (β : ℕ∞) ≤ ℓ • dvHgt F f j + (u * j : ℕ∞) := le_trans hβ hterm
  rcases eq_or_ne (dvHgt F f j) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hc, weight_read] at h
  rw [← hc]
  have hnat : β ≤ ℓ * c + u * j := by exact_mod_cast h
  exact_mod_cast Nat.le_of_mul_le_mul_left (by omega : ℓ * m ≤ ℓ * c) hℓ

end S2

end Uniformity.Density.Tower.RP23Probe
