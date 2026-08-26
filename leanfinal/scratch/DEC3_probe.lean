/-
DEC3R — machine probes for the mu_3 / Route-B campaign blueprint.

No proof placeholder, no custom declaration, no corpus edit. Run from `leanfinal/` with:
  lake env lean scratch/DEC3_probe.lean
-/
import Uniformity.ChapC.C130sg

set_option linter.style.longLine false

noncomputable section

namespace DEC3Probe

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130rp6

universe uKt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {pi : O}

section Numerals

variable [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- The witness's next stage really is `(e_3,f_3,u_3) = (2,1,21)`. -/
theorem stage_three_numerals :
    (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).e 3 = 2 ∧
      (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).f 3 = 1 ∧
      (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).u 3 = 21 :=
  ⟨rfl, rfl, rfl⟩

/-- The next key degree is `D_3 = 8` in the untruncated witness. -/
theorem stage_three_Dcum :
    (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).Dcum 3 = 8 := by
  change (∏ j ∈ Finset.Icc 1 3, (2 : Nat) * 1) = 8
  decide

/-- The depth-two consumer floor is exactly `20 < 21`. -/
theorem depth_two_floor : 2 * (s2DepthTwo h2 hq).Econst 2 < 21 := by
  change 20 < 21
  omega

/-- The rejected old target would ask for `20 < 5`. -/
theorem depth_two_floor_rejects_five :
    ¬ (2 * (s2DepthTwo h2 hq).Econst 2 < 5) := by
  change ¬ (20 < 5)
  omega

/-- In the paper's full-current-group integer coordinate, preceding-group membership at
the last S2 step is divisibility by `e_3 = 2`. -/
def Mu3PrevGrade (beta : Nat) : Prop := 2 ∣ beta

theorem mu3_prev_grade_iff_even (beta : Nat) : Mu3PrevGrade beta ↔ beta % 2 = 0 := by
  simp [Mu3PrevGrade, Nat.dvd_iff_mod_eq_zero]

/-- Hence the next key value is not a preceding-group grade. -/
theorem mu3_key_grade_not_previous : ¬ Mu3PrevGrade 21 := by
  simp [Mu3PrevGrade]

/-- Coprimality holds simultaneously, exposing the `hprev`/`hcop` collision. -/
theorem mu3_coprime_and_not_previous : Nat.Coprime 21 2 ∧ ¬ Mu3PrevGrade 21 := by
  exact ⟨by decide, mu3_key_grade_not_previous⟩

/-- The raw normalizer polynomial behind `FGMNCalculus.chainNorm`, separated from the
class so that its landed-key computation does not presuppose the sought μ₃ calculus. -/
noncomputable def rawChainNorm {F : KeyFrame O pi} {H0 : Nat} {hpin : F.Pin H0} {r : Nat}
    {W : DeepTower F H0 hpin r} (K : KeyChain W) (i k : Nat) : Polynomial O :=
  Polynomial.C (pi ^ (W.towerNorm i k).1) * Polynomial.X ^ (W.towerNorm i k).2.1 *
    ∏ j : Fin i, (K.keyAt (j.1 + 1)) ^ ((W.towerNorm i k).2.2 j)

/-- Executable normalizer exponent solve at the depth-two key grade. -/
theorem towerNorm_two_twenty_one :
    (s2DepthTwo h2 hq).towerNorm 2 21 = (0, 0, ![0, 1]) := by
  have hu3 : (s2DepthTwo h2 hq).u 3 = 21 := rfl
  have he3 : (s2DepthTwo h2 hq).e 3 = 2 := rfl
  have hu2 : (s2DepthTwo h2 hq).u 2 = 5 := rfl
  have he2 : (s2DepthTwo h2 hq).e 2 = 2 := rfl
  have hb3 : towerSolve 21 2 21 = 1 := by decide
  have hb2 : towerSolve 5 2 0 = 0 := by decide
  simp [DeepTower.towerNorm, hu3, he3, hu2, he2, hb3, hb2,
    C35b.e1_eq, C35b.h_eq, C130rp1.slotIdx_zero]
  funext j
  fin_cases j <;> rfl

/-- The depth-two normalizer at the key grade includes the last carried key itself. -/
theorem rawChainNorm_two_twenty_one :
    rawChainNorm (pi := (2 : O)) (s2DepthTwoKeyChain h2 hq) 2 21 =
      (s2DepthTwoKeyChain h2 hq).keyAt 2 := by
  rw [rawChainNorm, towerNorm_two_twenty_one]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Consequently the current strict degree supply cannot hold at `d = 1`. -/
theorem rawChainNorm_two_degree_not_lt :
    ¬ (rawChainNorm (pi := (2 : O)) (s2DepthTwoKeyChain h2 hq) 2 21).natDegree <
      ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree := by
  rw [rawChainNorm_two_twenty_one]
  omega

/-- The source-compatible lower normalizer uses only keys strictly below `keyAt 2`. -/
theorem towerNorm_one_twenty_one :
    (s2DepthTwo h2 hq).towerNorm 1 21 = (4, 0, ![1]) := by
  change (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).towerNorm 1 21 = (4, 0, ![1])
  rw [(s2Witness_values h2 hq 1 (s2Frame_pin h2 hq)).2.2.2.2.2.2]
  congr
  funext j
  fin_cases j
  rfl

theorem rawChainNorm_one_twenty_one :
    rawChainNorm (pi := (2 : O)) (s2DepthTwoKeyChain h2 hq) 1 21 =
      Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1 := by
  rw [rawChainNorm, towerNorm_one_twenty_one]
  simp

/-- With the lower index, the required strict degree fence is arithmetically viable. -/
theorem rawChainNorm_one_degree_lt :
    (rawChainNorm (pi := (2 : O)) (s2DepthTwoKeyChain h2 hq) 1 21).natDegree <
      ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree := by
  rw [rawChainNorm_one_twenty_one,
    Polynomial.natDegree_C_mul (pow_ne_zero 4 h2.ne_zero)]
  have hk1 : ((s2DepthTwoKeyChain h2 hq).keyAt 1).natDegree = 2 :=
    ((s2DepthTwoKeyChain h2 hq).keyAt_degree 1 ⟨by omega, by omega⟩).trans
      (s2DepthTwo_Dcum_one h2 hq)
  rw [hk1, C130rp8.s2KeyChain_keyAt_two_natDegree h2 hq]
  omega

end Numerals

/-! The previous theorem deliberately cannot be used: there is no depth-two laws record at
the old `(2,1,5)` operators. The normalizer computation below is therefore stated directly
from an arbitrary calculus whose `keyAt` is the landed chain. -/

section Consumer

variable {F : KeyFrame O pi} {H0 : Nat} {hpin : F.Pin H0} {r : Nat}
variable {W : DeepTower.{0, uKt} F H0 hpin r}

/-- `rawChainNorm` is definitionally the landed consumer normalizer once the calculus is
packaged from the same key chain.  This is the signature-match tooth used by the blueprint. -/
theorem rawChainNorm_eq_chainNorm (K : KeyChain W) {e' f' u' : Nat}
    (I : FGMNCalculus W e' f' u') (hkey : I.keyAt = K.keyAt) (i k : Nat) :
    rawChainNorm K i k = I.chainNorm i k := by
  simp only [rawChainNorm, FGMNCalculus.chainNorm, hkey]

/-- Route B needs no carrier or point packaging: the landed constructor accepts exactly the
depth-two key chain, the `(2,1,21)` source data, and its laws. -/
theorem route_b_packaging_signature (K : KeyChain W)
    (S : FGMNSourceData W K 2 1 21) (hL : FGMNSourceLaws W K 2 1 21 S) :
    Nonempty (FGMNCalculus W 2 1 21) :=
  fgmn_model_calculus_nonempty K S hL

/-- At `f' = 1`, the ratio conclusion needs no multiplication law and hence no `PrevGrade`:
it is only cancellation in the coefficient field. -/
theorem ratio_power_one (u' : Nat) (I : FGMNCalculus W 2 1 u')
    (hnorm : ∀ d, 0 < d → d ≤ 1 → I.ExactGrade (d * u') (I.chainNorm r (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ 1 →
      (I.chainNorm r (d * u')).natDegree < (I.keyAt r).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ 1 → I.chainNorm r (d * u') ≠ 0)
    {t : Nat} (ht : t < 1) :
    I.Rgr ((1 - t) * u') (I.chainNorm r ((1 - t) * u')) * I.thetaRatio (1 - t) =
      (I.Rgr u' (I.chainNorm r u')) ^ (1 - t) := by
  have ht0 : t = 0 := by omega
  subst t
  have hgrade : I.ExactGrade u' (I.chainNorm r u') := by
    simpa using hnorm 1 one_pos le_rfl
  have hdeg : (I.chainNorm r u').natDegree < (I.keyAt r).natDegree := by
    simpa using hnormdeg 1 one_pos le_rfl
  have hnz : I.chainNorm r u' ≠ 0 := by
    simpa using hnormz 1 one_pos le_rfl
  have ha : I.Rgr u' (I.chainNorm r u') ≠ 0 := I.Rgr_ne_zero u' _ hgrade hdeg hnz
  simp [FGMNCalculus.thetaRatio, ha]

end Consumer

end DEC3Probe

end

#print axioms DEC3Probe.stage_three_numerals
#print axioms DEC3Probe.stage_three_Dcum
#print axioms DEC3Probe.depth_two_floor
#print axioms DEC3Probe.depth_two_floor_rejects_five
#print axioms DEC3Probe.mu3_prev_grade_iff_even
#print axioms DEC3Probe.mu3_coprime_and_not_previous
#print axioms DEC3Probe.towerNorm_two_twenty_one
#print axioms DEC3Probe.rawChainNorm_two_twenty_one
#print axioms DEC3Probe.rawChainNorm_two_degree_not_lt
#print axioms DEC3Probe.towerNorm_one_twenty_one
#print axioms DEC3Probe.rawChainNorm_one_twenty_one
#print axioms DEC3Probe.rawChainNorm_one_degree_lt
#print axioms DEC3Probe.rawChainNorm_eq_chainNorm
#print axioms DEC3Probe.route_b_packaging_signature
#print axioms DEC3Probe.ratio_power_one
