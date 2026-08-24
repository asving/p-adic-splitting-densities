import Uniformity.ChapC.C130pk
import Uniformity.ChapC.C43
import Uniformity.ChapC.C56a
import Uniformity.ChapC.C45
import Uniformity.ChapC.C102gt
import Uniformity.ChapC.C11

/-!
# GSW_check — elaboration authority for unit GSW's GENTOW2 adjudication diffs

Statement-SHAPE checks only (each proposed re-sign is a `def … : Prop`; binders exactly the
re-signed leanspec telescopes), per `docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md`
(amendment A-C.12).  No `sorry`, no axiom, no instance.  Two deliberate stand-ins, both
documented per shape:

* `W₂ : DeepTower F H₀ hpin 2` stands in for leanspec's `T.deepTower hπ` (the §10-preamble
  axiom constant, unlanded in leanfinal — the GTA/GTB mechanical prerequisite);
* `recipe3` is a local byte-mirror of the leanspec §10 shared abbreviation (same reason).

The one PROOF in this file is the provability certificate for the re-signed C.99
(`gentow2_Bpp_resigned_provable`): the re-signed statement is a THEOREM of the A-C.11 class
fields alone — machine evidence that the A-C.12 antecedents are exactly the missing inputs.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.GSWCheck

open Uniformity.Density.Leaf Uniformity.Density.Tower IsLocalRing

universe uKt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Local mirror of the leanspec §10 shared abbreviation (unlanded in leanfinal) -/

/-- Byte-mirror of leanspec `recipe3` (NODE C.101/C.103 shared abbreviation). -/
noncomputable def recipe3 (T : TowerDatum F H₀ hpin) (e' f' u' : ℕ)
    (c : ℕ → AdjoinRoot (towerLabel T)) : Polynomial O :=
  (composedKey T) ^ (e' * f')
    - ∑ t ∈ Finset.range f', k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t)

/-! ## C.99 `gentow2_Bpp` — the A-C.12 re-sign shape -/

/-- Re-signed C.99 `gentow2_Bpp`: the three added binders are the source-stated B-1
normalizer supply (GENTOW2_PROOF S5.2 proof, ll.740–744). -/
def gentow2_Bpp_resigned {r : ℕ} (W : DeepTower.{0, uKt} F H₀ hpin r)
    (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (_hr : r = 2)
    (_he' : 0 < e') (_hf' : 0 < f') (_hcop : Nat.Coprime u' e')
    (_hfloor : e' * W.Econst r < u')
    (_hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNorm r (d * u')))
    (_hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNorm r (d * u')).natDegree < (I.keyAt r).natDegree)
    (_hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNorm r (d * u') ≠ 0)
    {t : ℕ} (_ht : t < f') : Prop :=
  I.Rgr ((f' - t) * u') (I.chainNorm r ((f' - t) * u')) * I.thetaRatio (f' - t)
    = (I.Rgr u' (I.chainNorm r u')) ^ (f' - t)

/-- Provability certificate: the re-signed C.99 is a theorem of the A-C.11 class fields
alone (`Rgr_mul` iterated + `Rgr_ne_zero` + field cancellation) — no scope fence, no floor
arithmetic, no cite is consumed by this algebra. -/
theorem gentow2_Bpp_resigned_provable {r : ℕ} (W : DeepTower.{0, uKt} F H₀ hpin r)
    (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (hf' : 0 < f')
    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNorm r (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNorm r (d * u')).natDegree < (I.keyAt r).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNorm r (d * u') ≠ 0)
    {t : ℕ} (ht : t < f') :
    I.Rgr ((f' - t) * u') (I.chainNorm r ((f' - t) * u')) * I.thetaRatio (f' - t)
      = (I.Rgr u' (I.chainNorm r u')) ^ (f' - t) := by
  set d := f' - t with hd
  have hd0 : 0 < d := Nat.sub_pos_of_lt ht
  have hdf : d ≤ f' := Nat.sub_le f' t
  -- power law: `Rgr (k*u') ((chainNorm r u')^k) = (Rgr u' (chainNorm r u'))^k` with the
  -- product's exact grade carried along, by induction from `Rgr_mul` at `hnorm 1`.
  have h1 : I.ExactGrade (1 * u') (I.chainNorm r (1 * u')) := hnorm 1 one_pos hf'
  have hbase : I.ExactGrade u' (I.chainNorm r u') := by simpa using h1
  have hpow : ∀ k : ℕ, 0 < k →
      I.ExactGrade (k * u') ((I.chainNorm r u') ^ k) ∧
      I.Rgr (k * u') ((I.chainNorm r u') ^ k) = (I.Rgr u' (I.chainNorm r u')) ^ k := by
    intro k hk
    induction k with
    | zero => exact absurd hk (lt_irrefl 0)
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        refine ⟨by simpa using hbase, by simp⟩
      · obtain ⟨ihg, ihr⟩ := ih hn
        have hmul := I.Rgr_mul (n * u') u' ((I.chainNorm r u') ^ n) (I.chainNorm r u')
          ihg hbase
        constructor
        · have : I.ExactGrade (n * u' + u') ((I.chainNorm r u') ^ n * I.chainNorm r u') :=
            hmul.1
          simpa [pow_succ, Nat.succ_mul] using this
        · have : I.Rgr (n * u' + u') ((I.chainNorm r u') ^ n * I.chainNorm r u')
              = I.Rgr (n * u') ((I.chainNorm r u') ^ n) * I.Rgr u' (I.chainNorm r u') :=
            hmul.2
          calc I.Rgr ((n + 1) * u') ((I.chainNorm r u') ^ (n + 1))
              = I.Rgr (n * u' + u') ((I.chainNorm r u') ^ n * I.chainNorm r u') := by
                rw [pow_succ, Nat.succ_mul]
            _ = I.Rgr (n * u') ((I.chainNorm r u') ^ n) * I.Rgr u' (I.chainNorm r u') :=
                this
            _ = (I.Rgr u' (I.chainNorm r u')) ^ n * I.Rgr u' (I.chainNorm r u') := by
                rw [ihr]
            _ = (I.Rgr u' (I.chainNorm r u')) ^ (n + 1) := by rw [pow_succ]
  -- the normalizer read at the slot grade is nonzero (Rgr_ne_zero at the B-1 supply)
  have hane : I.Rgr (d * u') (I.chainNorm r (d * u')) ≠ 0 :=
    I.Rgr_ne_zero (d * u') (I.chainNorm r (d * u')) (hnorm d hd0 hdf)
      (hnormdeg d hd0 hdf) (hnormz d hd0 hdf)
  -- unfold the ratio and cancel
  unfold FGMNCalculus.thetaRatio
  rw [mul_comm (I.Rgr (d * u') ((I.chainNorm r u') ^ d)) _, ← mul_assoc,
    mul_inv_cancel₀ hane, one_mul]
  exact (hpow d hd0).2

/-! ## C.99 companion `theta_letter_valued` — the recommended future shape (HOLD node) -/

/-- HOLD-side record: the recommended eventual re-sign of `theta_letter_valued` — the same
B-1 supply, and the letter clause at ℤ-exponents (`zpow`; the source's "grade-determined
integers j, k" are genuinely negative at the LP1 pin, so the signed ℕ-form overclaims).
The node stays BLOCKED on OPEN-LETTERS; this def only certifies the target shape. -/
def theta_letter_valued_target {r : ℕ} (W : DeepTower.{0, uKt} F H₀ hpin r)
    (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (_hr : r = 2)
    (_he' : 0 < e') (_hf' : 0 < f') (_hcop : Nat.Coprime u' e')
    (_hfloor : e' * W.Econst r < u')
    (_hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNorm r (d * u')))
    (_hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNorm r (d * u')).natDegree < (I.keyAt r).natDegree)
    (_hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNorm r (d * u') ≠ 0) : Prop :=
  I.thetaRatio 1 = 1 ∧
  ∀ t : ℕ, ∃ j k : ℤ, I.thetaRatio t = I.letterZ 1 ^ j * I.letterZ 2 ^ k

/-! ## C.101 `gentow2_B` — the A-C.12 re-sign shape

`W₂` stands in for leanspec's `T.deepTower hπ` (§10-preamble axiom, unlanded here). -/

/-- Re-signed C.101 `gentow2_B`: adds the source-stated recipe data (exact grade + degree
bound per slot, GENTOW2_PROOF S5 ll.307–309) and the per-slot B′ unit law `hunit` (the
C.100 discharge node applied at the used slots — carried explicitly because C.100 is HELD
on OPEN-EVAL-ISO). -/
def gentow2_B_resigned (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (_hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (W₂ : DeepTower.{0, uKt} F H₀ hpin 2)   -- stand-in for `T.deepTower hπ`
    (e' f' u' : ℕ) (I : FGMNCalculus W₂ e' f' u')
    (_hkey : I.keyAt 2 = composedKey T)
    (ρ : W₂.fld 2 ≃+* AdjoinRoot T.ψ₂)
    (_hκ : T.e₂ * T.f₂ * T.u₂ < u') (_he' : 0 < e') (_hf' : 0 < f')
    (_hcop : Nat.Coprime u' e')
    (c : ℕ → AdjoinRoot (towerLabel T)) (_hc0 : c 0 ≠ 0)
    (_hlift : ∀ t, t < f' →
      I.ExactGrade ((f' - t) * u') (k2DigitLift T (c t) ((f' - t) * u')))
    (_hliftdeg : ∀ t, t < f' →
      (k2DigitLift T (c t) ((f' - t) * u')).natDegree < T.D₂)
    (_hunit : ∀ t, t < f' →
      I.Rgr ((f' - t) * u') (k2DigitLift T (c t) ((f' - t) * u'))
        = I.Rgr ((f' - t) * u') (I.chainNorm 2 ((f' - t) * u'))
          * ρ.symm ((towerLabelEquiv T hπ) (c t))) : Prop :=
  I.Rres (recipe3 T e' f' u' c)
    = Polynomial.X ^ f'
      - ∑ t ∈ Finset.range f',
          Polynomial.C (I.Rgr ((f' - t) * u') (I.chainNorm 2 ((f' - t) * u'))
            * ρ.symm ((towerLabelEquiv T hπ) (c t))) * Polynomial.X ^ t

/-! ## C.103 `gentow2_A` — the A-C.12 re-sign shape -/

/-- Re-signed C.103 `gentow2_A`: `hadm` gains the source's `ψ₃(0) ≠ 0` antecedent
(GENTOW2_PROOF S4 ll.187–188) as its third conjunct, and the source-stated recipe degree
bounds are added (they type `KP_criterion`'s Monic/degree legs). -/
def gentow2_A_resigned (T : TowerDatum F H₀ hpin) (_hπ : Irreducible π) (_hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (W₂ : DeepTower.{0, uKt} F H₀ hpin 2)   -- stand-in for `T.deepTower hπ`
    (e' f' u' : ℕ) (I : FGMNCalculus W₂ e' f' u')
    (_hkey : I.keyAt 2 = composedKey T)
    (_ρ : W₂.fld 2 ≃+* AdjoinRoot T.ψ₂)
    (_hκ : T.e₂ * T.f₂ * T.u₂ < u') (_he' : 0 < e') (_hf' : 0 < f')
    (_hcop : Nat.Coprime u' e')
    (c : ℕ → AdjoinRoot (towerLabel T)) (_hc0 : c 0 ≠ 0)
    (_hliftdeg : ∀ t, t < f' →
      (k2DigitLift T (c t) ((f' - t) * u')).natDegree < T.D₂)
    (_hadm : Irreducible (I.Rres (recipe3 T e' f' u' c)) ∧
      (I.Rres (recipe3 T e' f' u' c)).natDegree = f' ∧
      (I.Rres (recipe3 T e' f' u' c)).coeff 0 ≠ 0) : Prop :=
  I.KP (recipe3 T e' f' u' c) ∧ Irreducible (recipe3 T e' f' u' c) ∧
  ¬ I.nuEquiv (recipe3 T e' f' u' c) (composedKey T)

/-! ## C.85 `theta_dictionary` — the A-C.12 tied re-sign shape -/

/-- Re-signed C.85 `theta_dictionary`: the quantifiers `s, t` are TIED to the dv₂-heights
of `A`, `B` and of the product (the EFF.GENTOW5.08 grading GTC found missing), and the
product's pinned-ness is carried as a hypothesis — the untied signed form collapses at
`s = t = 0` to exact multiplicativity of `dv2Res`, refuted by the PE4 cocycle pins. -/
def theta_dictionary_resigned (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (_hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)] : Prop :=
  ∃ θ : ℕ → AdjoinRoot (T.levelDatum hπ).r,
    θ 0 = 1 ∧ θ 1 = 1 ∧ (∀ t, θ t ≠ 0) ∧
    ∀ (s t : ℕ) (A B : Polynomial O),
      dv2Hgt (T.levelDatum hπ) A = (s : ℕ∞) →
      dv2Hgt (T.levelDatum hπ) B = (t : ℕ∞) →
      dv2Hgt (T.levelDatum hπ) (A * B) = ((s + t : ℕ) : ℕ∞) →
      dv2Res (T.levelDatum hπ) A ≠ 0 → dv2Res (T.levelDatum hπ) B ≠ 0 →
      dv2Res (T.levelDatum hπ) (A * B) ≠ 0 →
      θ (s + t) * dv2Res (T.levelDatum hπ) (A * B)
        = θ s * θ t * (dv2Res (T.levelDatum hπ) A * dv2Res (T.levelDatum hπ) B)

end Uniformity.Density.Tower.GSWCheck

/-! ## Axiom footprint (the one proved certificate) -/

#print axioms Uniformity.Density.Tower.GSWCheck.gentow2_Bpp_resigned_provable
