/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132sg2

/-!
# Uniformity.ChapC.C132sg3 — A-C.21 enacted: the cleared-grade GENTOW family and the
UNCONDITIONAL μ₃ `GENTOW5W` at `(2,1,21)`

**[ANORM, 2026-08-27]** — the amendment MSG2's refutation demanded
(`runs/wave-b/verdict_MSG2.md`; `C132sg2.s2Mu3_gentow5w_two_hnorm_refuted`), enacted as
**A-C.21** in `leanspec/Leanspec/ChapC.lean` and landed here.

## The defect and the print-read (the amendment's evidence)

The signed B-1 family `hnorm : I.ExactGrade (d * u') (I.chainNormBelow r (d * u'))` read
the normalizer's printed INDEX as its grade.  The source grades the ladder normalizers
`n̂₂(u₃)`/`n̂₂(u₃d)` at `κ̄ := u₃/e(μ₂)` resp. `β_t := u₃d/e(μ₂)`
(`GENTOW2_PROOF_2026-08-09.md` S5.2 ll.324–325, 711, 740–744) — **Γ-valued PRE-clearing
rationals**.  The interface's integer grade coordinate is the FULL-CURRENT clearing
(`MU3_CAMPAIGN_2026-08-26.md` §2, the OPEN-DICT-2 decision record: `grade = e(μ₃)·β`), so
the honest cleared grade is `e(μ₃)·(u₃d/e(μ₂)) = e₃·(d·u₃) = e'·(d·u')` (§2.2's identity
`e(μᵢ)β = eᵢ·(e(μᵢ₋₁)β)`).  Machine confirmation at both landed instances:
`chainNormBelow 2 21 = 2⁴Φ′` has μ₃ grade `42 = 2·21` (`C132rp9` +
`C132rp10b.s2Hgt₃_corr`), and the depth-1 honest grade is `10 = 2·5` vs printed `5` —
the recipe-fields printed-numeral defect genre.

The CONCLUSION grades carry the same factor (an off-grade `Rgr` reads zero — the landed
`C99r.gentow2_Bpp` proof reads `Rgr` at exactly the `hnorm` grades), and the `hprev`
fence's grade re-indexes with them: the power law multiplies at the normalizer's cleared
grade `e'·u'`, and the source's own peel step asserts exactly that membership ("at each
peel the split-off factor's grade, κ̄ resp. 0, lies in Γ₂", S5.2 l.748; Γ₂-membership =
`e₃ ∣ cleared grade` by §2.2) — TRUE at `e'·u'` (`e' ∣ e'·u'`), unlike the pre-A-C.21
odd `u'` (coprime to `e'`).

## Why NEW declarations (the two-name architecture)

The do-not-edit refutation record `C132sg2.lean` passes the OLD-shape `hnorm` term to
`C107ac14.gentow5w_two` and states its theorems against the pre-A-C.21 `GENTOW5W` — any
in-place re-index breaks it.  So the pre-A-C.21 family is RETAINED VERBATIM (dated
supersession comments at each site), and the A-C.21 signed statements' leanfinal twins
land here under `Cleared` names.  NOTE the charge's expected wiring — "fire
`s2Mu3_gentow5w_two_of_norm` with the corrected hnorm" — is a type error (that binder IS
the refuted old shape); the evidence-supported enactment rebuilds the same wiring at the
corrected signature and fires it, which is what Part 3 does.

## Contents

* Part 0 — the A-C.21 carriers: `FGMNCalculus.thetaRatioCleared`, `GENTOW5WCleared`,
  `WleCleared` (byte-twins of the amended leanspec defs).
* Part 1 — the cleared engine + abstract twins: `ratio_power_law_cleared`,
  `gentow2_Bpp_cleared` (C.99), `gentow5w_two_cleared` (C.89 i=2),
  `gentow5w_one_shape_of_letter_tie_cleared` (C.89 i=1, letter tie still carried —
  OPEN-LETTERS unchanged).
* Part 2 — `gentow5_key_certificate_cleared` (C.90(a), the `hres` display re-indexed).
* Part 3 — the μ₃ instance: `s2Mu3_B1_exact_grade_supply_cleared` (A-C.21's `hnorm`
  DISCHARGED from rp9's identification + rp10b's `s2Hgt₃_corr`), and the star
  `s2Mu3_gentow5w_two : GENTOW5WCleared (s2DepthTwo h2 hq) 2 1 21 (s2Mu3Calculus h2 hq)`
  — **UNCONDITIONAL**, every leg closed.
* Part 4 — `s2Mu3_gentow5w_old_refuted`: the pre-A-C.21 carrier is FALSE at the honest
  instance (grade 21 is strictly below the honest 42, so the old `Rgr` read is zero by
  `Rgr_zero_of_above`) — the definitional-level justification of the re-index.

Sorry-free, no new axiom, no existing statement touched.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing

universe uKt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O}

/-! ## Part 0 — the A-C.21 cleared carriers (amended-leanspec byte twins) -/

/-- **[A-C.21] the cleared `ϑ`-carrier** — the amended `FGMNCalculus.thetaRatio`
(leanspec `ChapC.lean`): the ratio read at the operands' honest full-current grades
`e'·(t·u')`.  (The pre-A-C.21 `thetaRatio` is retained in `C130pk.lean` for the
`C132sg2.lean` record.) -/
noncomputable def FGMNCalculus.thetaRatioCleared {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} {r : ℕ} {W : DeepTower.{0, uKt} F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (t : ℕ) : W.fld r :=
  I.Rgr (e' * (t * u')) ((I.chainNormBelow r u') ^ t) *
    (I.Rgr (e' * (t * u')) (I.chainNormBelow r (t * u')))⁻¹

/-- **[A-C.21] the cleared `𝒲` carrier** — the amended `GENTOW5W` (leanspec): the per-`t`
law's `Rgr` read at the honest cleared grade `e'·((f'-t)·u')`. -/
def GENTOW5WCleared {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ)
    (I : FGMNCalculus W e' f' u') : Prop :=
  ∃ w : W.fld r, w ≠ 0 ∧ ∀ t, t < f' →
    I.Rgr (e' * ((f' - t) * u')) (I.chainNormBelow r ((f' - t) * u'))
        * I.thetaRatioCleared (f' - t)
      = w ^ (f' - t)

/-- **[A-C.21] the cleared cumulative `𝒲_{≤n}`** — the amended `Wle` (leanspec). -/
def WleCleared {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ)
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u') (n : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ n → ∀ hi : i ≤ r, GENTOW5WCleared (W.trunc i hi) e' f' u' (I i hi)

namespace C132sg3

/-! ## Part 1 — the cleared ratio engine and the abstract A-C.21 twins

The `C99r.gentow2_Bpp`/`C107ac14.ratio_power_law` algebra at the cleared grades: the
base grade is `e'·u'`, each `Rgr_mul` step adds `e'·u'` (consuming the re-indexed
`hprev : PrevGrade (e'·u')`), and the accumulated grade `d·(e'·u')` matches `hnorm`'s
`e'·(d·u')` by `Nat.mul_left_comm`. -/

/-- the cleared general-depth ratio power law (the shared engine; no depth fence — the
algebra is class-field-only, the supply burden sits in the hypotheses). -/
theorem ratio_power_law_cleared {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (hf' : 0 < f')
    (hprev : 2 ≤ f' → I.PrevGrade (e' * u'))
    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (e' * (d * u')) (I.chainNormBelow r (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNormBelow r (d * u')).natDegree < (I.keyAt r).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNormBelow r (d * u') ≠ 0)
    {t : ℕ} (ht : t < f') :
    I.Rgr (e' * ((f' - t) * u')) (I.chainNormBelow r ((f' - t) * u'))
        * I.thetaRatioCleared (f' - t)
      = (I.Rgr (e' * u') (I.chainNormBelow r u')) ^ (f' - t) := by
  by_cases hf1 : f' = 1
  · subst f'
    have ht0 : t = 0 := by omega
    subst t
    have hgrade : I.ExactGrade (e' * u') (I.chainNormBelow r u') := by
      simpa using hnorm 1 one_pos le_rfl
    have hdeg : (I.chainNormBelow r u').natDegree < (I.keyAt r).natDegree := by
      simpa using hnormdeg 1 one_pos le_rfl
    have hnz : I.chainNormBelow r u' ≠ 0 := by
      simpa using hnormz 1 one_pos le_rfl
    have ha : I.Rgr (e' * u') (I.chainNormBelow r u') ≠ 0 :=
      I.Rgr_ne_zero (e' * u') _ hgrade hdeg hnz
    simp [FGMNCalculus.thetaRatioCleared, ha]
  have hf2 : 2 ≤ f' := by omega
  set d := f' - t with hd
  have hd0 : 0 < d := Nat.sub_pos_of_lt ht
  have hdf : d ≤ f' := Nat.sub_le f' t
  have hbase : I.ExactGrade (e' * u') (I.chainNormBelow r u') := by
    simpa using hnorm 1 one_pos hf'
  have hpow : ∀ k : ℕ, 0 < k →
      I.ExactGrade (k * (e' * u')) ((I.chainNormBelow r u') ^ k) ∧
      I.Rgr (k * (e' * u')) ((I.chainNormBelow r u') ^ k) =
        (I.Rgr (e' * u') (I.chainNormBelow r u')) ^ k := by
    intro k hk
    induction k with
    | zero => exact absurd hk (lt_irrefl 0)
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        refine ⟨by simpa using hbase, by simp⟩
      · obtain ⟨ihg, ihr⟩ := ih hn
        have hmul := I.Rgr_mul (n * (e' * u')) (e' * u') ((I.chainNormBelow r u') ^ n)
          (I.chainNormBelow r u') ihg hbase (hprev hf2)
        constructor
        · have : I.ExactGrade (n * (e' * u') + e' * u')
              ((I.chainNormBelow r u') ^ n * I.chainNormBelow r u') := hmul.1
          simpa [pow_succ, Nat.succ_mul] using this
        · have hstep : I.Rgr (n * (e' * u') + e' * u')
              ((I.chainNormBelow r u') ^ n * I.chainNormBelow r u') =
              I.Rgr (n * (e' * u')) ((I.chainNormBelow r u') ^ n) *
                I.Rgr (e' * u') (I.chainNormBelow r u') := hmul.2
          calc I.Rgr ((n + 1) * (e' * u')) ((I.chainNormBelow r u') ^ (n + 1))
              = I.Rgr (n * (e' * u') + e' * u')
                  ((I.chainNormBelow r u') ^ n * I.chainNormBelow r u') := by
                rw [pow_succ, Nat.succ_mul]
            _ = I.Rgr (n * (e' * u')) ((I.chainNormBelow r u') ^ n) *
                  I.Rgr (e' * u') (I.chainNormBelow r u') := hstep
            _ = (I.Rgr (e' * u') (I.chainNormBelow r u')) ^ n *
                  I.Rgr (e' * u') (I.chainNormBelow r u') := by
                rw [ihr]
            _ = (I.Rgr (e' * u') (I.chainNormBelow r u')) ^ (n + 1) := by rw [pow_succ]
  have hane : I.Rgr (e' * (d * u')) (I.chainNormBelow r (d * u')) ≠ 0 :=
    I.Rgr_ne_zero (e' * (d * u')) (I.chainNormBelow r (d * u')) (hnorm d hd0 hdf)
      (hnormdeg d hd0 hdf) (hnormz d hd0 hdf)
  unfold FGMNCalculus.thetaRatioCleared
  rw [mul_comm (I.Rgr (e' * (d * u')) ((I.chainNormBelow r u') ^ d)) _, ← mul_assoc,
    mul_inv_cancel₀ hane, one_mul]
  rw [Nat.mul_left_comm e' d u']
  exact (hpow d hd0).2

/-- **NODE C.99 `gentow2_Bpp`, A-C.21 twin** — byte-faithful to the amended leanspec
axiom (`hr`/`he'`/`hcop`/`hfloor` carried unused, for fidelity to the signed scope). -/
theorem gentow2_Bpp_cleared {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ) [I : FGMNCalculus W e' f' u']
    (hr : r = 2)
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst r < u')
    (hprev : 2 ≤ f' → I.PrevGrade (e' * u'))
    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (e' * (d * u')) (I.chainNormBelow r (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNormBelow r (d * u')).natDegree < (I.keyAt r).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNormBelow r (d * u') ≠ 0)
    {t : ℕ} (ht : t < f') :
    I.Rgr (e' * ((f' - t) * u')) (I.chainNormBelow r ((f' - t) * u'))
        * I.thetaRatioCleared (f' - t)
      = (I.Rgr (e' * u') (I.chainNormBelow r u')) ^ (f' - t) :=
  ratio_power_law_cleared W e' f' u' I hf' hprev hnorm hnormdeg hnormz ht

/-- **NODE C.89 `gentow5w_two`, A-C.21 twin** — the `i = 2` discharge from the cleared
C.99: witness `w := Rgr (e'·u') (chainNormBelow 2 u')`, nonzero by `Rgr_ne_zero` at the
`d = 1` supply rows. -/
theorem gentow5w_two_cleared {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (W : DeepTower.{0, uKt} F H₀ hpin 2) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst 2 < u')
    (hprev : 2 ≤ f' → I.PrevGrade (e' * u'))
    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (e' * (d * u')) (I.chainNormBelow 2 (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNormBelow 2 (d * u')).natDegree < (I.keyAt 2).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNormBelow 2 (d * u') ≠ 0) :
    GENTOW5WCleared W e' f' u' I := by
  refine ⟨I.Rgr (e' * u') (I.chainNormBelow 2 u'), ?_, fun t ht => ?_⟩
  · have h := I.Rgr_ne_zero (e' * (1 * u')) (I.chainNormBelow 2 (1 * u'))
      (hnorm 1 one_pos hf') (hnormdeg 1 one_pos hf') (hnormz 1 one_pos hf')
    simpa using h
  · exact ratio_power_law_cleared W e' f' u' I hf' hprev hnorm hnormdeg hnormz ht

/-- **NODE C.89 `gentow5w_one_shape`, A-C.21 conditional twin** — the cleared ratio law
at depth 1, the OPEN-LETTERS tie still carried as `htie` (this amendment re-indexes
grades only; the letter gap is untouched). -/
theorem gentow5w_one_shape_of_letter_tie_cleared {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀}
    (W : DeepTower.{0, uKt} F H₀ hpin 1) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u')
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst 1 < u')
    (hprev : 2 ≤ f' → I.PrevGrade (e' * u'))
    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (e' * (d * u')) (I.chainNormBelow 1 (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNormBelow 1 (d * u')).natDegree < (I.keyAt 1).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNormBelow 1 (d * u') ≠ 0)
    (htie : ∃ k : ℕ, I.Rgr (e' * u') (I.chainNormBelow 1 u') = I.letterZ 1 ^ k) :
    ∃ k : ℕ, ∀ t, t < f' →
      I.Rgr (e' * ((f' - t) * u')) (I.chainNormBelow 1 ((f' - t) * u'))
          * I.thetaRatioCleared (f' - t)
        = (I.letterZ 1 ^ k) ^ (f' - t) := by
  obtain ⟨k, hk⟩ := htie
  refine ⟨k, fun t ht => ?_⟩
  rw [ratio_power_law_cleared W e' f' u' I hf' hprev hnorm hnormdeg hnormz ht, hk]

/-! ## Part 2 — NODE C.90(a) `gentow5_key_certificate`, A-C.21 twin

The `hres` display's `Rgr` read at the cleared grades, rewritten through the cleared `𝒲`
law (`WleCleared` at the top rung); the `wconj` twist display is `C107ac14`'s helper,
reused verbatim (de-privatized there under this amendment, statement byte-unchanged). -/

/-- **NODE C.90(a), A-C.21 twin** — byte-faithful to the amended leanspec axiom. -/
theorem gentow5_key_certificate_cleared {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} (W : DeepTower.{0, uKt} F H₀ hpin r) (e' f' u' : ℕ)
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u')
    (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (hW : WleCleared W e' f' u' I r)
    (hr3 : 3 ≤ r)
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst r < u')
    (Φnext : Polynomial O) (hmon : Φnext.Monic)
    (hdeg : Φnext.natDegree = e' * f' * W.Dcum r)
    (ψ' : Polynomial ((W.trunc r le_rfl).fld r)) (hψm : ψ'.Monic) (hψd : ψ'.natDegree = f')
    (c : ℕ → (W.trunc r le_rfl).fld r)
    (hψc : ψ' = Polynomial.X ^ f'
      - ∑ t ∈ Finset.range f', Polynomial.C (c t) * Polynomial.X ^ t)
    (hres : (I r le_rfl).Rres Φnext
      = Polynomial.X ^ f' - ∑ t ∈ Finset.range f',
          Polynomial.C ((I r le_rfl).Rgr (e' * ((f' - t) * u'))
              ((I r le_rfl).chainNormBelow r ((f' - t) * u'))
            * (I r le_rfl).thetaRatioCleared (f' - t) * c t) * Polynomial.X ^ t)
    (hadm : Irreducible ((I r le_rfl).Rres Φnext) ∧
      ((I r le_rfl).Rres Φnext).natDegree = f' ∧
      ((I r le_rfl).Rres Φnext).coeff 0 ≠ 0) :
    (I r le_rfl).KP Φnext ∧
    ∃ w : (W.trunc r le_rfl).fld r, w ≠ 0 ∧
      (I r le_rfl).Rres Φnext = wconj w ψ' := by
  have hkdeg : ((I r le_rfl).keyAt r).natDegree = (W.trunc r le_rfl).Dcum r :=
    (I r le_rfl).keyAt_deg r (by omega) le_rfl
  have hdeg' : Φnext.natDegree = e' * f' * ((I r le_rfl).keyAt r).natDegree := by
    rw [hkdeg]; exact hdeg
  have hKP : (I r le_rfl).KP Φnext :=
    (I r le_rfl).KP_criterion Φnext hmon hdeg' hadm.1 hadm.2.1 hadm.2.2
  obtain ⟨w, hw0, hlaw⟩ := hW r hr3 le_rfl le_rfl
  refine ⟨hKP, w, hw0, ?_⟩
  rw [hres, hψc, C107ac14.wconj_X_pow_sub_sum w hw0 f' hf' c]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hlaw t (Finset.mem_range.mp ht)]

/-! ## Part 3 — the μ₃ instance: A-C.21's `hnorm` DISCHARGED, the star UNCONDITIONAL -/

section S2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open C80 C130s2 C132rp0 C132rp8 C132kp0 C132fd0 C132fd1 C132rp9 C132rp10b C132sg2

variable [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- ★★ **A-C.21's B-1 exact-grade family at the μ₃ point, DISCHARGED** — the corrected
`hnorm` (grades `e'·(d·u') = 2·(d·21)`; `d` ranges over `{1}` at `f' = 1`): rp9's
identification `chainNormBelow 2 21 = 2⁴Φ′` chained with rp10b's grade certificate
`s2Hgt₃_corr = 42` through the sg2 `rfl` grade pin.  This is the supply MSG2 proved
IMPOSSIBLE at the pre-A-C.21 odd grade `21`
(`C132sg2.s2Mu3_gentow5w_two_hnorm_refuted`). -/
theorem s2Mu3_B1_exact_grade_supply_cleared :
    ∀ d, 0 < d → d ≤ 1 →
      (s2Mu3Calculus h2 hq).ExactGrade (2 * (d * 21))
        ((s2Mu3Calculus h2 hq).chainNormBelow 2 (d * 21)) := by
  intro d hd hd1
  have hd' : d = 1 := by omega
  subst hd'
  have hid : (s2Mu3Calculus h2 hq).chainNormBelow 2 (1 * 21) = corr h2 hq := by
    rw [one_mul]
    exact s2Mu3_chainNormBelow_two_twenty_one h2 hq (s2Mu3Calculus h2 hq) rfl
  rw [hid, s2Mu3Calculus_ExactGrade h2 hq]
  show S2Mu3ExactGrade h2 hq 42 (corr h2 hq)
  unfold S2Mu3ExactGrade
  rw [s2Hgt₃_corr h2 hq]
  norm_cast

/-- ★★★ **THE UNCONDITIONAL SIGNED CONCLUSION** — campaign exit gate 4, closed at the
A-C.21 signature: `GENTOW5W (s2DepthTwo h2 hq) 2 1 21 (s2Mu3Calculus h2 hq)` (the amended
signed carrier; leanfinal name `GENTOW5WCleared`), with EVERY leg discharged — no carried
hypothesis.  Wiring = MSG2's `s2Mu3_gentow5w_two_of_norm` rebuilt at the corrected
signature (firing that theorem itself with a "corrected hnorm" is a type error: its
binder IS the refuted pre-A-C.21 shape), fed by `s2Mu3_B1_exact_grade_supply_cleared`
and FD1's degree/nonzero supplies; the `hprev` fence is vacuous at `f' = 1`. -/
theorem s2Mu3_gentow5w_two :
    GENTOW5WCleared (s2DepthTwo h2 hq) 2 1 21 (s2Mu3Calculus h2 hq) := by
  have hE : (s2DepthTwo h2 hq).Econst 2 = 10 :=
    (s2Bridge_Econst h2 hq).trans (s2Tower_data h2 hq).2.2.2.2
  exact gentow5w_two_cleared (s2DepthTwo h2 hq) 2 1 21 (s2Mu3Calculus h2 hq)
    (by norm_num) (by norm_num) (by decide)
    (by rw [hE]; norm_num)
    (fun hcon => absurd hcon (by norm_num))
    (s2Mu3_B1_exact_grade_supply_cleared h2 hq)
    (s2Mu3_B1_degree_supply h2 hq (s2Mu3Calculus h2 hq) rfl)
    (s2Mu3_B1_nonzero_supply h2 hq (s2Mu3Calculus h2 hq) rfl)

/-! ## Part 4 — the pre-A-C.21 carrier is FALSE at the honest instance -/

/-- ★★ **the definitional-level justification of the re-index**: the PRE-A-C.21
`GENTOW5W` is not merely unsuppliable but FALSE at the μ₃ instance — its `Rgr` read at
grade `21` sits strictly below the honest grade `42`, so it reads ZERO
(`Rgr_zero_of_above`), and the old per-`t` law forces the witness `w = 0`. -/
theorem s2Mu3_gentow5w_old_refuted :
    ¬ GENTOW5W (s2DepthTwo h2 hq) 2 1 21 (s2Mu3Calculus h2 hq) := by
  rintro ⟨w, hw, hlaw⟩
  have hid : (s2Mu3Calculus h2 hq).chainNormBelow 2 21 = corr h2 hq :=
    s2Mu3_chainNormBelow_two_twenty_one h2 hq (s2Mu3Calculus h2 hq) rfl
  have hpin : (s2Mu3Calculus h2 hq).AboveGrade = S2Mu3AboveGrade h2 hq := rfl
  have habove : (s2Mu3Calculus h2 hq).AboveGrade 21
      ((s2Mu3Calculus h2 hq).chainNormBelow 2 21) := by
    rw [hid, hpin]
    unfold S2Mu3AboveGrade
    rw [s2Hgt₃_corr h2 hq]
    have h21 : ((21 : ℕ) : WithTop ℤ) = ((21 : ℤ) : WithTop ℤ) := by norm_cast
    rw [h21]
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  have hz : (s2Mu3Calculus h2 hq).Rgr 21
      ((s2Mu3Calculus h2 hq).chainNormBelow 2 21) = 0 :=
    (s2Mu3Calculus h2 hq).Rgr_zero_of_above 21 _ habove
  have h0 := hlaw 0 (by norm_num)
  simp only [Nat.sub_zero, one_mul, pow_one] at h0
  rw [hz, zero_mul] at h0
  exact hw h0.symm

end S2

end C132sg3

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.FGMNCalculus.thetaRatioCleared
#print axioms Uniformity.Density.Tower.GENTOW5WCleared
#print axioms Uniformity.Density.Tower.WleCleared
#print axioms Uniformity.Density.Tower.C132sg3.ratio_power_law_cleared
#print axioms Uniformity.Density.Tower.C132sg3.gentow2_Bpp_cleared
#print axioms Uniformity.Density.Tower.C132sg3.gentow5w_two_cleared
#print axioms Uniformity.Density.Tower.C132sg3.gentow5w_one_shape_of_letter_tie_cleared
#print axioms Uniformity.Density.Tower.C132sg3.gentow5_key_certificate_cleared
#print axioms Uniformity.Density.Tower.C132sg3.s2Mu3_B1_exact_grade_supply_cleared
#print axioms Uniformity.Density.Tower.C132sg3.s2Mu3_gentow5w_two
#print axioms Uniformity.Density.Tower.C132sg3.s2Mu3_gentow5w_old_refuted

end AxCheck
