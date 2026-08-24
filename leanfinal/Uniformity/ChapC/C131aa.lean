/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C13
import Uniformity.ChapC.C35

/-!
# Uniformity.ChapC.C131aa — exact-half local lemmas for test keys

**Chapter C, NODES C.131aa′–ab′**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md`, §4.3 and §5).

This file supplies the corpus-local dictionary around the exact-half literature gate:
test-key slot data imply `dv`-purity, and the normalized level residual of a test key is
exactly its prescribed residual polynomial.  It neither declares nor restates the
`fgmn_dv_exact_mul` cite.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

private theorem gaussVal_one : gaussVal (1 : Polynomial O) = 0 := by
  rw [gaussVal, Polynomial.natDegree_one, Finset.range_one, Finset.inf_singleton,
    Polynomial.coeff_one_zero, IsDiscreteValuationRing.addVal_one]

private theorem stageHeight_one (F : KeyFrame O π) :
    F.stageHeight (1 : Polynomial O) = 0 := by
  rw [F.stageHeight_eq_inf]
  simp [Polynomial.coeff_one, gaussVal_one]

private theorem twistRead_zero_one (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key
      (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
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

private theorem twistRead_zero (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key
      (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) (k : ℕ) :
    F.twistRead H₀ hpin k (0 : Polynomial O) = 0 := by
  classical
  rw [KeyFrame.twistRead, KeyFrame.slotRes, Finset.sum_eq_zero]
  · simp
  intro t ht
  rw [Polynomial.coeff_zero, digAt_eq hπ (mul_zero (π ^
    ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁))).symm]
  simp

/-- The cleared `dv`-support of a test key is its seam value `ℓ · deg(r) · u`.
This is the common calculation behind both endpoint membership assertions. -/
private theorem dvSupp_testKey {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) :
    dvSupp F Ψ L.u L.ℓ = (((L.ℓ * L.r.natDegree) * L.u : ℕ) : ℕ∞) := by
  classical
  rcases hΨ with ⟨hmonic, hdeg, htop, hoff, hslots⟩
  have hweight (t : ℕ) (ht : t ≤ L.r.natDegree) :
      (((L.ℓ * L.r.natDegree) * L.u : ℕ) : ℕ∞) =
        L.ℓ • ((((L.r.natDegree - t) * L.u : ℕ) : ℕ∞)) +
          (L.u * (L.ℓ * t) : ℕ∞) := by
    have hn : (L.ℓ * L.r.natDegree) * L.u =
        L.ℓ * ((L.r.natDegree - t) * L.u) + L.u * (L.ℓ * t) := by
      calc
        (L.ℓ * L.r.natDegree) * L.u =
            (L.ℓ * ((L.r.natDegree - t) + t)) * L.u := by rw [Nat.sub_add_cancel ht]
        _ = L.ℓ * ((L.r.natDegree - t) * L.u) + L.u * (L.ℓ * t) := by ring
    simpa [nsmul_eq_mul] using congrArg (fun n : ℕ => (n : ℕ∞)) hn
  have htopmul : L.ℓ • (⊤ : ℕ∞) = ⊤ := by
    rw [nsmul_eq_mul, ENat.mul_top]
    exact_mod_cast L.hℓ.ne'
  rw [dvSupp]
  apply le_antisymm
  · have hzero := (hslots 0 L.hrdeg).2 L.hr0
    have hin := Finset.inf_le (f := fun j =>
      L.ℓ • dvHgt F Ψ j + (L.u * j : ℕ∞)) (show 0 ∈ Finset.range (Ψ.natDegree + 1) by simp)
    refine hin.trans_eq ?_
    have hzero' : F.stageHeight (dev F.key Ψ 0) = ((L.r.natDegree * L.u : ℕ) : ℕ∞) := by
      simpa using hzero.1
    rw [dvHgt, hzero']
    simpa using (hweight 0 (Nat.zero_le _)).symm
  · refine Finset.le_inf fun b hb => ?_
    by_cases hb_le : b ≤ L.ℓ * L.r.natDegree
    · by_cases hdvd : L.ℓ ∣ b
      · obtain ⟨t, rfl⟩ := hdvd
        have ht_le : t ≤ L.r.natDegree := by
          exact Nat.le_of_mul_le_mul_left (by simpa [Nat.mul_comm] using hb_le) L.hℓ
        rcases eq_or_lt_of_le ht_le with rfl | ht
        · rw [dvHgt, htop, stageHeight_one]
          simpa using (hweight L.r.natDegree (le_refl _)).le
        · by_cases hr : L.r.coeff t = 0
          · rw [dvHgt, (hslots t ht).1 hr, C118a.stageHeight_zero, htopmul, top_add]
            exact le_top
          · rw [dvHgt, ((hslots t ht).2 hr).1]
            exact (hweight t ht.le).le
      · have hb_lt : b < L.ℓ * L.r.natDegree := lt_of_le_of_ne hb_le (fun heq =>
          hdvd ⟨L.r.natDegree, by simpa [Nat.mul_comm] using heq⟩)
        rw [dvHgt, hoff b hb_lt hdvd, C118a.stageHeight_zero, htopmul, top_add]
        exact le_top
    · have hdev : dev F.key Ψ b = 0 := by
        have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
        refine dev_eq_zero_of_lt F.hmonic (F.hdeg ▸ hD) Ψ b ?_
        rw [hdeg, LevelDatum.keyDeg₂, F.hdeg]
        have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          (Nat.mul_lt_mul_left hD).2 (lt_of_not_ge hb_le)
      rw [dvHgt, hdev, C118a.stageHeight_zero, htopmul, top_add]
      exact le_top

/-- **NODE C.131aa′.** Every level-2 test key is one-sided at the level datum's `dv` slope. -/
theorem isTestKey_isDvPure {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) :
    IsDvPure F Ψ L.u L.ℓ := by
  classical
  rcases hΨ with ⟨hmonic, hdeg, htop, hoff, hslots⟩
  have hΨ' : IsTestKey L Ψ := ⟨hmonic, hdeg, htop, hoff, hslots⟩
  have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hquot : Ψ.natDegree / (F.e₁ * F.f₁) = L.ℓ * L.r.natDegree := by
    rw [hdeg, LevelDatum.keyDeg₂]
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_div_left (L.ℓ * L.r.natDegree) hD
  have hzero := (hslots 0 L.hrdeg).2 L.hr0
  have hzero' : F.stageHeight (dev F.key Ψ 0) = ((L.r.natDegree * L.u : ℕ) : ℕ∞) := by
    simpa using hzero.1
  have hsupp := dvSupp_testKey L hΨ'
  rw [IsDvPure, hquot]
  constructor
  · simp only [dvSideSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨by simp, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [hsupp, dvHgt, hzero']
      push_cast [nsmul_eq_mul]
      ring
    · rw [dvHgt, hzero']
      exact ENat.coe_ne_top _
  · simp only [dvSideSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · rw [hdeg, LevelDatum.keyDeg₂]
      exact Nat.lt_succ_of_le (by simpa [Nat.mul_assoc] using
        (Nat.le_mul_of_pos_left (L.ℓ * L.r.natDegree) hD))
    · refine ⟨?_, ?_⟩
      · rw [hsupp, dvHgt, htop, stageHeight_one]
        push_cast [nsmul_eq_mul]
        ring
      · rw [dvHgt, htop, stageHeight_one]
        exact ENat.coe_ne_top 0

/-- **NODE C.131ab′.** The normalized residual polynomial of a test key is exactly the
residual factor prescribed by its level datum, for every side witness and finite pin. -/
theorem dvResPoly_testKey {F : KeyFrame O π} (hπ : Irreducible π) {H₀ hpin}
    (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hne : (dvSideSet F Ψ L.u L.ℓ).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F Ψ (dvSideMin F Ψ L.u L.ℓ hne) = (M₀ : ℕ∞)) :
    dvResPoly F H₀ hpin Ψ L.u L.ℓ hne M₀ hp = L.r := by
  classical
  rcases hΨ with ⟨hmonic, hdeg, htop, hoff, hslots⟩
  have hΨ' : IsTestKey L Ψ := ⟨hmonic, hdeg, htop, hoff, hslots⟩
  have hpure := isTestKey_isDvPure L hΨ'
  have hmin : dvSideMin F Ψ L.u L.ℓ hne = 0 :=
    dvSideMin_eq_zero_of_isDvPure hpure hne
  have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hquot : Ψ.natDegree / (F.e₁ * F.f₁) = L.ℓ * L.r.natDegree := by
    rw [hdeg, LevelDatum.keyDeg₂]
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_div_left (L.ℓ * L.r.natDegree) hD
  have hside := natDegree_div_eq_of_isDvPure L.hℓ L.hcop hpure hne
  rw [hquot] at hside
  have hsideDeg : dvSideDeg F Ψ L.u L.ℓ hne = L.r.natDegree :=
    (Nat.eq_of_mul_eq_mul_left L.hℓ hside).symm
  have hzero := (hslots 0 L.hrdeg).2 L.hr0
  have hzero' : dvHgt F Ψ 0 = ((L.r.natDegree * L.u : ℕ) : ℕ∞) := by
    rw [dvHgt]
    simpa using hzero.1
  have hM : M₀ = L.r.natDegree * L.u := by
    have hc : (M₀ : ℕ∞) = ((L.r.natDegree * L.u : ℕ) : ℕ∞) := by
      rw [← hp, hmin, hzero']
    exact_mod_cast hc
  apply Polynomial.ext
  intro t
  rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, hsideDeg]
  by_cases ht : t ≤ L.r.natDegree
  · rw [if_pos (Nat.lt_succ_of_le ht), hmin, zero_add, hM, ← Nat.sub_mul,
      Nat.mul_comm t L.ℓ]
    rcases eq_or_lt_of_le ht with rfl | htlt
    · rw [Nat.sub_self, zero_mul, htop, twistRead_zero_one,
        L.hrmonic.coeff_natDegree]
    · by_cases hr : L.r.coeff t = 0
      · rw [(hslots t htlt).1 hr, twistRead_zero F hπ, hr]
      · exact ((hslots t htlt).2 hr).2
  · rw [if_neg (by omega), L.r.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge ht)]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.isTestKey_isDvPure
#print axioms Uniformity.Density.Tower.dvResPoly_testKey

end AxCheck
