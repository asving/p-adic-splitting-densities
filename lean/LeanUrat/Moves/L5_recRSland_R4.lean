/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore

/-!
# Moves/L5_recRSland_R4 — the RS landing + the anchored transform (D.10)

Unit `L5.recRSland` of `MANIFEST_CORE.json`. See `notes/MOVES_2026-07-24.md` ~2455-2476.

Conjunct 2 (the anchored transform, Case-J content) is exactly `hsub f` (the
`RecenterSubstCore` substitution identity) unfolded through the two anchor decompositions
and the `eval₂` ring hom into `RatFunc F`.

Conjunct 1 (the RS landing `ord_{z−c̃} Ranch = μ ⟺ a' = μ`): clear denominators in
conjunct 2 (multiply by `X^{(−a')⁺}·(X+c̃)^{(−a)⁺}`), pull the resulting identity back to
`F[X]` by injectivity of `algebraMap F[X] → RatFunc F`, and compare `rootMultiplicity` at
`0` on both sides: the left contributes `a'⁺` (the anchors' constant terms are nonzero and
`c̃ ≠ 0`), the right contributes `a'⁻ + m` with `m = ord_{X}(Ranch(X + c̃)) = ord_{z−c̃} Ranch`,
so `a' = m`; the `OrdPsiPoly` clause is `m = μ` via monic-map divisibility transfer and the
shift isomorphism `Q ↦ Q∘(X + c̃)`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanUrat.Moves

open Polynomial

/-- `algebraMap F[X] → RatFunc F` is `eval₂` at `RatFunc.X` (both ring homs agree on `C`, `X`). -/
private lemma algMap_eq_eval₂_ratfunc {F : Type*} [Field F] (Q : Polynomial F) :
    algebraMap (Polynomial F) (RatFunc F) Q
      = Polynomial.eval₂ (algebraMap F (RatFunc F)) RatFunc.X Q := by
  have h : (algebraMap (Polynomial F) (RatFunc F))
      = (Polynomial.eval₂RingHom (algebraMap F (RatFunc F)) RatFunc.X) := by
    apply Polynomial.ringHom_ext
    · intro a; simp [RatFunc.algebraMap_C]
    · simp [RatFunc.algebraMap_X]
  rw [h]; rfl

/-- Composing with `X + C c` and then with `X − C c` is the identity on `F[X]`. -/
private lemma comp_add_sub_cancel {F : Type*} [Field F] (c : F) (Q : Polynomial F) :
    (Q.comp (Polynomial.X + Polynomial.C c)).comp (Polynomial.X - Polynomial.C c) = Q := by
  rw [Polynomial.comp_assoc]
  simp [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, sub_add_cancel]

/-- `X^n ∣ Q∘(X + c)` iff `(X − c)^n ∣ Q`: the shift is a ring automorphism of `F[X]`. -/
private lemma X_pow_dvd_comp_iff {F : Type*} [Field F] (c : F) (Q : Polynomial F) (n : ℕ) :
    (Polynomial.X : Polynomial F) ^ n ∣ Q.comp (Polynomial.X + Polynomial.C c)
      ↔ (Polynomial.X - Polynomial.C c) ^ n ∣ Q := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S.comp (Polynomial.X - Polynomial.C c), ?_⟩
    have h := congrArg (fun P => P.comp (Polynomial.X - Polynomial.C c)) hS
    simpa [comp_add_sub_cancel, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.X_comp] using h
  · rintro ⟨S, hS⟩
    exact ⟨S.comp (Polynomial.X + Polynomial.C c), by
      simp [hS, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp,
        Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_right]⟩

theorem L5_recRSland {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ σ' : Stage p F) (cc : ↥σ.K) (hcc : cc ≠ 0) (tt : Polynomial ℤ_[p]) (hrec : IsRecenteringCore σ σ' cc tt) (hsub : RecenterSubstCore σ σ' cc) (μ : ℕ) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (a : ℤ) (Ranch : Polynomial ↥σ.K) (hanch : HasAnchorK (σ.R f) a Ranch) (a' : ℤ) (Ranch' : Polynomial ↥σ'.K) (hanch' : HasAnchorK (σ'.R f) a' Ranch') : (OrdPsiPoly (Polynomial.X - Polynomial.C cc) Ranch μ ↔ a' = (μ : ℤ)) ∧ (((ratX F ^ a' : (RatFunc F)ˣ) : RatFunc F) * algebraMap (Polynomial F) (RatFunc F) (Ranch'.map σ'.K.subtype) = ((ratXShift ((cc : ↥σ.K) : F) ^ a : (RatFunc F)ˣ) : RatFunc F) * algebraMap (Polynomial F) (RatFunc F) ((Ranch.map σ.K.subtype).comp (Polynomial.X + Polynomial.C ((cc : ↥σ.K) : F)))) := by
  -- ## Conjunct 2 first (it also feeds conjunct 1): `hsub f` unfolded through the anchors.
  have hkey : ((ratX F ^ a' : (RatFunc F)ˣ) : RatFunc F)
        * algebraMap (Polynomial F) (RatFunc F) (Ranch'.map σ'.K.subtype)
      = ((ratXShift ((cc : ↥σ.K) : F) ^ a : (RatFunc F)ˣ) : RatFunc F)
        * algebraMap (Polynomial F) (RatFunc F)
            ((Ranch.map σ.K.subtype).comp (Polynomial.X + Polynomial.C ((cc : ↥σ.K) : F))) := by
    have hLHS : σ'.ratRes f
        = ((ratX F ^ a' : (RatFunc F)ˣ) : RatFunc F)
            * algebraMap (Polynomial F) (RatFunc F) (Ranch'.map σ'.K.subtype) := by
      simp only [Stage.ratRes]
      rw [hanch'.2, map_mul, LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_toLaurent]
      congr 1
      rw [← Polynomial.eval₂_map]
      exact (algMap_eq_eval₂_ratfunc (Ranch'.map σ'.K.subtype)).symm
    have hRHS : σ.ratResShift ((cc : ↥σ.K) : F) f
        = ((ratXShift ((cc : ↥σ.K) : F) ^ a : (RatFunc F)ˣ) : RatFunc F)
            * algebraMap (Polynomial F) (RatFunc F)
                ((Ranch.map σ.K.subtype).comp (Polynomial.X + Polynomial.C ((cc : ↥σ.K) : F))) := by
      simp only [Stage.ratResShift]
      rw [hanch.2, map_mul, LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_toLaurent]
      congr 1
      rw [← Polynomial.eval₂_map, algMap_eq_eval₂_ratfunc, Polynomial.eval₂_comp]
      congr 1
      show ((ratXShift ((cc : ↥σ.K) : F)) : RatFunc F)
          = Polynomial.eval₂ (algebraMap F (RatFunc F)) RatFunc.X
              (Polynomial.X + Polynomial.C ((cc : ↥σ.K) : F))
      simp [ratXShift, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
    have key := hsub f
    rw [hLHS, hRHS] at key
    exact key
  refine ⟨?_, hkey⟩
  -- ## Conjunct 1: the RS landing `ord_{z−c̃}(Ranch) = μ ⟺ a' = μ`.
  set c : F := ((cc : ↥σ.K) : F) with hc_def
  set Q : Polynomial F := Ranch.map σ.K.subtype with hQ_def
  set Q' : Polynomial F := Ranch'.map σ'.K.subtype with hQ'_def
  set Qc : Polynomial F := Q.comp (Polynomial.X + Polynomial.C c) with hQc_def
  have hinj : Function.Injective (σ.K.subtype) := Subtype.coe_injective
  have hinj' : Function.Injective (σ'.K.subtype) := Subtype.coe_injective
  have hcne : c ≠ 0 := fun h => hcc (Subtype.ext h)
  have hQ0 : Q.coeff 0 ≠ 0 := by
    rw [hQ_def, Polynomial.coeff_map]
    exact fun h => hanch.1 (hinj (by simpa using h))
  have hQ'0 : Q'.coeff 0 ≠ 0 := by
    rw [hQ'_def, Polynomial.coeff_map]
    exact fun h => hanch'.1 (hinj' (by simpa using h))
  have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h]; simp)
  have hQ'ne : Q' ≠ 0 := fun h => hQ'0 (by rw [h]; simp)
  have hQcne : Qc ≠ 0 := by
    intro h
    have h2 := congrArg (fun P => P.comp (Polynomial.X - Polynomial.C c)) h
    simp only [hQc_def, comp_add_sub_cancel, Polynomial.zero_comp] at h2
    exact hQne h2
  -- ### Clear denominators in `hkey` and pull back to `F[X]`.
  have hXne : (RatFunc.X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
  have hSne : (RatFunc.X + RatFunc.C c : RatFunc F) ≠ 0 := by
    simpa [ratXShift] using (ratXShift c).ne_zero
  have hkey' : (RatFunc.X : RatFunc F) ^ a' * algebraMap (Polynomial F) (RatFunc F) Q'
      = (RatFunc.X + RatFunc.C c) ^ a * algebraMap (Polynomial F) (RatFunc F) Qc := by
    have h1 : ((ratX F ^ a' : (RatFunc F)ˣ) : RatFunc F) = (RatFunc.X : RatFunc F) ^ a' := by
      rw [Units.val_zpow_eq_zpow_val, ratX, Units.val_mk0]
    have h2 : ((ratXShift c ^ a : (RatFunc F)ˣ) : RatFunc F)
        = (RatFunc.X + RatFunc.C c : RatFunc F) ^ a := by
      rw [Units.val_zpow_eq_zpow_val, ratXShift, Units.val_mk0]
    rw [← h1, ← h2]; exact hkey
  have hP : (Polynomial.X : Polynomial F) ^ a'.toNat
        * (Polynomial.X + Polynomial.C c) ^ (-a).toNat * Q'
      = (Polynomial.X + Polynomial.C c) ^ a.toNat
        * (Polynomial.X : Polynomial F) ^ (-a').toNat * Qc := by
    apply RatFunc.algebraMap_injective F
    simp only [map_mul, map_pow, map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    rw [← zpow_natCast (RatFunc.X : RatFunc F) a'.toNat,
        ← zpow_natCast (RatFunc.X + RatFunc.C c : RatFunc F) ((-a).toNat),
        ← zpow_natCast (RatFunc.X + RatFunc.C c : RatFunc F) a.toNat,
        ← zpow_natCast (RatFunc.X : RatFunc F) ((-a').toNat)]
    have e1 : (a'.toNat : ℤ) = a' + ((-a').toNat : ℤ) := by omega
    have e2 : (a.toNat : ℤ) = a + ((-a).toNat : ℤ) := by omega
    rw [e1, e2, zpow_add₀ hXne, zpow_add₀ hSne]
    linear_combination ((RatFunc.X : RatFunc F) ^ (((-a').toNat : ℤ))
        * (RatFunc.X + RatFunc.C c : RatFunc F) ^ (((-a).toNat : ℤ))) * hkey'
  -- ### Compare `rootMultiplicity` at `0`: `a' = m` with `m = ord_X(Qc)`.
  have hXpolyne : ∀ k : ℕ, ((Polynomial.X : Polynomial F) ^ k) ≠ 0 :=
    fun k => pow_ne_zero k Polynomial.X_ne_zero
  have hSpolyne : ∀ k : ℕ, ((Polynomial.X + Polynomial.C c : Polynomial F) ^ k) ≠ 0 :=
    fun k => pow_ne_zero k (Polynomial.monic_X_add_C c).ne_zero
  have hrmX : ∀ k : ℕ, Polynomial.rootMultiplicity (0 : F) ((Polynomial.X : Polynomial F) ^ k) = k := by
    intro k
    simpa using Polynomial.rootMultiplicity_X_sub_C_pow (0 : F) k
  have hrmSpow : ∀ k : ℕ, Polynomial.rootMultiplicity (0 : F) ((Polynomial.X + Polynomial.C c) ^ k) = 0 := by
    intro k
    apply Polynomial.rootMultiplicity_eq_zero
    simp only [Polynomial.IsRoot.def, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, zero_add]
    exact pow_ne_zero k hcne
  have hrmQ' : Polynomial.rootMultiplicity (0 : F) Q' = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero]
    exact hQ'0
  have hL1 : (Polynomial.X : Polynomial F) ^ a'.toNat
      * (Polynomial.X + Polynomial.C c) ^ (-a).toNat ≠ 0 := mul_ne_zero (hXpolyne _) (hSpolyne _)
  have hR1 : (Polynomial.X + Polynomial.C c : Polynomial F) ^ a.toNat
      * (Polynomial.X : Polynomial F) ^ (-a').toNat ≠ 0 := mul_ne_zero (hSpolyne _) (hXpolyne _)
  have hm := congrArg (Polynomial.rootMultiplicity (0 : F)) hP
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hL1 hQ'ne),
      Polynomial.rootMultiplicity_mul hL1,
      Polynomial.rootMultiplicity_mul (mul_ne_zero hR1 hQcne),
      Polynomial.rootMultiplicity_mul hR1,
      hrmX a'.toNat, hrmX (-a').toNat, hrmSpow (-a).toNat, hrmSpow a.toNat, hrmQ'] at hm
  -- `hm : a'.toNat + 0 + 0 = 0 + (-a').toNat + rootMultiplicity 0 Qc`
  -- ### The dvd chain: `(X − c̃)^n ∣ Ranch ⟺ n ≤ m`.
  have hchain : ∀ n : ℕ, ((Polynomial.X - Polynomial.C cc) ^ n ∣ Ranch
      ↔ n ≤ Polynomial.rootMultiplicity (0 : F) Qc) := by
    intro n
    have hmap : ((Polynomial.X - Polynomial.C cc) ^ n).map σ.K.subtype
        = (Polynomial.X - Polynomial.C c) ^ n := by
      simp [Polynomial.map_pow, Polynomial.map_sub, hc_def]
    have h1 : (Polynomial.X - Polynomial.C cc) ^ n ∣ Ranch
        ↔ (Polynomial.X - Polynomial.C c) ^ n ∣ Q := by
      rw [← Polynomial.map_dvd_map σ.K.subtype hinj ((Polynomial.monic_X_sub_C cc).pow n),
        hmap, ← hQ_def]
    rw [h1, ← X_pow_dvd_comp_iff c Q n, ← hQc_def, Polynomial.le_rootMultiplicity_iff hQcne]
    simp
  -- ### Close: unfold `OrdPsiPoly` and let `omega` finish from `hm`.
  show ((Polynomial.X - Polynomial.C cc) ^ μ ∣ Ranch
      ∧ ¬(Polynomial.X - Polynomial.C cc) ^ (μ + 1) ∣ Ranch) ↔ a' = (μ : ℤ)
  rw [hchain μ, hchain (μ + 1)]
  omega

end LeanUrat.Moves
