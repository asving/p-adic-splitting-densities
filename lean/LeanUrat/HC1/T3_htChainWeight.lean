/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsTower
import LeanUrat.Moves.L3_K1
import LeanUrat.Moves.L2_keyResidualPow
import LeanUrat.Moves.ResVal

/-!
# HC1.T3_htChainWeight — LST(i-a): ht IS the K1-chain weight of the basis monomial

moves_ref: MOVES 3736–3738 "ht(b, l) is the K1-chain weight of the coordinate's
basis monomial p^l·∏_r Φ̂_r^{innerslot_r(b)}". Stage scale = strTop·abs
(strTop = STR_K·e_K, §2.2 — audit C-1; SANITY at K = 0, (e₀,h₀): w(p^l·φ^b) =
e₀·l + b·h₀ = e₀·(l + b·κ₀) = strTop·ht ✓). deps: DefsTower; Moves `L3_K1`,
`L2_keyResidualPow` (clean); the per-move κ-update discipline (LST proof, MOVES
3750–3777). difficulty: HARD. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## General stage-valuation lemmas -/

/- [SYN2-S1 SWEEP-1, 2026-07-31] ResVal.w_one/ResVal.w_pow DELETED — single proof
source `Moves/ResVal.lean` (α-identical); uses re-pointed to ResVal.w_one/w_pow. -/

private lemma stage_w_prod (σ : Stage p F) {ι : Type*} (s : Finset ι) (g : ι → Polynomial ℤ_[p])
    (hg : ∀ i ∈ s, g i ≠ 0) : σ.w (∏ i ∈ s, g i) = ∑ i ∈ s, σ.w (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ResVal.w_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hga : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
    have hgs : ∀ i ∈ s, g i ≠ 0 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hprod : (∏ i ∈ s, g i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hgs
    rw [σ.hwmul _ _ hga hprod, ih hgs]

/-! ## gaussVal of the base uniformizer, and strAux facts -/

private lemma gaussVal_C_p : gaussVal (C (p : ℤ_[p])) = 1 := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := PadicInt.prime_p.ne_zero
  have hsupp : (C (p : ℤ_[p])).support = {0} := by rw [Polynomial.support_C hp0]
  unfold gaussVal
  have hne : (C (p : ℤ_[p])).support.Nonempty :=
    ⟨0, by rw [hsupp]; exact Finset.mem_singleton_self 0⟩
  rw [dif_pos hne]
  have hval : ((C (p : ℤ_[p])).support).inf' hne (fun i => (((C (p : ℤ_[p])).coeff i).valuation : ℤ))
      = (((C (p : ℤ_[p])).coeff 0).valuation : ℤ) := by
    apply le_antisymm
    · exact Finset.inf'_le _ (by rw [hsupp]; exact Finset.mem_singleton_self 0)
    · apply Finset.le_inf'
      intro b hb
      rw [hsupp, Finset.mem_singleton] at hb
      rw [hb]
  rw [hval, coeff_C_zero, PadicInt.valuation_p, Nat.cast_one]

private lemma strAux_succ (T : Tower p F) (k : ℕ) (hk : k < T.K + 1) :
    T.strAux (k + 1) = T.strAux k * (T.stg ⟨k, hk⟩).e := by
  have h : T.strAux (k + 1)
      = T.strAux k * (if h : k < T.K + 1 then (T.stg ⟨k, h⟩).e else 1) := rfl
  rw [h, dif_pos hk]

private lemma strAux_pos (T : Tower p F) (k : ℕ) : 0 < T.strAux k := by
  induction k with
  | zero => exact Nat.one_pos
  | succ n ih =>
    by_cases hc : n < T.K + 1
    · rw [strAux_succ T n hc]
      exact Nat.mul_pos ih (by have := (T.stg ⟨n, hc⟩).he; omega)
    · have h : T.strAux (n + 1)
          = T.strAux n * (if h : n < T.K + 1 then (T.stg ⟨n, h⟩).e else 1) := rfl
      rw [h, dif_neg hc, mul_one]; exact ih

private lemma strTop_eq (T : Tower p F) : T.strTop = T.strAux (T.K + 1) := by
  rw [strAux_succ T T.K (Nat.lt_succ_self _)]; rfl

private lemma degC_lt (σ : Stage p F) : (C (p : ℤ_[p])).degree < σ.Φ.degree := by
  rw [Polynomial.degree_C PadicInt.prime_p.ne_zero, Polynomial.degree_eq_natDegree σ.hmonic.ne_zero]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one σ.hdeg

/-! ## Degree monotonicity and the cross-stage stretch chain -/

private lemma deg_mono_step (T : Tower p F) (m : ℕ) (hm : m < T.K) :
    (T.stg ⟨m, Nat.lt_succ_of_lt hm⟩).Φ.natDegree ≤ (T.stg ⟨m + 1, Nat.succ_lt_succ hm⟩).Φ.natDegree := by
  set k : Fin T.K := ⟨m, hm⟩ with hk
  show (T.stg k.castSucc).Φ.natDegree ≤ (T.stg k.succ).Φ.natDegree
  cases T.move k with
  | inc ψ g Φhat e' h' zbar hyp core _ =>
    have hkey := core.base.child_key
    have hdeg := (L3_liftMonic (T.stg k.castSucc) ψ g hyp.hg Φhat hyp.hlift).2
    rw [hkey, hdeg]
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (T.stg k.castSucc).he hyp.hg)
  | recenter cc tt core _ =>
    obtain ⟨_, _, _, htt, _, _, _, hΦ', _, _, _, _, _, _⟩ := core.base
    rw [hΦ']
    have hne1 : (T.stg k.castSucc).Φ - tt ≠ 0 := by rw [← hΦ']; exact (T.stg k.succ).hmonic.ne_zero
    have hne2 : (T.stg k.castSucc).Φ ≠ 0 := (T.stg k.castSucc).hmonic.ne_zero
    have hdegeq : ((T.stg k.castSucc).Φ - tt).degree = (T.stg k.castSucc).Φ.degree :=
      Polynomial.degree_sub_eq_left_of_degree_lt htt
    have hnd : ((T.stg k.castSucc).Φ - tt).natDegree = (T.stg k.castSucc).Φ.natDegree := by
      rw [Polynomial.degree_eq_natDegree hne1, Polynomial.degree_eq_natDegree hne2] at hdegeq
      exact_mod_cast hdegeq
    rw [hnd]

private lemma stretch_step (T : Tower p F) (m : ℕ) (hm0 : m < T.K + 1) (hm1 : m + 1 < T.K + 1)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hcoef : B.degree < (T.stg ⟨m + 1, hm1⟩).Φ.degree) :
    (T.stg ⟨m + 1, hm1⟩).w B = ((T.stg ⟨m + 1, hm1⟩).e : ℤ) * (T.stg ⟨m, hm0⟩).w B := by
  have hm : m < T.K := by omega
  set k : Fin T.K := ⟨m, hm⟩ with hk
  show (T.stg k.succ).w B = ((T.stg k.succ).e : ℤ) * (T.stg k.castSucc).w B
  cases T.move k with
  | inc ψ g Φhat e' h' zbar hyp core _ =>
    rw [(T.stg k.succ).hStretch B hB hcoef, core.base.child_wPrev B]
  | recenter cc tt core _ =>
    obtain ⟨_, he', _, _, _, _, _, _, hw, _, _, _, _, _⟩ := core.base
    rw [hw B, he']; simp

private lemma deg_le (T : Tower p F) (a : ℕ) :
    ∀ (b : ℕ) (hab : a ≤ b) (hbK : b < T.K + 1),
      (T.stg ⟨a, by omega⟩).Φ.natDegree ≤ (T.stg ⟨b, hbK⟩).Φ.natDegree := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ n hn ih =>
    intro hbK
    have hnK : n < T.K + 1 := by omega
    have hnlt : n < T.K := by omega
    exact le_trans (ih hnK) (deg_mono_step T n hnlt)

private lemma stretch_chain (T : Tower p F) (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (r : ℕ) (hr : r < T.K + 1)
    (hcoef : ∀ mm : Fin (T.K + 1), r < mm.val → B.degree < (T.stg mm).Φ.degree) :
    ∀ (m : ℕ) (_ : r ≤ m) (hmK : m < T.K + 1),
      (T.strAux (r + 1) : ℤ) * (T.stg ⟨m, hmK⟩).w B
        = (T.strAux (m + 1) : ℤ) * (T.stg ⟨r, hr⟩).w B := by
  intro m hrm
  induction m, hrm using Nat.le_induction with
  | base => intro _; rfl
  | succ n hn ih =>
    intro hbK
    have hnK : n < T.K + 1 := by omega
    have ihn : (T.strAux (r + 1) : ℤ) * (T.stg ⟨n, hnK⟩).w B
        = (T.strAux (n + 1) : ℤ) * (T.stg ⟨r, hr⟩).w B := ih hnK
    have hstep : (T.stg ⟨n + 1, hbK⟩).w B
        = ((T.stg ⟨n + 1, hbK⟩).e : ℤ) * (T.stg ⟨n, hnK⟩).w B :=
      stretch_step T n hnK hbK B hB (hcoef ⟨n + 1, hbK⟩ (Nat.lt_succ_of_le hn))
    have hstrAux : T.strAux (n + 1 + 1) = T.strAux (n + 1) * (T.stg ⟨n + 1, hbK⟩).e := by
      have h : T.strAux (n + 1 + 1)
          = T.strAux (n + 1) * (if h : n + 1 < T.K + 1 then (T.stg ⟨n + 1, h⟩).e else 1) := rfl
      rw [h, dif_pos hbK]
    rw [hstep, hstrAux]; push_cast
    linear_combination ((T.stg ⟨n + 1, hbK⟩).e : ℤ) * ihn

/-! ## The per-key rational identity -/

private lemma key_rat (T : Tower p F) (r : Fin (T.K + 1))
    (hCHAIN : (T.strAux (r.val + 1) : ℤ) * (T.stg (Fin.last T.K)).w ((T.stg r).Φ)
        = (T.strTop : ℤ) * ((T.stg r).h : ℤ)) :
    ((T.stg (Fin.last T.K)).w ((T.stg r).Φ) : ℚ) = (T.strTop : ℚ) * T.kappa r := by
  have he : ((T.stg r).e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (T.stg r).he; omega)
  have hsa : ((T.strAux r.val : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by have := strAux_pos T r.val; omega)
  have hsplit : (T.strAux (r.val + 1) : ℚ) = (T.strAux r.val : ℚ) * ((T.stg r).e : ℚ) := by
    have h := strAux_succ T r.val r.isLt
    rw [show (⟨r.val, r.isLt⟩ : Fin (T.K + 1)) = r from rfl] at h
    exact_mod_cast h
  have hCq : (T.strAux (r.val + 1) : ℚ) * ((T.stg (Fin.last T.K)).w ((T.stg r).Φ) : ℚ)
      = (T.strTop : ℚ) * ((T.stg r).h : ℚ) := by exact_mod_cast hCHAIN
  rw [hsplit] at hCq
  simp only [Tower.kappa, Tower.str]
  field_simp
  linear_combination hCq

/-! ## Main theorem -/

theorem T3_htChainWeight {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (c : T.Coord) (hc : c.MonoNZ) :
    (((T.stg (Fin.last T.K)).w (T.mono c) : ℤ) : ℚ) = (T.strTop : ℚ) * T.ht c := by
  have hCp0 : (C (p : ℤ_[p])) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]; exact PadicInt.prime_p.ne_zero
  have hΦne : ∀ r : Fin (T.K + 1), (T.stg r).Φ ≠ 0 := fun r => (T.stg r).hmonic.ne_zero
  -- expansion of w(mono c) as a linear combination of key-weights
  have hCppow : (C ((p : ℤ_[p]) ^ c.l)) = (C (p : ℤ_[p])) ^ c.l := by rw [map_pow]
  have hprodne : (∏ r : Fin (T.K + 1), (T.stg r).Φ ^ c.slot r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun r _ => pow_ne_zero _ (hΦne r))
  have hCpl_ne : (C (p : ℤ_[p])) ^ c.l ≠ 0 := pow_ne_zero _ hCp0
  have hmono : T.mono c
      = (C (p : ℤ_[p])) ^ c.l * ∏ r : Fin (T.K + 1), (T.stg r).Φ ^ c.slot r := by
    rw [Tower.mono, hCppow]
  have hsum_eq : (∑ r : Fin (T.K + 1), (T.stg (Fin.last T.K)).w ((T.stg r).Φ ^ c.slot r))
      = ∑ r : Fin (T.K + 1), (c.slot r : ℤ) * (T.stg (Fin.last T.K)).w ((T.stg r).Φ) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [ResVal.w_pow (T.stg (Fin.last T.K)) _ (hΦne r) (c.slot r)]
  have hexpand : (T.stg (Fin.last T.K)).w (T.mono c)
      = (c.l : ℤ) * (T.stg (Fin.last T.K)).w (C (p : ℤ_[p]))
        + ∑ r : Fin (T.K + 1), (c.slot r : ℤ) * (T.stg (Fin.last T.K)).w ((T.stg r).Φ) := by
    rw [hmono, (T.stg (Fin.last T.K)).hwmul _ _ hCpl_ne hprodne,
        ResVal.w_pow (T.stg (Fin.last T.K)) _ hCp0 c.l,
        stage_w_prod (T.stg (Fin.last T.K)) Finset.univ _ (fun r _ => pow_ne_zero _ (hΦne r)),
        hsum_eq]
  -- value of w(C p) = strTop
  have h0lt : (0 : ℕ) < T.K + 1 := Nat.succ_pos _
  have hstg0 : T.stg ⟨0, h0lt⟩ = T.stg 0 := rfl
  have hw0 : (T.stg ⟨0, h0lt⟩).w (C (p : ℤ_[p])) = ((T.stg ⟨0, h0lt⟩).e : ℤ) := by
    rw [hstg0, (T.stg 0).hStretch (C (p : ℤ_[p])) hCp0 (degC_lt (T.stg 0)),
        T.base.1.1 (C (p : ℤ_[p])) hCp0, gaussVal_C_p, mul_one]
  have hstrAux1 : T.strAux (0 + 1) = (T.stg ⟨0, h0lt⟩).e := by
    have h := strAux_succ T 0 h0lt
    rw [show T.strAux 0 = (1 : ℕ) from rfl, one_mul] at h
    exact h
  have hCpval : (T.stg (Fin.last T.K)).w (C (p : ℤ_[p])) = (T.strTop : ℤ) := by
    have h0 := stretch_chain T (C (p : ℤ_[p])) hCp0 0 h0lt
      (fun mm _ => degC_lt (T.stg mm)) T.K (Nat.zero_le _) (Nat.lt_succ_self _)
    rw [hw0, hstrAux1] at h0
    have he0 : (0 : ℤ) < ((T.stg ⟨0, h0lt⟩).e : ℤ) := by exact_mod_cast (T.stg ⟨0, h0lt⟩).he
    have h0' : ((T.stg ⟨0, h0lt⟩).e : ℤ)
          * (T.stg ⟨T.K, Nat.lt_succ_self T.K⟩).w (C (p : ℤ_[p]))
        = ((T.stg ⟨0, h0lt⟩).e : ℤ) * (T.strAux (T.K + 1) : ℤ) := by
      rw [h0]; ring
    have hX := mul_left_cancel₀ (ne_of_gt he0) h0'
    rw [strTop_eq T]; exact hX
  -- per-term rational identity: (slot r)·w(Φ_r) = strTop·(slot r · κ_r)
  have hterm : ∀ r : Fin (T.K + 1),
      (c.slot r : ℚ) * ((T.stg (Fin.last T.K)).w ((T.stg r).Φ) : ℚ)
        = (T.strTop : ℚ) * ((c.slot r : ℚ) * T.kappa r) := by
    intro r
    rcases eq_or_ne r.val T.K with hrlast | hrneK
    · -- top slot: r = last, direct from hwΦ
      have hchain : (T.strAux (r.val + 1) : ℤ) * (T.stg (Fin.last T.K)).w ((T.stg r).Φ)
          = (T.strTop : ℤ) * ((T.stg r).h : ℤ) := by
        have hrl : r = Fin.last T.K := Fin.ext (by rw [Fin.val_last]; exact hrlast)
        subst hrl
        rw [Fin.val_last, (T.stg (Fin.last T.K)).hwΦ, strTop_eq T]
      rw [key_rat T r hchain]; ring
    · rcases eq_or_ne (c.slot r) 0 with hs0 | hsne
      · rw [hs0]; push_cast; ring
      · -- interior slot nonzero: degree grows, so the stretch chain applies
        have hrltK : r.val < T.K := lt_of_le_of_ne (Nat.lt_succ_iff.mp r.isLt) hrneK
        have hcoef : ∀ mm : Fin (T.K + 1), r.val < mm.val
            → (T.stg r).Φ.degree < (T.stg mm).Φ.degree := by
          intro mm hmm
          have hslotpos : 1 ≤ c.slot r := Nat.one_le_iff_ne_zero.mpr hsne
          have hslt := c.slot_lt ⟨r.val, hrltK⟩
          have hkr : (⟨r.val, hrltK⟩ : Fin T.K).castSucc = r := Fin.ext (by simp)
          have hsucc : (⟨r.val, hrltK⟩ : Fin T.K).succ = (⟨r.val + 1, by omega⟩ : Fin (T.K + 1)) :=
            Fin.ext (by simp)
          rw [hkr] at hslt
          have hbnd : T.slotBound ⟨r.val, hrltK⟩
              = (T.stg ⟨r.val + 1, by omega⟩).Φ.natDegree / (T.stg r).Φ.natDegree := by
            unfold Tower.slotBound
            rw [hkr, hsucc]
          rw [hbnd] at hslt
          have hN0 : 1 ≤ (T.stg r).Φ.natDegree := (T.stg r).hdeg
          have hb2 : 2 ≤ (T.stg ⟨r.val + 1, by omega⟩).Φ.natDegree / (T.stg r).Φ.natDegree := by omega
          have hN1 : 2 * (T.stg r).Φ.natDegree ≤ (T.stg ⟨r.val + 1, by omega⟩).Φ.natDegree :=
            (Nat.le_div_iff_mul_le (by omega)).mp hb2
          have hlt_nd : (T.stg r).Φ.natDegree < (T.stg ⟨r.val + 1, by omega⟩).Φ.natDegree := by omega
          have hdeg1 : (T.stg r).Φ.degree < (T.stg ⟨r.val + 1, by omega⟩).Φ.degree := by
            rw [Polynomial.degree_eq_natDegree (T.stg r).hmonic.ne_zero,
                Polynomial.degree_eq_natDegree (T.stg ⟨r.val + 1, by omega⟩).hmonic.ne_zero]
            exact_mod_cast hlt_nd
          have hdeg2 : (T.stg ⟨r.val + 1, by omega⟩).Φ.degree ≤ (T.stg mm).Φ.degree := by
            have hle := deg_le T (r.val + 1) mm.val (by omega) mm.isLt
            rw [Polynomial.degree_eq_natDegree (T.stg ⟨r.val + 1, by omega⟩).hmonic.ne_zero,
                Polynomial.degree_eq_natDegree (T.stg mm).hmonic.ne_zero]
            exact_mod_cast hle
          exact lt_of_lt_of_le hdeg1 hdeg2
        have hchain : (T.strAux (r.val + 1) : ℤ) * (T.stg (Fin.last T.K)).w ((T.stg r).Φ)
            = (T.strTop : ℤ) * ((T.stg r).h : ℤ) := by
          have h0 := stretch_chain T ((T.stg r).Φ) (hΦne r) r.val r.isLt hcoef
            T.K (le_of_lt hrltK) (Nat.lt_succ_self _)
          have hwr : (T.stg ⟨r.val, r.isLt⟩).w ((T.stg r).Φ) = ((T.stg r).h : ℤ) := (T.stg r).hwΦ
          rw [hwr] at h0
          rw [strTop_eq T]; exact h0
        rw [key_rat T r hchain]; ring
  -- assemble
  rw [hexpand, hCpval]
  push_cast
  simp only [Tower.ht]
  rw [show (∑ r : Fin (T.K + 1), (c.slot r : ℚ) * ((T.stg (Fin.last T.K)).w ((T.stg r).Φ) : ℚ))
        = ∑ r : Fin (T.K + 1), (T.strTop : ℚ) * ((c.slot r : ℚ) * T.kappa r)
      from Finset.sum_congr rfl (fun r _ => hterm r), ← Finset.mul_sum]
  ring

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T3_htChainWeight
