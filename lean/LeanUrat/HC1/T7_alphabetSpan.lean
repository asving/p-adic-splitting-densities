/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.T6_carrierLaws
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.ResVal

/-!
# HC1.T7_alphabetSpan — the alphabet is the finite additive span of the slot images

moves_ref: MOVES 3815–3821 "image = the additive span of the slot images … = the
digit's ALPHABET". deps: DefsCar, T6. sketch: closure of finitely many F_p-lines in
an elementary abelian p-group; card a p-power. difficulty: easy. hyp: none.

Proof route (escalation, 2026-07-28): the graded piece `grQ γ` is p-TORSION for
every tower (T6's `HasSide` + the base→top stretch chain give
`w_top(C p) = strTop ≥ 1`, so `p·f` always climbs out of the piece), and each slot
line satisfies the ∃-form closure `g_c(y₁) + g_c(y₂) = g_c(y₃)` (the base-residue
carry is killed in the piece via `hRadd`/`hRne` + the stretch chain
`w_top B = strTop·gaussVal B` on base-cone coefficients). The span set is then an
additive subgroup (negation = (p−1)-fold sum), equal to the closure; finiteness is
image-of-finite-data; the p-power cardinality is `IsPGroup.iff_card`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## The stretch chain (base→top weight propagation on base-cone coefficients) -/

/- [SYN2-S1 SWEEP-1, 2026-07-31] ResVal.w_one DELETED (= ResVal.w_one). -/

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

/-! ## gaussVal facts and the top-weight formula on base-cone coefficients -/

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

private lemma gaussVal_one : gaussVal (1 : Polynomial ℤ_[p]) = 0 := by
  have h10 : (1 : ℤ_[p]) ≠ 0 := one_ne_zero
  have hsupp : (1 : Polynomial ℤ_[p]).support = {0} := by
    rw [← Polynomial.C_1, Polynomial.support_C h10]
  unfold gaussVal
  have hne : (1 : Polynomial ℤ_[p]).support.Nonempty :=
    ⟨0, by rw [hsupp]; exact Finset.mem_singleton_self 0⟩
  rw [dif_pos hne]
  have hval : ((1 : Polynomial ℤ_[p]).support).inf' hne
        (fun i => (((1 : Polynomial ℤ_[p]).coeff i).valuation : ℤ))
      = (((1 : Polynomial ℤ_[p]).coeff 0).valuation : ℤ) := by
    apply le_antisymm
    · exact Finset.inf'_le _ (by rw [hsupp]; exact Finset.mem_singleton_self 0)
    · apply Finset.le_inf'
      intro b hb
      rw [hsupp, Finset.mem_singleton] at hb
      rw [hb]
  rw [hval, Polynomial.coeff_one_zero, PadicInt.valuation_one]
  norm_num

private lemma gaussVal_nonneg (f : Polynomial ℤ_[p]) : 0 ≤ gaussVal f := by
  unfold gaussVal
  by_cases h : f.support.Nonempty
  · rw [dif_pos h]
    apply Finset.le_inf'
    intro i _
    positivity
  · rw [dif_neg h]

/-- **The top-weight formula** on base-cone coefficients: for `B ≠ 0` with
`deg B < deg Φ₀`, the TOP stage's weight is `strTop · gaussVal B` — the base→top
propagation the carry-kill rides (degree monotonicity keeps `B` in every cone). -/
private lemma wTop_cone (T : Tower p F) (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hdeg : B.degree < (T.stg 0).Φ.degree) :
    (T.stg (Fin.last T.K)).w B = (T.strTop : ℤ) * gaussVal B := by
  have h0lt : (0 : ℕ) < T.K + 1 := Nat.succ_pos _
  have hstg0 : T.stg ⟨0, h0lt⟩ = T.stg 0 := rfl
  have hcoef : ∀ mm : Fin (T.K + 1), (0 : ℕ) < mm.val → B.degree < (T.stg mm).Φ.degree := by
    intro mm _
    have hle := deg_le T 0 mm.val (Nat.zero_le _) mm.isLt
    have hdle : (T.stg ⟨0, by omega⟩).Φ.degree ≤ (T.stg mm).Φ.degree := by
      rw [Polynomial.degree_eq_natDegree (T.stg ⟨0, by omega⟩).hmonic.ne_zero,
          Polynomial.degree_eq_natDegree (T.stg mm).hmonic.ne_zero]
      exact_mod_cast hle
    exact lt_of_lt_of_le hdeg hdle
  have h0 := stretch_chain T B hB 0 h0lt hcoef T.K (Nat.zero_le _) (Nat.lt_succ_self _)
  have hw0 : (T.stg ⟨0, h0lt⟩).w B = ((T.stg ⟨0, h0lt⟩).e : ℤ) * gaussVal B := by
    rw [hstg0, (T.stg 0).hStretch B hB hdeg, T.base.1.1 B hB]
  have hstrAux1 : T.strAux (0 + 1) = (T.stg ⟨0, h0lt⟩).e := by
    have h := strAux_succ T 0 h0lt
    rwa [show T.strAux 0 = (1 : ℕ) from rfl, one_mul] at h
  rw [hw0, hstrAux1] at h0
  have he0 : (0 : ℤ) < ((T.stg ⟨0, h0lt⟩).e : ℤ) := by
    have := (T.stg ⟨0, h0lt⟩).he; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have h0' : ((T.stg ⟨0, h0lt⟩).e : ℤ) * (T.stg ⟨T.K, Nat.lt_succ_self T.K⟩).w B
      = ((T.stg ⟨0, h0lt⟩).e : ℤ) * ((T.strAux (T.K + 1) : ℤ) * gaussVal B) := by
    rw [h0]; ring
  have hX := mul_left_cancel₀ (ne_of_gt he0) h0'
  rw [strTop_eq T]
  exact hX

private lemma strTop_pos' (T : Tower p F) : 0 < T.strTop := by
  rw [strTop_eq T]; exact strAux_pos T (T.K + 1)

private lemma degC_lt' (σ : Stage p F) : (C (p : ℤ_[p])).degree < σ.Φ.degree := by
  rw [Polynomial.degree_C PadicInt.prime_p.ne_zero,
      Polynomial.degree_eq_natDegree σ.hmonic.ne_zero]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one σ.hdeg

private lemma deg_one_lt (σ : Stage p F) : (1 : Polynomial ℤ_[p]).degree < σ.Φ.degree := by
  rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree σ.hmonic.ne_zero]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one σ.hdeg

/-! ## inGr helpers (T6's private quotient toolkit, replicated) -/

private lemma inGr_off (T : Tower p F) {γ : ℚ} (honL : ¬ T.onLattice γ)
    (f : Polynomial ℤ_[p]) : T.inGr γ f = 0 := by
  rw [Tower.inGr, dif_neg (fun h => honL h.1)]

private lemma inGr_on (T : Tower p F) {γ : ℚ} (honL : T.onLattice γ) (f : Polynomial ℤ_[p])
    (hf : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w f) :
    T.inGr γ f = Submodule.Quotient.mk (⟨f, hf⟩ : T.side.ge (⌊(T.strTop : ℚ) * γ⌋)) := by
  rw [Tower.inGr, dif_pos ⟨honL, hf⟩]

private lemma mk_eq_zero_iff (T : Tower p F) (m : ℤ) (f : Polynomial ℤ_[p])
    (hf : f ∈ T.side.ge m) :
    (Submodule.Quotient.mk (⟨f, hf⟩ : T.side.ge m) : T.side.grPiece m) = 0
      ↔ (↑m : WithTop ℤ) < T.side.w f := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

private lemma inGr_zero (T : Tower p F) (γ : ℚ) : T.inGr γ 0 = 0 := by
  rw [Tower.inGr]
  split
  · rename_i h
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((T.side.gt _).zero_mem)
  · rfl

/-- `side.w` reads the TOP stage's valuation on nonzeros (T6's `HasSide`). -/
private lemma sideW (T : Tower p F) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    T.side.w f = (((T.stg (Fin.last T.K)).w f : ℤ) : WithTop ℤ) :=
  T.side_w (T6_carrierLaws T).1 hf

/-! ## The graded piece is p-torsion (every tower, every γ) -/

private lemma grPiece_torsion (T : Tower p F) (m : ℤ) (x : T.side.grPiece m) :
    p • x = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (T.side.gtIn m) x
  have hmk : (p • (Submodule.Quotient.mk v : T.side.grPiece m))
      = Submodule.Quotient.mk (p • v) := by
    rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply]
  rw [hmk, Submodule.Quotient.mk_eq_zero]
  show ((T.side.ge m).subtype) (p • v) ∈ T.side.gt m
  have hcoe : ((T.side.ge m).subtype) (p • v) = p • (v : Polynomial ℤ_[p]) := by
    simp
  rw [hcoe]
  have hf : ((m : ℤ) : WithTop ℤ) ≤ T.side.w (v : Polynomial ℤ_[p]) := v.2
  by_cases hf0 : (v : Polynomial ℤ_[p]) = 0
  · rw [hf0, smul_zero]; exact (T.side.gt _).zero_mem
  · have hpne : (p : ℤ_[p]) ≠ 0 := PadicInt.prime_p.ne_zero
    have hCpne : (C (p : ℤ_[p])) ≠ 0 := Polynomial.C_ne_zero.mpr hpne
    have hpf : (p : ℕ) • (v : Polynomial ℤ_[p]) = C (p : ℤ_[p]) * (v : Polynomial ℤ_[p]) := by
      rw [nsmul_eq_mul]
      norm_cast
    have hprod : C (p : ℤ_[p]) * (v : Polynomial ℤ_[p]) ≠ 0 := mul_ne_zero hCpne hf0
    show ((m : ℤ) : WithTop ℤ) < T.side.w ((p : ℕ) • (v : Polynomial ℤ_[p]))
    rw [hpf, sideW T hprod]
    have hwmul := (T.stg (Fin.last T.K)).hwmul (C (p : ℤ_[p])) (v : Polynomial ℤ_[p]) hCpne hf0
    have hwCp : (T.stg (Fin.last T.K)).w (C (p : ℤ_[p])) = (T.strTop : ℤ) := by
      rw [wTop_cone T _ hCpne (degC_lt' (T.stg 0)), gaussVal_C_p, mul_one]
    have hwf := hf
    rw [sideW T hf0] at hwf
    have hwfle : m ≤ (T.stg (Fin.last T.K)).w (v : Polynomial ℤ_[p]) := by
      exact_mod_cast hwf
    have hstpos : (0 : ℤ) < (T.strTop : ℤ) := by exact_mod_cast strTop_pos' T
    have : m < (T.stg (Fin.last T.K)).w (C (p : ℤ_[p]) * (v : Polynomial ℤ_[p])) := by
      rw [hwmul, hwCp]; omega
    exact_mod_cast this

private lemma grQ_torsion (T : Tower p F) (γ : ℚ) (x : T.grQ γ) : p • x = 0 :=
  grPiece_torsion T ⌊(T.strTop : ℚ) * γ⌋ x

/-! ## digLift facts and the single-slot evaluation -/

private lemma digLift_zero (T : Tower p F) : T.digLift (0 : ↥(T.stg 0).FQ) = 0 := by
  rw [Tower.digLift, dif_neg]
  rintro ⟨B, hB0, _, _, hBR⟩
  have hz : (⟨((0 : ↥(T.stg 0).FQ) : F), (T.stg 0).hFQ_le (0 : ↥(T.stg 0).FQ).2⟩ :
      ↥(T.stg 0).K) = 0 := by
    ext; simp
  rw [hz, map_zero, zero_mul] at hBR
  exact (T.stg 0).hRne B hB0 hBR

private lemma digLift_spec (T : Tower p F) {y : ↥(T.stg 0).FQ} (h : T.digLift y ≠ 0) :
    T.digLift y ≠ 0 ∧ inC (T.stg 0).Φ (T.digLift y) ∧ (T.stg 0).wPrev (T.digLift y) = 0 ∧
    (T.stg 0).R (T.digLift y)
      = LaurentPolynomial.C (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K)
        * LaurentPolynomial.T 0 := by
  by_cases hex : ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC (T.stg 0).Φ B ∧ (T.stg 0).wPrev B = 0 ∧
      (T.stg 0).R B = LaurentPolynomial.C (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K)
        * LaurentPolynomial.T 0
  · rw [Tower.digLift, dif_pos hex]
    exact hex.choose_spec
  · exact absurd (by rw [Tower.digLift, dif_neg hex]) h

private lemma digLift_ne (T : Tower p F) {y : ↥(T.stg 0).FQ} (hy : y ≠ 0) :
    T.digLift y ≠ 0 := by
  have h1ne : (1 : Polynomial ℤ_[p]) ≠ 0 := one_ne_zero
  have h1C : inC (T.stg 0).Φ (1 : Polynomial ℤ_[p]) := deg_one_lt (T.stg 0)
  have hw1 : (T.stg 0).wPrev 1 = 0 := by rw [T.base.1.1 1 h1ne, gaussVal_one]
  have h0mem : (0 : ℤ) ∈ (T.stg 0).weightSet := hw1 ▸ (T.stg 0).hWS 1 h1ne h1C
  have hyF : ((y : ↥(T.stg 0).FQ) : F) ≠ 0 := fun h => hy (Subtype.ext h)
  have hk₀ne : (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K) ≠ 0 :=
    fun h => hyF (congrArg Subtype.val h)
  have hmem : (((Units.mk0 _ hk₀ne : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K) : F) ∈ (T.stg 0).FQ :=
    y.2
  -- V5 coset form: at the base stage K = FQ, so the coset base b is absorbed by c := y·b⁻¹
  obtain ⟨b, hb⟩ := (T.stg 0).hS6a 0 h0mem
  have hKFQ : (T.stg 0).K = (T.stg 0).FQ := T.base.1.2.2
  have hbinv : (((Units.mk0 _ hk₀ne * b⁻¹ : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K) : F)
      ∈ (T.stg 0).FQ :=
    (le_of_eq hKFQ) ((Units.mk0 _ hk₀ne * b⁻¹ : (↥(T.stg 0).K)ˣ) : ↥(T.stg 0).K).2
  obtain ⟨B, hB0, hBC, hBw, hBR⟩ := hb (Units.mk0 _ hk₀ne * b⁻¹) hbinv
  rw [inv_mul_cancel_right] at hBR
  have hex : ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC (T.stg 0).Φ B ∧ (T.stg 0).wPrev B = 0 ∧
      (T.stg 0).R B = LaurentPolynomial.C (⟨(y : F), (T.stg 0).hFQ_le y.2⟩ : ↥(T.stg 0).K)
        * LaurentPolynomial.T 0 := by
    refine ⟨B, hB0, hBC, hBw, ?_⟩
    rw [hBR]
    norm_num
  rw [Tower.digLift, dif_pos hex]
  exact hex.choose_spec.1

/-- The single-coordinate composite is the class of `digLift y · mono c` (all other
slots carry the digit 0, whose lift is 0 by `hRne`). -/
private lemma slot_eval (T : Tower p F) (b : ℕ) (γ : ℚ) (c : ↥(T.levelSet b γ))
    (y : ↥(T.stg 0).FQ) :
    T.typComposite b γ (Pi.single c y) = T.inGr γ (T.digLift y * T.mono ↑c) := by
  rw [Tower.typComposite]
  congr 1
  rw [Tower.slotCoeff, finsum_mem_def]
  have hset : (↑c : T.Coord) ∈ {c' : T.Coord | T.blk c' = b} := c.2.1
  have hind : ∀ x : T.Coord, x ≠ ↑c →
      Set.indicator {c' : T.Coord | T.blk c' = b}
        (fun c' => T.digLift (if h : c' ∈ T.levelSet b γ
            then (Pi.single c y : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ) ⟨c', h⟩ else 0)
          * T.mono c') x = 0 := by
    intro x hx
    by_cases hxs : x ∈ {c' : T.Coord | T.blk c' = b}
    · rw [Set.indicator_of_mem hxs]
      have hzero : (if h : x ∈ T.levelSet b γ
          then (Pi.single c y : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ) ⟨x, h⟩ else 0) = 0 := by
        by_cases hxl : x ∈ T.levelSet b γ
        · rw [dif_pos hxl]
          have hne : (⟨x, hxl⟩ : ↥(T.levelSet b γ)) ≠ c := fun h => hx (congrArg Subtype.val h)
          apply Pi.single_eq_of_ne hne
        · rw [dif_neg hxl]
      rw [hzero, digLift_zero, zero_mul]
    · rw [Set.indicator_of_notMem hxs]
  rw [finsum_eq_single _ (↑c : T.Coord) hind, Set.indicator_of_mem hset]
  have hval : (if h : (↑c : T.Coord) ∈ T.levelSet b γ
      then (Pi.single c y : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ) ⟨↑c, h⟩ else 0)
      = y := by
    rw [dif_pos c.2]
    have hc : (⟨(↑c : T.Coord), c.2⟩ : ↥(T.levelSet b γ)) = c := Subtype.ext rfl
    rw [hc, Pi.single_eq_same]
  rw [hval]

private lemma typ_single_zero (T : Tower p F) (b : ℕ) (γ : ℚ) (c : ↥(T.levelSet b γ)) :
    T.typComposite b γ (Pi.single c (0 : ↥(T.stg 0).FQ)) = 0 := by
  rw [slot_eval, digLift_zero, zero_mul, inGr_zero]

/-- Non-vanishing forces: on-lattice, both factors nonzero, and weight EXACTLY the
piece index. -/
private lemma typ_ne_zero_spec (T : Tower p F) (b : ℕ) (γ : ℚ) (c : ↥(T.levelSet b γ))
    {y : ↥(T.stg 0).FQ} (h : T.typComposite b γ (Pi.single c y) ≠ 0) :
    T.onLattice γ ∧ T.digLift y ≠ 0 ∧ T.mono ↑c ≠ 0 ∧
    T.side.w (T.digLift y * T.mono ↑c) = ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ) := by
  rw [slot_eval] at h
  by_cases honL : T.onLattice γ
  · by_cases hcond : ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ) ≤ T.side.w (T.digLift y * T.mono ↑c)
    · have hnz := h
      rw [inGr_on T honL _ hcond] at hnz
      have hnlt : ¬ ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ) < T.side.w (T.digLift y * T.mono ↑c) :=
        fun hlt => hnz ((mk_eq_zero_iff T _ _ hcond).mpr hlt)
      have heq : T.side.w (T.digLift y * T.mono ↑c) = ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ) :=
        le_antisymm (not_lt.mp hnlt) hcond
      have hprodne : T.digLift y * T.mono ↑c ≠ 0 := by
        intro h0
        rw [h0, T.side.w_zero] at heq
        exact (by simp : (⊤ : WithTop ℤ) ≠ ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ)) heq
      exact ⟨honL, left_ne_zero_of_mul hprodne, right_ne_zero_of_mul hprodne, heq⟩
    · rw [Tower.inGr, dif_neg (fun hc => hcond hc.2)] at h
      exact absurd rfl h
  · rw [inGr_off T honL] at h
    exact absurd rfl h

/-! ## Line closure: two slot values on one coordinate sum to a third slot value -/

private lemma tag_add (T : Tower p F) (y₁ y₂ : ↥(T.stg 0).FQ) :
    (⟨(y₁ : F), (T.stg 0).hFQ_le y₁.2⟩ : ↥(T.stg 0).K)
      + ⟨(y₂ : F), (T.stg 0).hFQ_le y₂.2⟩
      = ⟨((y₁ + y₂ : ↥(T.stg 0).FQ) : F), (T.stg 0).hFQ_le (y₁ + y₂).2⟩ := by
  apply Subtype.ext
  push_cast
  rfl

/- [SYN2-S1 SWEEP-1, 2026-07-31] stage0_w_neg DELETED (= ResVal.w_neg at T.stg 0). -/

/-- Cone element of positive base weight: TOP weight is at least `strTop ≥ 1` —
the base carry is killed in every piece it did not open. -/
private lemma wTop_pos_of_base_pos (T : Tower p F) (g : Polynomial ℤ_[p]) (hg : g ≠ 0)
    (hdeg : g.degree < (T.stg 0).Φ.degree) (hpos : 0 < (T.stg 0).w g) :
    (1 : ℤ) ≤ (T.stg (Fin.last T.K)).w g ∧
    (T.strTop : ℤ) ≤ (T.stg (Fin.last T.K)).w g := by
  have hstr : (T.stg 0).w g = ((T.stg 0).e : ℤ) * (T.stg 0).wPrev g :=
    (T.stg 0).hStretch g hg hdeg
  have hgv : (T.stg 0).wPrev g = gaussVal g := T.base.1.1 g hg
  have hgv0 : 0 ≤ gaussVal g := gaussVal_nonneg g
  have he0 : (1 : ℤ) ≤ ((T.stg 0).e : ℤ) := by exact_mod_cast (T.stg 0).he
  have hgvpos : 1 ≤ gaussVal g := by
    rcases lt_or_ge 0 (gaussVal g) with h | h
    · omega
    · exfalso
      have : gaussVal g = 0 := le_antisymm h hgv0
      rw [hstr, hgv, this, mul_zero] at hpos
      exact lt_irrefl 0 hpos
  have hwtop : (T.stg (Fin.last T.K)).w g = (T.strTop : ℤ) * gaussVal g :=
    wTop_cone T g hg hdeg
  have hst1 : (1 : ℤ) ≤ (T.strTop : ℤ) := by exact_mod_cast strTop_pos' T
  constructor
  · rw [hwtop]; nlinarith
  · rw [hwtop]; nlinarith

private lemma line_closed (T : Tower p F) (b : ℕ) (γ : ℚ) (c : ↥(T.levelSet b γ))
    (y₁ y₂ : ↥(T.stg 0).FQ) :
    ∃ y₃ : ↥(T.stg 0).FQ,
      T.typComposite b γ (Pi.single c y₁) + T.typComposite b γ (Pi.single c y₂)
        = T.typComposite b γ (Pi.single c y₃) := by
  by_cases h1 : T.typComposite b γ (Pi.single c y₁) = 0
  · exact ⟨y₂, by rw [h1, zero_add]⟩
  by_cases h2 : T.typComposite b γ (Pi.single c y₂) = 0
  · exact ⟨y₁, by rw [h2, add_zero]⟩
  obtain ⟨honL, hf₁ne, hμne, hw₁⟩ := typ_ne_zero_spec T b γ c h1
  obtain ⟨_, hf₂ne, _, hw₂⟩ := typ_ne_zero_spec T b γ c h2
  obtain ⟨_, hC₁, hwP₁, hR₁⟩ := digLift_spec T hf₁ne
  obtain ⟨_, hC₂, hwP₂, hR₂⟩ := digLift_spec T hf₂ne
  -- base weights of the two lifts are 0
  have hw0₁ : (T.stg 0).w (T.digLift y₁) = 0 := by
    rw [(T.stg 0).hStretch _ hf₁ne hC₁, hwP₁, mul_zero]
  have hw0₂ : (T.stg 0).w (T.digLift y₂) = 0 := by
    rw [(T.stg 0).hStretch _ hf₂ne hC₂, hwP₂, mul_zero]
  have hgv₁ : gaussVal (T.digLift y₁) = 0 := by rw [← T.base.1.1 _ hf₁ne]; exact hwP₁
  have hgv₂ : gaussVal (T.digLift y₂) = 0 := by rw [← T.base.1.1 _ hf₂ne]; exact hwP₂
  -- top weights of the lifts are 0, hence w_top(mono c) = m
  have hwK₁ : (T.stg (Fin.last T.K)).w (T.digLift y₁) = 0 := by
    rw [wTop_cone T _ hf₁ne hC₁, hgv₁, mul_zero]
  have hwK₂ : (T.stg (Fin.last T.K)).w (T.digLift y₂) = 0 := by
    rw [wTop_cone T _ hf₂ne hC₂, hgv₂, mul_zero]
  have hprod₁ : T.digLift y₁ * T.mono ↑c ≠ 0 := mul_ne_zero hf₁ne hμne
  have hprod₂ : T.digLift y₂ * T.mono ↑c ≠ 0 := mul_ne_zero hf₂ne hμne
  have hwKμ : (T.stg (Fin.last T.K)).w (T.mono ↑c) = ⌊(T.strTop : ℚ) * γ⌋ := by
    have h := hw₁
    rw [sideW T hprod₁] at h
    have hint : (T.stg (Fin.last T.K)).w (T.digLift y₁ * T.mono ↑c)
        = ⌊(T.strTop : ℚ) * γ⌋ := by exact_mod_cast h
    rwa [(T.stg (Fin.last T.K)).hwmul _ _ hf₁ne hμne, hwK₁, zero_add] at hint
  -- the sum of the two classes
  have hge₁ : ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ)
      ≤ T.side.w (T.digLift y₁ * T.mono ↑c) := le_of_eq hw₁.symm
  have hge₂ : ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ)
      ≤ T.side.w (T.digLift y₂ * T.mono ↑c) := le_of_eq hw₂.symm
  have hgesum : ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ)
      ≤ T.side.w ((T.digLift y₁ + T.digLift y₂) * T.mono ↑c) := by
    rw [add_mul]
    exact (T.side.ge _).add_mem hge₁ hge₂
  have hsum : T.typComposite b γ (Pi.single c y₁) + T.typComposite b γ (Pi.single c y₂)
      = T.inGr γ ((T.digLift y₁ + T.digLift y₂) * T.mono ↑c) := by
    rw [slot_eval, slot_eval, inGr_on T honL _ hge₁, inGr_on T honL _ hge₂,
        inGr_on T honL _ hgesum]
    have hsub : (⟨T.digLift y₁ * T.mono ↑c, hge₁⟩ : T.side.ge ⌊(T.strTop : ℚ) * γ⌋)
        + ⟨T.digLift y₂ * T.mono ↑c, hge₂⟩
        = ⟨(T.digLift y₁ + T.digLift y₂) * T.mono ↑c, hgesum⟩ :=
      Subtype.ext (add_mul _ _ _).symm
    rw [← hsub]
    exact (Submodule.Quotient.mk_add (T.side.gtIn ⌊(T.strTop : ℚ) * γ⌋)
      (x := ⟨T.digLift y₁ * T.mono ↑c, hge₁⟩) (y := ⟨T.digLift y₂ * T.mono ↑c, hge₂⟩)).symm
  rw [hsum]
  -- branch on whether the summed coefficient still reads at weight m
  by_cases hlt : ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ)
      < T.side.w ((T.digLift y₁ + T.digLift y₂) * T.mono ↑c)
  · -- the sum climbed out of the piece: it is 0 = the 0-digit slot value
    refine ⟨0, ?_⟩
    rw [typ_single_zero, inGr_on T honL _ hgesum]
    exact (mk_eq_zero_iff T _ _ hgesum).mpr hlt
  · -- exact weight m: the base residues did NOT cancel; compare with digLift (y₁+y₂)
    have heq : T.side.w ((T.digLift y₁ + T.digLift y₂) * T.mono ↑c)
        = ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ) := le_antisymm (not_lt.mp hlt) hgesum
    have hg₁₂μne : (T.digLift y₁ + T.digLift y₂) * T.mono ↑c ≠ 0 := by
      intro h0
      rw [h0, T.side.w_zero] at heq
      exact (by simp : (⊤ : WithTop ℤ) ≠ ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ)) heq
    have hg₁₂ne : T.digLift y₁ + T.digLift y₂ ≠ 0 := left_ne_zero_of_mul hg₁₂μne
    have hdeg₁₂ : (T.digLift y₁ + T.digLift y₂).degree < (T.stg 0).Φ.degree :=
      lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hC₁ hC₂)
    -- base weight of the sum is ≥ 0
    have hw12ge : 0 ≤ (T.stg 0).w (T.digLift y₁ + T.digLift y₂) := by
      have h := (T.stg 0).hwult _ _ hf₁ne hf₂ne hg₁₂ne
      rwa [hw0₁, hw0₂, min_self] at h
    -- it must be EXACTLY 0, else the top weight exceeds m
    have hw12 : (T.stg 0).w (T.digLift y₁ + T.digLift y₂) = 0 := by
      by_contra hne0
      have hpos : 0 < (T.stg 0).w (T.digLift y₁ + T.digLift y₂) :=
        lt_of_le_of_ne hw12ge (Ne.symm hne0)
      obtain ⟨hone, _⟩ := wTop_pos_of_base_pos T _ hg₁₂ne hdeg₁₂ hpos
      have hK := (T.stg (Fin.last T.K)).hwmul _ _ hg₁₂ne hμne
      have hKe : (T.stg (Fin.last T.K)).w ((T.digLift y₁ + T.digLift y₂) * T.mono ↑c)
          = ⌊(T.strTop : ℚ) * γ⌋ := by
        have h := heq
        rw [sideW T hg₁₂μne] at h
        exact_mod_cast h
      rw [hKe, hwKμ] at hK
      omega
    -- base residue additivity: the residues add to the (y₁+y₂)-tag
    have hRsum : (T.stg 0).R (T.digLift y₁ + T.digLift y₂)
        = LaurentPolynomial.C (⟨((y₁ + y₂ : ↥(T.stg 0).FQ) : F),
            (T.stg 0).hFQ_le (y₁ + y₂).2⟩ : ↥(T.stg 0).K) * LaurentPolynomial.T 0 := by
      rw [(T.stg 0).hRadd _ _ hf₁ne hf₂ne hg₁₂ne (hw0₁.trans hw0₂.symm)
        (hw12.trans hw0₁.symm), hR₁, hR₂, ← add_mul, ← map_add, tag_add]
    -- the summed digit cannot vanish
    have hy12 : y₁ + y₂ ≠ 0 := by
      intro h0
      have htag : (⟨((y₁ + y₂ : ↥(T.stg 0).FQ) : F), (T.stg 0).hFQ_le (y₁ + y₂).2⟩ :
          ↥(T.stg 0).K) = 0 := by
        apply Subtype.ext
        rw [h0]
        simp
      rw [htag, map_zero, zero_mul] at hRsum
      exact (T.stg 0).hRne _ hg₁₂ne hRsum
    -- the realized lift of y₁ + y₂
    have hf₁₂ne : T.digLift (y₁ + y₂) ≠ 0 := digLift_ne T hy12
    obtain ⟨_, hC₁₂, hwP₁₂, hR₁₂⟩ := digLift_spec T hf₁₂ne
    have hw0₁₂ : (T.stg 0).w (T.digLift (y₁ + y₂)) = 0 := by
      rw [(T.stg 0).hStretch _ hf₁₂ne hC₁₂, hwP₁₂, mul_zero]
    have hgv₁₂ : gaussVal (T.digLift (y₁ + y₂)) = 0 := by
      rw [← T.base.1.1 _ hf₁₂ne]; exact hwP₁₂
    have hwK₁₂ : (T.stg (Fin.last T.K)).w (T.digLift (y₁ + y₂)) = 0 := by
      rw [wTop_cone T _ hf₁₂ne hC₁₂, hgv₁₂, mul_zero]
    refine ⟨y₁ + y₂, ?_⟩
    -- the carry dies in the piece
    by_cases hcarry : T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂) = 0
    · -- no carry at all: the lifts agree on the nose
      have hgeq : T.digLift y₁ + T.digLift y₂ = T.digLift (y₁ + y₂) := sub_eq_zero.mp hcarry
      rw [slot_eval, hgeq]
    · -- carry ≠ 0: it has base weight ≥ 1, so its top weight exceeds m
      have hcw0 : 0 ≤ (T.stg 0).w (T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂)) := by
        have hnegne : -(T.digLift (y₁ + y₂)) ≠ 0 := neg_ne_zero.mpr hf₁₂ne
        have h := (T.stg 0).hwult _ _ hg₁₂ne hnegne (by rwa [← sub_eq_add_neg])
        rwa [ResVal.w_neg (T.stg 0) _ hf₁₂ne, hw12, hw0₁₂, min_self, ← sub_eq_add_neg] at h
      have hadd_sub : T.digLift (y₁ + y₂)
          + (T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂))
          = T.digLift y₁ + T.digLift y₂ := by ring
      have hcwpos : 0 < (T.stg 0).w (T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂)) := by
        rcases lt_or_eq_of_le hcw0 with h | h
        · exact h
        · exfalso
          have hRc := (T.stg 0).hRadd (T.digLift (y₁ + y₂))
            (T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂)) hf₁₂ne hcarry
            (by rw [hadd_sub]; exact hg₁₂ne)
            (hw0₁₂.trans h) (by rw [hadd_sub, hw12, hw0₁₂])
          rw [hadd_sub, hRsum, hR₁₂] at hRc
          have hR0 : (T.stg 0).R (T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂)) = 0 := by
            have h0 := hRc.symm
            rwa [add_eq_left] at h0
          exact (T.stg 0).hRne _ hcarry hR0
      have hdegc : (T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂)).degree
          < (T.stg 0).Φ.degree :=
        lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hdeg₁₂ hC₁₂)
      obtain ⟨hcK1, _⟩ := wTop_pos_of_base_pos T _ hcarry hdegc hcwpos
      -- decompose the class: sum-lift = target-lift + carry, carry class = 0
      have hwK12μ : T.side.w (T.digLift (y₁ + y₂) * T.mono ↑c)
          = ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ) := by
        rw [sideW T (mul_ne_zero hf₁₂ne hμne),
            (T.stg (Fin.last T.K)).hwmul _ _ hf₁₂ne hμne, hwK₁₂, zero_add, hwKμ]
      have hge₁₂ : ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ)
          ≤ T.side.w (T.digLift (y₁ + y₂) * T.mono ↑c) := le_of_eq hwK12μ.symm
      have hcμne : (T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂)) * T.mono ↑c ≠ 0 :=
        mul_ne_zero hcarry hμne
      have hgtc : ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ)
          < T.side.w ((T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂)) * T.mono ↑c) := by
        rw [sideW T hcμne, (T.stg (Fin.last T.K)).hwmul _ _ hcarry hμne, hwKμ]
        have : ⌊(T.strTop : ℚ) * γ⌋
            < (T.stg (Fin.last T.K)).w (T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂))
              + ⌊(T.strTop : ℚ) * γ⌋ := by omega
        exact_mod_cast this
      have hgec : ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ)
          ≤ T.side.w ((T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂)) * T.mono ↑c) :=
        le_of_lt hgtc
      rw [slot_eval, inGr_on T honL _ hgesum, inGr_on T honL _ hge₁₂]
      have hsplit : ((T.digLift y₁ + T.digLift y₂) * T.mono ↑c)
          = T.digLift (y₁ + y₂) * T.mono ↑c
            + (T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂)) * T.mono ↑c := by
        ring
      have hmk : (Submodule.Quotient.mk (⟨(T.digLift y₁ + T.digLift y₂) * T.mono ↑c, hgesum⟩ :
            T.side.ge ⌊(T.strTop : ℚ) * γ⌋) : T.side.grPiece ⌊(T.strTop : ℚ) * γ⌋)
          = Submodule.Quotient.mk ⟨T.digLift (y₁ + y₂) * T.mono ↑c, hge₁₂⟩
            + Submodule.Quotient.mk
              ⟨(T.digLift y₁ + T.digLift y₂ - T.digLift (y₁ + y₂)) * T.mono ↑c, hgec⟩ := by
        rw [← Submodule.Quotient.mk_add]
        congr 1
        exact Subtype.ext hsplit
      rw [hmk, (mk_eq_zero_iff T _ _ hgec).mpr hgtc, add_zero]
/-! ## Level-set finiteness (T11's argument, replicated privately to keep the
blueprint's dependency order T7 → T11) -/

private lemma levelSet_finite' (T : Tower p F) (b : ℕ) (γ : ℚ) :
    (T.levelSet b γ).Finite := by
  refine Set.Finite.of_finite_image (f := fun c : T.Coord => c.slot) ?_ ?_
  · refine Set.Finite.subset (Set.Finite.pi (fun _ : Fin (T.K + 1) =>
      Set.finite_Iio (b + 1 + ∑ r, T.slotBound r))) ?_
    rw [Set.image_subset_iff]
    rintro c ⟨hblk, _hht⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Iio, forall_true_left]
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · calc c.slot j.castSucc < T.slotBound j := c.slot_lt j
        _ ≤ ∑ r, T.slotBound r :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        _ ≤ b + 1 + ∑ r, T.slotBound r := Nat.le_add_left _ _
    · have hb : c.slot (Fin.last T.K) = b := hblk
      rw [hb]
      calc b < b + 1 := Nat.lt_succ_self b
        _ ≤ b + 1 + ∑ r, T.slotBound r := Nat.le_add_right _ _
  · rintro c hc c' hc' hslot
    have hl : c.l = c'.l := by
      have key : T.ht c = T.ht c' := hc.2.trans hc'.2.symm
      simp only [Tower.ht, hslot] at key
      exact_mod_cast add_right_cancel key
    obtain ⟨l1, s1, p1⟩ := c
    obtain ⟨l2, s2, p2⟩ := c'
    dsimp only at hl hslot
    subst hl; subst hslot; rfl

theorem T7_alphabetSpan {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) :
    ((T.alphabet b γ : Set (T.grQ γ)) =
      { x | ∃ (s : Finset ↥(T.levelSet b γ)) (dig : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ),
          x = ∑ c ∈ s, T.typComposite b γ (Pi.single c (dig c)) }) ∧
    Finite ↥(T.alphabet b γ) ∧
    p ^ T.aDim b γ = Nat.card ↥(T.alphabet b γ) := by
  classical
  haveI : Finite ↥(T.levelSet b γ) := (levelSet_finite' T b γ).to_subtype
  -- the span set
  set S : Set (T.grQ γ) :=
    { x | ∃ (s : Finset ↥(T.levelSet b γ)) (dig : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ),
        x = ∑ c ∈ s, T.typComposite b γ (Pi.single c (dig c)) } with hS
  have hzero : (0 : T.grQ γ) ∈ S := ⟨∅, fun _ => 0, (Finset.sum_empty).symm⟩
  have hadd : ∀ x y : T.grQ γ, x ∈ S → y ∈ S → x + y ∈ S := by
    rintro x y ⟨s₁, d₁, rfl⟩ ⟨s₂, d₂, rfl⟩
    have h₁ : ∑ c ∈ s₁, T.typComposite b γ (Pi.single c (d₁ c))
        = ∑ c ∈ s₁ ∪ s₂, T.typComposite b γ
            (Pi.single c (if c ∈ s₁ then d₁ c else 0)) := by
      rw [show (∑ c ∈ s₁, T.typComposite b γ (Pi.single c (d₁ c)))
            = ∑ c ∈ s₁, T.typComposite b γ (Pi.single c (if c ∈ s₁ then d₁ c else 0)) from
        Finset.sum_congr rfl (fun c hc => by rw [if_pos hc])]
      exact Finset.sum_subset Finset.subset_union_left
        (fun c _ hc => by rw [if_neg hc, typ_single_zero])
    have h₂ : ∑ c ∈ s₂, T.typComposite b γ (Pi.single c (d₂ c))
        = ∑ c ∈ s₁ ∪ s₂, T.typComposite b γ
            (Pi.single c (if c ∈ s₂ then d₂ c else 0)) := by
      rw [show (∑ c ∈ s₂, T.typComposite b γ (Pi.single c (d₂ c)))
            = ∑ c ∈ s₂, T.typComposite b γ (Pi.single c (if c ∈ s₂ then d₂ c else 0)) from
        Finset.sum_congr rfl (fun c hc => by rw [if_pos hc])]
      exact Finset.sum_subset Finset.subset_union_right
        (fun c _ hc => by rw [if_neg hc, typ_single_zero])
    choose d₃ hd₃ using fun c : ↥(T.levelSet b γ) =>
      line_closed T b γ c (if c ∈ s₁ then d₁ c else 0) (if c ∈ s₂ then d₂ c else 0)
    refine ⟨s₁ ∪ s₂, d₃, ?_⟩
    rw [h₁, h₂, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ => hd₃ c)
  have hneg : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have hsmul : ∀ n : ℕ, n • x ∈ S := by
      intro n
      induction n with
      | zero => rw [zero_smul]; exact hzero
      | succ k ih => rw [succ_nsmul]; exact hadd _ _ ih hx
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    have hkey : (p - 1) • x = -x := by
      have hpx : (p - 1) • x + x = 0 := by
        rw [← succ_nsmul, Nat.sub_add_cancel hp1]
        exact grQ_torsion T γ x
      exact eq_neg_of_add_eq_zero_left hpx
    rw [← hkey]
    exact hsmul _
  -- the span subgroup
  let S' : AddSubgroup (T.grQ γ) :=
    { carrier := S
      add_mem' := fun hx hy => hadd _ _ hx hy
      zero_mem' := hzero
      neg_mem' := fun hx => hneg _ hx }
  -- conjunct 1: the alphabet IS the span set
  have hset : (T.alphabet b γ : Set (T.grQ γ)) = S := by
    apply Set.eq_of_subset_of_subset
    · have hle : T.alphabet b γ ≤ S' := by
        rw [Tower.alphabet]
        refine (AddSubgroup.closure_le S').mpr ?_
        rintro z hz
        simp only [Set.mem_iUnion, Set.mem_range] at hz
        obtain ⟨c, v, rfl⟩ := hz
        exact ⟨{c}, fun _ => v, (Finset.sum_singleton _ _).symm⟩
      exact fun x hx => hle hx
    · rintro x ⟨s, dig, rfl⟩
      exact AddSubgroup.sum_mem _ (fun c _ => AddSubgroup.subset_closure
        (Set.mem_iUnion.mpr ⟨c, Set.mem_range.mpr ⟨dig c, rfl⟩⟩))
  -- conjunct 2: finiteness
  have hSfin : S.Finite := by
    apply Set.Finite.subset (Set.finite_range
      (fun q : Finset ↥(T.levelSet b γ) × (↥(T.levelSet b γ) → ↥(T.stg 0).FQ) =>
        ∑ c ∈ q.1, T.typComposite b γ (Pi.single c (q.2 c))))
    rintro x ⟨s, dig, rfl⟩
    exact ⟨(s, dig), rfl⟩
  have hAfin : (T.alphabet b γ : Set (T.grQ γ)).Finite := hset ▸ hSfin
  haveI hfinA : Finite ↥(T.alphabet b γ) := hAfin.to_subtype
  -- conjunct 3: p-power cardinality via IsPGroup on the multiplicative shadow
  have hcard : ∃ n : ℕ, Nat.card ↥(T.alphabet b γ) = p ^ n := by
    haveI : Finite (Multiplicative ↥(T.alphabet b γ)) :=
      Finite.of_equiv _ Multiplicative.ofAdd
    have hPG : IsPGroup p (Multiplicative ↥(T.alphabet b γ)) := by
      intro g
      refine ⟨1, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, pow_one]
      have hval : ((p • g.toAdd : ↥(T.alphabet b γ)) : T.grQ γ)
          = ((0 : ↥(T.alphabet b γ)) : T.grQ γ) := by
        show (T.alphabet b γ).subtype (p • g.toAdd) = (T.alphabet b γ).subtype 0
        rw [map_nsmul, map_zero]
        exact grQ_torsion T γ _
      exact Subtype.ext hval
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPG
    refine ⟨n, ?_⟩
    rwa [Nat.card_congr Multiplicative.toAdd] at hn
  obtain ⟨n, hn⟩ := hcard
  have haDim : T.aDim b γ = n := by
    rw [Tower.aDim, hn, Nat.log_pow (Fact.out : p.Prime).one_lt]
  exact ⟨hset, hfinA, by rw [haDim, ← hn]⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T7_alphabetSpan
