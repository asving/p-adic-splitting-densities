/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.Moves.L2_strideRule
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L4_TRANSviii_b_R4

/-!
# HC1.V7_stripDischarge — S9a's (S6a′) obligation closes (blueprint §10, V7)

V′-KERNEL unit (blueprint §10.1), the (S6a′) coset discharge over an arbitrary lawful
child carrier `D : ChildResData` — for every child weight `ν ∈ 𝒜′` there is ONE coset
base `b(ν)` whose `F_Qˣ`-coset is realized in `D.Rc` at the forced position `−t′·ν`.

**AXIOM-CLEAN PROOF, pure-σ (no dependency on the sorry-backed V6/S9_transStage).**
Because `D.hS5'` pins `D.Rc B`'s scalar's F-image to the PARENT quantity
`σ.digPrime zbar B`, the whole obligation reduces to the parent digit set at weight `ν`:

* ABOVE THRESHOLD (`σ.w Φhat < ν`): base `b := 1`, digit surjectivity from the proved
  pure-σ `Moves.L4_TRANSviii_b` (any target digit `a ∈ K⟮z̄⟯` at any `ν` above the key
  weight), exactly S9a's in-file `hS6b'` pattern.
* BELOW THRESHOLD (the strip `ν ≤ σ.w Φ̂`): the single-slot realizer `B := C·Φ^j` with
  `C` a parent (S6a) coset realizer (`σ.hS6a`) at the parent-scale weight `w̃`, `j` the
  attaining slot of a Φ-adic development of a `childWeightSet` witness. The parent orbit
  scalar enters LINEARLY through `L2_strideRule` + `eval₂_C_mul_T`, giving digit
  `(c·b̃)·z̄^m`; the coset base `b(ν) := b̃·z̄^m` (parent base × a fixed z̄-monomial),
  c-independent. This is `L4_TRANSviii_a`'s conjunct-2 argument transcribed to the
  `digPrime`/`hS5'` coordinate — no child stage σ′ required.

This unit's statement is EXACTLY the hS6a′ obligation shape of S9a's literal (over any
lawful carrier — S9a applies it at its S9w carrier `hexD.choose`).
UNBLOCKS: S9a → S9b → S9c/S9d → S9.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Stage-valuation of a single-slot element: `w(C·Φ^j) = w C + j·w Φ = w C + j·h`.
(Local copy of the `L4_TRANSviii_a` private helper.) -/
private lemma v7_w_mul_keyPow {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (C : Polynomial ℤ_[p]) (hC : C ≠ 0) (j : ℕ) :
    σ.w (C * σ.Φ ^ j) = σ.w C + (j : ℤ) * (σ.h : ℤ) := by
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  induction j with
  | zero => simp
  | succ n ih =>
    have hΦn : σ.Φ ^ n ≠ 0 := pow_ne_zero n hΦ
    have hrw : C * σ.Φ ^ (n + 1) = (C * σ.Φ ^ n) * σ.Φ := by ring
    rw [hrw, σ.hwmul _ _ (mul_ne_zero hC hΦn) hΦ, ih, σ.hwΦ]
    push_cast; ring

/-- **Bounded Fact A**: for monic `Φ` of degree `≥ 1`, every `f` with `deg f < M·deg Φ`
has a Φ-adic development with slot budget exactly `M`. (Local copy of the
`L4_TRANSviii_a` private helper.) -/
private lemma v7_dev_exists_bounded {R : Type*} [CommRing R] (Φ : Polynomial R) (hΦ : Φ.Monic)
    (hd : 1 ≤ Φ.natDegree) :
    ∀ (M : ℕ) (f : Polynomial R), f.natDegree < M * Φ.natDegree →
      ∃ B : ℕ → Polynomial R, IsDevelopment Φ f B M := by
  have hRnt : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · rw [Subsingleton.elim Φ (0 : Polynomial R)] at hd; simp at hd
    · exact h
  have hΦ0 : Φ ≠ 0 := hΦ.ne_zero
  have hΦbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ0 (Polynomial.degree_eq_bot.mp h))
  intro M
  induction M with
  | zero =>
    intro f hf
    rw [zero_mul] at hf
    exact absurd hf (Nat.not_lt_zero _)
  | succ n IH =>
    intro f hf
    have hdiv : f %ₘ Φ + Φ * (f /ₘ Φ) = f := Polynomial.modByMonic_add_div f Φ
    have hqdev : ∃ B, IsDevelopment Φ (f /ₘ Φ) B n := by
      rcases eq_or_ne (f /ₘ Φ) 0 with hqz | hqz
      · refine ⟨fun _ => 0, ?_, fun j _ => rfl, ?_⟩
        · intro j
          show (0 : Polynomial R).degree < Φ.degree
          rw [Polynomial.degree_zero]; exact hΦbot
        · rw [hqz]; simp
      · apply IH
        have hdvz : ¬ (f.degree < Φ.degree) :=
          fun hlt => hqz ((Polynomial.divByMonic_eq_zero_iff hΦ).mpr hlt)
        have hnd : Φ.natDegree ≤ f.natDegree :=
          Polynomial.natDegree_le_natDegree (not_lt.mp hdvz)
        have hqnd : (f /ₘ Φ).natDegree = f.natDegree - Φ.natDegree :=
          Polynomial.natDegree_divByMonic f hΦ
        rw [Nat.succ_mul] at hf
        omega
    obtain ⟨B', hB'deg, hB'zero, hB'sum⟩ := hqdev
    refine ⟨(fun j => match j with | 0 => f %ₘ Φ | k + 1 => B' k), ?_, ?_, ?_⟩
    · intro j
      cases j with
      | zero =>
        show (f %ₘ Φ).degree < Φ.degree
        exact Polynomial.degree_modByMonic_lt f hΦ
      | succ k =>
        show (B' k).degree < Φ.degree
        exact hB'deg k
    · intro j hj
      cases j with
      | zero => exact absurd hj (by omega)
      | succ k =>
        show B' k = 0
        exact hB'zero k (by omega)
    · symm
      rw [Finset.sum_range_succ']
      show (∑ k ∈ Finset.range n, B' k * Φ ^ (k + 1)) + (f %ₘ Φ) * Φ ^ 0 = f
      rw [pow_zero, mul_one]
      have e1 : (∑ k ∈ Finset.range n, B' k * Φ ^ (k + 1)) = (f /ₘ Φ) * Φ := by
        rw [hB'sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ]; ring
      rw [e1]
      linear_combination hdiv

/-- Unit V7: the full (S6a′) coset discharge — for every child weight ν ∈ 𝒜′ there
is ONE coset base b(ν) whose F_Qˣ-coset is realized in the carrier at the forced
position `−t′·ν`; exactly the `hS6a` field shape of S9a's child Stage literal. -/
theorem V7_stripDischarge {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (ht'0 : e' = 1 → t' = 0)
    (D : ChildResData σ Φhat e' h' zbar s' t') (hD : ChildResLaws D) :
    ∀ ν : ℤ, ν ∈ childWeightSet σ Φhat →
      ∃ b : (↥(σ.nextField zbar))ˣ, ∀ c : (↥(σ.nextField zbar))ˣ,
        ((c : ↥(σ.nextField zbar)) : F) ∈ σ.FQ →
        ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
          D.Rc B = LaurentPolynomial.C
              ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) *
            LaurentPolynomial.T (- t' * ν) := by
  have hΦ : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hd1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
  have hg1 : 1 ≤ g := th.hg
  -- deg Φ̂ = e·g·deg Φ, from the standard-lift shape (proved, `L3_liftMonic`)
  have hΦdeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree :=
    (L3_liftMonic σ ψ g hg1 Φhat th.hlift).2
  -- z̄ a root in the `eval₂` coordinate `L4_TRANSviii_b` expects
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rwa [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
  -- single-slot elements `C·Φ^j`, `j < e·g`, land in `C_Φ̂` (degree bound)
  have hslot : ∀ (C : Polynomial ℤ_[p]) (j : ℕ), C ≠ 0 → inC σ.Φ C → j < σ.e * g →
      inC Φhat (C * σ.Φ ^ j) := by
    intro C j hC hCc hj
    have hΦj : σ.Φ ^ j ≠ 0 := pow_ne_zero j hΦ
    have hB0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC hΦj
    have hCd : C.natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree hC hCc
    have hΦhat0 : Φhat ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at hΦdeg
      have hpos : 0 < σ.e * g * σ.Φ.natDegree := Nat.mul_pos (by omega) (by omega)
      omega
    have hBnd : (C * σ.Φ ^ j).natDegree < Φhat.natDegree := by
      rw [Polynomial.natDegree_mul hC hΦj, Polynomial.natDegree_pow, hΦdeg]
      have h2 : (j + 1) * σ.Φ.natDegree ≤ σ.e * g * σ.Φ.natDegree := by gcongr; omega
      calc C.natDegree + j * σ.Φ.natDegree
          < σ.Φ.natDegree + j * σ.Φ.natDegree := by omega
        _ = (j + 1) * σ.Φ.natDegree := by ring
        _ ≤ σ.e * g * σ.Φ.natDegree := h2
    show (C * σ.Φ ^ j).degree < Φhat.degree
    rw [Polynomial.degree_eq_natDegree hB0, Polynomial.degree_eq_natDegree hΦhat0]
    exact_mod_cast hBnd
  -- transfer a child-field FQ-scalar to a parent-field unit with the same F-image
  have hFQtransfer : ∀ c : (↥(σ.nextField zbar))ˣ, ((c : ↥(σ.nextField zbar)) : F) ∈ σ.FQ →
      ∃ c₁ : (↥σ.K)ˣ, ((c₁ : ↥σ.K) : F) = ((c : ↥(σ.nextField zbar)) : F) ∧
        ((c₁ : ↥σ.K) : F) ∈ σ.FQ := by
    intro c hcFQ
    have hx0 : ((c : ↥(σ.nextField zbar)) : F) ≠ 0 :=
      fun h => (Units.ne_zero c) (ZeroMemClass.coe_eq_zero.mp h)
    have hxK : ((c : ↥(σ.nextField zbar)) : F) ∈ σ.K := σ.hFQ_le hcFQ
    have hc₁0 : (⟨((c : ↥(σ.nextField zbar)) : F), hxK⟩ : ↥σ.K) ≠ 0 := by
      simp [Subtype.ext_iff, hx0]
    exact ⟨Units.mk0 _ hc₁0, rfl, hcFQ⟩
  intro ν hν
  rcases lt_or_ge (σ.w Φhat) ν with hgt | hle
  · -- ABOVE THRESHOLD: base b = 1, digit surjectivity from `L4_TRANSviii_b`
    refine ⟨1, ?_⟩
    intro c hcFQ
    obtain ⟨B, hBc, hdig, hnz⟩ := L4_TRANSviii_b σ hσ.core ψ g th.hdeg th.hmonic th.hirr
      th.hne_z Φhat th.hlift zbar hzbar ν hgt ((c : ↥(σ.nextField zbar)) : F)
      (SetLike.coe_mem _)
    have hane : ((c : ↥(σ.nextField zbar)) : F) ≠ 0 :=
      fun h => (Units.ne_zero c) (ZeroMemClass.coe_eq_zero.mp h)
    obtain ⟨hB0, hBw⟩ := hnz hane
    obtain ⟨c', hc'R, hc'F⟩ := D.hS5' B hB0 hBc
    have hcs : (c' : ↥(σ.nextField zbar)) = ((c * 1 : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) := by
      apply Subtype.ext
      rw [hc'F, hdig]
      simp
    exact ⟨B, hB0, hBc, hBw, by rw [hc'R, hcs, hBw]⟩
  · -- BELOW THRESHOLD (the strip): the single-slot realizer `C·Φ^j`
    obtain ⟨B₀, hB₀0, hB₀c, hB₀w⟩ := hν
    have hBnd : B₀.natDegree < σ.e * g * σ.Φ.natDegree := by
      have h := Polynomial.natDegree_lt_natDegree hB₀0 hB₀c
      rwa [hΦdeg] at h
    obtain ⟨Bd, hdev⟩ := v7_dev_exists_bounded σ.Φ σ.hmonic hd1 (σ.e * g) B₀ hBnd
    obtain ⟨-, j, hjN, hnzj, hmin⟩ := σ.hK1 B₀ Bd (σ.e * g) hB₀0 hdev
    -- the attaining slot's coefficient, its parent-scale weight `w̃`
    have hBdjc : inC σ.Φ (Bd j) := hdev.1 j
    set wt : ℤ := σ.wPrev (Bd j) with hwt
    have hwtWS : wt ∈ σ.weightSet := σ.hWS (Bd j) hnzj hBdjc
    have hγstretch : σ.w (Bd j) = (σ.e : ℤ) * wt := σ.hStretch (Bd j) hnzj hBdjc
    -- ν = w(Bd j) + j·h  (from the attained slot-minimum + `hwΦ`)
    have hνdecomp : ν = σ.w (Bd j) + (j : ℤ) * (σ.h : ℤ) := by
      rw [← hB₀w, hmin, σ.hwΦ]
    -- the parent (S6a) coset base `b̃` at `w̃`, c-independent
    obtain ⟨btilde, hbtilde⟩ := σ.hS6a wt hwtWS
    -- the fixed z̄-monomial exponent
    set m : ℤ := - σ.t * wt + σ.s * (j : ℤ) with hm
    -- the child coset base `b := b̃·z̄^m ∈ K⟮z̄⟯`
    have hbtilde_mem : ((btilde : ↥σ.K) : F) ∈ σ.nextField zbar :=
      σ.le_nextField zbar (btilde : ↥σ.K).2
    have hzbar_mem : ((zbar : F)) ∈ σ.nextField zbar :=
      Subfield.subset_closure (Or.inr rfl)
    have hzpow_mem : (((zbar ^ m : Fˣ)) : F) ∈ σ.nextField zbar := by
      rw [Units.val_zpow_eq_zpow_val]
      exact Subfield.zpow_mem _ hzbar_mem m
    have hbval_mem : ((btilde : ↥σ.K) : F) * (((zbar ^ m : Fˣ)) : F) ∈ σ.nextField zbar :=
      Subfield.mul_mem _ hbtilde_mem hzpow_mem
    have hb1 : ((btilde : ↥σ.K) : F) ≠ 0 := by
      rw [Ne, ZeroMemClass.coe_eq_zero]; exact Units.ne_zero btilde
    have hzm1 : (((zbar ^ m : Fˣ)) : F) ≠ 0 := Units.ne_zero _
    have hbval_ne : (⟨((btilde : ↥σ.K) : F) * (((zbar ^ m : Fˣ)) : F), hbval_mem⟩
        : ↥(σ.nextField zbar)) ≠ 0 := by
      rw [Ne, ← ZeroMemClass.coe_eq_zero]
      exact mul_ne_zero hb1 hzm1
    set b : (↥(σ.nextField zbar))ˣ := Units.mk0 _ hbval_ne with hb
    have hbF : ((b : ↥(σ.nextField zbar)) : F)
        = ((btilde : ↥σ.K) : F) * (((zbar ^ m : Fˣ)) : F) := rfl
    refine ⟨b, ?_⟩
    intro c hcFQ
    obtain ⟨c₁, hc₁F, hc₁FQ⟩ := hFQtransfer c hcFQ
    -- the (S6a) coset realizer `C` at `(w̃, c₁)`
    obtain ⟨C, hC0, hCc, hCν, hCR⟩ := hbtilde c₁ hc₁FQ
    have hCw : σ.w C = σ.w (Bd j) := by
      rw [σ.hStretch C hC0 hCc, hCν, hwt, hγstretch]
    -- the single-slot realizer and its (parent) weight
    have hΦj : σ.Φ ^ j ≠ 0 := pow_ne_zero j hΦ
    have hBmul0 : C * σ.Φ ^ j ≠ 0 := mul_ne_zero hC0 hΦj
    have hBmulc : inC Φhat (C * σ.Φ ^ j) := hslot C j hC0 hCc hjN
    have hwB : σ.w (C * σ.Φ ^ j) = ν := by
      rw [v7_w_mul_keyPow σ C hC0 j, hCw, ← hνdecomp]
    -- the parent residual, then the digit: linear in the orbit scalar
    have hRB : σ.R (C * σ.Φ ^ j)
        = LaurentPolynomial.C ((c₁ * btilde : (↥σ.K)ˣ) : ↥σ.K) * LaurentPolynomial.T m := by
      rw [L2_strideRule σ C hC0 hCc j, hCR, mul_assoc, ← LaurentPolynomial.T_add, hm, hwt]
    have hdig : σ.digPrime zbar (C * σ.Φ ^ j)
        = (((c₁ * btilde : (↥σ.K)ˣ) : ↥σ.K) : F) * (((zbar ^ m : Fˣ)) : F) := by
      show LaurentPolynomial.eval₂ σ.K.subtype zbar (σ.R (C * σ.Φ ^ j)) = _
      rw [hRB, LaurentPolynomial.eval₂_C_mul_T]
      rfl
    -- read off `D.Rc` via the S5′ pin and match the scalar to `c·b`
    obtain ⟨c', hc'R, hc'F⟩ := D.hS5' (C * σ.Φ ^ j) hBmul0 hBmulc
    have hscalar : (c' : ↥(σ.nextField zbar))
        = ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) := by
      apply Subtype.ext
      rw [hc'F, hdig]
      show (((c₁ * btilde : (↥σ.K)ˣ) : ↥σ.K) : F) * (((zbar ^ m : Fˣ)) : F)
          = ((c : ↥(σ.nextField zbar)) : F) * ((b : ↥(σ.nextField zbar)) : F)
      rw [hbF, Units.val_mul, MulMemClass.coe_mul, hc₁F, ← mul_assoc]
    refine ⟨C * σ.Φ ^ j, hBmul0, hBmulc, hwB, ?_⟩
    rw [hc'R, hscalar, hwB]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V7_stripDischarge
