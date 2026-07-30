/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.S2_childW
import LeanUrat.Moves.L4_TRANSi_R3
import LeanUrat.Moves.L4_TRANSiii_R3
import LeanUrat.Moves.L0_FactA_exists

/-!
# HC1.V1_readWPack — the read functional's laws at the same key (blueprint §10, V1)

V′-KERNEL unit (blueprint §10.1): for σ cored, under `ReadPair` hypotheses, the
read functional `childW σ σ.Φ e★ h★` has the slot-min/attained-min pack (the S2
instance at Φhat := σ.Φ — the signature admits it verbatim), hwmul, hwult, and
the **Q-ASCENT** lemma: for parent coefficients with monic division
`B·B″ = Q·σ.Φ + R_dev`, the Q-slot's (†)-value exceeds the R_dev-slot's by
`h★ − e★·σ.h > 0` (ReadPair's steepness).

moves_ref: D.7(i) (MOVES 2331–2337) at the same-key instance; D.4.
deps: S2_childW, σ's hRmul/hwmul/hwult/hK1. difficulty: medium.
P-phase PROVED (2026-07-28): slot-min pack = S2 verbatim; hwult from slotwise
development linearity + σ.hwult; hwmul via the lift-free cores `TRANSi_ge_core` /
`TRANSiii_le_core` (extracted from L4_TRANSi/iii) fed the SAME-KEY DIV lemma
`sameKeyDIV`; Q-ascent = `sameKeyDIV` (key minimality via `R(σ.Φ)=z^s` a unit +
σ.e ∣ σ.h ⇒ σ.e=1 ⇒ σ.t=0 ⇒ residual-exponent clash) + σ.hK1 slot-1 bound.
Footprint: Lean core `{propext, Classical.choice, Quot.sound}`; zero `sorry`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

section V1Helpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Two `C·T` monomials with a nonzero leading scalar are equal only at equal exponents. -/
private lemma monomial_exp_eq {K : Type*} [Field K] {a b : K} {k1 k2 : ℤ} (ha : a ≠ 0)
    (h : LaurentPolynomial.C a * LaurentPolynomial.T k1
        = LaurentPolynomial.C b * LaurentPolynomial.T k2) : k1 = k2 := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at h
  have h' : (Finsupp.single k1 a : ℤ →₀ K) = Finsupp.single k2 b := h
  by_contra hne
  have hc := DFunLike.congr_fun h' k1
  rw [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl, if_neg (fun hk => hne hk.symm)] at hc
  exact ha hc

/-- **The SAME-KEY DIV lemma** (V1's Q-ascent core, the D.6 argument at `Φ̂ = σ.Φ`): for
`B, B'' ∈ C_{σ.Φ}∖0` with monic division `B·B'' = (B·B'')%ₘσ.Φ + σ.Φ·((B·B'')/ₘσ.Φ)`, the
remainder is nonzero with weight exactly `σ.w B + σ.w B''`, and the quotient slot lies weakly
above it by `σ.h`.  Ruling out the cancellation branch uses only `R(σ.Φ) = z^s` being a UNIT
(no descend-polynomial root): a `w`-jump forces `σ.e ∣ σ.h`, hence `σ.e = 1`, `σ.t = 0`,
`σ.s = 1`, contradicting the residual exponent match. -/
private lemma sameKeyDIV (σ : Stage p F) (B B'' : Polynomial ℤ_[p])
    (hB : B ≠ 0) (hB'' : B'' ≠ 0) (hBc : inC σ.Φ B) (hB''c : inC σ.Φ B'') :
    (((B * B'') %ₘ σ.Φ) ≠ 0 ∧ σ.w ((B * B'') %ₘ σ.Φ) = σ.w B + σ.w B'') ∧
      (((B * B'') /ₘ σ.Φ) ≠ 0 →
        σ.w ((B * B'') %ₘ σ.Φ) ≤ σ.w ((B * B'') /ₘ σ.Φ) + (σ.h : ℤ)) := by
  classical
  set Rdev := (B * B'') %ₘ σ.Φ with hRdevdef
  set Q := (B * B'') /ₘ σ.Φ with hQdef
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hBBne : B * B'' ≠ 0 := mul_ne_zero hB hB''
  have hsplit : B * B'' = Rdev + σ.Φ * Q := (Polynomial.modByMonic_add_div (B * B'') σ.Φ).symm
  have hwBB : σ.w (B * B'') = σ.w B + σ.w B'' := σ.hwmul B B'' hB hB''
  -- Rdev ∈ C
  have hRc : Rdev.degree < σ.Φ.degree := Polynomial.degree_modByMonic_lt _ σ.hmonic
  -- Q ∈ C (degree bookkeeping: deg(B·B'') < 2·deg σ.Φ)
  have hBBnat : (B * B'').natDegree < 2 * σ.Φ.natDegree := by
    rw [Polynomial.natDegree_mul hB hB'']
    have h1 : B.natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree hB hBc
    have h2 : B''.natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree hB'' hB''c
    omega
  have hQnat : Q.natDegree < σ.Φ.natDegree := by
    rw [hQdef, Polynomial.natDegree_divByMonic (B * B'') σ.hmonic]
    have := σ.hdeg; omega
  have hQc : Q.degree < σ.Φ.degree := by
    by_cases hQ0 : Q = 0
    · rw [hQ0, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (fun hb => hΦne (Polynomial.degree_eq_bot.mp hb))
    · rw [Polynomial.degree_eq_natDegree hQ0, Polynomial.degree_eq_natDegree hΦne]
      exact_mod_cast hQnat
  -- the 2-slot Φ-development and Lemma K1
  set Bseq : ℕ → Polynomial ℤ_[p] := fun j => if j = 0 then Rdev else if j = 1 then Q else 0
    with hBseqdef
  have hB0 : Bseq 0 = Rdev := by simp [hBseqdef]
  have hB1 : Bseq 1 = Q := by simp [hBseqdef]
  have hBj2 : ∀ j, 2 ≤ j → Bseq j = 0 := by
    intro j hj
    have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by omega
    simp only [hBseqdef, if_neg hj0, if_neg hj1]
  have hdev : IsDevelopment σ.Φ (B * B'') Bseq 2 := by
    refine ⟨?_, hBj2, ?_⟩
    · intro j
      by_cases hj0 : j = 0
      · rw [hj0, hB0]; exact hRc
      · by_cases hj1 : j = 1
        · rw [hj1, hB1]; exact hQc
        · rw [hBj2 j (by omega), Polynomial.degree_zero]
          exact bot_lt_iff_ne_bot.mpr (fun hb => hΦne (Polynomial.degree_eq_bot.mp hb))
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, hB0, hB1,
        pow_zero, pow_one, mul_one, zero_add, hsplit, mul_comm σ.Φ Q]
  have hK1 := σ.hK1 (B * B'') Bseq 2 hBBne hdev
  rw [σ.hwΦ] at hK1
  have hK1lb : ∀ j, j < 2 → Bseq j ≠ 0 →
      σ.w (B * B'') ≤ σ.w (Bseq j) + (j : ℤ) * (σ.h : ℤ) := hK1.1
  -- the residual-cancellation absurdity used to rule out a w-jump
  have hAbsurd : Q ≠ 0 → σ.R (B * B'') = σ.R (Q * σ.Φ) →
      σ.w B + σ.w B'' = σ.w Q + (σ.h : ℤ) → False := by
    intro hQne hReq hweq
    have hsB := σ.hStretch B hB hBc
    have hsB'' := σ.hStretch B'' hB'' hB''c
    have hsQ := σ.hStretch Q hQne hQc
    have hEq : (σ.h : ℤ) = (σ.e : ℤ) * (σ.wPrev B + σ.wPrev B'' - σ.wPrev Q) := by
      have hw := hweq
      rw [hsB, hsB'', hsQ] at hw
      linear_combination -hw
    have hdvd : (σ.e : ℤ) ∣ (σ.h : ℤ) := ⟨σ.wPrev B + σ.wPrev B'' - σ.wPrev Q, hEq⟩
    have hediv : σ.e ∣ σ.h := Int.natCast_dvd_natCast.mp hdvd
    have he1 : σ.e = 1 := (Nat.gcd_eq_left hediv).symm.trans σ.hcop
    have ht0 : σ.t = 0 := σ.he1t he1
    have hs1 : σ.s = 1 := by
      have hb := σ.hbez
      rw [show (σ.e : ℤ) = 1 by exact_mod_cast he1, ht0] at hb
      linarith [hb]
    obtain ⟨cB, hcB⟩ := σ.hS5 B hB hBc
    obtain ⟨cB'', hcB''⟩ := σ.hS5 B'' hB'' hB''c
    obtain ⟨cQ, hcQ⟩ := σ.hS5 Q hQne hQc
    have hForm1 : σ.R (B * B'')
        = LaurentPolynomial.C (((cB * cB'' : (↥σ.K)ˣ)) : ↥σ.K)
          * LaurentPolynomial.T ((- σ.t * σ.wPrev B) + (- σ.t * σ.wPrev B'')) := by
      rw [σ.hRmul B B'' hB hB'', hcB, hcB'', Units.val_mul, map_mul, LaurentPolynomial.T_add]
      ring
    have hForm2 : σ.R (Q * σ.Φ)
        = LaurentPolynomial.C ((cQ : ↥σ.K))
          * LaurentPolynomial.T ((- σ.t * σ.wPrev Q) + σ.s) := by
      rw [σ.hRmul Q σ.Φ hQne hΦne, hcQ, σ.hRΦ, LaurentPolynomial.T_add]
      ring
    have hMon : LaurentPolynomial.C (((cB * cB'' : (↥σ.K)ˣ)) : ↥σ.K)
          * LaurentPolynomial.T ((- σ.t * σ.wPrev B) + (- σ.t * σ.wPrev B''))
        = LaurentPolynomial.C ((cQ : ↥σ.K))
          * LaurentPolynomial.T ((- σ.t * σ.wPrev Q) + σ.s) := by
      rw [← hForm1, hReq, hForm2]
    have hexp := monomial_exp_eq (Units.ne_zero (cB * cB'')) hMon
    rw [ht0, hs1] at hexp
    simp only [neg_zero, zero_mul, add_zero, zero_add] at hexp
    exact zero_ne_one hexp
  -- Rdev ≠ 0
  have hRdevne : Rdev ≠ 0 := by
    intro h0
    have hBBQ : B * B'' = σ.Φ * Q := by rw [hsplit, h0, zero_add]
    have hQne : Q ≠ 0 := by
      intro hq; rw [hBBQ, hq, mul_zero] at hBBne; exact hBBne rfl
    have hReq : σ.R (B * B'') = σ.R (Q * σ.Φ) := by rw [hBBQ, mul_comm σ.Φ Q]
    have hweq : σ.w B + σ.w B'' = σ.w Q + (σ.h : ℤ) := by
      rw [← hwBB, hBBQ, σ.hwmul σ.Φ Q hΦne hQne, σ.hwΦ]; ring
    exact hAbsurd hQne hReq hweq
  -- σ.w Rdev = σ.w (B·B'')  (slot 0 is the minimizer)
  have hle : σ.w (B * B'') ≤ σ.w Rdev := by
    have hh := hK1lb 0 (by omega) (by rw [hB0]; exact hRdevne)
    simpa [hB0] using hh
  have hge : σ.w Rdev ≤ σ.w (B * B'') := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨jm, hjmlt, hjmnz0, hjmeq0⟩ := hK1.2
    have hjmnz : Bseq jm ≠ 0 := hjmnz0
    have hjmeq : σ.w (B * B'') = σ.w (Bseq jm) + (jm : ℤ) * (σ.h : ℤ) := hjmeq0
    have hjm1 : jm = 1 := by
      rcases (by omega : jm = 0 ∨ jm = 1) with h | h
      · exfalso
        rw [h, hB0] at hjmeq
        simp only [Nat.cast_zero, zero_mul, add_zero] at hjmeq
        rw [hjmeq] at hlt; exact lt_irrefl _ hlt
      · exact h
    rw [hjm1, hB1] at hjmnz hjmeq
    have hQne : Q ≠ 0 := hjmnz
    have hjmeq' : σ.w (B * B'') = σ.w Q + (σ.h : ℤ) := by rw [hjmeq]; push_cast; ring
    have hwQΦ : σ.w (σ.Φ * Q) = σ.w Q + (σ.h : ℤ) := by
      rw [σ.hwmul σ.Φ Q hΦne hQne, σ.hwΦ]; ring
    have hltΦ : σ.w (σ.Φ * Q) < σ.w Rdev := by rw [hwQΦ, ← hjmeq']; exact hlt
    have hReq : σ.R (B * B'') = σ.R (Q * σ.Φ) := by
      rw [hsplit, add_comm Rdev (σ.Φ * Q),
        σ.hRlt (σ.Φ * Q) Rdev (mul_ne_zero hΦne hQne) hRdevne
          (by rw [add_comm (σ.Φ * Q) Rdev, ← hsplit]; exact hBBne) hltΦ, mul_comm σ.Φ Q]
    have hweq : σ.w B + σ.w B'' = σ.w Q + (σ.h : ℤ) := by rw [← hwBB]; exact hjmeq'
    exact hAbsurd hQne hReq hweq
  have hwRdev : σ.w Rdev = σ.w B + σ.w B'' := by rw [le_antisymm hge hle, hwBB]
  refine ⟨⟨hRdevne, hwRdev⟩, ?_⟩
  intro hQne
  have hb := hK1lb 1 (by omega) (by rw [hB1]; exact hQne)
  rw [hB1] at hb
  rw [hwRdev, ← hwBB]
  simpa using hb

end V1Helpers

/-- Unit V1: the read functional's laws at the same key — the slot-min pack (S2 at
Φhat := σ.Φ), multiplicativity, the ultrametric law, and Q-ascent with the displayed
gap `h★ − e★·σ.h` (strictly positive by `ReadPair`). -/
theorem V1_readWPack {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar) :
    ((∀ f : Polynomial ℤ_[p], f ≠ 0 →
        ∃ (B : ℕ → Polynomial ℤ_[p]) (N : ℕ), IsDevelopment σ.Φ f B N ∧
          SlotMinAttained (childW σ σ.Φ estar hstar f) N
            (fun j => (estar : ℤ) * σ.w (B j) + (j : ℤ) * (hstar : ℤ))
            (fun j => B j ≠ 0)) ∧
      IsSlotMinWeight (childW σ σ.Φ estar hstar) σ.Φ estar hstar σ.w) ∧
    (∀ f g, f ≠ 0 → g ≠ 0 →
        childW σ σ.Φ estar hstar (f * g)
          = childW σ σ.Φ estar hstar f + childW σ σ.Φ estar hstar g) ∧
    (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
        min (childW σ σ.Φ estar hstar f) (childW σ σ.Φ estar hstar g)
          ≤ childW σ σ.Φ estar hstar (f + g)) ∧
    (∀ B B'' : Polynomial ℤ_[p], B ≠ 0 → B'' ≠ 0 → inC σ.Φ B → inC σ.Φ B'' →
        (((B * B'') %ₘ σ.Φ) ≠ 0 ∧ σ.w ((B * B'') %ₘ σ.Φ) = σ.w B + σ.w B'') ∧
        (((B * B'') /ₘ σ.Φ) ≠ 0 →
          (estar : ℤ) * σ.w ((B * B'') %ₘ σ.Φ)
              + ((hstar : ℤ) - (estar : ℤ) * (σ.h : ℤ))
            ≤ (estar : ℤ) * σ.w ((B * B'') /ₘ σ.Φ) + (hstar : ℤ))) := by
  classical
  -- conjunct 1: the S2 slot-min pack at Φhat := σ.Φ (signature admits it verbatim)
  have hpack := S2_childW σ σ.Φ σ.hmonic σ.hdeg estar hstar
  have hSMW : IsSlotMinWeight (childW σ σ.Φ estar hstar) σ.Φ estar hstar σ.w := hpack.2
  -- (I-aug) at the same key, from ReadPair's steepness `estar·σ.h < hstar`
  have hIAug : IAug σ σ.Φ estar hstar := by
    show (hstar : ℤ) > (estar : ℤ) * σ.w σ.Φ
    rw [σ.hwΦ]; exact hrp.2.2.2.2.2
  -- the same-key DIV fact in the core's shape
  have hDIVw : ∀ (B B'' : Polynomial ℤ_[p]), B ≠ 0 → B'' ≠ 0 →
      B.degree < σ.Φ.degree → B''.degree < σ.Φ.degree →
      (B * B'') %ₘ σ.Φ ≠ 0 ∧ σ.w ((B * B'') %ₘ σ.Φ) = σ.w B + σ.w B'' :=
    fun B B'' hB hB'' hBd hB''d => (sameKeyDIV σ B B'' hB hB'' hBd hB''d).1
  refine ⟨hpack, ?_, ?_, ?_⟩
  · -- hwmul: multiplicativity of the read functional (same-key MacLane augmentation)
    intro f g hf hg
    exact le_antisymm
      (TRANSiii_le_core σ σ.Φ σ.hmonic σ.hdeg estar hstar (childW σ σ.Φ estar hstar) hSMW hIAug
        hDIVw f g hf hg (mul_ne_zero hf hg))
      (TRANSi_ge_core σ σ.Φ σ.hmonic σ.hdeg estar hstar (childW σ σ.Φ estar hstar) hSMW hIAug
        hDIVw f g hf hg (mul_ne_zero hf hg))
  · -- hwult: the ultrametric law (slotwise linearity of the Φ-development + σ.hwult)
    intro f g hf hg hfg
    obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg f
    obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg g
    have hsub_f : Finset.range Nf ⊆ Finset.range (max Nf Ng) :=
      Finset.range_subset_range.mpr (le_max_left Nf Ng)
    have hsub_g : Finset.range Ng ⊆ Finset.range (max Nf Ng) :=
      Finset.range_subset_range.mpr (le_max_right Nf Ng)
    have hfsum : f = ∑ j ∈ Finset.range (max Nf Ng), Bf j * σ.Φ ^ j :=
      hdevf.2.2.trans (Finset.sum_subset hsub_f
        (fun j _ hj => by rw [hdevf.2.1 j (not_lt.mp (Finset.mem_range.not.mp hj)), zero_mul]))
    have hgsum : g = ∑ j ∈ Finset.range (max Nf Ng), Bg j * σ.Φ ^ j :=
      hdevg.2.2.trans (Finset.sum_subset hsub_g
        (fun j _ hj => by rw [hdevg.2.1 j (not_lt.mp (Finset.mem_range.not.mp hj)), zero_mul]))
    have hdevs : IsDevelopment σ.Φ (f + g) (fun j => Bf j + Bg j) (max Nf Ng) := by
      refine ⟨?_, ?_, ?_⟩
      · intro j
        exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt (hdevf.1 j) (hdevg.1 j))
      · intro j hj
        show Bf j + Bg j = 0
        rw [hdevf.2.1 j (le_trans (le_max_left Nf Ng) hj),
          hdevg.2.1 j (le_trans (le_max_right Nf Ng) hj), add_zero]
      · rw [hfsum, hgsum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    have hsm := hSMW (f + g) (fun j => Bf j + Bg j) (max Nf Ng) hfg hdevs
    have hlbf := (hSMW f Bf Nf hf hdevf).1
    have hlbg := (hSMW g Bg Ng hg hdevg).1
    obtain ⟨-, jm, hjmN, hjmnz0, hjmeq0⟩ := hsm
    have hjmnz : Bf jm + Bg jm ≠ 0 := hjmnz0
    have hjmeq : childW σ σ.Φ estar hstar (f + g)
        = (estar : ℤ) * σ.w (Bf jm + Bg jm) + (jm : ℤ) * (hstar : ℤ) := hjmeq0
    rw [hjmeq]
    have hestar : (0 : ℤ) ≤ (estar : ℤ) := Int.natCast_nonneg estar
    by_cases hbf : Bf jm = 0
    · have hbg : Bg jm ≠ 0 := fun h => hjmnz (by rw [hbf, h, add_zero])
      have hjmg : jm < Ng := by by_contra hc; exact hbg (hdevg.2.1 jm (not_lt.mp hc))
      have hgle := hlbg jm hjmg hbg
      rw [hbf, zero_add]
      exact le_trans (min_le_right _ _) hgle
    · by_cases hbg : Bg jm = 0
      · have hjmf : jm < Nf := by by_contra hc; exact hbf (hdevf.2.1 jm (not_lt.mp hc))
        have hfle := hlbf jm hjmf hbf
        rw [hbg, add_zero]
        exact le_trans (min_le_left _ _) hfle
      · have hjmf : jm < Nf := by by_contra hc; exact hbf (hdevf.2.1 jm (not_lt.mp hc))
        have hjmg : jm < Ng := by by_contra hc; exact hbg (hdevg.2.1 jm (not_lt.mp hc))
        have h1 := hlbf jm hjmf hbf
        have h2 := hlbg jm hjmg hbg
        have hult := σ.hwult (Bf jm) (Bg jm) hbf hbg hjmnz
        rcases le_total (σ.w (Bf jm)) (σ.w (Bg jm)) with hle | hle
        · have hw : σ.w (Bf jm) ≤ σ.w (Bf jm + Bg jm) := by
            rw [min_eq_left hle] at hult; exact hult
          have hmul := mul_le_mul_of_nonneg_left hw hestar
          calc min (childW σ σ.Φ estar hstar f) (childW σ σ.Φ estar hstar g)
                ≤ childW σ σ.Φ estar hstar f := min_le_left _ _
            _ ≤ (estar : ℤ) * σ.w (Bf jm) + (jm : ℤ) * (hstar : ℤ) := h1
            _ ≤ (estar : ℤ) * σ.w (Bf jm + Bg jm) + (jm : ℤ) * (hstar : ℤ) := by linarith
        · have hw : σ.w (Bg jm) ≤ σ.w (Bf jm + Bg jm) := by
            rw [min_eq_right hle] at hult; exact hult
          have hmul := mul_le_mul_of_nonneg_left hw hestar
          calc min (childW σ σ.Φ estar hstar f) (childW σ σ.Φ estar hstar g)
                ≤ childW σ σ.Φ estar hstar g := min_le_right _ _
            _ ≤ (estar : ℤ) * σ.w (Bg jm) + (jm : ℤ) * (hstar : ℤ) := h2
            _ ≤ (estar : ℤ) * σ.w (Bf jm + Bg jm) + (jm : ℤ) * (hstar : ℤ) := by linarith
  · -- Q-ascent: part (i) is the DIV fact; part (ii) is its slot-1 bound, scaled by estar
    intro B B'' hB hB'' hBc hB''c
    have hd := sameKeyDIV σ B B'' hB hB'' hBc hB''c
    refine ⟨hd.1, ?_⟩
    intro hQne
    have hbound := hd.2 hQne
    have hmul := mul_le_mul_of_nonneg_left hbound (Int.natCast_nonneg estar)
    rw [mul_add] at hmul
    linarith [hmul]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V1_readWPack
