/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.T3_htChainWeight
import LeanUrat.HC1.T6_carrierLaws
import LeanUrat.HC1.T7_alphabetSpan
import LeanUrat.Moves.L3_liftMonic

/-!
# HC1.ScratchC6 — machine certificate: C6's conjunct-2/3 attainability condition is
AUTOMATIC on the level set (the D-10 typing quantifies over the wrong index set)

**Finding (C6 specialist walk, 2026-07-28).** C6_alphabetCard's conjuncts 2–3 type the
note's "every height in γ's slot tree is attainable" PER LEVEL-SET COORDINATE
(blueprint Deviation D-10). But with T3 (`w_top(mono c) = strTop·ht c`) and T7's digit
apparatus both now proved, membership in the level set ALREADY forces attainability:
for `c ∈ levelSet b γ` and ANY digit `y ≠ 0`,

  (0)   w_top(digLift y · mono c) = 0 + strTop·γ   (exactly the piece index),

so the class is nonzero by weight-detection. Certificates below:

* `C6_attain_automatic` — every level-set slot is attainable at every nonzero digit;
* `C6_conjunct2_rhs_always` — conjunct 2's RHS is a theorem (no hypothesis);
* `C6_conjunct3_hyp_false` — conjunct 3's hypothesis is refutable (conjunct 3 is
  vacuously provable);
* `C6_forces_unconditional_fullness` — hence C6's conjunct 2, as fenced, is
  EQUIVALENT to the unconditional fullness claim
  `Nat.card 𝔸(b,γ) = Nat.card F_{K+1}` on every nonempty level set — precisely the
  pre-D¹¹c uniform display that CODEX_CONFIRM_D11B refuted at shallow heights
  (MOVES 2160–2165's own correction: "STRICTLY SMALLER at shallow heights").

Shallow-height instance (math-level, S1's gate data): base (e₀,h₀) = (1,1), K₀ = F₂
inside F = F₄, one g = 2 increment (ψ = z²+z+1, z̄ a cube root of unity). At
(b,γ) = (0,0) the level set is the single coordinate l = 0, slots ≡ 0 (κ₀ = 1 > 0,
κ₁ > 0 kill every other address), so 𝔸 is one base-digit line: card ≤ |F₂| = 2,
while |F_{K+1}| = |F₄| = 4. Conjunct 2's RHS holds (this file), its LHS fails. The
missing addresses (the note's unattainable slot-tree heights) would need l < 0 — they
are NOT coordinates, so the per-coordinate ∀ cannot see them.

Consequence: C6 as fenced is not provable (and is falsified by any tower with
residual growth); the honest residue is a STATEMENT-FENCE sign-off item, not a
missing bridge. The correct typing of the note's condition quantifies over ALL
bounded slot vectors in γ's alignment class (existence of the coordinate, i.e.
`0 ≤ γ − Σ_r s_r·κ_r`, is then the attainability condition), not over the level set.

The private lemmas below are verbatim copies of T7_alphabetSpan's private toolkit
(stretch chain, digLift facts, slot_eval, inGr helpers) — statements untouched.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## The stretch chain (T7's private toolkit, copied verbatim) -/

private lemma strAux_succ (T : Tower p F) (k : ℕ) (hk : k < T.K + 1) :
    T.strAux (k + 1) = T.strAux k * (T.stg ⟨k, hk⟩).e := by
  have h : T.strAux (k + 1)
      = T.strAux k * (if h : k < T.K + 1 then (T.stg ⟨k, h⟩).e else 1) := rfl
  rw [h, dif_pos hk]

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

/-- **The top-weight formula** on base-cone coefficients (T7's private lemma). -/
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
    rw [show T.strAux 0 = (1 : ℕ) from rfl, one_mul] at h
    exact h
  rw [hw0, hstrAux1] at h0
  have he0 : (0 : ℤ) < ((T.stg ⟨0, h0lt⟩).e : ℤ) := by
    have := (T.stg ⟨0, h0lt⟩).he; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have h0' : ((T.stg ⟨0, h0lt⟩).e : ℤ) * (T.stg ⟨T.K, Nat.lt_succ_self T.K⟩).w B
      = ((T.stg ⟨0, h0lt⟩).e : ℤ) * ((T.strAux (T.K + 1) : ℤ) * gaussVal B) := by
    rw [h0]; ring
  have hX := mul_left_cancel₀ (ne_of_gt he0) h0'
  rw [strTop_eq T]
  exact hX

private lemma deg_one_lt (σ : Stage p F) : (1 : Polynomial ℤ_[p]).degree < σ.Φ.degree := by
  rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree σ.hmonic.ne_zero]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one σ.hdeg

/-! ## inGr helpers (T7's private quotient toolkit, copied) -/

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

/-- `side.w` reads the TOP stage's valuation on nonzeros (T6's `HasSide`). -/
private lemma sideW (T : Tower p F) {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    T.side.w f = (((T.stg (Fin.last T.K)).w f : ℤ) : WithTop ℤ) :=
  T.side_w (T6_carrierLaws T).1 hf

/-! ## digLift facts and the single-slot evaluation (T7's private toolkit, copied) -/

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

/-- The single-coordinate composite is the class of `digLift y · mono c` (T7's copy). -/
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

/-! ## NEW: the basis monomial never vanishes -/

private lemma mono_ne (T : Tower p F) (c : T.Coord) : T.mono c ≠ 0 := by
  rw [Tower.mono]
  refine mul_ne_zero ?_ ?_
  · rw [Ne, Polynomial.C_eq_zero]
    exact pow_ne_zero _ PadicInt.prime_p.ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun r _ => pow_ne_zero _ (T.stg r).hmonic.ne_zero)

/-! ## THE CERTIFICATES -/

/-- **Attainability is automatic on the level set**: for every coordinate `c` OF the
level set and EVERY nonzero digit `y`, the slot value is nonzero — display (0):
`w_top(digLift y · mono c) = 0 + strTop·ht c = strTop·γ`, exactly the piece index,
so the class is weight-detected nonzero. Consumes T3 (proved) + T6 (proved) + T7's
digit toolkit (proved). -/
theorem C6_attain_automatic (T : Tower p F) (b : ℕ) (γ : ℚ) (c : ↥(T.levelSet b γ))
    (y : ↥(T.stg 0).FQ) (hy : y ≠ 0) :
    T.typComposite b γ (Pi.single c y) ≠ 0 := by
  have hμne : T.mono ↑c ≠ 0 := mono_ne T ↑c
  have hf : T.digLift y ≠ 0 := digLift_ne T hy
  obtain ⟨-, hC, hwP, -⟩ := digLift_spec T hf
  have hgv : gaussVal (T.digLift y) = 0 := by rw [← T.base.1.1 _ hf]; exact hwP
  have hwK : (T.stg (Fin.last T.K)).w (T.digLift y) = 0 := by
    rw [wTop_cone T _ hf hC, hgv, mul_zero]
  -- T3: the monomial reads at exactly strTop·γ
  have hht : T.ht ↑c = γ := c.2.2
  have hT3 := T3_htChainWeight T ↑c hμne
  rw [hht] at hT3
  -- the lattice pin and the floor value
  have honL : T.onLattice γ := by
    rw [Tower.onLattice, ← hT3, Int.floor_intCast]
  have hfl : ⌊(T.strTop : ℚ) * γ⌋ = (T.stg (Fin.last T.K)).w (T.mono ↑c) := by
    rw [← hT3, Int.floor_intCast]
  -- exact weight of the product
  have hprodne : T.digLift y * T.mono ↑c ≠ 0 := mul_ne_zero hf hμne
  have hwprod : (T.stg (Fin.last T.K)).w (T.digLift y * T.mono ↑c)
      = (T.stg (Fin.last T.K)).w (T.mono ↑c) := by
    rw [(T.stg (Fin.last T.K)).hwmul _ _ hf hμne, hwK, zero_add]
  have hside : T.side.w (T.digLift y * T.mono ↑c)
      = (((T.stg (Fin.last T.K)).w (T.mono ↑c) : ℤ) : WithTop ℤ) := by
    rw [sideW T hprodne, hwprod]
  have hcond : ((⌊(T.strTop : ℚ) * γ⌋ : ℤ) : WithTop ℤ)
      ≤ T.side.w (T.digLift y * T.mono ↑c) := by
    rw [hside, hfl]
  rw [slot_eval, inGr_on T honL _ hcond]
  intro h0
  have hlt := (mk_eq_zero_iff T _ _ hcond).mp h0
  rw [hside, hfl] at hlt
  exact lt_irrefl _ hlt

/-- **Conjunct 2's RHS is a theorem** — the fenced iff's right side holds for every
tower, block, and height, with no hypothesis (take `y = 1`). -/
theorem C6_conjunct2_rhs_always (T : Tower p F) (b : ℕ) (γ : ℚ) :
    ∀ c : ↥(T.levelSet b γ), ∃ y : ↥(T.stg 0).FQ,
      T.typComposite b γ (Pi.single c y) ≠ 0 :=
  fun c => ⟨1, C6_attain_automatic T b γ c 1 one_ne_zero⟩

/-- **Conjunct 3 is vacuous** — its hypothesis (an unattainable level-set slot) is
refutable outright. -/
theorem C6_conjunct3_hyp_false (T : Tower p F) (b : ℕ) (γ : ℚ) :
    ¬ ∃ c : ↥(T.levelSet b γ), ∀ y : ↥(T.stg 0).FQ,
        T.typComposite b γ (Pi.single c y) = 0 :=
  fun ⟨c, hall⟩ => C6_attain_automatic T b γ c 1 one_ne_zero (hall 1)

/-- **The collapse**: C6's conclusion, as fenced, FORCES the unconditional fullness
claim `card 𝔸(b,γ) = card F_{K+1}` on every level set — exactly the pre-D¹¹c uniform
display refuted at shallow heights (CODEX_CONFIRM_D11B; MOVES 2160–2165). So C6 is
provable only if that refuted claim holds for every tower. -/
theorem C6_forces_unconditional_fullness (T : Tower p F) (b : ℕ) (γ : ℚ)
    (hC6 : Nat.card ↥(T.alphabet b γ) = p ^ T.aDim b γ ∧
      (Nat.card ↥(T.alphabet b γ) = Nat.card ↥(T.stg (Fin.last T.K)).K ↔
        ∀ c : ↥(T.levelSet b γ), ∃ y : ↥(T.stg 0).FQ,
          T.typComposite b γ (Pi.single c y) ≠ 0) ∧
      ((∃ c : ↥(T.levelSet b γ), ∀ y : ↥(T.stg 0).FQ,
          T.typComposite b γ (Pi.single c y) = 0) →
        T.aDim b γ < Nat.log p (Nat.card ↥(T.stg (Fin.last T.K)).K))) :
    Nat.card ↥(T.alphabet b γ) = Nat.card ↥(T.stg (Fin.last T.K)).K :=
  hC6.2.1.mpr (C6_conjunct2_rhs_always T b γ)

/-- Conjunct 1 alone IS closable (T7). -/
theorem C6_conjunct1_closable (T : Tower p F) (b : ℕ) (γ : ℚ) :
    Nat.card ↥(T.alphabet b γ) = p ^ T.aDim b γ :=
  ((T7_alphabetSpan T b γ).2.2).symm

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C6_attain_automatic
#print axioms LeanUrat.HC1.C6_conjunct2_rhs_always
#print axioms LeanUrat.HC1.C6_conjunct3_hyp_false
#print axioms LeanUrat.HC1.C6_forces_unconditional_fullness
#print axioms LeanUrat.HC1.C6_conjunct1_closable
