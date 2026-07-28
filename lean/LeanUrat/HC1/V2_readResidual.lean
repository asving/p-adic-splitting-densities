/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.V1_readWPack
import LeanUrat.HC1.V6_alignedOrbits
import LeanUrat.HC1.S3_childK1
import LeanUrat.Moves.L3_K1
import LeanUrat.Moves.L4_TRANSii

/-!
# HC1.V2_readResidual — the lawful regrade carrier exists (blueprint §10, V2)

V′-KERNEL unit (blueprint §10.1) — **THE V′ FRAME CHANGE UNIT**: a lawful regrade
carrier exists (+ w_strict, the S9w-(ii) mirror).

Construction (P-phase route, recorded): RV per (†) — scalars from σ.hS5's monomial
digits (parent coefficients only, so every slot digit IS a monomial), positions
`(j − t★·wV f)/e★ = j·s★ − t★·σ.w(B_j)`, injective in j across minimizing slots
(elementary: the map `j ↦ (j − t★γ)/e★` on the tie set), so RV(f) ≠ 0.  hRmul:
V1's Q-ascent + σ.hRmul on slot products + the position additivity (exact,
carry-free in the total coordinate — the §10 DEMOTION NOTE: the carry cocycle is
INVISIBLE in the evaluated V′ coordinate; the proved D-layer certifies the
alignment, it is not load-bearing here).

moves_ref: D.6/D.7(i)–(iii) read at the level-free stage; D.5's "no coset-splitting"
absence note (MOVES 2291–2292). deps: V0, V1, the L3_K1 pattern.
difficulty: medium-hard (the S9w mirror, EASIER: no field extension).
`V2_readFrame` packages the frame (assembled from V1 + the carrier + V6(a)'s hS6a
fill in P-phase).

**P-PHASE (2026-07-28, escalation): the V8 engine mirrored IN-FILE at the same key.**
The explicit carrier `v2Rc` is (†) on THE Fact-A/B `σ.Φ`-development with the
**identity digit** `v2dig := eval₂ (RingHom.id ↥σ.K) 1 ∘ σ.R` (evaluation at `T = 1`
— a ring hom extracting the hS5 scalar of a `C·T` monomial; NO field extension, NO
`L3_digPrime_nonzero`: digit nonvanishing is FREE from `hS5`'s unit).  The descent
engine (`IsStandardLift`/`L3_DIV`/`L4_TRANSiii` — unsatisfiable at the regrade key)
is REPLACED by the same-key kernel `v2DIV`: remainder weight/nonvanishing from V1's
exposed Q-ascent; the residual product law `R((a·b) %ₘ Φ) = R(a)·R(b)` by the
`w(Φ·Q) ≥ w(R_dev)` trichotomy — strict: parent `hRlt`; tie: IMPOSSIBLE (hStretch
forces `σ.e ∣ σ.h`, so `σ.e = 1`, `σ.t = 0`, `σ.s = 1`, and the parent `hRadd`
monomial identity `C(c_a·c_b)·T0 = C(c_R)·T0 + C(c_Q)·T1` pins the unit `c_Q` to the
vanishing `T1`-coefficient).  hRmul is then V8's bilinear slot expansion verbatim
(product development `Cdev`, per-pair `v2DIV` remainders, (I-aug)-deep carried
quotients from ReadPair steepness `e★σ.h < h★`, the `v2gr` graded slot computation,
the Laurent convolution regroup).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ### P-phase infrastructure — the V8 engine mirrored at the same key `σ.Φ` with the
identity digit.  Private helpers in dependency order: parent w-arithmetic; the graded-
residue calculus `v2gr` (the D.1(b) tie laws packaged as one additive map on the
zero-or-`w ≥ ω` domain); development plumbing; the identity digit `v2dig` and its
laws (hS5-unit nonvanishing — the descent engine's `L3_digPrime_nonzero` is NOT
needed); the explicit carrier `v2Rc` with its Fact-B independence spec `v2Rc_eq`. -/

section V2Infra

variable (σ : Stage p F)

private lemma v2w_one : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h; omega

private lemma v2w_neg (f : Polynomial ℤ_[p]) (hf : f ≠ 0) : σ.w (-f) = σ.w f := by
  have hne : (-1 : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hneg1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by
    have h := σ.hwmul (-1) (-1) hne hne
    rw [neg_mul_neg, one_mul] at h
    have h1 := v2w_one σ
    omega
  have h := σ.hwmul (-1) f hne hf
  rw [neg_one_mul] at h
  omega

/-- ultrametric finite-sum lower bound (zeros allowed among the summands). -/
private lemma v2sum_w_ge {ι : Type*} (S : Finset ι) (a : ι → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ σ.w (a j)) (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ σ.w (∑ j ∈ S, a j) := by
  classical
  revert hm hsum
  induction S using Finset.induction with
  | empty => intro hm hsum; simp at hsum
  | insert i T hiT ih =>
    intro hm hsum
    rw [Finset.sum_insert hiT] at hsum ⊢
    by_cases hai : a i = 0
    · rw [hai, zero_add] at hsum ⊢
      exact ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsum
    · by_cases hsT : (∑ j ∈ T, a j) = 0
      · rw [hsT, add_zero] at hsum ⊢
        exact hm i (Finset.mem_insert_self i T) hai
      · have h1 : m ≤ σ.w (a i) := hm i (Finset.mem_insert_self i T) hai
        have h2 : m ≤ σ.w (∑ j ∈ T, a j) :=
          ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsT
        exact le_trans (le_min h1 h2) (σ.hwult (a i) (∑ j ∈ T, a j) hai hsT hsum)

/-- "zero, or `w`-deep at least `ω`" — the domain of the level-`ω` graded residue. -/
private def v2Deep (ω : ℤ) (x : Polynomial ℤ_[p]) : Prop := x = 0 ∨ ω ≤ σ.w x

open scoped Classical in
/-- **the graded residue at level `ω`**: `R x` on the `w = ω` stratum, `0` elsewhere. -/
private noncomputable def v2gr (ω : ℤ) (x : Polynomial ℤ_[p]) : LaurentPolynomial ↥σ.K :=
  if x ≠ 0 ∧ σ.w x = ω then σ.R x else 0

private lemma v2gr_zero (ω : ℤ) : v2gr σ ω 0 = 0 := by
  unfold v2gr; rw [if_neg]; rintro ⟨h, -⟩; exact h rfl

private lemma v2gr_eq {ω : ℤ} {x : Polynomial ℤ_[p]} (hx : x ≠ 0) (hw : σ.w x = ω) :
    v2gr σ ω x = σ.R x := by
  unfold v2gr; rw [if_pos ⟨hx, hw⟩]

private lemma v2gr_deep {ω : ℤ} {x : Polynomial ℤ_[p]} (hw : σ.w x ≠ ω) :
    v2gr σ ω x = 0 := by
  unfold v2gr; rw [if_neg]; rintro ⟨-, h⟩; exact hw h

private lemma v2gr_spec {ω : ℤ} {x : Polynomial ℤ_[p]} (h : v2gr σ ω x ≠ 0) :
    x ≠ 0 ∧ σ.w x = ω := by
  by_contra hcon
  exact h (by unfold v2gr; rw [if_neg hcon])

/-- The graded residue is additive on the `Deep ω` domain (closed under `+`): the
D.1(b) tie calculus in one lemma — `hRadd` at ties, `hRlt`/`w_strict` at strict
drops, `w_jump` at weight jumps, `R_neg` at exact cancellations. -/
private lemma v2gr_add (hσ : StageCore σ) {ω : ℤ} {x y : Polynomial ℤ_[p]}
    (hx : v2Deep σ ω x) (hy : v2Deep σ ω y) :
    v2Deep σ ω (x + y) ∧ v2gr σ ω (x + y) = v2gr σ ω x + v2gr σ ω y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_add, v2gr_zero, zero_add]; exact ⟨hy, rfl⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero, v2gr_zero, add_zero]; exact ⟨hx, rfl⟩
  have hxw : ω ≤ σ.w x := hx.resolve_left hx0
  have hyw : ω ≤ σ.w y := hy.resolve_left hy0
  rcases eq_or_ne (x + y) 0 with hxy0 | hxy0
  · -- exact cancellation: `y = −x`
    have hyx : y = -x := eq_neg_of_add_eq_zero_right hxy0
    refine ⟨Or.inl hxy0, ?_⟩
    rw [hxy0, v2gr_zero]
    rcases eq_or_ne (σ.w x) ω with hwx | hwx
    · have hwy : σ.w y = ω := by rw [hyx, v2w_neg σ x hx0]; exact hwx
      rw [v2gr_eq σ hx0 hwx, v2gr_eq σ hy0 hwy, hyx, hσ.R_neg, add_neg_cancel]
    · have hwy : σ.w y ≠ ω := by rw [hyx, v2w_neg σ x hx0]; exact hwx
      rw [v2gr_deep σ hwx, v2gr_deep σ hwy, add_zero]
  have hult := σ.hwult x y hx0 hy0 hxy0
  have hDeep : v2Deep σ ω (x + y) := Or.inr (le_trans (le_min hxw hyw) hult)
  refine ⟨hDeep, ?_⟩
  rcases eq_or_ne (σ.w x) ω with hwx | hwx
  · rcases eq_or_ne (σ.w y) ω with hwy | hwy
    · -- both at level ω: hRadd at a tie, w_jump at a jump
      rcases eq_or_ne (σ.w (x + y)) ω with hwxy | hwxy
      · rw [v2gr_eq σ hxy0 hwxy, v2gr_eq σ hx0 hwx, v2gr_eq σ hy0 hwy]
        exact σ.hRadd x y hx0 hy0 hxy0 (by rw [hwx, hwy]) (by rw [hwxy, hwx])
      · have hwge : ω ≤ σ.w (x + y) := le_trans (le_min hxw hyw) hult
        have hj : σ.w x < σ.w (x + y) := by omega
        rw [v2gr_deep σ hwxy, v2gr_eq σ hx0 hwx, v2gr_eq σ hy0 hwy]
        exact (hσ.w_jump x y hx0 hy0 hxy0 (by rw [hwx, hwy]) hj).symm
    · -- x at ω, y strictly deeper: hRlt + w_strict
      have hlt : σ.w x < σ.w y := by omega
      have hws := hσ.w_strict x y hx0 hy0 hlt
      rw [v2gr_eq σ hxy0 (by rw [hws, hwx]), v2gr_eq σ hx0 hwx, v2gr_deep σ hwy, add_zero]
      exact σ.hRlt x y hx0 hy0 hxy0 hlt
  · rcases eq_or_ne (σ.w y) ω with hwy | hwy
    · -- y at ω, x strictly deeper: symmetric
      have hlt : σ.w y < σ.w x := by omega
      have hws := hσ.w_strict y x hy0 hx0 hlt
      have hyx0 : y + x ≠ 0 := by rwa [add_comm]
      rw [v2gr_deep σ hwx, zero_add, add_comm x y,
        v2gr_eq σ hyx0 (by rw [hws, hwy]), v2gr_eq σ hy0 hwy]
      exact σ.hRlt y x hy0 hx0 hyx0 hlt
    · -- both strictly deeper
      have hgt : ω < σ.w (x + y) := by
        have h1 : ω < σ.w x := by omega
        have h2 : ω < σ.w y := by omega
        exact lt_of_lt_of_le (lt_min h1 h2) hult
      rw [v2gr_deep σ (by omega : σ.w (x + y) ≠ ω), v2gr_deep σ hwx, v2gr_deep σ hwy, add_zero]

/-- finite-sum graded additivity. -/
private lemma v2gr_sum (hσ : StageCore σ) {ω : ℤ} {ι : Type*} (S : Finset ι)
    (a : ι → Polynomial ℤ_[p]) (h : ∀ j ∈ S, v2Deep σ ω (a j)) :
    v2Deep σ ω (∑ j ∈ S, a j) ∧ v2gr σ ω (∑ j ∈ S, a j) = ∑ j ∈ S, v2gr σ ω (a j) := by
  classical
  revert h
  induction S using Finset.induction with
  | empty =>
    intro h
    simp only [Finset.sum_empty]
    exact ⟨Or.inl rfl, v2gr_zero σ ω⟩
  | insert i T hiT ih =>
    intro h
    rw [Finset.sum_insert hiT, Finset.sum_insert hiT]
    obtain ⟨hD, hE⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨hD', hE'⟩ := v2gr_add σ hσ (h i (Finset.mem_insert_self i T)) hD
    exact ⟨hD', by rw [hE', hE]⟩

/-- developments add slotwise. -/
private lemma v2dev_add {Φ : Polynomial ℤ_[p]} {f g : Polynomial ℤ_[p]}
    {B B' : ℕ → Polynomial ℤ_[p]} {N N' : ℕ}
    (h : IsDevelopment Φ f B N) (h' : IsDevelopment Φ g B' N') :
    IsDevelopment Φ (f + g) (fun j => B j + B' j) (max N N') := by
  refine ⟨fun j => lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt (h.1 j) (h'.1 j)),
    fun j hj => ?_, ?_⟩
  · show B j + B' j = 0
    rw [h.2.1 j (le_trans (le_max_left _ _) hj), h'.2.1 j (le_trans (le_max_right _ _) hj),
      add_zero]
  · have hf2 : f = ∑ j ∈ Finset.range (max N N'), B j * Φ ^ j := by
      rw [h.2.2]
      refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_left _ _))) ?_
      intro j _ hj
      rw [h.2.1 j (le_of_not_gt (fun hc => hj (Finset.mem_range.mpr hc))), zero_mul]
    have hg2 : g = ∑ j ∈ Finset.range (max N N'), B' j * Φ ^ j := by
      rw [h'.2.2]
      refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_right _ _))) ?_
      intro j _ hj
      rw [h'.2.1 j (le_of_not_gt (fun hc => hj (Finset.mem_range.mpr hc))), zero_mul]
    rw [hf2, hg2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by rw [add_mul])

/-- developments negate slotwise. -/
private lemma v2dev_neg {Φ : Polynomial ℤ_[p]} {f : Polynomial ℤ_[p]}
    {B : ℕ → Polynomial ℤ_[p]} {N : ℕ} (h : IsDevelopment Φ f B N) :
    IsDevelopment Φ (-f) (fun j => -(B j)) N := by
  refine ⟨fun j => by rw [Polynomial.degree_neg]; exact h.1 j,
    fun j hj => by show -(B j) = 0; rw [h.2.1 j hj, neg_zero], ?_⟩
  calc -f = -∑ j ∈ Finset.range N, B j * Φ ^ j := by rw [← h.2.2]
    _ = ∑ j ∈ Finset.range N, -(B j * Φ ^ j) := by rw [Finset.sum_neg_distrib]
    _ = ∑ j ∈ Finset.range N, -(B j) * Φ ^ j :=
        Finset.sum_congr rfl fun j _ => (neg_mul (B j) (Φ ^ j)).symm

/-- the single-slot development of a coefficient. -/
private lemma v2dev_single {Φ B : Polynomial ℤ_[p]} (hΦ : Φ ≠ 0) (hB : inC Φ B) :
    IsDevelopment Φ B (fun j => if j = 0 then B else 0) 1 := by
  have hbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ (Polynomial.degree_eq_bot.mp h))
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · by_cases h0 : j = 0
    · subst h0
      simpa using (show B.degree < Φ.degree from hB)
    · simpa [h0] using hbot
  · show (if j = 0 then B else 0) = 0
    rw [if_neg (by omega : j ≠ 0)]
  · simp

/-- the 2-slot development of the key itself: `Φ = 0·Φ⁰ + 1·Φ¹`. -/
private lemma v2dev_key {Φ : Polynomial ℤ_[p]} (hmon : Φ.Monic) (hd1 : 1 ≤ Φ.natDegree) :
    IsDevelopment Φ Φ (fun j => if j = 1 then 1 else 0) 2 := by
  have hΦ : Φ ≠ 0 := hmon.ne_zero
  have hbot : (⊥ : WithBot ℕ) < Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ (Polynomial.degree_eq_bot.mp h))
  have hdpos : (0 : WithBot ℕ) < Φ.degree := by
    rw [Polynomial.degree_eq_natDegree hΦ]
    exact_mod_cast hd1
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · by_cases h1 : j = 1
    · simpa [h1, Polynomial.degree_one] using hdpos
    · simpa [h1] using hbot
  · show (if j = 1 then 1 else 0) = 0
    rw [if_neg (by omega : j ≠ 1)]
  · simp

/-- attained slot minima are unique. -/
private lemma v2slotMin_unique {m m' : ℤ} {N : ℕ} {sw : ℕ → ℤ} {nz : ℕ → Prop}
    (h : SlotMinAttained m N sw nz) (h' : SlotMinAttained m' N sw nz) : m = m' := by
  obtain ⟨j, hj, hjnz, hje⟩ := h.2
  obtain ⟨k, hk, hknz, hke⟩ := h'.2
  have h1 := h.1 k hk hknz
  have h2 := h'.1 j hj hjnz
  omega

/-! #### the identity digit — evaluation at `T = 1` (the §10 regrade digit: same field,
scalars preserved; the hS5 monomial's unit scalar read off by a ring hom) -/

/-- the identity read evaluation `↥σ.K[T^{±1}] →+* ↥σ.K`: scalars by the identity,
`T ↦ 1`. -/
private noncomputable def v2ev : LaurentPolynomial ↥σ.K →+* ↥σ.K :=
  LaurentPolynomial.eval₂ (RingHom.id ↥σ.K) 1

private lemma v2ev_monomial (a : ↥σ.K) (k : ℤ) :
    v2ev σ (LaurentPolynomial.C a * LaurentPolynomial.T k) = a := by
  unfold v2ev
  rw [LaurentPolynomial.eval₂_C_mul_T]
  simp

/-- **the identity digit**: the `T = 1` evaluation of the parent residual. -/
private noncomputable def v2dig (x : Polynomial ℤ_[p]) : ↥σ.K := v2ev σ (σ.R x)

private lemma v2dig_def (x : Polynomial ℤ_[p]) : v2dig σ x = v2ev σ (σ.R x) := rfl

/-- digit multiplicativity on nonzero inputs. -/
private lemma v2dig_mul {f g : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0) :
    v2dig σ (f * g) = v2dig σ f * v2dig σ g := by
  rw [v2dig_def, σ.hRmul f g hf hg, map_mul]
  rfl

private lemma v2dig_of_Radd {x a b : Polynomial ℤ_[p]}
    (h : σ.R x = σ.R a + σ.R b) :
    v2dig σ x = v2dig σ a + v2dig σ b := by
  rw [v2dig_def, h, map_add]
  rfl

private lemma v2dig_of_Req {x a : Polynomial ℤ_[p]} (h : σ.R x = σ.R a) :
    v2dig σ x = v2dig σ a := by
  rw [v2dig_def, h]
  rfl

private lemma v2dig_of_Rneg (hσ : StageCore σ) (x : Polynomial ℤ_[p]) :
    v2dig σ (-x) = - v2dig σ x := by
  rw [v2dig_def, hσ.R_neg, map_neg]
  rfl

/-- **the digit unit (D.3(d) analogue, FREE at the same key)**: a nonzero coefficient's
digit is `hS5`'s unit scalar — the `L3_digPrime_nonzero` role with zero cost. -/
private lemma v2dig_unit {B : Polynomial ℤ_[p]} (hB : B ≠ 0) (hBc : inC σ.Φ B) :
    ∃ c : (↥σ.K)ˣ, v2dig σ B = (c : ↥σ.K) ∧
      σ.R B = LaurentPolynomial.C (c : ↥σ.K) *
        LaurentPolynomial.T (- σ.t * σ.wPrev B) := by
  obtain ⟨c, hc⟩ := σ.hS5 B hB hBc
  exact ⟨c, by rw [v2dig_def, hc, v2ev_monomial], hc⟩

private lemma v2dig_ne {x : Polynomial ℤ_[p]} (hx : x ≠ 0) (hxd : x.degree < σ.Φ.degree) :
    v2dig σ x ≠ 0 := by
  obtain ⟨c, hc, -⟩ := v2dig_unit σ hx hxd
  rw [hc]
  exact c.ne_zero

private lemma v2one_inC : inC σ.Φ (1 : Polynomial ℤ_[p]) := by
  show (1 : Polynomial ℤ_[p]).degree < σ.Φ.degree
  rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree σ.hmonic.ne_zero]
  exact_mod_cast σ.hdeg

private lemma v2dig_one : v2dig σ (1 : Polynomial ℤ_[p]) = 1 := by
  have hne : v2dig σ (1 : Polynomial ℤ_[p]) ≠ 0 := v2dig_ne σ one_ne_zero (v2one_inC σ)
  have hsq : v2dig σ (1 : Polynomial ℤ_[p]) * v2dig σ 1 = v2dig σ 1 * 1 := by
    rw [← v2dig_mul σ one_ne_zero one_ne_zero, mul_one, mul_one]
  exact mul_left_cancel₀ hne hsq

/-! #### the explicit regrade carrier (†) at the same key -/

open scoped Classical in
/-- the tied-slot sum: identity digits at `childW`-minimizing slots, positions per the
read Bézout pair — the body of the (†) carrier on one development. -/
private noncomputable def v2dsum (e' h' : ℕ) (s' t' : ℤ) (m : ℤ)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) : LaurentPolynomial ↥σ.K :=
  ∑ j ∈ (Finset.range N).filter
      (fun j => B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ) = m),
    LaurentPolynomial.C (v2dig σ (B j)) *
      LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (B j))

open scoped Classical in
/-- **the explicit regrade carrier** (§10 (†), regrade instance), as a total function:
the tied-slot sum of THE development (Fact A/B) at the `childW` value; `0` at `f = 0`. -/
private noncomputable def v2Rc (e' h' : ℕ) (s' t' : ℤ) (f : Polynomial ℤ_[p]) :
    LaurentPolynomial ↥σ.K :=
  if hf : f ≠ 0 ∧ ∃ BN : (ℕ → Polynomial ℤ_[p]) × ℕ, IsDevelopment σ.Φ f BN.1 BN.2
  then v2dsum σ e' h' s' t' (childW σ σ.Φ e' h' f) hf.2.choose.1 hf.2.choose.2
  else 0

private lemma v2Rc_zero (e' h' : ℕ) (s' t' : ℤ) :
    v2Rc σ e' h' s' t' 0 = 0 := by
  unfold v2Rc
  rw [dif_neg]
  rintro ⟨h, -⟩; exact h rfl

/-- `v2dsum` ignores padding beyond the last nonzero slot. -/
private lemma v2dsum_ext (e' h' : ℕ) (s' t' : ℤ)
    (m : ℤ) {B : ℕ → Polynomial ℤ_[p]} {N N₂ : ℕ} (hN : N ≤ N₂)
    (hvan : ∀ j, N ≤ j → B j = 0) :
    v2dsum σ e' h' s' t' m B N₂ = v2dsum σ e' h' s' t' m B N := by
  unfold v2dsum
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.ext
  intro j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hBj, he⟩
    refine ⟨?_, hBj, he⟩
    by_contra hc
    exact hBj (hvan j (le_of_not_gt hc))
  · rintro ⟨hj, hBj, he⟩
    exact ⟨lt_of_lt_of_le hj hN, hBj, he⟩

/-- **the carrier spec** (Fact B independence): on any development of a nonzero `f`,
`v2Rc f` IS the tied-slot sum of that development. -/
private lemma v2Rc_eq (e' h' : ℕ) (s' t' : ℤ)
    {f : Polynomial ℤ_[p]} {B : ℕ → Polynomial ℤ_[p]} {N : ℕ}
    (hf : f ≠ 0) (hdev : IsDevelopment σ.Φ f B N) :
    v2Rc σ e' h' s' t' f
      = v2dsum σ e' h' s' t' (childW σ σ.Φ e' h' f) B N := by
  have hex : f ≠ 0 ∧ ∃ BN : (ℕ → Polynomial ℤ_[p]) × ℕ, IsDevelopment σ.Φ f BN.1 BN.2 :=
    ⟨hf, ⟨(B, N), hdev⟩⟩
  unfold v2Rc
  rw [dif_pos hex]
  have hdev₀ : IsDevelopment σ.Φ f hex.2.choose.1 hex.2.choose.2 := hex.2.choose_spec
  have hBeq : hex.2.choose.1 = B := funext (L0_FactB_unique σ.Φ σ.hmonic f hdev₀ hdev)
  rw [← v2dsum_ext σ e' h' s' t' (childW σ σ.Φ e' h' f)
      (le_max_left hex.2.choose.2 N) hdev₀.2.1, hBeq,
    v2dsum_ext σ e' h' s' t' (childW σ σ.Φ e' h' f)
      (le_max_right hex.2.choose.2 N) hdev.2.1]

/-- position injectivity across tied slots: `e′·pos(j) = j − t′·m`, so positions
determine slots (Bézout). -/
private lemma v2pos_inj {e' h' : ℕ} {s' t' m : ℤ}
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) {j k : ℕ} {wj wk : ℤ}
    (hj : (e' : ℤ) * wj + (j : ℤ) * (h' : ℤ) = m)
    (hk : (e' : ℤ) * wk + (k : ℤ) * (h' : ℤ) = m)
    (hp : (j : ℤ) * s' - t' * wj = (k : ℤ) * s' - t' * wk) : j = k := by
  have h1 : (e' : ℤ) * ((j : ℤ) * s' - t' * wj) = (j : ℤ) - t' * m := by
    linear_combination (-t') * hj + (j : ℤ) * hbez'
  have h2 : (e' : ℤ) * ((k : ℤ) * s' - t' * wk) = (k : ℤ) - t' * m := by
    linear_combination (-t') * hk + (k : ℤ) * hbez'
  rw [hp] at h1
  have h3 : (j : ℤ) = (k : ℤ) := by linarith [h1.symm.trans h2]
  exact_mod_cast h3

/-- the tied-slot sum is nonzero once one tied slot exists: distinct positions
(`v2pos_inj`), nonzero digits (`v2dig_unit`). -/
private lemma v2dsum_ne (e' h' : ℕ) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1)
    {m : ℤ} {B : ℕ → Polynomial ℤ_[p]} {N : ℕ}
    (hdeg : ∀ j, (B j).degree < σ.Φ.degree)
    {j₀ : ℕ} (hj₀N : j₀ < N) (hj₀nz : B j₀ ≠ 0)
    (hj₀m : (e' : ℤ) * σ.w (B j₀) + (j₀ : ℤ) * (h' : ℤ) = m) :
    v2dsum σ e' h' s' t' m B N ≠ 0 := by
  classical
  have hdigne : ∀ j, B j ≠ 0 → v2dig σ (B j) ≠ 0 :=
    fun j hj => v2dig_ne σ hj (hdeg j)
  intro hcon
  unfold v2dsum at hcon
  set T := (Finset.range N).filter
      (fun j => B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ) = m) with hT
  have hj₀T : j₀ ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj₀N, hj₀nz, hj₀m⟩
  simp_rw [← LaurentPolynomial.single_eq_C_mul_T] at hcon
  have hcon' : (∑ j ∈ T, Finsupp.single ((j : ℤ) * s' - t' * σ.w (B j))
      (v2dig σ (B j)) : ℤ →₀ ↥σ.K) = 0 := hcon
  have happ := DFunLike.congr_fun hcon' ((j₀ : ℤ) * s' - t' * σ.w (B j₀))
  rw [Finset.sum_apply'] at happ
  simp only [Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at happ
  rw [Finset.sum_eq_single j₀] at happ
  · rw [if_pos rfl] at happ
    exact hdigne j₀ hj₀nz happ
  · intro b hb hbne
    rw [if_neg]
    intro hpe
    have hbT := hb
    simp only [hT, Finset.mem_filter, Finset.mem_range] at hbT
    exact hbne (v2pos_inj hbez' hbT.2.2 hj₀m hpe)
  · intro hnot
    exact absurd hj₀T hnot

/-! #### slot-value ↔ parent-weight converters (the `e′ > 0` cancellations) -/

private lemma v2Deep_of_slot {e' h' : ℕ} (he' : 1 ≤ e') {m ω : ℤ} {j : ℕ}
    (hω : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = m) {x : Polynomial ℤ_[p]}
    (hx : x = 0 ∨ m ≤ (e' : ℤ) * σ.w x + (j : ℤ) * (h' : ℤ)) : v2Deep σ ω x := by
  rcases hx with h | h
  · exact Or.inl h
  · right
    have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
    have h2 : (e' : ℤ) * ω ≤ (e' : ℤ) * σ.w x := by linarith
    exact le_of_mul_le_mul_left h2 he0

private lemma v2w_eq_of_slot {e' h' : ℕ} (he' : 1 ≤ e') {m ω : ℤ} {j : ℕ}
    (hω : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = m) {x : Polynomial ℤ_[p]}
    (hx : (e' : ℤ) * σ.w x + (j : ℤ) * (h' : ℤ) = m) : σ.w x = ω := by
  have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
  have h2 : (e' : ℤ) * σ.w x = (e' : ℤ) * ω := by linarith
  exact mul_left_cancel₀ he0.ne' h2

private lemma v2w_ne_of_slot {e' h' : ℕ} (he' : 1 ≤ e') {m ω : ℤ} {j : ℕ}
    (hω : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = m) {x : Polynomial ℤ_[p]}
    (hx : (e' : ℤ) * σ.w x + (j : ℤ) * (h' : ℤ) ≠ m) : σ.w x ≠ ω := by
  intro hc
  exact hx (by rw [hc]; exact hω)

/-! #### `childW` at the distinguished elements (same key) -/

/-- `childW` at the key: `wV(σ.Φ) = h′` (slot-1 arithmetic on the 2-slot development). -/
private lemma v2cw_key (e' h' : ℕ)
    (hSMW : IsSlotMinWeight (childW σ σ.Φ e' h') σ.Φ e' h' σ.w) :
    childW σ σ.Φ e' h' σ.Φ = (h' : ℤ) := by
  have hatt := hSMW σ.Φ _ 2 σ.hmonic.ne_zero (v2dev_key σ.hmonic σ.hdeg)
  refine v2slotMin_unique hatt ⟨?_, ?_⟩
  · intro j hj hnz
    have hj01 : j = 0 ∨ j = 1 := by omega
    rcases hj01 with rfl | rfl
    · exfalso
      apply hnz
      show (if 0 = 1 then (1 : Polynomial ℤ_[p]) else 0) = 0
      rw [if_neg (by omega : (0 : ℕ) ≠ 1)]
    · show (h' : ℤ) ≤ (e' : ℤ) * σ.w (if 1 = 1 then 1 else 0) + ((1 : ℕ) : ℤ) * (h' : ℤ)
      rw [if_pos rfl, v2w_one σ]
      push_cast
      omega
  · refine ⟨1, by omega, ?_, ?_⟩
    · show (if 1 = 1 then (1 : Polynomial ℤ_[p]) else 0) ≠ 0
      rw [if_pos rfl]
      exact one_ne_zero
    · show (h' : ℤ) = (e' : ℤ) * σ.w (if 1 = 1 then 1 else 0) + ((1 : ℕ) : ℤ) * (h' : ℤ)
      rw [if_pos rfl, v2w_one σ]
      push_cast
      omega

/-- `childW` is negation-invariant. -/
private lemma v2cw_neg (e' h' : ℕ)
    (hSMW : IsSlotMinWeight (childW σ σ.Φ e' h') σ.Φ e' h' σ.w)
    {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    childW σ σ.Φ e' h' (-f) = childW σ σ.Φ e' h' f := by
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg f
  have hatt := hSMW f B N hf hdev
  have hattn := hSMW (-f) _ N (neg_ne_zero.mpr hf) (v2dev_neg hdev)
  have hattn' : SlotMinAttained (childW σ σ.Φ e' h' (-f)) N
      (fun j => (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)) (fun j => B j ≠ 0) := by
    obtain ⟨hlo, jj, hjj, hjjnz, hjje⟩ := hattn
    have hjjB : B jj ≠ 0 := fun h0 => hjjnz (show -(B jj) = 0 by rw [h0, neg_zero])
    constructor
    · intro j hj hnz
      have h := hlo j hj (show -(B j) ≠ 0 from neg_ne_zero.mpr hnz)
      simpa only [v2w_neg σ (B j) hnz] using h
    · exact ⟨jj, hjj, hjjB, by simpa only [v2w_neg σ (B jj) hjjB] using hjje⟩
  exact v2slotMin_unique hattn' hatt

/-! #### the two `ReadResData` pins for the explicit carrier -/

/-- the D.3(b) key pin at the regrade: `v2Rc(σ.Φ) = z^{s′}`. -/
private lemma v2Rc_phi (e' h' : ℕ) (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ σ.Φ e' h') σ.Φ e' h' σ.w) :
    v2Rc σ e' h' s' t' σ.Φ = LaurentPolynomial.T s' := by
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  rw [v2Rc_eq σ e' h' s' t' hΦne (v2dev_key σ.hmonic σ.hdeg)]
  unfold v2dsum
  rw [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_one]
  have h0cond : ¬((if (0 : ℕ) = 1 then (1 : Polynomial ℤ_[p]) else 0) ≠ 0 ∧
      (e' : ℤ) * σ.w (if (0 : ℕ) = 1 then 1 else 0) + ((0 : ℕ) : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' σ.Φ) := by
    rintro ⟨h0, -⟩
    exact h0 (by rw [if_neg (by omega : (0 : ℕ) ≠ 1)])
  have h1cond : (if (1 : ℕ) = 1 then (1 : Polynomial ℤ_[p]) else 0) ≠ 0 ∧
      (e' : ℤ) * σ.w (if (1 : ℕ) = 1 then 1 else 0) + ((1 : ℕ) : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' σ.Φ := by
    rw [if_pos rfl, v2cw_key σ e' h' hSMW, v2w_one σ]
    refine ⟨one_ne_zero, ?_⟩
    push_cast
    omega
  rw [if_neg h0cond, if_pos h1cond, zero_add]
  have hred : ((fun j : ℕ => if j = 1 then (1 : Polynomial ℤ_[p]) else 0) 1) = 1 := by
    norm_num
  rw [hred, v2dig_one σ, map_one, one_mul, v2w_one σ]
  norm_num

/-- the (S5) pin at the regrade: single-slot coefficients carry the SAME hS5 unit
scalar, position re-forced at `−t′·σ.w B` — BOTH conjuncts of `ReadResData.hS5`
with one witness. -/
private lemma v2Rc_S5 (e' h' : ℕ) (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ σ.Φ e' h') σ.Φ e' h' σ.w)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBc : inC σ.Φ B) :
    ∃ c : (↥σ.K)ˣ,
      σ.R B = LaurentPolynomial.C (c : ↥σ.K) *
          LaurentPolynomial.T (- σ.t * σ.wPrev B) ∧
      v2Rc σ e' h' s' t' B
        = LaurentPolynomial.C (c : ↥σ.K) * LaurentPolynomial.T (- t' * σ.w B) := by
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hcw : childW σ σ.Φ e' h' B = (e' : ℤ) * σ.w B :=
    L4_TRANSii σ σ.Φ e' h' _ hSMW B hB hBc
  obtain ⟨c, hdig, hR⟩ := v2dig_unit σ hB hBc
  refine ⟨c, hR, ?_⟩
  rw [v2Rc_eq σ e' h' s' t' hB (v2dev_single hΦne hBc)]
  unfold v2dsum
  rw [Finset.sum_filter, Finset.sum_range_one]
  have h0cond : (if (0 : ℕ) = 0 then B else 0) ≠ 0 ∧
      (e' : ℤ) * σ.w (if (0 : ℕ) = 0 then B else 0) + ((0 : ℕ) : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' B := by
    rw [if_pos rfl, hcw]
    exact ⟨hB, by push_cast; ring⟩
  rw [if_pos h0cond]
  have hred : ((fun j : ℕ => if j = 0 then B else 0) 0) = B := by norm_num
  rw [hred, hdig]
  show LaurentPolynomial.C (c : ↥σ.K) *
      LaurentPolynomial.T (((0 : ℕ) : ℤ) * s' - t' * σ.w B) = _
  norm_num

/-! #### the easy law legs: hRne, hRneg -/

/-- hRne: the carrier is nonvanishing on nonzero inputs. -/
private lemma v2Rc_ne (e' h' : ℕ) (s' t' : ℤ)
    (hbez' : (e' : ℤ) * s' + (h' : ℤ) * t' = 1)
    (hSMW : IsSlotMinWeight (childW σ σ.Φ e' h') σ.Φ e' h' σ.w)
    {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    v2Rc σ e' h' s' t' f ≠ 0 := by
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg f
  obtain ⟨-, j₀, hj₀N, hj₀nz, hj₀e⟩ := hSMW f B N hf hdev
  rw [v2Rc_eq σ e' h' s' t' hf hdev]
  exact v2dsum_ne σ e' h' s' t' hbez' hdev.1 hj₀N hj₀nz hj₀e.symm

/-- hRneg: the carrier is odd (parent `R_neg` slotwise; positions and ties are
negation-invariant). -/
private lemma v2Rc_negLaw (hσ : StageCore σ) (e' h' : ℕ) (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ σ.Φ e' h') σ.Φ e' h' σ.w)
    (f : Polynomial ℤ_[p]) :
    v2Rc σ e' h' s' t' (-f) = - v2Rc σ e' h' s' t' f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · rw [neg_zero, v2Rc_zero, neg_zero]
  obtain ⟨B, N, hdev⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg f
  rw [v2Rc_eq σ e' h' s' t' hf hdev,
    v2Rc_eq σ e' h' s' t' (neg_ne_zero.mpr hf) (v2dev_neg hdev),
    v2cw_neg σ e' h' hSMW hf]
  unfold v2dsum
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  show (if -(B j) ≠ 0 ∧ (e' : ℤ) * σ.w (-(B j)) + (j : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f
      then LaurentPolynomial.C (v2dig σ (-(B j))) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (-(B j)))
      else 0)
    = -(if B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f
      then LaurentPolynomial.C (v2dig σ (B j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (B j))
      else 0)
  by_cases hBj : B j = 0
  · have hn1 : ¬(-(B j) ≠ 0 ∧ (e' : ℤ) * σ.w (-(B j)) + (j : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f) := by
      rintro ⟨h0, -⟩
      exact h0 (by rw [hBj, neg_zero])
    have hn2 : ¬(B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f) := by
      rintro ⟨h0, -⟩
      exact h0 hBj
    rw [if_neg hn1, if_neg hn2, neg_zero]
  · have hwn := v2w_neg σ (B j) hBj
    have hcd : v2dig σ (-(B j)) = - v2dig σ (B j) := v2dig_of_Rneg σ hσ (B j)
    by_cases hc : B j ≠ 0 ∧ (e' : ℤ) * σ.w (B j) + (j : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f
    · rw [if_pos hc, if_pos ⟨neg_ne_zero.mpr hBj, by rw [hwn]; exact hc.2⟩,
        hwn, hcd, map_neg, neg_mul]
    · rw [if_neg hc, if_neg (fun hcn => hc ⟨hBj, by rw [← hwn]; exact hcn.2⟩), neg_zero]

/-! #### monic-division sum plumbing -/

/-- `%ₘ` is additive (monic divisor). -/
private lemma v2add_modByMonic {q : Polynomial ℤ_[p]} (hq : q.Monic)
    (a b : Polynomial ℤ_[p]) : (a + b) %ₘ q = a %ₘ q + b %ₘ q := by
  have ha := Polynomial.modByMonic_add_div a q
  have hb := Polynomial.modByMonic_add_div b q
  refine (Polynomial.div_modByMonic_unique (a /ₘ q + b /ₘ q) (a %ₘ q + b %ₘ q) hq
    ⟨?_, ?_⟩).2
  · linear_combination ha + hb
  · exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt (Polynomial.degree_modByMonic_lt a hq) (Polynomial.degree_modByMonic_lt b hq))

/-- `%ₘ` distributes over finite sums (monic divisor). -/
private lemma v2sum_modByMonic {q : Polynomial ℤ_[p]} (hq : q.Monic) {ι : Type*}
    (S : Finset ι) (a : ι → Polynomial ℤ_[p]) :
    (∑ j ∈ S, a j) %ₘ q = ∑ j ∈ S, (a j %ₘ q) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i T hiT ih =>
    rw [Finset.sum_insert hiT, Finset.sum_insert hiT, v2add_modByMonic hq, ih]

/-! #### the three D.1(b) tie laws for the explicit carrier (per-slot `v2gr` calculus) -/

/-- hRadd: at a childW tie with no jump, the carrier adds. -/
private lemma v2Rc_addLaw (hσ : StageCore σ)
    (e' h' : ℕ) (he' : 1 ≤ e') (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ σ.Φ e' h') σ.Φ e' h' σ.w)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) (hfg : f + g' ≠ 0)
    (hEq : childW σ σ.Φ e' h' f = childW σ σ.Φ e' h' g')
    (hSum : childW σ σ.Φ e' h' (f + g') = childW σ σ.Φ e' h' f) :
    v2Rc σ e' h' s' t' (f + g')
      = v2Rc σ e' h' s' t' f + v2Rc σ e' h' s' t' g' := by
  classical
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg g'
  have hdevC : IsDevelopment σ.Φ (f + g') (fun j => Bf j + Bg j) (max Nf Ng) :=
    v2dev_add hdevf hdevg
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  rw [v2Rc_eq σ e' h' s' t' hfg hdevC,
    v2Rc_eq σ e' h' s' t' hf hdevf,
    v2Rc_eq σ e' h' s' t' hg' hdevg, hSum, ← hEq,
    ← v2dsum_ext σ e' h' s' t' (childW σ σ.Φ e' h' f)
      (le_max_left Nf Ng) hdevf.2.1,
    ← v2dsum_ext σ e' h' s' t' (childW σ σ.Φ e' h' f)
      (le_max_right Nf Ng) hdevg.2.1]
  unfold v2dsum
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  show (if (Bf j + Bg j) ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f
      then LaurentPolynomial.C (v2dig σ (Bf j + Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j + Bg j))
      else 0)
    = (if Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f
      then LaurentPolynomial.C (v2dig σ (Bf j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j))
      else 0)
      + (if Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f
      then LaurentPolynomial.C (v2dig σ (Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bg j))
      else 0)
  -- slot lower bounds (∨-form) for both halves, keyed to the common tie level
  have hDf : Bf j = 0 ∨ childW σ σ.Φ e' h' f
      ≤ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) := by
    rcases eq_or_ne (Bf j) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr (hminf j ?_ h0)
      by_contra hc
      exact h0 (hdevf.2.1 j (le_of_not_gt hc))
  have hDg : Bg j = 0 ∨ childW σ σ.Φ e' h' f
      ≤ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) := by
    rcases eq_or_ne (Bg j) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr (hEq ▸ hming j ?_ h0)
      by_contra hc
      exact h0 (hdevg.2.1 j (le_of_not_gt hc))
  by_cases hjf : Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ)
      = childW σ σ.Φ e' h' f
  · obtain ⟨hf0, hfe⟩ := hjf
    by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f
    · -- both tied at slot j; ω := σ.w (Bf j)
      obtain ⟨hg0, hge⟩ := hjg
      have hwg : σ.w (Bg j) = σ.w (Bf j) := v2w_eq_of_slot σ he' hfe hge
      have hgr := (v2gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (Or.inr (le_of_eq hwg.symm))).2
      rw [v2gr_eq σ hf0 rfl, v2gr_eq σ hg0 hwg] at hgr
      by_cases hd : v2dig σ (Bf j) + v2dig σ (Bg j) = 0
      · -- digit cancellation: the sum slot is NOT tied; the two terms cancel
        have hnotied : ¬((Bf j + Bg j) ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
              = childW σ σ.Φ e' h' f) := by
          rintro ⟨hs0, hse⟩
          have hws : σ.w (Bf j + Bg j) = σ.w (Bf j) := v2w_eq_of_slot σ he' hfe hse
          have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) + σ.R (Bg j) := by
            rw [← v2gr_eq σ hs0 hws]; exact hgr
          refine v2dig_ne σ hs0
            (lt_of_le_of_lt (Polynomial.degree_add_le _ _)
              (max_lt (hdevf.1 j) (hdevg.1 j))) ?_
          rw [v2dig_of_Radd σ hRs]
          exact hd
        rw [if_neg hnotied, if_pos ⟨hf0, hfe⟩, if_pos ⟨hg0, hge⟩, hwg,
          ← add_mul, ← map_add, hd, map_zero, zero_mul]
      · -- no cancellation: the sum slot is tied, digits add
        have hgrne : v2gr σ (σ.w (Bf j)) (Bf j + Bg j) ≠ 0 := by
          rw [hgr]
          intro h0
          apply hd
          have hev : v2dig σ (Bf j) + v2dig σ (Bg j)
              = v2ev σ (σ.R (Bf j) + σ.R (Bg j)) := by
            rw [map_add]
            rfl
          rw [hev, h0, map_zero]
        obtain ⟨hs0, hws⟩ := v2gr_spec σ hgrne
        have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) + σ.R (Bg j) := by
          rw [← v2gr_eq σ hs0 hws]; exact hgr
        have hcds : v2dig σ (Bf j + Bg j)
            = v2dig σ (Bf j) + v2dig σ (Bg j) := v2dig_of_Radd σ hRs
        rw [if_pos ⟨hs0, by rw [hws]; exact hfe⟩, if_pos ⟨hf0, hfe⟩,
          if_pos ⟨hg0, hge⟩, hws, hwg, hcds, map_add, add_mul]
    · -- f tied, g not: the g half is invisible at level ω
      have hgrg : v2gr σ (σ.w (Bf j)) (Bg j) = 0 := by
        rcases eq_or_ne (Bg j) 0 with h0 | h0
        · rw [h0, v2gr_zero]
        · refine v2gr_deep σ (v2w_ne_of_slot σ he' hfe ?_)
          intro hce
          exact hjg ⟨h0, hce⟩
      have hgr := (v2gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (v2Deep_of_slot σ he' hfe hDg)).2
      rw [v2gr_eq σ hf0 rfl, hgrg, add_zero] at hgr
      have hgrne : v2gr σ (σ.w (Bf j)) (Bf j + Bg j) ≠ 0 := by
        rw [hgr]; exact σ.hRne _ hf0
      obtain ⟨hs0, hws⟩ := v2gr_spec σ hgrne
      have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) := by
        rw [← v2gr_eq σ hs0 hws]; exact hgr
      have hcds : v2dig σ (Bf j + Bg j) = v2dig σ (Bf j) := v2dig_of_Req σ hRs
      rw [if_pos ⟨hs0, by rw [hws]; exact hfe⟩, if_pos ⟨hf0, hfe⟩, if_neg hjg,
        add_zero, hws, hcds]
  · by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f
    · -- g tied, f not: mirror
      obtain ⟨hg0, hge⟩ := hjg
      have hgrf : v2gr σ (σ.w (Bg j)) (Bf j) = 0 := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · rw [h0, v2gr_zero]
        · refine v2gr_deep σ (v2w_ne_of_slot σ he' hge ?_)
          intro hce
          exact hjf ⟨h0, hce⟩
      have hgr := (v2gr_add σ hσ (v2Deep_of_slot σ he' hge hDf)
        (Or.inr (le_refl (σ.w (Bg j))))).2
      rw [v2gr_eq σ hg0 rfl, hgrf, zero_add] at hgr
      have hgrne : v2gr σ (σ.w (Bg j)) (Bf j + Bg j) ≠ 0 := by
        rw [hgr]; exact σ.hRne _ hg0
      obtain ⟨hs0, hws⟩ := v2gr_spec σ hgrne
      have hRs : σ.R (Bf j + Bg j) = σ.R (Bg j) := by
        rw [← v2gr_eq σ hs0 hws]; exact hgr
      have hcds : v2dig σ (Bf j + Bg j) = v2dig σ (Bg j) := v2dig_of_Req σ hRs
      rw [if_pos ⟨hs0, by rw [hws]; exact hge⟩, if_neg hjf,
        if_pos ⟨hg0, hge⟩, zero_add, hws, hcds]
    · -- neither tied: the sum slot cannot be tied either
      have hnotied : ¬((Bf j + Bg j) ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
            = childW σ σ.Φ e' h' f) := by
        rintro ⟨hs0, hse⟩
        have hgrf : v2gr σ (σ.w (Bf j + Bg j)) (Bf j) = 0 := by
          rcases eq_or_ne (Bf j) 0 with h0 | h0
          · rw [h0, v2gr_zero]
          · refine v2gr_deep σ (v2w_ne_of_slot σ he' hse ?_)
            intro hce
            exact hjf ⟨h0, hce⟩
        have hgrg : v2gr σ (σ.w (Bf j + Bg j)) (Bg j) = 0 := by
          rcases eq_or_ne (Bg j) 0 with h0 | h0
          · rw [h0, v2gr_zero]
          · refine v2gr_deep σ (v2w_ne_of_slot σ he' hse ?_)
            intro hce
            exact hjg ⟨h0, hce⟩
        have hgr := (v2gr_add σ hσ (v2Deep_of_slot σ he' hse hDf)
          (v2Deep_of_slot σ he' hse hDg)).2
        rw [v2gr_eq σ hs0 rfl, hgrf, hgrg, add_zero] at hgr
        exact σ.hRne _ hs0 hgr
      rw [if_neg hnotied, if_neg hjf, if_neg hjg, add_zero]

/-- w_jump: at a childW tie whose sum jumps, the carriers cancel. -/
private lemma v2Rc_jumpLaw (hσ : StageCore σ)
    (e' h' : ℕ) (he' : 1 ≤ e') (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ σ.Φ e' h') σ.Φ e' h' σ.w)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) (hfg : f + g' ≠ 0)
    (hEq : childW σ σ.Φ e' h' f = childW σ σ.Φ e' h' g')
    (hJump : childW σ σ.Φ e' h' f < childW σ σ.Φ e' h' (f + g')) :
    v2Rc σ e' h' s' t' f + v2Rc σ e' h' s' t' g' = 0 := by
  classical
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg g'
  have hdevC : IsDevelopment σ.Φ (f + g') (fun j => Bf j + Bg j) (max Nf Ng) :=
    v2dev_add hdevf hdevg
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  obtain ⟨hminC, -⟩ := hSMW (f + g') _ (max Nf Ng) hfg hdevC
  rw [v2Rc_eq σ e' h' s' t' hf hdevf,
    v2Rc_eq σ e' h' s' t' hg' hdevg, ← hEq,
    ← v2dsum_ext σ e' h' s' t' (childW σ σ.Φ e' h' f)
      (le_max_left Nf Ng) hdevf.2.1,
    ← v2dsum_ext σ e' h' s' t' (childW σ σ.Φ e' h' f)
      (le_max_right Nf Ng) hdevg.2.1]
  unfold v2dsum
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  show (if Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f
      then LaurentPolynomial.C (v2dig σ (Bf j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j))
      else 0)
      + (if Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f
      then LaurentPolynomial.C (v2dig σ (Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bg j))
      else 0) = 0
  have hjN : j < max Nf Ng := Finset.mem_range.mp hj
  -- a tied sum-slot at the pre-jump level contradicts the jump
  have hnoslot : ∀ ω : ℤ, (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f →
      v2gr σ ω (Bf j + Bg j) = 0 := by
    intro ω hω
    by_contra hne
    obtain ⟨hs0, hws⟩ := v2gr_spec σ hne
    have hle : childW σ σ.Φ e' h' (f + g')
        ≤ (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ) := hminC j hjN hs0
    rw [hws] at hle
    omega
  by_cases hjf : Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ)
      = childW σ σ.Φ e' h' f
  · obtain ⟨hf0, hfe⟩ := hjf
    by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f
    · -- both tied: residues must cancel (else the sum slot survives at the old level)
      obtain ⟨hg0, hge⟩ := hjg
      have hwg : σ.w (Bg j) = σ.w (Bf j) := v2w_eq_of_slot σ he' hfe hge
      have hgr := (v2gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (Or.inr (le_of_eq hwg.symm))).2
      rw [v2gr_eq σ hf0 rfl, v2gr_eq σ hg0 hwg, hnoslot (σ.w (Bf j)) hfe] at hgr
      -- hgr : 0 = R (Bf j) + R (Bg j)
      have hcds : v2dig σ (Bf j) + v2dig σ (Bg j) = 0 := by
        have hev : v2dig σ (Bf j) + v2dig σ (Bg j)
            = v2ev σ (σ.R (Bf j) + σ.R (Bg j)) := by
          rw [map_add]
          rfl
        rw [hev, ← hgr, map_zero]
      rw [if_pos ⟨hf0, hfe⟩, if_pos ⟨hg0, hge⟩, hwg, ← add_mul, ← map_add, hcds,
        map_zero, zero_mul]
    · -- f tied alone: its residue would survive — contradiction
      exfalso
      have hgrg : v2gr σ (σ.w (Bf j)) (Bg j) = 0 := by
        rcases eq_or_ne (Bg j) 0 with h0 | h0
        · rw [h0, v2gr_zero]
        · refine v2gr_deep σ (v2w_ne_of_slot σ he' hfe ?_)
          intro hce
          exact hjg ⟨h0, hce⟩
      have hDg : Bg j = 0 ∨ childW σ σ.Φ e' h' f
          ≤ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) := by
        rcases eq_or_ne (Bg j) 0 with h0 | h0
        · exact Or.inl h0
        · refine Or.inr (hEq ▸ hming j ?_ h0)
          by_contra hc
          exact h0 (hdevg.2.1 j (le_of_not_gt hc))
      have hgr := (v2gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j))))
        (v2Deep_of_slot σ he' hfe hDg)).2
      rw [v2gr_eq σ hf0 rfl, hgrg, add_zero, hnoslot (σ.w (Bf j)) hfe] at hgr
      exact σ.hRne _ hf0 hgr.symm
  · by_cases hjg : Bg j ≠ 0 ∧ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f
    · -- g tied alone: mirror contradiction
      exfalso
      obtain ⟨hg0, hge⟩ := hjg
      have hgrf : v2gr σ (σ.w (Bg j)) (Bf j) = 0 := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · rw [h0, v2gr_zero]
        · refine v2gr_deep σ (v2w_ne_of_slot σ he' hge ?_)
          intro hce
          exact hjf ⟨h0, hce⟩
      have hDf : Bf j = 0 ∨ childW σ σ.Φ e' h' f
          ≤ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · exact Or.inl h0
        · refine Or.inr (hminf j ?_ h0)
          by_contra hc
          exact h0 (hdevf.2.1 j (le_of_not_gt hc))
      have hgr := (v2gr_add σ hσ (v2Deep_of_slot σ he' hge hDf)
        (Or.inr (le_refl (σ.w (Bg j))))).2
      rw [v2gr_eq σ hg0 rfl, hgrf, zero_add, hnoslot (σ.w (Bg j)) hge] at hgr
      exact σ.hRne _ hg0 hgr.symm
    · rw [if_neg hjf, if_neg hjg, add_zero]

/-- hRlt: below a strictly deeper summand, the carrier is unchanged. -/
private lemma v2Rc_ltLaw (hσ : StageCore σ)
    (e' h' : ℕ) (he' : 1 ≤ e') (s' t' : ℤ)
    (hSMW : IsSlotMinWeight (childW σ σ.Φ e' h') σ.Φ e' h' σ.w)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) (hfg : f + g' ≠ 0)
    (hLt : childW σ σ.Φ e' h' f < childW σ σ.Φ e' h' g')
    (hStr : childW σ σ.Φ e' h' (f + g') = childW σ σ.Φ e' h' f) :
    v2Rc σ e' h' s' t' (f + g') = v2Rc σ e' h' s' t' f := by
  classical
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg g'
  have hdevC : IsDevelopment σ.Φ (f + g') (fun j => Bf j + Bg j) (max Nf Ng) :=
    v2dev_add hdevf hdevg
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  rw [v2Rc_eq σ e' h' s' t' hfg hdevC,
    v2Rc_eq σ e' h' s' t' hf hdevf, hStr,
    ← v2dsum_ext σ e' h' s' t' (childW σ σ.Φ e' h' f)
      (le_max_left Nf Ng) hdevf.2.1]
  unfold v2dsum
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  show (if (Bf j + Bg j) ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f
      then LaurentPolynomial.C (v2dig σ (Bf j + Bg j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j + Bg j))
      else 0)
    = (if Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f
      then LaurentPolynomial.C (v2dig σ (Bf j)) *
        LaurentPolynomial.T ((j : ℤ) * s' - t' * σ.w (Bf j))
      else 0)
  -- the g half is strictly deep at every pre-level slot
  have hgdeep : ∀ ω : ℤ, (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f →
      v2gr σ ω (Bg j) = 0 ∧ (Bg j = 0 ∨ ω ≤ σ.w (Bg j)) := by
    intro ω hω
    rcases eq_or_ne (Bg j) 0 with h0 | h0
    · exact ⟨by rw [h0, v2gr_zero], Or.inl h0⟩
    · have hjNg : j < Ng := by
        by_contra hc
        exact h0 (hdevg.2.1 j (le_of_not_gt hc))
      have hgt : (e' : ℤ) * ω + (j : ℤ) * (h' : ℤ) < (e' : ℤ) * σ.w (Bg j)
          + (j : ℤ) * (h' : ℤ) := by
        have h1 : childW σ σ.Φ e' h' g'
            ≤ (e' : ℤ) * σ.w (Bg j) + (j : ℤ) * (h' : ℤ) := hming j hjNg h0
        omega
      have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
      have hwgt : ω < σ.w (Bg j) := by
        have h2 : (e' : ℤ) * ω < (e' : ℤ) * σ.w (Bg j) := by omega
        exact lt_of_mul_lt_mul_left h2 he0.le
      exact ⟨v2gr_deep σ (ne_of_gt hwgt), Or.inr hwgt.le⟩
  have hDf : Bf j = 0 ∨ childW σ σ.Φ e' h' f
      ≤ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) := by
    rcases eq_or_ne (Bf j) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr (hminf j ?_ h0)
      by_contra hc
      exact h0 (hdevf.2.1 j (le_of_not_gt hc))
  by_cases hjf : Bf j ≠ 0 ∧ (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ)
      = childW σ σ.Φ e' h' f
  · -- f tied: sum slot tied with f's digit and weight
    obtain ⟨hf0, hfe⟩ := hjf
    obtain ⟨hgrg, hDg⟩ := hgdeep (σ.w (Bf j)) hfe
    have hgr := (v2gr_add σ hσ (Or.inr (le_refl (σ.w (Bf j)))) hDg).2
    rw [v2gr_eq σ hf0 rfl, hgrg, add_zero] at hgr
    have hgrne : v2gr σ (σ.w (Bf j)) (Bf j + Bg j) ≠ 0 := by
      rw [hgr]; exact σ.hRne _ hf0
    obtain ⟨hs0, hws⟩ := v2gr_spec σ hgrne
    have hRs : σ.R (Bf j + Bg j) = σ.R (Bf j) := by
      rw [← v2gr_eq σ hs0 hws]; exact hgr
    have hcds : v2dig σ (Bf j + Bg j) = v2dig σ (Bf j) := v2dig_of_Req σ hRs
    rw [if_pos ⟨hs0, by rw [hws]; exact hfe⟩, if_pos ⟨hf0, hfe⟩, hws, hcds]
  · -- f untied: the sum slot cannot be tied
    have hnotied : ¬((Bf j + Bg j) ≠ 0 ∧
        (e' : ℤ) * σ.w (Bf j + Bg j) + (j : ℤ) * (h' : ℤ)
          = childW σ σ.Φ e' h' f) := by
      rintro ⟨hs0, hse⟩
      obtain ⟨hgrg, hDg⟩ := hgdeep (σ.w (Bf j + Bg j)) hse
      have hgrf : v2gr σ (σ.w (Bf j + Bg j)) (Bf j) = 0 := by
        rcases eq_or_ne (Bf j) 0 with h0 | h0
        · rw [h0, v2gr_zero]
        · refine v2gr_deep σ (v2w_ne_of_slot σ he' hse ?_)
          intro hce
          exact hjf ⟨h0, hce⟩
      have hgr := (v2gr_add σ hσ (v2Deep_of_slot σ he' hse hDf) hDg).2
      rw [v2gr_eq σ hs0 rfl, hgrf, hgrg, add_zero] at hgr
      exact σ.hRne _ hs0 hgr
    rw [if_neg hnotied, if_neg hjf]

/-! #### the same-key Lemma DIV — the descent engine's `L3_DIV` REPLACED (the V2
obstruction kernel).  Weight facts = V1's exposed Q-ascent verbatim.  The residual
product law `R((a·b) %ₘ Φ) = R(a)·R(b)` by the `w(Φ·Q) ≥ w(R_dev)` trichotomy:
`Q = 0` is trivial; strict is parent `hRlt`; the TIE IS IMPOSSIBLE — `hStretch` on
`a, b, Q ∈ C` forces `σ.e ∣ σ.h`, so `σ.e = 1` (hcop), `σ.t = 0` (P2), `σ.s = 1`
(Bézout), and the parent `hRadd` identity `C(c_a c_b)·T0 = C(c_R)·T0 + C(c_Q)·T1`
pins the UNIT `c_Q` to the vanishing exponent-1 coefficient. -/

private lemma v2DIV (hσL : StageCoreL σ) (e' h' : ℕ) (s' t' : ℤ)
    (hrp : ReadPair σ e' h' s' t')
    (a b : Polynomial ℤ_[p]) (ha : a ≠ 0) (hb : b ≠ 0)
    (had : a.degree < σ.Φ.degree) (hbd : b.degree < σ.Φ.degree) :
    (a * b) %ₘ σ.Φ ≠ 0 ∧ σ.w ((a * b) %ₘ σ.Φ) = σ.w a + σ.w b ∧
      v2dig σ ((a * b) %ₘ σ.Φ) = v2dig σ a * v2dig σ b := by
  classical
  obtain ⟨-, -, -, hQA⟩ := V1_readWPack σ hσL e' h' s' t' hrp
  obtain ⟨⟨hRne, hRw⟩, hQdep⟩ := hQA a b ha hb had hbd
  refine ⟨hRne, hRw, ?_⟩
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hsplit : a * b = (a * b) %ₘ σ.Φ + σ.Φ * ((a * b) /ₘ σ.Φ) :=
    (Polynomial.modByMonic_add_div (a * b) σ.Φ).symm
  by_cases hQ0 : (a * b) /ₘ σ.Φ = 0
  · -- no quotient: the remainder IS the product
    have hR : (a * b) %ₘ σ.Φ = a * b := by
      conv_rhs => rw [hsplit]
      rw [hQ0, mul_zero, add_zero]
    rw [hR, v2dig_mul σ ha hb]
  · -- Q ≠ 0: the quotient slot sits weakly above (V1's Q-ascent, cleared by e′ ≥ 1)
    have hepos : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast hrp.1
    have hwQle : σ.w ((a * b) %ₘ σ.Φ) ≤ σ.w ((a * b) /ₘ σ.Φ) + (σ.h : ℤ) := by
      have h := hQdep hQ0
      have h2 : (e' : ℤ) * σ.w ((a * b) %ₘ σ.Φ)
          ≤ (e' : ℤ) * (σ.w ((a * b) /ₘ σ.Φ) + (σ.h : ℤ)) := by
        rw [mul_add]
        linarith
      exact le_of_mul_le_mul_left h2 hepos
    have hwPQ : σ.w (σ.Φ * ((a * b) /ₘ σ.Φ)) = σ.w ((a * b) /ₘ σ.Φ) + (σ.h : ℤ) := by
      rw [σ.hwmul _ _ hΦne hQ0, σ.hwΦ]
      ring
    have hle : σ.w ((a * b) %ₘ σ.Φ) ≤ σ.w (σ.Φ * ((a * b) /ₘ σ.Φ)) := by
      rw [hwPQ]; exact hwQle
    rcases lt_or_eq_of_le hle with hlt | heq
    · -- strictly deeper quotient: parent hRlt kills the Φ·Q half
      have hR : σ.R (a * b) = σ.R ((a * b) %ₘ σ.Φ) := by
        conv_lhs => rw [hsplit]
        exact σ.hRlt _ _ hRne (mul_ne_zero hΦne hQ0) (by rw [← hsplit]; exact hab) hlt
      rw [← v2dig_of_Req σ hR, v2dig_mul σ ha hb]
    · -- THE TIE IS IMPOSSIBLE (the regrade replacement for L3_DIV's cancellation branch)
      exfalso
      -- Q ∈ C: degree bookkeeping (deg(a·b) < 2·deg Φ)
      have hQnat : ((a * b) /ₘ σ.Φ).natDegree < σ.Φ.natDegree := by
        rw [Polynomial.natDegree_divByMonic (a * b) σ.hmonic]
        have h1 : a.natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree ha had
        have h2 : b.natDegree < σ.Φ.natDegree := Polynomial.natDegree_lt_natDegree hb hbd
        have h3 : (a * b).natDegree = a.natDegree + b.natDegree :=
          Polynomial.natDegree_mul ha hb
        have := σ.hdeg
        omega
      have hQd : ((a * b) /ₘ σ.Φ).degree < σ.Φ.degree := by
        rw [Polynomial.degree_eq_natDegree hQ0, Polynomial.degree_eq_natDegree hΦne]
        exact_mod_cast hQnat
      -- the weight tie forces σ.e ∣ σ.h through hStretch, hence e = 1, t = 0, s = 1
      have hweq : σ.w ((a * b) /ₘ σ.Φ) + (σ.h : ℤ) = σ.w a + σ.w b := by
        rw [← hwPQ, ← heq]
        exact hRw
      have hsa := σ.hStretch a ha had
      have hsb := σ.hStretch b hb hbd
      have hsQ := σ.hStretch _ hQ0 hQd
      rw [hsa, hsb, hsQ] at hweq
      have hEq : (σ.h : ℤ)
          = (σ.e : ℤ) * (σ.wPrev a + σ.wPrev b - σ.wPrev ((a * b) /ₘ σ.Φ)) := by
        linear_combination hweq
      have hdvd : (σ.e : ℤ) ∣ (σ.h : ℤ) := ⟨_, hEq⟩
      have hediv : σ.e ∣ σ.h := Int.natCast_dvd_natCast.mp hdvd
      have he1 : σ.e = 1 := (Nat.gcd_eq_left hediv).symm.trans σ.hcop
      have ht0 : σ.t = 0 := σ.he1t he1
      have hs1 : σ.s = 1 := by
        have hbz := σ.hbez
        rw [show (σ.e : ℤ) = 1 by exact_mod_cast he1, ht0] at hbz
        linarith
      -- the three hS5 monomials, at their forced exponents 0 / 0 / 1
      obtain ⟨ca, -, hca⟩ := v2dig_unit σ ha had
      obtain ⟨cb, -, hcb⟩ := v2dig_unit σ hb hbd
      obtain ⟨cR, -, hcR⟩ := v2dig_unit σ hRne (Polynomial.degree_modByMonic_lt _ σ.hmonic)
      obtain ⟨cQ, -, hcQ⟩ := v2dig_unit σ hQ0 hQd
      have hRab' : σ.R (a * b)
          = LaurentPolynomial.C ((ca : ↥σ.K) * (cb : ↥σ.K)) * LaurentPolynomial.T 0 := by
        have he0 : -σ.t * σ.wPrev a + -σ.t * σ.wPrev b = 0 := by rw [ht0]; ring
        rw [σ.hRmul a b ha hb, hca, hcb, mul_mul_mul_comm, ← map_mul,
          ← LaurentPolynomial.T_add, he0]
      have hRdev' : σ.R ((a * b) %ₘ σ.Φ)
          = LaurentPolynomial.C (cR : ↥σ.K) * LaurentPolynomial.T 0 := by
        have he0 : -σ.t * σ.wPrev ((a * b) %ₘ σ.Φ) = 0 := by rw [ht0]; ring
        rw [hcR, he0]
      have hPQ' : σ.R (σ.Φ * ((a * b) /ₘ σ.Φ))
          = LaurentPolynomial.C (cQ : ↥σ.K) * LaurentPolynomial.T 1 := by
        have he1' : σ.s + -σ.t * σ.wPrev ((a * b) /ₘ σ.Φ) = 1 := by rw [ht0, hs1]; ring
        rw [σ.hRmul _ _ hΦne hQ0, σ.hRΦ, hcQ, mul_left_comm,
          ← LaurentPolynomial.T_add, he1']
      -- parent hRadd at the tie (both slots at the product weight, no jump)
      have hadd : σ.R (a * b)
          = σ.R ((a * b) %ₘ σ.Φ) + σ.R (σ.Φ * ((a * b) /ₘ σ.Φ)) := by
        conv_lhs => rw [hsplit]
        refine σ.hRadd _ _ hRne (mul_ne_zero hΦne hQ0)
          (by rw [← hsplit]; exact hab) heq ?_
        rw [← hsplit, σ.hwmul a b ha hb, hRw]
      rw [hRab', hRdev', hPQ'] at hadd
      rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
        ← LaurentPolynomial.single_eq_C_mul_T] at hadd
      have hadd' : (Finsupp.single (0 : ℤ) ((ca : ↥σ.K) * (cb : ↥σ.K)) : ℤ →₀ ↥σ.K)
          = Finsupp.single (0 : ℤ) (cR : ↥σ.K) + Finsupp.single (1 : ℤ) (cQ : ↥σ.K) :=
        hadd
      have hc1 := DFunLike.congr_fun hadd' 1
      rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
        Finsupp.single_apply] at hc1
      norm_num at hc1
      exact cQ.ne_zero hc1.symm

/-! #### hRmul — the bilinear slot expansion through `v2DIV` (blueprint §10 V2; the V8
route with the same-key kernel).  Route: the product development `Cdev` by convolution +
monic division; per-diagonal, the graded residue of `Cdev m` at the level forced by
V1's childW-multiplicativity is EXACTLY the sum of the tied-pair remainder residues
(`v2DIV` weights + ReadPair steepness for the carried quotients); evaluation at `T = 1`
turns this into the Laurent product's convolution coefficient, with a vanishing
coefficient = the SAME zero on both sides (a tied sum-slot with zero digit would
contradict the hS5 digit unit). -/
private lemma v2Rc_mulLaw (hσ : StageCore σ) (hσL : StageCoreL σ)
    (e' h' : ℕ) (s' t' : ℤ) (hrp : ReadPair σ e' h' s' t')
    (hSMW : IsSlotMinWeight (childW σ σ.Φ e' h') σ.Φ e' h' σ.w)
    (hWmul : ∀ f g, f ≠ 0 → g ≠ 0 →
        childW σ σ.Φ e' h' (f * g) = childW σ σ.Φ e' h' f + childW σ σ.Φ e' h' g)
    {f g' : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg' : g' ≠ 0) :
    v2Rc σ e' h' s' t' (f * g')
      = v2Rc σ e' h' s' t' f * v2Rc σ e' h' s' t' g' := by
  classical
  have hfg : f * g' ≠ 0 := mul_ne_zero hf hg'
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have he' : 1 ≤ e' := hrp.1
  have hiaug : (e' : ℤ) * σ.w σ.Φ < (h' : ℤ) := by
    rw [σ.hwΦ]
    exact hrp.2.2.2.2.2
  have hWmulfg : childW σ σ.Φ e' h' (f * g')
      = childW σ σ.Φ e' h' f + childW σ σ.Φ e' h' g' := hWmul f g' hf hg'
  have he0 : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
  obtain ⟨Bf, Nf, hdevf⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg f
  obtain ⟨Bg, Ng, hdevg⟩ := L0_FactA_exists σ.Φ σ.hmonic σ.hdeg g'
  obtain ⟨hminf, -⟩ := hSMW f Bf Nf hf hdevf
  obtain ⟨hming, -⟩ := hSMW g' Bg Ng hg' hdevg
  have hBfz : ∀ j, Nf ≤ j → Bf j = 0 := hdevf.2.1
  have hBgz : ∀ k, Ng ≤ k → Bg k = 0 := hdevg.2.1
  have hNf1 : 1 ≤ Nf := by
    by_contra hcon
    have h0 : Nf = 0 := by omega
    have := hdevf.2.2
    rw [h0] at this
    simp only [Finset.range_zero, Finset.sum_empty] at this
    exact hf this
  have hNg1 : 1 ≤ Ng := by
    by_contra hcon
    have h0 : Ng = 0 := by omega
    have := hdevg.2.2
    rw [h0] at this
    simp only [Finset.range_zero, Finset.sum_empty] at this
    exact hg' this
  -- ===== the generating polynomials and the convolution =====
  set FF : Polynomial (Polynomial ℤ_[p]) :=
    ∑ j ∈ Finset.range Nf, Polynomial.C (Bf j) * Polynomial.X ^ j with hFFdef
  set GG : Polynomial (Polynomial ℤ_[p]) :=
    ∑ k ∈ Finset.range Ng, Polynomial.C (Bg k) * Polynomial.X ^ k with hGGdef
  have hFFc : ∀ m, FF.coeff m = Bf m := by
    intro m
    rw [hFFdef, Polynomial.finsetSum_coeff]
    by_cases hm : m < Nf
    · rw [Finset.sum_eq_single m]
      · simp
      · intro j hj hjm
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjm]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hm) hnot
    · rw [hBfz m (not_lt.mp hm)]
      apply Finset.sum_eq_zero
      intro j hj
      have hmj : m ≠ j := by
        have := Finset.mem_range.mp hj; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hmj]
  have hGGc : ∀ m, GG.coeff m = Bg m := by
    intro m
    rw [hGGdef, Polynomial.finsetSum_coeff]
    by_cases hm : m < Ng
    · rw [Finset.sum_eq_single m]
      · simp
      · intro k hk hkm
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hkm]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hm) hnot
    · rw [hBgz m (not_lt.mp hm)]
      apply Finset.sum_eq_zero
      intro k hk
      have hmk : m ≠ k := by
        have := Finset.mem_range.mp hk; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hmk]
  have hFFeval : Polynomial.eval σ.Φ FF = f := by
    rw [hFFdef, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact hdevf.2.2.symm
  have hGGeval : Polynomial.eval σ.Φ GG = g' := by
    rw [hGGdef, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact hdevg.2.2.symm
  have hFFnd : FF.natDegree ≤ Nf - 1 := by
    rw [hFFdef]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    have := Finset.mem_range.mp hj
    omega
  have hGGnd : GG.natDegree ≤ Ng - 1 := by
    rw [hGGdef]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    have := Finset.mem_range.mp hk
    omega
  set H : Polynomial (Polynomial ℤ_[p]) := FF * GG with hHdef
  have hHnd : H.natDegree ≤ Nf + Ng - 2 := by
    rw [hHdef]
    refine le_trans Polynomial.natDegree_mul_le ?_
    omega
  have hHcoeff : ∀ m, H.coeff m = ∑ jk ∈ Finset.antidiagonal m, Bf jk.1 * Bg jk.2 := by
    intro m
    rw [hHdef, Polynomial.coeff_mul]
    exact Finset.sum_congr rfl (fun jk _ => by rw [hFFc, hGGc])
  have hHvan : ∀ m, Nf + Ng - 1 ≤ m → H.coeff m = 0 := by
    intro m hm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hprodsum : f * g' = ∑ m ∈ Finset.range (Nf + Ng), H.coeff m * σ.Φ ^ m := by
    rw [← hFFeval, ← hGGeval, ← Polynomial.eval_mul, ← hHdef]
    exact Polynomial.eval_eq_sum_range' (by omega) σ.Φ
  -- ===== the development of f·g': remainders on the diagonal, carried quotients shifted =====
  set Cdev : ℕ → Polynomial ℤ_[p] := fun m =>
    H.coeff m %ₘ σ.Φ + (if m = 0 then 0 else H.coeff (m - 1) /ₘ σ.Φ) with hCdef
  have hCdev_eq : ∀ m, Cdev m
      = H.coeff m %ₘ σ.Φ + (if m = 0 then 0 else H.coeff (m - 1) /ₘ σ.Φ) := fun m => rfl
  have hBfnd : ∀ j, (Bf j).natDegree ≤ σ.Φ.natDegree - 1 := by
    intro j
    by_cases hz : Bf j = 0
    · rw [hz]; simp
    · have := Polynomial.natDegree_lt_natDegree hz (hdevf.1 j)
      omega
  have hBgnd : ∀ k, (Bg k).natDegree ≤ σ.Φ.natDegree - 1 := by
    intro k
    by_cases hz : Bg k = 0
    · rw [hz]; simp
    · have := Polynomial.natDegree_lt_natDegree hz (hdevg.1 k)
      omega
  have hHcnd : ∀ m, (H.coeff m).natDegree ≤ 2 * σ.Φ.natDegree - 2 := by
    intro m
    rw [hHcoeff m]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro jk hjk
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 := hBfnd jk.1
    have h2 := hBgnd jk.2
    omega
  have hQdeg : ∀ m, (H.coeff m /ₘ σ.Φ).degree < σ.Φ.degree := by
    intro m
    have hnd : (H.coeff m /ₘ σ.Φ).natDegree < σ.Φ.natDegree := by
      rw [Polynomial.natDegree_divByMonic _ σ.hmonic]
      have h2 := hHcnd m
      have := σ.hdeg
      omega
    calc (H.coeff m /ₘ σ.Φ).degree
        ≤ ((H.coeff m /ₘ σ.Φ).natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < (σ.Φ.natDegree : WithBot ℕ) := by exact_mod_cast hnd
      _ = σ.Φ.degree := (Polynomial.degree_eq_natDegree hΦne).symm
  have hCdeg : ∀ m, (Cdev m).degree < σ.Φ.degree := by
    intro m
    rw [hCdev_eq m]
    by_cases hm : m = 0
    · rw [if_pos hm, add_zero]
      exact Polynomial.degree_modByMonic_lt _ σ.hmonic
    · rw [if_neg hm]
      refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
      · exact Polynomial.degree_modByMonic_lt _ σ.hmonic
      · exact hQdeg (m - 1)
  have hCvan : ∀ m, Nf + Ng ≤ m → Cdev m = 0 := by
    intro m hm
    rw [hCdev_eq m]
    have hm0 : m ≠ 0 := by omega
    rw [if_neg hm0, hHvan m (by omega), hHvan (m - 1) (by omega),
      Polynomial.zero_modByMonic, Polynomial.zero_divByMonic, add_zero]
  have hCsum : f * g' = ∑ m ∈ Finset.range (Nf + Ng), Cdev m * σ.Φ ^ m := by
    obtain ⟨N₁, hN₁⟩ : ∃ N₁, Nf + Ng = N₁ + 1 := ⟨Nf + Ng - 1, by omega⟩
    have hz2 : H.coeff N₁ = 0 := hHvan N₁ (by omega)
    have hsplit : ∀ m, Cdev m * σ.Φ ^ m
        = (H.coeff m %ₘ σ.Φ) * σ.Φ ^ m
          + (if m = 0 then 0 else (H.coeff (m - 1) /ₘ σ.Φ) * σ.Φ ^ m) := by
      intro m
      rw [hCdev_eq m]
      by_cases hm : m = 0
      · simp only [if_pos hm]
        rw [add_zero, add_zero]
      · simp only [if_neg hm]
        rw [add_mul]
    have hshift : (∑ m ∈ Finset.range (Nf + Ng),
          (if m = 0 then 0 else (H.coeff (m - 1) /ₘ σ.Φ) * σ.Φ ^ m))
        = ∑ m ∈ Finset.range (Nf + Ng), (H.coeff m /ₘ σ.Φ) * σ.Φ ^ (m + 1) := by
      rw [hN₁]
      rw [Finset.sum_range_succ'
        (fun m => if m = 0 then 0 else (H.coeff (m - 1) /ₘ σ.Φ) * σ.Φ ^ m) N₁]
      rw [Finset.sum_range_succ (fun m => (H.coeff m /ₘ σ.Φ) * σ.Φ ^ (m + 1)) N₁]
      rw [if_pos rfl, add_zero, hz2, Polynomial.zero_divByMonic, zero_mul, add_zero]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]
    rw [hprodsum]
    have e1 : ∑ m ∈ Finset.range (Nf + Ng), Cdev m * σ.Φ ^ m
        = (∑ m ∈ Finset.range (Nf + Ng), (H.coeff m %ₘ σ.Φ) * σ.Φ ^ m)
          + ∑ m ∈ Finset.range (Nf + Ng),
              (if m = 0 then 0 else (H.coeff (m - 1) /ₘ σ.Φ) * σ.Φ ^ m) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => hsplit m)
    rw [e1, hshift, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    conv_lhs => rw [← Polynomial.modByMonic_add_div (H.coeff m) σ.Φ]
    ring
  have hdevC : IsDevelopment σ.Φ (f * g') Cdev (Nf + Ng) := ⟨hCdeg, hCvan, hCsum⟩
  -- ===== the same-key Lemma DIV wrapper (weight + digit) =====
  have hDIV : ∀ (a b : Polynomial ℤ_[p]), a ≠ 0 → b ≠ 0 →
      a.degree < σ.Φ.degree → b.degree < σ.Φ.degree →
      (a * b) %ₘ σ.Φ ≠ 0 ∧ σ.w ((a * b) %ₘ σ.Φ) = σ.w a + σ.w b ∧
        v2dig σ ((a * b) %ₘ σ.Φ) = v2dig σ a * v2dig σ b :=
    fun a b ha hb had hbd => v2DIV σ hσL e' h' s' t' hrp a b ha hb had hbd
  -- ===== per-pair slot arithmetic =====
  have hpairw : ∀ (m' : ℕ) (jk : ℕ × ℕ), jk.1 + jk.2 = m' → Bf jk.1 ≠ 0 → Bg jk.2 ≠ 0 →
      childW σ σ.Φ e' h' f + childW σ σ.Φ e' h' g'
        ≤ (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) + (m' : ℤ) * (h' : ℤ) := by
    intro m' jk hd hBf hBg
    have hjNf : jk.1 < Nf := by
      by_contra hc; exact hBf (hBfz _ (le_of_not_gt hc))
    have hkNg : jk.2 < Ng := by
      by_contra hc; exact hBg (hBgz _ (le_of_not_gt hc))
    have h1 : childW σ σ.Φ e' h' f
        ≤ (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) := hminf jk.1 hjNf hBf
    have h2 : childW σ σ.Φ e' h' g'
        ≤ (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) := hming jk.2 hkNg hBg
    have hcast : (jk.1 : ℤ) + (jk.2 : ℤ) = (m' : ℤ) := by exact_mod_cast hd
    have hexp : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2))
        = (e' : ℤ) * σ.w (Bf jk.1) + (e' : ℤ) * σ.w (Bg jk.2) := by ring
    have hch : (jk.1 : ℤ) * (h' : ℤ) + (jk.2 : ℤ) * (h' : ℤ) = (m' : ℤ) * (h' : ℤ) := by
      rw [← add_mul, hcast]
    linarith
  have hpair_tie : ∀ (m' : ℕ) (jk : ℕ × ℕ), jk.1 + jk.2 = m' → Bf jk.1 ≠ 0 → Bg jk.2 ≠ 0 →
      ∀ ω : ℤ, (e' : ℤ) * ω + (m' : ℤ) * (h' : ℤ)
          = childW σ σ.Φ e' h' f + childW σ σ.Φ e' h' g' →
      (σ.w (Bf jk.1) + σ.w (Bg jk.2) = ω
        ↔ ((e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f
           ∧ (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ)
              = childW σ σ.Φ e' h' g')) := by
    intro m' jk hd hBf hBg ω hω
    have hjNf : jk.1 < Nf := by
      by_contra hc; exact hBf (hBfz _ (le_of_not_gt hc))
    have hkNg : jk.2 < Ng := by
      by_contra hc; exact hBg (hBgz _ (le_of_not_gt hc))
    have h1 : childW σ σ.Φ e' h' f
        ≤ (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) := hminf jk.1 hjNf hBf
    have h2 : childW σ σ.Φ e' h' g'
        ≤ (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) := hming jk.2 hkNg hBg
    have hcast : (jk.1 : ℤ) + (jk.2 : ℤ) = (m' : ℤ) := by exact_mod_cast hd
    have hexp : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2))
        = (e' : ℤ) * σ.w (Bf jk.1) + (e' : ℤ) * σ.w (Bg jk.2) := by ring
    have hch : (jk.1 : ℤ) * (h' : ℤ) + (jk.2 : ℤ) * (h' : ℤ) = (m' : ℤ) * (h' : ℤ) := by
      rw [← add_mul, hcast]
    constructor
    · intro hsum
      have hkey : (e' : ℤ) * σ.w (Bf jk.1) + (e' : ℤ) * σ.w (Bg jk.2)
          + (m' : ℤ) * (h' : ℤ)
          = childW σ σ.Φ e' h' f + childW σ σ.Φ e' h' g' := by
        rw [← hexp, hsum]
        exact hω
      constructor
      · linarith
      · linarith
    · rintro ⟨ht1, ht2⟩
      have hkey : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) = (e' : ℤ) * ω := by
        linarith
      exact mul_left_cancel₀ he0.ne' hkey
  -- ===== the carried quotient is strictly deep (ReadPair steepness = (I-aug)) =====
  have hQdeep : ∀ (m' : ℕ) (ω : ℤ),
      (e' : ℤ) * ω + ((m' : ℤ) + 1) * (h' : ℤ)
        = childW σ σ.Φ e' h' f + childW σ σ.Φ e' h' g' →
      H.coeff m' /ₘ σ.Φ ≠ 0 → ω < σ.w (H.coeff m' /ₘ σ.Φ) := by
    intro m' ω hω hy
    have hbound : ∀ jk ∈ Finset.antidiagonal m', Bf jk.1 * Bg jk.2 = 0 ∨
        ω + σ.w σ.Φ + 1 ≤ σ.w (Bf jk.1 * Bg jk.2) := by
      intro jk hjk
      by_cases hPz : Bf jk.1 * Bg jk.2 = 0
      · exact Or.inl hPz
      right
      have hBf := left_ne_zero_of_mul hPz
      have hBg := right_ne_zero_of_mul hPz
      have hp := hpairw m' jk (Finset.mem_antidiagonal.mp hjk) hBf hBg
      have hwP : σ.w (Bf jk.1 * Bg jk.2) = σ.w (Bf jk.1) + σ.w (Bg jk.2) :=
        σ.hwmul _ _ hBf hBg
      rw [hwP]
      by_contra hcon
      push_neg at hcon
      have hS : σ.w (Bf jk.1) + σ.w (Bg jk.2) ≤ ω + σ.w σ.Φ := by omega
      have hmul : (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2))
          ≤ (e' : ℤ) * (ω + σ.w σ.Φ) :=
        mul_le_mul_of_nonneg_left hS (Int.natCast_nonneg e')
      have hexp : (e' : ℤ) * (ω + σ.w σ.Φ) = (e' : ℤ) * ω + (e' : ℤ) * σ.w σ.Φ := by
        ring
      have hia : (e' : ℤ) * σ.w σ.Φ < (h' : ℤ) := hiaug
      linarith
    have hconv_ne : H.coeff m' ≠ 0 := fun h0 => hy (by rw [h0, Polynomial.zero_divByMonic])
    have hwconv : ω + σ.w σ.Φ + 1 ≤ σ.w (H.coeff m') := by
      rw [hHcoeff m']
      refine v2sum_w_ge σ _ _ _ (fun jk hjk hne0 => (hbound jk hjk).resolve_left hne0)
        (by rw [← hHcoeff m']; exact hconv_ne)
    have hyΦ : σ.Φ * (H.coeff m' /ₘ σ.Φ) = H.coeff m' + -(H.coeff m' %ₘ σ.Φ) := by
      have hmd := Polynomial.modByMonic_add_div (H.coeff m') σ.Φ
      linear_combination hmd
    have hΦyne : σ.Φ * (H.coeff m' /ₘ σ.Φ) ≠ 0 := mul_ne_zero hΦne hy
    have hwΦy : ω + σ.w σ.Φ + 1 ≤ σ.w (σ.Φ * (H.coeff m' /ₘ σ.Φ)) := by
      rw [hyΦ]
      by_cases hrz : H.coeff m' %ₘ σ.Φ = 0
      · rw [hrz, neg_zero, add_zero]; exact hwconv
      · have hrw : ω + σ.w σ.Φ + 1 ≤ σ.w (H.coeff m' %ₘ σ.Φ) := by
          have hremsum : H.coeff m' %ₘ σ.Φ
              = ∑ jk ∈ Finset.antidiagonal m', (Bf jk.1 * Bg jk.2) %ₘ σ.Φ := by
            rw [hHcoeff m']
            exact v2sum_modByMonic σ.hmonic _ _
          rw [hremsum]
          refine v2sum_w_ge σ _ _ _ ?_ (by rw [← hremsum]; exact hrz)
          intro jk hjk hne0
          have hPne : Bf jk.1 * Bg jk.2 ≠ 0 := by
            intro h0; rw [h0, Polynomial.zero_modByMonic] at hne0; exact hne0 rfl
          have hBf := left_ne_zero_of_mul hPne
          have hBg := right_ne_zero_of_mul hPne
          have hw_eq := (hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)).2.1
          rw [hw_eq]
          have hb := (hbound jk hjk).resolve_left hPne
          rw [σ.hwmul _ _ hBf hBg] at hb
          exact hb
        have hnegne : -(H.coeff m' %ₘ σ.Φ) ≠ 0 := neg_ne_zero.mpr hrz
        have hsumne : H.coeff m' + -(H.coeff m' %ₘ σ.Φ) ≠ 0 := by
          rw [← hyΦ]; exact hΦyne
        have hult := σ.hwult _ _ hconv_ne hnegne hsumne
        rw [v2w_neg σ _ hrz] at hult
        exact le_trans (le_min hwconv hrw) hult
    have hmulw := σ.hwmul σ.Φ (H.coeff m' /ₘ σ.Φ) hΦne hy
    rw [hmulw] at hwΦy
    omega
  -- ===== the graded slot computation: grw of Cdev m = the tied-pair residue sum =====
  have hgrC : ∀ (m : ℕ) (ω : ℤ),
      (e' : ℤ) * ω + (m : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f + childW σ σ.Φ e' h' g' →
      v2gr σ ω (Cdev m)
        = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
            ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g'))).filter
            (fun jk => jk.1 + jk.2 = m),
          σ.R ((Bf jk.1 * Bg jk.2) %ₘ σ.Φ) := by
    intro m ω hω
    have hCm : Cdev m = (∑ jk ∈ Finset.antidiagonal m, (Bf jk.1 * Bg jk.2) %ₘ σ.Φ)
        + (if m = 0 then 0 else H.coeff (m - 1) /ₘ σ.Φ) := by
      rw [hCdev_eq m, hHcoeff m, v2sum_modByMonic σ.hmonic]
    have hQpack : v2Deep σ ω (if m = 0 then 0 else H.coeff (m - 1) /ₘ σ.Φ)
        ∧ v2gr σ ω (if m = 0 then 0 else H.coeff (m - 1) /ₘ σ.Φ) = 0 := by
      by_cases hm0 : m = 0
      · rw [if_pos hm0]
        exact ⟨Or.inl rfl, v2gr_zero σ ω⟩
      · rw [if_neg hm0]
        by_cases hy : H.coeff (m - 1) /ₘ σ.Φ = 0
        · rw [hy]
          exact ⟨Or.inl rfl, v2gr_zero σ ω⟩
        · have hω' : (e' : ℤ) * ω + (((m - 1 : ℕ) : ℤ) + 1) * (h' : ℤ)
              = childW σ σ.Φ e' h' f + childW σ σ.Φ e' h' g' := by
            have hc : ((m - 1 : ℕ) : ℤ) + 1 = (m : ℤ) := by omega
            rw [hc]; exact hω
          have hlt := hQdeep (m - 1) ω hω' hy
          exact ⟨Or.inr hlt.le, v2gr_deep σ (ne_of_gt hlt)⟩
    have hDeepR : ∀ jk ∈ Finset.antidiagonal m,
        v2Deep σ ω ((Bf jk.1 * Bg jk.2) %ₘ σ.Φ) := by
      intro jk hjk
      by_cases hPz : Bf jk.1 * Bg jk.2 = 0
      · rw [hPz, Polynomial.zero_modByMonic]
        exact Or.inl rfl
      · have hBf := left_ne_zero_of_mul hPz
        have hBg := right_ne_zero_of_mul hPz
        obtain ⟨hrne, hrw, -⟩ := hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)
        right
        rw [hrw]
        have hp := hpairw m jk (Finset.mem_antidiagonal.mp hjk) hBf hBg
        have h2 : (e' : ℤ) * ω ≤ (e' : ℤ) * (σ.w (Bf jk.1) + σ.w (Bg jk.2)) := by
          linarith
        exact le_of_mul_le_mul_left h2 he0
    obtain ⟨hDsum, hEsum⟩ := v2gr_sum σ hσ (Finset.antidiagonal m) _ hDeepR
    have hEtot := (v2gr_add σ hσ hDsum hQpack.1).2
    rw [hCm, hEtot, hEsum, hQpack.2, add_zero]
    have hstep1 : ∑ jk ∈ Finset.antidiagonal m, v2gr σ ω ((Bf jk.1 * Bg jk.2) %ₘ σ.Φ)
        = ∑ jk ∈ (Finset.antidiagonal m).filter
            (fun jk => (Bf jk.1 ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)
            ∧ (Bg jk.2 ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g')),
            v2gr σ ω ((Bf jk.1 * Bg jk.2) %ₘ σ.Φ) := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro jk hjk hne
      obtain ⟨hrne, hrw⟩ := v2gr_spec σ hne
      have hPne : Bf jk.1 * Bg jk.2 ≠ 0 := by
        intro h0; rw [h0, Polynomial.zero_modByMonic] at hrne; exact hrne rfl
      have hBf := left_ne_zero_of_mul hPne
      have hBg := right_ne_zero_of_mul hPne
      obtain ⟨-, hwr, -⟩ := hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)
      have hsum : σ.w (Bf jk.1) + σ.w (Bg jk.2) = ω := by rw [← hwr]; exact hrw
      have hti := (hpair_tie m jk (Finset.mem_antidiagonal.mp hjk) hBf hBg ω hω).mp hsum
      exact ⟨⟨hBf, hti.1⟩, ⟨hBg, hti.2⟩⟩
    have hstep2 : ∀ jk ∈ (Finset.antidiagonal m).filter
        (fun jk => (Bf jk.1 ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf jk.1) + (jk.1 : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)
        ∧ (Bg jk.2 ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg jk.2) + (jk.2 : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g')),
        v2gr σ ω ((Bf jk.1 * Bg jk.2) %ₘ σ.Φ) = σ.R ((Bf jk.1 * Bg jk.2) %ₘ σ.Φ) := by
      intro jk hjk
      rw [Finset.mem_filter] at hjk
      obtain ⟨hjkd, ⟨hBf, ht1⟩, ⟨hBg, ht2⟩⟩ := hjk
      obtain ⟨hrne, hrw, -⟩ := hDIV (Bf jk.1) (Bg jk.2) hBf hBg (hdevf.1 jk.1) (hdevg.1 jk.2)
      have hsum : σ.w (Bf jk.1) + σ.w (Bg jk.2) = ω :=
        (hpair_tie m jk (Finset.mem_antidiagonal.mp hjkd) hBf hBg ω hω).mpr ⟨ht1, ht2⟩
      exact v2gr_eq σ hrne (by rw [hrw]; exact hsum)
    rw [hstep1, Finset.sum_congr rfl hstep2]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    apply Finset.ext
    intro jk
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_product,
      Finset.mem_range]
    constructor
    · rintro ⟨hd, ⟨hBf, ht1⟩, ⟨hBg, ht2⟩⟩
      have hjNf : jk.1 < Nf := by
        by_contra hc; exact hBf (hBfz _ (le_of_not_gt hc))
      have hkNg : jk.2 < Ng := by
        by_contra hc; exact hBg (hBgz _ (le_of_not_gt hc))
      exact ⟨⟨⟨hjNf, hBf, ht1⟩, ⟨hkNg, hBg, ht2⟩⟩, hd⟩
    · rintro ⟨⟨⟨hjNf, hBf, ht1⟩, ⟨hkNg, hBg, ht2⟩⟩, hd⟩
      exact ⟨hd, ⟨hBf, ht1⟩, ⟨hBg, ht2⟩⟩
  -- ===== final assembly: both sides as fiberwise sums over the diagonals =====
  rw [v2Rc_eq σ e' h' s' t' hfg hdevC,
    v2Rc_eq σ e' h' s' t' hf hdevf,
    v2Rc_eq σ e' h' s' t' hg' hdevg, hWmulfg]
  unfold v2dsum
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  have hmaps : ∀ jk ∈ ((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
        (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
      ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
        (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g')),
      jk.1 + jk.2 ∈ Finset.range (Nf + Ng) := by
    intro jk hjk
    rw [Finset.mem_product] at hjk
    obtain ⟨h1, h2⟩ := hjk
    rw [Finset.mem_filter, Finset.mem_range] at h1 h2
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  show (if Cdev m ≠ 0 ∧ (e' : ℤ) * σ.w (Cdev m) + (m : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f + childW σ σ.Φ e' h' g'
      then LaurentPolynomial.C (v2dig σ (Cdev m)) *
        LaurentPolynomial.T ((m : ℤ) * s' - t' * σ.w (Cdev m))
      else 0)
    = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
      (LaurentPolynomial.C (v2dig σ (Bf jk.1)) *
          LaurentPolynomial.T ((jk.1 : ℤ) * s' - t' * σ.w (Bf jk.1))) *
        (LaurentPolynomial.C (v2dig σ (Bg jk.2)) *
          LaurentPolynomial.T ((jk.2 : ℤ) * s' - t' * σ.w (Bg jk.2)))
  rcases Finset.eq_empty_or_nonempty ((((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
      (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
    ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
      (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g'))).filter
    (fun jk => jk.1 + jk.2 = m)) with hFIB | hFIB
  · -- empty fiber: a tied sum-slot would have zero graded residue — impossible
    rw [hFIB, Finset.sum_empty, if_neg ?_]
    rintro ⟨hs0, hse⟩
    have hgr := hgrC m (σ.w (Cdev m)) hse
    rw [hFIB, Finset.sum_empty, v2gr_eq σ hs0 rfl] at hgr
    exact σ.hRne _ hs0 hgr
  · -- nonempty fiber: constant weight-sum ω₀ and position across the fiber
    obtain ⟨jk₀, hjk₀⟩ := hFIB
    have hjk₀' := hjk₀
    rw [Finset.mem_filter, Finset.mem_product] at hjk₀'
    obtain ⟨⟨hj₀mem, hk₀mem⟩, hd₀⟩ := hjk₀'
    rw [Finset.mem_filter, Finset.mem_range] at hj₀mem hk₀mem
    obtain ⟨hj₀Nf, hBf₀, ht₀f⟩ := hj₀mem
    obtain ⟨hk₀Ng, hBg₀, ht₀g⟩ := hk₀mem
    have hω₀ : (e' : ℤ) * (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2)) + (m : ℤ) * (h' : ℤ)
        = childW σ σ.Φ e' h' f + childW σ σ.Φ e' h' g' := by
      have hcast : (jk₀.1 : ℤ) + (jk₀.2 : ℤ) = (m : ℤ) := by exact_mod_cast hd₀
      have hexp : (e' : ℤ) * (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2))
          = (e' : ℤ) * σ.w (Bf jk₀.1) + (e' : ℤ) * σ.w (Bg jk₀.2) := by ring
      have hch : (jk₀.1 : ℤ) * (h' : ℤ) + (jk₀.2 : ℤ) * (h' : ℤ)
          = (m : ℤ) * (h' : ℤ) := by
        rw [← add_mul, hcast]
      linarith
    -- fiberwise constancy of the weight sum
    have hwconst : ∀ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
        σ.w (Bf jk.1) + σ.w (Bg jk.2) = σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2) := by
      intro jk hjk
      rw [Finset.mem_filter, Finset.mem_product] at hjk
      obtain ⟨⟨hjmem, hkmem⟩, hd⟩ := hjk
      rw [Finset.mem_filter, Finset.mem_range] at hjmem hkmem
      exact (hpair_tie m jk hd hjmem.2.1 hkmem.2.1 _ hω₀).mpr ⟨hjmem.2.2, hkmem.2.2⟩
    -- the RHS fiber sum collapses to C (digit convolution) · T (forced position)
    have hRHS : (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
      (LaurentPolynomial.C (v2dig σ (Bf jk.1)) *
          LaurentPolynomial.T ((jk.1 : ℤ) * s' - t' * σ.w (Bf jk.1))) *
        (LaurentPolynomial.C (v2dig σ (Bg jk.2)) *
          LaurentPolynomial.T ((jk.2 : ℤ) * s' - t' * σ.w (Bg jk.2))))
      = LaurentPolynomial.C (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          v2dig σ (Bf jk.1) * v2dig σ (Bg jk.2)) *
        LaurentPolynomial.T ((m : ℤ) * s'
          - t' * (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2))) := by
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun jk hjk => ?_)
      have hw := hwconst jk hjk
      have hd : jk.1 + jk.2 = m := by
        rw [Finset.mem_filter] at hjk
        exact hjk.2
      have hcast : (jk.1 : ℤ) + (jk.2 : ℤ) = (m : ℤ) := by exact_mod_cast hd
      have hcs : (jk.1 : ℤ) * s' + (jk.2 : ℤ) * s' = (m : ℤ) * s' := by
        rw [← add_mul, hcast]
      rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add]
      congr 2
      rw [← hw]
      linarith
    rw [hRHS]
    -- the digit bridge: T = 1 evaluation of the tied residue sum = the digit convolution
    have hevalS : v2ev σ
        (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          σ.R ((Bf jk.1 * Bg jk.2) %ₘ σ.Φ))
        = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
            (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
          ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
            (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g'))).filter
          (fun jk => jk.1 + jk.2 = m),
          v2dig σ (Bf jk.1) * v2dig σ (Bg jk.2) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun jk hjk => ?_)
      rw [Finset.mem_filter, Finset.mem_product] at hjk
      obtain ⟨⟨hjmem, hkmem⟩, -⟩ := hjk
      rw [Finset.mem_filter] at hjmem hkmem
      have hdig := (hDIV (Bf jk.1) (Bg jk.2) hjmem.2.1 hkmem.2.1
        (hdevf.1 jk.1) (hdevg.1 jk.2)).2.2
      exact hdig
    have hgr := hgrC m (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2)) hω₀
    by_cases hS : (∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
          (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
        ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
          (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g'))).filter
        (fun jk => jk.1 + jk.2 = m),
        v2dig σ (Bf jk.1) * v2dig σ (Bg jk.2)) = 0
    · -- vanishing convolution coefficient: BOTH sides are the same zero
      rw [hS, map_zero, zero_mul, if_neg ?_]
      rintro ⟨hs0, hse⟩
      have hws : σ.w (Cdev m) = σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2) :=
        v2w_eq_of_slot σ he' hω₀ hse
      have hRs := hgr
      rw [v2gr_eq σ hs0 hws] at hRs
      refine v2dig_ne σ hs0 (hCdeg m) ?_
      rw [v2dig_def, hRs, hevalS]
      exact hS
    · -- surviving coefficient: the sum slot is tied with digit = the convolution
      have hgrne : v2gr σ (σ.w (Bf jk₀.1) + σ.w (Bg jk₀.2)) (Cdev m) ≠ 0 := by
        rw [hgr]
        intro h0
        apply hS
        rw [← hevalS, h0, map_zero]
      obtain ⟨hs0, hws⟩ := v2gr_spec σ hgrne
      have hRs : σ.R (Cdev m)
          = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
            ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g'))).filter
            (fun jk => jk.1 + jk.2 = m),
            σ.R ((Bf jk.1 * Bg jk.2) %ₘ σ.Φ) := by
        rw [← v2gr_eq σ hs0 hws]
        exact hgr
      have hcdS : v2dig σ (Cdev m)
          = ∑ jk ∈ (((Finset.range Nf).filter (fun j => Bf j ≠ 0 ∧
              (e' : ℤ) * σ.w (Bf j) + (j : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' f)) ×ˢ
            ((Finset.range Ng).filter (fun k => Bg k ≠ 0 ∧
              (e' : ℤ) * σ.w (Bg k) + (k : ℤ) * (h' : ℤ) = childW σ σ.Φ e' h' g'))).filter
            (fun jk => jk.1 + jk.2 = m),
            v2dig σ (Bf jk.1) * v2dig σ (Bg jk.2) := by
        rw [v2dig_def, hRs, hevalS]
      rw [if_pos ⟨hs0, by rw [hws]; exact hω₀⟩, hws, hcdS]

/-! #### w_strict — the S9w-(ii) mirror at the regrade (V1's hwult + the negation trick) -/

private lemma v2_wStrict (hσL : StageCoreL σ) (e' h' : ℕ) (s' t' : ℤ)
    (hrp : ReadPair σ e' h' s' t') :
    ∀ f g', f ≠ 0 → g' ≠ 0 →
      childW σ σ.Φ e' h' f < childW σ σ.Φ e' h' g' →
      childW σ σ.Φ e' h' (f + g') = childW σ σ.Φ e' h' f := by
  obtain ⟨⟨-, hSMW⟩, -, hwult, -⟩ := V1_readWPack σ hσL e' h' s' t' hrp
  intro f g' hf hg' hlt
  have hfg : f + g' ≠ 0 := by
    intro h0
    have hgeq : g' = -f := eq_neg_of_add_eq_zero_right h0
    rw [hgeq, v2cw_neg σ e' h' hSMW hf] at hlt
    exact lt_irrefl _ hlt
  have hge : childW σ σ.Φ e' h' f ≤ childW σ σ.Φ e' h' (f + g') := by
    have h := hwult f g' hf hg' hfg
    rwa [min_eq_left (le_of_lt hlt)] at h
  have hle : childW σ σ.Φ e' h' (f + g') ≤ childW σ σ.Φ e' h' f := by
    by_contra hcon
    push_neg at hcon
    have hng : (-g' : Polynomial ℤ_[p]) ≠ 0 := neg_ne_zero.mpr hg'
    have hsum : (f + g') + (-g') = f := by ring
    have h := hwult (f + g') (-g') hfg hng (by rw [hsum]; exact hf)
    rw [hsum, v2cw_neg σ e' h' hSMW hg'] at h
    have h1 : childW σ σ.Φ e' h' f <
        min (childW σ σ.Φ e' h' (f + g')) (childW σ σ.Φ e' h' g') :=
      lt_min hcon hlt
    omega
  omega

end V2Infra

/-- Unit V2: a lawful regrade carrier exists, plus the wV-only strict law (the
S9w-(ii) mirror at the regrade). -/
theorem V2_readResidual {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar) :
    (∃ D : ReadResData σ estar hstar sstar tstar, ReadResLaws D) ∧
    (∀ f g, f ≠ 0 → g ≠ 0 →
        childW σ σ.Φ estar hstar f < childW σ σ.Φ estar hstar g →
        childW σ σ.Φ estar hstar (f + g) = childW σ σ.Φ estar hstar f) := by
  classical
  obtain ⟨⟨-, hSMW⟩, hwmul, -, -⟩ := V1_readWPack σ hσ estar hstar sstar tstar hrp
  have hws := v2_wStrict σ hσ estar hstar sstar tstar hrp
  have hbez' : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 := hrp.2.2.2.1
  have he' : 1 ≤ estar := hrp.1
  refine ⟨⟨⟨v2Rc σ estar hstar sstar tstar,
      v2Rc_phi σ estar hstar sstar tstar hSMW,
      fun B hB hBc => v2Rc_S5 σ estar hstar sstar tstar hSMW B hB hBc⟩,
    v2Rc_zero σ estar hstar sstar tstar,
    fun f hf => v2Rc_ne σ estar hstar sstar tstar hbez' hSMW hf,
    fun f g hf hg => v2Rc_mulLaw σ hσ.core hσ estar hstar sstar tstar hrp hSMW hwmul hf hg,
    fun f g hf hg hfg hEq hSum =>
      v2Rc_addLaw σ hσ.core estar hstar he' sstar tstar hSMW hf hg hfg hEq hSum,
    fun f g hf hg hfg hLt =>
      v2Rc_ltLaw σ hσ.core estar hstar he' sstar tstar hSMW hf hg hfg hLt
        (hws f g hf hg hLt),
    fun f g hf hg hfg hEq hJump =>
      v2Rc_jumpLaw σ hσ.core estar hstar he' sstar tstar hSMW hf hg hfg hEq hJump,
    fun f => v2Rc_negLaw σ hσ.core estar hstar sstar tstar hSMW f⟩, hws⟩

/-- Unit V2 (frame packaging): the full `ReadFrame` is inhabited — the lawful
carrier (above) + V1's wV laws + V6(a)'s hS6a fill. -/
theorem V2_readFrame {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar) :
    Nonempty (ReadFrame σ estar hstar sstar tstar) := by
  classical
  obtain ⟨⟨D, hlaws⟩, -⟩ := V2_readResidual σ hσ estar hstar sstar tstar hrp
  obtain ⟨⟨-, hSMW⟩, hwmul, hwult, -⟩ := V1_readWPack σ hσ estar hstar sstar tstar hrp
  obtain ⟨hwPhi, hK1⟩ :=
    S3_childK1 σ σ.Φ σ.hmonic σ.hdeg estar hstar hrp.1 hrp.2.1 (v2w_one σ)
  exact ⟨⟨D, hlaws, hwmul, hwult, hwPhi, hK1,
    fun B hB hBc => L4_TRANSii σ σ.Φ estar hstar _ hSMW B hB hBc,
    V6_regradeOrbits σ hσ estar hstar sstar tstar hrp D⟩⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V2_readResidual
#print axioms LeanUrat.HC1.V2_readFrame
