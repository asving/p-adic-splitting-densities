/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.T1_baseStage
import LeanUrat.Moves.L3_liftExists
import LeanUrat.Moves.L3_liftWeight
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L2_slotDecomp_R4

/-!
# HC1.S1_transHypGate — TransHyp is non-vacuously inhabitable AND correctly exclusive

moves_ref: MOVES 2325–2328 (D.7 head); MOVESGR §8.2 `transitionCoreL_e0_false`;
HC1_AUDIT C-2. **RE-BASED (audit C-2)**: over T2's own base K = F₄ = F no g ≥ 2
TransHyp is inhabitable (hirr + hroot force [K(z̄):K] = g ≤ [F:K] = 1). Leg (a):
the DEGREE-1 base pin (φ = X, K = F_Q = the prime subfield F₂ = ⊥) inside ambient
F₄; ψ = z² + z + 1 now GENUINELY irreducible over K; z̄ = a primitive cube root in
F₄ˣ; (e′,h′) = (1, w(Φ̂)+1); every field discharged by the listed computation.
RECORDED CONSTRAINT: any increment gate needs [F : K] ≥ g. Leg (b): ¬∃ at e′ = 0
(respects the MovesGr certificate — provable by projection). deps: DefsTower, T1;
Moves `L3_liftExists`, `L3_liftWeight` (clean). E-phase latitude (recorded): if
GaloisField-root plumbing stalls, the fallback ambient is
`AdjoinRoot (X² + X + 1 : (ZMod 2)[X])` — G1's concrete F₄ model, same content.
difficulty: medium. hyp: none.

**PROVED (escalation route, 2026-07-28).** T1's existential conclusion exposes
neither `σ.Φ` nor `σ.K`, and every base-stage constructor on disk is sorried; so
leg (a) is discharged by constructing the degree-1 base stage IN-UNIT, concretely
(namespace `S1Work`): `w f := gaussVal (f(2X)) = min_i (v(aᵢ) + i)` (multiplicative
via the PROVED `L1_gaussVal_mul` through the ring hom `f ↦ f(2X)`), residual
`R f := toLaurent ((unit part of f(2X)) mod 2)` — a genuine initial-form map, all
Stage laws proved; the trivial unit group of K = ⊥ (𝔽₂) collapses every scalar to 1.
`StageCoreL` is assembled from the PROVED `L2_slotDecomp` plus explicit computation;
Φ̂ and (I-aug) from the PROVED `L3_liftExists`/`L3_liftWeight`/`L3_liftMonic`; z̄ = a
generator of F₄ˣ (order 3, so z̄² + z̄ + 1 = 0). Zero axioms beyond Lean core; no
`native_decide`; T1's (still-open) base theorem is NOT consumed — the axiom
footprint of both legs is Lean-core only, machine-printed below.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-! ## The in-unit degree-1 base-stage construction (leg (a) apparatus) -/

namespace S1Work


abbrev F4 : Type := GaloisField 2 2

/-! ### A. The prime subfield ⊥ of F₄: elements are 0 or 1 -/

private lemma two_eq_zero_F4 : (2 : F4) = 0 := by
  have := CharP.cast_eq_zero F4 2
  exact_mod_cast this

private lemma mem_bot_cases {x : F4} (hx : x ∈ (⊥ : Subfield F4)) : x = 0 ∨ x = 1 := by
  rw [← Subfield.closure_empty] at hx
  induction hx using Subfield.closure_induction with
  | mem x hx => exact absurd hx (Set.notMem_empty x)
  | one => exact Or.inr rfl
  | add x y hx hy ihx ihy =>
    rcases ihx with h | h <;> rcases ihy with h' | h' <;> subst h h' <;> simp
    rw [one_add_one_eq_two, two_eq_zero_F4]
  | neg x hx ihx => rcases ihx with h | h <;> subst h <;> simp
    <;> rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, two_eq_zero_F4]
  | inv x hx ihx => rcases ihx with h | h <;> subst h <;> simp
  | mul x y hx hy ihx ihy =>
    rcases ihx with h | h <;> rcases ihy with h' | h' <;> subst h h' <;> simp

private lemma k0_eq_zero_or_one (x : ↥(⊥ : Subfield F4)) : x = 0 ∨ x = 1 := by
  rcases mem_bot_cases x.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

private lemma k0_ne_zero_eq_one {x : ↥(⊥ : Subfield F4)} (hx : x ≠ 0) : x = 1 :=
  (k0_eq_zero_or_one x).resolve_left hx

private lemma k0_unit_eq_one (c : (↥(⊥ : Subfield F4))ˣ) : (c : ↥(⊥ : Subfield F4)) = 1 :=
  k0_ne_zero_eq_one c.ne_zero

/-! ### B. Content machinery over ℤ_[2] (the private `natGV` toolkit, re-derived) -/

private noncomputable def cont (f : Polynomial ℤ_[2]) : ℕ :=
  if h : f.support.Nonempty then f.support.inf' h (fun i => (f.coeff i).valuation) else 0

private lemma gaussVal_eq_cont (f : Polynomial ℤ_[2]) : gaussVal f = (cont f : ℤ) := by
  unfold gaussVal cont
  by_cases h : f.support.Nonempty
  · rw [dif_pos h, dif_pos h, Nat.cast_finsetInf']
  · rw [dif_neg h, dif_neg h, Nat.cast_zero]

private lemma cont_le {f : Polynomial ℤ_[2]} {i : ℕ} (hi : i ∈ f.support) :
    cont f ≤ (f.coeff i).valuation := by
  have hne : f.support.Nonempty := ⟨i, hi⟩
  unfold cont
  rw [dif_pos hne]
  exact Finset.inf'_le _ hi

private lemma cont_attained {f : Polynomial ℤ_[2]} (hf : f ≠ 0) :
    ∃ i ∈ f.support, cont f = (f.coeff i).valuation := by
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  unfold cont
  rw [dif_pos hne]
  exact Finset.exists_mem_eq_inf' hne _

private lemma padic_pow_dvd_iff {x : ℤ_[2]} (hx : x ≠ 0) (n : ℕ) :
    (2 : ℤ_[2]) ^ n ∣ x ↔ n ≤ x.valuation := by
  have h1 := PadicInt.mem_span_pow_iff_le_valuation x hx n
  rw [Ideal.mem_span_singleton] at h1
  simpa using h1

private lemma cpow_dvd_iff {f : Polynomial ℤ_[2]} (hf : f ≠ 0) (n : ℕ) :
    (C (2 : ℤ_[2])) ^ n ∣ f ↔ n ≤ cont f := by
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  rw [← map_pow, Polynomial.C_dvd_iff_dvd_coeff]
  unfold cont
  rw [dif_pos hne]
  constructor
  · intro hall
    apply Finset.le_inf'
    intro i hi
    exact (padic_pow_dvd_iff (Polynomial.mem_support_iff.mp hi) n).mp (hall i)
  · intro hle i
    by_cases hi : i ∈ f.support
    · exact (padic_pow_dvd_iff (Polynomial.mem_support_iff.mp hi) n).mpr
        (le_trans hle (Finset.inf'_le _ hi))
    · rw [Polynomial.mem_support_iff, not_not] at hi
      rw [hi]; exact dvd_zero _

private lemma cpow_cont_dvd (f : Polynomial ℤ_[2]) : (C (2 : ℤ_[2])) ^ (cont f) ∣ f := by
  by_cases hf : f = 0
  · rw [hf]; exact dvd_zero _
  · exact (cpow_dvd_iff hf _).mpr le_rfl

private lemma toZMod_eq_zero_iff (x : ℤ_[2]) :
    (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) x = 0 ↔ (2 : ℤ_[2]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]
  norm_num

private lemma toZMod_poly_eq_zero_iff (z : Polynomial ℤ_[2]) :
    z.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) = 0 ↔ (C (2 : ℤ_[2])) ∣ z := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  constructor
  · intro h0 n
    have hcn : (z.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)).coeff n = 0 := by rw [h0]; simp
    rw [Polynomial.coeff_map] at hcn
    exact (toZMod_eq_zero_iff _).mp hcn
  · intro hdvd
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact (toZMod_eq_zero_iff _).mpr (hdvd n)

/-- Extract the content: `f = C (2^cont f) * f₀` with `f₀` nonzero mod 2. -/
private lemma extract_content {f : Polynomial ℤ_[2]} (hf : f ≠ 0) :
    ∃ f₀ : Polynomial ℤ_[2], f = C ((2 : ℤ_[2]) ^ (cont f)) * f₀ ∧ f₀ ≠ 0 ∧
      f₀.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) ≠ 0 := by
  obtain ⟨f₀, hf₀⟩ := cpow_cont_dvd f
  rw [← map_pow] at hf₀
  refine ⟨f₀, hf₀, ?_, ?_⟩
  · intro h0; rw [h0, mul_zero] at hf₀; exact hf hf₀
  · intro hred
    rw [toZMod_poly_eq_zero_iff] at hred
    obtain ⟨w, hw⟩ := hred
    have hdvd : (C (2 : ℤ_[2])) ^ (cont f + 1) ∣ f := by
      refine ⟨w, ?_⟩
      conv_lhs => rw [hf₀, hw]
      rw [pow_succ, map_pow]
      ring
    have := (cpow_dvd_iff hf _).mp hdvd
    omega

private lemma val_two : ((2 : ℤ_[2])).valuation = 1 := by
  have := PadicInt.valuation_p (p := 2)
  exact_mod_cast this

private lemma val_two_pow (n : ℕ) : ((2 : ℤ_[2]) ^ n).valuation = n := by
  rw [PadicInt.valuation_pow, val_two, mul_one]

private lemma two_pow_ne_zero (n : ℕ) : (2 : ℤ_[2]) ^ n ≠ 0 :=
  pow_ne_zero n two_ne_zero

private lemma cont_C {c : ℤ_[2]} (hc : c ≠ 0) : cont (C c) = c.valuation := by
  have hs : (C c).support = {0} := Polynomial.support_C hc
  have hne : (C c).support.Nonempty := by rw [hs]; exact Finset.singleton_nonempty 0
  unfold cont
  rw [dif_pos hne]
  apply le_antisymm
  · have h0 : 0 ∈ (C c).support := by rw [hs]; exact Finset.mem_singleton_self 0
    simpa [Polynomial.coeff_C_zero] using
      Finset.inf'_le (fun i => ((C c).coeff i).valuation) h0
  · apply Finset.le_inf'
    intro i hi
    rw [hs, Finset.mem_singleton] at hi
    subst hi
    simp [Polynomial.coeff_C_zero]

private lemma gaussVal_C {c : ℤ_[2]} (hc : c ≠ 0) : gaussVal (C c) = (c.valuation : ℤ) := by
  rw [gaussVal_eq_cont, cont_C hc]

/-! ### C. The stretch substitution `comp2 f = f(2X)` and the stage valuation `wS1` -/

private noncomputable def comp2 (f : Polynomial ℤ_[2]) : Polynomial ℤ_[2] :=
  f.comp (C 2 * X)

private lemma comp2_coeff (f : Polynomial ℤ_[2]) (i : ℕ) :
    (comp2 f).coeff i = f.coeff i * 2 ^ i := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    unfold comp2 at *
    rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, add_mul]
  | monomial n a =>
    unfold comp2
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
      ← Polynomial.C_mul]
    by_cases h : i = n
    · subst h
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      ring
    · simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg h, mul_zero, zero_mul]

private lemma comp2_mul (f g : Polynomial ℤ_[2]) : comp2 (f * g) = comp2 f * comp2 g :=
  Polynomial.mul_comp f g _

private lemma comp2_add (f g : Polynomial ℤ_[2]) : comp2 (f + g) = comp2 f + comp2 g :=
  Polynomial.add_comp

private lemma comp2_neg (f : Polynomial ℤ_[2]) : comp2 (-f) = -comp2 f := by
  unfold comp2
  rw [Polynomial.neg_comp]

private lemma comp2_ne {f : Polynomial ℤ_[2]} (hf : f ≠ 0) : comp2 f ≠ 0 := by
  intro h0
  apply hf
  ext i
  have := comp2_coeff f i
  rw [h0, Polynomial.coeff_zero] at this
  rcases mul_eq_zero.mp this.symm with h | h
  · rw [Polynomial.coeff_zero]; exact h
  · exact absurd h (two_pow_ne_zero i)

private lemma comp2_support (f : Polynomial ℤ_[2]) : (comp2 f).support = f.support := by
  ext i
  simp only [Polynomial.mem_support_iff, comp2_coeff]
  constructor
  · intro h hc; exact h (by rw [hc, zero_mul])
  · intro h
    exact mul_ne_zero h (two_pow_ne_zero i)

private lemma comp2_coeff_val {f : Polynomial ℤ_[2]} {i : ℕ} (hi : i ∈ f.support) :
    ((comp2 f).coeff i).valuation = (f.coeff i).valuation + i := by
  rw [comp2_coeff, PadicInt.valuation_mul (Polynomial.mem_support_iff.mp hi)
    (two_pow_ne_zero i), val_two_pow]

/-- The stage valuation at the degree-1 pin: `w f := gaussVal (f(2X)) = min_i (v(aᵢ) + i)`. -/
private noncomputable def wS1 (f : Polynomial ℤ_[2]) : ℤ := gaussVal (comp2 f)

private lemma wS1_eq_cont (f : Polynomial ℤ_[2]) : wS1 f = (cont (comp2 f) : ℤ) :=
  gaussVal_eq_cont _

private lemma wS1_nonneg {f : Polynomial ℤ_[2]} (_ : f ≠ 0) : 0 ≤ wS1 f := by
  rw [wS1_eq_cont]; exact Int.natCast_nonneg _

private lemma wS1_mul {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0) :
    wS1 (f * g) = wS1 f + wS1 g := by
  unfold wS1
  rw [comp2_mul]
  exact L1_gaussVal_mul _ _ (comp2_ne hf) (comp2_ne hg)

private lemma wS1_le {f : Polynomial ℤ_[2]} {i : ℕ} (hi : i ∈ f.support) :
    wS1 f ≤ ((f.coeff i).valuation : ℤ) + i := by
  rw [wS1_eq_cont]
  have h1 : cont (comp2 f) ≤ ((comp2 f).coeff i).valuation :=
    cont_le (by rw [comp2_support]; exact hi)
  rw [comp2_coeff_val hi] at h1
  exact_mod_cast h1

private lemma wS1_attained {f : Polynomial ℤ_[2]} (hf : f ≠ 0) :
    ∃ i ∈ f.support, wS1 f = ((f.coeff i).valuation : ℤ) + i := by
  obtain ⟨i, hi, hv⟩ := cont_attained (comp2_ne hf)
  rw [comp2_support] at hi
  refine ⟨i, hi, ?_⟩
  rw [wS1_eq_cont, hv, comp2_coeff_val hi]
  push_cast
  ring

private lemma wS1_C {c : ℤ_[2]} (hc : c ≠ 0) : wS1 (C c) = (c.valuation : ℤ) := by
  unfold wS1 comp2
  rw [Polynomial.C_comp, gaussVal_C hc]

private lemma wS1_one : wS1 1 = 0 := by
  have := wS1_C (c := 1) one_ne_zero
  simpa using this

private lemma wS1_X : wS1 X = 1 := by
  have hs : (X : Polynomial ℤ_[2]).support = {1} := Polynomial.support_X
  obtain ⟨i, hi, hv⟩ := wS1_attained (Polynomial.X_ne_zero (R := ℤ_[2]))
  rw [hs, Finset.mem_singleton] at hi
  subst hi
  rw [hv, Polynomial.coeff_X_one, PadicInt.valuation_one]
  norm_num

private lemma wS1_neg (f : Polynomial ℤ_[2]) : wS1 (-f) = wS1 f := by
  by_cases hf : f = 0
  · rw [hf, neg_zero]
  · have hneg : -f = C (-1) * f := by rw [Polynomial.C_neg, Polynomial.C_1, neg_one_mul]
    rw [hneg, wS1_mul (by simp) hf, wS1_C (by norm_num : (-1 : ℤ_[2]) ≠ 0)]
    have hv : ((-1 : ℤ_[2])).valuation = 0 := by
      have h1 : ((-1 : ℤ_[2]) * (-1 : ℤ_[2])).valuation
          = (-1 : ℤ_[2]).valuation + (-1 : ℤ_[2]).valuation :=
        PadicInt.valuation_mul (by norm_num) (by norm_num)
      simp only [neg_mul_neg, one_mul, PadicInt.valuation_one] at h1
      omega
    rw [hv]
    norm_num

private lemma wS1_ult {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) : min (wS1 f) (wS1 g) ≤ wS1 (f + g) := by
  rw [wS1_eq_cont, wS1_eq_cont, wS1_eq_cont]
  set m : ℕ := min (cont (comp2 f)) (cont (comp2 g)) with hm
  have hdf : (C (2 : ℤ_[2])) ^ m ∣ comp2 f :=
    dvd_trans (pow_dvd_pow _ (Nat.min_le_left _ _)) (cpow_cont_dvd _)
  have hdg : (C (2 : ℤ_[2])) ^ m ∣ comp2 g :=
    dvd_trans (pow_dvd_pow _ (Nat.min_le_right _ _)) (cpow_cont_dvd _)
  have hdfg : (C (2 : ℤ_[2])) ^ m ∣ comp2 (f + g) := by
    rw [comp2_add]; exact dvd_add hdf hdg
  have h1 : m ≤ cont (comp2 (f + g)) := (cpow_dvd_iff (comp2_ne hfg) m).mp hdfg
  have h2 : min ((cont (comp2 f) : ℤ)) ((cont (comp2 g)) : ℤ) = (m : ℤ) := by
    rw [hm]
    push_cast [Nat.cast_min]
    rfl
  rw [h2]
  exact_mod_cast h1

private lemma wS1_strict {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hlt : wS1 f < wS1 g) : wS1 (f + g) = wS1 f := by
  have hfg : f + g ≠ 0 := by
    intro h0
    have : g = -f := by linear_combination h0
    rw [this, wS1_neg] at hlt
    exact lt_irrefl _ hlt
  apply le_antisymm
  · by_contra hgt
    push_neg at hgt
    have hrw : f = (f + g) + (-g) := by ring
    have hmin := wS1_ult hfg (neg_ne_zero.mpr hg) (by rw [← hrw]; exact hf)
    rw [← hrw, wS1_neg] at hmin
    rcases min_le_iff.mp hmin with h | h
    · exact absurd h (not_le_of_gt hgt)
    · exact absurd h (not_le_of_gt hlt)
  · have := wS1_ult hf hg hfg
    rw [min_eq_left (le_of_lt hlt)] at this
    exact this

/-! ### D. Exact division by the content and the residual map `RS1` -/

/-- the ℕ-content of `f(2X)`: `wS1 f` before the cast. -/
private noncomputable def kf (f : Polynomial ℤ_[2]) : ℕ := cont (comp2 f)

private lemma wS1_eq_kf (f : Polynomial ℤ_[2]) : wS1 f = (kf f : ℤ) := wS1_eq_cont f

private lemma kf_eq_of_wS1 {f g : Polynomial ℤ_[2]} (h : wS1 f = wS1 g) : kf f = kf g := by
  rw [wS1_eq_kf, wS1_eq_kf] at h
  exact_mod_cast h

-- the unit part: `f(2X) = 2^{kf f} · upf f`, with `upf f` nonzero mod 2.
open Classical in
private noncomputable def upf (f : Polynomial ℤ_[2]) : Polynomial ℤ_[2] :=
  if hf : f = 0 then 0 else (extract_content (comp2_ne hf)).choose

private lemma upf_spec {f : Polynomial ℤ_[2]} (hf : f ≠ 0) :
    comp2 f = C ((2 : ℤ_[2]) ^ (kf f)) * upf f ∧ upf f ≠ 0 ∧
      (upf f).map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) ≠ 0 := by
  unfold upf
  rw [dif_neg hf]
  exact (extract_content (comp2_ne hf)).choose_spec

private lemma upf_unique {f u : Polynomial ℤ_[2]} (hf : f ≠ 0)
    (hu : comp2 f = C ((2 : ℤ_[2]) ^ (kf f)) * u) : upf f = u := by
  have h1 := (upf_spec hf).1
  have hC : (C ((2 : ℤ_[2]) ^ (kf f))) ≠ 0 := by
    rw [Polynomial.C_ne_zero]; exact two_pow_ne_zero _
  exact mul_left_cancel₀ hC (h1.symm.trans hu)

/-- the coefficient reduction `ℤ_[2] → ↥⊥ ⊆ F₄`. -/
private noncomputable def ρred : ℤ_[2] →+* ↥(⊥ : Subfield F4) :=
  (ZMod.castHom dvd_rfl (↥(⊥ : Subfield F4))).comp (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)

private lemma map_ρred_ne {u : Polynomial ℤ_[2]}
    (hu : u.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) ≠ 0) : u.map ρred ≠ 0 := by
  intro h0
  apply hu
  have hcomp : u.map ρred
      = (u.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)).map
          (ZMod.castHom dvd_rfl (↥(⊥ : Subfield F4))) := by
    rw [Polynomial.map_map]; rfl
  rw [hcomp] at h0
  exact Polynomial.map_injective _ (ZMod.castHom dvd_rfl (↥(⊥ : Subfield F4))).injective
    (by rw [h0, Polynomial.map_zero])

/-- **The residual map at the pin**: reduce the unit part of `f(2X)` mod 2 and read it as a
Laurent polynomial in `z` over the prime subfield. -/
private noncomputable def RS1 (f : Polynomial ℤ_[2]) : LaurentPolynomial ↥(⊥ : Subfield F4) :=
  Polynomial.toLaurent ((upf f).map ρred)

private lemma RS1_zero : RS1 0 = 0 := by
  unfold RS1 upf
  rw [dif_pos rfl, Polynomial.map_zero, map_zero]

private lemma RS1_ne {f : Polynomial ℤ_[2]} (hf : f ≠ 0) : RS1 f ≠ 0 := by
  unfold RS1
  rw [Polynomial.toLaurent_ne_zero]
  exact map_ρred_ne (upf_spec hf).2.2

private lemma RS1_mul {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0) :
    RS1 (f * g) = RS1 f * RS1 g := by
  have hk : kf (f * g) = kf f + kf g := by
    have h1 := wS1_mul hf hg
    rw [wS1_eq_kf, wS1_eq_kf, wS1_eq_kf] at h1
    exact_mod_cast h1
  have hdec : comp2 (f * g) = C ((2 : ℤ_[2]) ^ (kf (f * g))) * (upf f * upf g) := by
    rw [comp2_mul, (upf_spec hf).1, (upf_spec hg).1, hk, pow_add, map_mul]
    ring
  have hu : upf (f * g) = upf f * upf g := upf_unique (mul_ne_zero hf hg) hdec
  unfold RS1
  rw [hu, Polynomial.map_mul, map_mul]

/-- Every nonzero constant has residual `1` (the only unit scalar of the prime subfield). -/
private lemma RS1_C {c : ℤ_[2]} (hc : c ≠ 0) : RS1 (C c) = 1 := by
  have hCc : (C c : Polynomial ℤ_[2]) ≠ 0 := by rwa [Ne, Polynomial.C_eq_zero]
  have hspec := upf_spec hCc
  have hcomp : comp2 (C c) = C c := Polynomial.C_comp
  -- the unit part of a constant is a constant
  have hdeg : (upf (C c)).degree ≤ 0 := by
    have h1 : (C c).degree = (C ((2 : ℤ_[2]) ^ (kf (C c)))).degree + (upf (C c)).degree := by
      conv_lhs => rw [← hcomp, hspec.1]
      exact Polynomial.degree_mul
    have h2 : (C c).degree ≤ 0 := Polynomial.degree_C_le
    have h3 : (C ((2 : ℤ_[2]) ^ (kf (C c)))).degree = 0 :=
      Polynomial.degree_C (two_pow_ne_zero _)
    rw [h3, zero_add] at h1
    rw [← h1]
    exact h2
  obtain ⟨x, hx⟩ : ∃ x : ℤ_[2], upf (C c) = C x := ⟨_, Polynomial.eq_C_of_degree_le_zero hdeg⟩
  have hx_ne : ρred x ≠ 0 := by
    intro h0
    apply hspec.2.2
    rw [hx]
    have : (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) x = 0 := by
      have := congrArg (ZMod.castHom dvd_rfl (↥(⊥ : Subfield F4))) (show (PadicInt.toZMod x : ZMod 2) = PadicInt.toZMod x from rfl)
      exact (ZMod.castHom dvd_rfl (↥(⊥ : Subfield F4))).injective (by rw [map_zero]; exact h0)
    rw [Polynomial.map_C, this, Polynomial.C_0]
  have hx1 : ρred x = 1 := k0_ne_zero_eq_one hx_ne
  unfold RS1
  rw [hx, Polynomial.map_C, hx1, Polynomial.toLaurent_C, map_one]

private lemma RS1_one : RS1 1 = 1 := by
  have := RS1_C (c := 1) one_ne_zero
  rwa [Polynomial.C_1] at this

private lemma kf_X : kf X = 1 := by
  have := wS1_X
  rw [wS1_eq_kf] at this
  exact_mod_cast this

private lemma RS1_X : RS1 X = LaurentPolynomial.T 1 := by
  have hdec : comp2 X = C ((2 : ℤ_[2]) ^ (kf X)) * X := by
    unfold comp2
    rw [Polynomial.X_comp, kf_X, pow_one]
  have hu : upf X = X := upf_unique Polynomial.X_ne_zero hdec
  unfold RS1
  rw [hu, Polynomial.map_X, Polynomial.toLaurent_X]

private lemma RS1_add {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (hwfg : wS1 f = wS1 g) (hwsum : wS1 (f + g) = wS1 f) :
    RS1 (f + g) = RS1 f + RS1 g := by
  have hk1 : kf g = kf f := kf_eq_of_wS1 hwfg.symm
  have hk2 : kf (f + g) = kf f := kf_eq_of_wS1 hwsum
  have hdec : comp2 (f + g) = C ((2 : ℤ_[2]) ^ (kf (f + g))) * (upf f + upf g) := by
    rw [comp2_add, (upf_spec hf).1, (upf_spec hg).1, hk1, hk2, mul_add]
  have hu : upf (f + g) = upf f + upf g := upf_unique hfg hdec
  unfold RS1
  rw [hu, Polynomial.map_add, map_add]

private lemma RS1_lt {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (hlt : wS1 f < wS1 g) : RS1 (f + g) = RS1 f := by
  have hwsum : wS1 (f + g) = wS1 f := wS1_strict hf hg hlt
  have hk2 : kf (f + g) = kf f := kf_eq_of_wS1 hwsum
  have hklt : kf f < kf g := by
    have := hlt
    rw [wS1_eq_kf, wS1_eq_kf] at this
    exact_mod_cast this
  have hexp : kf f + (kf g - kf f) = kf g := by omega
  have hdec : comp2 (f + g)
      = C ((2 : ℤ_[2]) ^ (kf (f + g))) * (upf f + C ((2 : ℤ_[2]) ^ (kf g - kf f)) * upf g) := by
    rw [comp2_add, (upf_spec hf).1, (upf_spec hg).1, hk2, mul_add, ← mul_assoc, ← map_mul,
      ← pow_add, hexp]
  have hu : upf (f + g) = upf f + C ((2 : ℤ_[2]) ^ (kf g - kf f)) * upf g :=
    upf_unique hfg hdec
  have hρ2 : ρred ((2 : ℤ_[2]) ^ (kf g - kf f)) = 0 := by
    rw [map_pow]
    have h2 : ρred (2 : ℤ_[2]) = 0 := by
      unfold ρred
      rw [RingHom.comp_apply]
      have : (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) (2 : ℤ_[2]) = 0 :=
        (toZMod_eq_zero_iff _).mpr dvd_rfl
      rw [this, map_zero]
    rw [h2, zero_pow (by omega)]
  unfold RS1
  rw [hu, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hρ2, Polynomial.C_0,
    zero_mul, add_zero]

private lemma RS1_jump {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (hwfg : wS1 f = wS1 g) (hjump : wS1 f < wS1 (f + g)) : RS1 f + RS1 g = 0 := by
  have hk1 : kf g = kf f := kf_eq_of_wS1 hwfg.symm
  have hkgt : kf f < kf (f + g) := by
    have := hjump
    rw [wS1_eq_kf, wS1_eq_kf] at this
    exact_mod_cast this
  have hCk : (C ((2 : ℤ_[2]) ^ (kf f))) ≠ 0 := by
    rw [Polynomial.C_ne_zero]; exact two_pow_ne_zero _
  have hgspec : comp2 g = C ((2 : ℤ_[2]) ^ (kf f)) * upf g := by
    rw [← hk1]; exact (upf_spec hg).1
  have hexp : kf f + (kf (f + g) - kf f) = kf (f + g) := by omega
  have hdec : C ((2 : ℤ_[2]) ^ (kf f)) * (upf f + upf g)
      = C ((2 : ℤ_[2]) ^ (kf f)) * (C ((2 : ℤ_[2]) ^ (kf (f + g) - kf f)) * upf (f + g)) :=
    calc C ((2 : ℤ_[2]) ^ (kf f)) * (upf f + upf g)
        = comp2 f + comp2 g := by rw [mul_add, ← (upf_spec hf).1, ← hgspec]
      _ = comp2 (f + g) := (comp2_add f g).symm
      _ = C ((2 : ℤ_[2]) ^ (kf (f + g))) * upf (f + g) := (upf_spec hfg).1
      _ = C ((2 : ℤ_[2]) ^ (kf f))
            * (C ((2 : ℤ_[2]) ^ (kf (f + g) - kf f)) * upf (f + g)) := by
          rw [← mul_assoc, ← map_mul, ← pow_add, hexp]
  have hsum : upf f + upf g = C ((2 : ℤ_[2]) ^ (kf (f + g) - kf f)) * upf (f + g) :=
    mul_left_cancel₀ hCk hdec
  have hρ2 : ρred ((2 : ℤ_[2]) ^ (kf (f + g) - kf f)) = 0 := by
    rw [map_pow]
    have h2 : ρred (2 : ℤ_[2]) = 0 := by
      unfold ρred
      rw [RingHom.comp_apply]
      have : (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) (2 : ℤ_[2]) = 0 :=
        (toZMod_eq_zero_iff _).mpr dvd_rfl
      rw [this, map_zero]
    rw [h2, zero_pow (by omega)]
  have hfin := congrArg (fun q => Polynomial.toLaurent (q.map ρred)) hsum
  simp only [Polynomial.map_add, map_add, Polynomial.map_mul, Polynomial.map_C, hρ2,
    Polynomial.C_0, zero_mul, Polynomial.map_zero, map_zero] at hfin
  unfold RS1
  exact hfin

private lemma RS1_neg (f : Polynomial ℤ_[2]) : RS1 (-f) = - RS1 f := by
  by_cases hf : f = 0
  · rw [hf, neg_zero, RS1_zero, neg_zero]
  · have hk : kf (-f) = kf f := kf_eq_of_wS1 (wS1_neg f)
    have hdec : comp2 (-f) = C ((2 : ℤ_[2]) ^ (kf (-f))) * (-upf f) := by
      rw [comp2_neg, (upf_spec hf).1, hk]
      ring
    have hu : upf (-f) = -upf f := upf_unique (neg_ne_zero.mpr hf) hdec
    unfold RS1
    rw [hu, Polynomial.map_neg, map_neg]

/-! ### E. Coefficient space at the key `X`, `gaussVal X`, and Lemma K1 at the pin -/

private lemma inC_X_eq_C {B : Polynomial ℤ_[2]} (hB : inC X B) : B = C (B.coeff 0) := by
  apply Polynomial.eq_C_of_degree_le_zero
  have h1 : B.degree < (1 : WithBot ℕ) := by
    have := hB
    unfold inC at this
    rwa [Polynomial.degree_X] at this
  exact Nat.WithBot.lt_one_iff_le_zero.mp h1

private lemma inC_X_C (c : ℤ_[2]) : inC (X : Polynomial ℤ_[2]) (C c) := by
  unfold inC
  rw [Polynomial.degree_X]
  exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)

private lemma gaussVal_X : gaussVal (X : Polynomial ℤ_[2]) = 0 := by
  rw [gaussVal_eq_cont]
  have h1 : (1 : ℕ) ∈ (X : Polynomial ℤ_[2]).support := by
    rw [Polynomial.support_X]; exact Finset.mem_singleton_self 1
  have h2 := cont_le h1
  rw [Polynomial.coeff_X_one, PadicInt.valuation_one] at h2
  have : cont (X : Polynomial ℤ_[2]) = 0 := Nat.le_zero.mp h2
  rw [this, Nat.cast_zero]

private lemma dev_X_coeff {f : Polynomial ℤ_[2]} {B : ℕ → Polynomial ℤ_[2]} {N : ℕ}
    (hdev : IsDevelopment X f B N) :
    ∀ i, f.coeff i = if i < N then (B i).coeff 0 else 0 := by
  obtain ⟨hdeg, hzero, hsum⟩ := hdev
  have hBC : ∀ j, B j = C ((B j).coeff 0) := fun j =>
    Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp
      (by have := hdeg j; rwa [Polynomial.degree_X] at this))
  intro i
  rw [hsum, Polynomial.finset_sum_coeff]
  have hterm : ∀ j ∈ Finset.range N, (B j * X ^ j).coeff i
      = if i = j then (B j).coeff 0 else 0 := by
    intro j _
    conv_lhs => rw [hBC j]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split
    · rw [mul_one]
    · rw [mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq (Finset.range N) i (fun j => (B j).coeff 0)]
  simp [Finset.mem_range]

private lemma K1_pin : K1At wS1 X (wS1 X) := by
  intro f B N hf hdev
  have hcoeff := dev_X_coeff hdev
  have hBC : ∀ j, B j = C ((B j).coeff 0) := fun j =>
    Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp
      (by have := hdev.1 j; rwa [Polynomial.degree_X] at this))
  constructor
  · -- lower bound over the nonzero slots
    intro j hjN hBj
    have hbj : (B j).coeff 0 ≠ 0 := by
      intro h0
      exact hBj (by rw [hBC j, h0, Polynomial.C_0])
    have hsupp : j ∈ f.support := by
      rw [Polynomial.mem_support_iff, hcoeff j, if_pos hjN]
      exact hbj
    have hle := wS1_le hsupp
    rw [hcoeff j, if_pos hjN] at hle
    have hgoal : wS1 f ≤ wS1 (B j) + (j : ℤ) * wS1 X := by
      rw [wS1_X]
      conv_rhs => rw [hBC j]
      rw [wS1_C hbj]
      calc wS1 f ≤ (((B j).coeff 0).valuation : ℤ) + j := hle
        _ = (((B j).coeff 0).valuation : ℤ) + (j : ℤ) * 1 := by ring
    exact hgoal
  · -- attainment at a minimizing support index
    obtain ⟨i, hi, hv⟩ := wS1_attained hf
    have hfi : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hiN : i < N := by
      by_contra hcon
      push_neg at hcon
      rw [hcoeff i, if_neg (not_lt.mpr hcon)] at hfi
      exact hfi rfl
    have hbi : (B i).coeff 0 = f.coeff i := by
      rw [hcoeff i, if_pos hiN]
    refine ⟨i, hiN, ?_, ?_⟩
    · intro h0
      rw [hcoeff i, if_pos hiN] at hfi
      exact hfi (by rw [h0, Polynomial.coeff_zero])
    · have hgoal : wS1 f = wS1 (B i) + (i : ℤ) * wS1 X := by
        rw [wS1_X]
        conv_rhs => rw [hBC i]
        rw [wS1_C (by rw [hbi]; exact hfi), hbi, hv]
        ring
      exact hgoal

/-! ### F. The pinned base stage `σpin` -/

private lemma cast_two_eq : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_cast

private lemma C2_ne : (C ((2 : ℕ) : ℤ_[2])) ≠ 0 := by
  rw [Polynomial.C_ne_zero, cast_two_eq]
  exact two_ne_zero

private lemma wS1_C2 : wS1 (C ((2 : ℕ) : ℤ_[2])) = 1 := by
  rw [cast_two_eq, wS1_C two_ne_zero, val_two]
  norm_num

private lemma RS1_C2 : RS1 (C ((2 : ℕ) : ℤ_[2])) = 1 := by
  rw [cast_two_eq]
  exact RS1_C two_ne_zero

/-- **The degree-1 pinned base stage** over the prime subfield of F₄:
`(e,h) = (1,1)`, `s = 1`, `t = 0`, key `Φ = X`, `w = wS1`, `wPrev = gaussVal`,
`K = F_Q = ⊥`, residual `RS1`, representatives `[C 2]`. -/
private noncomputable def σpin : Stage 2 F4 where
  e := 1
  h := 1
  s := 1
  t := 0
  he := le_refl 1
  hh := le_refl 1
  hcop := by norm_num
  hbez := by norm_num
  he1t := fun _ => rfl
  Φ := X
  hmonic := Polynomial.monic_X
  hdeg := by rw [Polynomial.natDegree_X]
  w := wS1
  wPrev := gaussVal
  K := ⊥
  FQ := ⊥
  hFQ_le := le_refl _
  R := RS1
  hwmul := fun f g hf hg => wS1_mul hf hg
  hwult := fun f g hf hg => by
    by_cases hfg : f + g = 0
    · intro h0; exact absurd hfg h0
    · intro _; exact wS1_ult hf hg hfg
  hvalgrp := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : ℤ) ∈ {n : ℤ | ∃ f g : Polynomial ℤ_[2],
        f ≠ 0 ∧ g ≠ 0 ∧ wS1 f - wS1 g = n} :=
      ⟨X, 1, Polynomial.X_ne_zero, one_ne_zero, by rw [wS1_X, wS1_one, sub_zero]⟩
    have h2 := AddSubgroup.subset_closure h1
    have h3 := AddSubgroup.zsmul_mem _ h2 x
    simpa using h3
  hwΦ := by rw [wS1_X]; norm_num
  hStretch := fun B hB hBC => by
    have hBc := inC_X_eq_C hBC
    have hc : B.coeff 0 ≠ 0 := by
      intro h0; exact hB (by rw [hBc, h0, Polynomial.C_0])
    conv_lhs => rw [hBc]
    conv_rhs => rw [hBc]
    rw [wS1_C hc, gaussVal_C hc]
    norm_num
  hR0 := RS1_zero
  hRne := fun f hf => RS1_ne hf
  hRmul := fun f g hf hg => RS1_mul hf hg
  hRadd := fun f g hf hg hfg hw hwsum => RS1_add hf hg hfg hw hwsum
  hRlt := fun f g hf hg hfg hlt => RS1_lt hf hg hfg hlt
  hRΦ := RS1_X
  hK1 := K1_pin
  hS5 := fun B hB hBC => by
    have hBc := inC_X_eq_C hBC
    have hc : B.coeff 0 ≠ 0 := by
      intro h0; exact hB (by rw [hBc, h0, Polynomial.C_0])
    refine ⟨1, ?_⟩
    rw [neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one, Units.val_one, map_one]
    conv_lhs => rw [hBc]
    exact RS1_C hc
  reps := [C ((2 : ℕ) : ℤ_[2])]
  hreps := fun ũ hũ => by
    rw [List.mem_singleton] at hũ
    subst hũ
    exact ⟨C2_ne, inC_X_C _⟩
  Tvec := [(C ((2 : ℕ) : ℤ_[2]), 1)]
  hTvec := rfl
  weightSet := {ν : ℤ | 0 ≤ ν}
  hWS := fun B hB hBC => by
    have hBc := inC_X_eq_C hBC
    have hc : B.coeff 0 ≠ 0 := by
      intro h0; exact hB (by rw [hBc, h0, Polynomial.C_0])
    have : gaussVal B = ((B.coeff 0).valuation : ℤ) := by
      conv_lhs => rw [hBc]
      exact gaussVal_C hc
    rw [Set.mem_setOf_eq, this]
    exact Int.natCast_nonneg _
  hS6a := fun ν hν => ⟨1, fun c _ => by
    rw [Set.mem_setOf_eq] at hν
    refine ⟨C ((2 : ℤ_[2]) ^ ν.toNat), by rw [Polynomial.C_ne_zero]; exact two_pow_ne_zero _,
      inC_X_C _, ?_, ?_⟩
    · rw [gaussVal_C (two_pow_ne_zero _), val_two_pow, Int.toNat_of_nonneg hν]
    · rw [k0_unit_eq_one (c * 1), map_one, neg_zero, zero_mul,
        LaurentPolynomial.T_zero, one_mul]
      exact RS1_C (two_pow_ne_zero _)⟩
  hS6b := fun ν a hν => by
    have hν0 : 0 ≤ ν := by
      have hX : gaussVal (X : Polynomial ℤ_[2]) = 0 := gaussVal_X
      rw [hX] at hν
      exact le_of_lt hν
    refine ⟨C ((2 : ℤ_[2]) ^ ν.toNat), by rw [Polynomial.C_ne_zero]; exact two_pow_ne_zero _,
      inC_X_C _, ?_, ?_⟩
    · rw [gaussVal_C (two_pow_ne_zero _), val_two_pow, Int.toNat_of_nonneg hν0]
    · rw [k0_unit_eq_one a, map_one, neg_zero, zero_mul,
        LaurentPolynomial.T_zero, one_mul]
      exact RS1_C (two_pow_ne_zero _)

/-! ### G. Projection lemmas and the round-5 core `StageCoreL σpin` -/

private lemma σpin_Φ : σpin.Φ = X := rfl
private lemma σpin_e : σpin.e = 1 := rfl
private lemma σpin_h : σpin.h = 1 := rfl
private lemma σpin_s : σpin.s = 1 := rfl
private lemma σpin_t : σpin.t = 0 := rfl
private lemma σpin_w : σpin.w = wS1 := rfl
private lemma σpin_wPrev : σpin.wPrev = gaussVal := rfl
private lemma σpin_K : σpin.K = ⊥ := rfl
private lemma σpin_R : σpin.R = RS1 := rfl
private lemma σpin_reps : σpin.reps = [C ((2 : ℕ) : ℤ_[2])] := rfl
private lemma σpin_Tvec : σpin.Tvec = [(C ((2 : ℕ) : ℤ_[2]), 1)] := rfl

private lemma gaussVal_ult {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) : min (gaussVal f) (gaussVal g) ≤ gaussVal (f + g) := by
  rw [gaussVal_eq_cont, gaussVal_eq_cont, gaussVal_eq_cont]
  set m : ℕ := min (cont f) (cont g) with hm
  have hdf : (C (2 : ℤ_[2])) ^ m ∣ f :=
    dvd_trans (pow_dvd_pow _ (Nat.min_le_left _ _)) (cpow_cont_dvd _)
  have hdg : (C (2 : ℤ_[2])) ^ m ∣ g :=
    dvd_trans (pow_dvd_pow _ (Nat.min_le_right _ _)) (cpow_cont_dvd _)
  have h1 : m ≤ cont (f + g) := (cpow_dvd_iff hfg m).mp (dvd_add hdf hdg)
  have h2 : min ((cont f : ℤ)) ((cont g) : ℤ) = (m : ℤ) := by
    rw [hm]
    push_cast [Nat.cast_min]
    rfl
  rw [h2]
  exact_mod_cast h1

private lemma tvecNum_pin : σpin.tvecNum = C ((2 : ℕ) : ℤ_[2]) := by
  unfold Stage.tvecNum
  rw [σpin_Tvec, σpin_t, σpin_Φ]
  simp

private lemma tvecDen_pin : σpin.tvecDen = 1 := by
  unfold Stage.tvecDen
  rw [σpin_Tvec, σpin_t, σpin_Φ]
  simp

/-! The "pin API": the residual/scalar facts restated at the `σpin` projection types
(defeq hop done ONCE per lemma, at the term level). -/

private lemma pin_unit_one (c : (↥σpin.K)ˣ) : (c : ↥σpin.K) = 1 := k0_unit_eq_one c

private lemma pin_RC {c : ℤ_[2]} (hc : c ≠ 0) : σpin.R (C c) = 1 := RS1_C hc

private lemma pin_R_one : σpin.R 1 = 1 := RS1_one

private lemma pin_RC2 : σpin.R (C ((2 : ℕ) : ℤ_[2])) = 1 := RS1_C2

private lemma pin_RX : σpin.R X = LaurentPolynomial.T 1 := RS1_X

private lemma pin_RX_split :
    σpin.R X = LaurentPolynomial.C (1 : ↥σpin.K) * LaurentPolynomial.T 1 := by
  have h : RS1 X = LaurentPolynomial.C (1 : ↥(⊥ : Subfield F4)) * LaurentPolynomial.T 1 := by
    rw [RS1_X, map_one, one_mul]
  exact h

private lemma pin_RC2_split :
    σpin.R (C ((2 : ℕ) : ℤ_[2]))
      = LaurentPolynomial.C (1 : ↥σpin.K) * LaurentPolynomial.T 0 := by
  have h : RS1 (C ((2 : ℕ) : ℤ_[2]))
      = LaurentPolynomial.C (1 : ↥(⊥ : Subfield F4)) * LaurentPolynomial.T 0 := by
    rw [RS1_C2, map_one, one_mul, LaurentPolynomial.T_zero]
  exact h

private lemma pin_RC1_split (c : (↥σpin.K)ˣ) :
    σpin.R (C (1 : ℤ_[2]))
      = LaurentPolynomial.C ((c : (↥σpin.K)ˣ) : ↥σpin.K)
          * LaurentPolynomial.T (-σpin.t * 0) := by
  rw [pin_unit_one c, σpin_t, neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one]
  rw [pin_RC one_ne_zero, map_one]

private lemma coeffProd_isC {f : Polynomial ℤ_[2]} (hf : IsCoeffProd σpin f) :
    ∃ c : ℤ_[2], f = C c := by
  obtain ⟨l, hl, hprod⟩ := hf
  subst hprod
  induction l with
  | nil => exact ⟨1, by rw [List.prod_nil, Polynomial.C_1]⟩
  | cons u t ih =>
    obtain ⟨c, hc⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem u hx))
    have hu : u = C (u.coeff 0) := by
      have := (hl u (List.mem_cons_self)).2
      rw [σpin_Φ] at this
      exact inC_X_eq_C this
    refine ⟨u.coeff 0 * c, ?_⟩
    rw [List.prod_cons, hc, Polynomial.C_mul]
    conv_lhs => rw [hu]

private lemma stageCore_pin : StageCore σpin := by
  constructor
  case wPrev_mul => exact fun f g hf hg => L1_gaussVal_mul f g hf hg
  case wPrev_ult => exact fun f g hf hg hfg => gaussVal_ult hf hg hfg
  case reps_nonempty => rw [σpin_reps]; exact List.cons_ne_nil _ _
  case p_is_rep => rw [σpin_reps]; exact List.mem_singleton_self _
  case w_strict => exact fun f g hf hg hlt => wS1_strict hf hg hlt
  case w_jump => exact fun f g hf hg hfg hw hj => RS1_jump hf hg hfg hw hj
  case R_neg => exact RS1_neg
  case tvec =>
    constructor
    · rw [tvecNum_pin, tvecDen_pin, σpin_w, wS1_C2, wS1_one]
      norm_num
    · rw [tvecNum_pin, tvecDen_pin]
      exact pin_RC2.trans pin_R_one.symm
  case prevIaug =>
    rw [σpin_e, σpin_h, σpin_wPrev, σpin_Φ, gaussVal_X]
    norm_num
  case slot =>
    exact L2_slotDecomp σpin (fun f g hf hg hlt => wS1_strict hf hg hlt)
      (fun f g hf hg hfg hw hj => RS1_jump hf hg hfg hw hj) RS1_neg
  case coeff =>
    refine ⟨?_, ?_, ?_⟩
    · -- every unit scalar realized: the only unit is 1, realized by B = C 1 at ν = 0
      intro c
      refine ⟨C 1, 0, by rw [Polynomial.C_1]; exact one_ne_zero, inC_X_C 1, ?_, pin_RC1_split c⟩
      show gaussVal (C (1 : ℤ_[2])) = (0 : ℤ)
      rw [gaussVal_C one_ne_zero, PadicInt.valuation_one, Nat.cast_zero]
    · -- equal-weight coefficient products differ by a K-constant (both residuals are 1)
      intro f g hf hg hf0 hg0 _
      obtain ⟨c, hc⟩ := coeffProd_isC hf
      obtain ⟨d, hd⟩ := coeffProd_isC hg
      have hcne : c ≠ 0 := fun h0 => hf0 (by rw [hc, h0, Polynomial.C_0])
      have hdne : d ≠ 0 := fun h0 => hg0 (by rw [hd, h0, Polynomial.C_0])
      refine ⟨1, ?_⟩
      rw [hc, hd, pin_RC hcne, pin_RC hdne, map_one, one_mul]
    · -- the degree-0 exponent group is all of ℤ: position difference 1 from (X, C 2)
      rw [eq_top_iff]
      intro x _
      have h1 : (1 : ℤ) ∈ {n : ℤ | ∃ (f g : Polynomial ℤ_[2]) (c c' : ↥σpin.K) (k k' : ℤ),
          IsUnitMonProd σpin f ∧ IsUnitMonProd σpin g ∧ f ≠ 0 ∧ g ≠ 0 ∧ σpin.w f = σpin.w g ∧
          σpin.R f = LaurentPolynomial.C c * LaurentPolynomial.T k ∧
          σpin.R g = LaurentPolynomial.C c' * LaurentPolynomial.T k' ∧ n = k - k'} := by
        refine ⟨X, C ((2 : ℕ) : ℤ_[2]), 1, 1, 1, 0, ?_, ?_, Polynomial.X_ne_zero, C2_ne,
          ?_, pin_RX_split, pin_RC2_split, by norm_num⟩
        · exact ⟨[], 1, fun u hu => absurd hu (List.not_mem_nil), by
            rw [List.prod_nil, one_mul, σpin_Φ, pow_one]⟩
        · exact ⟨[C ((2 : ℕ) : ℤ_[2])], 0, fun u hu => by
            rw [List.mem_singleton] at hu
            subst hu
            exact ⟨C2_ne, inC_X_C _⟩, by rw [List.prod_singleton, pow_zero, mul_one]⟩
        · rw [σpin_w, wS1_X, wS1_C2]
      have h2 := AddSubgroup.subset_closure h1
      have h3 := AddSubgroup.zsmul_mem _ h2 x
      simpa using h3

/-! ### H. The two demand-laws: `TvecUnitLaw` and `CoeffLocLaw` at the pin -/

private lemma reps_get_pin (i : Fin σpin.reps.length) :
    σpin.reps.get i = C ((2 : ℕ) : ℤ_[2]) := by
  have h1 : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rcases i with ⟨iv, hiv⟩
  simp only at h0
  subst h0
  rfl

private lemma tvec_get_pin (i : Fin σpin.Tvec.length) :
    σpin.Tvec.get i = (C ((2 : ℕ) : ℤ_[2]), 1) := by
  have h1 : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rcases i with ⟨iv, hiv⟩
  simp only at h0
  subst h0
  rfl

private lemma LTwo_CT_mul (a b : LaurentPolynomial ↥σpin.K) (m n : ℤ) :
    (LaurentPolynomial.C a * LaurentPolynomial.T m)
        * (LaurentPolynomial.C b * LaurentPolynomial.T n)
      = LaurentPolynomial.C (a * b) * LaurentPolynomial.T (m + n) := by
  rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add]

/-- the degree-1 unit `uY` with value `grRes X = C z · T 1`. -/
private noncomputable def uYpin : (LTwo ↥σpin.K)ˣ where
  val := LaurentPolynomial.C (LaurentPolynomial.T 1) * LaurentPolynomial.T 1
  inv := LaurentPolynomial.C (LaurentPolynomial.T (-1)) * LaurentPolynomial.T (-1)
  val_inv := by
    rw [LTwo_CT_mul, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      LaurentPolynomial.T_zero, map_one, one_mul]
  inv_val := by
    rw [LTwo_CT_mul, ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero,
      LaurentPolynomial.T_zero, map_one, one_mul]

private lemma grRes_C2 : σpin.grRes (C ((2 : ℕ) : ℤ_[2])) = LaurentPolynomial.T 1 := by
  unfold Stage.grRes
  rw [pin_RC2, map_one, one_mul, σpin_w, wS1_C2]

private lemma grRes_X :
    σpin.grRes X
      = LaurentPolynomial.C (LaurentPolynomial.T 1) * LaurentPolynomial.T 1 := by
  unfold Stage.grRes
  rw [pin_RX, σpin_w, wS1_X]

private lemma grUnit_C2 : IsGrUnit σpin (C ((2 : ℕ) : ℤ_[2])) (locT ↥σpin.K) := by
  unfold IsGrUnit
  rw [grRes_C2]
  rfl

private lemma grUnit_X : IsGrUnit σpin σpin.Φ uYpin := by
  unfold IsGrUnit
  rw [σpin_Φ, grRes_X]
  rfl

private lemma tvecUnitLaw_pin : TvecUnitLaw σpin := by
  refine ⟨uYpin, fun _ => locT ↥σpin.K, grUnit_X, ?_, ?_⟩
  · intro i
    unfold IsGrUnit
    rw [tvec_get_pin i]
    rw [grRes_C2]
    rfl
  · -- (∏ i, locT ^ (Tvec.get i).2) * uYpin ^ t = locT
    have hbody : ∀ i : Fin σpin.Tvec.length,
        (locT ↥σpin.K) ^ ((σpin.Tvec.get i).2) = locT ↥σpin.K := by
      intro i
      rw [tvec_get_pin i, zpow_one]
    calc (∏ i : Fin σpin.Tvec.length, (locT ↥σpin.K) ^ ((σpin.Tvec.get i).2))
          * uYpin ^ σpin.t
        = (∏ _i : Fin σpin.Tvec.length, locT ↥σpin.K) * uYpin ^ σpin.t := by
          rw [Finset.prod_congr rfl (fun i _ => hbody i)]
      _ = locT ↥σpin.K := by
          rw [σpin_t, zpow_zero, mul_one]
          have h1 : (∏ _i : Fin 1, locT ↥σpin.K) = locT ↥σpin.K := by
            rw [Fin.prod_univ_one]
          exact h1

/-- the outer-evaluation `Θ : L₀[T^{±1}] → L₀` at `T = 1` (kills outer positions). -/
private noncomputable def Θpin : LTwo ↥σpin.K →+* LaurentPolynomial ↥σpin.K :=
  LaurentPolynomial.eval₂ (RingHom.id (LaurentPolynomial ↥σpin.K)) 1

private lemma Θpin_C (ℓ : LaurentPolynomial ↥σpin.K) :
    Θpin (LaurentPolynomial.C ℓ) = ℓ := by
  unfold Θpin
  rw [LaurentPolynomial.eval₂_C]
  rfl

private lemma Θpin_T (k : ℤ) : Θpin (LaurentPolynomial.T k) = 1 := by
  unfold Θpin
  rw [LaurentPolynomial.eval₂_T, one_zpow, Units.val_one]

private lemma Θpin_CT (ℓ : LaurentPolynomial ↥σpin.K) (k : ℤ) :
    Θpin (LaurentPolynomial.C ℓ * LaurentPolynomial.T k) = ℓ := by
  rw [map_mul, Θpin_C, Θpin_T, mul_one]

private lemma pin_K_cases (x : ↥σpin.K) : x = 0 ∨ x = 1 := k0_eq_zero_or_one x

private lemma coeffLocLaw_pin : CoeffLocLaw σpin := by
  refine ⟨?_, ?_, ?_⟩
  · -- degree-0 elements of the coefficient localization are K-constants
    intro ℓ hℓ
    have hgen : σpin.coeffLocSR ≤ (⊥ : Subring (LaurentPolynomial ↥σpin.K)).comap Θpin := by
      apply Subring.closure_le.mpr
      intro x hx
      rcases hx with ⟨B, hBne, hBC, hBx⟩ | ⟨i, u, hu, hux⟩
      · -- coefficient generators: grRes of a constant is T(v), Θ kills it to 1
        have hBc : B = C (B.coeff 0) := by
          have h1 : inC (X : Polynomial ℤ_[2]) B := hBC
          exact inC_X_eq_C h1
        have hc : B.coeff 0 ≠ 0 := fun h0 => hBne (by rw [hBc, h0, Polynomial.C_0])
        have hval : Θpin x = 1 := by
          rw [hBx]
          unfold Stage.grRes
          rw [map_mul, Θpin_C, Θpin_T, mul_one]
          conv_lhs => rw [hBc]
          rw [pin_RC hc]
        show x ∈ Subring.comap Θpin (⊥ : Subring (LaurentPolynomial ↥σpin.K))
        rw [Subring.mem_comap, hval]
        exact Subring.one_mem _
      · -- inverse-representative generators: Θ(u) = 1 forces Θ(u⁻¹) = 1
        have hΘu : Θpin (u : LTwo ↥σpin.K) = 1 := by
          have h1 : (u : LTwo ↥σpin.K) = σpin.grRes (σpin.reps.get i) := hu
          rw [h1, reps_get_pin i, grRes_C2, Θpin_T]
        have hmul : Θpin (u : LTwo ↥σpin.K) * Θpin ((u⁻¹ : (LTwo ↥σpin.K)ˣ) : LTwo ↥σpin.K)
            = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [hΘu, one_mul] at hmul
        rw [hux]
        show ((u⁻¹ : (LTwo ↥σpin.K)ˣ) : LTwo ↥σpin.K)
            ∈ Subring.comap Θpin (⊥ : Subring (LaurentPolynomial ↥σpin.K))
        rw [Subring.mem_comap, hmul]
        exact Subring.one_mem _
    have hmem := hgen hℓ
    rw [Subring.mem_comap, Θpin_C] at hmem
    obtain ⟨n, hn⟩ := Subring.mem_bot.mp hmem
    refine ⟨((n : ℤ) : ↥σpin.K), ?_⟩
    rw [← hn]
    exact (map_intCast (LaurentPolynomial.C : ↥σpin.K →+* LaurentPolynomial ↥σpin.K) n).symm
  · -- every K-constant is in the localization subring
    intro d
    rcases pin_K_cases d with h | h
    · subst h
      rw [map_zero, map_zero]
      exact Subring.zero_mem _
    · subst h
      rw [map_one, map_one]
      exact Subring.one_mem _
  · -- the z-pinning: z = V^{-1}·Y at weight 0
    refine ⟨(fun _ => (-1 : ℤ), 1), (locT ↥σpin.K)⁻¹ * uYpin, ?_, ?_, ?_⟩
    · -- weight 0
      unfold Stage.lvecWeight
      have hbody : ∀ i : Fin σpin.reps.length,
          ((fun _ : Fin σpin.reps.length => (-1 : ℤ)) i) * σpin.w (σpin.reps.get i)
            = -1 := by
        intro i
        rw [reps_get_pin i, σpin_w, wS1_C2]
        norm_num
      rw [Finset.sum_congr rfl (fun i _ => hbody i)]
      have h1 : (∑ _i : Fin 1, (-1 : ℤ)) = -1 := by rw [Fin.sum_univ_one]
      have h2 : (∑ _i : Fin σpin.reps.length, (-1 : ℤ)) = -1 := h1
      rw [h2, σpin_h]
      simp
    · -- the monomial-vector value
      refine ⟨fun _ => locT ↥σpin.K, uYpin, ?_, grUnit_X, ?_⟩
      · intro i
        unfold IsGrUnit
        rw [reps_get_pin i, grRes_C2]
        rfl
      · have hbody : ∀ i : Fin σpin.reps.length,
            (locT ↥σpin.K) ^ ((fun _ : Fin σpin.reps.length => (-1 : ℤ)) i)
              = (locT ↥σpin.K)⁻¹ := by
          intro _
          rw [zpow_neg_one]
        rw [Finset.prod_congr rfl (fun i _ => hbody i)]
        have h1 : (∏ _i : Fin 1, (locT ↥σpin.K)⁻¹) = (locT ↥σpin.K)⁻¹ := by
          rw [Fin.prod_univ_one]
        have h2 : (∏ _i : Fin σpin.reps.length, (locT ↥σpin.K)⁻¹) = (locT ↥σpin.K)⁻¹ := h1
        rw [h2, zpow_one]
    · -- value = C z
      show (((locT ↥σpin.K)⁻¹ : (LTwo ↥σpin.K)ˣ) : LTwo ↥σpin.K)
          * ((uYpin : (LTwo ↥σpin.K)ˣ) : LTwo ↥σpin.K)
        = LaurentPolynomial.C (zvar ↥σpin.K)
      show LaurentPolynomial.T (-1)
          * (LaurentPolynomial.C (LaurentPolynomial.T 1) * LaurentPolynomial.T 1)
        = LaurentPolynomial.C (zvar ↥σpin.K)
      rw [mul_comm (LaurentPolynomial.T (-1)), mul_assoc, ← LaurentPolynomial.T_add,
        add_neg_cancel, LaurentPolynomial.T_zero, mul_one]

private lemma stageCoreL_pin : StageCoreL σpin :=
  ⟨stageCore_pin, tvecUnitLaw_pin, coeffLocLaw_pin⟩

private lemma isBaseStage_pin : IsBaseStage σpin :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

/-! ### I. The descend polynomial `ψ = z² + z + 1` over the prime subfield -/

private noncomputable def ψpin : Polynomial ↥σpin.K :=
  Polynomial.X ^ 2 + Polynomial.X + 1

private lemma k0_one_add_one : (1 : ↥σpin.K) + 1 = 0 := by
  have h2 : ((2 : ℕ) : ↥(⊥ : Subfield F4)) = 0 := CharP.cast_eq_zero _ 2
  have h1 : (1 : ↥(⊥ : Subfield F4)) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact_mod_cast h2
  exact h1

private lemma ψpin_monic : ψpin.Monic := by
  unfold ψpin
  rw [add_assoc]
  apply Polynomial.monic_X_pow_add
  apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
  rw [Polynomial.degree_X, Polynomial.degree_one, Nat.cast_ofNat]
  decide

private lemma ψpin_deg : ψpin.natDegree = 2 := by
  unfold ψpin
  rw [add_assoc]
  have hlt : (Polynomial.X + 1 : Polynomial ↥σpin.K).degree
      < (Polynomial.X ^ 2 : Polynomial ↥σpin.K).degree := by
    rw [Polynomial.degree_X_pow, Nat.cast_ofNat]
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    rw [Polynomial.degree_X, Polynomial.degree_one]
    decide
  have hdeg : (Polynomial.X ^ 2 + (Polynomial.X + 1) : Polynomial ↥σpin.K).degree = 2 := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow,
      Nat.cast_ofNat]
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

private lemma ψpin_ne_X : ψpin ≠ Polynomial.X := by
  intro h
  have hc := congrArg (fun q : Polynomial ↥σpin.K => q.coeff 0) h
  simp only [ψpin, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X_zero,
    Polynomial.coeff_one] at hc
  norm_num at hc

private lemma ψpin_no_root (x : ↥σpin.K) : ¬ ψpin.IsRoot x := by
  intro hroot
  have heval : ψpin.eval x = x ^ 2 + x + 1 := by
    simp [ψpin]
  rw [Polynomial.IsRoot, heval] at hroot
  rcases pin_K_cases x with h | h
  · subst h
    simp at hroot
  · subst h
    rw [one_pow, k0_one_add_one, zero_add] at hroot
    exact one_ne_zero hroot

private lemma ψpin_irr : Irreducible ψpin := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [ψpin_deg]; decide
  · exact ψpin_no_root

/-! ### J. The primitive cube root of unity in F₄ˣ -/

private lemma card_F4_units : Nat.card F4ˣ = 3 := by
  have h1 : Nat.card F4 = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  have h2 : Nat.card F4ˣ = Nat.card F4 - 1 := Nat.card_units F4
  omega

private lemma exists_cube_root : ∃ ξ : F4ˣ, (ξ : F4) ^ 2 + (ξ : F4) + 1 = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F4ˣ)
  have horder : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_F4_units]
  have hg3 : g ^ 3 = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder
    norm_num at horder
  have hval3 : ((g : F4)) ^ 3 = 1 := by
    have := congrArg (Units.val) hg3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hvne : (g : F4) ≠ 1 := fun h => hg1 (Units.ext (by rwa [Units.val_one]))
  have hfact : ((g : F4) - 1) * ((g : F4) ^ 2 + (g : F4) + 1) = 0 := by
    have hexp : ((g : F4) - 1) * ((g : F4) ^ 2 + (g : F4) + 1) = (g : F4) ^ 3 - 1 := by
      ring
    rw [hexp, hval3, sub_self]
  refine ⟨g, ?_⟩
  rcases mul_eq_zero.mp hfact with h | h
  · exact absurd (sub_eq_zero.mp h) hvne
  · exact h

/-! ### K. The lift and the full increment hypothesis -/

private lemma thr_pin : ∀ k : ℕ, k < 2 →
    σpin.wPrev σpin.Φ < (σpin.h : ℤ) * ((2 : ℤ) - (k : ℤ)) := by
  intro k hk
  rw [σpin_wPrev, σpin_Φ, gaussVal_X, σpin_h]
  have : (0 : ℤ) < 2 - (k : ℤ) := by omega
  omega

private lemma exists_transHyp :
    ∃ (Φhat : Polynomial ℤ_[2]) (h' : ℕ) (zbar : F4ˣ),
      TransHyp σpin ψpin 2 Φhat 1 h' zbar := by
  obtain ⟨Φhat, hlift⟩ := L3_liftExists σpin ψpin 2 ψpin_monic ψpin_deg thr_pin
  obtain ⟨ξ, hξ⟩ := exists_cube_root
  have hΦmon := L3_liftMonic σpin ψpin 2 (by norm_num) Φhat hlift
  have hΦne : Φhat ≠ 0 := hΦmon.1.ne_zero
  have hw2 : σpin.w Φhat = 2 := by
    have h1 := L3_liftWeight σpin ψpin 2 (by norm_num) Φhat hlift hΦne
    rw [σpin_e, σpin_h] at h1
    rw [h1]
    norm_num
  refine ⟨Φhat, 3, ξ, ?_⟩
  refine ⟨ψpin_monic, ψpin_irr, ψpin_ne_X, ψpin_deg, by norm_num, hlift, le_refl 1,
    by norm_num, by norm_num, ?_, ?_⟩
  · -- (I-aug): 3 > 1 · w(Φ̂) = 2
    unfold IAug
    rw [hw2]
    norm_num
  · -- z̄ is a root of ψ in F₄
    have hmap : ψpin.map σpin.K.subtype
        = Polynomial.X ^ 2 + Polynomial.X + 1 := by
      simp [ψpin, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_one]
    rw [hmap]
    have heval : Polynomial.aeval ((ξ : F4)) (Polynomial.X ^ 2 + Polynomial.X + 1
        : Polynomial F4) = (ξ : F4) ^ 2 + (ξ : F4) + 1 := by
      simp
    rw [heval]
    exact hξ

end S1Work

/-- Unit S1(a): the repaired concrete increment gate — a degree-1 faithfully-based
stage over the prime subfield of ambient F₄ admitting a genuine g = 2 TransHyp at
ψ = z² + z + 1. -/
theorem S1_transHypGate_a :
    ∃ (σ : Stage 2 (GaloisField 2 2)) (Φhat : Polynomial ℤ_[2]) (h' : ℕ)
      (zbar : (GaloisField 2 2)ˣ),
      IsBaseStage σ ∧ StageCoreL σ ∧ σ.Φ = Polynomial.X ∧ σ.e = 1 ∧ σ.h = 1 ∧
      σ.K = ⊥ ∧
      TransHyp σ (Polynomial.X ^ 2 + Polynomial.X + 1) 2 Φhat 1 h' zbar := by
  -- the concrete pinned stage σpin (Φ = X, (e,h) = (1,1), K = F_Q = ⊥) built in S1Work,
  -- with Φ̂ from L3_liftExists at threshold gaussVal(X) = 0 and z̄ the cube root of unity.
  obtain ⟨Φhat, h', zbar, hth⟩ := S1Work.exists_transHyp
  exact ⟨S1Work.σpin, Φhat, h', zbar, S1Work.isBaseStage_pin, S1Work.stageCoreL_pin,
    rfl, rfl, rfl, rfl, hth⟩

/-- Unit S1(b): correct exclusivity — NO TransHyp exists at e′ = 0 (the MovesGr
`transitionCoreL_e0_false` certificate, respected by projection on the `he'`
field). -/
theorem S1_transHypGate_b {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (Φhat : Polynomial ℤ_[p])
    (h' : ℕ) (zbar : Fˣ) :
    ¬ TransHyp σ ψ g Φhat 0 h' zbar :=
  -- projection on the `he'` field: `TransHyp … 0 …` carries `he' : 1 ≤ 0`, absurd.
  fun th => absurd th.he' (by decide)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S1_transHypGate_a
#print axioms LeanUrat.HC1.S1_transHypGate_b
