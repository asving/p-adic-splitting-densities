/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC2.U31_gateReadsOf
import LeanUrat.Moves.L1_gaussVal

/-!
# HC2.HK13_bStageCoreP1a — HK-13: `StageCoreL` at the gate base stage, part 1a

Bridge campaign BP2 (`lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md`, Block G, unit HK-13).
E-PHASE SKELETON: carrier definition + statements with `sorry` bodies; P-phase proves
(hard-fable, est. ~90 lines; "the U31 600-line build is the precedent and supplies the
carrier lemmas").

**Unit HK-13** — blueprint statement: "`StageCoreL bStage` part 1a — wPrev valuation laws
(v_p facts), genuine reps ([p]), tie laws, prevIaug at the diagonal (1,1) Gauss stage
over F4."  (SlotDecomp + CoeffFieldLawCore split to HK-56; TvecUnitLaw + CoeffLocLaw to
HK-14.)

## ⚠ TRANSCRIPTION FINDING + RESOLUTION (E-phase, 2026-07-30 — SURFACED TO THE
## ORCHESTRATOR; read before consuming)

`StageCoreL` at the LITERAL `U31.bStage` is REFUTABLE — the blueprint's target statement
cannot be hosted there:
* `U31.bStage.reps = []` (U31_gateReadsOf.lean l.662) refutes `StageCore.reps_nonempty`
  and `StageCore.p_is_rep` outright;
* `U31.bStage.wPrev = bw` with `bw X = 1` (the stage's own `hwΦ` scale) refutes
  `StageCore.prevIaug`: `1·bw X = 1 < 1` is false.
The blueprint's own clause "genuine reps ([p])" and the D.2 base pin (`HC1.IsBaseStage`,
DefsTower: "parent valuation = the Gauss valuation, reps = [C p]") prescribe the repair.
Since `U31_gateReadsOf.lean` is an existing file (frozen for this campaign — no edits),
the unit is stated at the BASE-PIN RE-DRESS `bStageP` defined below: byte-identical to
`U31.bStage` in every field EXCEPT `wPrev := gaussVal` (the Gauss valuation, DEF-4's
base-case prescription), `reps := [C 2]`, `Tvec := [(C 2, 1)]` (exponent 1: `grRes (C 2)
= T 1 = locT`, matching `TvecLaw`/`TvecUnitLaw` at `t = 0`).  Every recorded U31 gate
fact survives: `w`/`R` ARE `bw`/`bR` unchanged, `gaussVal` agrees with `bw` on the
coefficient carrier `C_X` (constants), and `wPrev` enters the recorded U31 data only
through (S5) positions scaled by `σ.t = 0`.  CROSS-CLUSTER CONSEQUENCE (surfaced, not
decided here): every Block-G unit keyed to "bStage" (HK-15/16/17/18/21/47, the gate node
ν₀ whose `σ` field is the literal `U31.bStage`, …) must re-key to `bStageP` — ν₀ by the
mechanical re-dress `{ν₀ with σ := bStageP}` — pending the orchestrator's ratification.
NOTE: the refutation of `StageCoreL U31.bStage` is deliberately NOT compiled here (the
cross-area rule: no compiled negation witness while sibling clusters may hold sorried
universals at the old carrier); this docstring + the campaign report are the record.

## Contents (statement shapes = `StageCore`'s field types at `σ := bStageP`, so HK-16's
## assembly is a constructor application)

`bStageP` (the carrier), then part 1a: `bStageP_wPrev_mul`, `bStageP_wPrev_ult` (the
parent valuation IS a valuation — v_2 facts of `gaussVal`), `bStageP_reps_nonempty`,
`bStageP_p_is_rep` (genuine reps), `bStageP_w_strict`, `bStageP_w_jump`, `bStageP_R_neg`
(the three D.1(b) tie laws at `bw`/`bR`), `bStageP_prevIaug` ((I-aug) at the base read:
`1·gaussVal X = 0 < 1`).

deps: — (Block-G root unit).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves

/-! ### `HK13R` — the shared re-derivation layer (P-phase, 2026-07-30)

`U31_gateReadsOf.lean` is FROZEN for this campaign and most of its NF/ρ/K₂ toolkit is
`private`. Block G's bStageP-keyed units (HK-13/56/14/16/19/57/20) need those lemmas, so
they are re-derived here ONCE, public, statements byte-matched to U31's (plus the new
`gaussVal` toolkit the base-pin re-dress needs). Downstream units import this module
(directly or through HK-18/HK-19). -/
namespace HK13R

open U31

lemma two_ne_zero' : (2 : ℤ_[2]) ≠ 0 := by norm_num

lemma ρ_two : ρ (2 : ℤ_[2]) = 0 := (ρ_eq_zero_iff 2).mpr dvd_rfl

lemma ρ_one_ne : ρ (1 : ℤ_[2]) ≠ 0 := by
  rw [map_one]
  exact one_ne_zero

lemma ρ_five : ρ (5 : ℤ_[2]) = 1 := by
  have h5 : (5 : ℤ_[2]) = 2 ^ 2 + 1 := by norm_num
  rw [h5, map_add, map_pow, ρ_two, map_one]
  norm_num

lemma ρ_seven : ρ (7 : ℤ_[2]) = 1 := by
  have h7 : (7 : ℤ_[2]) = 2 ^ 2 + 2 + 1 := by norm_num
  rw [h7, map_add, map_add, map_pow, ρ_two, map_one]
  norm_num

lemma K2_cases (x : ↥K2) : x = 0 ∨ x = 1 := by
  obtain ⟨z, hz⟩ := RingHom.mem_fieldRange.mp x.2
  have hz2 : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  rcases hz2 z with h | h
  · left; ext; rw [← hz, h, map_zero]; rfl
  · right; ext; rw [← hz, h, map_one]; rfl

lemma K2_ne_zero_eq_one {x : ↥K2} (hx : x ≠ 0) : x = 1 :=
  (K2_cases x).resolve_left hx

lemma K2_unit_eq_one (a : (↥K2)ˣ) : (a : ↥K2) = 1 :=
  K2_ne_zero_eq_one a.ne_zero

/-- `K2_unit_eq_one`, retyped at the (defeq) `U31.bStage.K` so `rw` stays uniform in
bStage-typed field goals. -/
lemma K2_unit_eq_one' (a : (↥U31.bStage.K)ˣ) : (a : ↥U31.bStage.K) = 1 :=
  K2_unit_eq_one a

lemma θ_apply (f : Polynomial ℤ_[2]) : θ f = eval₂ C (C 2 * X) f := rfl

lemma θ_coeff (f : Polynomial ℤ_[2]) (n : ℕ) :
    (θ f).coeff n = f.coeff n * 2 ^ n := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, coeff_add, add_mul]
  | monomial i a =>
      rw [θ_apply, eval₂_monomial, mul_pow, ← C_pow, ← mul_assoc, ← C_mul,
        coeff_monomial, coeff_C_mul, coeff_X_pow]
      by_cases h : n = i
      · subst h; simp
      · simp [h, Ne.symm h]

lemma θ_ne_zero {f : Polynomial ℤ_[2]} (hf : f ≠ 0) : θ f ≠ 0 := by
  intro h
  apply hf
  ext n
  have := congrArg (fun q => Polynomial.coeff q n) h
  simp only [θ_coeff, coeff_zero] at this
  have h2n : (2 : ℤ_[2]) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero'
  rcases mul_eq_zero.mp this with h' | h'
  · simpa using h'
  · exact absurd h' h2n

lemma map_ρ_eq_zero_iff (P : Polynomial ℤ_[2]) :
    P.map ρ = 0 ↔ C (2 : ℤ_[2]) ∣ P := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    have := congrArg (fun q => Polynomial.coeff q i) h
    simp only [coeff_map, coeff_zero] at this
    exact (ρ_eq_zero_iff _).mp this
  · intro h
    ext i
    rw [coeff_map, coeff_zero]
    exact_mod_cast (ρ_eq_zero_iff _).mpr (h i)

lemma map_ρ_pow2_mul {k : ℕ} (hk : k ≠ 0) (Q : Polynomial ℤ_[2]) :
    (((C 2) ^ k * Q : Polynomial ℤ_[2])).map ρ = 0 := by
  rw [Polynomial.map_mul, Polynomial.map_pow, map_C, ρ_two, map_zero, zero_pow hk, zero_mul]

lemma C2_pow_ne_zero (m : ℕ) : ((C 2 : Polynomial ℤ_[2])) ^ m ≠ 0 :=
  pow_ne_zero _ (C_ne_zero.mpr two_ne_zero')

lemma cancel_C2 {a b : ℕ} {x y : Polynomial ℤ_[2]} (hab : a ≤ b)
    (h : (C 2) ^ a * x = (C 2) ^ b * y) : x = (C 2) ^ (b - a) * y := by
  apply mul_left_cancel₀ (C2_pow_ne_zero a)
  rw [h, ← mul_assoc, ← pow_add]
  congr 2
  omega

lemma cancel_two {a b : ℕ} {x y : ℤ_[2]} (hab : a ≤ b)
    (h : 2 ^ a * x = 2 ^ b * y) : x = 2 ^ (b - a) * y := by
  apply mul_left_cancel₀ (pow_ne_zero a two_ne_zero')
  rw [h, ← mul_assoc, ← pow_add]
  congr 2
  omega

lemma NF_dominates {P : Polynomial ℤ_[2]} {m : ℕ} {Q : Polynomial ℤ_[2]}
    (h : NF P m Q) {k : ℕ} {S : Polynomial ℤ_[2]} (heq : P = (C 2) ^ k * S) : k ≤ m := by
  by_contra hkm
  push_neg at hkm
  have hQ : Q = (C 2) ^ (k - m) * S := cancel_C2 (le_of_lt hkm) (h.1.symm.trans heq)
  exact h.2 (hQ ▸ map_ρ_pow2_mul (by omega) S)

lemma NF_unique {P : Polynomial ℤ_[2]} {m m' : ℕ} {Q Q' : Polynomial ℤ_[2]}
    (h : NF P m Q) (h' : NF P m' Q') : m = m' ∧ Q = Q' := by
  have h1 : m' ≤ m := NF_dominates h h'.1
  have h2 : m ≤ m' := NF_dominates h' h.1
  have hm : m = m' := le_antisymm h2 h1
  subst hm
  refine ⟨rfl, ?_⟩
  have := h.1.symm.trans h'.1
  exact mul_left_cancel₀ (C2_pow_ne_zero m) this

lemma NF_exists {P : Polynomial ℤ_[2]} (hP : P ≠ 0) : ∃ m Q, NF P m Q := by
  have hirr : Irreducible (C (2 : ℤ_[2])) :=
    (prime_C_iff.mpr (by simpa using PadicInt.prime_p (p := 2))).irreducible
  obtain ⟨n, b, hnb, heq⟩ := WfDvdMonoid.max_power_factor hP hirr
  exact ⟨n, b, heq, fun h0 => hnb ((map_ρ_eq_zero_iff b).mp h0)⟩

lemma bR_eq {f : Polynomial ℤ_[2]} {m : ℕ} {Q : Polynomial ℤ_[2]}
    (h : NF (θ f) m Q) : bR f = (Q.map ρ).toLaurent := by
  have hex : ∃ mQ : ℕ × Polynomial ℤ_[2], NF (θ f) mQ.1 mQ.2 := ⟨(m, Q), h⟩
  rw [bR, RA, dif_pos hex]
  rw [(NF_unique hex.choose_spec h).2]

lemma bR_zero : bR 0 = 0 := by
  have hno : ¬ ∃ mQ : ℕ × Polynomial ℤ_[2], NF (θ 0) mQ.1 mQ.2 := by
    rintro ⟨⟨m, Q⟩, hQ1, hQ2⟩
    rw [map_zero] at hQ1
    have hQ0 : Q = 0 := by
      rcases mul_eq_zero.mp hQ1.symm with h | h
      · exact absurd h (C2_pow_ne_zero m)
      · exact h
    rw [hQ0, Polynomial.map_zero] at hQ2
    exact hQ2 rfl
  rw [bR, RA, dif_neg hno]

lemma bR_ne (f : Polynomial ℤ_[2]) (hf : f ≠ 0) : bR f ≠ 0 := by
  obtain ⟨m, Q, hQ⟩ := NF_exists (θ_ne_zero hf)
  rw [bR_eq hQ]
  intro h
  exact hQ.2 (map_eq_zero_iff _ Polynomial.toLaurent_injective |>.mp h)

lemma bw_mul (f g : Polynomial ℤ_[2]) (hf : f ≠ 0) (hg : g ≠ 0) :
    bw (f * g) = bw f + bw g := by
  obtain ⟨mf, P, hP⟩ := NF_exists (θ_ne_zero hf)
  obtain ⟨mg, Q, hQ⟩ := NF_exists (θ_ne_zero hg)
  have hfg : NF (θ (f * g)) (mf + mg) (P * Q) := by
    constructor
    · rw [map_mul, hP.1, hQ.1, pow_add]; ring
    · rw [Polynomial.map_mul]
      exact mul_ne_zero hP.2 hQ.2
  rw [bw_eq hfg, bw_eq hP, bw_eq hQ]
  push_cast
  ring

lemma bR_mul (f g : Polynomial ℤ_[2]) (hf : f ≠ 0) (hg : g ≠ 0) :
    bR (f * g) = bR f * bR g := by
  obtain ⟨mf, P, hP⟩ := NF_exists (θ_ne_zero hf)
  obtain ⟨mg, Q, hQ⟩ := NF_exists (θ_ne_zero hg)
  have hfg : NF (θ (f * g)) (mf + mg) (P * Q) := by
    constructor
    · rw [map_mul, hP.1, hQ.1, pow_add]; ring
    · rw [Polynomial.map_mul]
      exact mul_ne_zero hP.2 hQ.2
  rw [bR_eq hfg, bR_eq hP, bR_eq hQ, Polynomial.map_mul, map_mul]

/-- The strict-triangle tie law at `bw` (D.1(b) tie law 1's kernel). -/
lemma bw_strict {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hlt : bw f < bw g) : bw (f + g) = bw f := by
  obtain ⟨mf, P, hP⟩ := NF_exists (θ_ne_zero hf)
  obtain ⟨mg, Q, hQ⟩ := NF_exists (θ_ne_zero hg)
  have hmm : mf < mg := by
    rw [bw_eq hP, bw_eq hQ] at hlt
    exact_mod_cast hlt
  have hNF : NF (θ (f + g)) mf (P + (C 2) ^ (mg - mf) * Q) := by
    constructor
    · rw [map_add, hP.1, hQ.1, mul_add, ← mul_assoc, ← pow_add]
      congr 3
      omega
    · rw [Polynomial.map_add, map_ρ_pow2_mul (by omega) Q, add_zero]
      exact hP.2
  rw [bw_eq hNF, bw_eq hP]

/-- The weight-jump cancellation tie law at `bw`/`bR` (D.1(b) tie law 2's kernel). -/
lemma bR_jump {f g : Polynomial ℤ_[2]} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (hw : bw f = bw g) (hlt : bw f < bw (f + g)) : bR f + bR g = 0 := by
  obtain ⟨mf, P, hP⟩ := NF_exists (θ_ne_zero hf)
  obtain ⟨mg, Q, hQ⟩ := NF_exists (θ_ne_zero hg)
  have hmfg : mg = mf := by
    rw [bw_eq hP, bw_eq hQ] at hw
    exact_mod_cast hw.symm
  rw [hmfg] at hQ
  have heq : θ (f + g) = (C 2) ^ mf * (P + Q) := by
    rw [map_add, hP.1, hQ.1, mul_add]
  have hmap : (P + Q).map ρ = 0 := by
    by_contra hne
    have hNF : NF (θ (f + g)) mf (P + Q) := ⟨heq, hne⟩
    rw [bw_eq hNF, bw_eq hP] at hlt
    exact lt_irrefl _ hlt
  rw [bR_eq hP, bR_eq hQ, ← map_add, ← Polynomial.map_add, hmap, map_zero]

/-- The negation law at `bR` (D.1(b) tie law 3's kernel). -/
lemma bR_negf (f : Polynomial ℤ_[2]) : bR (-f) = - bR f := by
  by_cases hf : f = 0
  · rw [hf, neg_zero, bR_zero, neg_zero]
  obtain ⟨m, Q, hQ⟩ := NF_exists (θ_ne_zero hf)
  have hNF : NF (θ (-f)) m (-Q) := by
    constructor
    · rw [map_neg, hQ.1, mul_neg]
    · rw [Polynomial.map_neg, neg_ne_zero]
      exact hQ.2
  rw [bR_eq hNF, bR_eq hQ, Polynomial.map_neg, map_neg]

/-! ### Concrete normal forms and values (U31's private table, re-derived) -/

lemma map_ρ_one_ne : ((1 : Polynomial ℤ_[2])).map ρ ≠ 0 := by
  rw [Polynomial.map_one]
  exact one_ne_zero

lemma NF_θ_one : NF (θ 1) 0 1 := by
  refine ⟨?_, map_ρ_one_ne⟩
  rw [map_one, pow_zero, one_mul]

lemma NF_θ_C2pow (n : ℕ) : NF (θ (C (2 ^ n))) n 1 := by
  refine ⟨?_, map_ρ_one_ne⟩
  rw [θ_C, mul_one, ← C_pow]

lemma map_ρ_X_ne : ((X : Polynomial ℤ_[2])).map ρ ≠ 0 := by
  rw [Polynomial.map_X]
  exact X_ne_zero

lemma NF_θ_X : NF (θ X) 1 X := by
  refine ⟨?_, map_ρ_X_ne⟩
  rw [show θ X = C 2 * X from by rw [θ_apply, eval₂_X], pow_one]

lemma bw_X : bw X = 1 := bw_eq NF_θ_X

lemma bR_X : bR X = LaurentPolynomial.T 1 := by
  rw [bR_eq NF_θ_X, Polynomial.map_X, Polynomial.toLaurent_X]

lemma bw_one : bw 1 = 0 := bw_eq NF_θ_one

lemma bw_C2pow (n : ℕ) : bw (C (2 ^ n)) = n := bw_eq (NF_θ_C2pow n)

lemma bw_C2 : bw (C 2) = 1 := by
  have h : (2 : ℤ_[2]) = 2 ^ 1 := by norm_num
  rw [h, bw_C2pow]
  norm_num

lemma toLaurent_map_one : (((1 : Polynomial ℤ_[2])).map ρ).toLaurent = 1 := by
  rw [Polynomial.map_one, Polynomial.toLaurent_one]

lemma bR_one : bR 1 = 1 := by rw [bR_eq NF_θ_one, toLaurent_map_one]

lemma bR_C2pow (n : ℕ) : bR (C (2 ^ n)) = 1 := by
  rw [bR_eq (NF_θ_C2pow n), toLaurent_map_one]

lemma bR_C2 : bR (C 2) = 1 := by
  have h : (2 : ℤ_[2]) = 2 ^ 1 := by norm_num
  rw [h, bR_C2pow]

/-- The constant's stage residual is 1 (all p = 2 digits are 1). -/
lemma bR_const {b : ℤ_[2]} (hb : b ≠ 0) : bR (C b) = 1 := by
  obtain ⟨m, u, hNF, hu⟩ := NF_const hb
  have hNFθ : NF (θ (C b)) m (C u) := by rw [θ_C]; exact hNF
  rw [bR_eq hNFθ, map_C]
  have : ρ u = 1 := K2_ne_zero_eq_one hu
  rw [this, Polynomial.toLaurent_C, map_one]

/-- Weight of a normal-form constant: `bw (C (2^m·u)) = m` for a mod-2 unit `u`. -/
lemma bw_C_two_pow_mul {m : ℕ} {u : ℤ_[2]} (hu : ρ u ≠ 0) :
    bw (C ((2 : ℤ_[2]) ^ m * u)) = m := by
  have hNF : NF (θ (C ((2 : ℤ_[2]) ^ m * u))) m (C u) := by
    constructor
    · rw [θ_C, map_mul, map_pow]
    · rw [Polynomial.map_C]
      intro h
      exact hu (by simpa using h)
  exact bw_eq hNF

lemma inC_C {b : ℤ_[2]} : inC (X : Polynomial ℤ_[2]) (C b) := by
  show (C b).degree < (X : Polynomial ℤ_[2]).degree
  rw [degree_X]
  exact lt_of_le_of_lt degree_C_le (by norm_num)

/-! ### The `gaussVal` toolkit (the base-pin re-dress's parent valuation) -/

lemma padic_pow_dvd_iff {x : ℤ_[2]} (hx : x ≠ 0) (n : ℕ) :
    (2 : ℤ_[2]) ^ n ∣ x ↔ n ≤ x.valuation := by
  have h2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num
  rw [← h2]
  exact Ideal.mem_span_singleton.symm.trans (PadicInt.mem_span_pow_iff_le_valuation x hx n)

lemma le_gaussVal {f : Polynomial ℤ_[2]} (hf : f ≠ 0) (c : ℤ)
    (h : ∀ i ∈ f.support, c ≤ ((f.coeff i).valuation : ℤ)) : c ≤ gaussVal f := by
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  unfold gaussVal
  rw [dif_pos hne]
  exact Finset.le_inf' hne _ h

lemma gaussVal_le_coeff {f : Polynomial ℤ_[2]} {i : ℕ} (hi : i ∈ f.support) :
    gaussVal f ≤ ((f.coeff i).valuation : ℤ) := by
  have hne : f.support.Nonempty := ⟨i, hi⟩
  unfold gaussVal
  rw [dif_pos hne]
  exact Finset.inf'_le _ hi

lemma gaussVal_nonneg (f : Polynomial ℤ_[2]) : 0 ≤ gaussVal f := by
  by_cases hf : f = 0
  · rw [hf]
    unfold gaussVal
    rw [dif_neg (by simp)]
  · exact le_gaussVal hf 0 (fun i _ => Int.natCast_nonneg _)

lemma gaussVal_single {f : Polynomial ℤ_[2]} {n : ℕ} (hs : f.support = {n}) :
    gaussVal f = ((f.coeff n).valuation : ℤ) := by
  have hne : f.support.Nonempty := by rw [hs]; exact Finset.singleton_nonempty n
  unfold gaussVal
  rw [dif_pos hne]
  apply le_antisymm
  · exact Finset.inf'_le _ (by rw [hs]; exact Finset.mem_singleton_self n)
  · refine Finset.le_inf' hne _ (fun i hi => ?_)
    rw [hs, Finset.mem_singleton] at hi
    subst hi
    exact le_refl _

lemma gaussVal_X : gaussVal (X : Polynomial ℤ_[2]) = 0 := by
  rw [gaussVal_single (n := 1) Polynomial.support_X, Polynomial.coeff_X_one]
  simp

lemma gaussVal_C {b : ℤ_[2]} (hb : b ≠ 0) :
    gaussVal (C b) = (b.valuation : ℤ) := by
  have hs : (C b).support = {0} := by
    rw [← Polynomial.monomial_zero_left]
    exact Polynomial.support_monomial 0 hb
  rw [gaussVal_single (n := 0) hs, Polynomial.coeff_C_zero]

lemma val_two_pow_mul {m : ℕ} {u : ℤ_[2]} (hu : ρ u ≠ 0) :
    ((2 : ℤ_[2]) ^ m * u).valuation = m := by
  have hune : u ≠ 0 := fun h => hu (by rw [h, map_zero])
  have hne : (2 : ℤ_[2]) ^ m * u ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero') hune
  have hub : m ≤ ((2 : ℤ_[2]) ^ m * u).valuation :=
    (padic_pow_dvd_iff hne m).mp ⟨u, rfl⟩
  rcases eq_or_lt_of_le hub with h | h
  · exact h.symm
  · exfalso
    have h2 : (2 : ℤ_[2]) ^ (m + 1) ∣ 2 ^ m * u := (padic_pow_dvd_iff hne (m + 1)).mpr h
    obtain ⟨v, hv⟩ := h2
    have hu2 : u = 2 * v := by
      apply mul_left_cancel₀ (pow_ne_zero m two_ne_zero')
      rw [hv, pow_succ]
      ring
    apply hu
    rw [hu2, map_mul, ρ_two, zero_mul]

lemma gaussVal_C_two_pow_mul {m : ℕ} {u : ℤ_[2]} (hu : ρ u ≠ 0) :
    gaussVal (C ((2 : ℤ_[2]) ^ m * u)) = (m : ℤ) := by
  have hune : u ≠ 0 := fun h => hu (by rw [h, map_zero])
  rw [gaussVal_C (mul_ne_zero (pow_ne_zero _ two_ne_zero') hune), val_two_pow_mul hu]

lemma gaussVal_C2pow (n : ℕ) : gaussVal (C ((2 : ℤ_[2]) ^ n)) = (n : ℤ) := by
  have h := gaussVal_C_two_pow_mul (m := n) (u := 1) ρ_one_ne
  rwa [mul_one] at h

lemma gaussVal_one : gaussVal (1 : Polynomial ℤ_[2]) = 0 := by
  have h := gaussVal_C2pow 0
  rwa [pow_zero, map_one, Nat.cast_zero] at h

/-- The base-pin bridge: `bw` and the Gauss valuation agree on constants. -/
lemma bw_C_eq_gaussVal {b : ℤ_[2]} (hb : b ≠ 0) :
    bw (C b) = gaussVal (C b) := by
  obtain ⟨m, u, hNF, hu⟩ := NF_const hb
  have hNFθ : NF (θ (C b)) m (C u) := by rw [θ_C]; exact hNF
  have hbu : b = 2 ^ m * u := by
    have h1 := congrArg (fun q => Polynomial.coeff q 0) hNF.1
    simp only [← C_pow, ← C_mul, coeff_C_zero] at h1
    exact h1
  rw [bw_eq hNFθ, hbu, gaussVal_C_two_pow_mul hu]

/-- Ultrametric law for the Gauss valuation (coefficientwise 2-divisibility). -/
lemma gaussVal_ult (f g : Polynomial ℤ_[2]) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) : min (gaussVal f) (gaussVal g) ≤ gaussVal (f + g) := by
  apply le_gaussVal hfg
  intro i hi
  have hci : (f + g).coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  rw [Polynomial.coeff_add] at hci
  have hgoal : ((f + g).coeff i) = f.coeff i + g.coeff i := Polynomial.coeff_add f g i
  rw [hgoal]
  by_cases hfi : f.coeff i = 0
  · rw [hfi, zero_add] at hci ⊢
    exact le_trans (min_le_right _ _)
      (gaussVal_le_coeff (Polynomial.mem_support_iff.mpr hci))
  · by_cases hgi : g.coeff i = 0
    · rw [hgi, add_zero] at hci ⊢
      exact le_trans (min_le_left _ _)
        (gaussVal_le_coeff (Polynomial.mem_support_iff.mpr hfi))
    · have h1 : gaussVal f ≤ ((f.coeff i).valuation : ℤ) :=
        gaussVal_le_coeff (Polynomial.mem_support_iff.mpr hfi)
      have h2 : gaussVal g ≤ ((g.coeff i).valuation : ℤ) :=
        gaussVal_le_coeff (Polynomial.mem_support_iff.mpr hgi)
      set k : ℕ := min (f.coeff i).valuation (g.coeff i).valuation with hk
      have hdf : (2 : ℤ_[2]) ^ k ∣ f.coeff i :=
        (padic_pow_dvd_iff hfi k).mpr (min_le_left _ _)
      have hdg : (2 : ℤ_[2]) ^ k ∣ g.coeff i :=
        (padic_pow_dvd_iff hgi k).mpr (min_le_right _ _)
      have hval : (k : ℤ) ≤ ((f.coeff i + g.coeff i).valuation : ℤ) := by
        exact_mod_cast (padic_pow_dvd_iff hci k).mp (dvd_add hdf hdg)
      calc min (gaussVal f) (gaussVal g)
          ≤ min ((f.coeff i).valuation : ℤ) ((g.coeff i).valuation : ℤ) :=
            min_le_min h1 h2
        _ = (k : ℤ) := by rw [hk, Nat.cast_min]
        _ ≤ _ := hval

/-! ### ψ₂ facts (U31's private table, re-derived for the SideReads consumers) -/

lemma ψ₂_monic : ψ₂.Monic := by
  unfold U31.ψ₂
  monicity!

lemma ψ₂_natDegree : ψ₂.natDegree = 2 := by
  unfold U31.ψ₂
  compute_degree!

lemma ψ₂_ne_zero : ψ₂ ≠ 0 := ψ₂_monic.ne_zero

lemma ψ₂_coeff_zero : ψ₂.coeff 0 = 1 := by
  unfold U31.ψ₂
  simp [coeff_add, coeff_X_pow, coeff_one]

lemma ψ₂_coeff_one : ψ₂.coeff 1 = 1 := by
  unfold U31.ψ₂
  simp [coeff_add, coeff_X_pow, coeff_one]

lemma ord_ψ₂ : OrdPsiPoly ψ₂ ψ₂ 1 := by
  constructor
  · rw [pow_one]
  · intro hdvd
    have h1 := Polynomial.natDegree_le_of_dvd hdvd ψ₂_ne_zero
    rw [Polynomial.natDegree_pow, ψ₂_natDegree] at h1
    omega

lemma XXone_ne_zero {L : Type*} [Field L] : (X ^ 2 + X + 1 : Polynomial L) ≠ 0 := by
  intro h
  have := congrArg (fun q => Polynomial.coeff q 0) h
  simp at this

lemma map_ρ_q₁ : q₁.map ρ = X ^ 2 + X + 1 := by
  rw [U31.q₁, Polynomial.map_add, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_one]

lemma NF_θ_fq : NF (θ fq) 2 q₁ := by
  constructor
  · rw [U31.fq, map_add, map_add, map_pow, map_mul,
      show θ X = C 2 * X from by rw [θ_apply, eval₂_X], θ_C, θ_C, U31.q₁]
    have h4 : (C (4 : ℤ_[2])) = C 2 ^ 2 := by rw [← C_pow]; norm_num
    rw [h4]
    ring
  · rw [map_ρ_q₁]
    exact XXone_ne_zero

end HK13R

/-- **HK-13 carrier: `bStageP`** — the BASE-PIN RE-DRESS of `U31.bStage` (the (1,1)-diagonal
Gauss stage at `Φ = X` over `K₂ ≅ 𝔽₂` inside F4): `wPrev := gaussVal` (the Gauss
valuation — the D.2/`IsBaseStage` base pin; `U31.bStage`'s `wPrev := bw` junk-choice off
the coefficient carrier refutes `prevIaug`), `reps := [C 2]`, `Tvec := [(C 2, 1)]`
(genuine representatives — `U31.bStage.reps = []` refutes `reps_nonempty`/`p_is_rep`);
every other field byte-identical to `U31.bStage` (`w = bw`, `R = bR`, `Φ = X`,
`(e,h,s,t) = (1,1,1,0)`, `K = FQ = K₂`, `weightSet = Set.Ici 0`).  The seven
`wPrev`/`reps`/`Tvec`-typed Stage law fields are re-supplied (`sorry` = this unit's
P-phase duty; `hTvec` is definitional).  See the module header for the full finding
record and the cross-cluster re-key consequence.
[Blueprint BP2 HK-13; deps: —.] -/
noncomputable def bStageP : Stage 2 F4 :=
  { U31.bStage with
    wPrev := gaussVal
    reps := [Polynomial.C ((2 : ℕ) : ℤ_[2])]
    Tvec := [(Polynomial.C ((2 : ℕ) : ℤ_[2]), (1 : ℤ))]
    hreps := by
      intro ũ hũ
      rw [List.mem_singleton] at hũ
      subst hũ
      exact ⟨Polynomial.C_ne_zero.mpr (by norm_num), HK13R.inC_C⟩
    hTvec := rfl
    hStretch := by
      intro B hB hin
      have hBC : B = Polynomial.C (B.coeff 0) := U31.is_const hin
      have hb : B.coeff 0 ≠ 0 := fun h => hB (by rw [hBC, h, map_zero])
      have hw : U31.bStage.w B = gaussVal B := by
        rw [hBC]
        exact HK13R.bw_C_eq_gaussVal hb
      have he : U31.bStage.e = 1 := rfl
      rw [hw, he, Nat.cast_one, one_mul]
    hS5 := by
      intro B hB hin
      refine ⟨1, ?_⟩
      have hBC : B = Polynomial.C (B.coeff 0) := U31.is_const hin
      have hb : B.coeff 0 ≠ 0 := fun h => hB (by rw [hBC, h, map_zero])
      have hR : U31.bStage.R B = 1 := by
        rw [hBC]
        exact HK13R.bR_const hb
      have ht : U31.bStage.t = (0 : ℤ) := rfl
      rw [hR, HK13R.K2_unit_eq_one' 1, map_one, ht, neg_zero, zero_mul,
        LaurentPolynomial.T_zero, one_mul]
    hS6a := by
      intro ν hν
      refine ⟨1, fun c _ => ?_⟩
      refine ⟨Polynomial.C ((2 : ℤ_[2]) ^ ν.toNat),
        Polynomial.C_ne_zero.mpr (pow_ne_zero _ HK13R.two_ne_zero'), HK13R.inC_C, ?_, ?_⟩
      · rw [HK13R.gaussVal_C2pow, Int.toNat_of_nonneg hν]
      · have hR : U31.bStage.R (Polynomial.C ((2 : ℤ_[2]) ^ ν.toNat)) = 1 :=
          HK13R.bR_C2pow ν.toNat
        have ht : U31.bStage.t = (0 : ℤ) := rfl
        rw [hR, HK13R.K2_unit_eq_one' (c * 1), map_one, ht, neg_zero, zero_mul,
          LaurentPolynomial.T_zero, one_mul]
    hS6b := by
      intro ν a hν
      have hν' : gaussVal (X : Polynomial ℤ_[2]) < ν := hν
      rw [HK13R.gaussVal_X] at hν'
      refine ⟨Polynomial.C ((2 : ℤ_[2]) ^ ν.toNat),
        Polynomial.C_ne_zero.mpr (pow_ne_zero _ HK13R.two_ne_zero'), HK13R.inC_C, ?_, ?_⟩
      · rw [HK13R.gaussVal_C2pow, Int.toNat_of_nonneg (le_of_lt hν')]
      · have hR : U31.bStage.R (Polynomial.C ((2 : ℤ_[2]) ^ ν.toNat)) = 1 :=
          HK13R.bR_C2pow ν.toNat
        have ht : U31.bStage.t = (0 : ℤ) := rfl
        rw [hR, HK13R.K2_unit_eq_one' a, map_one, ht, neg_zero, zero_mul,
          LaurentPolynomial.T_zero, one_mul]
    hWS := fun B _ _ => HK13R.gaussVal_nonneg B }

/-! ### bStageP projection bridges (P-phase convenience for the downstream Block-G
units; every proof is `rfl` or a defeq retype — additive helpers, not unit statements) -/

lemma bStageP_w_def : bStageP.w = U31.bw := rfl

lemma bStageP_wPrev_def : bStageP.wPrev = gaussVal := rfl

lemma bStageP_Phi_def : bStageP.Φ = Polynomial.X := rfl

lemma bStageP_t_def : bStageP.t = 0 := rfl

lemma bStageP_e_def : bStageP.e = 1 := rfl

lemma bStageP_h_def : bStageP.h = 1 := rfl

lemma bStageP_s_def : bStageP.s = 1 := rfl

lemma bStageP_reps_def : bStageP.reps = [Polynomial.C ((2 : ℕ) : ℤ_[2])] := rfl

lemma bStageP_unit_eq_one (a : (↥bStageP.K)ˣ) : (a : ↥bStageP.K) = 1 :=
  HK13R.K2_unit_eq_one a

lemma bStageP_K_cases (x : ↥bStageP.K) : x = 0 ∨ x = 1 := HK13R.K2_cases x

/-- HK-13 (part 1a, `StageCore.wPrev_mul` shape): the parent valuation `gaussVal` is
multiplicative on nonzero polynomials — the v_2 content-exponent product law (Gauss's
lemma over the DVR `ℤ_[2]`).  [Blueprint BP2 HK-13; deps: —; supply: `L1_gaussVal`'s
Gauss-valuation toolkit.] -/
theorem bStageP_wPrev_mul :
    ∀ f g : Polynomial ℤ_[2], f ≠ 0 → g ≠ 0 →
      bStageP.wPrev (f * g) = bStageP.wPrev f + bStageP.wPrev g := by
  intro f g hf hg
  exact L1_gaussVal_mul f g hf hg

/-- HK-13 (part 1a, `StageCore.wPrev_ult` shape): the parent valuation `gaussVal` is
ultrametric — `min (v f) (v g) ≤ v (f + g)` on nonzero sums (coefficientwise v_2
minimum).  [Blueprint BP2 HK-13; deps: —.] -/
theorem bStageP_wPrev_ult :
    ∀ f g : Polynomial ℤ_[2], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      min (bStageP.wPrev f) (bStageP.wPrev g) ≤ bStageP.wPrev (f + g) := by
  intro f g hf hg hfg
  exact HK13R.gaussVal_ult f g hf hg hfg

/-- HK-13 (part 1a, `StageCore.reps_nonempty` shape): the representative list is genuine —
nonempty.  Definitional at the re-dress (`bStageP.reps = [C 2]`).  [Blueprint BP2 HK-13.] -/
theorem bStageP_reps_nonempty : bStageP.reps ≠ [] := by
  show [Polynomial.C ((2 : ℕ) : ℤ_[2])] ≠ []
  exact List.cons_ne_nil _ _

/-- HK-13 (part 1a, `StageCore.p_is_rep` shape): `[p]` — the representative list contains
`C p` at `p = 2` (cast-shape matched to `StageCore`'s field type `Polynomial.C (↑p)`).
Definitional at the re-dress.  [Blueprint BP2 HK-13.] -/
theorem bStageP_p_is_rep : (Polynomial.C ((2 : ℕ) : ℤ_[2])) ∈ bStageP.reps := by
  show Polynomial.C ((2 : ℕ) : ℤ_[2]) ∈ [Polynomial.C ((2 : ℕ) : ℤ_[2])]
  exact List.mem_singleton_self _

/-- HK-13 (part 1a, `StageCore.w_strict` shape — D.1(b) tie law 1): strict-triangle
equality for the stage weight `bw`.  [Blueprint BP2 HK-13; supply: U31's `bw_ult`/NF
normal-form machinery (the 600-line-build precedent).] -/
theorem bStageP_w_strict :
    ∀ f g : Polynomial ℤ_[2], f ≠ 0 → g ≠ 0 →
      bStageP.w f < bStageP.w g → bStageP.w (f + g) = bStageP.w f := by
  intro f g hf hg hlt
  exact HK13R.bw_strict hf hg hlt

/-- HK-13 (part 1a, `StageCore.w_jump` shape — D.1(b) tie law 2): residual cancellation at
a weight jump — equal weights, strictly larger sum weight ⇒ `R f + R g = 0` at `bR`.
[Blueprint BP2 HK-13; supply: U31's `bR_add`/NF machinery.] -/
theorem bStageP_w_jump :
    ∀ f g : Polynomial ℤ_[2], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      bStageP.w f = bStageP.w g → bStageP.w f < bStageP.w (f + g) →
      bStageP.R f + bStageP.R g = 0 := by
  intro f g hf hg hfg hw hlt
  exact HK13R.bR_jump hf hg hfg hw hlt

/-- HK-13 (part 1a, `StageCore.R_neg` shape — D.1(b) tie law 3): `R (−f) = −R f` at `bR`
(mod-2 reduction of the θ-cofactor; note at characteristic 2 the two sides coincide with
`R f` — still the law's shape).  [Blueprint BP2 HK-13.] -/
theorem bStageP_R_neg :
    ∀ f : Polynomial ℤ_[2], bStageP.R (-f) = - bStageP.R f := by
  intro f
  exact HK13R.bR_negf f

/-- HK-13 (part 1a, `StageCore.prevIaug` shape): (I-aug) at the read that created the base
stage — `e·wPrev Φ < h`, i.e. `1·gaussVal X = 0 < 1`.  (At the OLD `wPrev := bw` this was
REFUTED — `bw X = 1`; the re-dress restores the base case of the StageCore docstring:
"base: `wPrev(φ) = v(φ) = 0 < h`".)  [Blueprint BP2 HK-13.] -/
theorem bStageP_prevIaug :
    (bStageP.e : ℤ) * bStageP.wPrev bStageP.Φ < (bStageP.h : ℤ) := by
  show ((1 : ℕ) : ℤ) * gaussVal (X : Polynomial ℤ_[2]) < ((1 : ℕ) : ℤ)
  rw [HK13R.gaussVal_X]
  norm_num

end LeanUrat.MovesJ
