/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.LaurentOrd
import LeanUrat.Moves.L2_widthBound
import LeanUrat.Moves.L0_GRg
import LeanUrat.Moves.L3_liftResidual

/-!
# Moves/ResVal — the (w,R) residual-valuation engine, proved ONCE (SYN-E2/E3/E4, C1 cluster)

The no-cancellation kernel previously re-derived as `private` lemmas in ≥ 9 files
(census + statement-level concordance: `lean/notes/SYN_E0_CONCORDANCE_2026-07-30.md`;
plan: SYNTHESIS_PASS1 PART 2 C1, ratified BRIDGE_ADJUDICATIONS 2026-07-30).

## Layout

* `ResValPack p K` — the bare law pack `(w, R, hwmul, hwult, hRne, hRmul, hRadd, hRlt)`.
  LAW CENSUS (SYN-E0 §4): the plan's five laws PLUS `hRne` (needed by `R_one`'s
  Laurent-domain cancellation; both attested carriers prove it). `hR0` is consumed by
  no engine lemma and is omitted. `w`-codomain ℤ (SYN-E0 §5: no ℚ-valued copy exists).
* `ult_sum_ge` — the bare ultrametric finite-sum bound, VERBATIM from
  `L4_TRANSi_R3.wsum_ge'` (the weakest-assumption copy on disk); the single proof
  source for every `w_sum_ge`-family copy.
* `ResValPack.*` — the arithmetic nine + `w_sum_ge` + the distinct-position machine
  `residual_sum_machine` (SYN-E3; VERBATIM from `L5_landVertex` = `L5_landVertexDigit`,
  re-keyed `σ.w/σ.R ↦ P.w/P.R` — the ratified pack parameterization) + its monomial
  instance `decomp_machine` (statement from `HC2/SharedRecenter`, now DERIVED from the
  machine; per-conjunct record on `decomp_machine`).
* `Stage.pack` — the `Stage` instance (rfl-fields; SYN-E4). The `ReadFrame` instance
  lives at `HC1/V34_readKernel.lean` (import direction). Non-vacuity of the pack rides
  the existing `Stage` non-vacuity witnesses via `Stage.pack` (no new axiom surface).
* `ResVal.*` — Stage-keyed wrappers with the EXACT classic private statements
  (zero-churn migration targets), plus the deep Stage-keyed engine lemmas hoisted
  VERBATIM from `L3_K1` (= `L5_landTwoSided_repair`, statement-identical):
  `psiNotDvd`, `w_Phat`, `cslot`, `key_no_cancel`, `minsum_facts`.

Consumers `open LeanUrat.Moves.ResVal` (namespace-fenced — the R2/MovesGr shadowing
lesson; in particular NO collision with `LeanUrat.MovesJ.SharedRecenter`'s public
names, whose home file re-exports from here since SYN-M9).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

namespace LeanUrat.Moves

open Polynomial LaurentOrd

universe u

/-! ## The pack (SYN-E2) -/

/-- **The residual-valuation law pack**: a ℤ-valued weight `w` and a Laurent-valued
residual map `R` on `ℤ_[p][X]`, subject to the bare no-cancellation laws. Field list
fixed by the SYN-E0 concordance (§4): `hwmul`, `hwult`, `hRne`, `hRmul`, `hRadd`,
`hRlt`. Instances: `Stage.pack` (below), `ReadFrame.pack` (`HC1/V34_readKernel`),
and (queued, SYN-F1) the σV regrade via its `RegradeOf` record. -/
structure ResValPack (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] where
  /-- the stage/frame valuation (values on nonzero elements) -/
  w : Polynomial ℤ_[p] → ℤ
  /-- the residual map into the current field's Laurent ring -/
  R : Polynomial ℤ_[p] → LaurentPolynomial K
  hwmul : ∀ f g, f ≠ 0 → g ≠ 0 → w (f * g) = w f + w g
  hwult : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → min (w f) (w g) ≤ w (f + g)
  hRne : ∀ f, f ≠ 0 → R f ≠ 0
  hRmul : ∀ f g, f ≠ 0 → g ≠ 0 → R (f * g) = R f * R g
  hRadd : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → w f = w g → w (f + g) = w f →
            R (f + g) = R f + R g
  hRlt : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → w f < w g → R (f + g) = R f

/-- **Ultrametric finite-sum lower bound, bare form** — VERBATIM hoist of
`L4_TRANSi_R3.wsum_ge'` (SYN-E0: the weakest-assumption copy; every other
`w_sum_ge`-family copy is a specialization, recorded per migration). -/
lemma ult_sum_ge {p : ℕ} [Fact p.Prime] {ι : Type*} (W : Polynomial ℤ_[p] → ℤ)
    (hult : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → min (W f) (W g) ≤ W (f + g))
    (S : Finset ι) (a : ι → Polynomial ℤ_[p]) (c : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → c ≤ W (a j)) (hsum : (∑ j ∈ S, a j) ≠ 0) :
    c ≤ W (∑ j ∈ S, a j) := by
  classical
  revert hm hsum
  induction S using Finset.induction with
  | empty =>
    intro _ hsum
    exact absurd Finset.sum_empty hsum
  | insert i T hiT ih =>
    intro hm hsum
    rw [Finset.sum_insert hiT] at hsum ⊢
    by_cases hai : a i = 0
    · rw [hai, zero_add] at hsum ⊢
      exact ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsum
    · by_cases hsT : (∑ j ∈ T, a j) = 0
      · rw [hsT, add_zero] at hsum ⊢
        exact hm i (Finset.mem_insert_self i T) hai
      · have h1 : c ≤ W (a i) := hm i (Finset.mem_insert_self i T) hai
        have h2 : c ≤ W (∑ j ∈ T, a j) :=
          ih (fun j hj hj0 => hm j (Finset.mem_insert_of_mem hj) hj0) hsT
        exact le_trans (le_min h1 h2) (hult (a i) (∑ j ∈ T, a j) hai hsT hsum)

namespace ResValPack

variable {p : ℕ} [Fact p.Prime] {K : Type u} [Field K]

/-- `w 1 = 0`: from `w(1·1) = w 1 + w 1`. [Proof source: `L3_K1.w_one`, pack-keyed.] -/
lemma w_one (P : ResValPack p K) : P.w 1 = 0 := by
  have h := P.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/-- `w (-1) = 0`. [Proof source: `SharedRecenter.w_neg_one`, pack-keyed.] -/
lemma w_neg_one (P : ResValPack p K) : P.w (-1) = 0 := by
  have h := P.hwmul (-1) (-1) (by norm_num) (by norm_num)
  rw [neg_mul_neg, one_mul, P.w_one] at h
  omega

/-- `w(−f) = w f`. [Proof source: `L3_K1.w_neg`, pack-keyed.] -/
lemma w_neg (P : ResValPack p K) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) : P.w (-f) = P.w f := by
  have h := P.hwmul (-1) f (neg_ne_zero.mpr one_ne_zero) hf
  rw [neg_one_mul] at h
  rw [h, P.w_neg_one, zero_add]

/-- `w(f^n) = n·w f`. [Proof source: `L3_K1.w_pow`, pack-keyed.] -/
lemma w_pow (P : ResValPack p K) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (n : ℕ) :
    P.w (f ^ n) = (n : ℤ) * P.w f := by
  induction n with
  | zero => rw [pow_zero, P.w_one, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [pow_succ, P.hwmul _ _ (pow_ne_zero k hf) hf, ih]
    push_cast
    ring

/-- `R 1 = 1` (from `hRmul` + `hRne`, cancellation in the Laurent domain).
[Proof source: `L3_K1.R_one`, pack-keyed.] -/
lemma R_one (P : ResValPack p K) : P.R (1 : Polynomial ℤ_[p]) = 1 := by
  have h := P.hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  exact (mul_eq_left₀ (P.hRne 1 one_ne_zero)).mp h.symm

/-- `R(−1)² = 1`. (Only THIS is needed downstream — never the sign of `R(−1)`.)
[Proof source: `L3_K1.R_negone_sq`, pack-keyed.] -/
lemma R_neg_one_sq (P : ResValPack p K) : P.R (-1 : Polynomial ℤ_[p]) * P.R (-1) = 1 := by
  have h := P.hRmul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
  rw [neg_mul_neg, one_mul, P.R_one] at h
  exact h.symm

/-- `R(−f) = R(−1)·R(f)`. [Proof source: `L3_K1.R_neg`, pack-keyed.] -/
lemma R_neg (P : ResValPack p K) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    P.R (-f) = P.R (-1) * P.R f := by
  have h := P.hRmul (-1) f (neg_ne_zero.mpr one_ne_zero) hf
  rw [neg_one_mul] at h
  exact h

/-- `R(f^n) = R(f)^n`. [Proof source: `L3_K1.R_pow` (= the `L0.GRe` inline), pack-keyed.] -/
lemma R_pow (P : ResValPack p K) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (n : ℕ) :
    P.R (f ^ n) = (P.R f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, P.R_one]
  | succ k ih =>
    have hfk : f ^ k ≠ 0 := pow_ne_zero k hf
    rw [pow_succ, P.hRmul (f ^ k) f hfk hf, ih, ← pow_succ]

/-- **Ultrametric finite-sum lower bound** at the pack (specializes `ult_sum_ge`). -/
lemma w_sum_ge (P : ResValPack p K)
    (S : Finset ℕ) (a : ℕ → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ P.w (a j)) (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ P.w (∑ j ∈ S, a j) :=
  ult_sum_ge P.w P.hwult S a m hm hsum

/-- **The residual-sum machine (SYN-E3).** Terms of common weight `m`, with residuals
that can never satisfy `R(a_j) = u·Σ_{l∈T} R(a_l)` for `u² = 1` (`j ∉ T`), have all
sub-sums nonzero of weight `m` and residual the sum of the residuals. Cancellation
cases reduce, via `hRlt` applied to the negated partial sum (the ε-trick, `ε := R(−1)`,
`ε² = 1`), exactly to the excluded shape.
[VERBATIM hoist of `L5_landVertex.residual_sum_machine` (= `L5_landVertexDigit`,
byte-identical), re-keyed `σ ↦ P` per the ratified pack parameterization.] -/
lemma residual_sum_machine (P : ResValPack p K) (m : ℤ) (a : ℕ → Polynomial ℤ_[p])
    (S : Finset ℕ)
    (hSne : ∀ j ∈ S, a j ≠ 0) (hSw : ∀ j ∈ S, P.w (a j) = m)
    (hsep : ∀ j ∈ S, ∀ T ⊆ S, T.Nonempty → j ∉ T →
        ∀ u : LaurentPolynomial K, u * u = 1 → P.R (a j) ≠ u * ∑ l ∈ T, P.R (a l)) :
    ∀ T ⊆ S, T.Nonempty →
      (∑ j ∈ T, a j) ≠ 0 ∧ P.w (∑ j ∈ T, a j) = m ∧
        P.R (∑ j ∈ T, a j) = ∑ j ∈ T, P.R (a j) := by
  classical
  intro T
  induction T using Finset.induction with
  | empty =>
    intro _ hne
    exact absurd hne (by simp)
  | insert j T hjT ih =>
    intro hsub _
    have hjS : j ∈ S := hsub (Finset.mem_insert_self j T)
    have hTsub : T ⊆ S := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    have haj : a j ≠ 0 := hSne j hjS
    have hwj : P.w (a j) = m := hSw j hjS
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · refine ⟨by simpa using haj, by simpa using hwj, by simp⟩
    · obtain ⟨hT0, hTw, hTR⟩ := ih hTsub hTne
      have hcontra : P.R (a j) ≠ P.R (-1) * ∑ l ∈ T, P.R (a l) :=
        hsep j hjS T hTsub hTne hjT (P.R (-1)) (P.R_neg_one_sq)
      have hRST : P.R (-(∑ l ∈ T, a l)) = P.R (-1) * ∑ l ∈ T, P.R (a l) := by
        rw [P.R_neg _ hT0, hTR]
      have hne0 : a j + ∑ l ∈ T, a l ≠ 0 := by
        intro h0
        have haj_eq : a j = -(∑ l ∈ T, a l) := eq_neg_of_add_eq_zero_left h0
        exact hcontra (by rw [haj_eq, hRST])
      have hwmin : m ≤ P.w (a j + ∑ l ∈ T, a l) := by
        have h := P.hwult (a j) _ haj hT0 hne0
        rwa [hwj, hTw, min_self] at h
      have hwsum : P.w (a j + ∑ l ∈ T, a l) = m := by
        by_contra hne'
        have hlt : m < P.w (a j + ∑ l ∈ T, a l) := lt_of_le_of_ne hwmin (Ne.symm hne')
        have hnST : -(∑ l ∈ T, a l) ≠ 0 := neg_ne_zero.mpr hT0
        have heq : -(∑ l ∈ T, a l) + (a j + ∑ l ∈ T, a l) = a j := by ring
        have hR := P.hRlt (-(∑ l ∈ T, a l)) (a j + ∑ l ∈ T, a l) hnST hne0
          (by rw [heq]; exact haj) (by rw [P.w_neg _ hT0, hTw]; exact hlt)
        rw [heq] at hR
        exact hcontra (by rw [hR, hRST])
      have hRadd := P.hRadd (a j) _ haj hT0 hne0 (by rw [hwj, hTw]) (by rw [hwsum, hwj])
      refine ⟨?_, ?_, ?_⟩
      · rwa [Finset.sum_insert hjT]
      · rwa [Finset.sum_insert hjT]
      · rw [Finset.sum_insert hjT, Finset.sum_insert hjT, hRadd, hTR]

end ResValPack

/-! ## Laurent coefficient-extraction seams (used by the monomial instance) -/

namespace ResVal

/-- Coefficient extraction on a monomial `C c · T n` (the Finsupp seam, crossed by
`exact`-defeq only). [VERBATIM from `HC2/SharedRecenter.CT_apply`.] -/
lemma CT_apply {K : Type*} [Field K] (c : K) (n q : ℤ) :
    (LaurentPolynomial.C c * LaurentPolynomial.T n : LaurentPolynomial K) q
      = if n = q then c else 0 := by
  have h1 : LaurentPolynomial.C c * LaurentPolynomial.T n
      = (Finsupp.single n c : LaurentPolynomial K) :=
    (LaurentPolynomial.single_eq_C_mul_T c n).symm
  have h0 := congrArg (fun t : ℤ →₀ K => t q) h1
  exact h0.trans Finsupp.single_apply

/-- Coefficient extraction commutes with finite sums (Finsupp seam).
[VERBATIM from `HC2/SharedRecenter.sum_apply'`.] -/
lemma sum_apply' {K : Type*} [Field K] (T : Finset ℕ) (g : ℕ → LaurentPolynomial K)
    (q : ℤ) : (∑ l ∈ T, g l) q = ∑ l ∈ T, (g l) q :=
  Finsupp.finset_sum_apply T g q

/-- `C` is injective (coefficient at 0). [VERBATIM from `HC2/SharedRecenter.C_inj`.] -/
lemma C_inj {K : Type*} [Field K] {x y : K}
    (h : (LaurentPolynomial.C x : LaurentPolynomial K) = LaurentPolynomial.C y) : x = y := by
  have hCT : ∀ z : K, (LaurentPolynomial.C z : LaurentPolynomial K)
      = LaurentPolynomial.C z * LaurentPolynomial.T 0 := by
    intro z
    rw [LaurentPolynomial.T_zero, mul_one]
  have h0 : (LaurentPolynomial.C x : LaurentPolynomial K) (0 : ℤ)
      = (LaurentPolynomial.C y : LaurentPolynomial K) (0 : ℤ) := by rw [h]
  rwa [hCT x, hCT y, CT_apply, CT_apply, if_pos rfl, if_pos rfl] at h0

end ResVal

namespace ResValPack

variable {p : ℕ} [Fact p.Prime] {K : Type u} [Field K]

/-- **The distinct-position monomial machine**: nonzero terms of one common weight `m`
whose residuals are monomials at pairwise-distinct positions sum without cancellation.
STATEMENT from `HC2/SharedRecenter.decomp_machine` (pack-keyed, `↥σ.K ↦ K`); the body
is now DERIVED from `residual_sum_machine` — the separation hypothesis is discharged by
coefficient extraction at the fresh position (`u² = 1 ⟹ u = ±1` in the Laurent domain,
so `u·Σ` stays supported off `pos j`). Per-conjunct record: conclusion conjuncts 1–3
are literally the machine's; `(d, hd)` are RETAINED binders for statement fidelity to
the SharedRecenter original (the new proof does not consume them — the domain argument
replaces the constant-`R(−1)` argument, a PROVED strengthening, not a weakening). -/
lemma decomp_machine (P : ResValPack p K) (d : K)
    (hd : P.R (-1) = LaurentPolynomial.C d)
    (m : ℤ) (a : ℕ → Polynomial ℤ_[p]) (pos : ℕ → ℤ) (c : ℕ → K) (S : Finset ℕ)
    (h0 : ∀ j ∈ S, a j ≠ 0) (hw : ∀ j ∈ S, P.w (a j) = m)
    (hR : ∀ j ∈ S, P.R (a j) = LaurentPolynomial.C (c j) * LaurentPolynomial.T (pos j))
    (hc : ∀ j ∈ S, c j ≠ 0)
    (hinj : ∀ j ∈ S, ∀ k ∈ S, pos j = pos k → j = k) :
    ∀ T ⊆ S, T.Nonempty →
      (∑ j ∈ T, a j) ≠ 0 ∧ P.w (∑ j ∈ T, a j) = m ∧
        P.R (∑ j ∈ T, a j)
          = ∑ j ∈ T, LaurentPolynomial.C (c j) * LaurentPolynomial.T (pos j) := by
  classical
  have hsep : ∀ j ∈ S, ∀ T ⊆ S, T.Nonempty → j ∉ T →
      ∀ u : LaurentPolynomial K, u * u = 1 → P.R (a j) ≠ u * ∑ l ∈ T, P.R (a l) := by
    intro j hjS T hTsub hTne hjT u hu heq
    have hcoeff_j : (P.R (a j)) (pos j) = c j := by
      rw [hR j hjS, ResVal.CT_apply, if_pos rfl]
    -- the C-scalar form of the flip (uniform in the sign u = ±1)
    have key : ∀ u0 : K, P.R (a j) = LaurentPolynomial.C u0 * (∑ l ∈ T, P.R (a l)) →
        False := by
      intro u0 heq0
      have hsingles : LaurentPolynomial.C u0 * (∑ l ∈ T, P.R (a l))
          = ∑ l ∈ T, LaurentPolynomial.C (u0 * c l) * LaurentPolynomial.T (pos l) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        rw [hR l (hTsub hl), ← mul_assoc, ← map_mul]
      have h3 : (P.R (a j)) (pos j) = 0 := by
        rw [heq0, hsingles, ResVal.sum_apply']
        refine Finset.sum_eq_zero (fun l hl => ?_)
        rw [ResVal.CT_apply,
          if_neg (fun hpe => hjT ((hinj l (hTsub hl) j hjS hpe) ▸ hl))]
      exact hc j hjS (hcoeff_j.symm.trans h3)
    rcases mul_self_eq_one_iff.mp hu with rfl | rfl
    · exact key 1 (by rw [map_one]; exact heq)
    · exact key (-1) (by rw [map_neg, map_one]; exact heq)
  intro T hTsub hTne
  obtain ⟨h1, h2, h3⟩ := P.residual_sum_machine m a S h0 hw hsep T hTsub hTne
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  exact Finset.sum_congr rfl (fun l hl => hR l (hTsub hl))

end ResValPack

/-! ## The `Stage` instance (SYN-E4) -/

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **The `Stage` instance of the pack** (SYN-E4): fields are `σ.w`/`σ.R` and the
stage's own laws — definitional (every field a projection; `Stage.pack σ |>.w ≡ σ.w`
by `rfl`). Non-vacuity rides the existing compiled `Stage` witnesses. -/
def Stage.pack (σ : Stage p F) : ResValPack p ↥σ.K where
  w := σ.w
  R := σ.R
  hwmul := σ.hwmul
  hwult := σ.hwult
  hRne := σ.hRne
  hRmul := σ.hRmul
  hRadd := σ.hRadd
  hRlt := σ.hRlt

namespace ResVal

/-! ## Stage-keyed wrappers (zero-churn migration targets; statements are the exact
classic private statements per the SYN-E0 table, bodies = `Stage.pack` applications) -/

/-- `w 1 = 0`. [= the classic private; single proof source `ResValPack.w_one`.] -/
lemma w_one (σ : Stage p F) : σ.w 1 = 0 := σ.pack.w_one

/-- `w (-1) = 0`. -/
lemma w_neg_one (σ : Stage p F) : σ.w (-1) = 0 := σ.pack.w_neg_one

/-- `w(−f) = w f`. -/
lemma w_neg (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) : σ.w (-f) = σ.w f :=
  σ.pack.w_neg f hf

/-- `w(f^n) = n·w f`. -/
lemma w_pow (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (n : ℕ) :
    σ.w (f ^ n) = (n : ℤ) * σ.w f := σ.pack.w_pow f hf n

/-- `R 1 = 1`. -/
lemma R_one (σ : Stage p F) : σ.R (1 : Polynomial ℤ_[p]) = 1 := σ.pack.R_one

/-- `R(−1)² = 1` (K1/TS name). -/
lemma R_negone_sq (σ : Stage p F) : σ.R (-1 : Polynomial ℤ_[p]) * σ.R (-1) = 1 :=
  σ.pack.R_neg_one_sq

/-- `R(−1)² = 1` (landBox/landVertex name; same statement as `R_negone_sq`). -/
lemma R_neg_one_sq (σ : Stage p F) : σ.R (-1) * σ.R (-1) = 1 := σ.pack.R_neg_one_sq

/-- `R(−f) = R(−1)·R(f)`. -/
lemma R_neg (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) :
    σ.R (-f) = σ.R (-1) * σ.R f := σ.pack.R_neg f hf

/-- `R(f^n) = R(f)^n`. -/
lemma R_pow (σ : Stage p F) (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (n : ℕ) :
    σ.R (f ^ n) = (σ.R f) ^ n := σ.pack.R_pow f hf n

/-- **Ultrametric finite-sum lower bound** (K1 form). -/
lemma w_sum_ge (σ : Stage p F)
    (S : Finset ℕ) (a : ℕ → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ σ.w (a j)) (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ σ.w (∑ j ∈ S, a j) := σ.pack.w_sum_ge S a m hm hsum

/-- **The residual-sum machine** at a stage (landVertex/landVertexDigit form). -/
lemma residual_sum_machine (σ : Stage p F) (m : ℤ) (a : ℕ → Polynomial ℤ_[p])
    (S : Finset ℕ)
    (hSne : ∀ j ∈ S, a j ≠ 0) (hSw : ∀ j ∈ S, σ.w (a j) = m)
    (hsep : ∀ j ∈ S, ∀ T ⊆ S, T.Nonempty → j ∉ T →
        ∀ u : LaurentPolynomial ↥σ.K, u * u = 1 → σ.R (a j) ≠ u * ∑ l ∈ T, σ.R (a l)) :
    ∀ T ⊆ S, T.Nonempty →
      (∑ j ∈ T, a j) ≠ 0 ∧ σ.w (∑ j ∈ T, a j) = m ∧
        σ.R (∑ j ∈ T, a j) = ∑ j ∈ T, σ.R (a j) :=
  σ.pack.residual_sum_machine m a S hSne hSw hsep

/-! ## The deep Stage-keyed engine (VERBATIM hoists from `L3_K1` = `L5_landTwoSided_repair`) -/

/-- ψ ∤ R(B) for a nonzero below-`Φ̂`-width coefficient `B`.
[VERBATIM hoist of `L3_K1.psiNotDvd` (= `L5_landTwoSided_repair.psiNotDvd` =
`L5_landBox.landBox_psiNotDvd`, statement-identical); the `L5_landVertex{Digit}`
variant carries a redundant `hg1` hypothesis, dropped at its call sites (SYN-E0 §3).] -/
theorem psiNotDvd (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g)
    (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (B : Polynomial ℤ_[p])
    (hB : B ≠ 0) (hBdeg : B.natDegree < σ.e * g * σ.Φ.natDegree) :
    ¬ (Polynomial.toLaurent ψ ∣ σ.R B) := by
  classical
  intro hdvd
  have hgpos : 0 < ψ.natDegree := hψ.natDegree_pos
  have hg1 : 1 ≤ g := by omega
  obtain ⟨a, ha⟩ := L2_widthBound σ g hg1 B hB hBdeg
  obtain ⟨Ranch, hRdeg, hRB⟩ := L0_GRg (σ.hRne B hB) a g ha
  have hRanch_ne : Ranch ≠ 0 := by
    intro h
    rw [h, map_zero, mul_zero] at hRB
    exact σ.hRne B hB hRB
  have hdvdR : Polynomial.toLaurent ψ ∣ Polynomial.toLaurent Ranch := by
    have h := hdvd.mul_left (LaurentPolynomial.T (-a))
    rwa [hRB, ← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel,
      LaurentPolynomial.T_zero, one_mul] at h
  obtain ⟨q, hq⟩ := hdvdR
  obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow q
  have hkey : Ranch * Polynomial.X ^ n = ψ * f' := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, map_mul, Polynomial.toLaurent_X_pow, hq, mul_assoc, ← hf']
  have hdiv : ψ ∣ Ranch * Polynomial.X ^ n := ⟨f', hkey⟩
  have hprime : Prime ψ := hψ.prime
  have hnotdvdX : ¬ (ψ ∣ Polynomial.X) := by
    intro hdX
    exact hψz (Polynomial.eq_of_monic_of_associated hmon Polynomial.monic_X
      (hψ.associated_of_dvd Polynomial.irreducible_X hdX))
  rcases hprime.dvd_or_dvd hdiv with h1 | h2
  · have hle := Polynomial.natDegree_le_of_dvd h1 hRanch_ne
    omega
  · exact hnotdvdX (hprime.dvd_of_dvd_pow h2)

/-- `w(Φ̂) = e·h·g`: all present slots of the displayed `Φ`-development of `Φ̂` are tied
at `ehg`, so `hK1` at `Φ` pins the weight.
[VERBATIM hoist of `L3_K1.w_Phat` (= `L3_liftWeight` = `L5_landVertex{Digit}.liftWeight_local`,
statement-identical); `L5_landBox.w_lift` reorders binders and omits `hg1`
(the g = 0 strengthening is unconsumed — not hoisted, SYN-E0 §3);
`L5_landTwoSided_repair.w_Phat_priv` carries unused extra hypotheses, dropped at its
call sites.] -/
lemma w_Phat (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg1 : 1 ≤ g)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0) :
    σ.w Φhat = (σ.e : ℤ) * σ.h * g := by
  classical
  obtain ⟨hψmon, hψdeg, tt, htt0, httk, hΦhat⟩ := hlift
  set cc : ℕ → Polynomial ℤ_[p] := fun k => if k = g then 1 else tt k with hccdef
  set B : ℕ → Polynomial ℤ_[p] :=
    (fun j => ∑ k ∈ Finset.range (g + 1), if j = σ.e * k then cc k else 0) with hBdef
  have hccg : cc g = 1 := by simp [hccdef]
  have hcck : ∀ k, k < g → cc k = tt k := by
    intro k hk; simp only [hccdef]; rw [if_neg (by omega : k ≠ g)]
  have hΦ0 : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hΦdegbot : (⊥ : WithBot ℕ) < σ.Φ.degree :=
    bot_lt_iff_ne_bot.mpr (fun h => hΦ0 (Polynomial.degree_eq_bot.mp h))
  have hΦdeg0 : (0 : WithBot ℕ) < σ.Φ.degree := by
    rw [Polynomial.degree_eq_natDegree hΦ0]
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one σ.hdeg
  have hccdeg : ∀ k, k ≤ g → (cc k).degree < σ.Φ.degree := by
    intro k hk
    by_cases hkg : k = g
    · rw [hkg, hccg, Polynomial.degree_one]; exact hΦdeg0
    · have hklt : k < g := lt_of_le_of_ne hk hkg
      rw [hcck k hklt]
      by_cases hcoef : ψ.coeff k = 0
      · rw [htt0 k hcoef, Polynomial.degree_zero]; exact hΦdegbot
      · obtain ⟨-, hinC, -, -⟩ := httk k hklt hcoef
        exact hinC
  have hw1 : σ.w 1 = 0 := w_one σ
  have hsum : ∑ j ∈ Finset.range (σ.e * g + 1), B j * σ.Φ ^ j
      = (∑ k ∈ Finset.range g, tt k * σ.Φ ^ (σ.e * k)) + σ.Φ ^ (σ.e * g) := by
    have step1 : ∑ j ∈ Finset.range (σ.e * g + 1), B j * σ.Φ ^ j
        = ∑ k ∈ Finset.range (g + 1), cc k * σ.Φ ^ (σ.e * k) := by
      simp only [hBdef, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hmem : σ.e * k ∈ Finset.range (σ.e * g + 1) := by
        rw [Finset.mem_range]
        have : σ.e * k ≤ σ.e * g := Nat.mul_le_mul (le_refl σ.e) (by omega)
        omega
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq', if_pos hmem]
    rw [step1, Finset.sum_range_succ, hccg, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hcck k (Finset.mem_range.mp hk)]
  have hDev : IsDevelopment σ.Φ Φhat B (σ.e * g + 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      simp only [hBdef]
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff hΦdegbot]
      intro k hk
      rw [Finset.mem_range] at hk
      by_cases hjk : j = σ.e * k
      · rw [if_pos hjk]; exact hccdeg k (by omega)
      · rw [if_neg hjk, Polynomial.degree_zero]; exact hΦdegbot
    · intro j hj
      simp only [hBdef]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      apply if_neg
      intro hjk
      have hkg : σ.e * k ≤ σ.e * g := Nat.mul_le_mul (le_refl σ.e) (by omega)
      omega
    · rw [hΦhat, hsum]; ring
  have hSMA := σ.hK1 Φhat B (σ.e * g + 1) hΦne hDev
  obtain ⟨-, j₀, hj₀N, hj₀nz, hj₀eq⟩ := hSMA
  have hsumnz : (∑ k ∈ Finset.range (g + 1), if j₀ = σ.e * k then cc k else 0) ≠ 0 := by
    simpa only [hBdef] using hj₀nz
  obtain ⟨k₀, hk₀mem, hk₀ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumnz
  rw [Finset.mem_range] at hk₀mem
  have hcond : j₀ = σ.e * k₀ := by
    by_contra h
    exact hk₀ne (if_neg h)
  rw [if_pos hcond] at hk₀ne
  have hBval : B j₀ = cc k₀ := by
    simp only [hBdef]
    rw [Finset.sum_eq_single k₀]
    · rw [if_pos hcond]
    · intro k _ hkne
      exact if_neg (fun hh => hkne (Nat.eq_of_mul_eq_mul_left σ.he (hh.symm.trans hcond)))
    · exact fun h => absurd (Finset.mem_range.mpr hk₀mem) h
  rw [hj₀eq]
  change σ.w (B j₀) + (↑j₀ : ℤ) * σ.w σ.Φ = (σ.e : ℤ) * σ.h * g
  rw [hBval, hcond, σ.hwΦ]
  by_cases hk₀g : k₀ = g
  · rw [hk₀g, hccg, hw1]
    push_cast; ring
  · have hk₀lt : k₀ < g := lt_of_le_of_ne (by omega) hk₀g
    have httne : tt k₀ ≠ 0 := by rw [hcck k₀ hk₀lt] at hk₀ne; exact hk₀ne
    have hcoefne : ψ.coeff k₀ ≠ 0 := fun hc => httne (htt0 k₀ hc)
    obtain ⟨-, hinC, hwprev, -⟩ := httk k₀ hk₀lt hcoefne
    rw [hcck k₀ hk₀lt, σ.hStretch (tt k₀) httne hinC, hwprev]
    push_cast; ring

/-- The residual slot coefficient `c_j = R(B_j)·z^{j·m̂}` (`m̂ = −thg`), so that
`R(B_j·Φ̂^j) = c_j·ψ(z)^j`. [VERBATIM hoist of `L3_K1.cslot` (= `L5_landTwoSided_repair`).] -/
noncomputable def cslot (σ : Stage p F) (g : ℕ) (B : ℕ → Polynomial ℤ_[p]) (j : ℕ) :
    LaurentPolynomial ↥σ.K :=
  σ.R (B j) * LaurentPolynomial.T ((j : ℤ) * (-σ.t * (σ.h : ℤ) * (g : ℤ)))

/-- **The no-cancellation engine.** For development coefficients `B_j` (width < `deg Φ̂`),
no relation `Σ_{j∈T} R(B_j Φ̂^j) = R(−1)·R(B_i Φ̂^i)` with `i ∉ T` can hold.
[VERBATIM hoist of `L3_K1.key_no_cancel` (= `L5_landTwoSided_repair`, statement-identical).] -/
lemma key_no_cancel (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0)
    (hDeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (B : ℕ → Polynomial ℤ_[p]) (hdeg : ∀ j, (B j).degree < Φhat.degree)
    (i : ℕ) (T : Finset ℕ) (hiT : i ∉ T) (hBi : B i ≠ 0) (hBT : ∀ j ∈ T, B j ≠ 0) :
    (∑ j ∈ T, σ.R (B j * Φhat ^ j)) ≠ σ.R (-1) * σ.R (B i * Φhat ^ i) := by
  intro heq
  have hTne0 : ∀ n : ℤ, (LaurentPolynomial.T n : LaurentPolynomial ↥σ.K) ≠ 0 :=
    fun n => (LaurentPolynomial.isUnit_T n).ne_zero
  have hRhat := L3_liftResidual σ ψ g Φhat hlift
  -- the residual slot identity R(B_j Φ̂^j) = c_j ψ^j
  have hRa : ∀ j, B j ≠ 0 →
      σ.R (B j * Φhat ^ j) = cslot σ g B j * Polynomial.toLaurent ψ ^ j := by
    intro j hBj
    unfold cslot
    rw [σ.hRmul _ _ hBj (pow_ne_zero j hΦne), R_pow σ Φhat hΦne j, hRhat, mul_pow,
      LaurentPolynomial.T_pow, ← mul_assoc]
  have hBdeg' : ∀ j, B j ≠ 0 → (B j).natDegree < σ.e * g * σ.Φ.natDegree := by
    intro j hBj
    have h := Polynomial.natDegree_lt_natDegree hBj (hdeg j)
    rwa [hDeg] at h
  have hc0 : ∀ j, B j ≠ 0 → cslot σ g B j ≠ 0 := by
    intro j hBj
    unfold cslot
    exact mul_ne_zero (σ.hRne _ hBj) (hTne0 _)
  have hcnd : ∀ j, B j ≠ 0 → ¬ (Polynomial.toLaurent ψ ∣ cslot σ g B j) := by
    intro j hBj hdvd
    unfold cslot at hdvd
    have h2 := hdvd.mul_right (LaurentPolynomial.T (-((j : ℤ) * (-σ.t * (σ.h : ℤ) * (g : ℤ)))))
    rw [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one] at h2
    exact psiNotDvd σ ψ g hg hmon hψ hψz (B j) hBj (hBdeg' j hBj) h2
  have hRm1 : σ.R (-1 : Polynomial ℤ_[p]) ≠ 0 := σ.hRne _ (neg_ne_zero.mpr one_ne_zero)
  -- the twisted coefficient certificates
  have hc' : ∀ j ∈ insert i T,
      (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j) ≠ 0 ∧
      ¬ (Polynomial.toLaurent ψ ∣
        (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjT
    · rw [if_pos rfl]
      refine ⟨neg_ne_zero.mpr (mul_ne_zero hRm1 (hc0 j hBi)), ?_⟩
      intro hdvd
      rw [dvd_neg] at hdvd
      have h2 := hdvd.mul_left (σ.R (-1))
      rw [← mul_assoc, R_negone_sq σ, one_mul] at h2
      exact hcnd j hBi h2
    · have hne : j ≠ i := by rintro rfl; exact hiT hjT
      rw [if_neg hne]
      exact ⟨hc0 j (hBT j hjT), hcnd j (hBT j hjT)⟩
  -- the vanishing distinct-ψ-order sum forced by `heq`
  have hsum0 : (∑ j ∈ insert i T,
      (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)
        * Polynomial.toLaurent ψ ^ j) = 0 := by
    rw [Finset.sum_insert hiT, if_pos rfl]
    have hrest : (∑ j ∈ T,
        (if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)
          * Polynomial.toLaurent ψ ^ j)
        = ∑ j ∈ T, σ.R (B j * Φhat ^ j) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hne : j ≠ i := by rintro rfl; exact hiT hj
      rw [if_neg hne, ← hRa j (hBT j hj)]
    rw [hrest, heq, hRa i hBi]
    ring
  exact GRf_priv ψ hψ hψz
    (fun j => if j = i then -(σ.R (-1) * cslot σ g B i) else cslot σ g B j)
    (insert i T) ⟨i, Finset.mem_insert_self i T⟩ hc' hsum0

/-- **Minimizing-slot subsums are honest** (the `=` core of K1): a nonempty sum of slot
terms `B_j Φ̂^j`, all of weight exactly `m`, is nonzero of weight exactly `m`, with
additive residuals. [VERBATIM hoist of `L3_K1.minsum_facts`
(= `L5_landTwoSided_repair`, statement-identical).] -/
lemma minsum_facts (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0)
    (hDeg : Φhat.natDegree = σ.e * g * σ.Φ.natDegree)
    (B : ℕ → Polynomial ℤ_[p]) (hdeg : ∀ j, (B j).degree < Φhat.degree) (m : ℤ) :
    ∀ S' : Finset ℕ, (∀ j ∈ S', B j ≠ 0) → (∀ j ∈ S', σ.w (B j * Φhat ^ j) = m) →
      S'.Nonempty →
      (∑ j ∈ S', B j * Φhat ^ j) ≠ 0 ∧ σ.w (∑ j ∈ S', B j * Φhat ^ j) = m ∧
        σ.R (∑ j ∈ S', B j * Φhat ^ j) = ∑ j ∈ S', σ.R (B j * Φhat ^ j) := by
  intro S'
  induction S' using Finset.induction with
  | empty => exact fun _ _ h => absurd h Finset.not_nonempty_empty
  | insert i T hiT ih =>
    intro hB' hw' _
    have hBi : B i ≠ 0 := hB' i (Finset.mem_insert_self i T)
    have hwi : σ.w (B i * Φhat ^ i) = m := hw' i (Finset.mem_insert_self i T)
    have hai : B i * Φhat ^ i ≠ 0 := mul_ne_zero hBi (pow_ne_zero i hΦne)
    have hBT : ∀ j ∈ T, B j ≠ 0 := fun j hj => hB' j (Finset.mem_insert_of_mem hj)
    have hwT : ∀ j ∈ T, σ.w (B j * Φhat ^ j) = m := fun j hj => hw' j (Finset.mem_insert_of_mem hj)
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · simp only [Finset.sum_insert (Finset.notMem_empty i), Finset.sum_empty, add_zero]
      exact ⟨hai, hwi, trivial⟩
    · obtain ⟨hsTne, hwsT, hRsT⟩ := ih hBT hwT hTne
      rw [Finset.sum_insert hiT, Finset.sum_insert hiT]
      -- (a) the subsum cannot vanish (else Σ_T R(a_j) = R(−1)·R(a_i), killed by key_no_cancel)
      have hsne : B i * Φhat ^ i + (∑ j ∈ T, B j * Φhat ^ j) ≠ 0 := by
        intro h0
        have hsTeq : (∑ j ∈ T, B j * Φhat ^ j) = -(B i * Φhat ^ i) :=
          eq_neg_of_add_eq_zero_right h0
        have hR1 : σ.R (∑ j ∈ T, B j * Φhat ^ j) = σ.R (-1) * σ.R (B i * Φhat ^ i) := by
          rw [hsTeq, R_neg σ _ hai]
        exact key_no_cancel σ ψ g hg hmon hψ hψz Φhat hlift hΦne hDeg B hdeg i T hiT hBi hBT
          (hRsT.symm.trans hR1)
      have hwge : m ≤ σ.w (B i * Φhat ^ i + ∑ j ∈ T, B j * Φhat ^ j) := by
        have h1 := σ.hwult _ _ hai hsTne hsne
        rwa [hwi, hwsT, min_self] at h1
      rcases eq_or_lt_of_le hwge with hweq | hwlt
      · -- weight stays at m: hRadd gives residual additivity
        refine ⟨hsne, hweq.symm, ?_⟩
        rw [σ.hRadd _ _ hai hsTne hsne (by rw [hwi, hwsT]) (by rw [hwi]; exact hweq.symm), hRsT]
      · -- (b) the weight cannot jump (else hRlt forces the same killed relation)
        exfalso
        have hnegne : -(∑ j ∈ T, B j * Φhat ^ j) ≠ 0 := neg_ne_zero.mpr hsTne
        have haux : -(∑ j ∈ T, B j * Φhat ^ j) + (B i * Φhat ^ i + ∑ j ∈ T, B j * Φhat ^ j)
            = B i * Φhat ^ i := by ring
        have hlt' : σ.w (-(∑ j ∈ T, B j * Φhat ^ j))
            < σ.w (B i * Φhat ^ i + ∑ j ∈ T, B j * Φhat ^ j) := by
          rwa [w_neg σ _ hsTne, hwsT]
        have hRlt := σ.hRlt _ _ hnegne hsne (by rw [haux]; exact hai) hlt'
        rw [haux, R_neg σ _ hsTne, hRsT] at hRlt
        have hfinal : (∑ j ∈ T, σ.R (B j * Φhat ^ j)) = σ.R (-1) * σ.R (B i * Φhat ^ i) := by
          rw [hRlt, ← mul_assoc, R_negone_sq σ, one_mul]
        exact key_no_cancel σ ψ g hg hmon hψ hψz Φhat hlift hΦne hDeg B hdeg i T hiT hBi hBT
          hfinal

end ResVal

end LeanUrat.Moves
