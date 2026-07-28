/-
Unit U22-E1.SAE_spanStrict_endpoint  (HC-2 campaign — blueprint §9 F-4 endpoint of U22;
NEW unit, census +1; statement landed in-file from the proven reduction and
PROVER-REFINABLE — the assembled `readsOf_SAE` in U22_SAE.lean is normative and
byte-unchanged)
moves_ref: §C rev 12 (SAE) display; the F-4 semantic spec — THE STRICT SPAN-ENTRY
ENDPOINT: "at every recorded span slot strictly below the parent vertex, f's actual
frame-weight strictly exceeds the parent line's value (the parent's (ZC)-zeroed-strips
content: interior zeros push actual valuations strictly above the old line)".
deps: D4 (`SideReads` at reads i and i+1), the parent's (ZC)-zeroed strips, K1 slot
reading.  difficulty: HARD (the genuine frontier of the F-4 reduction).
hypothesis_fields: none.
SCALE NOTE (C.1.0(c)): stage-(i+1) weights are `STR_{i+1} ×` absolute, and `Node.line`
is absolute v_p-scale — the strict inequality is stated multiplied through by
`H.strFrame (i+1)`.  The guard `B j ≠ 0` keeps the claim statable (`σ.w` of the zero
polynomial is junk; a vanished span coefficient exceeds every finite line value morally,
and the assembled proof consumes this endpoint only at slots SideReads(ii) makes
nonzero).

PROVED (E1 close round, 2026-07-28; statement BYTE-UNCHANGED).  Species dispatch on the
PARENT read, mirroring the K1 kernel's perimeter:
* RECENTERING parent — the honest leg: U20c's landed machine (the `g = 1` standard-lift
  view `Φ' = Φ − lift` of `ψ = X − C center` at the PARENT stage, the distinct-position
  residual-sum machine pinning the two side endpoints, whence the h-tie `ν.h = σ.h` and
  `σ.w f = γ`), with `L5_landVertex` swapped for **`L5_landBox`** — D.8's STRICT (BOX)
  clause below the vertex: `σ.w f < σ.w (B j) + j·σ.h` for `j < μ`, `B j ≠ 0`.  The
  recentered valuation is the parent valuation (`σ'.w = σ.w`), and the slope law +
  γ-tie + `hLineU` convert `γ − j·h < σ.w (B j)` to the fenced ℚ-form (the private
  helper block below is U20c's, cloned verbatim — its lemmas are file-private there).
* NON-RECENTERING parent — `HC1.V9_E1box_nonrec` (V9's REV-6 addition, same file as the
  kernel): the `e·g ≥ 2` legs close by the V10 INCONSISTENCY finding (vacuous perimeter
  — read V9's REV-4 disclosure; never cite those legs as transport mathematics),
  `i ≥ 1 ∧ e·g = 1` by the species inventory, and the genuine `i = 0 ∧ e·g = 1` corner
  by `v9c_cornerBox` — the strict Taylor-VANISHING sibling of the REV-5 corner core: a
  minimizing child slot `j < μ` would pin its nonzero digit to the `j`-th Taylor
  coefficient of `X^{s0}·Ranch` at the recorded root, which vanishes below the recorded
  ψ-order (`v9c_taylor_zero`; only the divisibility half of `hOrd` is consumed).
SideReads(iii) is consumed HERE only on the recentering leg (the anchor `σ.R f =
T(a)·Ranch` — exactly U20c's consumption perimeter; single-side reads, where the
U31-fenced rendering is faithful per the fence's own text).  ZERO axioms beyond
Lean core; no new `sorry` anywhere in the cone.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.Moves.L2_strideRule
import LeanUrat.Moves.L5_landBox
import LeanUrat.HC1.V9_K1nonrec

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

section U22E1Helpers
/- U20c's private helper block, cloned verbatim (those lemmas are file-private to
`U20c_NAtransportRecentering.lean`; this unit consumes the identical machine). -/

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `w 1 = 0`. -/
private lemma w_one (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/-- `w (-1) = 0`. -/
private lemma w_neg_one (σ : Stage p F) : σ.w (-1) = 0 := by
  have h := σ.hwmul (-1) (-1) (by norm_num) (by norm_num)
  rw [neg_mul_neg, one_mul, w_one σ] at h
  omega

/-- `w (-x) = w x`. -/
private lemma w_neg (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    σ.w (-x) = σ.w x := by
  have h := σ.hwmul (-1) x (by norm_num) hx
  rw [neg_one_mul] at h
  rw [h, w_neg_one σ, zero_add]

/-- `w (x^n) = n·w x`. -/
private lemma w_pow (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    σ.w (x ^ n) = (n : ℤ) * σ.w x := by
  induction n with
  | zero => simpa [pow_zero] using w_one σ
  | succ k ih =>
    rw [pow_succ, σ.hwmul _ x (pow_ne_zero k hx) hx, ih]
    push_cast; ring

/-- `R 1 = 1`. -/
private lemma R_one (σ : Stage p F) : σ.R 1 = 1 := by
  have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  have hne : σ.R 1 ≠ 0 := σ.hRne 1 one_ne_zero
  exact (mul_left_cancel₀ hne (by rw [mul_one]; exact h)).symm

/-- `R (-x) = R (-1) · R x`. -/
private lemma R_neg (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    σ.R (-x) = σ.R (-1) * σ.R x := by
  have h := σ.hRmul (-1) x (by norm_num) hx
  rwa [neg_one_mul] at h

/-- Ultrametric finite-sum lower bound (mirror of the `L5_landVertex` private lemma). -/
private lemma w_sum_ge (σ : Stage p F) (S : Finset ℕ) (a : ℕ → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ σ.w (a j)) (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ σ.w (∑ j ∈ S, a j) := by
  classical
  revert hm hsum
  induction S using Finset.induction with
  | empty =>
    intro hm hsum
    simp only [Finset.sum_empty] at hsum
    exact absurd rfl hsum
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
        have hult := σ.hwult (a i) (∑ j ∈ T, a j) hai hsT hsum
        exact le_trans (le_min h1 h2) hult

/-- Coefficient extraction on a monomial `C c · T n` (the Finsupp seam, crossed by
`exact`-defeq only). -/
private lemma CT_apply {K : Type*} [Field K] (c : K) (n q : ℤ) :
    (LaurentPolynomial.C c * LaurentPolynomial.T n : LaurentPolynomial K) q
      = if n = q then c else 0 := by
  have h1 : LaurentPolynomial.C c * LaurentPolynomial.T n
      = (Finsupp.single n c : LaurentPolynomial K) :=
    (LaurentPolynomial.single_eq_C_mul_T c n).symm
  have h0 := congrArg (fun t : ℤ →₀ K => t q) h1
  exact h0.trans Finsupp.single_apply

/-- Coefficient extraction commutes with finite sums (Finsupp seam). -/
private lemma sum_apply' {K : Type*} [Field K] (T : Finset ℕ) (g : ℕ → LaurentPolynomial K)
    (q : ℤ) : (∑ l ∈ T, g l) q = ∑ l ∈ T, (g l) q :=
  Finsupp.finset_sum_apply T g q

/-- `C` is injective (coefficient at 0). -/
private lemma C_inj {K : Type*} [Field K] {x y : K}
    (h : (LaurentPolynomial.C x : LaurentPolynomial K) = LaurentPolynomial.C y) : x = y := by
  have hCT : ∀ z : K, (LaurentPolynomial.C z : LaurentPolynomial K)
      = LaurentPolynomial.C z * LaurentPolynomial.T 0 := by
    intro z
    rw [LaurentPolynomial.T_zero, mul_one]
  have h0 : (LaurentPolynomial.C x : LaurentPolynomial K) (0 : ℤ)
      = (LaurentPolynomial.C y : LaurentPolynomial K) (0 : ℤ) := by rw [h]
  rwa [hCT x, hCT y, CT_apply, CT_apply, if_pos rfl, if_pos rfl] at h0

/-- **The distinct-position residual-sum machine**: nonzero terms of one common weight `m`
whose residuals are monomials at pairwise-distinct positions sum without cancellation —
every nonempty sub-sum is nonzero of weight `m` with residual the `single`-sum.
Cancellation is excluded through the CONSTANT `R(-1) = C d` (position-preserving), so the
flipped residual can never match a monomial at a fresh position. -/
private lemma decomp_machine (σ : Stage p F) (d : ↥σ.K)
    (hd : σ.R (-1) = LaurentPolynomial.C d)
    (m : ℤ) (a : ℕ → Polynomial ℤ_[p]) (pos : ℕ → ℤ) (c : ℕ → ↥σ.K) (S : Finset ℕ)
    (h0 : ∀ j ∈ S, a j ≠ 0) (hw : ∀ j ∈ S, σ.w (a j) = m)
    (hR : ∀ j ∈ S, σ.R (a j) = LaurentPolynomial.C (c j) * LaurentPolynomial.T (pos j))
    (hc : ∀ j ∈ S, c j ≠ 0)
    (hinj : ∀ j ∈ S, ∀ k ∈ S, pos j = pos k → j = k) :
    ∀ T ⊆ S, T.Nonempty →
      (∑ j ∈ T, a j) ≠ 0 ∧ σ.w (∑ j ∈ T, a j) = m ∧
        σ.R (∑ j ∈ T, a j)
          = ∑ j ∈ T, LaurentPolynomial.C (c j) * LaurentPolynomial.T (pos j) := by
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
    have haj : a j ≠ 0 := h0 j hjS
    have hwj : σ.w (a j) = m := hw j hjS
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · refine ⟨by simpa using haj, by simpa using hwj, by simp [hR j hjS]⟩
    · obtain ⟨hT0, hTw, hTR⟩ := ih hTsub hTne
      -- the flip exclusion: `R(a j) = R(-1)·R(Σ_T)` is impossible at distinct positions
      have hkey : σ.R (a j) ≠ σ.R (-1) * σ.R (∑ l ∈ T, a l) := by
        intro hflip
        have h2 : (σ.R (a j)) (pos j) = c j := by
          rw [hR j hjS, CT_apply, if_pos rfl]
        have hsingles : σ.R (-1) * σ.R (∑ l ∈ T, a l)
            = ∑ l ∈ T, LaurentPolynomial.C (d * c l) * LaurentPolynomial.T (pos l) := by
          rw [hd, hTR, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun l hl => ?_)
          rw [← mul_assoc, ← map_mul]
        have h3 : (σ.R (a j)) (pos j) = 0 := by
          rw [hflip, hsingles, sum_apply']
          refine Finset.sum_eq_zero (fun l hl => ?_)
          rw [CT_apply, if_neg (fun hpe => hjT ((hinj l (hTsub hl) j hjS hpe) ▸ hl))]
        exact hc j hjS (h2.symm.trans h3)
      have hsum_ne : a j + ∑ l ∈ T, a l ≠ 0 := by
        intro h0'
        have hxe : a j = -(∑ l ∈ T, a l) := eq_neg_of_add_eq_zero_left h0'
        exact hkey (by rw [hxe, R_neg σ _ hT0])
      have hwge : m ≤ σ.w (a j + ∑ l ∈ T, a l) := by
        have h := σ.hwult (a j) _ haj hT0 hsum_ne
        rwa [hwj, hTw, min_self] at h
      have hwsum : σ.w (a j + ∑ l ∈ T, a l) = m := by
        by_contra hne'
        have hlt : m < σ.w (a j + ∑ l ∈ T, a l) := lt_of_le_of_ne hwge (Ne.symm hne')
        have hnT : -(∑ l ∈ T, a l) ≠ 0 := neg_ne_zero.mpr hT0
        have heq : -(∑ l ∈ T, a l) + (a j + ∑ l ∈ T, a l) = a j := by ring
        have hR' := σ.hRlt (-(∑ l ∈ T, a l)) (a j + ∑ l ∈ T, a l) hnT hsum_ne
          (by rw [heq]; exact haj) (by rw [w_neg σ _ hT0, hTw]; exact hlt)
        rw [heq] at hR'
        exact hkey (by rw [hR', R_neg σ _ hT0])
      have hRadd := σ.hRadd (a j) _ haj hT0 hsum_ne (by rw [hwj, hTw]) (by rw [hwsum, hwj])
      refine ⟨by rwa [Finset.sum_insert hjT], by rwa [Finset.sum_insert hjT], ?_⟩
      rw [Finset.sum_insert hjT, Finset.sum_insert hjT, hRadd, hR j hjS, hTR]

/-- `R(-1)` is a CONSTANT `C d` with `d² = 1`, read off the S5 digit of the negated
recentering lift (bare `Stage`, no `StageCore.R_neg`). -/
private lemma eps_const (σ : Stage p F) (ht0 : σ.t = 0) (cc : ↥σ.K) (hcc : cc ≠ 0)
    (tt : Polynomial ℤ_[p]) (htc : inC σ.Φ tt) (htne : tt ≠ 0)
    (htdig : σ.R tt = LaurentPolynomial.C cc * LaurentPolynomial.T (0 : ℤ)) :
    ∃ d : ↥σ.K, σ.R (-1) = LaurentPolynomial.C d ∧ d * d = 1 := by
  have hmtne : (-tt) ≠ 0 := neg_ne_zero.mpr htne
  have hmtc : inC σ.Φ (-tt) := by
    show (-tt).degree < σ.Φ.degree
    rw [Polynomial.degree_neg]
    exact htc
  obtain ⟨cu, hcu⟩ := σ.hS5 (-tt) hmtne hmtc
  rw [ht0] at hcu
  simp only [neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one] at hcu
  have h1 : σ.R (-tt) = σ.R (-1) * LaurentPolynomial.C cc := by
    rw [R_neg σ tt htne, htdig, LaurentPolynomial.T_zero, mul_one]
  have h2 : σ.R (-1) * LaurentPolynomial.C cc = LaurentPolynomial.C (cu : ↥σ.K) := by
    rw [← h1, hcu]
  have h3 : σ.R (-1) = LaurentPolynomial.C ((cu : ↥σ.K) * cc⁻¹) := by
    have h4 : σ.R (-1) * LaurentPolynomial.C cc * LaurentPolynomial.C cc⁻¹
        = LaurentPolynomial.C (cu : ↥σ.K) * LaurentPolynomial.C cc⁻¹ := by rw [h2]
    rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hcc, map_one, mul_one] at h4
    rw [h4, map_mul]
  refine ⟨(cu : ↥σ.K) * cc⁻¹, h3, ?_⟩
  have hsq : σ.R (-1) * σ.R (-1) = 1 := by
    have h := σ.hRmul (-1) (-1) (by norm_num) (by norm_num)
    rw [neg_mul_neg, one_mul, R_one σ] at h
    exact h.symm
  rw [h3, ← map_mul, ← map_one (LaurentPolynomial.C (R := ↥σ.K))] at hsq
  exact C_inj hsq

/-- The recentering-lift SIGN, from bare `Stage`: `R(-lift) = C(-center)`.  Either
`R(-1) = C(-1)` outright, or `R(-1) = C 1` — and then an (S6b) realizer pair for `±1`
above the key weight forces `(-1 : K) = 1` (char 2) through `hRadd`/`hRlt`, so the two
constants agree anyway. -/
private lemma R_neg_tt (σ : Stage p F) (he1 : σ.e = 1) (cc : ↥σ.K) (hcc : cc ≠ 0)
    (tt : Polynomial ℤ_[p]) (htc : inC σ.Φ tt) (htne : tt ≠ 0)
    (htdig : σ.R tt = LaurentPolynomial.C cc * LaurentPolynomial.T (0 : ℤ)) :
    σ.R (-tt) = LaurentPolynomial.C (-cc) := by
  have ht0 : σ.t = 0 := σ.he1t he1
  obtain ⟨d, hd, hd2⟩ := eps_const σ ht0 cc hcc tt htc htne htdig
  have hRmt : σ.R (-tt) = LaurentPolynomial.C (d * cc) := by
    rw [R_neg σ tt htne, htdig, LaurentPolynomial.T_zero, mul_one, hd, ← map_mul]
  rcases mul_self_eq_one_iff.mp hd2 with h1 | hm1
  · -- `d = 1`: derive `(-1 : K) = 1` (char 2), so `C cc = C (-cc)`
    have hneg1 : (-1 : ↥σ.K) = 1 := by
      obtain ⟨B₁, hB₁ne, hB₁c, hB₁w, hB₁R⟩ := σ.hS6b (σ.wPrev σ.Φ + 1) 1 (lt_add_one _)
      obtain ⟨B₂, hB₂ne, hB₂c, hB₂w, hB₂R⟩ := σ.hS6b (σ.wPrev σ.Φ + 1) (-1) (lt_add_one _)
      rw [ht0] at hB₁R hB₂R
      simp only [neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one, Units.val_one,
        Units.val_neg, map_one, map_neg] at hB₁R hB₂R
      -- hB₁R : σ.R B₁ = 1 ; hB₂R : σ.R B₂ = -1
      have hwB₁ : σ.w B₁ = σ.wPrev σ.Φ + 1 := by
        rw [σ.hStretch B₁ hB₁ne hB₁c, hB₁w, he1]
        push_cast
        ring
      have hwB₂ : σ.w B₂ = σ.wPrev σ.Φ + 1 := by
        rw [σ.hStretch B₂ hB₂ne hB₂c, hB₂w, he1]
        push_cast
        ring
      by_cases hx : B₁ + B₂ = 0
      · -- B₂ = -B₁, so C(-1) = R(-1)·R(B₁) = C d = C 1
        have hB₂eq : B₂ = -B₁ := by
          have h5 := eq_neg_of_add_eq_zero_left hx
          rw [h5, neg_neg]
        have h5 : (-1 : LaurentPolynomial ↥σ.K) = LaurentPolynomial.C d := by
          rw [← hB₂R, hB₂eq, R_neg σ B₁ hB₁ne, hB₁R, mul_one, hd]
        have h6 : LaurentPolynomial.C (-1 : ↥σ.K) = LaurentPolynomial.C d := by
          rw [map_neg, map_one]
          exact h5
        rw [C_inj h6, h1]
      · have hwge : σ.wPrev σ.Φ + 1 ≤ σ.w (B₁ + B₂) := by
          have h := σ.hwult B₁ B₂ hB₁ne hB₂ne hx
          rwa [hwB₁, hwB₂, min_self] at h
        by_cases hwx : σ.w (B₁ + B₂) = σ.wPrev σ.Φ + 1
        · -- equal-weight sum: residuals add to 0, contradicting `hRne`
          have hR' := σ.hRadd B₁ B₂ hB₁ne hB₂ne hx (hwB₁.trans hwB₂.symm)
            (by rw [hwx, hwB₁])
          rw [hB₁R, hB₂R, add_neg_cancel] at hR'
          exact absurd hR' (σ.hRne _ hx)
        · -- weight jump: `hRlt` transports the flipped digit onto `B₁`
          have hlt : σ.wPrev σ.Φ + 1 < σ.w (B₁ + B₂) := lt_of_le_of_ne hwge (Ne.symm hwx)
          have hnB₂ : -B₂ ≠ 0 := neg_ne_zero.mpr hB₂ne
          have heq : -B₂ + (B₁ + B₂) = B₁ := by ring
          have hR' := σ.hRlt (-B₂) (B₁ + B₂) hnB₂ hx (by rw [heq]; exact hB₁ne)
            (by rw [w_neg σ B₂ hB₂ne, hwB₂]; exact hlt)
          rw [heq, hB₁R, R_neg σ B₂ hB₂ne, hB₂R, hd, h1, map_one, one_mul] at hR'
          -- hR' : 1 = -1 in the Laurent ring
          have h6 : LaurentPolynomial.C (1 : ↥σ.K) = LaurentPolynomial.C (-1 : ↥σ.K) := by
            rw [map_one, map_neg, map_one]
            exact hR'
          exact (C_inj h6).symm
    have h7 : -cc = d * cc := by
      rw [h1, one_mul, ← neg_one_mul, hneg1, one_mul]
    rw [hRmt, ← h7]
  · rw [hRmt, hm1, neg_one_mul]

/-- `Φ − lift` is the `g = 1` standard lift of `ψ = X − C center` at the parent stage
(the `L5_recVV` construction, with the digit sign supplied by `R_neg_tt`). -/
private lemma recenter_lift_standard (σ : Stage p F) (he1 : σ.e = 1) (cc : ↥σ.K)
    (hcc : cc ≠ 0) (tt : Polynomial ℤ_[p]) (htc : inC σ.Φ tt) (htne : tt ≠ 0)
    (htw : σ.w tt = σ.w σ.Φ)
    (htdig : σ.R tt = LaurentPolynomial.C cc * LaurentPolynomial.T (0 : ℤ)) :
    IsStandardLift σ (Polynomial.X - Polynomial.C cc) 1 (σ.Φ - tt) := by
  have ht0 : σ.t = 0 := σ.he1t he1
  have hmtne : (-tt) ≠ 0 := neg_ne_zero.mpr htne
  have hmtc : inC σ.Φ (-tt) := by
    show (-tt).degree < σ.Φ.degree
    rw [Polynomial.degree_neg]
    exact htc
  have wnegtt : σ.w (-tt) = σ.w tt := w_neg σ tt htne
  have hcoeff0 : (Polynomial.X - Polynomial.C cc).coeff 0 = -cc := by simp
  refine ⟨Polynomial.monic_X_sub_C cc, Polynomial.natDegree_X_sub_C cc,
    fun k => if k = 0 then -tt else 0, ?_, ?_, ?_⟩
  · intro k hk
    dsimp only
    split_ifs with hk0
    · subst hk0
      rw [hcoeff0] at hk
      exact absurd (neg_eq_zero.mp hk) hcc
    · rfl
  · intro k hk1 _
    have hk0 : k = 0 := Nat.lt_one_iff.mp hk1
    subst hk0
    refine ⟨?_, ?_, ?_, ?_⟩
    · show -tt ≠ 0
      exact hmtne
    · show inC σ.Φ (-tt)
      exact hmtc
    · show σ.wPrev (-tt) = _
      have hs := σ.hStretch (-tt) hmtne hmtc
      rw [he1] at hs
      push_cast at hs ⊢
      rw [one_mul, wnegtt, htw, σ.hwΦ] at hs
      simp only [mul_one]
      omega
    · show σ.R (-tt) = _
      rw [R_neg_tt σ he1 cc hcc tt htc htne htdig, hcoeff0, ht0]
      simp only [neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one]
  · rw [he1]
    simp [sub_eq_add_neg]

end U22E1Helpers

/-- (SAE) strict span-entry endpoint (F-4/U22-E1): at consecutive reads of a run, at every
recorded span slot `j` of the child read strictly below the parent vertex (`j < μ`), f's
actual frame-(i+1) weight at slot `j` strictly exceeds the parent line's value at `j`'s
base index (stage scale: `σ.w = STR ×` absolute). -/
theorem SAE_spanStrict_endpoint {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd) :
    ∀ j : ℕ, (H.nodes[i+1]'hi1).s0 ≤ j →
      j ≤ (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide →
      j < (H.nodes[i]'(by omega)).μ → B j ≠ 0 →
      (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at (j * (H.nodes[i]'(by omega)).childWidth)
        < (((H.nodes[i+1]'hi1).σ.w (B j) : ℚ)) := by
  classical
  have hi : i < H.nodes.length := by omega
  intro j hj1 hj2 hjμ hBj
  by_cases hsp : (H.nodes[i]'hi).species = ReadSpecies.recentering
  · -- RECENTERING parent — U20c's landed machine with `L5_landBox` at the strict slot
    obtain ⟨hfmon, hfdeg, hcoh, hruns⟩ := h
    have hf : f ≠ 0 := hfmon.ne_zero
    obtain ⟨-, hslope, hgamtie, htrans⟩ := hcoh
    obtain ⟨hrec, -, -, -, -, -, -⟩ := htrans i hi1
    have hcore := hrec hsp
    obtain ⟨he1σ, he1σ', hccne, htc, htne, htw, htdig, hΦ', hw', -, -, -, -, -⟩ := hcore.base
    obtain ⟨B', Nd', Φnext, hdev', -, hside⟩ := hruns i hi
    obtain ⟨-, hdig, ⟨hanch, hord⟩, -, -, -⟩ := hside
    set ν : Node p F := H.nodes[i]'hi with hν
    set ν' : Node p F := H.nodes[i+1]'hi1 with hν'
    -- node-level recentering data
    obtain ⟨hre, hrg⟩ := ν.hspecRec hsp
    obtain ⟨hψeq, -⟩ := ν.hspecRecCenter hsp
    have hνt : ν.t = 0 := by
      have h1 := ν.hbezCanon
      rw [hre] at h1
      push_cast at h1
      omega
    have hνa : ν.a = (ν.s0 : ℤ) := by
      have h1 := ν.hAnchor
      rw [hre, hνt] at h1
      push_cast at h1
      linarith
    have hσt : ν.σ.t = 0 := ν.σ.he1t he1σ
    have hσs : ν.σ.s = 1 := by
      have h1 := ν.σ.hbez
      rw [he1σ, hσt] at h1
      push_cast at h1
      linarith
    -- the recorded anchor of `R f` at read i
    have hfdev : f = ∑ j ∈ Finset.range Nd', B' j * ν.σ.Φ ^ j := hdev'.2.2
    have hanchf : HasAnchorK (ν.σ.R f) ν.a ν.Ranch := by
      rw [hfdev]
      exact hanch
    -- `R(-1)` is constant
    obtain ⟨d, hd, -⟩ := eps_const ν.σ hσt ν.center hccne ν.lift htc htne htdig
    -- K1 at the parent key
    obtain ⟨hK1low, j₀, hj₀N, hj₀ne, hj₀eq⟩ := ν.σ.hK1 f B' Nd' hf hdev'
    have hΦne : ν.σ.Φ ≠ 0 := ν.σ.hmonic.ne_zero
    -- the minimizing slot set M
    set S0 : Finset ℕ := (Finset.range Nd').filter (fun j => B' j ≠ 0) with hS0
    set M : Finset ℕ :=
      S0.filter (fun j => ν.σ.w (B' j) + (j : ℤ) * ν.σ.w ν.σ.Φ = ν.σ.w f) with hM
    set Mc : Finset ℕ :=
      S0.filter (fun j => ¬(ν.σ.w (B' j) + (j : ℤ) * ν.σ.w ν.σ.Φ = ν.σ.w f)) with hMc
    have hS0mem : ∀ j ∈ S0, j < Nd' ∧ B' j ≠ 0 := by
      intro j hj
      have h1 := Finset.mem_filter.mp hj
      exact ⟨Finset.mem_range.mp h1.1, h1.2⟩
    have hfS0 : f = ∑ j ∈ S0, B' j * ν.σ.Φ ^ j := by
      rw [hfdev, hS0]
      refine (Finset.sum_filter_of_ne ?_).symm
      intro j hj hne hBj0
      exact hne (by rw [hBj0, zero_mul])
    -- the S5 digit at each nonzero slot, as a global function
    have hS5j : ∀ j : ℕ, ∃ c : ↥ν.σ.K, B' j ≠ 0 →
        (c ≠ 0 ∧ ν.σ.R (B' j * ν.σ.Φ ^ j)
          = LaurentPolynomial.C c * LaurentPolynomial.T ((j : ℕ) : ℤ)) := by
      intro j
      by_cases hBj0 : B' j = 0
      · exact ⟨1, fun hne => absurd hBj0 hne⟩
      · obtain ⟨cu, hcu⟩ := ν.σ.hS5 (B' j) hBj0 (hdev'.1 j)
        refine ⟨(cu : ↥ν.σ.K), fun _ => ⟨Units.ne_zero cu, ?_⟩⟩
        rw [L2_strideRule ν.σ (B' j) hBj0 (hdev'.1 j) j, hcu, hσt, hσs]
        simp only [neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one, one_mul]
    choose cdig hcdig using hS5j
    have hterm_ne : ∀ j ∈ M, B' j * ν.σ.Φ ^ j ≠ 0 := by
      intro j hj
      exact mul_ne_zero (hS0mem j (Finset.mem_filter.mp hj).1).2 (pow_ne_zero _ hΦne)
    have hterm_wt : ∀ j, B' j ≠ 0 →
        ν.σ.w (B' j * ν.σ.Φ ^ j) = ν.σ.w (B' j) + (j : ℤ) * ν.σ.w ν.σ.Φ := by
      intro j hBj0
      rw [ν.σ.hwmul _ _ hBj0 (pow_ne_zero _ hΦne), w_pow ν.σ _ hΦne]
    have hterm_w : ∀ j ∈ M, ν.σ.w (B' j * ν.σ.Φ ^ j) = ν.σ.w f := by
      intro j hj
      have hBj0 : B' j ≠ 0 := (hS0mem j (Finset.mem_filter.mp hj).1).2
      rw [hterm_wt j hBj0]
      exact (Finset.mem_filter.mp hj).2
    have hterm_R : ∀ j ∈ M, ν.σ.R (B' j * ν.σ.Φ ^ j)
        = LaurentPolynomial.C (cdig j) * LaurentPolynomial.T ((j : ℕ) : ℤ) := by
      intro j hj
      exact (hcdig j (hS0mem j (Finset.mem_filter.mp hj).1).2).2
    have hterm_c : ∀ j ∈ M, cdig j ≠ 0 := by
      intro j hj
      exact (hcdig j (hS0mem j (Finset.mem_filter.mp hj).1).2).1
    have hMinj : ∀ j ∈ M, ∀ k ∈ M, ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) → j = k :=
      fun j _ k _ hjk => by exact_mod_cast hjk
    have hMne : M.Nonempty :=
      ⟨j₀, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj₀N, hj₀ne⟩, hj₀eq.symm⟩⟩
    obtain ⟨hMsum_ne, hMsum_w, hMsum_R⟩ :=
      decomp_machine ν.σ d hd (ν.σ.w f) (fun j => B' j * ν.σ.Φ ^ j) (fun j => (j : ℤ)) cdig M
        hterm_ne hterm_w hterm_R hterm_c hMinj M Finset.Subset.rfl hMne
    -- `R f` is the M-supported monomial sum (heavier slots drop through `hRlt`)
    have hRf : ν.σ.R f
        = ∑ j ∈ M, LaurentPolynomial.C (cdig j) * LaurentPolynomial.T ((j : ℕ) : ℤ) := by
      have hsplit :
          (∑ j ∈ M, B' j * ν.σ.Φ ^ j) + (∑ j ∈ Mc, B' j * ν.σ.Φ ^ j)
            = ∑ j ∈ S0, B' j * ν.σ.Φ ^ j := by
        rw [hM, hMc]
        exact Finset.sum_filter_add_sum_filter_not _ _ _
      by_cases hr0 : (∑ j ∈ Mc, B' j * ν.σ.Φ ^ j) = 0
      · rw [hfS0, ← hsplit, hr0, add_zero, hMsum_R]
      · have hwrest : ν.σ.w f + 1 ≤ ν.σ.w (∑ j ∈ Mc, B' j * ν.σ.Φ ^ j) := by
          refine w_sum_ge ν.σ _ _ _ (fun j hj _ => ?_) hr0
          obtain ⟨hjS0, hjneq⟩ := Finset.mem_filter.mp hj
          obtain ⟨hjN, hBj0⟩ := hS0mem j hjS0
          have hlow := hK1low j hjN hBj0
          have hwt := hterm_wt j hBj0
          have hne2 : ν.σ.w (B' j) + (j : ℤ) * ν.σ.w ν.σ.Φ ≠ ν.σ.w f := hjneq
          have hlt2 : ν.σ.w f < ν.σ.w (B' j) + (j : ℤ) * ν.σ.w ν.σ.Φ :=
            lt_of_le_of_ne hlow (Ne.symm hne2)
          rw [hwt]
          linarith [hlt2]
        have hfsum : f = (∑ j ∈ M, B' j * ν.σ.Φ ^ j) + (∑ j ∈ Mc, B' j * ν.σ.Φ ^ j) := by
          rw [hfS0, hsplit]
        have hR' := ν.σ.hRlt _ _ hMsum_ne hr0 (by rw [← hfsum]; exact hf)
          (by rw [hMsum_w]; linarith [hwrest])
        rw [hfsum, hR', hMsum_R]
    -- anchored coefficients of `R f`
    have hanchcoeff : ∀ k : ℕ, (ν.σ.R f) (ν.a + (k : ℤ)) = ν.Ranch.coeff k := by
      intro k
      have h1 : (Polynomial.toLaurent ν.Ranch) ((k : ℕ) : ℤ) = ν.Ranch.coeff k := by
        rw [Polynomial.toLaurent_apply]
        exact Finsupp.mapDomain_apply Nat.cast_injective ν.Ranch.toFinsupp k
      rw [hanchf.2, mul_comm,
        show (LaurentPolynomial.T ν.a : LaurentPolynomial ↥ν.σ.K)
          = AddMonoidAlgebra.single ν.a 1 from rfl,
        AddMonoidAlgebra.mul_single_apply, mul_one, ← sub_eq_add_neg,
        show ν.a + (k : ℤ) - ν.a = ((k : ℕ) : ℤ) by ring, h1]
    -- anchored support pins minimizing slots
    have hMmem : ∀ k : ℕ, ν.Ranch.coeff k ≠ 0 → (ν.s0 + k) ∈ M := by
      intro k hk
      by_contra hnot
      have h0' : (ν.σ.R f) (ν.a + (k : ℤ)) = 0 := by
        rw [hRf, sum_apply']
        refine Finset.sum_eq_zero (fun l hl => ?_)
        rw [CT_apply, if_neg (fun hpe => hnot ?_)]
        have hleq : l = ν.s0 + k := by
          rw [hνa] at hpe
          exact_mod_cast hpe
        rwa [← hleq]
      rw [hanchcoeff k] at h0'
      exact hk h0'
    have hRanch0 : ν.Ranch.coeff 0 ≠ 0 := hanchf.1
    have hs0M : ν.s0 ∈ M := by simpa using hMmem 0 hRanch0
    have hwdiv : ν.wSide / ν.e = ν.wSide := by rw [hre, Nat.div_one]
    have hRanchTop : ν.Ranch.coeff ν.wSide = ν.pat ν.wSide := by
      rw [ν.hRanch, hwdiv, Polynomial.finset_sum_coeff]
      rw [Finset.sum_eq_single ν.wSide
        (fun b _ hbne => by
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun hh => hbne hh.symm),
            mul_zero])
        (fun hns => absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) hns)]
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    have hRanchTopNe : ν.Ranch.coeff ν.wSide ≠ 0 := by
      rw [hRanchTop]
      have h1 := ν.hpatTop
      rwa [hwdiv] at h1
    have hswM : (ν.s0 + ν.wSide) ∈ M := hMmem ν.wSide hRanchTopNe
    -- the two SideReads(ii) endpoint weights
    obtain ⟨-, hg0, -⟩ := hdig 0 (Nat.zero_le _) ν.hpat0
    obtain ⟨-, hgw, -⟩ := hdig (ν.wSide / ν.e) le_rfl ν.hpatTop
    rw [hre] at hg0 hgw
    simp only [Nat.div_one, Nat.cast_one, one_mul, mul_zero, add_zero] at hg0 hgw
    -- `1 ≤ wSide` (from `1 ≤ μ ≤ wSide`)
    have hRanchne : ν.Ranch ≠ 0 := fun hz => hRanch0 (by rw [hz, Polynomial.coeff_zero])
    have hup : ν.Ranch.natDegree ≤ ν.wSide := by
      refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => ?_)
      rw [ν.hRanch, hwdiv, Polynomial.finset_sum_coeff]
      refine Finset.sum_eq_zero (fun k hk => ?_)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by have := Finset.mem_range.mp hk; omega), mul_zero]
    have hμw : ν.μ ≤ ν.wSide := by
      have hdeg := Polynomial.natDegree_le_of_dvd hord.1 hRanchne
      rw [hψeq, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hdeg
      omega
    have hw1 : 1 ≤ ν.wSide := le_trans ν.hμ hμw
    -- the two minimizing-slot weights
    have hMs0 : ν.σ.w (B' ν.s0) + (ν.s0 : ℤ) * ν.σ.w ν.σ.Φ = ν.σ.w f :=
      (Finset.mem_filter.mp hs0M).2
    have hMsw : ν.σ.w (B' (ν.s0 + ν.wSide)) + ((ν.s0 + ν.wSide : ℕ) : ℤ) * ν.σ.w ν.σ.Φ
        = ν.σ.w f := (Finset.mem_filter.mp hswM).2
    rw [ν.σ.hwΦ] at hMs0 hMsw
    -- h-tie and `w f = γ`
    have hheq : (ν.σ.h : ℤ) = (ν.h : ℤ) := by
      have hcancel : (ν.wSide : ℤ) * (ν.σ.h : ℤ) = (ν.wSide : ℤ) * (ν.h : ℤ) := by
        push_cast at hMs0 hMsw hg0 hgw ⊢
        linarith
      have hwne : (ν.wSide : ℤ) ≠ 0 := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mp hw1
      exact mul_left_cancel₀ hwne hcancel
    have hwf : ν.σ.w f = ν.gam := by
      rw [hheq] at hMs0
      linarith
    -- the STRICT (BOX) transport at the child key (`L5_landBox` through the
    -- standard-lift view)
    have hψmon : (Polynomial.X - Polynomial.C ν.center).Monic := Polynomial.monic_X_sub_C _
    have hψdeg : (Polynomial.X - Polynomial.C ν.center).natDegree = 1 :=
      Polynomial.natDegree_X_sub_C _
    have hψirr : Irreducible (Polynomial.X - Polynomial.C ν.center) :=
      Polynomial.irreducible_X_sub_C ν.center
    have hψz : (Polynomial.X - Polynomial.C ν.center) ≠ Polynomial.X := by
      intro hX
      exact hccne (Polynomial.C_eq_zero.mp (sub_eq_self.mp hX))
    have hlift := recenter_lift_standard ν.σ he1σ ν.center hccne ν.lift htc htne htw htdig
    have hordψ : OrdPsiPoly (Polynomial.X - Polynomial.C ν.center) ν.Ranch ν.μ := by
      rw [← hψeq]
      exact hord
    rw [hΦ'] at hdev
    have hbox := L5_landBox ν.σ (Polynomial.X - Polynomial.C ν.center) 1 hψdeg
      hψmon hψirr hψz (ν.σ.Φ - ν.lift) hlift f hf ν.μ ν.a ν.Ranch hanchf hordψ B Nd hdev
      j hjμ hBj
    -- the recentered valuation is the parent valuation
    rw [hw' (B j)]
    -- integer content: γ − j·h < σ.w (B j)
    rw [he1σ, hwf, hheq] at hbox
    push_cast at hbox
    have hZ : ν.gam - (j : ℤ) * (ν.h : ℤ) < ν.σ.w (B j) := by linarith [hbox]
    -- scale arithmetic: STR_{i+1} = STR_i, childWidth = Dwidth
    have hSTR : H.strFrame (i + 1) = H.strFrame i := by
      unfold History.strFrame
      rw [List.take_succ, List.getElem?_eq_getElem hi]
      simp only [List.map_append, List.prod_append, Option.toList_some, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← hν, hre, mul_one]
    have hCW : ν.childWidth = ν.Dwidth := by
      show ν.e * ν.g * ν.Dwidth = ν.Dwidth
      rw [hre, hrg, one_mul, one_mul]
    have hsl := hslope i hi
    rw [← hν] at hsl
    have hgt := hgamtie i hi
    rw [← hν] at hgt
    have hLU := ν.hLineU
    have hlineJ : (H.strFrame (i + 1) : ℚ) * ν.line.at (j * ν.childWidth)
        = (ν.gam : ℚ) - (j : ℚ) * (ν.h : ℚ) := by
      rw [hSTR, hCW]
      simp only [LeanUrat.MovesC.Line.at] at hLU ⊢
      rw [hre] at hsl hgt
      push_cast at hsl hgt hLU ⊢
      linear_combination (H.strFrame i : ℚ) * hLU - hgt
        + (((ν.s0 : ℚ) + (ν.wSide : ℚ)) - (j : ℚ)) * hsl
    rw [hlineJ]
    exact_mod_cast hZ
  · -- NON-RECENTERING parent — the V9 REV-6 Box law (V10-vacuous legs + species
    -- inventory + the strict Taylor corner)
    exact LeanUrat.HC1.V9_E1box_nonrec h i hi1 hsp B Nd hdev j hjμ hBj

end LeanUrat.MovesJ
