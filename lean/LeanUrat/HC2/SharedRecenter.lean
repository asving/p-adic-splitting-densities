/-
LeanUrat.HC2.SharedRecenter  (HC-2 campaign — shared recentering-parent machine)

The RECENTERING-parent helper block consumed by BOTH U20c
(`NA_transport_recentering`, U20c_NAtransportRecentering.lean) and U22-E1
(`SAE_spanStrict_endpoint`, U22E1_spanStrict.lean): hoisted from the two
byte-identical file-private copies (dedup pass, 2026-07-30).  SYN-M9 (C1 cluster, same
day): the engine lemmas below are now RE-EXPORTS of `Moves/ResVal.lean` (statements
byte-identical; single proof source; concordance
`lean/notes/SYN_E0_CONCORDANCE_2026-07-30.md`); `decomp_machine` is derived from the
pack machine `ResValPack.residual_sum_machine` at `Stage.pack`.  `eps_const`/`R_neg_tt`/
`recenter_lift_standard`/`recentering_scaffold` are SharedRecenter-specific and keep
their proofs.  `recentering_scaffold` is a NEW bundling lemma — see its docstring for
the ratification record.  Contents:
* `Stage` weight/residual arithmetic from the bare axioms (`w_one` … `R_neg`,
  `w_sum_ge`), Laurent coefficient-extraction seams (`CT_apply`/`sum_apply'`/`C_inj`);
* `decomp_machine` — the distinct-position residual-sum machine (nonzero terms of one
  common weight with monomial residuals at pairwise-distinct positions sum without
  cancellation; the flip exclusion runs through the CONSTANT `R(-1) = C d`);
* `eps_const`/`R_neg_tt` — the recentering-lift SIGN from bare `Stage` (no
  `StageCore.R_neg`): `R(-1)` is a constant `C d`, `d² = 1`, and the `d = 1` branch
  forces `char K = 2` via an (S6b) realizer pair through `hRadd`/`hRlt`;
* `recenter_lift_standard` — `Φ − lift` is the `g = 1` STANDARD LIFT of
  `ψ = X − C center` at the parent stage (the `L5_recVV` construction), feeding
  `L5_landVertex` (U20c) and `L5_landBox` (U22-E1).
Exposure is namespace-fenced: everything lives under
`LeanUrat.MovesJ.SharedRecenter`; the two consuming units `open SharedRecenter`.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.Moves.L2_strideRule
import LeanUrat.Moves.ResVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ.SharedRecenter
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `w 1 = 0`. -/
lemma w_one (σ : Stage p F) : σ.w 1 = 0 := ResVal.w_one σ

/-- `w (-1) = 0`. -/
lemma w_neg_one (σ : Stage p F) : σ.w (-1) = 0 := ResVal.w_neg_one σ

/-- `w (-x) = w x`. -/
lemma w_neg (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    σ.w (-x) = σ.w x := ResVal.w_neg σ x hx

/-- `w (x^n) = n·w x`. -/
lemma w_pow (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    σ.w (x ^ n) = (n : ℤ) * σ.w x := ResVal.w_pow σ x hx n

/-- `R 1 = 1`. -/
lemma R_one (σ : Stage p F) : σ.R 1 = 1 := ResVal.R_one σ

/-- `R (-x) = R (-1) · R x`. -/
lemma R_neg (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    σ.R (-x) = σ.R (-1) * σ.R x := ResVal.R_neg σ x hx

/-- Ultrametric finite-sum lower bound (mirror of the `L5_landVertex` private lemma). -/
lemma w_sum_ge (σ : Stage p F) (S : Finset ℕ) (a : ℕ → Polynomial ℤ_[p]) (m : ℤ)
    (hm : ∀ j ∈ S, a j ≠ 0 → m ≤ σ.w (a j)) (hsum : (∑ j ∈ S, a j) ≠ 0) :
    m ≤ σ.w (∑ j ∈ S, a j) := ResVal.w_sum_ge σ S a m hm hsum

/-- Coefficient extraction on a monomial `C c · T n` (the Finsupp seam, crossed by
`exact`-defeq only). -/
lemma CT_apply {K : Type*} [Field K] (c : K) (n q : ℤ) :
    (LaurentPolynomial.C c * LaurentPolynomial.T n : LaurentPolynomial K) q
      = if n = q then c else 0 := ResVal.CT_apply c n q

/-- Coefficient extraction commutes with finite sums (Finsupp seam). -/
lemma sum_apply' {K : Type*} [Field K] (T : Finset ℕ) (g : ℕ → LaurentPolynomial K)
    (q : ℤ) : (∑ l ∈ T, g l) q = ∑ l ∈ T, (g l) q := ResVal.sum_apply' T g q

/-- `C` is injective (coefficient at 0). -/
lemma C_inj {K : Type*} [Field K] {x y : K}
    (h : (LaurentPolynomial.C x : LaurentPolynomial K) = LaurentPolynomial.C y) : x = y :=
  ResVal.C_inj h

/-- **The distinct-position residual-sum machine**: nonzero terms of one common weight `m`
whose residuals are monomials at pairwise-distinct positions sum without cancellation —
every nonempty sub-sum is nonzero of weight `m` with residual the `single`-sum.
Cancellation is excluded through the CONSTANT `R(-1) = C d` (position-preserving), so the
flipped residual can never match a monomial at a fresh position. -/
lemma decomp_machine (σ : Stage p F) (d : ↥σ.K)
    (hd : σ.R (-1) = LaurentPolynomial.C d)
    (m : ℤ) (a : ℕ → Polynomial ℤ_[p]) (pos : ℕ → ℤ) (c : ℕ → ↥σ.K) (S : Finset ℕ)
    (h0 : ∀ j ∈ S, a j ≠ 0) (hw : ∀ j ∈ S, σ.w (a j) = m)
    (hR : ∀ j ∈ S, σ.R (a j) = LaurentPolynomial.C (c j) * LaurentPolynomial.T (pos j))
    (hc : ∀ j ∈ S, c j ≠ 0)
    (hinj : ∀ j ∈ S, ∀ k ∈ S, pos j = pos k → j = k) :
    ∀ T ⊆ S, T.Nonempty →
      (∑ j ∈ T, a j) ≠ 0 ∧ σ.w (∑ j ∈ T, a j) = m ∧
        σ.R (∑ j ∈ T, a j)
          = ∑ j ∈ T, LaurentPolynomial.C (c j) * LaurentPolynomial.T (pos j) :=
  σ.pack.decomp_machine d hd m a pos c S h0 hw hR hc hinj

/-- `R(-1)` is a CONSTANT `C d` with `d² = 1`, read off the S5 digit of the negated
recentering lift (bare `Stage`, no `StageCore.R_neg`). -/
lemma eps_const (σ : Stage p F) (ht0 : σ.t = 0) (cc : ↥σ.K) (hcc : cc ≠ 0)
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
lemma R_neg_tt (σ : Stage p F) (he1 : σ.e = 1) (cc : ↥σ.K) (hcc : cc ≠ 0)
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
lemma recenter_lift_standard (σ : Stage p F) (he1 : σ.e = 1) (cc : ↥σ.K)
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

/-- **The recentering-parent scaffold** shared by U20c (`NA_transport_recentering`) and the
recentering leg of U22-E1 (`SAE_spanStrict_endpoint`): from the recorded RECENTERING at
read `i` of a `ReadsOf` run, the full package feeding `L5_landVertex`/`L5_landBox` —
`f ≠ 0`; the parent-stage data `σ.e = 1`, `center ≠ 0`; the recentered-stage transport
records `Φ' = Φ − lift` and `σ'.w = σ.w`; the recorded anchor `HasAnchorK (σ.R f) a Ranch`
(read off the recorded development); the ψ-order `ord_ψ Ranch = μ` at `ψ = X − C center`;
the `g = 1` standard-lift view of `ψ` (`recenter_lift_standard`); the h-tie `σ.h = ν.h`
and `σ.w f = γ` (the distinct-position residual-sum machine pins `s0` and `s0 + wSide` as
`w`-minimizing slots of the recorded development, then SideReads(ii) at both pattern
endpoints closes the two linear equations); and the ℚ-scale LINE LAW at every base slot
`k`: `STR_{i+1} · line.at(k·childWidth) = γ − k·h` (slope law + γ-tie + `hLineU`, with
`STR_{i+1} = STR_i` and `childWidth = Dwidth` at a recentering).

NEW STATEMENT, RATIFIED (2026-07-30, golf Phase 4): this lemma is NOT a verbatim hoist —
it bundles the shared inline derivations of the two pre-golf consumers (e9d2430) into one
named conclusion.  Codex equivalence pass (per-conjunct table on record, campaign notes
PHASE 4): conjuncts 1-10 are verbatim-equivalent to inline facts derived in BOTH pre-golf
files with matching quantifier scope; conjunct 11 (the `∀ k` line law) is a PROVED
GENERALIZATION — the pre-golf files held only the `k = μ` (U20c) and fixed-`j` (U22-E1)
instances; the general affine form is machine-checked here, Lean-core.  Ratified by the
orchestrator as a sanctioned addition on that record. -/
lemma recentering_scaffold {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hi : i < H.nodes.length)
    (hsp : (H.nodes[i]'hi).species = ReadSpecies.recentering) :
    f ≠ 0 ∧
    (H.nodes[i]'hi).σ.e = 1 ∧
    (H.nodes[i]'hi).center ≠ 0 ∧
    (H.nodes[i+1]'hi1).σ.Φ = (H.nodes[i]'hi).σ.Φ - (H.nodes[i]'hi).lift ∧
    (∀ g, (H.nodes[i+1]'hi1).σ.w g = (H.nodes[i]'hi).σ.w g) ∧
    HasAnchorK ((H.nodes[i]'hi).σ.R f) (H.nodes[i]'hi).a (H.nodes[i]'hi).Ranch ∧
    OrdPsiPoly (Polynomial.X - Polynomial.C (H.nodes[i]'hi).center)
      (H.nodes[i]'hi).Ranch (H.nodes[i]'hi).μ ∧
    IsStandardLift (H.nodes[i]'hi).σ (Polynomial.X - Polynomial.C (H.nodes[i]'hi).center)
      1 ((H.nodes[i]'hi).σ.Φ - (H.nodes[i]'hi).lift) ∧
    (H.nodes[i]'hi).σ.w f = (H.nodes[i]'hi).gam ∧
    ((H.nodes[i]'hi).σ.h : ℤ) = ((H.nodes[i]'hi).h : ℤ) ∧
    (∀ k : ℕ, (H.strFrame (i+1) : ℚ) *
        (H.nodes[i]'hi).line.at (k * (H.nodes[i]'hi).childWidth)
      = ((H.nodes[i]'hi).gam : ℚ) - (k : ℚ) * ((H.nodes[i]'hi).h : ℚ)) := by
  classical
  obtain ⟨hfmon, hfdeg, hcoh, hruns⟩ := h
  have hf : f ≠ 0 := hfmon.ne_zero
  obtain ⟨-, hslope, hgamtie, htrans⟩ := hcoh
  obtain ⟨hrec, -, -, -, -, -, -⟩ := htrans i hi1
  have hcore := hrec hsp
  obtain ⟨he1σ, he1σ', hccne, htc, htne, htw, htdig, hΦ', hw', -, -, -, -, -⟩ := hcore.base
  obtain ⟨B', Nd', Φnext, hdev', -, hside⟩ := hruns i hi
  obtain ⟨-, hdig, ⟨hanch, hord⟩, -, -, -⟩ := hside
  set ν : Node p F := H.nodes[i]'hi with hν
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
    intro j hj hne hBj
    exact hne (by rw [hBj, zero_mul])
  -- the S5 digit at each nonzero slot, as a global function
  have hS5j : ∀ j : ℕ, ∃ c : ↥ν.σ.K, B' j ≠ 0 →
      (c ≠ 0 ∧ ν.σ.R (B' j * ν.σ.Φ ^ j)
        = LaurentPolynomial.C c * LaurentPolynomial.T ((j : ℕ) : ℤ)) := by
    intro j
    by_cases hBj : B' j = 0
    · exact ⟨1, fun hne => absurd hBj hne⟩
    · obtain ⟨cu, hcu⟩ := ν.σ.hS5 (B' j) hBj (hdev'.1 j)
      refine ⟨(cu : ↥ν.σ.K), fun _ => ⟨Units.ne_zero cu, ?_⟩⟩
      rw [L2_strideRule ν.σ (B' j) hBj (hdev'.1 j) j, hcu, hσt, hσs]
      simp only [neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one, one_mul]
  choose cdig hcdig using hS5j
  have hterm_ne : ∀ j ∈ M, B' j * ν.σ.Φ ^ j ≠ 0 := by
    intro j hj
    exact mul_ne_zero (hS0mem j (Finset.mem_filter.mp hj).1).2 (pow_ne_zero _ hΦne)
  have hterm_wt : ∀ j, B' j ≠ 0 →
      ν.σ.w (B' j * ν.σ.Φ ^ j) = ν.σ.w (B' j) + (j : ℤ) * ν.σ.w ν.σ.Φ := by
    intro j hBj
    rw [ν.σ.hwmul _ _ hBj (pow_ne_zero _ hΦne), w_pow ν.σ _ hΦne]
  have hterm_w : ∀ j ∈ M, ν.σ.w (B' j * ν.σ.Φ ^ j) = ν.σ.w f := by
    intro j hj
    have hBj : B' j ≠ 0 := (hS0mem j (Finset.mem_filter.mp hj).1).2
    rw [hterm_wt j hBj]
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
        obtain ⟨hjN, hBj⟩ := hS0mem j hjS0
        have hlow := hK1low j hjN hBj
        have hwt := hterm_wt j hBj
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
  -- the standard-lift view of `ψ = X − C center` and the recorded ψ-order
  have hlift := recenter_lift_standard ν.σ he1σ ν.center hccne ν.lift htc htne htw htdig
  have hordψ : OrdPsiPoly (Polynomial.X - Polynomial.C ν.center) ν.Ranch ν.μ := by
    rw [← hψeq]
    exact hord
  -- scale arithmetic: STR_{i+1} = STR_i, childWidth = Dwidth, then the ℚ-line law
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
  have hline : ∀ k : ℕ, (H.strFrame (i+1) : ℚ) * ν.line.at (k * ν.childWidth)
      = (ν.gam : ℚ) - (k : ℚ) * (ν.h : ℚ) := by
    intro k
    rw [hSTR, hCW]
    simp only [LeanUrat.MovesC.Line.at] at hLU ⊢
    rw [hre] at hsl hgt
    push_cast at hsl hgt hLU ⊢
    linear_combination (H.strFrame i : ℚ) * hLU - hgt
      + (((ν.s0 : ℚ) + (ν.wSide : ℚ)) - (k : ℚ)) * hsl
  exact ⟨hf, he1σ, hccne, hΦ', hw', hanchf, hordψ, hlift, hwf, hheq, hline⟩


end LeanUrat.MovesJ.SharedRecenter
