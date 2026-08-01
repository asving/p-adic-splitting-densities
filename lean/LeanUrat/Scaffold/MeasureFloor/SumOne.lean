/-
BP_I §1.6 — SUM-ONE and TRANSFER (`SumOne.lean`).
Unit I-F2: `sum_alpha_eq_one` + `sum_alphaR_eq_one` (Thm SUM-ONE(iii)),
statements verbatim per BP_I §1.6 — **BLOCKED as keyed** (one `sorry`): the
row's "NS-NULL but not LOC" keying makes the equality refutable at a bare
`TypeData` (outer-measure finite additivity fails on non-measurable loci);
Df §5's own proof consumes MEAS-BRIDGE(i) = LOC-derived measurability. The
≥ half (`one_le_sum_alpha`) and the LOC-conditional equality
(`sum_alpha_eq_one_of_locality`, the exact Df §5 argument) are PROVED —
see the I-F2 honesty block below.
Unit I-F3: `ratFunc_eq_zero_of_infinite` (Lemma ID, the interpolation
principle), verbatim per BP_I §1.6 (Df §5 Lemma ID): A(z) = 0 on an
infinite Z ⊆ ℚ-embedded ℕ ⇒ `Polynomial.eq_zero_of_infinite_isRoot`
kills the numerator ⇒ R = 0 via `RatFunc.num_eq_zero_iff`. Stated over
an ARBITRARY infinite Z ⊆ ℕ (deliberately: the D-3 unramified-base
clause wants prime powers q = p^δ, not just primes). Deps: mathlib
RatFunc only.
Unit I-F4: `sum_R_eq_one_of_alpha_eq` — **TRANSFER (D-2 (iii)–(iv))**,
hypothesis-explicit over an abstract per-prime density family `A` with the
NAMED hypothesis rows `hP`/`hsum`/`hdef`/`htie`, verbatim per BP_I §1.6
(incl. the consumption-shape comment). Proof shape (BP row I-F4):
Q := Σ R_τ − 1 vanishes at P (`hsum` + `htie` per prime, transported from
ℝ to ℚ by injectivity of the cast), then Lemma ID (I-F3 above) kills Q.
The (REG-p) instance remark: the hypothesis set P infinite =
`MovesU/RegPFinite.regP_cofinite` + `Nat.infinite_setOf_prime`.
Deps: I-F3; I-F2 supplies `hsum` at consumption. Helper
`denom_sum_eval_ne_zero_and_eval_sum` is I-F4-internal (NOT a blueprint
statement): finset-sum transport for `RatFunc.eval` at a non-vanishing
point, by `Finset.cons_induction` on `RatFunc.denom_add_dvd` +
`RatFunc.eval_add`. (Merge note: two provers landed I-F4 concurrently in
this file; the duplicate copy was removed — one retained below.)
Unit I-F5 (remark unit, BP_I §2 Wave F row I-F5): the TRANSFER instance
rows (Df §5 instances ¶) — n = 1 (Wave G, unconditional; cited in the
section docstring, no re-proof) and n = 2 (corpus `OM.UniformCapstone`
values; the direct table check 1/(q+1) + q/(2(q+1))·2 = 1 as a
`RatFunc ℚ` computation, by `field_simp`). BP_I §3 fence displayed: the
n = 2 values are ANCHORS only — no unconditional α-instance is claimed
until the α-faithfulness tie exists. Deps: I-F4 (above), corpus
OM/UniformCapstone.
-/
import Mathlib
import LeanUrat.Scaffold.MeasureFloor.Semantic
import LeanUrat.OM.UniformCapstone

namespace LeanUrat.Scaffold

/-! ## I-F1: Cor PART (Df §3.2) — the loci partition the separable locus

Verbatim per BP_I §1.6. Route: TYPE-OF is a function (two locus memberships
force τ = τ'), and TYPE-OF-ISTYPE (`TD.typeOf_isType`) + I-D2
(`mem_typesFinset`) put every separable point's type in the Finset. Valid
also at n = 0 (the argument never mentions the degree). Deps: I-D2
(`typesFinset`, Types.lean), I-E2a (`TypeData`, Semantic.lean). -/

section CorPART

variable (p : ℕ) [Fact p.Prime] (n : ℕ) (TD : TypeData p n)

/-- Cor PART: the loci partition the separable locus over Σ_n. -/
theorem locus_pairwise_disjoint :
    Set.PairwiseDisjoint (typesFinset n) (TD.locus p n ·) := by
  intro τ _ τ' _ hne
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  rintro a ⟨_, hτ⟩ ⟨_, hτ'⟩
  exact hne (hτ.symm.trans hτ')

theorem sep_eq_biUnion_locus :
    {a | Sep p n a} = ⋃ τ ∈ typesFinset n, TD.locus p n τ := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hsep
    exact ⟨TD.typeOf a, mem_typesFinset.mpr (TD.typeOf_isType a hsep), hsep, rfl⟩
  · rintro ⟨τ, _, hsep, _⟩
    exact hsep

end CorPART

/-! ## I-F2: Thm SUM-ONE(iii) (Df §5) — Σ_τ α(n,τ;p) = 1, including n = 0

HONESTY BLOCK (why the verbatim unit carries a `sorry`). The BP row keys
I-F2 to "NS-NULL but not LOC", but the Df §5 proof of SUM-ONE(iii) consumes
MEAS-BRIDGE(i) — "each L_σ Borel" — which this scaffold derives ONLY from
the LOC row (I-E5 `measurableSet_locus (LR : LocalityRow ...)`). Over a bare
`TypeData` the loci are ARBITRARY disjoint sets and `TD.alpha` is the outer
measure of an arbitrary set, where finite additivity FAILS: with classical
choice pick a Bernstein set B ⊆ Coeff p 2 (every uncountable closed set
meets B and Bᶜ, so every measurable hull of either has full mass) and set
`typeOf := B.piecewise (const τ₁) (const τ₂)` for two degree-2 types; then
α(τ₁) + α(τ₂) = μ*(B) + μ*(Bᶜ) = 2 ≠ 1, with NS-NULL intact. So the unit
AS KEYED is refutable, not merely unproved. What IS true at the bare
`TypeData` is the subadditivity half `1 ≤ Σ α` (`one_le_sum_alpha` below,
PROVED), and the full equality under the additional LOC row
(`sum_alpha_eq_one_of_locality` below, PROVED — the exact Df §5 argument).
Repair options for the blueprint owner: (a) add `LR : LocalityRow p n TD`
to the unit (matches Df §5's actual consumption; TRANSFER consumers carry
LR anyway at the semantic instance), or (b) add a named measurability row
for the loci. Either is a statement change, hence fenced — reported, not
executed. -/

section SumOne

open MeasureTheory

variable (p : ℕ) [Fact p.Prime] (n : ℕ) (TD : TypeData p n)

/-- The separable locus has full mass from `NR.ns_null` alone — no
measurability of `Sep` consumed (subadditivity over the `em` cover). -/
theorem μHaar_sep_eq_one (NR : NsNullRow p n) :
    μHaar p n {a | Sep p n a} = 1 := by
  refine le_antisymm prob_le_one ?_
  have hcover : (Set.univ : Set (Coeff p n)) ⊆
      {a | Sep p n a} ∪ {a | ¬ Sep p n a} := fun a _ => em (Sep p n a)
  calc (1 : ENNReal) = μHaar p n Set.univ := measure_univ.symm
    _ ≤ μHaar p n ({a | Sep p n a} ∪ {a | ¬ Sep p n a}) := measure_mono hcover
    _ ≤ μHaar p n {a | Sep p n a} + μHaar p n {a | ¬ Sep p n a} :=
        measure_union_le _ _
    _ = μHaar p n {a | Sep p n a} := by rw [NR.ns_null, add_zero]

/-- The half of I-F2 provable at the bare `TypeData`: finite SUBadditivity
needs no measurability, so 1 ≤ Σ_τ α always (NS-NULL only). -/
theorem one_le_sum_alpha (NR : NsNullRow p n) :
    1 ≤ ∑ τ ∈ typesFinset n, TD.alpha p n τ :=
  calc (1 : ENNReal) = μHaar p n {a | Sep p n a} := (μHaar_sep_eq_one p n NR).symm
    _ = μHaar p n (⋃ τ ∈ typesFinset n, TD.locus p n τ) := by
        rw [sep_eq_biUnion_locus p n TD]
    _ ≤ ∑ τ ∈ typesFinset n, μHaar p n (TD.locus p n τ) :=
        measure_biUnion_finset_le _ _
    _ = ∑ τ ∈ typesFinset n, TD.alpha p n τ := rfl

/-- SUM-ONE(iii) PROVED under the additional LOC row (I-E5 measurability of
the loci) — the exact Df §5 finite-additivity argument. NOT the I-F2 unit
statement (which omits LOC; see the honesty block): displayed as the
compiled repair candidate. -/
theorem sum_alpha_eq_one_of_locality (LR : LocalityRow p n TD)
    (NR : NsNullRow p n) :
    ∑ τ ∈ typesFinset n, TD.alpha p n τ = 1 := by
  have hadd : μHaar p n (⋃ τ ∈ typesFinset n, TD.locus p n τ)
      = ∑ τ ∈ typesFinset n, μHaar p n (TD.locus p n τ) :=
    measure_biUnion_finset (locus_pairwise_disjoint p n TD)
      (fun τ _ => measurableSet_locus p n TD LR τ)
  calc ∑ τ ∈ typesFinset n, TD.alpha p n τ
      = μHaar p n (⋃ τ ∈ typesFinset n, TD.locus p n τ) := hadd.symm
    _ = μHaar p n {a | Sep p n a} := by rw [sep_eq_biUnion_locus p n TD]
    _ = 1 := μHaar_sep_eq_one p n NR

/-- ℝ-transport shared by the ℝ versions: probability-finite α's sum passes
through `ENNReal.toReal`. -/
theorem sum_alphaR_of_sum_alpha
    (h : ∑ τ ∈ typesFinset n, TD.alpha p n τ = 1) :
    ∑ τ ∈ typesFinset n, TD.alphaR p n τ = 1 := by
  have hne : ∀ τ ∈ typesFinset n, TD.alpha p n τ ≠ ⊤ :=
    fun τ _ => measure_ne_top _ _
  calc ∑ τ ∈ typesFinset n, TD.alphaR p n τ
      = (∑ τ ∈ typesFinset n, TD.alpha p n τ).toReal :=
        (ENNReal.toReal_sum hne).symm
    _ = 1 := by rw [h]; exact ENNReal.toReal_one

/-- The ℝ version under LOC (see `sum_alpha_eq_one_of_locality`). -/
theorem sum_alphaR_eq_one_of_locality (LR : LocalityRow p n TD)
    (NR : NsNullRow p n) :
    ∑ τ ∈ typesFinset n, TD.alphaR p n τ = 1 :=
  sum_alphaR_of_sum_alpha p n TD (sum_alpha_eq_one_of_locality p n TD LR NR)

/-- **SUM-ONE (Thm SUM-ONE(iii)): Σ_τ α(n,τ;p) = 1 at every p,
including n = 0.** -/
theorem sum_alpha_eq_one (NR : NsNullRow p n) :
    ∑ τ ∈ typesFinset n, TD.alpha p n τ = 1 := by
  -- BLOCKED(I-F2): as keyed (NS-NULL only, no LOC) this is REFUTABLE at a
  -- bare `TypeData`: `alpha` is an outer measure and finite additivity fails
  -- on a Bernstein-set `typeOf` (Σ α = 2 at n = 2) — see the honesty block
  -- above. Df §5's own proof consumes MEAS-BRIDGE(i) = LOC-derived
  -- measurability; with LR the equality is PROVED above
  -- (`sum_alpha_eq_one_of_locality`), and the ≥ half is unconditional
  -- (`one_le_sum_alpha`). Statement change (adding LR or a measurability
  -- row) is fenced — awaiting blueprint-owner adjudication.
  sorry

theorem sum_alphaR_eq_one (NR : NsNullRow p n) :
    ∑ τ ∈ typesFinset n, TD.alphaR p n τ = 1 :=
  sum_alphaR_of_sum_alpha p n TD (sum_alpha_eq_one p n TD NR)

end SumOne

/-! ## I-F3: Lemma ID (interpolation)

Note: the `hdef` hypothesis is part of the blueprint interface shape
(the TRANSFER consumer I-F4 supplies it per prime); the proof route via
the numerator does not consume it — `num R` already vanishes on the
infinite set `(↑) '' Z`, hence is the zero polynomial. -/

set_option linter.unusedVariables false in -- `hdef`: blueprint interface row, see note above
/-- Lemma ID (the interpolation principle), over an arbitrary infinite Z ⊆ ℕ
(deliberately: the D-3 unramified-base clause wants prime powers q = p^δ). -/
theorem ratFunc_eq_zero_of_infinite (R : RatFunc ℚ) {Z : Set ℕ} (hZ : Z.Infinite)
    (hdef : ∀ z ∈ Z, (RatFunc.denom R).eval (z : ℚ) ≠ 0)
    (hval : ∀ z ∈ Z, (RatFunc.num R).eval (z : ℚ) = 0) : R = 0 := by
  rw [← RatFunc.num_eq_zero_iff]
  apply Polynomial.eq_zero_of_infinite_isRoot
  have himg : ((fun z : ℕ => (z : ℚ)) '' Z).Infinite :=
    hZ.image (Set.injOn_of_injective Nat.cast_injective)
  refine himg.mono ?_
  rintro x ⟨z, hz, rfl⟩
  exact hval z hz

/-! ## I-F4: TRANSFER (D-2 (iii)–(iv), hypothesis-explicit)

Verbatim per BP_I §1.6 (Df §5 TRANSFER + instances). Route: Q := Σ_τ R τ − 1
vanishes on the infinite hypothesis set P (per prime q ∈ P, `hsum` + `htie`
identify Σ_τ eval(R τ)(q) with Σ_τ A q τ = 1, cast down ℝ → ℚ by injectivity),
so Lemma ID (I-F3, `ratFunc_eq_zero_of_infinite`) kills Q.

(REG-p) instance remark: at general n the hypothesis row `hP` (P infinite) is
supplied by `MovesU/RegPFinite.regP_cofinite` (the (REG-p)-failing primes form
a finite set) + `Nat.infinite_setOf_prime` (Euclid); `hsum` is supplied at
consumption by SUM-ONE (I-F2, `sum_alphaR_eq_one`) at any semantic instance;
`hdef` by pole-freeness (`MovesU/O12PoleFree`). -/

section Transfer

variable (n : ℕ)

/-- I-F4-internal helper (not a §1.6 display): if every summand's denominator
is non-vanishing at ξ, then the denominator of the finset sum is
non-vanishing at ξ and `RatFunc.eval` distributes over the sum
(`Finset.cons_induction` on `RatFunc.denom_add_dvd` + `RatFunc.eval_add`). -/
theorem denom_sum_eval_ne_zero_and_eval_sum {ι : Type*} (s : Finset ι)
    (F : ι → RatFunc ℚ) (ξ : ℚ)
    (h : ∀ i ∈ s, (RatFunc.denom (F i)).eval ξ ≠ 0) :
    (RatFunc.denom (∑ i ∈ s, F i)).eval ξ ≠ 0 ∧
      RatFunc.eval (RingHom.id ℚ) ξ (∑ i ∈ s, F i) =
        ∑ i ∈ s, RatFunc.eval (RingHom.id ℚ) ξ (F i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    obtain ⟨ihd, ihe⟩ := ih (fun i hi => h i (Finset.mem_cons_of_mem hi))
    have hda : (RatFunc.denom (F a)).eval ξ ≠ 0 := h a (Finset.mem_cons_self a s)
    -- denominator of the sum: `denom_add_dvd` + evaluation of a divisor
    have hd : (RatFunc.denom (F a + ∑ i ∈ s, F i)).eval ξ ≠ 0 := by
      have hdvd : (RatFunc.denom (F a + ∑ i ∈ s, F i)).eval ξ ∣
          (RatFunc.denom (F a)).eval ξ * (RatFunc.denom (∑ i ∈ s, F i)).eval ξ := by
        simpa [Polynomial.eval_mul] using
          Polynomial.eval_dvd (x := ξ)
            (RatFunc.denom_add_dvd (F a) (∑ i ∈ s, F i))
      exact ne_zero_of_dvd_ne_zero (mul_ne_zero hda ihd) hdvd
    -- evaluation of the sum: `RatFunc.eval_add`
    have he : RatFunc.eval (RingHom.id ℚ) ξ (F a + ∑ i ∈ s, F i) =
        RatFunc.eval (RingHom.id ℚ) ξ (F a) +
          RatFunc.eval (RingHom.id ℚ) ξ (∑ i ∈ s, F i) :=
      RatFunc.eval_add (f := RingHom.id ℚ) (a := ξ) hda ihd
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_cons]; exact hd
    · rw [Finset.sum_cons, he, ihe, Finset.sum_cons]

/-- **TRANSFER (D-2 (iii)–(iv), hypothesis-explicit).** Stated over an
ABSTRACT per-prime density family `A` (so no quantification over
`TypeSemantics` instances leaks into hypothesis position): the ONLY facts
consumed about `A` are per-prime normalization (`hsum`, supplied by SUM-ONE
at any semantic instance) and the pointwise tie to R (`htie`, the T-U-ledger
row at general n; unconditional at n = 1, 2 — §3). The prime set P is a NAMED
HYPOTHESIS ROW ((REG-p) primes at general n, infinite by `MovesU/RegPFinite`
+ Euclid). -/
theorem sum_R_eq_one_of_alpha_eq (R : FactorizationType → RatFunc ℚ)
    (A : ℕ → FactorizationType → ℝ) {P : Set ℕ} (hP : P.Infinite)
    (hsum : ∀ q ∈ P, ∑ τ ∈ typesFinset n, A q τ = 1)
    (hdef : ∀ q ∈ P, ∀ τ ∈ typesFinset n, (RatFunc.denom (R τ)).eval (q : ℚ) ≠ 0)
    (htie : ∀ q ∈ P, ∀ τ ∈ typesFinset n,
      A q τ = (RatFunc.num (R τ)).eval (q : ℚ) / (RatFunc.denom (R τ)).eval (q : ℚ)) :
    ∑ τ ∈ typesFinset n, R τ = 1 := by
  -- the (−1) summand has denominator 1
  have hneg1 : RatFunc.denom (-1 : RatFunc ℚ) = 1 := by
    have h1 : (-1 : RatFunc ℚ) = RatFunc.C (-1) := by rw [map_neg, map_one]
    rw [h1, RatFunc.denom_C]
  -- the denominator of Q := Σ R_τ − 1 is non-vanishing on P
  have hdQ : ∀ q ∈ P,
      (RatFunc.denom ((∑ τ ∈ typesFinset n, R τ) - 1)).eval (q : ℚ) ≠ 0 := by
    intro q hq
    obtain ⟨hd, -⟩ := denom_sum_eval_ne_zero_and_eval_sum (typesFinset n) R (q : ℚ)
      (fun τ hτ => hdef q hq τ hτ)
    have hdvd : (RatFunc.denom ((∑ τ ∈ typesFinset n, R τ) - 1)).eval (q : ℚ) ∣
        (RatFunc.denom (∑ τ ∈ typesFinset n, R τ)).eval (q : ℚ) := by
      have := Polynomial.eval_dvd (x := (q : ℚ))
        (RatFunc.denom_add_dvd (∑ τ ∈ typesFinset n, R τ) (-1))
      simpa [sub_eq_add_neg, hneg1, Polynomial.eval_mul] using this
    exact ne_zero_of_dvd_ne_zero hd hdvd
  -- the numerator of Q vanishes on P (hsum + htie per prime, cast down to ℚ)
  have hnQ : ∀ q ∈ P,
      (RatFunc.num ((∑ τ ∈ typesFinset n, R τ) - 1)).eval (q : ℚ) = 0 := by
    intro q hq
    obtain ⟨hd, he⟩ := denom_sum_eval_ne_zero_and_eval_sum (typesFinset n) R (q : ℚ)
      (fun τ hτ => hdef q hq τ hτ)
    -- the ℚ-identity Σ num/denom = 1 at q, by injectivity of ℚ ↪ ℝ
    have hQval : ∑ τ ∈ typesFinset n,
        (RatFunc.num (R τ)).eval (q : ℚ) / (RatFunc.denom (R τ)).eval (q : ℚ)
          = (1 : ℚ) := by
      have hR : ∑ τ ∈ typesFinset n,
          ((((RatFunc.num (R τ)).eval (q : ℚ) : ℚ) : ℝ)
            / (((RatFunc.denom (R τ)).eval (q : ℚ) : ℚ) : ℝ)) = (1 : ℝ) := by
        rw [← hsum q hq]
        exact Finset.sum_congr rfl (fun τ hτ => (htie q hq τ hτ).symm)
      exact_mod_cast hR
    -- eval(Σ R_τ) = 1: each eval(R_τ) is num/denom by definitional unfolding
    have hevalS : RatFunc.eval (RingHom.id ℚ) (q : ℚ) (∑ τ ∈ typesFinset n, R τ) = 1 := by
      rw [he, ← hQval]
      exact Finset.sum_congr rfl (fun τ _ => rfl)
    -- eval(−1) = −1 and eval distributes over the (−1) summand
    have hm1 : RatFunc.eval (RingHom.id ℚ) (q : ℚ) (-1 : RatFunc ℚ) = -1 := by
      have h1 : (-1 : RatFunc ℚ) = RatFunc.C (-1) := by rw [map_neg, map_one]
      rw [h1, RatFunc.eval_C]
      simp
    have hadd : RatFunc.eval (RingHom.id ℚ) (q : ℚ)
        ((∑ τ ∈ typesFinset n, R τ) + (-1)) =
        RatFunc.eval (RingHom.id ℚ) (q : ℚ) (∑ τ ∈ typesFinset n, R τ) +
          RatFunc.eval (RingHom.id ℚ) (q : ℚ) (-1 : RatFunc ℚ) :=
      RatFunc.eval_add (f := RingHom.id ℚ) (a := (q : ℚ)) hd (by simp [hneg1])
    -- eval(Q) = 0
    have hevalQ : RatFunc.eval (RingHom.id ℚ) (q : ℚ)
        ((∑ τ ∈ typesFinset n, R τ) - 1) = 0 := by
      rw [sub_eq_add_neg, hadd, hevalS, hm1]
      norm_num
    -- extract the numerator vanishing from eval(Q) = 0, denom(Q) ≠ 0
    have h0 : (RatFunc.num ((∑ τ ∈ typesFinset n, R τ) - 1)).eval (q : ℚ) /
        (RatFunc.denom ((∑ τ ∈ typesFinset n, R τ) - 1)).eval (q : ℚ) = 0 := hevalQ
    exact (div_eq_zero_iff.mp h0).resolve_right (hdQ q hq)
  -- Lemma ID (I-F3) interpolation kills Q
  have hQ0 : (∑ τ ∈ typesFinset n, R τ) - 1 = 0 :=
    ratFunc_eq_zero_of_infinite _ hP hdQ hnQ
  exact sub_eq_zero.mp hQ0
-- Consumption shape: A q := (canonical TypeSemantics at q).alphaR q n, with
-- hsum := sum_alphaR_eq_one; the (REG-p) instance takes P := regular primes.

end Transfer

/-! ## I-F4: TRANSFER (D-2 (iii)–(iv), hypothesis-explicit)

Verbatim per BP_I §1.6 (Df §5 TRANSFER + instances). Route: Q := Σ_τ R τ − 1
vanishes on the infinite hypothesis set P (per prime q ∈ P, `hsum` + `htie`
identify Σ_τ eval(R τ)(q) with Σ_τ A q τ = 1), so Lemma ID (I-F3,
`ratFunc_eq_zero_of_infinite`) kills Q.

(REG-p) instance remark: at general n the hypothesis row `hP` (P infinite) is
supplied by `MovesU/RegPFinite.regP_cofinite` (the (REG-p)-failing primes form
a finite set) + `Nat.infinite_setOf_prime` (Euclid); `hsum` is supplied at
consumption by SUM-ONE (I-F2, `sum_alphaR_eq_one`) at any semantic instance;
`hdef` by pole-freeness (`MovesU/O12PoleFree`). -/

section Transfer

variable (n : ℕ)

/-- Helper for I-F4 (I-F4-internal, not a §1.6 display): over a finite index
set, if every summand's denominator is nonvanishing at `q`, then the sum's
denominator is nonvanishing at `q` and `RatFunc.eval` distributes over the sum
(iterated `RatFunc.eval_add`, with `RatFunc.denom_add_dvd` propagating the
denominator control). -/
theorem denom_sum_eval_ne_zero_and_eval_sum {ι : Type*} (s : Finset ι)
    (F : ι → RatFunc ℚ) (q : ℚ)
    (h : ∀ i ∈ s, (RatFunc.denom (F i)).eval q ≠ 0) :
    (RatFunc.denom (∑ i ∈ s, F i)).eval q ≠ 0 ∧
      RatFunc.eval (RingHom.id ℚ) q (∑ i ∈ s, F i)
        = ∑ i ∈ s, RatFunc.eval (RingHom.id ℚ) q (F i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [RatFunc.denom_zero]
  | cons a s ha ih =>
    obtain ⟨hd, he⟩ := ih fun i hi => h i (Finset.mem_cons_of_mem hi)
    have hda : (RatFunc.denom (F a)).eval q ≠ 0 := h a (Finset.mem_cons_self a s)
    have hdsum : (RatFunc.denom (F a + ∑ i ∈ s, F i)).eval q ≠ 0 := by
      intro h0
      have h1 : (RatFunc.denom (F a) * RatFunc.denom (∑ i ∈ s, F i)).eval q = 0 :=
        Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd _ _) h0
      rw [Polynomial.eval_mul] at h1
      exact mul_ne_zero hda hd h1
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_cons]
      exact hdsum
    · rw [Finset.sum_cons, Finset.sum_cons,
        RatFunc.eval_add (f := RingHom.id ℚ) (a := q) hda hd, he]

/-- **TRANSFER (D-2 (iii)–(iv), hypothesis-explicit).** Stated over an
ABSTRACT per-prime density family `A` (so no quantification over
`TypeSemantics` instances leaks into hypothesis position): the ONLY facts
consumed about `A` are per-prime normalization (`hsum`, supplied by SUM-ONE
at any semantic instance) and the pointwise tie to R (`htie`, the T-U-ledger
row at general n; unconditional at n = 1, 2 — §3). The prime set P is a NAMED
HYPOTHESIS ROW ((REG-p) primes at general n, infinite by `MovesU/RegPFinite`
+ Euclid). -/
theorem sum_R_eq_one_of_alpha_eq (R : FactorizationType → RatFunc ℚ)
    (A : ℕ → FactorizationType → ℝ) {P : Set ℕ} (hP : P.Infinite)
    (hsum : ∀ q ∈ P, ∑ τ ∈ typesFinset n, A q τ = 1)
    (hdef : ∀ q ∈ P, ∀ τ ∈ typesFinset n, (RatFunc.denom (R τ)).eval (q : ℚ) ≠ 0)
    (htie : ∀ q ∈ P, ∀ τ ∈ typesFinset n,
      A q τ = (RatFunc.num (R τ)).eval (q : ℚ) / (RatFunc.denom (R τ)).eval (q : ℚ)) :
    ∑ τ ∈ typesFinset n, R τ = 1 := by
  have key : ∀ q ∈ P,
      (RatFunc.denom ((∑ τ ∈ typesFinset n, R τ) - 1)).eval (q : ℚ) ≠ 0 ∧
        (RatFunc.num ((∑ τ ∈ typesFinset n, R τ) - 1)).eval (q : ℚ) = 0 := by
    intro q hq
    obtain ⟨hdS, heS⟩ :=
      denom_sum_eval_ne_zero_and_eval_sum (typesFinset n) R (q : ℚ) (hdef q hq)
    -- the ℚ-level normalization at q, cast down from the ℝ-level `hsum` + `htie`
    have hQ : ∑ τ ∈ typesFinset n,
        (RatFunc.num (R τ)).eval (q : ℚ) / (RatFunc.denom (R τ)).eval (q : ℚ)
          = (1 : ℚ) := by
      have hR : ∑ τ ∈ typesFinset n,
          (((RatFunc.num (R τ)).eval (q : ℚ) : ℝ)
            / ((RatFunc.denom (R τ)).eval (q : ℚ) : ℝ)) = (1 : ℝ) := by
        rw [← hsum q hq]
        exact Finset.sum_congr rfl fun τ hτ => (htie q hq τ hτ).symm
      exact_mod_cast hR
    have hevalS :
        RatFunc.eval (RingHom.id ℚ) (q : ℚ) (∑ τ ∈ typesFinset n, R τ) = 1 := by
      rw [heS, ← hQ]
      exact Finset.sum_congr rfl fun τ _ => by simp [RatFunc.eval]
    -- denominator control for S − 1
    have hd1 : (RatFunc.denom (-1 : RatFunc ℚ)).eval (q : ℚ) ≠ 0 := by
      have h1 : (-1 : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) (-1) := by
        simp
      rw [h1, RatFunc.denom_algebraMap]
      simp
    have hdvd : RatFunc.denom ((∑ τ ∈ typesFinset n, R τ) - 1)
        ∣ RatFunc.denom (∑ τ ∈ typesFinset n, R τ) * RatFunc.denom (-1 : RatFunc ℚ) := by
      rw [sub_eq_add_neg]
      exact RatFunc.denom_add_dvd _ _
    have hdQ : (RatFunc.denom ((∑ τ ∈ typesFinset n, R τ) - 1)).eval (q : ℚ) ≠ 0 := by
      intro h0
      have h1 := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd h0
      rw [Polynomial.eval_mul] at h1
      exact mul_ne_zero hdS hd1 h1
    -- eval (S − 1) = 0 at q, via eval ((S − 1) + 1) = eval S = 1
    have hevalQ :
        RatFunc.eval (RingHom.id ℚ) (q : ℚ) ((∑ τ ∈ typesFinset n, R τ) - 1) = 0 := by
      have hden1 : (RatFunc.denom (1 : RatFunc ℚ)).eval (q : ℚ) ≠ 0 := by
        rw [RatFunc.denom_one]
        simp
      have hadd := RatFunc.eval_add (f := RingHom.id ℚ) (a := (q : ℚ)) hdQ hden1
      have hSid : (∑ τ ∈ typesFinset n, R τ) - 1 + 1 = ∑ τ ∈ typesFinset n, R τ := by
        ring
      rw [hSid, hevalS, RatFunc.eval_one] at hadd
      linarith [hadd]
    -- numerator vanishes: eval = num.eval / denom.eval with denom.eval ≠ 0
    have hnum : (RatFunc.num ((∑ τ ∈ typesFinset n, R τ) - 1)).eval (q : ℚ) = 0 := by
      have h2 : (RatFunc.num ((∑ τ ∈ typesFinset n, R τ) - 1)).eval (q : ℚ)
          / (RatFunc.denom ((∑ τ ∈ typesFinset n, R τ) - 1)).eval (q : ℚ) = 0 := by
        simpa [RatFunc.eval] using hevalQ
      exact (div_eq_zero_iff.mp h2).resolve_right hdQ
    exact ⟨hdQ, hnum⟩
  have hzero : (∑ τ ∈ typesFinset n, R τ) - 1 = 0 :=
    ratFunc_eq_zero_of_infinite _ hP (fun z hz => (key z hz).1) fun z hz => (key z hz).2
  exact sub_eq_zero.mp hzero
-- Consumption shape: A q := (canonical TypeSemantics at q).alphaR q n, with
-- hsum := sum_alphaR_eq_one; the (REG-p) instance takes P := regular primes.

end Transfer

/-! ## I-F5 (remark unit): the TRANSFER instance rows (Df §5 instances ¶)

**n = 1 — unconditional (Wave G, `Base.lean`; not re-proved here, no import
of the later-wave file).** Over the singleton menu Σ₁ = {(1,1)} the constant
family R := 1 sums to 1 (`base1_sumR`), and `base1_alpha_eq_ratFunc_one`
ties α to the num/denom evaluation of `1 : RatFunc ℚ` given the named (LIN)
row — the n = 1 TRANSFER instance is unconditional.

**n = 2 — the corpus `OM.UniformCapstone` values.** The fixed degree-2 table
(`numR/denR = 1/(X+1)` ramified; `numI/denI = numS/denS = X/(2X+2)` inert =
split) satisfies the direct table check 1/(q+1) + q/(2(q+1))·2 = 1 as a
`RatFunc ℚ` computation: `n2_table_check` below is the BP-row display,
`n2_table_check_corpus` keys it to the corpus polynomials of
`OM/UniformCapstone` §P (the `montes_uniform_n2` value table).

**The §3 fence (BP_I §3, review item 13), displayed:** the n = 2 corpus
values are ANCHORS only. `montes_uniform_n2` does not identify them with
this scaffold's `alpha`, so NO unconditional n = 2 α-instance of TRANSFER
(I-F4) is claimed until the α-faithfulness tie exists. The identities below
are pure `RatFunc ℚ` computations consuming nothing from the measure floor. -/

section InstanceRows

open Polynomial

/-- I-F5-internal helper (not a blueprint display): `X + 1 ≠ 0` in
`RatFunc ℚ` — it is the `algebraMap` image of the monic `X + 1`. -/
theorem ratFuncX_add_one_ne_zero : (RatFunc.X + 1 : RatFunc ℚ) ≠ 0 := by
  have hpoly : (Polynomial.X + 1 : Polynomial ℚ) ≠ 0 := by
    have h := Polynomial.monic_X_add_C (1 : ℚ)
    rw [Polynomial.C_1] at h
    exact h.ne_zero
  have hmap : (RatFunc.X + 1 : RatFunc ℚ)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X + 1) := by
    rw [map_add, RatFunc.algebraMap_X, map_one]
  rw [hmap]
  exact RatFunc.algebraMap_ne_zero hpoly

/-- I-F5, n = 2 direct table check, BP-row display:
`1/(q+1) + q/(2(q+1))·2 = 1` as a `RatFunc ℚ` computation (by `field_simp`,
per the BP proof-sketch column). -/
theorem n2_table_check :
    1 / (RatFunc.X + 1) + RatFunc.X / (2 * (RatFunc.X + 1)) * 2
      = (1 : RatFunc ℚ) := by
  have hX1 := ratFuncX_add_one_ne_zero
  field_simp
  ring

/-- I-F5, n = 2 direct table check keyed to the corpus `OM.UniformCapstone`
fixed polynomials (§P): ram + inert + split = 1 in `RatFunc ℚ`. ANCHOR only
— no α-identification claimed (the §3 fence above). -/
theorem n2_table_check_corpus :
    algebraMap (Polynomial ℚ) (RatFunc ℚ) OM.UniformCapstone.numR
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) OM.UniformCapstone.denR
      + algebraMap (Polynomial ℚ) (RatFunc ℚ) OM.UniformCapstone.numI
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) OM.UniformCapstone.denI
      + algebraMap (Polynomial ℚ) (RatFunc ℚ) OM.UniformCapstone.numS
        / algebraMap (Polynomial ℚ) (RatFunc ℚ) OM.UniformCapstone.denS
      = 1 := by
  have hX1 := ratFuncX_add_one_ne_zero
  unfold OM.UniformCapstone.numR OM.UniformCapstone.denR
    OM.UniformCapstone.numI OM.UniformCapstone.denI
    OM.UniformCapstone.numS OM.UniformCapstone.denS
  simp only [map_add, map_mul, map_one, map_ofNat, RatFunc.algebraMap_X]
  field_simp
  ring

end InstanceRows

end LeanUrat.Scaffold
