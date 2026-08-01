/-
BP_I §1.6 — SUM-ONE and TRANSFER (`SumOne.lean`).
Unit I-F3: `ratFunc_eq_zero_of_infinite` (Lemma ID, the interpolation
principle), verbatim per BP_I §1.6 (Df §5 Lemma ID): A(z) = 0 on an
infinite Z ⊆ ℚ-embedded ℕ ⇒ `Polynomial.eq_zero_of_infinite_isRoot`
kills the numerator ⇒ R = 0 via `RatFunc.num_eq_zero_iff`. Stated over
an ARBITRARY infinite Z ⊆ ℕ (deliberately: the D-3 unramified-base
clause wants prime powers q = p^δ, not just primes). Deps: mathlib
RatFunc only.
-/
import Mathlib
import LeanUrat.Scaffold.MeasureFloor.Semantic

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

end LeanUrat.Scaffold
