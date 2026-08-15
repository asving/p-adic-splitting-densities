/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B27

/-!
# Uniformity.ChapB.B45 — the residual factorization exists, into pairwise coprime factors

**Chapter B, NODE B.45** (`blueprint/CHAP-B_leaf_layer.md` §6).  *The residual factorization
exists and its factors are pairwise coprime.*  Let `K` be a finite field and `R ∈ K[Y]` monic of
positive degree.  Then there is a `Finset s` of monic irreducible `ψ` and a multiplicity function
`a` with

* every `ψ ∈ s` monic irreducible, and `0 < a ψ`;
* distinct `ψ, χ ∈ s` coprime;
* `R = ∏_{ψ ∈ s} ψ ^ a ψ` — an **equality**, not an association;
* `R.Separable ↔ ∀ ψ ∈ s, a ψ = 1`.

This is GMN Thm 1.19's `R_λ(f) ∼ ψ₁^{a₁} ⋯ ψ_t^{a_t}` made into a Lean object: the factorization
data every downstream residual split (B.48) and every census index (`EFF.W12.25`) quotes.  The
association of Thm 1.19 is upgraded to equality here because both sides are monic — that is what
makes the factor `Finset` usable as an index set with no unit bookkeeping.

DEPENDS: B.27 (`separable_iff_squarefree`, the finite-field bridge) · mathlib
`UniqueFactorizationMonoid.normalizedFactors` and its API
(`Polynomial.mem_normalizedFactors_iff`, `Polynomial.leadingCoeff_mul_prod_normalizedFactors`,
`UniqueFactorizationMonoid.normalizedFactors_eq_of_dvd`,
`UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`), `Finset.prod_multiset_count`,
`Irreducible.coprime_iff_not_dvd`, `Multiset.nodup_iff_count_le_one`.

**PROOF** (the concrete route the blueprint names).  Take
`s := (normalizedFactors R).toFinset` and `a ψ := (normalizedFactors R).count ψ`.

1. Over a field the normalisation of `K[Y]` **is** "monic", so
   `Polynomial.mem_normalizedFactors_iff` reads membership as `Irreducible ψ ∧ ψ.Monic ∧ ψ ∣ R` —
   clause 1 verbatim.  `0 < a ψ` is `Multiset.count_pos` on `Multiset.mem_toFinset`.
2. Coprimality: distinct members of `normalizedFactors R` do not divide one another
   (`normalizedFactors_eq_of_dvd`: within the normalized factors, `ψ ∣ χ → ψ = χ`), and an
   irreducible non-divisor is coprime in the Bézout ring `K[Y]`
   (`Irreducible.coprime_iff_not_dvd`, the same mathlib route B.46 confirmed).
3. The product: `Finset.prod_multiset_count` turns `∏_{ψ ∈ s} ψ ^ a ψ` into
   `(normalizedFactors R).prod`, and `leadingCoeff_mul_prod_normalizedFactors` says
   `C R.leadingCoeff * (normalizedFactors R).prod = R`; `hR.leadingCoeff = 1` kills the constant.
   (This is the "both monic, hence associated ⇒ equal" step, done in the form mathlib already
   provides.)
4. Separability: `R.Separable ↔ Squarefree R` is B.27 (this is the only place `[Finite K]` is
   used, via perfectness), `Squarefree R ↔ (normalizedFactors R).Nodup` is
   `squarefree_iff_nodup_normalizedFactors`, and `Nodup ↔ ∀ ψ ∈ s, count ψ = 1` is
   `Multiset.nodup_iff_count_le_one` combined with `0 < a ψ` on members (off `s` the count is `0`,
   so `≤ 1` is free).

The signed hypothesis `hd : 0 < R.natDegree` is not needed: `hR.ne_zero` alone drives every step,
and at `R = 1` the statement is true with `s = ∅`.  It is retained because the signature is frozen
against the gate-verified stub (`leanspec/Leanspec/ChapB.lean`, **B.45**).

**SOURCE.** `docs/GMN_citations.md` Thm 1.19 (*"`R_λ(f) ∼ ψ_1^{a_1} … ψ_t^{a_t}` into
pairwise-distinct monic irreducibles in `F_φ[y]`"*); `EFF.HE3.32` (*"`R_λ = Π_r r^{m_r}`"*);
`EFF.W12.25` (the censuses are indexed by exactly this factorization type).

ENVIRONMENT: ENV-D + `[Finite K]` — the node binds its own `{K : Type*} [Field K] [Finite K]`
and mentions no `O`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open UniqueFactorizationMonoid

-- `hd : 0 < R.natDegree` is part of the frozen signature and is not used by the proof; see the
-- module docstring.
set_option linter.unusedVariables false in
/-- **B.45 — the residual factorization exists and its factors are pairwise coprime.**  A monic
`R ∈ K[Y]` of positive degree over a finite field `K` is *equal* to `∏_{ψ ∈ s} ψ ^ a ψ` for a
`Finset s` of monic irreducibles with positive, pairwise-coprime-indexed multiplicities, and `R`
is separable exactly when every multiplicity is `1`. -/
theorem exists_residual_factorization {K : Type*} [Field K] [Finite K]
    {R : Polynomial K} (hR : R.Monic) (hd : 0 < R.natDegree) :
    ∃ (s : Finset (Polynomial K)) (a : Polynomial K → ℕ),
      (∀ ψ ∈ s, ψ.Monic ∧ Irreducible ψ) ∧ (∀ ψ ∈ s, 0 < a ψ) ∧
      (∀ ψ ∈ s, ∀ χ ∈ s, ψ ≠ χ → IsCoprime ψ χ) ∧
      R = ∏ ψ ∈ s, ψ ^ a ψ ∧
      (R.Separable ↔ ∀ ψ ∈ s, a ψ = 1) := by
  classical
  have hR0 : R ≠ 0 := hR.ne_zero
  set F : Multiset (Polynomial K) := normalizedFactors R with hFdef
  have hmemF : ∀ ψ ∈ F, Irreducible ψ ∧ ψ.Monic ∧ ψ ∣ R := fun ψ hψ =>
    (Polynomial.mem_normalizedFactors_iff hR0).1 hψ
  refine ⟨F.toFinset, fun ψ => F.count ψ, ?_, ?_, ?_, ?_, ?_⟩
  · -- monic irreducible factors
    intro ψ hψ
    obtain ⟨hirr, hmon, -⟩ := hmemF ψ (Multiset.mem_toFinset.1 hψ)
    exact ⟨hmon, hirr⟩
  · -- positive multiplicities
    intro ψ hψ
    exact Multiset.count_pos.2 (Multiset.mem_toFinset.1 hψ)
  · -- pairwise coprime
    intro ψ hψ χ hχ hne
    have hψm : ψ ∈ F := Multiset.mem_toFinset.1 hψ
    have hχm : χ ∈ F := Multiset.mem_toFinset.1 hχ
    refine ((hmemF ψ hψm).1.coprime_iff_not_dvd).2 fun hdvd => hne ?_
    exact normalizedFactors_eq_of_dvd R ψ hψm χ hχm hdvd
  · -- the product is `R` on the nose
    rw [← Finset.prod_multiset_count F]
    have hprod : Polynomial.C R.leadingCoeff * F.prod = R :=
      Polynomial.leadingCoeff_mul_prod_normalizedFactors R
    rwa [hR.leadingCoeff, map_one, one_mul, eq_comm] at hprod
  · -- separability ↔ all multiplicities are one
    rw [Uniformity.Density.Leaf.separable_iff_squarefree hR0,
      squarefree_iff_nodup_normalizedFactors hR0, ← hFdef]
    constructor
    · intro hnd ψ hψ
      exact le_antisymm (Multiset.nodup_iff_count_le_one.1 hnd ψ)
        (Multiset.count_pos.2 (Multiset.mem_toFinset.1 hψ))
    · intro hall
      refine Multiset.nodup_iff_count_le_one.2 fun ψ => ?_
      by_cases hψ : ψ ∈ F
      · exact le_of_eq (hall ψ (Multiset.mem_toFinset.2 hψ))
      · simp [Multiset.count_eq_zero_of_notMem hψ]

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.exists_residual_factorization
end AxCheck
