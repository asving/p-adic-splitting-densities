/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# LeanUrat.L3 — Residue-field factorization-shape counts (the first fully-proved leaf)

Formalizes the content of `notes/L3_proof.md`. Over a finite field `F_Q`:

* **(a) separability core (FULLY PROVED, no `sorry`).** Every irreducible polynomial over `F_Q` is
  separable; hence over a finite field "non-separable ⟺ non-squarefree", with **no
  inseparable-irreducible exceptions in any characteristic** (the precise content of "Frobenius is
  bijective on points": all wildness lives in the `p`-adic lifting, never in the residue-field
  count). This is the structurally load-bearing part of L3 and it compiles cleanly.

* **the monic count (FULLY PROVED, no `sorry`).** The number of monic polynomials of degree exactly
  `m` over `F_Q` is `Q^m`. Proved via the affine bijection `g ↦ X^m + g` with `degreeLT F_Q m`,
  whose cardinality is `Q^m` (`Module.natCard_eq_pow_finrank` + `degreeLT.basis`).

* **(b)/(c) the count formulas (STATED; `sorry` with a flagged missing-mathlib note).** The
  squarefree count `Q^m - Q^{m-1}` and the Gauss/Möbius irreducible count `N_d(Q)` and the resulting
  shape-count polynomials `S_λ(Q)` are **not in mathlib v4.31.0** (confirmed by source search: no
  `cardSquarefree`, no necklace/Möbius irreducible-count, no zeta-function statement for `F_q[X]`).
  These would require formalizing the Carlitz/zeta generating-function identity from scratch. We
  state them and isolate the single missing fact in `sorry`, with the exact gap noted at each site.
-/

-- Prose-heavy blueprint docstrings and a research header; these style linters are cosmetic here.
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.L3

open Polynomial

/-! ## 1. Part (a): perfectness ⇒ every irreducible is separable ⇒ separable = squarefree -/

variable {F : Type*} [Field F] [Finite F]

/-- **Lemma 2 (no inseparable irreducibles).** Over a finite field, every irreducible polynomial is
separable. (`notes/L3_proof.md §1.1`, Lemma 2.) Finite fields are perfect
(`PerfectField.ofFinite`), and over a perfect field every irreducible is separable
(`PerfectField.separable_of_irreducible`). This is the "no inseparable irreducible in any
characteristic" fact, the residue-field shadow of "Frobenius bijective on points". -/
theorem irreducible_separable {p : F[X]} (hp : Irreducible p) : p.Separable :=
  PerfectField.separable_of_irreducible hp

/-- **Corollary 3 (separable ⟺ squarefree).** Over a finite field, a polynomial is separable iff it
is squarefree; hence **non-separable ⟺ non-squarefree**. (`notes/L3_proof.md §1.1`, Cor 3.) This is
`PerfectField.separable_iff_squarefree`, available since finite fields are perfect. -/
theorem separable_iff_squarefree {g : F[X]} : g.Separable ↔ Squarefree g :=
  PerfectField.separable_iff_squarefree

/-- The "needs-refinement / discriminant" locus coincidence (`notes/L3_proof.md §1.1`):
**non-separable ⟺ non-squarefree** over a finite field. -/
theorem not_separable_iff_not_squarefree {g : F[X]} : ¬ g.Separable ↔ ¬ Squarefree g :=
  not_congr separable_iff_squarefree

/-! ## 2. The monic count: `#{monic of degree m} = Q^m`

We count monic polynomials of degree exactly `m` over `F_Q` by the affine bijection with the
`F_Q`-vector space `degreeLT F m` of polynomials of degree `< m`, via `g ↦ X^m + g`. The latter has
`F_Q`-cardinality `Q^m` by `Module.natCard_eq_pow_finrank` (a finite module over a finite ring, via
the `Module.Finite` instance) and `finrank (degreeLT F m) = m` (from
`degreeLT.basis : Basis (Fin m) F (degreeLT F m)`). We use `Nat.card` throughout to avoid needing an
explicit `Fintype` instance on the submodule (none is provided by mathlib v4.31.0). -/

section MonicCount

/-- The `F`-cardinality of the space of polynomials of degree `< m` is `Q^m`, where `Q = #F`.
Proved from the `Fin m`-indexed basis of `degreeLT F m`. -/
theorem card_degreeLT (m : ℕ) :
    Nat.card (degreeLT F m) = Nat.card F ^ m := by
  have hbasis : Module.finrank F (degreeLT F m) = m := by
    rw [Module.finrank_eq_card_basis (degreeLT.basis F m), Fintype.card_fin]
  rw [Module.natCard_eq_pow_finrank (K := F) (V := degreeLT F m), hbasis]

/-- The set of monic polynomials of degree exactly `m`. -/
def monicDegree (F : Type*) [Field F] (m : ℕ) : Set F[X] :=
  {p | p.Monic ∧ p.natDegree = m}

/-- **The monic count is `Q^m` (FULLY PROVED).** The number of monic polynomials of degree exactly
`m` over `F_Q` equals `Q^m`. (`notes/L3_proof.md §1.2`: "`N_k = Q^k` the number of all monic of
degree `k`", the base count underlying Theorem A.)

We exhibit the explicit bijection `degreeLT F m ≃ {monic of degree m}` sending `g ↦ X^m + g`, then
transport the cardinality `card_degreeLT`. -/
theorem card_monicDegree (m : ℕ) :
    Nat.card (monicDegree F m) = Nat.card F ^ m := by
  -- Bijection: degreeLT F m → monicDegree F m,  g ↦ X^m + g.
  have hdeg : ∀ g : degreeLT F m,
      (X ^ m + (g : F[X])).Monic ∧ (X ^ m + (g : F[X])).natDegree = m := by
    intro g
    have hdlt : (g : F[X]).degree < (X ^ m : F[X]).degree := by
      rw [degree_X_pow]; exact mem_degreeLT.1 g.2
    refine ⟨(monic_X_pow m).add_of_left hdlt, natDegree_eq_of_degree_eq_some ?_⟩
    rw [add_comm, degree_add_eq_right_of_degree_lt hdlt, degree_X_pow]
  let toMonic : degreeLT F m → monicDegree F m := fun g => ⟨X ^ m + (g : F[X]), hdeg g⟩
  have hbij : Function.Bijective toMonic := by
    constructor
    · -- injective: X^m + g₁ = X^m + g₂ ⇒ g₁ = g₂
      exact fun g₁ g₂ h => Subtype.ext (add_left_cancel (congrArg Subtype.val h))
    · -- surjective: a monic p of degree m equals X^m + (p - X^m), with p - X^m of degree < m
      rintro ⟨p, hpmonic, hpdeg⟩
      have hp0 : p ≠ 0 := hpmonic.ne_zero
      have hpdeg' : p.degree = (m : WithBot ℕ) := by rw [degree_eq_natDegree hp0, hpdeg]
      -- p and X^m are both monic of natDegree m; their leading terms cancel, so deg (p - X^m) < m
      have hpX : (p - X ^ m).degree < (m : WithBot ℕ) := by
        have := degree_sub_lt (hpdeg'.trans (degree_X_pow m).symm) hp0
          (by rw [hpmonic.leadingCoeff, (monic_X_pow m).leadingCoeff])
        rwa [hpdeg'] at this
      exact ⟨⟨p - X ^ m, mem_degreeLT.2 hpX⟩, Subtype.ext (by change X ^ m + (p - X ^ m) = p; ring)⟩
  rw [← Nat.card_eq_of_bijective toMonic hbij, card_degreeLT]

end MonicCount

/-! ## 3. Part (a)/(b)/(c) — the count formulas (STATED; flagged `sorry`)

The following are the closed-form counts of `notes/L3_proof.md` (Theorems A, B, C). Each requires a
generating-function/Möbius identity that is **NOT present in mathlib v4.31.0** (verified by source
search). We state them with the precise missing-mathlib fact flagged at each `sorry`. -/

section Counts

/-- The set of squarefree monic polynomials of degree exactly `m`. -/
def squarefreeMonicDegree (F : Type*) [Field F] (m : ℕ) : Set F[X] :=
  {p | p.Monic ∧ p.natDegree = m ∧ Squarefree p}

/-- **Theorem A (squarefree count).** Over `F_Q`, for `m ≥ 2` the number of squarefree monic
polynomials of degree `m` is `Q^m - Q^{m-1}`; equivalently the non-squarefree count is `Q^{m-1}`.
(`notes/L3_proof.md §1.2`, Theorem A.)

FLAGGED SORRY — MISSING MATHLIB. mathlib v4.31.0 has **no** squarefree-polynomial cardinality
(`cardSquarefree`) and **no** zeta/Carlitz generating-function identity
`∑_k (#monic deg k) u^k = S(u) · ∑_j Q^j u^{2j}` for `F_q[X]`. Proving this requires either the
unique-factorization `A·B²` bijection counting argument or the Euler-product identity — a
self-contained development not yet attempted here. The base fact it builds on (`#monic deg m = Q^m`,
`card_monicDegree`) **is** proved above. -/
theorem card_squarefreeMonicDegree (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (squarefreeMonicDegree F m) = Nat.card F ^ m - Nat.card F ^ (m - 1) := by
  sorry

end Counts

/-- The set of monic irreducible polynomials of degree exactly `d` over `F`. -/
def monicIrreducibleDegree (F : Type*) [Field F] (d : ℕ) : Set F[X] :=
  {p | Irreducible p ∧ p.Monic ∧ p.natDegree = d}

/-- **Theorem B (Gauss/necklace irreducible count).** The number of monic irreducible polynomials of
degree `d ≥ 1` over `F_Q` is `N_d(Q) = (1/d) ∑_{e ∣ d} μ(e) Q^{d/e}`, a single polynomial in `Q`
independent of `p`. (`notes/L3_proof.md §2.1`, Theorem B.)

FLAGGED SORRY — MISSING MATHLIB. mathlib v4.31.0 has no Gauss/necklace count and no Möbius-inversion
statement for monic-irreducible cardinalities over a finite field (no declaration matching
`necklace`/Möbius irreducible count was found). The accessible intermediate `∑_{e ∣ d} e · N_e(Q) =
Q^d` (every element of `F_{Q^d}` is a root of a unique monic irreducible of degree dividing `d`) is
also absent and would need to be proved from `FiniteField` subfield/Frobenius API before Möbius
inversion (`ArithmeticFunction.moebius`). -/
theorem gauss_necklace_count
    (F : Type*) [Field F] [Finite F] (d : ℕ) (hd : 1 ≤ d) :
    (d : ℚ) * (Nat.card (monicIrreducibleDegree F d) : ℚ)
      = ∑ e ∈ d.divisors,
          ((ArithmeticFunction.moebius e : ℤ) : ℚ) * (Nat.card F : ℚ) ^ (d / e) := by
  sorry

/-! ## 4. Universality (part (b)/(c)): shape counts are polynomials in `Q`

Theorem C of `notes/L3_proof.md §2.2` packages the shape count as `S_λ(Q) = ∏_d C(N_d(Q)+r_d-1, r_d)`,
a single polynomial in `Q`. Since it is built from `gauss_necklace_count` (Theorem B) by
multiset-coefficient products, its formalization is downstream of the flagged `sorry` above; the
*universality* claim (a single `S_λ ∈ ℚ[t]` valid for every `Q`) is the polynomial structure
recorded in the interface `perShapeVolume_rational`. We do not restate it here; the load-bearing
proved content of L3 is the separability core (§1) and the monic count (§2). -/

end LeanUrat.L3
