/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.QuadCert

/-!
# Uniformity.Density.AnisotropicForms — an anisotropic binary quadratic over every base

**CN-15** of `spec/CERTAIN_NODES_2026-08-14.md` (ledger HYP.147).

`Anisotropic a` (`Density/QuadCert.lean`) says the binary form `u² − a₁uv + a₀v²` of the monic
quadratic `X² + a₁X + a₀` has only the trivial zero mod `𝔪`. The landed inert certificates were
`ℤ_[p]`-only (`Gates.lean:441`); this file supplies the *general-`O`* existence statement

  `exists_anisotropic : ∃ a : Fin 2 → O, Anisotropic a`

for every DVR `O` with finite residue field, which is what the `n = 2` leaf of
`UniformityStatement` needs (it quantifies over every complete DVR).

## The finite-field input, re-derived here

The counting over the residue field is re-derived **self-contained from mathlib** in §1 rather
than imported: `leanfinal` must not depend on `leancheck`, where the same material lives as
`UniformityCheck.two_mul_card_aniK` (`FiniteFieldQuad.lean`). The names here are deliberately
distinct from leancheck's (`AniForm` vs `AniK`, `rootPairMap` vs `rootMap`) so that a file
opening both namespaces stays unambiguous.

The argument: `rootPairMap : Sym2 K → K × K`, `s(r,s) ↦ (rs, r+s)`, is injective with image
exactly the pairs whose quadratic *has* a root. If no pair were anisotropic it would be
surjective too, forcing `#Sym2 K = #(K × K)`, i.e. `q(q+1)/2 = q²`, i.e. `q = 1` — impossible
for a field. Nothing assumes `2 ≠ 0`: the proof works verbatim in characteristic two.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 1. The finite-field count (self-contained, mathlib only) -/

section FiniteField

variable {K : Type*} [Field K]

/-- **Anisotropy over a field, "no root" form.** The pair `p = (b₀, b₁)` encodes the monic
quadratic `X² − b₁X + b₀`; `AniForm p` says it has no root in `K`. (Named apart from
leancheck's `UniformityCheck.AniK`, which is the same predicate in the other repo.) -/
def AniForm (p : K × K) : Prop := ∀ y : K, y ^ 2 - p.2 * y + p.1 ≠ 0

/-- **The two readings agree**: the binary form `u² − b₁uv + b₀v²` has only the trivial zero iff
the monic quadratic `X² − b₁X + b₀` has no root. -/
theorem aniForm_iff (b₀ b₁ : K) :
    (∀ u v : K, u ^ 2 - b₁ * u * v + b₀ * v ^ 2 = 0 → u = 0 ∧ v = 0) ↔ AniForm (b₀, b₁) := by
  simp only [AniForm]
  constructor
  · intro h y hy
    exact one_ne_zero (h y 1 (by linear_combination hy)).2
  · intro h u v huv
    by_cases hv : v = 0
    · subst hv
      refine ⟨?_, rfl⟩
      have h2 : u ^ 2 = 0 := by linear_combination huv
      simpa using h2
    · exact absurd (by field_simp; linear_combination huv) (h (u / v))

/-- The map sending an unordered pair of roots `s(r, s)` to the coefficient pair `(rs, r + s)`
of the monic quadratic `X² − (r+s)X + rs`. -/
def rootPairMap (K : Type*) [Field K] : Sym2 K → K × K :=
  Sym2.lift ⟨fun r s => (r * s, r + s), by intro a b; simp [mul_comm, add_comm]⟩

@[simp] theorem rootPairMap_mk (r s : K) : rootPairMap K s(r, s) = (r * s, r + s) := rfl

theorem rootPairMap_injective : Function.Injective (rootPairMap K) := by
  intro z w
  induction z using Sym2.ind with
  | _ r s =>
    induction w using Sym2.ind with
    | _ r' s' =>
      intro h
      rw [rootPairMap_mk, rootPairMap_mk, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have key : (r' - r) * (r' - s) = 0 := by linear_combination h1 - r' * h2
      rcases mul_eq_zero.mp key with hk | hk
      · have hr : r' = r := sub_eq_zero.mp hk
        have hs : s' = s := by linear_combination -h2 - hr
        rw [hr, hs]
      · have hr : r' = s := sub_eq_zero.mp hk
        have hs : s' = r := by linear_combination -h2 - hr
        rw [hr, hs]
        exact Sym2.eq_swap

/-- The image of `rootPairMap` is exactly the set of pairs that are **not** anisotropic. -/
theorem exists_rootPairMap_iff (p : K × K) :
    (∃ z : Sym2 K, rootPairMap K z = p) ↔ ¬ AniForm p := by
  obtain ⟨b₀, b₁⟩ := p
  simp only [AniForm, ne_eq, not_forall, not_not]
  constructor
  · rintro ⟨z, hz⟩
    induction z using Sym2.ind with
    | _ r s =>
      rw [rootPairMap_mk, Prod.mk.injEq] at hz
      obtain ⟨h1, h2⟩ := hz
      exact ⟨r, by linear_combination r * h2 - h1⟩
  · rintro ⟨y, hy⟩
    refine ⟨s(y, b₁ - y), ?_⟩
    rw [rootPairMap_mk, Prod.mk.injEq]
    exact ⟨by linear_combination -hy, by ring⟩

theorem two_mul_choose_two (n : ℕ) : 2 * Nat.choose (n + 1) 2 = n * (n + 1) := by
  have hdvd : 2 ∣ (n + 1) * n := by
    rw [Nat.mul_comm]; exact (Nat.even_mul_succ_self n).two_dvd
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' hdvd, Nat.mul_comm]

/-- **Over every finite field some binary quadratic is anisotropic.** If none were, the injective
`rootPairMap : Sym2 K → K × K` would also be surjective, giving `q(q+1) = 2q²` for `q = #K`,
hence `q = 1` — impossible. (Concretely there are `q(q−1)/2 ≥ 1` anisotropic pairs.) -/
theorem exists_aniForm (K : Type*) [Field K] [Finite K] : ∃ p : K × K, AniForm p := by
  by_contra hcon
  have hsurj : Function.Surjective (rootPairMap K) := fun p =>
    (exists_rootPairMap_iff p).2 (fun hap => hcon ⟨p, hap⟩)
  have hcard : Nat.card (Sym2 K) = Nat.card (K × K) :=
    Nat.card_eq_of_bijective _ ⟨rootPairMap_injective, hsurj⟩
  rw [Sym2.natCard, Nat.card_prod] at hcard
  have h2 : 2 * Nat.choose (Nat.card K + 1) 2 = Nat.card K * (Nat.card K + 1) :=
    two_mul_choose_two _
  rw [hcard] at h2
  have hq : 1 < Nat.card K := Finite.one_lt_card
  nlinarith [h2, hq]

end FiniteField

/-! ## 2. The contract: an anisotropic pair over every DVR with finite residue field -/

/-- **CN-15 — `exists_anisotropic`.** Over a discrete valuation ring with finite residue field
there is a monic quadratic whose binary norm form is anisotropic mod `𝔪` — equivalently (with
the landed `typeOf_inert_of_anisotropic`) the inert type `⟨{(1,2)}⟩` is *attained* at every base,
not only at `ℤ_[p]`.

Route: pick an anisotropic pair `(b̄₀, b̄₁)` over the residue field (`exists_aniForm`), lift it
through `residue_surjective`, and read anisotropy of the lift off `aniForm_iff` after reducing
the form mod `𝔪`. -/
theorem exists_anisotropic (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] : ∃ a : Fin 2 → O, Anisotropic a := by
  obtain ⟨⟨p₀, p₁⟩, hp⟩ := exists_aniForm (ResidueField O)
  obtain ⟨b₀, hb₀⟩ := IsLocalRing.residue_surjective (R := O) p₀
  obtain ⟨b₁, hb₁⟩ := IsLocalRing.residue_surjective (R := O) p₁
  refine ⟨![b₀, b₁], ?_⟩
  intro u v huv
  have h0 : residue O (quadForm ![b₀, b₁] u v) = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 huv
  have key : (residue O u) ^ 2 - (residue O b₁) * (residue O u) * (residue O v)
      + (residue O b₀) * (residue O v) ^ 2 = 0 := by
    rw [← h0, quadForm]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_sub, map_mul, map_pow]
  rw [hb₀, hb₁] at key
  obtain ⟨hu, hv⟩ := (aniForm_iff p₀ p₁).2 hp (residue O u) (residue O v) key
  exact ⟨(Ideal.Quotient.eq_zero_iff_mem).1 hu, (Ideal.Quotient.eq_zero_iff_mem).1 hv⟩

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.exists_aniForm
#print axioms Uniformity.Density.exists_anisotropic

end AxCheck

end Uniformity.Density
