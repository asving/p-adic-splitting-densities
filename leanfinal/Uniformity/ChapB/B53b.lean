/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B36
import Uniformity.ChapB.B49

/-!
# Uniformity.ChapB.B53b — the key's order is a DVR, and the slot-lemma valuation

**Chapter B, NODE B.53, part (b) of the mandated 3-way split**
(`blueprint/CHAP-B_leaf_layer.md` §7). The blueprint's steps 2 and 3.

Two declarations:

* `keyIsDomain` — `AdjoinRoot φ` is a domain for an order-1 key `φ`. (`φ` is irreducible in
  `O[X]` because it is monic with irreducible reduction; `O[X]` is a UFD, so irreducible is
  prime, so `(φ)` is prime.) This is the instance the Quarry's DVR theorem needs and typeclass
  synthesis cannot find; **apply it explicitly** (`haveI := keyIsDomain hφ`).
* `span_mk_eq_span_algebraMap_pow` — **the slot lemma doing its real work.** For `h₀` of degree
  below `φ`'s, nonzero, with `gaussVal h₀ = c`,

  ```
  Ideal.span {AdjoinRoot.mk φ h₀}  =  Ideal.span {algebraMap O (AdjoinRoot φ) (π ^ c)}
  ```

  in `AdjoinRoot φ`: the class of `h₀` is `π ^ c` times a **unit**.

## The route

`AdjoinRoot φ` is a discrete valuation ring, *unramified* over `O`, by the Quarry backport
`AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue` (monic `φ` with irreducible
reduction, positive degree); the same theorem returns `𝔪_O · AdjoinRoot φ` maximal, so

```
maximalIdeal (AdjoinRoot φ) = (maximalIdeal O).map (algebraMap O (AdjoinRoot φ))
                            = Ideal.span {algebraMap O (AdjoinRoot φ) π},
```

i.e. `π` is a uniformizer upstairs too. Then, writing `h₀ = C (π ^ c) * b` (possible because
`gaussVal h₀ = c` makes `π ^ c` divide every coefficient — `Polynomial.C_dvd_iff_dvd_coeff`):

* `b`'s class in `AdjoinRoot φ` is a **unit**. If it were not, it would lie in the maximal
  ideal, i.e. `b ≡ C π * Y (mod φ)` for some `Y`; reducing that congruence mod `𝔪` (where
  `C π ↦ 0`) gives `φ̄ ∣ b̄`. But `b̄ = digPoly π c h₀` (B.24's `digPoly_eq_map`), so
  `AdjoinRoot.mk φ̄ b̄ = resMk π φ c h₀`, which B.36's `resMk_ne_zero` says is **nonzero** —
  exactly `EFF.HE6.15`'s "EXACTLY", i.e. the digit at the polygon's own height does not vanish.
  Contradiction.
* Hence `mk φ h₀ = algebraMap O (AdjoinRoot φ) (π ^ c) * (unit)`, and the two principal ideals
  agree (`Ideal.span_singleton_mul_right_unit`).

**Why the statement is phrased with `Ideal.span` and not with `maximalIdeal`.** Neither
`IsLocalRing (AdjoinRoot φ)` nor `IsDomain (AdjoinRoot φ)` is available to typeclass synthesis
at the point of statement (both are theorems here, keyed on the explicit non-class hypothesis
`hφ : IsKey φ` — the same B-D3 situation as B.25's `instFieldResField` and B.49's
`instLocalRingAdjoinRoot`). A statement mentioning `maximalIdeal (AdjoinRoot φ)` would therefore
not even elaborate. The `Ideal.span` form is instance-free and is what B53c consumes.

DEPENDS: B.01 (`IsKey`) · B.08 (`le_gaussVal_iff`) · B.23/B.24 (`digPoly`, `digPoly_eq_map`) ·
B.25 (`resMk`) · B.36 (`resMk_ne_zero`) · B.49 (imported for the Quarry backport
`Uniformity/Quarry/AdjoinRootDVR.lean`) · mathlib `Monic.irreducible_of_irreducible_map`,
`UniqueFactorizationMonoid.irreducible_iff_prime`, `Ideal.span_singleton_prime`,
`Ideal.Quotient.isDomain_iff_prime`, the Quarry's
`AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue`,
`IsLocalRing.eq_maximalIdeal`, `Irreducible.maximalIdeal_eq`, `Polynomial.C_dvd_iff_dvd_coeff`,
`Ideal.span_singleton_mul_right_unit`.

## Faithfulness

`EFF.HE6.15`'s exactness clause at `e₁ = 1` (through B.36) plus the classical fact that an
unramified monogenic extension of a DVR is a DVR with the same uniformizer. The corpus's
`dv(B₀)` (`EFF.HE3.20`) is `gaussVal (dev φ g 0)`; this file is the statement that the ideal it
measures is literally `π ^ dv(B₀)` upstairs.

SOURCE: `EFF.HE3.20`; `EFF.HE6.15`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A′ + the Quarry's DVR arena; `hπ : Irreducible π` is carried per signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **B.53, step 2 (a) — the key's order is a domain.** `φ` is monic with irreducible
reduction, hence irreducible in `O[X]`, hence prime (`O[X]` is a UFD), hence `(φ)` is a prime
ideal.

Keyed on the explicit non-class hypothesis `hφ`, so it is a `theorem`, not an `instance`:
consumers write `haveI := keyIsDomain hφ`. -/
theorem keyIsDomain {φ : Polynomial O} (hφ : IsKey φ) : IsDomain (AdjoinRoot φ) :=
  (Ideal.Quotient.isDomain_iff_prime (Ideal.span {φ})).mpr
    ((Ideal.span_singleton_prime hφ.monic.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Monic.irreducible_of_irreducible_map (IsLocalRing.residue O) φ hφ.monic hφ.irred)))

/-- **B.53, steps 2–3 — the slot-lemma valuation computation.** In `AdjoinRoot φ` the class of a
polynomial `h₀` of degree below `φ`'s, nonzero, with `gaussVal h₀ = c`, generates exactly the
ideal `(π ^ c)`: it is `π ^ c` times a unit, the unit being witnessed by B.36's `resMk_ne_zero`.
**This is the slot lemma doing its real work.** -/
theorem span_mk_eq_span_algebraMap_pow (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {h₀ : Polynomial O} (hdeg : h₀.degree < φ.degree) (h0 : h₀ ≠ 0) {c : ℕ}
    (hc : gaussVal h₀ = (c : ℕ∞)) :
    Ideal.span {AdjoinRoot.mk φ h₀} = Ideal.span {algebraMap O (AdjoinRoot φ) (π ^ c)} := by
  haveI := keyIsDomain hφ
  have hdegne : φ.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hφ.monic.ne_zero]
    exact_mod_cast hφ.pos.ne'
  obtain ⟨hmax, hdvr, _hloc⟩ :=
    AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue hφ.monic hdegne hφ.irred
  haveI := hdvr
  -- `π` is a uniformizer of `AdjoinRoot φ` as well: the extension is unramified.
  have hmaxspan : maximalIdeal (AdjoinRoot φ) = Ideal.span {algebraMap O (AdjoinRoot φ) π} := by
    rw [← IsLocalRing.eq_maximalIdeal hmax, hπ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  -- `h₀ = C (π ^ c) * b`, the exact division at the polygon's height.
  obtain ⟨b, hb⟩ : Polynomial.C (π ^ c) ∣ h₀ :=
    (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr ((le_gaussVal_iff hπ).mp hc.ge)
  -- the residual class of `b` is nonzero — B.36's exactness clause
  have hres : AdjoinRoot.mk (φ.map (IsLocalRing.residue O)) (b.map (IsLocalRing.residue O))
      ≠ 0 := by
    have h1 : resMk π φ c h₀ ≠ 0 := resMk_ne_zero hπ hφ hdeg h0 hc
    rwa [resMk, digPoly_eq_map hπ hb] at h1
  -- hence the class of `b` is a unit of `AdjoinRoot φ`
  have hunit : IsUnit (AdjoinRoot.mk φ b) := by
    by_contra hnu
    have hmem : AdjoinRoot.mk φ b ∈ maximalIdeal (AdjoinRoot φ) :=
      (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [hmaxspan, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, hy⟩ := hmem
    obtain ⟨Y, rfl⟩ := AdjoinRoot.mk_surjective y
    have hzero : AdjoinRoot.mk φ (b - Polynomial.C π * Y) = 0 := by
      rw [map_sub, map_mul, hy]
      simp [AdjoinRoot.algebraMap_eq]
    obtain ⟨W, hW⟩ := AdjoinRoot.mk_eq_zero.mp hzero
    refine hres (AdjoinRoot.mk_eq_zero.mpr ⟨W.map (IsLocalRing.residue O), ?_⟩)
    have hmap := congrArg (Polynomial.map (IsLocalRing.residue O)) hW
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C] at hmap
    have hπ0 : (IsLocalRing.residue O) π = 0 := by
      have hmemO : π ∈ maximalIdeal O := hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
      rwa [← IsLocalRing.ker_residue, RingHom.mem_ker] at hmemO
    rwa [hπ0, map_zero, zero_mul, sub_zero] at hmap
  -- conclude: the two principal ideals agree
  have hfact : AdjoinRoot.mk φ h₀
      = algebraMap O (AdjoinRoot φ) (π ^ c) * AdjoinRoot.mk φ b := by
    rw [hb, map_mul]; rfl
  rw [hfact, Ideal.span_singleton_mul_right_unit hunit]

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.keyIsDomain
#print axioms Uniformity.Density.Leaf.span_mk_eq_span_algebraMap_pow
end AxCheck
