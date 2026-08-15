/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H55

/-!
# Uniformity.ChapH.H56 — the quotient identity: `L_M(λ)`'s residue is `λ`

**Chapter H, NODE H.56** (`blueprint/CHAP-H_general_induction.md` §8, the slot/lift layer). The
last of the three facts about H.54's stage lift

`stageLift' G π i a lift = Σ_{s < f₁} (lift s · π^(a − s·h)) · X^(i + e₁·s)`.

Dividing the `s`-th summand by the height-`M` normalizer `n(M) = x^i π^a` leaves
`λ̃_s · (x^{e₁} π^{−h})^s`, whose residue at `θ` is `λ_s · η^s`; summing over `s < f₁` and using
H.53's independence of `1, η, …, η^{f₁−1}` gives residue `λ`, with no cancellation. This file
supplies the algebraic half of that sentence — the part that needs no carrier:

`π^(s·h) · (λ̃_s π^(a − s·h) · x^(i + e₁ s)) = (π^a x^i) · (λ̃_s · x^(e₁ s))`.

DEPENDS: H.54 (`stageLift'`, whose summand this is), H.55 (`stageLift_integral`, which supplies
the hypothesis `s·h ≤ a` at the height-`M` exponents) · mathlib `Polynomial.C_mul`, `pow_add`,
`Nat.add_sub_cancel'`.

SOURCE: `EFF.GENHN.81`'s PROOF, verbatim: *"Dividing by `n(M)=x^iπ^a` leaves residue
`λ_s η^s`; GENHN-2's independence gives their sum `λ`, with no cancellation."*; the spec's audit:
*"Dividing `x^{i+e₁s}π^{a−sh}` by `n(M) = x^iπ^a` gives `x^{e₁s}π^{−sh} = (x^{e₁}π^{−h})^s`, whose
residue at `θ` is `η^s` ✓"*.

**⚠ WHY THE STATEMENT IS CLEARED OF DENOMINATORS** (blueprint's note, carried forward).
`x^{e₁}π^{−h}` is not in `O[x]`; the corpus works in `L`/`O_L` (ERRATUM E3, honesty item
H-5(3)). Chapter H states the identity **multiplied through by `π^{s h}`**, which is an identity
in `Polynomial O` and needs no carrier at all. The step from this identity to *"the residue is
`η^s`"* needs `η := res(θ^{e₁} π^{−h})`, i.e. the carrier — and that step is a hypothesis of the
consuming statement, not a node. So nothing here is weakened: the cleared form is the whole
content that lives over the ambient ring, and the uncleared form is not a statement about
`Polynomial O`.

**⚠ WHAT THE HYPOTHESIS `hsa` IS DOING, AND WHY IT IS NOT `M`-INDEXED.** `stageLift'` takes `i`
and `a` as arguments (H.54's ⚠ SIGNATURE NOTE), so this node cannot mention `M`; the single
arithmetic input it needs is that the `π`-exponent `a − s·h` is honest, i.e. `s·h ≤ a`. At the
height-`M` exponents that is exactly `stageLift_integral` (H.55), and the last section of this
file records the composite — the identity with `hsa` discharged from `i < e₁`, `s < f₁`,
`i·h + e₁·a = M`, `keyDeg·h < M` — as an `example`, so the two nodes are visibly the two halves
of one sentence. With `hsa` FALSE the cleared identity fails: `ℕ`-truncation collapses
`a − s·h` to `0` and the left side loses the factor `π^(a − s·h)` it is supposed to carry.

**⚠ EXTERNAL-QUARRY NOTE (relayed 2026-08-15, `docs/VENDOR_QUARRY_MAP_2026-08-15.md`)**
(blueprint). The survey confirms four-way absence of Newton-polygon, MacLane/key-polynomial and
Okutsu–Montes API in our mathlib pin and in all four vendored quarries, so no node of §8 may be
labelled `quarry:` — every one is `fresh`, this one included.

TEETH: as H.55 — **PROOF-ONLY** (`EFF.GENHN.81`), with `hetowr1_supp.py`'s three `η ≠ 1` frames
as foreign evidence → **Lean theorem** (this file), at every commutative ring `O`, every `π`, and
every genre datum at once.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.56, the quotient identity.** The `s`-th summand of `L_M(λ)` equals the normalizer
`x^i π^a` times `(x^{e₁} π^{−h})^s` times the lifted coefficient, in the cleared form

`π^{s h} · (c · π^{a − s h} · x^{i + e₁ s}) = (π^a x^i) · (c · x^{e₁ s})`,

an identity in `Polynomial O` (no denominators, no carrier). The scalar content is
`π^{s h} · π^{a − s h} = π^a`, which is where `hsa : s·h ≤ a` (H.55) enters; the `X`-content is
`X^{i + e₁ s} = X^i · X^{e₁ s}`. -/
theorem stageLift_summand_eq {O : Type*} [CommRing O] (G : GenreDatum) (π : O)
    {i a s : ℕ} (hsa : s * G.h ≤ a) (c : O) :
    (Polynomial.C (π ^ (s * G.h)) : Polynomial O) *
        (Polynomial.C (c * π ^ (a - s * G.h)) * Polynomial.X ^ (i + G.e₁ * s))
      = (Polynomial.C (π ^ a) * Polynomial.X ^ i) *
        (Polynomial.C c * Polynomial.X ^ (G.e₁ * s)) := by
  -- The only arithmetic input: the two `π`-exponents recombine to `a` because `s·h ≤ a`.
  have hpow : π ^ (s * G.h) * π ^ (a - s * G.h) = π ^ a := by
    rw [← pow_add, Nat.add_sub_cancel' hsa]
  rw [← hpow]
  simp only [Polynomial.C_mul, pow_add]
  ring

end Uniformity.Density.Induction

/-! ## The composite with H.55, and the `f₁ = 2` whole-lift reading

Two `example`s, not declarations: H.56's signed contract is the single theorem above. The first
discharges `hsa` at the height-`M` exponents through H.55, which is the form every consumer
actually meets; the second multiplies the identity up to the whole lift at `f₁ = 2`, where the
cleared factorization exhibits the residue polynomial `λ₀ + λ₁·η` in the variable
`η = x^{e₁} π^{−h}` — the shape `EFF.GENH4.19`(F) writes out. -/

section Consumers

open Uniformity.Density.Induction

/-- The identity as consumers meet it: at the height-`M` exponents (`i < e₁`, `i·h + e₁·a = M`,
`keyDeg·h < M`) the integrality hypothesis is H.55's `stageLift_integral`, so the quotient
identity holds for every summand index `s < f₁` with no side condition left over. -/
example {O : Type*} [CommRing O] (G : GenreDatum) (π : O) {i a M s : ℕ} (hi : i < G.e₁)
    (hs : s < G.f₁) (hM : i * G.h + G.e₁ * a = M) (hbig : G.keyDeg * G.h < M) (c : O) :
    (Polynomial.C (π ^ (s * G.h)) : Polynomial O) *
        (Polynomial.C (c * π ^ (a - s * G.h)) * Polynomial.X ^ (i + G.e₁ * s))
      = (Polynomial.C (π ^ a) * Polynomial.X ^ i) *
        (Polynomial.C c * Polynomial.X ^ (G.e₁ * s)) :=
  stageLift_summand_eq G π (stageLift_integral G hi hs hM hbig) c

/-- The whole-lift reading at `f₁ = 2`: clearing by `π^h` factors `L_M(λ)` as the normalizer
`x^i π^a` times `λ̃₀ π^h + λ̃₁ x^{e₁}`, i.e. times `π^h · (λ̃₀ + λ̃₁ · (x^{e₁} π^{−h}))` — the
residue polynomial `λ₀ + λ₁ η` with its denominator cleared. -/
example {O : Type*} [CommRing O] (G : GenreDatum) (π : O) (i a : ℕ) (lift : ℕ → O)
    (hf : G.f₁ = 2) (hha : G.h ≤ a) :
    Polynomial.C (π ^ G.h) * stageLift' G π i a lift
      = (Polynomial.C (π ^ a) * Polynomial.X ^ i) *
        (Polynomial.C (lift 0 * π ^ G.h) + Polynomial.C (lift 1) * Polynomial.X ^ G.e₁) := by
  have hone : (1 : ℕ) * G.h ≤ a := by simpa using hha
  have hsummand := stageLift_summand_eq (i := i) G π hone (lift 1)
  rw [stageLift', hf, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.sub_zero, mul_one,
    Nat.one_mul] at hsummand ⊢
  rw [mul_add, hsummand]
  simp only [Polynomial.C_mul]
  ring

end Consumers

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.stageLift_summand_eq

end AxCheck
