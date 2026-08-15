/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B03
import Uniformity.ChapB.B50
import Uniformity.ChapB.B53a
import Uniformity.ChapB.B53b

/-!
# Uniformity.ChapB.B53c — the length count and the contract (steps 4–5 of NODE B.53)

**Chapter B, NODE B.53, part (c) of the mandated 3-way split**
(`blueprint/CHAP-B_leaf_layer.md` §7), ENV-C. This file carries the node's single signed
declaration.

*The norm of the key's value.* For an order-1 key `φ`, `g` monic of positive degree with
`φ ∤ g` (equivalently `dev φ g 0 ≠ 0`), and `α := AdjoinRoot.root g`,

```
addVal O (Algebra.norm O (φ(α)))  =  φ.natDegree * gaussVal (dev φ g 0),
```

read in `ℕ∞`.

Two declarations:

* `length_quot_eq_addVal_norm` — the determinant–length dictionary, extracted from B.51's proof
  as a reusable statement: for `A` free and module-finite over `O` of positive rank and `z : A`
  of nonzero norm, `Module.length O (A ⧸ (z)) = addVal O (Algebra.norm O z)`. B.50's
  elementary-divisor decomposition `A ⧸ zA ≃ₗ[O] ⨁ᵢ O ⧸ (π ^ eᵢ)` with
  `addVal (norm z) = Σᵢ eᵢ` gives it in three rewrites (each block has length `eᵢ` by
  `IsDiscreteValuationRing.length_quotient_pow_maximalIdeal`).
* `addVal_norm_key_eval` — the node's contract.

## The route

Write `c := gaussVal (dev φ g 0)` (a natural number, since `dev φ g 0 ≠ 0`), `m := φ.natDegree`,
`n := g.natDegree`, `A := AdjoinRoot g`, `B := AdjoinRoot φ`, `z := φ(α) = AdjoinRoot.mk g φ`.

1. **The ideal on the `B` side** (B53b): `(g(θ)) = ((dev φ g 0)(θ)) = (π ^ c)` in `B`.
2. **The norm is nonzero.** Transport `π ^ c ∈ ((dev φ g 0)(θ))` through B53a's `O`-algebra
   equivalence `A ⧸ (z) ≃ₐ[O] B ⧸ ((dev φ g 0)(θ))`: the equivalence is injective and commutes
   with `algebraMap`, so the class of `algebraMap O A (π ^ c)` vanishes too, i.e.
   `algebraMap O A (π ^ c) = z * w` for some `w`. Taking norms,
   `(π ^ c) ^ n = Algebra.norm O z * Algebra.norm O w`, and the left side is nonzero, so
   `Algebra.norm O z ≠ 0`. **This is the only role of `hd : 0 < g.natDegree` beyond positivity
   of the rank** — a nonzero norm is exactly what B.50 needs, and there is no domain hypothesis
   on `A` anywhere (`AdjoinRoot g` need not be one).
3. **The length chain.**
   ```
   addVal (norm z) = length_O (A ⧸ (z))                    (step 5, the dictionary)
                   = length_O (B ⧸ ((dev φ g 0)(θ)))       (B53a, an O-linear equivalence)
                   = length_O (B ⧸ (π ^ c))                (step 1)
                   = addVal (norm (algebraMap O B (π ^ c)))(the dictionary again)
                   = addVal ((π ^ c) ^ m) = m * c.         (`Algebra.norm_algebraMap`, rank `m`)
   ```
   Steps 4 and 5 of the blueprint are the last two lines and the first line respectively; the
   blueprint's "free of rank `m` over `O ⧸ π^c`, so its `O`-length is `m·c`" is replaced by the
   second application of the dictionary, which is shorter and reuses B.50 verbatim.

DEPENDS: B.01 (`IsKey`) · B.02 (`dev`) · B.03 (`degree_dev_lt`) · B.07/B.08 (`gaussVal`,
`gaussVal_eq_top_iff`) · B.50 (`exists_smith_of_norm`) · B53a (`quotKeyEquiv`) ·
B53b (`span_mk_eq_span_algebraMap_pow`) · mathlib `AdjoinRoot.powerBasis'`,
`AdjoinRoot.aeval_eq`, `Algebra.norm_algebraMap`, `Ideal.Quotient.eq_zero_iff_mem`,
`Ideal.quotientEquivAlgOfEq`, `LinearEquiv.length_eq`, `Module.length_pi_of_fintype`,
`IsDiscreteValuationRing.length_quotient_pow_maximalIdeal`, `Irreducible.addVal_pow`.

## ⚠ This node is the chapter's replacement for `LEMMA HE3-1`

`EFF.HE3.20` states the corpus's version as a **resultant identity**
`Σ_ρ dv(Φ″(ρ)) = D′ · dv(B₀)` — a sum over roots in `K̄₀`. This node is the same identity with
the roots replaced by a length and the resultant by a norm: at `e₁ = 1`, `dv = addVal`,
`D′ = m`, `B₀ = dev φ g 0`, and `Σ_ρ dv(φ(ρ)) = addVal (norm (φ(α)))`. **The correspondence is
exact and it is §14 item 7.** Concretely, the root-sum and the length agree because both compute
the `O`-colength of the ideal `(g, φ) ⊆ O[X]`, which is what B53a's `sup_comm` step makes
manifest; no separating field, no `K̄₀`, and no `Galois` input is used. **Flagged for human
review** (the corpus-to-Lean correspondence, not the Lean proof).

## `hres` is NOT among the hypotheses

The blueprint records at B.53 that its `hres` companion (B.54/B.55's
`g.map (residue O) = (φ.map (residue O)) ^ k`) is over-strong and is retained only to share
hypotheses at B.55. The signed B.53 above does **not** carry it, and the proof does not want it:
`AdjoinRoot g` is never asked to be local, and `AdjoinRoot φ`'s DVR structure (B53b) comes from
`hφ : IsKey φ` alone. What the proof does need and the blueprint's step 2 phrased through B.49
is only the *key's* order `AdjoinRoot φ`, at `k = 1`.

## Faithfulness

`EFF.HE3.20` (`LEMMA HE3-1`); `EFF.HE3.22` (`LEMMA HE3-1′`, the support-function form of the
same quantity, `dv(B₀) = min_j (dv(A_j) + jκ)` — that is B.14's `suppVal`, and it connects this
node to B.54).

SOURCE: `EFF.HE3.20`; `EFF.HE3.22`.

**TEETH.** `HE-NORM` (`EFF.HE3.50`, 72,134 identities, 0 violations, guarding `EFF.HE3.20`)
→ **Lean theorem**: the identity `LEMMA HE3-1` becomes this node. `HE-PSI` (`EFF.HE3.51`,
43,528 rows, guarding `EFF.HE3.22`) → **Lean theorem** at B.54, not here.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A′ (blueprint §0.1) for the dictionary; ENV-C is opened below for the contract.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **The determinant–length dictionary.** For `A` free and module-finite over the discrete
valuation ring `O`, of positive rank, and `z : A` of nonzero norm, the `O`-length of `A ⧸ zA`
is the valuation of the norm.

This is B.51's internal computation, exported: B.50's elementary-divisor decomposition
`A ⧸ zA ≃ₗ[O] ⨁ᵢ O ⧸ (π ^ eᵢ)` comes with `addVal (norm z) = Σᵢ eᵢ`, and each block has length
`eᵢ`. -/
theorem length_quot_eq_addVal_norm (hπ : Irreducible π) {A : Type*} [CommRing A] [Algebra O A]
    [Module.Free O A] [Module.Finite O A] (hr : 0 < Module.finrank O A)
    {z : A} (hz : Algebra.norm O z ≠ 0) :
    Module.length O (A ⧸ Ideal.span {z})
      = IsDiscreteValuationRing.addVal O (Algebra.norm O z) := by
  classical
  obtain ⟨e, ⟨eqv⟩, hsum⟩ := exists_smith_of_norm hπ hr hz
  have hpow : ∀ n : ℕ, Module.length O (O ⧸ Ideal.span {π ^ n}) = (n : ℕ∞) := by
    intro n
    rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O n
  have hlen : Module.length O (A ⧸ (Ideal.span {z}).restrictScalars O)
      = ((∑ i, e i : ℕ) : ℕ∞) := by
    rw [eqv.length_eq, (DirectSum.linearEquivFunOnFintype O _
      (fun i => O ⧸ Ideal.span {π ^ e i})).length_eq, Module.length_pi_of_fintype]
    simp only [hpow]
    rw [← Nat.cast_sum]
  -- the `Submodule`-quotient and the `Ideal`-quotient carry the same `O`-module structure
  have hlen' : Module.length O (A ⧸ Ideal.span {z}) = ((∑ i, e i : ℕ) : ℕ∞) := hlen
  rw [hlen', hsum]

section ENVC

-- ENV-C (blueprint §0.1): ENV-B plus finiteness of the residue field. Neither instance is
-- consumed below; both are kept so the binder list matches the frozen stub (the B.49
-- precedent).
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

set_option linter.unusedSectionVars false in
/-- **B.53 — the norm of the key's value.** For an order-1 key `φ` and a monic `g` of positive
degree not divisible by `φ`,
`addVal O (Algebra.norm O (φ(α))) = φ.natDegree * gaussVal (dev φ g 0)`, where
`α = AdjoinRoot.root g`.

The chapter's replacement for `LEMMA HE3-1` (`EFF.HE3.20`): the corpus's resultant/root-sum
`Σ_ρ dv(φ(ρ)) = m · dv(B₀)` with the roots replaced by an `O`-length and the resultant by a
norm. -/
theorem addVal_norm_key_eval (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree) (h0 : dev φ g 0 ≠ 0) :
    IsDiscreteValuationRing.addVal O (Algebra.norm O (Polynomial.aeval (AdjoinRoot.root g) φ))
      = (φ.natDegree : ℕ∞) * gaussVal (dev φ g 0) := by
  classical
  -- both orders are free and module-finite over `O`, of the expected ranks
  haveI : Module.Free O (AdjoinRoot g) := Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  haveI : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  haveI : Module.Free O (AdjoinRoot φ) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hφ.monic).basis
  haveI : Module.Finite O (AdjoinRoot φ) := (AdjoinRoot.powerBasis' hφ.monic).finite
  have hrkA : Module.finrank O (AdjoinRoot g) = g.natDegree := by
    rw [(AdjoinRoot.powerBasis' hg).finrank]; rfl
  have hrkB : Module.finrank O (AdjoinRoot φ) = φ.natDegree := by
    rw [(AdjoinRoot.powerBasis' hφ.monic).finrank]; rfl
  -- `c := gaussVal (dev φ g 0)` is a natural number
  obtain ⟨c, hc'⟩ := ENat.ne_top_iff_exists.1 (fun h => h0 (gaussVal_eq_top_iff.1 h))
  have hc : gaussVal (dev φ g 0) = (c : ℕ∞) := hc'.symm
  -- step 1 (B53b): the ideal generated by `(dev φ g 0)(θ)` in `AdjoinRoot φ` is `(π ^ c)`
  have hdegh : (dev φ g 0).degree < φ.degree := degree_dev_lt hφ.monic hφ.pos g 0
  have hspanB : Ideal.span {AdjoinRoot.mk φ (dev φ g 0)}
      = Ideal.span {algebraMap O (AdjoinRoot φ) (π ^ c)} :=
    span_mk_eq_span_algebraMap_pow hπ hφ hdegh h0 hc
  have hmemB : algebraMap O (AdjoinRoot φ) (π ^ c)
      ∈ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)} := by
    rw [hspanB]; exact Ideal.mem_span_singleton_self _
  -- step 2: transport the membership to `AdjoinRoot g` through B53a, and read off `norm ≠ 0`
  have hmemA : algebraMap O (AdjoinRoot g) (π ^ c) ∈ Ideal.span {AdjoinRoot.mk g φ} := by
    have h2 : algebraMap O (AdjoinRoot φ ⧸ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)}) (π ^ c)
        = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmemB
    have h3 : algebraMap O (AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.mk g φ}) (π ^ c) = 0 :=
      (quotKeyEquiv φ g).injective
        (by rw [(quotKeyEquiv φ g).commutes, h2, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hmemA
  have hnz : Algebra.norm O (AdjoinRoot.mk g φ) ≠ 0 := by
    intro hzero
    have hnn : Algebra.norm O (algebraMap O (AdjoinRoot g) (π ^ c)) = 0 := by
      rw [hw, map_mul, hzero, zero_mul]
    rw [Algebra.norm_algebraMap, hrkA] at hnn
    exact pow_ne_zero _ (pow_ne_zero _ hπ.ne_zero) hnn
  have hnzB : Algebra.norm O (algebraMap O (AdjoinRoot φ) (π ^ c)) ≠ 0 := by
    rw [Algebra.norm_algebraMap, hrkB]
    exact pow_ne_zero _ (pow_ne_zero _ hπ.ne_zero)
  have hrA : 0 < Module.finrank O (AdjoinRoot g) := by rw [hrkA]; exact hd
  have hrB : 0 < Module.finrank O (AdjoinRoot φ) := by rw [hrkB]; exact hφ.pos
  -- step 3: the length chain
  have hL1 : Module.length O (AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.mk g φ})
      = IsDiscreteValuationRing.addVal O (Algebra.norm O (AdjoinRoot.mk g φ)) :=
    length_quot_eq_addVal_norm hπ hrA hnz
  have hL2 : Module.length O (AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.mk g φ})
      = Module.length O (AdjoinRoot φ ⧸ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)}) :=
    (quotKeyEquiv φ g).toLinearEquiv.length_eq
  have hL3 : Module.length O (AdjoinRoot φ ⧸ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)})
      = Module.length O (AdjoinRoot φ ⧸ Ideal.span {algebraMap O (AdjoinRoot φ) (π ^ c)}) :=
    (Ideal.quotientEquivAlgOfEq O hspanB).toLinearEquiv.length_eq
  have hL4 : Module.length O (AdjoinRoot φ ⧸ Ideal.span {algebraMap O (AdjoinRoot φ) (π ^ c)})
      = IsDiscreteValuationRing.addVal O
          (Algebra.norm O (algebraMap O (AdjoinRoot φ) (π ^ c))) :=
    length_quot_eq_addVal_norm hπ hrB hnzB
  have hL5 : IsDiscreteValuationRing.addVal O
      (Algebra.norm O (algebraMap O (AdjoinRoot φ) (π ^ c)))
        = ((φ.natDegree * c : ℕ) : ℕ∞) := by
    rw [Algebra.norm_algebraMap, hrkB, ← pow_mul, hπ.addVal_pow, Nat.mul_comm]
  rw [AdjoinRoot.aeval_eq, ← hL1, hL2, hL3, hL4, hL5, hc]
  push_cast
  ring

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.length_quot_eq_addVal_norm
#print axioms Uniformity.Density.Leaf.addVal_norm_key_eval
end AxCheck
