/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.L3

/-!
# LeanUrat.L3Gauss — The Gauss / necklace count `d · N_d(Q) = ∑_{e∣d} μ(e) Q^{d/e}`

This file proves `L3.gauss_necklace_count` (stated, `sorry`-flagged, in `LeanUrat.L3`):
over a finite field `F_Q`, the number `N_d(Q)` of monic irreducible polynomials of degree
`d ≥ 1` satisfies
```
    d · N_d(Q) = ∑_{e ∣ d} μ(e) · Q^{d/e}    (in ℚ).
```

## Proof outline (`notes/L3_proof.md §2.1`, Theorem B)

1. **Physics lemma** (`sum_e_mul_card_eq_pow`): `∑_{e ∣ d} e · N_e(Q) = Q^d`. Every element of the
   degree-`d` extension `F_{Q^d}` is a root of a unique monic irreducible over `F_Q` of degree
   dividing `d`, and each monic irreducible of degree `e ∣ d` contributes `e` distinct roots in
   `F_{Q^d}`; counting `|F_{Q^d}| = Q^d` gives the identity.

2. **Möbius inversion** (`gauss_necklace_count`): apply
   `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` with `f e = e · N_e(Q)` and `g d = Q^d` to
   invert step 1.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.L3Gauss

open Polynomial Finset
open scoped IntermediateField

/-! ## 1. Möbius inversion of the physics identity

We first record the purely arithmetic step: Möbius inversion turns
`∑_{e∣d} e·N_e = Q^d` into `d·N_d = ∑_{e∣d} μ(e)·Q^{d/e}`. This is independent of any finite-field
input and is fully proved. -/

/-- **Möbius-inversion step (fully proved).** If the "physics" identity
`∑_{e ∣ n} e · N_e = Q^n` holds for every `n ≥ 1` (with `N : ℕ → ℚ`, `Q : ℚ`), then for every
`d ≥ 1`,
```
    d · N_d = ∑_{e ∣ d} μ(e) · Q^{d/e}.
```
This is `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` over `ℚ`, with `f e = e·N_e`,
`g n = Q^n`, followed by rewriting `divisorsAntidiagonal` as a sum over divisors via
`Nat.map_div_right_divisors`. -/
theorem moebius_inversion_step (N : ℕ → ℚ) (Q : ℚ)
    (hphys : ∀ n, 1 ≤ n → ∑ e ∈ n.divisors, N e * (e : ℚ) = Q ^ n)
    (d : ℕ) (hd : 1 ≤ d) :
    (d : ℚ) * N d = ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℚ) * Q ^ (d / e) := by
  classical
  -- Apply Möbius inversion (ring version) with `f e = N e · e`, `g n = Q^n`.
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℚ)
      (f := fun e => N e * (e : ℚ)) (g := fun n => Q ^ n)).mp (fun n hn => hphys n hn) d hd
  -- `hinv : ∑ x ∈ d.divisorsAntidiagonal, (μ x.fst : ℚ) * Q ^ x.snd = N d * ↑d`.
  -- Convert the antidiagonal sum to a sum over divisors via `map_div_right_divisors` (`e ↦ (e, d/e)`).
  rw [mul_comm, ← hinv, ← Nat.map_div_right_divisors, Finset.sum_map]
  rfl

/-! ## 2. The physics identity `∑_{e∣d} e·N_e = Q^d`

This is the genuine finite-field content. Let `L = F_{Q^d}` be the degree-`d` extension of `F`.
Every `x ∈ L` has a monic irreducible minimal polynomial `minpoly F x` over `F`, whose degree
divides `d`. Partitioning `L` by `x ↦ minpoly F x` and using that each monic irreducible `f` of
degree `e ∣ d` has **exactly `e` roots in `L`** (it is separable — finite fields are perfect — and
splits in `L`), we get `Q^d = #L = ∑_f deg f = ∑_{e∣d} e · N_e`. -/

section Physics

variable {F : Type*} [Field F] [Finite F]

open scoped Classical in
/-- **Backward inclusion: a monic irreducible of degree `e ∣ d` has a root in `F_{Q^d}`.**
Given a monic irreducible `f` over `F` with `f.natDegree ∣ d` and `d ≥ 1`, and any finite field
extension `L/F` of degree `d`, there is a root of `f` in `L`. Proof: `AdjoinRoot f` is a degree-`e`
field extension of `F` with `e = f.natDegree`; since `e ∣ d = finrank F L`, there is an
`F`-algebra map `AdjoinRoot f →ₐ[F] L`, and the image of the canonical root is a root of `f`. -/
theorem exists_aeval_eq_zero_of_natDegree_dvd
    {L : Type*} [Field L] [Algebra F L] [Finite L] {f : F[X]}
    (hf : Irreducible f) (_hmonic : f.Monic)
    (hdvd : f.natDegree ∣ Module.finrank F L) :
    ∃ x : L, aeval x f = 0 := by
  haveI : Fact (Irreducible f) := ⟨hf⟩
  -- `AdjoinRoot f` is a field of degree `f.natDegree` over `F`.
  have hfin : Module.finrank F (AdjoinRoot f) = f.natDegree :=
    (AdjoinRoot.powerBasis hf.ne_zero).finrank.trans (AdjoinRoot.powerBasis_dim hf.ne_zero)
  -- The degree divides `finrank F L`, so there is an `F`-algebra hom into `L`.
  have hdvd' : Module.finrank F (AdjoinRoot f) ∣ Module.finrank F L := by rw [hfin]; exact hdvd
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := F) (K := AdjoinRoot f) (L := L) hdvd'
  refine ⟨φ (AdjoinRoot.root f), ?_⟩
  -- `aeval (φ (root f)) f = φ (aeval (root f) f) = φ 0 = 0`.
  have hroot : (Polynomial.aeval (AdjoinRoot.root f) f) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [Polynomial.aeval_algHom_apply φ (AdjoinRoot.root f) f, hroot, map_zero]

/-- The minimal polynomial over `F` of an element `x` of a finite extension `L` is monic
irreducible of degree dividing `finrank F L`. -/
theorem minpoly_monic_irreducible_natDegree_dvd
    {L : Type*} [Field L] [Algebra F L] [Finite L] (x : L) :
    Irreducible (minpoly F x) ∧ (minpoly F x).Monic ∧
      (minpoly F x).natDegree ∣ Module.finrank F L := by
  have hint : IsIntegral F x := IsIntegral.of_finite F x
  refine ⟨minpoly.irreducible hint, minpoly.monic hint, ?_⟩
  -- `natDegree (minpoly F x) = finrank F F⟮x⟯ ∣ finrank F L` by the tower law.
  rw [(IntermediateField.adjoin.finrank hint).symm]
  exact ⟨Module.finrank F⟮x⟯ L, (Module.finrank_mul_finrank F F⟮x⟯ L).symm⟩

/-- For a monic irreducible `f` over `F` and a finite extension `L`, the elements `x : L` with
`minpoly F x = f` are exactly the roots of `f` in `L`: the fiber set equals `f.rootSet L`. -/
theorem minpoly_fiber_eq_rootSet
    {L : Type*} [Field L] [Algebra F L] [Finite L] {f : F[X]}
    (hf : Irreducible f) (hmonic : f.Monic) :
    {x : L | minpoly F x = f} = f.rootSet L := by
  haveI : Module.Finite F L := inferInstance
  ext x
  simp only [Set.mem_setOf_eq, Polynomial.mem_rootSet, hf.ne_zero, ne_eq, not_false_eq_true,
    true_and]
  constructor
  · intro h
    -- `minpoly F x = f` ⇒ `aeval x f = aeval x (minpoly F x) = 0`.
    rw [← h]; exact minpoly.aeval F x
  · intro h
    -- `aeval x f = 0`, `f` monic irreducible ⇒ `f = minpoly F x`.
    exact (minpoly.eq_of_irreducible_of_monic hf h hmonic).symm

/-- **Each monic irreducible of degree `e ∣ d = finrank F L` has exactly `e` roots in `L`.**
Combining separability (finite fields are perfect, so every irreducible is separable) with the fact
that `L/F` is Galois (hence normal, so `minpoly` of any element splits in `L`) and the backward
inclusion (`f` has a root in `L`, whence `f = minpoly F (that root)` splits in `L`). -/
theorem card_rootSet_eq_of_natDegree_dvd
    {L : Type*} [Field L] [Algebra F L] [Finite L] {f : F[X]}
    (hf : Irreducible f) (hmonic : f.Monic) (hdvd : f.natDegree ∣ Module.finrank F L) :
    Nat.card (f.rootSet L) = f.natDegree := by
  classical
  haveI : Fintype L := Fintype.ofFinite L
  -- `f` is separable (irreducible over the perfect field `F`) and splits in `L`: it has a root
  -- `x₀ ∈ L`, and `f = minpoly F x₀`, which splits since `L/F` is normal.
  obtain ⟨x₀, hx₀⟩ := exists_aeval_eq_zero_of_natDegree_dvd hf hmonic hdvd
  have hsplit : Splits (f.map (algebraMap F L)) := by
    rw [minpoly.eq_of_irreducible_of_monic hf hx₀ hmonic]; exact Normal.splits inferInstance x₀
  rw [Nat.card_eq_fintype_card]
  exact Polynomial.card_rootSet_eq_natDegree (PerfectField.separable_of_irreducible hf) hsplit

/-- **The physics identity** `∑_{e ∣ d} e · N_e(Q) = Q^d` over a finite field `F` with
`Q = Nat.card F`, `d ≥ 1`. Here `N_e = Nat.card (monicIrreducibleDegree F e)`.

Proof: with `L = F_{Q^d}`, fiber `L` over the monic irreducible `minpoly F · : L → F[X]`. The image
is exactly the set of monic irreducibles of degree dividing `d` (forward: minpolys divide `d`;
backward: each such irreducible has a root in `L`, so is a minpoly). Each fiber over `g` has
`g.natDegree` elements (= roots of `g` in `L`), so `Q^d = #L = ∑_{g ∈ image} g.natDegree`. Regrouping
by `g.natDegree = e` over `d.divisors` gives `∑_{e∣d} e · N_e`. -/
theorem sum_e_mul_card_eq_pow (d : ℕ) (hd : 1 ≤ d) :
    ∑ e ∈ d.divisors, e * Nat.card (L3.monicIrreducibleDegree F e)
      = Nat.card F ^ d := by
  classical
  -- Set up the degree-`d` extension `L`.
  obtain ⟨p, _⟩ := CharP.exists F
  haveI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  haveI : NeZero d := ⟨Nat.one_le_iff_ne_zero.mp hd⟩
  set L := FiniteField.Extension F p d with hL
  haveI : Fintype L := Fintype.ofFinite L
  have hcardL : Fintype.card L = Nat.card F ^ d := by
    rw [Fintype.card_eq_nat_card]; exact FiniteField.natCard_extension F p d
  have hfinrankL : Module.finrank F L = d := FiniteField.finrank_extension F p d
  -- Each `x : L` has monic-irreducible minpoly of degree dividing `d`.
  have hmin : ∀ x : L, Irreducible (minpoly F x) ∧ (minpoly F x).Monic ∧
      (minpoly F x).natDegree ∣ d := by
    intro x
    have := minpoly_monic_irreducible_natDegree_dvd (F := F) x
    rwa [hfinrankL] at this
  -- The image finset of `minpoly F` over `L`.
  set I : Finset F[X] := Finset.univ.image (fun x : L => minpoly F x) with hI
  -- `minpoly F` maps `univ` into `I`.
  have hmaps : (↑(Finset.univ : Finset L) : Set L).MapsTo (fun x => minpoly F x) (↑I) := by
    intro x _; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ x))
  -- Step 1: `Q^d = #L = ∑_{g ∈ I} #(fiber g)` and each fiber has card `g.natDegree`.
  have hfiber : ∀ g ∈ I, #{x ∈ (Finset.univ : Finset L) | minpoly F x = g} = g.natDegree := by
    intro g hg
    obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.mp hg
    have hgi := hmin x₀
    -- The fiber finset (over `univ`) equals the root set of `g = minpoly F x₀`.
    have hset : ((Finset.univ : Finset L).filter (fun x => minpoly F x = minpoly F x₀) : Set L)
        = (minpoly F x₀).rootSet L := by
      ext y
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      have := minpoly_fiber_eq_rootSet (F := F) (L := L) hgi.1 hgi.2.1
      rw [Set.ext_iff] at this
      simpa using this y
    -- Transport cardinalities: `#filter = ncard(↑filter) = ncard(rootSet) = Nat.card rootSet`.
    have hcard := card_rootSet_eq_of_natDegree_dvd (F := F) (L := L) hgi.1 hgi.2.1
      (by rw [hfinrankL]; exact hgi.2.2)
    rw [← hcard, Nat.card_coe_set_eq, ← hset, Set.ncard_coe_finset]
  have hstep1 : Nat.card F ^ d = ∑ g ∈ I, g.natDegree := by
    rw [← hcardL, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps]
    exact Finset.sum_congr rfl hfiber
  -- Step 2: regroup `∑_{g ∈ I} g.natDegree` by `g.natDegree` over `d.divisors`.
  -- `minpoly`-image degrees land in `d.divisors`.
  have hmaps2 : ∀ g ∈ I, g.natDegree ∈ d.divisors := by
    intro g hg
    obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.mp hg
    have hgi := hmin x₀
    exact Nat.mem_divisors.mpr ⟨hgi.2.2, Nat.one_le_iff_ne_zero.mp hd⟩
  have hstep2 : ∑ g ∈ I, g.natDegree
      = ∑ e ∈ d.divisors, e * Nat.card (L3.monicIrreducibleDegree F e) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps2 (fun g => g.natDegree)]
    refine Finset.sum_congr rfl ?_
    intro e he
    -- Inner sum: `∑_{g ∈ I | g.natDegree = e} g.natDegree = (#filter) * e = N_e * e`.
    rw [Finset.sum_congr rfl (fun g hg => (Finset.mem_filter.mp hg).2)]
    rw [Finset.sum_const, smul_eq_mul]
    -- `#{g ∈ I | g.natDegree = e} = N_e`. The filtered image is exactly `monicIrreducibleDegree F e`.
    have hcardfilter : #{g ∈ I | g.natDegree = e} = Nat.card (L3.monicIrreducibleDegree F e) := by
      have hsetfilter : ((I.filter (fun g => g.natDegree = e)) : Set F[X])
          = L3.monicIrreducibleDegree F e := by
        ext g
        simp only [Finset.coe_filter, Set.mem_setOf_eq, L3.monicIrreducibleDegree]
        constructor
        · rintro ⟨hgI, hge⟩
          obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.mp hgI
          exact ⟨(hmin x₀).1, (hmin x₀).2.1, hge⟩
        · rintro ⟨hirr, hmonic, hdeg⟩
          -- backward: `g` of degree `e ∣ d` has a root in `L`, hence is a minpoly, hence in `I`.
          have hedvd : e ∣ d := (Nat.mem_divisors.mp he).1
          have hgdvd : g.natDegree ∣ Module.finrank F L := by rw [hfinrankL, hdeg]; exact hedvd
          obtain ⟨x₀, hx₀⟩ := exists_aeval_eq_zero_of_natDegree_dvd hirr hmonic hgdvd
          have : g = minpoly F x₀ := minpoly.eq_of_irreducible_of_monic hirr hx₀ hmonic
          refine ⟨?_, hdeg⟩
          rw [this]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x₀)
      rw [← Set.ncard_coe_finset, hsetfilter, ← Nat.card_coe_set_eq]
    rw [hcardfilter, mul_comm]
  rw [hstep1, hstep2]

end Physics

/-! ## 3. The Gauss / necklace count (target theorem)

We assemble the physics identity and Möbius inversion into the exact statement of
`LeanUrat.L3.gauss_necklace_count`. -/

/-- **Theorem B (Gauss / necklace count).** Over `F_Q`, for `d ≥ 1`,
`d · N_d(Q) = ∑_{e ∣ d} μ(e) · Q^{d/e}` in `ℚ`, where `N_d = Nat.card (monicIrreducibleDegree F d)`.
This is the statement of `LeanUrat.L3.gauss_necklace_count`, here proved sorry-free. -/
theorem gauss_necklace_count
    (F : Type*) [Field F] [Finite F] (d : ℕ) (hd : 1 ≤ d) :
    (d : ℚ) * (Nat.card (L3.monicIrreducibleDegree F d) : ℚ)
      = ∑ e ∈ d.divisors,
          ((ArithmeticFunction.moebius e : ℤ) : ℚ) * (Nat.card F : ℚ) ^ (d / e) := by
  -- Apply Möbius inversion with `N e := (Nat.card (monicIrreducibleDegree F e) : ℚ)`, `Q := Nat.card F`.
  refine moebius_inversion_step
    (fun e => (Nat.card (L3.monicIrreducibleDegree F e) : ℚ)) (Nat.card F : ℚ) ?_ d hd
  intro n hn
  -- The physics identity `∑_{e∣n} e·N_e = Q^n`, cast to `ℚ`.
  have hcast := congrArg (Nat.cast : ℕ → ℚ) (sum_e_mul_card_eq_pow (F := F) n hn)
  rw [Nat.cast_sum, Nat.cast_pow] at hcast
  rw [← hcast]
  exact Finset.sum_congr rfl fun e _ => by rw [Nat.cast_mul, mul_comm]

end LeanUrat.L3Gauss
