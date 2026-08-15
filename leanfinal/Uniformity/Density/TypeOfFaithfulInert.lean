/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOfFaithful
import Uniformity.Quarry.AdjoinRootDVR

/-!
# Uniformity.Density.TypeOfFaithfulInert — HYP.01, hypothesis-free, at the inert leaf

`Uniformity/Density/TypeOfFaithful.lean` proves **HYP.01 (`typeOf` faithfulness)** on the
*monogenic-maximal locus*, i.e. conditional on `[IsDiscreteValuationRing (AdjoinRoot g)]` — "the
order `O[x]/(g)` is already the maximal order". This file discharges that hypothesis on the inert
locus, using the quarry backport `AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue`
(`Uniformity/Quarry/AdjoinRootDVR.lean`, from `vendor/FLT`), and so lands the first
**hypothesis-free** instance of HYP.01:

> for `O` any DVR and `g ∈ O[X]` monic of positive degree whose reduction is irreducible over the
> residue field, the classical `(e, f)` of the prime `𝔪_O · O[x]/(g)` is `(1, deg g)` and the
> gcd-defined `typeOf g` is `⟨{(1, deg g)}⟩` — the two readings agree, and both are the
> unramified pair.

## The three ingredients, and why the combination is more than its parts

* the **classical side** is the backport: `ḡ` irreducible makes `A = O[x]/(g)` a DVR whose maximal
  ideal is `𝔪_O · A`, so `e = 1` and (by the fundamental identity of
  `Uniformity/Quarry/RamificationInertiaLocal.lean`) `f = deg g`;
* the **bridge** is `TypeOfFaithful.{inertiaDegOf_eq_inertiaDeg', ramIndexOf_eq_ramificationIdx'}`;
* the **order is maximal**: `isIntegrallyClosed_adjoinRoot_of_irreducible_map` certifies
  `IsIntegrallyClosed (AdjoinRoot g)` in Lean, so `A` *is* the integral closure of `O` in its own
  fraction field — the classical `(e, f)` computed here is the maximal order's, not a suborder's.

**Independent cross-check of the definition.** The third conjunct of `typeOf_inert_faithful`,
`typeOf g = ⟨{(1, deg g)}⟩`, is also the conclusion of the already-landed
`Uniformity.Density.typeOf_inert_of_irreducible_map` (`Density/InertLeaf.lean:179`). The two proofs
share nothing: `InertLeaf` argues from the gcd definition alone, by strong induction on the
valuation showing `deg g ∣ v(N x)` for every `x`; this file argues from mathlib's classical
ramification/inertia machinery through the fundamental identity `e · f = [A : O]`. Two decorrelated
routes to the same value of a `[CORE-SET]` definition is exactly the evidence that definition wants,
so the duplication is deliberate and is recorded rather than removed.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density

open IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A monic `g` whose reduction is irreducible over the residue field is irreducible over `O`
(`Monic.irreducible_of_irreducible_map`), hence *prime* in the unique-factorization monoid `O[X]`,
hence `AdjoinRoot g` is a domain. -/
theorem isDomain_adjoinRoot_of_irreducible_map {g : Polynomial O} (hg : g.Monic)
    (h : Irreducible (g.map (residue O))) : IsDomain (AdjoinRoot g) :=
  AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.1
      (hg.irreducible_of_irreducible_map (residue O) g h))

/-- **The inert order is the maximal order.** `A = AdjoinRoot g` is a DVR when `ḡ` is irreducible
(the quarry backport), and a DVR is integrally closed; so `A` is the integral closure of `O` in
`Frac A`, which is what licenses reading the `(e, f)` of `𝔪_A` as *the* classical pair of the
extension. -/
theorem isIntegrallyClosed_adjoinRoot_of_irreducible_map {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) (h : Irreducible (g.map (residue O))) [IsDomain (AdjoinRoot g)] :
    IsIntegrallyClosed (AdjoinRoot g) := by
  obtain ⟨-, hdvr, -⟩ := AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue hg
    (ne_of_gt (natDegree_pos_iff_degree_pos.1 hd)) h
  haveI := hdvr
  infer_instance

/-- **HYP.01 at the inert leaf, with no standing hypothesis.** For `O` any DVR (no completeness)
and `g` monic of positive degree with irreducible reduction:

* the classical ramification index of `𝔪_O · O[x]/(g)` over `O` is `1`;
* its classical inertia degree is `deg g`;
* the gcd-defined splitting type `typeOf g` is the singleton `⟨{(1, deg g)}⟩`.

The first two clauses are the *classical* reading and the third is *our* reading; together they are
faithfulness of `typeOf` at this leaf. `𝔪_O · O[x]/(g)` is the maximal ideal of `O[x]/(g)`
(backport), and `O[x]/(g)` is integrally closed
(`isIntegrallyClosed_adjoinRoot_of_irreducible_map`), so the classical pair is the *maximal
order's*. -/
theorem typeOf_inert_faithful {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree)
    (h : Irreducible (g.map (residue O))) :
    (Ideal.map (algebraMap O (AdjoinRoot g)) (maximalIdeal O)).ramificationIdx' O = 1 ∧
      (Ideal.map (algebraMap O (AdjoinRoot g)) (maximalIdeal O)).inertiaDeg' O = g.natDegree ∧
      typeOf g = ⟨{(1, g.natDegree)}⟩ := by
  haveI := isDomain_adjoinRoot_of_irreducible_map hg h
  obtain ⟨hmax, hdvr, -⟩ := AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue hg
    (ne_of_gt (natDegree_pos_iff_degree_pos.1 hd)) h
  haveI := hdvr
  -- the image of `𝔪_O` IS the maximal ideal of `A`, so the ramification index is `1`
  have hmA : Ideal.map (algebraMap O (AdjoinRoot g)) (maximalIdeal O)
      = maximalIdeal (AdjoinRoot g) := IsLocalRing.eq_maximalIdeal hmax
  have he : (maximalIdeal (AdjoinRoot g)).ramificationIdx' O = 1 :=
    ramificationIdx'_eq_of_map_maximalIdeal_eq_pow hg hd (by rw [hmA, pow_one])
  -- hence our `e` is `1` and our `f` is the whole degree
  have hr : ramIndexOf g = 1 := by rw [ramIndexOf_eq_ramificationIdx' hg hd, he]
  have hf : inertiaDegOf g = g.natDegree := by
    have := ramIndexOf_mul_inertiaDegOf hg hd
    rwa [hr, one_mul] at this
  have hirr : Irreducible g := hg.irreducible_of_irreducible_map (residue O) g h
  refine ⟨by rw [hmA, he], ?_, ?_⟩
  · rw [hmA, ← inertiaDegOf_eq_inertiaDeg' hg hd, hf]
  · rw [typeOf_eq_classical_of_isDiscreteValuationRing hg hd hirr, he,
      ← inertiaDegOf_eq_inertiaDeg' hg hd, hf]

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.isDomain_adjoinRoot_of_irreducible_map
#print axioms Uniformity.Density.isIntegrallyClosed_adjoinRoot_of_irreducible_map
#print axioms Uniformity.Density.typeOf_inert_faithful

end AxCheck

end Uniformity.Density
