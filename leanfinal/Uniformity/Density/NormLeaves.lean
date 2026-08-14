/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOf

/-!
# Uniformity.Density.NormLeaves — the norm of the root, and the Eisenstein leaf at every `n`

Two nodes of `spec/CERTAIN_NODES_2026-08-14.md`:

* **CN-19** `norm_adjoinRoot_root` — `N(α) = (−1)ⁿ·a₀` for every monic `f` over a domain.
* **CN-20** `typeOf_eisenstein` — the totally ramified leaf `⟨{(n,1)}⟩` at every degree `n`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- The two signatures below are frozen contracts (`spec/CERTAIN_NODES_2026-08-14.md`), so the
-- standing `O`-bundle is carried in full even where a weaker one would do.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## CN-19 — the norm of the root of a monic polynomial

`typeOf` is defined through `Algebra.norm` on `AdjoinRoot g` (`TypeOf.lean`, `normValues`), so
every certificate needs at least one explicitly computed norm. The universal one is the norm of
the root itself: `N(α) = (−1)ⁿ a₀`.

**The route.** Not the companion-matrix determinant (mathlib has no companion-matrix determinant
lemma), but the minimal polynomial: for `pb : PowerBasis R S` over any commutative base,
mathlib's `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly` gives
`N(pb.gen) = (−1)^pb.dim · (minpoly R pb.gen).coeff 0` — this is the `det = ± charpoly.coeff 0`
computation, done once and for all in mathlib. Applying it to `AdjoinRoot.powerBasis' hf`
(`dim = f.natDegree`, `gen = root f`) leaves exactly one gap: `minpoly O (root f) = f`, which is
NOT mathlib's `AdjoinRoot.minpoly_root` (that one is over a field). It is proved below from
`minpoly.unique'`: `f` is monic and kills the root, and no nonzero polynomial of smaller degree
kills it, because the power basis `1, α, …, α^(n-1)` is linearly independent
(`PowerBasis.dim_le_degree_of_root`). No irreducibility, no field, no completeness. -/

section Norm

variable {O : Type*} [CommRing O] [IsDomain O]

/-- **The minimal polynomial of `AdjoinRoot.root f` is `f`**, for every monic `f` over a domain
— no irreducibility and no field hypothesis. (mathlib's `AdjoinRoot.minpoly_root` is stated over
a field; this is the monic-over-a-domain version, and it is what CN-19 needs.) -/
theorem minpoly_adjoinRoot_root {f : Polynomial O} (hf : f.Monic) :
    minpoly O (AdjoinRoot.root f) = f := by
  refine (minpoly.unique' O (AdjoinRoot.root f) hf ?_ ?_).symm
  · rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · intro q hq
    refine or_iff_not_imp_left.2 (fun hq0 h0 => ?_)
    have hroot : (Polynomial.aeval ((AdjoinRoot.powerBasis' hf).gen)) q = 0 := by
      rw [AdjoinRoot.powerBasis'_gen]; exact h0
    have hdim := (AdjoinRoot.powerBasis' hf).dim_le_degree_of_root hq0 hroot
    rw [AdjoinRoot.powerBasis'_dim] at hdim
    rw [Polynomial.degree_eq_natDegree hf.ne_zero] at hq
    exact absurd hq (not_lt.2 hdim)

/-- **CN-19 — `N(α) = (−1)ⁿ · a₀`.** The norm of the root of a monic `f` of degree `n` over a
domain is `(−1)^n` times the constant coefficient. Generalizes the landed degree-2 instance
`norm_root_quad` (where the sign is `+1`). -/
theorem norm_adjoinRoot_root {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree) :
    Algebra.norm O (AdjoinRoot.root f) = (-1) ^ f.natDegree * f.coeff 0 := by
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (AdjoinRoot.powerBasis' hf)
  rwa [AdjoinRoot.powerBasis'_gen, AdjoinRoot.powerBasis'_dim, minpoly_adjoinRoot_root hf] at h

end Norm

/-! ## CN-20 — the totally ramified (Eisenstein) leaf at every degree

`f` Eisenstein at `𝔪` (all lower coefficients in `𝔪`, the constant one not in `𝔪²`) has
`typeOf f = ⟨{(n,1)}⟩`: it is irreducible (mathlib's Eisenstein criterion), and its residue
degree is `1` because CN-19 exhibits a norm of valuation exactly `1` — the norm of the root,
`(−1)ⁿ a₀`, whose valuation is `v(a₀) = 1`. Then `e = n / f = n`. This generalizes the landed
degree-2 `typeOf_ram_of_eisenstein`, whose irreducibility step was proved by hand. -/

section Eisenstein

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **CN-20 — the Eisenstein leaf.** A monic `f` of degree `n > 0` whose coefficients below the
leading one all lie in `𝔪`, with `f.coeff 0 ∉ 𝔪²`, is totally ramified: `typeOf f = ⟨{(n,1)}⟩`.
Note that `(n,1)` is `(e,f)` in the frozen order — ramification index first. -/
theorem typeOf_eisenstein {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hlow : ∀ i < f.natDegree, f.coeff i ∈ maximalIdeal O)
    (h0 : f.coeff 0 ∉ (maximalIdeal O) ^ 2) :
    typeOf f = ⟨{(f.natDegree, 1)}⟩ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  -- (1) irreducibility, from mathlib's Eisenstein criterion
  have hEis : f.IsEisensteinAt (maximalIdeal O) :=
    hf.isEisensteinAt_of_mem_of_notMem (maximalIdeal.isMaximal O).ne_top
      (fun {i} hi => hlow i hi) h0
  have hirr : Irreducible f :=
    hEis.irreducible (maximalIdeal.isMaximal O).isPrime hf.isPrimitive hd
  -- (2) `v(a₀) = 1`: `a₀ = π b` with `b` a unit, else `a₀ ∈ 𝔪²`
  have hm : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  obtain ⟨b, hb⟩ : π ∣ f.coeff 0 := by
    have := hlow 0 hd
    rwa [hm, Ideal.mem_span_singleton] at this
  have hbu : IsUnit b := by
    by_contra hbn
    refine h0 ?_
    obtain ⟨c, rfl⟩ : π ∣ b := by
      rw [← Ideal.mem_span_singleton, ← hm]
      exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hbn)
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hb]
    exact ⟨c, by ring⟩
  have hbv : IsDiscreteValuationRing.addVal O b = 0 := by
    rw [← hbu.unit_spec]; exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
  have hval : IsDiscreteValuationRing.addVal O (f.coeff 0) = 1 := by
    rw [hb, AddValuation.map_mul, IsDiscreteValuationRing.addVal_uniformizer hπ, hbv, add_zero]
  -- (3) the root is nonzero — from `a₀ ≠ 0`, NOT from irreducibility
  haveI : Nontrivial (AdjoinRoot f) :=
    AdjoinRoot.nontrivial f (ne_of_gt (natDegree_pos_iff_degree_pos.1 hd))
  haveI : Module.Free O (AdjoinRoot f) := hf.free_adjoinRoot
  haveI : Module.Finite O (AdjoinRoot f) := hf.finite_adjoinRoot
  have hsign : ((-1 : O)) ^ f.natDegree ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have ha0 : f.coeff 0 ≠ 0 := fun hz => h0 (hz ▸ Ideal.zero_mem _)
  have hne : (AdjoinRoot.root f) ≠ 0 := by
    intro hz
    have hnorm := norm_adjoinRoot_root hf hd
    rw [hz, Algebra.norm_zero] at hnorm
    exact ha0 ((mul_eq_zero.1 hnorm.symm).resolve_left hsign)
  -- (4) `1` is a norm-valuation, hence the residue degree is `1`
  have hunit : IsUnit ((-1 : O) ^ f.natDegree) := (isUnit_one.neg).pow _
  have hsignval : IsDiscreteValuationRing.addVal O ((-1 : O) ^ f.natDegree) = 0 := by
    rw [← hunit.unit_spec]; exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
  have hmem : (1 : ℕ) ∈ normValues f := by
    refine ⟨one_pos, AdjoinRoot.root f, hne, ?_⟩
    rw [norm_adjoinRoot_root hf hd, AddValuation.map_mul, hval, hsignval, zero_add]
    rfl
  have hinf : inertiaDegOf f = 1 := inertiaDegOf_eq_of hmem (fun m _ => one_dvd m)
  -- (5) assemble: `f` is its own monic factorization, and `e = n / 1 = n`
  have hF : IsMonicFactorization f {f} :=
    ⟨by intro g hg; rw [Multiset.mem_singleton.1 hg]; exact ⟨hf, hirr⟩, by simp⟩
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [efPair, ramIndexOf, hinf]

end Eisenstein

/-! ## Axiom census -/

section AxCheck

#print axioms Uniformity.Density.minpoly_adjoinRoot_root
#print axioms Uniformity.Density.norm_adjoinRoot_root
#print axioms Uniformity.Density.typeOf_eisenstein

end AxCheck

end Uniformity.Density
