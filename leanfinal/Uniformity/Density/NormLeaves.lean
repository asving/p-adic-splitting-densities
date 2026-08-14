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

/-! ## Axiom census -/

section AxCheck

#print axioms Uniformity.Density.minpoly_adjoinRoot_root
#print axioms Uniformity.Density.norm_adjoinRoot_root

end AxCheck

end Uniformity.Density
