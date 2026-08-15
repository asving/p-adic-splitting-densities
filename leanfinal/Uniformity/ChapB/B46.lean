/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Uniformity.ChapB.B46 — a residual factor splits off, one at a time

**Chapter B, NODE B.46** (`blueprint/CHAP-B_leaf_layer.md` §6). *A residual factor splits off, one
at a time.* Let `K` be a field and let `ψ ∈ K[Y]` be irreducible. If `ψ ∤ S` then `ψ ^ a` and `S`
are coprime, for every exponent `a`.

This is the coprimality side condition every one-factor-at-a-time Hensel split of the residual
polynomial `R_λ(f) = ψ₁^{a₁} ⋯ ψ_t^{a_t}` needs: to peel `ψ^a` off `R_λ(f)` one must know that
`ψ^a` and the complementary factor are coprime, and the only input available at that point is that
`ψ` does not divide the complement.

DEPENDS: mathlib only — `Irreducible.coprime_iff_not_dvd` (available for any Bézout commutative
ring; `K[Y]` qualifies, being a principal ideal domain) and `IsCoprime.pow_left`.

ENVIRONMENT: ENV-D — the node binds its own `{K : Type*} [Field K]` and mentions no `O`.

**PROOF.** `IsCoprime ψ S` is `(hψ.coprime_iff_not_dvd).2 h`; then `IsCoprime.pow_left`.
(The blueprint flagged the mathlib name as needing confirmation, suggesting a possible
`EuclideanDomain.isCoprime_of_…`. Confirmed at our pin: the name is
`Irreducible.coprime_iff_not_dvd`, stated in `Mathlib/RingTheory/PrincipalIdealDomain.lean` for
`[CommRing R] [IsBezout R]`, and typeclass inference finds `IsBezout K[Y]` through the
`EuclideanDomain`/PID instance chain.)

**SOURCE.** `docs/GMN_citations.md` Thm 1.19 (`R_λ(f) ∼ ψ₁^{a₁} … ψ_t^{a_t}` into
pairwise-distinct monic irreducibles in `F_φ[y]`); `EFF.HE3.32` (`R_λ = Π_r r^{m_r}`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

/-- **B.46.** *A residual factor splits off, one at a time.* Over a field `K`, if `ψ` is
irreducible and does not divide `S`, then `ψ ^ a` is coprime to `S` for every `a`. -/
theorem isCoprime_pow_of_not_dvd {K : Type*} [Field K] {ψ S : Polynomial K}
    (hψ : Irreducible ψ) {a : ℕ} (h : ¬ ψ ∣ S) : IsCoprime (ψ ^ a) S :=
  ((hψ.coprime_iff_not_dvd).2 h).pow_left

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.isCoprime_pow_of_not_dvd
end AxCheck
