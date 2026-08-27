/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132kp2
import Uniformity.ChapC.C132rp10

/-!
# Uniformity.ChapC.C132kp3 — the conditional μ₃ key criterion

**[M3-KP3, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6):
assemble the literal degree-eight `key_criterion` field.  A monic polynomial of degree
`2 * 1 * deg(keyAt 2) = 8`, with irreducible normalized μ₃ residual of degree one and
nonzero constant coefficient, is a μ₃ key polynomial.

This is only the conditional field assembly: M3-RP10 records that the landed literal recipe
cannot currently supply such a residual, so this file does not manufacture a degree-eight
key witness.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132kp3

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp6 Uniformity.Density.Tower.C132rp7
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C132rp10
open Uniformity.Density.Tower.C132kp0 Uniformity.Density.Tower.C132kp1
open Uniformity.Density.Tower.C132kp2 Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- **NODE M3-KP3 — the literal μ₃ `key_criterion`:** at the depth-two recipe degree
`2 * 1 * deg(keyAt 2) = 8`, monicity, residual irreducibility, residual degree one, and a
nonzero residual scalar assemble μ₃-minimality and μ₃-irreducibility into key-polynomialhood.
The residual degree and scalar hypotheses are retained verbatim for the source-law field. -/
theorem s2Mu3_key_criterion :
    ∀ g : Polynomial O, g.Monic →
      g.natDegree = 2 * 1 * ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree →
      Irreducible (s2Mu3NormRes h2 hq g) →
      (s2Mu3NormRes h2 hq g).natDegree = 1 →
      (s2Mu3NormRes h2 hq g).coeff 0 ≠ 0 →
      S2Mu3KeyPoly h2 hq g := by
  intro g hmon hdeg hirr _ _
  have hdeg8 : g.natDegree = 8 := by
    rw [hdeg, s2Mu3KeyChain_keyAt_two_natDegree h2 hq]
  refine ⟨hmon, s2Mu3Minimal_of_irreducible_normRes h2 hq hdeg8 hirr, ?_⟩
  exact s2Mu3Irreducible_of_irreducible_normRes h2 hq hmon (by omega) hirr

/-- The μ₃ occurrence of `FGMNSourceLaws.key_criterion`: any source data at `(2, 1, 21)`
whose normalized residual and key predicate are the landed μ₃ ones inherits the literal
degree-eight criterion. -/
theorem s2Mu3_key_criterion_fills (K : KeyChain (s2DepthTwo h2 hq))
    (S : FGMNSourceData (s2DepthTwo h2 hq) K 2 1 21)
    (hnorm : S.normalizedResidual = s2Mu3NormRes h2 hq)
    (hkp : S.keyPolynomial = S2Mu3KeyPoly h2 hq) :
    ∀ g : Polynomial O, g.Monic →
      g.natDegree = 2 * 1 * (K.keyAt 2).natDegree →
      Irreducible (S.normalizedResidual g) →
      (S.normalizedResidual g).natDegree = 1 →
      (S.normalizedResidual g).coeff 0 ≠ 0 → S.keyPolynomial g := by
  intro g hmon hdeg hirr hfdeg hc0
  rw [hnorm] at hirr hfdeg hc0
  rw [hkp]
  refine s2Mu3_key_criterion h2 hq g hmon ?_ hirr hfdeg hc0
  have hKdeg : (K.keyAt 2).natDegree = 4 :=
    (K.keyAt_degree 2 ⟨by omega, le_rfl⟩).trans (s2DepthTwo_Dcum_two h2 hq)
  rw [hdeg, hKdeg, s2Mu3KeyChain_keyAt_two_natDegree h2 hq]

end S2

end Uniformity.Density.Tower.C132kp3

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132kp3.s2Mu3_key_criterion
#print axioms Uniformity.Density.Tower.C132kp3.s2Mu3_key_criterion_fills

end AxCheck
