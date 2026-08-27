/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132kp5

/-!
# Uniformity.ChapC.C132kp6 — μ₃ initial/residual interface

**[M3-KP6, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6).

The forward half of Proposition 5.6 is already the universal theorem landed by M3-KP1:
initial equivalence preserves the normalized residual.  The requested converse for arbitrary
`S2Mu3KeyPoly`s cannot be derived from M3-KP1--KP5: unlike the μ₂ development, this campaign
has not landed the three key-structure lemmas that turn residual equality into equality of
grades and unstripped graded residuals.

In particular, M3-KP4 supplies only the carried degree-four key with unit residual and M3-KP3
only constructs degree-eight keys conditionally.  Neither supplies the arbitrary-key degree
dictionary.  This file deliberately records only the reusable, fully proved forward interface;
it does not postulate the missing dictionary or a converse.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132kp6

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp6 Uniformity.Density.Tower.C132rp7
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C132kp0
open Uniformity.Density.Tower.C132kp1 Uniformity.Density.Tower.C132kp2
open Uniformity.Density.Tower.C132kp4 Uniformity.Density.Tower.C132kp5
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- The forward μ₃ half of the intended initial/residual equivalence.  It is universal: no
key-polynomial, degree, or nonzero hypothesis is needed. -/
theorem s2Mu3_initial_to_residual {g h : Polynomial O}
    (hgh : S2Mu3InitialEquiv h2 hq g h) :
    s2Mu3NormRes h2 hq g = s2Mu3NormRes h2 hq h :=
  s2Mu3NormRes_eq_of_initialEquiv h2 hq hgh

end S2

end Uniformity.Density.Tower.C132kp6

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132kp6.s2Mu3_initial_to_residual

end AxCheck
