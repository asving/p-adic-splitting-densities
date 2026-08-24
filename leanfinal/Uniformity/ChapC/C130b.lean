/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C83
import Uniformity.ChapE.E10

/-!
# Uniformity.ChapC.C130b — tower-instantiation freeze v2, layers C.130b/c

This file transcribes the part of layers C.130b/c of
`TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md` that is determined by C.83's carrier.
The general-depth stage degree is exactly C.83's cumulative degree
`D_i = ∏_{1 ≤ j ≤ i} e_j f_j`.

The remainder of the two layers is **BLOCKED**, for the exact carrier reason recorded by the
freeze itself.  `DeepTower` contains only `(e,f,u,ψ)` and abstract residue-field iterate
witnesses.  It contains no chain of polynomials `Φ_i : O[x]`, no equation identifying a
general `Φ_i` with the iterated EFF.HETOW.13/EFF.GENTOW5.21 recipe, and no legal node-point
realization from which the EFF.T2.04/.05/.09 height, digit, `Full`, and lift laws can be read.
Consequently neither `stageKey` nor the transported E.10 `stageCarrier` can be declared from
the present vocabulary without adding mathematical data absent from `DeepTower`.

In particular, this file does not approximate the missing data by an arbitrary polynomial,
an empty `Full` predicate, or a `True`-valued interface.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.DeepTower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ}
  {hpin : npHgt Polynomial.X F.key
    (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)}
  {r : ℕ}

/-- **Freeze-v2 layer C.130b (partial supply).** The degree of the live stage `i` is the
source's cumulative tower degree `D_i = ∏_{1 ≤ j ≤ i} e_j f_j`, already represented by
C.83's `DeepTower.Dcum`.  The accompanying general-depth polynomial `stageKey` is blocked as
explained in the module docstring. -/
def stageDeg (T : DeepTower F H₀ hpin r) (i : ℕ) : ℕ := T.Dcum i

end Uniformity.Density.Tower.DeepTower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.DeepTower.stageDeg

end AxCheck
