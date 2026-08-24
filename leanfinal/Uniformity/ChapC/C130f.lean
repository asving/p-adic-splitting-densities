/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10FreezeV2

/-!
# Uniformity.ChapC.C130f — freeze-v2 layer C.130f: lattices and gauge export

This file transcribes the typeable part of layer **C.130f** from
`TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md`: the Laurent exponent lattice on
`(π, x, Φ₁, …, Φ_{j-1})`, its synchronized finite product over the live gauge levels, the
level-height homomorphisms, the `towerNorm`-based normal section, and the explicit `ULift`
export required by D-TIF-2 and findings #28--#29.

The freeze additionally requires the section to have exact height for every integer.  That
statement is not declared here: C.83's `towerNorm` has `ℕ` exponents and uses truncated
subtraction, so it is not such a Laurent solve at small nonnegative heights (already
`(e₂,u₂,k)=(2,5,1)` is a counterexample).  The exact-height export is therefore BLOCKED on a
signed integer/Laurent general-depth normalizer replacing that missing carrier; no false law is
stored in a structure.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open scoped BigOperators
open Uniformity.Density.Gauge
open Uniformity.Density.Leaf

universe uG uKt

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ r : ℕ}
variable {hpin : npHgt Polynomial.X F.key
  (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)}

/-- A live level for the synchronized gauge product.  The strict upper bound is the one from
D-TIF-2: a gauge at level `j` consumes `u_(j+1)`. -/
abbrev LiveLevel (r : ℕ) := {j : ℕ // GaugeLive r j}

/-- The Laurent exponent lattice on `(π, x, Φ₁, …, Φ_{j-1})`.

The first two integer coordinates are the exponents of `π` and `x`; coordinate `a : Fin (j-1)`
is the exponent of `Φ_(a+1)`. -/
abbrev LevelExponentLattice (j : ℕ) :=
  Multiplicative (ℤ × ℤ × (Fin (j - 1) → ℤ))

/-- D-TIF-2's synchronized product before universe lifting. -/
abbrev GaugeLattice0 (r : ℕ) := ∀ j : LiveLevel r, LevelExponentLattice j.1

/-- Finding #28's explicit export of the concrete `Type 0` synchronized lattice to `Type uG`. -/
abbrev GaugeLattice (r : ℕ) : Type uG := ULift.{uG} (GaugeLattice0 r)

/-- The multiplicative equivalence implementing the `ULift` export. -/
def gaugeLatticeEquiv (r : ℕ) : GaugeLattice.{uG} r ≃* GaugeLattice0 r :=
  MulEquiv.ulift

/-- The level-`j` height of a Laurent exponent vector.

At depth `j`, the weights are `ê_j` on `π`, `(ê_j/e₁)u₁` on `x`, and
`(ê_j/ê_(a+2))u_(a+2)` on `Φ_(a+1)`, exactly the coefficient pattern regressed by D62w's
depth-two and depth-three lattices. -/
def levelExponentHeight (T : DeepTower F H₀ hpin r) (j : ℕ) :
    LevelExponentLattice j →* Multiplicative ℤ where
  toFun g :=
    let z := Multiplicative.toAdd g
    Multiplicative.ofAdd
      (z.1 * T.ehat j + z.2.1 * ((T.ehat j / T.e 1) * T.u 1) +
        ∑ a : Fin (j - 1), z.2.2 a * ((T.ehat j / T.e (a.1 + 2)) * T.u (a.1 + 2)))
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    ring

/-- Projection to a live level followed by its Laurent height map, on the concrete product. -/
def levelHeight0 (T : DeepTower F H₀ hpin r) (j : LiveLevel r) :
    GaugeLattice0 r →* Multiplicative ℤ :=
  (levelExponentHeight T j.1).comp
    { toFun := fun g => g j
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- The live height family on the `ULift`ed synchronized product. -/
def levelHeight (T : DeepTower F H₀ hpin r) (j : LiveLevel r) :
    GaugeLattice.{uG} r →* Multiplicative ℤ :=
  (levelHeight0 T j).comp (gaugeLatticeEquiv r).toMonoidHom

/-- C.83's nonnegative `towerNorm` exponent tuple, coerced into the Laurent lattice. -/
def towerNormLattice (T : DeepTower F H₀ hpin r) (j k : ℕ) : LevelExponentLattice j :=
  let p := T.towerNorm (j - 1) k
  Multiplicative.ofAdd ((p.1 : ℤ), (p.2.1 : ℤ), fun a => (p.2.2 a : ℤ))

/-- The literal D-TIF-2 extension of C.83's nonnegative `towerNorm`: zero and positive heights
use `towerNorm`, while negative heights use the inverse Laurent word. -/
def levelNorm (T : DeepTower F H₀ hpin r) (j : ℕ) : ℤ → LevelExponentLattice j
  | Int.ofNat k => towerNormLattice T j k
  | Int.negSucc k => (towerNormLattice T j (k + 1))⁻¹

/-- The bounded search used by C.83 chooses exponent zero at height zero. -/
theorem towerSolve_zero (u e : ℕ) : towerSolve u e 0 = 0 := by
  cases e with
  | zero => simp [towerSolve]
  | succ e =>
      unfold towerSolve
      rw [List.range_eq_range']
      change (List.find? (fun b => b * u % (e + 1) == 0 % (e + 1))
        (0 :: List.range' 1 e)).getD 0 = 0
      simp

/-- The frame solve also chooses exponent zero at height zero. -/
theorem KeyFrame.slotIdx_zero (F : KeyFrame O π) : F.slotIdx 0 = 0 := by
  change towerSolve F.h F.e₁ 0 = 0
  exact towerSolve_zero _ _

/-- C.83's exponent recursion returns the zero exponent tuple at height zero. -/
theorem towerNorm_zero (T : DeepTower F H₀ hpin r) (i : ℕ) :
    T.towerNorm i 0 = (0, 0, fun _ => 0) := by
  induction i with
  | zero =>
      simp only [DeepTower.towerNorm, F.slotIdx_zero]
      simp only [Nat.zero_mul, Nat.zero_sub, Nat.zero_div, Prod.mk.injEq, true_and]
      funext x
      exact x.elim0
  | succ i ih =>
      simp [DeepTower.towerNorm, towerSolve_zero, ih]
      funext x
      refine Fin.lastCases ?_ (fun a => ?_) x <;> simp

/-- The normal section assembled componentwise on the synchronized concrete product.

As required by `NormSection`, this records only the zero normalization.  Exact height is a
separate theorem obligation in D-TIF-2 and is blocked as documented in the module header. -/
def normSection0 (T : DeepTower F H₀ hpin r) : NormSection (GaugeLattice0 r) where
  n k j := levelNorm T j.1 k
  n_zero := by
    funext j
    apply Multiplicative.toAdd.injective
    simp [levelNorm, towerNormLattice, towerNorm_zero]
    funext a
    rfl

/-- The synchronized normal section transported through the explicit `ULift` equivalence. -/
def normSection (T : DeepTower F H₀ hpin r) : NormSection (GaugeLattice.{uG} r) where
  n k := (gaugeLatticeEquiv r).symm (normSection0 T |>.n k)
  n_zero := by rw [normSection0 T |>.n_zero]; rfl

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.LiveLevel
#print axioms Uniformity.Density.Tower.LevelExponentLattice
#print axioms Uniformity.Density.Tower.GaugeLattice0
#print axioms Uniformity.Density.Tower.GaugeLattice
#print axioms Uniformity.Density.Tower.gaugeLatticeEquiv
#print axioms Uniformity.Density.Tower.levelExponentHeight
#print axioms Uniformity.Density.Tower.levelHeight0
#print axioms Uniformity.Density.Tower.levelHeight
#print axioms Uniformity.Density.Tower.towerNormLattice
#print axioms Uniformity.Density.Tower.levelNorm
#print axioms Uniformity.Density.Tower.towerSolve_zero
#print axioms Uniformity.Density.Tower.KeyFrame.slotIdx_zero
#print axioms Uniformity.Density.Tower.towerNorm_zero
#print axioms Uniformity.Density.Tower.normSection0
#print axioms Uniformity.Density.Tower.normSection

end AxCheck
