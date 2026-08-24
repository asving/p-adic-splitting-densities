import Uniformity.ChapC.C130s17
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.ExtendToLocalization

/-!
Elaboration and contradiction probes for U13's `S2SourceFrontier` inhabitation audit.

This file contains no axiom declaration and no proof placeholder.  Its main result is a
negative feasibility certificate for the frontier exactly as currently typed: the terminal
residue-field algebra structure forces every coefficient homomorphism to kill `2`, while
`NodePointSource.slot_value` and `hgt_ne_top` require the nonzero constant polynomial `C 2`
to have finite evaluation height.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.Tower.U13Probe

open Polynomial IsLocalRing Uniformity.Density Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130s17

universe uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## The terminal S2 field and every algebra over it have characteristic two -/

theorem terminal_two_eq_zero : (2 : (s2DepthTwo h2 hq).fld 2) = 0 := by
  haveI : Finite ((s2DepthTwo h2 hq).fld 2) :=
    Nat.finite_of_card_ne_zero (by rw [s2Fld₂_card h2 hq]; norm_num)
  have hu : Nat.card ((s2DepthTwo h2 hq).fld 2)ˣ = 1 := by
    rw [Nat.card_units, s2Fld₂_card h2 hq]
  haveI : Subsingleton ((s2DepthTwo h2 hq).fld 2)ˣ :=
    (Nat.card_eq_one_iff_unique.mp hu).1
  by_contra h
  have hunit : IsUnit (2 : (s2DepthTwo h2 hq).fld 2) :=
    isUnit_iff_ne_zero.mpr h
  have heq : hunit.unit = 1 := Subsingleton.elim _ _
  have htwo_one : (2 : (s2DepthTwo h2 hq).fld 2) = 1 := by
    calc
      (2 : (s2DepthTwo h2 hq).fld 2) = (hunit.unit : (s2DepthTwo h2 hq).fld 2) :=
        hunit.unit_spec.symm
      _ = 1 := by rw [heq]; rfl
  have hone_ne_zero : (1 : (s2DepthTwo h2 hq).fld 2) ≠ 0 := one_ne_zero
  apply hone_ne_zero
  linear_combination htwo_one

theorem algebra_two_eq_zero {L : Type uL} [Field L]
    [Algebra ((s2DepthTwo h2 hq).fld 2) L] : (2 : L) = 0 := by
  rw [← map_ofNat (algebraMap ((s2DepthTwo h2 hq).fld 2) L) 2,
    terminal_two_eq_zero h2 hq, map_zero]

/-! ## The current node-point interface is contradictory at the constant polynomial `C 2` -/

theorem no_s2_node_source {L : Type uL} [Field L]
    [Algebra ((s2DepthTwo h2 hq).fld 2) L] :
    IsEmpty (NodePointSource (L := L) (s2DepthTwo h2 hq)
      (s2RepositoryRealization h2 hq).receiver
      (s2RepositoryRealization h2 hq).keys) := by
  constructor
  intro S
  let hi : StageLive 2 2 := ⟨by omega, by omega⟩
  let A : Polynomial O := Polynomial.C (2 : O)
  have hA : A ≠ 0 := by
    rw [Polynomial.C_ne_zero]
    exact h2.ne_zero
  have hdeg : A.natDegree < (s2DepthTwo h2 hq).Dcum 2 := by
    have hAdeg : A.natDegree = 0 := by
      simp [A]
    have hD : (s2DepthTwo h2 hq).Dcum 2 = 4 := s2DepthTwo_Dcum_two h2 hq
    omega
  obtain ⟨x, hx⟩ := S.point_exists 2 hi
  have heval : Polynomial.eval₂ S.coeffHom (S.coord x) A = 0 := by
    dsimp [A]
    rw [Polynomial.eval₂_C]
    rw [map_ofNat, algebra_two_eq_zero h2 hq]
  have hpoint_top : S.pointHgt 2 x A = ⊤ := by
    rw [S.pointHgt_eval, heval, S.value_zero 2 hi]
  have hslot : S.pointHgt 2 x A = S.hgt 2 A :=
    S.slot_value 2 hi x hx A hA hdeg
  have hfinite : S.hgt 2 A ≠ ⊤ := S.hgt_ne_top 2 hi A hA hdeg
  exact hfinite (hslot.symm.trans hpoint_top)

theorem no_s2_source_frontier {L : Type uL} [Field L]
    [Algebra ((s2DepthTwo h2 hq).fld 2) L] :
    IsEmpty (S2SourceFrontier h2 hq L) := by
  constructor
  intro S
  exact (no_s2_node_source h2 hq).false S.node

/-! ## A small finite-development tooth: concrete input computations do elaborate -/

example : (s2DepthTwo h2 hq).Dcum 2 = 4 := s2DepthTwo_Dcum_two h2 hq

example :
    ((s2RepositoryRealization h2 hq).keys.keyAt 2).natDegree = 4 := by
  rw [s2RepositoryRealization_keys]
  exact ((s2DepthTwoKeyChain h2 hq).keyAt_degree 2 ⟨by omega, by omega⟩).trans
    (s2DepthTwo_Dcum_two h2 hq)

example : s2Hgt₂ h2 hq (Polynomial.C (2 : O)) ≠ ⊤ :=
  s2Hgt₂_ne_top h2 hq (Polynomial.C_ne_zero.mpr h2.ne_zero)

end Uniformity.Density.Tower.U13Probe

#print axioms Uniformity.Density.Tower.U13Probe.terminal_two_eq_zero
#print axioms Uniformity.Density.Tower.U13Probe.algebra_two_eq_zero
#print axioms Uniformity.Density.Tower.U13Probe.no_s2_node_source
#print axioms Uniformity.Density.Tower.U13Probe.no_s2_source_frontier

/- Mathlib-search pins: these are useful primitives, but none is an augmented MacLane
valuation, an AdjoinRoot valuation constructor, or a Newton-polygon/residual-operator API. -/
#check Polynomial.gaussNorm_mul
#check Valuation.extendToLocalization
#check Valuation.HasExtension
