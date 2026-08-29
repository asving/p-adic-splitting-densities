/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG10
import Uniformity.ChapC.C133mh12

/-!
# Uniformity.ChapI.IFCG11 — the recentred-cluster exhaustion kernel

This file attacks the last mathematical input to the strong finite genre cover.  The target is
`IFCG9.RecentredClusterDegreeExhaustionStatement`: the strict coefficient-side floor in the
`F.key`-development should rule out a positive-degree C.33 below-floor remainder.

The one-side no-far-primes sub-kernel lands.  In the general multi-side case, the exact missing
entire/principal-polygon inheritance is isolated without mentioning `DvDissection`: every
positive-degree monic factor of a strictly recentred polynomial retains a genuine side above
the frame floor.  That statement implies the target kernel and fires IFCG10's assembled cover.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG11

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.IFCG9 Uniformity.Density.IFCG10

/-! ## §1 — the no-far-primes one-side sub-kernel -/

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The no-far-primes mechanism in exactly the shape needed by the exhaustion problem.
If the entire dissection product is pure at one above-floor direction, its point-sided
below-floor factor has degree zero and hence, being monic, is `1`. -/
theorem below_eq_one_of_isDvPure
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {f : Polynomial O} (D : DvDissection F f)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hpure : IsDvPure F f u ℓ) (hdvd : (F.e₁ * F.f₁) ∣ f.natDegree) :
    D.below = 1 := by
  classical
  let w : Polynomial O := ∏ p ∈ D.slopes, D.factor p
  have hw : w.Monic :=
    Polynomial.monic_prod_of_monic D.slopes D.factor (fun p hp => D.hmonic p hp)
  have hnq : (dvSideSet F D.below u ℓ).Nonempty :=
    dvSideSet_nonempty F D.hbelow_monic.ne_zero u hℓ
  have hpt : dvSideDeg F D.below u ℓ hnq = 0 :=
    D.hbelow u ℓ hℓ hcop hfloor hnq
  have hpure' : IsDvPure F (D.below * w) u ℓ := by
    rw [← D.hprod]
    exact hpure
  have hdvd' : (F.e₁ * F.f₁) ∣ (D.below * w).natDegree := by
    rw [← D.hprod]
    exact hdvd
  have hdeg : D.below.natDegree = 0 :=
    C133mh12.natDegree_eq_zero_of_isDvPure_mul_of_dvSideDeg_eq_zero
      hπ hh H₀ hpin hℓ hcop hfloor D.hbelow_monic hw hpure' hdvd' hnq hpt
  exact Polynomial.eq_one_of_monic_natDegree_zero D.hbelow_monic hdeg

/-- A one-side recentred context exhausts its C.33 dissection.  This is the complete
no-far-primes sub-kernel; the general recentred cluster can have several above-floor sides. -/
theorem degreeExhausted_of_isDvPure
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {f : Polynomial O}
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hpure : IsDvPure F f u ℓ) (hdvd : (F.e₁ * F.f₁) ∣ f.natDegree) :
    DissectionDegreeExhausted F f := by
  rw [degreeExhausted_iff_below_eq_one]
  intro D
  exact below_eq_one_of_isDvPure hπ hh H₀ hpin D hℓ hcop hfloor hpure hdvd

/-! ## §2 — the exhaustion kernel -/

/-- A genuine side strictly above the frame floor.  Unlike `DvDissection.hbelow`, this
requires positive side degree and therefore records actual far-side mass. -/
def HasGenuineAboveFloorSide (F : KeyFrame O π) (g : Polynomial O) : Prop :=
  ∃ (u ℓ : ℕ), 0 < ℓ ∧ Nat.Coprime u ℓ ∧
    ℓ * ((F.e₁ * F.f₁) * F.h) < u ∧
    ∃ hne : (dvSideSet F g u ℓ).Nonempty, 0 < dvSideDeg F g u ℓ hne

/-- The entire/principal Newton-polygon factor statement needed by the multi-side case:
every positive-degree monic factor of `f` still has genuine mass above the frame floor.
This is coefficient/factor language and mentions neither a C.33 dissection nor its `below`
field. -/
def MonicFactorsHaveAboveFloorSide (F : KeyFrame O π) (f : Polynomial O) : Prop :=
  ∀ (g w : Polynomial O), g.Monic → w.Monic → f = g * w → 0 < g.natDegree →
    HasGenuineAboveFloorSide F g

/-- Once positive-degree monic factors retain an above-floor side, a C.33 below-floor
remainder cannot have positive degree: its own `hbelow` field forbids precisely such a side. -/
theorem below_eq_one_of_monicFactorsHaveAboveFloorSide
    {F : KeyFrame O π} {f : Polynomial O}
    (hfac : MonicFactorsHaveAboveFloorSide F f) (D : DvDissection F f) :
    D.below = 1 := by
  classical
  by_cases hdeg : D.below.natDegree = 0
  · exact Polynomial.eq_one_of_monic_natDegree_zero D.hbelow_monic hdeg
  · have hpos : 0 < D.below.natDegree := Nat.pos_of_ne_zero hdeg
    have hw : (∏ p ∈ D.slopes, D.factor p).Monic :=
      Polynomial.monic_prod_of_monic D.slopes D.factor (fun p hp => D.hmonic p hp)
    obtain ⟨u, ℓ, hℓ, hcop, hfloor, hne, hside⟩ :=
      hfac D.below (∏ p ∈ D.slopes, D.factor p) D.hbelow_monic hw D.hprod hpos
    have hz := D.hbelow u ℓ hℓ hcop hfloor hne
    omega

/-- The exact remaining coefficient-to-factor bridge.  It says that IFCG9's strict
recentred coefficient floor is inherited, at the only strength needed here, by every
positive-degree monic factor.  Proving this is the entire/principal polygon comparison;
the conclusion is not phrased using `DvDissection` and is not a renamed `below = 1`. -/
def StrictRecentredFactorSideStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (π : O) (_hπ : Irreducible π) (F : KeyFrame O π) (f : Polynomial O),
    f.Monic → ¬ F.key ∣ f → StrictlyRecentredAboveFloor F f →
      MonicFactorsHaveAboveFloorSide F f

/-- **Honest multi-side reduction.**  The coefficient-to-factor polygon statement is
exactly sufficient for IFCG9's exhaustion kernel. -/
theorem recentredClusterDegreeExhaustion_of_factorSide
    (hfactor : StrictRecentredFactorSideStatement) :
    RecentredClusterDegreeExhaustionStatement := by
  unfold RecentredClusterDegreeExhaustionStatement
  intro O _ _ _ _ π hπ F f hmon hkey hrec
  apply degreeExhausted_of_below_eq_one
  intro D
  exact below_eq_one_of_monicFactorsHaveAboveFloorSide
    (hfactor O π hπ F f hmon hkey hrec) D

/-! ## §3 — the strong finite genre cover, fired from the residual bridge -/

/-- The already-assembled strong cover fired from the exact remaining coefficient/factor
polygon bridge. -/
theorem finiteGenreCoverAt_strong_of_factorSide
    (hfactor : StrictRecentredFactorSideStatement) :
    StrongCoverExhaustive ∧ StrongCoverDisjoint ∧ ∀ m : ℕ, DecreasingGenreBankAt m :=
  finiteGenreCoverAt_strong_of_kernel
    (recentredClusterDegreeExhaustion_of_factorSide hfactor)

end Uniformity.Density.IFCG11

end

/-! ## AXCHECK FOOTER -/

#print axioms Uniformity.Density.IFCG11.below_eq_one_of_isDvPure
#print axioms Uniformity.Density.IFCG11.degreeExhausted_of_isDvPure
#print axioms Uniformity.Density.IFCG11.below_eq_one_of_monicFactorsHaveAboveFloorSide
#print axioms Uniformity.Density.IFCG11.recentredClusterDegreeExhaustion_of_factorSide
#print axioms Uniformity.Density.IFCG11.finiteGenreCoverAt_strong_of_factorSide
