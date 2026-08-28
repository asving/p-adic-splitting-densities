/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C134dv2g
import Uniformity.ChapC.C134f12c

/-!
# Uniformity.ChapC.C134p1 — the residual nondivisibility to `¬ MuDvd` bridge [P1U 2026-08-28]

**[P1U 2026-08-28].**  This file lands P2 only.  P1 (`IsTestKey L Ψ → IsMuKey L Ψ`)
is citation-grade against the present corpus: Guàrdia--Nart, *Genetics of polynomials over
local fields*, Lemma 3.1(3), identifies representatives of a type with key polynomials,
but the dictionary from the five slot clauses of `IsTestKey` to a type representative is
not formalized.  Per the axiom policy, no cite is declared here.

P2 is Lean-core: initial equivalence preserves the normalized level residual by the landed
deep-perturbation theorem, and Theorem M's generic product law turns `Ψ ∣µ g` into
`R(Ψ) ∣ R(g)`.  For a test key, `R(Ψ) = L.r` by `C131aa.dvResPoly_testKey`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C134p1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C134dv2g

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

private theorem inner_floor (L : LevelDatum F H₀ hpin) :
    L.ℓ * ((F.e₁ * F.f₁) * F.h) < L.u := by
  rw [← mul_assoc]
  exact L.hκ

private theorem exists_pin (F : KeyFrame O π) {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1
    (dvOnSide_of_mem_dvSideSet (Finset.min'_mem _ hne)).2
  exact ⟨M, hM.symm⟩

private theorem dvResPoly_congr (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} {x y : Polynomial O} (hxy : x = y)
    (hnex : (dvSideSet F x u ℓ).Nonempty) (hney : (dvSideSet F y u ℓ).Nonempty)
    {Mx My : ℕ} (hpx : dvHgt F x (dvSideMin F x u ℓ hnex) = (Mx : ℕ∞))
    (hpy : dvHgt F y (dvSideMin F y u ℓ hney) = (My : ℕ∞)) :
    dvResPoly F H₀ hpin x u ℓ hnex Mx hpx =
      dvResPoly F H₀ hpin y u ℓ hney My hpy := by
  subst hxy
  have hM : Mx = My := by exact_mod_cast hpx.symm.trans hpy
  subst hM
  rfl

/-- Initial equivalence for the level valuation preserves the normalized level residual,
at arbitrary side witnesses and finite pins.  This is the frame-generic forward half of
the initial-form/residual correspondence needed by P2. -/
theorem dvResPoly_eq_of_muEquiv (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {g z : Polynomial O} (heq : MuEquiv L g z)
    (hng : (dvSideSet F g L.u L.ℓ).Nonempty)
    (hnz : (dvSideSet F z L.u L.ℓ).Nonempty) {Mg Mz : ℕ}
    (hpg : dvHgt F g (dvSideMin F g L.u L.ℓ hng) = (Mg : ℕ∞))
    (hpz : dvHgt F z (dvSideMin F z L.u L.ℓ hnz) = (Mz : ℕ∞)) :
    dvResPoly F H₀ hpin g L.u L.ℓ hng Mg hpg
      = dvResPoly F H₀ hpin z L.u L.ℓ hnz Mz hpz := by
  rcases heq with ⟨hdeep, hsupp⟩ | ⟨rfl, rfl⟩
  · have hfin : dvSupp F z L.u L.ℓ ≠ ⊤ := by
      intro htop
      have htopg : dvSupp F g L.u L.ℓ = ⊤ := hsupp.trans htop
      exact (not_lt_of_ge (le_top : dvSupp F (g - z) L.u L.ℓ ≤ ⊤))
        (htopg ▸ hdeep)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
    have hsum : z + (g - z) = g := by ring
    have hdeep' : (m : ℕ∞) < dvSupp F (g - z) L.u L.ℓ := by
      rw [hm, ← hsupp]
      exact hdeep
    have hnsum : (dvSideSet F (z + (g - z)) L.u L.ℓ).Nonempty := by
      rw [hsum]
      exact hng
    obtain ⟨Msum, hpsum⟩ := exists_pin F hnsum
    have hres := C131y.dvResPoly_add_deep L hπ hm.symm hdeep' hnz hnsum hpz hpsum
    have hcongr := dvResPoly_congr F H₀ hpin hsum hnsum hng hpsum hpg
    exact hcongr.symm.trans hres
  · exact False.elim ((dvOnSide_of_mem_dvSideSet (Finset.min'_mem _ hng)).2 (by
      rw [dvHgt, dev_of_zero, C118a.stageHeight_zero]))

/-- **P2, generic bridge.**  If the level residual of `g` is not divisible by the
test key's prescribed residual factor, then the key does not μ-divide `g`. -/
theorem not_muDvd_of_residual_notdvd (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h) {Ψ g : Polynomial O}
    (hΨ : IsTestKey L Ψ)
    (hng : (dvSideSet F g L.u L.ℓ).Nonempty) (Mg : ℕ)
    (hpg : dvHgt F g (dvSideMin F g L.u L.ℓ hng) = (Mg : ℕ∞))
    (hnd : ¬ L.r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hng Mg hpg) :
    ¬ MuDvd L Ψ g := by
  intro hdvd
  obtain ⟨q, heq⟩ := hdvd
  have hg : g ≠ 0 := by
    intro hg0
    subst g
    exact (dvOnSide_of_mem_dvSideSet (Finset.min'_mem _ hng)).2 (by
      rw [dvHgt, dev_of_zero, C118a.stageHeight_zero])
  have hΨ0 : Ψ ≠ 0 := hΨ.1.ne_zero
  have hq0 : q ≠ 0 := by
    intro hq0
    subst q
    simp only [mul_zero] at heq
    rcases heq with ⟨hlt, -⟩ | ⟨hg0, -⟩
    · rw [sub_zero] at hlt
      exact (lt_irrefl _ hlt)
    · exact hg hg0
  have hprod0 : Ψ * q ≠ 0 := mul_ne_zero hΨ0 hq0
  have hnΨ : (dvSideSet F Ψ L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hΨ0 L.u L.hℓ
  have hnq : (dvSideSet F q L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hq0 L.u L.hℓ
  have hnprod : (dvSideSet F (Ψ * q) L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hprod0 L.u L.hℓ
  obtain ⟨MΨ, hpΨ⟩ := exists_pin F hnΨ
  obtain ⟨Mq, hpq⟩ := exists_pin F hnq
  obtain ⟨Mprod, hpprod⟩ := exists_pin F hnprod
  have hie : dvResPoly F H₀ hpin g L.u L.ℓ hng Mg hpg
      = dvResPoly F H₀ hpin (Ψ * q) L.u L.ℓ hnprod Mprod hpprod :=
    dvResPoly_eq_of_muEquiv L hπ heq hng hnprod hpg hpprod
  have hmul := C133mh3.dvResPoly_mul_gen hπ hh H₀ hpin L.hℓ L.hcop
    (inner_floor L) hΨ0 hq0 hnΨ hnq hnprod hpΨ hpq hpprod
  apply hnd
  refine ⟨dvResPoly F H₀ hpin q L.u L.ℓ hnq Mq hpq, ?_⟩
  rw [hie, hmul, dvResPoly_testKey hπ L hΨ hnΨ MΨ hpΨ]

/-- P2 specialized to the complement supplied by signed F1.2. -/
theorem block_complement_not_muDvd (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hh : 0 < F.h) {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ)
    (hctx : BlockContext L f) :
    ¬ MuDvd L Ψ (f /ₘ blockFactor L f) := by
  have hres := (C134f12c.block_complement_notdvd L hπ hh hctx).2.1
  have hq0 : f /ₘ blockFactor L f ≠ 0 := by
    intro h0
    apply C134frt.quotient_dvSupp_ne_top L hπ hh hctx
    rw [h0]
    exact C130s6.dvSupp_zero_eq_top F L.u L.hℓ
  have hne : (dvSideSet F (f /ₘ blockFactor L f) L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hq0 L.u L.hℓ
  obtain ⟨M, hp⟩ := exists_pin F hne
  exact not_muDvd_of_residual_notdvd L hπ hh hΨ hne M hp (hres hne M hp)

end Uniformity.Density.Tower.C134p1

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C134p1.dvResPoly_eq_of_muEquiv
#print axioms Uniformity.Density.Tower.C134p1.not_muDvd_of_residual_notdvd
#print axioms Uniformity.Density.Tower.C134p1.block_complement_not_muDvd

end AxCheck
