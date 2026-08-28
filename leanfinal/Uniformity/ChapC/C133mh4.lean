/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C133mh0
import Uniformity.ChapC.C35
import Uniformity.ChapB.B13a

/-!
# Uniformity.ChapC.C133mh4 — `[MH4 2026-08-28]`: Corollary M-monic (the monic-residual law)

**Node MH.4** (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §3.5, §9's node table row
MH.4). **B.41's `hcu1` twin**, one level up: for a monic `(u,ℓ)`-pure `g` with
`D′ := F.e₁ * F.f₁` dividing `g.natDegree`, the left height pin reads
`M₀ = u · dvSideDeg F g u ℓ hne` (the polygon runs from `(0, u·d)` to `(ℓ·d, 0)`), and the
level residual `dvResPoly F H₀ hpin g u ℓ hne M₀ hp` is itself **MONIC**. This is what lets
Theorem A (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §2) take `hprod : R(g) = G * H`
with `G H` monic and no leftover unit, exactly as B.41b's `hcu1` step does one level down
(`Uniformity/ChapB/B41b.lean:234`, `hcu1 : (cu : resField φ) = 1`).

## The route

Order-0's `IsPure` packages both endpoint conditions as raw `OnSide` equations
(`B34.IsPure`), so `suppVal_of_pure`/`height_eq_of_pure` (`B35b`/`B35c`) read the pin
straight off. The order-1 `IsDvPure` (C.29) instead packages both endpoints as **Finset
membership** (`0 ∈ dvSideSet`, `deg g / D′ ∈ dvSideSet`) — the extra finiteness conjunct
that `DvOnSide` carries and `OnSide` does not (C.07's docstring) — so the raw on-side
equations must first be extracted via `dvOnSide_of_mem_dvSideSet` (C.35). Given those two
equations, the proof mirrors B.35c's `height_eq_of_pure` verbatim in shape:

1. `dvSideMin F g u ℓ hne = 0` (`dvSideMin_eq_zero_of_isDvPure`, C.35);
2. `dvSideMax F g u ℓ hne = g.natDegree / D′ = ℓ · dvSideDeg` (`dvSideMax_eq_of_isDvPure` +
   `natDegree_div_eq_of_isDvPure`, C.35), hence `g.natDegree = dvSideMax · F.key.natDegree`;
3. **the top digit is `1`**: `dev F.key g dvSideMax = 1` (`dev_top`, B.13a — the
   Monic-fenced input this node is keyed on), so `dvHgt F g dvSideMax = F.stageHeight 1 = 0`
   (`stageHeight_one`, C131ae — MH.0c's neighbourhood; not itself an MH.0c clause but the
   same C.02 dictionary);
4. combining the two on-side equations at `j = 0` and `j = dvSideMax` in `ℕ∞`, clearing the
   `ℓ`-scaling, gives `M₀ = u · dvSideDeg` (`dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure`);
5. the level residual's degree is `dvSideDeg` and its leading slot digit is the twist-read
   of the top development coefficient at height `M₀ − u·dvSideDeg = 0` of the digit `1`,
   which is `1` by `twistRead_one` (C133mh0's MH.0c remainder) — hence `dvResPoly … .Monic`
   (`dvResPoly_monic_of_isDvPure`), unfolding `Polynomial.Monic`/`leadingCoeff` exactly as
   B.41b's `hRfmonic` does at order 0.

Unlike the pre-MHFIX design document, this corollary carries **no separate `τ = 1`-on-a-fence
claim**: Theorem M's clause 3 (`C133mh3.dvResPoly_mul_gen`) is already `τ = 1` identically for
ALL nonzero inputs, so MH.4's role is exactly the monicity/value pair proved here (the
`[MHFIX 2026-08-27]` note at the end of doc §3.5). Consequently this file does not import or
consume `C133mh3` — the corollary is a fact about a single polynomial `g`, not a product.

## DEPENDS

C133mh0 (`twistRead_one`, MH.0c remainder) · C35 (`IsDvPure`, `dvSideMin_eq_zero_of_isDvPure`,
`dvSideMax_eq_of_isDvPure`, `natDegree_div_eq_of_isDvPure`, `dvOnSide_of_mem_dvSideSet`;
transitively C.26 `natDegree_dvResPoly`, C.25 `dvResPoly`, C.29 `IsDvPure`) · C131ae
(`stageHeight_one`, transitively via C133mh0) · B.13a (`dev_top`) · `Uniformity.Hensel`
(`coeff_sum_range_C_mul_X_pow`, transitively imported).

## Status

Sorry-free, zero new axiom, footprint Lean-core only (AxCheck footer).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C133mh4

open Polynomial Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131ae (stageHeight_one)
open Uniformity.Density.Tower.C133mh0 (twistRead_one)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 1 — the height pin `M₀ = u · dvSideDeg` -/

set_option linter.unusedVariables false in
/-- ★ **MH.4, clause 1.** For monic `(u,ℓ)`-pure `g` with `D′ ∣ deg g`, the left-side pin
`M₀` (the height of `g`'s development at `dvSideMin = 0`) reads `u · dvSideDeg`: the
`(u,ℓ)`-polygon of `g` runs from `(0, u·d)` down to `(ℓ·d, 0)`. -/
theorem dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure
    (F : KeyFrame O π) {g : Polynomial O} (hg : g.Monic) (hgpos : 0 < g.natDegree)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hpure : IsDvPure F g u ℓ) (hfd : F.e₁ * F.f₁ ∣ g.natDegree)
    (hne : (dvSideSet F g u ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞)) :
    M₀ = u * dvSideDeg F g u ℓ hne := by
  have hmin0 : dvSideMin F g u ℓ hne = 0 := dvSideMin_eq_zero_of_isDvPure hpure hne
  have hmaxeq : dvSideMax F g u ℓ hne = g.natDegree / (F.e₁ * F.f₁) :=
    dvSideMax_eq_of_isDvPure hpure hne
  have hdegdiv : g.natDegree / (F.e₁ * F.f₁) = ℓ * dvSideDeg F g u ℓ hne :=
    natDegree_div_eq_of_isDvPure hℓ hcop hpure hne
  have hmax_eq2 : dvSideMax F g u ℓ hne = ℓ * dvSideDeg F g u ℓ hne := hmaxeq.trans hdegdiv
  have hdeg_eq : g.natDegree = dvSideMax F g u ℓ hne * F.key.natDegree := by
    rw [hmaxeq, F.hdeg]; exact (Nat.div_mul_cancel hfd).symm
  have htopdig : dev F.key g (dvSideMax F g u ℓ hne) = 1 :=
    dev_top F.hmonic F.natDegree_key_pos hg hdeg_eq
  have hdvHgtmax : dvHgt F g (dvSideMax F g u ℓ hne) = (0 : ℕ∞) := by
    rw [dvHgt, htopdig]; exact stageHeight_one F
  have hminmem : dvSideMin F g u ℓ hne ∈ dvSideSet F g u ℓ := Finset.min'_mem _ hne
  have hmaxmem : dvSideMax F g u ℓ hne ∈ dvSideSet F g u ℓ := Finset.max'_mem _ hne
  have honmin : DvOnSide F g u ℓ (dvSideMin F g u ℓ hne) := dvOnSide_of_mem_dvSideSet hminmem
  have honmax : DvOnSide F g u ℓ (dvSideMax F g u ℓ hne) := dvOnSide_of_mem_dvSideSet hmaxmem
  have hs0 : dvSupp F g u ℓ = ((ℓ * M₀ : ℕ) : ℕ∞) := by
    have h1 := honmin.1
    rw [hp, hmin0] at h1
    simpa [nsmul_eq_mul] using h1
  have hsmax : dvSupp F g u ℓ = ((u * (ℓ * dvSideDeg F g u ℓ hne) : ℕ) : ℕ∞) := by
    have h2 := honmax.1
    rw [hdvHgtmax, hmax_eq2] at h2
    simpa [nsmul_eq_mul] using h2
  have hnat : ℓ * M₀ = u * (ℓ * dvSideDeg F g u ℓ hne) := by
    exact_mod_cast hs0.symm.trans hsmax
  have hcalc : ℓ * M₀ = ℓ * (u * dvSideDeg F g u ℓ hne) := by rw [hnat]; ring
  exact Nat.eq_of_mul_eq_mul_left hℓ hcalc

/-! ## Part 2 — the monic-residual law -/

set_option linter.unusedVariables false in
/-- ★ **MH.4, clause 2 (the corollary's headline).** For monic `(u,ℓ)`-pure `g` with
`D′ ∣ deg g`, the level residual `dvResPoly F H₀ hpin g u ℓ hne M₀ hp` is itself `Monic`.
B.41's `hcu1` twin, one level up: this is what lets Theorem A take `hprod` without a unit. -/
theorem dvResPoly_monic_of_isDvPure
    (F : KeyFrame O π) (hπ : Irreducible π) (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne)
      = (H₀ : ℕ∞))
    {g : Polynomial O} (hg : g.Monic) (hgpos : 0 < g.natDegree)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hpure : IsDvPure F g u ℓ) (hfd : F.e₁ * F.f₁ ∣ g.natDegree)
    (hne : (dvSideSet F g u ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞)) :
    (dvResPoly F H₀ hpin g u ℓ hne M₀ hp).Monic := by
  have hM0 : M₀ = u * dvSideDeg F g u ℓ hne :=
    dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure F hg hgpos hℓ hcop hpure hfd hne hp
  have hmin0 : dvSideMin F g u ℓ hne = 0 := dvSideMin_eq_zero_of_isDvPure hpure hne
  have hmaxeq : dvSideMax F g u ℓ hne = g.natDegree / (F.e₁ * F.f₁) :=
    dvSideMax_eq_of_isDvPure hpure hne
  have hdegdiv : g.natDegree / (F.e₁ * F.f₁) = ℓ * dvSideDeg F g u ℓ hne :=
    natDegree_div_eq_of_isDvPure hℓ hcop hpure hne
  have hmax_eq2 : dvSideMax F g u ℓ hne = ℓ * dvSideDeg F g u ℓ hne := hmaxeq.trans hdegdiv
  have hdeg_eq : g.natDegree = dvSideMax F g u ℓ hne * F.key.natDegree := by
    rw [hmaxeq, F.hdeg]; exact (Nat.div_mul_cancel hfd).symm
  have htopdig : dev F.key g (dvSideMax F g u ℓ hne) = 1 :=
    dev_top F.hmonic F.natDegree_key_pos hg hdeg_eq
  have hnd : (dvResPoly F H₀ hpin g u ℓ hne M₀ hp).natDegree = dvSideDeg F g u ℓ hne :=
    (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).1
  have habsc : dvSideMin F g u ℓ hne + dvSideDeg F g u ℓ hne * ℓ = dvSideMax F g u ℓ hne := by
    rw [hmin0, hmax_eq2]; ring
  have hsub0 : M₀ - dvSideDeg F g u ℓ hne * u = 0 := by
    have he : dvSideDeg F g u ℓ hne * u = M₀ := by rw [hM0]; ring
    rw [he]; exact Nat.sub_self _
  show (dvResPoly F H₀ hpin g u ℓ hne M₀ hp).coeff
      (dvResPoly F H₀ hpin g u ℓ hne M₀ hp).natDegree = 1
  rw [hnd, dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
    if_pos (Nat.lt_succ_self _), habsc, htopdig, hsub0]
  exact twistRead_one F H₀ hpin hh

end Uniformity.Density.Tower.C133mh4

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh4.dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure
#print axioms Uniformity.Density.Tower.C133mh4.dvResPoly_monic_of_isDvPure

end AxCheck
