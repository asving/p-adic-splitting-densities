/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.Classifier
import LeanUrat.OM.Order0Hull

/-!
# Order0Root — the γ2/γ3 root-data identification on the generic stratum
(`notes/HNODE0_BLUEPRINT.md` §1, nodes γ2 and γ3)

**Setting.** `f : QuotientBox.monicBox p N n` (monic degree-`n` box polynomial mod `p^N`, `0 < N`)
on the GENERIC STRATUM: unit constant coefficient, i.e.
`hunit : PadicLift.zmodValuation p N (f.coeff 0) = 0`, and `0 < n`.

**Results.**
1. Support facts: `(0, 0)` and `(n, 0)` lie in the box valuation support `B.boxValSupport p N f`,
   and every support abscissa is `≤ n` (`zero_zero_mem_boxValSupport`, `n_zero_mem_boxValSupport`,
   `boxValSupport_fst_le`).
2. **γ2** — the selected order-0 side is the flat side
   (`rootSide_eq_flat : B.rootSide p N hN f = some ⟨0, n, 0, 0⟩`), hence the root lattice face is
   the flat face (`rootFace_eq_flatFace`). NOTE: `⟨0, n, 0, 0⟩` is DEFINITIONALLY `flatSide n` of
   `Order0Capstone.lean` (and `M7.toSideFace ⟨0, n, 0, 0⟩` is definitionally `flatFace n`); the
   names themselves live in `Order0Capstone`, which is NOT imported here (it sits downstream of
   this module in the blueprint DAG), so the statements use the literal — downstream composes by
   `rfl`-unfolding `flatSide`/`flatFace`.
3. **γ3** — on the flat side the D7-FIXED `boxCoeffData` residual is EXACTLY the plain mod-`p`
   reduction: `rootResidual_eq_reduction : B.rootResidual p N hN f =
   (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))`. Per-coefficient heart:
   `valuation_ite_eq_castHom` — the on-side-guarded unit residue at height `0` is the residue-field
   projection `ZMod (p^N) →+* ZMod p` (valuation-`0` coefficients keep their unit part `= x.val
   mod p`; higher-valuation or zero coefficients are sent to `0` on both sides).
4. Consequences: `rootResidual_natDegree`, and the `fRootCtx` field reads `fRootCtx_dr`,
   `fRootCtx_Rr`, `fRootCtx_Nr`.

All sorry-free; footprint `[propext, Classical.choice, Quot.sound]` (the Classifier CITE axiom is
NOT used).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.Order0

open Polynomial
open scoped Classical

/-! ## 1. Support facts for the generic stratum -/

/-- **1a.** On the generic stratum the dot `(0, 0)` is in the box valuation support: the constant
coefficient has valuation `0`, hence is nonzero (`zmodValuation 0 = N > 0`), so `0 ∈ f.support`
and its decorated image is `(0, 0)` by `hunit`. -/
theorem zero_zero_mem_boxValSupport (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n)
    (hunit : PadicLift.zmodValuation p N ((f.1).coeff 0) = 0) :
    ((0 : ℕ), (0 : ℕ)) ∈ B.boxValSupport p N f := by
  have hc0 : (f.1).coeff 0 ≠ 0 := by
    intro h
    rw [h, PadicLift.zmodValuation_zero] at hunit
    omega
  unfold LeanUrat.OM.B.boxValSupport
  exact Finset.mem_image.mpr ⟨0, Polynomial.mem_support_iff.mpr hc0, by rw [hunit]⟩

/-- **1b.** The dot `(n, 0)` is in the box valuation support: `f` is monic of degree `n`, so
`f.coeff n = 1`, which is nonzero (`1 < p^N`) of valuation `0` (`val 1 = 1`,
`Nat.factorization 1 = 0`). -/
theorem n_zero_mem_boxValSupport (p : ℕ) [hp : Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) :
    ((n : ℕ), (0 : ℕ)) ∈ B.boxValSupport p N f := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  haveI : Nontrivial (QuotientBox.ResidueRing p N) := ZMod.nontrivial _
  have hcn : (f.1).coeff n = 1 := by
    have h := f.2.1.coeff_natDegree
    rwa [f.2.2] at h
  have hne : (f.1).coeff n ≠ 0 := by rw [hcn]; exact one_ne_zero
  have hval : PadicLift.zmodValuation p N ((f.1).coeff n) = 0 := by
    rw [hcn, PadicLift.zmodValuation_of_ne_zero p one_ne_zero, ZMod.val_one]
    simp
  unfold LeanUrat.OM.B.boxValSupport
  exact Finset.mem_image.mpr ⟨n, Polynomial.mem_support_iff.mpr hne, by rw [hval]⟩

/-- **1c.** Every abscissa of the box valuation support is `≤ n` (support ⊆ degrees ≤ natDegree). -/
theorem boxValSupport_fst_le (p : ℕ) [Fact p.Prime] (n N : ℕ)
    (f : QuotientBox.monicBox p N n) :
    ∀ P ∈ B.boxValSupport p N f, P.1 ≤ n := by
  intro P hP
  unfold LeanUrat.OM.B.boxValSupport at hP
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
  simpa [f.2.2] using Polynomial.le_natDegree_of_mem_supp i hi

/-! ## 2. γ2 — the selected order-0 side and face are flat -/

/-- **γ2 (`HNODE0_BLUEPRINT` §1).** On the generic stratum the selected order-0 side is the FLAT
side `⟨0, n, 0, 0⟩` (definitionally `flatSide n` of `Order0Capstone`): the valuation support
contains `(0, 0)` and `(n, 0)` with all abscissae `≤ n`, so `npSides_of_flat` collapses the side
list to the singleton flat side, and `head?` selects it. -/
theorem rootSide_eq_flat (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (f : QuotientBox.monicBox p N n)
    (hunit : PadicLift.zmodValuation p N ((f.1).coeff 0) = 0) :
    B.rootSide p N hN f = some (⟨0, n, 0, 0⟩ : NewtonPolygon.Side) := by
  unfold LeanUrat.OM.B.rootSide
  rw [npSides_of_flat (B.boxValSupport p N f) (B.boxValSupport_nonempty p N hN f) n hn
      (zero_zero_mem_boxValSupport p n N hN f hunit)
      (n_zero_mem_boxValSupport p n N hN f)
      (boxValSupport_fst_le p n N f)]
  rfl

/-- **γ2, face form.** The root lattice face on the generic stratum is the flat face
`M7.toSideFace ⟨0, n, 0, 0⟩` (definitionally `flatFace n` of `Order0Capstone`). -/
theorem rootFace_eq_flatFace (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (f : QuotientBox.monicBox p N n)
    (hunit : PadicLift.zmodValuation p N ((f.1).coeff 0) = 0) :
    B.rootFace p N hN f = M7.toSideFace (⟨0, n, 0, 0⟩ : NewtonPolygon.Side) := by
  unfold LeanUrat.OM.B.rootFace
  rw [rootSide_eq_flat p n N hN hn f hunit]

/-! ## 3. γ3 — the flat-side residual is the plain mod-`p` reduction -/

/-- **The per-coefficient heart of γ3.** For any `x : ZMod (p^N)`, the on-side-guarded unit
residue at height `0` — `if v(x) = 0 then unitRes(x) else 0` — is exactly the residue-field
projection `ZMod.castHom : ZMod (p^N) →+* ZMod p` of `x`:
* `x = 0`: valuation is `N ≠ 0`, both sides are `0`;
* `v(x) = 0`: `ordCompl[p] x.val = x.val / p^0 = x.val`, and `castHom x = (x.val : ZMod p)`;
* `v(x) > 0`: `p ∣ x.val` (`Nat.dvd_of_factorization_pos`), so `castHom x = (x.val : ZMod p) = 0`,
  matching the guard's `0`. -/
theorem valuation_ite_eq_castHom (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N)
    (x : ZMod (p ^ N)) :
    (if (PadicLift.zmodValuation p N x : ℤ) = 0 then PadicLift.zmodUnitResidue p N x else 0)
      = ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p) x := by
  haveI : NeZero (p ^ N) := QuotientBox.instNeZeroPow p N
  by_cases hx0 : x = 0
  · subst hx0
    rw [PadicLift.zmodValuation_zero, if_neg (by exact_mod_cast hN.ne'), map_zero]
  · rw [PadicLift.zmodValuation_of_ne_zero p hx0, ZMod.castHom_apply, ← ZMod.natCast_val x]
    by_cases hv : (x.val).factorization p = 0
    · rw [if_pos (by exact_mod_cast hv), PadicLift.zmodUnitResidue, hv, pow_zero, Nat.div_one]
    · rw [if_neg (by exact_mod_cast hv)]
      exact ((ZMod.natCast_eq_zero_iff x.val p).mpr (Nat.dvd_of_factorization_pos hv)).symm

/-- On the FLAT side the D7-fixed `boxCoeffData` reads the plain column `t` at height `0`:
`i₀ = 0`, `e = 1` (`flatSide_e`), `v₀ = 0`, `h = 0` (`flatSide_h`), so the datum is
`if v(f.coeff t) = 0 then unitRes(f.coeff t) else 0`. -/
theorem boxCoeffData_flatSide (p : ℕ) [Fact p.Prime] (n N : ℕ)
    (f : QuotientBox.monicBox p N n) (t : ℕ) :
    B.boxCoeffData p N (⟨0, n, 0, 0⟩ : NewtonPolygon.Side) f t
      = if (PadicLift.zmodValuation p N ((f.1).coeff t) : ℤ) = 0
        then PadicLift.zmodUnitResidue p N ((f.1).coeff t) else 0 := by
  have he : (⟨0, n, 0, 0⟩ : NewtonPolygon.Side).e = 1 := flatSide_e n
  have hh : (⟨0, n, 0, 0⟩ : NewtonPolygon.Side).h = 0 := flatSide_h n
  simp only [B.boxCoeffData, he, hh, mul_one, mul_zero, zero_add, add_zero, Nat.cast_zero]

/-- **γ3 residual form.** The flat-side residual polynomial of the D7-fixed datum is EXACTLY the
mod-`p` reduction of `f`: coefficientwise, `residualPoly_coeff` + `flatSide_residualDeg` gives the
guarded datum for `j ≤ n` (which is `castHom (f.coeff j)` by `valuation_ite_eq_castHom`), and for
`j > n` both sides vanish (`natDegree f = n`). -/
theorem residualPoly_flat_eq_reduction (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) :
    M4.residualPoly (B.boxCoeffData p N (⟨0, n, 0, 0⟩ : NewtonPolygon.Side) f)
        (⟨0, n, 0, 0⟩ : NewtonPolygon.Side)
      = (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) := by
  ext j
  rw [M4.residualPoly_coeff, Polynomial.coeff_map, flatSide_residualDeg]
  by_cases hj : j ≤ n
  · rw [if_pos hj, boxCoeffData_flatSide p n N f j]
    exact valuation_ite_eq_castHom p N hN ((f.1).coeff j)
  · rw [if_neg hj]
    have hc : (f.1).coeff j = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [f.2.2]; omega)
    rw [hc, map_zero]

/-- **γ3 (`HNODE0_BLUEPRINT` §1, the heart).** On the generic stratum the order-0 root residual is
the PLAIN mod-`p` reduction of `f`: the selected side is flat (γ2), on it the D7-fixed datum is the
reduction (`residualPoly_flat_eq_reduction`), and the `≤ n` degree guard KEEPS the branch since the
reduction of a monic degree-`n` polynomial has `natDegree = n` (`Monic.natDegree_map`). -/
theorem rootResidual_eq_reduction (p : ℕ) [hp : Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (f : QuotientBox.monicBox p N n)
    (hunit : PadicLift.zmodValuation p N ((f.1).coeff 0) = 0) :
    B.rootResidual p N hN f
      = (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) := by
  have hdeg : ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))).natDegree = n := by
    rw [f.2.1.natDegree_map]
    exact f.2.2
  unfold LeanUrat.OM.B.rootResidual
  rw [rootSide_eq_flat p n N hN hn f hunit]
  simp only [residualPoly_flat_eq_reduction p n N hN f]
  rw [if_pos (le_of_eq hdeg)]

/-! ## 4. Degree and `fRootCtx` field consequences -/

/-- **The generic-stratum root residual has full degree `n`** (γ3 + `Monic.natDegree_map`). -/
theorem rootResidual_natDegree (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (f : QuotientBox.monicBox p N n)
    (hunit : PadicLift.zmodValuation p N ((f.1).coeff 0) = 0) :
    (B.rootResidual p N hN f).natDegree = n := by
  rw [rootResidual_eq_reduction p n N hN hn f hunit, f.2.1.natDegree_map]
  exact f.2.2

/-- `fRootCtx.dr = n` on the generic stratum (definitional from `dr := Rr.natDegree` + γ3). -/
theorem fRootCtx_dr (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (f : QuotientBox.monicBox p N n)
    (hunit : PadicLift.zmodValuation p N ((f.1).coeff 0) = 0) :
    (B.fRootCtx p N hN f).dr = n :=
  rootResidual_natDegree p n N hN hn f hunit

/-- `fRootCtx.Rr` is the plain mod-`p` reduction of `f` on the generic stratum (γ3, field form). -/
theorem fRootCtx_Rr (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (f : QuotientBox.monicBox p N n)
    (hunit : PadicLift.zmodValuation p N ((f.1).coeff 0) = 0) :
    (B.fRootCtx p N hN f).Rr
      = (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) :=
  rootResidual_eq_reduction p n N hN hn f hunit

/-- `fRootCtx.Nr` is the flat face on the generic stratum (γ2, field form). -/
theorem fRootCtx_Nr (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (f : QuotientBox.monicBox p N n)
    (hunit : PadicLift.zmodValuation p N ((f.1).coeff 0) = 0) :
    (B.fRootCtx p N hN f).Nr = M7.toSideFace (⟨0, n, 0, 0⟩ : NewtonPolygon.Side) :=
  rootFace_eq_flatFace p n N hN hn f hunit

end LeanUrat.OM.Order0
