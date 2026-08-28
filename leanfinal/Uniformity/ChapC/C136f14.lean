/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136l2e3

/-!
# Uniformity.ChapC.C136f14 — UNIT A24A: the F1.4/C.39 scalar-shape diagnostics
[A24A 2026-08-28]

**This file does NOT land the signed F1.4/C.39 `dv2ResPoly_scalar`, and no leanspec
statement was re-signed by this unit.**  It is the machine-evidence record for the A24A
adjudication (`runs/wave-c/verdict_A24A.md`): BOTH candidate conclusions for C.39 — the
SIGNED one (scalar `γg · root^cocycle`) and the drafted A-C.24 repair (scalar `γg` alone)
— are stated over the UNGUARDED `dv2ResPoly`, whose lattice-slot coefficients are the
per-digit `dv2Res` reads at the digit's OWN height.  Unlike the level-1 `dvResPoly`
(C.25: fixed-grade `twistRead (M₀ - t*u)`; C.26: coefficient `= 0` iff the slot is
off-side), the level-2 assembly carries no off-side junk-`0` guard, so an off-side
lattice slot contributes the digit's own nonzero residual read.

## The diagnostics

* ★ `dv2ResPoly_scalar_shape_digit_kill` — SCALAR-GENERIC: if
  `dv2ResPoly f = C c * dv2ResPoly (blockFactor f)` holds for ANY constant
  `c : AdjoinRoot L.r`, then at every in-range lattice slot where the block's `Ψ`-digit
  vanishes, the product's `Ψ`-digit is forced to vanish too.  (The root-power factor of
  the signed row cannot rescue the shape: `c * 0 = 0` for every `c`.)
* `digit_kill_of_normalized_scalar_shape` / `digit_kill_of_signed_scalar_shape` — the two
  named instantiations (drafted A-C.24 scalar; signed C.39 scalar).
* `dev_witness_block_digit_zero` + `dev_witness_product_digit_one` — the vanishing
  transfer is FALSE for polynomial multiplication as a mechanism: for any monic `Ψ` of
  positive degree, `b := Ψ² + X^(deg Ψ - 1)` has `dev Ψ b 1 = 0` while
  `dev Ψ (b * X) 1 = 1`.  (A fully in-frame counterexample additionally needs a
  `BlockContext` instance with this digit shape; the two witnesses isolate the abstract
  mechanism the row's hypotheses do not constrain.)

## Supporting bank

* `dv2Res_zero` — the coherent read of `0` is junk `0` (the `dif` guard fails).
* `dv2Res_ne_zero_of_ne_zero_of_natDegree_lt` — every NONZERO polynomial short of the
  recipe degree has a nonzero coherent read (public re-derivation of `C136l2e1`'s private
  `dv2Res_ne_zero_of_natDegree_lt_keyDeg`, generalized from a finite-height hypothesis to
  bare nonvanishing; mechanism credit: C136l2e1 / `C134p1d.not_residual_dvd_of_natDegree_lt`).

No landed or leanspec file is edited; no signed name is declared; nothing here is
S2-special.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136f14

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C132nv2 Uniformity.Density.Tower.C134dv2g
open Uniformity.Density.Tower.C136l2e3

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## The supporting bank -/

/-- The coherent read of `0` is the junk value `0`: the zero polynomial has no pinned
level-1 side, so `dv2Res`'s guard fails. -/
theorem dv2Res_zero (L : LevelDatum F H₀ hpin) : dv2Res L (0 : Polynomial O) = 0 := by
  classical
  have hnex : ¬ ∃ (hne : (dvSideSet F (0 : Polynomial O) L.u L.ℓ).Nonempty) (M₀ : ℕ),
      dvHgt F (0 : Polynomial O) (dvSideMin F 0 L.u L.ℓ hne) = (M₀ : ℕ∞) := by
    rintro ⟨hne0, M, hM⟩
    obtain ⟨j, hj⟩ := hne0
    have hon := dvOnSide_of_mem_dvSideSet hj
    have h1 := hon.1
    rw [dvSupp_zero_eq_top F L.u L.hℓ] at h1
    obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.1 hon.2
    rw [← hHj] at h1
    have hfin : L.ℓ • ((Hj : ℕ) : ℕ∞) + (L.u * j : ℕ∞)
        = ((L.ℓ * Hj + L.u * j : ℕ) : ℕ∞) := by
      push_cast [nsmul_eq_mul]
      ring
    rw [hfin] at h1
    exact (ENat.coe_ne_top _) h1.symm
  rw [dv2Res, dif_neg hnex]

/-- Every nonzero polynomial short of the level recipe degree has a NONZERO coherent
read: its level residual cannot be `L.r`-divisible (public re-derivation of
`C136l2e1.dv2Res_ne_zero_of_natDegree_lt_keyDeg`, generalized to a bare `A ≠ 0`). -/
theorem dv2Res_ne_zero_of_ne_zero_of_natDegree_lt (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) {A : Polynomial O} (hA : A ≠ 0)
    (hdeg : A.natDegree < L.keyDeg₂) : dv2Res L A ≠ 0 := by
  classical
  have hne : (dvSideSet F A L.u L.ℓ).Nonempty := dvSideSet_nonempty F hA L.u L.hℓ
  have hon := dvOnSide_dvSideMin F A L.u L.ℓ hne
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1 hon.2
  let hex : ∃ (hne' : (dvSideSet F A L.u L.ℓ).Nonempty) (M' : ℕ),
      dvHgt F A (dvSideMin F A L.u L.ℓ hne') = (M' : ℕ∞) := ⟨hne, M, hM.symm⟩
  rw [dv2Res, dif_pos hex]
  intro hzero
  exact (C134p1d.not_residual_dvd_of_natDegree_lt L hπ hdeg
    hex.choose hex.choose_spec.choose hex.choose_spec.choose_spec)
    (AdjoinRoot.mk_eq_zero.mp hzero)

/-! ## The scalar-generic digit-kill diagnostic -/

/-- ★ **The scalar-shape digit kill (A24A).**  If the two unguarded level-2 residual
polynomials of `f` and its block factor are proportional by ANY constant
`c : AdjoinRoot L.r`, then at every in-range lattice slot at which the block's `Ψ`-digit
vanishes, `f`'s own `Ψ`-digit is forced to vanish.  This consequence is not supplied by
any hypothesis of the signed C.39 row (the row does not constrain off-side interior
digits), and the companion witnesses below show the transfer is false for polynomial
multiplication as a mechanism.  Both the SIGNED C.39 scalar and the drafted A-C.24
scalar are instances (`digit_kill_of_signed_scalar_shape`,
`digit_kill_of_normalized_scalar_shape`). -/
theorem dv2ResPoly_scalar_shape_digit_kill (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) {Ψ f : Polynomial O} (hΨ : IsTestKey L Ψ)
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty)
    {c : AdjoinRoot L.r}
    (hLaw : dv2ResPoly L Ψ f u₂ ℓ₂ hne
      = Polynomial.C c * dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne')
    {t : ℕ} (htf : t ≤ dv2SideDeg L Ψ f u₂ ℓ₂ hne)
    (htb : t ≤ dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne')
    (hbz : dev Ψ (blockFactor L f)
      (dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne' + t * ℓ₂) = 0) :
    dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂) = 0 := by
  have hcoeff : (dv2ResPoly L Ψ f u₂ ℓ₂ hne).coeff t
      = (Polynomial.C c * dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne').coeff t := by
    rw [hLaw]
  rw [dv2ResPoly_coeff_of_le L hne htf, Polynomial.coeff_C_mul,
    dv2ResPoly_coeff_of_le L hne' htb, hbz, dv2Res_zero, mul_zero] at hcoeff
  by_contra hfz
  have hdeg : (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)).natDegree < L.keyDeg₂ := by
    have h := natDegree_dev_lt hΨ.1 (C134p1d.natDegree_pos_of_isTestKey L hΨ) f
      (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)
    rwa [hΨ.2.1] at h
  exact dv2Res_ne_zero_of_ne_zero_of_natDegree_lt L hπ hfz hdeg hcoeff

/-- The digit kill at the drafted A-C.24 conclusion (`γg` alone). -/
theorem digit_kill_of_normalized_scalar_shape (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) {Ψ f : Polynomial O} (hΨ : IsTestKey L Ψ)
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty)
    (hLaw : dv2ResPoly L Ψ f u₂ ℓ₂ hne
      = Polynomial.C (γg L f) * dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne')
    {t : ℕ} (htf : t ≤ dv2SideDeg L Ψ f u₂ ℓ₂ hne)
    (htb : t ≤ dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne')
    (hbz : dev Ψ (blockFactor L f)
      (dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne' + t * ℓ₂) = 0) :
    dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂) = 0 :=
  dv2ResPoly_scalar_shape_digit_kill L hπ hΨ hne hne' hLaw htf htb hbz

/-- The digit kill at the SIGNED C.39 conclusion (`γg · root^cocycle`): the root-power
factor does not rescue the shape — the off-side channel refutes it independently of the
L2E1/L2E3 `root^cocycle = 1` obstruction. -/
theorem digit_kill_of_signed_scalar_shape (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) {Ψ f : Polynomial O} (hΨ : IsTestKey L Ψ)
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty)
    (hLaw : dv2ResPoly L Ψ f u₂ ℓ₂ hne
      = Polynomial.C (γg L f * (AdjoinRoot.root L.r)
            ^ (L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne')
                (complementConst L f)))
          * dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne')
    {t : ℕ} (htf : t ≤ dv2SideDeg L Ψ f u₂ ℓ₂ hne)
    (htb : t ≤ dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne')
    (hbz : dev Ψ (blockFactor L f)
      (dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne' + t * ℓ₂) = 0) :
    dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂) = 0 :=
  dv2ResPoly_scalar_shape_digit_kill L hπ hΨ hne hne' hLaw htf htb hbz

/-! ## The mechanism witnesses

The digit-vanishing transfer forced above is false for polynomial multiplication: for
any monic `Ψ` of positive degree, the block-shaped `b := Ψ² + X^(deg Ψ - 1)` has a
vanishing slot-1 digit, while `b * X` has slot-1 digit `1`. -/

/-- The block-shaped witness `b = Ψ² + X^(deg Ψ - 1)` has vanishing slot-1 `Ψ`-digit. -/
theorem dev_witness_block_digit_zero {Ψ : Polynomial O} (hΨm : Ψ.Monic)
    (hd : 0 < Ψ.natDegree) :
    dev Ψ (Ψ ^ 2 + Polynomial.X ^ (Ψ.natDegree - 1)) 1 = 0 := by
  rw [dev_add_of_monic hΨm]
  have h1 : dev Ψ (Ψ ^ 2) 1 = 0 := by
    have h := dev_mul_pow_of_lt hΨm 2 (1 : Polynomial O) 1 (by omega)
    rwa [one_mul] at h
  have h2 : dev Ψ (Polynomial.X ^ (Ψ.natDegree - 1)) 1 = 0 := by
    have hstep : dev Ψ (Polynomial.X ^ (Ψ.natDegree - 1)) 1
        = dev Ψ ((Polynomial.X ^ (Ψ.natDegree - 1)) /ₘ Ψ) 0 := rfl
    have hq0 : (Polynomial.X ^ (Ψ.natDegree - 1) : Polynomial O) /ₘ Ψ = 0 := by
      refine (Polynomial.divByMonic_eq_zero_iff hΨm).mpr ?_
      rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hΨm.ne_zero]
      exact_mod_cast (by omega : Ψ.natDegree - 1 < Ψ.natDegree)
    rw [hstep, hq0, dev_of_zero]
  rw [h1, h2, add_zero]

/-- The product `b * X` of the same witness has slot-1 `Ψ`-digit `1 ≠ 0`: the transfer
forced by any constant-scalar `dv2ResPoly` law is absurd as a general mechanism. -/
theorem dev_witness_product_digit_one {Ψ : Polynomial O} (hΨm : Ψ.Monic)
    (hd : 0 < Ψ.natDegree) :
    dev Ψ ((Ψ ^ 2 + Polynomial.X ^ (Ψ.natDegree - 1)) * Polynomial.X) 1 = 1 := by
  have hsplit : (Ψ ^ 2 + Polynomial.X ^ (Ψ.natDegree - 1)) * Polynomial.X
      = Polynomial.X * Ψ ^ 2 + Polynomial.X ^ Ψ.natDegree := by
    have hpow : (Polynomial.X ^ (Ψ.natDegree - 1) : Polynomial O) * Polynomial.X
        = Polynomial.X ^ Ψ.natDegree := by
      rw [← pow_succ]
      congr 1
      omega
    rw [add_mul, hpow, mul_comm (Ψ ^ 2) Polynomial.X]
  rw [hsplit, dev_add_of_monic hΨm]
  have h1 : dev Ψ (Polynomial.X * Ψ ^ 2) 1 = 0 :=
    dev_mul_pow_of_lt hΨm 2 Polynomial.X 1 (by omega)
  have h2 : dev Ψ (Polynomial.X ^ Ψ.natDegree : Polynomial O) 1 = 1 := by
    have hXd : (Polynomial.X ^ Ψ.natDegree : Polynomial O)
        = (Polynomial.X ^ Ψ.natDegree - Ψ) + Ψ := by ring
    rw [hXd, dev_add_of_monic hΨm]
    have hlow : dev Ψ (Polynomial.X ^ Ψ.natDegree - Ψ) 1 = 0 := by
      have hstep : dev Ψ (Polynomial.X ^ Ψ.natDegree - Ψ) 1
          = dev Ψ ((Polynomial.X ^ Ψ.natDegree - Ψ) /ₘ Ψ) 0 := rfl
      have hdeglt : (Polynomial.X ^ Ψ.natDegree - Ψ : Polynomial O).degree < Ψ.degree := by
        have hddeg : (Polynomial.X ^ Ψ.natDegree : Polynomial O).degree = Ψ.degree := by
          rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hΨm.ne_zero]
        have h := Polynomial.degree_sub_lt hddeg
          (Polynomial.monic_X_pow Ψ.natDegree).ne_zero
          (by rw [(Polynomial.monic_X_pow Ψ.natDegree).leadingCoeff, hΨm.leadingCoeff])
        rwa [hddeg] at h
      have hq0 : (Polynomial.X ^ Ψ.natDegree - Ψ : Polynomial O) /ₘ Ψ = 0 :=
        (Polynomial.divByMonic_eq_zero_iff hΨm).mpr hdeglt
      rw [hstep, hq0, dev_of_zero]
    have hself : dev Ψ Ψ 1 = 1 := by
      have hstep : dev Ψ Ψ 1 = dev Ψ (Ψ /ₘ Ψ) 0 := rfl
      have hqq : Ψ /ₘ Ψ = 1 := by
        have h := Polynomial.mul_divByMonic_cancel_left (1 : Polynomial O) hΨm
        rwa [mul_one] at h
      have hone : (1 : Polynomial O) %ₘ Ψ = 1 := by
        refine (Polynomial.modByMonic_eq_self_iff hΨm).mpr ?_
        rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hΨm.ne_zero]
        exact_mod_cast hd
      rw [hstep, hqq, dev_zero_pin, hone]
    rw [hlow, hself, zero_add]
  rw [h1, h2, zero_add]

end Uniformity.Density.Tower.C136f14

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136f14.dv2Res_zero
#print axioms Uniformity.Density.Tower.C136f14.dv2Res_ne_zero_of_ne_zero_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C136f14.dv2ResPoly_scalar_shape_digit_kill
#print axioms Uniformity.Density.Tower.C136f14.digit_kill_of_normalized_scalar_shape
#print axioms Uniformity.Density.Tower.C136f14.digit_kill_of_signed_scalar_shape
#print axioms Uniformity.Density.Tower.C136f14.dev_witness_block_digit_zero
#print axioms Uniformity.Density.Tower.C136f14.dev_witness_product_digit_one

end AxCheck
