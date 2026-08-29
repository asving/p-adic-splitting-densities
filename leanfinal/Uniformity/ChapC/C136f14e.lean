/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136f14d

/-!
# Uniformity.ChapC.C136f14e — UNIT A24F: the CONDITIONAL re-signed C.39 (the
carried-hypothesis composition down to the one open supplier)

The A-C.24″ enactment's Lean leg.  The re-signed C.39 row
(`leanspec/Leanspec/ChapC.lean`, `dv2ResPolyTw_scalar`) is here proved as a THEOREM
conditional on explicitly carried hypotheses, of which the single PROOF-BEARING one is
F14C §2.1's **digit-split convolution supplier** (`hconv` below — byte-shaped as the
premise of `C136f14c.dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution`, instantiated
at the block/complement pair).  The composition chain, all landed Lean-core:

`hconv` → (F14C's assembler) → the weighted convolution → (A24C's ID2 product law
`C136f14d.dv2ResPolyTw_mul_of_weightedConv`) → the twisted product law → (the degree-0
complement collapse, THIS FILE) → **EFF.HE6R1.39's display, the byte-kept scalar
`γ̂_g · root^{c₁(pinHeight, c_g)}`**.

F14C §2.2's "terminal stationarity subgoal" — the obstruction that stopped the enacted
A-C.24′ constant on the untwisted carrier — does NOT appear: it is discharged by the
twist bookkeeping (ID1/ID2), which is the whole content of A-C.24″.

## Carried hypotheses (the honest remainder inventory)

* `hconv` — **THE one open proof obligation** (F14C §2.1): the fixed-grade read of the
  product digit equals the guarded weighted antidiagonal.  Battery-certified at S2
  (8128/8128) and shape-certified at the 𝔽₄ frame through the unreduced level (A24C
  battery Part D).  The intended route (`C132rp5.dev_mul_conv_split_monic` +
  fixed-grade additivity + L2E1/L2E2 strict off-pair and carry pricing +
  `dv2FullRead_modByMonic` + `dv2FullReadCarryLaw`) was attempted and not completed by
  the dedicated unit F14C; it is OUT OF SCOPE here (recorded, not improvised).
* bookkeeping legs, each a C.36/C.37-genre side-geometry fact at the block/complement
  split (open as theorems, none proof-bearing for the scalar mechanism): `hsplit` (the
  exact split, C.35's clause under `BlockContext`), `hM` (pin addition — C.37's
  translation at the side minima), `hdeg`/`hzdeg` (side-degree addition; the complement
  outer side is a POINT), `hpz` (the complement's outer pin is `complementConst`),
  `hγ` (the complement's side-min digit reads as the anchored complement read
  `γgAnch`), `hfS` (the block line floor, GC-1 territory).

## This file

* `γgAnch` — the pin-anchored complement read (leanspec NODE C.39's def, byte-faithful
  twin; not previously landed in `leanfinal`).
* `dv2ResPolyTw_congr`, `dv2Pin_sideMin_congr` — propositional-transport helpers
  (the `dvResPoly_congr` pattern of C136f14c).
* `pinHeight_eq_of_pin` — `pinHeight = M₂'` under the GC-1 pin binder.
* ★★ `dv2ResPolyTw_scalar_of_conv_split` — **the conditional re-signed C.39**: from
  `hconv` + the bookkeeping legs, the EXACT A-C.24″ conclusion, byte-shaped as the
  signed axiom `dv2ResPolyTw_scalar`'s display.  Closing `hconv` (+ the bookkeeping
  legs at genuine C.39 sites) retires the F1.4/F1.5 axiom rows outright.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136f14e

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C132nv2 Uniformity.Density.Tower.C134dv2g
open Uniformity.Density.Tower.C136l2e0 Uniformity.Density.Tower.C136l2e1
open Uniformity.Density.Tower.C136l2e2 Uniformity.Density.Tower.C136l2e3
open Uniformity.Density.Tower.C136f14b Uniformity.Density.Tower.C136f14c
open Uniformity.Density.Tower.C136f14d

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Part 0 — the anchored complement read (leanspec C.39's `γgAnch`, transcribed) -/

/-- `γ̂_g` — the complement's ANCHORED absolute read at its own level grade
(the pin-anchored normalization of PE3 F-1's `γ_g`; byte-faithful twin of the signed
leanspec NODE C.39 def). -/
noncomputable def γgAnch (L : LevelDatum F H₀ hpin) (f : Polynomial O) :
    AdjoinRoot L.r :=
  dv2FullRead L (complementConst L f) (f /ₘ blockFactor L f)

/-! ## Part 1 — propositional transport (the `dvResPoly_congr` pattern) -/

/-- Pins at side minima transport along propositional equality of the carriers. -/
theorem dv2Pin_sideMin_congr (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    {u₂ ℓ₂ : ℕ} {x y : Polynomial O} (hxy : x = y)
    (hnex : (dv2SideSet L Ψ x u₂ ℓ₂).Nonempty)
    (hney : (dv2SideSet L Ψ y u₂ ℓ₂).Nonempty) :
    dv2Pin L Ψ x (dv2SideMin L Ψ x u₂ ℓ₂ hnex)
      = dv2Pin L Ψ y (dv2SideMin L Ψ y u₂ ℓ₂ hney) := by
  subst hxy
  rfl

/-- The twisted carrier transports along propositional equality of the polynomials. -/
theorem dv2ResPolyTw_congr (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    {u₂ ℓ₂ : ℕ} {x y : Polynomial O} (hxy : x = y)
    (hnex : (dv2SideSet L Ψ x u₂ ℓ₂).Nonempty)
    (hney : (dv2SideSet L Ψ y u₂ ℓ₂).Nonempty) {Mx My : ℕ}
    (hpx : dv2Pin L Ψ x (dv2SideMin L Ψ x u₂ ℓ₂ hnex) = (Mx : ℕ∞))
    (hpy : dv2Pin L Ψ y (dv2SideMin L Ψ y u₂ ℓ₂ hney) = (My : ℕ∞)) :
    dv2ResPolyTw L Ψ x u₂ ℓ₂ hnex Mx hpx
      = dv2ResPolyTw L Ψ y u₂ ℓ₂ hney My hpy := by
  subst hxy
  have hM : Mx = My := by
    have h := hpx.symm.trans hpy
    exact_mod_cast h
  subst hM
  rfl

/-- Under the GC-1 pin binder the `pinHeight` def evaluates to the bound pin. -/
theorem pinHeight_eq_of_pin (L : LevelDatum F H₀ hpin) {Ψ f : Polynomial O}
    {u₂ ℓ₂ : ℕ} (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {M₂ : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) :
    pinHeight L Ψ f u₂ ℓ₂ hne = M₂ := by
  rw [pinHeight, hp₂]
  simp

/-! ## Part 2 — ★★ the conditional re-signed C.39 -/

/-- ★★ **The A-C.24″ signed row as a CONDITIONAL THEOREM** (the carried-hypothesis
pattern).  Conclusion byte-shaped as the signed axiom `dv2ResPolyTw_scalar`
(`leanspec/Leanspec/ChapC.lean` NODE C.39): EFF.HE6R1.39's display over the twisted
carrier, ONE constant per side, the PIN-HEIGHT exponent, the scalar
`γ̂_g · root^{c₁(pinHeight, c_g)}` byte-kept from the source.

The ONE open proof obligation is `hconv` — F14C §2.1's digit-split convolution
supplier, byte-shaped as the premise of
`C136f14c.dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution` at the
block/complement pair.  The remaining hypotheses are C.36/C.37-genre side-geometry
bookkeeping at the split (see the file docstring); NONE of them is the stationarity
premise F14C §2.2 demanded — that obstruction is discharged by the twist bookkeeping
(ID1/ID2), which is this composition's content. -/
theorem dv2ResPolyTw_scalar_of_conv_split (L : LevelDatum F H₀ hpin)
    {Ψ f : Polynomial O} {u₂ ℓ₂ : ℕ}
    (hsplit : blockFactor L f * (f /ₘ blockFactor L f) = f)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty)
    (hnz : (dv2SideSet L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂).Nonempty)
    (hngz : (dv2SideSet L Ψ (blockFactor L f * (f /ₘ blockFactor L f)) u₂ ℓ₂).Nonempty)
    {M₂ M₂' : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞))
    (hp₂' : dv2Pin L Ψ (blockFactor L f)
        (dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne') = (M₂' : ℕ∞))
    (hpz : dv2Pin L Ψ (f /ₘ blockFactor L f)
        (dv2SideMin L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz)
        = ((complementConst L f : ℕ) : ℕ∞))
    (hpgz : dv2Pin L Ψ (blockFactor L f * (f /ₘ blockFactor L f))
        (dv2SideMin L Ψ (blockFactor L f * (f /ₘ blockFactor L f)) u₂ ℓ₂ hngz)
        = (M₂ : ℕ∞))
    (hM : M₂ = M₂' + complementConst L f)
    (hdeg : dv2SideDeg L Ψ (blockFactor L f * (f /ₘ blockFactor L f)) u₂ ℓ₂ hngz
        = dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne'
          + dv2SideDeg L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz)
    (hzdeg : dv2SideDeg L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz = 0)
    (hfS : dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne' * u₂ ≤ M₂')
    (hγ : dv2FullRead L (complementConst L f)
        (dev Ψ (f /ₘ blockFactor L f)
          (dv2SideMin L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz))
        = γgAnch L f)
    (hconv : ∀ t, t ≤ dv2SideDeg L Ψ (blockFactor L f * (f /ₘ blockFactor L f)) u₂ ℓ₂ hngz →
      dv2FullRead L (M₂ - t * u₂)
          (dev Ψ (blockFactor L f * (f /ₘ blockFactor L f))
            (dv2SideMin L Ψ (blockFactor L f * (f /ₘ blockFactor L f)) u₂ ℓ₂ hngz
              + t * ℓ₂)) =
        ∑ t₁ ∈ Finset.range (t + 1),
          if t₁ ≤ dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne' ∧
              t - t₁ ≤ dv2SideDeg L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz then
            AdjoinRoot.root L.r ^
                L.cocycle (M₂' - t₁ * u₂) (complementConst L f - (t - t₁) * u₂) *
              ((dv2ResPolyAnch L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂').coeff t₁ *
                (dv2ResPolyAnch L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz
                  (complementConst L f) hpz).coeff (t - t₁))
          else 0) :
    dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂
      = Polynomial.C (γgAnch L f * (AdjoinRoot.root L.r)
            ^ (L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne')
                (complementConst L f)))
          * dv2ResPolyTw L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂' := by
  -- the complement line floor is trivial at a point side
  have hfz : dv2SideDeg L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz * u₂
      ≤ complementConst L f := by
    rw [hzdeg, zero_mul]
    exact Nat.zero_le _
  -- F14C's assembler: the supplier gives the weighted convolution
  have hw := dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution L hne' hnz hngz
    hp₂' hpz hpgz hdeg hconv
  -- A24C's ID2 product law: the twisted carriers multiply with the single pin cocycle
  have hprod := dv2ResPolyTw_mul_of_weightedConv L hne' hnz hngz hp₂' hpz hpgz
    hM hfS hfz hw
  -- the degree-0 complement collapses to the constant `γ̂_g` (`ε_0 = 0`)
  have hzc : dv2ResPolyTw L Ψ (f /ₘ blockFactor L f) u₂ ℓ₂ hnz
      (complementConst L f) hpz = Polynomial.C (γgAnch L f) := by
    rw [dv2ResPolyTw, hzdeg]
    simp only [zero_add, Finset.sum_range_one, twistExp_zero, pow_zero, one_mul,
      mul_one]
    rw [dv2ResPolyAnch_coeff_zero, hγ]
  -- the pin-height dressing
  have hpinh : pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne' = M₂' :=
    pinHeight_eq_of_pin L hne' hp₂'
  -- transport the conclusion carrier along the exact split
  have hcongr : dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂
      = dv2ResPolyTw L Ψ (blockFactor L f * (f /ₘ blockFactor L f)) u₂ ℓ₂ hngz
          M₂ hpgz :=
    dv2ResPolyTw_congr L hsplit.symm hne hngz hp₂ hpgz
  rw [hcongr, hprod, hzc, hpinh, Polynomial.C_mul]
  ring

end Uniformity.Density.Tower.C136f14e

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136f14e.γgAnch
#print axioms Uniformity.Density.Tower.C136f14e.dv2Pin_sideMin_congr
#print axioms Uniformity.Density.Tower.C136f14e.dv2ResPolyTw_congr
#print axioms Uniformity.Density.Tower.C136f14e.pinHeight_eq_of_pin
#print axioms Uniformity.Density.Tower.C136f14e.dv2ResPolyTw_scalar_of_conv_split

end AxCheck
