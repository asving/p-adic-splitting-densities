/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C11
import Uniformity.ChapC.C130s6

/-!
# Uniformity.ChapC.C132nv0 — the `dv2Supp` valuation-law bank (μ₃ campaign, node M3-NV0)

**[M3-NV0, 2026-08-26]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-NV0):
generalizes the `dvSupp` zero/finiteness/add/negation bank landed at
`Uniformity.ChapC.C130s6` (`dvSupp_zero_eq_top` through `dvSupp_add_eq`,
`C130s6.lean:169-293`) ONE LEVEL UP, to C.11's level-2 cleared support `dv2Supp L Ψ f u₂ ℓ₂`
(`C11.lean:128-144`). Every statement below is parameter-free in the campaign's sense: no
S2 numeral (`21`, `Φ₂`, or the S2 tower) occurs anywhere in this file. The bank is generic
over any level datum `L : LevelDatum F H₀ hpin` (C.09), any level-2 key `Ψ : Polynomial O`,
and any side `(u₂, ℓ₂)`.

## Why this is shape reuse, not new mathematics

`dv2Hgt L A = dvSupp F A L.u L.ℓ` definitionally (C.11's "one line that is the whole
node"), so every SLOT-level fact (`A = 0` ↦ `⊤`, `A ≠ 0` ↦ finite, additive/negation
behaviour) at the `dv2Hgt` level is already proved — it is exactly the corresponding
`dvSupp` fact at the side `(L.u, L.ℓ)`, consumed here by unfolding and one application. The
only genuinely new step is climbing the SECOND `Finset.inf` layer (`dv2Supp`'s own
development in `Ψ`, mirroring `dvSupp`'s development in `F.key`): the range-truncation
argument (`dv2Supp_eq_inf_range`), the ultrametric inequality
(`min_dv2Supp_le_dv2Supp_add`), and equality off ties (`dv2Supp_add_eq`) are proved by the
SAME two-line arguments C130s6 used one level down, with `Ψ`'s development (B.02's `dev`)
standing in for `F.key`'s.

## The `Ψ`-monicity hypothesis

`dvSupp`'s lemmas take a `KeyFrame`, which bundles `F.key.Monic` and `0 < F.key.natDegree`.
`dv2Supp`'s `Ψ` argument is a bare `Polynomial O` with no such bundling (C.11's own design:
`dv2Hgt` does not mention `Ψ` at all, and `dv2Pin`/`dv2Supp` take it unconstrained), so
every lemma here that needs B32a's `dev_add_of_monic` or B39b's `dev_neg` carries
`hΨ : Ψ.Monic` explicitly, and every lemma that needs the degree-truncation argument
(B04's `dev_eq_zero_of_lt`, B05's `sum_dev_eq`) carries `hΨd : 0 < Ψ.natDegree` alongside
it. Neither hypothesis is needed for the zero law (C118a's `dev_zero_any` handles the zero
polynomial for ANY divisor, monic or not).

**DEPENDS.** C.11 (`dv2Hgt`, `dv2Pin`, `dv2Supp`) · C.09 (`LevelDatum`) · C130s6
(`dvSupp_zero_eq_top`, `dvSupp_ne_top_of_ne_zero`, `min_dvSupp_le_dvSupp_add`,
`dvSupp_neg`) · C118a (`inf_range_ext`, `smul_top_pos`, `dev_zero_any`) · B.04
(`dev_eq_zero_of_lt`) · B.05 (`sum_dev_eq`) · B32a (`dev_add_of_monic`) · B39b (`dev_neg`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the row's sketch.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132nv0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `dv2Pin` vanishes to `⊤` past the degree (mirror of C118a's `dvHgt_top_of_gt`, one
level up: the development term itself vanishes by B04's `dev_eq_zero_of_lt`, and `dv2Hgt`
of `0` is `⊤` by C130s6's `dvSupp_zero_eq_top`). -/
theorem dv2Pin_top_of_gt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) (f : Polynomial O) {j : ℕ}
    (hj : f.natDegree < j) : dv2Pin L Ψ f j = ⊤ := by
  have hjd : j ≤ j * Ψ.natDegree := Nat.le_mul_of_pos_right _ hΨd
  rw [dv2Pin, dev_eq_zero_of_lt hΨ hΨd f j (by omega), dv2Hgt]
  exact dvSupp_zero_eq_top F L.u L.hℓ

/-- `dv2Supp` of `0` is `⊤` (mirror of C130s6's `dvSupp_zero_eq_top`; no monicity needed,
since `dev` of the zero polynomial vanishes for ANY divisor). -/
theorem dv2Supp_zero_eq_top {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ : Polynomial O) (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) :
    dv2Supp L Ψ (0 : Polynomial O) u₂ ℓ₂ = ⊤ := by
  rw [dv2Supp]
  simp only [Polynomial.natDegree_zero, Nat.zero_add, Finset.range_one, Finset.inf_singleton]
  rw [dv2Pin, C118a.dev_zero_any, dv2Hgt, dvSupp_zero_eq_top F L.u L.hℓ,
    C118a.smul_top_pos hℓ₂, top_add]

/-- `dv2Supp` read over any range past the degree (mirror of C130s6's
`dvSupp_eq_inf_range`; the added abscissae have `dv2Pin = ⊤` by `dv2Pin_top_of_gt`). -/
theorem dv2Supp_eq_inf_range {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (f : Polynomial O) {M : ℕ} (hM : f.natDegree < M) :
    dv2Supp L Ψ f u₂ ℓ₂ = (Finset.range M).inf (fun j => ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞)) := by
  rw [dv2Supp]
  have h := C118a.inf_range_ext (m := f.natDegree) (M := M - 1) (by omega)
      (fun j => ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞)) (fun i hi1 _ => by
        rw [dv2Pin_top_of_gt L hΨ hΨd f hi1, C118a.smul_top_pos hℓ₂, top_add])
  rw [h, show M - 1 + 1 = M by omega]

/-- a nonzero polynomial has finite `dv2Supp` (mirror of C130s6's
`dvSupp_ne_top_of_ne_zero`; the per-slot step is C130s6's `dvSupp_ne_top_of_ne_zero`
applied at `dv2Hgt`'s underlying `dvSupp`, rather than a fresh degree argument). -/
theorem dv2Supp_ne_top_of_ne_zero {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) (u₂ ℓ₂ : ℕ) {f : Polynomial O}
    (hf : f ≠ 0) : dv2Supp L Ψ f u₂ ℓ₂ ≠ ⊤ := by
  intro htop
  rw [dv2Supp] at htop
  have hall : ∀ j ∈ Finset.range (f.natDegree + 1), dev Ψ f j = 0 := by
    intro j hj
    have hle := Finset.inf_le (f := fun j => ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞)) hj
    rw [htop] at hle
    have hterm : ℓ₂ • dv2Pin L Ψ f j + ((u₂ : ℕ∞) * (j : ℕ∞)) = ⊤ := top_le_iff.mp hle
    have hleft : ℓ₂ • dv2Pin L Ψ f j = ⊤ := by
      rcases WithTop.add_eq_top.mp hterm with h | h
      · exact h
      · rw [← Nat.cast_mul] at h
        exact absurd h (ENat.coe_ne_top _)
    have hdvtop : dv2Pin L Ψ f j = ⊤ := by
      by_contra hx
      rw [nsmul_eq_mul] at hleft
      exact WithTop.mul_ne_top (ENat.coe_ne_top ℓ₂) hx hleft
    rw [dv2Pin, dv2Hgt] at hdvtop
    by_contra hne
    exact absurd hdvtop (dvSupp_ne_top_of_ne_zero F L.u L.ℓ hne)
  have hrec : ∑ j ∈ Finset.range (f.natDegree + 1), dev Ψ f j * Ψ ^ j = f :=
    sum_dev_eq hΨ hΨd f
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_mul_of_pos_right _ hΨd))
  refine hf ?_
  rw [← hrec]
  exact Finset.sum_eq_zero fun j hj => by rw [hall j hj, zero_mul]

/-- **the `dv2Supp` ultrametric inequality** (mirror of C130s6's
`min_dvSupp_le_dvSupp_add`): per-slot, `dev` is additive (B32a) and `dv2Hgt` is
ultrametric (C130s6's `min_dvSupp_le_dvSupp_add`, one level down). -/
theorem min_dv2Supp_le_dv2Supp_add {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (f g : Polynomial O) :
    min (dv2Supp L Ψ f u₂ ℓ₂) (dv2Supp L Ψ g u₂ ℓ₂) ≤ dv2Supp L Ψ (f + g) u₂ ℓ₂ := by
  set M := max (max f.natDegree g.natDegree) (f + g).natDegree + 1 with hMdef
  rw [dv2Supp_eq_inf_range L hΨ hΨd hℓ₂ f (M := M) (by omega),
    dv2Supp_eq_inf_range L hΨ hΨd hℓ₂ g (M := M) (by omega),
    dv2Supp_eq_inf_range L hΨ hΨd hℓ₂ (f + g) (M := M) (by omega)]
  refine Finset.le_inf fun j hj => ?_
  have hmono : Monotone fun x : ℕ∞ => ℓ₂ • x + ((u₂ : ℕ∞) * (j : ℕ∞)) := by
    intro x y hxy
    exact add_le_add (nsmul_le_nsmul_right hxy ℓ₂) le_rfl
  have hs : min (dv2Pin L Ψ f j) (dv2Pin L Ψ g j) ≤ dv2Pin L Ψ (f + g) j := by
    rw [dv2Pin, dv2Pin, dv2Pin, dev_add_of_monic hΨ f g j, dv2Hgt, dv2Hgt, dv2Hgt]
    exact min_dvSupp_le_dvSupp_add F L.hℓ (dev Ψ f j) (dev Ψ g j)
  calc min ((Finset.range M).inf fun i => ℓ₂ • dv2Pin L Ψ f i + (u₂ * i : ℕ∞))
        ((Finset.range M).inf fun i => ℓ₂ • dv2Pin L Ψ g i + (u₂ * i : ℕ∞))
      ≤ min (ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞)) (ℓ₂ • dv2Pin L Ψ g j + (u₂ * j : ℕ∞)) :=
        min_le_min (Finset.inf_le hj) (Finset.inf_le hj)
    _ = ℓ₂ • min (dv2Pin L Ψ f j) (dv2Pin L Ψ g j) + (u₂ * j : ℕ∞) := (hmono.map_min).symm
    _ ≤ ℓ₂ • dv2Pin L Ψ (f + g) j + (u₂ * j : ℕ∞) := hmono hs

/-- `dv2Supp` is negation-invariant (per-slot mirror of C130s6's `dvSupp_neg`, through
B39b's `dev_neg` and C130s6's `dvSupp_neg` at `dv2Hgt`'s underlying `dvSupp`). -/
theorem dv2Supp_neg {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hΨ : Ψ.Monic) (f : Polynomial O) (u₂ ℓ₂ : ℕ) :
    dv2Supp L Ψ (-f) u₂ ℓ₂ = dv2Supp L Ψ f u₂ ℓ₂ := by
  rw [dv2Supp, dv2Supp, Polynomial.natDegree_neg]
  refine Finset.inf_congr rfl fun j _ => ?_
  rw [dv2Pin, dv2Pin, dev_neg hΨ, dv2Hgt, dv2Hgt, dvSupp_neg]

/-- the strict half of equality off ties: the lower side wins outright (mirror of
C130s6's `dvSupp_add_eq_of_lt`). -/
theorem dv2Supp_add_eq_of_lt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    {f g : Polynomial O} (hlt : dv2Supp L Ψ f u₂ ℓ₂ < dv2Supp L Ψ g u₂ ℓ₂) :
    dv2Supp L Ψ (f + g) u₂ ℓ₂ = dv2Supp L Ψ f u₂ ℓ₂ := by
  have hge : dv2Supp L Ψ f u₂ ℓ₂ ≤ dv2Supp L Ψ (f + g) u₂ ℓ₂ := by
    have h := min_dv2Supp_le_dv2Supp_add (u₂ := u₂) L hΨ hΨd hℓ₂ f g
    rwa [min_eq_left hlt.le] at h
  refine le_antisymm ?_ hge
  have h2 : min (dv2Supp L Ψ (f + g) u₂ ℓ₂) (dv2Supp L Ψ g u₂ ℓ₂) ≤ dv2Supp L Ψ f u₂ ℓ₂ := by
    have h3 := min_dv2Supp_le_dv2Supp_add (u₂ := u₂) L hΨ hΨd hℓ₂ (f + g) (-g)
    rw [dv2Supp_neg L hΨ] at h3
    calc min (dv2Supp L Ψ (f + g) u₂ ℓ₂) (dv2Supp L Ψ g u₂ ℓ₂)
        ≤ dv2Supp L Ψ ((f + g) + -g) u₂ ℓ₂ := h3
      _ = dv2Supp L Ψ f u₂ ℓ₂ := by rw [add_neg_cancel_right]
  by_contra hcon
  exact absurd h2 (not_le.mpr (lt_min (not_le.mp hcon) hlt))

/-- ★ **the `dv2Supp` ultrametric EQUALITY OFF TIES** (mirror of C130s6's
`dvSupp_add_eq`, the E.10 `hgt_add_eq` law one level up). -/
theorem dv2Supp_add_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ : Polynomial O} (hΨ : Ψ.Monic) (hΨd : 0 < Ψ.natDegree) {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    {f g : Polynomial O} (hne : dv2Supp L Ψ f u₂ ℓ₂ ≠ dv2Supp L Ψ g u₂ ℓ₂) :
    dv2Supp L Ψ (f + g) u₂ ℓ₂ = min (dv2Supp L Ψ f u₂ ℓ₂) (dv2Supp L Ψ g u₂ ℓ₂) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le]
    exact dv2Supp_add_eq_of_lt L hΨ hΨd hℓ₂ h
  · rw [min_eq_right h.le, add_comm]
    exact dv2Supp_add_eq_of_lt L hΨ hΨd hℓ₂ h

end Uniformity.Density.Tower.C132nv0

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132nv0.dv2Pin_top_of_gt
#print axioms Uniformity.Density.Tower.C132nv0.dv2Supp_zero_eq_top
#print axioms Uniformity.Density.Tower.C132nv0.dv2Supp_eq_inf_range
#print axioms Uniformity.Density.Tower.C132nv0.dv2Supp_ne_top_of_ne_zero
#print axioms Uniformity.Density.Tower.C132nv0.min_dv2Supp_le_dv2Supp_add
#print axioms Uniformity.Density.Tower.C132nv0.dv2Supp_neg
#print axioms Uniformity.Density.Tower.C132nv0.dv2Supp_add_eq_of_lt
#print axioms Uniformity.Density.Tower.C132nv0.dv2Supp_add_eq

end AxCheck
