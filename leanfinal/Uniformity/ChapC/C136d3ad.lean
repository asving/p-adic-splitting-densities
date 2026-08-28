/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132kp0
import Uniformity.ChapC.C132nv2
import Uniformity.ChapC.C132nv4
import Uniformity.ChapC.C132nv6
import Uniformity.ChapC.C132rp10b
import Uniformity.ChapC.C136t
import Uniformity.ChapC.C136d0

/-!
# Uniformity.ChapC.C136d3ad — the depth-three μ-key adapter: D3-03 discharged, D3-04 landed [D3AD 2026-08-28]

**Unit D3AD** (the D3-03/D3-10 unblocker demanded by `runs/wave-c/verdict_L2E3.md`'s
"D3 exact adapter mismatch" section).

## The adapter adjudication (recorded honestly)

`verdict_L2E3.md` asked for a "depth-three `LevelDatum`/operator adapter" identifying the
`C136d0.Dv3ResSurv` read `dv2Supp L Ψ₂ · u₂ ℓ₂` with an L2E-engine-shaped inner read.  Three
candidate shapes were adjudicated:

* **(a) a depth-three `LevelDatum` instance — IMPOSSIBLE.**  `LevelDatum` (C.09) carries no
  valuation field: the engine's inner read `dv2Hgt L := dvSupp F · L.u L.ℓ` (C.11) is a
  fixed one-development read through the frame's `stageHeight`.  No choice of
  `L' : LevelDatum F' H₀' hpin'` makes `dvSupp F' · L'.u L'.ℓ` the NESTED two-level read
  `dv2Supp L Ψ₂ · u₂ ℓ₂`, so no type-correct instantiation of the landed L2E theorems exists.
* **(b) the landed engine is LevelDatum-polymorphic — FALSE as landed.**  DWR §11.7's design
  claim ("instantiate both at `(g8,85,2)` and for F1.4–F1.6") holds for the STATEMENT SHAPES
  (no S2 numeral occurs in C136l2e0–3), but the ROOT CARRIER of every landed engine theorem
  is `L : LevelDatum` with the level-1 inner read baked in — a genuine design-vs-landed gap.
* **(c) a mirror — CHEAP, and taken here.**  The μ-key survival core (`C134dv2g` Parts 1–3)
  consumes exactly six laws of its inner valuation: zero→⊤, finiteness off zero, the
  ultrametric min, equality off ties, negation invariance, and multiplicativity on nonzero
  factors.  All six have landed `dv2Supp` twins (C132nv0's bank; multiplicativity via
  C132nv2's endpoint product law).  So the adapter is THIS FILE: the survival core restated
  at the level-3 valuation `dv2Supp L Ψ₂ · u₂ ℓ₂`, generic over `(L, Ψ₂, u₂, ℓ₂)`, with
  multiplicativity threaded as one honest hypothesis `hmul` (dischargeable at S2 from
  `C132nv4.s2_dv2ResSurv_at_21`).

## What lands

* Part 1 — the generic μ-predicates at the level-3 valuation (`Mu3Equiv`/`Mu3Dvd`/
  `Mu3Minimal`/`Mu3Prime`/`IsMu3Key`), the one-level-up mirror of `C134dv2g` Part 1.
* Part 2 — the generic survival core one level up (`dv2Supp_mul_modByKey_le/eq`,
  `dv2Supp_add_le_key_quot_add`) and ★ **the D3-03 generic discharge**
  `dv3ResSurv_of_mu3Key : Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃` from `IsMu3Key` + the key grade
  + the OUTER floor `ℓ₃ · KΨ₃ < u₃` — the exact one-level-up mirror of
  `C134dv2g.dv2ResSurv_of_muKey`.  Plus `dv3SideSet_nonempty_of_ne_zero` (the dv3 twin of
  `C134dv2g.dv2SideSet_nonempty_of_ne_zero`).
* Part 3 — ★ **the S2 discharge at `(g8, 85, 2)`** (row D3-03):
  `s2_dv3ResSurv_at_85 : Dv3ResSurv L Φ₂ 21 2 (g8) 85 2`, from the T2 key proof
  `C136t.s2Mu3KeyPoly_g8` (bridged from the `s2Hgt₃`-anchored `S2Mu3KeyPoly` to the
  ℕ∞-valued predicates through the `toZ` order bridge), the landed grade
  `C132rp10b.s2Hgt₃_g8 = 42`, and the fence `2·42 = 84 < 85`.
* Part 4 — ★ **row D3-04**: the UNCONDITIONAL μ₄ product law
  `s2Hgt₄_mul_unconditional` / `s2Hgt₄_mul_all` via C136d0's endpoint assembly
  (`dv3Supp_mul_eq_add_of_endpoint_le`) fired at the discharged survival — the exact μ₄
  twin of `C132nv6.s2Hgt₃_mul_unconditional`/`s2Hgt₃_mul_all`.

## Status

Sorry-free, Lean core only; no new axiom, no `unsafe`, no landed file edited.  New statement
shapes (`Mu3Equiv` through `IsMu3Key`, and every theorem here) are trust-boundary
declarations flagged for human review.  Verdict: `runs/wave-c/verdict_D3AD.md`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136d3ad

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C132nv0
open Uniformity.Density.Tower.C132nv2 Uniformity.Density.Tower.C136d0
open Uniformity.Density.Tower.C130nv2 (dev_zero_pin)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Part 1 — the generic μ-predicates at the level-3 valuation

`C134dv2g` Part 1's shapes (FGMN Def 1.2/1.4), one level up: the valuation is the level-3
inner read `dv2Supp L Ψ₂ · u₂ ℓ₂` (= `C136d0.dv3Hgt L Ψ₂ u₂ ℓ₂`, definitionally) instead of
`dvSupp F · L.u L.ℓ` (= `dv2Hgt L`).  Generic over any level datum and inner key/side —
despite the "3" the declarations carry no S2 numeral. -/

/-- FGMN Def 1.2's `g ∼µ h` at the level-3 valuation (one-level-up twin of
`C134dv2g.MuEquiv`). -/
def Mu3Equiv (L : LevelDatum F H₀ hpin) (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ)
    (g h : Polynomial O) : Prop :=
  (dv2Supp L Ψ₂ g u₂ ℓ₂ < dv2Supp L Ψ₂ (g - h) u₂ ℓ₂ ∧
    dv2Supp L Ψ₂ g u₂ ℓ₂ = dv2Supp L Ψ₂ h u₂ ℓ₂) ∨ (g = 0 ∧ h = 0)

/-- FGMN Def 1.2's `Ψ₃ ∣µ g` at the level-3 valuation (twin of `C134dv2g.MuDvd`). -/
def Mu3Dvd (L : LevelDatum F H₀ hpin) (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ)
    (Ψ₃ g : Polynomial O) : Prop :=
  ∃ q : Polynomial O, Mu3Equiv L Ψ₂ u₂ ℓ₂ g (Ψ₃ * q)

/-- FGMN Def 1.2's µ-minimality at the level-3 valuation (twin of `C134dv2g.MuMinimal`). -/
def Mu3Minimal (L : LevelDatum F H₀ hpin) (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ)
    (Ψ₃ : Polynomial O) : Prop :=
  0 < Ψ₃.natDegree ∧
    ∀ g : Polynomial O, g ≠ 0 → g.natDegree < Ψ₃.natDegree → ¬ Mu3Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ g

/-- The prime clause of FGMN Def 1.2's µ-irreducibility at the level-3 valuation (twin of
`C134dv2g.MuPrime`). -/
def Mu3Prime (L : LevelDatum F H₀ hpin) (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ)
    (Ψ₃ : Polynomial O) : Prop :=
  ∀ g h : Polynomial O,
    Mu3Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ (g * h) → Mu3Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ g ∨ Mu3Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ h

/-- FGMN Def 1.4's key-polynomialhood at the level-3 valuation (twin of
`C134dv2g.IsMuKey`). -/
def IsMu3Key (L : LevelDatum F H₀ hpin) (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ)
    (Ψ₃ : Polynomial O) : Prop :=
  Ψ₃.Monic ∧ Mu3Minimal L Ψ₂ u₂ ℓ₂ Ψ₃ ∧ Mu3Prime L Ψ₂ u₂ ℓ₂ Ψ₃

variable (L : LevelDatum F H₀ hpin) {Ψ₂ : Polynomial O}

/-- `0` is μ₃-divisible by anything (witness `0`; twin of `C134dv2g.muDvd_zero`). -/
theorem mu3Dvd_zero {u₂ ℓ₂ : ℕ} (Ψ₃ : Polynomial O) :
    Mu3Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ (0 : Polynomial O) :=
  ⟨0, Or.inr ⟨rfl, mul_zero Ψ₃⟩⟩

/-! ## Part 2 — the generic survival core one level up

`C134dv2g` Part 2's proofs verbatim, with each inner-valuation law swapped for its landed
`dv2Supp` twin (C132nv0), and the inner multiplicativity — which one level down was
`C133mh3.dvSupp_mul` at the datum's own floor `L.hκ` — threaded as the one honest explicit
hypothesis `hmul` (no landed generic `dv2Supp` multiplicativity exists; at S2 it is supplied
by `C132nv4.s2_dv2ResSurv_at_21` through C132nv2's endpoint product law, Part 3 below). -/

/-- ★ **The `≤` half** (twin of `C134dv2g.dvSupp_mul_modByKey_le`, one level up): for
`a, b` of degree `< deg Ψ₃`, reducing `a·b` modulo the μ₃-key `Ψ₃` does not raise the
level-3 value above the sum of the factors' values. -/
theorem dv2Supp_mul_modByKey_le (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hmul : ∀ ⦃g z : Polynomial O⦄, g ≠ 0 → z ≠ 0 →
      dv2Supp L Ψ₂ (g * z) u₂ ℓ₂ = dv2Supp L Ψ₂ g u₂ ℓ₂ + dv2Supp L Ψ₂ z u₂ ℓ₂)
    {Ψ₃ : Polynomial O} (hkey : IsMu3Key L Ψ₂ u₂ ℓ₂ Ψ₃) {a b : Polynomial O}
    (ha : a.natDegree < Ψ₃.natDegree) (hb : b.natDegree < Ψ₃.natDegree) :
    dv2Supp L Ψ₂ ((a * b) %ₘ Ψ₃) u₂ ℓ₂ ≤ dv2Supp L Ψ₂ a u₂ ℓ₂ + dv2Supp L Ψ₂ b u₂ ℓ₂ := by
  obtain ⟨hΨ₃m, hΨ₃min, hΨ₃pr⟩ := hkey
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_mul, Polynomial.zero_modByMonic, dv2Supp_zero_eq_top L Ψ₂ u₂ hℓ₂, top_add]
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero, Polynomial.zero_modByMonic, dv2Supp_zero_eq_top L Ψ₂ u₂ hℓ₂, add_top]
  set r := (a * b) %ₘ Ψ₃ with hrdef
  set q0 := (a * b) /ₘ Ψ₃ with hq0def
  have hab : r + Ψ₃ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ₃
  rw [← hmul ha0 hb0]
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : dv2Supp (a·b) < dv2Supp r`
  have hmin' : min (dv2Supp L Ψ₂ r u₂ ℓ₂) (dv2Supp L Ψ₂ (Ψ₃ * q0) u₂ ℓ₂)
      ≤ dv2Supp L Ψ₂ (a * b) u₂ ℓ₂ := by
    have h := min_dv2Supp_le_dv2Supp_add (u₂ := u₂) L hΨ₂ hΨ₂d hℓ₂ r (Ψ₃ * q0)
    rwa [hab] at h
  have hy : dv2Supp L Ψ₂ (Ψ₃ * q0) u₂ ℓ₂ < dv2Supp L Ψ₂ r u₂ ℓ₂ := by
    by_contra hge
    rw [not_lt] at hge
    rw [min_eq_left hge] at hmin'
    exact absurd hmin' (not_le.mpr hcon)
  have heq' : dv2Supp L Ψ₂ (a * b) u₂ ℓ₂ = dv2Supp L Ψ₂ (Ψ₃ * q0) u₂ ℓ₂ := by
    rw [← hab, add_comm]
    exact dv2Supp_add_eq_of_lt L hΨ₂ hΨ₂d hℓ₂ hy
  -- initial equivalence `a·b ∼µ Ψ₃·q0`, hence `Ψ₃ ∣µ a·b`
  have hMuDvd : Mu3Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ (a * b) := by
    refine ⟨q0, Or.inl ⟨?_, heq'⟩⟩
    have hsub : a * b - Ψ₃ * q0 = r := by rw [← hab]; ring
    rw [hsub]
    exact hcon
  -- contradiction: μ-primality + μ-minimality at the digit-bounded factors
  rcases hΨ₃pr a b hMuDvd with h | h
  · exact hΨ₃min.2 a ha0 ha h
  · exact hΨ₃min.2 b hb0 hb h

/-- ★ **The EQUALITY** (twin of `C134dv2g.dvSupp_mul_modByKey_eq`, one level up): reduction
modulo the μ₃-key preserves the product's level-3 value exactly. -/
theorem dv2Supp_mul_modByKey_eq (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hmul : ∀ ⦃g z : Polynomial O⦄, g ≠ 0 → z ≠ 0 →
      dv2Supp L Ψ₂ (g * z) u₂ ℓ₂ = dv2Supp L Ψ₂ g u₂ ℓ₂ + dv2Supp L Ψ₂ z u₂ ℓ₂)
    {Ψ₃ : Polynomial O} (hkey : IsMu3Key L Ψ₂ u₂ ℓ₂ Ψ₃) {a b : Polynomial O}
    (ha : a.natDegree < Ψ₃.natDegree) (hb : b.natDegree < Ψ₃.natDegree) :
    dv2Supp L Ψ₂ ((a * b) %ₘ Ψ₃) u₂ ℓ₂ = dv2Supp L Ψ₂ a u₂ ℓ₂ + dv2Supp L Ψ₂ b u₂ ℓ₂ := by
  refine le_antisymm (dv2Supp_mul_modByKey_le L hΨ₂ hΨ₂d hℓ₂ hmul hkey ha hb) ?_
  obtain ⟨hΨ₃m, hΨ₃min, hΨ₃pr⟩ := hkey
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_mul, Polynomial.zero_modByMonic, dv2Supp_zero_eq_top L Ψ₂ u₂ hℓ₂]
    exact le_top
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero, Polynomial.zero_modByMonic, dv2Supp_zero_eq_top L Ψ₂ u₂ hℓ₂]
    exact le_top
  rw [← hmul ha0 hb0]
  set r := (a * b) %ₘ Ψ₃ with hrdef
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [hr0, dv2Supp_zero_eq_top L Ψ₂ u₂ hℓ₂]
    exact le_top
  set q0 := (a * b) /ₘ Ψ₃ with hq0def
  have hab : r + Ψ₃ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ₃
  have hΨ₃d : 0 < Ψ₃.natDegree := hΨ₃min.1
  have hΨ₃ne1 : Ψ₃ ≠ 1 := fun h1 => by simp [h1] at hΨ₃d
  have hrdeg : r.natDegree < Ψ₃.natDegree :=
    Polynomial.natDegree_modByMonic_lt (a * b) hΨ₃m hΨ₃ne1
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : dv2Supp r < dv2Supp (a·b)` — the tie analysis forces `dv2Supp r = dv2Supp (Ψ₃·q0)`
  have htie : dv2Supp L Ψ₂ r u₂ ℓ₂ = dv2Supp L Ψ₂ (Ψ₃ * q0) u₂ ℓ₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have heqX : dv2Supp L Ψ₂ (a * b) u₂ ℓ₂ = dv2Supp L Ψ₂ r u₂ ℓ₂ := by
        rw [← hab]
        exact dv2Supp_add_eq_of_lt L hΨ₂ hΨ₂d hℓ₂ hlt
      rw [heqX] at hcon
      exact lt_irrefl _ hcon
    · have heqX : dv2Supp L Ψ₂ (a * b) u₂ ℓ₂ = dv2Supp L Ψ₂ (Ψ₃ * q0) u₂ ℓ₂ := by
        rw [← hab, add_comm]
        exact dv2Supp_add_eq_of_lt L hΨ₂ hΨ₂d hℓ₂ hgt
      rw [heqX] at hcon
      exact lt_irrefl _ (hcon.trans hgt)
  -- initial equivalence `r ∼µ Ψ₃·(−q0)`, hence `Ψ₃ ∣µ r` — excluded by μ-minimality
  have hMuDvd : Mu3Dvd L Ψ₂ u₂ ℓ₂ Ψ₃ r := by
    refine ⟨-q0, Or.inl ⟨?_, ?_⟩⟩
    · have hsub : r - Ψ₃ * -q0 = a * b := by rw [mul_neg, sub_neg_eq_add, hab]
      rw [hsub]
      exact hcon
    · rw [mul_neg, dv2Supp_neg L hΨ₂]
      exact htie
  exact hΨ₃min.2 r hr0 hrdeg hMuDvd

/-- ★ **The sharp slot-1 relation** (twin of `C134dv2g.dvSupp_add_le_key_quot_add`, one
level up): `µ₃(a) + µ₃(b) ≤ µ₃(Ψ₃) + µ₃((a·b) /ₘ Ψ₃)`. -/
theorem dv2Supp_add_le_key_quot_add (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hmul : ∀ ⦃g z : Polynomial O⦄, g ≠ 0 → z ≠ 0 →
      dv2Supp L Ψ₂ (g * z) u₂ ℓ₂ = dv2Supp L Ψ₂ g u₂ ℓ₂ + dv2Supp L Ψ₂ z u₂ ℓ₂)
    {Ψ₃ : Polynomial O} (hkey : IsMu3Key L Ψ₂ u₂ ℓ₂ Ψ₃) {a b : Polynomial O}
    (ha : a.natDegree < Ψ₃.natDegree) (hb : b.natDegree < Ψ₃.natDegree) :
    dv2Supp L Ψ₂ a u₂ ℓ₂ + dv2Supp L Ψ₂ b u₂ ℓ₂
      ≤ dv2Supp L Ψ₂ Ψ₃ u₂ ℓ₂ + dv2Supp L Ψ₂ ((a * b) /ₘ Ψ₃) u₂ ℓ₂ := by
  set r := (a * b) %ₘ Ψ₃ with hrdef
  set q0 := (a * b) /ₘ Ψ₃ with hq0def
  rcases eq_or_ne q0 0 with hq00 | hq00
  · rw [hq00, dv2Supp_zero_eq_top L Ψ₂ u₂ hℓ₂, add_top]
    exact le_top
  rcases eq_or_ne a 0 with rfl | ha0
  · exact absurd (by rw [hq0def, zero_mul, Polynomial.zero_divByMonic]) hq00
  rcases eq_or_ne b 0 with rfl | hb0
  · exact absurd (by rw [hq0def, mul_zero, Polynomial.zero_divByMonic]) hq00
  have hΨ₃m : Ψ₃.Monic := hkey.1
  have hab : r + Ψ₃ * q0 = a * b := Polynomial.modByMonic_add_div (a * b) Ψ₃
  have heq0 : dv2Supp L Ψ₂ r u₂ ℓ₂ = dv2Supp L Ψ₂ a u₂ ℓ₂ + dv2Supp L Ψ₂ b u₂ ℓ₂ :=
    dv2Supp_mul_modByKey_eq L hΨ₂ hΨ₂d hℓ₂ hmul hkey ha hb
  have hXab : dv2Supp L Ψ₂ (a * b) u₂ ℓ₂ = dv2Supp L Ψ₂ a u₂ ℓ₂ + dv2Supp L Ψ₂ b u₂ ℓ₂ :=
    hmul ha0 hb0
  have heqXr : dv2Supp L Ψ₂ (a * b) u₂ ℓ₂ = dv2Supp L Ψ₂ r u₂ ℓ₂ := by rw [hXab, heq0]
  rw [← hXab, ← hmul hΨ₃m.ne_zero hq00]
  -- `min(dv2Supp(a·b), dv2Supp r) ≤ dv2Supp(Ψ₃·q0)`, and slot 0 collapses the `min`
  have hmin : min (dv2Supp L Ψ₂ (a * b) u₂ ℓ₂) (dv2Supp L Ψ₂ r u₂ ℓ₂)
      ≤ dv2Supp L Ψ₂ (Ψ₃ * q0) u₂ ℓ₂ := by
    have h := min_dv2Supp_le_dv2Supp_add (u₂ := u₂) L hΨ₂ hΨ₂d hℓ₂ (a * b) (-r)
    rw [dv2Supp_neg L hΨ₂] at h
    have hsub : a * b + -r = Ψ₃ * q0 := by rw [← hab]; ring
    rwa [hsub] at h
  rwa [← heqXr, min_self] at hmin

/-- Slot 1 of a short product's `Ψ₃`-development is the bare quotient
(`C134dv2g`'s private `dev_one_eq_quot`, re-proved verbatim — generic in the key). -/
private theorem dev_one_eq_quot {Ψ₃ : Polynomial O} (hΨ₃m : Ψ₃.Monic) {a b : Polynomial O}
    (ha : a.natDegree < Ψ₃.natDegree) (hb : b.natDegree < Ψ₃.natDegree) :
    dev Ψ₃ (a * b) 1 = (a * b) /ₘ Ψ₃ := by
  have hunfold : dev Ψ₃ (a * b) 1 = dev Ψ₃ ((a * b) /ₘ Ψ₃) 0 := rfl
  rw [hunfold, dev_zero_pin]
  set q0 := (a * b) /ₘ Ψ₃ with hq0def
  rcases eq_or_ne q0 0 with h0 | h0
  · rw [h0, Polynomial.zero_modByMonic]
  · have hqdeg : q0.natDegree < Ψ₃.natDegree := by
      rw [hq0def, Polynomial.natDegree_divByMonic _ hΨ₃m]
      have hABdeg : (a * b).natDegree ≤ a.natDegree + b.natDegree :=
        Polynomial.natDegree_mul_le
      omega
    exact (Polynomial.modByMonic_eq_self_iff hΨ₃m).mpr
      (by rw [Polynomial.degree_eq_natDegree h0, Polynomial.degree_eq_natDegree hΨ₃m.ne_zero]
          exact_mod_cast hqdeg)

/-- ★ **THE D3-03 GENERIC DISCHARGE** (the one-level-up mirror of
`C134dv2g.dv2ResSurv_of_muKey`): `Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃` holds at ANY level
datum and inner key/side with multiplicative level-3 value, for ANY μ₃-key `Ψ₃` of known
level-3 grade `KΨ₃`, at ANY outer pair `(u₃, ℓ₃)` clearing the OUTER floor
`ℓ₃ · KΨ₃ < u₃` (at S2: `KΨ₃ = 42`, `(u₃, ℓ₃) = (85, 2)`, `2·42 < 85`). -/
theorem dv3ResSurv_of_mu3Key (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂)
    (hmul : ∀ ⦃g z : Polynomial O⦄, g ≠ 0 → z ≠ 0 →
      dv2Supp L Ψ₂ (g * z) u₂ ℓ₂ = dv2Supp L Ψ₂ g u₂ ℓ₂ + dv2Supp L Ψ₂ z u₂ ℓ₂)
    {Ψ₃ : Polynomial O} (hkey : IsMu3Key L Ψ₂ u₂ ℓ₂ Ψ₃)
    {KΨ₃ : ℕ} (hKΨ₃ : dv2Supp L Ψ₂ Ψ₃ u₂ ℓ₂ = (KΨ₃ : ℕ∞))
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) (hfence : ℓ₃ * KΨ₃ < u₃) :
    Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃ := by
  intro A B Ha Hb hA hB hHa hHb
  have hHa' : dv2Supp L Ψ₂ A u₂ ℓ₂ = (Ha : ℕ∞) := hHa
  have hHb' : dv2Supp L Ψ₂ B u₂ ℓ₂ = (Hb : ℕ∞) := hHb
  constructor
  · -- slot-0 equality = `Dv3ResSurv`'s first clause, verbatim
    show dv2Supp L Ψ₂ (dev Ψ₃ (A * B) 0) u₂ ℓ₂ = ((Ha + Hb : ℕ) : ℕ∞)
    rw [dev_zero_pin, dv2Supp_mul_modByKey_eq L hΨ₂ hΨ₂d hℓ₂ hmul hkey hA hB, hHa', hHb']
    push_cast
    ring
  · -- slot-1 strict carry bound, from the sharp relation + the OUTER floor
    show ℓ₃ • ((Ha + Hb : ℕ) : ℕ∞) + 1
      ≤ ℓ₃ • dv2Supp L Ψ₂ (dev Ψ₃ (A * B) 1) u₂ ℓ₂ + (u₃ : ℕ∞)
    rw [dev_one_eq_quot hkey.1 hA hB]
    have hsharp := dv2Supp_add_le_key_quot_add L hΨ₂ hΨ₂d hℓ₂ hmul hkey hA hB
    rw [hHa', hHb', hKΨ₃] at hsharp
    set Hq0 := dv2Supp L Ψ₂ ((A * B) /ₘ Ψ₃) u₂ ℓ₂ with hHq0def
    rcases eq_or_ne Hq0 ⊤ with hq0top | hq0ne
    · rw [hq0top, C118a.smul_top_pos hℓ₃, top_add]
      exact le_top
    · obtain ⟨Hq0', hHq0'⟩ := ENat.ne_top_iff_exists.1 hq0ne
      rw [← hHq0'] at hsharp ⊢
      have hnat : Ha + Hb ≤ KΨ₃ + Hq0' := by exact_mod_cast hsharp
      have hgoal : ℓ₃ * (Ha + Hb) + 1 ≤ ℓ₃ * Hq0' + u₃ := by
        have h1 : ℓ₃ * (Ha + Hb) ≤ ℓ₃ * (KΨ₃ + Hq0') := Nat.mul_le_mul le_rfl hnat
        have h2 : ℓ₃ * (KΨ₃ + Hq0') = ℓ₃ * KΨ₃ + ℓ₃ * Hq0' := Nat.mul_add ℓ₃ KΨ₃ Hq0'
        omega
      calc ℓ₃ • ((Ha + Hb : ℕ) : ℕ∞) + 1 = ((ℓ₃ * (Ha + Hb) + 1 : ℕ) : ℕ∞) := by
            rw [nsmul_eq_mul]; push_cast; ring
        _ ≤ ((ℓ₃ * Hq0' + u₃ : ℕ) : ℕ∞) := by exact_mod_cast hgoal
        _ = ℓ₃ • ((Hq0' : ℕ) : ℕ∞) + ((u₃ : ℕ) : ℕ∞) := by
            rw [nsmul_eq_mul]; push_cast; ring

/-- The level-3 side set of a nonzero polynomial is nonempty (the dv3 twin of
`C134dv2g.dv2SideSet_nonempty_of_ne_zero`). -/
theorem dv3SideSet_nonempty_of_ne_zero (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic)
    (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    {f : Polynomial O} (hf : f ≠ 0) :
    (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃).Nonempty := by
  classical
  have hfin : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ ≠ ⊤ :=
    dv3Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hf
  obtain ⟨j₁, _, hj₁⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (f.natDegree + 1))
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
      (fun j => ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j + (u₃ * j : ℕ∞))
  have hside : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃
      = ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j₁ + (u₃ * j₁ : ℕ∞) := hj₁
  have hhgt₁ : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j₁ ≠ ⊤ := by
    intro htop
    apply hfin
    rw [hside, htop, C118a.smul_top_pos hℓ₃, top_add]
  exact ⟨j₁, mem_dv3SideSet_of_dv3OnSide L hℓ₂ hΨ₃ hΨ₃d ⟨hside, hhgt₁⟩⟩

/-! ## Part 3 — ★ the S2 discharge at `(g8, 85, 2)` (row D3-03)

The T2 chain's key proof `C136t.s2Mu3KeyPoly_g8 : S2Mu3KeyPoly (g8)` is anchored at
`s2Hgt₃ = toZ ∘ dv2Supp L Φ₂ · 21 2` (`WithTop ℤ`-valued); the generic predicates above are
`ℕ∞`-valued.  The bridge is the `toZ` order isomorphism (`toZ_le_toZ_iff`/`toZ_inj`),
exactly the value bridge `C134dv2g`'s docstring records for the level-2 S2 instance. -/

section S2

open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132nv4
open Uniformity.Density.Tower.C132nv6 Uniformity.Density.Tower.C132kp0
open Uniformity.Density.Tower.C132rp10b Uniformity.Density.Tower.C136t

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- `toZ` reflects and preserves strict order (the `<` face of `C130s6.toZ_le_toZ_iff`). -/
private theorem toZ_lt_toZ_iff {x y : ℕ∞} : toZ x < toZ y ↔ x < y := by
  constructor
  · intro h
    exact lt_of_le_of_ne (toZ_le_toZ_iff.mp h.le) fun e => h.ne (congrArg toZ e)
  · intro h
    exact lt_of_le_of_ne (toZ_le_toZ_iff.mpr h.le) fun e => h.ne (toZ_inj e)

/-- The `toZ` bridge for initial equivalence: the generic `ℕ∞`-valued `Mu3Equiv` at the S2
numerals IS the landed `s2Hgt₃`-anchored `S2Mu3InitialEquiv`. -/
private theorem mu3Equiv_iff_s2 (g h : Polynomial O) :
    Mu3Equiv ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 g h
      ↔ S2Mu3InitialEquiv h2 hq g h := by
  unfold Mu3Equiv S2Mu3InitialEquiv
  constructor
  · rintro (⟨hlt, heq⟩ | hz)
    · refine Or.inl ⟨?_, ?_⟩
      · rw [s2Hgt₃_eq_dv2Supp, s2Hgt₃_eq_dv2Supp]
        exact toZ_lt_toZ_iff.mpr hlt
      · rw [s2Hgt₃_eq_dv2Supp, s2Hgt₃_eq_dv2Supp]
        exact congrArg toZ heq
    · exact Or.inr hz
  · rintro (⟨hlt, heq⟩ | hz)
    · rw [s2Hgt₃_eq_dv2Supp, s2Hgt₃_eq_dv2Supp] at hlt
      rw [s2Hgt₃_eq_dv2Supp, s2Hgt₃_eq_dv2Supp] at heq
      exact Or.inl ⟨toZ_lt_toZ_iff.mp hlt, toZ_inj heq⟩
    · exact Or.inr hz

/-- The `toZ` bridge for μ₃-divisibility. -/
private theorem mu3Dvd_iff_s2 (φ g : Polynomial O) :
    Mu3Dvd ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 φ g
      ↔ S2Mu3Dvd h2 hq φ g :=
  exists_congr fun q => mu3Equiv_iff_s2 h2 hq g (φ * q)

/-- ★ **The T2 key proof, bridged**: `g₈` is a μ₃ key in the generic `ℕ∞`-valued sense —
`C136t.s2Mu3KeyPoly_g8` read through the `toZ` bridge. -/
theorem s2_isMu3Key_g8 :
    IsMu3Key ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) := by
  obtain ⟨hmon, hmin, hirr⟩ := s2Mu3KeyPoly_g8 h2 hq
  refine ⟨hmon,
    ⟨hmin.1, fun g hg hdeg hdvd => hmin.2 g hg hdeg ((mu3Dvd_iff_s2 h2 hq _ g).mp hdvd)⟩,
    fun g h hdvd => ?_⟩
  rcases hirr.2.2 g h ((mu3Dvd_iff_s2 h2 hq _ (g * h)).mp hdvd) with h' | h'
  · exact Or.inl ((mu3Dvd_iff_s2 h2 hq _ g).mpr h')
  · exact Or.inr ((mu3Dvd_iff_s2 h2 hq _ h).mpr h')

/-- The key's own level-3 grade, `ℕ∞`-cleared: `dv2Supp L Φ₂ g₈ 21 2 = 42` — literally
`C132rp10b.s2Hgt₃_g8` read backwards through `toZ`. -/
theorem s2_dv2Supp_g8 :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g8 h2 hq) 21 2
      = ((42 : ℕ) : ℕ∞) := by
  apply C130s6.toZ_inj
  rw [← s2Hgt₃_eq_dv2Supp h2 hq, s2Hgt₃_g8 h2 hq, toZ_coe]
  norm_num

/-- The inner multiplicativity at `(Φ₂, 21, 2)`: C132nv2's endpoint product law fired at
the landed survival `C132nv4.s2_dv2ResSurv_at_21` (the `hmul` supplier). -/
private theorem s2_dv2Supp_mul {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2
      = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
        + dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 := by
  obtain ⟨Hg, hHg⟩ := exists_dv2SideMin_height ((s2Tower h2 hq).levelDatum h2) g 21 2
    (s2_dv2SideSet_nonempty_at_21 h2 hq hg)
  obtain ⟨Hz, hHz⟩ := exists_dv2SideMin_height ((s2Tower h2 hq).levelDatum h2) z 21 2
    (s2_dv2SideSet_nonempty_at_21 h2 hq hz)
  exact s2_dv2Supp_mul_at_21 h2 hq (s2_dv2SideSet_nonempty_at_21 h2 hq hg)
    (s2_dv2SideSet_nonempty_at_21 h2 hq hz) hHg hHz

/-- ★ ★ **ROW D3-03 DISCHARGED: the μ₃-residual survival at `(g8, 85, 2)`** — the ONE
explicit hypothesis of C136d0's Part 3 (D3-02), now UNCONDITIONAL at the S2 depth-three
instance.  Fence: `2 · 42 = 84 < 85`. -/
theorem s2_dv3ResSurv_at_85 :
    Dv3ResSurv ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) 85 2 := by
  refine dv3ResSurv_of_mu3Key ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) ?_ (s2_isMu3Key_g8 h2 hq)
    (s2_dv2Supp_g8 h2 hq) (by norm_num) (by norm_num)
  intro g z hg hz
  exact s2_dv2Supp_mul h2 hq hg hz

/-- The S2 depth-three side set of a nonzero polynomial is nonempty (the μ₄ twin of
`C132nv6.s2_dv2SideSet_nonempty_at_21`). -/
theorem s2_dv3SideSet_nonempty_at_85 {g : Polynomial O} (hg : g ≠ 0) :
    (dv3SideSet ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) g 85 2).Nonempty := by
  exact dv3SideSet_nonempty_of_ne_zero ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) hg

/-! ## Part 4 — ★ row D3-04: the UNCONDITIONAL μ₄ product law -/

/-- ★ **ROW D3-04, nonzero factors** (the μ₄ twin of
`C132nv6.s2Hgt₃_mul_unconditional`): `s2Hgt₄ (g·z) = s2Hgt₄ g + s2Hgt₄ z` for `g, z ≠ 0` —
C136d0's endpoint assembly fired at the discharged survival. -/
theorem s2Hgt₄_mul_unconditional {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    s2Hgt₄ h2 hq (g * z) = s2Hgt₄ h2 hq g + s2Hgt₄ h2 hq z := by
  have hng := s2_dv3SideSet_nonempty_at_85 h2 hq hg
  have hnz := s2_dv3SideSet_nonempty_at_85 h2 hq hz
  obtain ⟨Hg, hHg⟩ := exists_dv3SideMin_height ((s2Tower h2 hq).levelDatum h2) g 85 2 hng
  obtain ⟨Hz, hHz⟩ := exists_dv3SideMin_height ((s2Tower h2 hq).levelDatum h2) z 85 2 hnz
  have hmul3 : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) (g * z) 85 2
      = dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) g 85 2
        + dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) z 85 2 :=
    dv3Supp_mul_eq_add_of_endpoint_le ((s2Tower h2 hq).levelDatum h2) (s2Φ₂_monic h2 hq)
      (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
      (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) (s2_dv3ResSurv_at_85 h2 hq)
      hng hnz hHg hHz
  rw [s2Hgt₄_eq_dv3Supp h2 hq (g * z), s2Hgt₄_eq_dv3Supp h2 hq g, s2Hgt₄_eq_dv3Supp h2 hq z,
    ← C130nv.toZ_add]
  exact congrArg toZ hmul3

/-- ★ **ROW D3-04, zero cases folded in** (the μ₄ twin of `C132nv6.s2Hgt₃_mul_all`):
`AddValuation.of`'s `hmul` shape. -/
theorem s2Hgt₄_mul_all (x y : Polynomial O) :
    s2Hgt₄ h2 hq (x * y) = s2Hgt₄ h2 hq x + s2Hgt₄ h2 hq y := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_mul, s2Hgt₄_zero h2 hq, top_add]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [mul_zero, s2Hgt₄_zero h2 hq, add_top]
  exact s2Hgt₄_mul_unconditional h2 hq hx hy

end S2

end Uniformity.Density.Tower.C136d3ad

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136d3ad.Mu3Equiv
#print axioms Uniformity.Density.Tower.C136d3ad.Mu3Dvd
#print axioms Uniformity.Density.Tower.C136d3ad.Mu3Minimal
#print axioms Uniformity.Density.Tower.C136d3ad.Mu3Prime
#print axioms Uniformity.Density.Tower.C136d3ad.IsMu3Key
#print axioms Uniformity.Density.Tower.C136d3ad.mu3Dvd_zero
#print axioms Uniformity.Density.Tower.C136d3ad.dv2Supp_mul_modByKey_le
#print axioms Uniformity.Density.Tower.C136d3ad.dv2Supp_mul_modByKey_eq
#print axioms Uniformity.Density.Tower.C136d3ad.dv2Supp_add_le_key_quot_add
#print axioms Uniformity.Density.Tower.C136d3ad.dv3ResSurv_of_mu3Key
#print axioms Uniformity.Density.Tower.C136d3ad.dv3SideSet_nonempty_of_ne_zero
#print axioms Uniformity.Density.Tower.C136d3ad.s2_isMu3Key_g8
#print axioms Uniformity.Density.Tower.C136d3ad.s2_dv2Supp_g8
#print axioms Uniformity.Density.Tower.C136d3ad.s2_dv3ResSurv_at_85
#print axioms Uniformity.Density.Tower.C136d3ad.s2_dv3SideSet_nonempty_at_85
#print axioms Uniformity.Density.Tower.C136d3ad.s2Hgt₄_mul_unconditional
#print axioms Uniformity.Density.Tower.C136d3ad.s2Hgt₄_mul_all

end AxCheck
