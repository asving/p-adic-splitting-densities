/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C52
import Uniformity.ChapC.C131a
import Uniformity.ChapC.C50
import Uniformity.ChapC.C131af

/-!
# Uniformity.ChapC.C131ag — Chapter C, NODE C.131ag′ (unit U-ARITH, stage 1)

(`docs/in-progress/AF_REVERSE_PLAN_2026-08-25.md` §3, unit U-ARITH.)

Pure ceiling arithmetic for the af′-reverse route: `budgetFloor`'s `⌈·⌉`-plus-tie display is
EXACTLY the least `v` clearing a strict `ℕ` floor `X + 1 ≤ d·v + w` (AF-5a), and the ℕ∞
wrapper that turns a `wtCoeff` floor into a `budgetFloor`-vs-`addVal` bound (AF-5b). Both are
Lean-core, no cite, no `sorry`. `AF-5a` is proved directly (never handing `omega` a combined
mod/div goal — the pinned `omega` is incomplete there; every division fact is discharged first
via `Nat.div_add_mod`/`Nat.mul_add_div`/`Nat.div_eq_of_lt`, and `omega` only ever sees the
resulting linear facts), mirroring the case split already worked out in `C52.budgetFloor_le_iff`
and `C131ae.budgetFloor_wtCoeff_bound` (same genre, opposite direction).

Later units (U-ASSEMBLE, per the plan) EXTEND this file with `AF-6a`/`AF-6b`; this stage adds
only `AF-5a`/`AF-5b`.

## U-ASSEMBLE (stage 2)

Adds `AF-6a` (`budget_of_mem_towerLocus`, ★ NODE C.131af′) and `AF-6b`
(`towerLocus_iff_budget`, ★ NODE C.131ag′, the byte-mirror of leanspec `ChapC.lean:2030`'s
signed `axiom towerLocus_iff_budget`). `AF-6a` chains AF-4
(`Uniformity.Density.Tower.towerLocus_dev_strict_floor`, U-HEART's strict per-digit floor,
landed in `C131af.lean`) through the flattening bridge
`C131t.dv2Hgt_eq_WT_phiNF` → `C131a.WT_le_wtCoeff` → `C131k.xNF_coeff`/`xDigit_eq_dev` into
AF-5b's ceiling wrapper. `AF-6b` assembles the iff from `AF-6a` (→) and the already-landed
`Uniformity.Density.Tower.mem_towerLocus_of_budget` (C131ae.lean, ←). Both stages Lean-core
plus the inherited declared cite `fgmn_dv_exact_mul` (C66b), never re-consumed independently.
-/

namespace Uniformity.Density.Tower.C131ag

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131a

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **AF-5a** (`budgetFloor_le_of_succ_le`, pure `ℕ`): the ceiling-plus-tie display, in
`budgetFloor`'s own spelling (`X := (μ₂−j)E₂`, `w := slotOffset`, `d := e₁e₂`), is `≤ v`
whenever the strict floor `X + 1 ≤ d·v + w` holds. Template precedent:
`C52.budgetFloor_le_iff`'s `hkey` block (reverse direction). -/
theorem budgetFloor_le_of_succ_le {d v w X : ℕ} (hd : 0 < d) (h : X + 1 ≤ d * v + w) :
    (if X < w then 0
     else (X - w + d - 1) / d + (if (X - w) % d == 0 then 1 else 0)) ≤ v := by
  by_cases hlt : X < w
  · simp [hlt]
  · rw [if_neg hlt]
    push Not at hlt
    have hqr := Nat.div_add_mod (X - w) d
    have hrlt : (X - w) % d < d := Nat.mod_lt _ hd
    have hkey : (X - w + d - 1) / d + (if (X - w) % d == 0 then 1 else 0)
        = (X - w) / d + 1 := by
      simp only [beq_iff_eq]
      by_cases h0 : (X - w) % d = 0
      · rw [if_pos h0]
        have h1 : X - w + d - 1 = d * ((X - w) / d) + (d - 1) := by omega
        have hdiv : (d * ((X - w) / d) + (d - 1)) / d = (X - w) / d := by
          rw [Nat.mul_add_div hd, Nat.div_eq_of_lt (Nat.sub_lt hd Nat.one_pos), Nat.add_zero]
        rw [h1, hdiv]
      · rw [if_neg h0]
        have hrpos : 0 < (X - w) % d := Nat.pos_of_ne_zero h0
        have hmul : d * ((X - w) / d + 1) = d * ((X - w) / d) + d := by ring
        have h1 : X - w + d - 1 = d * ((X - w) / d + 1) + ((X - w) % d - 1) := by omega
        have hdiv : (d * ((X - w) / d + 1) + ((X - w) % d - 1)) / d
            = (X - w) / d + 1 := by
          rw [Nat.mul_add_div hd,
            Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) hrlt), Nat.add_zero]
        rw [h1, hdiv]
    rw [hkey, Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul hd, Nat.mul_comm v d]
    omega

/-- **AF-5b** (`budgetFloor_le_addVal_of_wtCoeff`, the `ℕ∞` wrapper): a strict floor on
`wtCoeff T c a b` converts to `budgetFloor T μ₂ j a b ≤ addVal O c`, via AF-5a at
`d := F.e₁ * T.e₂`, `X := (μ₂ − j) * T.E₂`, `w := slotOffset T a b`. -/
theorem budgetFloor_le_addVal_of_wtCoeff {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {μ₂ j a b : ℕ} {c : O}
    (hle : (((μ₂ - j) * T.E₂ + 1 : ℕ) : ℕ∞) ≤ wtCoeff T c a b) :
    (budgetFloor T μ₂ j a b : ℕ∞) ≤ addVal O c := by
  have hposE : 0 < F.e₁ * T.e₂ := Nat.mul_pos F.he₁ T.he₂
  rcases eq_or_ne (addVal O c) ⊤ with hT | hT
  · rw [hT]; exact le_top
  · obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp hT
    have hwc : wtCoeff T c a b
        = (((F.e₁ * T.e₂) * v + slotOffset T a b : ℕ) : ℕ∞) := by
      rw [wtCoeff, slotOffset, ← hv]
      push_cast [nsmul_eq_mul]
      ring
    rw [hwc] at hle
    have hle' : (μ₂ - j) * T.E₂ + 1 ≤ (F.e₁ * T.e₂) * v + slotOffset T a b := by
      exact_mod_cast hle
    have hbud : budgetFloor T μ₂ j a b ≤ v :=
      budgetFloor_le_of_succ_le hposE hle'
    calc (budgetFloor T μ₂ j a b : ℕ∞) ≤ (v : ℕ∞) := by exact_mod_cast hbud
      _ = addVal O c := hv

end Uniformity.Density.Tower.C131ag

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131a Uniformity.Density.Tower.C131k
open Uniformity.Density.Tower.C131t

/-! ## AF-6a — locus membership implies every budget floor (U-ASSEMBLE, ★ NODE C.131af′) -/

set_option linter.unusedVariables false in
/-- **AF-6a (★ `budget_of_mem_towerLocus`, NODE C.131af′, `EFF.GENTOW1.22`).** A locus
member `f ∈ towerLocus T μ₂` clears every budget floor: AF-4's strict per-digit floor on
`dev Φ₂ f j`, flattened through the two-index weight (`dv2Hgt_eq_WT_phiNF`,
`WT_le_wtCoeff`, `xNF_coeff`/`xDigit_eq_dev`) into a `wtCoeff` floor on the two-key
development digit's own scalar coefficient, then converted to the `budgetFloor`-vs-`addVal`
shape by AF-5b. The range hypotheses `ha`/`hb` are UNUSED — the floor holds for every
`a b`, not just those in range — kept only to match the signed C.52 shape. -/
theorem Uniformity.Density.Tower.budget_of_mem_towerLocus
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] {μ₂ : ℕ} (hμ₂ : 0 < μ₂)
    {f : Polynomial O} (hf : f ∈ towerLocus T μ₂)
    (j a b : ℕ) (hj : j < μ₂) (ha : a < F.e₁ * F.f₁) (hb : b < T.e₂ * T.f₂) :
    (budgetFloor T μ₂ j a b : ℕ∞)
      ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a) := by
  have hfloor : (((μ₂ - j) * T.E₂ + 1 : ℕ) : ℕ∞)
      ≤ dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) :=
    towerLocus_dev_strict_floor T hπ hh hμ₂ hf hj
  rw [dv2Hgt_eq_WT_phiNF T hπ] at hfloor
  have hWT := WT_le_wtCoeff T (xNF F (dev (composedKey T) f j)) a b
  rw [xNF_coeff, xDigit_eq_dev] at hWT
  exact Uniformity.Density.Tower.C131ag.budgetFloor_le_addVal_of_wtCoeff T (hfloor.trans hWT)

/-! ## AF-6b — the signed iff (U-ASSEMBLE, ★ NODE C.131ag′ / signed C.52) -/

/-- **AF-6b (★ `towerLocus_iff_budget`, NODE C.131ag′, `EFF.GENTOW1.15`).** The signed iff,
byte-mirroring leanspec `ChapC.lean:2030`'s `axiom towerLocus_iff_budget` (modulo
`axiom → theorem` and namespace): the forward direction is AF-6a; the reverse direction is
the already-landed `Uniformity.Density.Tower.mem_towerLocus_of_budget` (C131ae.lean). -/
theorem Uniformity.Density.Tower.towerLocus_iff_budget
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = μ₂ * T.D₂) :
    f ∈ towerLocus T μ₂
      ↔ ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
          (budgetFloor T μ₂ j a b : ℕ∞)
            ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a) :=
  ⟨fun hmem j a b hj ha hb =>
      Uniformity.Density.Tower.budget_of_mem_towerLocus T hπ hh hμ₂ hmem j a b hj ha hb,
   fun hbud => mem_towerLocus_of_budget T hπ hh hμ₂ hf hdeg hbud⟩

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131ag.budgetFloor_le_of_succ_le
#print axioms Uniformity.Density.Tower.C131ag.budgetFloor_le_addVal_of_wtCoeff
#print axioms Uniformity.Density.Tower.budget_of_mem_towerLocus
#print axioms Uniformity.Density.Tower.towerLocus_iff_budget

end AxCheck
