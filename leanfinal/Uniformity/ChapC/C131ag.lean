/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C52
import Uniformity.ChapC.C131a
import Uniformity.ChapC.C50

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

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131ag.budgetFloor_le_of_succ_le
#print axioms Uniformity.Density.Tower.C131ag.budgetFloor_le_addVal_of_wtCoeff

end AxCheck
