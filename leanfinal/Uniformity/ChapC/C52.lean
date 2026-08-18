/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C43
import Uniformity.ChapC.C50
import Uniformity.ChapC.C51

/-!
# Uniformity.ChapC.C52 — GENTOW-1(a): the weight characterization / composed budget floors

**Chapter C, NODE C.52** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §6, composed keys
and the tower bridges — the GENTOW1 half; the A-C.1 amendment set governs, and the SIGNATURES are
`[signed: A-C.1 — elaborated in leanspec/Leanspec/ChapC.lean]`).

Two signed declarations, both transcribed byte-identically from the signed block:

* `budgetFloor T μ₂ j a b` — the composed budget floor: the r2-F2 display evaluated at
  `(E₂, w(a,b), e₁e₂)`, with `w(a,b) = slotOffset T a b` (C.50). The numeric-gate mirror is
  `budgetFloorN` (leanspec §13 gates).
* `towerLocus_iff_budget` — membership in the tower-entry locus `𝒯 = towerLocus T μ₂` (C.51)
  is EXACTLY the conjunction of per-slot valuation floors on the composed digits
  `dev F.key (dev (composedKey T) f j) b` (C.43's wrap-corrected composed key, B.02's `dev`).

## Status

**SKELETON** — frozen statements committed first per the survival-floor rule; step lemmas and
proofs to follow in per-leg commits.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- the composed budget floor (the r2-F2 display at `(E₂, w(a,b), e₁e₂)`); the numeric-gate
mirror is `budgetFloorN`. -/
def budgetFloor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ j a b : ℕ) : ℕ :=
  let w := slotOffset T a b
  let tgt := (μ₂ - j) * T.E₂ - w
  let d := F.e₁ * T.e₂
  if (μ₂ - j) * T.E₂ < w then 0
  else (tgt + d - 1) / d + (if tgt % d == 0 then 1 else 0)

/-- **NODE C.52** (GENTOW-1(a)) — the weight characterization: `f ∈ 𝒯` iff every composed digit
clears its budget floor. Signed A-C.1; statement byte-frozen from `leanspec/Leanspec/ChapC.lean`. -/
theorem towerLocus_iff_budget {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = μ₂ * T.D₂) :
    f ∈ towerLocus T μ₂
      ↔ ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
          (budgetFloor T μ₂ j a b : ℕ∞)
            ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a) := by
  sorry

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.budgetFloor
#print axioms Uniformity.Density.Tower.towerLocus_iff_budget

end AxCheck
