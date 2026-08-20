/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C67

/-!
# Uniformity.ChapC.C64 — `blockDeg_eq` REFUTED: the naked exact-degree law is FALSE

**Chapter C, NODE C.64** [theorem] (leanspec `blockDeg_eq` + `mult₂_readable`).  **The signed
`blockDeg_eq` is FALSE** — the FIFTH member of the EXACT-DEGREE (D-CARRY) family, and the
cheapest refutation yet: every ingredient landed at C67 (2026-08-20), so this file is pure
assembly.  Both signed statements stay at the leanspec stubs (no axiom, no `sorry`, no
weakened restatement); `mult₂_readable` (the dv2-side translation half of the node) is NOT
adjudicated here — it is a different statement, untouched.

## The mechanism

`blockDeg_eq` asserts, at a bare `BlockContext L f`,

```
(blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f
```

Since `mult₂ L f := (blockFactor L f).natDegree / L.keyDeg₂` (a FLOOR), this is literally the
claim `L.keyDeg₂ ∣ (blockFactor L f).natDegree` — the divisibility that D13's refutation
killed (`C35B_D13_REFUTED_2026-08-20.md`): a labelled polynomial's degree need NOT be
divisible by `keyDeg₂`, because `HasLabel` loses provenance.  At the workhorse probe
`(s2Frame, L₀, g₀)` over `ℤ_[2]`: `BlockContext L₀ g₀` HOLDS (`blockContext_g₀`, C67 —
squarefreeness included), `blockFactor L₀ g₀ = g₀` (`blockFactor_g₀`), `keyDeg₂ = 2`,
`mult₂ = 1` (`mult₂_g₀`), and the conclusion demands **`3 = 2`**.

Contrast within the same family, machine-checked TODAY on both sides of the fault line:
C.48's `fullSide_block` (LANDED) carries the degree law as a HYPOTHESIS (`hdeg`) — the
protected shape; C.64's `blockDeg_eq` asserts it as a CONCLUSION from floor-divided data —
the refuted shape.

## Registry consequence (for the D-CARRY sweep record)

The corrected mechanical check ("does the conclusion assert an exact degree of a labelled
object?") run over the signed spec (2026-08-20, this session) returns EIGHT sites:
`blockFactor_spec` (BLOCKED, member), `level2_peel` (BLOCKED, member), `multiplicity_tie`
(REFUTED, C67), **`blockDeg_eq` (REFUTED, here)**, `fullSide_block` (LANDED — protected by
its `hdeg` HYPOTHESIS), and THREE remaining candidates — `partial_projection` (C.77 clause
(iii)), `partial_block_decision` (C.78), `tie_pure_power` (C.80) — all tower-borne
(`BlockContext (T.levelDatum hπ) f`), so the `s2Frame` probe CANNOT instantiate them
(`T.hcomp : 2 ≤ e₂f₂` excludes `keyDeg₂ = 2` at `d_r = ℓ = 1`); a tower-borne probe (the
`linTower` analog of `g₀`, `keyDeg₂ = D₂ = 2` at `(e₂, f₂) = (2, 1)`) is the analysis route,
NOT run here.

## Status

Zero `sorry`; axiom footprint Lean-core only (AxCheck footer).  No cite.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C64

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Tower.C35b
open Uniformity.Density.Tower.C67

/-- The signed `blockDeg_eq` (NODE C.64), closed over everything — `blockDegEq_false` below
proves this FALSE. -/
def BlockDegEqStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O)
    (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key
      (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (L : LevelDatum F H₀ hpin) (_hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (f : Polynomial O) (_hctx : BlockContext L f),
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f

/-- ★ **NODE C.64's signed `blockDeg_eq` is FALSE** — at `(s2Frame, L₀, g₀)` over `ℤ_[2]`,
where the block context holds (C67), the block is `g₀` itself, and the conclusion demands
`3 = 2 · 1`. -/
theorem blockDegEq_false : ¬ BlockDegEqStatement := by
  intro hax
  have h := hax ℤ_[2] (2 : ℤ_[2]) (s2Frame h2_padic rc2) 1
    (s2Frame_pin h2_padic rc2) (L₀ h2_padic rc2) h2_padic (g₀ ℤ_[2])
    (blockContext_g₀ h2_padic rc2)
  have hkd : (L₀ h2_padic rc2).keyDeg₂ = 2 := by
    rw [LevelDatum.keyDeg₂, e1_eq h2_padic rc2, f1_eq h2_padic rc2,
      show (L₀ h2_padic rc2).ℓ = 1 from rfl,
      show (L₀ h2_padic rc2).r = ρ h2_padic rc2 from rfl, ρ_natDegree h2_padic rc2]
  rw [blockFactor_g₀ h2_padic rc2, g₀_natDegree, mult₂_g₀ h2_padic rc2, hkd] at h
  norm_num at h

end Uniformity.Density.Tower.C64

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C64.BlockDegEqStatement
#print axioms Uniformity.Density.Tower.C64.blockDegEq_false

end AxCheck
