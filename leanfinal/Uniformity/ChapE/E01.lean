/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Nat.GCD.Basic

/-!
# Uniformity.ChapE.E01 — `RungDatum`, the arithmetic core of one σ-ladder level

**Chapter E, NODE E.01** (`blueprint/CHAP-E_sigma_ladder.md` §3, as amended by A-E.1). A *rung
datum* `(ℓ, g, u, T)` is the arithmetic core of `EFF.HE7.47`'s level datum
`𝔇_i = (Φ_i, D_i, w_i, ℓ_i, g_i, u_i, K_i, K_{i+1}, 𝒫_i)`: the slope denominator `ℓ` (the rung's
value-group index), the residual-factor degree `g` (the residue-degree jump), the slope numerator
`u`, and the rung's disk threshold `T`. The polynomial `Φ_i`, the fields `K_i ⊆ K_{i+1}` and the
point set `𝒫_i` are *carrier* data and live in §4's structures (`SlotCarrier`, `BlockData`,
`RungInterface`), never here.

Side conditions, the corpus's verbatim: `1 ≤ ℓ`, `1 ≤ g`, `Nat.Coprime u ℓ` (the slope
`λ = u/ℓ` in lowest terms) and the **node condition** `ℓ * T < u`, i.e. `λ > T`
(DEFINITION HE7-2's `λ_i > T_i`).

The **base rung** (level 0 → 1) is `(ℓ, g, u, T) = (e₁, f₁, h, 0)` — `EFF.HE7.47`'s `𝔇_0` with
`T_0 := 0`, where the node condition degenerates to `1 ≤ h`. The **level-2 rung** is
`(ℓ, d_r, u, D′h)` with `u = ℓλ > ℓD′h` (DEFINITION HE7-1's `λ > D′h`, `EFF.HE7.06`).

CARRIER FENCE (blueprint): `u : ℕ`, not `ℤ` — every consumed height in the corpus sits strictly
above the rung's threshold (`EFF.HE7.24`'s use-site chain), and `T ≥ 0` with the node condition
forces `u ≥ 1`. The normalizer `ϖ = x^{i₀}π^{a₀}` with possibly `a₀ < 0` (`EFF.HE7.05`) is
chapter-C carrier content, not a rung field.

CONSUMER WARNING (blueprint defect A-E.1/E-D7): the node condition `ℓ * T < u` is real strength.
The third `q = 3` sharpness frame of E.68, `(2,2,1,2,2,7)`, is NOT a legal level-2 rung at its
corpus threshold `T₂ = D′h = 4` (`¬ (2 * 4 < 7)`). A consumer that builds a `RungDatum` from an
enumeration frame must check `hnode` first.

Definitional, no proof obligation. DEPENDS: none.

SOURCE: `EFF.HE7.47` (DEFINITION HE7-2's tuple: `ℓ_i ≥ 1`, `g_i ≥ 1`, `gcd(u_i, ℓ_i) = 1`, the
node condition `λ_i > T_i`, and the level-0 datum); `EFF.HE7.06` (DEFINITION HE7-1:
`λ = u/ℓ ∈ ℚ` in lowest terms, `λ > D′h`, `d_r := deg r`); `EFF.T2.04` (`(DEG-EF)`, carried at
E.10 as a field, never inferred from monicity).

TEETH: HE7-T-SLOT2TIE (`EFF.HE7.06`: at `gcd(u, ℓ) ≠ 1` the slot-min is not exact) — the `hcop`
field makes that tooth's hypothesis structural.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- A **rung datum**: the arithmetic core of one σ-ladder level (`EFF.HE7.47`/`.107`).
`ℓ` = slope denominator (value-index jump), `g` = residual degree (residue-degree jump),
`u` = slope numerator, `T` = the rung's disk threshold; `ℓ*T < u` is the node condition
`λ > T`. -/
structure RungDatum where
  /-- The slope denominator; the rung's value-group index. -/
  ℓ : ℕ
  /-- The residual-factor degree; the rung's residue-degree jump. -/
  g : ℕ
  /-- The slope numerator: the slope is `λ = u / ℓ`. -/
  u : ℕ
  /-- The rung's disk threshold `T_i`. -/
  T : ℕ
  hℓ : 1 ≤ ℓ
  hg : 1 ≤ g
  hcop : Nat.Coprime u ℓ
  hnode : ℓ * T < u

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.RungDatum
#print axioms Uniformity.Density.Ladder.RungDatum.mk

end AxCheck
