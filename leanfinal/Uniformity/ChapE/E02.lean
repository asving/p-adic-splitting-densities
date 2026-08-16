/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E01

/-!
# Uniformity.ChapE.E02 — derived rung data: `slotCount`, `nextT`, `nextBound`

**Chapter E, NODE E.02** [def] (`blueprint/CHAP-E_sigma_ladder.md` §3, as amended by A-E.1),
ENV-E1 (the arithmetic arena: exponent and threshold bookkeeping, no local base `O`).

The three arithmetic recursions the σ-ladder runs on one rung datum `R = (ℓ, g, u, T)` (E.01):

* the **slot count** `slotCount = ℓ * g` — `EFF.HE7.47`'s `L_i := ℓ_i g_i`, the number of slots
  the rung's key-development occupies;
* the **next threshold** `nextT = slotCount * u` — `EFF.HE7.47`'s `T_{i+1} := L_i · u_i`, the
  disk threshold inherited by level `i+1` (`EFF.HE7.06`'s level-2 instance `T₂ := ℓ d_r · u`);
* the **bound step** `nextBound b = (slotCount − 1) * u + ℓ * b` — `EFF.HE7.23`'s recursion
  `bound_{i+1} = (ℓ_i g_i − 1)·u_i + ℓ_i·bound_i`, with `bound_0 = 0` supplied at the use site
  (the recursion is a step function here, not an iterator: the ladder's fold lives at §6).

The **degree multiplier** of the blueprint's STATEMENT (`EFF.HE7.47`'s key-degree recursion
`D_{i+1} := D_i · L_i`, i.e. `degMul = L`) is `slotCount` itself and gets NO separate
declaration — the signed SIGNATURE has three definitions, and a `degMul := slotCount` alias
would be a fourth name for one number.

`nextBound` uses truncated `ℕ` subtraction in `(slotCount − 1)`. This is faithful, not a
rounding: `1 ≤ ℓ` and `1 ≤ g` (E.01's fields) give `1 ≤ slotCount`, so the truncation never
fires on a legal rung. Consumers that need the subtraction to behave (E.31/E.35, and E.68's
frame table) should discharge it from `R.hℓ`/`R.hg` via `Nat.one_le_iff_ne_zero` /
`Nat.sub_add_cancel` rather than assume it.

Definitional, no proof obligation. DEPENDS: E.01.

ARITHMETIC AUDIT (blueprint, recomputed there fresh; reproduced here as the intended reading,
NOT as Lean gates — the executable frame table is E.68's). Base rung `(e₁,f₁,h,0) = (2,1,1,0)`:
`slotCount = 2`, `nextT = 2`, `nextBound 0 = (2−1)·1 + 2·0 = 1 = (D′−1)h` with `D′ = 2, h = 1`.
Level-2 rung `(2,1,5,2)` (the `q = 3` frame `(2,1,1,2,1,5)`): `nextBound 1 = (2·1−1)·5 + 2·1 = 7`,
matching the frame table's `thr₂ = 7`. Rung `(2,2,5,2)`: `nextBound 1 = (4−1)·5 + 2·1 = 17`.
Rung `(2,3,13,6)` over base `(3,1,2,0)` (`nextBound 0 = 4`): `(6−1)·13 + 2·4 = 73`.

SOURCE: `EFF.HE7.47` (the displayed recursions `L_i := ℓ_i g_i`, `D_{i+1} := D_i L_i`,
`T_{i+1} := L_i · u_i`); `EFF.HE7.23` (the bound recursion — one formula for the whole ladder,
"explicitly preserved by ANNEX R: 'The bound recursion is unchanged — values never see the
twist'"); `EFF.HE7.06` (`T₂ := ℓ d_r · u`, the level-2 instance).

TEETH: Q3 / HE7-LIFT2 (`EFF.HE7.23`: five level-2 frames' thresholds verified against exhaustive
enumeration) — these definitions are what E.31/E.35 state as Lean theorems and what E.68 fires
the numeric leg through.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- `L = ℓg`, the number of slots the rung's key-development occupies (`EFF.HE7.47`'s
`L_i := ℓ_i g_i`). It is also the key-degree multiplier `D_{i+1} = D_i · L_i`. -/
def RungDatum.slotCount (R : RungDatum) : ℕ := R.ℓ * R.g

/-- `T' = L·u`, the next level's disk threshold (`EFF.HE7.47`'s `T_{i+1} := L_i · u_i`). -/
def RungDatum.nextT (R : RungDatum) : ℕ := R.slotCount * R.u

/-- One step of the (LIFT) threshold recursion (`EFF.HE7.23`):
`bound' = (L−1)·u + ℓ·bound`. The base value `bound_0 = 0` is supplied at the use site. -/
def RungDatum.nextBound (R : RungDatum) (b : ℕ) : ℕ :=
  (R.slotCount - 1) * R.u + R.ℓ * b

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.RungDatum.slotCount
#print axioms Uniformity.Density.Ladder.RungDatum.nextT
#print axioms Uniformity.Density.Ladder.RungDatum.nextBound

end AxCheck
