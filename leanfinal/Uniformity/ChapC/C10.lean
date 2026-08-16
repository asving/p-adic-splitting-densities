/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C09

/-!
# Uniformity.ChapC.C10 — dictionary arithmetic: the `D″` regrouping, the seam, the `L_λ ≥ 4` floor

**Chapter C, NODE C.10** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame
and the level dictionary; the A-C.1 amendment set governs). ENV-C5 (arithmetic only; stated over
the `LevelDatum` structure for keying). Three signed public declarations.

*Dictionary arithmetic.* For a level datum `L` over a frame `F` (C.09 — the level-2 label
`(λ = u/ℓ, r)` with its dictionary numerals):

* **(i) `keyDeg₂_regroup`** — `D″ = (e₁ℓ)(f₁d_r)`. C.09 DEFINES `keyDeg₂` as `(e₁f₁)·ℓ·d_r`,
  i.e. grouped as `D′·ℓ·d_r` with `D′ = e₁f₁` the stage key degree. This node supplies the OTHER
  grouping, `(e₁ℓ)·(f₁d_r)`, which is the arithmetically identical but semantically different
  read: `e₁ℓ` is the level-2 **ramification** index and `f₁d_r` the level-2 **residue** degree.
  `EFF.HE6R1.16`'s audit row is exactly this equality (`D″ = D′ℓd_r = (e₁f₁)ℓd_r = (e₁ℓ)(f₁d_r)`
  ✓), and it is what drives the peel's `e·f` sandwich downstream.
* **(ii) `seam_mul`** — the honest integer form of `T₂ = ℓ·d_r·λ` at `λ = u/ℓ`. C.09 clears the
  denominator by DEFINING `seam := d_r·u`; the statement that this is the right clearing is
  `ℓ·T₂ = (ℓd_r)·u`. The blueprint's STATEMENT is explicit that the tempting form
  `ℓ·T₂ = D″·u/(e₁f₁)` is **avoided** — it would need a `ℕ`-division that is exact only under
  side conditions this node does not carry, and truncated division is a silent-falsehood
  generator. The multiplicative form has no division and no hypotheses.
* **(iii) `four_le_keyDeg₂`** — the jump-frame floor `L_λ ≥ 4` that §5's descent grammar consumes.
  Two "genuinely at level ≥ 2" hypotheses (`2 ≤ D′` and `2 ≤ ℓd_r`) multiply to `4 ≤ D″`. This is
  `EFF.HE6R1.08`/F1's non-propagation arithmetic (`m ≥ 2 ∧ ℓ₂d_{r₂} ≥ 2 ⟹ ≥ 4`).

## Why these are not `rfl`

All three are `ℕ`-arithmetic over three opaque naturals (`F.e₁`, `F.f₁`, `L.ℓ`, `L.r.natDegree`,
`L.u`), so the content is associativity/commutativity, not unfolding. (i) and (ii) are `ring`
after the definitional `simp only`; (iii) is `Nat.mul_le_mul` against the reassociated product.
There is nothing valuation-theoretic here, which is why the blueprint files the node under ENV-C5
(arithmetic) even though it is stated over the ENV-C1 structure.

## The `ℓ = 1` degeneration, clause (iii) of the STATEMENT prose

The blueprint's STATEMENT lists a third bullet before the floor — *"at `L.ℓ = 1` the dictionary
degenerates benignly (`EFF.HE6R1.06`): `keyDeg₂ = D′·d_r`, `seam = d_r·u`, and the level-2
normalization scale collapses"*. It carries **no signed declaration** (the A-C.1 SIGNATURE block
has exactly the three theorems below, and the gate-verified twin
`leanspec/Leanspec/ChapC.lean` axiomatises exactly those three). This is not a gap: at `L.ℓ = 1`
both listed identities are the DEFINITIONS with `1` substituted (`keyDeg₂ = (e₁f₁)·1·d_r` and
`seam = d_r·u`, the latter not even mentioning `ℓ`), so a Lean statement of them would be
`by simp` on an unfolded numeral and would add nothing. The third half of the bullet — the
collapse of the level-2 normalization scale — is a statement about C.11's `dv2Hgt`, not about
C.09's numerals, and it belongs to C.11's recursion, not here. Recorded so a later reader does not
mistake the missing declaration for a dropped clause.

## Hypothesis hygiene on (iii)

Neither of `four_le_keyDeg₂`'s two hypotheses can be dropped by reading the structures. The only
numeric constraints C.09 and C.01 impose on the four factors are positivity — `0 < ℓ`, `0 < d_r`
(C.09's `hℓ`, `hrdeg`) and `0 < e₁`, `0 < f₁` (C.01's `he₁`, `hf₁`) — and the assignment
`e₁ = f₁ = ℓ = d_r = 1` violates none of them while making `keyDeg₂ = 1 < 4`. So the conclusion is
not a consequence of the fields, and both binders stay. They are supplied by the callers in §5:
the jump trigger is what makes `ℓd_r ≥ 2` true.

**DEPENDS.** C.09 (`LevelDatum`, `keyDeg₂`, `seam`) — by committed node ID (GC-13(b)). C.01
(`KeyFrame`) enters through C.09's own signature. The import is `Uniformity.ChapC.C09`.

**PROOF.** The blueprint's three steps, unchanged: 1. `ring`. 2. `ring`. 3. `Nat.mul_le_mul`
(H.03's pattern) against `keyDeg₂` reassociated by `mul_assoc`.

SOURCE: `EFF.HE6R1.16` (audit: `D″ = D′ℓd_r = (e₁f₁)ℓd_r = (e₁ℓ)(f₁d_r)` ✓); `EFF.HE6R1.18` (the
dictionary audit rows); `EFF.HE6R1.06` (the `ℓ = 1` degeneration table); `EFF.HE6R1.08` / F1's
non-propagation arithmetic (`m ≥ 2 ∧ ℓ₂d_{r₂} ≥ 2 ⟹ ≥ 4`).

**TEETH.** `EFF.HE6R1.18`'s frame audit row ("Every frame parameter is forced and every one
checks") → **Lean theorem**, this node. Per GC-11's numerics rider the frame's concrete values
(`(e₁,f₁,h) = (2,1,1)`, `Φ′ = x²−π`, `D″ = 4`, `T₂ = 2λ`, `μ₂ = 2`) are NOT hard-coded here — this
node proves the general identities and the numerals re-fire as executable regressions at blueprint
§13 (`q = 3` and the `q = 2` analogue). The general statements specialise to the audit row by
substitution: at `e₁ = 2, f₁ = 1, ℓ = 2, d_r = 1`, (i) reads `4 = (2·2)(1·1)` and (iii)'s
hypotheses `2 ≤ 2` and `2 ≤ 2` hold, giving `4 ≤ 4` — the audit's `D″ = 4` on the nose.

ENVIRONMENT: ENV-C5.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **C.10 (i) — the `D″` regrouping.** `D″ = D′ℓd_r = (e₁ℓ)(f₁d_r)`: the level-2 key degree
read as (ramification index) × (residue degree). `EFF.HE6R1.16`'s audit row. -/
theorem LevelDatum.keyDeg₂_regroup {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    L.keyDeg₂ = (F.e₁ * L.ℓ) * (F.f₁ * L.r.natDegree) := by
  simp only [LevelDatum.keyDeg₂]
  ring

/-- **C.10 (ii) — the seam, cleared.** `ℓ·T₂ = (ℓd_r)·u`, the division-free integer form of
`T₂ = ℓd_rλ` at `λ = u/ℓ`. The `ℕ`-division form is deliberately avoided (see the file
docstring). -/
theorem LevelDatum.seam_mul {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    L.ℓ * L.seam = (L.ℓ * L.r.natDegree) * L.u := by
  simp only [LevelDatum.seam]
  ring

/-- **C.10 (iii) — the jump-frame floor `L_λ ≥ 4`.** Genuinely-level-2 on both factors
(`2 ≤ D′` and `2 ≤ ℓd_r`) forces `4 ≤ D″`. Neither binder is redundant: the structures constrain
the four factors only by positivity, and at `e₁ = f₁ = ℓ = d_r = 1` one has `keyDeg₂ = 1`. -/
theorem LevelDatum.four_le_keyDeg₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hD : 2 ≤ F.e₁ * F.f₁) (hjump : 2 ≤ L.ℓ * L.r.natDegree) : 4 ≤ L.keyDeg₂ := by
  have h : 2 * 2 ≤ (F.e₁ * F.f₁) * (L.ℓ * L.r.natDegree) := Nat.mul_le_mul hD hjump
  simpa [LevelDatum.keyDeg₂, mul_assoc] using h

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.LevelDatum.keyDeg₂_regroup
#print axioms Uniformity.Density.Tower.LevelDatum.seam_mul
#print axioms Uniformity.Density.Tower.LevelDatum.four_le_keyDeg₂

end AxCheck
