/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Defs

/-!
# Uniformity.ChapH.H62 — the R2 counterexample: triangular WITHOUT unit pivots

**Chapter H, NODE H.62** (`blueprint/CHAP-H_general_induction.md` §9, source `EFF.GENIND.155`
(`R2.0`, CODEX F1's counterexample verbatim: *"Codex's valid toy: `(x, y) ↦ (x, (x+π)y)` mod `π²`,
triangular, fiber collapses at `x = 0`"*), with `EFF.GENIND.156` (the rider's sharpness witness)
and `EFF.GENIND.157` (*"The toy's pivot `x + π` is the lead of a non-monic multiplier — a shape the
displayed species exclude"*)).

Over `R = ZMod 4` with `π = 2`, the map `Φ v = ![v 0, (v 0 + 2) * v 1]` is triangular — the second
output depends on `v 1` with a coefficient reading `v 0` only — but is **not surjective**, and its
fibres are **not** of constant size. So H.60's unit-pivot hypothesis cannot be dropped: this file is
the negative half of the `ANNEX R R2` repair whose positive half is H.60.

DEPENDS: none. **Deliberately independent of H.59** — the toy is *not* a `TriangularUnitPivot`,
which is exactly the point; no `import Uniformity.ChapH.H59` here.

## Why the counterexample is a node and not a comment

Three reasons, all recorded in the corpus. (1) The gap was invisible to the executable battery by
construction (`EFF.GENIND.155`: *"the runner only ever executes monic ledgers, so the failure mode
is off its state space … the runs EXCLUDE the signature and therefore cannot FIND the missing
hypothesis"*). (2) `EFF.GENIND.157`'s species check is `PROOF-ONLY`, so the only machine evidence
for the whole repair is leg G's planted mutant — and this node is that mutant, promoted to a
theorem. (3) A future node tempted to state "triangular ⟹ bijective" is refuted here, loudly.

## Arithmetic audit (transcribed from the blueprint, and machine-checked below)

Fibre over `![0,0]`: `v 0 = 0` and `2 * v 1 = 0` ⟹ `v 1 ∈ {0, 2}` ⟹ 2. Fibre over `![1,0]`:
`v 0 = 1` and `3 * v 1 = 0` ⟹ `v 1 = 0` (`3` is a unit mod `4`) ⟹ 1. Image size: at `v 0 = 0` the
second coordinate ranges over `{0,2}` (2 values); at `v 0 ∈ {1,3}` over all 4; at `v 0 = 2` the
pivot is `4 = 0`, so the second coordinate is `0` only (1 value) — total `2 + 4 + 1 + 4 = 11 < 16`,
and `![0,1]` is missing. The image count is landed below as `codexToy_image_card`.

## Proof method

`by decide` throughout: the domain has `16` elements, and `Fintype`/`DecidableEq` instances for
`Fin 2 → ZMod 4` plus `Fintype.decidableSurjectiveFintype` make all three statements decidable.
`native_decide` is **forbidden** here (it would add `Lean.ofReduceBool` to the footprint) and is
not needed — the kernel evaluates all three in well under a second.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- Codex's toy (`ANNEX R R2.0`): `(x, y) ↦ (x, (x+π)y)` mod `π²`, at `π = 2`, `R = ZMod 4`. -/
def codexToy (v : Fin 2 → ZMod 4) : Fin 2 → ZMod 4 := ![v 0, (v 0 + 2) * v 1]

/-- **Triangular is not enough for ONTO.** The toy misses `![0, 1]`: at `v 0 = 0` the pivot
`0 + 2 = 2` is a non-unit of `ZMod 4` and `2 * v 1 ∈ {0, 2}`. -/
theorem codexToy_not_surjective : ¬ Function.Surjective codexToy := by decide

/-- **Triangular is not enough for CONSTANT FIBRES.** Two fibres of different sizes: `2` over
`![0, 0]` (the collapsed pivot `2` kills a coordinate) versus `1` over `![1, 0]` (the pivot `3` is
a unit). -/
theorem codexToy_fibre_not_constant :
    (Finset.univ.filter (fun v : Fin 2 → ZMod 4 => codexToy v = ![0, 0])).card = 2 ∧
    (Finset.univ.filter (fun v : Fin 2 → ZMod 4 => codexToy v = ![1, 0])).card = 1 := by
  constructor <;> decide

/-- The blueprint's ARITHMETIC AUDIT, machine-checked: the image has exactly `11` of the `16`
points (`2 + 4 + 1 + 4`), which re-derives `codexToy_not_surjective` by counting. -/
theorem codexToy_image_card : (Finset.univ.image codexToy).card = 11 := by decide

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.codexToy
#print axioms Uniformity.Density.Induction.codexToy_not_surjective
#print axioms Uniformity.Density.Induction.codexToy_fibre_not_constant
#print axioms Uniformity.Density.Induction.codexToy_image_card

end AxCheck
