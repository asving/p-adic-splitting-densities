/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E07

/-!
# Uniformity.ChapE.E59 — the per-block level-jump gate and the μ ≤ 3 non-propagation

**Chapter E, NODE E.59** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §8 — root-continuation and
exhaust: the refine chain, the block split, termination), ENV-E1.

Two clauses of pure `ℕ`-arithmetic, the block-reduced form of the μ ≥ 4 gate:

* `block_jump_gate` — a block whose single side has length `L = k · (ℓ · d)`, with `k ≥ 2` the
  pure-residual multiplicity and `ℓ · d ≥ 2` the deciding factor's product, has `L ≥ 4`. Since any
  interface containing that block has `μ = Σ len ≥ L`, every level jump sits at `μ ≥ 4`. This is
  `EFF.HE7.96`(a)'s *"the μ₂ ≥ 4 gate is unchanged: `L_{λ,r} = k·ℓ₂ deg r ≥ 4`, so
  `μ₂ ≥ L_λ ≥ L_{λ,r} ≥ 4`"* — the gate SURVIVES the block reduction.
* `no_jump_of_mu_le_three` — the contrapositive, in the shape its consumers use: at `μ ≤ 3` a
  block of length `L ≤ μ` cannot reach the jump floor. This is the NON-PROPAGATION display of
  `EFF.HE7.14`, consumed by E.52 and by chapter I's degree-indexing; it is what makes
  HE7.A(3)'s μ₂ ≤ 3 clause — hence COROLLARY HE7.B(i)'s `n ≤ 15` coverage — go through.

## Relation to E.07 (no duplicated content)

Clause 1 is E.07(i) `jump_floor` (`2 ≤ m → 2 ≤ p → 4 ≤ m * p`) instantiated at the block's own
`(k, ℓ·d)` split and transported along `hL`. It is landed as a separate declaration because the
BLOCK-reduced phrasing is what E.52 and chapter I cite by name; the arithmetic is E.07's and is
consumed, not re-proved. Clause 2 is `omega`.

## Reading the hypotheses honestly

`hld : 2 ≤ ℓ * d` is the PRODUCT hypothesis, matching E.07's `[r1]` rider: it covers both live
branches — `ℓ ≥ 2` with `d_r ≥ 1`, and `ℓ = 1` with `d_r ≥ 2` — without asserting either factor is
individually ≥ 2. Clause 2's `hLμ : L ≤ μ` is the interface inequality `L ≤ Σ len = μ` supplied by
the caller (E.60's clause (1)); this node does not re-derive it.

DEPENDS: E.07 (`jump_floor`).

SOURCE: `EFF.HE7.96`(a) (*"the μ₂ ≥ 4 gate is unchanged: `L_{λ,r} = k·ℓ₂ deg r ≥ 4`, so
`μ₂ ≥ L_λ ≥ L_{λ,r} ≥ 4`, so the μ₂ ≤ 3 non-propagation of HE7.A(3) — hence COROLLARY HE7.B(i)'s
n ≤ 15 coverage — is unchanged by the block reduction"*); `EFF.HE7.14` (the non-propagation
display).

TEETH: `he7annex_supp.py` (96/96 at μ₂ = 4 — the first live jump row) → **Lean theorem**.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **NODE E.59**, clause 1 — *the per-block level-jump gate*: a jump configuration on a block
(pure-residual multiplicity `k ≥ 2`, deciding factor product `ℓ · d ≥ 2`) forces the block's
single-side length `L = k · (ℓ · d)` up to at least `4`. Any interface containing the block then
has `μ = Σ len ≥ L ≥ 4`, so no level jump can occur below mass `4`. E.07(i)'s `jump_floor` at the
block's own split. -/
theorem block_jump_gate {k ℓ d L : ℕ} (hk : 2 ≤ k) (hld : 2 ≤ ℓ * d)
    (hL : L = k * (ℓ * d)) : 4 ≤ L := by
  rw [hL]
  exact jump_floor hk hld

/-- **NODE E.59**, clause 2 — *non-propagation at `μ ≤ 3`*: a block of length `L ≤ μ` inside an
interface of mass `μ ≤ 3` cannot meet clause 1's floor, so no jump configuration exists there —
every node is decided by rows 1–4/6 or by a pure refine (`EFF.HE7.14`). -/
theorem no_jump_of_mu_le_three {μ L : ℕ} (hμ : μ ≤ 3) (hLμ : L ≤ μ) : ¬ 4 ≤ L := by
  omega

end Uniformity.Density.Ladder

/-! ## Numeric gate — the gate, the non-propagation, and the boundary that separates them

`#guard` fails elaboration when the checked `Bool` is `false`, so these run at build time. The
third block is the one that matters: it exhibits the μ = 4 row as LIVE (a jump configuration
really does fit at mass 4, matching `he7annex_supp.py`'s 96/96 first live jump row), so clause 2
is a genuine threshold and not a vacuous bound. -/

section NumericGate

open Uniformity.Density.Ladder

/-- Does `(k, ℓ, d)` present a jump configuration, and does its block length clear `4`? -/
private def jumpFits (k ℓ d : ℕ) : Bool :=
  !(2 ≤ k && 2 ≤ ℓ * d) || 4 ≤ k * (ℓ * d)

-- Clause 1 over a finite window: every jump configuration with `k, ℓ, d ≤ 6` clears `4`.
#guard (List.range 7).all fun k => (List.range 7).all fun l => (List.range 7).all fun d =>
  jumpFits k l d

-- Both live branches of the `[r1]` rider, at their smallest instances.
#guard 4 ≤ 2 * (2 * 1)   -- `ℓ = 2`, `d_r = 1`
#guard 4 ≤ 2 * (1 * 2)   -- `ℓ = 1`, `d_r = 2`

-- Clause 2 over `μ ≤ 3`: no block length `L ≤ μ ≤ 3` reaches the floor.
#guard (List.range 4).all fun m => (List.range 4).all fun L => !(L ≤ m && 4 ≤ L)

-- The threshold is sharp: at `μ = 4` a block of length `4 = 2 * (2 * 1)` fits and DOES jump.
#guard (4 : ℕ) ≤ 4 && 2 * (2 * 1) == 4

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.block_jump_gate
#print axioms Uniformity.Density.Ladder.no_jump_of_mu_le_three

end AxCheck
