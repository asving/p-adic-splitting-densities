/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapD.D01 — `NormSection`, the normalizer section

**Chapter D, NODE D.01** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, the abstract
cocycle arena; amendments A-1, A-D.1, A-D.2 govern). ENV-D2. One signed declaration,
definitional.

*The normalizer section.* A **normalizer section** on a commutative group `G` is a map
`n : ℤ → G` (heights are integers — `EFF.T1.02`'s integrality clause scopes every consumed
height to `ℤ`) with the height-zero normalization `n 0 = 1` (`(C2-zero-normalizer)`,
`EFF.T1.02`). This is the whole §3 carrier: exact heights, residues, and the tower do not enter
until D.07.

The design note of blueprint §3 is what this node implements: every §3 identity is an identity
between elements constructed from a height-indexed section into a commutative group, and the
"exact-height arithmetic" half of the corpus derivations is pure group algebra. Proving the
group half once, abstractly, is what makes the level-1 instance (§4), the `i = 2` GENTOW2
instance (chapter C's, consumed at D.42) and the depth-`i ≥ 3` conditional layer (§9)
*instances of one theorem* instead of three parallel calculations — D-1's licence (honesty item
D-H3).

## Faithfulness

**⚠ Mandatory, trust-boundary definition.** Two recasts against the corpus, flagged for the
chapter cross-read:

* *heights are integers.* The field `n` is typed `ℤ → G`, not `ℕ → G`: `EFF.T1.02`'s
  integrality clause scopes every consumed height to `ℤ`, and §4's level-1 instance really is
  evaluated at negative heights (the A-D.1 negative-height gate ran `iexp`/`aexp`/`qexp` on
  `k = −3…5`).
* *no exact-height field here.* `EFF.T1.01`'s level-1 clause `i(k)h + a(k)e₁ = k` is NOT a
  field of this structure; it becomes D.07's `exact_height` field on the arena. A normalizer
  section carries the zero-normalization and nothing else, which is exactly what §3's
  identities consume.

**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

DEPENDS: none (mathlib `CommGroup` only).

**PROOF.** Definitional. The body is the gate-verified `leanspec/Leanspec/ChapD.lean` stub body
(`structure NormSection`, the §3 layer) verbatim, with the blueprint's
`namespace Uniformity.Density.Gauge` header restored (the leanspec wrapper `LeanspecD` is a
stub-side artifact; the landed namespace assignment is `Uniformity.Density.Gauge`, GC-6.2).

SOURCE: `EFF.T1.02` (the boxed `(C2-zero-normalizer)`: "n̂_i(0) = 1"); `EFF.T3.01`
("`N(k) := n̂_i(k)`, `N(0) = 1`"); `EFF.T1.01` (the level-1 instance this abstracts — the
exact-height clause becomes D.07's `exact_height` field, not a field here).

**TEETH.** T3 §8.1(1) (normalized endpoints) → Lean theorem at D.05/D.09; nothing to score at
this node (a definition).

ENVIRONMENT: ENV-D2.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- A **normalizer section** at a fixed tower level: heights to monomials, normalized at
height zero (`(C2-zero-normalizer)`, `EFF.T1.02`; `N(0) = 1`, `EFF.T3.01`). -/
structure NormSection (G : Type*) [CommGroup G] where
  /-- The height-indexed normalizer `k ↦ n̂(k)`.  Heights are INTEGERS (`EFF.T1.02`'s
  integrality clause). -/
  n : ℤ → G
  /-- `(C2-zero-normalizer)`: the height-zero normalization `n̂(0) = 1`. -/
  n_zero : n 0 = 1

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.NormSection
#print axioms Uniformity.Density.Gauge.NormSection.mk

end AxCheck
