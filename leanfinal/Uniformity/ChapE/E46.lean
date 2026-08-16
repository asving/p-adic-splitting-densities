/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E45

/-!
# Uniformity.ChapE.E46 — degree conservation for the σ dictionary (GC-4's mandatory invariant)

**Chapter E, NODE E.46** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §7 — the σ dictionary and
the transport laws, the chapter's TERMINAL SUPPLY), ENV-E1 (the arithmetic arena) plus, for the
second clause only, a commutative base `O` carrying the polynomial `F` whose degree the leaves
account for.

**This file IS the GC-4 obligation of NODE E.45.** GC-4 binds every σ output to ship its
degree-conservation lemma; E.45 declares `ladderSigma` and defers the invariant here (landing it
in both files would collide at the chapter roll-up). Two clauses:

* **`ladderSigma_degree` — the unconditional multiset identity.** The degree of the dictionary's
  value is the sum of the leaves' `e · f`:
  `(ladderSigma e₀ f₀ leaves).degree = Σ_{l ∈ leaves} (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2`.
  This is `EFF.T2.30`'s `(FUND)` `|Ω| = ef` summed over the emission, and it holds for ANY base
  pair and ANY multiset of leaves — no weight hypothesis, no monicity, no arena.
* **`ladderSigma_degree_eq_deg` — the conditional block-degree form.** Under E.20/E.21's weight
  bookkeeping (each leaf's `e · f` is its emitted block degree, and the emitted blocks exhaust
  `F`), the same degree is `F.natDegree`. **The weight bookkeeping is a HYPOTHESIS (`hwt`), not
  a theorem of this file**: exhaustion of `F` by the read's emissions is the induction engine's
  business (E.20/E.21), and `EFF.HE7.36`'s `D″ ∣ deg f_S` / orbit-size sum is its source. This
  file only transports it across the dictionary.

## Why the first clause is not `rfl`

`Uniformity.FactorizationType.degree σ = (σ.data.map fun p => p.1 * p.2).sum`
(`Uniformity/Density/LocalData.lean:49`) and `ladderSigma e₀ f₀ leaves = ⟨leaves.map (·.ef e₀ f₀)⟩`
(E.45), so the left side is a `Multiset.map` of a `Multiset.map`, while the statement's right
side is a single map of the composite. `Multiset.map_map` collapses the two — the identity is
definitional only up to that collapse, which is why the invariant is a lemma with a proof and
not a `rfl` remark.

## Executable-gate constraint (E-D10, in force)

`Uniformity.FactorizationType`'s `DecidableEq` is `Classical.decEq` (noncomputable), so no gate
may `decide` an equation between σ-VALUES. Everything gated below is a `.degree` (a `ℕ`) or a
`.data` (`Multiset (ℕ × ℕ)`, a real instance) — the GC-11 gate-spelling rider.

DEPENDS: E.45 (`LadderLeaf`, `LadderLeaf.ef`, `ladderSigma`) · landed
`Uniformity.FactorizationType.degree` (`Uniformity/Density/LocalData.lean:49`) · mathlib
`Multiset.map_map`.

SOURCE: GC-4 (the mandatory invariant, the `stageSigma_degree`/`typeOf_degree` pattern);
`EFF.HE7.36` (`D″ ∣ deg f_S` and the orbit-size sum — the weight bookkeeping's source, and the
reason `hwt` is stated as a hypothesis rather than proved here); `EFF.T2.30` (`(FUND)`
`|Ω| = ef`).

TEETH: Q1's `Σ e·f = 8` per member (every one of the 1,335 PARI σ agreements at `n = 8` is a
value of E.45's dictionary whose degree must come out `8`) → **Lean theorem** (this file) +
E.67's executable gate. The numeric gate below runs the invariant on the μ₂ = 2 alphabet and
instantiates the second clause against a genuine `Polynomial ℤ` of degree 8.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **NODE E.46, clause 1 — GC-4's mandatory invariant for E.45's dictionary.** *Degree
conservation:* the degree of `ladderSigma e₀ f₀ leaves` is the sum, over the emitted leaves, of
the products `e · f` of their composed invariants. Unconditional: no weight hypothesis and no
local base — this is `(FUND)` `|Ω| = ef` (`EFF.T2.30`) summed over the emission. -/
theorem ladderSigma_degree (e₀ f₀ : ℕ) (leaves : Multiset LadderLeaf) :
    (ladderSigma e₀ f₀ leaves).degree
      = (leaves.map fun l => (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2).sum := by
  simp [ladderSigma, Uniformity.FactorizationType.degree, Multiset.map_map]

/-- **NODE E.46, clause 2 — the block-degree form.** With E.20/E.21's weight bookkeeping supplied
as the hypothesis `hwt` (each leaf's `e · f` is its emitted block degree, and the emitted blocks
exhaust `F`), the dictionary's degree is `F.natDegree`. The hypothesis is exactly where the
exhaustion content sits: this clause transports it, it does not prove it. -/
theorem ladderSigma_degree_eq_deg {O : Type*} [CommRing O]
    (e₀ f₀ : ℕ) (leaves : Multiset LadderLeaf) (F : Polynomial O)
    (hwt : (leaves.map fun l => (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2).sum = F.natDegree) :
    (ladderSigma e₀ f₀ leaves).degree = F.natDegree := by
  rw [ladderSigma_degree, hwt]

end Uniformity.Density.Ladder

/-! ## Numeric gate — the invariant, evaluated

`#guard` fails elaboration when the checked `Bool` is `false`, so these run at build time. Per
E-D10 nothing compares two σ-values: the checks are on `.degree` (`ℕ`) and on `.data`
(`Multiset (ℕ × ℕ)`). The frames are E.45's — the μ₂ = 2 alphabet `{(8,1)}`, `{(4,2)}`,
`{(4,1),(4,1)}` at degree 8, plus deeper leaves and a scaled base — now checked against the
THEOREM's right-hand side rather than against a hand-computed number. -/

section NumericGate

open Uniformity Uniformity.Density.Ladder

/-- The two sides of clause 1, as a `Bool`: `.degree` on the left, the leaf-wise `e·f` sum on the
right. Every frame below asserts this is `true`. -/
private def conserved (e₀ f₀ : ℕ) (leaves : Multiset LadderLeaf) : Bool :=
  (ladderSigma e₀ f₀ leaves).degree ==
    (leaves.map fun l => (l.ef e₀ f₀).1 * (l.ef e₀ f₀).2).sum

/-- Depth-0 leaf, terminal read `(8, 1)`: the inert letter of the μ₂ = 2 alphabet. -/
private def leafInert : LadderLeaf := ⟨[], (8, 1)⟩

/-- Depth-0 leaf, terminal read `(4, 2)`: the `e > 1 ∧ f > 1` letter. -/
private def leafMixed : LadderLeaf := ⟨[], (4, 2)⟩

/-- Depth-0 leaf, terminal read `(4, 1)`: two of these make the split letter of degree 8. -/
private def leafHalf : LadderLeaf := ⟨[], (4, 1)⟩

/-- Depth-1 leaf `⟨[(2,1)], (1,2)⟩`: at base `(2, 1)` it composes to `(4, 2)` (`EFF.HE7.48`). -/
private def leafTwoLevel : LadderLeaf := ⟨[(2, 1)], (1, 2)⟩

/-- Depth-2 leaf `⟨[(2,1), (1,2)], (2,1)⟩`: at base `(1, 1)` it composes to `(4, 2)`. -/
private def leafThreeLevel : LadderLeaf := ⟨[(2, 1), (1, 2)], (2, 1)⟩

-- Clause 1 on the μ₂ = 2 alphabet, on deeper frames, at a scaled base, and on the empty emission.
#guard conserved 1 1 {leafInert}
#guard conserved 1 1 {leafMixed}
#guard conserved 1 1 {leafHalf, leafHalf}
#guard conserved 2 1 {leafTwoLevel}
#guard conserved 1 1 {leafThreeLevel}
#guard conserved 3 5 {leafInert, leafMixed, leafHalf, leafTwoLevel, leafThreeLevel}
#guard conserved 0 1 {leafInert, leafMixed}
#guard conserved 1 1 (0 : Multiset LadderLeaf)

-- The conserved value itself, at the alphabet: degree 8 per letter (`(FUND)` summed).
#guard (ladderSigma 1 1 {leafInert}).degree == 8
#guard (ladderSigma 1 1 {leafMixed}).degree == 8
#guard (ladderSigma 1 1 {leafHalf, leafHalf}).degree == 8
#guard (ladderSigma 2 1 {leafTwoLevel}).degree == 8

-- A multi-letter emission: `8 + 8 + 8 = 24`, i.e. the invariant is additive over the emission.
#guard (ladderSigma 1 1 {leafInert, leafMixed, leafTwoLevel}).degree == 8 + 8 + 4

end NumericGate

/-! ## Clause 2, instantiated against a real polynomial

The block-degree form is only as useful as the weight hypothesis it consumes, so it is exercised
here at a genuine `Polynomial ℤ` of degree 8 — the `n = 8` frame of Q1's battery — with `hwt`
discharged by computation rather than assumed. -/

section BlockDegreeGate

open Polynomial Uniformity Uniformity.Density.Ladder

/-- The inert letter accounts for the whole degree of a degree-8 polynomial: `Σ e·f = 8·1 = 8`
and `(X^8 + 3).natDegree = 8`, so clause 2 fires. -/
example : (ladderSigma 1 1 {(⟨[], (8, 1)⟩ : LadderLeaf)}).degree
    = ((X ^ 8 + C 3 : Polynomial ℤ)).natDegree := by
  have hdeg : ((X ^ 8 + C 3 : Polynomial ℤ)).natDegree = 8 := by
    compute_degree!
  refine ladderSigma_degree_eq_deg 1 1 _ _ ?_
  rw [hdeg]
  decide

/-- The split letter accounts for the same degree by two blocks of degree 4: `4·1 + 4·1 = 8`. -/
example : (ladderSigma 1 1 {(⟨[], (4, 1)⟩ : LadderLeaf), (⟨[], (4, 1)⟩ : LadderLeaf)}).degree
    = ((X ^ 8 + C 3 : Polynomial ℤ)).natDegree := by
  have hdeg : ((X ^ 8 + C 3 : Polynomial ℤ)).natDegree = 8 := by
    compute_degree!
  refine ladderSigma_degree_eq_deg 1 1 _ _ ?_
  rw [hdeg]
  decide

end BlockDegreeGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.ladderSigma_degree
#print axioms Uniformity.Density.Ladder.ladderSigma_degree_eq_deg

end AxCheck
