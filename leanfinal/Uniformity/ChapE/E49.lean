/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapE.E49 — `Mu2Row`, `mu2Sigma`: the μ₂ = 2 dictionary and its degree law

**Chapter E, NODE E.49** [def+lemma] (`blueprint/CHAP-E_sigma_ladder.md` §7 — the σ dictionary and
the transport laws, the chapter's TERMINAL SUPPLY), ENV-E1 (the arithmetic arena) plus the landed
kernel.

`EFF.HE7.58`'s six-row table, transcribed row-for-row. The frame is `EFF.HE7.57`'s n = 8 frame:
`D″ = 4`, `K₂ = K = F_q`, `T₂ = 2u`, `μ₂ = 2`, base `(e₁ℓ, f₁d_r) = (4, 1)`. At that frame the
rows read

| row | condition | σ |
|---|---|---|
| 1 `oneSideHalf` | one side, length 2, `λ₂ ∉ ℤ` (so `ℓ₂ = 2`) | `⟨{(8, 1)}⟩` |
| 2 `oneSideInert` | `λ₂ ∈ ℤ`, `R₂` an irreducible quadratic | `⟨{(4, 2)}⟩` |
| 3 `oneSideSplit` | `λ₂ ∈ ℤ`, `R₂` split | `⟨{(4, 1), (4, 1)}⟩` |
| 4 `twoSides` | two sides of length 1 | `⟨{(4, 1), (4, 1)}⟩` |
| 5 `refineRow` | `R₂ = (Z − s₂)²` — α-refine, re-read at the refined key | (no value: re-read) |
| 6 `peelRow` | `Ψ ∣ f` — peel | `⟨{(4, 1), (4, 1)}⟩` |

Row 5 is a POINTER, not a value: the read is repeated at the refined key `Ψ − w` and lands on one
of the other rows, a loop that terminates by E.55/E.56 and is packaged as E.52. It is therefore
sent to `none`, which is what makes `mu2Sigma` total as an `Option`-valued function without
inventing a σ-value the source does not assert. Row 6's presence is load-bearing: `EFF.HE7.58`'s
own exhaustiveness claim *"holds only WITH row 6"*.

## GC-4 conformance (declared)

* **Output carrier.** The landed `Uniformity.FactorizationType`
  (`Uniformity/Density/LocalData.lean:43`), by anonymous constructor against its landed definition
  — no parallel σ type. **Spelling per defect A-E.1/E-D8:** the blueprint SIGNATURE writes
  `Uniformity.Density.FactorizationType`, which does not resolve; the carrier lives directly in
  `Uniformity`.
* **Named dictionary function.** `mu2Sigma`, not an inline table.
* **Dictionary DOMAIN.** `Mu2Row`, a six-constructor `inductive` with `DecidableEq` — a case
  label, never itself a σ-value.
* **Mandatory degree-conservation lemma.** `mu2Sigma_degree` below IS this dictionary's GC-4
  lemma: every decided row has degree 8, the frame's `n`. (Chapter E's other σ output,
  `ladderSigma` of E.45, has its own at NODE E.46; nothing is duplicated here.)
* **Executable-gate constraint (defect A-E.1/E-D10).** `FactorizationType`'s `DecidableEq` is
  `Classical.decEq` (noncomputable), so no gate may `decide` an equation between σ-VALUES. The
  gates below are `rfl` (definitional, not decidable-instance driven) and `#guard`s on `.data`
  and `.degree` only.

The three-letter alphabet claim ("no fourth value possible", `EFF.HE7.61`) is a SEPARATE node,
E.50 (`mu2Sigma_alphabet`), and is deliberately not declared here.

DEPENDS: E.45 (GC-4 conformance shape) · landed `Uniformity.FactorizationType`.

SOURCE: `EFF.HE7.58` (the table, transcribed row-for-row in the source's own six-row markdown
form; row 5's *"→ one of the above"* upgraded at `EFF.HE7.59` = E.52's licence; row 6 per
`EFF.HE7.60`); `EFF.HE7.57` (the n = 8 frame: `D″ = 4`, `K₂ = K = F_q`, `T₂ = 2u`, `μ₂ = 2`).

TEETH: Q1 (*"exactly the three outputs of THEOREM HE7.A's μ₂ = 2 dictionary (§S8), and no fourth
value ever appears"*, 1,335/1,335) + `he7r1_supp.py` (row 6: 8/8 + 2/2 + 2/2) → the value map is a
**Lean def + lemma**; E.65/E.67 fire it numerically.

## Trust boundary

`mu2Sigma` is a DEFINITION transcribed from a table: Lean checks the degree lemma, not the
table's fidelity to `EFF.HE7.58`. The six rows and their values are flagged for human review.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **NODE E.49.** *The μ₂ = 2 dictionary rows* — `EFF.HE7.58`'s six-row table as a case type.
Rows 1–4 are the polygon cases, row 5 is the α-refine POINTER (re-read at the refined key, E.52),
row 6 is the peel. This is a dictionary DOMAIN only (GC-4). -/
inductive Mu2Row
  /-- Row 1: one side of length 2 with `λ₂ ∉ ℤ`, so `ℓ₂ = 2`. -/
  | oneSideHalf
  /-- Row 2: `λ₂ ∈ ℤ` and `R₂` an irreducible quadratic. -/
  | oneSideInert
  /-- Row 3: `λ₂ ∈ ℤ` and `R₂` split. -/
  | oneSideSplit
  /-- Row 4: two sides, each of length 1. -/
  | twoSides
  /-- Row 5: `R₂ = (Z − s₂)²` — α-refine; the read is repeated at the refined key. -/
  | refineRow
  /-- Row 6: `Ψ ∣ f` — peel. -/
  | peelRow
  deriving DecidableEq

/-- **NODE E.49.** *The decided-row σ values at the n = 8 frame* (`EFF.HE7.57`'s frame: base
`(e₁ℓ, f₁d_r) = (4, 1)`, `K₂ = F_q`). Row 5 is `none` — it is a pointer to a re-read, not a
value; every other row is decided, and the five decided values use only three distinct letters
(that count is NODE E.50, not stated here). -/
def mu2Sigma : Mu2Row → Option Uniformity.FactorizationType
  | .oneSideHalf  => some ⟨{(8, 1)}⟩
  | .oneSideInert => some ⟨{(4, 2)}⟩
  | .oneSideSplit => some ⟨{(4, 1), (4, 1)}⟩
  | .twoSides     => some ⟨{(4, 1), (4, 1)}⟩
  | .refineRow    => none        -- re-read at the refined key (E.52)
  | .peelRow      => some ⟨{(4, 1), (4, 1)}⟩

/-- **NODE E.49**, the lemma half — **GC-4's mandatory degree-conservation lemma for this
dictionary**: the value map on decided rows is total into degree 8, the frame's `n`
(`8·1 = 8`, `4·2 = 8`, `4 + 4 = 8`). Row 5 contributes nothing, its value being `none`. -/
theorem mu2Sigma_degree : ∀ r v, mu2Sigma r = some v → v.degree = 8 := by
  intro r v h
  cases r
  case oneSideHalf =>
    obtain rfl : (⟨{(8, 1)}⟩ : Uniformity.FactorizationType) = v := Option.some.inj h
    simp [Uniformity.FactorizationType.degree]
  case oneSideInert =>
    obtain rfl : (⟨{(4, 2)}⟩ : Uniformity.FactorizationType) = v := Option.some.inj h
    simp [Uniformity.FactorizationType.degree]
  case oneSideSplit =>
    obtain rfl : (⟨{(4, 1), (4, 1)}⟩ : Uniformity.FactorizationType) = v := Option.some.inj h
    simp [Uniformity.FactorizationType.degree]
  case twoSides =>
    obtain rfl : (⟨{(4, 1), (4, 1)}⟩ : Uniformity.FactorizationType) = v := Option.some.inj h
    simp [Uniformity.FactorizationType.degree]
  case refineRow =>
    -- Row 5 has no value: the hypothesis `none = some v` is absurd.
    exact absurd h (by simp [mu2Sigma])
  case peelRow =>
    obtain rfl : (⟨{(4, 1), (4, 1)}⟩ : Uniformity.FactorizationType) = v := Option.some.inj h
    simp [Uniformity.FactorizationType.degree]

end Uniformity.Density.Ladder

/-! ## Numeric gate — the table, evaluated

The six `rfl` rows are the table itself, re-read from the definition (`rfl` is definitional, so it
sidesteps defect E-D10's noncomputable `DecidableEq FactorizationType` — nothing here `decide`s an
equation between σ-values). The `#guard`s then run on `.data` (`Multiset (ℕ × ℕ)`, a real
`DecidableEq`) and on `.degree` (ℕ-equality), and re-execute `mu2Sigma_degree` numerically. -/

section NumericGate

open Uniformity Uniformity.Density.Ladder

-- The six rows of `EFF.HE7.58`, verbatim.
example : mu2Sigma .oneSideHalf = some ⟨{(8, 1)}⟩ := rfl
example : mu2Sigma .oneSideInert = some ⟨{(4, 2)}⟩ := rfl
example : mu2Sigma .oneSideSplit = some ⟨{(4, 1), (4, 1)}⟩ := rfl
example : mu2Sigma .twoSides = some ⟨{(4, 1), (4, 1)}⟩ := rfl
example : mu2Sigma .refineRow = none := rfl
example : mu2Sigma .peelRow = some ⟨{(4, 1), (4, 1)}⟩ := rfl

-- The same rows on `.data`, decidably.
#guard (mu2Sigma .oneSideHalf).map (fun σ => σ.data) == some ({(8, 1)} : Multiset (ℕ × ℕ))
#guard (mu2Sigma .oneSideInert).map (fun σ => σ.data) == some ({(4, 2)} : Multiset (ℕ × ℕ))
#guard (mu2Sigma .oneSideSplit).map (fun σ => σ.data) == some ({(4, 1), (4, 1)} : Multiset (ℕ × ℕ))
#guard (mu2Sigma .twoSides).map (fun σ => σ.data) == some ({(4, 1), (4, 1)} : Multiset (ℕ × ℕ))
#guard (mu2Sigma .refineRow).map (fun σ => σ.data) == (none : Option (Multiset (ℕ × ℕ)))
#guard (mu2Sigma .peelRow).map (fun σ => σ.data) == some ({(4, 1), (4, 1)} : Multiset (ℕ × ℕ))

-- GC-4's degree law, re-executed on every row: decided rows have degree 8, row 5 has no value.
private def rowDegree (r : Mu2Row) : Option ℕ := (mu2Sigma r).map (fun σ => σ.degree)

#guard rowDegree .oneSideHalf == some 8
#guard rowDegree .oneSideInert == some 8
#guard rowDegree .oneSideSplit == some 8
#guard rowDegree .twoSides == some 8
#guard rowDegree .refineRow == none
#guard rowDegree .peelRow == some 8

-- Exactly one row is undecided, and it is row 5.
#guard ([Mu2Row.oneSideHalf, .oneSideInert, .oneSideSplit, .twoSides, .refineRow,
  .peelRow].filter (fun r => (mu2Sigma r).isNone)) == [Mu2Row.refineRow]

end NumericGate

/-! ## Axiom footprint

`#print axioms` on the `def` reports its BODY's footprint — the check that matters for a
definitional node. -/

section AxCheck

#print axioms Uniformity.Density.Ladder.Mu2Row
#print axioms Uniformity.Density.Ladder.mu2Sigma
#print axioms Uniformity.Density.Ladder.mu2Sigma_degree

end AxCheck
