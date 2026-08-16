/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E49

/-!
# Uniformity.ChapE.E50 — the three-letter alphabet ("no fourth value possible")

**Chapter E, NODE E.50** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §7 — the σ dictionary and
the transport laws), ENV-E1.

E.49's μ₂ = 2 dictionary `mu2Sigma` sends its six rows into `Option FactorizationType`. This
node is the **image** statement: every decided row lands in the three-element alphabet

`{ ⟨{(8, 1)}⟩ , ⟨{(4, 2)}⟩ , ⟨{(4, 1), (4, 1)}⟩ }`,

so no fourth σ-value is emitted at the frame. Five rows are decided and they use three letters
(rows 3, 4, 6 all emit the split letter); row 5 is `none` — the α-refine pointer — and the
statement is vacuous there, which is exactly right: row 5 emits nothing, and E.52 is what
routes its re-read back into this same alphabet.

## What is claimed and what is not

* **Claimed (Lean):** the image of `mu2Sigma` on decided rows is *contained in* the three
  letters. Together with the attainment checks in the gate (each letter is hit), the image is
  *exactly* those three.
* **Not claimed (evidence, not theorem):** that this alphabet is the *same* alphabet HE6
  observed independently (`HE6-T-CASEB`). `EFF.HE7.61` records the match as the chapter's
  decorrelation anchor — two separately-derived tables agreeing letter-for-letter — and it is
  recorded here as prose only. Lean cannot certify an agreement with an off-repo table.
* **Not claimed:** anything about row 5's re-read. That is E.52 (`he7a_prime_schema`), which
  consumes a termination supply (E.55/E.56) this file does not have.

## Executable-gate constraint (E-D10, in force)

`Uniformity.FactorizationType`'s `DecidableEq` is `Classical.decEq` (noncomputable), so no gate
may `decide` an equation between σ-VALUES. The `rfl`s below are definitional and the `#guard`s
run on `.data` (`Multiset (ℕ × ℕ)`, a real instance) — the GC-11 gate-spelling rider.

DEPENDS: E.49 (`Mu2Row`, `mu2Sigma`) · landed `Uniformity.FactorizationType`.

SOURCE: `EFF.HE7.58` (exhaustiveness WITH row 6 — "The exhaustiveness claim holds only WITH row
6"); `EFF.HE7.61` (the alphabet-match fence quoted above); `EFF.HE7.60` ("the three-σ alphabet
and the 'no fourth value possible' claim survive verbatim").

TEETH: HE7-T-CASEB-SEP (three distinct PARI σ inside ONE outer family, 8/8 predicted) →
**Lean theorem** for the alphabet; the family-realization half stays machine evidence (§13).

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, Lean-core axioms only.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **NODE E.50.** *The three-letter alphabet.* Every decided row of E.49's μ₂ = 2 dictionary
emits one of exactly three σ-values — "no fourth value possible" (`EFF.HE7.61`). Row 5 is
`none`, so the claim is vacuous there. -/
theorem mu2Sigma_alphabet :
    ∀ r v, mu2Sigma r = some v →
      v = ⟨{(8, 1)}⟩ ∨ v = ⟨{(4, 2)}⟩ ∨ v = ⟨{(4, 1), (4, 1)}⟩ := by
  intro r v h
  cases r
  case oneSideHalf =>
    obtain rfl : (⟨{(8, 1)}⟩ : Uniformity.FactorizationType) = v := Option.some.inj h
    exact Or.inl rfl
  case oneSideInert =>
    obtain rfl : (⟨{(4, 2)}⟩ : Uniformity.FactorizationType) = v := Option.some.inj h
    exact Or.inr (Or.inl rfl)
  case oneSideSplit =>
    obtain rfl : (⟨{(4, 1), (4, 1)}⟩ : Uniformity.FactorizationType) = v := Option.some.inj h
    exact Or.inr (Or.inr rfl)
  case twoSides =>
    obtain rfl : (⟨{(4, 1), (4, 1)}⟩ : Uniformity.FactorizationType) = v := Option.some.inj h
    exact Or.inr (Or.inr rfl)
  case refineRow =>
    -- Row 5 has no value: the hypothesis `none = some v` is absurd.
    exact absurd h (by simp [mu2Sigma])
  case peelRow =>
    obtain rfl : (⟨{(4, 1), (4, 1)}⟩ : Uniformity.FactorizationType) = v := Option.some.inj h
    exact Or.inr (Or.inr rfl)

end Uniformity.Density.Ladder

/-! ## Numeric gate — the alphabet, counted

Containment is the theorem; ATTAINMENT and the count are the gate's job (a containment lemma
whose alphabet were never hit would be true and worthless). Per E-D10 nothing compares two
σ-values: the `rfl`s are definitional, the `#guard`s run on `.data`. -/

section NumericGate

open Uniformity Uniformity.Density.Ladder

/-- Every row of the dictionary, for the enumeration gates. -/
private def allRows : List Mu2Row :=
  [.oneSideHalf, .oneSideInert, .oneSideSplit, .twoSides, .refineRow, .peelRow]

/-- The `.data` shadow of a row's σ-value — decidable, unlike the σ-value itself (E-D10). -/
private def rowData (r : Mu2Row) : Option (Multiset (ℕ × ℕ)) := (mu2Sigma r).map (fun σ => σ.data)

-- ATTAINMENT: each of the three letters is emitted by some row, so the containment above is an
-- equality of images, not a vacuous over-estimate.
example : mu2Sigma .oneSideHalf = some ⟨{(8, 1)}⟩ := rfl
example : mu2Sigma .oneSideInert = some ⟨{(4, 2)}⟩ := rfl
example : mu2Sigma .oneSideSplit = some ⟨{(4, 1), (4, 1)}⟩ := rfl

-- THE COUNT: exactly three distinct decided values across all six rows — "no fourth value".
#guard ((allRows.filterMap rowData).eraseDups).length == 3

-- The three letters, named, are pairwise distinct (so "three" is not three copies of one).
#guard ({(8, 1)} : Multiset (ℕ × ℕ)) != ({(4, 2)} : Multiset (ℕ × ℕ))
#guard ({(8, 1)} : Multiset (ℕ × ℕ)) != ({(4, 1), (4, 1)} : Multiset (ℕ × ℕ))
#guard ({(4, 2)} : Multiset (ℕ × ℕ)) != ({(4, 1), (4, 1)} : Multiset (ℕ × ℕ))

-- The theorem, re-executed row by row on the `.data` shadow: every decided row's value is one
-- of the three letters.
#guard allRows.all fun r =>
  match rowData r with
  | none => true
  | some d =>
      d == ({(8, 1)} : Multiset (ℕ × ℕ)) || d == ({(4, 2)} : Multiset (ℕ × ℕ)) ||
        d == ({(4, 1), (4, 1)} : Multiset (ℕ × ℕ))

-- Five rows decided, one undecided, and the undecided one is row 5 (the α-refine pointer).
#guard (allRows.filter (fun r => (mu2Sigma r).isSome)).length == 5
#guard (allRows.filter (fun r => (mu2Sigma r).isNone)) == [Mu2Row.refineRow]

-- NEGATIVE control: a candidate "fourth letter" of the right degree (`2 · 4 = 8`) is emitted by
-- NO row — the alphabet is genuinely three letters, not an artifact of the degree law E.49.
#guard (allRows.filterMap rowData).all (fun d => d != ({(2, 4)} : Multiset (ℕ × ℕ)))
#guard (allRows.filterMap rowData).all (fun d => d != ({(8, 1), (8, 1)} : Multiset (ℕ × ℕ)))

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.mu2Sigma_alphabet

end AxCheck
