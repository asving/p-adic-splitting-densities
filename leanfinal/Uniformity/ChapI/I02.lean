/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Statement
import Uniformity.Density.Drainage
import Uniformity.ChapG.G51

/-!
# Uniformity.ChapI.I02 — `A0_n`, the decided-value law at degree `n` — **CARRIER + TWO GATES**

**Chapter I, NODE I.02** [def] [fresh] (`blueprint/CHAP-I_capstone_conditionality.md` §4,
`### NODE I.02`; SIGNED twin `leanspec/Leanspec/ChapI.lean`, the `### NODE I.02` block,
lines 427–446).  **ENV-I1**.  Statement transcribed BYTE-FROZEN; re-namespaced only
(`LeanspecI` → `Uniformity.Density`, GC-6.2).

Unlike I.01/I.05/I.06/I.07/I.21, **this node's signed body is real, not a placeholder** — it is
the LITERAL degree-`n` slice of the landed capstone target `UniformityStatementDecided`
(`Density/Statement.lean:84`), copied rather than re-typed.  That copy is what makes I.16's
one-line `exact` close, and the `Iff.rfl` pin below is the standing regression on it.

## ⚠ DISPOSITION

* **Nothing is asserted about the capstone.**  `DecidedSliceAt` is a `Prop` carrier; no
  declaration here proves it at general `n`, no axiom is declared, no cite is imported, and the
  capstone statement is not asserted.  The only theorems here are the two gate `example`s, both
  of which conclude something strictly weaker than the node's content.
* **NOT owner-gated.**  I.02 is Display A's `(A0)` conjunct (ledger `HYP.25`); its terminal
  fate is the count layer, which is OPEN MATH, not a cite.  No signature is needed to land it.

## MANDATORY BINDER-VACUITY AUDIT (A-C.8.4; verdict committed before any proving)

**Verdict: NON-VACUOUS AND SHARP, with one recorded HYPOTHESIS-SIDE OVER-DEMAND (I-D10).**

**(1) The degree guard `σ.degree = n` is load-bearing, and it is exactly the landed target's.**
Byte-identical to `UniformityStatementDecided`'s (`Density/Statement.lean:85`).  It is not
vacuous: at `n = 2` it is satisfied by all three of `splitType`, `inertType`, `ramType`
(landed `splitType_degree`/`inertType_degree`/`ramType_degree`), and it is not trivially
satisfied either, since `FactorizationType` carries types of every degree.

**(2) The five complete-DVR instance binders are inhabited** — `ℤ_[p]` (landed
`Density/LocalData.lean` §6) — verbatim the bundle of landed `DrainageAt`.  Not the C.113
`hne` shape.

**(3) `den ≠ 0` plus the per-`O` `den.eval q ≠ 0` is the sharp pair, not a redundancy.**
`den ≠ 0` is a polynomial-level nondegeneracy; `den.eval ((residueCard O : ℕ) : ℚ) ≠ 0` is the
per-residue-cardinality one, and neither implies the other (a nonzero `den` can vanish at some
`q`).  Dropping the second would make the density equation divide by zero at those `q`; dropping
the first would admit `den = 0` with the eval clause false, emptying the conclusion.  Both are
therefore live.

**(4) NON-VACUITY IS MACHINE-WITNESSED, not asserted.**  `DecidedSliceAt 2` is PROVED outright
in the second gate below, from chapter G's landed `uniformityStatement_two` (`ChapG/G51.lean`)
through the landed `n = 2` tie `genuineDensity_eq_decidedDensity_two`
(`Density/Drainage.lean:858`).  So the carrier is inhabited at a real degree, and it is *not*
provable in general — the `n ≥ 3` slices are the open count layer.  This is the A-C.8.4 ideal
row: **load-bearing and sharp at a named instance.**

**(5) THE RECORDED DEFECT — I-D10, hypothesis-side over-demand at `n = 0`.**  The landed target
guards its body with `0 < n`; `DecidedSliceAt` does not carry that guard (correctly — the guard
belongs to the ∀-`n` wrapper, and the first gate below proves the two fit together on the nose).
The over-demand appears only at I.10's `a0 : DecidedSliceAt n` field, where `∀ n,
CapstoneHypotheses n` would demand `DecidedSliceAt 0`, a law the capstone never asks for.
**Class: harmless to soundness, dishonest to the open surface** (it makes the hypothesis block
look one law bigger than Display A).  Left OPEN by amendment A-I.1; **not repairable from this
node** — the fix is a field-level change at I.10, which is owner-gated (Part V gate (a)) and
under the standing I.10 freeze.  Recorded here so I.02's consumer cannot inherit it silently.
Contrast: `a2`'s `DrainageAt 0` IS genuinely required, since landed
`UniformityStatement.ofDecided` takes `∀ n, DrainageAt n`.

**(6) FAITHFULNESS DIVERGENCE, disclosed (honesty I-6, carried from the signed docstring).**
The corpus states `(A0)` on the `disc ≠ 0` locus; `decidedDensity` counts the every-lift decided
classes with **no** such restriction (GC-9), which is the strictly STRONGER read.  The
divergence is recorded, not silently strengthened; it is faithfulness text on this node.

## Definitional choices made here (flagged for human review)

1. **Namespace** `Uniformity.Density`, flat (GC-6.2).
2. **Imports** are per-node minimal — `Density.Statement` (the pinned target), `Density.Drainage`
   (the `n = 2` tie) and `ChapG.G51` (`uniformityStatement_two`) — rather than ENV-I1's nominal
   `import Uniformity`, which inherits leanspec defect **I-D1** (the `ChapD` roll-up and the
   chapter-E deep-twist branch are a hard Lean error together at HEAD).  Statement unaffected.
3. **The two gates are `example`s, deliberately anonymous**, so this file adds exactly ONE public
   name.  The `Iff.rfl` pin is a *regression test*: it fails the build the moment either body
   drifts by so much as an instance binder order.  Both are transcribed from the leanspec's
   executed gates (`§6 GATE` item (1), line 1033; `I.23` item (iii), lines 1209–1217).
-/

namespace Uniformity.Density

open IsLocalRing Polynomial

/-- `A0_n` (Display A; ledger HYP.25): the degree-`n` decided-value law — the degree-`n` slice of
`UniformityStatementDecided`. FAITHFULNESS (honesty I-6): the corpus states `(A0)` on the
`disc ≠ 0` locus; `decidedDensity` counts the every-lift decided classes (GC-9, the strictly
stronger read) — divergence recorded, not silently strengthened. -/
def DecidedSliceAt (n : ℕ) : Prop :=
  ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          decidedDensity O n σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

section GateTwo

-- (1) **THE LITERAL-SLICE PIN (I.02 ⟷ the landed target).** `UniformityStatementDecided` IS
-- `∀ n, 0 < n → DecidedSliceAt n`, on the nose. This `Iff.rfl` fails the build the moment either
-- body drifts by so much as an instance order — the standing regression behind I.16's `exact`,
-- and the machine-visible form of defect I-D10 (the landed target has the `0 < n` guard; the
-- slice does not, so a `∀ n` field list demands `DecidedSliceAt 0`).
example : UniformityStatementDecided ↔ ∀ n : ℕ, 0 < n → DecidedSliceAt n := Iff.rfl

-- (2) **NON-VACUITY of `A0` at `n = 2`**: `DecidedSliceAt 2` is PROVED outright, from chapter G's
-- landed `uniformityStatement_two` through the landed `n = 2` drainage tie
-- `genuineDensity_eq_decidedDensity_two`. This is the carrier's witness that it says something.
example : DecidedSliceAt 2 := by
  intro σ hσ
  obtain ⟨num, den, hden, hlaw⟩ := uniformityStatement_two σ hσ
  refine ⟨num, den, hden, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨h1, h2⟩ := hlaw O
  exact ⟨h1, by rw [← genuineDensity_eq_decidedDensity_two]; exact h2⟩

end GateTwo

end Uniformity.Density

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.DecidedSliceAt
