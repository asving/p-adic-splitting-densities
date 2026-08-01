/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Scaffold/O12/Semantic — the semantic hypothesis rows [unit II-M0]

STATEMENT LAYER ONLY: the `SemanticRows` structure, transcribed verbatim from
`lean/blueprints/BP_II.md` §1.9 (unit II-M0 of the unit table; rows table §1.10).
Semantic-guardian audit + Codex review REQUIRED before any prover consumes these
rows (BP_II §2 unit II-M0). The analytic inputs enter by the corpus's
recorded-via-hypothesis convention (cf. `LeanUrat.L4.cellVolume_eq`'s `hfactor`,
`R1.stratum_volume`, `L2core.perShapeVolume_baseChange`): ONE displayed structure
of rows, everything downstream derived sorry-free. These are NAMED hypothesis
rows — never axioms, never discharged by fiat.

## The named hypothesis rows (BP_II §1.10; the movement's honest conditionality)

| row | content | discharge path |
|---|---|---|
| **(HAAR-COORD)** `SemanticRows.haar*` | per-coordinate valuation measure law + independence | the corpus convention (L4 `hfactor`); a future `PadicMeasure` bridge could discharge it — out of Movement II scope |
| **(NP-SLOPES)** `SemanticRows.npSlopes` | root valuations = polygon slopes | standard (Neukirch II.6); consumed only by L6e(i)/L1-last-sentence — off the pole-free path |
| **(TYPE-INV)** `SemanticRows.type*` | L2/L3 splitting-type preservation | VALUE-side, expressly outside the O-12 claim; consumed by Movements IV–V only |

§1.9 results are conditional exactly on these displayed semantic rows.

## Display adjustment (sanctioned; same convention as `Scaffold/Spine.lean`)

BP_II §1 head: "Signatures are sketches: provers may adjust implicit
binders/instance arguments, never the mathematical content." The §1.9 display
binds `(Coeff … : Type*)` with no algebraic instance, but `Polynomial Coeff`
requires one (`Mathlib.Algebra.Polynomial.Basic`:
`structure Polynomial (R : Type*) [Semiring R]`); verbatim, elaboration fails
with "failed to synthesize Semiring Coeff". The unique minimal repair is the
instance binder `[Semiring Coeff]`, added below; no other token changes.
-/

set_option linter.style.longLine false

open scoped ENNReal

namespace LeanUrat.Scaffold

/-- **The semantic rows** (the [M]-style hypothesis structure of this movement;
each field is a standard cited fact, flagged for the semantic-guardian audit):
(HAAR-COORD) the per-coordinate valuation law μ{v ≥ t} = q₀^{−t}, μ{v = t} =
(1−q₀^{−1})q₀^{−t}, coordinates independent (brief §2.1; = L4.lean's `hfactor`
convention); (NP-SLOPES) the multiset of root valuations equals the multiset of
Newton-polygon slopes (brief L1 last sentence; standard, cite Neukirch II.6);
(TYPE-INV) splitting types invariant under x ↦ πx rescale and x ↦ x + c recenter
(brief L2/L3 — VALUE-side, consumed only by Movements IV–V). -/
structure SemanticRows
    (Coeff Root Γ TypeCode : Type*)
    [Semiring Coeff]
    [LinearOrderedCommGroupWithZero Γ]
    (valuation : Coeff → Γ)
    (coeffVector : Polynomial Coeff → ℕ → Coeff)
    (rootValues polygonSlopes : Polynomial Coeff → Multiset Γ)
    (splitType : Polynomial Coeff → TypeCode)
    (rescale recenter : Polynomial Coeff → Polynomial Coeff)
    (coordMeasure : Set Coeff → ℝ≥0∞)
    (q₀ : ℝ≥0∞) where
  haarBall :
    ∀ t : ℕ, coordMeasure {a | valuation a ≤ (valuation a) ^ t} = (q₀ ^ t)⁻¹
  haarShell :
    ∀ t : ℕ, coordMeasure {a | valuation a = (valuation a) ^ t} =
      (1 - q₀⁻¹) * (q₀ ^ t)⁻¹
  haarIndep :
    ∀ (I : Finset ℕ) (A : ℕ → Set Coeff),
      coordMeasure {a | ∀ i ∈ I, a ∈ A i} =
        ∏ i ∈ I, coordMeasure (A i)
  npSlopes :
    ∀ g : Polynomial Coeff, rootValues g = polygonSlopes g
  typeRescale :
    ∀ g : Polynomial Coeff, splitType (rescale g) = splitType g
  typeRecenter :
    ∀ g : Polynomial Coeff, splitType (recenter g) = splitType g

end LeanUrat.Scaffold
