/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# SerreLocalFields — the Wave-2b-class structure-theorem axiom (sign-off queue item 2,
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`; Asvin sign-off 2026-07-31)

THE DOCUMENTED MATHLIB WALL (recorded at `OM/QpType.lean` lines 65–67, and re-hit by the
BP1 Group-E plan per SYNTHESIS PASS 1 finding C3/N1): mathlib at the pin (v4.31.0) cannot
prove that the integral closure of `ℤ_[p]` in a finite field extension `L` of `ℚ_[p]` is a
discrete valuation ring once `[L : ℚ_p] ≥ 2` is wild — there is no
`IsNonarchimedeanLocalField`, no finite-extension `Valued`/extension-of-valuation API, and
no DVR-ness result for `integralClosure ℤ_[p] L`. This module declares that ONE missing
scalar fact as a literature axiom, per the C3/N1 adjudication ("the documented Mathlib
wall … rides the Wave-2b axiom = the classical structure theorem for complete DVRs").

## The citation (exact)

**Serre, *Corps Locaux* (Hermann, Paris 1962; 2ᵉ éd. 1968) = *Local Fields* (transl.
M. J. Greenberg, Graduate Texts in Mathematics 67, Springer 1979), Chapter II
("Completion"), §2 ("Extension of a Complete Field"), Proposition 3.** The proposition:
for `A` a complete discrete valuation ring with fraction field `K` and `L/K` a finite
extension of degree `n`, the integral closure `B` of `A` in `L` is a discrete valuation
ring, `B` is a free `A`-module of rank `n`, `B` is complete, and the valuation of `B` is
the unique extension of that of `A`. (Cross-check of the numbering: the same clause is
cited as "Chapter 2, Section 2, Proposition 3 in Serre's Local Fields" by the
de Frutos-Fernández–Nuccio formalization, `LocalClassFieldTheory/DiscreteValuationRing/
Extensions.lean`, `integralClosure.discreteValuationRing_of_finite_extension` — the
CPP '24 paper arXiv:2310.01998 formalizes exactly this wall for abstract complete DVRs.)

## What is declared (MINIMAL clause, per the item-2 charge)

ONLY the DVR-ness clause, ONLY at the instance `(A, K) = (ℤ_[p], ℚ_[p])`:

* `AX_integralClosure_dvr` — for every finite-dimensional field extension `L` of `ℚ_[p]`
  (the `ℤ_[p]`-structure pinned through the tower `ℤ_[p] → ℚ_[p] → L`),
  `IsDiscreteValuationRing (integralClosure ℤ_[p] L)`.

NOT declared (each either derivable at the pin or not needed by the wall): freeness/rank
`n` (derivable: `IsIntegralClosure.isNoetherian` in char 0 + finite torsion-free over a
PID), completeness of `B`, uniqueness of the extended valuation, e·f = n, lying-over
(DERIVED below, axiom-free, from integrality + locality: `maximalIdeal_liesOver`).

Faithfulness note (the algebra-structure quantifier): the axiom quantifies over ANY
`Algebra ℚ_[p] L` making `L` finite-dimensional, with `Algebra ℤ_[p] L` REQUIRED to be
the composite through `ℚ_[p]` (the `IsScalarTower` hypothesis). For any such structure
map `φ : ℚ_[p] → L` (a field embedding), `integralClosure ℤ_[p] L` depends only on the
image subring `φ(ℤ_[p])` — a complete DVR with fraction field `φ(ℚ_[p])` by transport
along the ring isomorphism — so every instance of the axiom is literally an instance of
the cited Proposition 3 with `(A, K, L) = (φ(ℤ_[p]), φ(ℚ_[p]), L)`. No instance asserts
anything beyond the book statement.

## Consumers and gating (item-2 duty (d))

The re-pointed `MovesT.ramIdx`/`resDeg` (item 2 duty (a)) junk-dispatch on the Prop-class
`IsLocalRing (integralClosure ℤ_[p] (AdjoinRoot (g.map (algebraMap ℤ_[p] ℚ_[p]))))`; the
smoke theorem `isLocalRing_integralClosure_adjoinRoot` below shows the axiom FIRES that
dispatch on the whole monic ℚ_p-irreducible locus. **BP1 Group E provers (IB-E5–E7) stay
gated**: the orchestrator runs a Codex audit of this axiom statement BEFORE any Group-E
consumer is dispatched (recorded in `notes/QUEUE_EXECUTION_2026-07-31.md`, item 2).

## Safety evidence (the U1 lesson, axiom edition)

* Hypothesis-class non-vacuity: `axiom_nonvacuous` — the instance pack synthesizes at
  `L = ℚ_[p]` (so the axiom is not quantifying over an empty class).
* Degree-1 coherence: the axiom's `L = ℚ_[p]` instance asserts DVR-ness of
  `integralClosure ℤ_[p] ℚ_[p]`; the SAME content at the `IsIntegralClosure` witness
  `O = ℤ_[p]` is machine-checked axiom-free at `OM/QpType.trivialFactorData` (ℤ_[p] IS a
  DVR, integrally closed in `ℚ_[p]`). A direct axiom-free proof for the subalgebra
  carrier itself stalled at the pin (no `RingEquiv.isDiscreteValuationRing` transfer;
  `Algebra.botEquiv` needs a field base) — recorded as an open (cheap) upside probe,
  3 bounded attempts spent 2026-07-31.
* An OM-side consequence check: the axiom makes `OM/QpType.LocalFactorData p g`
  constructible for every monic ℚ_p-irreducible `g` (all remaining bundle fields are
  mathlib-derivable) — construction deliberately NOT executed here (Group-E/OM wiring is
  behind the Codex audit gate).

Leaf module: imports Mathlib only; exactly ONE axiom; zero `sorry`. Census block at the
bottom; the file is registered in `LeanUrat/AxChk_baseline.lean` (the trusted-base ground
truth) — the density capstones must remain Lean-core (this axiom must NOT enter their
footprints).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.SerreLocalFields

open Polynomial

/-- **The Wave-2b-class literature axiom** (Serre, *Corps Locaux* / *Local Fields*
GTM 67, Chapter II §2, Proposition 3 — the DVR clause, at the instance
`(A, K) = (ℤ_[p], ℚ_[p])`): the integral closure of `ℤ_[p]` in a finite field extension
`L` of `ℚ_[p]` is a discrete valuation ring. The `ℤ_[p]`-algebra structure on `L` is
pinned to the composite through `ℚ_[p]` by the `IsScalarTower` hypothesis. Declared
2026-07-31 (sign-off queue item 2); Codex statement audit PENDING — Group E consumers
stay gated until it passes. -/
axiom AX_integralClosure_dvr (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] :
    IsDiscreteValuationRing (integralClosure ℤ_[p] L)

/-- The dispatch Prop-class of the re-pointed `MovesT.ramIdx`/`resDeg`, from the axiom:
a DVR is local. (Footprint: the axiom.) -/
theorem integralClosure_isLocalRing (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] :
    IsLocalRing (integralClosure ℤ_[p] L) :=
  letI := AX_integralClosure_dvr p L
  inferInstance

/-- Lying-over is DERIVED, not axiomatized (stated over an `IsLocalRing` HYPOTHESIS, so
this theorem is AXIOM-FREE): the maximal ideal of the integral closure lies over
`p·ℤ_[p]`, by integrality (maximal contracts to maximal) + locality of `ℤ_[p]`.
This discharges the `LocalFactorData.liesOver` field shape once the axiom supplies the
instance. -/
theorem maximalIdeal_liesOver (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L]
    [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]
    [IsLocalRing (integralClosure ℤ_[p] L)] :
    (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] L)).LiesOver
      (IsLocalRing.maximalIdeal ℤ_[p]) := by
  haveI : Algebra.IsIntegral ℤ_[p] (integralClosure ℤ_[p] L) :=
    ⟨fun x => integralClosure.isIntegral x⟩
  have hmax : (Ideal.comap (algebraMap ℤ_[p] (integralClosure ℤ_[p] L))
      (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] L))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  constructor
  rw [Ideal.under_def]
  exact (IsLocalRing.eq_maximalIdeal hmax).symm

/-- **The smoke theorem (item-2 "what the repair opens")**: on the monic
ℚ_p-irreducible locus, the axiom FIRES the re-pointed `MovesT.ramIdx`/`resDeg` junk
dispatch — `IsLocalRing (integralClosure ℤ_[p] (AdjoinRoot (g.map (algebraMap ℤ_[p]
ℚ_[p]))))` holds (the field/finite-dimension/tower instance pack synthesizes at
`AdjoinRoot`). Stated in pure mathlib vocabulary (this leaf does not import MovesT);
the Prop is syntactically the dispatch guard of `MovesT.ramIdx`/`resDeg`. -/
theorem isLocalRing_integralClosure_adjoinRoot (p : ℕ) [Fact p.Prime]
    (g : Polynomial ℤ_[p]) (hm : g.Monic)
    (hirr : Irreducible (g.map (algebraMap ℤ_[p] ℚ_[p]))) :
    IsLocalRing (integralClosure ℤ_[p] (AdjoinRoot (g.map (algebraMap ℤ_[p] ℚ_[p])))) := by
  haveI : Fact (Irreducible (g.map (algebraMap ℤ_[p] ℚ_[p]))) := ⟨hirr⟩
  have hne : g.map (algebraMap ℤ_[p] ℚ_[p]) ≠ 0 :=
    (hm.map (algebraMap ℤ_[p] ℚ_[p])).ne_zero
  haveI : FiniteDimensional ℚ_[p] (AdjoinRoot (g.map (algebraMap ℤ_[p] ℚ_[p]))) :=
    PowerBasis.finite (AdjoinRoot.powerBasis hne)
  haveI := AX_integralClosure_dvr p (AdjoinRoot (g.map (algebraMap ℤ_[p] ℚ_[p])))
  exact inferInstance

/-- Hypothesis-class NON-VACUITY (the U1 lesson): the axiom's instance pack synthesizes
at `L = ℚ_[p]` — the quantified class is inhabited, so the axiom is not a vacuous ∀.
(Its content at this instance — DVR-ness of the closure of `ℤ_[p]` in `ℚ_[p]` — is the
degree-1 case, independently witnessed axiom-free at the `IsIntegralClosure` carrier by
`OM/QpType.trivialFactorData`.) -/
theorem axiom_nonvacuous (p : ℕ) [Fact p.Prime] :
    IsDiscreteValuationRing (integralClosure ℤ_[p] ℚ_[p]) :=
  AX_integralClosure_dvr p ℚ_[p]

/-! ## Census (this module declares exactly ONE axiom; the consumers below it print
`AX_integralClosure_dvr` + core; `maximalIdeal_liesOver` must print CORE ONLY) -/

section AxCheck

#print axioms LeanUrat.SerreLocalFields.AX_integralClosure_dvr
#print axioms LeanUrat.SerreLocalFields.integralClosure_isLocalRing
#print axioms LeanUrat.SerreLocalFields.maximalIdeal_liesOver
#print axioms LeanUrat.SerreLocalFields.isLocalRing_integralClosure_adjoinRoot
#print axioms LeanUrat.SerreLocalFields.axiom_nonvacuous

end AxCheck

end LeanUrat.SerreLocalFields
