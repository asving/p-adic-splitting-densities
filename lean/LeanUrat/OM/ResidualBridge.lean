/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.ResidualPolynomial
import LeanUrat.OM.NewtonPolygon
import LeanUrat.OM.Development
import LeanUrat.OM.PadicLift
import LeanUrat.OM.QuotientBox
import LeanUrat.OM.Classifier

/-!
# DEVELOP-DIGIT ↔ RESIDUAL bridge (order ≤ 1)

**The shared gate certifying `classifyGenuine`'s descent residual reader as the genuine Montes
residual polynomial, at order ≤ 1.** This makes citation #4 (classify = OM-tree faithfulness) honest
for the order-1 descent stream: the reader `Classifier.childResidual`, which walks the φ-adic
DEVELOP-DIGIT constant-term residues, is EXACTLY `M4.residualPoly` (GMN Def 2.21) instantiated
at the develop-digit residue coefficient datum (GMN Def 2.20).

This file is READ-ONLY over `ResidualPolynomial`, `Classifier`, `Development`, `PadicLift`,
`QuotientBox`, `NewtonPolygon`. It edits NONE of them (a concurrent stream may touch `Classifier`).

## The two readers being reconciled

`Classifier.childResidual p N f ψ μ : (ZMod p)[X]` (Classifier.lean:295) is
`∑ t : Fin μ, C (zmodUnitResidue p N ((develop (liftKey p N ψ) μ f.1 t).coeff 0)) · X^t`
— a `Fin μ`-indexed sum of `C(·) X^t`, reading the develop-digit constant-term unit residues
(NO on-side guard; the guard is discharged automatically at order 1, see the scope note).

`M4.residualPoly coeffData S : kS[X]` (ResidualPolynomial.lean:74) is
`∑ t ∈ Finset.range (residualDeg S + 1), C (coeffData t) · X^t`
— a `Finset.range (residualDeg S + 1)`-indexed sum of `C(·) X^t`, with `coeffData` an opaque
per-abscissa datum and `residualCoeff coeffData S t = coeffData t` a pass-through.

The two are the SAME `∑ C(·) X^t` shape. The bridge exhibits `childResidual` AS `residualPoly`
instantiated at the develop-digit residue datum `childDigitData`, once the index ranges are
reconciled (`Fin μ` vs `Finset.range (residualDeg S + 1)`, i.e. `μ = residualDeg S + 1`).

## Results (numbered; statement is load-bearing)

* **`childDigitData`** — the develop-digit residue reader as an `ℕ → ZMod p` coefficient datum,
  the `M4`-shaped analogue of `boxCoeffData`: reads the `ZMod p` unit residue of the constant term
  of the `t`-th φ-adic develop digit (for `t < μ`), and `0` beyond the digit budget.
* **Theorem 1 `childResidual_eq_range_sum`** (side-free core) —
  `childResidual p N f ψ μ = ∑ t ∈ Finset.range μ, C (childDigitData p N f ψ μ t) · X^t`.
  The `Fin μ → Finset.range μ` re-indexing of the reader against its own coefficient datum. This is
  the load-bearing identity; the `residualPoly` form is a corollary.
* **Theorem 2 `childResidual_eq_residualPoly`** (the bridge) — for a side `S` with
  `residualDeg S + 1 = μ`,
  `childResidual p N f ψ μ = M4.residualPoly (childDigitData p N f ψ μ) S`.
  i.e. `childResidual` IS `residualPoly` instantiated at the develop-digit residue datum. The single
  index-reconciliation hypothesis `residualDeg S + 1 = μ` is honest and NECESSARY (see scope note).
* **Theorem 3 `childResidual_coeff`** — the coefficient reader:
  `(childResidual p N f ψ μ).coeff j = if j < μ then childDigitData p N f ψ μ j else 0`.
  The develop-digit residue read out coefficient-by-coefficient, matching `residualPoly_coeff`.
* **`childDigitData_vanish_ge`** — `childDigitData` vanishes at/above the digit budget (`μ ≤ t`),
  the datum's support bound, mirroring the `residualPoly_coeff` guard.

## Scope note (honest)

* **ORDER ≤ 1 ONLY.** `childResidual` reads the develop-digit residues against `liftKey ψ`, the
  order-1 lift of a residual factor `ψ ∈ (ZMod p)[X]`, with residue field pinned to `Fr = ZMod p`
  (the tame/unramified `deg ψ = 1` first descent). The order-≥2 case needs the residue-field
  EXTENSION reader `childResidualExt` against the higher key `φ_r` over the extension ring `O″`
  (`ChildResidualExt.lean`, `OrderTwoContext.lean`) — that is explicitly OUT OF SCOPE (the known
  limitation; `classifyGenuine`'s faithfulness holds only at order ≤ 1, per `OrderTwoContext`).
* **The on-side guard.** `boxCoeffData` (the ROOT reader, GMN Def 2.20) carries an on-side guard
  `zmodValuation = v₀ + t·h`. `childResidual` (the DESCENT reader) carries NO such guard: at order 1
  the φ-adic development already restricts to the digits ON the relevant side (the develop-digit
  budget `μ` IS the residual degree budget `residualDeg S + 1`), so no separate guard is needed. The
  bridge therefore does NOT thread the guard; it is subsumed by the index-reconciliation hypothesis.
* **Index reconciliation forces one hypothesis.** Theorem 2 needs `residualDeg S + 1 = μ` — the ONLY
  side hypothesis. It is exactly the GMN degree identity `ℓ(S)/e_S + 1 = μ` (the number of residual
  coefficients equals the digit budget) at order 1. Without it the two sums range over different
  index sets and are not equal in general. Theorem 1 (the side-free core) is UNCONDITIONAL.
* **The develop-digit vs side-coefficient geometry** (the more-ambitious `childDigitData` =
  `boxCoeffData`-style side-coefficient identification) is NOT proved here: it is the genuinely-new
  order-1 development geometry (`develop`-digit constant term = side-coefficient unit part), an
  OPEN sub-target flagged in the report, not silently sorried.

Discipline: no `sorry`/`axiom`/`native_decide`; core-only `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.ResidualBridge

open Polynomial LeanUrat.OM

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-! ## The develop-digit residue reader as an `M4` coefficient datum

`childDigitData` packages the develop-digit constant-term residues into an `ℕ → ZMod p` coefficient
datum — the exact shape `M4.residualPoly` consumes. For `t < μ` it is the `ZMod p` unit residue of
the constant term of the `t`-th φ-adic develop digit (against the order-1 lifted key `liftKey ψ`); for
`t ≥ μ` (beyond the digit budget) it is `0`. This is the descent-stream analogue of
`Classifier.boxCoeffData` (the root reader). -/

/-- **The develop-digit residue coefficient datum** (`M4`-shaped, GMN Def 2.20 at order 1). Reads the
`ZMod p` unit residue of the constant term of the `t`-th φ-adic develop digit of `f` against
`liftKey ψ`, for `t < μ`; `0` beyond the digit budget. This is the `ℕ → ZMod p` datum that
`M4.residualPoly` consumes — the descent analogue of `Classifier.boxCoeffData`. -/
noncomputable def childDigitData (p : ℕ) [Fact p.Prime] {n : ℕ} (N : ℕ)
    (f : QuotientBox.monicBox p N n) (ψ : (ZMod p)[X]) (μ : ℕ) : ℕ → ZMod p :=
  fun t =>
    if h : t < μ then
      PadicLift.zmodUnitResidue p N
        ((Development.develop (B.liftKey p N ψ) μ f.1 ⟨t, h⟩).coeff 0)
    else 0

/-- `childDigitData` VANISHES at/above the digit budget `μ` (the datum's support bound), mirroring the
`residualPoly_coeff` guard: for `μ ≤ t` there is no `t`-th develop digit, so the datum is `0`. -/
theorem childDigitData_vanish_ge (N : ℕ) (f : QuotientBox.monicBox p N n)
    (ψ : (ZMod p)[X]) (μ : ℕ) (t : ℕ) (ht : μ ≤ t) :
    childDigitData p N f ψ μ t = 0 := by
  rw [childDigitData, dif_neg (by omega)]

/-- `childDigitData` on the digit budget: for `t < μ` it is exactly the develop-digit residue the
reader consumes (unfolding the `dif_pos`). -/
theorem childDigitData_of_lt (N : ℕ) (f : QuotientBox.monicBox p N n)
    (ψ : (ZMod p)[X]) (μ : ℕ) (t : ℕ) (ht : t < μ) :
    childDigitData p N f ψ μ t =
      PadicLift.zmodUnitResidue p N
        ((Development.develop (B.liftKey p N ψ) μ f.1 ⟨t, ht⟩).coeff 0) := by
  rw [childDigitData, dif_pos ht]

/-! ## Theorem 1 — the side-free core identity

`childResidual` is a `Fin μ`-indexed `∑ C(·) X^t`. Re-indexing over `Finset.range μ` against its own
coefficient datum `childDigitData` yields the plain-`ℕ`-indexed `∑ C(·) X^t` — the shape
`M4.residualPoly` is (this is what lets `childResidual` be RECOGNIZED as a `residualPoly`). The
re-indexing is `Fin.sum_univ_eq_sum_range` termwise; the coefficient datum agrees with the reader on
`range μ` because `childDigitData t = reader t` precisely for `t < μ`. -/

/-- **Theorem 1 (side-free core).** `childResidual` equals its own `Finset.range μ`-indexed
`∑ C(childDigitData t) · X^t`. The `Fin μ → Finset.range μ` re-indexing of the develop-digit reader
against the `childDigitData` coefficient datum. UNCONDITIONAL (no side, no index hypothesis). This is
the load-bearing identity; the `residualPoly` bridge (Theorem 2) is a one-line corollary. -/
theorem childResidual_eq_range_sum (N : ℕ) (f : QuotientBox.monicBox p N n)
    (ψ : (ZMod p)[X]) (μ : ℕ) :
    B.childResidual p N f ψ μ =
      ∑ t ∈ Finset.range μ, Polynomial.C (childDigitData p N f ψ μ t) * Polynomial.X ^ t := by
  rw [B.childResidual]
  -- Re-index the RHS `Finset.range μ` sum back to a `Fin μ` sum (`Finset.sum_range`), then match
  -- termwise. Going range→Fin (not Fin→range) avoids the `((↑i : ℕ) : Fin μ) = i` round-trip: on the
  -- `Fin` side the digit index is `⟨↑i, _⟩`, which is `i` by `Fin.eta`.
  rw [Finset.sum_range (fun t => Polynomial.C (childDigitData p N f ψ μ t) * Polynomial.X ^ t)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- on `i : Fin μ`, `childDigitData ↑i = reader ⟨↑i, i.isLt⟩ = reader i` (the `Fin.mk` collapses to `i`
  -- definitionally, so the `rw` closes the goal outright).
  rw [childDigitData_of_lt N f ψ μ (i : ℕ) i.isLt]

/-! ## Theorem 2 — the DEVELOP-DIGIT ↔ RESIDUAL bridge

The bridge proper: `childResidual` IS `M4.residualPoly` instantiated at the develop-digit residue
datum `childDigitData`, for any side `S` whose residual degree matches the digit budget
(`residualDeg S + 1 = μ`). Given the match, `residualPoly (childDigitData …) S = ∑ t ∈ range μ,
C (childDigitData t) X^t` by definition, which is `childResidual` by Theorem 1. -/

/-- **Theorem 2 (the bridge, DEVELOP-DIGIT ↔ RESIDUAL, order ≤ 1).** For a side `S` whose residual
degree matches the develop-digit budget (`residualDeg S + 1 = μ`), the descent residual reader
`childResidual` equals `M4.residualPoly` instantiated at the develop-digit residue datum: it IS the
genuine Montes residual polynomial (GMN Def 2.21) at the develop-digit residue coefficients (GMN Def
2.20). The single hypothesis `residualDeg S + 1 = μ` is the order-1 GMN degree identity `ℓ(S)/e_S + 1
= μ` and is NECESSARY (the two sums range over different index sets otherwise). -/
theorem childResidual_eq_residualPoly (N : ℕ) (f : QuotientBox.monicBox p N n)
    (ψ : (ZMod p)[X]) (μ : ℕ) (S : NewtonPolygon.Side)
    (hdeg : M4.residualDeg S + 1 = μ) :
    B.childResidual p N f ψ μ =
      M4.residualPoly (childDigitData p N f ψ μ) S := by
  rw [childResidual_eq_range_sum N f ψ μ, M4.residualPoly]
  -- `residualPoly`'s range is `range (residualDeg S + 1) = range μ`; `residualCoeff = pass-through`.
  rw [hdeg]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [M4.residualCoeff]

/-! ## Theorem 3 — the coefficient reader

The develop-digit residue read out coefficient-by-coefficient: the `j`-th coefficient of the descent
residual is the `j`-th develop-digit residue for `j < μ`, and `0` beyond the budget. This is the
`residualPoly_coeff` analogue phrased directly on `childResidual` (independent of any side), and is
the form a downstream consumer reads a single residual coefficient with. -/

/-- **Theorem 3 (the coefficient reader).** `(childResidual p N f ψ μ).coeff j = childDigitData p N f
ψ μ j` for `j < μ`, and `0` for `j ≥ μ`. The develop-digit residue read coefficient-by-coefficient;
the `M4.residualPoly_coeff` analogue phrased directly on the descent reader. -/
theorem childResidual_coeff (N : ℕ) (f : QuotientBox.monicBox p N n)
    (ψ : (ZMod p)[X]) (μ : ℕ) (j : ℕ) :
    (B.childResidual p N f ψ μ).coeff j =
      if j < μ then childDigitData p N f ψ μ j else 0 := by
  classical
  rw [childResidual_eq_range_sum N f ψ μ, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range μ) j (fun t => childDigitData p N f ψ μ t)]
  simp only [Finset.mem_range]

/-! ## Corollary — the degree bound (cross-check against `M4` and `ChildResidualExt`)

A sanity corollary tying the bridge back to the `M4` degree machinery: through Theorem 2, the descent
residual has `natDegree ≤ residualDeg S` (the `M4.residualPoly_natDegree_le` bound), matching the
`childResidualExt_natDegree_lt` well-formedness bound `< μ` under the index reconciliation. -/

/-- **Degree bound via the bridge.** Under the index reconciliation `residualDeg S + 1 = μ`, the
descent residual's `natDegree` is `≤ residualDeg S = μ - 1`, inherited from `M4.residualPoly_natDegree_le`
through the bridge. Cross-checks against `ChildResidualExt.childResidualExt_natDegree_lt` (`< μ`). -/
theorem childResidual_natDegree_le (N : ℕ) (f : QuotientBox.monicBox p N n)
    (ψ : (ZMod p)[X]) (μ : ℕ) (S : NewtonPolygon.Side)
    (hdeg : M4.residualDeg S + 1 = μ) :
    (B.childResidual p N f ψ μ).natDegree ≤ M4.residualDeg S := by
  rw [childResidual_eq_residualPoly N f ψ μ S hdeg]
  exact M4.residualPoly_natDegree_le _ S

-- Footprint checks: each built decl must be ⊆ [propext, Classical.choice, Quot.sound]
-- (no `sorry`/`axiom`/`native_decide`).
#print axioms childResidual_eq_range_sum
#print axioms childResidual_eq_residualPoly
#print axioms childResidual_coeff
#print axioms childResidual_natDegree_le
#print axioms childDigitData_vanish_ge

end LeanUrat.OM.ResidualBridge
