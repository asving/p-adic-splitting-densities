/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.ResidualPolynomial
import LeanUrat.OM.NewtonPolygon
import LeanUrat.OM.DevelopmentExt
import LeanUrat.OM.OrderTwoContext
import LeanUrat.OM.ChildResidualExt

/-!
# DEVELOP-DIGIT ↔ RESIDUAL bridge over the residue-field EXTENSION `k_S = resField` (P9, WAVE 3)

**The EXTENSION ANALOGUE of the order-1 `ResidualBridge` (build #67), now over the genuine finite
extension field `k_S = resField = F_{p^{deg g}}` instead of `ℤ/p`.** This is `OPEN TARGET B.2` of
`DevelopmentExt.lean` / wave-3 Goal 1, made tractable by the confirmed semantic fact (Asvin,
2026-07-16): the genuine GMN Def 2.20 residual coefficient `c_t` IS the FULL `k_S`-element — the
whole develop-digit reduced in the residue field — NOT merely its `ℤ/p` constant term.
`ChildResidualExt.childResidualExt` (waves 1/2) ALREADY reads that full `resField`-element
(`resUnitResidue` of the `O″`-develop-digit constant term); so putting it in `M4.residualPoly`-over-
`resField` FORM certifies it IS the genuine Def 2.20 residual for `deg ψ ≥ 2`.

This file is READ-ONLY over `ResidualPolynomial`, `DevelopmentExt`, `OrderTwoContext`,
`ChildResidualExt`, `UnramifiedBase`, `NewtonPolygon`. It edits NONE of them (two-stream contention
rule: only B's own + new files; NEVER `Classifier`/`Development`/`OMType`/`ResidualPolynomial`/
`UnramifiedBase`).

## The two readers being reconciled (over `resField`, mirroring #67 over `ℤ/p`)

`ChildResidualExt.childResidualExt p N g hgm hN Φ μ h : resField[X]`
(`ChildResidualExt.lean:213`) is
`∑ t : Fin μ, C (resUnitResidue … ((developExt … Φ μ h t).coeff 0)) · X^t`
— a `Fin μ`-indexed sum reading the FULL `resField` unit residue of each `O″`-develop-digit constant
term. Per the confirmed fact this full-element reading IS GMN Def 2.20's `c_t` for `deg ψ ≥ 2`.

`M4.residualPoly coeffData S : kS[X]` (`ResidualPolynomial.lean:74`, GENERIC over any
`kS : Type* [Field kS] [Finite kS]`) is
`∑ t ∈ Finset.range (residualDeg S + 1), C (residualCoeff coeffData S t) · X^t`, with
`residualCoeff coeffData S t = coeffData t` a pass-through. It instantiates at `kS = resField`
(a `Field` under `Fact (Irreducible ḡ)`, `Finite` via `OrderTwoContext.finite_resField`).

Same `∑ C(·) X^t` shape. The bridge exhibits `childResidualExt` AS `residualPoly` instantiated at the
FULL-`resField`-element develop-digit datum `childDigitDataExt`, once `μ = residualDeg S + 1`.

## Results (numbered; statement is load-bearing)

* **`childDigitDataExt`** — the `O″`-develop-digit residue reader as an `ℕ → resField` coefficient
  datum (the `M4`-shaped, EXTENSION analogue of `ResidualBridge.childDigitData`): for `t < μ` it is
  the FULL `resField` element `resUnitResidue ((developExt Φ μ h ⟨t,·⟩).coeff 0)`; `0` beyond the
  digit budget. This is the genuine GMN Def 2.20 residual datum over `resField` (per the confirm).
* **Theorem 1 `childResidualExt_eq_range_sum`** (side-free core) —
  `childResidualExt … = ∑ t ∈ Finset.range μ, C (childDigitDataExt … t) · X^t`. The
  `Fin μ → Finset.range μ` re-indexing of the reader against its own datum. UNCONDITIONAL. The
  load-bearing identity; the `residualPoly` form is a corollary.
* **Theorem 2 `childResidualExt_eq_residualPoly`** (THE EXTENSION BRIDGE, the gating result) — under
  `Fact (Irreducible ḡ)` + `Finite resField`, for a side `S` with `residualDeg S + 1 = μ`:
  `childResidualExt … = M4.residualPoly (childDigitDataExt …) S` over `k_S = resField`.
  i.e. `childResidualExt` IS `M4.residualPoly` (GMN Def 2.21) at the FULL-`resField`-element
  develop-digit residue datum (GMN Def 2.20). The single hypothesis `residualDeg S + 1 = μ` is the
  order-`r` GMN degree identity `ℓ(S)/e_S + 1 = μ` and is NECESSARY (the two sums range over
  different index sets otherwise) — the exact extension analogue of #67's `residualDeg S + 1 = μ`.
* **Theorem 3 `childResidualExt_coeff`** — the coefficient reader:
  `(childResidualExt …).coeff j = if j < μ then childDigitDataExt … j else 0`.
* **`childDigitDataExt_vanish_ge`** — the datum vanishes at/above the digit budget (`μ ≤ t`).

## What THIS CERTIFIES (exact, honest)

Given the confirmed semantic fact (the full-`k_S`-element reading IS GMN Def 2.20's `c_t`), Theorem 2
certifies: **`childResidualExt` is the genuine GMN Def 2.21 residual polynomial in the
`residualPoly`-over-`k_S = resField` FORM, for residue-field extensions `deg ψ ≥ 2`**, exactly as
#67 certifies `childResidual` for order ≤ 1. This is the EXTENSION ANALOGUE of the committed #67
bridge, closing wave-3 Goal 1.

## Scope note (honest — what is NOT yet closed)

* **Index reconciliation forces one hypothesis** (Theorem 2): `residualDeg S + 1 = μ`, the ONLY side
  hypothesis, exactly as #67. Theorem 1 (side-free core) is UNCONDITIONAL.
* **`Φ`, `h` still ARBITRARY.** Like `childResidualExt` itself, this bridge is over an ARBITRARY monic
  key `Φ : O″[X]` and box element `h : O″[X]`. It does NOT here tie `Φ = liftKeyExt … Ψ` (Lemma A) nor
  `h` to a base-changed `f` — that wiring is `classifyGenuineExtAux` (blueprint §3), a SEPARATE
  recursion (wave 4). What is certified is the `residualPoly`-FORM identity, which is what makes the
  reader recognizable as `M4.residualPoly`; the reader-of-a-genuine-`f` wiring is the remaining wave.
* **`resUnitResidue` canonicity** (witness-independence, `x ≠ 0`) is PROVED in wave 2
  (`resUnitResidue_eq_of_witness`); the `x = 0` boundary is genuinely non-canonical and is NOT
  claimed (a residual coefficient read off the polygon is `0`, handled by the guard, never by
  `resUnitResidue 0`). This bridge does not depend on canonicity — it is a `∑ C(·) X^t`-form fact.

Discipline: no `sorry`/`axiom`/`native_decide`; core-only `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.ResidualBridgeExt

open Polynomial LeanUrat.OM

noncomputable section

variable (p N : ℕ) [hp : Fact p.Prime] (g : (ZMod (p ^ N))[X])

/-! ## The `O″`-develop-digit residue reader as an `M4` coefficient datum over `resField`

`childDigitDataExt` packages the `O″`-develop-digit constant-term residues (read via
`resUnitResidue` into the FULL residue field `resField`) into an `ℕ → resField` coefficient datum —
the exact shape `M4.residualPoly` consumes. For `t < μ` it is `resUnitResidue` of the constant term
of the `t`-th `O″`-develop digit of `h` against the monic key `Φ`; for `t ≥ μ` (beyond the digit
budget) it is `0`. The EXTENSION analogue of `ResidualBridge.childDigitData`. -/

/-- **The `O″`-develop-digit residue coefficient datum** over `resField` (`M4`-shaped, GMN Def 2.20
for `deg ψ ≥ 2`). Reads the FULL `resField` unit residue of the constant term of the `t`-th
`O″`-develop digit of `h` against the monic key `Φ`, for `t < μ`; `0` beyond the digit budget. This
is the `ℕ → resField` datum `M4.residualPoly` consumes — the EXTENSION analogue of
`ResidualBridge.childDigitData`. Per the confirmed semantic fact, this full-element reading IS the
genuine GMN Def 2.20 residual coefficient over the extension field. -/
def childDigitDataExt (hgm : g.Monic) (hN : 0 < N)
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (h : (UnramifiedBase.Oring p N g)[X]) :
    ℕ → UnramifiedBase.resField p N g hN :=
  fun t =>
    if ht : t < μ then
      ChildResidualExt.resUnitResidue p N g hgm hN
        ((DevelopmentExt.developExt p N g Φ μ h ⟨t, ht⟩).coeff 0)
    else 0

/-- `childDigitDataExt` VANISHES at/above the digit budget `μ` (the datum's support bound), mirroring
the `residualPoly_coeff` guard: for `μ ≤ t` there is no `t`-th develop digit, so the datum is `0`. -/
theorem childDigitDataExt_vanish_ge (hgm : g.Monic) (hN : 0 < N)
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (h : (UnramifiedBase.Oring p N g)[X])
    (t : ℕ) (ht : μ ≤ t) :
    childDigitDataExt p N g hgm hN Φ μ h t = 0 := by
  rw [childDigitDataExt, dif_neg (by omega)]

/-- `childDigitDataExt` on the digit budget: for `t < μ` it is exactly the develop-digit residue the
reader consumes (unfolding the `dif_pos`). -/
theorem childDigitDataExt_of_lt (hgm : g.Monic) (hN : 0 < N)
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (h : (UnramifiedBase.Oring p N g)[X])
    (t : ℕ) (ht : t < μ) :
    childDigitDataExt p N g hgm hN Φ μ h t =
      ChildResidualExt.resUnitResidue p N g hgm hN
        ((DevelopmentExt.developExt p N g Φ μ h ⟨t, ht⟩).coeff 0) := by
  rw [childDigitDataExt, dif_pos ht]

/-! ## Theorem 1 — the side-free core identity

`childResidualExt` is a `Fin μ`-indexed `∑ C(·) X^t`. Re-indexing over `Finset.range μ` against its
own coefficient datum `childDigitDataExt` yields the plain-`ℕ`-indexed `∑ C(·) X^t` — the shape
`M4.residualPoly` is. The re-indexing is `Finset.sum_range` termwise; the coefficient datum agrees
with the reader on `range μ` because `childDigitDataExt t = reader ⟨t, _⟩` precisely for `t < μ`.
Verbatim the `ResidualBridge.childResidual_eq_range_sum` argument, now over `resField`. -/

/-- **Theorem 1 (side-free core, EXTENSION).** `childResidualExt` equals its own `Finset.range μ`-
indexed `∑ C(childDigitDataExt t) · X^t`. The `Fin μ → Finset.range μ` re-indexing of the
`O″`-develop-digit reader against the `childDigitDataExt` coefficient datum. UNCONDITIONAL (no side,
no index hypothesis; no `hgirr`/field structure needed — `resField` is a `CommRing` regardless). The
load-bearing identity; the `residualPoly` bridge (Theorem 2) is a one-line corollary. -/
theorem childResidualExt_eq_range_sum (hgm : g.Monic) (hN : 0 < N)
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (h : (UnramifiedBase.Oring p N g)[X]) :
    ChildResidualExt.childResidualExt p N g hgm hN Φ μ h =
      ∑ t ∈ Finset.range μ,
        Polynomial.C (childDigitDataExt p N g hgm hN Φ μ h t) * Polynomial.X ^ t := by
  rw [ChildResidualExt.childResidualExt]
  -- Re-index the RHS `Finset.range μ` sum back to a `Fin μ` sum (`Finset.sum_range`), then match
  -- termwise. Going range→Fin (not Fin→range) avoids the `((↑i : ℕ) : Fin μ) = i` round-trip: on the
  -- `Fin` side the digit index is `⟨↑i, _⟩`, which is `i` by `Fin.eta`.
  rw [Finset.sum_range
    (fun t => Polynomial.C (childDigitDataExt p N g hgm hN Φ μ h t) * Polynomial.X ^ t)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- on `i : Fin μ`, `childDigitDataExt ↑i = reader ⟨↑i, i.isLt⟩ = reader i` (the `Fin.mk` collapses
  -- to `i` definitionally, so the `rw` closes the goal outright).
  rw [childDigitDataExt_of_lt p N g hgm hN Φ μ h (i : ℕ) i.isLt]

/-! ## Theorem 2 — the DEVELOP-DIGIT ↔ RESIDUAL bridge over `k_S = resField` (the gating result)

The bridge proper: `childResidualExt` IS `M4.residualPoly` instantiated at the FULL-`resField`-element
develop-digit residue datum `childDigitDataExt`, for any side `S` whose residual degree matches the
digit budget (`residualDeg S + 1 = μ`). The `resField` field/finite instances are supplied from
`hgirr` (`Fact (Irreducible ḡ)` fires `AdjoinRoot.instField`; `OrderTwoContext.finite_resField`
supplies `Finite`), which is what lets `M4.residualPoly`'s `[Field kS] [Finite kS]` instantiate at
`kS = resField`. Given the match, `residualPoly (childDigitDataExt …) S = ∑ t ∈ range μ,
C (childDigitDataExt t) X^t` by definition (range `= range μ`, `residualCoeff = pass-through`), which
is `childResidualExt` by Theorem 1. The EXTENSION analogue of `ResidualBridge.childResidual_eq_residualPoly` (#67). -/

/-- **Theorem 2 (THE EXTENSION BRIDGE, DEVELOP-DIGIT ↔ RESIDUAL over `k_S = resField`).** Under
`Fact (Irreducible ḡ)` (fixing the `Field` structure on `resField`) with `Finite resField`, for a
side `S` whose residual degree matches the develop-digit budget (`residualDeg S + 1 = μ`), the
`O″`-development residual reader `childResidualExt` equals `M4.residualPoly` instantiated at the
FULL-`resField`-element develop-digit residue datum: it IS the genuine Montes residual polynomial
(GMN Def 2.21) at the develop-digit residue coefficients (GMN Def 2.20), NOW over the residue-field
EXTENSION `k_S = resField = F_{p^{deg g}}` (the `deg ψ ≥ 2` regime).

The single hypothesis `residualDeg S + 1 = μ` is the order-`r` GMN degree identity `ℓ(S)/e_S + 1 = μ`
and is NECESSARY (the two sums range over different index sets otherwise) — the EXACT extension
analogue of #67's index reconciliation. Per the confirmed semantic fact (the full-`k_S`-element
develop-digit reading IS Def 2.20's `c_t` for `deg ψ ≥ 2`), this certifies `childResidualExt` as the
genuine residual for residue-field extensions, closing wave-3 Goal 1. Core-only. -/
theorem childResidualExt_eq_residualPoly (hgm : g.Monic) (hN : 0 < N)
    [Fact (Irreducible (UnramifiedBase.gbar p N g hN))]
    [Finite (UnramifiedBase.resField p N g hN)]
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (h : (UnramifiedBase.Oring p N g)[X])
    (S : NewtonPolygon.Side) (hdeg : M4.residualDeg S + 1 = μ) :
    ChildResidualExt.childResidualExt p N g hgm hN Φ μ h =
      M4.residualPoly (childDigitDataExt p N g hgm hN Φ μ h) S := by
  rw [childResidualExt_eq_range_sum p N g hgm hN Φ μ h, M4.residualPoly]
  -- `residualPoly`'s range is `range (residualDeg S + 1) = range μ`; `residualCoeff = pass-through`.
  rw [hdeg]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [M4.residualCoeff]

/-! ## Theorem 3 — the coefficient reader

The `O″`-develop-digit residue read out coefficient-by-coefficient: the `j`-th coefficient of the
extension residual is the `j`-th develop-digit residue for `j < μ`, and `0` beyond the budget. The
`residualPoly_coeff` analogue phrased directly on `childResidualExt` (independent of any side). -/

/-- **Theorem 3 (the coefficient reader, EXTENSION).** `(childResidualExt …).coeff j =
childDigitDataExt … j` for `j < μ`, and `0` for `j ≥ μ`. The `O″`-develop-digit residue read
coefficient-by-coefficient; the `M4.residualPoly_coeff` analogue phrased directly on the extension
reader. UNCONDITIONAL (no field structure needed). -/
theorem childResidualExt_coeff (hgm : g.Monic) (hN : 0 < N)
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (h : (UnramifiedBase.Oring p N g)[X]) (j : ℕ) :
    (ChildResidualExt.childResidualExt p N g hgm hN Φ μ h).coeff j =
      if j < μ then childDigitDataExt p N g hgm hN Φ μ h j else 0 := by
  classical
  rw [childResidualExt_eq_range_sum p N g hgm hN Φ μ h, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range μ) j (fun t => childDigitDataExt p N g hgm hN Φ μ h t)]
  simp only [Finset.mem_range]

/-! ## Corollary — the degree bound cross-check (via the bridge)

Under the index reconciliation, the extension residual has `natDegree ≤ residualDeg S`
(`M4.residualPoly_natDegree_le`), matching `ChildResidualExt.childResidualExt_natDegree_lt`'s `< μ`
well-formedness bound. A consistency corollary, exactly as #67's `childResidual_natDegree_le`. -/

/-- **Degree bound via the extension bridge.** Under `residualDeg S + 1 = μ` (with `hgirr` fixing the
field structure), the extension residual's `natDegree` is `≤ residualDeg S = μ - 1`, inherited from
`M4.residualPoly_natDegree_le` through the bridge. Cross-checks against
`ChildResidualExt.childResidualExt_natDegree_lt` (`< μ`). -/
theorem childResidualExt_natDegree_le (hgm : g.Monic) (hN : 0 < N)
    [Fact (Irreducible (UnramifiedBase.gbar p N g hN))]
    [Finite (UnramifiedBase.resField p N g hN)]
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (h : (UnramifiedBase.Oring p N g)[X])
    (S : NewtonPolygon.Side) (hdeg : M4.residualDeg S + 1 = μ) :
    (ChildResidualExt.childResidualExt p N g hgm hN Φ μ h).natDegree ≤ M4.residualDeg S := by
  rw [childResidualExt_eq_residualPoly p N g hgm hN Φ μ h S hdeg]
  exact M4.residualPoly_natDegree_le _ S

-- Footprint checks: each built decl must be ⊆ [propext, Classical.choice, Quot.sound]
-- (no `sorry`/`axiom`/`native_decide`).
#print axioms childResidualExt_eq_range_sum
#print axioms childResidualExt_eq_residualPoly
#print axioms childResidualExt_coeff
#print axioms childResidualExt_natDegree_le
#print axioms childDigitDataExt_vanish_ge

end

end LeanUrat.OM.ResidualBridgeExt
