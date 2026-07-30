/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.Defs

/-! # TV-B4 — redPoly/henPayload/factor-roster level-1 transfer under `chart_pin`

BRIDGE CAMPAIGN unit **TV-B4** (area BP3, cluster B; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.B + §4). E-PHASE SKELETON —
statements pinned, bodies `sorry`.

INFORMAL STATEMENT: `fiberAt`'s clause (iii) reads x only through
`henPayload χ x` (= a function of `redPoly χ x` = a function of the chart
coordinates `x (χ b)`), and clause (vi) only through
`normalizedFactors (redPoly χ x)`. Under (S-chart) = `StableInputs.chart_pin`
(the chart lands in the LEVEL-1 block: `(χ b : ℕ) < n`), two boxes agreeing on
the first n·N coordinates with N ≥ 1 have `(χ b : ℕ) < n ≤ n·N`, hence equal
chart coordinates, hence equal redPoly — and so equal henPayload and equal
normalizedFactors roster.

STATEMENT RESOLUTION (recorded): stated in two layers, mirroring TV-B3 —
* `tv_b4_redPoly_transfer`, the CHART-COORDINATE CORE at generic m: agreement
  ON THE CHART (`x (χ b) = x' (χ b)`) gives `redPoly χ x = redPoly χ x'`.
  This is E5's `hredeq` computation (E5_rootSplit.lean:430-434, "both in one
  root cell") generalized to "agree on the chart coordinates" — the identical
  `Finset.sum_congr` argument; also = `TBCapPinned`'s hen-cap leg shape
  (Defs.lean:1677) without the injectivity hypothesis (unused by the congr);
* the three `_cyl` corollaries at the tower level m = n·N', deriving the chart
  agreement from `chart_pin` + level-<n·N agreement + 1 ≤ N. The `1 ≤ N` guard
  is FREE for the B6 consumer: `VTree.thr … = (… ⊔ 1)` (Defs.lean:734), so
  N ≥ Tr.thr n ≥ 1.

PROOF SKETCH: core — unfold `redPoly` (X^n + Σ_b C (x (χ b))·X^b) and
`Finset.sum_congr rfl` with the pointwise chart agreement. `_cyl` corollaries:
apply `hagree` at the coordinate `χ b`, whose index arithmetic is
(χ b : ℕ) < n ≤ n·N from `hpin b` and `hN : 1 ≤ N`; then the
henPayload/normalizedFactors equalities are `congrArg` through the redPoly
equality (henPayload = henDegrees ∘ redPoly compositionally, Defs.lean:207-216).

deps: B2 (consumes `chart_pin`'s shape; no import needed — the corollaries take
the pinned chart as a hypothesis, so B6 can feed `SI.chart_pin N' h'` directly).
Consumed by: TV-B6 (clauses (iii)/(vi)). difficulty: routine-opus, ~25 lines. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- **TV-B4, the chart-coordinate core** — two boxes agreeing on the chart have
equal level-0 reductions (the E5 `hredeq` computation, `Finset.sum_congr`). -/
theorem tv_b4_redPoly_transfer (χ : Fin n → Fin m) (x x' : Box p m)
    (hchart : ∀ b : Fin n, x (χ b) = x' (χ b)) :
    redPoly χ x = redPoly χ x' := by
  sorry

/-- **TV-B4, redPoly cylinder transfer** — under (S-chart) (`chart_pin`'s shape
at one level: the chart lands in the level-1 block), level-<n·N agreement with
N ≥ 1 gives equal reductions. -/
theorem tv_b4_redPoly_cyl (N' : ℕ) (χ : Fin n → Fin (n * N'))
    (hpin : ∀ b : Fin n, ((χ b : ℕ)) < n)
    (hN : 1 ≤ N) (x x' : Box p (n * N'))
    (hagree : ∀ c : Fin (n * N'), (c : ℕ) < n * N → x c = x' c) :
    redPoly χ x = redPoly χ x' := by
  sorry

/-- **TV-B4, henPayload cylinder transfer** — `fiberAt` clause (iii)'s input:
the (τ-hen) payload is level-<n·N determined under (S-chart). -/
theorem tv_b4_henPayload_cyl (N' : ℕ) (χ : Fin n → Fin (n * N'))
    (hpin : ∀ b : Fin n, ((χ b : ℕ)) < n)
    (hN : 1 ≤ N) (x x' : Box p (n * N'))
    (hagree : ∀ c : Fin (n * N'), (c : ℕ) < n * N → x c = x' c) :
    henPayload χ x = henPayload χ x' := by
  sorry

/-- **TV-B4, factor-roster cylinder transfer** — `fiberAt` clause (vi)'s input:
the normalized-factor multiset of the reduction (hence its repeated-track
filter and every count) is level-<n·N determined under (S-chart). -/
theorem tv_b4_factors_cyl (N' : ℕ) (χ : Fin n → Fin (n * N'))
    (hpin : ∀ b : Fin n, ((χ b : ℕ)) < n)
    (hN : 1 ≤ N) (x x' : Box p (n * N'))
    (hagree : ∀ c : Fin (n * N'), (c : ℕ) < n * N → x c = x' c) :
    UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)
      = UniqueFactorizationMonoid.normalizedFactors (redPoly χ x') := by
  sorry

end LeanUrat.MovesT
