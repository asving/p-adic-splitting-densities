/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Nat.GCD.Basic

/-!
# Uniformity.ChapH.H01 — `GenreDatum`, the local genre datum

**Chapter H, NODE H.01** (`blueprint/CHAP-H_general_induction.md` §3). A *genre datum*
`G = (Q; e₁, f₁, μ; h)` packages the local invariants of a composite-stage opening: this is
`THEOREM GENHN.CLASS`(i)'s datum **minus the entry pattern**, which is a separate parameter of
every consuming statement rather than a field (blueprint SIGNATURE NOTE: the entry pattern indexes
the *fiber*, not the stage system, and making it a field would both import a chapter-C object into
a chapter-H structure and destroy `DecidableEq`).

The five side conditions are the corpus's, verbatim: `gcd(h, e₁) = 1`, `e₁ ≥ 1`, `f₁ = deg ψ`,
`μ ≥ 2`, `e₁ f₁ ≥ 2` ("else the event is order-1 α/β"), plus the residue-cardinality floor
`2 ≤ Q`.

Definitional, no proof obligation. DEPENDS: none.

SOURCE: `EFF.GENHN.07` (clause (i)); `EFF.GENIND.62` (the stage datum `(m′, D′, E, K)`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- A **genre datum** `G = (Q; e₁, f₁, μ; h)`: the local invariants of a composite-stage opening
(`GENHN.CLASS`(i)). The residual factor `ψ` has degree `f₁` and multiplicity `μ`; the side carrying
it has slope `h / e₁` in lowest terms. -/
structure GenreDatum where
  /-- The ambient cluster's residue cardinality `Q = q ^ d`. -/
  Q : ℕ
  /-- The slope denominator; the stage's value-group index `E = e₁`. -/
  e₁ : ℕ
  /-- The residual factor's degree; the stage residue field is `F_(Q ^ f₁)`. -/
  f₁ : ℕ
  /-- The residual factor's multiplicity, `= the stage multiplicity`. -/
  μ : ℕ
  /-- The slope numerator. -/
  h : ℕ
  hQ : 2 ≤ Q
  he₁ : 1 ≤ e₁
  hh : 1 ≤ h
  hkey : 2 ≤ e₁ * f₁
  hmul : 2 ≤ μ
  hcop : Nat.Coprime h e₁

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.GenreDatum
#print axioms Uniformity.Density.Induction.GenreDatum.mk

end AxCheck
