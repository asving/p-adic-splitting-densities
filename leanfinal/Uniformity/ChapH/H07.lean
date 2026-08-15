/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H01

/-!
# Uniformity.ChapH.H07 — occupied `dv`-heights

**Chapter H, NODE H.07** (`blueprint/CHAP-H_general_induction.md` §3). A `dv`-height `m` is
*occupied* for a genre datum `G` (H.01) when the normalizer monomial `n(m) = x^{i} π^{a}` exists
**with `a` a natural number**: there are `i < e₁` and `a : ℕ` with `i·h + e₁·a = m`. Integrality of
the exponent `a = (m − i h)/e₁` is the whole content — `EFF.GENHN.28`'s normalizer *"presumes
`a(m) ≥ 0`, which fails at unoccupied heights"*, and this predicate is the TERMINAL scope word of
`GENHN.A`(ii) after the post-D2b corrigendum.

Definitional, no proof obligation. DEPENDS: H.01. Guarded downstream by H.10–H.12 (in particular
the A2/R4 unoccupied-height witness).

SOURCE: `EFF.GENHN.28` (the normalizer `n(m) := x^{i(m)}π^{a(m)}`, `i(m)·h + e₁·a(m) = m`,
`0 ≤ i(m) < e₁`); `EFF.GENHN.09` (the owner re-display: *"per OCCUPIED integer dv-height — a height
`m` admitting an integral normalizer monomial … with `0 ≤ i(m) < e₁` and
`a(m) = (m − i(m)h)/e₁ ≥ 0`"*).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- `G.Occupied m`: the `dv`-height `m` admits an INTEGRAL normalizer monomial
`n(m) = x^{i} π^{a}` with `0 ≤ i < e₁` and `a ≥ 0`.  This is the TERMINAL scope word of
`GENHN.A`(ii) after the post-D2b corrigendum. -/
def GenreDatum.Occupied (G : GenreDatum) (m : ℕ) : Prop :=
  ∃ i a : ℕ, i < G.e₁ ∧ i * G.h + G.e₁ * a = m

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.GenreDatum.Occupied

end AxCheck
