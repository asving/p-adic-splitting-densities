/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Nat.Choose.Basic

/-!
# Uniformity.ChapH.H13 — `clusterC`, the α-bracket exponent coefficient offset

**Chapter H, NODE H.13** (`blueprint/CHAP-H_general_induction.md` §4, **HOISTED** above §3's H.09,
whose `hbracket` field mentions `clusterC`; see leanspec FINDING O1). The corpus's
`c(m) := m(m−1)/2`, landed as `Nat.choose m 2`.

Definitional, no proof obligation. DEPENDS: none.

**Why `Nat.choose` and not `m * (m - 1) / 2`** (blueprint ⚠): `ℕ`-division floors, and while
`m * (m - 1)` is always even — so the two agree — that agreement is only *provable* via
`Nat.choose_two_right`. Defining `clusterC` by `choose` makes H.14's `2 * clusterC m = m * (m − 1)`
a mathlib rewrite rather than a parity argument, and puts `Finset.sum_range_id`-style identities
in reach for H.15.

SOURCE: `EFF.GENIND.07` (*"Write `c(m) := m(m−1)/2`"*).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- `c(m) = m(m−1)/2`, the α-bracket's exponent coefficient offset (`GENIND` §S1). Defined as
`m.choose 2` so that `2 * clusterC m = m * (m − 1)` is exact in `ℕ` with no floor. -/
def clusterC (m : ℕ) : ℕ := m.choose 2

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.clusterC

end AxCheck
