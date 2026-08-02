/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.GRDefs

/-!
# B2D/GR3_keyResidual — the summed key residual  [B2DEF_LEAN unit GR-3; wave 2a]

Blueprint §5 GR-3. moves_ref: §B2-DEF D.5 RESIDUAL sum + D.1(b) no-cancellation
(MOVES :2270–2277), D.8 m̂ = −t·h·g. deps: GR-1, GR-2. difficulty: medium-hard.
REUSE: `L1_initialForm_add_lt` (Laurent face), `Node.mhat` (the existing m̂ —
cite, don't rebuild).

E-phase file: statements only, sorry bodies = the open-goals ledger.

STATEMENT FLAG (N-GR1 gate): the PINNED form (`m̂ = ν.mhat = −t·h·g`, filling
`GrBKeyLaws.key_res` with c = 1) is the blueprint's displayed prediction, gated
by the N-GR1 falsifier family (exponent bookkeeping = the recurring defect
class); the ∃-form is §4's frozen `graded_read` clause and is what GR-4
consumes — a pinned-form refutation re-adjudicates ONLY the pinned display. -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open Polynomial LeanUrat.Moves LeanUrat.MovesC

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **GR-3, pinned form**: distinct slot positions (GR-2's strictly monotone
`readPos`) mean no cancellation (D.1(b)), and the slot sum recomposes to
`σ.R Φ′ = T^{m̂}·toLaurent ψ` at the D.8 normalization `m̂ = Node.mhat = −t·h·g`.
N-GR1-gated display (module docstring). -/
theorem GR3_keyResidual_pinned (ν : Node p F) (Φ' : Polynomial ℤ_[p])
    (hlift : IsNodeLift ν Φ') (R : ReadHyps ν) :
    ν.σ.R Φ' = LaurentPolynomial.T ν.mhat * Polynomial.toLaurent ν.ψ := by
  sorry -- B2DEF_LEAN E-phase sorry [unit GR-3]

/-- **GR-3, the ∃-form** (§4's frozen `graded_read` clause 2; fills
`GrBKeyLaws.key_res` with `c = 1`). -/
theorem GR3_keyResidual (ν : Node p F) (Φ' : Polynomial ℤ_[p])
    (hlift : IsNodeLift ν Φ') (R : ReadHyps ν) :
    ∃ mh : ℤ, ν.σ.R Φ' = LaurentPolynomial.T mh * Polynomial.toLaurent ν.ψ := by
  sorry -- B2DEF_LEAN E-phase sorry [unit GR-3]

end LeanUrat.B2D
