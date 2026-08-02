/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDDefsV2

/-!
# B2D/TD4_junctionPin — `JunctionPinLaw` at the ledger instance
  [B2DEF_LEAN unit TD-4; wave 2b]

Blueprint §5 TD-4. moves_ref: §B2-DEF D.8 (VERTEX)
`dig′(B_μ) = z̄^{−μm̂}·((R(f)/ψ^μ) mod ψ) ≠ 0`, D.6 (dig′ ∈ F′ˣ), D.10.
deps: TD-0. difficulty: medium.

ENCODING [R1-G2 fold]: the field digit passes through the `Fin (q^D.d)` ℕ-coding
to `c := L.pin ρ` (`hpin_ne`/`hpin_lt`), reachable ONLY at q = q₀ — E2's SUPPORT
CONSTRAINT gives `rhoCount q = 0` for all other q, so the `∃ c` clause is vacuous
off support, q ∈ {0, 1} included [R2-C1 fold — what makes the all-q law
well-founded]. The off-c `fiberDigits = 0` leg rides the `junction` +
`semantics` clauses (empty cylinder ⟹ card 0); T11's forced-value/off-alphabet
dichotomy is discharged inside TD-0's clauses.

Route ADJUDICATED (§6 fence (v)): rides S16/`L5_landVertexDigit` +
`K1_vertexPin` through TD-0 — **never V9**; this file MUST NOT import V9.
E-phase file: statement only.

STATEMENT ROUND 2 (v2, 2026-08-02): the lawfulness hypothesis is now
`LedgerLawfulV2` (TDDefsV2's finite-box semantics). Under v1 this law was
VACUOUSLY satisfiable (`cylFiberDigits ≡ 0` forced — the TD-0/TD-3
refutation's adjacent consequence); at v2 the off-c `fiberDigits = 0` leg is
substantive (empty finite cylinder via the `junction` clause), and the
off-alphabet leg (`z k ≥ q₀`) is built into the `Fin q₀` box carrier. -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LedgerStratumData

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-- **TD-4**: the (J) clause at the ledger instance — the junction read is a
ρ-determined nonzero constant (nonvanishing + ρ-fixedness ONLY: the junction
VALUE identification is fenced out, TransDeep fence (ii)). -/
theorem ledger_junctionPin (L : LedgerStratumData D W P) (hL : L.LedgerLawfulV2)
    (hscope : LedgerScope W P) (hclean : LedgerClean D W P L.N) :
    JunctionPinLaw W P L.ledgerJoint := by
  sorry -- B2DEF_LEAN E-phase sorry [unit TD-4, statement round 2 (v2)]

end LeanUrat.B2D
