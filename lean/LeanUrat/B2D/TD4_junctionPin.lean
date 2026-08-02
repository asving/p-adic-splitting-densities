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
off-alphabet leg (`z k ≥ q₀`) is built into the `Fin q₀` box carrier.

PROVED (TD mop-up wave, 2026-08-08 wallclock 2026-08-02) — AT THE v2
STATEMENT, byte-unchanged. **v3-seam audit (the a1e14ef re-key protocol,
applied before proving)**: the TD-3 round-2 seams do NOT implicate this law —
the pin argument reads `semantics` + `junction` + the datum's `hpin_ne`/
`hpin_lt` ONLY (no member existence: the ∃ c clause asserts a VANISHING, not
a nonempty c-fiber — "the c-fiber is NOT asserted nonempty" is
`JunctionPinLaw`'s own docstring; no parent/box-slot factorization anywhere),
and both round-2 countermodels `cmL3`/`cmL4` SATISFY the v2 statement.
Deliberately NOT re-keyed to v3 (the TD-1 precedent: weaker hypothesis =
stronger theorem, non-vacuous by `td_lawfulV2`); v3-lawful instances consume
it through `extends`.

Proof: at q = q₀ take c := `L.pin ρ` (`hpin_ne`/`hpin_lt` give c ≠ 0,
c < q₀^d); any member of an off-c prescribed-digit cylinder would read the
pin at the junction (`junction` clause) AND the prescribed z ≠ c through
`slotCoord` — unsatisfiable, so the finite-box count is 0
(`blockCount_of_not`). Off q₀ the law is vacuous by the [R2-C1] support
constraint (`ledger_rhoCount_off_support`) — exactly the R2-C1 fold above,
q ∈ {0, 1} included. The `monicTop = false` guard is never drawn on at q₀
(the junction clause holds unconditionally at the lawful datum). -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LedgerStratumData

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

set_option linter.unusedVariables false in
/-- **TD-4**: the (J) clause at the ledger instance — the junction read is a
ρ-determined nonzero constant (nonvanishing + ρ-fixedness ONLY: the junction
VALUE identification is fenced out, TransDeep fence (ii)). PROVED at the v2
statement (v3-seam audit in the module docstring: not implicated).
`hscope`/`hclean` are the standing CEN-J/LED(i) guards of the TD statement
family — the pin argument never draws on them. -/
theorem ledger_junctionPin (L : LedgerStratumData D W P) (hL : L.LedgerLawfulV2)
    (hscope : LedgerScope W P) (hclean : LedgerClean D W P L.N) :
    JunctionPinLaw W P L.ledgerJoint := by
  intro hmt q ρ hρ
  by_cases hq : q = L.q0
  · subst hq
    have hρ0 : ρ < L.rho0 := by
      simpa [LedgerStratumData.ledgerJoint] using hρ
    refine ⟨L.pin ρ, L.hpin_ne ρ hρ0, L.hpin_lt ρ hρ0, fun hk z hz => ?_⟩
    simp only [LedgerStratumData.ledgerJoint, if_true]
    rw [(hL.semantics ρ hρ0).2 z]
    refine blockCount_of_not _ _ _ fun x hx => ?_
    exact hz ((hx.2 ⟨W.ks, hk⟩).symm.trans (hL.junction ρ hρ0 x hx.1 hk))
  · rw [ledger_rhoCount_off_support L q hq] at hρ
    omega

end LeanUrat.B2D

#print axioms LeanUrat.B2D.ledger_junctionPin
