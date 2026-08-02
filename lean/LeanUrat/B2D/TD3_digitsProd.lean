/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDDefsV2

/-!
# B2D/TD3_digitsProd — `DigitsProdLaw` at the ledger instance
  [B2DEF_LEAN unit TD-3; wave 1 — THE HARDEST HOLE, front 1]

Blueprint §5 TD-3 (+ the §5 hardest-hole call, [R2-G2 fold]). moves_ref: §B2-DEF
D.3(e)(ii.3)/(ii.4), D.8 (BOX), D.11 attainable product. deps: TD-0.
difficulty: **hardest**.

Proof skeleton (blueprint verbatim, transposed to the TD-0 clauses): (ii.3) =
`slots_disjoint`/`parent_interior_disjoint` (distinct pins hit disjoint leaf
sets; T9's display) + (ii.4) = `pinned_forced` (unit-diagonal: each pinned leaf
forced given predecessors — T12's display) ⟹ the level-N box splits as a product
over slot blocks (`member_split` + the support clauses; the parent factor is 1 by
`pinned_forced`) ⟹ card = ∏ (`semantics` + `slot_sem`/`slotDigits_sem`
`blockCount`s). The shallow-height regime rides the ATTAINABLE product (T11
dichotomy, discharged inside TD-0's `slotDigits_sem` counts) — NEVER full
alphabets (D¹¹c: the uniform field-alphabet display is FALSE at shallow heights).
Falsifier N-TD1 (shallow-height harness) gates this statement BEFORE proof
effort. E-phase file: statement only.

**STATEMENT ROUND 2 (v2, 2026-08-02) — this file's history in two rounds.**
Round 1 (v1, commit 5371139): the N-TD1 gate FAILED at the Lean statement
level (`verification/openmath/ntd1_td3_ledger_semantics_trace.py`: intended
MOVES D.11 finite-box counts match the product 3/3, the v1 statement fails
3/3) and `TD3_countermodel.lean` compiled the refutation:
`ledger_digitsProd_refuted` is the ¬∀ of the v1 closure (preserved verbatim
there as the record), and `not_digitsProd_of_lawful` shows EVERY v1-lawful
instance with `1 ≤ rho0` violates the law — the defect was E2's v1
`LedgerSemantics` (`Nat.card` over all of `Coord → ℕ` is empty-or-infinite
⟹ ≡ 0, against the positive `slot_count_val` product).
Round 2 (THIS statement): the hypothesis is `LedgerLawfulV2` — TDDefsV2's
finite-box semantics (counts over `supportUnion` with `Fin q₀` values, the
MOVES D.11 `#{f mod p^N}` reading the trace matched). The countermodel
mechanism provably does NOT apply to this round: `TD3v2_control.lean`
compiles the positive control (`cm2_digitsProd` — the law HOLDS, proved, at
the v2 control instance whose shape refuted v1) and
`v2_mechanism_inapplicable` (the ¬∀ of the mechanism's v2 transposition).
The N-TD1 trace's [LHS-V2] column is 3/3 MATCH against this statement's
semantics (incl. the on-line digit instances i2/i3). The sorry below is
therefore an honest OPEN goal again, not a refuted one.

**ROUND 2 REFUTED (2026-08-02, wave-2 prover run).** The v2 statement below
is ALSO false as stated: `TD3v2_countermodel.lean` compiles
`ledger_digitsProd_v2_refuted` — the ¬∀ of this exact statement — via two
v2-LAWFUL witnesses on the control geometry: `cmL3` (Seam B: `parentBlock`
overlapping an OFF-LINE box slot's block, which `parent_interior_disjoint`
does not fence — NONEMPTY stratum, `pinned_forced` substantive, joint count
1 vs product 2) and `cmL4` (Seam A: unsatisfiable parent condition — no
clause asserts per-realization member existence — count 0 vs positive
product). The pack supplies D.11's injectivity half (`pinned_forced`) but
not the surjectivity half (member existence) nor full parent/box-slot
disjointness; the N-TD1 instances never probed either seam (`parentBlock =
[]` throughout). Positive controls on that subfamily STAND: `cm2_digitsProd`
and TD-0's `td_digitsProd` (r = 1, genuine on-line digit content, landed
2026-08-02). The sorry below STANDS refuted-open pending an E2 v3 statement
round (the two missing clauses named in the countermodel docstring);
statement fence respected — nothing here is weakened or restated.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LedgerStratumData

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-- **TD-3**: the (F) product-box face at the ledger instance — fiberwise
per-slot factorization of the prescribed-digit counts (on-line digit counts ×
off-line height counts). -/
theorem ledger_digitsProd (L : LedgerStratumData D W P) (hL : L.LedgerLawfulV2)
    (hscope : LedgerScope W P) (hclean : LedgerClean D W P L.N) :
    DigitsProdLaw W P L.ledgerJoint := by
  sorry -- B2DEF_LEAN E-phase sorry [unit TD-3, statement round 2 (v2)]

end LeanUrat.B2D
