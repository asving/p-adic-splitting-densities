/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDDefsV2

/-!
# B2D/TD5_leakCarrier — the TYPED (L) carrier  [B2DEF_LEAN unit TD-5; wave 2b]

Blueprint §5 TD-5. moves_ref: §B2-DEF D.3(e)(ii.3)/(ii.4) (the TransDeep
docstring's key: "parent equations pin blocks DISJOINT from interior window
blocks; each pinned leaf's value is forced given predecessors"). deps: TD-0.
difficulty: medium. REUSE: T9, T12 (through TD-0's lawfulness clauses).

PRIORITY HONESTY [R1-G4 fold]: neither compiled consumer INSPECTS `leakFree`
today (`fresh_of_transDeep` ignores it); this unit is CHARTER-DEMANDED
([R2-G1]: a required deliverable, not optional) — its real consumer is the
gated H2-U10 classifier face, which CONSUMES, never builds, this carrier when
un-gated. TD-6 plugs it into `TransDeep.leakFree` (NOT the `True` fallback).
E-phase file: the typed carrier DEF (no sorry) + the supplier statement (sorry).

STATEMENT ROUND 2 (v2, 2026-08-02): the supplier's lawfulness hypothesis is
now `LedgerLawfulV2` (TDDefsV2's finite-box semantics). The carrier DEF
itself is UNCHANGED — it reads only the (ii.3)/(ii.4) geometry clauses,
which the v1→v2 diff never touched.

PROVED (TD mop-up wave, 2026-08-08 wallclock 2026-08-02) — AT THE v2
STATEMENT, byte-unchanged. **v3-seam audit (the a1e14ef re-key protocol,
applied before proving)**: the TD-3 round-2 seams do NOT implicate this
supplier — the carrier is EXACTLY the pair (`parent_interior_disjoint`,
`pinned_forced`), two clauses the v1→v2→v3 diffs never touched, so the proof
is the projection of the pack onto them. Note the carrier's first conjunct is
the INTERIOR (ii.3) form by design (§5's verbatim referent) — v3's stronger
`parent_box_disjoint` implies it but is NOT needed; re-keying to v3 would
weaken the theorem for no content. Deliberately NOT re-keyed (the TD-1
precedent); v3-lawful instances consume it through `extends`. -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC
open LedgerStratumData

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-- **The TYPED (L) carrier** — §5's verbatim referent ("at every interior
on-line slot k ≠ k_s, the parent's realized conditions impose NO constraint on
the height-β_k digit of a_k beyond (F)'s floor"), typed as (ii.3) + (ii.4):
parent-pinned blocks are DISJOINT from every interior on-line slot's height-β_k
block, and each pinned leaf's value is forced given ≺-predecessors. -/
def LeakFreeCarrier (L : LedgerStratumData D W P) : Prop :=
  (∀ k : ↥W.onLine, (k : Fin (W.ℓ + 1)) ≠ W.ks →
    Disjoint L.parentBlock (L.slotBlock (k : Fin (W.ℓ + 1)))) ∧
  (∀ ρ, ρ < L.rho0 → ∀ c ∈ L.parentBlock,
    ∀ x y : Coord → ℕ, L.inStratum ρ x → L.inStratum ρ y →
    (∀ c' : Coord, CoordPrec c' c → x c' = y c') → x c = y c)

/-- **TD-5 supplier**: the typed (L) carrier holds at every lawful ledger datum
(the (ii.3)/(ii.4) clauses land at TD-0 via T9/T12). PROVED at the v2
statement: the carrier IS the (`parent_interior_disjoint`, `pinned_forced`)
pair of the pack, verbatim (v3-seam audit in the module docstring). -/
theorem ledger_leakFree (L : LedgerStratumData D W P) (hL : L.LedgerLawfulV2) :
    LeakFreeCarrier L :=
  ⟨hL.parent_interior_disjoint, hL.pinned_forced⟩

end LeanUrat.B2D

#print axioms LeanUrat.B2D.ledger_leakFree
