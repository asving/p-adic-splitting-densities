/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TD3_countermodel

/-!
# B2D/TDDefsV2 — the FINITE-BOX (v2) ledger semantics
  [B2DEF_LEAN unit E2, STATEMENT ROUND 2; supersedes TDDefs' `LedgerSemantics`
   / `LedgerLawful` / `LedgerStrata` per the TD-0/TD-3 refutation]

Blueprint: `lean/blueprints/B2DEF_LEAN_2026-08-08.md` §3 + §5 (unit E2, v2
round). moves_ref: §B2-DEF D.3(e)(ii), D.8, D.11 (`#{f mod p^N}` — the FINITE
level-N box count). Statement authority: standing statement-change rule (an
honest restatement of a REFUTED transcription, refutation compiled on file).

## Provenance: why a round 2 (the countermodel record)

The wave-1 hard-hole run (commit 5371139) REFUTED the v1 statements:
`TD3_countermodel.not_digitsProd_of_lawful` proves EVERY v1-lawful instance
with `1 ≤ rho0` violates `DigitsProdLaw`, because v1's `LedgerSemantics` set
`cylFiber`/`cylFiberDigits` := `Nat.card {x : Coord → ℕ // …}` over the
INFINITE chart `Coord = ℕ × ℕ` with UNBOUNDED digit values — box-supported
membership (`member_split` + the support clauses) makes every stratum set
empty-or-infinite, so the left side is FORCED to 0 against the positive
`slot_count_val` product (`card_zero_of_finite_support`, the seam isolated).
The N-TD1 gate (`verification/openmath/ntd1_td3_ledger_semantics_trace.py`)
pinned the defect to the TRANSCRIPTION: the intended MOVES D.11 finite-box
counts match the per-slot product EXACTLY (3/3), the v1 Lean reading fails
3/3. This file imports the countermodel DELIBERATELY: v2 is the repair of the
seam it compiled, and reuses its general counting lemmas.

## The v1 → v2 diff (everything else verbatim)

ONE change: the two fiber-count semantics clauses. v2 counts members as
BOX-RESTRICTED digit assignments on the FINITE support union
`supportUnion L = parentBlock ∪ boxSlots.biUnion slotBlock` with values in
`Fin q0` — i.e. through the SAME `blockCount` pattern
`Nat.card {v : ↥box → Fin q0 // cond (extension-by-zero)}` that the per-slot
clauses (`slot_sem`/`slotDigits_sem`) and the product side already use. This
is MOVES D.11's `#{f mod p^N}` reading restricted to the constrained
coordinates (the trace's `members_on_window(U, q0)` count, which IS the spec:
it matched the product 3/3). The union runs over `W.boxSlots` (NOT all of
`Fin (ℓ+1)`): `member_split` quantifies box slots only, so the erased
monic-top slot's block must contribute no free factor. `Nat.card` now
COMPUTES: the carrier `↥U → Fin q0` is a Fintype, so the countermodel's
empty-or-infinite dichotomy has no purchase (compiled check:
`TD3v2_control.lean` — the positive control `cmL2` with `Nat.card` computed
= the product, and `v2_mechanism_inapplicable`, the ¬∀ of the v1 refutation
mechanism's exact v2 transposition).

All OTHER `LedgerLawful` clauses (member_split, the two supports,
disjointness, slot_coord_mem, parent_interior_disjoint, pinned_forced,
junction, digit_range, slot_sem, slotDigits_sem, slot_count_val) are
VERBATIM from TDDefs v1 — they were never implicated (the countermodel's
Part 1 derives the defect from `semantics` alone, the other clauses standing).

## E-phase discipline

The v1 layer + the countermodel STAY ON FILE as the refutation record
(TDDefs docstrings marked superseded; no v1 theorem touched). The TD-1..TD-6
fan-out is restated on THIS carrier (same names, `LedgerLawfulV2`/
`LedgerStrataV2` hypotheses, E-phase sorries with unit tags). TD-0's duties
(a)-(c) now target `LedgerLawfulV2`; duty (c) (positive fiber counts) is
POSSIBLE at v2 (`TD3v2_control.v2_devacuify_possible`) where it was PROVABLY
IMPOSSIBLE at v1 (`lawful_fiber_devacuify_impossible`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC

variable {D : CensusData}

namespace LedgerStratumData

variable {W : WindowDatum D} {P : ParentShape D W}

/-- **The finite coordinate support of the level-N ledger stratum** (v2's
counting box): the parent-pinned block together with the BOX slots' blocks —
`member_split`'s own read perimeter. Deliberately over `W.boxSlots`, not all
of `Fin (ℓ+1)`: the erased monic-top slot is outside `member_split`'s
quantifier, so its block must not contribute free (uncounted-condition)
coordinates. Distinct from the countermodel's `blockUnion` (which unions ALL
slots — any finite SUPERSET works for the v1 zero-forcing argument; the v2
COUNT needs the exact perimeter). -/
def supportUnion (L : LedgerStratumData D W P) : Finset Coord :=
  L.parentBlock ∪ W.boxSlots.biUnion L.slotBlock

/-- `blockCount` respects pointwise-iff conditions. -/
theorem blockCount_congr (q : ℕ) (B : Finset Coord)
    {cond cond' : (Coord → ℕ) → Prop} (h : ∀ x, cond x ↔ cond' x) :
    blockCount q B cond = blockCount q B cond' :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => h _)

/-- `blockCount` of an unsatisfiable condition vanishes. -/
theorem blockCount_of_not (q : ℕ) (B : Finset Coord)
    (cond : (Coord → ℕ) → Prop) (h : ∀ x, ¬ cond x) :
    blockCount q B cond = 0 := by
  simp only [LedgerStratumData.blockCount]
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun v => h _ v.2⟩

/-- **Layer 2, v2: the q₀ FINITE-BOX cylinder-count semantics** [R1-G1, round
2] — the datum's fiber counting fields ARE the `blockCount`s of its member
condition over the finite support union: digit assignments
`v : ↥(supportUnion L) → Fin q₀`, extended by zero off the box, satisfying
`inStratum` (resp. `inStratum` + the prescribed on-line reads through
`slotCoord`). This is the MOVES D.11 `#{f mod p^N}` count at the constrained
coordinates — the reading whose shallow-instance values matched the per-slot
product 3/3 at the N-TD1 gate. Off-alphabet digit vectors (`z k ≥ q₀`) get
count 0 automatically (box values are `< q₀` and reads land in the box for
lawful data via `slot_coord_mem`) — T11's off-alphabet dichotomy, now built
into the carrier. Stated for ALL z (`JunctionPinLaw` consumes off-alphabet z
too). TD-0 duty (b) discharges this at the designated instance. -/
def LedgerSemanticsV2 (L : LedgerStratumData D W P) : Prop :=
  ∀ ρ, ρ < L.rho0 →
    (L.cylFiber ρ = blockCount L.q0 L.supportUnion (L.inStratum ρ)) ∧
    (∀ z : ↥W.onLine → ℕ,
      L.cylFiberDigits ρ z
        = blockCount L.q0 L.supportUnion
            (fun x => L.inStratum ρ x ∧
              ∀ k : ↥W.onLine, x (L.slotCoord k) = z k))

/-- **The lawfulness pack, v2** [R1-G3 fold; statement round 2] — what unit
TD-0 PROVES at the designated instance and what units TD-1..TD-5 consume.
IDENTICAL to v1's `LedgerLawful` except the ONE refuted clause: `semantics`
is now the finite-box `LedgerSemanticsV2` (the v1→v2 diff in the module
docstring). Every other clause is byte-for-byte v1's; clause names carry
their §B2-DEF displays as before. -/
structure LedgerLawfulV2 (L : LedgerStratumData D W P) : Prop where
  /-- layer-2 semantics, v2: counting fields = FINITE-BOX cylinder cards -/
  semantics : LedgerSemanticsV2 L
  /-- D.3(e)(ii): the stratum is a digit CYLINDER — parent equations ∧ per-slot
      conditions over the box slots -/
  member_split : ∀ ρ x, L.inStratum ρ x ↔
    (L.parentCond ρ x ∧ ∀ k ∈ W.boxSlots, L.slotCond ρ k x)
  /-- the parent condition reads only the parent block -/
  parent_support : ∀ ρ x y, (∀ c ∈ L.parentBlock, x c = y c) →
    (L.parentCond ρ x ↔ L.parentCond ρ y)
  /-- slot k's condition reads only slot k's block -/
  slot_support : ∀ ρ k x y, (∀ c ∈ L.slotBlock k, x c = y c) →
    (L.slotCond ρ k x ↔ L.slotCond ρ k y)
  /-- slot blocks are pairwise disjoint (the product-box geometry) -/
  slots_disjoint : ∀ k k' : Fin (W.ℓ + 1), k ≠ k' →
    Disjoint (L.slotBlock k) (L.slotBlock k')
  /-- the on-line read leaf sits in its own slot's block -/
  slot_coord_mem : ∀ k : ↥W.onLine, L.slotCoord k ∈ L.slotBlock (k : Fin (W.ℓ + 1))
  /-- (ii.3): parent-pinned blocks are DISJOINT from every interior on-line
      slot's block (the typed (L) input; T9's display) -/
  parent_interior_disjoint : ∀ k : ↥W.onLine, (k : Fin (W.ℓ + 1)) ≠ W.ks →
    Disjoint L.parentBlock (L.slotBlock (k : Fin (W.ℓ + 1)))
  /-- (ii.4): each parent-pinned leaf's value is FORCED given ≺-predecessors,
      whatever the predecessors (T12's unit-diagonal display) -/
  pinned_forced : ∀ ρ, ρ < L.rho0 → ∀ c ∈ L.parentBlock,
    ∀ x y : Coord → ℕ, L.inStratum ρ x → L.inStratum ρ y →
    (∀ c' : Coord, CoordPrec c' c → x c' = y c') → x c = y c
  /-- D.8 (VERTEX) + D.6 + D.10: every member's junction read IS the ρ-determined
      pin code (nonzero by `hpin_ne`) -/
  junction : ∀ ρ, ρ < L.rho0 → ∀ x, L.inStratum ρ x →
    ∀ hk : W.ks ∈ W.onLine, x (L.slotCoord ⟨W.ks, hk⟩) = L.pin ρ
  /-- range: members' on-line digit reads are in the Fin (q₀^d) code range -/
  digit_range : ∀ ρ, ρ < L.rho0 → ∀ x, L.inStratum ρ x →
    ∀ k : ↥W.onLine, x (L.slotCoord k) < L.q0 ^ D.d
  /-- per-slot count semantics: the height count IS slot k's block count -/
  slot_sem : ∀ ρ, ρ < L.rho0 → ∀ k ∈ W.boxSlots,
    L.cylSlot ρ k = blockCount L.q0 (L.slotBlock k) (L.slotCond ρ k)
  /-- per-slot per-digit count semantics through the `slotCoord` read -/
  slotDigits_sem : ∀ ρ, ρ < L.rho0 → ∀ (k : ↥W.onLine) (z : ℕ),
    L.cylSlotDigits ρ k z
      = blockCount L.q0 (L.slotBlock (k : Fin (W.ℓ + 1)))
          (fun x => L.slotCond ρ (k : Fin (W.ℓ + 1)) x ∧ x (L.slotCoord k) = z)
  /-- D.8 (BOX) + D.11 through the proved A1/TRI ledger: the per-slot height
      count VALUE at the joint floor (design flag 2: the LED/CL5 substance is
      discharged HERE by TD-0; TD-1 derives the H2 law from it) -/
  slot_count_val : ∀ ρ, ρ < L.rho0 → ∀ k ∈ W.boxSlots,
    L.cylSlot ρ k
      = L.q0 ^ ((D.period * D.d) * L.N - D.s (max (W.beta k) (P.g k)))

end LedgerStratumData

/-- **The designated strata family, v2** (blueprint §3 "fill the row", round
2): the v2-lawful ledger instances' q-generic carriers. TD-0 de-vacuifies it
(duty (c), now POSSIBLE — see `TD3v2_control.v2_devacuify_possible`). -/
def LedgerStrataV2 (D : CensusData) (W : WindowDatum D) (P : ParentShape D W) :
    Set (JointStratum D W P) :=
  {J | ∃ L : LedgerStratumData D W P,
    L.LedgerLawfulV2 ∧ J = L.ledgerJoint}

end LeanUrat.B2D

#print axioms LeanUrat.B2D.LedgerStratumData.blockCount_congr
#print axioms LeanUrat.B2D.LedgerStratumData.blockCount_of_not
