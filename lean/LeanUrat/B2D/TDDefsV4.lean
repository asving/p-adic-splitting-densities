/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDDefsV3

/-!
# B2D/TDDefsV4 — the d-LEAF-READ (huni-v2) ledger carrier
  [B2DEF_LEAN unit E2, STATEMENT ROUND 4; the huni REPAIR round.
   Supersedes `LedgerLawfulV3` / `LedgerStrataV3` as the consumable pack for
   the (FRESH) digit-law chain, per the compiled HUNI refutation]

Statement authority: Asvin's standing statement-change rule (2026-08-05) — an
honest re-key pinned by a compiled countermodel (`HuniProbe.lean`, commit
375487c; countermodel-first protocol, note
`lean/notes/openmath/HUNI_PROBE_2026-08-08.md`).

## Provenance: why a round 4 (the huni refutation record)

The HUNI probe DECIDED `SlotUniformLaw` (the `huni` face — the ONE displayed
open input of the TD supply chain) at the compiled instances and found an
ALPHABET SEAM in the v2/v3 ledger READ, not in the H2 law:

* `slotUniform_td2_false` — at the v3-LAWFUL non-degenerate extension `td2`
  (d = 2, a non-junction on-line slot), `SlotUniformLaw` is FALSE: the law
  quantifies digit codes `z < q^D.d`, but the v1–v3 carrier reads ONE leaf
  (`slotCoord`) of a `Fin q₀` box vector, so `slotDigits ρ k z q₀ = 0` is
  FORCED at every z ∈ [q₀, q₀^d) while some in-alphabet digit counts
  positively. Generic at every d ≥ 2 census with a non-junction on-line slot.
* `freshReads_td2_false` — the CONSUMER's conclusion (`FreshReadsLaw`, what
  `fresh_of_transDeep` outputs) fails at `td2` too, so no re-guard of `huni`
  alone can repair the chain: the READ must move.
* `ledger_huni_face_false_at_tdD` — `ledger_freshRowOn`'s `huni` binder is
  UNSATISFIABLE over the v3 family at the census `tdD`.

## The v3 → v4 diff (the re-key, and nothing else)

The probe's adjudicated minimal honest repair: re-key the ledger read to the
full d-leaf digit CODE — the [R1-G2] field-element-to-code bijection that
TD-0 only ever exercised at the pin value 1 < q₀. Concretely, on the finite
`Fin q₀` box carrier an F_{q^d} digit is d leaves, and its ℕ-code is the
base-q₀ evaluation of the leaf tuple:

* **Datum**: `LedgerStratumDataV4` = the v1–v3 datum (every field verbatim,
  via `extends`) + ONE field `slotCoords : ↥W.onLine → ℕ → Coord`, the d read
  leaves of each on-line slot (ℕ-indexed; only `t < D.d` is ever read). The
  inherited single `slotCoord` field is RETIRED as a read: no v4 clause
  consumes it (instances keep it as the designated leaf `slotCoords k 0`, the
  leaf the v1–v3 rounds pinned — the `pin = 1 < q₀` exercise).
* **The read**: `slotRead L x k = Σ_{t < D.d} x(slotCoords k t) · q₀^t` —
  the [R1-G2] coding `F_{q^d} ∋ ξ = Σ ξ_t θ^t ↦ Σ code(ξ_t)·q₀^t`, realized
  on the box carrier. On `Fin q₀` leaf values it ranges over the FULL code
  alphabet [0, q₀^d) — the seam is closed at the carrier, so uniformity over
  `z < q^d` is satisfiable (compiled: `HuniV4Probe.slotUniform_td2V4`).
* **Pack**: `LedgerLawfulV4` = the 15 v3 clauses with EXACTLY the five
  read-keyed items re-keyed to `slotRead` and everything else byte-verbatim:
  - `semantics` → `LedgerSemanticsV4` (the fiber clause UNCHANGED; the
    prescribed-digit clause reads `slotRead x k = z k`),
  - `slot_coord_mem` → `slot_coords_mem` (all d leaves sit in the slot block),
  - `junction` (the junction READ CODE is the pin code),
  - `digit_range` (members' READ CODES are in the `Fin (q₀^d)` range),
  - `slotDigits_sem` (per-digit counts keyed by the READ CODE);
  verbatim: `member_split`, `parent_support`, `slot_support`,
  `slots_disjoint`, `parent_interior_disjoint`, `pinned_forced`, `slot_sem`,
  `slot_count_val`, `member_exists`, `parent_box_disjoint`.

`SlotUniformLaw` and `FreshReadsLaw` (H2/FreshLaws.lean) are byte-UNCHANGED:
the probe pinned the defect to the ledger read, and at the re-keyed carrier
both laws are satisfied at the transported countermodel instance
(`HuniV4Probe.lean`) — no H2-law statement moves.

## E-phase discipline

v1–v3 layers + all countermodel files STAY byte-unchanged as refutation
records (the v1→v2→v3 precedent, one round up). `tdL`/`td2` REMAIN v3-lawful
and in `LedgerStrataV3` (nothing above them is touched); the v3 chain
(`transDeep_of_ledger`, `ledger_freshRowOn`) stands as the round-3 record —
its huni binder is dead at d ≥ 2 (`ledger_huni_face_false_at_tdD`), which is
exactly why the LIVE chain is re-keyed here (`TDV4_chain.lean`:
`transDeep_of_ledger_v4`, `ledger_freshRowOnV4`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LeanUrat.MovesC LedgerStratumData

variable {D : CensusData}

/-- **The round-4 ledger-stratum datum**: the v1–v3 datum (verbatim, via
`extends`) plus the d read leaves of each on-line slot — the [R1-G2] carrier
of the field-element-to-code bijection. ℕ-indexed (the corpus's digit-code
convention); only `t < D.d` is read by `slotRead`/the v4 clauses. The
inherited `slotCoord` is retired as a read (kept as the designated leaf 0 by
instance convention; no v4 clause consumes it). -/
structure LedgerStratumDataV4 (D : CensusData) (W : WindowDatum D)
    (P : ParentShape D W) extends LedgerStratumData D W P where
  /-- the d read leaves of on-line slot k (leaf t carries the θ^t-component's
      F_q digit; the height-β_k F_{q^d} digit = the coded d-tuple) -/
  slotCoords : ↥W.onLine → ℕ → Coord

namespace LedgerStratumDataV4

variable {W : WindowDatum D} {P : ParentShape D W}

/-- **The d-leaf digit READ CODE** [R1-G2, round 4]: the base-q₀ evaluation of
slot k's leaf tuple — `Σ_{t < d} x(leaf t) · q₀^t`. On `Fin q₀` box values
this is exactly the field-element-to-code bijection's ℕ-code, ranging over
the FULL `Fin (q₀^d)` alphabet (the v1–v3 single-leaf read capped it at q₀ —
the compiled huni seam). -/
def slotRead (L : LedgerStratumDataV4 D W P) (x : Coord → ℕ) (k : ↥W.onLine) : ℕ :=
  ∑ t ∈ Finset.range D.d, x (L.slotCoords k t) * L.q0 ^ t

/-- The read code is slot-block supported (given the leaf-membership clause):
box vectors agreeing on slot k's block have equal read codes. -/
theorem slotRead_congr (L : LedgerStratumDataV4 D W P) {k : ↥W.onLine}
    (hmem : ∀ t < D.d, L.slotCoords k t ∈ L.slotBlock (k : Fin (W.ℓ + 1)))
    {x y : Coord → ℕ} (hxy : ∀ c ∈ L.slotBlock (k : Fin (W.ℓ + 1)), x c = y c) :
    L.slotRead x k = L.slotRead y k :=
  Finset.sum_congr rfl fun t ht => by
    rw [hxy _ (hmem t (Finset.mem_range.mp ht))]

/-- **Layer 2, v4: the q₀ finite-box semantics at the d-leaf read** — the
fiber clause is v2's VERBATIM; the prescribed-digit clause counts members by
their READ CODES (`slotRead`), closing the alphabet seam: prescribed codes
range over `Fin (q₀^d)` and the carrier can realize all of them. -/
def LedgerSemanticsV4 (L : LedgerStratumDataV4 D W P) : Prop :=
  ∀ ρ, ρ < L.rho0 →
    (L.cylFiber ρ = blockCount L.q0 L.toLedgerStratumData.supportUnion (L.inStratum ρ)) ∧
    (∀ z : ↥W.onLine → ℕ,
      L.cylFiberDigits ρ z
        = blockCount L.q0 L.toLedgerStratumData.supportUnion
            (fun x => L.inStratum ρ x ∧
              ∀ k : ↥W.onLine, L.slotRead x k = z k))

/-- **The lawfulness pack, v4** [statement round 4; the huni repair] — the 15
v3 clauses with EXACTLY the five read-keyed items re-keyed to the d-leaf
`slotRead` code (module docstring diff list); everything else byte-verbatim
from v3. NOT an `extends` of v3: the old single-leaf read clauses are the
refuted transcription and must not co-constrain the counting fields. -/
structure LedgerLawfulV4 (L : LedgerStratumDataV4 D W P) : Prop where
  /-- layer-2 semantics, v4: counting fields = finite-box cylinder cards, the
      prescribed-digit clause keyed by the d-leaf READ CODE -/
  semantics : LedgerSemanticsV4 L
  /-- D.3(e)(ii): the stratum is a digit CYLINDER — parent equations ∧ per-slot
      conditions over the box slots (v3 verbatim) -/
  member_split : ∀ ρ x, L.inStratum ρ x ↔
    (L.parentCond ρ x ∧ ∀ k ∈ W.boxSlots, L.slotCond ρ k x)
  /-- the parent condition reads only the parent block (v3 verbatim) -/
  parent_support : ∀ ρ x y, (∀ c ∈ L.parentBlock, x c = y c) →
    (L.parentCond ρ x ↔ L.parentCond ρ y)
  /-- slot k's condition reads only slot k's block (v3 verbatim) -/
  slot_support : ∀ ρ k x y, (∀ c ∈ L.slotBlock k, x c = y c) →
    (L.slotCond ρ k x ↔ L.slotCond ρ k y)
  /-- slot blocks are pairwise disjoint (v3 verbatim) -/
  slots_disjoint : ∀ k k' : Fin (W.ℓ + 1), k ≠ k' →
    Disjoint (L.slotBlock k) (L.slotBlock k')
  /-- RE-KEYED: ALL d read leaves of an on-line slot sit in its own block
      (was `slot_coord_mem`, the single leaf) -/
  slot_coords_mem : ∀ k : ↥W.onLine, ∀ t < D.d,
    L.slotCoords k t ∈ L.slotBlock (k : Fin (W.ℓ + 1))
  /-- (ii.3) interior form (v3 verbatim) -/
  parent_interior_disjoint : ∀ k : ↥W.onLine, (k : Fin (W.ℓ + 1)) ≠ W.ks →
    Disjoint L.parentBlock (L.slotBlock (k : Fin (W.ℓ + 1)))
  /-- (ii.4) pinned leaves forced given ≺-predecessors (v3 verbatim) -/
  pinned_forced : ∀ ρ, ρ < L.rho0 → ∀ c ∈ L.parentBlock,
    ∀ x y : Coord → ℕ, L.inStratum ρ x → L.inStratum ρ y →
    (∀ c' : Coord, CoordPrec c' c → x c' = y c') → x c = y c
  /-- RE-KEYED, D.8 (VERTEX) + D.6 + D.10: every member's junction READ CODE
      is the ρ-determined pin code (the pin's `Fin (q₀^d)` ℕ-code is now
      genuinely reachable by the read) -/
  junction : ∀ ρ, ρ < L.rho0 → ∀ x, L.inStratum ρ x →
    ∀ hk : W.ks ∈ W.onLine, L.slotRead x ⟨W.ks, hk⟩ = L.pin ρ
  /-- RE-KEYED range: members' on-line READ CODES are in the `Fin (q₀^d)`
      code range -/
  digit_range : ∀ ρ, ρ < L.rho0 → ∀ x, L.inStratum ρ x →
    ∀ k : ↥W.onLine, L.slotRead x k < L.q0 ^ D.d
  /-- per-slot height-count semantics (v3 verbatim) -/
  slot_sem : ∀ ρ, ρ < L.rho0 → ∀ k ∈ W.boxSlots,
    L.cylSlot ρ k = blockCount L.q0 (L.slotBlock k) (L.slotCond ρ k)
  /-- RE-KEYED: per-slot per-digit count semantics through the d-leaf READ
      CODE (the huni repair's load-bearing clause: digit alphabet = read
      alphabet = the `Fin (q₀^d)` code) -/
  slotDigits_sem : ∀ ρ, ρ < L.rho0 → ∀ (k : ↥W.onLine) (z : ℕ),
    L.cylSlotDigits ρ k z
      = blockCount L.q0 (L.slotBlock (k : Fin (W.ℓ + 1)))
          (fun x => L.slotCond ρ (k : Fin (W.ℓ + 1)) x ∧ L.slotRead x k = z)
  /-- D.8 (BOX) + D.11 count value (v3 verbatim) -/
  slot_count_val : ∀ ρ, ρ < L.rho0 → ∀ k ∈ W.boxSlots,
    L.cylSlot ρ k
      = L.q0 ^ ((D.period * D.d) * L.N - D.s (max (W.beta k) (P.g k)))
  /-- D.11 existence half (v3 verbatim) -/
  member_exists : ∀ ρ, ρ < L.rho0 →
    ∃ v : ↥L.toLedgerStratumData.supportUnion → Fin L.q0,
      L.inStratum ρ (fun c =>
        if h : c ∈ L.toLedgerStratumData.supportUnion then (v ⟨c, h⟩ : ℕ) else 0)
  /-- (ii.3) at full box-slot range (v3 verbatim) -/
  parent_box_disjoint : ∀ k ∈ W.boxSlots, Disjoint L.parentBlock (L.slotBlock k)

end LedgerStratumDataV4

/-- **The designated strata family, v4** (the huni-v2 carrier family): the
v4-lawful d-leaf-read ledger instances' q-generic carriers. Inhabited at the
huni countermodel's own census (`HuniV4Probe.td2V4_mem_ledgerStrataV4`) —
where, unlike over v3, the `huni` face is SATISFIABLE
(`HuniV4Probe.slotUniform_td2V4`). -/
def LedgerStrataV4 (D : CensusData) (W : WindowDatum D) (P : ParentShape D W) :
    Set (JointStratum D W P) :=
  {J | ∃ L : LedgerStratumDataV4 D W P,
    L.LedgerLawfulV4 ∧ J = L.toLedgerStratumData.ledgerJoint}

end LeanUrat.B2D
