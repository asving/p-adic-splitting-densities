# HUNI PROBE — huni/SlotUniformLaw decided at the compiled ledger instances

**Unit**: synthesis pass 5 finding F1 target (i), queue #7 (countermodel-first entry
probe). **Artifact**: `lean/LeanUrat/B2D/HuniProbe.lean` — `lake env lean` GREEN,
all `#print axioms` = Lean core only (`propext, Classical.choice, Quot.sound`), 0 sorry.

## The statement (pinned)

`SlotUniformLaw` (`Scaffold/HDischarge/H2/FreshLaws.lean:125`), the standalone Prop the
`huni` binders display:

```
SlotUniformLaw W P J :=
  ∀ q ρ, ρ < J.rhoCount q →
    ∀ k : ↥W.onLine, (k : Fin (W.ℓ+1)) ≠ W.ks →
      ∀ z z' : ℕ, z < q ^ D.d → z' < q ^ D.d →
        J.slotDigits ρ k z q = J.slotDigits ρ k z' q
```

Consumers: `freshReads_of_digitsProd`/`fresh_of_transDeep` (per-J `huni`), and
`TD6_assembly.ledger_freshRowOn` (the displayed family face:
`∀ W P, ∀ J ∈ LedgerStrataV3 D W P, SlotUniformLaw W P J`).

## Verdicts

1. **At `tdL` (the compiled r = 1 instance): VACUOUSLY TRUE** —
   `slotUniform_tdL_vacuous`. `tdW.onLine = {0} ∋ ks = 0`: the quantifier over
   non-junction on-line slots is EMPTY (`tdW_onLine_eq_junction`). The designated
   instance cannot decide the face.
2. **At `td2` (cheapest non-degenerate extension, built in-file): FALSE** —
   `slotUniform_td2_false`. `td2` = same census `tdD` (r = 1, d = 2, q₀ = 2), same
   blocks/junction, off-line slot 1 promoted on-line with the FREE alphabet-bounded
   condition. `td2L` is fully **v3-lawful** (`td2_lawfulV3`,
   `td2_mem_ledgerStrataV3`) and inside the supplier's firing perimeter
   (`td2_scope`/`td2_clean`; the TransDeep row EXISTS: `td2_transDeep`).
   Failure: slotDigits(z=0) = 2 ≠ 0 = slotDigits(z=2), both z < q^d = 4.
3. **Family face therefore UNSATISFIABLE at `tdD`**: `ledger_huni_face_false_at_tdD`
   refutes `ledger_freshRowOn`'s exact `huni` binder at this census.
4. **Bonus: the consumer's CONCLUSION also fails**: `freshReads_td2_false` —
   `FreshReadsLaw` (what `fresh_of_transDeep` would output) is false at `td2`.

## The mechanism (why this is generic, not adversarial)

An ALPHABET seam: the law's digit alphabet is `q^D.d` (the F_{q^d} digit code, here 4),
but the v2/v3 ledger carrier reads ONE leaf (`slotCoord`) of a `Fin q₀` box vector, so
`slotDigits ρ k z q₀ = 0` is FORCED at every z ∈ [q₀, q₀^d), while some in-alphabet
digit counts positively (member_exists + slot_sem/slot_count_val force a positive
count). So at ANY census with d ≥ 2, huni fails at EVERY v3-lawful instance having a
non-junction on-line slot — no pinned/adversarial slotCond needed (td2's slot 1 is
free). tdL escaped only by window degeneracy (onLine = {ks}).

## Implication (per F1: FALSE ⇒ restatement before supplier work)

The huni face needs RESTATEMENT; the instance points at the LEDGER read, not the H2 law:

* **Faithful repair**: re-key the ledger read to the full d-leaf digit CODE — the
  [R1-G2] "field-element-to-code bijection" that TD-0 only ever exercised at the pin
  value 1 < q₀. `slotCoord : ↥W.onLine → Coord` becomes a d-tuple read (or
  `slotDigits_sem` counts by the coded d-block value). Under that carrier, uniformity
  over z < q^d is satisfiable.
* **Mere re-guarding (z, z' < q) is NOT sufficient**: `FreshReadsLaw` itself consumes
  and fails the full-alphabet range at `td2` (`freshReads_td2_false`), so the guard
  would have to propagate through every (FRESH)(b) consumer — a statement-round on the
  H2 row, strictly more invasive than the ledger-side re-key.

Status update: huni does NOT survive first contact — it moves from [M]-row displayed
hypothesis to **refuted-as-stated over the compiled family** (at d ≥ 2, non-degenerate
windows). New helper decls: `blockCount_congr_ext`, `blockCount_pin2` (HuniProbe.lean).

---

## REPAIR RECORD — huni-v2, the d-leaf-read (v4) re-key [EXECUTED 2026-08-02 wallclock; adjudicated wave-8 unit]

**Authority**: Asvin's standing statement-change rule (2026-08-05); honest repair pinned
by THIS compiled countermodel (countermodel-first protocol). **Artifacts** (all
`lake build` GREEN, `#print axioms` = Lean core only, 0 sorry):
`lean/LeanUrat/B2D/TDDefsV4.lean` · `TDV4_chain.lean` · `HuniV4Probe.lean`.

### The re-key design (the faithful-repair option above, executed)

* **Datum round 4**: `LedgerStratumDataV4 extends LedgerStratumData` + ONE field
  `slotCoords : ↥W.onLine → ℕ → Coord` — the d read leaves per on-line slot (ℕ-indexed,
  only `t < D.d` read). The inherited single `slotCoord` is RETIRED as a read (kept as
  the designated leaf 0 by instance convention; no v4 clause consumes it).
* **The read**: `slotRead L x k = Σ_{t<D.d} x(slotCoords k t)·q₀^t` — the [R1-G2]
  field-element-to-code bijection realized on the `Fin q₀` box carrier (base-q₀ code of
  the d-leaf tuple). Range = the FULL `Fin (q₀^d)` code alphabet: the seam is closed at
  the carrier, exactly as adjudicated ("slotDigits_sem counts by the coded d-block value").
* **Pack `LedgerLawfulV4`**: the 15 v3 clauses, with EXACTLY five re-keyed to `slotRead`
  (`semantics` z-clause → `LedgerSemanticsV4`; `slot_coord_mem` → `slot_coords_mem`;
  `junction`; `digit_range`; `slotDigits_sem`) and the other ten byte-verbatim. NOT an
  `extends` of v3: the single-leaf read clauses are the refuted transcription and must
  not co-constrain the counting fields (junction/slotDigits_sem would contradict at d ≥ 2).
* **Family**: `LedgerStrataV4`. Chain re-proved on it (`TDV4_chain.lean`): TD-1/TD-2/
  TD-4/TD-3 v4 twins (per-decl provenance table in the module docstring; TD-2's
  partition core generalized to functional reads `blockCount_read_partition_fn`; TD-3's
  parent-factor step copied verbatim — it reads only read-free clauses), TD-5 projection,
  `transDeep_of_lawful_v4`/`transDeep_of_ledger_v4`/`ledger_freshRowOnV4` (+ the [R2-G1]
  `rfl` leakFree-plug gate).

### Acceptance tests (all three PASSED, compiled)

* **(a) the td2 countermodel FAILS against huni-v2**: td2 transported to the v4 carrier
  (`HuniV4Probe.td2V4` — same `tdD`/`td2W`/`td2P`, same pin 1, same counts 4/4/16;
  deltas all named in the module docstring: junction block +1 leaf (0,3), junction
  condition pins the 2-leaf code, free slot bounds both leaves). Verdicts:
  `slotUniform_td2V4 : SlotUniformLaw td2W td2P td2V4…ledgerJoint` **HOLDS** (the free
  slot's per-code count ≡ 1 on the full alphabet), and the EXACT old failing pair
  (z = 0 vs z = 2, counts 2 ≠ 0 at v3) is uniform: `td2V4_oldPair_uniform` (1 = 1).
* **(b) tdL/td2 REMAIN v3-lawful and in `LedgerStrataV3`**: byte-untouched
  (`td_lawfulV3`/`td2_lawfulV3`/`td2_mem_ledgerStrataV3` replayed green; the whole v1–v3
  record incl. this probe is unmodified — the repair is a round-4 addition, the
  v1→v2→v3 precedent one level up).
* **(c) the TD chain re-proves against huni-v2**: `fresh_of_transDeep`,
  `freshRowOn_of_transDeep`, `freshReads_of_digitsProd` and ALL H2 law statements
  (`SlotUniformLaw`, `FreshReadsLaw`, `FreshClauses`, `TransDeep`) byte-UNCHANGED — the
  probe pinned the seam to the ledger read, and the compiled transport confirms no H2
  statement had to move. The chain FIRES end-to-end at the repaired carrier:
  `td2V4_transDeep` → `td2V4_freshClauses` → `td2V4_freshReads : FreshReadsLaw` — the
  exact consumer conclusion refuted above (`freshReads_td2_false`) is now DELIVERED at
  the same census/window. `ledger_freshRowOn` (v3) stands as the round-3 record with its
  dead binder; the LIVE face is `ledger_freshRowOnV4` (huni binder over `LedgerStrataV4`,
  satisfiable at d ≥ 2 by `slotUniform_td2V4`).

### Changed signatures

NONE changed in place. New decls only (TDDefsV4/TDV4_chain/HuniV4Probe as above); the
huni face for future suppliers is `ledger_freshRowOnV4`'s binder
`∀ W P, ∀ J ∈ LedgerStrataV4 D W P, SlotUniformLaw W P J` — `SlotUniformLaw` text
byte-identical, carrier family re-keyed v3 → v4. huni's status moves from
refuted-as-stated (over v3) to **displayed-and-satisfiable** (over v4; still (ADM) +
(GR-B)-line content, never supplied by the TD chain).
