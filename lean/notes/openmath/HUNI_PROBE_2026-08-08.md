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
