# W4-SYNC interface deltas from the ratification repairs (2026-07-29)

The MovesS/MovesD as-built corpora changed under the adjudicated ratification repairs
(commit "RATIFICATION REPAIRS APPLIED"; charges MOVESD/MOVESS_RATIFY_REPAIR_CHARGE,
adjudication in the campaign ledger). The wave-4 blueprints (MovesT/MovesV REV 6) were
written BEFORE these landed. Every wave-4 audit round and rev from round 6 on must judge
blueprint↔corpus references against THIS state, not the pre-repair one.

## MovesS deltas (consumed by MovesV; some by MovesT)

1. `RS4Chain.legs_read` — NEW FIELD: for every base prime pool and every consumed
   δ ∈ `consumedDeltas` whose pool `p^δ` is NOT all-active, `LegAgree` (the note (ii-c)
   read-off gate at that pool: MOVES 12204–12218). Wave-4 instances must supply it.
2. `RS4Chain.wsh17_pin` — the `Prop` FIELD IS DELETED. `RS4Chain.wsh17_pin` is now a
   projection-NAMED DEF equal to `W17ii` at the chain's own carriers (production core:
   WshP evaluates to WshVal AND WshVal is the shDom height-sum of shWeightH; MOVES
   12095–12099). Consequence for MovesV: the blueprint's W17ii duty is no longer
   "instantiate the pin with W17ii's statement" — wave 4 must PROVE `W17ii` for its
   instance (or carry it as an explicit sorry-gated obligation with THIS type). The
   `h17 : C.wsh17_pin` binder in U-28 is byte-identical but now contentful.
3. `RatBurdens` gains the per-cell J-RAT interface (owner [1v] = the §V-TABLES side):
   `jPCell` (per-cell tables over the EXISTING carrier `M.Cell`), `jcell_ok`,
   `jcell_interp` (per-cell eval = `M.μcell`, rep-quantified, split-guarded),
   `jcell_sum` (symbolic Σ over the cell fiber = the `jP` aggregate). MovesV's table
   units must target/consume THESE types, not invent parallel ones.
4. `deltaFactors` NARROWED: split members filtered to `Member.continuing` (halted = factor
   1, note; MOVES 11696–11698, 12165–12166). `RegP`/`legs_reg`/`legs_read` quantify over
   fewer pools. Blueprint text quoting the old collection is stale.
5. New named objects available: `LegAgree`, `W17ii`, `PolyGeomLaws` (count-value laws
   for `PolyGeom.countT/countS`; countT pinned via carried `tCount` data — a recorded
   MovesV seam residue), `ReadOffBundle.legAgree_forall`/`.ofLegAgree`,
   `ksub_eval_counted`/`ksub_pool_counted` (CL-6-facing premise variants).

## MovesD deltas (consumed by MovesT's seam rows; some by MovesV)

6. W4-4 (NP-ID) is now TYPED: `NPIDPin` + `NthrSup` + `noteNP` (L12's piecewise
   threshold verbatim) + `D4R4_all_noteRange` (the SUM ∧ EV conclusion on L12's own
   range). Seam rows citing "NP-ID: ledger pin, no Lean object" are stale.
7. W4-5 (POL-PIN) EXISTS: `OffsetPPin` (Type-valued; `Realizes` predicate field + laws
   `total`, `realizes_ne_zero`; non-vacuity witness `lift_ne_zero`) + `CD_canonical`.
8. Empty-shape dispatch [SUPERSEDED at repair round 2, 2026-07-29]: the dispatch is now
   wired INTO the designated objects — `Presented.event`/`mult` themselves carry the
   reads = [] ↦ univ/1 branch; `eventO`/`multO` are DELETED (no parallel semantics).
   Unfolding lemmas: `event_of_ne`/`mult_of_ne` (reads ≠ []) and `event_empty_shape`/
   `mult_empty_shape`. FORCED statement change: D11a `mult_sum` gained an `hne` premise
   (the incidence identity is false at reads = [] under the dispatch — LHS counts the
   full box, RHS sums over empty PrefIdx); D12/D13 already carried hne. Consumers key
   on `event`/`mult` directly.
9. New: `card_classes_abs` (PrefIdx count = the policy-free Galois-quotient count under
   `hnorm`), `SW2_scaleCoherence` (`lineS_at_jstar`, `gamTie_stage_form` — the D1 ruling
   seal), `G2_gatesClassifier` (`PhatStarShape : Shape 3`; typed gate Props `Gate_CD_q2`
   (=3), `Gate_CD_q3` (=48), `Gate_multOne`, four sealed event counts 384/3072/3888/104976
   at MOVES 5344–5372; FC8/FC9 NOT typed — census stratum vocabulary, documented).

## MovesT-side CONTRACT CHANGE, recorded FOR the MovesD-side W4-SYNC (2026-07-29,
## MovesT REV 7 ruling 1 — the W4-1 five-round adjudication)

10. W4-1 (`eligible`/`child_iff`) GAINS the (c2) per-track COVERING clause, by
    orchestrator ruling (MovesT REV-7 charge, ruling 1; the fourth-round BDY hold
    OVERTURNED): at a realized window-opening read (a repeated reduction factor ψ,
    m_i ≥ 2), a root child EXISTS carrying that track's data, in the track-ψ
    reduction cell's own branch set — warrant (c2)'s L1 totality (D4R.0-K(a),
    MOVES 7112–7119), fence-free (no `HistoryCoherent` content). MovesT-side
    value: `ChildCover` (MovesT blueprint §2.9) + the in-corpus falsifier
    `constFalse_childCover_false` (T-D2) — the constant-false-child/unit-cell
    model is now FALSE at the W4-1 interface itself. DUTY ON THE MovesD SIDE:
    the next MovesD ratification/contract pass absorbs the covering clause into
    the W4-1 contract text (its own §2.5 row); until then the MovesT §5 W4-1 row
    carries the change with this entry as the cross-corpus pointer.
