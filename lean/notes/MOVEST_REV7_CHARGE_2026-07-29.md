# MovesT REV-7 CHARGE (2026-07-29) — the round-6 union, orchestrator-adjudicated

Blueprint: lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md (REV 6, 4470 lines, 55 units).
Verdicts to fold (READ ALL): lean/notes/MOVEST_AUDIT_CODEX6_2026-07-29.md (REJECT 8/6)
+ lean/notes/MOVEST_AUDIT_FABLE6_2026-07-29.md (2 crit/3 gap). Note section: MOVES
§T-ASSEMBLY 6970–7761. Produce REV 7 in place. Header REV 7 + a full disposition table
(§7 = the round-6 union, every row). No git. Staged writes ≤4000 tokens/response.

## Adjudicated rulings (bind these; do not relitigate)
1. W4-1 BDY HOLD OVERTURNED (5th round; verifiers split, orchestrator direct read
   decides): the note's covering case-analysis (c2) lives AT this layer (MOVES 7112–7119:
   "fix f and a live track. At level 0, m_i = 1 gives τ-hen and m_i ≥ 2 opens the
   window — total…"). The W4-1 contract TYPE gains the per-track covering clause: at a
   realized window read with an eligible μ ≥ 2 branch, a child EXISTS carrying that
   branch/track data (cite (c2)'s L1-totality warrant, D4R.0-K(a)). The constant-false-
   child/unit-cell model must be FALSE at the W4-1 interface itself. Update the seam
   census (this is a contract change, record it for the MovesD-side W4-SYNC).
2. root_total (Codex#1 = Fable GAP-1, converged): per-track tie —
   ∀ ψ repeated (m_i ≥ 2), ∃ ν, trackOf ν = ψ ∧ (Tat N' h).child none ν x. "One track
   per root cluster;" the untied ∃ is a silent weakening. Fable verified the fix keeps
   the childless-tower refutation dead.
3. hdict HOLD STANDS (both legs license it; note 7537–7540). Its blocker is row 4 below.

## Fable round-6 criticals (fix shapes verified by the auditor — apply verbatim, then
re-run the decide checks yourself and re-verify census integers unchanged)
4. CRIT-1: the toy `cellOf .red` guards read NEITHER g NOR x0/x1 — `child_cell_red` is
   decide-FALSE on both carriers (witness: carrier A, χ=toyχ, g=(1,0), x=(1,0,0,…)).
   FIX: add x0 = 0 ∧ x1 = 0 to BOTH winC guards. Auditor verified: cellEventE at the
   true entrance and every census integer unchanged (A 2³, B 2⁶). Re-walk RedCellPartition
   uniqueness at g ≠ toyG this time.
5. CRIT-2: `cellLevel := fun _ => 3` makes `cell_local` decide-FALSE (coords 4,5 sit at
   level 3; toyCell reads x4/x5). FIX: cellLevel ≥ 4 (auditor: levelIdx c < 4 ⟺ c < 6
   covers every read coordinate; all integers unchanged).

## Codex round-6 criticals (accepted)
6. #3 OmSat vacuity via unrelated trackOf: the monic/irred/divisibility conjuncts admit
   a degree-(> n) polynomial making ClusterFactorOf witness-free. FIX: tie trackOf to the
   REALIZED head-track factor — degree ∣/≤ through membership in the realized root
   factorization (RedCellPartition's track roster or the f̄-factor multiset), not just
   abstract divisibility of a cluster degree.
7. #4 hScale/hRes: `windowBlockHts`/`slot0Block` may NOT be E-phase name-bindings —
   load-bearing accessors must be CLOSED defs in the blueprint (define them from the
   existing Node/window vocabulary now).
8. #5 ns_bridge : Prop — the bare-Prop tag defect. TYPE the note's clause ("μ((τ-ns)
   class │ Σ) = 0 by continuity from above"): the finite-level form (the (τ-ns) class's
   finite-level cell proportion → 0, or an abstract measure field with the limit law) in
   the blueprint's own carriers; whatever genuinely needs the measure route is a NAMED
   typed seam with the statement AS the type, never a bare Prop.
9. #6 toy node tables: EVERY data field of the toys must be pinned (no "E-phase-bound
   junk" in DATA positions; junk is only allowed where a field provably cannot affect
   NodeExtends/HistLawful/shapes/tracks/ledgers — if you claim that, display the proof
   obligation).
10. #7 shapeExp: define `bandFresh` CLOSED now (it gates hdict's checkability).
11. #8 seam re-key: MovesD's `Presented.event`/`mult` are being REDEFINED in place
    (repair round 2, in flight): the ∅-shape dispatch (reads = [] ↦ univ/1) moves INSIDE
    event/mult; eventO/multO are DELETED. Key T-F4 (S.mult) and the CONSUMES roster to
    event/mult directly under the new semantics; note the in-flight contract.

## Codex round-6 gaps + Fable gaps
12. F1 joint witness: numerical compatibility ≠ existence; add an E-phase obligation row
    (construct the CellAssign/ledger/scaffold witness) — disclosed, not silently claimed.
13. Stale seam accountings (Fable GAP-2/GAP-3 + Codex g2–g6): per
    lean/notes/W4_SYNC_DELTAS_2026-07-29.md — W4-4 row re-keyed to the BUILT
    `NPIDPin`/`NthrSup`/`noteNP`/`D4R4_all_noteRange` (import by name; no re-bracketing —
    the blueprint's own REV-4 rule); ADD the W4-5 row (`OffsetPPin`/`CD_canonical`, being
    strengthened in repair round 2 with support/determinism laws) and adjudicate wave-4's
    consumer duty; S-8 → wsh17_pin is a projection-def = W17ii (duty = PROVE);
    S-10 → RS4Chain.legs_read exists (add the provenance row); deltaFactors narrowed to
    continuing members (refresh any inherited description); seam census 19 → recount.
14. Fix the hRes note cite (7216–7217, not 7213).

## Discipline
Faithfulness both directions; typed fields; open kernels neither vacuous nor accidentally
closed; every claim you make in the disposition table must be REAL in the text (round-6
burned six claimed-fixed rows — do not repeat). Recompute your own decide/census checks
and DISPLAY the arithmetic. Return {units, dispositions, summary} per the schema.
