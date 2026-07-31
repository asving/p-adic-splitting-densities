# M09 FORMALIZED (2026-07-31) — `cl11_ksub` at GENERAL n, landed in the corpus

## What landed

New module `lean/LeanUrat/MovesU/KsubGeneral.lean` (0 sorry, all four theorems
Lean-core `[propext, Classical.choice, Quot.sound]`, `#print axioms` re-run at
landing and recorded in the module's EOF comment):

1. `LeanUrat.MovesU.ksubM1C1T_of_degCons {n} (T : MovesS.TableShape n)
   (hdc : MovesS.DegCons T) : KsubM1C1T T` — the (K-SUB) m = 1 classification is
   a theorem of DEG-CONS alone, at EVERY n and every table. Pigeonhole on the
   member-size sum: all members of size e with sizes summing to ≤ e
   (`DegCons.size_sum`) forces m·e ≤ e, and e ≥ 1 forces m = 1; c ≤ m
   (filter sublist) and c ≠ 0 force c = 1. Consumes only `size_sum`.
2. `LeanUrat.MovesU.UCarriers.cl11_ksub_general {n} (C : UCarriers n) :
   KsubM1C1T C.T` — the ledger-row form: the row is derivable from the carried
   `C.hdc` at every carrier pack, every n, every p.
3. `LeanUrat.MovesU.ksub_exists_form` — the guard-form equivalence (the
   `KsubM1C1T` docstring's parenthetical, made precise): under full DEG-CONS
   (`size_pos` + `size_sum`) the ∃-a-size-e-member guard already forces
   m = 1 ∧ all-members-size-e; the converse direction is immediate from
   `Outcome.hm`. The two published guard readings of (K-SUB) coincide.
4. `LeanUrat.MovesU.ksubM1C1T_n2_viaGeneral : KsubM1C1T n2T` — subsumption
   cross-check: the SYN2-K1 conclusion re-derived from the general theorem +
   the instance DEG-CONS term `n2hdc` (`MovesS/N2ScsData.lean`).

## Provenance: DUAL-PROVED (the acceptance basis)

Per `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (OPEN-MATH FIRST RETURNS,
2026-07-31): Fable and the Codex twin, working INDEPENDENTLY from the brief
(`lean/notes/openmath/M09-cl11-general_brief.md`), returned IDENTICAL proofs —
pigeonhole from `DegCons.size_sum` alone. Fable's attempt with full write-up,
Lean sources, and the executed numerics (7000 PARI factorpadic samples, zero
deg-sum violations; 1912 all-deg-n cases, zero pigeonhole violations) is
`lean/notes/openmath/M09-cl11-general_attempt.md`; the green scratch files it
records were `/tmp/M09_cl11_general_check.lean` + `/tmp/M09_cl11_exists_form.lean`,
whose proof bodies this module adopts verbatim.

## KEEP-AND-SUPPLY wiring (no statement change, no row deletion)

Both `cl11_ksub` rows are KEPT byte-identical; the module is their derived
supply:

- `BridgeKernels.cl11_ksub` (`MovesU/BridgeKernels.lean:267`, type
  `KsubM1C1T C.T`): any future `BridgeKernels` instantiation supplies the row
  by `UCarriers.cl11_ksub_general C`.
- `CapstoneLedger.cl11_ksub` (`MovesU/DefsLedger.lean:794`, same type): same
  supply term. The IB-F3 assembly (`bridgeCapstoneLedger`,
  `MovesU/BridgeMk.lean:121`) keeps its verbatim
  `cl11_ksub := BD.BK.cl11_ksub` transport — no definition change; the BK-side
  row is now derivable at source.
- `SynK1_ksubN2.lean` (`ksubM1C1T_n2`, the n = 2 roster walk) is NOT edited —
  records stay; verified still building green at landing
  (`lake build LeanUrat.MovesU.SynK1_ksubN2`, 2026-07-31). It remains the
  recorded instance discharge and now doubles as a roster-walk cross-check of
  the general theorem (agreement exhibited by `ksubM1C1T_n2_viaGeneral`).

ROW DELETION (making `cl11_ksub` a derived non-field of both structures, the
`cl13_wf`/`menuWFT_holds` precedent) is a STATEMENT-CHANGE event: flagged as a
future queue decision per the adjudication record, NOT executed here.

## Obligation accounting

No new axiom, no new obligation. The proof consumes only `C.hdc` — CL-11's
DEG-CONS remains the carried burden it already was (produced at the n = 2
instance by `n2hdc`/`n2_degcons_scs`, generically by the MovesV gate
`V2_degcons`/`V7_tsGate`). The (K-SUB) face adds nothing on top of it. The
remaining-census entry "BK.`cl11_ksub` at general n (n=2 DISCHARGED)"
(`notes/REMAINING_CENSUS_2026-07-31.md` item 11) is CLOSED by this module.

## Gates run at landing (2026-07-31)

- `lake build LeanUrat.MovesU.KsubGeneral` — success (8574 jobs).
- `lake env lean LeanUrat/MovesU/KsubGeneral.lean` — 0 errors (style-linter
  warnings only, house-standard set_options).
- `#print axioms` all four theorems: `[propext, Classical.choice, Quot.sound]`.
- `lake build LeanUrat.MovesU.SynK1_ksubN2` — success (unedited).
- `grep -c sorry` on the module: 0.
