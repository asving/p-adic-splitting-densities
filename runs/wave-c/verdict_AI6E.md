# Verdict AI6E — ENACTMENT of amendment A-I.6 (rebind `CapstoneHypotheses.ladder` to the live-range record)

**Date:** 2026-08-28
**Unit:** AI6E
**Verdict:** **ENACTED — all verification gates green.**
**Basis:** `runs/wave-c/verdict_AI6.md` (the exact rebinding diff, followed subsection by
subsection); forcing refutation re-verified on this machine BEFORE enactment:
`leanfinal/scratch/AI6_probe.lean` exit 0, all eight footer prints exactly
`[propext, Classical.choice, Quot.sound]`, including
`AI6Probe.ladderField_four_refuted : ¬ IFC0.LadderField 4` and (pre-rebind)
`AI6Probe.capstoneHypotheses_four_refuted : ¬ CapstoneHypotheses 4`.
Pre-rebind state archived at commit `ce301df1` (verified present).

## Touched files (9)

| file | change |
|---|---|
| `leanfinal/Uniformity/ChapI/I10LadderLive.lean` | **NEW** (AI6 diff §1): imports `ChapC.C130s18` + `ChapE.E24`, namespace `Uniformity.Density.IFC5`; `CanonicalLadderLiveAt` + `LadderSupplyLive` MOVED from IFC5 — machine byte-diff of both declaration bodies against `HEAD:IFC5.lean:105-123,146-157`: **BYTE_IDENTICAL** (docstrings carried verbatim) |
| `leanfinal/Uniformity/ChapI/IFC5.lean` | the two blocks deleted (dated move-marker comments left); `import Uniformity.ChapI.I10LadderLive` added; header "Honesty scope" A-I.6 strike-update (comment-level). All 8 footer prints still resolve (constants now live in I10LadderLive, same namespace) |
| `leanfinal/Uniformity/ChapI/I10_I15_I18.lean` | AI6 diff §2: `ladder` field result record `Ladder.LadderSupply.{0,0,uW,uG,uKt,uL} C B G Kt L N v ρ q` → `Uniformity.Density.IFC5.LadderSupplyLive.{uW,uG,uKt,uL} C B G Kt L N v ρ q n`; import + dated field comment + header provenance note. **NOTHING ELSE** — see the statement-shape proof below |
| `leanfinal/Uniformity/ChapI/IFC0.lean` | AI6 diff §3: ONLY the two docstrings + the anti-drift pin `example … := h.ladder` replaced (new pin spells the live ∀-type, still closed by `h.ladder` — elaboration certifies the rebound field's exact type). `LadderField`, `LadderVarthetaSupplier`, `ladderField_iff_suppliers`/`_of_suppliers` **byte-frozen** as the refuted tension record; a dated A-I.6 note added to the §1 section comment |
| `leanfinal/Uniformity/ChapI.lean` | aggregator: `import Uniformity.ChapI.I10LadderLive` (so the roll-up covers the new module) |
| `leanfinal/scratch/CHFD_probe.lean` | AI6 diff §4 sole constructor hunk: `hladder`'s conclusion → `IFC5.LadderSupplyLive … 2`; `ladder := hladder` literal unchanged |
| `leanfinal/scratch/AI6_probe.lean` | task step 5 (overriding AI6 §4's remove-suggestion): local VERBATIM copy of the OLD structure added as `CapstoneHypothesesUnbounded` (RETIRED-RECORD, dated, cite-forbidden) + `universe uW uG uKt uL`; `capstoneHypotheses_four_refuted` retargeted to it (proof byte-unchanged: `fun h => ladderField_four_refuted h.ladder`); `ladderField_four_refuted` and everything else byte-identical; footer prints kept |
| `leanspec/Leanspec/ChapI.lean` | AI6 diff §2+§4: import; **STATE UPDATE (2026-08-28, AMENDMENT A-I.6)** block (quoted below); the `ladder` field rebound byte-identically to the leanfinal twin (same comment block); gate item (4) gains the `hLive : IFC5.CanonicalLadderLiveAt … n i` binder and applies `.vartheta i hi hLive` — items (2)/(3) untouched (first three record fields byte-identical), all other gate items untouched |
| `docs/REVIEW_QUEUE_2026-08-26.md` | Tier 1 row **6** appended (capstone-surface amendment, ENACTED; supersedes the Tier-2 LVT row's "future A-I.6, NOT enacted" clause) |

## I.15–I.18 statement-shape proof (conclusions unchanged)

The complete `git diff` of `I10_I15_I18.lean` (both packages) contains **zero** lines from
§3 — every hunk is the import, the header provenance note, and the `ladder` field block.
The four assembly theorems stand byte-identical in both files:

```lean
theorem drainage_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : ∀ n, DrainageAt n
theorem decided_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : UniformityStatementDecided
theorem uniformity_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : UniformityStatement
theorem totalMassOne_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : TotalMassOne
```

Names, binders, and conclusions: **diff-empty** (their ladder-hypothesis plumbing changes
only through `CapstoneHypotheses`' rebound field, exactly as the diff licenses — the four
proofs project `.a2`/`.a0` only and never touch `.ladder`).

## Verification (all run on this machine, in order)

| gate | command (cwd `leanfinal` unless noted) | result |
|---|---|---|
| forcing probe (pre-enactment) | `timeout 580 lake env lean scratch/AI6_probe.lean` | exit 0, 8/8 Lean-core |
| new module | `lake build Uniformity.ChapI.I10LadderLive`; `lake env lean Uniformity/ChapI/I10LadderLive.lean` | green (8710 jobs); exit 0 |
| rebound I.10 | `lake build Uniformity.ChapI.I10_I15_I18`; `lake env lean …/I10_I15_I18.lean` | green (8856 jobs); exit 0 |
| IFC0 pin | `lake build Uniformity.ChapI.IFC0`; `lake env lean …/IFC0.lean` | green; exit 0 |
| IFC5 trim | `lake build Uniformity.ChapI.IFC5`; `lake env lean …/IFC5.lean` | green; exit 0 |
| scoped roll-up | `timeout 580 lake build Uniformity.ChapI` | **green, 8923 jobs** (covers IFC1–IFC4 + CW wrappers `I02_I03w`/`I03_I04w` — no changes needed there, as AI6 predicted: nothing projects `.ladder`) |
| CHFD ripple | `timeout 580 lake env lean scratch/CHFD_probe.lean` | exit 0 |
| probe post-rebind | `timeout 580 lake env lean scratch/AI6_probe.lean` | exit 0, 8/8 Lean-core, `ladderField_four_refuted` intact |
| leanspec | `cd leanspec && timeout 580 lake env lean Leanspec/ChapI.lean` | exit 0 (all `#axiom_core` census guards pass, incl. `LeanspecI.CapstoneHypotheses`) |
| byte-identity of the move | `diff` of the two decl bodies vs `git show HEAD:…IFC5.lean` slices | `BYTE_IDENTICAL` |

## Footprint table (every `#print axioms` in touched leanfinal files)

Strict scan over the four lib-file logs: every bracketed axiom list is exactly
`[propext, Classical.choice, Quot.sound]` or a subset (`[propext, Quot.sound]`,
"does not depend on any axioms") — **no new axiom anywhere**.

| file | prints | footprint |
|---|---|---|
| `I10LadderLive.lean` | `CanonicalLadderLiveAt`, `LadderSupplyLive` | Lean-core |
| `IFC5.lean` | 8 (incl. the two moved constants) | Lean-core |
| `I10_I15_I18.lean` | 7 (incl. `CapstoneHypotheses`, I.15–I.18) | Lean-core |
| `IFC0.lean` | 24 footer prints | Lean-core / subsets |
| `scratch/AI6_probe.lean` | 8 | Lean-core |
| `scratch/CHFD_probe.lean` | 6 probe decls Lean-core; 7th print is landed `ns7Termination_of_cite` = Lean-core + the previously-declared allowlisted `Tower.agnprw_termination` (already so pre-edit; the probe's own constructor stays Lean-core) |

## The leanspec A-I.6 record (header block, quoted from `Leanspec/ChapI.lean`)

> **STATE UPDATE (2026-08-28, AMENDMENT A-I.6): THE `ladder` FIELD IS REBOUND TO THE
> LIVE-RANGE RECORD — A STATEMENT CHANGE, MACHINE-FORCED.** The rider route the LVT record
> above held open is CLOSED BY REFUTATION: `leanfinal/scratch/AI6_probe.lean` (Lean-core,
> exit 0, orchestrator re-verified; adjudication `runs/wave-c/verdict_AI6.md`) proves
> `AI6Probe.ladderField_four_refuted : ¬ IFC0.LadderField 4` and
> `AI6Probe.capstoneHypotheses_four_refuted : ¬ CapstoneHypotheses 4` — VAUD's teeth
> assemble INSIDE the field's own quantification at the landed degree-4 S2 socket …, so
> the signed block's bytes were machine-EMPTY at degree 4 and an interpretive rider is
> IMPOSSIBLE — the A-I.5 rider precedent requires the signed field to remain inhabitable
> in principle. The pre-rebind refutation … is archived at commit `ce301df1`; after this
> amendment the probe's `capstoneHypotheses_four_refuted` is pinned to a local
> RETIRED-RECORD verbatim copy (`AI6Probe.CapstoneHypothesesUnbounded`) and
> `ladderField_four_refuted` still compiles against byte-frozen `IFC0.LadderField`.
> THE EXACT REBINDING: the `ladder` field's result record
> `Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C B G Kt L N v ρ q` is replaced by
> `Uniformity.Density.IFC5.LadderSupplyLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n` — the
> first three record fields (`package`/`lb1`/`mp1`) are byte-identical to E.24's; ONLY the
> `vartheta` leg gains the `CanonicalLadderLiveAt` premise …. To keep the import order
> acyclic the two live declarations … are MOVED byte-for-byte from
> `Uniformity/ChapI/IFC5.lean` to the new `Uniformity/ChapI/I10LadderLive.lean` (namespace
> `Uniformity.Density.IFC5` unchanged), which I.10 now imports here and in `leanfinal`.
> This weakens a hypothesis and therefore STRENGTHENS the conditional capstone; the field
> list and I.15–I.18's statements are BYTE-UNCHANGED. `IFC0.LadderField`/
> `LadderVarthetaSupplier` and their exact split stay byte-frozen as the refuted tension
> record. Gate change: item (4) ALONE …; items (2)/(3) are unchanged …. Review:
> `docs/REVIEW_QUEUE_2026-08-26.md`, Tier 1 row A-I.6 (capstone-surface amendment).

(Full text in-file; elided only with `…` above. The earlier LVT block's closing sentence
"would be a numbered amendment (A-I.6) — NOT enacted" is left byte-unchanged as the dated
historical record, per the A-I.1→A-I.3 precedent of never editing prior STATE blocks.)

## Deviations from verdict_AI6's §4 (both licensed by the unit charge)

1. **AI6_probe**: AI6 §4 said "remove `capstoneHypotheses_four_refuted` and its footer
   print"; the unit charge (step 5) instead ordered the RETIRED-RECORD pin — enacted as
   ordered, so the degree-4 emptiness of the OLD bytes stays permanently compiled.
2. **Aggregator import** (`Uniformity/ChapI.lean`): not in AI6's diff; required so the
   scoped roll-up target covers the new module. Import-only; no statement content.

## Opens (unchanged by this unit)

* Inhabiting `LadderSupplyLive`'s `vartheta` leg at arising sockets (the campaign target
  `IFC5.LadderFieldLive`); LB1's LS-G0 stop and MP1's LS-G1 refuted cite route persist —
  the first three supplier legs are open exactly as before.
* A degree-two countermodel remains BLOCKED-BECAUSE (no landed depth-one
  `SplitNodePointSource`) — AI6's ledger row carried over.
* `∀ n, CapstoneHypotheses n` remains OPEN (not provably empty, not claimed inhabited):
  `a0`/`a1` open at `n ≥ 3`, weld debts untouched.
* Owner read: REVIEW_QUEUE Tier 1 row 6 (this amendment — highest reading priority).

No git operations performed (orchestrator lands). No `sorry`, no new axiom, zero
statement changes beyond the licensed diff.
