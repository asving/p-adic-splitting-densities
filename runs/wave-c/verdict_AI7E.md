# Verdict AI7E — ENACTMENT of amendment A-I.7 (rebind the capstone `ladder` record's `mp1` leg to the same-realization `MP1CarrierLive`)

**Date:** 2026-08-28
**Unit:** AI7E
**Verdict:** **ENACTED — all verification gates green.**
**Basis:** `runs/wave-c/verdict_REX.md` (the forcing adjudication + the three-layer export
design, followed section by section); forcing refutation re-verified on this machine BEFORE
enactment: `leanfinal/scratch/REX_probe.lean` exit 0, all six footer prints exactly
`[propext, Classical.choice, Quot.sound]`, including
`REXProbe.s2_unrestricted_mp1_false : ¬ Ladder.MP1Carrier C2 B2`,
`REXProbe.s2_ladderSupplyLive_false : ¬ IFC5.LadderSupplyLive C2 B2 … 4`, and (pre-rebind)
`REXProbe.capstoneHypotheses_four_refuted_via_mp1 : ¬ CapstoneHypotheses 4`.
Pre-rebind state archived at commit `05f067b7` (verified present: the LVS+REX landing).
Procedural template: `runs/wave-c/verdict_AI6E.md` (unit AI6E), mirrored throughout.

## Import-home analysis (plan step 1, recorded as ordered)

The three REX layers need: `FGMNSourceData`/`FGMNSourceLaws`/`ChainRealization` (C130fg),
the CC-12 views + `RealizedInput` (C130vw/C130in), `kerComapAlong` (C130s18),
`MidPeelEmission`/`RungInterface` (E40/E12) — ALL already in the transitive closure of
`I10LadderLive`'s imports (`C130s18` + `E24`).  So extending `I10LadderLive.lean` was
import-feasible, but REJECTED: the unit charge freezes `I10LadderLive` byte-for-byte as
the A-I.6 record (supersede, never rewrite history).  Home therefore:
**NEW `I10RecenterLive.lean`, importing exactly `Uniformity.ChapI.I10LadderLive`** —
acyclic by construction: `I10_I15_I18 → I10RecenterLive → I10LadderLive → {C130s18, E24}`.
The S2-instance construction (plan step 5) needs the C132 μ₃ bank; it goes to a SECOND new
file **`I10RecenterLiveS2.lean`** (imports `I10RecenterLive` + `C130sg`/`C132fd0`/`C132sg2`)
which is NOT imported by `I10_I15_I18` — the capstone import graph stays free of the C132
bank; the aggregator covers both.

## Touched files (10)

| file | change |
|---|---|
| `leanfinal/Uniformity/ChapI/I10RecenterLive.lean` | **NEW**: `MP1StepCore`, `GNCitePayload`, `RecenterStep`, `MP1CarrierLive` PROMOTED from the probe — machine byte-diff of the 87-line declaration block against `scratch/REX_probe.lean:37-123`: **BYTE_IDENTICAL** (docstrings carried verbatim); `LadderSupplyLive₂` (the charge's working name adopted; subscript numerals are house style): `package`/`lb1` byte-identical to E.24's fields, `vartheta` byte-identical to A-I.6's live field, ONLY `mp1 : MP1CarrierLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n`; supersession pins `mp1CarrierLive_of_mp1` (OLD unrestricted ⟹ live, restriction only) + `ladderSupplyLive₂_of_live` (record level) — the converse is exactly what REX refuted and is absent |
| `leanfinal/Uniformity/ChapI/I10RecenterLiveS2.lean` | **NEW** (plan step 5): `S2LandedPrefix` + `s2LandedPrefix` + `s2LandedPrefix_tangentClass_impossible` PROMOTED — machine byte-diff of the 43-line block against `scratch/REX_probe.lean:127-169`: **BYTE_IDENTICAL**; header documents the NAMED OPEN `S2-RECENTER-EXPORT` (REX's GAP rows, none fabricated) |
| `leanfinal/Uniformity/ChapI/I10_I15_I18.lean` | the `ladder` field's result record `IFC5.LadderSupplyLive.{uW, uG, uKt, uL} … n` → `IFC5.LadderSupplyLive₂.{uW, uG, uKt, uL} … n`; import + dated field comment + header provenance note.  **NOTHING ELSE** — see the statement-shape proof below |
| `leanspec/Leanspec/ChapI.lean` | import; **STATE UPDATE (2026-08-28, AMENDMENT A-I.7)** block in the A-I.5/A-I.6 numbered style (quoted below); the `ladder` field rebound — comment block + field text machine-diffed against the leanfinal twin: **BYTE_IDENTICAL** (16 lines); gate item (3) ALONE gains the `hstep : IFC5.RecenterStep.{uW, uG, uKt, uL} C B B' G Kt L N v ρ q n Λ` binder and applies `.mp1 Λ hΛ hdeg B' hB' hdvd hstep` — items (2)/(4) untouched (their fields are byte-identical) |
| `leanfinal/Uniformity/ChapI/IFC0.lean` | ONLY the anti-drift pin retargeted (`example … := h.ladder` now spells the `LadderSupplyLive₂` ∀-type — elaboration certifies the rebound field's exact type) + its docstring + a dated A-I.7 sentence in the §1 section comment.  `LadderField`, all four suppliers, and the exact split **byte-frozen** as the tension record |
| `leanfinal/Uniformity/ChapI.lean` | aggregator: imports for both new modules (roll-up coverage; the AI6E precedent) |
| `leanfinal/scratch/REX_probe.lean` | plan step 4 (the AI6E step-5 pattern): local VERBATIM copy of the pre-A-I.7 structure added as `CapstoneHypothesesUnrestrictedMP1` (⚠ RETIRED-RECORD, dated, cite-forbidden); `capstoneHypotheses_four_refuted_via_mp1` retargeted to it (proof byte-unchanged: `h.ladder O2 K2 C2 B2 G2 K2 L2 N2 v2 rho2 q2 s2_canonical_ladder_config`); `s2_ladderSupplyLive_false` still compiles against byte-frozen `IFC5.LadderSupplyLive`; everything else byte-identical; footer prints kept |
| `leanfinal/scratch/CHFD_probe.lean` | sole constructor hunk: `hladder`'s conclusion → `IFC5.LadderSupplyLive₂ … 2`; `ladder := hladder` literal unchanged (the AI6E ripple pattern) |
| `docs/REVIEW_QUEUE_2026-08-26.md` | Tier 1 row **7** appended (capstone-surface amendment, ENACTED) |
| `docs/in-progress/LADDER_SUPPLY_2026-08-27.md` | `[AI7E 2026-08-28]` entry: enactment + the NAMED OPEN `S2-RECENTER-EXPORT` spelled as the campaign's next node |

`IFC5.lean`, `I10LadderLive.lean`, `E40.lean`, `E24.lean`: **byte-untouched** (git-clean),
as the charge ordered — `LadderSupplyLive` and `MP1Carrier` stand as the refuted tension
records.

## I.15–I.18 statement-shape proof (conclusions unchanged)

The complete `git diff` of `I10_I15_I18.lean` is 16 changed lines containing **zero**
`theorem`/`def`/`example`/`structure` keywords and zero occurrences of the four assembly
names — every hunk is the import, the header provenance note, and the `ladder` field
comment+record.  The four assembly theorems stand byte-identical in both files:

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

Names, binders, and conclusions: **diff-empty** (the four proofs project `.a2`/`.a0` only
and never touch `.ladder`).  The `CapstoneHypotheses` field LIST is also byte-unchanged —
only the `ladder` field's result record changed, exactly as licensed.

## Verification (all run on this machine, in order)

| gate | command (cwd `leanfinal` unless noted) | result |
|---|---|---|
| forcing probe (pre-enactment) | `timeout 580 lake env lean scratch/REX_probe.lean` | exit 0, 6/6 Lean-core |
| new module 1 | `lake env lean Uniformity/ChapI/I10RecenterLive.lean`; `lake build Uniformity.ChapI.I10RecenterLive` | exit 0; green (8711 jobs) |
| new module 2 | `lake env lean Uniformity/ChapI/I10RecenterLiveS2.lean` | exit 0 |
| byte-identity (promotions) | `diff` probe lines 37–123 / 127–169 vs the production blocks | `BYTE_IDENTICAL` both |
| rebound I.10 | `lake build Uniformity.ChapI.I10_I15_I18`; `lake env lean …/I10_I15_I18.lean` | green (8857 jobs); exit 0 |
| IFC0 pin | `lake env lean Uniformity/ChapI/IFC0.lean` | exit 0, 23/23 prints Lean-core/subsets (strict scan) |
| scoped roll-up | `timeout 580 lake build Uniformity.ChapI` | **green, 8925 jobs** (AI6E's 8923 + the two new modules; covers IFC1–IFC5 + CW wrappers — no changes needed there: nothing else projects `.mp1` through the capstone) |
| REX probe post-rebind | `timeout 580 lake env lean scratch/REX_probe.lean` | exit 0, 6/6 Lean-core, refutation now pinned to the retired copy |
| AI6 probe post-rebind | `timeout 580 lake env lean scratch/AI6_probe.lean` | exit 0, 8/8 Lean-core (self-contained; needed no ripple) |
| CHFD ripple | `timeout 580 lake env lean scratch/CHFD_probe.lean` | exit 0 |
| leanspec | `cd leanspec && timeout 580 lake env lean Leanspec/ChapI.lean` | exit 0 (all `#axiom_core` census guards pass, incl. `LeanspecI.CapstoneHypotheses`) |
| twin byte-identity | `diff` of the 16-line ladder comment+field block, leanfinal vs leanspec | `BYTE_IDENTICAL` |
| external consumers | `rg "import Uniformity.ChapI"` outside ChapI | only `Uniformity.lean` (root roll-up) and `C130f.lean` (imports untouched `I10FreezeV2`) — no further ripple |

(Pre-existing, unchanged: the aggregator's `Copyright too short!` style warning — the file
has no copyright header and never did; my diff there is two import lines.)

## Footprint table (every `#print axioms` in touched leanfinal files)

Strict scan (wrapped lines joined, every bracketed list checked ⊆ Lean core):
**no new axiom anywhere**.

| file | prints | footprint |
|---|---|---|
| `I10RecenterLive.lean` | 7 (`MP1StepCore`, `GNCitePayload`, `RecenterStep`, `MP1CarrierLive`, `LadderSupplyLive₂`, both pins) | Lean-core |
| `I10RecenterLiveS2.lean` | 3 (`S2LandedPrefix`, `s2LandedPrefix`, `s2LandedPrefix_tangentClass_impossible`) | Lean-core |
| `I10_I15_I18.lean` | 7 (incl. `CapstoneHypotheses`, I.15–I.18) | Lean-core |
| `IFC0.lean` | 23 footer prints | Lean-core / subsets |
| `scratch/REX_probe.lean` | 6 | Lean-core |
| `scratch/AI6_probe.lean` | 8 | Lean-core |
| `scratch/CHFD_probe.lean` | 6 probe decls Lean-core; 7th print is landed `ns7Termination_of_cite` = Lean-core + the previously-declared allowlisted `Tower.agnprw_termination` (already so pre-edit) |

## The leanspec A-I.7 record (header block, quoted from `Leanspec/ChapI.lean`)

> **STATE UPDATE (2026-08-28, AMENDMENT A-I.7): THE `ladder` FIELD'S `mp1` LEG IS REBOUND TO
> THE SAME-REALIZATION LIVE CARRIER — A STATEMENT CHANGE, MACHINE-FORCED.**  A-I.6's record
> was refuted through its remaining unrestricted leg: `leanfinal/scratch/REX_probe.lean`
> (Lean-core, exit 0, orchestrator re-verified pre-enactment; adjudication
> `runs/wave-c/verdict_REX.md`) proves
> `REXProbe.s2_unrestricted_mp1_false : ¬ Ladder.MP1Carrier C2 B2` …
> `REXProbe.capstoneHypotheses_four_refuted_via_mp1 : ¬ CapstoneHypotheses 4` —
> `IFC5.LadderSupplyLive.mp1` still demanded the UNRESTRICTED `Ladder.MP1Carrier`, and the
> landed degree-4 S2 producer's own data (`B2.μ = 1`, `B2.F = B2.Φ + 1`) admit `Λ = −1` with
> the legal successor `B2'.Φ = B2.F`, whose demanded `MidPeelEmission` quotient is
> degree-impossible at the length-one parent ….  The pre-rebind refutation … is archived at
> commit `05f067b7`; after this amendment the probe's `capstoneHypotheses_four_refuted_via_mp1`
> is pinned to a local RETIRED-RECORD verbatim copy (`REXProbe.CapstoneHypothesesUnrestrictedMP1`)
> ….  THE EXACT REBINDING: … `IFC5.LadderSupplyLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n` is
> replaced by `IFC5.LadderSupplyLive₂.{uW, uG, uKt, uL} C B G Kt L N v ρ q n` … ONLY the `mp1`
> leg is replaced by the same-realization `IFC5.MP1CarrierLive`: the
> `Nonempty (MidPeelEmission B B')` conclusion is demanded only at successors `B'` exported by
> an `IFC5.RecenterStep` — ONE existential witness carrying the SAME slot/block/gauge-family
> views as the socket, the GN15-Thm-2.3 payload (`IFC5.GNCitePayload`, a STATEMENT CARRIER
> one-to-one with the source's exact hypothesis list …; NO cite consumed) …, and the peel core
> (`IFC5.MP1StepCore` = `MidPeelEmission` items 2–4, neither `hirr` nor `hef`).  … supersession
> pins … prove OLD ⟹ NEW (restriction only — the converse is exactly what REX refuted).  This
> weakens a hypothesis and therefore STRENGTHENS the conditional capstone; the field list and
> I.15–I.18's statements are BYTE-UNCHANGED.  … Gate change: item (3) ALONE …; items (2)/(4)
> are unchanged.  … the remaining GAP rows … are the NAMED OPEN `S2-RECENTER-EXPORT` ….
> Review: `docs/REVIEW_QUEUE_2026-08-26.md`, Tier 1 row A-I.7.

(Full text in-file; elided only with `…` above.  The A-I.6 block above it is byte-unchanged,
per the standing rule of never editing prior STATE blocks.)

## Deviations from the unit charge (all within its licence)

1. **Two new files, not one**: the S2 landed prefix went to `I10RecenterLiveS2.lean` rather
   than into `I10RecenterLive.lean` — step 5's construction needs the C132 μ₃ bank, which
   would otherwise enter the capstone's import graph through I.10.  Both are aggregated.
2. **Record name**: the charge's working name `LadderSupplyLive₂` adopted as-is (house style
   has Unicode subscripts; nothing in the repo collides).

## Opens (the honest state after A-I.7)

* **NAMED OPEN `S2-RECENTER-EXPORT`** (the supply campaign's next node,
  `docs/in-progress/LADDER_SUPPLY_2026-08-27.md` [AI7E]): no `RecenterStep` instance exists
  at the S2 socket; `s2LandedPrefix_tangentClass_impossible` proves the carried key cannot
  serve, so a genuinely new recentered-key export is required.  `MP1CarrierLive` is OPEN
  there, not refuted — which is the point of the amendment.
* LB1's LS-G0 stop and the live-vartheta supplier's LVS-CANONICAL-TAU-EXPORT open persist;
  `package`/`lb1`/`vartheta` supply legs open exactly as before (their field text unchanged).
* `∀ n, CapstoneHypotheses n` remains OPEN (not provably empty, not claimed inhabited):
  `a0`/`a1` open at `n ≥ 3`, weld debts untouched.
* A degree-two countermodel remains BLOCKED-BECAUSE (no landed depth-one
  `SplitNodePointSource`) — carried from AI6E.
* Owner read: REVIEW_QUEUE Tier 1 row 7 (this amendment — highest reading priority; note
  `GNCitePayload` is flagged NEW-STATEMENT for the standing review even though no cite is
  consumed).

No git operations performed (orchestrator lands).  No `sorry`, no new axiom, zero statement
changes beyond the licensed diff.
