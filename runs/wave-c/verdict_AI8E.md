# Verdict AI8E — ENACTMENT of amendment A-I.8 (retire `GNCitePayload` from the live `RecenterStep`; the mp1 leg goes cite-free via the direct key route)

**Date:** 2026-08-28
**Unit:** AI8E
**Verdict:** **ENACTED — all verification gates green.**
**Basis:** `runs/wave-c/verdict_DWR.md` (the forcing stop-line: `GNCitePayload`'s shape is
structurally defective — the GN-selected factor can never literally equal the recentered
key, so NO source-faithful occurrence exists under the payload, for ANY tower) +
`runs/wave-c/verdict_A8D.md` (the adjudication: fork (β) — the direct key route; exact
shapes machine-verified in `leanfinal/scratch/A8D_probe.lean`), both read in full and
followed section by section.  Forcing basis re-verified on this machine BEFORE enactment:
`scratch/A8D_probe.lean` exit 0, all six footer prints exactly
`[propext, Classical.choice, Quot.sound]`, including
`A8DProbe.irreducible_of_isMuKey` and the generic compiler
`A8DProbe.mp1CarrierLiveDirect_of_steps`.
Pre-enactment state archived at commit `3d545e6e` (verified present: the A8D landing).
Procedural templates: `runs/wave-c/verdict_AI6E.md` + `verdict_AI7E.md`, mirrored.

## ⚠ The forcing's honest character (different from A-I.6/A-I.7)

This rebind is **NOT emptiness-forced**: no machine refutation of the old surface exists
or is claimed.  DWR's stop-line is an HONESTY forcing — the old `GNCitePayload` Prop
remains formally inhabitable, but only by source-UNFAITHFUL instances (its `exactLeaf`
clause equates the GN-selected finite-slope factor with the literal test-key divisor,
which GN's factorization places in the separate key-power term).  Hence no retired-record
refutation pin exists for A-I.8; the tension record is the byte-frozen A-I.7 surface
itself plus DWR's verdict.

## Naming adjudications (both recorded per the charge's licence)

1. **Supersede, not rebind-in-place** (the charge's fork): `LadderSupplyLive₂` lives in
   `I10RecenterLive.lean`, which the charge freezes byte-for-byte — in-place rebinding is
   impossible under the freeze, so the AI7E supersession pattern is kept:
   **`LadderSupplyLive₃`** in the new file.
2. **The charge's working names `RecenterStep₂`/`MP1CarrierLive₂` are replaced by the
   probe's names** `RecenterStepDirect` / `MP1CarrierLiveDirect` / `DirectKeyPayload` /
   `midPeelEmission_of_recenterStepDirect` / `mp1CarrierLiveDirect_of_steps`: byte-identical
   promotion from the machine-verified probe is the stronger verification property, A8D's
   §5 table cites these exact names, and the file name `I10RecenterDirect.lean` (fixed by
   the charge) matches.

## Touched files (10)

| file | change |
|---|---|
| `leanfinal/Uniformity/ChapI/I10RecenterDirect.lean` | **NEW** (the charge's named home): `DirectKeyPayload`/`RecenterStepDirect`/`midPeelEmission_of_recenterStepDirect`/`MP1CarrierLiveDirect`/`mp1CarrierLiveDirect_of_steps` PROMOTED from `scratch/A8D_probe.lean:89-193` — machine diff of the 105-line block: **exactly ONE line differs**, the docstring sentence `A-I.8 draft surface.` → `The A-I.8 live surface.` (declaration bytes identical); `LadderSupplyLive₃` (`package`/`lb1`/`vartheta` byte-identical to `LadderSupplyLive₂`'s, ONLY `mp1 : MP1CarrierLiveDirect.{uW, uG, uKt, uL} C B G Kt L N v ρ q n`); supersession pins `directKeyPayload_of_gnCitePayload` (payload level) + `ladderSupplyLive₃_of_live₂` (record level); §3 comment records WHY no step-level adapter exists.  Import analysis: imports ONLY `Uniformity.ChapI.I10RecenterLive` — acyclic `I10_I15_I18 → I10RecenterDirect → I10RecenterLive → I10LadderLive → {C130s18, E24}`; the monic Gauss equivalence resolved inside that closure (no extra import); the C132/C134 banks are NOT imported (capstone graph stays free of them) |
| `leanfinal/Uniformity/ChapI/I10_I15_I18.lean` | the `ladder` field's result record `IFC5.LadderSupplyLive₂.{uW, uG, uKt, uL} … n` → `IFC5.LadderSupplyLive₃.{uW, uG, uKt, uL} … n`; import + header provenance clause + the dated 9-line field comment.  **NOTHING ELSE** — see the statement-shape proof below |
| `leanspec/Leanspec/ChapI.lean` | import; **STATE UPDATE (2026-08-28, AMENDMENT A-I.8)** block in the A-I.6/A-I.7 numbered style (quotes DWR's stop-line and A8D's adjudication VERBATIM; names commit `3d545e6e`); the `ladder` field rebound — comment block + field text machine-diffed against the leanfinal twin: **BYTE_IDENTICAL** (17 lines); gate item (3) ALONE: `hstep`'s type → `IFC5.RecenterStepDirect.{uW, uG, uKt, uL} …` + dated comment, application shape unchanged; items (2)/(4) untouched (their fields are byte-identical) |
| `leanfinal/Uniformity/ChapI/IFC0.lean` | ONLY the anti-drift pin retargeted (`example … := h.ladder` now spells the `LadderSupplyLive₃` ∀-type — elaboration certifies the rebound field's exact type) + its docstring + a dated A-I.8 paragraph in the §1 section comment.  `LadderField`, all four suppliers, the exact split: **byte-frozen** |
| `leanfinal/Uniformity/ChapI.lean` | aggregator: `import Uniformity.ChapI.I10RecenterDirect` (roll-up coverage; the AI6E/AI7E precedent) |
| `leanfinal/Uniformity/ChapI/I10RecenterLiveS2.lean` | declarations **byte-frozen**; dated `[A-I.8]` header note ONLY (the charge's "freeze with a dated note" fork): the S2 vacuity/prefix results remain valid history; the tangent-class certificate is NO LONGER a blocking row (`DirectKeyPayload` demands no `tangentClass`); the named open re-scoped to the direct fields |
| `leanfinal/scratch/CHFD_probe.lean` | sole constructor hunk (the AI6E/AI7E ripple pattern): `hladder`'s conclusion → `IFC5.LadderSupplyLive₃ … 2` + one dated comment line; `ladder := hladder` literal unchanged |
| `docs/REVIEW_QUEUE_2026-08-26.md` | Tier 1 row **8** appended (capstone-surface amendment, ENACTED; records the honesty-forcing character and the mp1-discharge asymmetry) |
| `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` | `[AI8E 2026-08-28]` enactment paragraph appended inside the existing `[A8D]` §12 (the charge's ordered append): §12.3 is ENACTED; the spine row "A8D-S0 → generic MP1 compiler → MP1CarrierLive" is landed |
| `docs/in-progress/LADDER_SUPPLY_2026-08-27.md` | `[AI8E]` entry: the NAMED OPEN `S2-RECENTER-EXPORT` RE-SCOPED to the direct fields (GN-only rows DELETED with the payload; SRX's mass-one degree obstruction stands — the occurrence tooth needs the DWC/DWR deep-witness tower) |

`I10RecenterLive.lean`, `I10LadderLive.lean`, `IFC5.lean`, `E40.lean`, `E24.lean`,
`scratch/REX_probe.lean`, `scratch/SRX_probe.lean`, `scratch/AI6_probe.lean`,
`scratch/A8D_probe.lean`, `scratch/MP1R_probe.lean`: **byte-untouched** (git-clean) — the
whole A-I.7 GN surface stands as the tension record, and (a finding, see "Ripple analysis")
no probe pin needed re-targeting.

## The superseding shapes (charge step 1, per A8D §1's table)

`RecenterStepDirect` = A-I.7's `RecenterStep` with the same one-existential-witness
slot/block/gauge-family views, `Λ ≠ 0`, degree bound, recenter equality, divisor — and the
two-clause replacement exactly as probed:

```diff
- (∃ (kRes : Type) (_fRes : Field kRes),
-   Nonempty (GNCitePayload (Kt := Kt) (L := L) A B.F B'.Φ kRes)) ∧
- Nonempty (MP1StepCore.{uW} B B')
+ B'.T = B.T ∧
+ Nonempty (DirectKeyPayload (Kt := Kt) (L := L) A B'.Φ) ∧
+ ∃ step : IFC5.MP1StepCore.{uW} B B',
+   step.quot.F = B'.F ∧
+   step.quot.T = B.T ∧
+   B.F = B'.Φ * B'.F
```

(the four added equalities are DWR's anti-splicing bindings; `DirectKeyPayload` =
`e'/f'/u'` + the same-chain `FGMNSourceData` + `source.keyPolynomial phi` + the universal
`key_irreducible : ∀ g, keyPolynomial g → Monic g → Irreducible g`).  `MP1CarrierLiveDirect`
is `MP1CarrierLive` with only the producer premise retyped.  The compiler
`midPeelEmission_of_recenterStepDirect` projects the peel core, applies the payload's law
+ monic Gauss for `hirr`, and fills `hef` by `B'.hΦdeg.trans C.hef`;
`mp1CarrierLiveDirect_of_steps` then proves the carrier **outright**.

**The honest asymmetry, stated plainly:** the rebound `mp1` leg is a THEOREM.  The
`ladder` field's remaining open content is exactly `package`/`lb1`/`vartheta`; MP1's
mathematical content moved to producing `RecenterStepDirect` occurrences (A8D's C4d/C5d,
resting on the D3/D4 key tails).  One occurrence yields nonvacuity only.

## Adapter analysis (charge step 1's check, executed)

* **Payload level — the direction HOLDS, enacted as a pin**: the GN payload's key-hood
  clause plus its `sourceLaws` field imply the direct demand, because
  `FGMNSourceLaws.key_irreducible : ∀ g, S.keyPolynomial g → g.Monic → Irreducible g`
  (`C130fg.lean:260-261`) is exactly `DirectKeyPayload.key_irreducible`'s type at
  `S := P.source`.  `directKeyPayload_of_gnCitePayload` proves it (Lean-core).
* **Step level — NO adapter exists, reason recorded** (`I10RecenterDirect.lean` §3):
  old → new fails on DWR's bindings — from the old core only `step.quot.T = B.T` (`hthr`)
  and `B.F = B'.Φ * step.quot.F` (`hpeel`) are derivable; `step.quot.F = B'.F` and
  `B'.T = B.T` are strictly new producer content.  New → old fails too (no GN
  slope/residual/leaf data in the direct payload).
* **Record level — OLD ⟹ NEW holds**: `ladderSupplyLive₃_of_live₂`, with the new `mp1`
  filled by the generic compiler (it needs nothing from the old leg).

## Ripple analysis (charge step 3; a finding vs. the charge's expectation)

`rg RecenterStep|MP1CarrierLive|GNCitePayload|LadderSupplyLive₂` over
`leanfinal/ + leanspec/ + scratch`: hits confined to the ten files above plus the frozen
surfaces.  **The charge anticipated SRX/REX pin re-targets (the AI6E/AI7E step-5 pattern);
NONE were needed**: SRX_probe pins against the production `GNCitePayload`/`RecenterStep`/
`MP1StepCore`/`MP1CarrierLive` — all byte-frozen in `I10RecenterLive.lean`, so its
refuter bytes compile unchanged; REX_probe's refutation chain targets byte-frozen
`IFC5.LadderSupplyLive` and its own local retired copy (self-contained since AI7E);
AI6_probe is self-contained; MP1R_probe's `MP1CarrierLive` is a local namespace copy.
All six probes re-verified exit 0 post-rebind (table below).  Post-sweep, the only
code-level `LadderSupplyLive₂` uses are its frozen home and the new pin's premise.

## I.15–I.18 statement-shape proof (conclusions unchanged)

The complete `git diff` of `I10_I15_I18.lean` is 16 insertions + 2 deletions containing
**zero** `theorem`/`def`/`structure`/`example` keywords and **zero** occurrences of the
four assembly names (machine-grepped) — every hunk is the import, the header provenance
clause, and the `ladder` field comment+record.  The four assembly theorems stand
byte-identical in both files:

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

The `CapstoneHypotheses` field LIST is byte-unchanged — only the `ladder` field's result
record changed, exactly as licensed.

## Verification (all run on this machine, in order)

| gate | command (cwd `leanfinal` unless noted) | result |
|---|---|---|
| forcing probe (pre-enactment) | `timeout 580 lake env lean scratch/A8D_probe.lean` | exit 0, 6/6 Lean-core |
| new module | `lake env lean Uniformity/ChapI/I10RecenterDirect.lean`; `lake build Uniformity.ChapI.I10RecenterDirect` | exit 0, 8/8 prints Lean-core; green (8712 jobs) |
| byte-identity (promotion) | `diff` probe lines 89–193 vs the production block (105 vs 105 lines) | exactly ONE line differs — the recorded docstring word |
| rebound I.10 | `lake env lean Uniformity/ChapI/I10_I15_I18.lean` | exit 0, 7/7 prints Lean-core |
| scoped roll-up | `timeout 580 lake build Uniformity.ChapI` | **green, 8952 jobs** (AI7E's 8925 + the new module + rebuilds; only the pre-existing aggregator copyright style warning) |
| IFC0 pin | `lake env lean Uniformity/ChapI/IFC0.lean` | exit 0, 23/23 prints Lean-core/subsets (strict scan: 20 axiom lists + 3 axiom-free) |
| S2 file (frozen + note) | `lake env lean Uniformity/ChapI/I10RecenterLiveS2.lean` | exit 0, 3/3 Lean-core |
| frozen A-I.7 surface | `lake env lean Uniformity/ChapI/I10RecenterLive.lean` (git-clean) | exit 0, 7/7 Lean-core |
| A8D probe post-rebind | `timeout 580 lake env lean scratch/A8D_probe.lean` | exit 0, 6/6 Lean-core |
| REX probe post-rebind | `timeout 580 lake env lean scratch/REX_probe.lean` | exit 0, 6/6 Lean-core, refuter bytes unchanged |
| SRX probe post-rebind | `timeout 580 lake env lean scratch/SRX_probe.lean` | exit 0, 8/8 Lean-core, refuter bytes unchanged |
| AI6 probe post-rebind | `timeout 580 lake env lean scratch/AI6_probe.lean` | exit 0, 8/8 Lean-core |
| CHFD ripple | `timeout 580 lake env lean scratch/CHFD_probe.lean` | exit 0 (6 probe decls Lean-core; 7th print is landed `ns7Termination_of_cite` = Lean-core + previously-declared allowlisted `Tower.agnprw_termination`, byte-identically as pre-edit) |
| MP1R probe (imports IFC0) | `timeout 580 lake env lean scratch/MP1R_probe.lean` | exit 0 |
| leanspec | `cd leanspec && timeout 580 lake env lean Leanspec/ChapI.lean` | exit 0, zero errors (all census guards pass) |
| twin byte-identity | `diff` of the 17-line A-I.8 ladder comment+field block, leanfinal vs leanspec | `BYTE_IDENTICAL` |
| freeze check | `git status` on `I10RecenterLive.lean`/`I10LadderLive.lean`/`IFC5.lean`/`E40.lean`/`E24.lean` + all probes except CHFD | all git-clean |

## Footprint table (every `#print axioms` in touched/re-verified leanfinal files)

Strict scan (wrapped lines joined, every bracketed list checked ⊆ Lean core):
**no new axiom anywhere**.

| file | prints | footprint |
|---|---|---|
| `I10RecenterDirect.lean` | 8 (`DirectKeyPayload`, `RecenterStepDirect`, `midPeelEmission_of_recenterStepDirect`, `MP1CarrierLiveDirect`, `mp1CarrierLiveDirect_of_steps`, `LadderSupplyLive₃`, both pins) | Lean-core |
| `I10_I15_I18.lean` | 7 (incl. `CapstoneHypotheses`, I.15–I.18) | Lean-core |
| `IFC0.lean` | 23 footer prints | Lean-core / subsets |
| `I10RecenterLiveS2.lean` | 3 | Lean-core |
| `I10RecenterLive.lean` (frozen) | 7 | Lean-core |
| `scratch/A8D_probe.lean` | 6 | Lean-core |
| `scratch/REX_probe.lean` | 6 | Lean-core |
| `scratch/SRX_probe.lean` | 8 | Lean-core |
| `scratch/AI6_probe.lean` | 8 | Lean-core |
| `scratch/CHFD_probe.lean` | 6 Lean-core + the pre-existing allowlisted cite print (unchanged) | as pre-edit |

## Deviations from the unit charge (all within its licence, each recorded above)

1. **Names**: the working names `RecenterStep₂`/`MP1CarrierLive₂` replaced by the probe's
   `Direct` names (byte-identical promotion + A8D's own vocabulary; adjudication section).
2. **One docstring word** changed in the promotion (`draft` → `live`) — declaration bytes
   identical; the exact diff is quoted in the verification table.
3. **No SRX/REX pin re-targets** — the charge's step-5 pattern turned out unnecessary
   (analysis in "Ripple analysis"); all probes re-verified instead.
4. **The generic `IsMuKey → Irreducible` bridge is NOT promoted** into production: it
   stays compiled in `scratch/A8D_probe.lean` and enters with the D3-16/D4-15 key tails,
   per A8D's explicit "put it in the A-I.8 support file **or instantiate it in D3-16**"
   fork — promoting it now would drag the C134 bank into the capstone import graph,
   violating the AI7E acyclicity discipline.
5. **`LADDER_SUPPLY_2026-08-27.md` [AI8E] entry** added beyond the charge's three ordered
   records: the named open's row list there was GN-scoped and would have gone stale.

## Opens (the honest state after A-I.8)

* **NAMED OPEN `S2-RECENTER-EXPORT`, re-scoped**: a `RecenterStepDirect` occurrence needs
  a recentered external `B'` with `source.keyPolynomial B'.Φ`, the directly proved
  `key_irreducible` law (D3-16/D4-15 twins — load-bearing proof nodes, NOT transcription),
  and the peel core with DWR's bindings.  SRX's degree obstruction stands: the landed
  mass-one degree-4 S2 parent cannot host `MP1StepCore`, so the occurrence tooth needs the
  DWC/DWR mass-two deep-witness tower (C4d/C5d).
* The `mp1` supply leg is CLOSED (discharged by the generic compiler); `package`/`lb1`/
  `vartheta` open exactly as before (LB1's LS-G0 stop, LVS-CANONICAL-TAU-EXPORT, etc.).
* `∀ n, CapstoneHypotheses n` remains OPEN (not provably empty, not claimed inhabited):
  `a0`/`a1` open at `n ≥ 3`, weld debts untouched.
* Owner read: REVIEW_QUEUE Tier 1 row 8 (this amendment — note it is an HONESTY-forced
  statement change, the first not backed by a machine refutation; DWR's verdict is the
  evidence to audit).
* Coordination: unit A23E's concurrent ChapC edits were untouched by this unit (verified:
  my diff footprint contains no ChapC file).

No git operations performed (orchestrator lands).  No `sorry`, no new axiom, zero
statement changes beyond the licensed diff, no owner's-paper citation used.
