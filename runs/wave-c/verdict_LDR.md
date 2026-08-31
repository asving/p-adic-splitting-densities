# verdict_LDR — UNIT LDR: the capstone `ladder` field's remaining legs, scoped + advanced

**Date:** 2026-08-31.  **Status: COMPLETE.**
`leanfinal/Uniformity/ChapI/I10LadderLegs.lean` — 0 errors, 0 warnings, 0 `sorry`, all 11
printed footprints exactly Lean core `{propext, Classical.choice, Quot.sound}`.  Verified
per-file: `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10LadderLegs.lean`
(clean, footprints printed).  Registered in the chapter aggregator `Uniformity/ChapI.lean`
(one import line; only landed-file edit).  Cite ledger: **empty**.  No git ops (per charge).

## Charge 1 — SCOPE: `LadderSupplyLive₃`'s four legs against today's corpus

The capstone `ladder` field (`I10_I15_I18.lean` NODE I.10, post-A-I.8; ID12's `hladder`):
∀ canonical ladder configs at degree `n`, `CanonicalLadderConfig → IFC5.LadderSupplyLive₃`.
The record (`I10RecenterDirect.lean:225-236`):

| leg | shape | status | genre |
|---|---|---|---|
| `mp1` | `MP1CarrierLiveDirect` | **CLOSED generically** (`mp1CarrierLiveDirect_of_steps`, A-I.8) — and now ELIMINATED from the field's boundary (★ `ladderFieldLive₃_iff_suppliers`: the exact split has THREE suppliers, not four) | closed |
| `vartheta` | `∀ i ≥ 3, CanonicalLadderLiveAt → VarthetaRes` | **SUBSUMED** (this unit, ★ `ladderVarthetaSupplierLive_of_universal`): any discharge of the deepTwist campaign's `UniversalVarthetaSupplier n` (G10U §5) discharges it; through USUP+TWD it rests on `UniversalKernelSpan` + `UniversalGeneratorDescent` | research — but NO LONGER an independent ladder-side item: it merges into deepTwist rows C3 (abstract normalizers) + R5 (OPEN-LETTERS) |
| `lb1` | `Ladder.LB1Carrier C B` | OPEN; LB1G's RESTRICT-ANYWAY twin now NAMED in production (`IFC5.LB1CarrierLive`, promoted byte-identically from `scratch/LB1G_probe.lean` + a new `⊤`-degeneracy fence `lb1CarrierLive_top_iff`); retyping the signed record field is an **owner amendment** (LB1G "BLOCKED-BECAUSE") — flagged, NOT enacted | owner-gated (supersession) + research (the missing C-to-E export relation) |
| `package` | `Ladder.HE7APackage C B` = `Nonempty (RungInterface C B)` | OPEN — no landed declaration produces a `RungInterface` from arising data (only the synthetic E57i/E57ih interfaces exist, not arising-exported); the deep-witness campaign explicitly excludes it | research (XL-blocked, per the old ledger) — NOTE: `package` and `lb1` sit behind the SAME missing C-to-E interface-export layer |

## Charge 2 — what the landed supplier chain reaches (all PROVED, Lean-core)

* ★ `ladderFieldLive₃_iff_suppliers` — **the exact post-A-I.8 boundary**:
  `LadderFieldLive₃ n ↔ IFC0.LadderPackageSupplier n ∧ IFC0.LadderLB1Supplier n ∧
  LadderVarthetaSupplierLive n`.  `LadderFieldLive₃` is the signed field's exact type
  (anti-drift pin `example … := h.ladder` compiles definitionally); `mp1` is eliminated
  by the A-I.8 generic compiler.
* ★ `ladderVarthetaSupplierLive_of_universal` — **the vartheta unification** (the unit's
  main proof, first-attempt compile): `UniversalVarthetaSupplier n →
  LadderVarthetaSupplierLive n`.  Mechanism: the live guard `CanonicalLadderLiveAt` hands
  an arising realization with the I.10b gauge view + `GaugeLive core.r i`; with `3 ≤ i`
  the index is `DeepLive`, the per-witness exporter fires, and G10U's
  `varthetaRes_of_perWitness_view` transports to the external socket datum.  SUFFICIENT
  only; no converse claimed.
* `ladderVarthetaSupplierLive_of_tauSupply` (⟸ USUP `UniversalTauWordDescentSupply`) and
  ★ `ladderVarthetaSupplierLive_of_span_descent` (⟸ TWD `UniversalKernelSpan ∧
  UniversalGeneratorDescent`) — the leg at its deepest landed boundary.
* ★ `ladderFieldLive₃_of_boundary` — the capstone field's assembly from
  {package supplier, lb1 supplier, universal vartheta supplier}.
* §3 promotions: `LB1CarrierLive` / `lb1CarrierLive_of_unrestricted` /
  `lb1CarrierLive_of_exported_partitionLegs` byte-identical to the probe (diff-checked at
  landing), + NEW fence `lb1CarrierLive_top_iff` (`Exported := ⊤` degenerates the twin to
  exactly the unrestricted carrier — the anti-cook tooth for the later amendment).

### The canonical-normalizer question (charge 2's specific ask) — answered NO

The vartheta leg does NOT fire unconditionally from I10TauSupply's canonical-normalizer
machinery: `CanonicalLadderLiveAt` is an EXISTENTIAL over all `ChainRealization`s — the
consumer RECEIVES an arbitrary-normalizer witness, it does not choose a landed one.  TWD's
`rfl` closure (`s2Four_normalizer_eq_laurent`) applies to CHOSEN landed witnesses (all
canonical by construction); TWD simultaneously proved `KernelSpanAt` falsifiable across
the abstract normalizer field (the index-2 twist), so no unconditional proof from the
guard alone can exist.  The honest reach is exactly the universal-supplier route above.

### LB1G RESTRICT-ANYWAY — named, not enacted (charge 2's second ask)

The design doc (verdict_LB1G.md) does NOT say how to enact: the production `Exported`
instantiation requires the missing C-to-E `RealizedRungInterfaceExport`-genre relation
(GAP — no `RealizedInput → RungInterface` exporter or export relation is landed), and the
supersession retypes the signed `LadderSupplyLive₃.lb1` (owner amendment).  Enacted
instead: the minimal naming (the twin's shape + pins + fence, §3), per the charge's
"else name minimally".  Owner-gated items flagged, not enacted.

## Charge 3 — the ladder field's exact post-unit boundary

`ladder` field at degree `n` ⟸ machine-exactly (`ladderFieldLive₃_iff_suppliers` is an
iff):

1. `IFC0.LadderPackageSupplier n` — HE7A at every canonical config.  OPEN, research;
   blocked on the C-to-E interface-export layer (no arising `RungInterface` producer).
2. `IFC0.LadderLB1Supplier n` — LB1 at every canonical config.  OPEN; the honest path is
   the owner-gated restricted-twin supersession (target shapes now landed), whose
   `Exported` relation is the same missing export layer as (1).
3. `LadderVarthetaSupplierLive n` — now ⟸ `UniversalVarthetaSupplier n` ⟸
   `UniversalTauWordDescentSupply n` ⟸ `UniversalKernelSpan n ∧
   UniversalGeneratorDescent n` — i.e. deepTwist campaign rows C3 (at abstract
   normalizers; closed pointwise at every canonical-normalizer realization) + R5
   (OPEN-LETTERS).  NOT an independent ladder-side campaign item anymore.

**NO FULL CLOSURE** — honest partial: `mp1` closed + boundary-eliminated, `vartheta`
merged into the deepTwist boundary, `lb1` target named + owner gate flagged, `package`
scoped (research, shared blocker with `lb1`).

## Files

* `leanfinal/Uniformity/ChapI/I10LadderLegs.lean` — NEW (the unit's landing).
* `leanfinal/Uniformity/ChapI.lean` — one aggregator import line added.
* New statements flagged for standing review: `IFC5.LadderFieldLive₃`,
  `IFC5.LB1CarrierLive` (supplier-side interface `Prop`s below the signed surface; no
  leanspec name touched).
