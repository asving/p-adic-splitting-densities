# verdict_CEX — UNIT CEX: the C-to-E interface-export layer — PACKAGE SUPPLIER CLOSED, the export relation's core LANDED

**Date:** 2026-08-31.  **Status: COMPLETE.**
`leanfinal/Uniformity/ChapI/I10CExport.lean` (NEW, ~400 lines, namespace
`Uniformity.Density.IFC5`) — 0 errors, 0 warnings, 0 `sorry`, all **18** printed
footprints exactly Lean core `{propext, Classical.choice, Quot.sound}`.  Verified
per-file (`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10CExport.lean`,
exit 0), per-target (`lake build Uniformity.ChapI.I10CExport` — Build completed
successfully, 8975 jobs), and the chapter aggregator `Uniformity/ChapI.lean` re-verified
exit 0 after the one standing import-line edit (only landed-file edit).  Cite ledger:
**empty**.  IFCG53.lean untouched.  No git ops (per charge).

## STATUS FIRST

| charge | status | exact result |
|---|---|---|
| 1. SCOPE | **DONE — two machine-grade findings + the XL adjudication** | (F1) the signed package leg is a TAUTOLOGY; (F2) the export relation factors through `(C,B)`; XL-block = size/effort (1,500–3,000 lines, F1/F2 prerequisites), NOT an obstruction — details below |
| 2. BUILD + fire | **★ PACKAGE SUPPLIER CLOSED at every degree**; export-relation CORE landed; lb1 wired to it | `ladderPackageSupplier_all : ∀ n, IFC0.LadderPackageSupplier n` (Lean-core); ★ `ladderFieldLive₃_iff_lb1_vartheta` — the capstone `ladder` field's post-CEX boundary is TWO suppliers: `IFC0.LadderLB1Supplier n ∧ LadderVarthetaSupplierLive n` (machine-exact iff); `ladderFieldLive₃_of_lb1_universal` — lb1 + `UniversalVarthetaSupplier` now assemble the SIGNED field |
| 3. remainder | **NAMED, minimal** | R1: discharge `IfaceExportedCore` at arising pairs (the F1 frontier construction — the scoped XL item); R2: full-strength export clauses (residual factorizations through `C.dig`, counts, rank); R3: owner amendments re-signing `package`/`lb1` to the exported twins — flagged, NOT enacted |

## Finding 1 — the signed package leg is TAUTOLOGICALLY dischargeable (machine pin)

`HE7APackage C B = Nonempty (RungInterface C B)` (E.24), and E.12's interface reads
`(C, B)` only through `(C.D, B.μ, B.T)` — whose positivity the carriers THEMSELVES supply
(`SlotCarrier.hD : 0 < D`, `BlockData.hμ : 1 ≤ μ`).  ★ `rungInterfaceSynth C B` inhabits
the interface at EVERY pair: one side `(B.T+1, 1)` of length `μ`, one linear residual
factor (root `0`, multiplicity `μ`), all counts `D·μ`, rank carrier `PUnit`/`emptyWf` —
all five clause families check (first-attempt compile).  Consequences, all Lean-core:
`he7aPackage_all` (E.24's conjunct is unconditional), ★ `ladderPackageSupplier_all`
(the supplier at every degree; the config binder is UNUSED — that unused binder IS the
disclosure, machine-visible).

⚠ HONESTY (standing review): the old ledger's XL sizing priced the MEANINGFUL arising
exporter; the SIGNED `Nonempty` needed ~40 lines.  The closure is the letter of the
signed statement (sign-off criterion 2026-08-26); the signed `package` field, as typed,
never constrained the arising data.  The meaningful form is the exported twin (below),
named for the same later owner amendment as LB1G's lb1 twin.  Anti-abuse pin:
`rungInterfaceSynth_sides_card` (one side — never witnesses the `1 < card` LB1 trigger
half); anti-cook tooth on the §2 relation: `ifaceExportedCore_synth_two_point` (the
synthetic interface is NOT vacuously exported — export would force `B`'s own heights to
realize slope `B.T+1` on a genuine two-abscissa side).

## Finding 2 — the C-to-E export relation FACTORS THROUGH `(C, B)`

LB1G demanded a contentful `RealizedRungInterfaceExport X eK I`.  Scope result: the
socket views already pin every field E.12 reads (`BlockViewEq` pins `B.Φ/F/μ/A/T` to the
realized development, `SlotViewEq` pins `C.hgt/dig/D` — C130vw), so "exported by the
realization" ≡ "agrees with `B`'s OWN development heights" — stateable TODAY against
E.11's landed `onLadderSide` (the argmin predicate sides/slopes/lengths derive from, per
E.11's own design note; no polygon type needed).  The realization witness re-enters at
DISCHARGE time (F1), not statement time.

Landed core (NEW STATEMENTS, review): `SideOnBlock B p` (two distinct abscissas attain
the `(u,ℓ)` support value) · `IfaceExportedCore B I` (every side of `I` is a genuine
side of `B`'s ladder AND `I.len` is that side's extremal argmin window width) ·
`RealizedRungInterfaceExport X eK I` (the LB1G-genre relation at the realization
witness; body = the core at the view-pinned block; `realizedRungInterfaceExport_def`
makes the factoring an `Iff.rfl`).  TOOTH `sideOnBlock_two_point`: exported sides
satisfy the two-point support equation in `B.devHgt` — nothing `⊤`-shaped proves this.
Necessity is the design bar; the relation is deliberately restrictive and NOT claimed
inhabited (that is R1).

## Finding 3 — the XL-block's content (charge-1 ask): size, not obstruction

Explore-agent sweep over runs/spec/docs: every "XL" occurrence near HE7A is a
campaign-sizing label — "XL: roughly 1,500–3,000 new Lean lines, 3–6 focused weeks, plus
unfinished F1/F2 prerequisites" (`LADDER_SUPPLY_2026-08-27.md:54`); the package leg was
never refuted (unlike old lb1/mp1/vartheta, each machine-refuted).  F1 (`BlockFrontier`
— sides/len from real block data, "residual Bézout Newton correction") is flagged
genuinely new mathematics in `BLOCKERS_PLAN_2026-08-26.md`.  Post-CEX the XL item is
scoped to exactly: discharge `IfaceExportedCore` (R1) and extend it to full strength (R2).

## The exported twins (owner-amendment targets; flagged, NOT enacted)

`HE7APackageLive C B Exported := ∃ I, Exported I` + anti-cook fence
`he7aPackageLive_top_iff` (at `Exported := True` it degenerates to exactly the signed
package — mirror of `lb1CarrierLive_top_iff`) + forgetting direction
`he7aPackage_of_live` · `HE7APackageExported C B` (the twin at the landed core — R1's
endpoint) · `lb1CarrierExported_of_partitionLegs` (E.57 partition legs for core-exported
triggering interfaces assemble LDR's `LB1CarrierLive` at `IfaceExportedCore B` — the
twin's `Exported` slot is no longer free).  Re-signing `LadderSupplyLive₃.package`/`.lb1`
to these twins is the owner amendment (LB1G "BLOCKED-BECAUSE" + the Finding-1
disclosure); nothing signed is touched here.

## The capstone `ladder` field's exact post-CEX boundary

`LadderFieldLive₃ n ↔ IFC0.LadderLB1Supplier n ∧ LadderVarthetaSupplierLive n`
(★ `ladderFieldLive₃_iff_lb1_vartheta`, machine-exact), and the second conjunct ⟸
`UniversalVarthetaSupplier` ⟸ deepTwist rows C3 + R5 (LDR §2).  So the field's open
content is now: **{lb1 supplier (behind R1/R2/R3), the deepTwist campaign's own rows}** —
the package leg is OFF the boundary.

## Files

* `leanfinal/Uniformity/ChapI/I10CExport.lean` — NEW (the unit's landing).
* `leanfinal/Uniformity/ChapI.lean` — one aggregator import line added.
* New statements flagged for standing review: `rungInterfaceSynth` (+ the Finding-1
  tautology disclosure on the signed `package` field), `SideOnBlock`,
  `IfaceExportedCore`, `RealizedRungInterfaceExport`, `HE7APackageLive`,
  `HE7APackageExported`.
