# Verdict LVT — enactment of the VAUD vartheta owner amendment

**Date:** 2026-08-28
**Unit:** LVT (enactment, supersession route)
**Verdict:** **ENACTED — six probe declarations promoted to production in NEW
`leanfinal/Uniformity/ChapI/IFC5.lean`; IFC0 byte-untouched as the tension record;
leanspec comment-level record added; owner rebinding of `CapstoneHypotheses.ladder`
deliberately NOT enacted (owner gate).**

## Route adjudication (step 2 of the charge)

**Chosen: (b) SUPERSESSION** — new file `IFC5.lean` promoting the probe's declarations;
IFC0's `LadderField`/`ladderField_iff_suppliers` byte-untouched. Rejected: (a) in-place
IFC0 edit per VAUD's diff. Reasons:

1. **Route (a) cannot compile alone.** IFC0's anti-drift pin
   (`example {n} (h : CapstoneHypotheses n) : LadderField n := h.ladder`, IFC0.lean:69-70)
   ties `LadderField` definitionally to `CapstoneHypotheses.ladder`, which returns E.24's
   unbounded `LadderSupply`. Applying VAUD's diff breaks the pin unless
   `CapstoneHypotheses.ladder` (SIGNED: leanspec NODE I.10, bodies re-signed at A-I.3) is
   simultaneously rebound — a capstone-field statement change, one of the two owner gates.
   The probe's own record: "An IFC0-only edit that pretends the old capstone field is
   definitionally unchanged would be false."
2. **House precedent (GCW-6).** IFC3 retired IFC0's `DeepGentowSupplier` as a campaign
   target with IFC0 byte-untouched as the tension record; IFC3's header and leanspec
   A-I.5 record the coordination rule "`IFC0.lean` untouched; corrected shapes route
   through supersession twins in this file's genre."
3. **Honesty invariant.** The refuted-as-guard-derivable unbounded target survives as a
   named record, not a silent rewrite.
4. **Zero downstream cost.** `LadderField` has no consumers outside `IFC0.lean`
   (orchestrator grep 2026-08-28, re-verified by this unit: only IFC3 header PROSE
   mentions the names).

## Landed (step 3)

`leanfinal/Uniformity/ChapI/IFC5.lean`, namespace `Uniformity.Density.IFC5`, import
`Uniformity.ChapI.IFC0` only. Verification:
`cd leanfinal && lake env lean Uniformity/ChapI/IFC5.lean` → **exit 0, zero `sorry`,
all 8 `#print axioms` exactly `[propext, Classical.choice, Quot.sound]`** (one printed
list line-wrapped; still Lean-core).

The six probe declarations, byte-shape (machine-diffed: the four `def`/`structure`
statement hunks are byte-IDENTICAL to `scratch/VAUD_probe.lean`; the two theorem proofs
are the probe's projection/constructor bodies verbatim), universes matched
(`CanonicalLadderLiveAt.{uG', uKt', uL'}` explicit; file-level `universe uW uG uKt uL`
gives the probe's `{uW, uG, uKt, uL}` orders elsewhere):

| # | Declaration | Role |
|---|---|---|
| 1 | `CanonicalLadderLiveAt` | live-index predicate: a realization witnessing the SAME external socket views (slot/block/gauge) with `GaugeLive core.r i` |
| 2 | `LadderVarthetaSupplierLive` | supplier 4′: `∀ i ≥ 3, CanonicalLadderLiveAt … n i → VarthetaRes … i` |
| 3 | `LadderSupplyLive` | repaired record; fields 1–3 byte-identical to E.24, only vartheta gains the live premise |
| 4 | `LadderFieldLive` | the repaired ladder field (VAUD's proposed capstone shape; NOT bound to `CapstoneHypotheses`) |
| 5 | `ladderFieldLive_iff_suppliers` | exact four-way split at the repaired target; suppliers 1–3 are IFC0's OWN, unchanged |
| 6 | `ladderFieldLive_of_suppliers` | assembly direction in consumable form |
| +7 | `ladderVarthetaSupplierLive_of_unbounded` | supersession pin: OLD unbounded supplier ⟹ NEW live one (range restriction only) |
| +8 | `ladderFieldLive_of_ladderField` | supersession pin at field level; converse (the refuted derivability) deliberately absent |

`IFC0.LadderVarthetaSupplier` / `IFC0.LadderField` are RETIRED AS CAMPAIGN TARGETS,
byte-frozen; `IFC5.LadderFieldLive` is the campaign target.

## Leanspec finding (step 4)

The unbounded demand **IS signed at the leanspec surface**: NODE I.10's `ladder` field
consumes E.24's `LadderSupply`, whose `vartheta` field is the unbounded `∀ i ≥ 3`
(consumption rule 2 of the ChapI header reaches it through E.61's `VarthetaRes` socket).
Therefore a comment-level dated record was added to `leanspec/Leanspec/ChapI.lean`
immediately after the A-I.5 state-update block (which had carried the VAUD finding as
"PROPOSED, owner-gated"): the LVT ENACTMENT RECORD — quoting the three machine
certificates (`gauge_view_offRange_kernel_replacement`, `vartheta_sitewise_negative`,
`s2_three_not_gaugeLive`), stating the supersession, and pinning that rebinding
`CapstoneHypotheses.ladder` to `LadderSupplyLive` remains OWNER-GATED and would be the
numbered amendment A-I.6. **NO signed statement, declaration, gate, or count changed**
(git diff: +20 insertions, 0 deletions, all inside the module docstring);
`cd leanspec && lake env lean Leanspec/ChapI.lean` re-run → exit 0, zero errors.

## Records written (steps 5–6)

- `docs/in-progress/LADDER_SUPPLY_2026-08-27.md`: `[LVT 2026-08-28]` section appended
  (route + reasons, decl table, leanspec finding, honest opens) + a two-line pointer at
  the top `[VAUD]` note.
- `docs/REVIEW_QUEUE_2026-08-26.md`: Tier 2 row added (newest-first, above A-I.5),
  labeled "VAUD-ϑ live-range (SUPERSESSION — no signed statement changed; …A-I.6
  owner-gated…)".

## Honest opens (unchanged by this unit)

- **Owner gate (would be A-I.6):** rebind `CapstoneHypotheses.ladder` to
  `LadderSupplyLive` (or move the live record into E.24). Until then the capstone field
  still demands the unbounded range.
- **LS-G0 (LB1) stop stands:** the landed S2 socket still feeds an independently
  quantified arbitrary `RungInterface`; owner decision (canonical vs realization-linked
  `I`) owed before any LB1 proof fleet.
- **LS-G1 (MP1) cite route REFUTED:** [GN15] Thm 2.3 / GMN Thm 2.11 cannot fill `hirr`
  at the divisibility-only trigger; owner repair of the MP1 trigger owed.
- **Package supplier (HE7A):** XL, blocked on F1/F2 prerequisites + the C-to-E
  `RungInterface` exporter.
- **Degree-2 non-vacuity:** no closed degree-two occurrence; first missing object is a
  depth-one `SplitNodePointSource` on `s2DepthOne`.
- **Vartheta mathematics:** `LadderVarthetaSupplierLive` is a typed target, not a proof;
  canonical residue descent at live indices (LS-V10) is the remaining content.

## Files delivered

- `leanfinal/Uniformity/ChapI/IFC5.lean` (NEW; not wired into any roll-up — orchestrator
  wires `Uniformity/ChapI.lean`)
- `leanspec/Leanspec/ChapI.lean` (comment-only LVT record, +20/-0)
- `docs/in-progress/LADDER_SUPPLY_2026-08-27.md` (`[LVT]` section + pointer)
- `docs/REVIEW_QUEUE_2026-08-26.md` (Tier 2 row)
- `runs/wave-b/verdict_LVT.md` (this file)

No commit was made. `IFC0.lean`, `scratch/VAUD_probe.lean`, and `C133mh3.lean` untouched
by LVT (the working-tree `M` on C133mh3 is the other unit's live edit).
