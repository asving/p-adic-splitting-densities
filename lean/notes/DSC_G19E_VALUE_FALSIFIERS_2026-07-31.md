# IB-G19a VALUE-LEVEL FALSIFIERS — landing record (2026-07-31)

Unit IB-G19a, the three value-level falsifiers the G19c header left open after
the degenerate class closed (`SlotsG19c_degenFalsifiers.lean` /
`SlotsG19d_canonFalsifiers.lean`; H-phase fill record
`DSC_HPHASE_FILL_2026-07-31.md`).  Deliverable: NEW module
`lean/LeanUrat/MovesU/SlotsG19e_valueFalsifiers.lean` — **0 sorry, all
footprints Lean-core `[propext, Classical.choice, Quot.sound]`** (verified via
`#print axioms` scratch over the built module; footprint table in the module's
EOF comment).  `lake env lean` green per-file; `lake build
LeanUrat.MovesU.SlotsG19e_valueFalsifiers` green (8571 jobs; the only warning
attributed to the new file is the corpus-wide unscoped-`maxHeartbeats` style
note every sibling emits).

## What this unit certifies (the class G19c/G19d could not)

The canonical FILLED slots are FALSE at CONTENT-BEARING carriers with wrong
VALUES — nonempty events, positive cell mass, inhabited leg roster, the
degenerate escapes all closed — so each refutation is value-borne, and each
comes with a compiled certificate that the non-value legs HOLD at the carrier.

## The shared carrier (one site, one pack)

* `diracSite p : RelSite p` — the G2 BLOCKED record's junk site compiled as
  the promised falsifier witness (G14 R-7): δ = δrel = d = 1, continuation
  points = the F_p-digit atom `↥(Fsub p 1)` (p ≥ 2 points), FULL powerset event
  algebra, `cellMass = 1`, Dirac conditional `diracMass` at digit 0 (its
  finitely-additive laws proved; two-valuedness displayed at
  `diracMass_two_valued`).
* `wrongValuedData p Sp AD : SiteData p (diracSite p) Sp AD` — constant `Θ`,
  identity ambient trees vs CONSTANT target `tgtTcan` (non-constant composite),
  `vread` verdict readers separating the square's legs, `TgtRealizes ≡ True`
  (realization event = the full box event), β-table ≡ 2, `entryFirst = 0`.

## The falsifiers (all named lemmas, each with its carrier instance)

* **(F1) `sitedSlot_rel2b_refuted_at_diracSite`** — the inverted-Dirac pricing
  falsifier: ¬`SitedSlot_rel2b (diracSite p) SD CI` for EVERY data pack SD and
  EVERY CI — the `vol_cyl` field pins the level-1 cylinder at p⁻¹ ∉ {0, 1},
  which the two-valued Dirac conditional cannot meet.  Guard fires
  (`diracSite_cellMass_pos`), pullback is an event (`diracSite_events_total`):
  only the priced equality fails.  Instantiation witness at the compiled pack:
  `sitedSlot_rel2b_refuted_at_wrongValued`.
* **(F2) `sitedSlot_rel2d_refuted_at_wrongValued`** —
  ¬`SitedSlot_rel2d (diracSite p) (wrongValuedData p Sp AD)`: the square fails
  at the NON-constant composite (`wrongValued_composite_nonconstant`), and the
  break is verdict-visible ([true] vs [], `wrongValued_verdict_mismatch` — the
  proof routes the square through the verdict reader).  All non-square legs
  hold: `wrongValued_rel2d_nonsquare_legs`.
* **(F3) `sitedSlot_rel2e_refuted_at_betaTwo`** — the β ≡ 2 value falsifier
  (per the G19c-header assignment to rel2e): ¬`SitedSlot_rel2e` at EVERY
  `tableConv`, EVERY `consumed`, EVERY CI — β reads 2 where the certified
  BoxVol mass of the (full, realizable) realization event is `vol_univ`-pinned
  at 1.  The (e1)/(e4)/(e5) legs hold at the pinned non-degenerate exports
  (`tableConv := (· = 0)`, `consumed := {Tj}`):
  `wrongValued_rel2e_nonvalue_legs`.
* **(F3′, rel3 co-assignee) `sitedSlot_rel3_refuted_at_betaTwo`** — the ONE-LEG
  JUNK PACK (G17 header's named falsifier): singleton family `oneLegFam p`,
  assignment `oneLegAssign` carrying the β ≡ 2 pack (data/tgt transported to
  the singleton member; per-site `tableConv := (· = 0)`, `consumed := univ`),
  single-leg display pack `oneLegPack` — refutes `SitedSlot_rel3` through the
  per-leg certification VALUE, at every CI.  Population/coverage/keying/tie all
  hold: `oneLeg_rel3_nonvalue_legs`.  (The G3 record's junk-value arm,
  resurrected at the derived-not-free design exactly as P3 predicted: with no
  value field to junk, the wrong value must sit in the assignment's β-table —
  and the slot catches it.)

## M1 fence check (run before landing, grep-verified)

The negation targets are the FILLED, sorry-free canonical `SitedSlot_rel2b/2d/
2e/rel3` (H-phase fill 2026-07-31, Q5 ACCEPT).  The only sorries in the import
cone are the four UNTOUCHED G2 BLOCKED records (`Slot_rel2a/b/d/e` — unfilled
Prop DEFINITIONS, not statements these witnesses refute), exactly the
configuration the unit charge sanctions.  No probe-local copies were needed;
no existing file was touched.

## Notes for consumers

* The falsifiers quantify over `CI : CInterface …` — they hold against EVERY
  cylinder-pinned target (stronger than one concrete CI); a concrete inhabited
  `CInterface`/`BoxVol` instance (the REL.1 Haar construction) remains wave-D /
  REL.1-pass work, unchanged by this unit.
* `diracSite`/`wrongValuedData`/`oneLeg*` are falsifier vocabulary ONLY:
  nothing may consume them as evidence of content — they exist to make the
  slots' falsehood compiled, per the IB-G19a non-vacuity duty.
* Remaining at IB-G20 (unchanged): the closure-manifest drift flag between the
  G16/G17 headers, the G19b probes, and the G19c probe-local copies.
