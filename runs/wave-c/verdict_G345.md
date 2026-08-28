# VERDICT G345 — gates G3 (WLE per-level amendment) + G4 (shared deep-level export): ENACTED

Unit: G345 · Date: 2026-08-28 · Agent: Fable
Charge: DWC (`docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md`) §4.2/§4.3 + §6.1 rows
G3/G4 — promote the probe-validated WLE/TAU shapes into production as signing/review-grade
records, under the LVT/AI6E supersession discipline.
Statement authorities: `leanfinal/scratch/WLE_probe.lean` (WLEProbe.*),
`leanfinal/scratch/TAU_probe.lean` (TAUProbe.CanonicalGeneratorDescent), the [WLE] section
of `docs/in-progress/GC13_WIRING_2026-08-27.md`, DWR §11.4.

## VERDICT: ENACTED — one new production module, all gates green, NO leanspec change

New file: `leanfinal/Uniformity/ChapI/I10DeepExport.lean`
(namespace `Uniformity.Density.DeepExport`; 29 declarations, every one `#print axioms`
Lean-core; imports ONLY `Uniformity.ChapI.IFC4` — the WLE probe's exact import; acyclic
analysis in the module header).  Aggregator `leanfinal/Uniformity/ChapI.lean` +1 import
line.  Landed IFC1–IFC4/I10* files BYTE-FROZEN (untouched); both probes remain in scratch
as the design record.  No other file touched (concurrent units' C136* files untouched).

## G3 — the fixed-triple total family SUPERSEDED by a true site package

`WleClearedLevelExport X j hjr` RETYPED (machine-diffable; diff list in the module header):

| probe field | production field |
|---|---|
| `calculus : ∀ i, (hi : i ≤ core.r) → FGMNCalculus (core.T.trunc i hi) e' f' u'` (TOTAL fixed-triple family) | `calculus : FGMNCalculus (core.T.trunc j hjr) e' f' u'` (ONE site calculus) |
| `cleared : WleCleared core.T e' f' u' calculus j` (cumulative, only top member consumed) | `cleared : GENTOW5WCleared (core.T.trunc j hjr) e' f' u' calculus` (ONE top law) |
| every consumer `S.calculus j hjr` | `S.calculus` |

Everything else byte-identical to the probe: binders/universes, `f_pos : 0 < f'`, and the
own-export `IFC3.GC13Wiring` leg at the witness's own `useHeightFamily`/`towerReadFamily`/
`normalizer` and receiver `Aℛ.receiver.levelHom j`.  No off-site calculus is demanded to
inhabit the `j = 3` export; the two campaign calculi `(2,1,85)` at `j=3` and `(1,1,171)`
at `j=4` can now coexist per level.  Retyped in the SAME amendment (gate G3's rule):
`ThetaCompatibleAt`, `PeelCompatibleAt`, `RangeCompleteAt` (consumer laws, not fields),
and the wired assembly `wiredDemand_of_level_export` (proof ported; engine unchanged:
`IFC1.gentowWWindow_of_cleared_law` + `IFC1.gentowW_iff_zero_window_tail`; the receiver
identification enters only through `S.wiring.read_norm`).  Also landed:
`WleClearedPerLevelExporter` (probe shape), `UniversalWiredDeepGentowSupplier` (retyped
target def), and the indexed cumulative wrapper `WleClearedIndexed` (parameters AND
calculus level-indexed) with the supersession pins `wleClearedIndexed_of_fixed` /
`wleCleared_of_indexed_const` (landed `WleCleared` ↔ the wrapper at constant families)
and `WleClearedIndexed.at_level`.
Adapter from the old fixed-triple shape (the direction that holds):
`WleClearedLevelExport.ofFixedTriple` — total family + cumulative cleared + wiring at a
deep level ⟹ the site package.  The converse is false by design (recorded).

## G4 — ONE shared owner record; TAU and WLE dictionaries not designed separately

`DeepLevelExport X j (hj : DeepLive core.r j)` with exactly the three gate components:

1. `site : WleClearedLevelExport X j hj.2.le` — the corrected G3 calculus/wiring package
   (WLE dictionary projection `DeepLevelExport.wleExport`);
2. `descent : CanonicalGeneratorDescent Aℛ j hj.gaugeLive` — promoted BYTE-IDENTICALLY
   from `TAUProbe.CanonicalGeneratorDescent` together with `unitAlgebraMap`
   (machine-diffed: identical; docstrings aside) (TAU dictionary projection
   `DeepLevelExport.tauDictionary`);
3. `letter_receiver : ∀ a : Fin (j-1), algebraMap Kt L (Aℛ.receiver.levelHom j
   (site.calculus.letterZ (a.1 + 2))) = (Aℛ.node.letterValue Aℛ.normalizer _ a : L)` —
   the receiver/letter equality: the calculus letters through the SAME receiver used by
   the wiring leg and the SAME embedding used by the descent, tied to the canonical
   generator values.  **Letter-index decision (review flag)**: the pairing `Λ_a ↦
   letterZ (a.1 + 2)` follows the landed `letterClass` display
   (`Λ_a = Φ_{a+1}^{e_{a+2}}·n̂⁻¹`, stage-(a+2) data; C130cr) and the landed S2 template
   `C130s17.S2SourceFrontier.letter_compat`; inhabiting it is row R5 (OPEN-LETTERS).

Per the gate: the tau-word spanning theorem stays OUTSIDE the dictionary (future C3
consumer record), and the WLE theta/peel/range proofs remain consumer laws (hypotheses of
`wiredDemand`/`wiredDemand_of_level_export`, never fields).

What the promotions made FREE (landed):
* `letter_descent_of_receiver_eq` — the receiver/letter equality FORCES TAU's
  letter-descent clause (`Units.mk0` at the nonzero preimage), hence
  `DeepLevelExport.ofLetterEq`: site + wrap descent + letter equality suffice — the
  machine-checked justification that the two dictionaries belong in one record;
* `wiredDemand_of_level_export` at production types + `DeepLevelExport.wiredDemand`,
  `top_cleared`, `wiring` projections;
* `DeepLevelPerWitnessExporter` (DWR §11.4's exact exporter shape; inhabitants = rows
  C0/G10, OPEN) and `wleClearedPerLevelExporter_of_deep` (shared ⟹ WLE exporter);
* r=2/shallow teeth: `no_s2_deep_level` + `wleCleared_two_vacuous` promoted
  BYTE-IDENTICALLY from the WLE probe (machine-diffed), plus the new twins
  `wleClearedIndexed_two_vacuous` and `deepLevelPerWitnessExporter_of_shallow`
  (`core.r ≤ 3` ⟹ vacuous exporter — shallow witnesses, the landed S2 chain included,
  supply NO deep evidence; IFC4's S2 theorem stays a base/shape tooth).

E-universe note: the G4 records fix `E : Type` (Type 0), matching the TAU/LVS/IFC5
byte-shapes; the G3 package stays `E : Type uE`-polymorphic (WLE probe bytes) and is
consumed at `uE := 0` inside the shared record.

## leanspec CHECK — DEFAULT CONFIRMED: NO signed change (no A-I.9)

The deepTwist signed surface is untouched: NODES I.10c (`GC13Wiring`) and I.10d
(`WiredGentowDemand`) are CONSUMED byte-unchanged as field/conclusion types;
`CanonicalDeepTwistConfig`/`CapstoneHypotheses` are not mentioned; no name landed here
occurs in `leanspec/Leanspec/ChapI.lean`.  A-I.5's own BLOCKED-BECAUSE note already marks
the universal wired supplier as waiting on exactly this supplier-side "`WleCleared`
truncation exporter" — these are supplier-side interfaces BELOW the signed surface.
leanspec not rebuilt (untouched).

## Gates (all green, run from `leanfinal/`)

```text
timeout 580 lake env lean Uniformity/ChapI/I10DeepExport.lean   # exit 0; 0 errors/warnings/sorries
timeout 580 lake build Uniformity.ChapI                          # exit 0, 8953 jobs
  (one PRE-EXISTING style warning: chapter aggregators carry no copyright header — convention)
timeout 580 lake env lean scratch/WLE_probe.lean                 # exit 0; clean
timeout 580 lake env lean scratch/TAU_probe.lean                 # exit 0; clean
timeout 580 lake env lean scratch/LVS_probe.lean                 # exit 0; clean (adjacent record)
#print axioms (all 29 decls)                                     # ⊆ {propext, Classical.choice, Quot.sound}
byte-diff of cited promotions (unitAlgebraMap, CanonicalGeneratorDescent,
  no_s2_deep_level, wleCleared_two_vacuous)                      # IDENTICAL
```

## Downstream (unchanged obligations)

C0 inhabits `DeepLevelExport` at the exact `X`/`j=3` (needs D3-19, R5, R9); C1 the top
cleared law; C2 the theta/peel/range dictionaries; G10 the universal exporter half; the
r ≥ 4 wall and the OPEN-LETTERS core stand exactly as graded in DWR §11.5.  GCW-6/D-D12
fences inherited and restated in the module header; the review rows for the three NEW
STATEMENTS (`WleClearedLevelExport`, `WleClearedIndexed`, `DeepLevelExport` incl. the
letter-index pairing) go to the standing queue.
