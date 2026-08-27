# VERDICT — unit GCW3 (node GCW-3 of GC13_WIRING_2026-08-27.md): the S2 re-assembly with
# the law-satisfying read → the FIRST `GentowWWindow` at an arising witness's OWN exports

**[GCW-3, 2026-08-27] · STATUS: LANDED, GREEN.**  New file
`leanfinal/Uniformity/ChapI/IFC4.lean` (433 lines, 23 declarations, Lean-core only).
Scratch authority: `leanfinal/scratch/GCW3_probe.lean` (the structure-update elaboration
+ the live-read computation, validated against IFC2 before IFC3's olean finished).
No existing file touched; no commits; no roll-up/leanspec edit.

## What landed (the charge's four steps)

1. **The read-1 witness, construction reused (not forked).**  NP-8's freedom
   parameterizes exactly the bare data field `SplitNodePointSource.towerRead` (no node or
   frontier law reads it — checked against C130k2/C130s17 field lists).  So the variant
   is a structure UPDATE: `s2SplitNodeWired := { s2SplitNode … with towerRead := 1 }`,
   `s2FrontierWired := { s2Frontier … with node := s2SplitNodeWired … }`; anti-drift pins
   `s2SplitNodeWired_inherits` (hgt/pointHgt/thresholdZ/arenaRead/peelUnit all `rfl`) and
   `s2FrontierWired_fgmn`.  The SG-1 funnel re-fires verbatim (stages 1/3/4a/4b:
   `s2FrontierWiredChainRealization`, `s2FrontierWiredRealizedInput`,
   `s2FrontierWired_ladder_socket`, `s2FrontierWired_deepTwist_socket`) — same exact
   conditionality as C130sg: `wT : S2LevelOneThreshold` + `IsAdicComplete`.
   P3 licence quoted verbatim in the module doc (GCW-0 F3 + IFC3's fence); the choice is
   made once, at the construction site, after the signing — exactly the licensed scope.
2. **`GC13Wiring` PROVED at the wired witness's own exports** — `s2Wired_gc13Wiring`:
   every gauge-live level, every `(N, q, φ)` (hence in particular the witness's own
   exported norm section/use height): the exported read is `1` by construction
   (`s2Wired_towerReadFamily_live`), the μ₃ FGMN read is the unit `1`
   (`IFC2.s2Mu3_read_eq_one`), receivers preserve it.
3. **The tooth fired** — ★★ `s2Wired_gentowWWindow_at_own_exports`: the law +
   C132sg3's UNCONDITIONAL `GENTOW5WCleared` (inside `IFC3.s2Mu3_gentowWWindow_of_wiring`)
   → `∃ w, GentowWWindow (arenaFamily X … j) (useHeightFamily X j) (towerReadFamily X j) w 1`
   at `X := s2FrontierWiredRealizedInput` — the blueprint's GCW-3 tooth, at the witness's
   own socket exports.  Bonus: ★★ `s2Wired_wiredGentowDemand_at_own_exports` fires the
   signed NODE I.10d demand (`WiredGentowDemand`, law ∧ full identity, same read) at the
   first honest site, receiver `id`.
4. **GCW-5 residue discharged at S2** — `s2Wired_gcw5_residue`: D.44's `s = 0` clause AND
   the `s > f' = 1` tail at the wired exports (projections of the full identity
   `s2Wired_gentowW_at_own_exports` through `IFC1.gentowW_iff_zero_window_tail`), as the
   blueprint predicted.  General instances remain supply obligations of the law record.

## Falsifier compliance (blueprint §3)

1. The discharge is at a witness whose read SATISFIES the signed law (constructed to,
   under P3); the landed zero-read witness stays refuted — IFC3's
   `s2_wiring_refuted_at_landed_exports` untouched, and the junk-range refutation is
   REPRODUCED at the new witness (`s2Wired_gc13Wiring_junk_refuted` — no swallowing).
2. Nothing quantifies `GentowW` over unconstrained reads.
3. `IFC2.s2_gentowW_of_read_one` is consumed ONLY in the position the blueprint's GCW-3
   row itself sanctions: as algebra applied to the exported read of the constructed
   witness; the supply claim rests on the witness + the law instance, documented in the
   module doc and at the use site (`s2Wired_gentowW`).

## Honesty (restated per charge)

* **Depth vacuity stands**: `r = 2` supplies NO `r ≥ 4` level —
  `s2Wired_deep_demand_still_vacuous` (`3 ≤ j < 2` empty); the deep SHAPE tooth
  (`DeepGentowSupplier`-ward) remains OPEN; GCW-6's mechanism (law-satisfying reads at
  construction) is rehearsed here, not discharged at depth.
* Conditionality unchanged: every S2 statement carries `wT` (the one open level-1
  threshold datum) + `IsAdicComplete`.
* Off the gauge-live range the exported read is the CC-11 junk `0`
  (`s2Wired_towerReadFamily_junk`); the law is FALSE there — disclosed, machine-pinned.
* All 23 statements NEW → review-flagged (standing queue, GCW3 rows).

## Validation (from `leanfinal/`)

```text
lake build Uniformity.ChapI.IFC3          # exit 0 (8912 jobs; fresh olean for the import)
lake env lean scratch/GCW3_probe.lean     # exit 0
lake env lean Uniformity/ChapI/IFC4.lean  # exit 0; no error/warning/sorry
```

## AxChk footer

`#print axioms` on ALL 23 declarations of `Uniformity.Density.IFC4` (footer of
`IFC4.lean`, run via `lake env lean Uniformity/ChapI/IFC4.lean`, 2026-08-27):

```text
23/23: depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean core only — zero `sorry`, zero new axiom, zero cite (in particular
`fgmn_dv_exact_mul` is NOT consumed; the μ₃ package C132sg2/sg3 and the NP/SG chain are
cite-free).  NEXT (per blueprint): GCW-4 (θ beyond `s = 1`), the `WleCleared` per-level
exporter for the universal wired supplier twin.
