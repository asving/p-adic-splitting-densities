# Verdict LVS — live vartheta supplier mathematics and Lean surface

**Date:** 2026-08-28  
**Unit:** LVS  
**Overall verdict:** **PARTIAL: depth-two vacuity and all supplier/field bridges PROVED;
general canonical tau-residue export OPEN-LEMMA.**

Statement authority: `leanfinal/scratch/LVS_probe.lean` (new, zero `sorry`).  Mathematical
record: appended `[LVS 2026-08-28]` section in
`docs/in-progress/LADDER_SUPPLY_2026-08-27.md`.

## Claim ledger

| Brief item | Status | Exact result and landed citations |
|---|---|---|
| Read mandated sources | **PROVED** | Read in the required order: `I10LadderLive.lean`, `IFC5.lean`, `verdict_AI6E.md`, the full 915-line ladder-supply document, E.61's definition, the full `C130vw.lean`, and the full `IFC4.lean`; also read `[WLE]` in `GC13_WIRING_2026-08-27.md`. |
| Arithmetic at the landed depth-two witness | **PROVED** | `GaugeLive r i` is `1 <= i and i < r` (`Tower.gaugeLive_iff`, `C130k.lean:48-49`). Therefore `i >= 3` and `GaugeLive 2 i` are contradictory. Probe: `LVSProbe.vartheta_live_r_two_vacuous` (`LVS_probe.lean:31-40`) and `vartheta_live_of_realization_depth_two` (`:44-60`). |
| “The tooth is real only at r >= 4” | **PROVED** | The signed intersection is `3 <= i < r`, empty for `r <= 3`, first inhabited at `r=4,i=3`. General arithmetic follows from `gaugeLive_iff`; finite independent certificate: `verification/lvs_live_range_spot.py`. |
| What `VarthetaRes` demands at a live index | **PROVED** | E.61's socket is exactly D.62's `HVarthetaRes` at `(N,v i,rho i,q i)` (`E61.lean:145-157`); D.62 requires kernel membership of every vartheta word and equality of its ambient residue to an embedded `Kt`-unit (`D62.lean:81-85`). `GaugeFamilyViewEq` pins transported `N`, the dependent `(v i,rho i)` package, and `q i` to the same witness's normalizer/`levelHeight`/`canonicalResAt`/`u(i+1)` (`C130vw.lean:214-222`). |
| Exact per-level sufficient export | **PROVED (statement)** | `LVSProbe.VarthetaTauLevelExport` (`LVS_probe.lean:72-91`) is attached to explicit `X/eG` and the exact family view and contains only tau kernel membership plus embedded-`Kt` residue values. It contains neither `HVarthetaRes` nor `VarthetaRes`. |
| General `varthetaRes_of_live_of_exports` | **PROVED** | `LVSProbe.varthetaRes_of_live_of_exports` (`LVS_probe.lean:95-109`) applies landed `Gauge.hvarthetaRes_of_tau_letters` (`D62w.lean:94-120`) and E.61's constructor. Zero additional mathematics or hypothesis conversion. |
| WLE-style universal per-witness exporter shape | **PROVED (statement)** | `LVSProbe.VarthetaTauLiveExporter` (`LVS_probe.lean:114-129`) binds `core/A/X` before the site package and asks only at the exact signed range `3 <= j` plus `GaugeLive core.r j`. This mirrors `[WLE]`'s owner-attached design without its unrelated calculus/receiver fields. |
| Exact bridge to `LadderSupplyLive.vartheta` | **PROVED** | `LVSProbe.ladderSupplyLive_vartheta_of_exports` (`LVS_probe.lean:134-152`) unpacks the very witness in `CanonicalLadderLiveAt`, applies the exporter to the same `core/A/X/eG/hview/hgi`, and returns the exact signed conclusion (`I10LadderLive.lean:89-91`). |
| Full record constructor pin | **PROVED** | `LVSProbe.ladderSupplyLive_of_vartheta_exports` (`LVS_probe.lean:158-171`) installs the bridge as field four of `IFC5.LadderSupplyLive`, leaving `package/lb1/mp1` unchanged (`I10LadderLive.lean:80-91`). |
| General arising-realization tau export | **OPEN-LEMMA** | `LVS-CANONICAL-TAU-EXPORT`: inhabit `VarthetaTauLevelExport` for every explicit arising witness and every `3 <= j < core.r`. Current views identify `canonicalResAt` but provide no embedded-`Kt` residue law. The fixed-depth model is D62w's tau descent; the missing general-depth content is LS-V10/`OPEN-LETTERS`. |
| Derive the exporter from the present bare realization fields | **BLOCKED-BECAUSE** | CC-18 permits arbitrary canonical-read twists while preserving `ChainRealization` and `RealizedInput` (`twistNode`/`twistRealization`/`twistRealizedInput`, `C130s18.lean:407-465`). `canonicalResAt_twist` changes the live read (`:467-474`), and `embeddedValue_not_uniform` refutes a uniform embedded-value derivation (`:527-543`). A new source-faithful tower export is necessary. |
| Use IFC4's S2 mu3/Gentow tooth as the missing vartheta export | **BLOCKED-BECAUSE / INDEX MISMATCH** | IFC4's explicit wired input and ladder socket land (`IFC4.lean:176-199`), but its Gentow result concerns the separate `towerReadFamily`. Its own honesty pin proves the `3 <= j < 2` demand empty (`s2Wired_deep_demand_still_vacuous`, `IFC4.lean:384-398`). It supplies no live deep vartheta index or ambient canonical-residue embedding. |
| Treat the external S2 socket's whole field as vacuous from one known witness | **BLOCKED-BECAUSE / QUANTIFIER** | `CanonicalLadderLiveAt` existentially ranges over any realization matching the same socket (`I10LadderLive.lean:57-75`). The landed S2 witness has depth two, but no landed `LVS-DEPTH-RIGIDITY-S2` theorem says every matching witness does. Local explicit-witness vacuity is proved; the signed external field is closed by the general exporter unless such rigidity is separately proved. |
| Numeric spot-certificate | **PROVED** | `python3 verification/lvs_live_range_spot.py` exits 0 and enumerates `r=2 -> []`, `r=3 -> []`, `r=4 -> [3]`, through `r=8 -> [3,4,5,6,7]`. |

## Named open lemmas

1. **`LVS-CANONICAL-TAU-EXPORT`** — prove `VarthetaTauLiveExporter n`, equivalently the
   tau membership and embedded-unit fields at every arising witness's own live deep site.
2. **`LVS-TAU-WORD`** — generalize D62w's fixed-depth tau descent to an arbitrary arising
   `core.T`, factoring the tau cocycle into synchronized wrap/letter generators.
3. **`LVS-CANONICAL-LETTERS`** — prove the same witness's `canonicalResAt` sends those
   generators to embedded `Kt`-units.  `C130cr` supplies generator-read factorizations but not
   this general level-field embedding dictionary.
4. **`LVS-DEPTH-RIGIDITY-S2`** — optional: prove every realization matching the exact
   external S2 socket has `core.r = 2`; not required after the general exporter lands.

## Verification

Run from `leanfinal/`:

```text
timeout 580 ~/.elan/bin/lake env lean scratch/LVS_probe.lean
```

Result: exit `0`, zero warnings/sorries.  Footer footprints:

```text
vartheta_live_r_two_vacuous                  [propext, Quot.sound]
all other probe declarations                 [propext, Classical.choice, Quot.sound]
```

Numeric certificate, from repository root:

```text
python3 verification/lvs_live_range_spot.py
```

Result: exit `0`; final line
`PASS: depth 2 is empty; the first real tooth is r=4, i=3`.

No git commits.  No landed `.lean`, leanspec, or existing scratch file was edited.
