# Unit XSC verdict — cross-chapter sweep of UNLANDED signed names outside chapter C

Source: `python3 spec/census_driver.py` (2026-08-24), chapters B/D/E/F/G/H/I. B and F have
zero UNLANDED rows. Total UNLANDED outside C at start: **48** (D 7, E 3, G 7, H 22, I 9).

Four classes used below: **LANDED** (this unit landed it just now), **FALSE-POSITIVE**
(already landed; the census's line-regex tool misses it — auto-generated structure-field
projections, inductive constructors, or an inline `@[attr] def` on one line — verified by
`rg` against leanfinal), **DESIGN** (an explicit, already-adjudicated repo decision to leave
it unlanded — quoted below, not re-opened), **BLOCKED** (a genuinely missing object: another
chapter's obligation, an open research step, or a structure under a fire-ban).

## Chapter D (7 UNLANDED → 4 landed, 3 DESIGN)

| name | blueprint id | class | landed / blocker |
|---|---|---|---|
| `portWitness` | — | MECHANICAL | **LANDED** `leanfinal/Uniformity/ChapD/D68.lean:64` |
| `gradWitness` | — | MECHANICAL | **LANDED** `leanfinal/Uniformity/ChapD/D68.lean:82` |
| `certWitness` | — | MECHANICAL | **LANDED** `leanfinal/Uniformity/ChapD/D68.lean:88` |
| `certWitness_touched` | — | MECHANICAL | **LANDED** `leanfinal/Uniformity/ChapD/D68.lean:99` |
| `HVarthetaResVoided` | — | DESIGN | deliberately voided, not re-landed — D62.lean:80 verbatim: "the pre-A-D.2 existential form is `HVarthetaResVoided` (leanspec, VOID — not re-landed)" |
| `hvarthetaResVoided_iff` | — | DESIGN | same voided family (D-D12 refutation record; D63.lean:50 "any consumer instantiating `HVR` at `HVarthetaResVoided` is a defect") |
| `hvarthetaResVoided_of_exact_height` | D.63 | DESIGN | same voided family |

These four were D's "one gate open" (`docs/PROJECT_STATE.md` §2): D.68, the chapter's
census gate, owns the non-vacuity witnesses for `BoundaryReadPort` (D.37) and `CertFrame`
(D.46) by explicit routing in both of those files' TEETH notes ("gate content owned by
D.68"), but `D68.lean` did not exist yet. Transcribed verbatim from
`leanspec/Leanspec/ChapD.lean:1500-1533`; compiles axiom-clean.

## Chapter E (3 UNLANDED → 0 landed: 1 false-positive, 2 BLOCKED)

| name | blueprint id | class | landed / blocker |
|---|---|---|---|
| `ladderState_wf` | E.19 | FALSE-POSITIVE | already landed, `leanfinal/Uniformity/ChapE/E19.lean:127` as `@[reducible] def ladderState_wf ...` — the census's `DECL_RE` requires the decl keyword at line-start after only whitespace/known modifiers; an inline `@[attr]` prefix on the same line is invisible to it |
| `peel_row_law` | E.51 | BLOCKED | GC-13 placeholder `hpeel : True`; leanspec explicit: "A fleet agent must NOT prove E.51 while the placeholder is `True`: it would be vacuous" |
| `BlockSplitTarget` | E.57 | BLOCKED | needs GC-13 to type `hpart : Nonempty (PartitionLeg I)` against chapter C's partition record (C.63 `classSize_separable` / C.69 `classSize_supply`); leanspec explicit: "**NOT ASSERTED**" until that lands — matches the brief's own note that E.57's remainder is the E.22/23-genre instance bridge |

## Chapter G (7 UNLANDED → 0 landed: 6 false-positive, 1 DESIGN)

| name | blueprint id | class | landed / blocker |
|---|---|---|---|
| `CertFamily.m` | G.05a | FALSE-POSITIVE | auto-generated structure-field projection, `leanfinal/Uniformity/ChapG/G05.lean:37` (`structure CertFamily ... m : ℕ`) — census only scans explicit `def`/`theorem` lines, never derived field projections |
| `CubicFamilyIndex.sep` | G.62a | FALSE-POSITIVE | inductive constructor, `leanfinal/Uniformity/ChapG/G62.lean:79` |
| `CubicFamilyIndex.dbl` | G.62a | FALSE-POSITIVE | same file:80 |
| `CubicFamilyIndex.tierI` | G.62a | FALSE-POSITIVE | same file:81 |
| `CubicFamilyIndex.tierII` | G.62a | FALSE-POSITIVE | same file:82 |
| `CubicFamilyIndex.bTier` | G.62a | FALSE-POSITIVE | same file:83 |
| `depthSet_eq_iUnion_resStratum` | G.23b | DESIGN | blueprint `CHAP-G_base_cases_menus.md:5306` verbatim: "UNLANDED, true as stated. The union is genuinely a union but is not disjoint, so it cannot carry a count; and after §A-8 no consumer needs it" — kept as the chapter's one deliberately-visible open stub |

## Chapter H (22 UNLANDED → 0 landed: 17 false-positive/parser-artifact, 5 BLOCKED)

| name | blueprint id | class | landed / blocker |
|---|---|---|---|
| `CapBranch.ram` | H.88 | FALSE-POSITIVE | inductive constructor, `leanfinal/Uniformity/ChapH/H88.lean:42` |
| `CapBranch.twoSided` | H.88 | FALSE-POSITIVE | same |
| `CapBranch.und` | H.88 | FALSE-POSITIVE | same |
| `LeafE.ram` | H.91 | FALSE-POSITIVE | inductive constructor, `leanfinal/Uniformity/ChapH/H91.lean:56` |
| `LeafE.twoSided` | H.91 | FALSE-POSITIVE | same |
| `LeafE.splitEq` | H.91 | FALSE-POSITIVE | same |
| `LeafE.inert` | H.91 | FALSE-POSITIVE | same |
| `LeafE.splTail` | H.91 | FALSE-POSITIVE | same |
| `LeafE.und` | H.91 | FALSE-POSITIVE | same |
| `StageLeaf.ram` | H.73 | FALSE-POSITIVE | inductive constructor, `leanfinal/Uniformity/ChapH/H73.lean:54` |
| `StageLeaf.twoSided` | H.73 | FALSE-POSITIVE | same |
| `StageLeaf.inert` | H.73 | FALSE-POSITIVE | same |
| `inferInstance` (×5, leanspec lines 1290/1291/1450/1515/1516) | — | PARSER-ARTIFACT | not a signed name at all — the census's `example_target()` captured the generic term `inferInstance` from `example : DecidableEq X := inferInstance` retirement stubs; the real obligation is the `DecidableEq`/`Fintype` instance, auto-derived by the landed `deriving` clauses on `StageLeaf`/`CapBranch`/`LeafE` |
| `betaExtract_fiber_card` | H.116b | BLOCKED | research-open; `leanfinal/notes/H116B4_OUTLINE_2026-08-18.md:701`: "H.116b4 remains research-open, numerically certified, statement unchanged" |
| `planted_presentation_card` | — | BLOCKED | same H.116b research family (gauge-resultant count, `OM2_h116b_gauge_resultant.py`) |
| `uClusterNorm_rateSpecies` | H.30b/H.122 | BLOCKED | `leanfinal/notes/CLOSING_CHAIN_AH6_2026-08-16.md:13`: "BLOCKED — downstream of (iii)"; clause (iii) is `uCluster_beta_leg`, itself blocked on H.116b |
| `uCluster_beta_leg` | H.121d | BLOCKED | `leanfinal/notes/CLOSING_CHAIN_AH6_2026-08-16.md:12`: "RESCHEDULE: needs H.116b (`betaExtract_fiber_card`)" |
| `undecidedCount_le_uCluster` | H.123 | BLOCKED | needs the open mathematical amendment in `leanfinal/notes/BETA_ASSEMBLY_BLUEPRINT_2026-08-18.md` ("obstruction 2 of H.123") |

## Chapter I (9 UNLANDED → 0 landed: all DESIGN/BLOCKED, per brief's explicit instruction not to attempt)

| name | blueprint id | class | landed / blocker |
|---|---|---|---|
| `CapstoneHypotheses` | I.10 | DESIGN/BLOCKED | leanspec explicit: "THIS DECLARATION IS AN ELABORATION GATE, NOT A SIGNATURE — defect I-D7 ... no fleet agent may fire on I.10 until the owner re-signs the field list" (defect I-D13 now dominates); `leanfinal/Uniformity/ChapI/I10FreezeV2.lean` is the adjacent, explicitly off-limits file |
| `CanonicalLadderConfig` | I.10a | DESIGN/BLOCKED | signed body is `True` (also PLACEHOLDER-BODY); leanspec: "BLOCKED-UNTIL-RESOLUTION, and the block is on chapter C, not on this chapter... No fleet agent may fire on I.10" |
| `CanonicalDeepTwistConfig` | I.10b | DESIGN/BLOCKED | same fire-ban, consumes `CanonicalLadderConfig` |
| `axchkSelfTestAxiom` | — | DESIGN | deliberate self-test fixture for the AXCHK gate itself (a non-core axiom used to prove the gate rejects non-core axioms); leanspec: "declared and immediately fenced — nothing in this file or any other consumes it"; landing it in leanfinal would itself violate the repo's no-new-axiom policy |
| `axchkSelfTestConsumer` | — | DESIGN | paired self-test consumer of the above; same reasoning |
| `drainage_of_capstoneHypotheses` | I.15 | BLOCKED | proof body is a one-line projection (`(h n).a2`) — genuinely mechanical IF `CapstoneHypotheses` existed, but that structure is under the I.10 fire-ban above, so this cannot land without violating it |
| `decided_of_capstoneHypotheses` | I.16 | BLOCKED | same — one-line projection `(h n).a0 σ hσ`, blocked on `CapstoneHypotheses` |
| `uniformity_of_capstoneHypotheses` | I.16/I.17 | BLOCKED | same — term application of already-landed `UniformityStatement.ofDecided`, blocked on `CapstoneHypotheses` |
| `totalMassOne_of_capstoneHypotheses` | I.18 | BLOCKED | same — term application of already-landed `totalMassOne_of_drainage`, blocked on `CapstoneHypotheses` |

All four `_of_capstoneHypotheses` theorems' non-`CapstoneHypotheses` ingredients
(`DrainageAt`, `TotalMassOne`, `UniformityStatement`, `UniformityStatement.ofDecided`,
`totalMassOne_of_drainage`) are already landed in `leanfinal/Uniformity/Density/Statement.lean`
— the sole blocker is `CapstoneHypotheses` itself.

## Summary

| chapter | UNLANDED | LANDED (this unit) | FALSE-POSITIVE/PARSER-ARTIFACT | DESIGN | BLOCKED |
|---|---|---|---|---|---|
| D | 7 | 4 | 0 | 3 | 0 |
| E | 3 | 0 | 1 | 0 | 2 |
| G | 7 | 0 | 6 | 1 | 0 |
| H | 22 | 0 | 17 | 0 | 5 |
| I | 9 | 0 | 0 | 5 | 4 |
| **total** | **48** | **4** | **24** | **9** | **11** |

Re-running `python3 spec/census_driver.py` after this unit: chapter D's UNLANDED count drops
7 → 3 (exactly the three DESIGN-voided names); B/E/F/G/H/I census counts are otherwise
unchanged (as expected — false-positives and DESIGN/BLOCKED items are not lines this unit
touches).
