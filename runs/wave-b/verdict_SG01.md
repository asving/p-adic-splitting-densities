# Verdict — unit SG01 (nodes SG-0 + SG-1): the corrected frontier CONSTRUCTED, the funnel FIRED

Date: 2026-08-25 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 rows SG-0/SG-1
(the FINAL nodes).  New file `leanfinal/Uniformity/ChapC/C130sg.lean` (26 declarations) +
the two SANCTIONED edits `C130s17.lean` (leg re-type + `LegacyFGMN` quarantine + funnel
arity) and `C130s18.lean` (`lf` threading through the S2 gate).  `lake env lean` exit 0 on
all three files, zero errors/warnings/`sorry`; ALL `#print axioms` rows Lean-core only
(C130sg: 25 rows exactly `[propext, Classical.choice, Quot.sound]`, 1 pure structure
axiom-free; C130s17: 46 rows; C130s18: 28 rows — all Lean-core subsets).  Cite ledger
EMPTY at all three files.  `lake build Uniformity.ChapC` and `lake build Uniformity.ChapI`
green (see Build results).  No commit.

## The SG-0 re-type (the sanctioned C130s17 edit, executed exactly as briefed)

FD01's machine refutation (`s2SourceLaws_depthTwo_unsatisfiable`) made the frontier's old
`fgmn`/`fgmnLaws` legs (depth-two typing) uninhabitable at the landed operators.  The legs
now read

```
fgmn     : FGMNSourceData  (s2FgmnAnchor h2 hq) (s2FgmnAnchorKeys h2 hq) 2 1 5
fgmnLaws : FGMNSourceLaws (s2FgmnAnchor h2 hq) (s2FgmnAnchorKeys h2 hq) 2 1 5 fgmn
```

where `s2FgmnAnchor`/`s2FgmnAnchorKeys` are byte-duplicates of C130fd0's
`s2DepthOne`/`s2DepthOneKeyChain` (duplication FORCED by the import direction — C130fd0
transitively imports C130s17), rfl-pinned in C130sg (`s2FgmnAnchor_eq_depthOne`,
`s2FgmnAnchorKeys_eq_depthOne`).  The refuted depth-two half became the quarantined
packaging premise `S2SourceFrontier.LegacyFGMN` (mirror of `LegacyEvaluation`, with the
FD-1 compat shapes), and `toChainRealization`/`calculusNonempty`/`realizedInput`/
`s2RealizedInput` gained the second premise `lf : S.LegacyFGMN`.  `LegacyEvaluation`'s
quarantine, `withLegacy`, the SF-4 tooth, and everything repository-side are UNTOUCHED.
C130s18's S2 gate theorems (`s2_ladder_socket_application`,
`s2_deepTwist_socket_application`, the refinement example,
`s2_arenaAgreement_not_uniform`) were re-premised at `(S, ev, lf)` — the sanctioned
"retyped premise" edit; the general-carrier §1–§3 and the non-swallowing audit §5 are
byte-untouched.

## SG-0 — the frontier field table

★★ `s2SplitNode h2 hq L w : SplitNodePointSource (S2DepthTwo) (FractionRing (Polynomial O))
(s2RepositoryRealization).receiver (s2RepositoryRealization).keys` — the FIRST inhabitant
of the split node — and ★★ `s2Frontier h2 hq L w : S2SourceFrontier h2 hq
(FractionRing (Polynomial O)) L`, both conditional on exactly ONE datum `w` (see STOP row).

| field | status | witness |
|---|---|---|
| `Point` / `Pt` / `point_exists` | FILLED | NP-0 `S2NPPoint`/`s2NPPt`/`s2NP_point_exists` |
| `coeffHom` / `coord` | FILLED | NP-0 `s2NPCoeffHom`/`s2NPCoord` (SF-4 probe pair, injective read) |
| `valueOn` + 4 value laws | FILLED | NP-0 `s2NPValueOn` (`[μ₁; Φ′ : 5]` at `i ≤ 1`, NV-6's `s2Hgt₂`-extension at `i ≥ 2`) + `s2NP_value_zero/mul/add_ge/add_eq` |
| `hgt` / `dig` | FILLED | NP-0 `s2NPHgt` (= `s2Hgt₁`/`s2Hgt₂`) / NP-3 `s2NPDig` (= `s2Dig₁`/`s2Dig₂`) |
| `pointHgt` / `pointDig` / `pointHgt_eval` | FILLED | NP-0 `s2NPPointHgt` (+ `rfl` eval law) / NP-3 `s2NPPointDig` |
| `slot_value` / `slot_digit` | FILLED | NP-0 `s2NP_slot_value` / NP-3 `s2NP_slot_digit` (both live levels) |
| 7 stage laws (`hgt_zero`…`dig_add`) | FILLED | SG-0 `interval_cases` fencing of the per-level banks: NV-1/NP-1 (`s2Hgt₁_*`, `s2Dig₁_*`) at `i = 1`, CC-6 (`s2Hgt₂_*`, `s2Dig₂_*`) at `i = 2` — the assembly NP-0 deferred to this node |
| `Full` / `lift` | FILLED | SG-0 `s2NPFull` (NP-1 `S2Full₁` / CC-6 `S2Full₂`); NP-1 `s2Lift₁` / CC-6 `s2Lift₂` |
| `thresholdZ` / `thresholdNat` / `threshold_nonneg` at `i = 2` | FILLED | NP-4's SOURCE FORMULA `LevelDatum.seam` (`EFF.HE6R1.18`, `T₂ = d_r·u`), numeral `5` by `seam_s2Tower` (pin `s2Frontier_thresholdZ_two`) |
| `thresholdZ` at `i = 1` | **STOP → PARAMETRIZED** | `w.T` — see the STOP row |
| `window` at `i = 2` | FILLED | NP-5 `s2_window_at_two` (`5 < 10 = d(Φ₂(ρ))`, computed, `≠ ⊤`) |
| `window` at `i = 1`, finiteness | FILLED | NP-0/NP-5 `s2NP_window_ne_top` |
| `window` at `i = 1`, strict | **STOP → PARAMETRIZED** | `w.T_lt_key` + NP-0 `s2NPPointHgt_keyAt_one` (`d(Φ₁(ρ)) = u₂ = 5`) |
| `ambientLetter` / `psi_root` | FILLED | NP-6 `s2AmbientLetter`/`s2_psi_root` |
| `key_value` | FILLED | NP-0 `s2NP_key_value` (gauge level 1, `= u₂`) |
| `canonicalRead` | FILLED | NP-7 `s2CanonicalRead` (generator regressions tie to NP-6's letters) |
| `arenaRead` / `towerRead` / `peelUnit` | FILLED | NP-8 `s2ArenaRead`/`s2TowerRead`/`s2PeelUnit` |
| frontier `hgt_two`/`dig_two`/`full_two` | FILLED, **all `rfl`** | the exact level-two table ties (re-exposed `s2Frontier_levelTwo_ties`) |
| frontier `fgmn`/`fgmnLaws` (re-typed, r = 1) | FILLED | FD-0 `s2SourceDataOne`/`s2SourceLawsOne` (all thirteen laws, named theorems) |
| frontier `grade_compat`/`letter_compat` | FILLED | FD-1's proofs (NP-0 `s2NPPointHgt_two` normalization pin; `map_one` at the forced letters) |

**The ONE STOP (named, exactly as the brief anticipated): the level-1 inherited threshold.**
The frontier's field list DOES demand it (`window` quantifies over `StageLive 2 ⊇ {1}`,
`thresholdZ`/`threshold_nonneg` read index 1).  NP-4 found NO source occurrence naming `T₁`
(level 1 is the base `KeyFrame`, no prior `LevelDatum`); NP-5 proved the necessary bound
`T₁ < 5` and refuted both landed avatars (`5 ≮ 5`, `10 ≮ 5`).  Per the no-invented-numeral
rule the datum is PARAMETRIZED: `C130sg.S2LevelOneThreshold` (`T : ℤ`, `Tnat : ℕ`, cast
dictionary, `T < 5`).  The parametrization is EXACT — necessity is a theorem
(`S2LevelOneThreshold.ofSplitNode`: every split node at the repository pair carries one,
via `key_value` + the strict window half).  DISCLOSURE (loud, in-file): the structure is
Lean-nonempty (anonymous tooth `⟨0, 0, rfl, _⟩`, deliberately unnamed) — the openness is a
FAITHFULNESS gap (which numeral EFF.T2.04's inherited `T₁` is), not an emptiness; no named
instance is landed.

## SG-1 — the funnel, fired end-to-end at the SG-0 frontier

Every stage is a named declaration at `S := s2Frontier h2 hq L w`, footprint exactly
`[propext, Classical.choice, Quot.sound]` (from `/tmp` elaboration log, row-by-row):

| stage | declaration | conditionality | footprint |
|---|---|---|---|
| 0 (frontier) | `s2Frontier` | `w` only | Lean-core |
| 1 | `s2FrontierChainRealization` (= `toChainRealization`) | `w`, `ev`, `lf` | Lean-core |
| 2 | `s2Frontier_calculusNonempty` (`Nonempty (FGMNCalculus (s2DepthTwo) 2 1 5)`) | `w`, `ev`, `lf` | Lean-core |
| 3 | `s2FrontierRealizedInput` (= `s2RealizedInput`, the `keyAt 2 + 1` occurrence at degree 4) | `w`, `ev`, `lf` + `IsAdicComplete` | Lean-core |
| 4a | `s2Frontier_ladder_socket` (the I.10a body) | `w`, `ev`, `lf` + `IsAdicComplete` | Lean-core |
| 4b | `s2Frontier_deepTwist_socket` (the I.10b body, depth pinned `r = 2`) | `w`, `ev`, `lf` + `IsAdicComplete` | Lean-core |

The two quarantined premises are REFUTED where the campaign said they are — both now
THEOREMS, not prose:

* ★ `s2Frontier_legacyEvaluation_isEmpty` — `IsEmpty ((s2Frontier …).LegacyEvaluation)`:
  U13's char-2 contradiction machine-transplanted against the CONCRETE node (`[Algebra Kt
  L]` forces `coeffHom 2 = 0` hence `pointHgt 2 x (C 2) = ⊤`, vs NP-0's landed `= 4`).
  CC-17's prose caveat is now machine-checked: the `ev` leg of the funnel is PROVABLY empty
  at S2, so stages 1–4 are true-but-packaging-shapes until the plan's SF-3 carrier ripple.
* ★ `s2LegacyFGMN_landed_empty` — no `LegacyFGMN` over ANY split frontier can read its
  operators as the landed `s2NormRes`/`S2KeyPoly` (FD-0's unsatisfiability, transplanted).
  Honest scope: conditional on those two operator readings; a genuinely-μ₃-level depth-two
  record (plan §5.2, nowhere landed) is NOT refuted — that is `lf`'s only honest
  inhabitation route.

**Honest bottom line.**  The S2 gate's non-vacuous content is now the `ev`/`lf`-free
frontier: a full `SplitNodePointSource` + `S2SourceFrontier` instance, inhabited modulo ONE
named faithfulness datum (`T₁`).  The funnel and both socket applications fire end-to-end
but remain vacuous at S2 in the PROVABLY-empty `ev` leg (and `lf` at the landed readings) —
no socket conclusion is claimed non-vacuously.  De-vacuifying them = SF-3 (re-type
`NodePointSource`/`ChainRealization` at the split ambient and at per-leg FGMN anchoring),
which is downstream design work, not this unit's row.

## Build results

* `lake env lean Uniformity/ChapC/C130s17.lean` — exit 0, 0 errors/warnings/sorry; 46
  axiom rows, all exactly Lean-core.
* `lake env lean Uniformity/ChapC/C130s18.lean` — exit 0, clean; 28 rows, Lean-core
  subsets (two rows `[propext, Quot.sound]`).
* `lake env lean Uniformity/ChapC/C130sg.lean` — exit 0, clean; 25 rows exactly
  `[propext, Classical.choice, Quot.sound]` + `S2LevelOneThreshold` axiom-free.
* `lake build Uniformity.ChapC.C130sg Uniformity.ChapC.C130fd0 Uniformity.ChapC
  Uniformity.ChapI` — **Build completed successfully (8898 jobs)**, zero errors: both
  required roll-ups (`Uniformity.ChapC`, `Uniformity.ChapI`) green, and C130fd0 (which
  opens the edited C130s17) rebuilt clean — no name collision from the SG-0 duplicates.
* C130s18's non-swallowing grep-tooth re-run post-edit: `sed -n '/SOCKET BODY
  [S]ECTION/,/NON-SWALLOWING AUDIT [S]ECTION/p' … | rg "hvartheta|HVartheta"` → empty
  (exit 1), as required.

## Files touched (sanction audit)

`leanfinal/Uniformity/ChapC/C130sg.lean` (NEW) · `C130s17.lean` (sanctioned: leg re-type
[SG-0 note], `s2FgmnAnchor`/`s2FgmnAnchorKeys`, `LegacyFGMN`, funnel arity, AxChk rows) ·
`C130s18.lean` (sanctioned: `lf` threading in §4/AuditS2 + docstring conditionality
update) · this verdict.  leanspec/ and roll-up import lists untouched; no other unit's
file touched; no commit.

**Flagged for human review** (trust boundary — new statements): `S2LevelOneThreshold` +
its disclosure tooth, `s2SplitNode`/`s2Frontier` instance statements,
`s2Frontier_legacyEvaluation_isEmpty`, `s2LegacyFGMN_landed_empty`,
`S2LevelOneThreshold.ofSplitNode`, the `LegacyFGMN` quarantine typing, and the retyped
`fgmn`/`fgmnLaws` field types in `S2SourceFrontier`.
