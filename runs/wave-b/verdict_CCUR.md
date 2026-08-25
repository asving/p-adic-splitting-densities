# Unit CCUR verdict — chapter-C THEOREM-KIND curation of every UNLANDED signed name

Source: `python3 spec/census_driver.py` (2026-08-25), chapter C section. **73 UNLANDED rows**
(not the ~35-45 estimated pre-sweep — DT2 already cleared the def/inductive-kind rows down
from 113→73 two sessions ago; all 73 remaining rows are `axiom`/`theorem`-kind except the 3
DT2 explicitly skipped and re-confirms below). Method: for each name, read its leanspec
docstring/NODE tag in `leanspec/Leanspec/ChapC.lean`, `rg` it (and its semantic siblings —
`blockFactor`, `composedKey`, `FGMNCalculus`, etc.) across the landed corpus (every
`ChapC/C1*.lean`/`C130*.lean`/`C131*.lean` file, the dv-engine v2 blueprint
`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md`, the GENTOW2 adjudication
`docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md`, every `*_BLOCKED_*.md`/`*_REFUTED*`
ledger under `ChapC/`, and `runs/wave-b/verdict_C123R.md`), and classify per the discipline in
`runs/wave-b/verdict_XSC.md` (adapted to this task's four-class scheme).

**Zero ARTIFACT-class rows.** Unlike chapters G/H, none of chapter C's 73 UNLANDED names are
inductive-constructor or structure-field parser noise — DT2's prior pass already removed the
def/inductive-kind rows, so every remaining name is a genuine `axiom` obligation (or one of
the 3 already-adjudicated non-axiom leftovers below).

## Summary

| class | count |
|---|---|
| READY | 10 (high-confidence) + 8 (moderate-confidence, flagged) |
| BLOCKED | 48 |
| DESIGN/HOLD | 7 |
| ARTIFACT | 0 |
| **total** | **73** |

Two chain-blockers dominate the BLOCKED count and are worth naming up front, because landing
either would cascade-unblock several other rows:

* **NODE C.27 `slot2_exact`** (the guarded/repaired form, not the refuted naked form) is the
  root of a 6-row chain: `ramLeg_dvd`(C.59) → `tier1_typeOf`(C.61) → {`tier1_typeOf_composed`
  (C.62), `classSize_separable`(C.63)} → {`composed_dictionary`, `classSize_supply`(C.69)}.
  No Lean proof of the repaired form exists yet; `leanfinal/Uniformity/ChapC/C27.lean` only
  proves the OLD (unguarded) form false. Landing it is a real, self-contained norm-computation
  task (all definitional inputs — `dv2Hgt`, `blockFactor`, `Algebra.norm` — are landed); it is
  not blocked on any further missing object, so it is the single highest-leverage target in
  the whole census, but it is genuine unattempted proof work, not a 30-60 min wrap.
* **`BlockFrontier`/`blockFactor_spec`** (NODE C.35): the maximal-labelled-divisor existence
  content. `leanfinal/Uniformity/ChapC/C35_BLOCKED_2026-08-20.md` names two missing
  mechanisms: (1) a dv-graded one-slope Hensel lift with residual Bézout — still fully open;
  (2) FGMN Thm 2.8 polygon additivity / purity-of-factors — **this half is now plausibly
  covered by the declared cite `fgmn_dv_exact_mul` (C66b, DECLARED 2026-08-24, i.e. AFTER
  this blocked-record was written)**, an update worth a dedicated re-check unit. Mechanism
  (1) alone remains the blocker for an 8-row family: `blockFactor_spec`,
  `exists_dv_residual_dissection`(C.34), `block_complement_notdvd`, `dv2Supp_translation`,
  `dv2ResPoly_radical_eq`, `dv2ResPoly_scalar`, `level2_peel`, `mult₂_readable`,
  `dv2_length_sum`, `dv2Pin_translation_interior`, `multiplicity_tie` (repaired form),
  `tie_pure_power` (repaired form) — all of them use `blockFactor L f`'s actual identity in
  their conclusion under a bare `BlockContext`, which is exactly the content `BlockFrontier`
  supplies and nothing else landed does.

## A. The dv-engine v1 foundational layer (§4-§6, before the tower; C.27-C.40)

| name | NODE | class | evidence |
|---|---|---|---|
| `slot2_exact` | C.27 | BLOCKED | `C27.lean` proves the OLD unguarded form FALSE (`slot2_exact_false`); the current leanspec's re-signed guarded form (`hx : IsPure X g F.h F.e₁` added, A-C.10) has **no proof attempt landed** — root of the ramLeg_dvd/tier1 chain, see summary |
| `ramLeg_dvd` | C.59 | BLOCKED | `C61_BLOCKED_2026-08-20.md`: needs C.27's cleared-value reads at π/X/F.key; `rg '^theorem ramLeg_dvd'` returns nothing |
| `exists_dv_residual_dissection` | C.34 | BLOCKED | `C34_BLOCKED_2026-08-18.md`: FRONTIER 1 (dv-graded one-slope Hensel) fully open; FRONTIER 2's purity-of-factors half now plausibly covered by declared `fgmn_dv_exact_mul` (post-dates the blocked record) — re-check candidate |
| `blockFactor_spec` | C.35 | BLOCKED | `C35_BLOCKED_2026-08-20.md`: reduces entirely to the missing `BlockFrontier` Prop (`blockFactor_spec_of_frontier` landed, consumes `BlockFrontier` alone) |
| `block_complement_notdvd` | C.36 | BLOCKED | same `BlockFrontier` chain (`C35_BLOCKED...md` names it a direct consumer); no `C36.lean` |
| `dv2Supp_translation` | C.37 | BLOCKED | same chain; no `C37.lean` |
| `dv2ResPoly_radical_eq` | C.38 | BLOCKED | conclusion compares `f` vs `blockFactor L f`'s dv2-residuals — needs `BlockFrontier`; no `C38.lean` (only the vocabulary cluster `C38a.lean` is landed) |
| `dv2ResPoly_scalar` | C.39 | BLOCKED | same chain; no `C39.lean` |
| `level2_peel` | C.40 | BLOCKED | `HX_SWEEP_2026-08-20.md` §7 registry: explicit BLOCKED member (same D-CARRY/`BlockFrontier` family); `C40.lean` exists but only carries `peel_once_of_squarefree` + commentary — "the signed `level2_peel` is absent by design" |

## B. The tower budget/floor cluster (§8 opening; C.51-C.58)

| name | NODE | class | evidence |
|---|---|---|---|
| `towerLocus_iff_budget` | C.52 | BLOCKED | `C52_BLOCKED_2026-08-18.md` + confirmed live 2026-08-25: needs the assembly of C.131ae′ (landed, `mem_towerLocus_of_budget`, `C131ae.lean`) **and** C.131af′ (locus⇒budget, the "reverse correspondence" — **not yet landed**, `docs/LOG.md`: "af′ reverse correspondence (C.53-sized, queued)"; no `C131af.lean` exists). Precisely named, actively-queued gap — not a deliberate hold, just not yet executed |
| `towerLocus_fibration` | C.53 | **READY** | `C53b.lean:733` `towerLocus_fibration_of_leg1` proves the **FULL signed conclusion** (docstring: "proves the FULL signed conclusion of C.53's `towerLocus_fibration`"), via a measure-preserving (not box-preserving) repair after leg 2 was refuted (`C53_LEG2_REFUTED_2026-08-20.md`). Landing = verify the hypothesis list matches the signed axiom exactly and wrap/rename. ~20-30 min |
| `towerLocus_node_floor` | C.54 | BLOCKED | `runs/wave-b/verdict_C123R.md` row 1: no `C54.lean`; `DV_GRADED_ENGINE_V2` §5 plans C.131ah′ for this, not yet landed |
| `towerLocus_node_floor_sharp` | C.54 | BLOCKED | same — needs C.131ai′ (CRT realization), not landed |
| `towerLocus_field_floor` | C.54 | BLOCKED | same — needs C.131aj′ (field floor, "not advertised as a floor-engine corollary" per the v2 doc), not landed |
| `towerLocus_depth3_floor` | C.55 | BLOCKED | same C.54/C.55 node-floor family, no `C55.lean` |
| `refine_invariants` | C.56 | **READY** | `RESCHEDULE_C56_2026-08-16.md`'s sole named blocker was `composedKey` (C.43) having no file — **`C43.lean` now exists** (landed since); no second blocker is recorded for this clause specifically. All inputs (`dv2SideSet`/`dv2ResPoly` C.38a, `IsTestKey` C.13, `k2DigitLift` C.56a) landed |
| `refine_kills` | C.56 | BLOCKED (moderate) | same note flags a SECOND blocker at general `μ₂`: "DEPENDS on §9's C.85 (`theta_dictionary`)" — but C.85's own docstring (later A-C.1 pass) instead lists `refine_kills` as an INPUT it consumes ("the grid leg is C.56's `refine_kills`, already signed"), i.e. the dependency direction in the 2026-08-16 note may be stale. Flag for a fresh 1-unit re-check rather than assuming either direction |
| `refine_bijection` | C.57 | BLOCKED (chain) | restates `refine_invariants`/`refine_kills`'s hypotheses as a bijection between `refineDom`/`refineCod`; batch with C.56 once that lands, not independently blocked |
| `refine_transported_event` | C.57 | BLOCKED (chain) | same — consumes `refine_kills`'s conclusion as a hypothesis directly |
| `window_band1` | C.58 | READY (moderate) | invariance of `dv2Pin`/`dv2Res` under `proj`-congruence below a band — same genre as the now-landed `C131y.shadow_faithful_band`/`dv2Res_add_deep` congruence-stability lemmas; no file yet, unattempted but plausible |
| `window_consultation` | C.58 | **READY** | pure `ℕ` arithmetic, **zero chapter-C vocabulary**: `(d N m w : ℕ) (hd:0<d)(hw:w<d)(hm:m<d*N)(hcong:m%d=w%d) : m ≤ d*(N-1)+w` — `omega`-shaped. ~10 min |

## C. Class-size and block-length (§7, C.59-C.70) — the ramLeg_dvd/BlockFrontier chains

| name | NODE | class | evidence |
|---|---|---|---|
| `tier1_typeOf` | C.61 | BLOCKED | `C61_BLOCKED_2026-08-20.md`: PROVED at `L.ℓ=1` (`tier1_typeOf_of_ell_one`, landed); at general `ℓ` reduces to ONE missing input, `ramLeg_dvd`(C.59) — "the instant C.59 lands, C.61 is one line" |
| `tier1_typeOf_composed` | C.62 | BLOCKED | same typeOf-singleton-with-e-leg shape as C.61, over `ComposedLabel`; inherits the same ram-divisibility gap (no `C62.lean`) |
| `classSize_separable` | C.63 | BLOCKED | `HX_SWEEP_2026-08-20.md` §2: one of only 3 chapter-C statements carrying the `hx` x-purity guard, alongside `tier1_typeOf`/`ramLeg_dvd` — same e-leg family, no `C63.lean` |
| `blockDeg_eq` | C.64 | **READY** | `C64.lean`: the naked form is REFUTED (`blockDegEq_false`); the **current leanspec text is already the re-signed, protected form** (riders `hlab`/`hdvd` present) and is **already PROVED** under a different name, `blockDeg_eq_resigned` (`(hasLabel_natDegree_eq_of_dvd L hπ hlab hdvd).1`). Landing = a one-line wrapper under the signed name. ~10 min |
| `mult₂_readable` | C.64 (companion) | BLOCKED | conclusion compares `f` vs `blockFactor L f`'s dv2-side data — `BlockFrontier` chain |
| `dv2_length_sum` | C.65 | BLOCKED | all three conjuncts reference `blockFactor L f` directly — `BlockFrontier` chain |
| `multiplicity_tie` | C.67 | BLOCKED | naked form REFUTED (`C67.lean` `multiplicityTie_false`); the repaired 3-conjunct leanspec form still has 2 of 3 conjuncts reading `blockFactor L f`'s identity (`mult₂ L f`, `IsDvPure F (blockFactor L f)...`) — same `BlockFrontier` chain, not floor-immune as first appeared |
| `dv2Pin_translation_interior` | C.68 | BLOCKED | conclusion explicitly contains `dv2Pin L Ψ (blockFactor L f) j` — `BlockFrontier` chain |
| `classSize_supply` | C.69 | BLOCKED | packages C.63+C.64+C.67 into one structure; C.64's piece is READY but C.63/C.67 are chain-blocked, so the bundle as a whole is BLOCKED until both land |
| `side_degree_conservation` | C.70 | **READY** | `HX_SWEEP_2026-08-20.md` §6.2: "EXPECTED TRUE... structurally immune" — conclusion is `dvSideLen = ℓ * (dvResPoly...).natDegree`, a floor-level identity that never mentions `blockFactor`; hypotheses are just `f.Monic`+`IsDvPure`, both landed (C.06/C.34/C.38a). Unattempted. ~30-45 min |

## D. The §6-tail carry-over (C.49, placed after §7)

| name | NODE | class | evidence |
|---|---|---|---|
| `composed_dictionary` | C.49 | BLOCKED | explicitly "consumes C.62" (`tier1_typeOf_composed`) per its own leanspec placement note — inherits C.62's ramLeg_dvd/C.27 chain |
| `level3_dead_at_mult2_three` | C.49 | **READY** | pure `ℕ` contradiction, zero chapter-C vocabulary: `hm:2≤mr, hjump:2≤ℓ₃*d₃, hL:mr*(ℓ₃*d₃)≤L, hLμ:L≤μ₂=3 ⊢ False` — `mr*(ℓ₃*d₃)≥4>3≥L` is `omega`-shaped. ~10 min |
| `tower_termination_instance` | C.49 | **READY** | pure `ℕ` induction, zero chapter-C vocabulary: a sequence with `a 0 ≤ 6`, `∀j, 4≤a j`, `∀j, 2*a(j+1)≤a j`, over a length-`J+1` window, forces `J=0` (halving floor≥4 vs a bound of 6 permits at most one step). Straightforward induction/`omega` combination. ~20-30 min |

## E. The shadow-read and partial-sides layer (§8, C.71-C.82)

C.71 (`theta`/`margin`), C.72 (`ShadowFloorStatement`/`ShadowFaithfulBandStatement`, both
proved in general via C.131w′/y′), C.73 (`IsXFree`, `devQ`), C.74 (`TouchCert`) are ALL landed
— this is the richest "just-unblocked" section in the census.

| name | NODE | class | evidence |
|---|---|---|---|
| `entry_band_faithful` | C.75 | **READY** | Its hypothesis `hm : m ≤ (μ₂-j)*T.E₂` implies `m < T.theta μ₂ j = (μ₂-j)*E₂+margin` (landed `TowerDatum.one_le_margin`/`.theta`, `C71.lean`), and its conclusion is **byte-identical in shape** to the now fully-general `Uniformity.Density.Tower.C131y.shadow_faithful_band` (`C131y.lean:559`). A direct, one-line-ish corollary. ~15-20 min |
| `shadow_attained_of_certificate` | C.74 family | **READY** | `TouchCert T hπ μ₂ j` unfolds to `dv2Hgt(shadowDev(f^μ₂,j) - dev(composedKey^μ₂,j)) = theta`; `dev_pow_self` (landed, C.52, used exactly this way in `C123r.lean:182/200`) gives `dev(composedKey^μ₂,j) = 0` for `j<μ₂`, which discharges both conjuncts via `sub_zero`. ~20 min |
| `shadow_persistence` | C.74 family | READY (moderate) | same "add a budget-floored perturbation, height/residual persist" genre as the landed `C131y.dv2Hgt_add_eq_left_of_lt`/`dv2Res_add_deep`; plausible but the `hbudget` hypothesis's exact fit is unverified — flag for a dedicated check, not a guaranteed one-liner |
| `shadow_not_sigma_function` | C.74 family | READY (harder) | an ∃-∃ statement needing TWO constructed witness pairs in `towerLocus T μ₂` (same/different `typeOf` with different/same `shadowDev`) — same genre as C.80's `f₅`/`s2Tower` probe construction, reusable frame, but needs fresh explicit polynomials, not a pure corollary |
| `partial_projection` | C.77(iii) | BLOCKED | naked form REFUTED (`C80.lean` `partialProjection_false`); current leanspec's repaired 2-conjunct form (Monic + implication) has **no landed proof** under any name — unattempted, not yet re-examined post-repair |
| `partial_block_decision` | C.78 | BLOCKED | `C78adj.lean`: **ADJUDICATED TRUE** at the `(s2Tower,f₅)` dv2-probe (exact 2⁶⁰ certificate, no cite); the UNIVERSAL Lean proof needs an order-2 factorization carrier (`FGMNCalculus`/`ChainRealization`, the CC-16 path) or a faithful order-2 cite — neither landed, named precisely in the file's own closing note |
| `tie_pure_power` | C.80 | BLOCKED | naked form REFUTED (`tiePurePower_false`); repaired single-conjunct form `mult₂ (T.levelDatum hπ) f = μ₂` still unfolds through `blockFactor` — same `BlockFrontier` chain as §C above, no proof landed |
| `partial_floor_and_datum` | C.76 | BLOCKED (unattempted) | level-1 statement (`KeyFrame`/no `TowerDatum`), needs the frame-opening hypothesis `hopen`; no `C76.lean`, not examined by any note found |
| `partial_frame_peel` | C.76 | BLOCKED (unattempted) | same file/section, no note found; docstring says clause (c) IS C.47 (already signed, re-export) but the standalone axiom itself is unexamined |
| `partial_mu2star_two_decision` | C.79 | BLOCKED (unattempted) | 5-branch case table (`Mu2TwoCase`) over `BlockContext`; no note found, no `C79.lean` |
| `cg_read` | C.81 | BLOCKED (unattempted) | needs `dv2Pin`/`complementConst` machinery (landed) but the right-endpoint identity itself is unexamined; no `C81.lean` |
| `block_budget` | C.82 | BLOCKED (unattempted) | explicitly "BUDGET half ONLY" per its own leanspec fence; a `Nat.card` counting identity over `towerLocus`, no `C82.lean`, unexamined |

## F. The GENTOW2 supply layer (§10, C.97-C.106) — fully adjudicated

All four remaining UNLANDED names here were explicitly adjudicated by units GSW/GTA/GTB/C106
(`docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md`, `runs/wave-b/verdict_{GSW,GTA,GTB,C106}.md`)
as HOLDS on named, cited FGMN-dictionary gaps — this is the task's own example class.

| name | NODE | class | evidence |
|---|---|---|---|
| `theta_letter_valued` | C.99 companion | DESIGN/HOLD | `GENTOW2_ADJUDICATION_2026-08-24.md:15`: "RE-SIGN (shape) + still BLOCKED (proof)... letter clause stays **OPEN-LETTERS**" |
| `gentow2_Bp` | C.100 | DESIGN/HOLD | ibid `:16`: "**HOLD (c)** — IS the B′ lemma itself; needs **OPEN-EVAL-ISO**... no honest antecedent short of the conclusion" |
| `gentow2_Bp_unit_iff` | C.100 | DESIGN/HOLD | same HOLD (the iff depends on the same blocked equality) |
| `letter_formula` | C.102 | DESIGN/HOLD | ibid `:18`: "**HOLD (c)** — needs the γ-dictionary (**OPEN-LETTERS**) + **OPEN-EVAL-ISO**" |

## G. The §9 "third stage" (C.84-C.96) — FGMNCalculus-scoped vs. shadow-machinery-only

C.84-C.91 all carry `[I : FGMNCalculus W e' f' u']` as a genuine (non-carried) hypothesis of
the theorem's own content — the same missing-bridge scope U7/U9 adjudicated for the GENTOW2
cluster (`docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md`). C.95/C.96 do NOT use
`FGMNCalculus` at all — they are pure `shadowDev`/`dev`/`towerLocus` statements and belong with
§E's now-unblocked machinery instead.

| name | NODE | class | evidence |
|---|---|---|---|
| `theta_dictionary` | C.85 | BLOCKED (chain) | consumes `refine_kills` (C.56) per its own docstring ("the grid leg is C.56's `refine_kills`, already signed") — chain, not independently blocked |
| `substitution_kills_level1` | C.86 | READY (moderate) | a LEVEL-1 statement (no `TowerDatum`, generic `IsKey φ`/`resPoly`/`npHgt`) — independent of the whole tower apparatus; looks like a Hensel-perturbation argument over already-landed order-0/1 B-chapter machinery, unattempted but self-contained |
| `tower_slot_exact` | C.88 | BLOCKED | genuine `FGMNCalculus`-native content (`Algebra.norm`, `I.ExactGrade`, `I.KP`) — same missing-bridge scope as the GENTOW2 cluster |
| `tower_lift` | C.88 | BLOCKED | same — `I.Rgr`/`I.ExactGrade` native |
| `GENTOW5W` | C.89 | DESIGN | the `𝒲` hypothesis-family carrier itself (a `def`, not an axiom) — DT2 already confirmed this out-of-scope per the FGMNCalculus carve-out; re-confirmed unchanged |
| `gentow5w_two` | C.89 | BLOCKED | `FGMNCalculus`-native, depth-2 instance of the same carrier |
| `gentow5w_one_shape` | C.89 | BLOCKED | `FGMNCalculus`-native, depth-1 instance |
| `gentow5_key_certificate` | C.90 | BLOCKED | `FGMNCalculus`-native; its own docstring flags clause (b) as "the BOOKED C.92 residual field" — C.92 is ADJUDICATED NOT-SIGNABLE (PROJECT_STATE §3), so this node inherits that same open dictionary |
| `gentow5_selffeed` | C.91 | **READY** | **no `FGMNCalculus`, no `KeyFrame`** — pure abstract statement over `P : ℕ→ℕ∞`/`hOnSide` (landed, `C98.lean`). A self-contained finite order/arithmetic argument. ~30-45 min |
| `cap_free` | C.95 | READY (moderate) | uses only `dev`/`shadowDev`/`TowerDatum` (all landed, §E); "development vanishes above declared degree" genre, similar to landed `dev_eq_zero_of_lt`-style lemmas |
| `attainment_certificate` | C.95 | READY (moderate) | pinned at `F.f₁=1`; uses only landed `dv2Hgt`/`shadowDev`/`TouchCert`/`theta` |
| `attainment_certificate'` | C.95 | READY (moderate) | the `F.f₁≥2` twin of the above — likely the same proof shape, batch together |
| `box1_attainment_if` | C.96 | READY (moderate) | `runs/wave-b/verdict_C123R.md` row 5 shows only a SPECIFIC numeric instantiation (FR5X negative control) is deferred; the general axiom itself uses only landed §E machinery and is otherwise unexamined |

## H. The HT-count layer (§11, C.107-C.122) — chapter H's supplier of record

| name | NODE | class | evidence |
|---|---|---|---|
| `ht_leaf_certified` | C.113(ii) | BLOCKED (unattempted) | `C113.lean` docstring: "This file lands clause (i) only... Clause (ii) (`ht_leaf_certified`...) [is future work]" — no note found beyond that |
| `ht_branch` | C.114 | BLOCKED | `C114.lean:105/533`: "the signed names `ht_branch`/`ht_global` are **neither proved nor declared here**... BLOCKED" — needs "the corpus's step-3 fiber [bijection]" (the booked B.37-B.40 weighted-grading construction, named at C.111); only degenerate one-node/empty-tree specializations are proved |
| `ht_global` | C.114 | BLOCKED | same — needs the same fiber-bijection engine, plus the κ₀-rule/distinctness machinery |
| `tower_cert_kernel` | C.119 | BLOCKED | `verdict_C123R.md` row 4: "C.119/C.120/C.122 (no such files)"; `find leanfinal -iname "*c119*"` → nothing |
| `tower_decidedAt` | C.120 | BLOCKED | same — no `C120.lean` |
| `exists_certifying_N` | C.121 | BLOCKED | no `C121.lean`; not named in the C123r deferral list but structurally identical (per-member `DecidedAt`/`Visible₂` existence), same unexamined family |
| `tower_cert_peel_path` | C.122 | BLOCKED | same as `tower_cert_kernel`/`_decidedAt`, no `C122.lean` |

## I. The isolated late items

| name | NODE | class | evidence |
|---|---|---|---|
| `lawBS2_pair_or_triple` | C.128 | BLOCKED | `leanfinal/notes/C128_PARTIAL_2026-08-16.md`: extensive partial landing (`C128.lean`/`C128b1.lean`/`C128b2.lean`, ~20 public declarations); the capstone needs (B1) a generic non-binomial wrap-seed identity for which **the source itself gives no exact formula** ("this file does not invent that missing formula", `C128b1.lean`'s own docstring) — a genuine research gap, not an assembly task, despite how much machinery now surrounds it |
| `DescentStep` | (struck) | DESIGN | DT2-confirmed: the A-C.1 draft is machine-refuted and struck in leanspec itself ("kept for the record and MUST NOT BE CONSUMED"); the A-C.6 redraft `DescentStepR` is already landed in `C94.lean`. Re-confirmed unchanged at current line numbers |
| `NS7TerminationStatement` | (struck) | DESIGN | same struck-draft family; `NS7TerminationStatementR` already landed in `C94.lean` |

## Ranked READY batches (next wave's launch list)

**Batch 1 — the theta/faithful-band corollaries (fastest, all reduce to already-landed
C131y/C71/C72/C52 machinery; each is a genuine near-one-liner).**
1. `entry_band_faithful` (C.75) — corollary of `C131y.shadow_faithful_band` + `TowerDatum.one_le_margin`.
2. `shadow_attained_of_certificate` (C.74 family) — `TouchCert` unfold + landed `dev_pow_self`.
3. `blockDeg_eq` (C.64) — wrap already-proved `blockDeg_eq_resigned` (`C64.lean`) under the signed name.
4. `towerLocus_fibration` (C.53) — wrap already-proved `towerLocus_fibration_of_leg1` (`C53b.lean`) under the signed name.

*Input inventory:* `C131y.lean` (`shadow_faithful_band`, `dv2Res_add_deep`), `C71.lean`
(`TowerDatum.theta`/`.margin`/`.one_le_margin`), `C52.lean` (`dev_pow_self`), `C74.lean`
(`TouchCert`), `C64.lean` (`blockDeg_eq_resigned`), `C53b.lean`
(`towerLocus_fibration_of_leg1`). No new math — pure wiring/renaming + hypothesis-implication
checks.

**Batch 2 — pure arithmetic, zero chapter-C vocabulary (trivial, no dependency reading needed).**
1. `window_consultation` (C.58) — `omega`-shaped ℕ inequality.
2. `level3_dead_at_mult2_three` (C.49) — `omega`-shaped ℕ contradiction.
3. `tower_termination_instance` (C.49) — ℕ induction on a halving-floor sequence.
4. `gentow5_selffeed` (C.91) — abstract order argument over landed `hOnSide` (C.98), no FGMNCalculus.

*Input inventory:* none beyond core Lean/mathlib `Nat`/`omega`/`induction`, plus `C98.lean`'s
`hOnSide` for item 4.

**Batch 3 — the now-composedKey-unblocked §7-tail/§8 family (real proof content, moderate size).**
1. `refine_invariants` (C.56) — `composedKey`(C.43)'s only recorded blocker is now cleared; land the theorem itself.
2. `side_degree_conservation` (C.70) — floor-level side-length identity, HX_SWEEP-confirmed immune to the D-CARRY defect.
3. `shadow_persistence` (C.74 family) — verify the `hbudget` fit against `C131y`'s add-deep lemmas.
4. `window_band1` (C.58) — congruence-stability of `dv2Pin`/`dv2Res`, same genre as `C131y`.

*Input inventory:* `C43.lean` (`composedKey`), `C38a.lean`/`C56a.lean` (`dv2SideSet`,
`k2DigitLift`), `C13.lean` (`IsTestKey`), `C34.lean`/`C35b.lean` (`dvSideLen`/`IsDvPure`),
`C131y.lean` (`dv2Hgt_add_eq_left_of_lt`, `dv2Res_add_deep`).

**Batch 4 — §9's non-FGMNCalculus shadow-machinery cluster (moderate confidence, batch as a
family since they likely share one proof shape).**
1. `cap_free` (C.95)
2. `attainment_certificate` (C.95)
3. `attainment_certificate'` (C.95, the `f₁≥2` twin of #2)
4. `box1_attainment_if` (C.96)

*Input inventory:* `C71.lean`-`C74.lean` (`theta`, `margin`, `shadowDev`, `dev`, `TouchCert`,
`IsXFree`), `C43.lean`/`C51.lean` (`composedKey`, `towerLocus`). All four use only this
already-landed §E machinery; #2/#3 are near-twins so batching them should roughly halve the
marginal cost of the second.

**Batch 5 (lower confidence, worth a scoping pass before committing an agent) —**
`substitution_kills_level1` (C.86, level-1/generic, independent of the tower apparatus),
`shadow_not_sigma_function` (needs two constructed witness pairs, reusable `s2Tower`/`f₅`-style
frame), `refine_bijection`+`refine_transported_event` (C.57, batch with `refine_kills` once
that lands).
