# PROJECT STATE — state-now (rewritten 2026-08-24; keep it this way)

**This file is the CURRENT STATE, not a history.** It is rewritten in place at every
milestone and must stay short enough to re-read in full before any orchestration decision.
Raw dated history: `docs/LOG.md` (append-only, started 2026-08-24) and
`docs/archive/PROJECT_STATE_pre-2026-08-24_ARCHIVE.md` (the old append-log, entries through
#112 — consult only for provenance). Resumability test applies: a fresh agent must be able
to continue from this file + the repo alone.

## 1. Goal and standing protocol

**GOAL:** prove the main theorem — the uniformity-in-`p` of splitting densities, the
`leanfinal/` capstone `UniformityStatement` via `uniformity_of_capstoneHypotheses` —
**COMPLETELY, modulo literature cites** (published results only, restricted to the
p-adic-densities and Montes-algorithm literature — Asvin's /goal, 2026-08-24; **his own
paper is never citable**). Target: all 1236 signed names disposed (proved / carrier-landed / cite),
capstone `#print axioms` = Lean core + the declared cites, no `sorry`, no vacuity.

**PROTOCOL (Asvin, 2026-08-24):** owner input is needed ONLY for literature-cite Lean
transcriptions, and only as a SECONDARY (non-blocking) check — `docs/CITE_REVIEW_LIST.md`
is his reading queue. Everything else — re-signs of refuted statements, field lists,
design decisions — proceeds autonomously under the **end-to-end-proof criterion**: a design
choice is right iff it leads to a completed proof. Honesty invariants unchanged: no fake
axioms, no `sorry`-shaped discharges, statements never weakened silently (re-signs are
recorded amendments), faithfulness entry per cite, `sorry`-free ≠ non-vacuous.

**FLEET:** Codex `codex exec -c model_reasoning_effort=high` for new math + blueprint
conversion; default effort for Lean transcription; Fable subagents allowed (API permitting).
Disciplines in force: commit-early ratchet; the ORCHESTRATOR wires roll-ups (never units);
per-file `lake env lean` (never bare `lake build` on this NFS box; roll-up targets like
`lake build Uniformity.ChapC` are fine); LANDED/SUPPLY/BLOCKED verdicts from every unit;
never pipe an output you need through head/tail; never trust a bare name-grep
(comment-strip or `#print axioms`).

## 2. What is proved (honest picture)

* **Legacy `lean/` project (untouched since 07/08):** the order-0 σ-keyed capstone
  `OM.RealInstanceV2.montes_unconditional` + wild wave 1 — machine-checked, Lean-core,
  conditional on `htameFE`/`hExhaust` as recorded there. Not this campaign's workstream.
* **`leanfinal/` (the campaign):** census **664 / 1237 signed names PROVED**, 487 carrier,
  72 unlanded, 6 conditional, 5 placeholder-body, 2 cite, 1 unresolved (2026-08-26 EOD,
  post-RSGN) (`python3 spec/census_driver.py`).
  Chapters: B and H required-work done; F complete; G complete; D one gate open;
  E one hard node (E.57); **C carries ~145 of the unlanded names**; I is the capstone
  conditionality chapter (placeholders + owner-era gates now unblocked by the protocol).
* **The capstone chain (chapter I) — ASSEMBLY LANDED (A-I.3 + RSGN, 2026-08-26).**
  All four assembly theorems (I.15–I.18: `drainage/decided/uniformity/totalMassOne
  _of_capstoneHypotheses`) are PROVED Lean-core in `leanfinal/Uniformity/ChapI/
  I10_I15_I18.lean`, with the I.10a/b sockets typed at C130s18's enacted carriers
  (ambient universe pinned to 0, disclosed; I-D13 lifted; non-swallowing fence
  machine-re-checked). Honest status: `CapstoneHypotheses n` is OPEN — no longer
  provably empty, NOT claimed inhabited. The full theorem = inhabiting it:
  `a0`/`a1` at n ≥ 3, the arising-configuration socket supply (S2 teeth landed
  conditional on `w : S2LevelOneThreshold` + `IsAdicComplete`), the `jd0`/`genhnBox2`
  placeholders + `w1` debt (A-I.1), and the five I-D12 `True` bodies (NS7Termination —
  the ready-to-declare C.94 cite — WindowPinningAt, GenhnHEAt, GenhnTow1At, TypeOfFaithful).

## 3. Trusted base (cites)

Declared-and-landed allowlist (SEVEN): `exists_slope_factorization`, `fgmn_residual_mul`,
`agnprw_termination`, `bBox1_cite`, `exists_dvDissection`, `fgmn_dvDissection_factor_eq`,
and NEW (2026-08-24) `fgmn_dv_exact_mul` (C66b — the engine's exact half; FGMN Thm 2.8 +
Cor 4.12(3), print-read verbatim, dictionary on the review list).
Pending authoring under the new protocol (each gets a faithfulness entry +
CITE_REVIEW_LIST row): **C.94** (AGNPRW Thm 5.6 termination — the A-C.6 redraft
`NS7TerminationStatementR` exists, machine-safe, ready to declare), **C.92**:
ADJUDICATED NOT-SIGNABLE (U7 + orchestrator, 2026-08-24) — `fgmn_calculus_exists` stays
UNDECLARED (Lean-core inhabitable per `C92_VACUITY`; no faithful unconditional statement
exists over a bare `DeepTower`); the GENTOW2 consumers stay conditional on the
`FGMNCalculus` hypothesis carrier, whose laws live IN the class (orchestrator decision on
U7 §9 Q8, end-to-end criterion); the discharge path is a future `FGMNChainRealization`
bridge (OPEN-DICT-1..4, U7 §8). U9 (codex HIGH) is adjudicating U7 §9 Q1–Q7 and drafting
the A-C.11 class-correction diff. Audit file: `docs/AXIOM_FAITHFULNESS.md`; standing log:
`lean/notes/SEMANTIC_AUDIT_LOG.md`.

## 4. The live frontier (what blocks what) — rewritten 2026-08-26

1. **The CapstoneHypotheses INHABITATION campaign (the new top item — RSGN closed the
   assembly gate 2026-08-26).** With I.15–I.18 landed, `UniformityStatement` reduces to
   inhabiting `CapstoneHypotheses n`. The named debts, in likely order of attack:
   (a) the five I-D12 `True` bodies — NS7Termination first (= the C.94 AGNPRW Thm 5.6
   cite, redraft `NS7TerminationStatementR` machine-safe and READY TO DECLARE per §3);
   (b) the arising-configuration socket supply beyond the landed S2 teeth (feeds from
   the μ₃ campaign, item 2); (c) `a0`/`a1` at n ≥ 3; (d) `jd0`/`genhnBox2` + the `w1`
   debt (A-I.1's ruling). NEXT CONCRETE STEP: a decomposer unit enumerating
   `CapstoneHypotheses`' full field list against the landed corpus (what each field
   needs, supplier chapter, sizing) — then fleet the suppliers.
2. **The μ₃ campaign — blueprint DELIVERED** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md`,
   DEC3R): 29 nodes wired to `fgmn_model_calculus_nonempty`, zero new packaging.
   OPEN-DICT-2 DECIDED: full-current clearing `e(μᵢ)α` (FGMN Def 3.12) — so `hprev` is
   source-faithfully impossible at u′=21. GATE before the fleet: TWO signed consumer
   amendments (unit AMND): the `2 ≤ f'` hprev fence, and the coordinated
   `chainNormBelow`/`thetaRatio` re-index (the source's n̂₂ = `towerNorm 1`; `chainNorm 2 21
   = keyAt 2` falsifies the strict degree premise as signed). In-construction open:
   OPEN-RP1-TRANSPORT (the μ₂ read realizes the ε-normalized coefficient of Defs 3.10/3.12-13).
3. **The dv-engine: FULLY CLOSED (2026-08-26).** C.72 (both halves), C.52
   (`towerLocus_iff_budget` byte-identical), C.54(c)'s strict floor, af′/ag′, AND the
   C.53 wiring: UFEED landed `towerLocus_fibration` UNCONDITIONAL at the leanspec signed
   shape (axiom→theorem, `C131uf.lean`) plus the non-drain witness `s2Witness` disposing
   verdict_C123R's named gap. E.57: CLOSED (`block_split` under its blueprint name).
   Chapter D's gate: CLOSED (D68).
4. **Remaining chapter-C blockers — plan DELIVERED** (`docs/in-progress/
   BLOCKERS_PLAN_2026-08-26.md`, DEC4R; probes 246 lines green in `scratch/DEC4_check.lean`).
   Ordering: (i) the probe-complete norm↔resultant bridge + shadow-linearity API —
   FIREABLE NOW (unit BW1); (ii) RB3 examples-first certificates → RB3 closure (only
   genuinely-new mechanism: the upward budget→dv2Hgt bridge); (iii) ramified level-1
   exactness (priced 285–485 lines, new completion-free mechanism); (iv) the one-slope
   dv-graded Hensel engine (the C.34/C.35 root) → `BlockFrontier` 8 rows unconditional;
   (v) arbitrary-C C.27 last. Held fence unchanged: C.100 (OPEN-EVAL-ISO), C.102 +
   one_shape's htie (OPEN-LETTERS), peel_row_law (undesigned PeelLeg), hprev/hcop → AMND.
5. **Chapter H's research step H.116b4 — map DELIVERED** (`docs/in-progress/
   H116B4_MAP_2026-08-26.md`, DEC5R; battery extended, ALL PASSED — mechanism found:
   children = 0 or #ker(Tₙ) by an affine obstruction class; aggregate pushforward uniform
   on support). Rows GR-1/2 (ghosts) + GR-3/3b (cofactor/Fit) FIREABLE from landed inputs
   (unit HW1); three research cores stay BLOCKED (restricted Smith; one-grade lifting over
   general complete DVRs; the uniform-pushforward induction). Node verdict unchanged:
   research-open, numerically certified.
6. **Maintenance queues**: the SIMP map is DELIVERED (`docs/in-progress/
   SIMPLIFICATION_MAP_2026-08-26.md` — two live risks flagged: C131af.lean:46-47
   dual-namespace open; the 4-way `slot_eq` collision) — enactment wave unscheduled;
   RQ DELIVERED (`docs/REVIEW_QUEUE_2026-08-26.md`, Asvin's queue); roll-up wiring DONE
   (2026-08-26: 57 files wired, all 8 targets + Leanspec.ChapI green; B86/G78 are
   roll-up CONSUMERS, never wire them — cycle). Wiring rule now: sorted import lists,
   append new nodes on landing.

## 5. Instruments and reusable assets

* **Probe frames** (build once, refute cheaply): `(s2Frame, L₀, g₀)` over ℤ_[2]
  (C35b/C61/C67 — labelled-but-not-x-pure witness); `(linFrame, linTower)` any-DVR
  (C53c — first `TowerDatum` value; `IsTestKey` witnessed); `(s2Tower, f₅)` (C80 —
  tower-borne, floor slack, `Squarefree` by descent). The q=2 collapse: `|K₁| = 2` makes
  any deg-1 nonzero-endpoint polynomial `X+1` (C80) — free residual identifications.
* **Landed key lemmas for re-use:** `blockFactor_eq_of_frontier` (maximality one-liner),
  `hasLabel_natDegree_eq_of_dvd` (the rider-form degree law), `card_res_ge` cluster
  (LocalData §5b), `div_modByMonic_unique` dev-computation pattern, `fullSide_block`
  (C.48 — the protected exact-degree shape).
* **Tools:** `spec/frontier.py`, `spec/census_driver.py` (+`signed_name_census.py`
  comment-stripping parser), `verification/dv_ledger_cert.py`.

## 6. In-flight ledger (update on every change)

| unit | what | status |
|---|---|---|
| (archive) | everything through 2026-08-26 (S2-source campaign, GC-13 bridge, af′ chain, amendments, E.57/D-gate/dv-engine closures, PK-1..7, RQ, UFEED, SIMP, EFF sweep GENTOW5+T2s5s6+W12) | ALL DONE — LOG + git log; every landing orchestrator-verified |
| RSGN | the leanspec I.10a/b socket re-sign → capstone assembly (FABLE) | DONE — A-I.3 enacted + ALL FOUR I.15–I.18 LANDED Lean-core; orchestrator re-verified both builds; committed |
| DEC3R | μ₃/Route-B blueprint (codex HIGH) | DONE — commit b5d16d0f; gates unit AMND |
| DEC4R | chain-blockers plan (codex HIGH) | DONE — commit 5755bc59; wave-1 = unit BW1 |
| DEC5R | H.116b4 examples-first map (codex HIGH) | DONE — commit 93c618b8; fireable rows = unit HW1 |
| AMND | the two DEC3R-mandated signed consumer amendments (hprev fence; chainNorm re-index) (codex HIGH) | QUEUED — auto-launch at the codex 22:26 reset via `runs/wave-b/launch_wave_20260826.sh` |
| CHFD | the CapstoneHypotheses field-list supply map (codex HIGH) | QUEUED — same launch |
| BW1 | BLOCKERS_PLAN wave 1: norm bridge + shadow linearity corpus landing | RUNNING (SONNET — reassigned from codex per Asvin 2026-08-26 evening) |
| HW1 | H116B4_MAP fireable rows GR-1/2 + GR-3/3b | RUNNING (SONNET — reassigned likewise) |
| MHENS | MATH: the dv-graded one-slope Hensel engine, the C.34/C.35 root (FABLE) | RUNNING |
| MBRIDGE | MATH: RB3's upward budget→dv2Hgt bridge, certificate-first (FABLE) | RUNNING |
| MSMITH | MATH: H.116b4 core I — restricted Smith identification (FABLE) | LAUNCH-PENDING (classifier storm; auto-retry scheduled) |
| MLIFT | MATH: H.116b4 cores II-a/II-b — one-grade lifting + pushforward induction (FABLE) | LAUNCH-PENDING (same retry) |
| MRAMX | MATH: completion-free ramified level-1 exactness (FABLE) | LAUNCH-PENDING (same retry) |
| EXPO | public exposition refresh (standing obligation at major milestones) | PENDING — after the CHFD map lands |

## 7. Resume protocol (fresh agent)

Read this file whole → `git log --oneline -15` → the in-flight ledger (§6) → act on the
frontier (§4) top-down. The map of the repo is in the repo CLAUDE.md; the blueprint is
`blueprint/CHAP-*.md`; signed statements live in `leanspec/Leanspec/Chap*.lean`
(byte-frozen; re-signs only via recorded amendments); landed Lean in
`leanfinal/Uniformity/`. When a milestone lands: update §§2/4/6 here IN PLACE, append the
dated details to `docs/LOG.md`, commit both with the work.
