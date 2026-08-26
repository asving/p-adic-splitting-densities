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
* **`leanfinal/` (the campaign):** census **646 / 1239 signed names PROVED**, 419 carrier,
  161 unlanded, 5 conditional, 5 placeholder-body, 2 cite, 1 unresolved (2026-08-24 EOD)
  (`python3 spec/census_driver.py`); frontier 543/612 node-files
  (`python3 spec/frontier.py` — file-existence proxy, do NOT quote as progress).
  Chapters: B and H required-work done; F complete; G complete; D one gate open;
  E one hard node (E.57); **C carries ~145 of the unlanded names**; I is the capstone
  conditionality chapter (placeholders + owner-era gates now unblocked by the protocol).
* **The capstone chain (chapter I):** `CapstoneHypotheses n` (structure, landed as
  elaboration gate) → I.15–I.18 assembly → `UniformityStatement`. Honest status: the
  structure's `ladder`/`deepTwist` fields are guarded by the I.10a/I.10b sockets (bodies
  `True`, owed to the tower-instantiation freeze); `jd0`/`genhnBox2` placeholders and the
  `w1` debt are ruled open by A-I.1; five I-D12 `True` bodies (NS7Termination,
  WindowPinningAt, GenhnHEAt, GenhnTow1At, TypeOfFaithful) await their resolution passes.

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

1. **The packaging enactment (PK plan, U15's Route A)**: PK-1/2 IN FLIGHT (the carrier
   retype removing the machine-refuted fgmn legs); then PK-3..6 (factored `fgmnCalculusOf`,
   S2 re-wire, the leanspec I.10 socket-body re-sign, the ev/lf-free funnel). U15's scratch
   already elaborates the first non-vacuous UNCONDITIONAL `Nonempty (FGMNCalculus
   (s2DepthOne) 2 1 5)`. After PK: the I.10 sockets + the class discharge are non-vacuous,
   lifting the I.10 fire-ban → the four capstone-assembly theorems
   (`uniformity_of_capstoneHypotheses` among them) become mechanical projections.
2. **The μ₃ campaign** (DEC3 authoring the blueprint): the corrected-parameter (2,1,21)
   operators one level up, so the GENTOW consumer CONCLUSIONS fire at S2 depth 2.
   U15-adjudicated as ~20-30 nodes; NP-0's parameter-free-engine discovery should make
   most nodes reuse-with-numerals.
3. **The dv-engine: CLOSED.** C.72 (both halves), C.52 (`towerLocus_iff_budget` byte-
   identical), C.54(c)'s strict floor, af′/ag′ — all proved; C.53 wiring + the C123R feed
   in flight (UFEED). E.57: CLOSED (`block_split` under its blueprint name). Chapter D's
   gate: CLOSED (D68).
4. **Remaining chapter-C blockers** (DEC4 planning): the C.35 `BlockFrontier` 8-row family;
   general C.27's two mechanisms (norm↔resultant bridge + ramified level-1 exactness);
   RB3's two gaps (Hensel refinement; the upward height bridge). Held/adjudicated: C.100
   (OPEN-EVAL-ISO), C.102 + one_shape's htie (OPEN-LETTERS), peel_row_law (undesigned
   PeelLeg), hprev/hcop satisfiability at μ₃ (DEC3's decision).
5. **Chapter H's research step** H.116b4 (5 rows; DEC5 mapping it examples-first).
6. **Maintenance queues**: the SIMP consolidation map; the review queue for the owner (RQ);
   the roll-up wiring for the ~25 newest files (orchestrator, at the next quiet window).

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
| (archive) | everything through 2026-08-26 00:30 (the S2-source campaign, the GC-13 bridge N1-N7, the af′ chain, A-C.10..16/A-E.7/A-I.2 amendments, E.57 + D-gate + C.52/C.72 closures) | ALL DONE — LOG + git log; every landing orchestrator-verified |
| PK12 | PK-1/2: the ChainRealization retype + ripple (FABLE) | RUNNING |
| UFEED | af′ U-FEED + the C.53 wiring (SONNET) | RUNNING |
| DEC3 | the μ₃ campaign blueprint (FABLE) | RUNNING |
| DEC4 | the chain-blockers plan: BlockFrontier/C.27/RB3-gaps (FABLE) | RUNNING |
| DEC5 | H.116b4 examples-first map (FABLE) | RUNNING |
| RQ | the consolidated owner review queue (SONNET) | RUNNING |
| SIMP | the read-only simplification map (SONNET) | RUNNING |

## 7. Resume protocol (fresh agent)

Read this file whole → `git log --oneline -15` → the in-flight ledger (§6) → act on the
frontier (§4) top-down. The map of the repo is in the repo CLAUDE.md; the blueprint is
`blueprint/CHAP-*.md`; signed statements live in `leanspec/Leanspec/Chap*.lean`
(byte-frozen; re-signs only via recorded amendments); landed Lean in
`leanfinal/Uniformity/`. When a milestone lands: update §§2/4/6 here IN PLACE, append the
dated details to `docs/LOG.md`, commit both with the work.
