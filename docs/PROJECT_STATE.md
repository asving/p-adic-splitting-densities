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
* **`leanfinal/` (the campaign):** census **639 / 1236 signed names PROVED**, 390 carrier,
  194 unlanded, 5 conditional, 5 placeholder-body, 2 cite, 1 unresolved
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

## 4. The live frontier (what blocks what)

1. **The dv-graded engine** (one proof behind C.72 shadow-floor, C.52's legs incl. leg 1 =
   C.53's only remaining input, C.54): v1 assembled + numerically certified (floor law
   sharp, 4143/0, `verification/dv_ledger_cert.py`) but **NEEDS-REDESIGN** (Codex review,
   13 findings — `docs/in-progress/DV_GRADED_ENGINE_REVIEW_2026-08-23.md`). Two halves:
   the FLOOR engine and the **EXACT half**. **v2 DELIVERED (unit E2, 2026-08-24):**
   `DV_GRADED_ENGINE_V2_2026-08-24.md` — all 13 findings disposed (structural-recursion
   normal form, two-index weight, full conversion chain), honest PROVED/BLUEPRINT/OPEN
   statuses, and the exact-half adjudication = **CITE** (FGMN, J. Algebra 427 (2015):
   published Thm 2.8 polygon additivity + Cor 4.12(3) exact normalized residual
   multiplicativity; coexists with C.66, does not replace it). The gate-(b) cite
   `fgmn_dv_exact_mul` is DECLARED (allowlist → 7, commit 38e0153d). **C.131′ first-wave
   fleet RUNNING on codex (2026-08-24):** C131a (a′–c′ weight+product law), C131d (d′–e′
   hpure bridge+x-carry; polls C131a for `WT`), C131k (k′–l′ structural normal forms),
   C131p (p′–s′ conversion utilities), C131aa (aa′–ab′ exact-half locals) — relaunched on
   codex after the original Fable fleet died to API 529s before writing anything.
   **C.72 `shadow_floor` LANDED (2026-08-24, Fable unit C131w): signed statement
   byte-identical, Lean-core, no cite** — the engine's headline. Remaining in the plan:
   y′ (faithful band, in flight), ae′/af′ (budget↔locus closers, in flight); then the
   C.52/C.53/C.54 consumer chain fires.
2. **The tower-instantiation freeze** (types I.10a/I.10b, gives I.05/06/07 their domains —
   chapter I's critical path): v1 **NEEDS-REDESIGN** (swallowing trap + arising-linkage
   gap; findings in the doc's banner, `TOWER_INSTANTIATION_FREEZE_DRAFT_2026-08-20.md`).
   **v2 DELIVERED (unit F2, 2026-08-24):** `TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md`
   (D-TIF-4 carrier, non-swallowing residue design). **A-I.2 ENACTED (2026-08-24):** E.63
   re-signed to the live range `3 ≤ i < r`; I.10b + the `deepTwist` field carry the tower
   depth `r` and conclude at F3's `DeepTwistConjunctLive`. **The CC carrier plan is
   EXECUTED through CC-17 (2026-08-24, 18 of 19 nodes disposed; CC-18 in flight):**
   the S2 REPOSITORY realization is fully inhabited (`s2RepositoryRealization`,
   C130s17.lean), and everything still missing is ONE named bundle —
   **`S2SourceFrontier`** (the source-side MacLane model: `NodePointSource` instance,
   `FGMNSourceData`/`FGMNSourceLaws`, OPEN-DICT-2/4 compatibilities) — with conditional
   constructors proving the diagnosis exact: `S2SourceFrontier → ChainRealization →
   Nonempty (FGMNCalculus (2,1,5)) → RealizedInput` (no cite, Lean-core). U12's
   level-general audit says inhabiting it = formalizing the source MacLane valuation
   chain — the ONE remaining hard-math campaign on this path. CC-18 (in flight) lands
   the socket applications conditionally on the same bundle.
3. **The five exact-degree re-signs: DONE (amendment A-C.10, 2026-08-24)** — enacted in the
   leanspec (elaborates green) with per-stub annotations + the blueprint amendment entry;
   the re-signed C.64 is already PROVED (`C64.lean` `blockDeg_eq_resigned`, Lean-core).
   C.78 remains the lone unadjudicated exact-degree site (different shape).
4. **The §10 GENTOW2 supply chain** (C.99–C.106) + C.88/C.85: the gating `FGMNCalculus`
   field list is DELIVERED (unit U7, 2026-08-24 — `FGMNCALCULUS_FIELDLIST_2026-08-24.md`:
   type-checked candidate class, 16-consumer matrix, citation reconciliation, explicit
   OPEN dictionary obligations; rejects the unconditional `fgmn_calculus_exists` form).
   NEXT (orchestrator): author the C.92 cite from it, print-read first.
5. **C.123/C.124 gates** (q=2/q=3 executable rows): partial firing possible now —
   **Fable test unit on C.123 in flight.** C.126 (axiom census gate) waits on C.92/C.94.
6. **E.57** (mixed-node block split; `hpart : True` target FALSE as signed — needs the
   A-E.6 partition leg typed) and **C.78** (the FGMN block-decision existential; needs
   dv2-level probe instruments): dedicated hard units, unassigned.

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
| (archive) | all 2026-08-24 waves through CC-16/A-E.7 | DONE — details in docs/LOG.md + git log; every landing orchestrator-verified |
| GTA | GENTOW2 C.99–C.101 (codex, relaunched after silent Fable death) | RUNNING (runs/wave-b/out_GTA.log) |
| C131ae | C.131ae′–af′ budget↔locus closers (SONNET) | RUNNING (C131ae.lean at 45KB, finishing) |
| C78 | HARD: C.78 exact-degree adjudication (FABLE) | RUNNING (C78adj.lean at 43KB, verifying) |
| CC17 | **ACCEPTANCE GATE: full S2 ChainRealization + first non-vacuous FGMNCalculus instance** (codex HIGH) | RUNNING (runs/wave-b/out_CC17.log) |

## 7. Resume protocol (fresh agent)

Read this file whole → `git log --oneline -15` → the in-flight ledger (§6) → act on the
frontier (§4) top-down. The map of the repo is in the repo CLAUDE.md; the blueprint is
`blueprint/CHAP-*.md`; signed statements live in `leanspec/Leanspec/Chap*.lean`
(byte-frozen; re-signs only via recorded amendments); landed Lean in
`leanfinal/Uniformity/`. When a milestone lands: update §§2/4/6 here IN PLACE, append the
dated details to `docs/LOG.md`, commit both with the work.
