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
2. **The tower-instantiation freeze** (types I.10a/I.10b, gives I.05/06/07 their domains —
   chapter I's critical path): v1 **NEEDS-REDESIGN** (swallowing trap + arising-linkage
   gap; findings in the doc's banner, `TOWER_INSTANTIATION_FREEZE_DRAFT_2026-08-20.md`).
   **v2 DELIVERED (unit F2, 2026-08-24):** `TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md`
   (D-TIF-4 carrier, non-swallowing residue design). **A-I.2 ENACTED (2026-08-24):** E.63
   re-signed to the live range `3 ≤ i < r`; I.10b + the `deepTwist` field carry the tower
   depth `r` and conclude at F3's `DeepTwistConjunctLive` (leanfinal `I10FreezeV2.lean`,
   wired). The sockets' bodies stay `True` — the C.130 layers were BLOCKED on a missing
   carrier (C130A/C130B verdicts; C130B refuted the freeze's all-integer exact-height
   demand with a counterexample — needs a Laurent normalizer). **The carrier is now
   DESIGNED (U11, 2026-08-24): layered `ChainRealization` over `DeepTower`,
   `CHAIN_CARRIER_DESIGN_2026-08-24.md`** — 19-node plan CC-0…CC-18 (CC-17/CC-18 are the
   serial acceptance gates that land the sockets; after CC-1/2, nodes CC-3/4/5/9/13 run
   parallel). This plan is ALSO the FGMNCalculus discharge path (CC-16:
   `ChainRealization → Nonempty FGMNCalculus`). NEXT: execute the CC plan.
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
| E2 | dv-engine v2 + exact-half adjudication (codex HIGH) | DONE 2026-08-24 (v2 delivered; verdict CITE) |
| F2 | freeze v2 (codex HIGH) | DONE 2026-08-24 (commit 241a997d) |
| FT | C.123 q=2 gate partial (fable test / API probe) | DONE 2026-08-24 (5 rows fired, 5 deferred; commit 241a997d) |
| A-C.10 | the five re-signs (orchestrator) | DONE 2026-08-24 |
| U7 | FGMNCalculus field list (codex HIGH) | DONE 2026-08-24 (`FGMNCALCULUS_FIELDLIST_2026-08-24.md`) |
| U8 | n=3 drainage math (codex HIGH) | DONE 2026-08-24 (`N3_DRAINAGE_PROOF_2026-08-24.md`: u_N ≤ q⁻ᴺ + q⁻⁵u_{N−3}, uniform incl. p=2,3) |
| C131a | C.131a′–c′ weight + product law (codex) | DONE 2026-08-24 — all 3 nodes LANDED (`C131a.lean`, orchestrator-verified Lean-core) |
| C131d | C.131d′–e′ hpure bridge + x-carry (codex) | DONE 2026-08-24 — both nodes LANDED (`C131d.lean`, reuses C131a's `WT`; orchestrator-verified Lean-core) |
| C131k | C.131k′–l′ structural normal forms (codex) | DONE 2026-08-24 — both nodes LANDED (`C131k.lean`, orchestrator-verified Lean-core) |
| C131p | C.131p′–s′ conversion utilities (codex) | DONE 2026-08-24 — all 4 nodes LANDED (`C131p.lean`, orchestrator-verified Lean-core) |
| C131aa | C.131aa′–ab′ exact-half locals (codex) | DONE 2026-08-24 — both nodes LANDED (`C131aa.lean`; orchestrator-verified Lean-core) |
| C131f | C.131f′–g′ export fence + composed-key floor (codex) | RUNNING (runs/wave-b/out_C131f.log) |
| C131m | C.131m′ paid-branch recursion + erasure (codex) | RUNNING (runs/wave-b/out_C131m.log) |
| C131t | C.131t′+x′ weight-to-height + strict exactness (codex) | RUNNING (runs/wave-b/out_C131t.log) |
| C131u | C.131u′–v′ DvAbove bridge + shadow discrepancy (codex) | RUNNING (runs/wave-b/out_C131u.log) |
| U9 | FGMN adjudication Q1–Q7 (codex HIGH) | DONE 2026-08-24 — all DECIDED; **A-C.11 ENACTED** (class body + Q6 C.100 re-sign, Leanspec.ChapC green) |
| F3 | I.10a/I.10b sockets vs freeze v2 (codex HIGH) | DONE 2026-08-24 — SUPPLY (`I10FreezeV2.lean` wired); **A-I.2 ENACTED** (E.63 live-range re-sign + I.10b `r` binder, both leanspecs green); sockets stay `True` pending C.130 layers |
| U10 | n=3 drainage blueprint (codex HIGH) | DONE 2026-08-24 — audit finding: **`DrainageAt 3` ALREADY UNCONDITIONAL** (`drainageAt_three`, H97b, Lean-core — orchestrator-verified); H.97's literal (1,1,0) sharpening = 2 BLUEPRINT nodes; Haar-null OPEN (not needed) |
| C131f | C.131f′–g′ (codex) | DONE 2026-08-24 — both LANDED (public fence + `WT K_T = E₂`; orchestrator-verified Lean-core) |
| C131m | C.131m′ (codex) | DONE 2026-08-24 — LANDED (`taggedOuterNF_erasure`; orchestrator-verified Lean-core) |
| C131t | C.131t′+x′ (codex) | DONE 2026-08-24 — both LANDED (orchestrator-verified Lean-core) |
| C131u | C.131u′–v′ (codex) | DONE 2026-08-24 — u′ LANDED; v′ was BLOCKED on m′ (now landed) → requeued as unit C131v |
| C131h | C.131h′–j′ division ledger F6–F8 (codex) | DONE 2026-08-24 — all 3 LANDED (orchestrator-verified Lean-core) |
| C130A | freeze layers C.130b/c + d/e (codex) | DONE 2026-08-24 — `stageDeg` landed; b–e BLOCKED on the missing key-chain/node-point carrier (→ U11) |
| C130B | freeze layer C.130f (codex) | DONE 2026-08-24 — 15 decls LANDED; exact-height law BLOCKED: freeze demand FALSE vs C.83 `towerNorm` truncation at (2,5,1); Laurent normalizer named (→ U11) |
| U11 | chain-realization carrier DESIGN (codex HIGH) | DONE 2026-08-24 — layered `ChainRealization` DECIDED (`CHAIN_CARRIER_DESIGN_2026-08-24.md`: signatures elaborate, S2 depth-2 key chain constructed in scratch, 19-node CC-plan); orchestrator-verified |
| CC01 | CC-0 core re-home + CC-1 carrier skeleton (FABLE) | DONE 2026-08-24 — both LANDED byte-faithfully (C130a/C130k; all builds green, orchestrator-verified) |
| CC02 | CC-2 S2 key bridge (FABLE) | RUNNING (→ C130s2.lean) |
| CC03 | CC-3 terminal maps (FABLE) | RUNNING (→ C130tr.lean) |
| CC04 | CC-4 Laurent solve (FABLE) | RUNNING (→ C130ln.lean) |
| CC05 | CC-5 stage source interface (FABLE) | RUNNING (→ C130st.lean) |
| C131v | C.131v′ retry post-m′ (FABLE probe) | RUNNING |
| C131ac | C.131ac′ exact powers (FABLE probe) | RUNNING |
| C131n | C.131n′–o′ recarry + census floor (FABLE) | RUNNING |
| C131ad | C.131ad′ box-monomial floor (FABLE) | RUNNING |

## 7. Resume protocol (fresh agent)

Read this file whole → `git log --oneline -15` → the in-flight ledger (§6) → act on the
frontier (§4) top-down. The map of the repo is in the repo CLAUDE.md; the blueprint is
`blueprint/CHAP-*.md`; signed statements live in `leanspec/Leanspec/Chap*.lean`
(byte-frozen; re-signs only via recorded amendments); landed Lean in
`leanfinal/Uniformity/`. When a milestone lands: update §§2/4/6 here IN PLACE, append the
dated details to `docs/LOG.md`, commit both with the work.
