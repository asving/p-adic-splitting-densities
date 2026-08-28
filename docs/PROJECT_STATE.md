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

**FLEET (weekly codex at 77%, 2026-08-28 — conserve: codex ONLY for the hardest math + adversarial verification; mechanical work to Fable/Sonnet):** Codex `codex exec -c model_reasoning_effort=high` for new math + blueprint
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
* **The capstone chain (chapter I) — ASSEMBLY LANDED (A-I.3 + RSGN, 2026-08-26);
  ladder field REBOUND (A-I.6, 2026-08-28).** All four assembly theorems (I.15–I.18)
  are PROVED Lean-core in `I10_I15_I18.lean` and stayed BYTE-UNCHANGED through A-I.6
  (the `ladder` field now demands `IFC5.LadderSupplyLive` — live-range vartheta — after
  AI6 machine-refuted the old unbounded field at n = 4; `AI6_probe.lean`, records in
  leanspec + REVIEW_QUEUE Tier 1). Honest status: `CapstoneHypotheses n` is OPEN — not
  provably empty (the n = 4 refuter targets only the RETIRED shape), NOT claimed
  inhabited. Remaining supply: the ladder live legs (LVS/REX in flight; mp1 may need
  A-I.7 — REX adjudicating), deepTwist deep (r ≥ 4) witnesses + the WLE exporter,
  `a0`/`a1` at n ≥ 3, `jd0`/`genhnBox2` + `w1` (A-I.1), and four I-D12 bodies
  (WindowPinningAt, GenhnHEAt, GenhnTow1At, TypeOfFaithful; NS7Termination CLOSED via
  A-I.4 + the declared `agnprw_termination` cite).
* **THE HENSEL ENGINE (F1.H0–H3) — COMPLETE (2026-08-28, ~48h wall-clock).** Theorem M
  (mixed residual law, all clauses, the root `m1TwistProductLaw` unconditional), the
  side lift Λ (R(Λ(P)) = P exact), Lemma S, Theorem A (`C133mh9.theoremA`, Lean-core,
  no cite), Theorems H0/B/C, and ★ `C133mh15.blockFrontier_of_context : BlockContext →
  BlockFrontier` (Lean core + the one allowlisted dissection cite). First payoff row
  landed (`C134cfs.blockFactor_spec` + 5 reads); F1.2–F1.8 await the CSX context-split
  exporter (in flight). The engine files: C133mh0–mh15, C133h0leg, C134cfs.
* **The μ₃/deepTwist S2 chain — CLOSED UNCONDITIONAL (2026-08-27/28).** The depth-2
  calculus `s2Mu3_calculus_nonempty` at (2,1,21); the signed GENTOW consumer
  `s2Mu3_gentow5w_two`; the GCW wired witness + the first `GentowWWindow` at own
  exports (IFC4); A-I.5 signed (GC13Wiring + WiredGentowDemand).

## 3. Trusted base (cites)

Declared-and-landed allowlist, SIX (2026-08-28, unit UNT — physically SIX, not just
effectively): `exists_slope_factorization`, `fgmn_residual_mul`, `agnprw_termination`,
`bBox1_cite`, `exists_dvDissection`, `fgmn_dvDissection_factor_eq`. `fgmn_dv_exact_mul`
(C66b) is **PHYSICALLY RETIRED 2026-08-28**: unit H0LEG proved it redundant
(`C133h0leg.fgmn_dv_exact_mul_full`, byte-identical, Lean-core) but the removal was
blocked by a textual import cycle (its sole consumer, `C131ac.lean:120`, sat inside the
theorem's own import foundation via `C130nv → C131ae → C131ac`); unit UNT untangled it
(`C130nv`'s one used `C131ae` lemma, `suppVal_add_eq_left_of_lt`, split verbatim into a
new `C131ac`-free file `C131ae0.lean`) and converted the `axiom` keyword to a `theorem`
in `C66b.lean` in place, statement bytes unchanged. `#print axioms` of the theorem and
every downstream consumer (`C131ac`'s pow chain, `C131ae`'s `mem_towerLocus_of_budget`)
now print Lean core only. Verdict: `runs/wave-c/verdict_UNT.md`.
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

## 4. The live frontier (what blocks what) — rewritten 2026-08-28 post-engine

1. **The CapstoneHypotheses INHABITATION campaign (top item).** `UniformityStatement`
   reduces to inhabiting `CapstoneHypotheses n` (post-A-I.6 shape). Named debts:
   (a) **ladder** — the live legs: LVS (live vartheta supplier; r = 2 possibly vacuous)
   and REX (recenter export + `MP1CarrierLive`; ★ may force A-I.7 since unrestricted
   MP1Carrier is REFUTED) — both in flight; LB1G's RESTRICT-ANYWAY design awaits
   enactment; the HE7APackage supplier stays XL-blocked;
   (b) **deepTwist** — the deep (r ≥ 4) arising-witness campaign + the WLE per-level
   exporter (design anchored; deep inhabitants open; WleCleared r=2 vacuity mapped);
   (c) `a0`/`a1` at n ≥ 3; (d) `jd0`/`genhnBox2` + `w1` (A-I.1); (e) four I-D12 bodies
   (WindowPinningAt, GenhnHEAt, GenhnTow1At, TypeOfFaithful). The CHFD supply map
   (docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md) is the field-by-field ledger.
2. **The Hensel engine: COMPLETE — payoff propagation is the open work.** F1.1 landed
   (C134cfs); F1.2–F1.8 await CSX (in flight); signed C.34 stays blocked (Theorem A's
   `D′ ∣ deg g` entry rider absent from its premises + no `hsep` supplier — needs its
   own adjudication). After CSX: sweep the C.34/C.35 downstream consumers.
3. **Maintenance/held**: the C130nv→C131ae import untangle (enables physical
   `fgmn_dv_exact_mul` removal); the SIMP map enactment wave (unscheduled); held fence
   unchanged: C.100 (OPEN-EVAL-ISO), C.102 + one_shape's htie (OPEN-LETTERS),
   peel_row_law, OPEN-RP1-TRANSPORT faithfulness legs, gentow2_A_supply's 4 inputs.
4. **Chapter-H research tails** (H.116b4, not capstone-blocking): Smith SMGR-I-COMB +
   SMGR-RSE (GR-7b-0R PROVED); lift MSF-GENRE (MSF j ≥ 3 REFUTED by a depth-6 secant),
   SR general, the GSP-n handle (GSP-n ⇒ U(n) proved; WASH-n at separated μ=2 families).
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
| (archive) | everything through 2026-08-28 ~00:00 — capstone assembly (I.15–I.18), the μ₃ campaign CLOSED UNCONDITIONAL (`s2Mu3_calculus_nonempty` at (2,1,21), C132kp6b + the signed GENTOW consumer `s2Mu3_gentow5w_two`, C132sg2/sg3), VAUD's three ladder negatives + MHG's Hensel-gate proofs, the GCW chain (A-I.5: GC13Wiring + WiredGentowDemand; the wired S2 witness + first GentowWWindow at own exports, IFC1–IFC4), FML1 lift tails (U4 unconditional/target-free), Hensel promotions MH.1-core (C133mh1), MH.8+X1 (C133mh8), and MH3's CHECKPOINT: Theorem M all three clauses + the cite payoff `fgmn_dv_exact_mul_of_twistLaw`, conditional on the ONE root `M1TwistProductLawStatement`; `m1DigitFaithful` unconditional (C133mh3) | ALL DONE — LOG + git log; every landing orchestrator-verified; pushed through a55fbd43 |
| MH3 FINAL | THE ENGINE ROOT PROVED (24d1051b) — `m1TwistProductLaw` unconditional; MH.1+MH.2+MH.3 CLOSED; `fgmn_dv_exact_mul_thm` = the cite's statement as a THEOREM (byte-identical modulo `0 < F.h`); retirement needs only the h=0 degenerate leg (C.05 dictionary); ALL THREE MHDISP GATES LANDED — the assembly fleet is UNFENCED | DONE |
| MH10 | Theorem H0 `dvResidualBezout` + uniqueness | DONE (1ebedc0c) — Sonnet existence (died twice to 529s) + orchestrator uniqueness; Lean-core; wired |
| MH4 | §3.5 M-monic corollary | DONE — C133mh4.lean (M₀ = u·sideDeg + the monic residual law, both unconditional; product-law-free per MHFIX) |
| MH11 | Theorem B `dv_oneSlope_split_unique` | DONE (f061b65c) — F1.H2 CLOSED unconditionally, zero carried hypotheses; ∃/∀-pin resolutions recorded |
| MH12 | §6.1 defect-vanishing + Gauss descent | DONE (3647cc6e) — the three primitives feeding MH.13; defect-vanishing proved symmetric/stronger |
| MH13 | Theorem C placement | DONE — theoremC_placement §2-verbatim (A-C.20 competitor shape byte-matched) + the reusable per-prime core, UNCONDITIONAL; proof strengthens §6.2 (Squarefree carried-unconsumed, statement unchanged); survived FOUR 529 deaths via increment-resume cycling |
| MH14T | §8 BlockFrontier modulo Theorem A | DONE (3c84fdbd) — residual_transport Lean-core + blockFrontier_of_context_of_theoremA (sole extra axiom: the allowlisted dissection cite); THE ENGINE'S GAP IS THEOREM A ALONE |
| MH5S | the §4.1 side lift + Lemma S prefix | DONE (79244661) — MH.5 CLOSED (R(Λ(P)) = P exactly, finiteness-free); MH.7 prefix proved; `LemmaSStatement` carried — the missing leg is M clause 3 ABOVE the support line (MH.9's obligation, the next engine math node) |
| AI6E | ENACT A-I.6 | DONE (367c47c7) — CapstoneHypotheses.ladder rebound to LadderSupplyLive (vartheta leg gains the live premise; all else byte-identical); I.15–I.18 BYTE-UNCHANGED and green (the machine certificate the off-range demand was never consumed); IFC0 frozen as the tension record; refuters preserved; leanspec A-I.6 record + Tier 1 review row |
| MH9M | Theorem A MATH-PROVED (af2f4732) — the above-line law + Lemma S discharge + the full assembly against the exact landed statements; NO math gap; 9 transcription nodes + 4 named transcription opens; 3188 checks ALL PASS |
| MH9L+MH15 | THE ENGINE COMPLETE (24c8b84f) — theoremA UNCONDITIONAL Lean-core (all 9 nodes, all 4 transcription opens closed); blockFrontier_of_context : BlockContext → BlockFrontier, no carried hypothesis, Lean core + the ONE dissection cite; F1.H0–H3 ALL LANDED |
| H0LEG | the h=0 leg + retirement | DONE (5686b2d0) — fgmn_dv_exact_mul_full BYTE-IDENTICAL to the axiom, Lean-core (the machine certificate); allowlist member 7 PROVED REDUNDANT (trusted base effectively SIX); physical removal queued behind the textual C130nv→C131ae import untangle |
| LVT | enact VAUD's vartheta owner amendment | DONE (a38c26af) — IFC5.lean supersession (six live-range decls + OLD⟹NEW pins); IFC0 byte-frozen tension record; leanspec comment record; `LadderFieldLive` is the ladder target; A-I.6 (CapstoneHypotheses.ladder rebinding) adjudication QUEUED for the codex wave |
| MH0A6 | MH.0a + MH.0c remainder + MH.6 (M4) | DONE (ae36c7a1) — C133mh0.lean, 7/7 Lean-core, every clause unweakened; MH.4 is the only small pre-assembly node left |
| (wave-c) | six codex sol-HIGH units 03:04–03:27 | ALL LANDED (ce301df1) — ★AI6: ¬CapstoneHypotheses 4 PROVED (probe orchestrator-re-verified) ⟹ A-I.6 REBIND FORCED, exact acyclic diff delivered; MP1R: unrestricted MP1Carrier FALSE (countermodel re-verified), blocker = the producer-side recenter export; LB1G: RESTRICT-ANYWAY + LB1CarrierLive designed; WLE: exporter designed-anchored, deep inhabitants open; SMGR: GR-7b-0R PROVED, I+/II+ partial (SMGR-I-COMB, SMGR-RSE named); MSF3: MSF j≥3 REFUTED-BY a depth-6 secant, MSF-GENRE is the open replacement, GSP-n ⇒ U(n), WASH-n for separated μ=2 families n≥5 |
| LVS | the live vartheta supplier | DONE (05f067b7) — r=2 vacuity PROVED; full bridge chain proved at statement level; ONE open lemma LVS-CANONICAL-TAU-EXPORT (the source-faithful tower export; CC-18 twist freedom blocks bare-field derivation); depth-rigidity quantifier caution recorded |
| REX | recenter export + funnel adjudication | DONE (05f067b7) — ★ REBOUND CAPSTONE REFUTED VIA MP1 at current bytes ⟹ A-I.7 FORCED; three-layer export design (GNCitePayload 1:1 with GN CM637 Thm 2.3, checked at the primary pdf) + four-step plan delivered |
| AI7E | ENACT A-I.7 | DONE (39e3ed55) — mp1 → MP1CarrierLive via LadderSupplyLive₂ (all else byte-identical); I.15–I.18 byte-unchanged; all gates orchestrator-re-run green; ladder supply now targets: package (XL), lb1 (advisory), S2-RECENTER-EXPORT, LVS-CANONICAL-TAU-EXPORT |
| CFS | the BlockFrontier family sweep | DONE (bbad3a22) — F1.1 head blockFactor_spec + 5 reads unconditional (Lean core + the dissection cite; recorded 0 < F.h binder); F1.2–F1.8 blocked on ONE exporter |
| CSX | the context-split exporter | DONE (5f11bd2e) — context_split re-exports f = blockFactor·g₂·Wf with the F-row clauses; Lean core + the dissection cite |
| FRT | F1.2 partial | DONE (00e397a5) — quotient bridge + clauses 1/3; clause-2 block DISSENTED by the orchestrator (the mixed law needs no purity) |
| F12C | F1.2 + F1.7 | DONE (54025c36) — dissent confirmed; the transport Lean-core; F1.3–F1.6 reduced to two level-2 subgoals |
| DV2G | the two gate subgoals | DONE (62fd7a95) — both frame-generic Lean-core + the byte-exact F1.3 carrier; F1.3–F1.6 hang on P1 (test-key⟹mu-key), P2 (¬MuDvd bridge), P3 (signed-floor fence gap, owner row) |
| P1U | P1/P2/P3 | DONE (e91d3b4f) — P2 LANDED (C134p1, 3/3 Lean-core); P1 CITE-GRADE (GN Lemma 3.1(3)), declaration withheld pending the C.13-representative dictionary; P3 amendment FORCED (A-C.22 draft delivered) |
| TAU | the tau export mechanism | DONE (419350a4) — CanonicalTauLiveSource companion + CanonicalGeneratorDescent dictionary; conversion to VarthetaRes proved; deep witnesses must supply the dictionary |
| SRX | S2 recenter export | DONE (419350a4) — NOT constructible at S2 (MP1StepCore universally empty at μ=1 ⟹ mp1-live VACUOUS there, mirroring vartheta r=2); g₈.s key math landed; GNCitePayload surface gaps named |
| DWC | the deep witness blueprint | DONE — GO: S2 → depth 4 via g₈ (μ4 (2,1,85) + μ5 refinement (1,1,171)); 69 nodes, 10 gates, risk node C4; cert passes (orchestrator re-ran) |
| DWV | the blueprint adversarial read | DONE (e91d3b4f) — REJECT: TWO CRITICAL errors in the leaf² mp1 input (hkeyfree self-coprimality; ord_ψ = 2 vs GN.s multiplicity-one) + 5 gaps (3 missing gates, no occurrence→universal quantifier gate, research nodes mislabeled); tower numerics independently CONFIRMED — the DWR revision gates the fleet |
| A22E | enact A-C.22 | DONE (d9af7106) — four floors re-signed engine-honest, conclusions byte-unchanged; scope fence recorded (C.65/C.68/C.118 untouched with reasons); review row placed |
| C93T | the C93Census manifest | DONE (97ee96c0) — 4/7 verbatim (incl. a caught stale-name trap: the bare-name match was a refuted carrier), 1/7 half, 2/7 honest blocks (one census annotation REFUTED — review finding) |
| TSTK | carrier rows T1–T5 | DONE (fef6aa98) — the depth-4 tower datum STANDS (s2WitnessFour, pure data per Gate 10); g8.s key proof + depth-3 KeyChain; both normalizer pins; planned deferrals recorded; the rfl-timeout fleet lesson |
| L2E0 | the engine roots | DONE — L2E-00/01/02 landed S2-free at arbitrary LevelDatum (8/8 Lean-core); wired |
| L2E1 | L2E-03/04/05 | DONE — 03+05 landed + dv2Res_mul (NO root factor); the L2E-00 twist shape a MIS-TRANSPOSITION (the normalized read.s carry cancels by construction — the τ=1 story one level up); corrected shapes → L2E2 |
| L2E2 | corrected shapes + L2E-06/07/08 | DONE (2daa5ca7) — the clean normalized law + the FULL side bank incl. F13A.s reverse inequality; the carry confined to the absolute read |
| L2E3 | the engine closer | DONE (2ade1f6e) — ★ SIGNED F1.6 LANDS; the F1.5 adapter ready; TWO findings: F1.4.s signed scalar carries the rejected root factor (A-C.24 candidate); the D3 legs need a depth-3 datum adapter |
| A24A | F1.4 adjudication | DONE (91c96848) — the signed root power CONFIRMED unsuppliable (the signer transposed the source.s ANCHORED-read cocycle onto the bare carrier) AND the drafted γg-alone repair ALSO refuted (the off-side junk channel; scalar-generic digit-kill landed); fork → A-C.24′ = repair the C.38a carrier (guarded/anchored R₂); one open risk → battery |
| A24B | battery + carrier | DONE (dea24337) — the anchor risk REAL (135/135 events) and absorbed by the anchored dv2FullRead (unconditional stability theorem); the carrier landed 15/15 Lean-core; the A-C.24′ draft machine-ripple-free |
| A24E | enact A-C.24′ | DONE — the anchored carrier signed (C.38a′ + the re-signs, source-faithful scalar); F1.4/F1.5 stay open on TWO named legs (the anchored digit-split assembly + the carry law) |
| D3AD | the depth-3 adapter | DONE (4eb8daa0) — D3-03 DISCHARGED unconditional (the cheap survival-core mirror; the engine.s root not valuation-polymorphic, gap recorded) + D3-04 (the unconditional μ₄ product law) |
| D3B | μ₄ stack D3-05..09 | DONE — 56 decls Lean-core, all five rows green; the chain funnels through hconv |
| L2E4 | hconv + D3-10 | DONE (a9a8155f) — the generic hconv REFUTED at the bare carrier (the anchor obstruction; confirms A24B's anchored route); ★ D3-10 LANDED via the cheap mirror — the D3 chain unblocked |
| EXPOAUD | the EXPO audit | DONE — FIX-THEN-PUSH with 28 findings (incl. a false countermodel count, the Haar scope, the one-way status) |
| EXPOFIX | fix the 28 findings in the site working tree (no push) | IN FLIGHT (Fable, ~19:10) |
| D3C | μ₄ stack D3-11..14 (product/scalar, normalized operator, recipe grade-170, g16 existence) → C136d2 | IN FLIGHT (Sonnet, ~19:10) |
| (EXPO) | draft in the site working tree, push after EXPOAUD + orchestrator review | HELD |
| G345 | gates G3+G4 | DONE — the shared DeepLevelExport stands (29/29 Lean-core; the letter equality FORCES the descent clause); no leanspec change; pre-fleet gates ALL clear |
| G5F | gate G5 | PASS — the refinement source-faithful + operator-level (primary cites); the D4 stack cleared |
| D3A | μ₄ stack base D3-00/01/02 | DONE — the dv3 layer + s2Hgt₄ (tooth 85) + the endpoint bank modulo the explicit Dv3ResSurv; 52/52 Lean-core |
| A0C | A0-CUBIC | DONE (d11cb4cf) — ★★ DecidedSliceAt 3 LEAN-CORE (not even a cite): all five exact cubic densities proved uniformly over every complete DVR incl. wild primes; G61.s rider retired BY PROOF; cert 38/38; the n≥4 generalization genres named |
| P1D | the P1 dictionary | DONE (adc165eb) — ★ P1 CLOSED OUTRIGHT, the GN cite retired UNDECLARED (isMuKey_of_isTestKey a Lean-core THEOREM; the residual-lift wall fell to C130kp1 made frame-generic); trust-boundary flags carried |
| F13A | signed F1.3 | DONE (ba49bc4f) — dv2Supp_translation (NODE C.37) landed; F1.4–F1.6 need the LEVEL-2 Theorem-M twin (= DWC.s D3-03/D3-10 — shared root, folded into DWR) |
| RB3R | re-base refine_invariants | DONE (523c8a7b) — the IsTestKey conjunct a statement-level OVERCLAIM (codex-confirmed); conjuncts landed; A-C.23 forced |
| A23E | enact A-C.23 (re-sign C.56(i) to the source-faithful M4 package) + land the repaired theorem → C150rb5 | DONE — leanspec C.56(i) re-signed (record at the node; pre-A-C.23 bytes at 523c8a7b); the re-signed statement is a THEOREM `refine_invariants` (C150rb5.lean, Lean-core: MH.6/M4 + the new grade floor `dvSupp_k2DigitLift_ge`, EFF.GENTOW1.27 audit closed from hfloor); C93 census row (2) BLOCKED→LANDED (C135c93 live `#check`, 5 of 7); leanspec + roll-up exit 0; verdict_A23E.md |
| DWR | the blueprint revision | DONE (b7c895e7) — tower survives; leaf² a rejected control; the distinct-factor F0 passes all formal controls; ★ STOP-LINE: GNCitePayload.s SHAPE structurally defective (the selected factor can never be the key) — A-I.8 fork flagged |
| A8D | the A-I.8 adjudication | DONE (3d545e6e) — (β) WINS, no row blocked: E.40 needs only hirr (Monic∧MuMinimal∧MuPrime → Gauss bridge, probe-checked) + hef; four GN-only research nodes die; twins = the blueprint.s D3/D4 tails + L2E |
| AI8E | ENACT A-I.8 | DONE (05a91441) — GNCitePayload retired; LadderSupplyLive₃; ★ the mp1 leg DISCHARGED BY THEOREM (mp1CarrierLiveDirect_of_steps); ladder.s open content = package/lb1/vartheta + RecenterStepDirect occurrences on the deep tower |
| CHA | the unattacked capstone fields | DONE (1be8359f) — ★ a1 CLOSED at every degree (menuLawAt_all, signed bytes unchanged; MENU-FAMILY retired); a0 reduced to FIVE named cubic value theorems via the landed socket; μ=3 HE slice packaged; rest re-based honestly (I.03 audit-belief refutation carried to review) |
| UNT | physical cite retirement | DONE (a163867d) — axiom → theorem in place, statement bytes unchanged; allowlist a TRUE SIX; C131ac.s whole pow chain now pure Lean-core; cycle broken by one verbatim lemma move (C131ae0.lean) |
| EXPO | public exposition refresh DRAFT | IN FLIGHT (Fable, resumed after a 529, ~16:30) |
| R0 | realization row R0 | DONE (2daa5ca7) — the depth-4 receiver/normalizer with pins at 5/21/85/171; first-attempt, zero repairs |

## 7. Resume protocol (fresh agent)

Read this file whole → `git log --oneline -15` → the in-flight ledger (§6) → act on the
frontier (§4) top-down. The map of the repo is in the repo CLAUDE.md; the blueprint is
`blueprint/CHAP-*.md`; signed statements live in `leanspec/Leanspec/Chap*.lean`
(byte-frozen; re-signs only via recorded amendments); landed Lean in
`leanfinal/Uniformity/`. When a milestone lands: update §§2/4/6 here IN PLACE, append the
dated details to `docs/LOG.md`, commit both with the work.
