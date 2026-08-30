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

**DIRECTIVE (Asvin, 2026-08-28): COMPLETE PROOF AT EVERY POINT.** Every degree/order/depth-indexed
target is pursued at the UNIFORM statement; concrete degrees appear only as math-side pattern
batteries (the examples-first discipline) or as single nonvacuity witnesses for sitewise fields.
"Generalizes per degree" is a warning, not a plan — the uniform mechanism is designed before any fleet.

**PROTOCOL (Asvin, 2026-08-24):** owner input is needed ONLY for literature-cite Lean
transcriptions, and only as a SECONDARY (non-blocking) check — `docs/CITE_REVIEW_LIST.md`
is his reading queue. Everything else — re-signs of refuted statements, field lists,
design decisions — proceeds autonomously under the **end-to-end-proof criterion**: a design
choice is right iff it leads to a completed proof. Honesty invariants unchanged: no fake
axioms, no `sorry`-shaped discharges, statements never weakened silently (re-signs are
recorded amendments), faithfulness entry per cite, `sorry`-free ≠ non-vacuous.

**FLEET (weekly codex at 87%, 2026-08-28 late — STRICT conservation: codex ONLY for the A0G-GC stop-line + adversarial verification; everything else Fable/Sonnet):** Codex `codex exec -c model_reasoning_effort=high` for new math + blueprint
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

## 4. The live frontier (what blocks what) — rewritten 2026-08-30 post-census-blitz

1. **The CapstoneHypotheses INHABITATION campaign (top item).** `UniformityStatement`
   reduces to inhabiting `CapstoneHypotheses n` (post-A-I.8 shape). Field-by-field TRUTH
   (2026-08-30, after the ~30-unit census/deepTwist blitz — §6 has the unit rows):
   (ns7) **CLOSED** (`ns7Termination_of_cite`). (a1) **CLOSED for all n**
   (`IFC6.menuLawAt_all`). (jd0/genhnBox2) `True` placeholders — trivially inhabited;
   the I-D7/I-D8 honesty defects are leanspec matters, not proof blockers.
   (a0 = `DecidedSliceAt n`) — THE CENSUS FRONT, now machine-reduced through the
   IFCG14→41 chain to: {`LeafSectorLaw`'s cell count (the decision half CLOSED by RIS —
   B-BOX-1 PROVED Lean-core, the proposed cite killed)} + {split: `CollisionLaw`/`StrayLaw`
   (the q-power fiber law) + the `LiftsFactor` Hensel leg — unit CSL IN FLIGHT} +
   {power: four named legs on PSL2's landed Eisenstein cascade — unit PSL3 IN FLIGHT} +
   {mass-4 dd/E2 recursion terms (ER4/DBL: all depth-0 limits closed)}. Unramified σ:
   ZERO at every mass (UZL). Bridges: GONE (INS2's InertiaScaling, Lean-core).
   (a2 = `DrainageAt n`) — closed n ≤ 3 (DRN); UDR's master inequality reduces the rest to
   `DeepTailDrainAt n` (the primary ψ^k single-cluster tail; strictly easier than H.124).
   (ladder) — mp1 DISCHARGED generically (A-I.8); remaining: the vartheta live leg +
   the package/lb1 universal fields (the I10 supplier chain feeds these; TWD killed
   row C3 at canonical normalizers).
   (deepTwist) — the exact boundary (G10U's iff → USUP/WSS/SCS/LRS reductions): the
   carrier program's remaining packs {`RungLift` per rung ≥ 3, `PrevGrade` f' ≥ 2,
   `BankWiringSupply`, the `CarrierReadLaw` tie} + the tau side {`UniversalKernelSpan`
   (pointwise-rfl at canonical normalizers), `UniversalGeneratorDescent` = `WrapDescentAt`
   (OPEN-LETTERS, research)}. Rung-2 packs land at EVERY arising truncation (D3AD-spine).
   (windowPinning/genhnHE/genhnTow1) — **⚠ COVERAGE GAP: the three I-D12 bodies
   (+ TypeOfFaithful) have NO active lane.**
   The CHFD supply map (docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md) predates the
   blitz; THIS section supersedes it field-by-field.
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
| EXPOFIX | fix the 28 findings | DONE — all dispositions + two self-caught draft errors |
| D3C | μ₄ stack D3-11..14 | DONE (c82e9cf1) — all four unconditional incl. ★ g16 = g8²−2⁸Φ₂ (monic deg 16, residual X+1, grade 170; the campaign's hardest row closed completely); T4's deferred half closes |
| D3D | the μ₄ closer | DONE (45a452e0) — ★★ s2Mu4_calculus_nonempty UNCONDITIONAL (all 13 laws, no carried hypotheses); keyAt 4 = g16; T5's Λ pin complete; THE μ₄ STACK IS CLOSED |
| D4A | μ₅ base D4-00..04 | DONE (c2452f01) — all five unconditional incl. ★ the survival core at (g16,171,1); PrevGrade ALL grades at e'=1 |
| D4B | μ₅ middle D4-05..12 | DONE — all eight rows incl. ★ the leaf + Λ's exact grade + a real key-read catch (X not 1 at e'=1) |
| R12 | realization rows R1+R2 | DONE (51743fed) — the four-branch total tables + the level-4 slot carrier; the forced card-2 bank derived generically |
| D4C | the μ₅ closer | DONE — ★★ s2Mu5_calculus_nonempty UNCONDITIONAL (all 13 laws non-vacuous); s2_g16_irreducible NEW; the [DWR] g16+1 Bézout legs; BOTH refinement calculi stand — the DWC operator phase is DONE |
| R34 | realization rows R3+R4 | DONE (7049244d) — the valuation-extension combinator + the four-branch point dictionary + the level-2/3/4 thresholds with threaded strict bounds; two opens deferred to R7 |
| F14C | the F1.4/F1.5 legs | DONE (af0ad200) — ★ the CARRY LAW landed frame-generically + the weighted assembler; C.39's re-sign exposes a THIRD defect (slot-varying weights vs the pinned constant — stationarity unsupplied) |
| A24C | round-3 archaeology | DONE (48927e49) — ★ THE SOURCE VINDICATED: the constant scalar is honest over its own TWIST-CARRYING carrier (HE7-3's closed-form exponents; the transcription dropped the twist); dv2ResPolyTw + the family→constant transfer LANDED; the 𝔽₄ battery discriminates 15/127 vs 127/127 |
| A24F | enact A-C.24″ | DONE (63561bbd) — the round-4 close: C.38/C.39 re-signed over dv2ResPolyTw; the conditional C.39 LANDED (5/5 Lean-core); ONE open supplier |
| HCONV | the F1 family's last leg | ★★★ DONE — the convolution supplier Lean-core; C.39 + C.38 fired byte-as-is; THE F1 FAMILY (F1.1–F1.7) COMPLETE at the source-faithful signed statements |
| R5 | the OPEN-LETTERS core | ★★ DONE (ad7809ea) — the canonical reads (triangular inversion) + the G4 equalities at every live level + the R7 node-conditional handoffs; htie NARROWS to one μ-bank claim |
| R67 | the KEYSTONE | ★★ DONE (d06f4545) — s2SplitNodeFour + the chain realization + the realized input; the G4 descent record INHABITED; the export modulo the site package; R34's opens closed (incl. the honest key_value refuter + fix) |
| NP1 | the GC runway's classifier | DONE (9db945ba, orchestrator-banked post-hang) — the read-off well-definedness (GC2's ingredient); 11/16 A0G nodes |
| C0123 | the consumer legs | ★★★ DONE (ba94a4e7 area) — the export INHABITED at X/j=3; the SIGNED wired GENTOW demand at own exports; THE FIRST LIVE-INDEX VarthetaRes; conditionality exactly the keystone's |
| C56R | the final occurrence rows: C5r (★ the first honest MidPeelEmission at the R8r input) + C6r (the deepTwist tooth, same X) → C136c5 | IN FLIGHT (Fable, ~05:55) |
| BRIDGE | the dissection-skeleton bridge | DONE (75c79104) — exists_realizesSkeletonAt_of_dissection with ONE scoped hypothesis (hbelow1 → GC1); §§1–3 unconditional; 12/16 nodes |
| GC | the stop-line's honest partial | DONE (9331f5be) — DECREASING landed; the carrier's disjointness insufficiency MACHINE-PROVED (+ the StrongRealizesFaceAt repair defined); the exhaustion kernel ISOLATED as one named statement; the cover deliberately NOT declared from the weak bank |
| C56R | the final occurrence rows | ★★★ DONE (c1287ebe area) — the FIRST MidPeelEmission (bindings by rfl) + the deepTwist tooth at the same X; the occurrence phase COMPLETE |
| GCF | the repair legs | ★★ DONE (8fe42879) — the strong bridge + UNCONDITIONAL Lean-core disjointness (the countermodel pair discriminated); the cover = finiteGenreCoverAt_strong_of_kernel, conditional on ONE input |
| GCK | the exhaustion kernel's partial | DONE (d5f31674) — the one-side sub-kernel via the predicted mechanism; the residual bridge NAMED: StrictRecentredFactorSideStatement (the multi-side factor-polygon inheritance) |
| GCK2 | ★★★ THE GENRE COVER FALLS | DONE (3f78101d area) — the bridge PROVED ON LEAN CORE ALONE (the secant lemma = the genuinely new polygon math); the kernel + finiteGenreCoverAt_strong_all UNCONDITIONAL; 13/16 nodes; the rest is assembly |
| A0G-RW | the rational weights | ★★ DONE (6f6fcc1e) — IFCG13 at PURE LEAN CORE 15/15 (a three-agent relay: two hangs → codex 8/14 → the closer 6/6 from fresh angles); the exact schema measures exist with the IFC7 recoveries |
| A0GA | the assembly | DONE (94e0d3ae) — the honest package: decidedSliceAt_all_of_recursion (∀n, pure Lean core) + the new n=1 slice + off-menu everywhere; the prize blocked on the ONE socket |
| FP0 | the counting socket's reduction | DONE (ee26fa4b) — the loop-cell count PROVED entirely; the socket ⟺ ONE remainder: RationalNonloopRemainderAt (the realization→cell cardinality bridge); zero new axioms |
| FP1 | the bridge's honest form | DONE (8330c4d4) — the binary cardinality bridge COMPLETE (finite-precision Hensel uniqueness + fold bijectivity + the exact stratum product count, all Lean-core); the remainder ⟺ the per-genre census (audit iff proved); the NP-layer classifier/cell-measure gap named + localized |
| FP3 | census assembly + the single-point kernel | DONE (4878fd3c) — IFCG18.lean: the labelled/unlabelled exchange, the URLim calculus, the pattern-cell partition, and ★★ `decidedSliceAt_all_of_singlePoint` — the ALL-DEGREE decided-slice theorem rests on exactly TWO named kernels: `SinglePointAggregateLaw` + `DeepLinearClusterLaw`. Next sub-units: (a) the (δ ≤ 3, e = 1) restricted kernel from IFCG4+H124b; (b) the uniform Gauss irreducible count δ ≥ 2 (needs unramified base change); (c) the fractional-slope OM-cone census e ≥ 2 |
| DTD | the deep tail drain | DONE — IFCG49.lean (Lean-core): ★★★ the KÖNIG compactness engine (reusable §3) — a2 = TWO decoupled classical Props: `KrasnerAt n` (mathlib's IsKrasner is the pointer) + `DiscNullAt n` (Serre null-count; the Bezout instrument in mathlib); the deep-box direct route refuted honestly; CellTypeScalingAt deliberately not consumed |
| UDR | the undecided drain rate | DONE — IFCG46.lean (Lean-core): ★★★ the a2 field = ONE family `DeepTailDrainAt n` (n ≥ 4) — the master inequality (depth buckets + q^v packing + the transfer) closes everything but the PRIMARY (ψ^k, k ≥ 2) deep-collision tail = the single-cluster locus; H.124 revival rejected on evidence |
| DTR | the OM-step decision transport | DONE — IFCG47.lean (PURE core, cite-free): ★★★ `transport_decidedAt_iff` both directions on ONE named pointwise Prop `CellTypeScalingAt D` (D=1 PROVED; D ≥ 2 = the deep-wild tower, FGMN cite the honest fallback); devT non-multiplicativity hand-checked (the charge's pull-back mechanism corrected); ★★ `powerFullSpanLaw_of_prime` — UNCONDITIONAL at every prime mass; ER4's dd terms = CellTypeScalingAt 2 + conversions |
| PSL4 | firing the power law | DONE — IFCG44.lean: ★★ `powerSectorLaw_of_rebase` (Lean-core) — the sector partitions EXACTLY into proper (descends through the convolution table) ⊔ full-span (the class IS pure; cite-free); PowerSectorLaw = `PowerConvolutionDefectLaw` + `PowerFullSpanLaw`; the one missing full-span leg = DECISION TRANSPORT ACROSS THE RECENTRING (the OM tower step, C136 territory) |
| DRN | DrainageAt general n | DONE — IFCG45.lean: a2 CLOSED at n ≤ 3 (n=3 was already landed — the §4 flag was stale); ★ the lossless σ-free reduction `drainageAt_iff_undecidedDrain` + the packing majorant; the exact remainder: ∀n a2 ⟺ `UndecidedDrainAt` at n ≥ 4 = the H.124 FullClusterRateBound frontier (B-BOX-1 gates — RIS's x-frame proof may now feed it) |
| CSL | the q-power fiber law | DONE — IFCG42.lean (13/13 PURE core): ★★ #fiber = q^v EXACTLY both directions (Sylvester-kernel bijection; the NEW reusable index-determinant engine `natCard_quotient_range_smith`); LiftsFactor DISCHARGED (the depth-v Newton engine); the transfer criterion FIRES; CollisionLaw/StrayLaw = depth-stratum root counts (N-free digit boxes) + the drainage tiling premise |
| PSL3 | the four power legs | DONE — IFCG43.lean (15/15 PURE core): compositum stack; cellTransport (boxes, fScale = e' exact); the ∀-DVR instantiation + one-pair ZcURLim value; ★★ THE HEART both directions (eis_transfer_digits_iff — lattice digits ⟺ deep recentred box; the binomial digit-vanishing). PowerSectorLaw = 3 remainder items: assembly bookkeeping, general-(h,d) lattices (verbatim replay expected), induction wiring |
| PSL2 | the power sector cascade | DONE — IFCG39.lean (22/22 PURE Lean core): the strict mass drop; ★ the ramified Eisenstein complete-DVR cascade (C27x's hole CLOSED at h=1) + coordinate lattice; the dev-transform bijection + two-way level exactness (fScale = e'); the dd (2,2) stack fired; PowerSectorLaw = four named legs (residual-box transfer, cell correspondence, ZcURLim at O', the d ≥ 2 compositum) |
| RDC | the resultant-depth fiber census | DONE — IFCG41.lean (no C.33/AX_cellRecursion — elementary): the depth instrument + exact graded census identities; ★★ the depth-v gap engine (factors determined mod π^{N−v} exactly); the decidedness transfer at the shifted level; the m ≥ 4 split leg = `CollisionLaw` + `StrayLaw` (the q-power fiber law, Smith-normal-form genre) + the LiftsFactor Hensel leg |
| LRS | the ladder read supply | DONE — I10LadderRead.lean: s=1 rung + head proved derivable; s ≥ 2 non-closure ADJUDICATED (free-field fence); ★ the carrier normal form `CarrierReadLaw` (one read_ker_pow field + tie) = EXACTLY the law genre RUNG's rung-2 carrier produces — row C2's target aligned with the carrier program; `deepTwistField_of_carrier_supplies` |
| SDL | the convolution defect law | DONE — IFCG40.lean: the class-level Minkowski transfer (faces concatenate, residuals multiply) + the sector converse; the charged injectivity REFUTED (fibers q^{v(Res)}; witness at v=1); ★★ the EXACT defect decomposition (collisions + strays) + the iff with SplitSectorLaw; FIRES at m ≤ 3 (split sector empty below 4); the m ≥ 4 leg re-aimed at the resultant-depth-graded fiber census |
| SSL | the split sector law | DONE — IFCG38.lean: the refinement map (visible-corner split classes = mulClass of two DECIDED smaller-mass classes) + the convolution majorant + conditional firing; the sector re-based on ONE Prop `SplitConvolutionDefectLaw` (= polygon-block product-count exactness: Minkowski transfer + finite-precision polygon-block factorization uniqueness) |
| RIS | the residual inertia supply | DONE — IFCG37.lean: ★★★ B-BOX-1 at the x-frame PROVED LEAN-CORE (the proposed [FGMN 6.6]/[GN15 2.3] cite KILLED); leaf laws unconditional at every (e',d); ER4's e1IrrLeafDecision fired; LeafSectorLaw = the leaf-cell count only. (One mid-unit commit 8672b8c3 flagged against the no-git clause) |
| DBL | the depth-0 box limits | DONE — IFCG36.lean: both limits EXACT at every level on Lean core (the digit instrument: residual coefficients ARE class digits via resFieldEquivX; split = C(q−1,2) resolved by proof); the ∀σ split family discharged unconditionally; mass-4 rests on leaf + dd/E2 recursions only |
| RECUR | the uniform remainder recursion | DONE — IFCG35.lean: ★★★ the exact leaf/power/split trichotomy at every mass (unique min-slope face + canonical class residual); leaf d=1 closed premise-free; ★★★ `decidedSliceAt_all_of_sectorLaws` — THE CENSUS ENDGAME: 3 sector-law families (e ≥ 5 ramified, under smaller laws) + `ResidualInertiaSupply` (d ≥ 2; IFCG32's norm machinery the route) + ER4's five e=4 laws |
| ER4 | the five even-ram e=4 types | DONE — IFCG34.lean: the forced sector partitioned exactly (E1 trichotomy + E2); split decided; the irreducible pin Lean-core ({(2,2)} or {(4,1)}); `E1IrrLeafDecision` = a B-BOX-1 instance; dd = ORDER-2 Montes recursion; the five laws on named sector-limit premises + the wire. CORRECTIONS: (4,1)-empty-at-odd-q REFUTED (PARI p=3 witness); survivors = E1IrrLeafDecision + 2 depth-0 box limits + order-2 dd (3) + E2 recursion (3) |
| INS2 | the inertia scaling identity | DONE — IFCG32.lean (Lean-core, the leg cite-free): ★★★ `inertiaScaling_all` for EVERY δ (norm transport + the new coprimality-free norm-multiplicativity; the gcd witness via Nakayama-comaximal CRT conjugates + the invariants theorem); ★★★ the bridges UNCONDITIONAL for all δ,e — `decidedSliceAt_all_of_remainder5_even4` with hBr discharged: THE CENSUS = the remainder laws ALONE (ramified e ≥ 5 + five e=4 even-ram) |
| UZL | the unramified zero-law | DONE — IFCG33.lean: ★★★ `coneRemainderLaw_unramified` — the conjecture PROVED uniform in (q,m,σ), count identically zero (the last-hull-edge argmin construction; visibility automatic); odd-e extension REFUTED as zero law (mixed value = witness), exclusion engine landed instead; ★★★ the front: DecidedSliceAt = ramified e ≥ 5 laws + five even-ram e=4 types + `InertiaScaling` |
| CCA | the remainder carrier assembly | DONE — IFCG31.lean: ★★★ mass 4's odd half CLOSED (6/11 types; the mixed value (q−1)(q³+1)/q⁹ exact; zero at all-odd σ); the X-strip frontier DISSOLVED at m=4; the front re-based: DecidedSliceAt = e ≥ 5 laws + FIVE even-ram e=4 types + `InertiaScaling`; conjecture recorded: unramified zero-law at every e via staircase generalization; PARI battery (720 samples) green |
| UBC | the unramified block count | DONE — IFCG29.lean (1973 lines): the bridge family COLLAPSED to the single e-independent `InertiaScaling δ` (= δ ∣ f_G, B.52's content, verified true classically; the gcd-witness subtlety recorded); the δ-root conjugation family replaces Frobenius (no Witt); invariants by degree count; surjectivity by construction; irreducibility proved. CENSUS = ConeRemainderLaw (e ≥ 4) + InertiaScaling δ |
| XHS | the x-frame Hensel split | DONE — IFCG30.lean: RECORD CORRECTION — the 'absent' engine was landed B.41 (shared import blind spot); the x-frame + class + unit-part splits ALL landed Lean-core; WFR's wide-face refinement law FIRED; ★★ IFCG23 §7's `FracFaceForcesRamStatement` CLOSED at general position (unit-corner polygon transfer). Surviving: X-strip, B.63 leaf decision, block recursion, bridges |
| WFR | the wide-face refinement e ≥ 4 | DONE — IFCG28.lean (Lean core + B.42): ★★ the pigeonhole decisions (mixed denominators, no width lemma; + the off-one variant at every mass); the staircase sector closed AND proved DEEP (never in the remainder carrier); ★★ the x-frame residual polynomial proved a CLASS INVARIANT (CN1-for-residuals); e ≥ 4 surviving set = the counting campaign + class X-strip + the x-frame coprime-residual Hensel split |
| UBB | the unramified block bridge | DONE (43b1643d; NOTE: the agent committed its own increments against the unit fence — content verified clean) — IFCG27.lean: legs (a)+(b) CLOSED (adjoinRoot_isAdicComplete via the NEW isPrecomplete_of_basis; residue count q^δ); the vanishing half PROVED outright (B.52's δ ∣ f); scalar extension closed (Möbius positivity); ★★ the bridge REDUCED to ONE Prop `UnramifiedBlockCount δ e` (concrete extension, no ∃-telescope) + `decidedSliceAt_all_of_remainder_blockCount`; e=1 member proved at every δ; successor map recorded (Frobenius invariants, H124b surjectivity, inertiaDegOf descent f_O = δ·f_{O'}) |
| CRL | the remainder laws at e ≥ 3 | DONE — IFCG26.lean (Lean core + the signed B.42 cite only): ★★ `coneRemainderLaw_three` for EVERY σ (the mass-3 remainder not empty — closed by exact evaluation, count (q−1)q^(3K−5)); general-position forcing proved AT the census carrier; `decidedSliceAt_all_of_remainder4_bridge` — THE CENSUS FRONT = ConeRemainderLaw at e ≥ 4 + UnramifiedBlockBridge, nothing else; wide-face survivor reduced to class-stable residuals + order1Type bridge; named residue: x-frame unit-part Hensel coprime split |
| CN5 | PointConeLaw base change | DONE — IFCG25.lean: ★★★ the census front re-based on exactly TWO named families: `ConeRemainderLaw e σ` (e ≥ 3; e=2 closed; AMENDMENT: strictly larger than the m ≥ 4 wiring, e=3 forced) + `UnramifiedBlockBridge δ e` (the δ ≥ 2 carrier correspondence in ONE Prop; heart = the level-exact Hensel block correspondence with fScale δ); ★★ CN3 proved outright (δ=1 clauses close; necklace not needed); the (1,2) tooth zero-hypothesis |
| D3AD-spine | the spine adapter | DONE — I10SpineAdapter.lean: LevelDatum-per-truncation from DeepTower (C.42→C.44→C.09, truncation-invariant by rfl); ★ rung-2 packs at every arising truncation; ★ B-1 PROVED from the tower's own hfloor 2; depth-adapter row DISCHARGED at rung 2; rungs ≥ 3 provably not LevelDatum-shaped → RungLift unchanged |
| RUNG | per-rung carrier packs | DONE — I10RungPacks.lean: ★ the rung-2 pack at a GENERAL tower (the C28 cocycle is a coboundary — normExp twist makes f14c's carry law exact; no S2 pin; wcoeff_mul fires level-2→3); iteration: nextCarrier unconditional, quotient pass PROVABLY forced, `RungLift` named per rung ≥ 3 + towerPacks induction wrapper; bank remainder = D3-03 spine adapter + RungLift ≥ 3 + PrevGrade f' ≥ 2 + one rung-2 slope inequality |
| CN4 | the cone geometric sums | DONE — IFCG24.lean: ★★★ range = deep box (uniform in m); ★★ the m=2 zero-cone EXACT ((q−1)q^(2M+1); ZeroConeLaw's m=2 clause fires for EVERY σ; ECONE's 1/(q²+q+1) recovered as HasSum regression); the pure-face monomial bank + partition at every m; reduction: ZeroConeLaw/CenteredConeLaw ⟸ `ConeRemainderLaw m σ` (EMPTY at m=2) — census open content = `PointConeLaw` + per-(m≥4,σ) remainders |
| WCC | the weighted convolution carrier | DONE — I10WeightedCarrier.lean: ★★ `wcoeff_mul` — the general tower-level convolution law (line floors only, no exactness) on the abstract WeightedCarrier; the S2 pin re-derived byte-identically; CONVOLUTION REMOVED from the site bank's research list — remainder = per-rung pack instantiation (depth adapter, key lifting `read_key = 0`, B-1 numerics) |
| CN2 | the at-floor decidedness heart | DONE — IFCG23.lean: ★★ `decidedAt_of_eisenstein_face` PROVED (the class-level fractional-face criterion, uniform in q/m/h/N — the blueprint's designated hardest object, closed beyond its fallback); the floor sharp for decidedness itself (the deep boundary counts ZERO); e=2 cone reduced to CN4 geometric sums; remainder: `FracFaceForcesRamStatement` (general-position, pure instance proved), residual refinement e' < m, CN4, CN5 |
| SCS | the site calculus from the L2E engine | DONE — I10SiteCalc.lean: ★ `siteCalculusSupply_iff_wiredBank` (IFF) — the supply factors EXACTLY into a tower-side `LevelSiteBank` (research half: the S2 pin funnels through the ONE lemma `s2Mu4Coeff_mul`, generic counterpart REFUTED at the bare carrier → weighted convolution carrier needed) ⊗ `BankWiredAt` wiring (parametric); keystone split: bank = (h2,hq) alone, wiring = witness payload |
| CN01 | cone stages CN0+CN1 | DONE — IFCG22.lean: CN0 full (`centeredConeLaw_iff_zeroCone` — ONE centred cone at 0; the box action is the identity); CN1 on the class-stable part (class NP lift-stable strictly below the frame floor; floor sharpness machine-checked). CN2 (the at-floor decidedness heart, C61's open ℓ-half) is next |
| TWD | the tau-word/descent supply | DONE — I10TauSupply.lean: ★★ the triangular-basis bridge (freeze v2's OPEN) proved uniformly in q — ROW C3 ELIMINATED at every canonical-normalizer realization (keystone re-derived card-2-free); R5 = WrapDescentAt (the irreducible OPEN-LETTERS core) + site letter_receiver equalities; vartheta boundary now `UniversalKernelSpan` + `UniversalGeneratorDescent`; owner-gated rec RECORDED not enacted: pin normalizer := laurentNormalizer to erase C3 |
| ECONE | the fractional-slope cone reduction | DONE — IFCG21.lean: ★★ `decidedSliceAt_all_of_cones` — the census front's WHOLE remaining content = `PointConeLaw` + `CenteredConeLaw` (both reductions proved; the exact partition fracCellCount = Σ per-centre cones); CN0–CN5 discharge blueprint in verdict_ECONE.md (heart: CN2 class-level NP fractional-face decidedness = C61's open ℓ-half) |
| DLC | the deep-linear cluster kernel | DONE — IFCG20.lean: boundary annihilation drainage-free; ★★ `deepLinearClusterLaw_iff_fractionalCell` (lossless IFF; the remainder = the fractional-Newton-slope cell, provably no integer recentering) + the composite `decidedSliceAt_all_of_singlePoint_fractional`. CENSUS FRONT'S WHOLE GAP: `SinglePointAggregateLaw` (e ≥ 2 cones; e=1 CLOSED by GAUSS2) + `DeepFractionalCellLaw` — two entry points into ONE fractional-slope OM-cone census |
| GAUSS2 | the uniform irreducible census | DONE (fdf7f7b1) — IFCG19.lean: the Möbius/necklace count ALL δ ≥ 1 (IFCG4's δ ≤ 4 pin removed); ★★ SinglePointAggregateLaw's e=1 clause CLOSED unconditionally for all δ (constant normalized family N_δ(q)/q^δ) + the all-ones sector; scoping correction: NO base-change leg at e=1 — the census kernel's remaining content is the e ≥ 2 deep cones only |
| WSS | the wired-site supply at general q | DONE (230661ce) — I10SiteSupply.lean: the dictionaries' calculus coupling was card-2 convenience, discharged generically; ★ `deepTwistField_of_bank_supplies` — the capstone field from THREE named supply Props; the C0/C1/C2 boundary shrunk to `SiteCalculusSupply` (frame-generic L2E output) + `LadderReadSupply` (calculus-free D.44 read law), both keystone-inhabited |
| USUP | the universal supplier pair | DONE (f29b1435) — I10Suppliers.lean: scope machine-settled (view/tau_mem derivable at EVERY realization; tau_word/descent/site-calculus not); the C3 record from tau_word+descent alone; ★ `deepTwistField_of_supplies` — the capstone's deepTwist field reduced to TWO named per-realization supply Props (`UniversalTauWordDescentSupply` = rows C3+R5, `UniversalWiredSiteSupply` = rows C0/C1/C2), inhabited at every keystone witness |
| G10U | the deepTwist universal-supplier boundary | DONE (ca2097be) — I10Universal.lean sorry-free Lean-core: the G10 per-witness exporter family PROVED (all deep-live levels, own exports) + wired-genre instances at every keystone witness (genre-wide deepTwist tooth); ★ the exit gate `deepTwistField_iff_universalPerWitness` — the capstone's deepTwist field = EXACTLY the two universal suppliers at GENERAL witnesses (C1/C2 site-package + C3/R5 tau-word), the campaign's next named target |
| FP2 | the multi-point census machinery | DONE (da7a9c0b) — the decided-refinement (no Hensel) + the convolution law + ★ stratPoly's ring product law (the fold = multiplication); banked mid-stub after the orchestrator's final fix; the per-stage closure statuses + the single-point kernel isolation = the FP3 charge |
| EXPO | the public exposition refresh | ★ PUSHED (site aaf1ddb) — stage 13 live: draft → 28-finding audit → fix → clean skim → orchestrator spot-check; carry-over: maps.json/story.json still ignore stage 13 (graph pipeline absent) |
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

