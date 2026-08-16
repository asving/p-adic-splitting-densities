# PHASE-0b — HYPOTHESIS-CLOSURE LEDGER (v7)

Scope: surviving conditions on the path from `leanfinal`’s `UniformityStatement` through W12/GENIND, the T-unit chain, low-degree checks, tightness census, eight generality audits, and cited external mathematics. This is enumeration and classification only; it resolves none of the listed mathematics. CARRY means keep the condition visible until a named node closes it; MATH is missing proof work and must not be disguised as a field hypothesis; NODE is bounded audit, transcription, citation, interface, or proof-packaging work; MERGED remains indexed but is represented by another row and is not counted twice; CLOSED means a named instrument, run, or **owner answer** has discharged the row and the reference is recorded in the row itself; **PROPOSED-NODE** (new in v4) means a unit an audit has *synthesized* but no accepted note asserts — it is indexed so it is not lost, and it may re-disposition nothing until it has run as its own unit; **IN-PROGRESS** (new in v5) means a launched unit whose result is not yet in — it may still re-disposition nothing, but it is no longer merely proposed; **OUT-OF-PATH-BY-POLICY** (new in v5) means the row is a real obligation somewhere in the repo but an owner policy answer has put it off the `leanfinal` capstone path, so it no longer conditions the capstone.

v3 folds the Phase-0b completeness sub-sweep’s fifteen delta items (`runs/qgen/HYPLEDGER_deltas.md`, TIER-1/2/3). Every delta quote was re-verified against its source file and line before transcription. Items that are actions rather than conditions are in `MAINTENANCE QUEUE`, not in the row list; TIER-3 off-path items are one line each in `OFF-PATH`.

**v4 folds `runs/qgen/WELD_FACE_AUDIT.md` (census row S-4, executed 2026-08-13 at the WIDENED charter): thirteen corrections COR-WFA-01…13.** Every NOT-REACHED quote was re-verified at its cited file and line before folding; two audit statements did not survive that check and were folded CORRECTED, not verbatim (flagged at their rows and in `CHANGES-FROM-v3`). **Unlike v3, this fold CHANGES the capstone-conditionality preview** — four conjuncts leave and two enter; the BEFORE/AFTER is displayed at the head of the preview section.

**v5 folds the 0d CLOSURE — all nine owner questions answered** (`docs/PROJECT_STATE.md` appends **#47** L4541 (Q1–Q5 + the review-boundary policy), **#48** L4566 (the Q5 rewire, landed as UNIFORMITY-P4), and **#49** L4593 (Q6–Q9 + the new directives)) — plus the ORPHAN-1 verification that v4 deferred and the P4 rename sweep. The needs-Asvin count goes to **0**. Two things this fold does *not* do: it proves no mathematics, and it closes no row on the strength of an answer that did not actually reach that row — every re-disposition below cites the append clause that authorizes it.

**v6 is a DISCHARGE fold: it books the CERTAIN-NODES program's 23/23 landing against this ledger's rows, plus one tally correction the v5 fold left stale.** Sources: `docs/PROJECT_STATE.md` append **#48** L4566 (UNIFORMITY-P4, already reflected at v5), append **#49a**/**#50** L4636 (the certain-nodes program closes, 23/23 landed, zero blocked), `spec/CERTAIN_NODES_2026-08-14.md` (node → row provenance), and the four batch unit notes `leanfinal/notes/CN_BATCH_{A,B,C,D}_2026-08-14.md`. Two rows are DISCHARGED against a CERTAIN-NODES landing, each verified against the live Lean declaration before stamping (HYP.03, HYP.147) — every other CN lands new infrastructure with no pre-existing ledger row, so it enters this file only via the MAINTENANCE QUEUE follow-ups, not as a row re-disposition. Separately, this fold corrects a **stale tally**, not a stale row: HYP.04/05/06 were already stamped **DISCHARGED 2026-08-14 (UNIFORMITY-P5)** in the row bodies before the v5 fold was written, but the v5 tally line still counted all three as MATH — this file's own glossary (line 3) says a DISCHARGED row **is** a CLOSED row, so v6's tally recounts them there. No row's disposition text is rewritten by this correction; only the count changes. No new mathematics is proved by this fold and no row not named above moves.

**v7 folds five accumulated post-v6 blocks, verifying each source before writing.** **(1)** the HE6/T2 adjudication's return (T2's dated consumption-record EOF append, commit `66062771`, raised by `spec/EFF-HE6.md` OPEN-CALL 2) as five new rows, HYP.150–154. **(2)** the 0a sweep's six named supplier-findings (`docs/PROJECT_STATE.md` append **#53** L4725–4733) as six new MAINTENANCE QUEUE actions, MQ-7–12 — one of which, MQ-7 (GENTOW6's unresolvable commit token), turned out to be **already landed mid-fold** by a dated correction append discovered while verifying it (commit `b8365d9e`), so it is recorded as MQ-LANDED rather than pending. **(3)** chapter G's effect on the four standing rows its own §10 structural-edge table names: HYP.137 gets the blueprint's own H-2 honesty-block confirmation (disclosure, not discharge, plus G.76's landed lower-bound half of its bracket); HYP.27 gets a genuine partial discharge at `n = 2` (`leanfinal/Uniformity/ChapG/G36.lean`, `G37.lean`); HYP.28 and HYP.29 are checked against G.72/G.71 and confirmed NOT discharged, in the blueprint's own words. All four recorded as v7 ARC NOTEs with no bucket change. **(4)** the WELD-ZERO arc's continuation past v6's "clean-pass 1 of 2": append **#56** (L4778–4799) reassigns the still-owed second (model-diverse) confirmation pass from gpt-5.6-sol to a Fable-max agent, launched and **IN FLIGHT** at fold time (no commit lands it yet) — recorded at HYP.148/149 as v7 ARC NOTEs; nothing is licensed. **(5)** the Fable-max substitution regime itself, as a standing header note plus an annotation on MQ-1 (the one existing MAINTENANCE QUEUE action append #56 names explicitly). **No row's mathematics is proved by this fold; five rows are added (149→154), none of the 149 pre-existing rows changes bucket.**

> **THE REVIEW-BOUNDARY POLICY (Q4, append #47 — supersedes the per-node SPEC-SIGNED design).**
> Human-checked = **the MAIN statement and definitions ONLY**: the types, the uniformity
> theorem, `genuineDensity`/`decidedDensity`, and the cites. Append #47, verbatim: *“every
> intermediate node is defined/proven as a consumer or discharger of these and is ‘forced right
> if the entire project works out’; the Hensel statements take care of themselves.”* Append #48
> adds the changed definitions’ faithfulness paragraphs (unit-note §8) to the core set.
> **Consequence for this file:** a per-row FAITHFULNESS or “deserves a human read” burden on a
> **non-core** row is **LIFTED** — such rows keep their NODE disposition as ordinary
> proof-packaging work and are no longer owner-visible. Rows *inside* the core set are stamped
> `[CORE-SET]` and stay human-review items. The policy changes the **review surface**, not any
> row’s mathematical status, and it lifts nothing from a CARRY or MATH row.

> **THE P4 RENAME (Q5, executed — append #48).** Old `genuineDensity` → **`decidedDensity`**
> (the certified/inner route); old `upperDensity` → **`genuineDensity`** := `⨅N possibleSeq`
> (the limit of the proportion of coefficient classes consistent with σ — **THE** density).
> Convention: unsuffixed = the density; `_decided` = the certified route. Every pre-rewire
> occurrence in this file has been swept and is stamped **[RENAMED per P4]** at the point of
> use. Names re-verified in the tree at HEAD:
> `leanfinal/Uniformity/Density/GenuineDensity.lean:245` (`def decidedDensity`), `:266`
> (`def genuineDensity`), `:348` (`genuineDensity_eq_of_drainage`);
> `leanfinal/Uniformity/Density/Statement.lean:71` (`UniformityStatement`), `:84`
> (`UniformityStatementDecided`), `:166` (`TotalMassOne`), `:174`
> (`totalMassOne_of_drainage`); `Gates.lean:125` (`drainage_one`), `:159`
> (`sum_genuineDensity_eq_one_of_drainage`).

> **THE FABLE-MAX SUBSTITUTION (append #56, 2026-08-15).** Asvin: *"try (on our branched path)
> to finish the blueprint with fable on max reasoning instead of sol pro 5.6 (and the other
> tasks we initially deferred to sol pro)."* The sol-deferred queue this reassigns, verbatim from
> #56: **spec/blueprint cross-reads, the WELD-ZERO + JD0 confirmation passes, the n=2 adversarial
> pass, and hard-chapter authorship E/C.** Codex's Tuesday cross-read window becomes **optional
> belt-and-braces** (the only cross-FAMILY check — retained where cheap) rather than a blocking
> requirement. **Consequence for this file: wherever a row or MAINTENANCE QUEUE action reads
> "CODEX CROSS-READ OWED", "hostile arc owed", or names a gpt-5.6-sol confirmation pass as still
> owed, and that owed review falls inside the reassigned queue above, it may now be discharged by
> a Fable-max agent — codex is optional for it, not required.** This does not retroactively
> license anything already recorded as owed; it changes who may supply the review, not whether
> one is still needed. Two standing items it names directly: **MQ-1** (the n=2 adversarial pass,
> named explicitly) and the **WELD-ZERO arc's second confirmation pass** (HYP.148/149 — see the
> v7 ARC NOTEs there; the Fable-max pass is LAUNCHED and IN FLIGHT at fold time, per #56's own EOF
> line, "WELD-ZERO confirmation pass (pass 2 of 2) runs on Fable-max now"). Honesty note carried
> from #56 itself: Fable-reviewing-Opus is cross-*tier* but same-*family* decorrelation, weaker
> than the codex cross-family check it substitutes for — recorded, Asvin's call, not this file's
> to second-guess.

## Ledger

### Capstone and low-degree interface

HYP.01  `typeOf` faithfulness
WHERE: `leanfinal/notes/GENUINE_DENSITY_2026-08-13.md`, STATUS/trust-boundary discussion.
STATEMENT: On the `disc ≠ 0` locus, the gcd-defined `typeOf` agrees with the classical ramification-degree/residue-degree multiset.
CONSUMED BY: **[RENAMED per P4]** `decidedDensity` AND `genuineDensity` (both post-rewire names — the type map keys both routes), `UniformityStatement`, and every classical-to-Lean splitting-type transfer.
CLASS: lean-open-statement
PROPOSED DISPOSITION: NODE **[CORE-SET]** — formal faithfulness review and packaging; `typeOf_degree` is landed. The Q4 policy does NOT lift this one: `typeOf` is the engine of the type definition, so its faithfulness to the classical (e,f)-multiset is inside the human-reviewed core set.

HYP.02  `eq_of_add_mul_eq`
WHERE: `leanfinal/notes/HENSEL_FACT_2026-08-13.md`, §6.1.
STATEMENT: The degree-bounded map (u,v) ↦ hu+gv is injective, hence bijective with landed surjectivity; this is uniqueness of exact solve S3, not uniqueness in a congruence class.
CONSUMED BY: optional injectivity refinements of two-block Hensel; the n=3 consumer does not obviously need it.
CLASS: lean-open-statement
PROPOSED DISPOSITION: NODE — equal-rank finite-free-module/Orzech proof unit.

HYP.03  n-fold Hensel factorization
WHERE: `leanfinal/notes/HENSEL_FACT_2026-08-13.md`, §§6.2–7.
STATEMENT: A finite pairwise-coprime residual factorization lifts to the corresponding finite monic factorization.
CONSUMED BY: general-degree factorization and n≥4 splitting-type assembly.
CLASS: lean-open-statement
PROPOSED DISPOSITION: NODE — induction from the landed two-block theorem using `IsCoprime.prod_right`.
**DISCHARGED 2026-08-14 (CERTAIN-NODES BATCH D, CN-17)**: `Uniformity.Hensel.exists_monic_factorization_finset` (`leanfinal/Uniformity/MultiHensel.lean:111`, commit `bbe155c6`), sorry-free, Lean-core axioms (`[propext, Classical.choice, Quot.sound]`, `leanfinal/notes/CN_BATCH_D_2026-08-14.md`). Signature verified verbatim at the file: for a finite index set `s`, monic `f`, and a pairwise-coprime monic residual factorization `g₀ : ι → Polynomial (ResidueField R)` with `f.map (residue R) = ∏ i ∈ s, g₀ i`, there exists a monic lift `g : ι → Polynomial R` with `f = ∏ i ∈ s, g i`, each `g i` reducing to `g₀ i` and matching its degree — exactly the row's STATEMENT, "a finite pairwise-coprime residual factorization lifts to the corresponding finite monic factorization," at general `ι`/`s` rather than the landed two-block case. Proved exactly as the PROPOSED DISPOSITION guessed: `Finset.induction_on` over the landed two-block `Hensel.exists_monic_factorization_dvr`, with `IsCoprime.prod_right` supplying the peeled block's coprimality to the product of the rest (private auxiliary `exists_monic_factorization_finset_aux`, line 47). Uniqueness is deliberately NOT part of the discharged statement (matches the row's own silence on it). **Residual scope, not covered by this discharge**: composing this with `typeOf_mul` (CN-03, also landed 2026-08-14, `Uniformity.Density.typeOf_mul`) into the full order-0 leaf law at every degree is flagged but not yet assembled (`spec/CERTAIN_NODES_2026-08-14.md` REJECTED R10) — the row's own "n≥4 splitting-type assembly" consumer still awaits that weld.

HYP.04  strong Hensel inequality
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.
STATEMENT: If monic F has v(F(x₀))>2v(F′(x₀))=2w with w≥1, some root r has v(r−x₀)>w.
CONSUMED BY: repeated-root cubic recursion and `CertRam3`.
CLASS: lean-open-statement
PROPOSED DISPOSITION: MATH — medium formal proof absent from the corpus.
**DISCHARGED 2026-08-14 (UNIFORMITY-P5)**: `Uniformity.Hensel.strongHensel` /
`strongHensel_addVal` (`leanfinal/Uniformity/StrongHensel.lean`), general complete-DVR bundle,
sorry-free, Lean-core axioms. Landed STRONGER than the row: no monicity, no `w ≥ 1`, sharp
distance `k − w`, plus uniqueness in the disc `v(· − x₀) > w`. Non-vacuity gate `gate_fires`.
Consumer: `leancheck/UniformityCheck/P5Consume.lean::exists_cubic_root_strong(_addVal)`.
Note: `leanfinal/notes/P5_INFRA_2026-08-14.md` §1.

HYP.05  `typeOf` shift invariance
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.
STATEMENT: Integral translation X↦X+c preserves `typeOf`.
CONSUMED BY: cubic recentering at c≠0.
CLASS: lean-open-statement
PROPOSED DISPOSITION: MATH — small formal lemma absent at the `typeOf` level.
**DISCHARGED 2026-08-14 (UNIFORMITY-P5)**: `Uniformity.Density.typeOf_shift`
(`leanfinal/Uniformity/Density/TypeOfInvariance.lean`), unconditional, general DVR, sorry-free,
Lean-core axioms. Consumer:
`leancheck/UniformityCheck/P5Consume.lean::typeOf_ram3_of_eisenstein_shift`.
Note: `leanfinal/notes/P5_INFRA_2026-08-14.md` §2.

HYP.06  `typeOf` scale invariance
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.
STATEMENT: Under X=πᵐY, the normalized polynomial has the splitting-type relation asserted by the recursion.
CONSUMED BY: cubic depth reduction and recurrence.
CLASS: lean-open-statement
PROPOSED DISPOSITION: MATH — medium formal work.
**DISCHARGED 2026-08-14 (UNIFORMITY-P5)**: `Uniformity.Density.typeOf_scaleRoots` (backward form,
no side condition) and `Uniformity.Density.typeOf_scale` (the recursion's own
`F(π^m Y) = π^(m n) G(Y)` phrasing), general DVR, sorry-free, Lean-core axioms; non-vacuity gate
`typeOf_scale_gate`. Consumer: `leancheck/UniformityCheck/P5Consume.lean::typeOf_cubic_scale`.
NOTE the residual gap this does NOT close: the LEVEL bookkeeping across the extraction
(classes mod π^N ↦ classes mod π^(N−3m)) is a separate, still-open statement — see
`leanfinal/notes/P5_INFRA_2026-08-14.md` §7 item 3, which is part of HYP.08.

HYP.07  nonintegral-slope `CertRam3`
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.
STATEMENT: The nonintegral Newton-slope branch has the asserted cubic ramification type.
CONSUMED BY: cubic menu exhaustiveness and exact cubic densities.
CLASS: lean-open-statement
PROPOSED DISPOSITION: MATH — norm/valuation proof absent.

HYP.08  cubic tail recurrence
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §9.4.
STATEMENT: u(N) ≤ q^(−N/2)+q^(−5)u(N−3).
CONSUMED BY: drainage of the cubic triple-root branch.
CLASS: named-obligation
PROPOSED DISPOSITION: MATH — stated but not derived.

HYP.09  cubic triple-root drainage
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, STATUS and §§8–12.
STATEMENT: After finite classified cubic strata are removed, the infinite triple-root recursion has null complement.
CONSUMED BY: `UndecidedVanishes O 3 σ`, `drainage_three_of_triple`, and exact cubic assembly.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: MATH — depends on HYP.04–HYP.08 and remains unproved.

HYP.10  exactly five cubic splitting types
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§8–12.
STATEMENT: Every separable monic cubic has one of the five listed (e,f)-multisets.
CONSUMED BY: converse drainage and the cubic sum-to-one — **[RENAMED per P4]** that target is now the named Prop `TotalMassOne` at n=3, whose supplier is `sum_genuineDensity_eq_one_of_drainage` (`Statement.lean:166/174`); it is NOT a clause of `UniformityStatement`.
CLASS: lean-open-statement
PROPOSED DISPOSITION: NODE — finite multiset enumeration from landed `typeOf_degree`; LOW-CONFIDENCE until checked in Lean.

HYP.11  exact cubic densities
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§8, 10.3, 12; W12 HMENU3/HEX3 perimeter.
STATEMENT: Each cubic splitting type has the asserted rational density in q.
CONSUMED BY: degree-three `UniformityStatement`.
CLASS: lean-open-statement
PROPOSED DISPOSITION: MATH — resultant-weighted peeling, drainage, and DEEP-X/B1/B2/B3 tiers remain.

HYP.12  ordering convention for (e,f)
WHERE: `N3_CHECK_2026-08-13.md`, §§3,8; `GENUINE_DENSITY_2026-08-13.md`.
STATEMENT: Implemented ordering and multiset normalization agrees with the classical convention.
CONSUMED BY: exact-event equality with `typeOf`.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE **[CORE-SET]** — human definitional audit. **Question 4 ANSWERED [v5, append #47]:** not by discharging this row but by *placing* it — the `(e,f)` ordering/multiset convention is part of the type definition, so it stays inside the human-reviewed core set (“the types”) and remains a human read. What lifts is the *per-row* framing: it is reviewed as one clause of the core-set definitional audit (HYP.98), not as a standalone owner call. No owner question remains.

### Citation and theorem-scope residue

HYP.13  all-O citation swap
WHERE: `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`, verdict table.
STATEMENT: About thirteen imported facts must cite all-complete-DVR sources rather than narrower p-adic surrogates.
CONSUMED BY: external-reference layer.
CLASS: cite-scope-residue
PROPOSED DISPOSITION: NODE — replacement sources are identified.

HYP.14  `NS-6` stopping criterion
WHERE: `CITE_SCOPE_RESOLUTION_2026-08-13.md`, NS-6.
STATEMENT: The tower stops at order r iff every order-r residual is separable; descent continues iff some is inseparable.
CONSUMED BY: higher-degree descent/drainage.
CLASS: cite-scope-residue
PROPOSED DISPOSITION: NODE — short GN15/AGNPRW corollary.

HYP.15  `NS-7` termination
WHERE: `CITE_SCOPE_RESOLUTION_2026-08-13.md`, NS-7 and §5 Stage 3.
STATEMENT: The project’s MacLane/Okutsu construction terminates over every complete DVR in scope.
CONSUMED BY: finite certificates, GENIND termination, finite menu/drain descriptions.
CLASS: cite-scope-residue
PROPOSED DISPOSITION: **CARRY-as-CITE — question 1 ANSWERED [v5, append #47]** *(owner, verbatim: “cite thm 5.2 for now at least”)*. The choice is made: **[AGNPRW] Thm 5.2 is the termination resolution for the informal corpus**, and the internal F-2 index-descent proof is NOT taken. The row stays CARRY because the answer resolves the *branch*, not the *obligation* — append #47 continues: *“in Lean, NS7 stays a carried hypothesis until proved or declared-with-faithfulness.”* So `NS7(O)†` stands in preview Display A, now **undaggered** (no owner call left on it) and re-labelled as a cite rather than a choice. Three consequences recorded, none of them an owner question: **(a)** citing a theorem *by number* makes HYP.17’s publisher-number verification load-bearing on this row — it is elevated there; **(b)** MQ-3 ([GMN12] §4 characteristic audit, unperformed) qualified only the internal-F-2 branch, which is not taken, so MQ-3 **lapses as a question-1 rider** and survives only as general cite hygiene; **(c)** the owner’s “for now at least” is recorded as a revisit licence, not as an open question — re-opening would be a new decision, not an unanswered one.

HYP.16  `NS-15` finite-depth bound
WHERE: `CITE_SCOPE_RESOLUTION_2026-08-13.md`, NS-15/F-3.
STATEMENT: If retained, replace B(n,p) by depth ≤ ½v(disc f).
CONSUMED BY: `L5fix(b)` and finite certificates; capstone needs finiteness, not this constant.
CLASS: cite-scope-residue
PROPOSED DISPOSITION: **CLOSED — LAPSED per question 1 [v5, append #47 / COR-13].** The coupling recorded at COR-13 fires: the `≤ ½ v(disc f)` depth bound was available **only** on HYP.15’s internal-F-2 branch, and the owner took the **cite** branch, which *“gives no explicit constant.”* So the replacement this row proposed is not available and is not retained — the row is disposed, not deferred. Nothing downstream breaks, because the row’s own CONSUMED-BY already records that **the capstone needs finiteness, not this constant**, and finiteness is exactly what the [AGNPRW] Thm 5.2 cite supplies (HYP.15). Re-opening condition, stated so it is not lost: any future consumer that needs an *explicit* depth constant must re-open the F-2 branch — and would then also inherit MQ-3, the unperformed [GMN12] §4 characteristic audit.

HYP.17  publisher-number verification
WHERE: `CITE_SCOPE_RESOLUTION_2026-08-13.md`, verdict table.
STATEMENT: Check AGNPRW, GN15, and Kuhlmann theorem numbering against publisher versions.
CONSUMED BY: bibliography and attribution — **and, since v5, HYP.15’s trusted base.**
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE **[CORE-SET]** — **ELEVATED at v5, no longer “bibliographic only.”** Question 1 answered by citing **[AGNPRW] Thm 5.2 by number**, so the AGNPRW half of this row is now load-bearing: if the publisher numbering differs, the project’s termination cite points at the wrong theorem. Cites are inside the Q4 core set, so this stays owner-visible as a review item — but it is a bounded lookup, not an owner decision, and it opens no question.

HYP.18  `AX-DEFECT` correction
WHERE: `CITE_SCOPE_RESOLUTION_2026-08-13.md`, NS-14.
STATEMENT: Use discreteness for defectlessness and state the separability fence: only inseparable extensions need characteristic zero; uses are on disc≠0.
CONSUMED BY: external field-theory layer.
CLASS: cite-scope-residue
PROPOSED DISPOSITION: NODE — Kuhlmann Theorem 3.3 with corrected scope.

### W12 and general induction

HYP.19  `[W12-H]`
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-08.md`, §4.2 L1132–1167.
STATEMENT: Only order≥2 clause (i), hence n≥4 composite stages, depends on [H-a]–[H-e]; n=2 is unconditional and n=3 has menu/exhaustion only.
CONSUMED BY: W12 composite stages and n≥4 capstone.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — aggregate only; omit when children are expanded.

HYP.20  `[H-a]` / JC warrant
WHERE: `W12_PROOF_2026-08-08.md`, §4.2.
STATEMENT: GRTJC supplies the composite-stage warrant with its own displayed conditionality retained.
CONSUMED BY: W12 composite partition.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — child conditions such as DMULT-S remain separate.

HYP.21  `[H-b]` / JB row 12
WHERE: `W12_PROOF_2026-08-08.md`, §4.2 L1143–1145.
STATEMENT: JB row-12’s u≥0 membership proviso holds on the unbounded grid.
CONSUMED BY: **[WELD-FACE-AUDIT 2026-08-13, NOT-REACHED]** No capstone-path consumer. W12’s own dependency ledger, L1507–1509 (re-verified at L1508): the six ACCEPTED weld notes are “consumed ONLY in §S5’s composition display and as [W12-H]’s named inputs (S4.2); NO S2/S3 proof depends on them”. The n≥4 route actually taken is GENIND’s (CS-1..3) discharged by GENH4/GENHN; GENIND L860 (re-verified): “n ≤ 3 program never consulted [W12-H].” The only other reach is `W11-BOX-1`’s S4.3 program (HYP.146), itself unproved and superseded.
CLASS: hypothesis-box
PROPOSED DISPOSITION: **NODE** (re-dispositioned CARRY→NODE, COR-WFA-06) — record OUT of the cone; dropped from preview Display A (it sat inside the `JB-NOLEG` conjunct). Represented for GRTJB-internal purposes by HYP.75. Needs-Asvin question 2 is ANSWERED by the audit; the row no longer carries an owner call.

HYP.22  `[H-c]` / J-D1 value package
WHERE: `W12_PROOF_2026-08-08.md`, §§4.2 L1146–1148, 5.
STATEMENT: J-D1 is conditional on the six weld notes’ boxes plus Σ-law, including VD-m, C-coll, R-coll, DMULT-S, and PERIM-μ.
CONSUMED BY: **[WELD-FACE-AUDIT 2026-08-13, NOT-REACHED]** Only `[W12-H]` (§S4.2) and W12 §S5’s composition display — the route W-12 priced but did not take. The actual (A0)/(A1) suppliers at n≥4 are GENH4.C and GENHN.C per W12’s own [r4] FIRING CHECK table (L437–447), and both declare no weld face inside a count law (GENH4 L58, re-verified: “no weld face sits inside any count law below”; GENHN L98–99, re-verified: “no weld face sits inside the count laws”). W12-BOX-1 (L1213–1214, re-verified): “No count law at composite stages is claimed; the route is priced in S4.2 ((H-a)–(H-d))”. GENIND L1524 (re-verified): WELDMASTER / DULEMMA / [W12-H] are “named in S7.1’s (CS-1..3) pricing only”.
CLASS: hypothesis-box
PROPOSED DISPOSITION: **NODE** (re-dispositioned CARRY→NODE, COR-WFA-07) — record OUT of the cone; the whole `[H-c]` conjunct is dropped from preview Display A. Child accounting: 83–86 (VD-m, C-coll, R-coll, PERIM-μ) inherit NOT-REACHED; 76/77 are NOT-REACHED on their own rows; **74 is re-parented off `[H-c]`** and carried on its own REACHABLE-AND-CONSUMED footing. **Honest gap, deliberately not closed in this fold:** rows 83–86 remain dispositioned CARRY though their only parent conjunct has left the preview — no COR-WFA line authorizes re-dispositioning them, so the inconsistency is recorded rather than silently resolved (see the stamp on each of HYP.83–86 and `CHANGES-FROM-v3` item ORPHAN-1).

HYP.23  `[H-d]` residual censuses
WHERE: `W12_PROOF_2026-08-08.md`, §4.2.
STATEMENT: Once [H-a]–[H-c] identify the reads, universal residual-tower censuses hold level by level.
CONSUMED BY: W12 weights and GENIND counts.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — conditioned finite-field census nodes.

HYP.24  `[H-e]` decision plus window pinning
WHERE: `W12_PROOF_2026-08-08.md`, §4.2 L1153–1167; GENIND CS-3.
STATEMENT: Separable order≥2 residuals decide σ for all disc≠0 lifts, and all consumed read data are pinned inside the stage window by the [H-a]/[H-b] leg.
CONSUMED BY: W12/GENIND leaves and composite-stage A0.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — GMN supplies only decision; project-internal pinning remains. **SUPPLIER RE-SOURCED (v4, COR-WFA preview item iv):** W12’s own (H-e) text sources the window pinning to “the (H-a)/(H-b)-leg”, but the audit shows that leg is not on the taken route (HYP.21, HYP.22 both NOT-REACHED). On the route actually walked the pinning is supplied **elementarily**, by `LEMMA GENHN-3` (caps, raggedness, consultation — `GENHN_PROOF_2026-08-08.md` L741–770, heading re-verified at L741) together with GENIND-2’s consulted-height bound. **The conjunct itself does not move** — `(H-e)-window-pinning` stands unchanged in preview Display A; only its stated supplier changes, and it changes from an unreachable weld leg to an elementary in-cone one.
**ARC NOTE (2026-08-16, unit OM-6).** The elementary supplier's transcription gap (CHAP-I honesty I-11(ii) / orchestrator item O-2: `EFF.GENHN.29` consumed by committed H only at H.51's (c)-bound) is now BOOKED: `leanfinal/Uniformity/ChapH/H89w.lean` (H.89-adjacent appendix per the H09w precedent; blueprint AMENDMENT A-H.3) lands GENHN-3's (c) general-`e₁` congruence bound, (b) general string ends + band count, (a)'s rider-corrected interior criterion with the no-tie/undercut computation, the `[r2]`/CAP-GEN band-census arithmetic tied to H.44's `pinCensus` at the committed `(1,3,2)` instance numbers, and (d)'s update-map descent (both ring types in one statement) — 17 declarations, sorry-free, Lean-core only. One finding: the (c) display's "inside the string" needs an occupancy scope pin (machine-refuted at `(e₁,h,m) = (3,2,1)`; the same family as HYP-adjacent `EFF.GENHN.28`'s `a(m) ≥ 0` defect); landed in the occupied form, source not edited. **Still carried, disposition UNCHANGED: CARRY** — the pinning half's general-genre content remains `StageInterface.hwin` (HYP.36, GC-5's table, not discharged) and `GENHN-CAP-GEN`'s reader rule remains un-formalized (CHAP-H §16 item 3 upheld); the `e₁ = 2` discharge (H.89) and its fence are unchanged. Unit record: `docs/openmath-campaign/OM-6_window-pinning_2026-08-16.md`; numeric certification `verification/om6_window_pinning_check.py` (26/26).

HYP.25  `A0` lift well-posedness
WHERE: `W12_PROOF_2026-08-08.md`, W-12.D L267–303.
STATEMENT: Every window-decided core-family member has all disc≠0 O-lifts of the read’s type.
CONSUMED BY: W12.D and capstone measure identity.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: CARRY — fixed-n public assumption with load-bearing fence.

HYP.26  `A1` exact core menu
WHERE: `W12_PROOF_2026-08-08.md`, W-12.D L267–303.
STATEMENT: For fixed n and all q simultaneously, a finite disjoint q-independent family list carries internal σ_F labels and exact weights; σ is not an A1 binder.
CONSUMED BY: W12.D for every degree-n type.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: CARRY — public fixed-n interface.

HYP.27  `A2` drainage
WHERE: `W12_PROOF_2026-08-08.md`, W-12.D L267–303.
STATEMENT: For fixed n, the mass outside visible core families, including undecided and boundary families, has r(N)/q^(nN)→0.
CONSUMED BY: exhaustion and capstone equality.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: CARRY — n≥4 supplier is DRAIN-N4/CS-1Q.
**v7 ARC NOTE (2026-08-15, chapter G).** `blueprint/CHAP-G_base_cases_menus.md` §10's structural-edge table adds `BP.G.36 → HYP.27`: "G.36 discharges `(A2)` drainage **at `n = 2`** with the exact rate." Re-verified in the tree: `leanfinal/Uniformity/ChapG/G36.lean:43`, `theorem undecidedCount_two_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) : undecidedCount O 2 N = residueCard O ^ N`, sorry-free, Lean core only (`#print axioms` line present at the file's own AxCheck section) — general complete DVR with finite residue field, general `N`, both characteristics, no hypothesis beyond the standing bundle. This is a genuine **partial discharge, `n = 2` only**: it sharpens the previously-landed lossy bound `undecidedCount_le` (`Drainage.lean:757`, which only gives `q^(3M)` at level `2M`) to the exact law, and `G37.lean` derives the exact rate `q^(-N)` from it. The row's own STATEMENT is universally quantified over `n`; the `n = 2` instance is now DISCHARGED but the general claim — in particular n≥4, whose supplier stays `DRAIN-N4`/`CS-1Q` as written above — is untouched. **Disposition unchanged: CARRY**, now with one degree fully landed.

HYP.28  `hMenu3` / `W12-BOX-2`
WHERE: `W12_PROOF_2026-08-08.md`, boxes.
STATEMENT: Cubic cases form the stated finite disjoint menu.
CONSUMED BY: degree-three W12.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — HMENU3 perimeter; HYP.11 records unproved deeper tiers.
**v7 ARC NOTE (2026-08-15, chapter G).** `blueprint/CHAP-G_base_cases_menus.md` §10's structural-edge table adds `BP.G.72 → HYP.28`: “G.72 is the *type-level shadow* of `(hMenu-3)`, not its discharge (H-3).” Re-verified: `leanfinal/Uniformity/ChapG/G72.lean` lands `totalMass_three_of_drainage` (`Σ_σ genuineDensity O 3 σ = 1` over the five named types `{c3split, c3linInert, c3inert, c3linRam, c3ram}`, **given** drainage) and the unconditional `one_le_sum_three` (`1 ≤ Σ_σ genuineDensity O 3 σ`), both sorry-free, Lean core only. This exercises the five names as a well-typed `Finset` sum (using `c3_pairwise_ne`'s ten distinctness conjuncts) but does **not** prove they are the finite disjoint menu this row asserts, nor that the menu is exhaustive — G.72's own docstring: “the individual five values stay unproved here; this node only gives the sum.” Chapter G separately proves the type list (exactly five cubic types occur, G.49–G.50) and `CoveringMenu O 3` (G.51), but not the 53-family count obligation `hMenu3` itself asserts (blueprint honesty-block item H-3). **Not discharged; disposition unchanged: NODE.**

HYP.29  `hExhaust3` / `W12-BOX-3`
WHERE: `W12_PROOF_2026-08-08.md`, boxes.
STATEMENT: Cubic menu exhausts the separable event up to a null set.
CONSUMED BY: degree-three W12.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — HEX3 perimeter; ANNEX-2 correction remains indexed. TAIL-CERT=HEX3-BOX-1=HM3-BOX-1 is NO LONGER index-only: it is promoted to its own row HYP.137 because it has a named live consumer (GENIND’s S8.2 W-12.B consistency clause). Its `hExhaust3` non-consumption is preserved — see HYP.137 (v3 delta item 2).
**v7 NOTE (2026-08-15, chapter G).** Checked against the blueprint's structural-edge table: `BP.G.71 → HYP.29`, "G.71 names `(hExhaust-3)` as its explicit hypothesis (frontier, H-1)." Chapter G's own honesty block H-1 is explicit that the `n = 3` exact conservative-residue law (THEOREM HEX3.A) is "not a chapter-G Lean deliverable" — the chapter lands its arithmetic layer unconditionally and the σ-undecided lower bound (G.76, see HYP.137's v7 ARC NOTE) but leaves the HEX3 LEMMA H-1/H-2/H-3 bridge that would discharge `hExhaust3` itself as "the named frontier." **Not discharged; disposition unchanged.**

HYP.30  `W12-BOX-4` / `DRAIN-N4`
WHERE: `W12_PROOF_2026-08-08.md`; `TIGHTNESS_CENSUS_2026-08-11.md`, I-1.
STATEMENT: For every n≥4, the unclassified complement of the general finite menu is null.
CONSUMED BY: A2 and n≥4 capstone.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — lower supplier HYP.36; distinct from GENIND-BOX-4.

HYP.31  `[GENIND-H]`
WHERE: `GENIND_PROOF_2026-08-08.md`, §S1 L186–227 and L3081–3084.
STATEMENT: Empty for n≤3; for n≥4 contains CS-1/2/3/EXACT, with GENHN-HE first live n=6 and GENHN-TOW-1 additionally at n≥8.
CONSUMED BY: general menu and drainage.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — aggregate only.

HYP.32  `CS-1` count-fibration
WHERE: `GENIND_PROOF_2026-08-08.md`, §S7.1 L1123–1146.
STATEMENT: Every composite/mixed stage has the asserted exact count-fibration and product transport.
CONSUMED BY: GENIND recursion, A1, and Step-4/A2 drainage rate.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — uniform embedded/mixed transport unproved.

HYP.33  `CS-2` stage bracket
WHERE: `GENIND_PROOF_2026-08-08.md`, §S7.1 L1147–1168.
STATEMENT: Each stage has the claimed mass-normalized bracket.
CONSUMED BY: measure recursion and exact weights.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — no general-genre proof identified.

HYP.34  `CS-3`
WHERE: `GENIND_PROOF_2026-08-08.md`, §S7.1 L1169–1171.
STATEMENT: Separable stage residuals decide σ with (eE,f[K-ext]) for all disc≠0 lifts, with HYP.24 window pinning.
CONSUMED BY: GENIND leaves.
CLASS: named-obligation
PROPOSED DISPOSITION: MERGED — exactly HYP.24 at GENIND layer.

HYP.35  `CS-EXACT`
WHERE: `GENIND_PROOF_2026-08-08.md`, §S7.1 L1172–1190.
STATEMENT: CS-1+CS-2 deliver an exact finite q-power sum for every stage menu and stage drain, not asymptotic or bound-only laws.
CONSUMED BY: induction’s fourth member and rational extraction.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — bound-only drainage does not close induction.

HYP.36  `(CS-1Q)`
WHERE: `GENIND_PROOF_2026-08-08.md`, §C2-G1 L3592–3722.
STATEMENT: Both clauses hold: M_G≥e(N−1−H)−Δ_G, and the displayed digit-loss rate follows; the rate does not by itself assert all residual mass is zero.
CONSUMED BY: DRAIN-N4/A2.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — embedded/mixed affine ledgers are not universally checked.

HYP.37  `GENIND-BOX-2`
WHERE: `GENIND_PROOF_2026-08-08.md`, §S8 L1357–1360.
STATEMENT: Displayed schema expands faithfully to every induction route.
CONSUMED BY: partition auditability.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — presentation debt.

HYP.38  `FGMN-MAIN` Lean declaration
WHERE: `TIGHTNESS_CENSUS_2026-08-11.md`, I-3.
STATEMENT: Declare the cited FGMN theorem faithfully and wire consumers.
CONSUMED BY: higher-order leaves and factorization.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — declaration/wiring.

HYP.39  `JD0-BAR`
WHERE: `TIGHTNESS_CENSUS_2026-08-11.md`, I-5.
STATEMENT: J-D0 gauge-blindness is PROVED grade with 68,523/0 machine evidence but below process bar because the two-clean hostile arc has not run.
CONSUMED BY: JD0 inside [H-c] — **LOCATOR CORRECTED (v4, COR-WFA-02 knock-on):** `[H-c]` is NOT J-D0’s home on the capstone path. J-D0 is consumed DIRECTLY at seven cone notes at FRAME grade; see HYP.74 for the verified site list. This grade cap therefore bears on those seven sites, not on the unreachable `[H-c]` package.
CLASS: grade-cap
PROPOSED DISPOSITION: **CLOSED-SIGNED — question 6 ANSWERED [v5, append #49].** The owner **signed the 68,523/0 machine grade as the bar**; the two-clean hostile arc is not required for J-D0. Reasoning recorded at #49 in the owner’s frame: J-D0’s gauge-blindness *“MUST be true for the proof strategy/uniformity to work at all”*, and conviction of truth implies any proof defect would be fixable. The grade cap therefore no longer caps the seven direct cone sites (HYP.74) at which J-D0 is consumed. **The optional post-reset codex pass is NOT cancelled — it is demoted to belt-and-braces and moved to the maintenance queue as MQ-4**, so this row closes without swallowing a queued action.

HYP.40  single-w B″ transport
WHERE: `TIGHTNESS_CENSUS_2026-08-11.md`, I-2; `GENTOW5_WI_2026-08-10.md`; SOL certification row 18.
STATEMENT: The single-w monomial B″ transport at i≥3 is certified 2/2; surviving work is S12.1 scope re-verification, not pending PE2 and not a “window lemma.”
CONSUMED BY: GENTOW5-B(a) residual/certificate legs, FGMN displays, and all deep towers.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — scope audit; does not discharge HYP.63.

### T2 carrier obligations and grade

HYP.41  `(LB1)`
WHERE: `T2_SIGMA_LADDER_MASTER_2026-08-12.md`, §S1.7B L2214 and acceptance.
STATEMENT: Every triggered level-one state has monic-side and label blocks with full developments, single-side hulls, pure residuals, product identities, disjoint exhaustive root partitions, and inherited continuation data.
CONSUMED BY: clause 4, S4.1, and S4.2 exclusions.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — one of exactly two standing T2 obligations.

HYP.42  `(MP1)`
WHERE: `T2_SIGMA_LADDER_MASTER_2026-08-12.md`, §S1.8A L2423–2438 and acceptance.
STATEMENT: Whenever the recentered key divides its block, quotient G′ satisfies WINDOW, full development/ACCOUNT/S1.7 and height/lift/frame/origin/degree data, and the peeled key has certified orbit/(e,f) decomposition—items 2–5.
CONSUMED BY: clause 5, S1.8 induction, and RANK item 3.
CLASS: named-obligation
PROPOSED DISPOSITION: CARRY — the other standing T2 obligation.

HYP.43  `(SEC-RANK)`
WHERE: `T2_SIGMA_LADDER_MASTER_2026-08-12.md`, L2341–2353, L2391, L4496.
STATEMENT: Secondary rank σ_C into a well-founded W_C strictly decreases at each product-1 linear recentering and has no requirement at other transitions.
CONSUMED BY: third RANK component; its descent yields termination and exhaustion.
CLASS: carrier-hypothesis
PROPOSED DISPOSITION: NODE — stipulated carrier data, explicitly not a ledger obligation and fencing no read.

HYP.44  `(RISE)`
WHERE: `T2_SIGMA_LADDER_MASTER_2026-08-12.md`, L3329–3333, L3357, L4497.
STATEMENT: At refine/product-1 recentering, d(Φ_new(ρ))>λ for every refined-class root; HT with k=λ is derived.
CONSUMED BY: refine-step HT, not termination.
CLASS: carrier-hypothesis
PROPOSED DISPOSITION: NODE — stipulated, not a ledger obligation.

HYP.45  `(GRADE)`
WHERE: `T2_SIGMA_LADDER_MASTER_2026-08-12.md`, L4503.
STATEMENT: HE3 is simultaneously attempt grade 0/2 and clean count 1/2; this caps any level-two chain consuming an HE3 pin through S1.8C.
CONSUMED BY: level-one and affected level-two proof-status claims.
CLASS: grade-cap
PROPOSED DISPOSITION: NODE — evidence completion only.

### T1/T3/T5 supplier conditions

HYP.46  canonical-letter scope
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, §1.1 R2-1 L1388–1432 and §5 item 1.
STATEMENT: T1 proves value zero but no arbitrary-depth preceding-letter monomial or terminating reduction; such a description needs `(H-JA-CONJ)_i`, while level two is unconditional.
CONSUMED BY: T1 canonical-form consumers.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — narrow carrier claim and expose supplier.

HYP.47  `C3-ladder-multiplicativity`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L2413–2430 and §5 item 2.
STATEMENT: For consumed s, R_(i+1,sκ̄_i)(N^s)=R_(i+1,κ̄_i)(N)^s.
CONSUMED BY: B-law and higher-depth residual comparison.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — sitewise supplier; level-general name requires verification.

HYP.48  `C3-slot-grade`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L2457–2470 and §5 item 2.
STATEMENT: With s=f_(i+1)−t, β_t=sκ̄_i=(f_(i+1)−t)κ̄_i.
CONSUMED BY: B-law and slot comparison.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — sitewise grade identity.

HYP.49  `C3-graded-scalar-covariance`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L2432–2441 and §5 item 2.
STATEMENT: For consumed homogeneous ladder X and permitted value-zero g, R_(i+1,β)(Xg)=R_(i+1,β)(X)res(g); no all-homogeneous claim.
CONSUMED BY: B-law and canonical comparison.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — sitewise read supplier.

HYP.50  `C3-zero-read`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L2993–3002.
STATEMENT: R_(i+1,β)(0)=0; a zero coherent digit is a zero homogeneous component, not a value-zero factor with zero residue.
CONSUMED BY: zero-digit B-law branches.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — sitewise zero read.

HYP.51  `C3-ladder-nonvanishing`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L3315–3330 and §5 items 2/19.
STATEMENT: The base ladder read is nonzero independently of multiplicativity, covariance, and zero-read.
CONSUMED BY: w_i≠0, rescaling, factor-pattern transport.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — discharged at i=2; explicit level-general supplier required for i≥3.

HYP.52  `C3-read-codomain`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, R11-1 L3655–3672 and §5 item 22.
STATEMENT: Every consumed grade-β read is K_i-scalar-valued, not merely valued in gr(μ_i).
CONSUMED BY: w_i∈K_i×, y↦y/w_i, rescaled key, and factor-pattern transport.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — i=2 is supplied; i≥3 rides an unverified level-general package and is not inferred by T1.

HYP.53  `(H-JA-CONJ_i)`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L1388–1411 and §5 item 1.
STATEMENT: A specified Laurent monomial J_i satisfies res(n̂_i(u_(i+1))/π_(i+1)^(u_(i+1)))=J_i(z₁,…,z_i).
CONSUMED BY: arbitrary-depth preceding-letter specialization.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — imported JA hypothesis; T1 names no discharged supplier/pin.

HYP.54  `(H-JA-RES-CONJ)`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L1448–1479.
STATEMENT: For nonzero H,P,Q, H=y^νQ and P=aQ(by) with a,b units, so support translates by ν and degree shifts by ν.
CONSUMED BY: residual-support/degree comparison.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — exact JA supplier interface. CORRECTED (v3, delta item 7): T1 names “the accepted harness/print conjugation formula” but supplies no grep-verifiable external designation — `spec/EFF-T1-s1of3.md` OPEN-CALL 2, which also refuses the `JA-EPS-CORR` conflation (that unit verifies the origin correction, not this whole-polynomial supplier). The interface has no named source yet; see HYP.141.

HYP.55  `(H-GENHN-CLEAR)`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L1554–1577.
STATEMENT: For r=f₂−t, M=ru₂, u₂>e₂D′h, every product clears by at least r(u₂−e₂D′h)/e₁>0, and collection/Φ′-carry only cancels or moves upward.
CONSUMED BY: outer-side residual computation.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — exact GENHN supplier interface. CORRECTED (v3, delta item 7): the designation T1 cites is refuted. `spec/EFF-T1-s1of3.md` OPEN-CALL 3 — “T1 calls it the accepted `T(b)'(i)` site, but fixed-string grep for that designation in `GENHN_PROOF_2026-08-08.md` returns zero” — re-verified here: `grep -c "H-GENHN-CLEAR" lean/notes/openmath/GENHN_PROOF_2026-08-08.md` = 0. `GENHN-LIFT` covers the lift and must not be invented as the clearance theorem. See HYP.141.

HYP.56  `(H-HETOW-LOCAL)`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L2590–2633.
STATEMENT: HETOW supplies the displayed normalizers, carry data, local bridge, second-level carry equations, and τ(k)=η^(−Q(m(k))).
CONSUMED BY: T1 A2 transport.
CLASS: hypothesis-box
PROPOSED DISPOSITION: NODE — complete local supplier interface.

HYP.57  `(H-VARTHETA-RES_i)`
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L3523–3541/§5 item 21; T5 honesty item 13.
STATEMENT: For i≥3 and s≥0, res(n̂_i(u_(i+1))^s/n̂_i(su_(i+1)))∈K_i.
CONSUMED BY: T1 B-law and C3-key, T5 consumers, and general tower path.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — technical unit to adjudicate whether T5 S11.2 §S2.1 implies it; not an owner question.

**ARC NOTE (2026-08-16, unit OM-8).** The row's named CARRY task — the S2.1-implication adjudication — is PERFORMED: **YES at every DEF GENTOW5-1 instantiation with the canonical node-point residue read (all `i ≥ 3`, all `s ≥ 0` at once), NO for the abstract A-D.2 sitewise carrier at an arbitrary ambient datum ρ.** The discharge decomposes into three legs (OM-8 unit note §3.1): (L1) the letter-lattice factorization — every value-zero normalizer monomial factors uniquely over `(x^{e₁}/π^h, Φ_j^{e_{j+1}}/n̂_j(u_{j+1}))` by triangular descent from the gcd chain, = GENTOW5_PROOF S2.3 step (3)'s accepted computation, independently re-derived and now Lean-general (`leanfinal/Uniformity/ChapD/D62w.lean`: `triangular_descent` + `dvd_stage`; concrete depths 2/3 `deep2_tau_descent`/`deep3_tau_descent` at ALL heights; 400-frame/7007-row sweep); (L2) residue multiplicativity at node points (standard; PARI + equal-char oracles agree at every frame); (L3) letters = (`w`-twisted) ψ-roots ∈ `K_iˣ`. New machine coverage: first `f₄ = 3` three-slot deep frame (p = 5, `(e,f) = (8,3)`), first deep ϑ OUTSIDE the prime field (`ϑ_{3,2} = 2z₂, ϑ_{3,3} = z₂ ∈ F₉∖F₃`), first equal-characteristic deep-twist rows (`F₃((t))`) — `verification/om8_vartheta_deep.py`, GREEN 52/0 bit-identical. The ρ-defeat is REAL at real tower exponents (adversarial `ρ′: γ₃ ↦ ω` kills the carrier where the canonical read holds — LEG D2), so the discharge is exactly AT the canonical read. Lean: NODE D.62 landed in leanfinal at the A-D.2 signature (`D62.lean`, voided form NOT re-landed per I.10's fence) + the `i ∈ {1,2}` corpus proofs transcribed (`hvarthetaRes_levelOne`, `hvarthetaRes_deep2`) + `(H-VARTHETA-RES)₃` reduced to the three letter-memberships (`hvarthetaRes_deep3`) — all sorry-free, Lean-core. **Still carried, disposition UNCHANGED: CARRY** — the residual is supply-side wiring, not an open residue law: (i) E.61's socket must be typed at the A-D.2 form WITH chapter C's canonical residue data (an unpinned ρ is undischargeable); (ii) the T1 site-by-site convention walk (T1's `n̂` system vs the tower's — the bridge reduces to (L1), the walk rides D.64 OPEN-CALL-5's existing route). Unit record: `docs/openmath-campaign/OM-8_deep-twist_2026-08-16.md`.

HYP.58  integral K₁ lift range
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, acceptance standing conditionality.
STATEMENT: Full integral K₁ lift is asserted only for M>D′h.
CONSUMED BY: corresponding lift branch.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — retain strict domain.

HYP.59  `WELD-M-PKG` boundary
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, C7 L726–759 and §5 item 11.
STATEMENT: Five heterogeneous fields assert no single cross-face map, coherence, map uniqueness, or gauge uniqueness beyond anchors.
CONSUMED BY: weld consumers and [H-c].
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — enforce narrow interface.

HYP.60  raw/canonical equality
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, §5 item 5.
STATEMENT: Equality is iff z^ν=1, not iff ν=0 without an order hypothesis.
CONSUMED BY: equality/cancellation tests.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — correct consumers.

HYP.61  dv_i codomain
WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L4239–4241 and L4416.
STATEMENT: dv_i lies in (e(μ_i)/e(μ_r))ℤ generally; only enumerated nonzero consumed arguments are integral, while dv_i(0)=+∞.
CONSUMED BY: valuation and zero-lift branches; gates no C1–C7 conclusion.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — scope typing.

HYP.62  `T3-JOINT-OPEN`
WHERE: `T3_COCYCLE_TELESCOPE_2026-08-12.md`, §8.5 L1065–1081.
STATEMENT: Machine suite lacks a realized p-adic B″ frame with Θ≠1 and w≠1.
CONSUMED BY: realized regression coverage only.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — not merged with HYP.135’s finite graded model.

HYP.63  `[GENTOW5-W(i)]` / 𝒲_(≤i)
WHERE: `T5_WFRAME_2026-08-12.md`, L616, L926–930, L1499–1500; `Q4_output.log`.
STATEMENT: Cumulative 𝒲_(≤i) required by frozen GENTOW5 holds for every i≥3.
CONSUMED BY: T3/T5 higher-depth laws and G5-COND ride list.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: CARRY — WI proves only the induction step, not induction from empty base.

**ARC NOTE (2026-08-16, unit OM-8).** T5 S12.1's named re-verification obligation ("the induction closing the conjuncts from the empty base … NOT performed by the companion as written") is PERFORMED (OM-8 unit note §3.2): the closure is an INTERLEAVED induction — base = the landed GENTOW2 clause (b) at index 2; step = the WI lemma (SOL row 18, CERTIFIED 2/2), whose census consumes clause (b) at index `i−1` only (C-5); chain = frozen GENTOW5's `𝒲_{≤n} ⟹ (a)@n ⟹ Cor 6.4 ⟹ (b)@n` (T5 §4, WF-chain) — so `B i` is never consumed before `W i` and the circularity T5 flagged dissolves (`B 2 → W 3 → 𝒲_{≤3} → B 3 → W 4 → …`). The skeleton is PROVED in Lean (`leanfinal/Uniformity/ChapD/D62w.lean`: `wle_of_interleaved`, with `wle_two` proving the empty base that leanspec stubs as an axiom); the footprint walk (quotes at each census item; the S1 "P_{i+1} nonempty" recital is consumed NOWHERE in the S2 proof body, and the r1 append's `(b)@i` derivation is post-hoc-sound in the interleaved order) is §3.2's record. New machine coverage at the WI honesty-box's two disclosed gaps: the three-slot W-law at `f₄ = 3` (p = 5: `tr(Y) = 0`, unique `w ∈ F₅ˣ`, `e₂(Y) = w²`, `norm(Y) = 4w³`; gauge-naive twin SPLITS — 2 primes) and the `K₃ = F₉` alphabet frame (`w₂ = 1` measured, letters `(2, z₂, z₂)`) — `verification/om8_vartheta_deep.py` GREEN 52/0. **Still carried, disposition UNCHANGED: CARRY** — the frozen GENTOW5/T5 statements retain their explicit `𝒲_{≤i}` hypotheses (T5 S12.1's own fence); consumption routes through the composed chain {GENTOW2 base, WI step, frozen (a)→(b) chain} + the skeleton. Residual pinned: the three suppliers at their existing grades, plus ONE fresh-context hostile pass on this unit's index-alignment reading of WI census items C-3/C-5 — to be commissioned by chapter I's discharge node when it composes the citation. Unit record: `docs/openmath-campaign/OM-8_deep-twist_2026-08-16.md`.

HYP.64  `WFRAME OPEN-1`
WHERE: `T5_WFRAME_2026-08-12.md`, L388.
STATEMENT: No structural formula/criterion for w_i, including w_i=1, is proved.
CONSUMED BY: no current capstone leg.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — keep stronger claim out.

HYP.65  `WFRAME OPEN-2`
WHERE: `T5_WFRAME_2026-08-12.md`, L390 and L1185–1193.
STATEMENT: Either identify S11.3’s fixed letter-power unit with w₁ or retain distinct normalizations; no u₁=w₁ claim.
CONSUMED BY: entire i=1 stratum, presently excluded.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — normalization interface.

HYP.66  `WFRAME OPEN-3`
WHERE: `T5_WFRAME_2026-08-12.md`, L283–286, L392.
STATEMENT: Avatar value can differ from intrinsic WF-w; open task is exact gap, not equality.
CONSUMED BY: avatar bookkeeping.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — quantify known nontrivial gap if needed; the gap is now MEASURED, not merely known (v3, delta item 11): GENTOW2 S6.1 row 23, the avatar = w identification this row is gated on, is DESCRIPTIVE-status and “is now measured to GAP at LW3” (`GENTOW5_WI_2026-08-10.md:480`). See HYP.145.

### T4 boxes and tightness suspects

HYP.67  `GENTOW6-BOX-1`
WHERE: `T4_CERTIFICATE_WITNESS_2026-08-12.md`, §S7 L526–539; upstream GENTOW6.
STATEMENT: Lower-coordinate classification at μ₂≥3, including f₁≥2 compound face, is incomplete.
CONSUMED BY: **RE-HOMED off `[H-c]` (COR-WFA-08).** Not a weld-face residue and outside the weld-face audit’s remit: the row has **zero weld-layer content** — it is GENTOW6’s own μ₂≥3 attainment-classification residue (the Y-bookkeeping k-extraction ledger). GENTOW6 L610–615 (re-verified at L610): “GENTOW6-BOX-1 (mu2 >= 3 attainment). THEOREM 6.3 is scoped to mu2 = 2 … the Y-bookkeeping of (a) needs the k-extraction ledger re-derived; not claimed.” The v3 attribution “potentially [H-c]” was a MIS-ATTRIBUTION: `[H-c]` is by definition the six weld notes’ displayed boxes plus the Σ-LAW residue (W12 L1146–1148), and GENTOW6 is not a weld note and cites none. Real home: the GENTOW6/T4 attainment layer (note GENTOW6 L1201–1204 records BOX-1 **CLOSED AT f1 = 1**, leaving the f₁≥2 face).
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — retained. The audit re-homes the consumer and does NOT settle reachability: as a *weld-face* residue it is NOT-REACHED, but it may be in-cone as a *tower-leg* residue under HYP.82/HYP.144, which is a different audit. Question-2 scheduling no longer gates it.

HYP.68  `GENTOW6-BOX-2`
WHERE: T4 §S7; upstream GENTOW6.
STATEMENT: Product-measure count is open already at FULL sides; budget half is proved and only ledger/count half remains.
CONSUMED BY: **RE-HOMED off `[H-c]` (COR-WFA-09).** Zero weld-layer content. GENTOW6 L616–619 (re-verified at L616, L618): “GENTOW6-BOX-2 (the count LEDGER at partial sides) … open already at FULL sides (GENTOW-1’s count-law remark)”. The consumer, if any, is **the tower count layer**, not `[H-c]` — it belongs beside HYP.144’s GENTOW4-BOX-2 open COUNT layer, which is the same μ≥3 count-layer obligation family as HYP.139 and HYP.142.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — retained; consumer re-homed, reachability as a tower-leg residue not settled by this audit.

HYP.69  `GENTOW6-BOX-3`
WHERE: T4 §S7; upstream GENTOW6.
STATEMENT: Entry-driven/non-top-overflow cases lack exhaustive classification.
CONSUMED BY: **RE-HOMED off “W12 value partition” (COR-WFA-10).** Zero weld-layer content; **W12 has no value partition consuming GENTOW6**, so the v3 attribution was a mis-attribution. Real home: GENTOW6’s own regime-3 (entry-driven / non-top-overflow) display. GENTOW6 L620–623 (re-verified at L620, L622): “GENTOW6-BOX-3 (regime-3 classification). Which non-x-free, no-top-overflow members diverge, and exact THETA-attainment via entry drivers: displayed only … no theorem.”
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — retained; consumer re-homed, reachability not settled by this audit.

HYP.70  `GENTOW6-BOX-4` residue
WHERE: T4 §S7 L533–535/L2105–2109; `GENTOW6_PROOF_2026-08-09.md` L1249–1255.
STATEMENT: Sealed-row ask is DISCHARGED at HEAD, GREEN 265/0 at four x-ful rows including f₁=2; only theorem-grade all-f₁≥2 widening remains unsealed.
CONSUMED BY: a widened theorem, not the discharged box.
CLASS: theorem-strength-residue
PROPOSED DISPOSITION: MATH — no OPEN-CALL; keep battery discharge distinct from widening.

HYP.71  `GENTOW3-BOX-1`
WHERE: T4 §S7; upstream GENTOW3.
STATEMENT: Neither genre-general nonvanishing nor battery witnesses for entry-driven overflow with self-power below D′ are delivered.
CONSUMED BY: **RE-HOMED off `[H-c]` (COR-WFA-11).** Zero weld-layer content — it is the attainment/non-cancellation certificate. Real home: **GENTOW-6.3 / CERT-TOP**, not `[H-c]`. GENTOW3 L449–456 (re-verified at L455): “a genre-general non-vanishing proof, and battery witnesses for entry-digit-driven overflows … are NOT delivered.” T4 §S7 L537 (re-verified): the original genre-general non-cancellation ask “is replaced, not magically solved, by the explicit witness ω_j”.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — retained; consumer re-homed. Read with HYP.112’s fence: a candidate implies neither ω_j≠0, touched j, nor threshold attainment.

HYP.72  disc≠0 downstream fence
WHERE: `T4_CERTIFICATE_WITNESS_2026-08-12.md`, L1827–1860.
STATEMENT: disc≠0 is not T4 membership; later decided-leaf σ consumers import it alongside membership.
CONSUMED BY: W12/other σ consumers; T4 consumes no σ-content.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE — thread downstream.

HYP.73  `WELD-FACE-AUDIT`
WHERE: `TIGHTNESS_CENSUS_2026-08-11.md`, S-4; record `runs/qgen/WELD_FACE_AUDIT.md` (2026-08-13).
STATEMENT: Check unresolved weld-face reachability.
CONSUMED BY: chartered HYP.74–77; the orchestrator widened the charter by default to HYP.21/22/67/68/69/71 (COR-41 / question 2).
CLASS: audit-work-item
PROPOSED DISPOSITION: **CLOSED** (COR-WFA-01) — executed at the WIDENED charter, ten rows, AUDIT-ONLY (no note edited, no grade moved). Verdicts: **1 REACHABLE-AND-CONSUMED · 0 CORROBORATIVE-ONLY · 9 NOT-REACHED**. Method: the census cone (20 note files) grepped for every weld-layer label, every hit read in context, plus each cone note’s own dependency ledger. The audit also found and named one face with no ledger row — `GENHN-BOX-2`, now HYP.148 — and refuted the charter’s premise that no weld row sat in the preview (six of the ten did). Not an open obligation; retained as the reference that closes it.

HYP.74  `JD0-BOX-2`
WHERE: census S-5; `lean/notes/openmath/JD0_PROOF_2026-08-08.md` §4 L219–225 (re-verified at L220).
STATEMENT: JD0 unit-character warrant is synthesis, not proved theorem: “That the weld’s ENTIRE conditional value dictionary acts by slot-wise unit characters is the synthesis §3.2 reading of JA-RES [GRTJA, 1/2], the (ξ,w) covariance family [GRTW2, ACCEPTED], and the ℓ-orbit rescalings ORB-RES [J-A].”
CONSUMED BY: **[WELD-FACE-AUDIT 2026-08-13, REACHABLE-AND-CONSUMED]** — **NOT via `[H-c]`.** J-D0 is consumed DIRECTLY at seven cone notes; all seven dependency-ledger sites re-verified at HEAD (W11 L599, W12 L1499, HMENU3 L717, HEX3 L720, GENIND L1518, GENH4 L938, GENHN L1515). Two declare BOX-2’s perimeter INHERITED: W11 L602–603 (re-verified) “J-D0 is corroborating at the instance, load-bearing only for the general-program framing (S4.3 inherits its BOX-2 gauge-form perimeter)”; W12 L1502–1504 (re-verified) “J-D0 is corroborating at the instances and load-bearing for the general framing (its BOX perimeter inherited)”. At all ten counted routing sites the consuming note exhibits the type-preserving bijection itself, so J-D0 enters at **FRAME grade**, not as an imported theorem.
CLASS: hypothesis-box
PROPOSED DISPOSITION: **CARRY — reachability SIGNED** (COR-WFA-02; disposition unchanged, parentage and grade corrected). This is the ONLY member of the deleted `[H-c]` block that survives into the preview, and it now appears there as its own conjunct rather than inside the package. Discharge is a fold, not a theorem: record per site that the gauge consumed there is an explicit z-power unit character verified in-note, which strikes the inheritance. The general lemma census S-5 proposed (“every value-dictionary entry the corpus consumes is a unit character”) is **NOT needed on the capstone path**.

**ARC NOTE (2026-08-16, unit OM-9).** The carrier and the fold route's SITE-INDEPENDENT half are now LANDED and PROVED in `leanfinal` (chapter F's first landings, blueprint AMENDMENT A-W.2): `JD0Box2`/`ValueDictSite` (F.04) and `JD0SiteStrike` (F.05) at the gate signatures, plus `JD0SiteStrike.jd0Box2` (`Uniformity/ChapF/F04w.lean`) — a strike with its ledger leg witnesses the perimeter, so each of the seven per-site records, once written against chapter-H/C site objects (GC-13), discharges its site by ONE lemma application. The mechanism side of the box is now theorems: count-blindness `card_image_slotScale` (F.02, was an axiom stub), the residual-leg conclusions `natDegree/monic/isRoot_resTwist` (F.03 ×3), the F₂-vacuity disclosure (F.06), and NEW: the perimeter's consistency `gaugeCobdry_isCocycle` (the ledger leg carries 2-cocycles to 2-cocycles) with the action law `gaugeCobdry_gaugeCobdry`. All Lean-core; certified first by `verification/openmath/om9_weld_cert.py` LEG A (95-GREEN battery, both primes, NONCHAR shift + zero-letter + wrong-normalization mutants caught, the involution separator documented at F₃ vs F₄). **Still carried, disposition UNCHANGED: CARRY** — the residual is exactly (a) the SYNTHESIS that the weld's actual dictionary IS of the four-line form (GRTJA 1/2 priced, honesty F-6/F-7; no in-cone route) and (b) the seven per-site strike records (REDUCES-TO chapter H/C site landings). Unit record: `docs/openmath-campaign/OM-9_weld_2026-08-16.md`.

HYP.75  `JB-NOLEG`
WHERE: census S-6; `GRTJB_PROOF_2026-08-08.md` §0M.
STATEMENT: Open no-machine-leg cells are row 4 GRID, row 5 RES, row 12 d4/u≥0, and row 22 v=0.
CONSUMED BY: **[WELD-FACE-AUDIT 2026-08-13, NOT-REACHED]** No capstone-path consumer. W11 L391–393 (re-verified): “JB row-12 u ≥ 0 proviso (GRTJB @ 83f47f4): not consumed — all polygons computed outright on the finite grid {0,1,2}”. Row 12 reaches only (i) `JD0-BOX-1`’s B(c)-tie → **W-10** (census O-11, out of cone; JD0 L217 re-verified: “the B(c)-tie to the welded grid still owes JB row 12’s u ≥ 0 proviso”) and (ii) `[W12-H](H-b)`, the route W-12 priced but did not take. W11 S4.3’s owed-input list is `W11-BOX-1`’s unproved program (HYP.146), superseded by GENIND/GENH4/GENHN. J-D0’s own L4 leg consumes JB-VTX/JB-DEV, the ACCEPTED faces — **not** the NO-LEG rows.
CLASS: named-obligation
PROPOSED DISPOSITION: **NODE** (re-dispositioned CARRY→NODE, COR-WFA-03) — audit signs NON-REACHABILITY on all four JB rows; record OUT of the cone and drop from preview Display A. Retain as a GRTJB-internal frontier row.

HYP.76  `W2-VALUE`
WHERE: census S-7; `GRTW2_PROOF_2026-08-08.md` §5.3 L890–900 (re-verified), §5.2, §3.5.
STATEMENT: W2 value formula and two side conditions hold on every claimed face; GRTW2’s own grade is “instance-confirmed, not proved” (L890, re-verified; 16 towers / 684 groups).
CONSUMED BY: **[WELD-FACE-AUDIT 2026-08-13, NOT-REACHED]** GRTW2 reaches the spine only through W11’s “template faces” list and W12 §S5’s composition display; `JD0-BOX-2` cites GRTW2’s **ACCEPTED** (ξ,w) covariance, not the open value layer. Four cone notes state the seam is off (re-verified: GENH4 L69 and L870, GENHN L120 — “the W-2/LIFTCORNER seam NOT consumed”; HEX3 L503). GRTW2 L900 (re-verified): the W-2 → W-5 seam “is NOT claimed here”. **CORRECTED on fold (the audit’s row block overstated this one):** the audit wrote “Zero occurrences of W2-OPEN-1/-2 or W2-BOX-1 in any of the 20 cone notes”, which is FALSE — `W12_PROOF_2026-08-08.md` carries two, at L1190 and L1509. Both were read: L1190 is §S5’s composition display recording the weld notes’ own displayed conditionality (“the surviving open surface being W2-OPEN-2/OPEN-2a … NARROWED to the Σ-LAW single lemma”) and L1509 is the dependency ledger’s status annotation on that same display. Neither is a consumption, so the NOT-REACHED verdict is unaffected; the accurate statement is **zero occurrences in nineteen of the twenty cone notes, two in W12, both non-consuming display bookkeeping.** (The audit’s own §1 states the W12 carve-out correctly; only the §2 row block generalized past it.)
CLASS: hypothesis-box
PROPOSED DISPOSITION: **NODE** (re-dispositioned CARRY→NODE, COR-WFA-04) — record OUT of the cone; drop from preview Display A.

HYP.77  `DMULT-S`
WHERE: census S-8; `GRTJC_PROOF_2026-08-08.md` JC-BOX-3 [r2,G-1] L1985–1990 (re-verified at L1987–1989), L1220.
STATEMENT: Exact ω=1 multiplicity tier satisfies claimed formula beyond measured cases.
CONSUMED BY: **[WELD-FACE-AUDIT 2026-08-13, NOT-REACHED]** The one reachable GRTJC face, COROLLARY W-9, rides the **citable** (DMULT-w) tier, not this one. GRTJC L1987–1989 (re-verified): “if only (DMULT-s) failed (ω ≢ 1), JC-COB’s sharp values and R1-COB’s exact predicate fail while the structural clauses stand”; JC-F1 [r1] at L1823 (re-verified): “**THROUGH, general m**, on (DMULT-w) + JC-IND”. W11 L383–384 (re-verified): “DULEMMA / (DMULT-s) … NOT consumed anywhere above”. `JC-COB`’s sharp form and `R1-COB`’s exact predicate — the only (DMULT-s) consumers — have no cone consumer. The reachable (DMULT-w) cite is PDF-VERIFIED (census I-4 fold, 2026-08-12).
CLASS: named-obligation
PROPOSED DISPOSITION: **NODE** (re-dispositioned CARRY→NODE, COR-WFA-05) — record OUT of the cone; drop from preview Display A. The `[H-a]` half of its old double parentage is likewise not a count-law consumer (GRTJC’s structural clauses stand without it).

HYP.78  `S8.1-MEMBER`
WHERE: census S-1.
STATEMENT: Above-floor divergence cases have complete membership classification.
CONSUMED BY: drainage/value decomposition.
CLASS: named-obligation
PROPOSED DISPOSITION: MATH — pending RCT hard unit; no OPEN-CALL/HYP.73 dependency.

HYP.79  `P-BINOM`
WHERE: census S-2.
STATEMENT: If p divides binom(m,2), floor attainment and lower-coordinate cases are classified.
CONSUMED BY: compound value branch.
CLASS: named-obligation
PROPOSED DISPOSITION: MATH — rider on HYP.78; no OPEN-CALL.

HYP.80  `COMPOUND-6.5′`
WHERE: census S-3.
STATEMENT: f₁≥2, μ₂≥3 compound case has required classification and measure law.
CONSUMED BY: compound genre under [H-c].
CLASS: named-obligation
PROPOSED DISPOSITION: MATH — proof+machine unit; no OPEN-CALL/HYP.73 dependency.

### Completeness additions from the adjudication

HYP.81  `[GENHN-HE(μ ≥ 3)]`
WHERE: W12 L437; GENIND L3081–3084.
STATEMENT: Stage leaves of multiplicity μ≥3 have required σ-decision; first live n=6.
CONSUMED BY: W12/GENIND from n=6.
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY — independent leaf obligation. SCOPE SPLIT ADDED (v3, delta item 9): HE3 proves THEOREM HE3.A and [GENHN-HE(μ)] UNCONDITIONAL for μ≤3 — exactly the first-live n=6,7 case — while at μ≥4 (n≥8) COROLLARY HE3.B rides the open HE3-BOX-6 ramified branch (ii). The conjunct is unchanged; its supplier is conditional above μ=3. See HYP.143.

**ARC NOTE (2026-08-16, unit OM-7).** The μ=3 slice's missing transcription owner (CHAP-I honesty I-11(i) / orchestrator item O-1: corpus-unconditional per HE3.A, "NO owner in any committed chapter") is now BOOKED: `leanfinal/Uniformity/ChapH/H73w.lean` (H.73-adjacent appendix per the H09w/H89w precedent; blueprint AMENDMENT A-H.4) lands the transport `(e,f) ↦ (e₁e, f₁f)` with its degree law, the five-type μ=3 dictionary with degree conservation, five-type EXHAUSTIVENESS (multiset-induction proof), the μ=2 consistency theorem (H.73's `stageSigma` = the transport's μ=2 shadow — `EFF.HE3.03`'s no-circularity as a theorem), and HE3.B's unconditionality arithmetic (stage-CS ⟹ μ≥4; strict descent μ′ ≤ μ/2; branch (ii) ⟹ μ≥4; n = D′μ ≥ 6 sharp, μ≥4 ⟹ n≥8) — sorry-free, Lean-core. The σ-DECISION analytics stay corpus-side at H.73's own trust standard, with NEW decorrelated teeth: `verification/openmath/om7_cert.py` (97 rows GREEN, 6/6 planted mutants caught) closes the four recorded coverage gaps — first embedded n=7 rows ever (EFF.HE3 source defect 9), first equal-characteristic μ=3 rows (HE3-BOX-4b's ℤ_p-only disclosure; F_2[[t]] and F_3[[t]], construction-certified), first f₁≥2 frame at D′=4 (degree-12, PARI), first h=3 frame (both at p∈{3,5}). **Still carried, disposition UNCHANGED: CARRY** — the μ≥4 slice rides HYP.143 exactly as before (OM-10's family); E's BLOCKED-HYP.81 stubs (GC-5/E-3) unchanged, except that a μ=3 consumer may now cite the owner through I.06. The D′=1 leg (HE3-4D1) is outside `GenreDatum`'s grammar and remains order-1-layer property. Unit record: `docs/openmath-campaign/OM-7_genhn-he-tow_2026-08-16.md`.

HYP.82  `[GENHN-TOW-1]`
WHERE: GENIND L3081–3084.
STATEMENT: n≥8 tower leg satisfies additional GENHN supplier law.
CONSUMED BY: GENIND at n≥8, in addition to HYP.81 and [GENIND-H].
CLASS: hypothesis-box
PROPOSED DISPOSITION: CARRY.

**ARC NOTE (2026-08-16, unit OM-7).** C.93's clause (i) — the threshold arithmetic the census rests on (`n = D_r·μ_r ≥ 2^{r+1}`, depth 2 first-live at 8 / 3 at 16 / 4 at 32) — is now PROVED in Lean at the A-C.1-signed signature VERBATIM: `leanfinal/Uniformity/ChapC/C93.lean` (`tower_first_live` + the sharpness law `tower_first_live_sharp`; Lean-core footprint; root wiring left to the ChapC fleet's roll-up regeneration, flagged for the orchestrator). Numeric leg: `om7_cert.py` LEG F — 27,300 exhaustive tuples 0 bad, sharpness at the all-2 tower, tooth T-TOW (the strengthened bound 2^{r+2} fails), and the GENTOW5 S4 witness chain u = 5, 21, 85, 341 = (4^{k+2}−1)/3 recomputed with n = 32 exactly minimal. The census DISPOSITION re-verified item-by-item at HEAD against C-H4's table (items (1)–(5)+(6)(β) = C §6/§8 theorems; (6)(α) depth 3 = GENTOW5-A's acceptance scope, first live n = 16; depth ≥ 4 claimed by NO node). **Still carried, disposition UNCHANGED: CARRY** — the open remainder is exactly the n≥8 box family (HYP.67–71/78–80/142/143/144-BOX-2, OM-10's charge), which this unit verified leaks nothing below n = 8; no conjunct added, none discharged. Unit record: `docs/openmath-campaign/OM-7_genhn-he-tow_2026-08-16.md`.

HYP.83  `(VD-m)`
WHERE: W12 L219–221; GRTJB value ledger.
STATEMENT: Value-decomposition law holds for m≥2; unconditional only m≤1, while VD-2 is false on 10/13 roster boundaries.
CONSUMED BY: JB-CREAD and [H-c] — **both verified UNREACHABLE at v5 (see the ORPHAN-1 verification block below). No capstone-path consumer.**
CLASS: named-obligation
PROPOSED DISPOSITION: **NODE** (re-dispositioned CARRY→NODE, **COR-ORPH-01**) — record OUT of the cone; retain as a GRTJB/weld-internal frontier row. ORPHAN-1 is CURED, and cured by fresh verification rather than by inheritance.

> **ORPHAN-1 VERIFICATION [v5] — applies to HYP.83, HYP.84, HYP.85, HYP.86.**
> v4 left these four CARRY because no COR-WFA line authorized moving them; the charge for
> v5 was to verify their consumption sites independently rather than inherit the parent’s
> verdict. Done, by the weld audit’s own per-row method, re-run from scratch at HEAD.
>
> **(1) Direct reach into the cone: one occurrence, and it is a disclaimer.** Fixed-string
> grep for `VD-m`, `C-coll`, `R-coll`, `PERIM` across the audit’s twenty cone notes returns
> **exactly one** hit for the four labels — `W12_PROOF_2026-08-08.md:219`, verbatim: *“with NO
> value-layer hypothesis ((VD-m), (C-coll), (R-coll), (DMULT-s), PERIM-μ **all absent**, J-D0
> frame)”*. That is a non-consumption: it is W-12.A’s census display recording their absence.
> (The one further `PERIM` hit, `GENHN_PROOF:1353`, is the unrelated string
> “CERTIFIED-PERIMETER FINDING”.) Nineteen of twenty cone notes contain none of the four.
>
> **(2) Reach through the two surviving weld faces — the question v4 could not have asked,
> because one of those faces was only named in v4.** After the audit the spine consumes exactly
> two weld faces: **J-D0** (HYP.74) and **W-9 inside GENHN-4 layer 1** (HYP.148). Both were
> checked directly:
> * **J-D0 does not carry them — it is the theorem that deletes them.**
>   `JD0_PROOF_2026-08-08.md:277–278`, verbatim: *“**Fence bookkeeping** — count-layer consumers
>   **need not carry** PERIM-μ / (C-coll)/(R-coll)/(VD-m); this deletes the fence-patching genre
>   from the J-D block entirely.”* Re-affirmed post-certification at L653–656: *“**Fence
>   bookkeeping survives.** PERIM-μ, (C-coll), (R-coll), and (VD-m) remain unnecessary for
>   count-layer consumers whenever the consumer uses the L3 × L4 coefficient and the documented
>   gauge dictionary.”* (That trailing clause is the one live proviso, and it is a property of
>   the consumer, not of these four rows.)
> * **W-9 does not carry them either.** `GRTJC_PROOF_2026-08-08.md:1777` states the corollary’s
>   hypotheses in full — *“**COROLLARY W-9.** **Given W-6, W-7, W-8:** …”* — with no value-layer
>   fence. GRTJC does inherit `(VD-m)`/`(R-coll)` from JB-BOX-2, but it **localizes** that
>   inheritance: JC-BOX-6, L2045–2047, *“**§3.3’s germ display** additionally rides JB-BOX-2’s
>   geography ((VD-m) free only at m ≤ 1; JA-VDIND at m ≥ 2; JA-BOX-2’s (R-coll) at m ≥ 3 …)”* —
>   i.e. it attaches to the germ display inside **W-7’s OB-3 VALUE** sub-clause, at L1525. What
>   GENHN consumes is the *structural* clause, not the value one — `GENHN_PROOF:92–94`,
>   verbatim: *“COROLLARY W-9’s dim_K 𝒜(T) = E (the stage slot geometry: E graded K-lines per
>   integer height, the twisted algebra K^c[ℤ/E]) and JC-LOAD’s graded no-cancellation”*, and
>   L908–910: *“At general μ, layer 1 CONSUMES the W-9 graded frame (accepted 2/2) rather than
>   re-deriving the carry digit-by-digit”*. GRTJC’s own failure analysis separates the tiers
>   exactly this way (JC-BOX-3, L1987–1989, already re-verified in v4): if the value tier fails,
>   *“**the structural clauses stand**.”* Confirming the severance mechanically: **`W-7`,
>   `JB-CREAD`, and `JB-BOX-2` each occur ZERO times in all twenty cone notes** — the germ
>   display is named nowhere on the path.
>
> **(3) Nothing else reaches them.** Zero occurrences of any of the four labels in `T1`–`T5`
> (the whole T-unit chain), in `docs/HUMAN_PROOF.md`, and in **both Lean trees** (`leanfinal/`,
> `leancheck/`). The tightness census names them once, at S-7, under `W2-VALUE` — which is
> HYP.76, itself signed NOT-REACHED. Corpus-wide the remaining hits are the weld notes
> themselves, their pass reports and certification briefs, three `docs/in-progress/` design
> notes, `W10_PROOF` (out of cone, census O-11), and this ledger.
>
> **Verdict: NOT-REACHED, signed independently — not inherited.** All four move CARRY→NODE,
> the same disposition the audit gave the other nine NOT-REACHED rows (HYP.21/22/75/76/77).
> **What this does NOT mean:** none of the four is proved, none is refuted (`(VD-m)` is in fact
> *false* on 10/13 roster boundaries at m ≥ 2, per HYP.83’s own statement), and each remains a
> live obligation *inside the weld layer* for any future consumer that re-enters it. They leave
> the capstone’s conditionality; they do not leave the corpus. The preview already omits them
> (v4), so **this cure moves no conjunct** — it only makes the row dispositions consistent with
> the display that was already correct.

HYP.84  `(C-coll)`
WHERE: W12 L219–221; GRTJB value ledger.
STATEMENT: Claimed collection law holds at order≥2 value layer.
CONSUMED BY: [H-c] — **verified UNREACHABLE at v5; no capstone-path consumer.** `(C-coll)` is the **W-2** side of the value layer (`WELD_SYNTHESIS_2026-08-05.md:229`: *“W-2 ((C-coll)), J-A ((R-coll)) and J-B ((VD-m))”*), and W-2/`W2-VALUE` is itself NOT-REACHED (HYP.76) — so this row has no live parent on either the `[H-c]` or the W-2 side. Census S-7 lists it under `W2-BOX-1/(C-coll)`, i.e. under HYP.76.
CLASS: named-obligation
PROPOSED DISPOSITION: **NODE** (re-dispositioned CARRY→NODE, **COR-ORPH-02**) — record OUT of the cone; retain as a GRTW2/weld-internal frontier row. See the ORPHAN-1 VERIFICATION block at HYP.83, which covers this row.

HYP.85  `(R-coll)`
WHERE: W12 L219–221; GRTJB value ledger.
STATEMENT: Claimed residual collection law holds at order≥2 value layer.
CONSUMED BY: [H-c] — **verified UNREACHABLE at v5; no capstone-path consumer.** `(R-coll)` is the **J-A** side (`WELD_SYNTHESIS:229`) and enters GRTJC only as `JA-BOX-2`’s fence *“at m ≥ 3”* inside §3.3’s germ display (`GRTJC_PROOF:2046–2047`) — a display no cone note names (`W-7`, `JB-CREAD`, `JB-BOX-2`: zero hits across all twenty). J-D0 explicitly relieves count-layer consumers of it (`JD0_PROOF:277–278`).
CLASS: named-obligation
PROPOSED DISPOSITION: **NODE** (re-dispositioned CARRY→NODE, **COR-ORPH-03**) — record OUT of the cone; retain as a GRTJA/weld-internal frontier row. See the ORPHAN-1 VERIFICATION block at HYP.83, which covers this row.

HYP.86  `PERIM-μ`
WHERE: W12 L219–221; weld value ledgers.
STATEMENT: Multiplicity perimeter law holds on all claimed order≥2 faces.
CONSUMED BY: [H-c] — **verified UNREACHABLE at v5; no capstone-path consumer.** `PERIM-μ` is WELDMASTER §S3’s one-perimeter character-triviality condition (`JD0_PROOF:66–67`), and WELDMASTER is *“named in S7.1’s (CS-1..3) pricing only”* (GENIND L1523–1524) — pricing, not consumption. Independently re-confirmed here: the string `PERIM-μ` occurs in **zero** of the twenty cone notes. J-D0 names it first in the list of fences count-layer consumers need not carry (`JD0_PROOF:277–278`, L653).
CLASS: named-obligation
PROPOSED DISPOSITION: **NODE** (re-dispositioned CARRY→NODE, **COR-ORPH-04**) — record OUT of the cone; retain as a WELDMASTER-internal frontier row. See the ORPHAN-1 VERIFICATION block at HYP.83, which covers this row.

HYP.87  `GENIND-BOX-3`
WHERE: GENIND §S8 L1361–1366.
STATEMENT: All-prime-power and d≥2 scope rests on proof q-uniformity; battery covers d=1 at prime q only.
CONSUMED BY: all-prime-power GENIND.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — generality/corroboration audit.

HYP.88  `GENIND-BOX-4`
WHERE: GENIND §S8 L1367–1372.
STATEMENT: Simple-slice β-bookkeeping compression for n≥4 drainage is proved on every route.
CONSUMED BY: GENIND drainage; distinct from HYP.30.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — separate bookkeeping proof.

HYP.89  `GENIND-BOX-5`
WHERE: GENIND §S8 L1373–1420.
STATEMENT: Clean count for the conditional general-degree structure has not started.
CONSUMED BY: GENIND acceptance grade.
CLASS: grade-cap
PROPOSED DISPOSITION: NODE.

HYP.90  `GENIND-BOX-6`
WHERE: GENIND §S8 L1421–1425.
STATEMENT: Machine oracle is mixed-characteristic only; equal-characteristic conventions/coverage remain unaudited.
CONSUMED BY: all-characteristic GENIND.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE.

HYP.91  `GENIND-5` / `OB-a…OB-d`
WHERE: GENIND obstruction section.
STATEMENT: Four displayed obstructions and their routing are represented in the induction DAG.
CONSUMED BY: branch completeness.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — expand/map, do not compress silently.

HYP.92  `ANNEX-LEMMA GENIND-C2Q`
WHERE: GENIND C2Q annex.
STATEMENT: Annex quantitative lemma has exactly HYP.36’s hypotheses/rate.
CONSUMED BY: CS-1Q/A2.
CLASS: named-obligation
PROPOSED DISPOSITION: MERGED — supplier node under HYP.36.

HYP.93  `GENIND-6`
WHERE: GENIND §S4.3 L814–825.
STATEMENT: Clause (d)’s stage-side content is [GENIND-H]’s and not discharged here.
CONSUMED BY: stage-side induction.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MERGED — represented by HYP.31 and children.

HYP.94  `UniformityStatement` signature
WHERE: `GENUINE_DENSITY_2026-08-13.md`, §2.5.
STATEMENT: Freeze universe of O, q-evaluation/coercion, and per-O denominator nonvanishing; old σ.degree point is superseded by `typeOf_degree`.
CONSUMED BY: phase 0d.
CLASS: owner-definition-decision
PROPOSED DISPOSITION: **CLOSED-SIGNED — question 3 ANSWERED [v5, append #47]** (*“Q3 capstone signature’s three points SIGNED”*). The three signed points survive the P4 rewire **verbatim** (append #48: *“Asvin’s three signed points preserved verbatim”*) and are re-verified in the tree at HEAD, `leanfinal/Uniformity/Density/Statement.lean:55–58`: *“(i) The `∀ O` is over `Type` (universe 0)… (ii) The rational function is evaluated at `(q : ℚ)` and the equality is read in `ℝ` via the coercion. (iii) `den.eval q ≠ 0` is demanded per-`O`, not globally.”* The fourth point is likewise settled in the same docstring, in the opposite direction from the v1 reading: *“(iv) The hypothesis `σ.degree = n` **does real work** (`typeOf_degree`): off-degree `σ` are forced to density `0`”* — so it is not superseded-as-idle but superseded-as-*discharged*. Both `UniformityStatement` (`:71`) and `UniformityStatementDecided` (`:84`) carry the signed signature.

HYP.95  Haar bridge
WHERE: `GENUINE_DENSITY_2026-08-13.md` §3B.4; `N2_EXACT_2026-08-13.md` §7.
STATEMENT: Limit of decided proportions equals Haar measure of the type locus.
CONSUMED BY: informal W-12.D Haar conclusion — **and, as of v5, by nothing on the capstone path.**
CLASS: optional-theorem-leg
PROPOSED DISPOSITION: **CLOSED — question 5 ANSWERED, NO HAAR [v5, append #47/#48].** The owner redefined the density rather than bridging to Haar: `genuineDensity` **IS** the limit of the proportion of σ-consistent classes, full stop — so the capstone asserts a proportion limit and never asserts a Haar measure, and this bridge is no longer a leg of anything frozen. The Lean tree says the same in its own words at HEAD, `leanfinal/Uniformity/Density/GenuineDensity.lean:263–265`: *“**What this is NOT.** It is not asserted here to be the Haar measure of the type-σ locus: that bridge needs measurability of the locus and is not formalized (see the unit note §3B.4). `genuineDensity` is, formally, the limit of the consistent-class proportions, full stop.”* **Honesty fence on this closure:** the row is closed as *off-path*, not as *proved* — the Haar identification remains an unproved (and unformalized) mathematical statement, and it stays true that the informal W-12.D text draws a Haar conclusion this ledger does not underwrite. Anyone re-introducing a Haar claim re-opens this row and owes the measurability leg. Also folded here: **MISS-05 / DEF-07’s Haar question is CLOSED by the same answer.**

HYP.96  `AX-CELLREC` / `AX-LEAF`
WHERE: census L-3.
STATEMENT: Draft faithfulness entries gate the older Lean capstone path.
CONSUMED BY: theorem-strength older realization **— the quarry’s measure route only; `leanfinal` never imports them.**
CLASS: owner-axiom-decision
PROPOSED DISPOSITION: **OUT-OF-PATH-BY-POLICY — question 7 ANSWERED [v5, append #49].** *“leanfinal stays LEAN-CORE-ONLY; the AX-CELLREC/AX-LEAF axioms stay QUARANTINED in the quarry’s measure route (no file move needed — leanfinal never imports them; policy now explicit).”* So these axioms condition the **quarry**, not the capstone, and the census’s worry that they *“gate the LEAN capstone claim”* is answered: they do not gate `leanfinal`. **What the closure does NOT say:** the faithfulness entries in `docs/AXIOM_FAITHFULNESS.md` are still DRAFT, and they still gate any *quarry* measure-route claim — the policy moved the row off the capstone path, it did not complete the entries. Enforcement instrument already standing: `lake env lean LeanUrat/AxChk_baseline.lean`, the footprint census.

HYP.97  `RealInstanceAt.faithful`
WHERE: census L-4; `Stage2/UniformityTarget.lean`.
STATEMENT: True-placeholder consumption at theorem strength is illegitimate before gates.
CONSUMED BY: older Stage2 realization, not automatically new Lean-core projects.
CLASS: owner-axiom-decision
PROPOSED DISPOSITION: **OUT-OF-PATH-BY-POLICY — question 7 ANSWERED [v5, append #49]**, same clause as HYP.96 (question 7 explicitly covers *“census L-4, the `RealInstanceAt.faithful` placeholder”*). `leanfinal` is Lean-core-only and does not realize through `Stage2/UniformityTarget.lean`; the placeholder conditions the quarry. Consistent with the two disclosed `sorry`s in that same superseded file, already recorded under `OFF-PATH`. **Fence:** the placeholder is still illegitimate to consume at theorem strength *inside the quarry* — this row is off the capstone path, not repaired.

HYP.98  `DEFINITION-AUDIT`
WHERE: census L-5; GENUINE_DENSITY definition audit.
STATEMENT: Frozen event, density, type, evaluation, and convention definitions match the mathematical capstone.
CONSUMED BY: phase 0d.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE **[CORE-SET]** — includes HYP.12/94/111 interfaces. **RETARGETED at v5 by the Q4 policy:** this row *is* the core-set definitional audit, so it is the one place the human-review surface lives. Its scope is now exactly the core set — the types, the uniformity theorem, `genuineDensity`/`decidedDensity`, the cites, and (per append #48) the changed definitions’ faithfulness paragraphs — and it no longer carries the whole ledger’s definitional debt. HYP.94 closed under it (signature signed); HYP.12 rides inside it; HYP.111’s definitional half rides inside it while its deep-tail reconciliation half lifts out. **Standing directive folded in (append #49, directive 2):** *“keep one warning sign out on the main definitions/axiom-cites and PERIODICALLY PULL FRESH EYES onto the core set as the Lean build proceeds”* — a recurring fresh-context definitional audit at chapter milestones, not a one-shot review.

HYP.99  T3/T5 frame staleness
WHERE: T5 rider m-2; T3 frame; T1 r12–r13.
STATEMENT: T5 pins T1 through r10 and T3 pins no revision, while r12 adds two-clause w_i∈K_i× gate and T3 consumes higher-depth data without both fences.
CONSUMED BY: T3/T5 higher-depth soundness.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — cross-note HEAD audit.

HYP.100  contradictory T5 sentence
WHERE: T5 stale L299 versus governing L616.
STATEMENT: Stale text says WI discharges the conjuncts; governing text says it does not.
CONSUMED BY: extraction of HYP.63 status.
CLASS: corpus-consistency-item
PROPOSED DISPOSITION: NODE — strike/append stale sentence.

HYP.101  HE7.A source suite
WHERE: T2 §S4.1 L1167.
STATEMENT: Every instance supplies ACCOUNT, RES-DEG, nonemptiness, exhaustion, and root-preserving continuation.
CONSUMED BY: HE7.A instantiation; naming a carrier is insufficient.
CLASS: source-obligation-suite
PROPOSED DISPOSITION: CARRY — SEC-RANK/RISE do not replace the suite.

HYP.102  `(MID-PEEL)` items 2–5
WHERE: T2 L2415/S1.8.
STATEMENT: Items 2–5 are standing clause hypotheses discharged per instance; only item 1 is master-proved.
CONSUMED BY: mid-peel instances.
CLASS: source-obligation-suite
PROPOSED DISPOSITION: NODE — record each discharge.

HYP.103  T2 S4.2 non-claims
WHERE: T2 §S4.2 L1171–1184.
STATEMENT: Twelve exclusions, including partial-side budget and density laws, bound T2.
CONSUMED BY: downstream density use.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE — preserve list.

HYP.104  `C3-lift-coefficient-space`
WHERE: T1 L3228–3311; §5 item 18.
STATEMENT: Every C3-key coefficient is bounded, especially deg k̂_t<deg Φ_i; height/residue do not imply it.
CONSUMED BY: corrected key formation/monicity.
CLASS: named-obligation
PROPOSED DISPOSITION: NODE — independent site obligation.

HYP.105  factor patterns need tower correctness
WHERE: T1 §5 item 9.
STATEMENT: Gauge-invariant residual factor patterns become splitting types only via surrounding tower correctness.
CONSUMED BY: T1-to-capstone transfer.
CLASS: interface-obligation
PROPOSED DISPOSITION: NODE — but ROUTED TO 0d (v3, delta item 7): both Phase-0a shards escalate this row to an owner decision. `spec/EFF-T3.md:1610` heads it “**OPEN-CALL 1 — FOR-0d — NEEDS ASVIN**” and states “Neither T3 nor the identical T1 fence names that theorem… Phase 0d must decide the trust-boundary theorem connecting residual factor patterns to splitting types”; `spec/EFF-T1-s1of3.md` OPEN-CALL 4 records the same missing designation. It is not a new owner question — it is the naming half of the trust boundary already inside question 4’s definitions package. See HYP.141. **v5 update:** question 4 is ANSWERED by the review-boundary policy, and this row lands on the **core** side of it — the theorem connecting residual factor patterns to splitting types is the trust boundary of the *type* definition, so it rides inside HYP.98’s core-set audit next to HYP.01. The row keeps its NODE disposition; what changes is that it is no longer waiting on an owner decision, and the two shard OPEN-CALLs that escalated it (`EFF-T3` OPEN-CALL 1, `EFF-T1` OPEN-CALL 4) are answered by placement: name the theorem inside the core-set audit, do not open a tenth question.

HYP.106  nonzero-digit lift contract
WHERE: T1 §5 items 15–16.
STATEMENT: Exact height is for nonzero digits; zero lifts to zero with zero residue and no finite-height term.
CONSUMED BY: key height/zero branch.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE.

HYP.107  A2 binary carry
WHERE: T1 §5 item 17.
STATEMENT: A2 HETOW pin is restricted to stated binary-carry regime.
CONSUMED BY: A2 absorption.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE.

HYP.108  A6 provenance
WHERE: T1 §5 item 20/r9.
STATEMENT: Scalar read is HE6 F-1; lift is GENTOW6 S6.1; GENTOW6 alone has no scalar display.
CONSUMED BY: A6 absorption.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE.

HYP.109  T-unit grade caveats
WHERE: T1/T4 acceptance and T1 PE reports.
STATEMENT: T1’s 2/2 is minors-only with unreviewed riders/note-internal pin audit and newly scored teeth; T4 adds no fresh machine computation.
CONSUMED BY: T-unit evidence claims.
CLASS: grade-cap
PROPOSED DISPOSITION: NODE.

HYP.110  `W12-BOX-5`
WHERE: W12 boxes.
STATEMENT: Lean omCount is order-0 and W-2/LIFTCORNER lift-convention seam is unconsumed.
CONSUMED BY: Phase-B evaluator and convention audit.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE.

HYP.111  `W12-BOX-7`
WHERE: W12 boxes.
STATEMENT: “Decided” means certified from window digits for all disc≠0 lifts; conventions can differ on deep-tail TRP.
CONSUMED BY: leaf events/0d definitions — **[RENAMED per P4]** the Lean carrier of “decided” is now `decidedDensity` (old `genuineDensity`).
CLASS: owner-definition-decision
PROPOSED DISPOSITION: NODE — **question 4 ANSWERED [v5, append #47], and this row SPLITS under the answer.** (a) The **definitional half** — what the predicate “decided” means, since it is what `decidedDensity` counts — is CORE and rides inside HYP.98’s core-set audit. (b) The **deep-tail TRP reconciliation half** — that two conventions can disagree on deep-tail members — is a consumer-side convention question on an intermediate node, so its FAITHFULNESS burden is **LIFTED** by the review-boundary policy: it stays ordinary NODE proof-packaging and is no longer owner-visible. Note the P4 rewire *narrows* the exposure: the frozen capstone’s headline density is now `genuineDensity`, the **outer** proportion limit, which does not depend on where the decided/undecided line is drawn at all; the deep-tail convention can only move `decidedDensity`, and the two are tied under drainage.

HYP.112  T4 μ₂≥3 candidate fence
WHERE: T4 acceptance/candidate.
STATEMENT: Candidate implies neither ω_j≠0, touched j, nor threshold attainment; consumption banned.
CONSUMED BY: attempted widening.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE.

HYP.113  T4.2(c) exposure premise
WHERE: T4.2(c).
STATEMENT: f₁≥2 clause applies only under displayed full-exposure premise.
CONSUMED BY: T4.2(c).
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: NODE.

HYP.114  T4.2(d) provenance exclusion
WHERE: T4.2(d).
STATEMENT: All-provenance case is excluded.
CONSUMED BY: T4.2(d).
CLASS: scope-fence
PROPOSED DISPOSITION: NODE.

HYP.115  T4 fail-closed pins
WHERE: T4 pin/critical record.
STATEMENT: Missing or mismatched pins fail closed.
CONSUMED BY: all T4 imported premises.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE.

HYP.116  `GENTOW3-BOX-2`
WHERE: upstream GENTOW3; T4 residue-home omission.
STATEMENT: Five committed families cover only f₁=1 and η=1.
CONSUMED BY: GENTOW3 evidence claims.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE.

HYP.117  `(G5-COND)` ride list
WHERE: T3 G5 conditionality.
STATEMENT: At n≥3, key membership, primality, admissibility, non-equivalence, exact values, P_(n+1)-membership, clause (c), and clause (e) ride HYP.63.
CONSUMED BY: all eight T3 objects.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: MERGED — consumer map for HYP.63.

HYP.118  T3 narrowed delivery
WHERE: T3 scope record.
STATEMENT: Two absorptions plus one non-instance are delivered; GENTOW-6.4 remains additive, triangular, unabsorbed.
CONSUMED BY: absorption claims.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE.

HYP.119  HENSEL branch-(ii) residue
WHERE: `HENSEL_FACT_2026-08-13.md`, §7.
STATEMENT: Residual trigger, finite-level class determinacy with loss c, and counting step are named; trigger/count appear superseded by N3B, determinacy is unadjudicated.
CONSUMED BY: branch-(ii) uses outside N3B.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — reconcile without assuming determinacy superseded.

HYP.120  eight-audit coverage debt
WHERE: `Q1_brief.txt` through `Q8_brief.txt`; cite-scope resolution.
STATEMENT: v1 read Q4 only; cite-scope closes H6, not separate INTERFACE rows.
CONSUMED BY: all-O DAG completeness.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — umbrella for HYP.121–134.

HYP.121  `GENIND-1` all-O
WHERE: Q1 W12-4.
STATEMENT: GENIND-1, essential to W12-HT Step 3 and termination/compatibility, is valid over arbitrary complete DVRs.
CONSUMED BY: history transfer.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.122  `[RMG]` all-O
WHERE: audit INTERFACE rows.
STATEMENT: RM-m, L-CELL, L-LINE, L-EXACT, L-CANON hold over arbitrary complete/henselian DVRs.
CONSUMED BY: reduction machine.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.123  `[ILN]†` all-O
WHERE: audit INTERFACE rows.
STATEMENT: Standard lifts/realization satisfy laws over F_q[[t]] as well as mixed characteristic.
CONSUMED BY: GRTJB/GRTJC.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.124  `GRB` all-O
WHERE: audit INTERFACE rows.
STATEMENT: Ladder and last-read carry algebra do not rely on finite v(p), odd p, or characteristic zero.
CONSUMED BY: GRB branches.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.125  `ITER-LAW` all-O
WHERE: audit INTERFACE rows.
STATEMENT: Iteration law holds over every complete DVR in scope.
CONSUMED BY: tower/history iteration.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.126  `W-1/W-2/J-A/J-B` all-O
WHERE: audit INTERFACE rows.
STATEMENT: Weld/J suppliers are characteristic-general at every use.
CONSUMED BY: [H-a]–[H-c].
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY — explicit generality edge even where aggregate covers substance.

HYP.127  `DU lemma` all-O
WHERE: audit INTERFACE rows.
STATEMENT: DU lemma holds over all complete DVRs in scope.
CONSUMED BY: tower/value consumers.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.128  `W-10` all-O
WHERE: audit INTERFACE rows; census O-11.
STATEMENT: Consumed W-10 instances are characteristic-general; this does not revive stronger W10-GEN.
CONSUMED BY: W-10 instance consumers.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.129  `J-D0` all-O
WHERE: audit INTERFACE rows.
STATEMENT: J-D0 mathematics is characteristic-general.
CONSUMED BY: [H-c] JD0 branch — **LOCATOR CORRECTED (v4, COR-WFA-02 knock-on):** re-sourced to J-D0’s seven direct cone sites (HYP.74). The all-O generality edge is live exactly where J-D0 is consumed, which is the spine, not `[H-c]`; the `AllOInterfaces[… J-D0 …]` conjunct is unchanged and correct.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY — distinct from grade HYP.39.

HYP.130  `L2core` all-O
WHERE: audit INTERFACE rows.
STATEMENT: L2core holds over arbitrary complete DVRs.
CONSUMED BY: low-level core.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.131  HUMAN_PROOF all-O
WHERE: audit INTERFACE rows.
STATEMENT: L1_proof, M6_lemma, BB3_infinity, L5fix_complete are all-O.
CONSUMED BY: named consumers.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.132  local-integrals all-O
WHERE: audit INTERFACE rows/paper lemma.
STATEMENT: Lemma stated only unramified p-adic extends to capstone scope if used.
CONSUMED BY: retained measure route.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY — removable only by explicit route exclusion.

HYP.133  `(CONV)=α⁻¹` bridge
WHERE: audit INTERFACE rows.
STATEMENT: Monic/projective convention bridge is correct and characteristic-general.
CONSUMED BY: projective-to-monic transfer.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.134  GENHN count all-O
WHERE: Q5 out-of-slice INTERFACE.
STATEMENT: GENHN count supplier is correct in mixed and equal characteristic.
CONSUMED BY: GENHN counts/general capstone.
CLASS: interface-generality
PROPOSED DISPOSITION: CARRY.

HYP.135  `F4-JOINT` graded model
WHERE: T1 §4.1 battery.
STATEMENT: A finite graded-carrier frame has f₁=2, η=ω≠1, w=ω≠1 and scored predictions, but is not an explicit Q_p-polynomial realization.
CONSUMED BY: T1 battery, not HYP.62’s realized demand.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — keep supply model separate.

### v3 additions from the completeness sub-sweep

Twelve rows folded from `runs/qgen/HYPLEDGER_deltas.md`. Delta items 6, 12, 13 were actions and are in `MAINTENANCE QUEUE`; delta item 16’s six sub-items are in `OFF-PATH`. Every quote below was re-verified at its cited file and line.

HYP.136  `S-0` statement-ledger tripwire
WHERE: `verification/openmath/statement_ledger.py --check`; `runs/qgen/s0_check_postcampaign.txt`; `docs/PROJECT_STATE.md` append #45a L4485.
STATEMENT: The compression campaign never weakened a statement — the instrument guarding that guarantee, flagged stale by the sub-sweep (baseline `head_commit 788bba26…`, 178 statements, 20 later commits touching `lean/notes/openmath/`), has now been run against the working tree at HEAD.
CONSUMED BY: every ledger row whose source quote is a post-compression statement — i.e. the trust of this file’s own transcriptions.
CLASS: instrument-tripwire
PROPOSED DISPOSITION: **CLOSED** — GREEN post-campaign. `runs/qgen/s0_check_postcampaign.txt`: “CHECK: 178 baseline statements; 0 changed, 0 deleted, 2 added. / GREEN: every baseline statement byte-stable (normalized)”, both additions ADDED-allowed (HETOW-4 #2, GENTOW2-B″ #2). Recorded at PROJECT_STATE #45a. Not an open obligation; retained as the reference that closes it. (v3 delta item 1.)

HYP.137  `HEX3-BOX-1` tail-σ-certification lemma
WHERE: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md` L437, L681–693; `GENIND_PROOF_2026-08-08.md` L1498; `TIGHTNESS_CENSUS_2026-08-11.md` O-10 L93.
STATEMENT: The exact law for the σ-undecided mass is not derived — “q^N ≤ U₃^σ ≤ U₃^conv = q·u(q,N) and its exact law is NOT derived” (HEX3 L437) — because the TRP tail-σ transport loses ghost digits.
CONSUMED BY: GENIND’s S8.2 W-12.B consistency clause, pinned open at HEAD: “r3 b6a1d69 (17:53: the S8.2 W-12.B consistency clause conditionalized on the open HEX3-BOX-1 tail-σ lemma)”. Failure price displayed at HEX3 L684–686: undecided(3,q,N)·q^(−2N) diverges linearly in N and “W-12.B would be FALSE at n = 3”. NOT consumed by drainage: HEX3 L692–693 — “the (hExhaust-3) discharge never needed the split; only this aside’s W-12.B corroboration is conditional on it.”
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: MATH — the tail-σ lemma is unproved and now has a named live consumer, so it is no longer index-only under HYP.29. **The delta’s framing is corrected here**: census O-10 (OUT-OF-CONE, “open (refinement)”, “Drainage consumes only the proved conservative upper bound U₃^conv”) and GENIND’s pin record are BOTH accurate and do not contradict — they name different consumers (drainage vs. the n=3 W-12.B corroboration aside). Carry-vs-node was owner question 9. **QUESTION 9 ANSWERED [v5, append #49]** — owner: *“doesn’t matter too much”*, disposed per the standing recommendation: **HEX3-BOX-1 is now NAMED PARENTHETICALLY inside the n=3 perimeter clause of the preview** (edit executed; see the sentence following the dagger note in `Capstone-conditionality preview`). This is deliberately the middle option: disclosure without promotion — it is *visible* in the preview but is **not** a conjunct of Display A’s hypothesis block, because `hExhaust3` provably never needed it (HEX3 L692–693) and its only live consumer is the W-12.B corroboration aside. The row’s disposition is unchanged: **MATH**, an unproved lemma. **PREMISE CORRECTION relayed with the answer (append #49), recorded here because it corrects a natural misreading of this row:** the n≤3 menus and drainage **DO** enter the final proof — they are the induction’s base cases, and GENIND consumes HMENU3/HEX3 as base data. What stays out of the load-bearing chain is **HEX3-BOX-1 specifically**, not the n=3 work around it. (v3 delta item 2; v5 question-9 fold.)
**v7 ARC NOTE (2026-08-15, chapter G's carve-out).** `blueprint/CHAP-G_base_cases_menus.md` §1's HONESTY BLOCK now implements this row's exact disposition in Lean-facing form, and names this row by number. Quoted verbatim, item **H-2**: "`HEX3-BOX-1` / ledger `HYP.137` is an EXPLICIT NON-NODE. The tail-σ-certification lemma ... has **no node in this chapter and must not be given one**. Its ledger disposition is disclosure-without-promotion: it is *not* a conjunct of the capstone's hypothesis block, because the `(hExhaust-3)` discharge provably never needed it ... and its only live consumer is GENIND's S8.2 W-12.B corroboration aside. Chapter G inherits that disposition unchanged ... A fleet agent who finds itself needing the tail-σ lemma has left the chapter and must return `BLOCKED: HYP.137` rather than assume it." The DAG's structural-edge table (§10) records `BP.G.76 → HYP.137`: "G.76 proves the LOWER half of HEX3-BOX-1's bracket; the tail-σ lemma stays a NON-NODE (H-2)." Re-verified: `leanfinal/Uniformity/ChapG/G76.lean`, `theorem card_le_undecidedCount_three (N : ℕ) : residueCard O ^ N ≤ undecidedCount O 3 N`, sorry-free, Lean core only — exactly the lower half of HEX3's own `q^N ≤ U₃^σ ≤ U₃^conv` bracket, general `O`, unconditional, and the file's own docstring self-polices the scope: "chapter G proves no more of the bracket than this." **This is disclosure, not discharge**: no exact tail-σ law is proved anywhere in ChapG, and the chapter now carries a live-coded tripwire (`BLOCKED: HYP.137`) against a future fleet agent silently assuming it. **Disposition unchanged: MATH.**

HYP.138  N3_CHECK §6d HEX3 reconciliation
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md` L359, L366, L372.
STATEMENT: An unresolved corpus-side reconciliation, dated after the census: “### 6d. ⚠ A reconciliation item for the corpus side (reported, not resolved)”; the two readers’ numbers are “**not measuring the same set**, so these runs neither confirm nor refute THEOREM HEX3.A”; “Reconciling the two readers’ conventions (per-centre vs whole-space…)” is left “a task for whoever next touches HEX3.”
CONSUMED BY: the same HEX3 supplier as HYP.29 — the machine corroboration of `hExhaust3`, not its proof.
CLASS: corpus-consistency-item
PROPOSED DISPOSITION: NODE — convention reconciliation between the two readers; until it lands, neither reader’s count may be cited as confirming or refuting HEX3.A. (v3 delta item 3.)

HYP.139  `W-1` transport
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md` I-4 L48 and §5 L131.
STATEMENT: After the FGMN-WELD cite was PDF-verified and DISCHARGED (2026-08-12), the residue is not citational: “Residue is NOT the cite but the transport: **W-1 (harness w, 𝑅 → FGMN objects) stays ATTEMPT**, unchanged by this unit” (I-4); §5 — “the FGMN residue that remains is the W-1 transport (ATTEMPT), which is **a proof obligation, not a citation one**.”
CONSUMED BY: I-4’s own consumer chain — W-9 (proved GIVEN W-6..W-8) → GENHN-4’s layer-1 carry bookkeeping at μ≥3 (GENHN-BOX-2) → count laws at μ≥3; hence under HYP.23 ([H-d] censuses) and HYP.81. **CONFIRMED by WELD-FACE-AUDIT 2026-08-13 (COR-WFA-13)**: the chain is exactly right, and the audit supplies the missing middle term — GENHN-BOX-2 now has its own row, **HYP.148**, under which this transport rides. GRTJC L1990–1993 (re-verified at L1990): “Transport of the harness w and 𝑅 to the FGMN objects is still W-1 (ATTEMPT) — and the corpus’s own march-level dictionary for that transport, TR-3′-GEN, is OPEN at general order.” This row is the **live residue that does NOT discharge with HYP.148 by a transcription fold** — it is class MATH where HYP.148 is class CARRY.
CLASS: named-obligation
PROPOSED DISPOSITION: MATH — an in-cone ATTEMPT-grade proof obligation the v2 sweep dropped while folding census rows I-1/I-2/I-3/I-5. (v3 delta item 4.) **v4 note (COR-WFA-13):** the audit’s synthesized GENTOW5-A0/A1 route for HYP.148 would, if it ran, **retire this row from the cone with it** — the replacement frame is gr(O_L), not an FGMN object, so the W-1 transport would no longer be consumed. That is a *reason the proposed unit is high-value*, **not** a discharge: the route is asserted by no accepted note and is indexed as HYP.149 (PROPOSED-NODE). This row stays MATH and stays in the cone until that unit runs.
**v6 ARC NOTE (2026-08-14).** Same route, same arc as HYP.148: HYP.149's composed unit is at **clean-pass 1 of 2** post-r1 (detail at HYP.149). This row is **UNCHANGED, MATH at full strength** — a route that *passes* its hostile arc would retire this row per the v4 note above, but the arc has not yet passed.

**ARC NOTE (2026-08-16, unit OM-9).** The carrier is LANDED (`W1Transport`, F.12 at the gate signature, `leanfinal/Uniformity/ChapF/F12.lean`) and everything the CARRIER VOCABULARY can carry is now PROVED (`F12w.lean`, blueprint AMENDMENT A-W.2; certified first by `om9_weld_cert.py` LEG B — exhaustive at |ι| = 3 over F₃/F₄ with the exact count ((q−1)²+1)³, and the ω-legs over all (Kˣ)^{ℤ/6} at F₃/F₄/F₅ with #{ω ≡ 1} = gcd(6, q−1) exact): **`w1Transport_iff_zero_iff`** — over a field the carrier's existential is EQUIVALENT to equality of vanishing loci — plus the orbit identification with F.01's slotScale action, refl/symm/trans, `w1Transport_of_ne_zero`, and the (DMULT-w) mechanism (`lineCobdry_cocycle`: ω = c_{λ+μ}/(c_λc_μ) is always a 2-cocycle; `lineCobdry_eq_one_iff`: ω ≡ 1 iff the system is a homomorphism — the corpus's "nothing gives ω ≡ 1" with a `decide` witness). **PRECISION GAINED, NOT A DISCHARGE — this row is UNCHANGED, MATH at full strength**: the characterization proves the Lean carrier is the transport's SIGNATURE only (exactly F.12's FAITHFULNESS disclosure, now machine-checked), so chapter I's `w1` field is formally satisfiable at any nonvanishing site while the MATH content of THIS row — TR-3′-GEN's compatible dictionary at general order, the transport of the harness (w, 𝑅) to the FGMN objects — lives strictly in the site instantiation and is NOT touched by any carrier-level proof. A future claim to discharge HYP.139 must therefore point at site-level mathematics (or at the fenced WELD-ZERO arc passing), never at the carrier's ∃. Unit record: `docs/openmath-campaign/OM-9_weld_2026-08-16.md`.

HYP.140  `GENTOW5_WI` stale grade box
WHERE: `lean/notes/openmath/GENTOW5_WI_2026-08-10.md` L2 and S7 L465; `docs/TIGHTNESS_CENSUS_2026-08-11.md` I-2 L46; `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 18.
STATEMENT: Three grades coexist in the corpus for the same unit. The note’s own S7 box at HEAD still reads “**Grade: 0/2 (composed; hostile arc owed)**” (title line L2 likewise), census I-2 reads “arc at **1/2** (PE1 CLEAN; PE2 in flight, skeleton committed)”, and the SOL certification ledger row 18 reads “WI ([GENTOW5-W(i)]) … **CERTIFIED 2026-08-12** — R10 pass 3: zero findings on all five charges, sol verdict ‘CERTIFIED 2/2’ (runs/cert/R10_wi_pass3_output.log)”.
CONSUMED BY: extraction of HYP.40’s and HYP.63’s grade status — a reader landing on the note alone reads 0/2.
CLASS: corpus-consistency-item
PROPOSED DISPOSITION: NODE — strike/append the stale S7 box and title line, exactly as HYP.100 handles the stale T5 sentence. **The delta’s conclusion is corrected here**: this is NOT a contradiction of HYP.40 or HYP.63. HYP.40’s “certified 2/2” is right at HEAD-of-record (SOL row 18, 2026-08-12, which also postdates census I-2), and the note carries an r1 append of 2026-08-12 that itself “Repairs the Codex passPE2 finding G-1” (L528) — so PE2 demonstrably ran. The delta’s other half, that the ledger “disposes [GENTOW5-W(i)] as NODE”, was already absorbed: v2 re-dispositioned HYP.63 NODE→CARRY (COR-32/33). (v3 delta item 5.)

HYP.141  Phase-0a shard source-designation refutations
WHERE: `spec/EFF-T3.md` L1599, L1610; `spec/EFF-T1-s1of3.md` §8 L1644–1670 (OPEN-CALLs 1–5).
STATEMENT: The Phase-0a effective shards, written after the v2 sweep’s inputs, carry live calls that refute source designations this ledger’s dispositions lean on. Two bite: OPEN-CALL 3 for `(H-GENHN-CLEAR)` — “fixed-string grep for that designation in `GENHN_PROOF_2026-08-08.md` returns zero” (re-verified: count 0) — and OPEN-CALL 2 for `(H-JA-RES-CONJ)`, which supplies no external unit designation and refuses the `JA-EPS-CORR` conflation.
CONSUMED BY: HYP.54 and HYP.55, whose dispositions are corrected above; and HYP.105, routed to 0d by EFF-T3 OPEN-CALL 1 / EFF-T1 OPEN-CALL 4.
CLASS: corpus-consistency-item
PROPOSED DISPOSITION: NODE — keep the shard OPEN-CALLs and this ledger’s rows in one register; every future disposition citing “the accepted <X> site” must carry a grep-verifiable designation or be marked undesignated. ALREADY ABSORBED and not re-folded: OPEN-CALL 1 (`(H-JA-CONJ)_i`) is v2 HYP.53, whose COR-23 correction already removed the nonexistent accepted supplier; OPEN-CALL 4 is v2 HYP.105; OPEN-CALL 5 is v2 HYP.52/HYP.57. (v3 delta item 7.)

HYP.142  `GENHN-ERR-1` dual disposition
WHERE: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md` L2593, L2624; `HE6R1_RECON_2026-08-08.md` L926, L1031.
STATEMENT: Two un-reconciled records at HEAD. Settled side: “**GENHN-ERR-1 is settled.** The ordinary μ=2 stage law is the (2,K)-law at B=D′h, not at the old numeric node S=e₁h” (L2593), with “a final transcription-confirmation rides the next queue” (L2624). Un-retracted side: “Repairing the completion statement without weakening it **requires a new lemma** re-running GENHN’s f₁≥2 count argument on the corrected region” (HE6R1 L926), and the dated re-display heads “R7 finding 1 closed under the owner’s directive; **finding 2 routed to a proof unit**” (L1031).
CONSUMED BY: GENHN count laws at f₁≥2, hence the n≥8 leg (HYP.82) and the μ≥3 censuses (HYP.23).
CLASS: corpus-consistency-item
PROPOSED DISPOSITION: NODE — reconcile the two records and say which governs; escalates to MATH if the HE6R1 reading governs, since that reading owes a new count lemma. (v3 delta item 8.)

HYP.143  `HE3-BOX-6` ramified branch (ii)
WHERE: `lean/notes/openmath/HE3_PROOF_2026-08-08.md` L1334–1361, L1694.
STATEMENT: “**HE3-BOX-6 (THE ONE SURVIVING GAP** — found by this unit’s own review, before any hostile pass; it localizes to μ≥4, so μ=3 is unconditional).” LEMMA HE3-4 branch (ii) has no test key at a non-integer dv height, and the substitute ramified base change O ↝ O[Π]/(Π^ℓ−π) is “stated too cheaply: **Φ′ need not remain irreducible over O₂**”, so the SLOT LEMMA and HE3-1’s norm computation are unavailable there. Post-R8: “**Only the ramified branch (ii) remains in HE3-BOX-6.**” The repair route (higher-degree test polynomials at fractional heights, i.e. the higher-order Montes construction) is “IDENTIFIED REPAIR ROUTE (**not executed here**)”.
CONSUMED BY: COROLLARY HE3.B for μ≥4, i.e. degree n ≥ e₁f₁μ ≥ 8 — the supplier under HYP.81’s conjunct above μ=3, alongside HYP.82. HE3.A and [GENHN-HE(μ)] stay UNCONDITIONAL for μ≤3 and every n≤7.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — named repair route, not executed. Supplier-side only: it refines HYP.81 rather than adding a conjunct. (v3 delta item 9.)

HYP.144  `GENTOW4-BOX-1/-2/-4`
WHERE: `lean/notes/openmath/GENTOW4_PROOF_2026-08-09.md` L577–584, L585–590, L614–618.
STATEMENT: BOX-1 (mixed-side multiplicity tie) — the tie mu2*(r) = m_r “is UNPROVED here (S4; Ore-II/FGMN Lemma 2.17 content — a faithful-cite unit in GENTOW2’s pattern would retire it)”; READ and σ are unaffected, what is lost is the level-1 prediction of block length. BOX-2 (partial-side entry budgets) — the budget fibration is proved only on the FULL-side locus 𝒯; “the item-(4) **COUNT layer stays open**”. BOX-4 (grade) — “**0/2 attempt**, composed this session, no hostile arc”, over a conditionality stack including HETOW-1/2 (HETOW 0/2) and the HE6R1 0/2-grade annex stack.
CONSUMED BY: partial-side count laws feeding the same μ≥3 count layer as HYP.139 and HYP.142.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — BOX-2’s open COUNT layer is the binding residue; BOX-1 is retirable by a faithful-cite unit; BOX-4 is a standing grade cap on all three. (v3 delta item 10.)

HYP.145  GENTOW2 S6.1 rows 23–24
WHERE: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md` L1342; `GENTOW5_WI_2026-08-10.md` L480.
STATEMENT: “Status disclosure: rows 23-24 enter at DESCRIPTIVE / record-interpretation status, **not consumed status** — a future round elevating either cite to consumed status **owes** the S6.1 two-leg method.” Row 23’s content, the avatar = w identification, “is NOT consumed and is now **measured to GAP at LW3**.”
CONSUMED BY: HYP.66 (`WFRAME OPEN-3`), which is gated on exactly this row; and any future consumed-status use of rows 23–24.
CLASS: scope-fence
PROPOSED DISPOSITION: NODE — preserve the descriptive fence and the two-leg debt attached to elevating it. (v3 delta item 11.)

HYP.146  `W11-BOX-1`
WHERE: `lean/notes/openmath/W11_PROOF_2026-08-08.md` L474.
STATEMENT: “**W11-BOX-1 (n = 2 only).** The general W-11 — the menu tie at all degrees and orders — is **NOT proved**: S4.3 is a program with named owed inputs (S_λ(q) censuses, JB row-12 residue, JC warrant, uniform drainage).”
CONSUMED BY: any W-11 use above n=2; its named owed inputs are HYP.21 (JB row 12), HYP.20 (JC warrant), and the drainage rows HYP.27/HYP.30.
CLASS: hypothesis-box
PROPOSED DISPOSITION: MATH — a program, not a proof. Distinct from HYP.128 (`W-10` all-O), which is an instance-generality edge, not a menu tie. (v3 delta item 14.)

HYP.147  `exists_anisotropic`
WHERE: `leanfinal/notes/GENUINE_DENSITY_2026-08-13.md` L697, L704.
STATEMENT: “What is **fenced out**: the *general-`O`* inert lower bound … the `gate_bracket_*` payoff is therefore stated at `q = 2, 3` rather than for all `O`.” The missing declaration is displayed: `theorem exists_anisotropic (O) [bundle] : ∃ a : Fin 2 → O, Anisotropic a`.
CONSUMED BY: the general-`O` reading of the `gate_bracket_*` payoff; the q=2,3 statement stands without it.
CLASS: lean-open-statement
PROPOSED DISPOSITION: NODE — declaration/proof-packaging; re-verified absent from both trees (`grep -rn exists_anisotropic leanfinal/ leancheck/ --include=*.lean` returns nothing), plausibly reachable from leancheck’s `card_aniPairSet` / `2A + q = q²` but not landed. (v3 delta item 15.)
**DISCHARGED 2026-08-14 (CERTAIN-NODES BATCH D, CN-15)**: `Uniformity.Density.exists_anisotropic` (`leanfinal/Uniformity/Density/AnisotropicForms.lean:149`, commit `d714d94a`), signature byte-identical to the row's own displayed target: `(O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] : ∃ a : Fin 2 → O, Anisotropic a`, sorry-free, Lean-core axioms. **Lands in `leanfinal`, not `leancheck`** (orchestrator's placement ruling on the node's RISK disposition (b), minus the file move): the finite-field anisotropic-pair count is **re-derived from mathlib**, not imported from leancheck's `two_mul_card_aniK` as this row's own route sketch guessed — a new self-contained `AniForm`/`rootPairMap`/`exists_aniForm` triple (`AnisotropicForms.lean:55-124`), named apart from leancheck's `AniK`/`rootMap` so the two repos' open namespaces stay unambiguous. Route: lift the residual anisotropic pair through `IsLocalRing.residue_surjective` and read anisotropy off `aniForm_iff` after reducing mod `𝔪` (`leanfinal/notes/CN_BATCH_D_2026-08-14.md`). **Residual scope, not covered by this discharge**: the row's own CONSUMED-BY target — "the general-`O` reading of the `gate_bracket_*` payoff" — is a separate downstream integration not yet performed (the payoff still reads `q = 2, 3` at `Gates.lean:441`/`:454`), and the new `exists_aniForm` duplicates leancheck's own `exists_aniK` rather than merging with it (retirement decision booked as MQ-6).

### v4 additions from the weld-face audit

Two rows folded from `runs/qgen/WELD_FACE_AUDIT.md`. HYP.148 is the one weld face the capstone path genuinely consumes, previously indexed only through its sub-residue; HYP.149 is the audit's own synthesis and asserts nothing.

HYP.148  `GENHN-BOX-2` / the W-9 graded face
WHERE: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md` S6.1 L865–921, BOX L1331–1338 (re-verified at L1338), dependency ledger L1511–1514 (re-verified at L1512–1513); `SG2_PROBE_2026-08-10.md`.
STATEMENT: LEMMA GENHN-4’s layer 1 at μ≥3 consumes COROLLARY W-9’s twisted group algebra as the carry bookkeeping rather than re-deriving it. GENHN’s own dependency ledger, verbatim at HEAD: GRTJC W-6..W-9 + JC-LOAD/W-8 are “consumed at LEMMA GENHN-4 layer 1 (μ ≥ 3) — **the ONE weld face inside a count law**, disclosed (GENHN-BOX-2); elsewhere frame-only (GENHN-2 re-proves the slot geometry elementarily)”. The box itself prices it: “the count laws at μ ≥ 3 stand on one accepted weld face” (L1338). **This is the ONE weld face inside a count law on the whole capstone path** — the audit’s single REACHABLE-AND-CONSUMED verdict across ten chartered rows plus two unchartered faces.
CONSUMED BY: GENHN.A(iv) at μ≥3 → the composite-stage count laws → GENIND.B / W-12.D at n≥4; **first live degree n=6**, the same threshold `[GENHN-HE(μ≥3)]` (HYP.81) already carries. NOT inherited by the σ chain (HE3 L1293, re-verified: “the W-9 weld face (GENHN-BOX-2) is absent from the σ chain”; HE3 L88, re-verified: “SIGMALAW, JC-LOAD, DULEMMA: not consumed”) and NOT by the tower leg (GENTOW5 L157, re-verified: “no W-9-style weld face is consumed”; L1311, the GENTOW-BOX-1 analogue RETIRED). Carries HYP.139 (the W-1 transport, ATTEMPT) as its sub-residue.
CLASS: conditional-theorem-leg
PROPOSED DISPOSITION: **CARRY** (COR-WFA-12) — and it is now an explicit preview conjunct, which it was not before. Discharge status has two independent readings and both are recorded: (a) **from the weld notes alone, NO** — `SG2_PROBE_2026-08-10.md` L26–29 returns NEEDS-X, “GENHN-4 is NOT re-derivable from WELDMASTER (M0)–(M4) + WM-COB + J-D0 as those clauses are stated”, with two named obstructions (perimeter re-instantiation; the additive recentering, since “(M4)’s covariance is a character-system action, not the additive-translation formula”); (b) **from the accepted corpus, a named route exists and is CARRY-class** — see HYP.149, which is the audit’s synthesis and is asserted by no accepted note. Compensating instrument already standing: GN-REFINE3 (pointwise re-division transport at every μ=3 stage-α event, GENHN L1834 “GENHN-BOX-2’s compensating instrument, delivered”). Machine corroboration: GENHN L1710, pin checks per row, 0 violations. Until HYP.149 runs, this row is carried, not discharged.
**v6 ARC NOTE (2026-08-14).** The candidate discharge route (HYP.149) has run its r1 repair round and a post-pass rider and now sits at **clean-pass 1 of 2** — see HYP.149 for the full arc. This row is **UNCHANGED, CARRY at full strength**: nothing licenses a move until the route's second (model-diverse, gpt-5.6-sol) clean pass lands, queued not before Tue 2026-08-18 10:23+.

**ARC NOTE (2026-08-16, unit OM-9) — the box's ABSTRACT side is now theorems; the FACE stays carried; the WELD-ZERO fence untouched.** W-9's clauses (i)–(iii), which this face consumes, are now PROVED at the landed carrier vocabulary (chapter F first landings, AMENDMENT A-W.2; certified first by `om9_weld_cert.py` LEG C — including the exact biconditional assoc ⟺ cocycle over ALL unit tables at four (K,E) pairs, and the |Z²| = |Kˣ|^E count law): `CarryCocycle` (F.07) with `TwistedAlgebra.mul_assoc` (F.09 — associativity from the cocycle identity, the `EFF.GRTJC.90` elegance in the abstract direction), `finrank_eq`/`nat_card` (F.10a/F.13 — "one K-line per dv-height"), `pow_card_single` (F.10b — JC-F1's power basis at the SIGNED orbit product ∏ c(1,k)), the unit laws, and two fresh certified-then-proved structural lemmas (`c_one_comm`; **`c_comm`: every carry cocycle is symmetric** — JC-F1's cyclic presentation echoed abstractly). The carrier `GenhnBox2` (F.11) is LANDED at gate signature with clause (iv) structurally absent and the μ ≥ 3 guard in the Prop. **Effect on this row: the carried content NARROWS to exactly the instantiation claim** — that GENHN-4 layer 1's carry table IS a `CarryCocycle` instance (`∃ cc` matching the site's table) — plus HYP.139's transport sub-residue; every consequence downstream of the instantiation is now a Lean theorem, not a cited conclusion. **Still carried, disposition UNCHANGED: CARRY at full strength.** The discharge route stays HYP.149 = WELD-ZERO at clean-pass 1 of 2 (pass 2 IN FLIGHT, Fable-max, no landing commit at HEAD): this unit consumed NOTHING from `WELDZERO_2026-08-14.md`, transcribed no WZ lemma, and anticipates nothing — honesty F-2 verified intact at close. Unit record: `docs/openmath-campaign/OM-9_weld_2026-08-16.md`.
**v7 ARC NOTE (2026-08-15).** The still-owed second clean pass changes SUPPLIER, not status: `docs/PROJECT_STATE.md` append **#56** (L4778–4799) reassigns the WELD-ZERO + JD0 confirmation passes from gpt-5.6-sol to a Fable-max agent, and its own EOF line records "WELD-ZERO confirmation pass (pass 2 of 2) runs on Fable-max now" — LAUNCHED, **IN FLIGHT** at fold time (no landing commit exists in the tree at HEAD). This row is **UNCHANGED, CARRY at full strength**: a launched confirmation pass is not a landed one, whichever model runs it.

HYP.149  `GENHN-BOX-2` discharge route — gr(O_L) re-aim + GENTOW5-A0/A1
WHERE: **`runs/qgen/WELD_FACE_AUDIT.md` §4 — the audit’s own synthesis.** Supplying displays, all re-verified at HEAD: `GENHN_PROOF_2026-08-08.md` [r2] erratum L515–517 (“S6.1 layer 1’s graded frame re-aims at **gr(O_L)** … every graded read of an evaluated element happens in gr(O_L)”), with the forcing chain establishing L a complete DVR field at L500–512; `GENTOW5_PROOF_2026-08-09.md` LEMMA GENTOW5-A0 at L159–183 (“gr of a valued field is a graded division ring”; “pointwise, at a root, there is no carry problem”) and LEMMA GENTOW5-A1 at L209–248 (the coefficient-for-coefficient dictionary, `c_j = ι(γ_j)·θ_{μ₂−j}^{−1}`, x0-free); GENHN-2’s pointwise-faithful slot passage.
STATEMENT: One fold unit rewrites GENHN-4 layer 1 in the A0/A1 idiom, replacing the imported W-9 twisted algebra with gr of the leaf field, and strikes GENHN-BOX-2. If it runs clean it would **retire BOTH HYP.148 and HYP.139** — taking the weld layer’s contribution to the capstone’s conditionality from one face to zero — and would remove two conjunct-bearing obligations from the preview. Non-circularity checked by the audit: at level 1 GENHN **derives** its own S4 cocycle from the normalizer arithmetic (L732–733, re-verified: “n(κ)^t = ẑ^{fl}·n(tκ) with the explicit integer fl = the wrap count — W-9’s cocycle, literal”) and only **identifies** it with W-9’s, so the route does not re-consume the face it replaces. Independent corroboration that the missing content is the right target: SG-2’s item X(ii) (the additive action T ↦ T+s) was DELIVERED at attempt grade (census O-1).
CONSUMED BY: **nothing — and it STILL may re-disposition nothing.** It is indexed so the synthesis is not lost, and so that any future claim to have discharged HYP.148 must point at a unit rather than at this row.
CLASS: audit-synthesized-unit
PROPOSED DISPOSITION: **IN-PROGRESS** (re-dispositioned PROPOSED-NODE→IN-PROGRESS, **COR-WZ-01**) — **the WELD-ZERO composition unit was LAUNCHED 2026-08-14** under the owner’s directive at append #49: *“Lets also try the candidate route synthesized by the audit right now”* — compose GENHN’s [r2] `gr(O_L)` re-aim + GENTOW5-A0/A1 into the fold retiring GENHN-BOX-2 (HYP.148) and the W-1 transport (HYP.139), taking the weld layer’s contribution to the capstone’s conditionality **from one face to zero**. Launch terms recorded verbatim from #49: **corpus-grade note, 0/2, hostile arc owed post-reset.** **What IN-PROGRESS does and does not license.** It licenses nothing new: HYP.148 stays CARRY at full strength and HYP.139 stays MATH at full strength until this unit *lands and passes its arc*. A launched unit is not a result, and the preview is untouched by this re-disposition. The bucket exists only so a reader can tell “synthesized but unowned” (v4) from “running” (v5). The v4 reasoning for the old bucket is retained below and still governs what may be claimed: audit-synthesized, asserted by **no accepted note** (the audit states this itself: “the route is this audit’s synthesis, not a corpus display”). It needs its own unit before it can re-disposition anything, and it is deliberately NOT counted as a discharge of HYP.148 or HYP.139, both of which stand at full strength above. **One audit caveat is CORRECTED on fold:** the audit’s caveat (b), “GENTOW5 is itself at grade 0/2 (hostile arc owed), so the fold inherits that arc”, is STALE at HEAD. `GENTOW5_PROOF_2026-08-09.md` L2026 reads “Grade: **ACCEPTED 2/2** stands, ANNOTATED by RUN A”, and `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 10 reads GENTOW5 “**CERTIFIED 2026-08-12**”; by this ledger’s own standing rule the 2026-08-12 SOL certification ledger is HEAD-of-record for unit grades and supersedes in-note grade boxes (the audit appears to have read one of the L1471/L1531/L1612 repair-round “0/2 UNCHANGED” lines, which predate the acceptance append). The proposed unit therefore does **not** inherit a 0/2 arc — this strengthens the route rather than weakening it, and it does not change the PROPOSED-NODE disposition, which rests on the absence of any asserting note, not on GENTOW5’s grade. Same correction pattern as HYP.140.

**v6 ARC UPDATE (2026-08-14) — still IN-PROGRESS, licenses nothing.** Source: `lean/notes/openmath/WELDZERO_2026-08-14.md`. The composed unit has moved through one repair round and one post-pass rider since launch, and now sits at **clean-pass 1 of 2**. **r1 (2026-08-14):** one CRITICAL repair (**C-1**) — WZ-3(ii)'s type-preservation claim is FALSE at live ϑ and is withdrawn; the multiplicative half is re-routed through a relabelling bijection (LEMMA WZ-3 (r1)), and J-D0 is removed from the fold's supplier list (it remains a supplier of GENHN-4's own layer 3, untouched by this fold) — plus one GAP repair (**G-1**) — the §5 coverage claim is corrected, and GENHN's own sealed live-wrap row (972 events, pins dead at every one) is folded in as evidence FOR the fold — plus eight further minors, all cured in the same round; status line after r1: "composed, r1, attempt 0/2, hostile arc owed IN FULL over the r1 effective text (two clean passes, both after the r1 reset)." **Post-pass rider (2026-08-14, after r1):** a hostile pass on the r1 effective text — the **Opus/Claude-arm pass, `runs/comp13/WZP2_output.log`** — returned **0 CRITICAL + 0 GAP + 6 minors**; a minors-only pass is a clean pass, its six minors fold as riders, and the repair counter is **not** reset — **the clean-pass counter therefore stands at 1 of 2**, with this pass as the first. **Still owed at the acceptance gate:** the **gpt-5.6-sol confirmation pass** — the second of the two required consecutive clean passes, model-diverse per the standing prover-RCT protocol — taken over the r1 effective text PLUS this rider, queued **not before Tue 2026-08-18 10:23+** (the codex weekly usage window's reset); until it lands the unit's own status line reads **"composed, attempt 0/2, hostile arc owed"**, and by `(GRADE)` the instance stays 0/2 regardless of any supplier's grade. **What this does and does not license (unchanged from the launch note above):** nothing new — HYP.148 stays CARRY and HYP.139 stays MATH at full strength, and this row stays IN-PROGRESS, until the second clean pass lands and the arc is accepted.
**v7 ARC UPDATE (2026-08-15) — still IN-PROGRESS, licenses nothing.** Source: `docs/PROJECT_STATE.md` append **#56** L4778–4799. The second (model-diverse) clean pass this row has owed since v6 — there described as "the gpt-5.6-sol confirmation pass" — is REASSIGNED under Asvin's Fable-max substitution directive (#56, quoted in full at this file's header note): "try ... to finish the blueprint with fable on max reasoning instead of sol pro 5.6." Append #56's own closing line: "WELD-ZERO confirmation pass (pass 2 of 2) runs on Fable-max now." **LAUNCHED, IN FLIGHT at fold time** — no commit in the tree at HEAD records its landing, so the clean-pass counter stays at **1 of 2** and the unit's status line is unchanged: "composed, attempt 0/2, hostile arc owed." Model substitution changes who may supply the confirming pass, not the counter, not the grade, and not this row's bucket: **HYP.148 stays CARRY, HYP.139 stays MATH, this row stays IN-PROGRESS** — all at full strength, exactly as at v6.

### v7 additions from the HE6/T2 adjudication

Five rows folded from T2's dated consumption record (2026-08-14), `lean/notes/openmath/T2_SIGMA_LADDER_MASTER_2026-08-12.md` EOF append, commit `66062771`, itself answering `spec/EFF-HE6.md` OPEN-CALL 1/2. Every quote below was re-verified at its cited commit/file/line before transcription. This adjudication is scoped to **T2's own consumption of HE6**; it is not a general re-audit of HE6's other two named consumers (HE7, HE6R1 — `spec/EFF-HE6.md`'s zero-orphan check names exactly these three), and none of the five rows below asserts anything about those two.

HYP.150  EFF-HE6 OPEN-CALL 2, closed for T2's consumption
WHERE: commit `66062771` (T2 EOF append, 2026-08-14), parts (a)/(c)/(d); raised by `spec/EFF-HE6.md` OPEN-CALL 2, L2507–2522.
STATEMENT: OPEN-CALL 2 flagged that three of HE6's four 2026-08-12 A3 corrections (F-1, F-3, F-4) sit outside every one of T2's nine HE6 pin spans, with F-1 landing on `HE6-SLOT-SEAM`, a span T2 cites 48 times, and asked whether T2 owes two new pins, widened spans, or a record that its consumption is confined to clauses A3 does not touch. T2's adjudication samples nine consumption sites across its own rounds (S1.2, S3.2, the HE3-INSTANCE box, the pass-1 seam gate, r4 repairs 1/9, S1.8C's key-freeness, r9 repairs 1(a)/1(b)/1(e)) and finds every one immune: T2's own `(GAMMA)`/`(HE6-SEAM)` displays already ARE F-1's corrected form (letter-for-letter, per part (a)); F-3 corrects a lemma (`LEMMA HE6-0`, the disk criterion) T2's r10 repair 1(c) already declines to consume; F-4 corrects HE6 towards the reading T2's own S1.3 already carries.
CONSUMED BY: T2's pin-table discipline (the carrier for HYP.41/HYP.42); the record is T2-side only — HE7 and HE6R1's own consumption of the same three A3-corrected spans is untouched by this adjudication and remains, if it matters at all, an open question at EFF-HE6's own OPEN-CALL 2 for those two notes.
CLASS: audit-work-item
PROPOSED DISPOSITION: **CLOSED-FOR-T2.** No tenth or eleventh pin is owed, no span is widened, and T2's own two consumed `HE6-SLOT-SEAM` clauses are exactly F-1's corrected displays — option (c) of OPEN-CALL 2's three offered remedies, taken because it is simply true rather than chosen among equals. **Residual, explicitly not closed by this row:** EFF-HE6 OPEN-CALL 2 as a general compilation finding is closed only for T2; nothing here checks whether HE7 or HE6R1 consume the bare pre-A3 forms.

HYP.151  A3 F-1's "vacuous" claim: a real, dated HE6 source defect, sharp threshold
WHERE: commit `66062771`, part (b), the re-derivation.
STATEMENT: The pre-A3 `HE6-SLOT-SEAM` bare display is not merely stylistically loose but AFFIRMATIVELY FALSE in HE6's own consumed regime. At the attaining index `i₀` the minimum height gives `v(a_{i₀}) = (k−i₀h)/e₁`, strictly positive once `k > i₀h`; sharper, every summand index `j = i₀+e₁t < D′` has `jh ≤ (D′−1)h`, so at every height `k > (D′−1)h` EVERY term of the bare sum vanishes and the uncorrected display asserts `res(A(ξ)/ϖ(ξ)^k) = 0` — against the same lemma's own `dv(A(ξ)) = k` EXACTLY, which forces `A(ξ)/ϖ(ξ)^k` to be a unit with nonzero residue. HE6's own standing regime, DEFINITION HE6-1's `κ > D′h > (D′−1)h`, sits entirely inside the false region. The span's own `[r2]` witness `(e₁,f₁,h)=(2,2,3)`, `k=3` sits in the coincidence regime `k ≤ (D′−1)h = 9` where the bare and corrected readings agree, which is exactly why it never caught the defect across four rounds.
CONSUMED BY: nothing on the capstone path — A3 F-1 (2026-08-12) already supersedes the false display with `γ_k(A)`, and HYP.150's nine-site sample finds zero reliance on the bare reading anywhere in T2.
CLASS: corpus-consistency-item
PROPOSED DISPOSITION: **CLOSED** — informational/historical. The defect is real and precisely bounded (`k > (D′−1)h`), but it lives in already-superseded pre-A3 text with a confirmed zero-consumer footprint; nothing is owed beyond this record.

HYP.152  Consumption, not citation, is the gated relation (standing protocol)
WHERE: `T2_SIGMA_LADDER_MASTER_2026-08-12.md` §S5 item 3's governing sentence (quoted at L4381, and again at L4459/4469/4471 per T2's own post-pass rider 3), invoked at commit `66062771` part (d) to answer both of OPEN-CALL 2's "does T2 owe a new pin" questions and, via F-3, OPEN-CALL 1's tenth-pin question.
STATEMENT: A byte-range CITATION to a span that a later correction touches does not by itself create a pin obligation. The gated relation is CONSUMPTION: whether any of the citing note's own conclusions actually relies on the specific (possibly stale) byte content of the cited span. T2's nine A3-sampled sites are citation-adjacent to the corrected spans but the test the adjudication actually applies at each is consumption, and by that test all nine are immune.
CONSUMED BY: HYP.150's and HYP.154's dispositions directly; general applicability to any future EFF-* OPEN-CALL of the same shape (a correction landing outside a downstream note's pin table).
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — standing protocol clarification, illustrated by this adjudication rather than invented by it (the sentence itself predates this fold). No mathematics attached; not itself a capstone-path obligation.

HYP.153  "The compiler has invented no span" (standing EFF-* process rule)
WHERE: `spec/EFF-HE6.md` L2505, L2522.
STATEMENT: The EFF-* compilation process's self-audit discipline: a compiler pass may FLAG a decision point as an OPEN-CALL (e.g., "does T2 owe a new pin?") but must not itself invent, apply, or resolve the pin/span/decision — such calls are routed to the relevant note's own owner (`FOR-0b`) or to Asvin (`FOR-0d`) as a named, dated OPEN-CALL, never silently absorbed. Commit `66062771` is exactly such a FOR-0b resolution — T2's owner adjudicating T2's own OPEN-CALL 2 exposure — executed downstream of, and consistent with, the compiler's flag.
CONSUMED BY: every EFF-* compilation's OPEN-CALL taxonomy (FOR-0b/FOR-0d); demonstrated in practice by this adjudication and by HYP.150/HYP.154.
CLASS: audit-work-item
PROPOSED DISPOSITION: NODE — standing process rule; no mathematics attached, no capstone-path obligation.

HYP.154  `LEMMA HE6-0`'s tenth-pin question, re-classed from a T2 decision to a chapter-cut concern
WHERE: `spec/EFF-HE6.md` OPEN-CALL 1, L2499–2505; commit `66062771` part (a), F-3's disposition; T2's own r10 repair 1(c), "consumes no disk criterion."
STATEMENT: OPEN-CALL 1 asked whether T2 owes a tenth pin for `LEMMA HE6-0` (the disk criterion, in no pin span itself, and consumed inside `HE6-ACCOUNT` by HE6-3(a)'s proof and by HE6-`.22` — "a chapter cut assembled from T2's pins alone would omit a lemma two of them consume"). Under HYP.152's consumption test, F-3's disposition in the adjudication answers the T2 half decisively: T2's r10 repair 1(c) already establishes T2 "consumes no disk criterion" at all — the S1.7 clause 1 property it reads as the intended-disk property is LEMMA HE6-1's own conclusion, not HE6-0's. So T2 owes no tenth pin, because it does not consume the lemma the question is about. What OPEN-CALL 1 correctly diagnosed — that HE6-0 is genuinely needed by HE6-3(a)'s proof, which T2 does partially cite/consume elsewhere — is real, but it is not a T2 pin-table gap: it is a fact about what a future *chapter cut* built from T2's nine pins alone would be missing, i.e. a leanspec/0e extraction-scope concern, not a T2-owner decision.
CONSUMED BY: any future leanspec chapter-cut extraction that assembles HE6-adjacent material from T2's pins (would need to separately source `LEMMA HE6-0` from HE6 itself, not from T2).
CLASS: cite-scope-residue
PROPOSED DISPOSITION: NODE — re-classed from a T2-owner (FOR-0b) decision to ordinary chapter-cut/leanspec bookkeeping; no pin is owed, no action is owed of T2, and no action is currently queued of the leanspec process either (recorded only so the concern is not lost if a chapter cut ever needs HE6-0).

## MAINTENANCE QUEUE (owner: orchestrator)

Actions, not conditions. These are NOT hypotheses and are not counted in the row tallies; they are recorded here so the completeness sub-sweep’s action items are not lost by being un-foldable as HYP rows.

MQ-1  **n=2 adversarial pass.** `leancheck/notes/N2_EXACT_2026-08-13.md:327` — “**No independent adversarial (Codex) pass was run on this unit.**” This unit supplies the capstone’s entire degree-2 leaf (ram = 1/(q+1), split = inert = q/(2(q+1))), which the preview calls unconditional. Already in PROJECT_STATE #45a’s queued batch (“the n=2 codex pass”). (v3 delta item 6.) **v7 note:** `docs/PROJECT_STATE.md` append **#56** names "the n=2 adversarial pass" explicitly in the sol-deferred queue it reassigns to Fable-max (see this file's header note, THE FABLE-MAX SUBSTITUTION). This action may now be discharged by a Fable-max agent; codex remains optional belt-and-braces. Not yet run either way as of fold time.

MQ-2  **Consumption checks + dated appends.** `runs/qgen/EFFT3_crossread.md:149` — “GENTOW5-W consumption check was never run and its dated append never landed”; `spec/EFF-T3.md:1599` — ABS-G5W “marked ‘check + append outstanding.’”; `lean/notes/openmath/T4_CERTIFICATE_WITNESS_2026-08-12.md:2241` — “Consumption checks + the absorbed notes’ dated appends” ride the next queue. Already in PROJECT_STATE #45a’s queued batch. (v3 delta item 12.)

MQ-3  **[GMN12] §4 characteristic audit — unperformed.** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` §6 item 5 L481–482: “**[GMN12] §4 (theorem of the index) characteristic-audit.** I did **not** read GMN §4 line by line. §3 F-2’s claim that its argument is characteristic-free is *a plan, not a verified fact*.” This bears on owner question 1: it qualifies the internal-F-2 branch of HYP.15’s choice, which is offered as the alternative to citing. Not in the PROJECT_STATE #45a batch — new. (v3 delta item 13.) **v5 status change:** question 1 took the **cite** branch, so this audit no longer qualifies a branch anyone is walking. It **lapses as a question-1 rider** and is retained only as general cite hygiene (and as the price of ever re-opening the F-2 branch — see HYP.16).

MQ-4  **JD0 optional codex pass (belt-and-braces).** Queued, not owed. Append #49 signs the JD0 machine grade as the bar (question 6, HYP.39 CLOSED-SIGNED) while keeping the post-reset codex pass *“queued as belt-and-braces.”* Recorded here so that closing HYP.39 does not silently swallow a queued action: the pass is optional, it gates nothing, and its absence caps no claim. (v5.)

MQ-5  **CN-21 / degree-2 inert certificate merge (landed-file merge decision).** `leanfinal/notes/CN_BATCH_D_2026-08-14.md` "For the orchestrator": the general-`n` `Uniformity.Density.typeOf_inert_of_irreducible_map` (CN-21, `InertLeaf.lean:179`) now subsumes the landed degree-2 `typeOf_inert_of_anisotropic` — at `n = 2`, `Anisotropic a` says exactly that the residual reduction has no root, i.e. is irreducible, and the two conclusions agree (`⟨{(1,2)}⟩`). Exactly parallel to CN-20/`typeOf_ram_of_eisenstein` (same batch note). Neither merge has been performed: both would touch a landed file, which is an orchestrator call, not a fleet-batch action. Not urgent — the two declarations coexist without conflict or duplication of *proof* (one is a special case of the other, not a re-proof). (v6, booked from append #50.)

MQ-6  **`exists_aniForm`/`exists_aniK` duplication (retirement decision).** `leanfinal/notes/CN_BATCH_D_2026-08-14.md`: CN-15's `Uniformity.Density.exists_aniForm` (`AnisotropicForms.lean:124`) duplicates leancheck's `UniformityCheck.exists_aniK` (`N3Density.lean:234`) — proved by a different route (re-derived from mathlib rather than from `two_mul_card_aniK`), and named apart deliberately so the two repos' open namespaces stay unambiguous, since `leanfinal` must not import `leancheck`. This is the accepted price of the import fence, not a bug. If the fence is ever lifted — the same placement question CN-15's own RISK line left open, moving `FiniteFieldQuad.lean` into `leanfinal` — one of the two copies should be retired in favor of the other. No action owed now. (v6, booked from append #50.)

MQ-7  **GENTOW6: one unresolvable commit token.** `spec/EFF-GENTOW6.md` §3.2 (P-02, ~L1018): the seal citation "sealed `640b31ff` at `14329683`" has `14329683` and the RED commit `e803c21d` resolving, but `git cat-file -t 640b31ff` → "Not a valid object name." The seal event itself is independently confirmed by `14329683`'s own commit message ("GENTOW6 r1 (commit 2/3, SEAL)..."), so nothing mathematical is in doubt — one token in `lean/notes/openmath/GENTOW6_PROOF_2026-08-09.md`'s prose is wrong or points outside this repository. OPEN-CALL 4, "FOR-0b." **MQ-LANDED (caught mid-v7-fold):** `lean/notes/openmath/GENTOW6_PROOF_2026-08-09.md`'s own dated correction append (2026-08-15, commit `b8365d9e`) resolves this exactly — re-independently-confirmed there: `git cat-file -t 640b31ff` fails, `14329683` resolves and is the seal, `e803c21d` is the RED run — "Erratum on the citation only — no artifact md5, verdict, grade or box status moves." No action remains owed.

MQ-8  **HETOW: F-2's transliterated, unmarked-elided quote.** `spec/EFF-HETOW.md:1819` (also 1966, 2171): the GENTOW1 Step-4 quotation at HETOW `.54` is ASCII→Unicode transliterated AND silently elides the source's parenthetical justification ("the level-1 Newton polygon of the inner read has the one side of slope kappa2, residual psi2^{mu2} zero-free at the corners —"), splicing the em-dash with no ellipsis. Substance and attribution are correct; only quotation discipline is off. Disposition NEAR-MISS (v3 rule 15); referent verified at `GENTOW1_PROOF_2026-08-09.md:246`. OPEN-CALL 3. Proposed fix (compiler suggestion, not source text): re-quote with an explicit `…` and the source's ASCII notation, or re-mark as paraphrase. **MQ-BATCH-PENDING**: no commit touching `GENTOW1_PROOF_2026-08-09.md` postdates the sweep; nothing depends on the letter.

MQ-9  **GRTJB §7.1: 6,575-vs-6,700 headline.** `spec/EFF-GRTJB.md:4806` (and `-s3of3.md:157`): the sample column sums to `1+893+25+893+893+34+79+194+955+28+79+5+4+2,480 = 6,563`, plus 4 tooth families × 3 rows = 12, giving **6,575** — against the headline **6,700**, a discrepancy of 125 not reconstructible from the table (substituting the with-chambers JB-TREE count, 125 for 79, gives 6,621, still not 6,700). "Source defect 2"; "**nothing in the note's fences depends on the 6,700**." OPEN-CALL 13 (merged numbering) / OPEN-CALL 4 (pre-merge shard 3). **MQ-BATCH-PENDING**: no commit touching `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` postdates the sweep; the merged spec reports both numbers and flags the gap rather than resolving it.

MQ-10  **GRTW2 §6.1: 6,396-vs-6,403 headline.** `spec/EFF-GRTW2.md:2005` (and `-s1of2.md:1773`): the 17-family sample column sums to **6,396** against the header's **6,403** — a 7-sample shortfall not reconcilable from the displayed table (family count, 17, reproduces exactly). "Source defect 4"; every family is GREEN with 0 violations, so no claim is thereby false. **MQ-BATCH-PENDING**: no commit touching `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md` postdates the sweep; the merged spec reports 6,403 (the note's own re-verified figure) and flags the gap.

MQ-11  **HE7 Q1: two battery-table defects, signed non-repairs.** `spec/EFF-HE7-s2of3.md:534–540` and `:1694–1696`: (i) the `[r1]` degenerate-count distribution mislabels one row "F₅[[t]] λ=5/2 s=2 → 2" where Q1's table forces `s=1` (the count and the total of 8 are both right; one letter is wrong — "source defect 2"); (ii) Q1's three σ columns sum to the *read-OK* member count, not the `members` column, on the four rows carrying degenerate members, an unstated convention invisible except by arithmetic ("source defect 3"). Both are explicitly **signed non-repairs**: `lean/notes/openmath/HE7_PROOF_2026-08-08.md` is byte-frozen, so each is disclosed with its audit rather than edited, by design. **MQ-BATCH-PENDING in the narrow sense** (no append has corrected either label/convention) **but no correction is owed** — the note's own protocol is to disclose byte-frozen defects, not fix them; nothing depends on either.

MQ-12  **LIFTCORNER: 15-vs-20 self-count, already corrected at merge.** `spec/EFF-LIFTCORNER.md:4335–4340`: shard 2 of the pre-merge compilation asserted "fifteen" `[TRANSCRIBED — certifier]` units in two places, but its own cited ranges (`.22`–`.28`, `.31`–`.36`, `.39`–`.45`, i.e. 7+6+7) and a fresh header recount both give **20**. Unlike MQ-7–11, this defect lived in a compiler artifact (the pre-merge shard), not in a byte-frozen informal proof note, and the merge step itself is the correction: the current, committed `spec/EFF-LIFTCORNER.md` records 20, not 15, "as a new source-defect finding ... not silently reconciled." **MQ-LANDED** — no further action owed; recorded here only so the finding is not lost.

## OFF-PATH (v3 TIER-3, one line each)

Recorded for completeness; none is on the capstone path, and none is counted in the tallies.

- `leanfinal/notes/GENUINE_DENSITY_2026-08-13.md:614` — the n=3 Python leg “needs a `ℚ_p`-factorization oracle; left as an open verification item.”
- `leanfinal/verification/EQUALCHAR_PROBE_2026-08-13.md:141` — the char-2 classifier fix “was validated empirically (exact match to Z_p) at N≤4, **not proved complete** in general.”
- `docs/TIGHTNESS_CENSUS_2026-08-11.md:97` (O-14 RIDER-DEBT) — minor acceptance riders owed per appends; “Some may have landed in B-wave folds; **not re-verified here**.”
- `lean/notes/openmath/WFRAME_NOTE_2026-08-10.md:374` — OPEN-4 (“w = 1 as a question, correctly housed”); the v2 dedup section already folds it into OPEN-1, so it is indexed, not new.
- `lean/notes/openmath/HE7_PROOF_2026-08-08.md:1304` — “(PE3) on the post-r3 text” — **SUPERSEDED at HEAD**: ANNEX F-1 (L1603–1605) records “HE7 was **ACCEPTED 2/2** at PE3”, so the pass the delta reports as owed has run.
- `lean/LeanUrat/Stage2/UniformityTarget.lean:92,107` — two `sorry`s in the superseded quarry capstone, by design and disclosed in the file header (“it contains exactly two `sorry`s — the two target theorems’ bodies — per the E-phase precedent”); distinct from the clean `leanfinal`/`leancheck` result.

## Deduplication and non-deduplication

- A0/A1/A2 are W12.D’s public fixed-n interface. [W12-H] and [GENIND-H] are lower suppliers, not extra conjuncts when expanded.
- Drainage levels are linked but not identical: A2 ← W12-BOX-4/DRAIN-N4 ← GENIND-(CS-1Q) for n≥4. Cubic Lean names are `UndecidedVanishes O 3 σ` and `drainage_three_of_triple`. GENIND-BOX-4 is a distinct bookkeeping box.
- CS-1 is a count-fibration with both menu and drainage consumers, CS-2 is a bracket, and CS-EXACT forbids bound-only laws; A1 is their public compression.
- [H-e]=CS-3 only when both the citable GMN decision and project-internal window pinning are included; at composite stages it supplies A0.
- [H-b] is JB row 12 only. JB-NOLEG is the strict four-row superset 4/5/12/22. They are not merged.
- [H-c] aggregates VD-m, C-coll, R-coll, PERIM-μ, DMULT-S, JD0-BOX-2, W2-VALUE, and reachable T4 residue. DMULT-S is double-parented through [H-a]/GRTJC and [H-c].
- GENTOW5-W(i), Q4’s conditional, and 𝒲_(≤i) are one live cumulative premise. WI certification proves an induction step, not the premise.
- W12-BOX-2/hMenu3 and W12-BOX-3/hExhaust3 are the HMENU3/HEX3 perimeter. TAIL-CERT=HEX3-BOX-1=HM3-BOX-1; ANNEX-2’s disc≠0 correction remains.
- Strong Hensel HYP.04 is not coprime-factor Hensel: X·X² is not coprime.
- `typeOf` shift/scale invariance is stronger than certificate-local lemmas such as `RamAt_shift`.
- T3-JOINT-OPEN and F4-JOINT are opposite objects—realized p-adic demand versus finite graded-carrier supply—and are not merged.
- WFRAME OPEN-1 absorbs the older “can w=1?” question.
- GENTOW6-BOX-1 overlaps COMPOUND-6.5′ on f₁≥2,μ₂≥3; P-BINOM and S8.1-MEMBER are adjacent proof units, not identical.
- `RealInstanceAt.faithful` and the Haar bridge are live indexed items, not superseded plans; only the Denef route remains superseded. **[v5 AMENDMENT — this line is now WRONG as written and is corrected, not deleted, so the change is traceable.]** Both rows moved off the capstone path at v5 by owner answers, and they moved for *different* reasons that must not be conflated: `RealInstanceAt.faithful` (HYP.97) is **OUT-OF-PATH-BY-POLICY** — `leanfinal` is Lean-core-only, so the placeholder conditions the quarry and remains a live obligation there (question 7); the Haar bridge (HYP.95) is **CLOSED** — the capstone no longer *asserts* Haar at all, because `genuineDensity` was redefined to be the proportion limit itself (question 5). One row was relocated; the other’s consumer was dissolved.
- MP1′ removes only an extra frame-level obligation: it is retired relative to the same LB1/MP1 triggers, which remain.
- GENIND-BOX-1 is coextensive with [GENIND-H]; GENIND-6 and ANNEX-LEMMA GENIND-C2Q are indexed under parent rows rather than counted as new public conjuncts.

v3 additions to this section:

- HEX3-BOX-1 (HYP.137) is promoted out of HYP.29’s index because it has a named live consumer, but the two rows are not merged and not duplicates: HYP.29 is the `hExhaust3` menu-exhaustion box, HYP.137 is the tail-σ law it explicitly does not need. Census O-10 (drainage) and GENIND’s S8.2 pin (W-12.B corroboration) name different consumers and are both correct.
- HE3-BOX-6 (HYP.143) is a supplier under HYP.81, not a new conjunct: [GENHN-HE(μ≥3)] is unconditional at μ≤3 (n=6,7) and rides HE3-BOX-6 only at μ≥4 (n≥8), where HYP.82 also lives. It is not merged with HYP.82 — a tower leg and a branch gap are different objects.
- W11-BOX-1 (HYP.146) and HYP.128 (`W-10` all-O) are distinct: a general menu tie versus an instance-generality edge.
- The GENTOW5_WI grade box (HYP.140) is a corpus-consistency row, the sibling of HYP.100, and does NOT correct HYP.40 or HYP.63 — SOL certification row 18 (2026-08-12) is HEAD-of-record and postdates both the note’s S7 box and census I-2.
- W-1 (HYP.139), GENHN-ERR-1 (HYP.142), and GENTOW4-BOX-2 (HYP.144) all feed the same μ≥3 count layer but are three separate obligations: a transport, a record reconciliation, and a partial-side count layer.
- Delta items already absorbed by v2 and deliberately not re-folded: the GENTOW5_WI NODE-disposition complaint (cured by v2’s COR-32/33 NODE→CARRY on HYP.63) and EFF-T1 OPEN-CALLs 1/4/5 (v2 HYP.53, HYP.105, HYP.52/57).

v4 additions to this section:

- **`[H-c]` is no longer J-D0’s home.** The v3 dedup line “[H-c] aggregates VD-m, C-coll, R-coll, PERIM-μ, DMULT-S, JD0-BOX-2, W2-VALUE, and reachable T4 residue” describes W12’s *definition* of the package and stays true as a definition — but it is not a consumption map. On the capstone path `[H-c]` is consumed by nothing (HYP.22), and J-D0 is consumed directly at seven cone notes (HYP.74). The two claims are not in conflict: one is what W12 declares `[H-c]` to contain, the other is what the spine actually cites.
- **DMULT-S’s double parentage collapses, but not by merger.** Both parents are now off-route: `[H-c]` is NOT-REACHED (HYP.22) and the `[H-a]`/GRTJC side rides the citable (DMULT-w) tier, whose structural clauses stand without (DMULT-s). HYP.20 and HYP.77 remain separate rows; what changed is that neither reaches a count law.
- **HYP.148 and HYP.139 are one chain, two obligations, and must not be merged.** HYP.148 is the *consumption* of the W-9 graded face inside GENHN-4 layer 1 (class CARRY, dischargeable by a fold); HYP.139 is the *W-1 transport* riding under it (class MATH, an ATTEMPT-grade proof obligation). A fold that strikes HYP.148 would retire HYP.139 as a side effect — that is a property of the proposed route, not evidence the rows are the same object.
- **HYP.148 and HYP.81 are distinct at the same threshold.** Both are live from n=6, both key on μ≥3, and both are GENHN suppliers — but `[GENHN-HE(μ≥3)]` is a σ-decision obligation on stage leaves and `GENHN-BOX-2` is a weld-face consumption inside a count law. HE3 explicitly declines GENHN-4, so the σ chain carries HYP.81 without carrying HYP.148.
- **HYP.149 is not a discharge and is not a NODE.** PROPOSED-NODE is a distinct bucket precisely so that an audit-synthesized route cannot be mistaken for sanctioned bounded work. It is counted as a row so it is not lost, and excluded from the NODE tally so it cannot be read as scheduled.
- **`WELD-M-PKG` (HYP.59) needs no widening.** The audit checked it independently: consumed on the spine as naming only (GENIND L1523 “named in S7.1’s (CS-1..3) pricing only”; GENH4 L938–941), and T1 C7 confirms from the other side that T1 “proves no cross-face coherence theorem”. The existing narrow-interface disposition is correct as written.

v5 additions to this section:

- **`genuineDensity` and `decidedDensity` are two objects, not one renamed twice.** The P4 rewire is easy to misread as a pure relabelling. It is not: `genuineDensity` (post-P4) is the **outer** limit — `⨅N possibleSeq`, the proportion of coefficient classes still *consistent* with σ — while `decidedDensity` is the **inner** limit, the proportion of classes on which the type is *forced*. Inner ≤ outer always; they coincide exactly under drainage. Any text that treats them as interchangeable without invoking `genuineDensity_eq_of_drainage` (or n ≤ 2) is wrong, and any pre-2026-08-14 document that says `genuineDensity` means the object now called `decidedDensity`.
- **`TotalMassOne` is not a strengthening of the capstone — it is the drainage leg wearing a different hat.** Σ_σ = 1 at general n is *equivalent in strength* to drainage, which Display A already assumes as `A2_n`. Stating it as a separate Prop rather than a conjunct of `UniformityStatement` is what keeps the ledger from counting one obligation twice. It is not evidence of extra progress that both appear.
- **Closing a question is not discharging a row, and this fold keeps the two apart.** Of the eight questions answered at v5, exactly four *closed* rows (HYP.16, 39, 94, 95) and two *relocated* rows (HYP.96, 97); the rest changed a review surface, a label, or a display. HYP.15 in particular is answered and still CARRY. A reader auditing progress should read the disposition column, not the question count.
- **`OUT-OF-PATH-BY-POLICY` is not CLOSED and must not be summed with it.** A closed row is discharged; an out-of-path row is *still open where it lives* (the quarry) and merely stops conditioning the capstone. They are tallied separately for exactly this reason.
- **`IN-PROGRESS` supersedes `PROPOSED-NODE` for HYP.149 only, and licenses nothing.** The v4 note above — “PROPOSED-NODE is a distinct bucket precisely so that an audit-synthesized route cannot be mistaken for sanctioned bounded work” — still governs. IN-PROGRESS records that the WELD-ZERO unit is *running*, not that it has produced anything: HYP.148 (CARRY) and HYP.139 (MATH) stand at full strength, and the preview is unchanged by the launch.

## Coverage statement

The v2 sweep incorporates the full cross-read and quoted loci. The W12 locator is corrected to `W12_PROOF_2026-08-08.md`; T1 rows cite §1.1/§5 rather than a nonexistent “effective hypothesis list”; GENIND rows cite §S1/§S7.1/§S8/§C2-G1; census labels are hyphenated. Coverage includes all T-unit acceptance records, W12/GENIND, low-degree Lean notes, citation-scope resolution, tightness census, Project State through the ledger append, GENTOW5_WI, and all eight qgen audits’ INTERFACE rows.

v3 extends coverage to the completeness sub-sweep’s sources: HEX3/HE3/W11/GENHN/GENTOW2/GENTOW4/GENTOW5_WI/HE6R1 proof notes at HEAD, census rows I-4 and O-10, N3_CHECK §6d, N2_EXACT §7 grade disclosure, CITE_SCOPE §6, the Phase-0a shards `spec/EFF-T3.md` and `spec/EFF-T1-s1of3.md`, the SOL certification ledger, and the S-0 instrument with its post-campaign green run. The 2026-08-12 SOL certification ledger is HEAD-of-record for unit grades and supersedes both in-note grade boxes and the 2026-08-11 census where they disagree.

v4 extends coverage to `runs/qgen/WELD_FACE_AUDIT.md` and, through it, to the twenty cone notes it swept: W-12.D ∘ GENIND.B ∘ GENH4 ∘ GENHN ∘ HEX3 ∘ HE6 ∘ HE7 ∘ HE3 ∘ HE6R1 ∘ HETOW ∘ GENTOW1–6 plus W11/W12/HMENU3. New sources read at HEAD for this fold’s verification: `GRTW2_PROOF` §5.3, `GRTJC_PROOF` JC-BOX-3/JC-F1, `JD0_PROOF` §4/BOX-1, `GENTOW3_PROOF` S7, `GENTOW6_PROOF` S5 boxes and its BOX-1 f1=1 closure, `GENTOW5_PROOF` S1.1/S11 and its acceptance append, `SG2_PROBE_2026-08-10.md`, and the seven dependency-ledger J-D0 sites. The 2026-08-12 SOL certification ledger remains HEAD-of-record for unit grades and was applied against the audit’s own stale GENTOW5 grade caveat.

v5 extends coverage to the 0d closure record — `docs/PROJECT_STATE.md` appends **#47** (L4541–4565), **#48** (L4566–4592), **#49** (L4593–4619) — and, for the P4 rename, to the post-rewire Lean tree read directly at HEAD: `leanfinal/Uniformity/Density/GenuineDensity.lean` (the two density definitions and the drainage tie), `Statement.lean` (both capstone targets, the signed signature docstring, `TotalMassOne` and its conditionality paragraph), and `Gates.lean` (`drainage_one`, the n=1 total-mass instance). For the ORPHAN-1 verification it extends coverage to a fresh sweep of the twenty cone notes plus `JD0_PROOF_2026-08-08.md` §S1/§S4/§S6/§S10, `GRTJC_PROOF_2026-08-08.md` §5 (COROLLARY W-9) and JC-BOX-6, `GENHN_PROOF_2026-08-08.md` §S6.1 and its dependency ledger, and negative sweeps of `T1`–`T5`, `docs/HUMAN_PROOF.md`, and both Lean trees.

v7 extends coverage to: T2's dated consumption record (commit `66062771`) and, through it, `spec/EFF-HE6.md` in full (its pin table, both OPEN-CALLs, and the compilation-summary self-audit); `docs/PROJECT_STATE.md` appends **#53** (L4716–4740), **#54** (L4742–4760), **#55** (L4761–4776), **#56** (L4778–4799); the six 0a-sweep source files named at MQ-7–12 (`spec/EFF-GENTOW6.md`, `EFF-HETOW.md`, `EFF-GRTJB.md`, `EFF-GRTW2.md`, `EFF-HE7-s2of3.md`, `EFF-LIFTCORNER.md`) cross-checked against their underlying informal proof notes for post-sweep corrections; `blueprint/CHAP-G_base_cases_menus.md` (the HONESTY BLOCK and the structural DAG-edge table) and the Lean tree it blueprints, `leanfinal/Uniformity/ChapG/{G36,G37,G76}.lean`, read directly at HEAD; and `lean/notes/openmath/WELDZERO_2026-08-14.md`'s status line, re-checked against the tree for a landing commit that does not (yet) exist.

Deliberate exclusions: `htameFE`; closed quadratic STATUS items; stronger quadratic rate/sharpness questions; X-LEMMA; stronger out-of-cone W10-GEN; TAIL-CERT as a separate row because indexed under HYP.29; rider debt/pure coverage disclosures without a consumer; nonexistent GENTOW6-BOX-5; and retired MP1′. The 2026-08-11 census headline is chronologically superseded for ledger purposes by the 2026-08-12 CS-1Q correction and 2026-08-13 Lean notes.

## Capstone-conditionality preview

> ## ⚠ THE PREVIEW CHANGED IN v4 — READ THIS BEFORE THE DISPLAYS
>
> v1→v3 never moved a conjunct. **v4 does.** If you are mid-way through the 0d
> review, the object you were reviewing is not the object below. Source:
> `runs/qgen/WELD_FACE_AUDIT.md` §5c, on the §2 per-row verdicts.
>
> **BEFORE (v3, Display A lines 8–11 of the hypothesis block):**
>
> ```
>   ∧ JB-NOLEG(rows 4,5,12,22)†
>   ∧ [H-c]† = JD1ValuePackage[
>        VD-m, C-coll, R-coll, PERIM-μ,
>        DMULT-S†, JD0-BOX-2†, W2-VALUE†]
> ```
>
> **AFTER (v4):**
>
> ```
>   ∧ JD0-BOX-2†            -- unit-character gauge-form perimeter, inherited FRAME-grade
>   ∧ (GENHN-BOX-2 if n≥6)  -- the W-9 graded face in GENHN-4 layer 1 at μ≥3;
>                           --   carries HYP.139 (W-1 transport, ATTEMPT)
> ```
>
> **What moved, and why.**
>
> | Conjunct | v4 | Reason (audit §2, quotes on the rows) |
> |---|---|---|
> | `JB-NOLEG(rows 4,5,12,22)†` | **OUT** | NOT-REACHED. No capstone-path consumer; W11 L391–393 “JB row-12 u ≥ 0 proviso … not consumed”. Rows: HYP.75, HYP.21. |
> | `[H-c]†` (the whole package) | **OUT** | NOT-REACHED. Its only consumption site is `[W12-H]`, **the route W-12 priced but did not take**; the real n≥4 suppliers are GENH4.C/GENHN.C, which declare no weld face inside a count law. Row: HYP.22. |
> | ├ `VD-m, C-coll, R-coll, PERIM-μ` | **OUT** (with parent) | Zero cone consumers; W12 L218–220 displays them as ABSENT. Rows HYP.83–86, flagged ORPHAN-1. |
> | ├ `DMULT-S†` | **OUT** | NOT-REACHED. W-9 rides the citable **(DMULT-w)** tier instead; that cite is PDF-VERIFIED. Row: HYP.77. |
> | ├ `W2-VALUE†` | **OUT** | NOT-REACHED. GRTW2 reaches the spine only through display bookkeeping. Row: HYP.76. |
> | └ `JD0-BOX-2†` | **SURVIVES, promoted** | The **only** reachable member of the deleted block — two spine notes declare its perimeter inherited *in their own words*. It leaves the package and stands as its own conjunct. Row: HYP.74. |
> | `(GENHN-BOX-2 if n≥6)` | **IN (new)** | The **one weld face inside a count law** on the whole path — GENHN’s own phrase (L1512–1513). It was invisible in v3, present only obliquely through HYP.139. Row: HYP.148. |
>
> **The carry was exactly inverted.** v3 carried the unreachable value package and
> omitted the single face the proof actually stands on. That is the audit's
> headline finding, and it is the reason this fold touches the display at all.
>
> **Owner-decision surface shrinks from six daggers to two.** Leaving:
> `JB-NOLEG†`, `[H-c]†`, `DMULT-S†`, `W2-VALUE†`. Remaining: `NS7(O)†`
> (question 1) and `JD0-BOX-2†`. `GENHN-BOX-2` enters **undaggered** — it is a
> proof unit with a named fold route (HYP.149), not an owner call. Every other
> dagger and fence in both displays is untouched.
>
> **Also re-sourced, without moving:** the `(H-e)-window-pinning` conjunct stays
> exactly where it is, but its supplier changes from W12's “(H-a)/(H-b)-leg” —
> now known off-route — to `LEMMA GENHN-3` plus GENIND-2's consulted-height
> bound. See HYP.24. `AllOInterfaces[… J-D0 …]` is unchanged and correct.
>
> **Not a reduction in honest conditionality.** Four conjuncts left because they
> were never load-bearing, not because anything was proved. One entered because
> it was load-bearing and undisclosed. The net effect on what the capstone
> actually rests on is a *correction*, not a *weakening*.

> ## ✔ v5 — DISPLAY A IS FROZEN, AND NO DAGGERS REMAIN
>
> **Question 8 ANSWERED [append #49]: DISPLAY A is FROZEN** (*“readability; fewer error
> surfaces”*). **Display B is HISTORICAL** as of v5 — retained below for the supplier map it
> records, marked as not the frozen object, and it may not be cited as the capstone’s public
> interface. The old fence “Displays A and B are alternatives and must never be conjoined”
> still holds and is now moot in one direction: there is only one live display.
>
> **The dagger count reaches zero.** v4 cut the owner-decision surface from six daggers to
> two (`NS7(O)†`, `JD0-BOX-2†`). v5 removes both — not by proving anything, but because the
> 0d answers landed: `NS7(O)` is **decided as a cite** ([AGNPRW] Thm 5.2, question 1, HYP.15)
> and `JD0-BOX-2`’s grade bar is **signed** (question 6, HYP.39). Both conjuncts **remain in
> the display at full strength**; what left is the owner call attached to them. A conjunct
> without a dagger is not a discharged conjunct — it is an undischarged one whose disposition
> is no longer waiting on a person.

A dagger marks an owner decision, not every proof unit — **as of v5 there are none left; the
symbol is retained only in the v4 BEFORE/AFTER block above, as history.** Parent aggregates
appear once. Display A is the frozen public interface (question 8); Display B is historical.
The n=2 W-12.D case is unconditional; n=3 is conditional only on the cubic HMENU3/HEX3 proof
perimeter (*and, disclosed inside that perimeter without being a conjunct of it:*
`HEX3-BOX-1`, *the unproved tail-σ-certification lemma — HYP.137, question 9; it conditions
the S8.2 W-12.B corroboration aside only, never `hExhaust3` or drainage*).

### Display A — public interface — **FROZEN [v5, question 8]**

For n≥4 and every complete DVR O with residue field size q, assume uniformly in O:

[
  NS7(O)                  -- decided as a CITE: [AGNPRW] Thm 5.2 (Q1, HYP.15);
                          --   undaggered at v5, still a carried hypothesis
  ∧ LB1 ∧ MP1
  ∧ HE7A[ACCOUNT, RES-DEG, nonempty, exhaust, root-continuation]
  ∧ ∀ i≥3, ((H-VARTHETA-RES)_i ∧ 𝒲_(≤i))
  ∧ A0_n[disc≠0] ∧ A1_n ∧ A2_n
  ∧ JD0-BOX-2             -- unit-character gauge-form perimeter, inherited FRAME-grade;
                          --   undaggered at v5: machine grade SIGNED as the bar (Q6, HYP.39)
  ∧ (GENHN-BOX-2 if n≥6)  -- the W-9 graded face in GENHN-4 layer 1 at μ≥3;
                          --   carries HYP.139 (W-1 transport, ATTEMPT).
                          --   WELD-ZERO unit launched to retire both (HYP.149, IN-PROGRESS)
  ∧ (H-e)-window-pinning
  ∧ ([GENHN-HE(μ≥3)] if n≥6)
  ∧ ([GENHN-TOW-1] if n≥8)
  ∧ AllOInterfaces[
       GENIND-1, RMG, ILN, GRB, ITER-LAW, W/J, DU, W-10,
       J-D0, L2core, HUMAN_PROOF, local-integrals, CONV, GENHN-count]
]
  ⇒ ∀ σ with deg σ=n,
       ∃ num, den ∈ ℤ[q], independent of O,
         genuineDensity_O(σ) = decidedDensity_O(σ) = num(q)/den(q).

**[RENAMED per P4 — read this before reading the conclusion line.]** The pre-rewire text of
this conclusion said `genuineDensity_O(σ)`, and under the pre-rewire naming that meant **the
certified/decided route**, which is now called `decidedDensity`. Both names now appear, and
they are not a hedge — they are two statements the display genuinely delivers:

* `genuineDensity` (post-P4) is **THE** density: `⨅N possibleSeq`, the limit of the proportion
  of coefficient classes consistent with σ (`GenuineDensity.lean:266`). This is what question 5
  chose as the definition.
* `decidedDensity` (post-P4, = the old `genuineDensity`) is the certified/inner route
  (`GenuineDensity.lean:245`) — the object the informal count laws (W-12.D, GENIND) actually
  produce.
* The two are tied by `genuineDensity_eq_of_drainage` (`GenuineDensity.lean:348`), whose
  hypothesis is drainage — **already assumed in this display as the `A2_n` conjunct**. So the
  display carries both readings without a new assumption. Unconditionally at n=1 and n=2
  (`drainage_one`, `drainage_two`) the tie needs nothing at all.

**Σ_σ = 1: NOT a clause of the frozen statement [question 5 ANSWERED].** It is the separate
named Prop **`TotalMassOne`** (`Statement.lean:166`), supplied by
`sum_genuineDensity_eq_one_of_drainage` via `totalMassOne_of_drainage` (`:174`). Its exact
conditionality, in the Lean file’s own words at `:163`: *“`TotalMassOne` is **the general-`n`
drainage leg in disguise**: drainage implies it outright, and the frontier that blocks it is
exactly the open one (order ≥ 2 of the Okutsu–Montes tower).”* Proved: `≥ 1` unconditionally
for any covering menu at every n; equality unconditionally at n=1 and n=2; equality at general
n given drainage. Keeping it out of `UniformityStatement` is what stops the capstone from
quietly absorbing the drainage leg twice.

**Haar: NOT asserted [question 5 ANSWERED].** The frozen capstone claims a proportion limit and
nothing measure-theoretic; the Haar identification is off the path (HYP.95, CLOSED). The
informal W-12.D text still draws a Haar conclusion — that conclusion is **not** underwritten by
this display.

### Display B — expanded suppliers — **HISTORICAL [v5, question 8]**

> Display B is **not** the frozen public interface. Question 8 froze Display A; Display B is
> retained because its expanded CS-* supplier list is the map from the public interface down to
> the GENIND obligations, and deleting it would lose that map. It may be read as documentation
> and must not be cited as the capstone’s statement.

Display B is identical except that

    A0_n[disc≠0] ∧ A1_n ∧ A2_n

is replaced, never supplemented, by

    ∀ G ∈ Genres(n),
      CS1_G ∧ CS2_G ∧ CS3_G[disc≠0, window-pinning]
      ∧ CSExact_G ∧ CS1Q_G.

CSExact means an exact finite q-power-sum menu and an exact stage drain, not asymptotic bounds; CS1 serves both menu and drainage. In both displays O,q are bound on the hypothesis side, A0–A2 are fixed-n, and σ is quantified only in the conclusion. The window law, GENHN thresholds, pinning half, HE7.A suite, and all-O supplier interfaces are visible. **v4:** the four JB rows and the four restored value hypotheses are **no longer visible in either display**, because the audit signed them NOT-REACHED — they are recorded OUT of the cone at HYP.21/75 and HYP.83–86 rather than displayed as conditions the theorem rests on; the weld layer's one genuine contribution, `GENHN-BOX-2`, is displayed in their place. MATH rows remain proof blockers; where a public aggregate is carried, they are not falsely declared absent from its supplier DAG.

## THE 0d PACKAGE — nine owner questions, **ALL NINE ANSWERED**

> # ✅ 0d CLOSED — 2026-08-14
>
> **All nine owner questions are answered. The needs-Asvin count is 0.** The 0d package
> opened at v1 as the list of decisions only the owner could make; it closes here. Every
> question below is stamped **in place** with its answer and the append that carries it —
> nothing is deleted, so the package still reads as one list and every answer is traceable to
> a dated record in `docs/PROJECT_STATE.md`.
>
> | Q | Subject | Answer | Append | Rows moved |
> |---|---|---|---|---|
> | **1** | Trusted base, `NS-7` termination | **CITE** [AGNPRW] Thm 5.2 (*“for now at least”*); internal F-2 not taken | **#47** L4541 | HYP.15 → CARRY-as-CITE (undaggered) · HYP.16 → CLOSED (½·v(disc f) route **lapses**, COR-13) · HYP.17 **elevated** (the cite is by number) · MQ-3 lapses as a Q1 rider |
> | **2** | Scheduling + charter width of the weld-face audit | **RUN, widened-by-default** — executed 2026-08-13 | #46/v4 | HYP.73 CLOSED · 5 rows CARRY→NODE at v4 · **ORPHAN-1 cured at v5** (HYP.83–86) |
> | **3** | Capstone signature, three live points | **SIGNED** | **#47** L4541 | HYP.94 → CLOSED-SIGNED |
> | **4** | Definitions / human-review surface | **THE REVIEW-BOUNDARY POLICY**: human-checked = the main statement and definitions only | **#47** L4541 | Header policy note added · HYP.01/12/17/98 stamped `[CORE-SET]` · HYP.111 **splits** (definitional half core, deep-tail half lifted) |
> | **5** | What the theorem claims (Haar? Σ=1?) | **EXECUTED, not merely decided** — `genuineDensity` redefined as the proportion limit; **no Haar**; Σ=1 is a separate Prop | **#47** L4541 + **#48** L4566 | HYP.95 → CLOSED (no Haar) · P4 rename swept file-wide · Σ=1 rows re-keyed to `TotalMassOne` |
> | **6** | JD0 grade bar | **MACHINE GRADE SIGNED** (68,523/0); codex pass optional | **#49** L4593 | HYP.39 → CLOSED-SIGNED · **MQ-4** added so the optional pass is not swallowed |
> | **7** | Axioms on the Lean path | **`leanfinal` is LEAN-CORE-ONLY**; AX-CELLREC/AX-LEAF quarantined in the quarry’s measure route | **#49** L4593 | HYP.96, HYP.97 → OUT-OF-PATH-BY-POLICY |
> | **8** | Display shape | **DISPLAY A FROZEN**; Display B historical | **#49** L4593 | Preview headnote + both display headings |
> | **9** | `HEX3-BOX-1` carry-vs-node | *“doesn’t matter too much”* → **named parenthetically** in the n=3 perimeter clause | **#49** L4593 | HYP.137 stays MATH; preview edit executed; premise correction recorded |
>
> **What closing 0d does NOT mean.** Not one line of mathematics was proved by these answers.
> Five of the nine were decisions about *what to claim and what to check* (1, 4, 5, 7, 8), two
> were *grade bars* (3, 6), one was *scheduling* (2), and one was *presentation* (9). The
> capstone’s conditionality after 0d is the same conditionality as before it, more accurately
> displayed and no longer waiting on a person. The daggers are gone from Display A because the
> owner calls are made — **the conjuncts they marked are all still there.**
>
> **Two consequences worth carrying forward, neither an open question.** (i) Citing [AGNPRW]
> Thm 5.2 *by number* makes HYP.17’s publisher-number check load-bearing where it used to be
> bibliographic hygiene. (ii) Question 7 moved the axiom rows off the capstone path without
> completing their DRAFT faithfulness entries — those still gate the quarry.

All nine are carried **verbatim** from v3 (the heading’s v3 count of “eight” was stale — question 9 was appended without it). Question 2 was ANSWERED at v4; **the remaining eight are ANSWERED at v5** and are likewise stamped in place rather than deleted.

1. **Trusted base (HYP.15, `NS-7`).** Do we cite [AGNPRW] Thm 5.2 for OM termination over every complete DVR — accepting that its index step is itself discharged by citation to ℚ_p-scope sources, recorded honestly in `AXIOM_FAITHFULNESS.md` — or spend F-2's 2–4 pages proving index-descent internally on the `L4` lattice machinery? *(The source recommends citing. Coupling: the cite branch forfeits the `≤ ½ v(disc f)` depth bound that HYP.16 assumes — COR-13.)*
   → **ANSWERED [v5, append #47]: CITE.** Owner, verbatim: *“cite thm 5.2 for now at least.”* [AGNPRW] Thm 5.2 is the termination resolution for the informal corpus; F-2’s internal index-descent is not spent. The coupling fires as COR-13 predicted: **HYP.16’s ½·v(disc f) depth bound LAPSES** (CLOSED), which costs nothing because the capstone needs finiteness, not a constant. In Lean, `NS7` **stays a carried hypothesis** *“until proved or declared-with-faithfulness”* — so HYP.15 remains CARRY, re-labelled CARRY-as-CITE and undaggered. Two riders: HYP.17’s AGNPRW numbering is now load-bearing, and MQ-3 (the unperformed [GMN12] §4 audit) lapses as a question-1 rider because it qualified only the branch not taken.
2. **Scheduling + scope (collapses 10 open calls).** Run the `WELD-FACE-AUDIT` (census S-4, one session) before the 0d freeze, so the weld residues are carried only if reachable — and if so, do we widen its charter from the four rows the census assigns it (HYP.74–77) to also cover HYP.21, 22, 67, 68, 69, 71 (COR-41)?
   → **ANSWERED [v4]: audit run, charter width widened-by-default.** The orchestrator took the widening as the default and the audit executed at the full ten rows before the 0d freeze (`runs/qgen/WELD_FACE_AUDIT.md`, 2026-08-13; HYP.73 CLOSED). **The reachability half is resolved by the outcome, not by a decision:** 1 REACHABLE-AND-CONSUMED / 0 CORROBORATIVE-ONLY / 9 NOT-REACHED, so the weld residues are now carried only where reachable and the preview was corrected accordingly. Nothing here awaits the owner; the question is retained verbatim for the record. Residual owner-visible consequence, *not* a re-opening of this question: rows HYP.83–86 are left CARRY though their parent conjunct has gone (ORPHAN-1), which is a v5 bookkeeping item. → **ORPHAN-1 CURED at v5**, and cured by independent re-verification rather than by inheriting the parent’s verdict: all four move CARRY→NODE (COR-ORPH-01…04; the verification block sits at HYP.83).
3. **Capstone signature (MISS-04).** Sign off `UniformityStatement`'s three live points: `∀ 𝒪` over `Type` (universe 0); the rational function evaluated at `(q : ℚ)` with equality read in `ℝ` by coercion; `den.eval q ≠ 0` demanded per-`𝒪` rather than globally. *(The note's fourth point, `σ.degree = n` doing no work, is self-superseded — `typeOf_degree` landed as gate G13.)*
   → **ANSWERED [v5, append #47]: SIGNED.** All three points stand and survive the P4 rewire **verbatim** (append #48). Re-verified in the tree at `leanfinal/Uniformity/Density/Statement.lean:55–58`, which also settles the fourth point in the stronger direction: *“(iv) The hypothesis `σ.degree = n` **does real work** (`typeOf_degree`): off-degree `σ` are forced to density `0`.”* HYP.94 → CLOSED-SIGNED.
4. **Definitions (HYP.12, MISS-13, MISS-04).** The `(e,f)` ordering/multiset convention *"deserves a human read"*; `W12-BOX-7`'s σ-convention at the TRP tail (two conventions can disagree on deep-tail members); and `HENSEL_FACT` §4's faithfulness paragraphs, headed *"FLAGGED FOR ASVIN'S REVIEW"*.
   → **ANSWERED [v5, append #47]: THE REVIEW-BOUNDARY POLICY**, which supersedes the per-node SPEC-SIGNED design. Human-checked = **the main statement and definitions only** — the types, the uniformity theorem, `genuineDensity`/`decidedDensity`, the cites (plus, per #48, the changed definitions’ faithfulness paragraphs). Everything else is *“a consumer or discharger of these”* and is *“forced right if the entire project works out”*; *“the Hensel statements take care of themselves.”* **Applied to the three items in the question:** the `(e,f)` convention is CORE (it is the type) and stays a human read, folded into HYP.98; `W12-BOX-7`’s TRP-tail convention SPLITS — its definitional half is core, its deep-tail reconciliation half is lifted; `HENSEL_FACT` §4’s faithfulness paragraphs are **lifted** by the policy’s own last clause. The full policy text is in the file header. **This answer changes the review surface, not any row’s mathematical status.**
5. **What the theorem claims (MISS-05, DEF-07).** Does the frozen capstone assert the **Haar density** — as W-12.D and the census do — or only the limit of decided proportions, which is what Lean's `genuineDensity` is and which `GENUINE_DENSITY` §3B.4 records the bridge to as unformalized? And is `Σ_σ R_σ = 1` inside the frozen statement?
   → **ANSWERED AND EXECUTED [v5, appends #47 + #48]** — this is the only 0d answer that changed the Lean tree rather than a disposition. **Neither horn of the question as posed:** the owner *redefined the object*. `genuineDensity` is now the limit of the proportion of σ-consistent classes (the outer limit) — **THE** density — and the old `genuineDensity` (the certified route) is renamed `decidedDensity`; the two are tied by `genuineDensity_eq_of_drainage`, unconditional at n=1 and n=2. **Haar: NOT asserted** — the proportion limit IS the definition, so the bridge is off the path (HYP.95 CLOSED; MISS-05/DEF-07’s Haar question closed with it). **Σ_σ R_σ = 1: NOT inside the frozen statement** — it is the separate named Prop `TotalMassOne`, proved `≥ 1` unconditionally, `= 1` given drainage, unconditional at n=1,2. Honesty note carried from #47: Σ=1 at general n *is* the drainage leg, already conjunct A2 — so keeping it outside `UniformityStatement` prevents assuming it twice. The rename is swept through this file and stamped **[RENAMED per P4]** at each site.
6. **Grade (COR-08).** `JD0-BAR`: run JD0's 2-clean hostile arc, or sign off the 68,523/0 machine grade as the bar? *(The census offers both; the ledger silently chose the first.)*
   → **ANSWERED [v5, append #49]: MACHINE GRADE SIGNED as the bar.** Owner’s reasoning: J-D0’s gauge-blindness *“MUST be true for the proof strategy/uniformity to work at all”*, and conviction of truth implies any proof defect would be fixable. HYP.39 → CLOSED-SIGNED; the cap lifts off J-D0’s seven direct cone sites (HYP.74). The optional post-reset codex pass stays queued as belt-and-braces — **MQ-4**, so closing the row does not swallow it.
7. **Axioms (MISS-06).** `AX-CELLREC`/`AX-LEAF` faithfulness entries are **DRAFT, PENDING ASVIN REVIEW** and the census says they *"gate the LEAN capstone claim"*. Are they on the `leanfinal` path at all, or is `leanfinal` Lean-core-only? Same question for census **L-4**, the `RealInstanceAt.faithful` placeholder.
   → **ANSWERED [v5, append #49]: `leanfinal` is LEAN-CORE-ONLY.** The axioms *“stay QUARANTINED in the quarry’s measure route (no file move needed — `leanfinal` never imports them; policy now explicit)”*. So the census’s worry is answered in the negative: they gate the quarry, not the capstone. HYP.96 and HYP.97 → **OUT-OF-PATH-BY-POLICY**. **Not closed, relocated:** the faithfulness entries are still DRAFT and still gate any quarry measure-route claim; `lake env lean LeanUrat/AxChk_baseline.lean` remains the enforcing instrument.
8. **Display shape (DEF-01).** Freeze **Display A** (public interface A0–A2) or **Display B** (expanded CS-* supplier list) — not both.
   → **ANSWERED [v5, append #49]: DISPLAY A FROZEN** (*“readability; fewer error surfaces”*). Display B is marked **HISTORICAL** — retained for its supplier map, not citable as the capstone’s interface. Both headings are stamped in the preview section.
9. **[v3] `HEX3-BOX-1` carry-vs-node (HYP.137).** The tail-σ-certification lemma is unproved and `hExhaust3` provably never needed it (HEX3 L692–693), yet GENIND's r3 pin conditionalizes the S8.2 W-12.B consistency clause on it and HEX3 displays the price as "W-12.B would be FALSE at n = 3" — so do we CARRY it as a named n=3 conjunct in the preview, or keep it a NODE-grade refinement indexed under HYP.29 on the strength of the census's OUT-OF-CONE reading?
   → **ANSWERED [v5, append #49]: neither extreme — NAMED PARENTHETICALLY.** Owner: *“doesn’t matter too much”*, disposed per the standing recommendation. The edit is executed: `HEX3-BOX-1` now appears inside the preview’s n=3 perimeter clause, disclosed but **not** promoted to a Display A conjunct. HYP.137 stays MATH. **Premise correction relayed with the answer and recorded at the row:** the n≤3 menus and drainage **do** enter the final proof as the induction’s base cases (GENIND consumes HMENU3/HEX3 as base data); it is `HEX3-BOX-1` *specifically* that stays out of the load-bearing chain, consumed only by the W-12.B corroboration cross-check.

## CHANGES-FROM-v1

- HYP.01 corrected: restored the disc≠0 faithfulness locus (MISS-04/06 context).
- HYP.02 corrected: exact-solve injectivity, not congruence uniqueness (COR-11).
- HYP.10 re-dispositioned MATH→NODE, LOW-CONFIDENCE (COR-10).
- HYP.11 re-dispositioned NODE→MATH and restored prerequisites (COR-09).
- HYP.12 corrected into the owner definitions package (row verification/owner Q4).
- HYP.14 corrected stop/continue polarity (COR-12).
- HYP.16 corrected coupling to HYP.15’s F-2 branch (COR-13).
- HYP.18 corrected with separability fence (COR-14).
- HYP.19 corrected: W12 filename and n≥4 composite-stage scope (COR-01/COR-03).
- HYP.20 corrected: W12 filename and child-conditionality fence (COR-01/D-06).
- HYP.21 corrected: W12 filename and refusal of the JB-NOLEG merge (COR-01/D-05).
- HYP.22 corrected: W12 filename and restored value-layer children (COR-01/MISS-02).
- HYP.23 corrected: W12 filename and [H-a]–[H-c] conditioning (COR-01/COR-07).
- HYP.24 corrected/re-dispositioned NODE→CARRY: window-pinning half and fences restored (COR-01/COR-04/COR-30).
- HYP.25 corrected: window-decided core family and disc≠0 fence restored (COR-01/COR-05).
- HYP.26 corrected: σ removed from A1’s binder and simultaneous all-q scope restored (COR-01/COR-06).
- HYP.27 corrected: W12 filename and exact remainder scope restored (COR-01).
- HYP.28 corrected: W12 filename and deeper-tier perimeter exposed (COR-01/COR-09).
- HYP.29 corrected: W12 filename and tail aliases/correction indexed (COR-01/D-08).
- HYP.30 corrected: W12 filename, I-1 label, and GENIND-BOX-4 nonmerge (COR-01/COR-02/D-02).
- HYP.31 corrected: real GENIND loci, n≤3 vacuity, and n≥6/8 conjuncts (COR-28/COR-31/MISS-01).
- HYP.32 corrected: real locus and dual menu/drainage consumer (COR-28/D-03).
- HYP.33 corrected: real GENIND locus (COR-28).
- HYP.34 corrected/merged: separability, disc≠0, and pinning restored; represented by HYP.24 (COR-04/COR-28/COR-30/D-04).
- HYP.35 corrected: exact menu and exact drain, not bounded/asymptotic (COR-27/COR-28).
- HYP.36 corrected: both CS-1Q clauses restored without overstated conclusion (COR-28/COR-29).
- HYP.37 corrected: real §S8 locator (COR-28).
- HYP.38 corrected: census label I-3 (COR-02).
- HYP.39 corrected: PROVED/machine grade, process sub-bar, and owner option (COR-02/COR-08).
- HYP.40 corrected: real name, certified grade, scope residue, and deep consumers (COR-02/COR-15/COR-34).
- HYP.41 corrected full LB1 trigger/consequent/consumers (COR-18).
- HYP.42 corrected own locator and MP1 items 2–5/consumers (COR-19).
- HYP.43 corrected/reclassified as SEC-RANK carrier hypothesis with termination consumer (COR-16).
- HYP.44 corrected/reclassified as RISE carrier hypothesis with HT consumer (COR-17).
- HYP.45 corrected simultaneous 0/2 and 1/2 grades plus level-two consumer (COR-20).
- HYP.46 corrected: removed deleted arbitrary-depth terminating reduction (COR-21/COR-26).
- HYP.47 corrected: real T1 locus and ladder formula (COR-21/COR-26).
- HYP.48 corrected: real T1 locus and slot-grade identity (COR-21/COR-26).
- HYP.49 corrected: consumed-ladder/value-zero restrictions restored (COR-21/COR-26).
- HYP.50 corrected: zero-component formula and fence restored (COR-21/COR-26).
- HYP.51 corrected: independent nonvanishing and i=2/i≥3 supplier split (COR-21/COR-26).
- HYP.52 corrected: scalar K_i codomain and false general discharge removed (COR-21/COR-22).
- HYP.53 corrected: real locus and nonexistent accepted supplier removed (COR-21/COR-23).
- HYP.54 corrected: exact polynomial/support/degree formulas restored (COR-21/COR-26).
- HYP.55 corrected: hypothesis, clearance bound, and carry clause restored (COR-21/COR-26).
- HYP.56 corrected: complete HETOW data/formulas restored (COR-21/COR-26).
- HYP.57 corrected/re-dispositioned: vartheta membership, loci/consumers, and technical CARRY unit (COR-24/open-call adjudication).
- HYP.58 corrected: real T1 locus and strict domain retained (COR-21/COR-26).
- HYP.59 corrected: real T1 locus and forbidden strengthenings enumerated (COR-21/COR-26).
- HYP.60 corrected: real T1 locus and exact iff criterion retained (COR-21/COR-26).
- HYP.61 corrected: zero argument and “gates no C1–C7” consumer status (COR-21/COR-26).
- HYP.62 corrected/split from HYP.135 and moved to T3 §8.5 (COR-25/COR-40/D-11).
- HYP.63 re-dispositioned NODE→CARRY under governing T5 text (COR-32/33).
- HYP.65 corrected notation/disjunction/i=1 consumer (COR-38).
- HYP.66 corrected: equality fails; exact gap is open (COR-37).
- HYP.67 corrected: real T4/upstream locus and no false HYP.73 dependency (COR-35/COR-41).
- HYP.68 corrected: full-side openness and proved-budget/open-ledger split (COR-35/COR-40).
- HYP.69 corrected: real locus and no false HYP.73 dependency (COR-35/COR-41).
- HYP.70 corrected/re-dispositioned: sealed ask DISCHARGED; widening residue separated; OPEN-CALL removed (COR-35/COR-36).
- HYP.71 corrected: missing battery-witness conjunct and no false HYP.73 dependency (COR-35/COR-40/COR-41).
- HYP.72 corrected downstream, not T4, fence consumer (COR-39).
- HYP.73 corrected charter to HYP.74–77 (COR-41).
- HYP.74 corrected: S-5 label and owner call collapsed into question 2 (COR-02/open-call adjudication).
- HYP.75 corrected: four JB rows restored and [H-b] merge refused (COR-02/D-05).
- HYP.76 corrected: S-7 label and owner call collapsed into question 2 (COR-02/open-call adjudication).
- HYP.77 corrected: S-8 label, double parentage, and owner-call collapse (COR-02/D-06/open-call adjudication).
- HYP.78 re-dispositioned: MATH retained, OPEN-CALL/HYP.73 dependency removed, route named (open-call adjudication/COR-41).
- HYP.79 re-dispositioned: MATH retained, OPEN-CALL/HYP.73 dependency removed, route named (open-call adjudication/COR-41).
- HYP.80 re-dispositioned: MATH retained, OPEN-CALL/HYP.73 dependency removed, route named (open-call adjudication/COR-41).
- HYP.81 added: GENHN-HE multiplicity≥3 conjunct (MISS-01).
- HYP.82 added: GENHN-TOW-1 n≥8 conjunct (MISS-01).
- HYP.83 added: VD-m value-layer hypothesis (MISS-02).
- HYP.84 added: C-coll value-layer hypothesis (MISS-02).
- HYP.85 added: R-coll value-layer hypothesis (MISS-02).
- HYP.86 added: PERIM-μ value-layer hypothesis (MISS-02).
- HYP.87 added: GENIND-BOX-3 (MISS-03).
- HYP.88 added: GENIND-BOX-4, distinct from W12-BOX-4 (MISS-03).
- HYP.89 added: GENIND-BOX-5 grade cap (MISS-03).
- HYP.90 added: GENIND-BOX-6 conventions (MISS-03).
- HYP.91 added: GENIND-5 obstruction list (MISS-03).
- HYP.92 added/merged: ANNEX-LEMMA GENIND-C2Q under HYP.36 (MISS-03).
- HYP.93 added/merged: GENIND-6 under HYP.31 (MISS-03).
- HYP.94 added: capstone signature sign-off (MISS-04).
- HYP.95 added: Haar bridge (MISS-05/D-14).
- HYP.96 added: census L-3 AX-CELLREC/AX-LEAF row (MISS-06).
- HYP.97 added: census L-4 RealInstanceAt placeholder (MISS-06).
- HYP.98 added: census L-5 DEFINITION-AUDIT (MISS-06).
- HYP.99 added: T3/T5 frame staleness (MISS-07).
- HYP.100 added: contradictory T5 HEAD sentence (MISS-08).
- HYP.101 added: HE7.A source suite (MISS-09).
- HYP.102 added: MID-PEEL items 2–5 (MISS-10).
- HYP.103 added: T2 S4.2 nonclaims (MISS-10).
- HYP.104 added: C3 lift coefficient-space obligation (MISS-11).
- HYP.105 added: tower-correctness splitting-type gate (MISS-11).
- HYP.106 added: nonzero-digit exact-lift contract (MISS-11).
- HYP.107 added: binary-carry restriction (MISS-11).
- HYP.108 added: A6 provenance split (MISS-11).
- HYP.109 added: T-unit evidence caveats (MISS-12).
- HYP.110 added: W12-BOX-5 code/convention seam (MISS-13).
- HYP.111 added: W12-BOX-7 σ-convention (MISS-13).
- HYP.112 added: T4 μ₂≥3 candidate fence (MISS-14).
- HYP.113 added: T4.2(c) full-exposure premise (MISS-14).
- HYP.114 added: T4.2(d) provenance exclusion (MISS-14).
- HYP.115 added: T4 fail-closed pin convention (MISS-14).
- HYP.116 added: GENTOW3-BOX-2 coverage (MISS-14).
- HYP.117 added/merged: G5-COND consumer list under HYP.63 (MISS-15).
- HYP.118 added: T3 delivered-scope narrowing (MISS-15).
- HYP.119 added: Hensel branch-(ii) reconciliation (MISS-16).
- HYP.120 added: seven unread audit slices/INTERFACE class (MISS-17).
- HYP.121 added: GENIND-1 all-O interface (MISS-18).
- HYP.122 added: RMG all-O interface (MISS-18).
- HYP.123 added: ILN all-O interface (MISS-18).
- HYP.124 added: GRB all-O interface (MISS-18).
- HYP.125 added: ITER-LAW all-O interface (MISS-18).
- HYP.126 added: W-1/W-2/J-A/J-B all-O interfaces (MISS-18).
- HYP.127 added: DU lemma all-O interface (MISS-18).
- HYP.128 added: W-10 instance all-O interface (MISS-18).
- HYP.129 added: J-D0 all-O interface (MISS-18).
- HYP.130 added: L2core all-O interface (MISS-18).
- HYP.131 added: HUMAN_PROOF subproof all-O interfaces (MISS-18).
- HYP.132 added: local-integrals all-O interface (MISS-18).
- HYP.133 added: CONV monic/projective bridge (MISS-18).
- HYP.134 added: GENHN count all-O interface (MISS-18).
- HYP.135 added: F4-JOINT separated from realized T3 demand (COR-40/D-11).
- Dedup section corrected: all nine adjudicated defects are reflected, including wrong JB and joint merges, live GENTOW5-W, partial H-e merge, and live RealInstance/Haar rows (DEDUP audit).
- Preview recomputed as alternative public/expanded displays with correct binders, fences, thresholds, windows, restored components, and conclusion choices (DEF-01–07 plus MISS-18).

## CHANGES-FROM-v2 (v3 completeness-delta fold)

Source: `runs/qgen/HYPLEDGER_deltas.md`, fifteen items in three tiers. Every quoted line was re-verified at its cited file and line before transcription; **zero items were rejected for misquotation** — all fifteen quotes are accurate. Two items were folded with their *adjudication* corrected (HYP.137, HYP.140); the quotes in both were sound, the inferences drawn from them were not.

TIER-1 (items 1–7):
- HYP.136 added: S-0 statement-ledger tripwire, **CLOSED** — the sub-sweep reported it stale; the orchestrator then ran it GREEN post-campaign (178/178 byte-stable, 2 allowed additions), recorded at PROJECT_STATE #45a. Folded as a closed row with its green-run reference, not as an open obligation (delta item 1).
- HYP.137 added: HEX3-BOX-1 promoted from index-only to its own MATH row on a named live consumer; HYP.29 corrected to point at it. Delta framing corrected: census O-10 and GENIND's pin are not in contradiction — different consumers (delta item 2).
- HYP.138 added: N3_CHECK §6d reader-convention reconciliation, unresolved and dated after the census (delta item 3).
- HYP.139 added: the W-1 transport, census row I-4's ATTEMPT-grade proof obligation, missed when v2 folded I-1/I-2/I-3/I-5 (delta item 4).
- HYP.140 added: the GENTOW5_WI stale S7 grade box (0/2 at HEAD vs SOL row 18's CERTIFIED 2/2). Delta conclusion corrected: HYP.40 and HYP.63 are NOT contradicted; the NODE-disposition half was already absorbed by v2's COR-32/33 (delta item 5).
- HYP.141 added, HYP.54/HYP.55/HYP.105 corrected: Phase-0a shard source-designation refutations, including the re-verified grep-zero for `(H-GENHN-CLEAR)`'s cited site. EFF-T1 OPEN-CALLs 1/4/5 were already absorbed by HYP.53/105/52+57 and were not re-folded (delta item 7).
- MQ-1 queued: the n=2 unit's missing adversarial pass (delta item 6).

TIER-2 (items 8–15):
- HYP.142 added: GENHN-ERR-1's two un-reconciled dispositions at HEAD (delta item 8).
- HYP.143 added, HYP.81 corrected with its scope split: HE3-BOX-6's ramified branch (ii), unconditional at μ≤3, conditional at μ≥4 / n≥8 (delta item 9).
- HYP.144 added: GENTOW4-BOX-1/-2/-4, with BOX-2's open COUNT layer as the binding residue (delta item 10).
- HYP.145 added, HYP.66 corrected: GENTOW2 S6.1 rows 23–24 descriptive-status fence; row 23 now measured to GAP at LW3 (delta item 11).
- HYP.146 added: W11-BOX-1 — the general W-11 menu tie is a program, not a proof (delta item 14).
- HYP.147 added: `exists_anisotropic`, re-verified absent from both Lean trees (delta item 15).
- MQ-2, MQ-3 queued: consumption checks + dated appends; the unperformed [GMN12] §4 characteristic audit, which qualifies the internal-F-2 branch of owner question 1 (delta items 12–13).

TIER-3 (item 16): six sub-items placed in `OFF-PATH`, one line each. One is superseded at HEAD — HE7's owed PE3 pass has run (ANNEX F-1, ACCEPTED 2/2).

- **Capstone-conditionality preview: UNCHANGED.** No folded delta adds, removes, or re-binds a conjunct in Display A or Display B. The two rows that touch the preview act on the supplier side only: HYP.143 refines the supplier of the existing `[GENHN-HE(μ≥3)]` conjunct above μ=3, and HYP.139 sits under the existing count-law/census suppliers. HYP.137 lies inside the preview's existing carve-out that "n=3 is conditional only on the cubic HMENU3/HEX3 proof perimeter"; whether it should be *named* there is owner question 9, and until that is answered the displays are left byte-unchanged.
- The eight v2 owner questions are carried verbatim; question 9 is appended and marked [v3].

## CHANGES-FROM-v3 (v4 weld-face-audit fold)

Source: `runs/qgen/WELD_FACE_AUDIT.md` (census row S-4, executed 2026-08-13 at the WIDENED charter: HYP.74–77 plus HYP.21/22/67/68/69/71). Thirteen corrections, **COR-WFA-01…13**. The audit ran AUDIT-ONLY — it edited no note, upgraded no grade, and every verdict is sourced to a corpus quote. This fold verified those quotes before transcribing them; **two did not survive verification and were folded CORRECTED**, both flagged at their rows.

Verdict folded: **1 REACHABLE-AND-CONSUMED · 0 CORROBORATIVE-ONLY · 9 NOT-REACHED** across the ten chartered rows, plus one previously unindexed face promoted to a row of its own.

Re-dispositions (5, all CARRY→NODE — the dead-branch weld rows):
- HYP.21 `[H-b]`/JB row 12 → NODE: reachable only via `[W12-H]` and `W11-BOX-1`’s superseded S4.3 program (COR-WFA-06).
- HYP.22 `[H-c]`/J-D1 value package → NODE: the aggregate is unreachable; only `[W12-H]` and W12 §S5’s display consume it (COR-WFA-07).
- HYP.75 `JB-NOLEG` → NODE: non-reachability signed on all four JB rows (COR-WFA-03).
- HYP.76 `W2-VALUE` → NODE: non-reachability signed (COR-WFA-04).
- HYP.77 `DMULT-S` → NODE: W-9 rides the citable (DMULT-w) tier (COR-WFA-05).

Corrections without re-disposition (7):
- HYP.73 **CLOSED** — the audit is the discharging run; record `runs/qgen/WELD_FACE_AUDIT.md` (COR-WFA-01).
- HYP.74 `JD0-BOX-2` — CONSUMED BY re-sourced from `[H-c]` to seven verified direct spine sites; reachability SIGNED; CARRY retained with the discharge route named (COR-WFA-02).
- HYP.67/68/69/71 — CONSUMED-BY re-homings off `[H-c]` / “W12 value partition”, all four shown to have zero weld-layer content; MATH retained, reachability as tower-leg residues explicitly NOT settled (COR-WFA-08…11).
- HYP.139 `W-1` transport — consumer chain confirmed and its missing middle term supplied (HYP.148); the note that a GENTOW5-A0/A1 fold would retire it is recorded as a property of a proposed unit, not a discharge (COR-WFA-13).
- HYP.24 `[H-e]` — supplier re-sourced from the off-route “(H-a)/(H-b)-leg” to `LEMMA GENHN-3` + GENIND-2’s consulted-height bound; the conjunct does not move (preview item iv).

New rows (2):
- **HYP.148** `GENHN-BOX-2` / the W-9 graded face, class CARRY — the ONE weld face inside a count law on the whole capstone path, in GENHN’s own words, previously indexed only through its sub-residue HYP.139 (COR-WFA-12).
- **HYP.149** the audit’s BONUS synthesis, class **PROPOSED-NODE** — GENHN’s [r2] gr(O_L) re-aim + GENTOW5-A0/A1 + GENHN-2’s pointwise-faithful slot passage, a route that would retire HYP.148 *and* HYP.139 together. Recorded because it is valuable and must not be lost; marked PROPOSED-NODE because **no accepted note asserts it** and it may re-disposition nothing until it runs as its own unit.

Knock-on locator fixes (2, not counted as corrections): HYP.39 and HYP.129 both named `[H-c]` as J-D0’s home and now point at HYP.74’s verified site list instead.

**Two audit statements folded CORRECTED, not verbatim:**
1. **HYP.76.** The audit’s row block asserts “Zero occurrences of W2-OPEN-1/-2 or W2-BOX-1 in any of the 20 cone notes.” FALSE — W12 carries two, at L1190 and L1509. Both were read in context: §S5’s composition display and its dependency-ledger status annotation, neither a consumption. The NOT-REACHED verdict is unaffected; the wording is corrected to “zero in nineteen of twenty; two in W12, both non-consuming display bookkeeping”. The audit’s own §1 states the W12 carve-out correctly — only the §2 row block generalized past it.
2. **HYP.149.** The audit’s caveat that “GENTOW5 is itself at grade 0/2 (hostile arc owed), so the fold inherits that arc” is STALE at HEAD: `GENTOW5_PROOF_2026-08-09.md` L2026 reads “Grade: ACCEPTED 2/2 stands, ANNOTATED by RUN A”, and SOL certification ledger row 10 reads “CERTIFIED 2026-08-12”. By this ledger’s standing rule the SOL ledger is HEAD-of-record for unit grades. The audit appears to have read one of the earlier repair-round “0/2 UNCHANGED” lines (L1471/L1531/L1612). Corrected on fold; the disposition is unchanged, since PROPOSED-NODE rests on the absence of an asserting note, not on GENTOW5’s grade. Same pattern as v3’s HYP.140 correction.

**ORPHAN-1 (recorded, deliberately not resolved).** Rows HYP.83–86 (`VD-m`, `(C-coll)`, `(R-coll)`, `PERIM-μ`) inherit NOT-REACHED from HYP.22 and their only preview conjunct has been removed — so they are dispositioned CARRY with nothing to be visible in. No COR-WFA line authorizes re-dispositioning them, so v4 stamps the inconsistency on each row rather than curing it silently. This is a v5 bookkeeping item and is surfaced to the owner under question 2’s answer. → **CURED AT v5 (COR-ORPH-01…04):** all four move CARRY→NODE, on a *fresh* reachability verification rather than on the parent’s verdict — the block is at HYP.83, and it checks the two weld faces that survived the v4 audit, which v4 could not have done for the one it had only just discovered.

- **Capstone-conditionality preview: CHANGED — the first change since v1.** Four conjuncts out (`JB-NOLEG†`, `[H-c]†` with its `VD-m/C-coll/R-coll/PERIM-μ` children, `DMULT-S†`, `W2-VALUE†`), two in (`JD0-BOX-2†` promoted out of the deleted package, `(GENHN-BOX-2 if n≥6)` newly disclosed). Owner-decision surface falls from six daggers to two. The BEFORE/AFTER is displayed in full at the head of the preview section with the audit citation. **This is a correction, not a weakening:** the four departing conjuncts were never load-bearing, and the entering one was load-bearing and undisclosed. v3 carried the weld layer exactly inverted — the unreachable value package in, the one consumed face out.
- The nine v3 owner questions are carried verbatim; **question 2 is stamped ANSWERED** (audit run, charter widened-by-default; the reachability half resolved by the audit's outcome). Eight remain open.

## CHANGES-FROM-v4 (v5 — the 0d-closure fold)

Sources: `docs/PROJECT_STATE.md` appends **#47** (L4541), **#48** (L4566), **#49** (L4593). Every quoted decision was read at its append before folding, and every Lean name asserted by the P4 rewire was re-verified in the tree at HEAD before being written into a row. **No new rows; no mathematics proved; the row count is unchanged at 149.**

**Re-dispositions (12).**

Closed by an owner answer (4):
- HYP.94 capstone signature → **CLOSED-SIGNED** (Q3, #47); three points signed, re-verified at `Statement.lean:55–58`.
- HYP.39 `JD0-BAR` → **CLOSED-SIGNED** (Q6, #49); the 68,523/0 machine grade is the bar. Optional codex pass preserved as **MQ-4**.
- HYP.95 Haar bridge → **CLOSED, off-path** (Q5, #47/#48); `genuineDensity` IS the proportion limit, so nothing frozen asserts Haar. Closed as off-path, **not** as proved — the measurability leg is still unproved and unformalized.
- HYP.16 `NS-15` finite-depth bound → **CLOSED, LAPSED** (Q1 coupling, COR-13); the ½·v(disc f) route was available only on the internal-F-2 branch, which the cite branch forecloses. Costless: the capstone needs finiteness, not the constant.

Moved off the capstone path by policy (2):
- HYP.96 `AX-CELLREC`/`AX-LEAF` → **OUT-OF-PATH-BY-POLICY** (Q7, #49).
- HYP.97 `RealInstanceAt.faithful` → **OUT-OF-PATH-BY-POLICY** (Q7, #49). Both remain live obligations *inside the quarry*; their faithfulness entries are still DRAFT.

ORPHAN-1 cured, all four CARRY→NODE (COR-ORPH-01…04):
- HYP.83 `(VD-m)`, HYP.84 `(C-coll)`, HYP.85 `(R-coll)`, HYP.86 `PERIM-μ` → **NODE**, recorded OUT of the cone. **Verified independently at v5, not inherited** — the full verification block is at HYP.83. Headline of that verification: one occurrence of the four labels across all twenty cone notes (`W12_PROOF:219`) and it is a *disclaimer* (*“all absent”*); and, crucially, the two weld faces that **did** survive the v4 audit were checked directly — J-D0 is the theorem that *deletes* these fences from count-layer conditionality (`JD0_PROOF:277–278`), and W-9’s hypotheses are *“Given W-6, W-7, W-8”* with no value-layer fence (`GRTJC:1777`), its `(VD-m)`/`(R-coll)` inheritance localized to a germ display that no cone note names (`W-7`, `JB-CREAD`, `JB-BOX-2`: zero cone hits).

Status change on a launched unit (1):
- HYP.149 WELD-ZERO route → **PROPOSED-NODE → IN-PROGRESS** (COR-WZ-01, directive 1 of #49). Launched 2026-08-14 at corpus grade, 0/2, hostile arc owed post-reset. **Re-dispositions nothing:** HYP.148 stays CARRY and HYP.139 stays MATH at full strength until the unit lands and passes its arc.

Re-labelled without changing bucket (1):
- HYP.15 `NS-7` → **CARRY-as-CITE** (Q1, #47). Still CARRY, now undaggered: the *branch* is decided (cite [AGNPRW] Thm 5.2), the *obligation* is not — in Lean `NS7` stays carried until proved or declared-with-faithfulness.

**Corrections without re-disposition (5).**
- **Header:** the Q4 review-boundary policy and the P4 rename map added as standing notes; the disposition glossary gains `IN-PROGRESS` and `OUT-OF-PATH-BY-POLICY`.
- **HYP.17** publisher-number verification **ELEVATED** from “bibliographic only” to `[CORE-SET]` and load-bearing: Q1 cites [AGNPRW] Thm 5.2 *by number*.
- **HYP.111** `W12-BOX-7` **SPLIT** under the Q4 policy — definitional half core (rides HYP.98), deep-tail TRP reconciliation half **lifted** to ordinary NODE work. Recorded alongside: the P4 rewire *narrows* this exposure, since the frozen headline density is now the outer limit, which does not depend on where the decided/undecided line falls.
- **HYP.98** `DEFINITION-AUDIT` **RETARGETED** to the core set and made **recurring** (directive 2 of #49: periodically pull fresh eyes onto the main definitions/axiom-cites as the Lean build proceeds).
- **HYP.137** carry-vs-node **DISPOSED** (Q9) by naming `HEX3-BOX-1` parenthetically in the preview; the append’s premise correction is recorded at the row — the n≤3 menus/drainage **do** enter the final proof as base cases; only `HEX3-BOX-1` stays out.

**P4 rename sweep (Q5, executed).** Every pre-rewire name in this file was found and updated, each stamped **[RENAMED per P4]**: HYP.01’s CONSUMED-BY (now names both `decidedDensity` and `genuineDensity` — the type map keys both routes); HYP.10’s “cubic sum-to-one” (re-keyed to `TotalMassOne` / `sum_genuineDensity_eq_one_of_drainage`); HYP.111’s carrier; Display A’s conclusion line; the dedup section’s Haar/RealInstance line; and question 5’s own text. Fixed-string re-grep confirms **zero surviving *use-site* occurrences of `upperDensity`** — the only two mentions left in the file are the rename map in the header and this sentence, both of which name the old label deliberately so the map stays readable.

**Preview changes (3, none of them a conjunct move).**
- **Display A FROZEN, Display B HISTORICAL** (Q8) — headings and a headnote.
- **The dagger count reaches 0.** `NS7(O)†` and `JD0-BOX-2†` lose their daggers to Q1 and Q6. Both conjuncts remain in the display at full strength; only the owner call attached to them is gone.
- **`HEX3-BOX-1` named parenthetically** in the n=3 perimeter clause (Q9).
- Display A’s conclusion now states `genuineDensity_O(σ) = decidedDensity_O(σ) = num(q)/den(q)`, with the tie (`genuineDensity_eq_of_drainage`) resting on the `A2_n` conjunct **already** assumed there, plus explicit notes that Σ_σ=1 is the separate Prop `TotalMassOne` and that Haar is not asserted. **No hypothesis conjunct was added, removed, or re-bound at v5.**

**Anything still open?** Reviewed deliberately, since the instruction was to flag rather than silently zero: **no owner question remains open.** All nine are answered by a dated append, and none of the answers is partial in a way that hands a decision back. Three items are *consequences* of the answers and are recorded as work, not as questions: HYP.17’s numbering check (now load-bearing), the DRAFT quarry axiom-faithfulness entries (relocated, not completed), and MQ-4 (an optional pass that gates nothing). The owner’s *“for now at least”* on question 1 is logged at HYP.15 as a revisit licence — re-opening it would be a new decision, not an unanswered one.

## CHANGES-FROM-v5 (v6 — the discharge fold)

Sources: `docs/PROJECT_STATE.md` appends **#48** L4566 (UNIFORMITY-P4, already reflected at v5), **#49a**/**#50** L4636 (the CERTAIN-NODES program closes, 23/23 landed, zero blocked); `spec/CERTAIN_NODES_2026-08-14.md`; `leanfinal/notes/CN_BATCH_{A,B,C,D}_2026-08-14.md`; `lean/notes/openmath/WELDZERO_2026-08-14.md`. **No new rows; no mathematics proved by this fold itself** (the mathematics was proved by the CERTAIN-NODES fleet on 2026-08-14 and is booked here); the row count is unchanged at 149.

**Discharges (2), each verified against the live Lean declaration before stamping.**
- HYP.03 `n-fold Hensel factorization` → **DISCHARGED**, `Uniformity.Hensel.exists_monic_factorization_finset` (CN-17, `leanfinal/Uniformity/MultiHensel.lean:111`, commit `bbe155c6`). Signature re-elaborated and compared word-for-word against the row's STATEMENT before stamping; residual scope noted (the weld with `typeOf_mul` into the full order-0 leaf law, REJECTED R10, is not yet assembled).
- HYP.147 `exists_anisotropic` → **DISCHARGED**, `Uniformity.Density.exists_anisotropic` (CN-15, `leanfinal/Uniformity/Density/AnisotropicForms.lean:149`, commit `d714d94a`). Lands in `leanfinal`, not `leancheck` as the row's own route sketch guessed; residual scope noted (the general-`O` `gate_bracket_*` integration is separate downstream work, and `exists_aniForm` duplicates leancheck's `exists_aniK` — MQ-6).

**Tally correction (1), no row text rewritten.** HYP.04/05/06 (`strongHensel`, `typeOf_shift`, `typeOf_scaleRoots`/`typeOf_scale`) were stamped **DISCHARGED 2026-08-14 (UNIFORMITY-P5)** in their row bodies before the v5 fold was written, but the v5 tally still counted all three under MATH. This file's own glossary (line 3) defines CLOSED as "a named instrument... has discharged the row and the reference is recorded in the row itself" — exactly their state — so v6's tally recounts them as CLOSED. The rows themselves are untouched; only the count is corrected.

**The other 21 CERTAIN-NODES landings (CN-01/02/04/05/06/07/08/09/10/11/12/13/14/16/18/19/20/21/22/23) have no pre-existing ledger row** — they are new infrastructure (general-`n` density/census API, the peel law, the two norm leaves, the covering-menu existence proof, etc.) that the v1–v5 sweeps never flagged as an open hypothesis, so booking them here would manufacture rows rather than discharge them. Two are instead booked as bounded follow-up actions, **MQ-5** (the CN-21/degree-2 landed-file merge decision) and **MQ-6** (the `exists_aniForm`/`exists_aniK` duplication retirement decision) — both orchestrator calls on landed files, neither a hypothesis.

**WELD-ZERO arc recorded (3 rows touched, 0 re-dispositioned).** HYP.148, HYP.139, and HYP.149 each get a v6 ARC NOTE recording the unit's progress since launch: **r1** (one CRITICAL repair C-1 — WZ-3(ii)'s type-preservation claim withdrawn and re-routed through a relabelling bijection, J-D0 removed from the fold's supplier list — plus one GAP repair G-1 and eight minors, all cured), then a **post-pass rider** folding six further minors (0 CRITICAL, 0 GAP) from the Opus/Claude-arm hostile pass on the r1 effective text (`runs/comp13/WZP2_output.log`). **The clean-pass counter now stands at 1 of 2**; the second, model-diverse gpt-5.6-sol confirmation pass is queued not before Tue 2026-08-18 10:23+ (the codex weekly window's reset). None of this licenses anything: per the unit's own status line ("composed, attempt 0/2, hostile arc owed") HYP.148 stays CARRY and HYP.139 stays MATH at full strength, and HYP.149 stays IN-PROGRESS — a launched, partially-repaired unit is still not a landed result.

## CHANGES-FROM-v6 (v7 — the five-block fold)

Sources: T2's dated consumption record, `lean/notes/openmath/T2_SIGMA_LADDER_MASTER_2026-08-12.md` EOF append, commit `66062771` (2026-08-14), itself answering `spec/EFF-HE6.md` OPEN-CALL 1/2; `docs/PROJECT_STATE.md` appends **#53** L4716–4740 (the sweep's supplier-findings), **#54** L4742–4760 and **#55** L4761–4776 (chapter G launches), **#56** L4778–4799 (the Fable-max substitution); `blueprint/CHAP-G_base_cases_menus.md` §1 (HONESTY BLOCK) and §10 (structural DAG edges); `leanfinal/Uniformity/ChapG/{G36,G37,G76}.lean`; `lean/notes/openmath/WELDZERO_2026-08-14.md`. Every quote and every Lean signature was re-verified at HEAD before being written into a row. **Five new rows (150–154); no pre-existing row changes bucket; six new MAINTENANCE QUEUE actions (MQ-7–12); one existing action (MQ-1) annotated.**

**Five new rows, the HE6/T2 adjudication (0 re-dispositioned elsewhere).**
- HYP.150 EFF-HE6 OPEN-CALL 2, closed for T2's consumption → **CLOSED-FOR-T2**. Nine sampled sites immune; scoped explicitly to T2, not to HE7/HE6R1.
- HYP.151 A3 F-1's "vacuous" claim, a real dated HE6 source defect → **CLOSED**, informational; false in HE6's own consumed regime `k > (D′−1)h`, but zero live consumers of the false reading anywhere in the sampled corpus.
- HYP.152 "Consumption, not citation, is the gated relation" (standing protocol) → **NODE**.
- HYP.153 "The compiler has invented no span" (standing EFF-* process rule) → **NODE**.
- HYP.154 `LEMMA HE6-0`'s tenth-pin question, re-classed from a T2 decision to a chapter-cut concern → **NODE**.

**Six new MAINTENANCE QUEUE actions, the 0a sweep's supplier-findings (append #53).** MQ-8 (HETOW's transliterated/elided F-2 quote), MQ-9 (GRTJB §7.1's 6,575-vs-6,700), and MQ-10 (GRTW2 §6.1's 6,396-vs-6,403) are **MQ-BATCH-PENDING** — each lives in a byte-frozen informal proof note with no dated append correcting it since the sweep; in two of the three (GRTJB, GRTW2) no correction is owed at all, since nothing downstream depends on the flagged number. MQ-11 (HE7 Q1's two battery-table label/convention slips) is disclosed, signed, and explicitly **not owed a fix** by the corpus's own byte-freeze protocol. MQ-7 (GENTOW6's unresolvable commit token `640b31ff`) turned out to be **MQ-LANDED, caught mid-fold**: `GENTOW6_PROOF_2026-08-09.md`'s own dated correction append (commit `b8365d9e`, 2026-08-15) resolves it, postdating append #53's sweep — the row is updated to cite the fix rather than describe a still-owed action. MQ-12 (LIFTCORNER's 15-vs-20 self-count) is likewise **MQ-LANDED**: this defect lived in a pre-merge compiler shard, not an informal proof note, and the merge itself already corrects it in the committed `spec/EFF-LIFTCORNER.md`.

**Chapter G checked against five standing rows; one partial discharge, none else.**
- **HYP.27** (`A2` drainage) gets a genuine partial discharge at **n = 2 only**: `leanfinal/Uniformity/ChapG/G36.lean:43`, `undecidedCount_two_eq`, sorry-free Lean-core, sharpens the previously-landed lossy `undecidedCount_le` bound to the exact law. The row's general-`n` CARRY bucket is unchanged — n≥4's supplier stays DRAIN-N4/CS-1Q as before.
- **HYP.137** (`HEX3-BOX-1` tail-σ lemma) gets the blueprint's own honesty-block confirmation (H-2, quoted verbatim at the row) that chapter G treats it as an EXPLICIT NON-NODE with a live-coded `BLOCKED: HYP.137` tripwire, plus `G76.lean`'s `card_le_undecidedCount_three` — the LOWER half only of HEX3's bracket. **Disclosure, not discharge; still MATH.**
- **HYP.28, HYP.29** (`hMenu3`, `hExhaust3`) checked against `BP.G.72`/`BP.G.71` and confirmed NOT discharged in the blueprint's own words ("type-level shadow, not its discharge"; "names ... as its explicit hypothesis") — **NODE, unchanged.**

**WELD-ZERO arc: model substitution, not progress.** HYP.148 and HYP.149 each get a v7 ARC NOTE: append #56 reassigns the still-owed second (model-diverse) confirmation pass from gpt-5.6-sol to a Fable-max agent, and #56's own EOF line records it as LAUNCHED and running ("WELD-ZERO confirmation pass (pass 2 of 2) runs on Fable-max now"). **IN FLIGHT at fold time — no landing commit exists.** Clean-pass counter stays at 1 of 2; HYP.148 stays CARRY, HYP.139 stays MATH, HYP.149 stays IN-PROGRESS, all unchanged from v6.

**Header note added.** THE FABLE-MAX SUBSTITUTION (append #56) — a standing note, in the same style as THE REVIEW-BOUNDARY POLICY and THE P4 RENAME, recording that the sol-deferred queue (spec/blueprint cross-reads, WELD-ZERO + JD0 confirmation passes, the n=2 adversarial pass, hard-chapter authorship E/C) may now be discharged by Fable-max, with codex demoted to optional belt-and-braces. MQ-1 is annotated accordingly (it is the one existing MAINTENANCE QUEUE action append #56 names by description).

**Anything still open?** No owner question is raised or answered by this fold (needs-Asvin stays 0). Two items are recorded as residuals rather than closed: HYP.150's HE7/HE6R1 side of EFF-HE6 OPEN-CALL 2 (not checked, not asserted), and MQ-8–10 (disclosed, unreconciled defects genuinely awaiting a dated correction append; MQ-11 is disclosed but explicitly not owed a fix, and MQ-7/MQ-12 both turned out already landed).

HYPLEDGER v7: 154 rows / 35 carry / 18 math / 0 needs-Asvin
(dispositions: 35 CARRY · 18 MATH · 81 NODE · 4 MERGED · 13 CLOSED · 2 OUT-OF-PATH-BY-POLICY · 1 IN-PROGRESS; plus 12 MAINTENANCE-QUEUE actions and 6 OFF-PATH lines, neither counted as rows. Owner questions: 9 listed, 9 ANSWERED, 0 open — unchanged from v6, this fold answers none.)
Superseded tally — HYPLEDGER v6: 149 rows / 35 carry / 18 math / 0 needs-Asvin
(dispositions: 35 CARRY · 18 MATH · 78 NODE · 4 MERGED · 11 CLOSED · 2 OUT-OF-PATH-BY-POLICY · 1 IN-PROGRESS; plus 6 MAINTENANCE-QUEUE actions and 6 OFF-PATH lines, neither counted as rows. Owner questions: 9 listed, 9 ANSWERED, 0 open — unchanged from v5, this fold answers none.)
Superseded tally — HYPLEDGER v5: 149 rows / 35 carry / 21 math / 0 needs-Asvin
(dispositions: 35 CARRY · 21 MATH · 80 NODE · 4 MERGED · 6 CLOSED · 2 OUT-OF-PATH-BY-POLICY · 1 IN-PROGRESS; plus 4 MAINTENANCE-QUEUE actions and 6 OFF-PATH lines, neither counted as rows. Owner questions: 9 listed, **9 ANSWERED, 0 open — the 0d package is CLOSED**.)
Superseded tally — HYPLEDGER v4: 149 rows / 39 carry / 22 math / 8 needs-Asvin
(dispositions: 39 CARRY · 22 MATH · 81 NODE · 4 MERGED · 2 CLOSED · 1 PROPOSED-NODE; plus 3 MAINTENANCE-QUEUE actions and 6 OFF-PATH lines, neither counted as rows. Owner questions: 9 listed, 1 ANSWERED at v4, 8 open.)
Superseded tally — HYPLEDGER v3: 147 rows / 43 carry / 22 math / 9 needs-Asvin
(dispositions: 43 CARRY · 22 MATH · 77 NODE · 4 MERGED · 1 CLOSED; plus 3 MAINTENANCE-QUEUE actions and 6 OFF-PATH lines, neither counted as rows)
Superseded tally — HYPLEDGER v2: 135 rows / 43 carry / 17 math / 8 needs-Asvin
