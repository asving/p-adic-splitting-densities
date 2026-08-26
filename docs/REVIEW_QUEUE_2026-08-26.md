# OWNER REVIEW QUEUE — 2026-08-26

Consolidated secondary-review queue, compiled by unit RQ from four sources: (1)
`docs/CITE_REVIEW_LIST.md` (the queue's existing spine — referenced, not duplicated,
below); (2) all `runs/wave-b/verdict_*.md` files (106 at sweep time — one, `verdict_PK12.md`,
landed mid-sweep on 2026-08-26 and is folded in below), grepped for
review/flagged/owner/human and read in full context; (3) the dated amendment records
`[A-C.10..16]`, `[A-E.7]`, `[A-I.2]`, `[SG-0]`, `[PK-*]` in `leanspec/` and
`leanfinal/Uniformity/`; (4) `docs/in-progress/PACKAGING_ROUTE_2026-08-25.md` §6's
review-list rows (U15). Coverage stats and method are in
`runs/wave-b/verdict_RQ.md`.

**How to use this document.** Three tiers, ordered by how directly they match the
owner's two standing gates (main Lean statement changes; literature-cite imports —
`signoff-scope-2026-08-24`/`-08-15` memory entries). Tier 1 is the owner's stated
primary role (cite spot-checks). Tier 2 is re-signs of already-signed statements
(should be skimmable — most are honest repairs of machine-refuted forms, already
enacted, not asking permission but flagging what changed). Tier 3 is net-new general
lemma banks the fleet wrote, flagged by the units themselves as worth a look because
they are new mathematical content rather than transcription. Every row names the exact
file/declaration and where to look; nothing here has been re-derived or re-checked by
this unit — RQ only located, deduplicated, and organized what other units already
flagged.

---

## Tier 1 — Cite transcriptions (the owner's primary role)

| # | cite | Lean name(s) | landed at | quoted-clause location to spot-check | status |
|---|---|---|---|---|---|
| 1 | [AGNPRW] Thm 5.6 (OM descent terminates) | `agnprw_termination : NS7TerminationStatementR` + NEW binding `NS7Termination` (I.01), discharged via `ns7Termination_of_cite` | `leanfinal/Uniformity/ChapC/C94.lean` + `ChapI/I01.lean` | C94.lean module docstring (the executed print-read) | OPEN — review the I.01 BINDING only (the redraft grammar itself was audited at A-C.6) |
| 2 | FGMN, *Residual ideals of MacLane valuations*, J. Algebra 427 (2015): Thm 2.8 + Cor 4.12(3) + Cor 4.9(3) + Def 5.4 | `fgmn_dv_exact_mul` (axiom; C66b) | `leanfinal/Uniformity/ChapC/C66b.lean` | C66b.lean module docstring (quotes + the corpus↔paper dictionary: `IsDvPure`↔Def 5.4, `dvResPoly`↔R_r up to twist) | OPEN — review the dictionary + spot-check quotes against the journal text. **New consumers since the row opened:** `C123r.lean` (`s2_composedKeyPow_mem` etc., via C.131ac's `composedKey_pow_mem_towerLocus`) and `U-HEART`/`UASM`'s chain at `C131af.lean` — same axiom, no new dictionary content, listed here so the spot-check covers every use site |
| 3 | FGMN Cor 4.12(2) grade-anchoring vs. the S2 parity twist (U14/A-C.13, 2026-08-25) | `FGMNSourceData.PrevGrade`, `FGMNSourceLaws.graded_mul`'s restored `PrevGrade β'` premise, `FGMNCalculus.Rgr_mul` | `leanfinal/Uniformity/ChapC/C130fg.lean`, leanspec `ChapC.lean` NODE C.92, `C130pk.lean`, `C130la.lean`, `C99r.lean` | `docs/in-progress/COR412_ADJUDICATION_2026-08-25.md` §3–4 (Def 3.12/3.13 + Cor 4.12(2) proof, "because `s_r(β)=0`") | **ENACTED as A-C.13** (see Tier 2 row 4) — still needs the owner's spot-check of the two quoted clauses (Def 3.13's line parameterization; the Cor 4.12(2) proof line) against the journal text, per the original CITE_REVIEW_LIST row |
| 4 | (not yet declared) FGMN's order-2 theorem of the residual polynomial, same J. Algebra 427 (2015) paper | none — flagged only | would land near `C78.lean`'s dv-purity chain (CC-16/`FGMNCalculus` path) | `runs/wave-b/verdict_C78.md` lines 62–65 | **FUTURE Tier-1 item** — explicitly flagged "print-read + owner review-list row required — NOT declared by this unit"; nothing to check yet, recorded so it isn't missed when it lands |
| 5 | (decision point, not yet made) C.63 `classSize_separable` | none | would land at the C.27→C.59→C.61→{C.62,C.63}→{C.49,C.69} chain (`runs/wave-b/verdict_AC15C27.md` §"6-row chain") | `runs/wave-b/verdict_DEC1.md` row "Genuinely MISSING objects" | **FUTURE Tier-1 item** — DEC1 named the fork explicitly: "landing = prove, or cite-axiom behind the owner gate"; currently a leanspec axiom only, blocked on the C.34 dissection frontier either way |

**Not re-derived here, flagged for completeness:** `docs/AXIOM_FAITHFULNESS.md` carries
four older entries still marked "DRAFT — PENDING ASVIN REVIEW" (dated 2026-07-30/31,
predating this queue's protocol and CITE_REVIEW_LIST): `AX-CELLREC`
(`PadicMeasure.AX_cellRecursion`), `AX-INDEX`
(`OM.Classifier.omReadValuation_lt_of_certLevel_fkeyed`), `AX-LEAF`
(`OM.OmLeafFaithful.om_leaf_faithful`), and `AX-GMN-INDEX` (not yet declared as a Lean
axiom — additionally gated on two unbuilt definitions). These are out of this sweep's
four named sources; if still open they belong in a future pass over that file.

---

## Tier 2 — Amendments to signed statements (newest first)

Each row: the old (pre-amendment) form, the new (re-signed) form, and where the machine
evidence (refutation + repaired-form proof) lives.

| amendment | node / declaration | old form | new form | machine evidence | unit / date |
|---|---|---|---|---|---|
| A-C.16 | C.91 `gentow5_selffeed` | naked `hj` absent (live-range fence missing) | `(hj : j < μ)` restored | `C150rb2.gentow5_selffeed_false` (naked form FALSE: `j=μ`,`u=0` satisfies `hOnSide`, forces `ℓE<0`); repaired form PROVED as `gentow5_selffeed_resigned` (floor telescoping) | RB2, 2026-08-25 |
| A-C.15 | C.69 `ClassSizeSupplyData.read_form` | quoted the naked C.64 law with no riders | gains `HasLabel L (blockFactor L f)` + `(F.e₁*F.f₁) ∣ (blockFactor L f).natDegree` riders | `C64.lean`'s `blockDegEq_false` (3=2 at `(s2Frame,L₀,g₀)`/ℤ_[2]); repaired shape = C.35's landed `hasLabel_natDegree_eq_of_dvd`, proved as `blockDeg_eq_resigned` | AC15C27, 2026-08-25 (DEC1's stop-the-line finding; A-C.10 had fixed the standalone axiom but missed this bundle field) |
| A-C.14 | C.89 `gentow5w_two`/`gentow5w_one_shape`, C.90 `gentow5_key_certificate` | no C.99 supply cascade; C.90 missing `hr3`, the `ψ'`↔`Φnext` recipe coupling, and `hadm`'s 3rd conjunct | four supply binders (`hprev`,`hnorm`,`hnormdeg`,`hnormz`) added to both C.89 axioms; C.90 gains `hr3 : 3 ≤ r`, `(c, hψc, hres)` recipe-coupling binders, and `hadm`'s `coeff 0 ≠ 0` conjunct | `C107ac14.lean`: `gentow5w_two` and `gentow5_key_certificate` LANDED Lean-core; `gentow5w_one_shape` still HOLD (OPEN-LETTERS) with a conditional form landed; pre-repair instantiation `ψ' := X^f'` is shown to derive `False` at `f'≥2` | AC14, 2026-08-25 (predicted verbatim by GENTOW2_ADJUDICATION's "cascade flag") |
| A-C.13 | C.92 `FGMNCalculus`/`FGMNSourceLaws.graded_mul`/`Rgr_mul`, C.99 `gentow2_Bpp` | U9/A-C.11 had removed the `β∈Γ_{r-1}` premise as "automatic after clearing" | `PrevGrade : ℕ → Prop` field restored; `graded_mul`/`Rgr_mul` regain `S.PrevGrade β' →`; `gentow2_Bpp` gains explicit `(hprev : I.PrevGrade u')` | `docs/in-progress/COR412_ADJUDICATION_2026-08-25.md` (print-read: Cor 4.12(2) proof line "because `s_r(β)=0`"); RP23's tooth machine-refutes the unrestricted plain law at odd×odd; 5 files rebuilt green (`C130fg/C130la/C130pk/C99r.lean` + leanspec), all `#print axioms` Lean-core | AC13, 2026-08-25, correcting U9 Q3 |
| A-I.2 | I.10b `CanonicalDeepTwistConfig`/`deepTwist`, E.63 `DeepTwistConjunct` | unbounded `∀ i, 3 ≤ i → …` (E.63); I.10 sockets had no finite-tower-depth binder | (a) interpretive rider: `K_t` is the terminal common receiver, not literal per-level `K_i` membership; (b) `DeepTwistConjunct r`/`DeepTwistConjunctLive` bounded to `3 ≤ i ∧ i < r`, with an `r` binder threaded through I.10b/E.63/the I.24 core registry | `leanfinal/Uniformity/ChapI/I10FreezeV2.lean` (`DeepTwistConjunctLive`, `deepTwistConjunctLive_iff` — an `Iff.rfl` anti-drift pin); `lake build Uniformity.ChapI` green (8686 jobs) | F3 (proposal, 2026-08-24) → enacted in `leanspec/Leanspec/ChapI.lean:625,657,734-743` + `ChapE.lean:1406` |
| A-C.12 | C.99 `gentow2_Bpp`/`theta_letter_valued`, C.101 `gentow2_B`, C.103 `gentow2_A`, C.85 `theta_dictionary` | C.99/101/103 omitted source-stated supply data (B-1 normalizer families, recipe data, admissibility antecedent); `theta_dictionary` asserted an untied `θ(s+t)` cocycle | RE-SIGN (a) on C.99/101/103 (supply hypotheses added; `gentow2_Bpp` machine-certified provable from the class fields alone); `theta_dictionary` RE-SIGN with height-tied quantifiers (still open); C.100/C.102/C.88 stay HOLD (need OPEN-EVAL-ISO/OPEN-DICT-2/OPEN-LETTERS) | `docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md` §0 verdict table + §9 diff; `leanfinal/scratch/GSW_check.lean` (`gentow2_Bpp_resigned_provable`, Lean-core) | GSW, 2026-08-24 |
| A-C.11 | leanspec NODE C.92 `FGMNCalculus` (whole class body) | provisional class body (U7 §9's open questions Q1–Q7) | exact replacement per U9's 7 decisions: class = calculus of the next augmented valuation (Q1); `Rgr`=coeff-0 of the *polynomial*-valued `R_{r+1,β}` (Q2); `PrevGrade` removed as redundant (Q3 — **later reversed by A-C.13**); class kept live at `r=0` (Q4); Gauss cite pinned (Q5); C.100 re-scoped to `deg g < D₂`, `hfree` deleted (Q6); C.90 stays OPEN-LEVEL-GENERAL, no fake field added (Q7) | `docs/in-progress/FGMN_ADJUDICATION_2026-08-24.md` §1 verdict table + §11 unified diff | U9, 2026-08-24 |
| A-C.10 | 5 axioms: `slot2_exact` (C.27), `blockDeg_eq` (C.64), the C.67 mult-tie bundle, and two `C.80`-family tower clauses | naked forms with no label/divisibility/purity riders | riders restored (`hx : IsPure X g F.h F.e₁` on C.27; `HasLabel`+divisibility riders on C.64/C.67/C.80's two clauses); each dropped conjunct survives only as a separate floor-level theorem | `ChapC/C27.lean:slot2_exact_false`, `C64.lean:blockDegEq_false` (3=2), `C67.lean:multiplicityTie_false` (3=2), `C80.lean:partialProjection_false`/`tiePurePower_false` (5=4) — all machine-refuted at concrete probe frames over ℤ_[2] | 2026-08-24 (5 leanspec sites, `ChapC.lean:879,2286,2331,3549,3624`) |
| A-E.7 | E.57 `BlockSplitTarget` | `hpart : True` | `hpart : Nonempty (PartitionLeg I)` | landed `PartitionLeg` + proof `block_split_of_partitionLeg`, `leanfinal/Uniformity/ChapE/E57p.lean`; `lake build Leanspec.ChapE` green (9240 jobs); field-list diffed byte-for-byte, empty diff | AE7, 2026-08-24 |
| SG-0 / PK-1..6 | S2 `ChainRealization`/`FGMNSourceData`/`FGMNSourceLaws` carrier + `fgmnCalculusOf`, ~12 files (`C130fg/in/k2/th/pt/cr/ar/vw/pk/s17/s18/sg.lean`) | `ChainRealization` carried `(e' f' u')` params + `fgmn`/`fgmnLaws`/`grade_compat`/`letter_compat` fields typed at the refuted depth-two shape `(2,1,5)`; `FGMNCalculus` had NO inhabitant anywhere | **FULLY ENACTED 2026-08-26 (unit PK12, superseding U15's proposal and SG01's conditional discharge)**: `ChainRealization` retyped to the split node (params/fields removed, `node : SplitNodePointSource …` added); `C130pk.fgmn_model_calculus_nonempty` (factored map) + ★ `C130sg.s2_calculus_discharge : Nonempty (FGMNCalculus (s2DepthOne h2 hq) 2 1 5)` — **UNCONDITIONAL**, no `w` witness needed any more (SG01's version was conditional on one datum `w`) | `lake build Uniformity.ChapC` (8804 jobs) + `Uniformity.ChapI` (8710 jobs) + leanspec `ChapC`/`ChapI` (9278 jobs) all green; 12 touched/new files' `#print axioms` all Lean-core; both non-swallowing grep-teeth pass (exit 1) | U15 (design, 2026-08-25) → PK-1/PK-2 (folding in PK-3..6) enacted by unit **PK12**, 2026-08-26 |

**Open review-list rows carried forward from PACKAGING_ROUTE §6 (U15), not yet amendments — read alongside the table above:**
1. Depth-2 parameter: every mention of the S2 depth-two class at `(2,1,5)` (CC-17's typing, `LegacyFGMN`, SG-1's `calculusNonempty` target) should really be `(2,1,21)` — confirmed by 3 independent legs, but not yet re-signed.
2. The `hprev`/`hcop` clearing tension: `I.PrevGrade u'` (A-C.13) is unsatisfiable at any evenness-realized instance passing `hcop` — `¬S2PrevGrade 5 ∧ ¬S2PrevGrade 21`, machine-pinned. Which clearing the future μ₃ operators use (OPEN-DICT-2) must be decided before Route-B. A candidate unblock: fence `hprev` by `2 ≤ f'` (A-C.15-style re-sign).
3. Leanspec NODE C.90's `gentow5_key_certificate` binds ONE `(e',f',u')` triple across all truncations `i ≤ r`, but each truncation's honest data differ — satisfiable only for uniform-data towers; needs a per-level family at its next re-sign.
4. `gentow5w_one_shape`'s remaining holds: `htie` (OPEN-LETTERS) and `hprev` — depth-1 consumer cannot fire until both move.

---

## Tier 3 — New general statements (reusable lemma banks), grouped by file

These are net-new mathematical content the fleet flagged itself ("Flagged for human
review — trust boundary — new statements") because Lean-checked ≠ correctly-modeled;
Lean verifies the proof, not that the statement says what the unit thinks it says.

| file | unit | flagged declarations | one-line what-it-is |
|---|---|---|---|
| `leanfinal/Uniformity/ChapC/C130nv2.lean` | NV2 | `stageHeight_le_modByMonic`/`_eq_min_mod_div`, `stageHeight_dev_mul_eq`, `le_line_dev_term`/`lt_line_dev_term`, `dvSupp_add_le_dvSupp_mul` | the one-step MacLane expansion (`dv(w)=min(dv(w%ₘΦ′), dv(w/ₘΦ′)+dv(Φ′))`) + both-direction convolution-term estimates + the ≥-half of the level-two product law |
| `leanfinal/Uniformity/ChapC/C130nv3.lean` | NV3 | `stageHeight_dev_endpoint_le_of_surv` (generic, conditional on `hsurv`), `s2_stageHeight_mul_modByMonic_le` (S2 survival core, unconditional), `s2_dvSupp_mul`, `s2_mul_modByMonic` | the "survival core": does the unique lowest convolution term survive residual cancellation. Generic case genuinely open (needs `hresirr`, a reducible-residual counterexample is given); S2 case proved unconditionally by parity case-split |
| `leanfinal/Uniformity/ChapC/C130rp2.lean` | RP23 | `twistRead_add_of_le`, `twistRead_eq_zero_of_lt`, `dev_mul_endpoint_split` | generic-frame, strict-admissibility read/development lemmas (not S2-specific) |
| `leanfinal/Uniformity/ChapC/C130rp4.lean` | RP4 | `dev_mul_conv_split`, `le_stageHeight_finsetSum`, `twistRead_finsetSum_of_le`, `ceil_le_dvHgt_of_le_dvSupp`, `le_stageHeight_mul_modByMonic`, `s2_dev_mul_one` | convolution/finite-sum height bounds feeding the graded residual machinery |
| `leanfinal/Uniformity/ChapC/C130rp6.lean` | RP56 | `S2PrevGrade` (evenness realization — carried as a def until OPEN-DICT-2 proves the divisibility test), `exists_slotOnGrade_of_exact`, `s2GradedRes_ne_zero_of_exact`, 3 assembly theorems | the S2 realization of A-C.13's new `PrevGrade` field, plus the graded-residual nonvanishing/assembly bank |
| `leanfinal/Uniformity/ChapC/C130rp8.lean` | RP78 | `s2GradeOf`, `s2NormRes` (certified `= ⌊s(g)/e₂⌋`), `s2_graded_scalar_nonzero` (+worker/fills), 2 endpoint pins, a degree law | the normalized-residual scalar and its nonvanishing |
| `leanfinal/Uniformity/ChapC/C130rp9.lean` | RP910 | `s2GradedRes_natTrailingDegree_mul`, `dvSideMin_mul_of_exact`, `s2NormRes_mul`, FD-0/A-C.11 shape pins | Cor 4.12(3)-shaped exact multiplicativity at the normalized residual |
| `leanfinal/Uniformity/ChapC/C130kp0.lean` | KP0 | 5 predicate definitions (incl. "prime-ideal-through-divisibility" rendering), the graded-piece characterization, the odd-carry engine | new predicates characterizing the S2 key polynomial's minimality shape |
| `leanfinal/Uniformity/ChapC/C130kp1.lean` | KP12 | the backward translation + fences, carried-key characterization, KP-2's statement, the naked-KP-2 refutation, the named-gap discharge | KP-2's μ-minimality-at-recipe-degree bank |
| `leanfinal/Uniformity/ChapC/C130kp3.lean` | KP34 | KP-3's honest hypothesis set, the trichotomy teeth, `s2_key_criterion`, "the crown", the pin's `keyAt 1` anchoring | the S2 key-polynomial irreducibility criterion (trichotomy form) |
| `leanfinal/Uniformity/ChapC/C130kp5.lean` | KP56 | `s2Key_eisenstein_irreducible`, `s2Key_irreducible_map_fractionRing`, the `…cX` generalization bank, `s2NormRes_composedKey`, `s2KeyPoly_composedKey` | Eisenstein-criterion irreducibility for the S2 key polynomial, ported to the composed/tower setting |
| `leanfinal/Uniformity/ChapC/C130fd0.lean` | FD01 | `s2_key_irreducible` (**published Lemma 1.8's conclusion, new direct proof at KP-0's predicates, no cite**), `g₈` adapter statements, both depth-two refutation statements, `s2SourceLaws_depthTwo_unsatisfiable`, `s2DepthOne`/`s2DepthOne_fld_eq` truncation typing, the vacuous discharge of field 6 at `r=1`, 2 FD-1 statements | the S2 depth-one `FGMNSourceData` instance + the machine-refutation that depth-TWO is unsatisfiable at the landed operators (which forced SG-0's anchor workaround, Tier 2 row) |
| `leanfinal/Uniformity/ChapC/C130sg.lean` | SG01 (2026-08-25), superseded by PK12 (2026-08-26) | `S2LevelOneThreshold` + its disclosure tooth, `s2SplitNode`/`s2Frontier` instance statements, `s2Frontier_legacyEvaluation_isEmpty`, `s2LegacyFGMN_landed_empty`, `S2LevelOneThreshold.ofSplitNode`, the `LegacyFGMN` quarantine typing | SG01's FIRST inhabitant of the S2 split-node frontier was conditional on one datum `w`; PK12 (Tier 2 SG-0/PK row) replaced the relevant stage with ★ `s2AnchorCalculus`/`s2_calculus_discharge` — **UNCONDITIONAL**. Both emptiness theorems above are retained statement-verbatim and still worth a look |
| `leanfinal/Uniformity/ChapC/C130pk.lean`, `C130fg.lean`, `C130s17.lean`, `C130s18.lean` (+ 8 more) | PK12 (2026-08-26) | `fgmnCalculusOf`/`fgmn_model_calculus_nonempty` (factored packaging map), ★ `s2_calculus_discharge` (see above), the retyped `ChainRealization`/`RealizedInput`/`SplitNodePointSource` carrier shapes, C130s18's re-premised socket bodies (`∃ (E : Type uE) (fE : Field E) …` replacing the `(e' f' u')` existential) | the full packaging-route enactment (Tier 2 row) — flagged here because 12 files' worth of new/retyped general statements landed in one unit; `runs/wave-b/verdict_PK12.md` §"Sites the diff didn't cover" also records 4 minimal-repair judgment calls (named instance binders, universe pinning, `C130st.lean` left un-retyped by import-direction necessity) worth a skim |
| `leanfinal/Uniformity/ChapC/C107ac14.lean` | AC14 | (covered under Tier 2 A-C.14; landing proofs, not new statements) | — |
| `leanfinal/scratch/U15_check.lean` (superseded, no longer elaborates) | U15 | `fgmnCalculusOf`, `s2AnchorCalculus`/`s2_calculus_discharge`, `ChainRealizationV2`/`V2b`/`RealizedInputV2`, 4 floor/PrevGrade numeral pins | the proposed PK-1..3 retyped shapes, pre-registered before enactment. PK12's own verdict notes this scratch file "will no longer elaborate against the enacted corpus" — historical record only, cross-check against the landed row above rather than this file |
| `leanfinal/Uniformity/ChapC/C84d.lean` | TDW | (module docstring's "⚠ mandatory-review block") | the telescope/junk-value conventions for `TowerDatum.deepTower`'s off-range indices (rungs outside `{1,2}`); `hπ` is carried but unused, flagged as the same pattern C.97 already established |

---

*Compiled 2026-08-26 by unit RQ. Read-only sweep — no files other than this one and
`runs/wave-b/verdict_RQ.md` were written; nothing was committed.*
