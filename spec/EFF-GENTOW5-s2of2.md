# EFF-GENTOW5-s2of2 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: gpt-5.6-sol high (2026-08-18), compiler/cross-read replacement of the 2026-08-14 opus draft.**

## 1. Shard header

**Source note:** `lean/notes/openmath/GENTOW5_PROOF_2026-08-09.md`

**HOME range:** source lines 1475–2313 inclusive (§S8 PE2 repair record · §S9 PE3 repair record · §S10 post-PE4 fold · the dated acceptance record · §S11 `[GT5-r4]` RUN A repairs · §S12 `[GT5-r5]` residual-discharge repairs · the post-D3i corrigendum). Earlier and later text is used only to resolve material homed in that range.

**HEAD blob hash:** `00a4c7e80cfd652bc4416edb476d44ae6ca0a420` (fresh `git hash-object`; source clean in the working tree; last touched by commit `ddfc6b61`, verified by `git cat-file -t` = `commit`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md`; temporary IDs `EFF.GENTOW5.s2of2.<nn>`. Companion shard: `spec/EFF-GENTOW5-s1of2.md` (lines 1–1474), which owns the base statements this shard corrects.

### Governing effective-text record

This shard's HOME range *contains* the note's effective-text rule. The acceptance record (lines 1671–1741, homed here) reads:

> “**GENTOW5 IS ACCEPTED 2/2** — passPE4 CLEAN (0 CRITICAL + 0 GAP + 2 MINOR, GENTOW5_passPE4_report.md @ b22b37b; counter 0/2 -> 1/2) followed by passPE5 CLEAN (0 CRITICAL + 0 GAP + 3 MINOR, GENTOW5_passPE5_report.md @ 18900e03; counter 1/2 -> 2/2): two consecutive clean hostile passes, the standing acceptance bar.
> **THE NOTE IS FROZEN AT THIS RECORD: dated appends and dated brackets only; statement displays and sealed artifacts stay byte-untouched.**”

> “Grade after this record: **ACCEPTED 2/2**. Dated appends only beyond this line.”

The two post-acceptance appends state their own discipline. S11 (line 1752):

> “The note is frozen: these are dated corrections BY SUPERSESSION — the superseded sentences are quoted, stay byte-intact above, and read as corrected here. Pure-append discipline: the ledger at S11.6 carries the per-commit prefix md5s.”

S11.6 (line 2023):

> “Statement displays above stay byte-intact; corrections are by dated supersession (S11.1 direction + closure, S11.3 (a)@i=1 re-scope, S11.5 (b) re-index) and dated fences (S11.2 [GENTOW5-W(i)], S11.4 m-range).”

S12 head (line 2033):

> “## S12. [GT5-r5] RESIDUAL DISCHARGE REPAIRS (2026-08-12 — dated append; acceptance 2/2 remains ANNOTATED)”

**Effective text for this shard = every append in the range, applied in chronological order, with the later append governing the earlier where they name the same object.** Two in-range supersession chains matter and are resolved below: S12.2 supersedes S11.4 (the lift rung), and S12.1 supersedes S11.2's “unaffected scope” list — with the post-D3i corrigendum then correcting S12.1's own clause-(b) twist index.

### Scope split

**ABSORPTION/supply SET.** This range does not add supply; it *narrows* it. The narrowing is stated at S11.2 and S12.1 and summarized at S11.3:

> “Net position after S11.2 + S11.3: the pinned-w_i form is unconditionally realized at i = 2 exactly; at i = 1 the shape is proved with the tie open; at i >= 3 the form is open behind [GENTOW5-W(i)].”

**APPEND/consumption PROTOCOL scope.** Two distinct protocol facts are recorded here and must not be conflated with the supply set:

> “Sealed artifacts untouched this round: gentow5_checks.py 5fa684c7..., gentow5_output_exact.txt dc499a49..., gentow5_output_full.txt 839a8660..., gentow5_rider_f32dev.py 81bbb5db... — no runner edited, no sealed re-run.” (S11.6)

> “Awaiting sol re-confirmation in the next queue.” (the post-D3i corrigendum, line 2313 — the last sentence in this shard's HOME range)

Neither is a mathematical claim: the first is a byte-freeze protocol statement, the second an outstanding certification-protocol step. See the reading note at §8.

The later dated consumption append (lines 2315–2435, outside HOME) advances the append protocol without correcting the frozen mathematics:

> “**WHAT T5 TAKES FROM THIS NOTE IS A FENCE, NOT A THEOREM.** T5 imports S12.1's cumulative hypothesis 𝒲_{≤n} := ⋀_{3≤q≤n}[GENTOW5-W(q)] and carries it on every arrow of its own consequence chain; it takes the *proved* half of S11.2 for a nonvanishing discharge; and it treats S11.2's superseded scope walk as a declared NON-IMPORT.”

Thus T5 is a verified consumer of the conditional fence; the append does not turn the fence into an unconditional theorem.

**INBOUND corrections RECEIVED from suppliers.** This range consumes the landed GENTOW2 r3 B-law at `i = 2`, the accepted GENTOW2-A letter formula at `i = 1`, and HE7 ANNEX R's bound recursion. S11.2 explicitly fences their generalization: the HE7 ride carries `(SLOT_i)/(LIFT_i)` counting content, not the higher-level GENTOW2-B‴ monomial law.

### Freeze predicates

1. **Text freeze:** “THE NOTE IS FROZEN AT THIS RECORD: dated appends and dated brackets only; statement displays and sealed artifacts stay byte-untouched.” Pin: dated acceptance record, lines 1671–1741.
2. **Instrument freeze:** “Sealed machine artifacts BYTE-FROZEN at their committed md5s” (`gentow5_checks.py` `5fa684c7…`, exact output `dc499a49…`, full output `839a8660…`). Fresh md5 verification is recorded in §3.2.
3. **Acceptance-scope enumeration:** the acceptance covers the two TARGET bullets enumerated in §S6, while leaving their named hypotheses and the later `𝒲_{≤n}` fence intact; T5 consumes that fence, not an unconditional higher-rung theorem.

### Resolution rules applied

1. Lines 1475–2313 supply the HOME material: the three repair records (S8/S9/S10), the acceptance record, and the two dated appends (S11, S12) with the post-D3i corrigendum.
2. Appends apply in chronology. Within this range: S8 (2026-08-10) → S9 (2026-08-10) → S10 (2026-08-10) → acceptance record (2026-08-10) → S11 (2026-08-10) → S12 (2026-08-12) → post-D3i corrigendum (2026-08-12).
3. **S12.2 supersedes S11.4**: the `bound_{i+1}` range assertion for the displayed `lift_i(c; m)` is WITHDRAWN and replaced by the `bound_i` threshold. `.28` records S11.4 as superseded; `.35`–`.39` carry the effective statement.
4. **S12.1 supersedes S11.2's unaffected-scope list**: exact values, repo-side residue classes, `P`-membership, clause (c) and clause (e) are NOT unconditional at n ≥ 3. S11.2's *fence itself* (the open lemma) stands.
5. **The post-D3i corrigendum supersedes S12.1's clause-(b) display index**: read `ψ_j^{(ω_j)}` as `ψ_j^{(ω_{j−1})}`.
6. The acceptance record governs status for the whole note: **ACCEPTED 2/2**, annotated (not downgraded) by S11 and S12 — “Grade: ACCEPTED 2/2 stands, ANNOTATED by RUN A” (S11.6); “acceptance 2/2 remains ANNOTATED” (S12 head).
7. Every repair item in S8/S9/S10 lands on a base sentence homed in **shard 1**; those items are emitted here as changes-records (their HOME is this range), and the corrected base statements are inventoried in shard 1. No base statement is re-emitted here.
8. External repo records (the SOL certification ledger, the codex RUN A record, the cert logs) are **reading notes**, never edits — §8.
9. The 2026-08-15 consumption append (lines 2315–2435) is outside HOME and explicitly says “Nothing in this note is corrected by this append”. It nevertheless resolves two perimeter questions: S12.1's withdrawal is **partial**, and certification of the WI companion does not erase `𝒲_{≤n}` from frozen GENTOW5 statements. It also creates reverse consumer edges to T5 (`WF-w`, fixed-string count 16; `I4 — GENTOW5-PE3`, count 2).

---

## 2. Statement inventory

### EFF.GENTOW5.s2of2.01  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** §S8 `[GT5-r2]` PE2 REPAIR RECORD — head

> “PE2 verdict (GENTOW5_passPE2_report.md @ 40f313a): NOT CLEAN — 0 CRITICAL + 2 GAP (PE2-F-1, PE2-F-2) + 2 MINOR (PE2-F-3, PE2-F-4); counter stays 0/2. This section is the r2 repair round; this round's edits are tagged [GT5-r2]. Sealed machine artifacts BYTE-FROZEN at their committed md5s (gentow5_checks.py 5fa684c7..., gentow5_output_exact.txt dc499a49..., gentow5_output_full.txt 839a8660...; the PE1/PE2 fresh instruments live at their own commits, 0160b94 / 40f313a); no runner edited, no re-run.”

**CONDITIONALITY:** Historical. “counter stays 0/2” is superseded by the acceptance record (`.13`).

**DERIVATION:** Round bookkeeping; the mathematical derivations live at the four items below and at the base sentences they repaired (shard 1).

**RESOLUTION TRACE:** Base §S8, lines 1477–1484.

**TEETH:** Byte-freeze assertion on three sealed artifacts (md5 prefixes recorded).

---

### EFF.GENTOW5.s2of2.02  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** PE2-F-1 (GAP) — the `psi^{(w_i)}` re-scope

> “* **PE2-F-1 (GAP) -> RE-SCOPED at S3(a).** THEOREM GENTOW5-B(a) now reads: the pinned recipe realizes R_{nu_i}(Phi_{i+1}) = psi_{i+1}^{(w_i)} := w_i^{f_{i+1}} psi_{i+1}(y/w_i) — the landed GENTOW2 r3 B-law (u_i(beta_t) = theta_i(t) w_i^{f_{i+1}-t}; LEMMA GENTOW2-B [r3 RESTATED] + B'' @ d798529) applied at the S2.1 digits: theta_i(t) = vartheta_{i,f_{i+1}-t}^{-1} cancels the vartheta twist, the w-leg survives. Admissibility at each w_i: B'' + the PE5 verification (GENTOW2_passPE5_report @ 75923bc); GENTOW2-A's hypothesis (ii) quantifier accepts the twisted form — the same re-scope GENTOW2's own S4 consumer took (acdf97a). w_i = 1 stated OPEN (the uncomputed cross-frame unit; verdict-level machine data w-blind). Ripple: the [GT5-r2] consumer walk after S3(e) checks (b)'s cite legs, (b)'s P_{i+1} clause (repo classes; FR-A's psi_3 row), (c)'s repo-side stage read, (d), (e), the S4 witness (w_i = 1 trivially at K_i = F_2), and the sigma/degree/irreducibility data — per consumer; (b) gains the per-level twist rider; the S2.1 FGMN-R-read parenthetical fixed. S7's "consistent both ways" corrected in place to the two-clause statement (the instance leg stands; the no-re-parameterization identification was false at the w-leg).”

**CONDITIONALITY:** The re-scope is unconditional *as a re-scope*; the resulting clause (a) is later fenced at i ≥ 3 (`.25`), corrected at i = 1 (`.27`), and its certificate legs made conditional at n ≥ 3 (`.32`).

**DERIVATION:** The cancellation `theta_i(t) = vartheta_{i,f_{i+1}-t}^{-1}` applied to the landed B-law at the pinned digits; the full computation is quoted in shard 1's clause-(a) unit.

**RESOLUTION TRACE:** Base §S8, lines 1486–1506; lands on shard 1's clause (a), its consumer walk, and §S7's F-2 bullet.

**SUPERSESSION KIND:** scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.27` (clause (a)) and `EFF.GENTOW5.s1of2.32` (consumer walk).

**CHAIN:** on-the-nose `psi_{i+1}` → `[GT5-r2] psi_{i+1}^{(w_i)}` → S11.3 **TERMINAL for i=1** (`psi_2^{(u1)}`, tie open); landed GENTOW2 law **TERMINAL for i=2**; S11.2/S12.1 **TERMINAL for i≥3** (conditional on `𝒲_{≤i}`).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B` — grep-verified count **32**; and `[r3 RESTATED]` — grep-verified count **1**. **Composite check:** the composite designation as GENTOW5 writes it, `LEMMA GENTOW2-B [r3 RESTATED]`, has count **0** in GENTOW2_PROOF; both components verify and the referent is unique, so the composite is recorded as GENTOW5's own compression, not an invented designation.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` — grep-verified count **11** (Unicode double prime; the ASCII `LEMMA GENTOW2-B''` has count **1** there).

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:THEOREM GENTOW2-A` — grep-verified count **8**; its hypothesis-(ii) quantifier is the admissibility consumer named by this repair.

XREF: `lean/notes/openmath/GENTOW2_passPE5_report.md:verifiably admissible` — grep-verified count **1**. The report's line 10 reads “algebra and ψ₃^{(w)} is verifiably admissible for every w ∈ K₂^×”; GENTOW5's `psi_3^{(w)} is verifiably admissible for every w in K_2^x` is the ASCII transliteration of that sentence.

**TEETH:** FR-A (`gentow5_pe2_fresh.py` @ 40f313a, 22/0) for the repo-side `psi_3` class; GENTOW2 PE5 @ 75923bc for admissibility.

---

### EFF.GENTOW5.s2of2.03  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** PE2-F-2 (GAP) — the per-flavor base re-solve

> “* **PE2-F-2 (GAP) -> CORRECTED at S2.1's lift display.** lift_i(c; m) re-displayed as the per-flavor base re-solve: flavor monomials M_{r,t}(m) = nhat_i(m - Delta(r,t)) * (step monomial), derived from LEMMA GENTOW5-C's class separation (flavor residues = the tau_i-cocycle letter units; inverse-twisted digits). Verified at FR-A's numbers: the fixed-base t_1 = 1 flavor at m = 14 demands pi-exponent 11/2 — no monomial; the re-solved member 3^5*x*Phi_1 = FR-A's khat_0. Machine row FA1-LIFT (gentow5_pe2_fresh.py @ 40f313a, 22/0). Ripple pins: heights and deg < D_i unchanged (khat_t + S2.4 read heights only); GENTOW1 S3's fixed-base reading flagged for that note's own arc, not consumed here.”

**CONDITIONALITY:** The corrected display's own height range is settled later, at `.35` (`m > bound_i`).

**DERIVATION:** Class separation (LEMMA GENTOW5-C step (3)) plus the FR-A numerical falsification of the fixed-base display.

**RESOLUTION TRACE:** Base §S8, lines 1507–1518; lands on shard 1's K_i-digit-lift unit.

**SUPERSESSION KIND:** replacement.

**TARGETS:** `EFF.GENTOW5.s1of2.17`.

**CHAIN:** fixed-base flavor display → `[GT5-r2]` per-flavor base re-solve → S11.4 `m > bound_{i+1}` → **S12.2 `m > bound_i` TERMINAL**.

**TEETH:** `FA1-LIFT` (22/0) — asserts the fixed-base flavor's non-existence AND runs the re-solved member.

---

### EFF.GENTOW5.s2of2.04  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** PE2-F-3 (MINOR) — the i = 1 edge of LEMMA GENTOW5-D

> “* **PE2-F-3 (MINOR) -> STATED at S2.4.** The i = 1 edge: the x-carry IS the top carry (j = 0 = i-1), key-part Phi_1 PRESERVED at E_1 = D_1 h = wt_1(x^{D_1}); the rung range 1..i-1 is EMPTY there; the strict clause now reads "the x-carry when i >= 2". Unconsumed edge (named consumers at i >= 2).”

**CONDITIONALITY:** Declared unconsumed: the named consumers instantiate i ≥ 2.

**DERIVATION:** At i = 1 the only reduction move is the x-carry, and `wt_1(Phi_1) = E_1 = D_1 h = wt_1(x^{D_1})`, so no strictness is available and no floor rung is consumed.

**RESOLUTION TRACE:** Base §S8, lines 1519–1523; lands on shard 1's LEMMA GENTOW5-D unit.

**SUPERSESSION KIND:** scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.25`.

**CHAIN:** blanket strictness → `[GT5-r1]` interior-only strictness/top preservation → **`[GT5-r2]` i=1 top-carry edge TERMINAL for the i=1 consumer class**; S11.1 later governs converse rewriting.

**TEETH:** Covered by the S7 F-3 grid equality fence; no dedicated row.

---

### EFF.GENTOW5.s2of2.05  [open-obligation]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** PE2-F-4 (MINOR) — the compound coverage row

> “* **PE2-F-4 (MINOR) -> NAMED at S6's coverage box.** The compound seam-live x e_stage >= 2: the existing seam-live rows (FR-1, FR-A) are e-trivial at the live stage and the committed battery is seam-blind, so the compound has no machine contact in the program's committed rows — honest uncovered row; proof-side uniform (S2.3 step (3)).”

**CONDITIONALITY:** Machine-side coverage gap only; the proof is asserted uniform in `e_{i+1}`.

**DERIVATION:** Coverage audit of the committed rows against the (letter-live × e_stage) axes.

**RESOLUTION TRACE:** Base §S8, lines 1524–1529; lands on shard 1's coverage-box unit.

**SUPERSESSION KIND:** inventory completion.

**TARGETS:** `EFF.GENTOW5.s1of2.40`.

**CHAIN:** seam-axis coverage inventory → **compound `(vartheta live × e_stage≥2)` row added TERMINAL**; no committed battery row supplies it.

**TEETH:** This IS a teeth-coverage record: the named gap has NO committed row.

---

### EFF.GENTOW5.s2of2.06  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** §S9 `[GT5-r3]` PE3 REPAIR RECORD — head

> “PE3 verdict (GENTOW5_passPE3_report.md @ 39c36aa): NOT CLEAN — 0 CRITICAL + 1 GAP (PE3-F-1) + 2 MINOR (PE3-F-2, PE3-F-3); counter stays 0/2. This section is the r3 repair round; this round's edits are tagged [GT5-r3]. Sealed machine artifacts BYTE-FROZEN, md5s re-verified this round (gentow5_checks.py 5fa684c7..., gentow5_output_exact.txt dc499a49..., gentow5_output_full.txt 839a8660...; the PE1/PE2/PE3 fresh instruments live at their own commits, 0160b94 / 40f313a / 9f0eca7); no runner edited, no re-run.”

**CONDITIONALITY:** Historical; counter superseded at `.13`.

**DERIVATION:** Round bookkeeping.

**RESOLUTION TRACE:** Base §S9, lines 1537–1544.

**TEETH:** md5 re-verification of the three sealed artifacts.

---

### EFF.GENTOW5.s2of2.07  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** PE3-F-1 (GAP) — clause (c)'s entry read RE-INDEXED, with the refutation of the composed pairing

> “* **PE3-F-1 (GAP) -> RE-INDEXED at S3(c).** The entry-read clause is RE-DERIVED as the uniform GENTOW-1 transport 2 -> i+1: the template (GENTOW1_PROOF S2, re-read at source this round) anchors its read one level BELOW the key with all stage data the KEY'S OWN (level-1 read, kappa_2 = u_2/e_2, psi_2^{mu2}, box vs Phi_2^{mu2} at mu2*E_2+1, pins (mu2-j)E_2+1, floor dv_2(Phi_2) > E_2), so T_{i+1}'s read clause is "level-i stage read, slope kappa_{i+1}, residual psi_{i+1}^{mu}" — the anchoring the display's degree/weight/pin/floor half already had; GENTOW-1 is the i = 1 instance verbatim. The composed (i+2)-read pairing is killed by the residual-degree count (level-(i+1) polygon length mu, full kappa_{i+2}-side residual degree mu/e_{i+2} vs deg psi_{i+2}^{mu} = mu*f_{i+2}: forces l_{i+2} = 1, improper) and refuted at the committed P-B3 rows f32@Phi4 (pins [682,inf,0]: kappa_5-side, residual degree 1 = psi_5, box 341 = 2E_4+1 holds) and Phi4@Phi3 (pins [170,inf,0]: same shape, box 85 = 2E_3+1).”

> “The corrected pairing VERIFIES at both committed witnesses, re-derived by hand this round from the digit expansions f32 = Phi_3^4 - 512 Phi_2 Phi_3^2 - 2^16 Phi_3 + 2^16 Phi_2^2 and Phi_4 = Phi_2^4 - 32 Phi_1 Phi_2^2 + 1024x (after Phi_1^2 = Phi_2 + 4x) … : f32@Phi3 (pins [340,inf,186,inf,0]: one kappa_4-side, j=2 digit 186 strictly above the chord 170, on-chord support {0,4}, residual y^2+1 = (y-1)^2 = psi_4^2 in F_2) and Phi4@Phi2 (pins [84,inf,50,inf,0]: one kappa_3-side, support {0,4}, residual psi_3^2) — LHS and RHS both hold at each.”

> “Proof side: the (c)-proof's substitution table entry "E_{i+1} -> E_{i+2}" resolved to E_{i+2} and the Step-2 parenthetical re-anchored — the step displays sit uniformly at the entered stage Phi_{i+2} and prove the corrected (c) at index i+1, consuming (b) at Phi_{i+2} + (SLOT_{i+1}) (step-(i+1) data of the same induction); with the index-1 base, indices 1..r-1 are covered. Consumers re-verified: (e) consumes the pins + box at E_{i+1} (the sound half) and its conclusion u_{i+2} > e_{i+2}E_{i+1} matches DEF GENTOW5-1's floor-chain provenance one index down; (d) is self-contained (GENTOW5-A's pattern); the S4 witness consumes (b)+(e); no sentence in the note consumes the retired (i+2)-read pairing.”

**Embedded rider (post-PE4, PE4-F-2) correcting this record's own display:**

> “[rider (post-PE4, 2026-08-10; PE4-F-2): the f32 display above is a true identity but HALFWAY reduced — its constant slot 2^16 Phi_2^2 has degree 8 = deg Phi_3, not a legal Phi_3-adic digit. Completing with the key relation Phi_2^2 = Phi_3 + 16 Phi_1 (the Phi_3-analogue of the Phi_1^2 = Phi_2 + 4x parenthetical) rewrites 2^16 Phi_2^2 = 2^16 Phi_3 + 2^20 Phi_1, and the +2^16 Phi_3 term CANCELS the -2^16 Phi_3 term: the CANONICAL dev is f32 = Phi_3^4 - 512 Phi_2 Phi_3^2 + 2^20 Phi_1, slots C_3 = C_1 = 0 (the quoted p_1 = p_3 = inf) and C_0 = 2^20 Phi_1 at dv_4 = 16*(20 + 5/4) = 340. Re-derived and machine-checked this fold by exact integer polynomial arithmetic (gentow5_rider_f32dev.py: halfway identity TRUE, completion relation exact, canonical slot degrees (4, 2) < 8, pins reproduced against the committed artifact row "f32@Phi3: pins [340, 'inf', 186, 'inf', 0]", gentow5_output_exact.txt byte-frozen at dc499a49). Conclusions invariant: one kappa_4-side, on-chord support {0,4}, residual psi_4^2, box 341 = 2E_4+1 unchanged.]”

**CONDITIONALITY:** The re-indexing is unconditional (a degree count plus committed rows). The *clause* it repairs is later made conditional at n ≥ 3 by `.32`.

**DERIVATION:** Two independent legs, both quoted: (i) the residual-degree count — a full `kappa_{i+2}`-side of a length-`mu` polygon carries residual degree `mu/e_{i+2}`, while `deg psi_{i+2}^{mu} = mu f_{i+2}`, and equality forces `e_{i+2} f_{i+2} = 1`, excluded by properness; (ii) the committed P-B3 rows, which refute the composed pairing and verify the corrected one.

**RESOLUTION TRACE:** Base §S9, lines 1546–1599, with the post-PE4 `[rider]` inserted inside the display at lines 1566–1583. Lands on shard 1's clause (c) and its proof.

**SUPERSESSION KIND:** replacement plus scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.29`.

**CHAIN:** mixed `(i+2)` read → `[GT5-r3]` uniform `(i+1)` read → S11.1 one-directional Step-2 proof → **S12.1 conditional-on-`𝒲_{≤n}` reading TERMINAL for n≥3**. Inside this record, halfway `f32` development → **post-PE4 canonical development TERMINAL**.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:S2` — grep-verified count **16**; the template re-read at source for the anchoring.

**TEETH:** P-B3 rows `f32@Phi4`, `Phi4@Phi3` (REFUTING) and `f32@Phi3`, `Phi4@Phi2` (VERIFYING); `gentow5_rider_f32dev.py` (7 checks / 0 violations) for the canonical development.

---

### EFF.GENTOW5.s2of2.08  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** PE3-F-2 (MINOR) — the “uncomputed” claims DATED at both flank sites

> “* **PE3-F-2 (MINOR) -> DATED at both flank sites.** One dated bracket each at the S6 TARGET-2 bullet and the (a)-proof parenthetical: w is measured at the 7 measured primes (GENTOW2 PE6's 6 across LD1/LD3/GA1/GA3 + PE3 leg W's carrier-(8,4) prime at GA3*); the w_i = 1-OPEN claims themselves stand (closed-form law + unmeasured frames/levels), per the S3(a) dated note.”

**CONDITIONALITY:** The measurement dates the word “uncomputed”; it does not close `w_i = 1`, and it does not extend to unmeasured frames or to levels i > 2.

**DERIVATION:** Measurement record from GENTOW2 PE6 plus this note's own PE3 fresh leg W.

**RESOLUTION TRACE:** Base §S9, lines 1600–1606; lands on shard 1's clause-(a) dated note and §S6 TARGET-2 bullet.

**SUPERSESSION KIND:** as-of scoping.

**TARGETS:** `EFF.GENTOW5.s1of2.27` and `EFF.GENTOW5.s1of2.38`.

**CHAIN:** “w uncomputed anywhere” → **measured at seven primes, closed-form/unmeasured cases still open TERMINAL**.

XREF: `lean/notes/openmath/GENTOW2_passPE6_report.md:w-avatar` — grep-verified count **6**; the per-frame w measurements.

REVERSE XREF: `lean/notes/openmath/T5_WFRAME_2026-08-12.md:I4 — GENTOW5-PE3` — grep-verified count **2**; the 2026-08-15 append records T5's avatar-coherent consumption of the PE3 seventh-prime row, not an intrinsic upgrade.

**TEETH:** GENTOW2 PE6 fresh route (GREEN 68/0, seal `ade1727`); this note's PE3 fresh leg W (`gentow5_pe3_fresh.py` @ 9f0eca7).

---

### EFF.GENTOW5.s2of2.09  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** PE3-F-3 (MINOR) — the consumer-walk pointer correction

> “* **PE3-F-3 (MINOR) -> POINTER CORRECTED at the consumer walk.** The S4-witness bullet now points the w-triviality record at S6's TARGET-2 [GT5-r2] rider; the coverage box carries the seam axis (S4.1's re-check) and no w row.”

> “Grade: 0/2 UNCHANGED (repair round, not a pass). TARGET 1 (GENTOW5-A/A0/A1) was not at stake at PE3 and is untouched this round; the r2 repairs, the w-note rider, LEMMA GENTOW5-D, and (a)/(b)/(d)/(e) all survived PE3's attack and are untouched beyond the three sites named here.”

**CONDITIONALITY:** Historical; the grade line is superseded at `.13`.

**DERIVATION:** Bookkeeping correction — two records were conflated (w-triviality vs the seam axis) and are separated.

**RESOLUTION TRACE:** Base §S9, lines 1607–1616; lands on shard 1's consumer-walk unit.

**SUPERSESSION KIND:** provenance-rider.

**TARGETS:** `EFF.GENTOW5.s1of2.32`.

**CHAIN:** S4 w-triviality pointer to coverage box → **pointer to S6 TARGET-2 rider TERMINAL**; the coverage box continues to carry the seam axis only.

**TEETH:** NONE (pointer hygiene).

---

### EFF.GENTOW5.s2of2.10  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** §S10 post-PE4 fold — head and PE4-F-1 (index scope of (c)/(e))

> “PE4 verdict (GENTOW5_passPE4_report.md @ b22b37b): CLEAN — 0 CRITICAL + 0 GAP + 2 MINOR; counter 0/2 -> 1/2, the arc's first clean pass. This fold applies the two minors as dated [rider] brackets (no repair round owed; both are display hygiene at the r3 repair's edges, neither moves a conclusion). Both fixes were RE-DERIVED from the note's own lemmas and the committed artifacts, not transcribed from the report.”

> “* **PE4-F-1 (MINOR) -> SCOPED at the statement's (c) clause.** The blanket header "by induction on i < r" left (c)'s index-0 instance (T_1, level-0 read) formally in scope while the r3 coverage sentence names indices 1..r-1. The rider bracket states the honest scope: (c) — and (e), whose proof consumes (c)'s pins at the same index — are claimed at i >= 1 only (entry loci T_2..T_r; base = the index-1 GENTOW-1 instance, steps enter at Phi_{i+2} for i = 1..r-2). Verified at source this fold: DEF GENTOW5-1's floor-chain rung 1 rides the accepted [r1] node floor u_2 > e_2 E_1 = e_2 D'h directly (S2.1's provenance sentence), NOT (e)@index-0; S2.4's Phi_1-part weight bound consumes that same DEF hypothesis; a grep audit (T_1 / kappa_1 / psi_1^mu / level-0 read) found no other sentence instantiating (c) or (e) at index 0. T_1 is left unclaimed rather than cited.”

**CONDITIONALITY:** A scope narrowing, not a weakening of a proved statement: the r3 proof already had this scope; the rider records it.

**DERIVATION:** The induction's own base (GENTOW-1 = index 1) and step structure (steps enter at `Phi_{i+2}`), plus a grep audit for index-0 instantiations.

**RESOLUTION TRACE:** Base §S10, lines 1620–1645; lands on shard 1's clause (c)/(e) scope rider.

**SUPERSESSION KIND:** scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.26`, `EFF.GENTOW5.s1of2.29`, and `EFF.GENTOW5.s1of2.31`.

**CHAIN:** blanket `i<r` → post-PE4 `(c)/(e): i≥1` → **post-PE5 per-clause index set TERMINAL**: `(a),(b),(c),(e): i≥1`; `(d): i≥0`.

**TEETH:** The grep audit is the negative check; PE5's fresh route later instantiates the unclaimed `T_1` TRUE at one frame (`.15`).

---

### EFF.GENTOW5.s2of2.11  [run-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** PE4-F-2 (MINOR) — the canonical f32 development COMPLETED

> “* **PE4-F-2 (MINOR) -> COMPLETED at S9's f32 display.** The displayed f32 digit expansion was a true identity but halfway reduced (constant slot 2^16 Phi_2^2 of degree 8 = deg Phi_3 — not a legal Phi_3-adic digit). Re-derived this fold: Phi_2^2 = Phi_3 + 16 Phi_1 (the defining relation of Phi_3) completes the reduction and the resulting +2^16 Phi_3 cancels the -2^16 Phi_3 term, giving the canonical dev f32 = Phi_3^4 - 512 Phi_2 Phi_3^2 + 2^20 Phi_1 (C_3 = C_1 = 0, C_0 at dv_4 = 340). Machine leg (new helper, committed this fold): gentow5_rider_f32dev.py — exact integer polynomial arithmetic, 7 checks / 0 violations: halfway identity, completion relation, canonical dev, slot legality (degrees 4, 2 < 8), pins (340, inf, 186, inf, 0) = the committed artifact row f32@Phi3 (gentow5_output_exact.txt, byte-frozen at dc499a49), strict j = 2 chord clearance (186 > 170), and the Phi_4@Phi_2 display confirmed already-canonical. Conclusions invariant: one kappa_4-side, on-chord support {0,4}, residual psi_4^2, box 341 = 2E_4+1.”

**CONDITIONALITY:** Display hygiene inside a repair record; conclusions explicitly invariant.

**DERIVATION:** The key relation `Phi_2^2 = Phi_3 + 16 Phi_1` completes the Phi_3-adic reduction; the cancellation of `±2^16 Phi_3` is exact; all seven legs machine-checked.

**RESOLUTION TRACE:** Base §S10, lines 1646–1663; lands inside `.07`'s display (the rider is quoted there in place).

**SUPERSESSION KIND:** replacement.

**TARGETS:** `EFF.GENTOW5.s2of2.07`'s halfway-reduced `f32` display.

**CHAIN:** halfway reduction with illegal constant slot → **canonical `Phi_3`-adic development TERMINAL**.

**TEETH:** `gentow5_rider_f32dev.py` — 7 checks / 0 violations, cross-checked against the byte-frozen artifact row.

---

### EFF.GENTOW5.s2of2.12  [fence]

**FORM:** inline sentence

**CANONICAL STATEMENT:** §S10 grade line and statement fence

> “Grade after this fold: counter 1/2 (PE4's verdict; a rider is not a pass). The statement fence: no theorem statement weakened — the PE4-F-1 bracket records the scope the r3 proof already had; the PE4-F-2 bracket corrects a display inside a repair record. PE5 next.”

**CONDITIONALITY:** Historical counter, superseded at `.13`. The statement fence itself is the note's own no-weakening declaration for this fold.

**DERIVATION:** Declaration, with per-bracket justification quoted.

**RESOLUTION TRACE:** Base §S10, lines 1665–1669.

**TEETH:** NONE (declaration).

---

### EFF.GENTOW5.s2of2.13  [acceptance-box]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** Dated acceptance record (2026-08-10, post-PE5)

> “**GENTOW5 IS ACCEPTED 2/2** — passPE4 CLEAN (0 CRITICAL + 0 GAP + 2 MINOR, GENTOW5_passPE4_report.md @ b22b37b; counter 0/2 -> 1/2) followed by passPE5 CLEAN (0 CRITICAL + 0 GAP + 3 MINOR, GENTOW5_passPE5_report.md @ 18900e03; counter 1/2 -> 2/2): two consecutive clean hostile passes, the standing acceptance bar.
> **THE NOTE IS FROZEN AT THIS RECORD: dated appends and dated brackets only; statement displays and sealed artifacts stay byte-untouched.**”

> “Grade after this record: **ACCEPTED 2/2**. Dated appends only beyond this line.”

**CONDITIONALITY:** Acceptance is a *process* verdict (two consecutive clean hostile passes), not a discharge of the note's named conditionality stack. It is later ANNOTATED — not downgraded — by S11 (“Grade: ACCEPTED 2/2 stands, ANNOTATED by RUN A”) and S12 (“acceptance 2/2 remains ANNOTATED”).

**DERIVATION:** The standing acceptance bar applied to the arc's counter.

**RESOLUTION TRACE:** Base lines 1671–1741. This record governs STATUS for the whole note, including every earlier “grade 0/2 / counter stays 0/2 / PEn next” sentence in shard 1's range.

**SUPERSESSION KIND:** as-of scoping (status only).

**TARGETS:** `EFF.GENTOW5.s2of2.01`, `EFF.GENTOW5.s2of2.06`, `EFF.GENTOW5.s2of2.12`, `EFF.GENTOW5.s1of2.01`, `EFF.GENTOW5.s1of2.13`, `EFF.GENTOW5.s1of2.38`, and `EFF.GENTOW5.s1of2.43`.

**CHAIN:** grade/counter 0/2 → PE4 counter 1/2 → **post-PE5 ACCEPTED 2/2 TERMINAL (status consumer)**; S11/S12 annotate but do not downgrade it.

**TEETH:** The two clean passes are the teeth of record; the byte-freeze is verified by the ledger at `.16`.

---

### EFF.GENTOW5.s2of2.14  [changes-record]

**FORM:** inline sentence

**CANONICAL STATEMENT:** The arc in one breath

> “The arc in one breath: seal (2026-08-09) -> PE1 (1C+2G+3m) -> r1 (the GAUGE PIN: vartheta-twisted khat_t, machine-caught at the letter-live FR-1) -> PE2 (0C+2G+2m) -> r2 (the psi^{(w_i)} re-scope on the landed GENTOW2 r3 B-law + the per-flavor lift re-solve) -> PE3 (0C+1G+2m) -> r3 (the (c) entry-read RE-INDEXED to the uniform GENTOW-1 transport; the composed (i+2)-pairing killed by the residual-degree count and at committed rows) -> PE4 CLEAN (2 minors; counter 1/2) -> rider (both minors folded; f32 canonical dev machine-checked 7/7) -> PE5 CLEAN (3 minors; counter 2/2 — the (c) <-> GENTOW-1 seam adjudicated BINDING at the post-R2a/b/c GENTOW1 HEAD 4caf0fb; fresh route GREEN 40/0 with the first mu = 3 (c)-read anywhere and the first odd-p proper-(2,2) mid-stage tower at depths 3 and 4).”

**CONDITIONALITY:** Chronology only.

**DERIVATION:** Summary of the arc; each leg's derivation lives at its repair record.

**RESOLUTION TRACE:** Base lines 1682–1694.

**TEETH:** PE5 fresh route GREEN 40/0 (first mu = 3 (c)-read; first odd-p proper-(2,2) mid-stage tower at depths 3 and 4).

---

### EFF.GENTOW5.s2of2.15  [changes-record]

**FORM:** inline sentence

**CANONICAL STATEMENT:** The companion fold — PE5-F-1, PE5-F-2, PE5-F-3

> “This append's companion fold (commit "GENTOW5 dated acceptance record (commit 1/2)") folded PE5's three MINORs at source as dated [acceptance fold] brackets, each RE-DERIVED from the note's own lemmas and the primary sources, not transcribed from the report:
> * PE5-F-1 -> the S3 statement header gains the INDEX-0 SCOPE bracket, completing the post-PE4 rider's (c)/(e) scoping to the clause list (a)/(b)/(d): (a)/(b) are claimed at i >= 1 ((a)@0's display dereferences nhat_0, not a DEF object — the index-0 content is the accepted chain data, T(b)' setting + GENTOW2 S2 dictionary; (b)@0 reduces to the j = 1 leg, the same accepted datum); (d)@0 IS claimed, via S1.4(ii)'s level-1 rider; Phi_1 is named the DEF-datum (recipe-built keys = Phi_2, ..., Phi_r); T_1 stays unclaimed, with PE5's fresh TRUE instantiation (f4 over p = 5) recorded in the conservative direction.
> * PE5-F-2 -> the (B-2) discharge's level lists gain their i = 1 line: the accepted GENTOW2-A(c) letter-formula content, verified at source this fold (GENTOW2_PROOF @ HEAD 33f8620: Cor 5.6(2) + S5.1's LETTER FORMULA z_2 = eta_2 * z_1^{-floor(l_1 u_2/e_1)} + the R3-4 disambiguation fence), with the i = 1 KP-membership leg at Lemma 5.3(1) [Q4] (the GENTOW2 [r1] F4-cure); an exponent-level tie of the w_1 display to the letter formula is NOT claimed.
> * PE5-F-3 -> S2.3's (LIFT_i) bound recursion's truncated token restored: e_{i+1}*bound_i, re-derived from ANNEX-THEOREM R1-c's displayed recursion plus the lemma's own step-(1) height split (grep-scoped: no numeric bound_i consumer in the note).”

**CONDITIONALITY:** PE5-F-2's closing disclaimer (“an exponent-level tie of the w_1 display to the letter formula is NOT claimed”) is what S11.3 later promotes into a statement correction (`.27`).

**DERIVATION:** Each fold is re-derived at the primary source, not transcribed — the note states this explicitly and names the source HEADs it re-read (`33f8620` for GENTOW2).

**RESOLUTION TRACE:** Base lines 1696–1724; the three brackets themselves are landed inside shard 1's range (S3 header, S3(a)'s (B-2) leg, S2.3's bound display) and are inventoried there.

**SUPERSESSION KIND:** scope-pin (PE5-F-1), provenance-rider (PE5-F-2), and replacement (PE5-F-3).

**TARGETS:** `EFF.GENTOW5.s1of2.26`, `EFF.GENTOW5.s1of2.27`, and `EFF.GENTOW5.s1of2.22`.

**CHAIN:** blanket index scope → **per-clause index scope TERMINAL**; silent i=1 B-2 line → **accepted letter-formula species with exponent-level tie unclaimed TERMINAL**; `e...*bound_i` → **`e_{i+1}*bound_i` TERMINAL**.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Cor 5.6` — grep-verified count **6**.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.1` — grep-verified count **42**; the LETTER FORMULA's home.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q4]` — grep-verified count **5**; Lemma 5.3(1), the KP-membership leg.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` — grep-verified count **3**; the bound recursion's primary source.

**TEETH:** PE5 fresh route (GREEN 40/0), which instantiates `T_1` TRUE at `f4 = Phi_1^2 - 25x` over `p = 5`.

---

### EFF.GENTOW5.s2of2.16  [changes-record]

**FORM:** inline sentence

**CANONICAL STATEMENT:** BYTE-FREEZE LEDGER (acceptance round)

> “BYTE-FREEZE LEDGER (this round): pre-fold body md5 85efc5b4 (85efc5b445aa2d738301338c6075e118; 1,592 lines, 90,017 bytes) = the rider state @ cc7c944; the three fold brackets landed insertions-only (+77/-0; prefix through the first insertion byte-identical, md5 e9c5a20d at L561; commit a803a2ce), giving post-fold body md5 4292d8c8 (4292d8c86d58389ce91d38cb2aa759b7; 1,669 lines, 94,765 bytes); this record is a PURE APPEND on that body, verified by prefix md5 after the append. Sealed artifacts byte-frozen, md5s re-verified this round: gentow5_checks.py 5fa684c7..., gentow5_output_exact.txt dc499a49..., gentow5_output_full.txt 839a8660...; the rider helper gentow5_rider_f32dev.py 81bbb5db... untouched; no runner edited, no re-run.”

**CONDITIONALITY:** Protocol record. The md5s are of the note body and the artifacts at that round, not of the current HEAD state (the note has since grown by S11 and S12).

**DERIVATION:** Prefix-md5 verification of an insertions-only edit plus a pure append.

**RESOLUTION TRACE:** Base lines 1726–1738.

**TEETH:** The prefix-md5 discipline is itself the tooth: `+77/-0`, prefix byte-identical at L561.

---

### EFF.GENTOW5.s2of2.17  [scope-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** §S11 `[GT5-r4]` — head, provenance and supersession discipline

> “## S11. [GT5-r4] CODEX TOWERRAT2 RUN A REPAIRS (2026-08-10 — dated append; acceptance 2/2 stands ANNOTATED, per the batch charter)”

> “Provenance: decorrelated-model adversarial RUN A (record CODEX_TOWERRAT2_2026-08-10.md S2 @ eeac45f6; raw log verification/openmath/towerrat2_runA_gentow5_output.txt), adjudicated 5/5 REAL (1 CRITICAL A-F1 + 2 GAP A-F2/A-F3 + 2 display MINOR A-F4/A-F5). Every correction below is RE-DERIVED from this note's own displays and the committed artifacts, not transcribed from the verifier. The note is frozen: these are dated corrections BY SUPERSESSION — the superseded sentences are quoted, stay byte-intact above, and read as corrected here. Pure-append discipline: the ledger at S11.6 carries the per-commit prefix md5s.”

**CONDITIONALITY:** The append annotates, it does not downgrade: “acceptance 2/2 stands ANNOTATED”.

**DERIVATION:** Adjudication of an external adversarial run; 5/5 findings judged REAL, each repaired from the note's own displays.

**RESOLUTION TRACE:** Base §S11 head, lines 1743–1755.

XREF: `lean/notes/openmath/CODEX_TOWERRAT2_2026-08-10.md:A-F1` — grep-verified count **3**; and `A-F2` — count **2**. The record's GENTOW5 section is `S2` (count **6** in that file; `GENTOW5` appears **12** times).

**READING NOTE:** the raw log `verification/openmath/towerrat2_runA_gentow5_output.txt` exists in the repo (checked).

**TEETH:** The decorrelated-model run itself; its per-finding machine legs are at `.18`.

---

### EFF.GENTOW5.s2of2.18  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.1 `[A-F1, CRITICAL]` — the converse-rewriting direction CORRECTED

**Superseded sentences (quoted by the note itself):**

> “**Superseded sentences (quoted).** S2.4's proof close: "The converse rewriting (Phi_{j+1} = Phi_j^{l_{j+1}} - weight-E_{j+1} lifts) is weight-nondecreasing by the same displays." — FALSE as written. And the statement's consequence clause: "Hence 'all slots at weight >= W' is the same condition on every grid of the tower (the two-directional rewriting closes)" — WITHDRAWN to the one-directional form below.”

**The corrected statement:**

> “**The corrected direction (from S2.4's own displays).** The converse rewriting replaces the single slot Phi_{j+1} — priced (ehat_i/ehat_{j+2})u_{j+2} at an interior rung (j+1 <= i-1), E_i at the top rung (j+1 = i) — by the slots {Phi_j^{l_{j+1}}, khat_t Phi_j^{e_{j+1}t}}, all of which the Phi_j-carry display prices at (ehat_i/ehat_{j+1})E_{j+1} exactly. Hence the converse rewriting is weight-NONINCREASING: preserved exactly at the top rung (the lemma's own worked grid-4 instance Phi_4 = Phi_3^2 - 2^8 Phi_2, three slots at 170), and STRICTLY LOWERED at each interior rung by floor rung j+1 ((ehat_i/ehat_{j+2})u_{j+2} > (ehat_i/ehat_{j+1})E_{j+1}) — the same rung that makes the forward key-part strict.”

**CONDITIONALITY:** Consumes only the S2.4 displays and the floor chain — no new input. The LEMMA GENTOW5-D *statement* is explicitly untouched (see `.19`).

**DERIVATION:** [ASSEMBLED — the note's own pricing comparison, quoted above, plus its worked witness instance]

> “Witness instance (S4.1 chain, ehat_i = 2^i, E_3 = 42; committed ladder @ dc499a49): grid i = 4, interior rung j+1 = 3: Phi_3 = Phi_2^2 - 16 Phi_1 trades wt_4(Phi_3) = u_4 = 85 for wt_4(Phi_2^2) = 2*2*21 = 84 and wt_4(16 Phi_1) = 64 + 20 = 84 = (ehat_4/ehat_3)E_3; the drop 85 -> 84 is floor rung 3's tight margin (u_4 = 85 > e_4 E_3 = 84). Machine leg (ISOLATED repair-round re-check, not a sealed battery): gentow5_af1_direction_check.py — GREEN, 8 checks 0 violations (C1 rung, C2 the 85 -> 84 drop, C3 the 170 top-rung preservation, C4 forward nondecreasing, C5 the exact Z[x] identity + canonical Phi_1-adic development of Phi_3, C6 its level-1 polygon/descmin, C7 the rho-ladder, C8 the margin instance); md5s at S11.6.”

**RESOLUTION TRACE:** Base §S11.1, lines 1757–1789. Supersedes two sentences homed in shard 1 (LEMMA GENTOW5-D's consequence clause and its proof's closing sentence).

**SUPERSESSION KIND:** partial-withdrawal; replacement direction attached.

**TARGETS:** `EFF.GENTOW5.s1of2.25`.

**CHAIN:** two-directional weight-nondecreasing closure → **forward nondecreasing + converse nonincreasing replacement TERMINAL**; the top-rung converse survives as equality.

**READING NOTE:** the isolated instrument `verification/openmath/gentow5_af1_direction_check.py` and its output file both exist in the repo (checked).

**TEETH:** `gentow5_af1_direction_check.py` — 8 checks / 0 violations, explicitly flagged as an isolated re-check, NOT part of the sealed battery.

---

### EFF.GENTOW5.s2of2.19  [fence]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.1 — what survives (one-directional)

> “**What survives (one-directional).** The lemma's STATEMENT is untouched: forward carry moves are wt_i-nondecreasing, so "all slots at weight >= W" propagates from a representation to its carry-reductions (the canonical direction). One true remnant of the withdrawn closure, used below: the SINGLE-STEP converse at the TOP rung (expanding only Phi_i = Phi_{i-1}^{l_i} - lifts, i.e. the grid-i <-> level-(i-1)-read translation) preserves slot weights exactly — that is the top-rung display read backwards, no floor rung consumed.”

**CONDITIONALITY:** The surviving converse is single-step and top-rung only; interior descent is not available.

**DERIVATION:** The top-rung display of LEMMA GENTOW5-D read backwards — an equality, hence direction-independent.

**RESOLUTION TRACE:** Base §S11.1, lines 1791–1799.

**SUPERSESSION KIND:** partial-withdrawal.

**TARGETS:** `EFF.GENTOW5.s1of2.25`.

**CHAIN:** two-directional closure → **forward propagation plus top-rung-only converse TERMINAL**; interior converse propagation is withdrawn.

**NON-IMPORT (explicit):** the two-directional grid closure is withdrawn; “no two-directional grid agreement is consumed anywhere in the repaired chain” (S11.1.3).

**TEETH:** `gentow5_af1_direction_check.py` C3 (top-rung preservation at 170) and C4 (forward nondecreasing).

---

### EFF.GENTOW5.s2of2.20  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.1 — consumption walk (the charged sites, re-audited)

> “**Consumption walk (the charged sites, re-audited).**
> * S2.4's consumer note ("nondecreasing is all any named consumer uses") — VERIFIED at GENTOW5-A Step B, S3(c) Steps 0/3, S3(d): each consumes forward reduction and/or (SLOT)-exactness. S3(c) Step 3's necessity leg reads the ENTERED level-(i+1) read against grid-(i+2) slots: that translation expands Phi_{i+2} only — the top rung, weight-preserving (the true remnant), not interior descent.
> * S3(c) Step 1 — SURVIVES: Phi_{i+2}^mu's slots at weight >= mu E_{i+2} come from reducing the mu-fold recipe product by FORWARD carries from side terms at E_{i+2} exactly.
> * S3(c) Step 2's parenthetical "(g strictly above, by GENTOW5-D both grids agree on 'above')" — THE BROKEN CONSUMPTION (the deeper reads at level j <= i sit across interior rungs, where the grids do NOT agree). Superseded by the derivation S11.1.1-S11.1.3; the ladder's conclusion stands on the new route.”

**CONDITIONALITY:** Exactly one consumer is broken; the other three survive with reasons given.

**DERIVATION:** Site-by-site audit against the corrected direction.

**RESOLUTION TRACE:** Base §S11.1, lines 1801–1816. Lands on shard 1's GENTOW5-A Step B, clause (c) Steps 0/1/2/3 and clause (d).

**SUPERSESSION KIND:** replacement (consumer-sweep vehicle).

**TARGETS:** `EFF.GENTOW5.s1of2.10`, `EFF.GENTOW5.s1of2.29`, and `EFF.GENTOW5.s1of2.30`.

**CHAIN:** broken “both grids agree” Step-2 consumption → **S11.1.1–S11.1.3 one-directional derivation TERMINAL**; the other named consumers keep their forward/top-rung readings.

**TEETH:** The grep audit recorded at S11.1's honest residue (`.24`).

---

### EFF.GENTOW5.s2of2.21  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.1.1 (descent floor)

> “**S11.1.1 (descent floor).** Fix the ladder rung j and write L_k := l_{j+1}...l_k (L_j := 1), lam := (ehat_j/ehat_{j+1})u_{j+1}. For j < k <= i+2, clause (b) at index k-1 ((b)@(i+1) is proved before (c) inside the same induction step; k-1 <= i is induction data) plus (SLOT_{j-1})-exactness give: the level-j polygon of Phi_k is one-sided from (0, L_k lam) to (L_k, 0), and since each pin is the slot-min of that coefficient, every slot of the canonical Phi_j-adic development of Phi_k satisfies
>
>     (slot weight of the coefficient part) + m*lam >= L_k * lam,
>
> with equality at the monic leading slot ("descmin(Phi_k) = L_k lam"). Here coefficient parts are grid-(j-1) monomials, priced exactly at level-j points; witness instance: Phi_3's level-1 read Phi_1^4 - 8x Phi_1^2 - 16 Phi_1 + 16 x^2, pins (10, 8, 7, -, 0), descmin = 10 = L_3 lam (re-check C5/C6).”

**CONDITIONALITY:** Consumes clause (b) at index k−1 and `(SLOT_{j-1})`-exactness. Because it consumes (b), S12.1 places it inside the `𝒲_{≤n}` chain at n ≥ 3 (`.32` item 3).

**DERIVATION:** One-sidedness from (b) plus pin-as-slot-min from (SLOT), giving the displayed inequality with equality at the monic leading slot; the witness instance is the level-1 read of `Phi_3` with its pins.

**RESOLUTION TRACE:** Base §S11.1.1, lines 1818–1833; conditionality set by S12.1 item 3.

**SUPERSESSION KIND:** replacement (proof replacement component).

**TARGETS:** `EFF.GENTOW5.s1of2.29`'s broken Step-2 parenthetical.

**CHAIN:** two-directional grid-agreement proof → S11.1.1 descent floor → S11.1.3 aboveness → **S12.1 conditional proof TERMINAL for n≥3**.

**TEETH:** `gentow5_af1_direction_check.py` C5 (exact `Z[x]` identity + canonical `Phi_1`-adic development of `Phi_3`) and C6 (its level-1 polygon/descmin).

---

### EFF.GENTOW5.s2of2.22  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.1.2 (the rho-ladder = the floor chain)

> “**S11.1.2 (the rho-ladder = the floor chain).** Scale the box's weight functional to level j: price\*(Phi_k) := (ehat_j/ehat_{k+1})u_{k+1} for j <= k <= i+1 and price\*(Phi_{i+2}) := (ehat_j/ehat_{i+2})E_{i+2} (wt_{i+2}'s own top price, scaled); x, pi, and Phi_k with k < j at their exact dv_j prices. Set rho_k := price\*(Phi_k)/L_k - lam. Then rho_j = 0, and
>
>     rho_k < rho_{k+1} (j <= k <= i)  <=>  u_{k+2} > e_{k+2}E_{k+1}
>                                           (floor rung k+1);
>     rho_{i+2} = rho_{i+1}            (E_{i+2} = l_{i+2}u_{i+2}: the
>                                       top price per Phi_j-degree IS
>                                       the deepest interior one).
>
> So rho\* := rho_{i+2} = max_k rho_k, consuming floor rungs j+1..i+1 — in-datum. Witness (j = 1, entered stage 3): rho = (0, 1/8, 1/8), strictness at rung 2 (21 > 20) — re-check C7.”

**CONDITIONALITY:** Unconditional floor arithmetic — S12.1 says so explicitly: “The numerical \(\rho\)-ladder of S11.1.2 is unconditional floor arithmetic”.

**DERIVATION:** The equivalence `rho_k < rho_{k+1} ⟺ u_{k+2} > e_{k+2}E_{k+1}` is the floor rung restated after scaling; the top equality is `E_{i+2} = l_{i+2}u_{i+2}`.

**RESOLUTION TRACE:** Base §S11.1.2, lines 1835–1850.

**SUPERSESSION KIND:** replacement (proof replacement component).

**TARGETS:** `EFF.GENTOW5.s1of2.29`'s broken Step-2 parenthetical.

**CHAIN:** two-directional grid-agreement proof → **numerical `rho`-ladder replacement TERMINAL and unconditional**; only the surrounding descent-floor/aboveness legs acquire `𝒲_{≤n}`.

**TEETH:** `gentow5_af1_direction_check.py` C7 (the rho-ladder), witness `rho = (0, 1/8, 1/8)`.

---

### EFF.GENTOW5.s2of2.23  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.1.3 (Step 2's aboveness, one-directional)

> “**S11.1.3 (Step 2's aboveness, one-directional).** Let T be a grid-(i+2) slot of g (the (c) box: wt_{i+2}(T) >= mu E_{i+2} + 1; scaled, wt\*(T) >= mu L_{i+2}(lam + rho\*) + ehat_j/ehat_{i+2}). Descend T to canonical Phi_j-adic form: the lam-priced weight is additive on monomial products, each deep factor Phi_k contributes at least L_k lam = price\*(Phi_k) - L_k rho_k (S11.1.1), and the re-reduction of coefficient products to deg < D_j is by grid-j FORWARD carries, nondecreasing also under the lam-pricing (the grid-j top carry prices Phi_j at lam > E_j by floor rung j, in-datum). With deg_j(T) = Sum_k J_k L_k < mu L_{i+2} =: M (from deg g < mu D_{i+2}, D_k = L_k D_j):
>
>     descmin(T) >= wt*(T) - Sum_k J_k L_k rho_k
>                >= wt*(T) - rho* M
>                >= M lam + ehat_j/ehat_{i+2}  >  M lam.
>
> By the ultrametric bound (only a LOWER bound on g's side is consumed), every Phi_j-adic coefficient of g satisfies dv_j(c_m(xi)) > (M - m) lam at xi in P_j: g's level-j pins sit STRICTLY ABOVE Phi_{i+2}^mu's side, whose own pins are (M - m) lam on the side ((b) + the power multiplicativity of Step 1, (SLOT)-exact). The level-j polygon of f = Phi_{i+2}^mu + g therefore carries Phi_{i+2}^mu's side and side residual verbatim — the ladder rung's exact need; the ascent proceeds as written, and no two-directional grid agreement is consumed anywhere in the repaired chain. Margin instance at the witness: 43/4 - 1/2 = 41/4 > 10 (re-check C8).”

**CONDITIONALITY:** Consumes S11.1.1 (hence clause (b)) — so at n ≥ 3 it sits inside the `𝒲_{≤n}` chain (`.32` item 3). Forward direction of LEMMA GENTOW5-D only.

**DERIVATION:** The displayed three-line chain: additivity of the lam-priced weight, the per-factor floor from S11.1.1, the uniform bound by `rho*` from S11.1.2, and the degree bound `deg_j(T) < M`; then the ultrametric comparison against `Phi_{i+2}^mu`'s side.

**RESOLUTION TRACE:** Base §S11.1.3, lines 1852–1878; replaces shard 1's clause-(c) Step 2 parenthetical.

**SUPERSESSION KIND:** replacement (proof replacement component).

**TARGETS:** `EFF.GENTOW5.s1of2.29`'s broken Step-2 parenthetical.

**CHAIN:** “both grids agree on above” → **one-directional `descmin`/ultrametric proof TERMINAL**, conditional on `𝒲_{≤n}` at n≥3.

**TEETH:** `gentow5_af1_direction_check.py` C8 (the margin instance `41/4 > 10`).

---

### EFF.GENTOW5.s2of2.24  [fence]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.1 — honest residue

> “**Honest residue.** The repaired Step 2 consumes (b)@(i+1) before (c)@(i+1) inside the step (the note's stated order), floor rungs j..i+1, (SLOT_{j-1}), and the forward direction of LEMMA GENTOW5-D — nothing outside the note's own pin stack. A grep audit this round ("same condition on every grid", "two-directional", "both grids agree") finds the withdrawn closure consumed at S3(c) Step 2's parenthetical and nowhere else in the body above.”

**CONDITIONALITY:** The audit's scope is the three quoted search strings; it establishes single-site consumption of the withdrawn closure.

**DERIVATION:** Consumption census plus a negative grep audit.

**RESOLUTION TRACE:** Base §S11.1, lines 1880–1886.

**TEETH:** The grep audit is the negative check.

---

### EFF.GENTOW5.s2of2.25  [open-obligation]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.2 `[A-F2, GAP]` — the i ≥ 3 B″-transport FENCED; `[GENTOW5-W(i)]` declared open

**Superseded reading (quoted by the note):**

> “**Superseded reading (quoted).** S3(a)'s (B-2) leg: "at i >= 3 the same derivation transports with (SLOT_i) = LEMMA GENTOW5-C in place of B-1" and "transported to i >= 3 on the same S2.3 annex-precedent ride". As consumption of the MONOMIAL LAW those sentences overclaim: the ride carries (SLOT_i)/(LIFT_i) counting statements, not GENTOW2-B'''s normalizer-cocycle monomial computation.”

**What is proved, per level, and what is not:**

> “**What IS proved, per level (the accepted GENTOW2 consumption-walk shape):**
> * i = 2 — VERBATIM: the landed GENTOW2 r3 B-law (LEMMA GENTOW2-B [r3 RESTATED] + LEMMA GENTOW2-B'' @ d798529), u_2(beta_t) = theta_2(t) * w_2^{f_3 - t} with the single cross-frame unit w_2 — the level this note's (a)/(B-2) display cites at source.
> * i >= 3 — PROVED by this note's own sections: per-grade FIXEDNESS of u_i(beta) (S2.3 step (3)'s tau_i-cocycle letter computation: each grade's unit is a fixed K_i^x-value), x0-freeness and g-freeness (the (SLOT_i) value clause), and the definitional reciprocity theta_i(t) = vartheta_{i,f_{i+1}-t}^{-1} (S2.1's same monomial quotient, inverse read). NOT PROVED at i >= 3: the single-w geometric form
>
>       [GENTOW5-W(i)]   u_i(beta_t) = theta_i(t) * w_i^{f_{i+1}-t},
>                        w_i = R_{i+1,kbar_i}(nhat_i(u_{i+1})),
>
>   which per-grade fixedness underdetermines (fixed families exist that fit no single w) — this is GENTOW2-B'''s computation run at level i, which this note does not reproduce. [GENTOW5-W(i)] is hereby an OPEN transported lemma, the honest-sorry analogue.”

**CONDITIONALITY:** This unit IS a conditionality declaration. Its own scope statement (`.26`) is partly withdrawn by S12.1.

**DERIVATION:** The gap is exhibited, not merely asserted: per-grade fixedness underdetermines the single-w form because “fixed families exist that fit no single w”.

**RESOLUTION TRACE:** Base §S11.2, lines 1888–1918.

**SUPERSESSION KIND:** scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.27` and its i≥3 B-2 transport derivation.

**CHAIN:** claimed annex-precedent transport of the single-`w` law → **open `[GENTOW5-W(i)]` fence TERMINAL for frozen GENTOW5 at i≥3**. The 2026-08-15 append confirms WI certification does not remove the fence.

XREF: `lean/notes/openmath/GENTOW5_WI_2026-08-10.md:[GENTOW5-W(i)]` — grep-verified count **24**. **This is the reverse supplier edge**: the WI note proves the companion lemma, but the 2026-08-15 GENTOW5 append expressly says its certification does not discharge the conjuncts from frozen GENTOW5 statements.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` — grep-verified count **11**; the level-2 computation this note does not reproduce at level i.

**TEETH:** PROOF-ONLY — “the machine record does not discriminate this fence”; the proof-side gap is the absence of a single-`w` derivation.

---

### EFF.GENTOW5.s2of2.26  [scope-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.2 — scope of the fence

> “**Scope of the fence (what rides on [GENTOW5-W(i)] at i >= 3 and what does not).** Conditional on it: clause (a)'s realized-residual display psi_{i+1}^{(w_i)} AND the (a)-certificate legs that consume that form (KP membership via admissibility of psi^{(w)}, prime, non-equivalence), and with them (b)'s FGMN-side residual DISPLAYS at i >= 3 (the (b)-cite enters through (a)'s certificate at the same index). Not conditional (the [GT5-r2] per-consumer walk, unchanged): sigma, values, degrees, irreducibility transport, the repo-side residue classes and P-membership clauses, (c)'s budgets, (d), (e) — w-blind there. At i = 2 the display is unconditional (the landed law); at i = 1 see S11.3. The S4 depth-4 witness is w-trivial (K_i = F_2), so the machine record does not discriminate this fence — disclosed at S6's coverage box already.”

**CONDITIONALITY — PARTLY WITHDRAWN in range.** S12.1's opening supersedes the second sentence:

> “but its subsequent assertion that exact values, repo-side residue classes, \(P\)-membership, clause (c), and clause (e) remain unconditional is WITHDRAWN.”

**Effective reading:** the *conditional* list stands and grows; the *not-conditional* list shrinks to what S12.1's unaffected-scope paragraph names (`.34`). The two clauses that survive from the original not-conditional list are (d) at its stated event hypotheses and the formal/arithmetic content; `(c)`, `(e)`, exact values, repo-side classes and P-membership move to the conditional side at n ≥ 3.

**DERIVATION:** The original scope split rested on “w-blindness” of repo-side data; S12.1 identifies the flaw in that reasoning (`.31`).

**RESOLUTION TRACE:** Base §S11.2, lines 1919–1931; superseded in part by S12.1 (resolution rule 4).

**SUPERSESSION KIND:** scope-pin, later partial-withdrawal.

**TARGETS:** `EFF.GENTOW5.s1of2.27`, `EFF.GENTOW5.s1of2.28`, `EFF.GENTOW5.s1of2.29`, `EFF.GENTOW5.s1of2.30`, `EFF.GENTOW5.s1of2.31`, and `EFF.GENTOW5.s1of2.32`.

**CHAIN:** `[GT5-r2]` w-blind walk → S11.2 conditional residual/certificate list → **S12.1 partial withdrawal TERMINAL**: exact values, repo classes, P-membership, (c), and (e) also become conditional; clause (d), σ/degrees, formal recipe arithmetic, and S4 survive.

**TEETH:** signed vacuity disclosure — S4 is `w`-trivial (`K_i^×={1}`), so “the machine record does not discriminate this fence”.

---

### EFF.GENTOW5.s2of2.27  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.3 `[A-F3, GAP]` — clause (a) at i = 1 RE-SCOPED

> “**The two sentences in tension (quoted).** The statement's (a) displays R_{nu_i}(Phi_{i+1}) = psi_{i+1}^{(w_i)} at the pinned w_i = R_{i+1,kbar_i}(nhat_i(u_{i+1})), claimed at i >= 1; the PE5-F-2 acceptance fold discharges the i = 1 line at the shape "a psi_2^{(u)} with u a fixed z_1-letter power" and closes "an exponent-level tie of the w_1 display to the letter formula is NOT claimed."”

> “**Adjudicated from the fold's own scope bracket: the DISCLAIMER is right; the statement's i = 1 instance is corrected.** The fold's derivation is GENTOW2-A(c)'s letter-formula content (z_2 = eta_2 * z_1^{-floor(l_1 u_2/e_1)}): it pins the SPECIES of the twist unit (a fixed z_1-letter power) and never evaluates the residue R_{2,kbar_1}(nhat_1(u_2)) — so it cannot identify the unit with the pinned w_1, and different units give different residual polynomials (the twist acts on coefficients grade-by-grade). Dated statement correction (honest re-scope, standing authority): clause (a) AT i = 1 reads
>
>     R_{nu_1}(Phi_2) = psi_2^{(u1)},  u1 in K_1^x a FIXED
>     z_1-letter-power unit (the letter formula's species);
>     the tie u1 = w_1 = R_{2,kbar_1}(nhat_1(u_2)) is OPEN.”

> “Consumers: the fold's grep audit (zero instantiations of the w_1 display against the letter formula; no consumer on the record read needs the tie) re-verified this round. Net position after S11.2 + S11.3: the pinned-w_i form is unconditionally realized at i = 2 exactly; at i = 1 the shape is proved with the tie open; at i >= 3 the form is open behind [GENTOW5-W(i)].”

**CONDITIONALITY:** At i = 1 the *species* is proved; the *identification* with the pinned `w_1` is OPEN. Declared consumer-free (grep audit).

**DERIVATION:** The letter formula fixes the species but never evaluates the residue that defines `w_1`; since different units give different residual polynomials, species does not determine the twist. Hence the statement is re-scoped rather than the tie asserted.

**RESOLUTION TRACE:** Base §S11.3, lines 1933–1964. This is a **statement correction** on a clause homed in shard 1, taken under “standing authority” and in the conservative direction (it weakens the note's own claim; the statement fence in the parent CLAUDE.md concerns weakening a *target* to make it provable, which this is not — here the note narrows its own asserted conclusion).

**SUPERSESSION KIND:** scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.27`.

**CHAIN:** pinned `w_1` identity → **fixed `z_1`-letter-power species TERMINAL for i=1**, with `u1=w_1` open.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.1` — grep-verified count **42**; the LETTER FORMULA's home.

**READING NOTE:** the clause-level pointer `GENTOW2-A(c)` is not separately greppable (`GENTOW2-A(c)` count **0** in GENTOW2_PROOF); the parent `THEOREM GENTOW2-A` is verified (count **8**). Carried descriptively, not as a designation.

**TEETH:** The grep audit (zero consumer instantiations), re-verified at this round.

---

### EFF.GENTOW5.s2of2.28  [changes-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.4 `[A-F4, MINOR]` — the `lift_i(c; m)` m-range bracket **(SUPERSEDED IN RANGE)**

> “Dated bracket on the S2.2 K_i-digit-lifts display: the flavor display and the realization sentence ("O-digit coefficients d_{r,t} realizing c") read AT HEIGHTS m IN (LIFT_i)'S VALIDITY RANGE — k-uniformly above the bound_{i+1} recursion of LEMMA GENTOW5-C, whose (LIFT_i) clause the display's existence/freeness sentence already cites. Unrestricted m is overbroad: below the range a flavor can fail integrality (at i = 1, e_1 = 2, f_1 = 2, h = 1, m = 0 the r = 1 flavor's base nhat_1(-2) demands pi^{-1} — no such monomial in O[x]; the "flavor is absent when nhat_i(m - Delta(r,t)) has no ladder solution" proviso already excludes negative-height bases, and the m-range bracket makes the realization claim's scope match it). Consumers unchanged: the recipe's khat_t heights and the floor chain sit in-range per the lemma's own bound arithmetic.”

**CONDITIONALITY:** **Superseded by S12.2 in this same range** (resolution rule 3): the `bound_{i+1}` threshold is WITHDRAWN and replaced by `bound_i`. What survives from this bracket is (i) the observation that unrestricted `m` is overbroad, and (ii) the worked integrality failure at `i = 1, e_1 = 2, f_1 = 2, h = 1, m = 0`.

**DERIVATION:** The negative-height base `nhat_1(-2)` would demand `pi^{-1}`, which is not in `O[x]`.

**RESOLUTION TRACE:** Base §S11.4, lines 1966–1980; superseded at §S12.2, lines 2137–2142.

**SUPERSESSION KIND:** scope-pin, then withdrawal.

**TARGETS:** `EFF.GENTOW5.s1of2.17`.

**CHAIN:** unrestricted `m` → S11.4 `m>bound_{i+1}` → **S12.2 `m>bound_i` TERMINAL**. The worked `pi^{-1}` counterexample survives the withdrawn middle scope.

**RECORDED SOURCE DEFECT (flagged, not silently repaired):** the bracket is addressed to “the S2.2 K_i-digit-lifts display”, but that display is homed in §S2.1 (§S2.2 is the consistency-checks section). The referent is unique in the note, so the bracket is applied to the §S2.1 display; the mis-pointer is recorded. S12.2, which supersedes the bracket, refers to it without a section number.

**TEETH:** The worked `pi^{-1}` failure instance.

---

### EFF.GENTOW5.s2of2.29  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S11.5 `[A-F5, MINOR]` — clause (b)'s residual display RE-INDEXED

> “Dated bracket on the statement's (b): the residual display "R_{j-1}(Phi_{i+1}) = psi_{j-1}^{l_j ... l_{i+1}}" dereferences psi_0 at j = 1 and fails the residual-degree count. Corrected, in this note's stage numbering:
>
>     R_{j-1}(Phi_{i+1}) = psi_j^{l_{j+1} ... l_{i+1}}
>     (1 <= j <= i+1; empty product = 1 at j = i+1),
>
> re-derived from the note's own rows: the level-(j-1) polygon of Phi_{i+1} has length l_j...l_{i+1}, and one full side of slope lam_j (gcd(u_j, e_j) = 1) carries residual degree l_j...l_{i+1}/e_j = f_j * l_{j+1}...l_{i+1} = deg of the corrected display (the composed display's degree f_{j-1}*l_j...l_{i+1} fails this count); checked at the committed rows — the j = 1 leg (level-0 read, residue class a psi_1-root: psi_1, exponent l_2...l_{i+1} consistent), the top leg j = i+1 (level-i read, residual psi_{i+1} of degree f_{i+1}), and P-B3's Phi_4@Phi_2 (level-2 read, j = 3: psi_3^{l_4} = (y-1)^2, measured residual degree 2, S10). The (b) proof's citation line "R_{j-1}(F) = psi_{j-1}^{l_j...}" transcribes [Q10]'s display (23) in the source's own numbering; the consumed content (one-sidedness, exact intermediate values, root classes) is index-convention-blind, and no psi_0 is consumed anywhere in the proof. [Per S11.2, at i >= 3 the psi symbols in this display read at their levels' twisted forms per the re-scoped (a), now behind [GENTOW5-W(i)].]”

**CONDITIONALITY:** The re-index is a display correction with no consumption change (“the consumed content … is index-convention-blind”). At i ≥ 3 the display's psi symbols carry the twists, indexed as the post-D3i corrigendum fixes (`.41`).

**DERIVATION:** The residual-degree count: polygon length `l_j...l_{i+1}`, one full side with `gcd(u_j, e_j) = 1` gives residual degree `l_j...l_{i+1}/e_j = f_j·l_{j+1}...l_{i+1}` — matching the corrected display, not the composed one; three committed rows check it.

**RESOLUTION TRACE:** Base §S11.5, lines 1982–2008; further twisted by S12.1 item 2 and re-indexed by the post-D3i corrigendum.

**SUPERSESSION KIND:** replacement plus scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.28`.

**CHAIN:** `psi_{j-1}^{l_j⋯l_{i+1}}` → S11.5 `psi_j^{l_{j+1}⋯l_{i+1}}` → S12.1 `psi_j^{(ω_j)}` → **post-D3i `psi_j^{(ω_{j-1})}` TERMINAL**; the i≥3 display and all of clause (b) ride `𝒲_{≤n}`.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:[Q10]` — grep-verified count **6**; and `(23)` — count **4**. **Source-display check:** GENTOW2's `[Q10]` quote block prints “R_{i−1}(F) = (ψ_{i−1})^{ℓ_i}”, confirming the diagnosis that the base display transcribed FGMN's own index convention.

**TEETH:** P-B3's `Phi_4@Phi_2` row (level-2 read, `psi_3^{l_4} = (y-1)^2`, measured residual degree 2).

---

### EFF.GENTOW5.s2of2.30  [changes-record]

**FORM:** inline sentence

**CANONICAL STATEMENT:** S11.6 `[GT5-r4]` BYTE-FREEZE + APPEND LEDGER

> “Pre-append state: post-acceptance body @ 43b42e9c, md5 d9e6b5ba (d9e6b5ba069c19eb5f528b03c1807f14; 1,741 lines, 98,509 bytes). Commit 1 (S11 head + S11.1): PURE APPEND, prefix-98,509 md5 re-verified d9e6b5ba; post state md5 0b850dda (1,886 lines, 106,419 bytes); machine leg gentow5_af1_direction_check.py md5 82acd3d2 (output 503279ef, GREEN 8 checks / 0 violations, exit 0). Commit 2 (S11.2-S11.6): PURE APPEND on that state, prefix-106,419 md5 re-verified at commit (recorded in the commit message). Sealed artifacts untouched this round: gentow5_checks.py 5fa684c7..., gentow5_output_exact.txt dc499a49..., gentow5_output_full.txt 839a8660..., gentow5_rider_f32dev.py 81bbb5db... — no runner edited, no sealed re-run. Statement displays above stay byte-intact; corrections are by dated supersession (S11.1 direction + closure, S11.3 (a)@i=1 re-scope, S11.5 (b) re-index) and dated fences (S11.2 [GENTOW5-W(i)], S11.4 m-range). Grade: ACCEPTED 2/2 stands, ANNOTATED by RUN A; the repairs above discharge the adjudication's charges A-F1/A-F3/A-F4/A-F5 in full and convert A-F2 into the named open lemma [GENTOW5-W(i)].”

**CONDITIONALITY:** Protocol record. Note the asymmetric disposition: four charges discharged, one (A-F2) **converted into an open lemma** rather than discharged.

**DERIVATION:** Prefix-md5 verification per commit.

**RESOLUTION TRACE:** Base §S11.6, lines 2010–2029.

**TEETH:** Prefix-md5 re-verification at each of the two commits; the isolated instrument's own md5/output pair.

---

### EFF.GENTOW5.s2of2.31  [scope-record]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S12.1 `[R-i2]` — the withdrawal, and the cumulative condition `𝒲_{≤n}`

> “**Superseded scope in S11.2.** S11.2 correctly leaves open, for every \(i\ge 3\),
>
> \[
> [{\rm GENTOW5\!-\!W}(i)]\qquad
> u_i(\beta_t)=\theta_i(t)\,w_i^{\,f_{i+1}-t},
> \qquad
> w_i=R_{i+1,\bar k_i}(\widehat n_i(u_{i+1})),
> \]
>
> but its subsequent assertion that exact values, repo-side residue classes, \(P\)-membership, clause (c), and clause (e) remain unconditional is WITHDRAWN. A fixed per-grade unit family is not enough: “\(w\)-blind” means invariance AFTER the family has been proved to have the single-\(w_i\) geometric form. It does not construct that form.”

> “For \(n\ge3\), write
>
> \[
> \mathcal W_{\le n}:=
> \bigwedge_{3\le q\le n}[{\rm GENTOW5\!-\!W}(q)].
> \]
>
> The cumulative condition records the induction history; locally, the new input at rung \(n\) is \([{\rm GENTOW5\!-\!W}(n)]\).”

**CONDITIONALITY:** This unit defines the conditionality vocabulary used by `.32`–`.34` and by shard 1's clauses (a)/(b)/(c)/(e). The post-D3i corrigendum adds how the chain diagram reads under it: “the dependency chain diagram is read under the ambient hypothesis 𝒲_{≤n} as a whole (its first arrow consumes [GENTOW5-W(n)] with the earlier instances ambient)”.

**DERIVATION:** The one-sentence defeater, quoted above: per-grade fixedness is a weaker property than single-`w` geometry, so “w-blindness” arguments presuppose exactly what is unproved.

**RESOLUTION TRACE:** Base §S12.1, lines 2037–2055; supersedes §S11.2's scope paragraph (`.26`).

**SUPERSESSION KIND:** partial-withdrawal; replacement scope attached.

**TARGETS:** `EFF.GENTOW5.s2of2.26` and `EFF.GENTOW5.s1of2.32`.

**CHAIN:** S11.2's broad w-blind unaffected list → **five-item partial withdrawal + cumulative `𝒲_{≤n}` scope TERMINAL**. The 2026-08-15 append expressly confirms that the withdrawal is partial, not total.

XREF: `lean/notes/openmath/GENTOW5_WI_2026-08-10.md:[GENTOW5-W(i)]` — grep-verified count **24**; the certified companion note. The frozen GENTOW5 conditional remains in force by the later consumption append.

**TEETH:** PROOF-ONLY — no committed row discriminates the single-`w` law; the unit is guarded by the source's explicit coverage-hole sentence.

---

### EFF.GENTOW5.s2of2.32  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S12.1 `[R-i2]` — the correct conditional scope, clause by clause

> “1. **Clause (a).** At index \(n\ge3\), conditional on \(\mathcal W_{\le n}\), the pinned recipe has
>
>    \[
>    R_{\nu_n}(\Phi_{n+1})
>    =\psi_{n+1}^{(w_n)}
>    :=w_n^{f_{n+1}}\psi_{n+1}(y/w_n),
>    \]
>
>    and the admissibility, key-polynomial membership, prime/irreducibility certificate, and non-equivalence conclusions follow as written. Without \([{\rm GENTOW5\!-\!W}(n)]\), per-grade fixedness supplies no single substitution \(y\mapsto w_ny\), so none of those certificate legs is established for the pinned key.”

> “2. **Clause (b), including exact values and \(P\)-membership.** Corollary 6.4 fires only after clause (a) has supplied the key-polynomial/prime certificate for \(\Phi_{n+1}\). Consequently, at index \(n\ge3\), ALL of clause (b) is conditional on \(\mathcal W_{\le n}\): one-sidedness at every lower level, the corrected residual powers
>
>    \[
>    R_{j-1}(\Phi_{n+1})
>    =\bigl(\psi_j^{(\omega_j)}\bigr)^{\,l_{j+1}\cdots l_{n+1}}
>    \qquad(1\le j\le n+1),
>    \]
>
>    the exact intermediate values
>
>    \[
>    v(\Phi_{j-1}(\xi))=\frac{u_j}{\widehat e_j},
>    \]
>
>    the repo-side residue-class identifications, and therefore \(\xi\in P_{n+1}\). Here \(\omega_1\) is S11.3's proved fixed \(z_1\)-letter-power unit, \(\omega_2=w_2\) from the landed GENTOW2 law, and \(\omega_j=w_j\) for \(j\ge3\). The B'' root correspondence is usable only after the corresponding common \(\omega_j\) exists; it cannot turn an arbitrary per-grade unit family into a geometric twist.”

> “3. **S11.1 and clause (c).** The numerical \(\rho\)-ladder of S11.1.2 is unconditional floor arithmetic, but S11.1.1 and S11.1.3 consume clause (b): S11.1.1 obtains the one-sided polygons and
>
>    \[
>    \operatorname{descmin}(\Phi_k)=L_k\lambda
>    \]
>
>    from \((b)@(k-1)\), while S11.1.3 compares \(g\) against those sides and their exact pins. Thus clause (c) at index \(n\ge3\), including its sufficiency direction, deeper-read ascent, fibration, node pins, and field-floor conclusion, is conditional on \(\mathcal W_{\le n}\). Step 1 already consumes \((b)@n\); the repaired Step 2 additionally consumes the earlier \((b)@q\) instances occurring in its descent.”

> “4. **Clause (e) and the induction feed.** Clause (e) at index \(n\ge3\) consumes clause (c)'s pins, so its automatic next-floor conclusion
>
>    \[
>    u_{n+2}>e_{n+2}E_{n+1}
>    \]
>
>    is conditional on \(\mathcal W_{\le n}\) as well. Later arguments may still use that inequality unconditionally when it is included explicitly in the fixed tower datum; only its claimed automatic derivation from the recipe is conditional.”

**CONDITIONALITY:** Item 2's twist indexing is itself corrected by the post-D3i corrigendum (`.41`): read `ψ_j^{(ω_j)}` as `ψ_j^{(ω_{j−1})}`.

**DERIVATION:** A dependency audit, each step quoted: (a) needs the single substitution; Cor 6.4 needs (a)'s certificate; S11.1.1/S11.1.3 consume (b); (e) consumes (c)'s pins.

**RESOLUTION TRACE:** Base §S12.1, lines 2057–2119; item 2 re-indexed at lines 2299–2313. Lands on shard 1's clauses (a), (b), (c), (e) and on this shard's `.21`, `.23`.

**SUPERSESSION KIND:** scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.27`, `EFF.GENTOW5.s1of2.28`, `EFF.GENTOW5.s1of2.29`, `EFF.GENTOW5.s1of2.31`, `EFF.GENTOW5.s2of2.21`, and `EFF.GENTOW5.s2of2.23`.

**CHAIN:** S11.2 residual-display-only fence → S12.1 full consequence-chain fence → **post-D3i twist-index correction TERMINAL**; `𝒲_{≤n}` is ambient on the whole chain.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:Cor 6.4` — grep-verified count **11**; the corollary whose firing order is the load-bearing step of item 2.

**TEETH:** AUDIT: decorrelated-model audit (D1a → E12); no ordinary battery row could establish this dependency propagation.

---

### EFF.GENTOW5.s2of2.33  [scope-record]

**FORM:** display

**CANONICAL STATEMENT:** S12.1 — the complete dependency chain

> “The complete dependency chain is therefore
>
> \[
> [{\rm GENTOW5\!-\!W}(n)]
> \Longrightarrow (a)@n
> \Longrightarrow {\rm Corollary\ 6.4}\Longrightarrow (b)@n
> \Longrightarrow {\rm S11.1.1/S11.1.3}
> \Longrightarrow (c)@n
> \Longrightarrow (e)@n
> \Longrightarrow\text{the next automatic floor}.
> \]”

**CONDITIONALITY:** Read under the ambient hypothesis `𝒲_{≤n}` per the post-D3i corrigendum:

> “Correspondingly, the dependency chain diagram is read under the ambient hypothesis 𝒲_{≤n} as a whole (its first arrow consumes [GENTOW5-W(n)] with the earlier instances ambient).”

**DERIVATION:** The chain is the composition of `.32`'s four items.

**RESOLUTION TRACE:** Base §S12.1, lines 2121–2131; ambient reading fixed at lines 2309–2312.

**SUPERSESSION KIND:** scope-pin.

**TARGETS:** `EFF.GENTOW5.s1of2.27`, `EFF.GENTOW5.s1of2.28`, `EFF.GENTOW5.s1of2.29`, and `EFF.GENTOW5.s1of2.31`.

**CHAIN:** single-new-conjunct antecedent read in isolation → **whole diagram under ambient `𝒲_{≤n}` TERMINAL**.

**TEETH:** PROOF-ONLY — guarded by `.32`'s dependency audit and the absence of a discriminating machine row.

---

### EFF.GENTOW5.s2of2.34  [fence]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S12.1 — unaffected scope

> “**Unaffected scope.** The \(i=2\) rung remains unconditional by the landed GENTOW2 law; the \(i=1\) residual remains exactly S11.3's fixed-letter-power statement with only its identification with the displayed \(w_1\) open. LEMMAS GENTOW5-A0/A1, the refine-transfer clause (d) at its stated event hypotheses, LEMMA GENTOW5-D under an explicitly supplied floor-chain datum, formal monicity/degrees and recipe-height arithmetic, and the S4 witness remain unaffected. At S4 every \(K_i^\times=\{1\}\), so each required geometric law is tautological there.”

**CONDITIONALITY:** This is the post-narrowing positive list — the units of shard 1 that stay unconditional. Note the qualifier on LEMMA GENTOW5-D: “under an explicitly supplied floor-chain datum”. The automatic derivation of that datum is a separate conditional predicate.

**DERIVATION:** Complement of the dependency chain; the S4 clause is derived from `K_i^× = {1}`.

**RESOLUTION TRACE:** Base §S12.1, line 2133.

**SUPERSESSION KIND:** scope-pin (survivor enumeration after partial withdrawal).

**TARGETS:** `EFF.GENTOW5.s2of2.26`.

**CHAIN:** S11.2 broad unaffected list → **S12.1 narrowed survivor list TERMINAL**; the 2026-08-15 append confirms σ/degrees/irreducibility transport and clause (d) survive.

**TEETH:** The S4 witness (w-trivial by construction) is named as the tautological case.

---

### EFF.GENTOW5.s2of2.35  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S12.2 `[R-i4]` — the lift rung CORRECTED

> “**Superseded S11.4 bracket.** The sentence placing the displayed \(\operatorname{lift}_i(c;m)\) above \(\operatorname{bound}_{i+1}\) is WITHDRAWN. That display realizes \(c\in K_i\) by a polynomial of degree \(<D_i\); hence it consumes the PRECEDING lift instance and has threshold \(\operatorname{bound}_i\), not \(\operatorname{bound}_{i+1}\).”

> “Precisely,
>
> \[
> \operatorname{lift}_i(c;m)\in\mathcal O[x],\qquad
> \deg\operatorname{lift}_i(c;m)<D_i,\qquad
> \operatorname{res}\!\left(
>  \frac{\operatorname{lift}_i(c;m)}{\widehat n_i(m)}
> \right)=\iota^{(i)}(c)
> \]
>
> is valid for
>
> \[
> m>\operatorname{bound}_i.
> \]
>
> For \(i\ge2\) this is supplied by \(({\rm LIFT}_{i-1})\); for \(i=1\) it is the accepted base lift. By contrast, the clause labelled \(({\rm LIFT}_i)\) in LEMMA GENTOW5-C constructs \(K_{i+1}\)-digits of degree \(<D_{i+1}\) and therefore correctly has threshold
>
> \[
> \operatorname{bound}_{i+1}
> =(l_{i+1}-1)u_{i+1}
>  +e_{i+1}\operatorname{bound}_i.
> \]”

**CONDITIONALITY:** Unconditional rung arithmetic; independent of `[GENTOW5-W(i)]`. The post-D3i corrigendum confirms: “R-i4 (the lift rung) is unaffected and was DISCHARGED.”

**DERIVATION:** The threshold is fixed by *what the object realizes*: `lift_i` realizes `K_i` with degree `< D_i`, hence it is the level-`i` instance and consumes the preceding rung's bound; `(LIFT_i)` realizes `K_{i+1}` with degree `< D_{i+1}` and keeps `bound_{i+1}`.

**RESOLUTION TRACE:** Base §S12.2, lines 2137–2169; supersedes `.28` (S11.4) and lands on shard 1's K_i-digit-lift unit.

**SUPERSESSION KIND:** replacement plus withdrawal of the intervening range.

**TARGETS:** `EFF.GENTOW5.s2of2.28` and `EFF.GENTOW5.s1of2.17`.

**CHAIN:** unrestricted `m` → S11.4 `m>bound_{i+1}` → **S12.2 `m>bound_i` TERMINAL**; `(LIFT_i)` itself retains `bound_{i+1}` because it constructs the next-rung object.

XREF: `lean/notes/openmath/HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` — grep-verified count **3**; the source of the `bound_{i+1}` recursion restored at PE5-F-3.

**TEETH:** The depth-4 numeric separation at `.38`.

---

### EFF.GENTOW5.s2of2.36  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** S12.2 — the boxed bound inequality

> “**The bound needed by every recipe lift is automatically met.** At the base,
>
> \[
> \operatorname{bound}_1=(l_1-1)u_1<E_1=l_1u_1.
> \]
>
> Inductively, if \(\operatorname{bound}_{i-1}<E_{i-1}\), the floor rung \(u_i>e_iE_{i-1}\) gives
>
> \[
> e_i\operatorname{bound}_{i-1}<u_i
> \]
>
> and hence
>
> \[
> \operatorname{bound}_i
> =(l_i-1)u_i+e_i\operatorname{bound}_{i-1}
> <l_i u_i=E_i.
> \]
>
> Thus
>
> \[
> \boxed{\operatorname{bound}_i<E_i\quad\text{for every }i\ge1.}
> \]”

**CONDITIONALITY:** Consumes the floor chain `u_i > e_i E_{i-1}` — at n ≥ 3 it is usable unconditionally when explicitly supplied as datum, while its automatic derivation is conditional (`.34`). The induction is otherwise elementary arithmetic.

**DERIVATION:** The two-line induction quoted above.

**RESOLUTION TRACE:** Base §S12.2, lines 2171–2198.

**TEETH:** `.38`'s depth-4 numbers `(1, 7, 35, 155)` vs `E_i = (2, 10, 42, 170)` instantiate the box.

---

### EFF.GENTOW5.s2of2.37  [lemma]

**FORM:** inline sentence

**CANONICAL STATEMENT:** S12.2 — every recipe lift lands in range, and the corrected consumer sweep

> “For a nonzero recipe coefficient \(c_t\), put \(s=f_{i+1}-t\). Since \(t<f_{i+1}\), one has \(s\ge1\), and the recipe height is
>
> \[
> m_t=s\,u_{i+1}\ge u_{i+1}
> >e_{i+1}E_i\ge E_i>\operatorname{bound}_i.
> \]
>
> Therefore the required preceding-rung lift exists and gives
>
> \[
> \widehat k_t
> =\operatorname{lift}_i
>  \bigl(c_t\vartheta_{i,s};\,s u_{i+1}\bigr)
> \in\mathcal O[x],\qquad
> \deg\widehat k_t<D_i,
> \]
>
> with exact \(dv_i\)-height \(s u_{i+1}\) and the prescribed coherent \(K_i\)-digit. When \(c_t=0\), \(\widehat k_t=0\) and no lift is required. Consequently every nonzero recipe side term has exact \(dv_{i+1}\)-height
>
> \[
> e_{i+1}s u_{i+1}+e_{i+1}t u_{i+1}
> =e_{i+1}f_{i+1}u_{i+1}=E_{i+1},
> \]
>
> and its degree is \(<D_{i+1}\).”

> “No recipe consumer needs \(m_t>\operatorname{bound}_{i+1}\). The corrected consumer sweep is:
>
> * DEF GENTOW5-1 and clause (a) need the preceding-rung \(K_i\)-digit lift above \(\operatorname{bound}_i\), proved above.
> * LEMMA GENTOW5-D's \(({\rm INV}\!-\!j)\) carry display needs only \(\deg\widehat k_t<D_i\) and the exact height \(s u_{i+1}\), both now proved in the correct range.
> * Clause (c), including Step 1 and Step 5, consumes those same exact side heights and coherent digits; it does not consume \(\operatorname{bound}_{i+1}\) for a recipe coefficient.
> * The S4 recipe keys consume respectively \(\operatorname{bound}_1,\operatorname{bound}_2, \operatorname{bound}_3,\operatorname{bound}_4\), never the next bounds.”

**CONDITIONALITY:** Uses `u_{i+1} > e_{i+1}E_i` (floor chain) and the boxed `bound_i < E_i`. No `[GENTOW5-W(i)]` dependence.

**DERIVATION:** The displayed inequality chain `m_t ≥ u_{i+1} > e_{i+1}E_i ≥ E_i > bound_i`, then the height/degree arithmetic of the recipe side terms.

**RESOLUTION TRACE:** Base §S12.2, lines 2200–2245; discharges the range obligation for shard 1's recipe unit and (INV-j) display.

**SUPERSESSION KIND:** replacement (consumer-sweep vehicle).

**TARGETS:** `EFF.GENTOW5.s1of2.17`, `EFF.GENTOW5.s1of2.18`, `EFF.GENTOW5.s1of2.25`, and `EFF.GENTOW5.s1of2.29`.

**CHAIN:** next-rung recipe-lift demand → **preceding-rung `bound_i` consumer readings TERMINAL** for DEF, clause (a), INV-j, clause (c), and S4.

**TEETH:** `.38`'s witness separation.

---

### EFF.GENTOW5.s2of2.38  [instance-record]

**FORM:** inline sentence

**CANONICAL STATEMENT:** S12.2 — the depth-4 witness makes the rung distinction explicit

> “The depth-4 witness makes the rung distinction explicit:
>
> \[
> (\operatorname{bound}_1,\operatorname{bound}_2,
>   \operatorname{bound}_3,\operatorname{bound}_4)
> =(1,7,35,155),
> \]
>
> while its successive recipe heights are
>
> \[
> 5,\ 21,\ 85,\ 341.
> \]
>
> Thus \(5>1\), \(21>7\), \(85>35\), and \(341>155\), exactly as required. The rejected next-rung demands would be \(5>7\), \(21>35\), \(85>155\), and \(341>651\), explaining why S11.4's range assertion was false while every actual recipe lift remains valid.”

**CONDITIONALITY:** One chain (the S4.1 all-(2,1) tower); it exhibits the rung distinction rather than proving the general statement, which is `.35`–`.37`.

**DERIVATION:** `bound_i` computed from the recursion of `.35` on the S4.1 datum, compared rung by rung with the recipe heights `u_{i+1}` of shard 1's witness chain.

**RESOLUTION TRACE:** Base §S12.2, lines 2247–2265.

**TEETH:** The four-fold numeric separation is itself the check; it is re-computed independently in the orchestrator verification note (`.40`).

---

### EFF.GENTOW5.s2of2.39  [lemma]

**FORM:** inline sentence

**CANONICAL STATEMENT:** S12.2 — the refine consumers use the other rung correctly

> “Finally, genuine refine consumers use the other rung correctly: \(\operatorname{lift}_{i+1}(s;\lambda)\) realizes \(K_{i+1}\) with degree \(<D_{i+1}\), so it needs \(\lambda>\operatorname{bound}_{i+1}\). Their event hypothesis gives
>
> \[
> \lambda>E_{i+1}>\operatorname{bound}_{i+1},
> \]
>
> by the boxed inequality. Hence THEOREM GENTOW5-A and clause (d)'s refine lifts also land in their required ranges. This proves every actual lift consumption; no qualification of the recipe or refine statements is needed.”

**CONDITIONALITY:** Uses the event hypothesis `λ > E_{i+1}` (shard 1's clause (d) / THEOREM GENTOW5-A setting) and the boxed inequality of `.36`.

**DERIVATION:** `λ > E_{i+1} > bound_{i+1}` by the box, so the `(i+1)`-rung lift exists at the event slope.

**RESOLUTION TRACE:** Base §S12.2, lines 2267–2279; closes the lift-range obligation for shard 1's THEOREM GENTOW5-A and clause (d).

**SUPERSESSION KIND:** scope-pin (consumer-sweep vehicle).

**TARGETS:** `EFF.GENTOW5.s1of2.10` and `EFF.GENTOW5.s1of2.30`.

**CHAIN:** unresolved refine-lift range → **`λ>E_{i+1}>bound_{i+1}` TERMINAL**, so no qualification of the refine statements is needed.

**TEETH:** Covered by `.38`'s numeric instance.

---

### EFF.GENTOW5.s2of2.40  [changes-record]

**FORM:** bracketed rider

**CANONICAL STATEMENT:** S12 provenance and orchestrator verification

> “*(The S12 append above was derived by the E12 certification run (gpt-5.6-sol high, runs/cert2/E12_gentow5_output.log, 2026-08-12), repairing the two D1a residuals (INSUFFICIENT finding 2 and NEW-ISSUE finding 4); orchestrator verification before transcription — R-i2's dependency chain checked against the D1a finding ((a)@n needs [W(n)]; Corollary 6.4 fires only after (a); (b) ⟹ S11.1.1/S11.1.3 ⟹ (c) ⟹ (e)), with the unaffected scope (i = 2 by the landed GENTOW2 law; S4's trivial K_i^×) named; R-i4's rung logic checked (lift_i realizes K_i with deg < D_i, so its threshold is bound_i — the level-i instance) and the depth-4 witness re-computed (bounds (1,7,35,155) vs recipe heights (5,21,85,341): each exceeds its level-i bound, none the next-rung bound — 5>1, 21>7, 85>35, 341>155 vs the failing 5>7 etc.); refine consumers correctly use lift_{i+1} at λ > E_{i+1} > bound_{i+1}. Transcribed unaltered per the standing division of labor. Ledger: row 10 → both residuals repaired, awaiting sol discharge (cert3).)*”

**CONDITIONALITY:** Declares a two-stage provenance: derived by a decorrelated model, hand-verified by the orchestrator before transcription, transcribed unaltered. The ledger line (“awaiting sol discharge (cert3)”) is a protocol state, later advanced by the post-D3i corrigendum and by the external ledger (§8 reading note).

**DERIVATION:** Verification record, with the re-computed numbers quoted.

**RESOLUTION TRACE:** Base §S12, lines 2281–2296.

XREF: `runs/cert/D1a_gentow5_output.log:INSUFFICIENT` — grep-verified count **2**; and `NEW-ISSUE` — count **2**. **Provenance check:** the two finding labels live in the **D1a** discharge output, as the note says (“the two D1a residuals”); the E12 log is the deriving run and restates them in its charge brief `runs/cert2/E12_gentow5_brief.txt` (“the INSUFFICIENT finding 2”, “the NEW-ISSUE finding 4”). Both files exist in the repo.

**TEETH:** The orchestrator's independent re-computation of the depth-4 bounds is the check of record for `.38`.

---

### EFF.GENTOW5.s2of2.41  [lemma]

**FORM:** bold-headed paragraph

**CANONICAL STATEMENT:** Dated corrigendum (2026-08-12, post-D3i) — S12.1's residual-twist index

> “**Dated corrigendum (2026-08-12, post-D3i — S12.1's residual-twist index).** The D3i discharge pass (gpt-5.6-sol high, runs/cert3/D3i_gentow5_output.log) adjudicated S12.1 NEW-ISSUE at one index: clause (a) at index r supplies the twist w_r for ψ_{r+1}, so in clause (b)'s corrected residual display the twist attached to ψ_j is INDEXED j−1: ψ₂ carries S11.3's fixed letter-power unit, ψ₃ carries w₂, and ψ_j carries w_{j−1} for j ≥ 4 — read every ψ_j^{(ω_j)} in S12.1's clause (b) as ψ_j^{(ω_{j−1})} with ω₁ = the S11.3 unit (the outer ψ₁ leg handled separately as accepted). The display as first written demanded w_{n+1} at the top term, exceeding the assumed 𝒲_{≤n}. Correspondingly, the dependency chain diagram is read under the ambient hypothesis 𝒲_{≤n} as a whole (its first arrow consumes [GENTOW5-W(n)] with the earlier instances ambient). R-i4 (the lift rung) is unaffected and was DISCHARGED. Awaiting sol re-confirmation in the next queue.”

**CONDITIONALITY:** This is the **last mathematical correction** in the note; the later T5 consumption append explicitly makes no correction. Its closing protocol sentence (“Awaiting sol re-confirmation in the next queue”) is an as-of certification-protocol state, not a mathematical qualifier.

**DERIVATION:** Index bookkeeping made forced by the hypothesis set: clause (a) at index `r` supplies `w_r` for `ψ_{r+1}`, so the twist on `ψ_j` must be `ω_{j−1}`; the original indexing would have demanded `w_{n+1}`, which `𝒲_{≤n}` does not supply.

**RESOLUTION TRACE:** Base lines 2299–2313; corrects `.32` item 2 and fixes how `.33`'s chain reads. It is the governing reading of clause (b)'s twisted residual display at i ≥ 3.

**SUPERSESSION KIND:** replacement.

**TARGETS:** `EFF.GENTOW5.s2of2.32`, `EFF.GENTOW5.s2of2.33`, and `EFF.GENTOW5.s1of2.28`.

**CHAIN:** `psi_j^{(ω_j)}` → **`psi_j^{(ω_{j-1})}` TERMINAL**; the top term now consumes `w_n`, never `w_{n+1}`.

XREF: `runs/cert3/D3i_gentow5_output.log:NEW-ISSUE` — grep-verified count **2**; and `DISCHARGED` — count **2**.

**TEETH:** AUDIT: decorrelated-model index audit (D3i); the `ψ₁` leg is explicitly carved out (“handled separately as accepted”).

---

## 3. Consumption tables

### 3.1 Verified import/XREF designations [TABLE]

Every designation below was checked with fixed-string `grep -cF` in the named target file (template rule 2). Rows 17–20 target repo records rather than proof notes; they are verified the same way.

| # | Target and designation | Count | Material consumed by GENTOW5 §§1475–2313 |
|---:|---|---:|---|
| 1 | `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B` | 32 | The landed r3 B-law re-scoping clause (a) |
| 2 | `GENTOW2_PROOF_2026-08-09.md:[r3 RESTATED]` | 1 | The r3 restatement tag of that law |
| 3 | `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` | 11 | The single cross-frame unit `w`; the root correspondence; the level-i computation NOT reproduced |
| 4 | `GENTOW2_PROOF_2026-08-09.md:THEOREM GENTOW2-A` | 8 | Hypothesis-(ii) quantifier accepting the twisted residual |
| 5 | `GENTOW2_PROOF_2026-08-09.md:S5.1` | 42 | The LETTER FORMULA behind the i = 1 re-scope |
| 6 | `GENTOW2_PROOF_2026-08-09.md:Cor 5.6` | 6 | The FGMN residual identification at i = 1 |
| 7 | `GENTOW2_PROOF_2026-08-09.md:[Q4]` | 5 | Lemma 5.3(1), the i = 1 KP-membership leg |
| 8 | `GENTOW2_PROOF_2026-08-09.md:[Q10]` | 6 | FGMN Corollary 6.4 (the (b) cite) |
| 9 | `GENTOW2_PROOF_2026-08-09.md:(23)` | 4 | The source display re-indexed by S11.5 |
| 10 | `GENTOW2_PROOF_2026-08-09.md:Cor 6.4` | 11 | Firing order in the S12.1 dependency chain |
| 11 | `GENTOW1_PROOF_2026-08-09.md:S2` | 16 | The GENTOW-1 template re-read at source for the (c) re-index |
| 12 | `HE7_PROOF_2026-08-08.md:ANNEX-THEOREM R1-c` | 3 | The `bound_{i+1}` recursion's primary source |
| 13 | `GENTOW5_WI_2026-08-10.md:[GENTOW5-W(i)]` | 24 | The certified companion lemma; the frozen GENTOW5 fence nevertheless remains explicit |
| 14 | `CODEX_TOWERRAT2_2026-08-10.md:A-F1` | 3 | RUN A's CRITICAL finding |
| 15 | `CODEX_TOWERRAT2_2026-08-10.md:A-F2` | 2 | RUN A's first GAP (→ the open lemma) |
| 16 | `CODEX_TOWERRAT2_2026-08-10.md:S2` | 6 | The record's GENTOW5 section |
| 17 | `GENTOW2_passPE5_report.md:verifiably admissible` | 1 | Admissibility of `ψ₃^{(w)}` for every `w ∈ K₂^×` |
| 18 | `GENTOW2_passPE6_report.md:w-avatar` | 6 | The first measurements of `w` (≠ 1 at every measured prime) |
| 19 | `runs/cert/D1a_gentow5_output.log:INSUFFICIENT` | 2 | D1a residual finding 2, repaired by S12 |
| 20 | `runs/cert/D1a_gentow5_output.log:NEW-ISSUE` | 2 | D1a residual finding 4, repaired by S12 |
| 21 | `runs/cert3/D3i_gentow5_output.log:NEW-ISSUE` | 2 | The twist-index adjudication |
| 22 | `runs/cert3/D3i_gentow5_output.log:DISCHARGED` | 2 | The R-i4 discharge |
| 23 | `T5_WFRAME_2026-08-12.md:WF-w` | 16 | Reverse consumer designation for the conditional fence, verified after the 2026-08-15 append |
| 24 | `T5_WFRAME_2026-08-12.md:I4 — GENTOW5-PE3` | 2 | Reverse consumer designation for the avatar-coherent PE3 seventh-prime row |

**Arithmetic audit:** 24 designation rows; the occurrence-count column sums to **213**. Fresh row recount = closing XREF tally **24**. Every individual count was recomputed with fixed-string grep; the sum is only a checksum, not a semantic multiplicity.

**Designations counted but NOT emitted as XREFs:** `LEMMA GENTOW2-B [r3 RESTATED]` as a composite string (count **0**; both components verified — row 1 and row 2 — and the referent is unique, so it is recorded as GENTOW5's own compression); `GENTOW2-A(c)` (count **0**; parent `THEOREM GENTOW2-A` verified at row 4, clause letter carried descriptively).

**Files verified to exist (path checks, not designations):** `verification/openmath/towerrat2_runA_gentow5_output.txt`, `verification/openmath/gentow5_af1_direction_check.py` and its `_output.txt`, `runs/cert2/E12_gentow5_output.log`, `runs/cert2/E12_gentow5_brief.txt`, `runs/cert3/D3i_gentow5_output.log`.

### 3.2 Commit and artifact pin verification [TABLE]

Every commit-shaped pin cited by an in-range unit was checked with `git cat-file -t`; every row below returned `commit`:

| Pin class | Verified commits |
|---|---|
| Pass/fresh-run pins | `0160b94`, `18900e03`, `39c36aa`, `40f313a`, `75923bc`, `9f0eca7`, `ade1727`, `b22b37b` |
| Supplier/consumer and source-state pins | `33f8620`, `4caf0fb`, `acdf97a`, `d798529`, `eeac45f6` |
| Freeze/edit-history pins | `43b42e9c`, `a803a2ce`, `cc7c944`, plus source last-touch `ddfc6b61` |

Artifact verification was fresh against the working tree:

| Artifact | Current md5 | Disposition |
|---|---|---|
| `verification/openmath/gentow5_checks.py` | `5fa684c74326aea31d2b065b373fcf22` | PINNED; matches source prefix |
| `verification/openmath/gentow5_output_exact.txt` | `dc499a4967537d157756905c21104acb` | PINNED; matches source prefix |
| `verification/openmath/gentow5_output_full.txt` | `839a866006f9f6fc341a789c463a763a` | PINNED; matches source prefix |
| `verification/openmath/gentow5_rider_f32dev.py` | `81bbb5db3a8a40b211a7f1101d865e91` | PINNED; matches source prefix |
| `verification/openmath/gentow5_af1_direction_check.py` | `82acd3d2f48e5d03b50c4e2cf181370b` | PINNED; matches S11.6 |
| `verification/openmath/gentow5_af1_direction_check_output.txt` | `503279efe175eef3cdf6896c0962a1c9` | PINNED; matches S11.6 |

Historical note-body md5s (`85efc5b4…`, `4292d8c8…`, `d9e6b5ba…`, `0b850dda…`) are **AS-OF-PIN** evidence: they were checkable at their append times but are not current-file checksums because the note grew by design.

### 3.3 Reverse consumer edges: mathematical supply versus append protocol [TABLE]

| Consumer | Exact verified designation | Supply direction | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| `GENTOW5_WI_2026-08-10.md` | `[GENTOW5-W(i)]` (24) | **Reverse supplier**: WI proves the lemma GENTOW5 fences | Corpus-level theorem exists; frozen GENTOW5 still retains `𝒲_{≤n}` | The 2026-08-15 append explicitly refuses an automatic discharge |
| `GENTOW2_PROOF_2026-08-09.md` | `LEMMA GENTOW2-B″` (11) | GENTOW5 consumes | Level-2 law consumed verbatim; level-i version NOT reproduced | No append landed on GENTOW2 by this note |
| `T5_WFRAME_2026-08-12.md` | `WF-w` (16); `I4 — GENTOW5-PE3` (2) | **Reverse consumer**: T5 consumes GENTOW5 S12.1/S11.2 and the PE3 row | T5 takes the cumulative fence/proved fixed-unit half and the PE3 result only as avatar-coherent, never as an intrinsic upgrade | Dated append landed 2026-08-15; all checks PASS with two riders |
| `CODEX_TOWERRAT2_2026-08-10.md` | `A-F1` (3), `A-F2` (2) | External adversarial run consumed | 5/5 adjudicated REAL; 4 discharged, A-F2 converted to the open lemma | S11 is the note-side record; the codex record is byte-separate |
| `runs/cert/D1a_gentow5_output.log` / `runs/cert2/E12_gentow5_output.log` | `INSUFFICIENT` (2), `NEW-ISSUE` (2) | Certification findings consumed | Both residuals repaired at S12 | Ledger line inside the note: “row 10 → both residuals repaired, awaiting sol discharge (cert3)” |
| `runs/cert3/D3i_gentow5_output.log` | `NEW-ISSUE` (2), `DISCHARGED` (2) | Certification findings consumed | Twist index corrected; R-i4 DISCHARGED | The HOME-range sentence says “Awaiting sol re-confirmation”; later ledger status is a reading note, not an edit |

**Arithmetic audit:** 6 edge rows; the ten displayed designation counts sum to **66** (`24+11+16+2+3+2+2+2+2+2`). Counts shared with §3.1 agree exactly; no consumer edge lacks a verified designation.

---

## 4. NON-IMPORTS [TABLE]

| Fence | Explicit material not imported or not proved in lines 1475–2313 |
|---|---|
| Grid closure | The two-directional grid closure is WITHDRAWN; only the forward direction and the single-step top-rung converse survive; “no two-directional grid agreement is consumed anywhere in the repaired chain.” |
| Converse direction | “The converse rewriting … is weight-nondecreasing by the same displays.” — “FALSE as written.” |
| Annex ride | “the ride carries (SLOT_i)/(LIFT_i) counting statements, not GENTOW2-B‴s normalizer-cocycle monomial computation.” |
| Single-`w` form | `[GENTOW5-W(i)]` at i ≥ 3 is “NOT PROVED … this note does not reproduce” it — “the honest-sorry analogue”. |
| w-blindness | “A fixed per-grade unit family is not enough: ‘w-blind’ means invariance AFTER the family has been proved to have the single-w_i geometric form. It does not construct that form.” |
| T5 definition audit | The 2026-08-15 append records S11.2's superseded w-blind scope walk as a T5 **NON-IMPORT**; T5 references it only to record its withdrawal. |
| i = 1 tie | “the tie u1 = w_1 = R_{2,kbar_1}(nhat_1(u_2)) is OPEN”; the fold's “exponent-level tie … is NOT claimed”. |
| Automatic floor | At n ≥ 3 “only its claimed automatic derivation from the recipe is conditional” — the inequality may be a datum, but is not derived. |
| Lift rung | “No recipe consumer needs \(m_t>\operatorname{bound}_{i+1}\)”; S11.4's `bound_{i+1}` assertion is WITHDRAWN. |
| Machine discrimination | “The S4 depth-4 witness is w-trivial (K_i = F_2), so the machine record does not discriminate this fence.” |
| Sealed artifacts | “no runner edited, no sealed re-run” (S11.6); “Sealed artifacts untouched this round”. |
| Statement displays | “Statement displays above stay byte-intact; corrections are by dated supersession … and dated fences.” |
| Certification status inside HOME | “Awaiting sol re-confirmation in the next queue.” is the HOME-range protocol sentence; later certification-ledger state is a reading note, not a textual supersession. |

---

## 5. Teeth inverse table [TABLE]

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| `gentow5_af1_direction_check.py` C1 (interior rung) | `.18` | Executable regression, ISOLATED re-check (not the sealed battery) |
| C2 (the 85 → 84 drop at floor rung 3's tight margin) | `.18`, `.22` | Executable regression |
| C3 (170 top-rung preservation) | `.18`, `.19` | Executable regression |
| C4 (forward nondecreasing) | `.19`, `.20` | Executable regression |
| C5 (exact `Z[x]` identity + canonical `Phi_1`-adic development of `Phi_3`) | `.21` | Executable regression |
| C6 (level-1 polygon / descmin = 10) | `.21` | Executable regression |
| C7 (the rho-ladder `rho = (0, 1/8, 1/8)`, strict at rung 2: 21 > 20) | `.22` | Executable regression |
| C8 (margin instance `43/4 − 1/2 = 41/4 > 10`) | `.23` | Executable regression |
| `gentow5_rider_f32dev.py` (7 checks / 0 violations: halfway identity, completion relation, canonical dev, slot legality, pins vs the byte-frozen artifact row, chord clearance 186 > 170, `Phi_4@Phi_2` already canonical) | `.07`, `.11` | Executable regression, rider helper |
| P-B3 committed rows `f32@Phi4`, `Phi4@Phi3` (pins `[682,inf,0]`, `[170,inf,0]`) | `.07` | Executable regression used as a REFUTATION of the composed (i+2)-pairing |
| P-B3 committed rows `f32@Phi3`, `Phi4@Phi2` (pins `[340,inf,186,inf,0]`, `[84,inf,50,inf,0]`) | `.07`, `.29` | Executable regression VERIFYING the corrected pairing and the re-indexed residual |
| `FA1-LIFT` (`gentow5_pe2_fresh.py` @ 40f313a, 22/0) | `.02`, `.03` | Executable regression; asserts a non-existence and runs the re-solved member |
| S7 F-3 worked grid equality (top carry preserves weight) | `.04` | PROOF-ONLY: no dedicated PE2 row; the repair points to the already-worked equality fence |
| Compound `(vartheta live × e_stage≥2)` | `.05` | disclosed non-repair: the source says the compound has “NO machine contact” |
| PE5 fresh route (`gentow5_pe5_fresh.py`, GREEN 40/0; first mu = 3 (c)-read; first odd-p proper-(2,2) mid-stage tower at depths 3 and 4) | `.10`, `.14`, `.15` | AUDIT: hostile-pass certification on a fresh instrument |
| Consecutive PE4/PE5 clean hostile passes | `.13` | hostile-pass certification: process acceptance tooth, distinct from mathematical hypothesis discharge |
| PE3 fresh leg W (`gentow5_pe3_fresh.py` @ 9f0eca7) + GENTOW2 PE6 (`w-avatar`, 6 hits; fresh route GREEN 68/0, seal ade1727) | `.08` | Measurement (7 primes; `w ≠ 1` at each) |
| GENTOW2 PE5 @ 75923bc (`verifiably admissible`, 1 hit) | `.02` | Foreign-note verification of admissibility at every `w` |
| Byte-freeze / prefix-md5 discipline (S8/S9 heads, acceptance ledger, S11.6 two commits; `+77/-0`, prefix md5 `e9c5a20d` at L561) | `.01`, `.06`, `.13`, `.16`, `.30` | Document-integrity check (append-only proof) |
| Grep audits: S11.1's three-string closure audit; PE4-F-1's `T_1 / kappa_1 / psi_1^mu / level-0 read` audit; S11.3's w_1-consumer audit | `.10`, `.20`, `.24`, `.27` | Signed non-applicability (negative checks) |
| RUN A (`CODEX_TOWERRAT2`, 5/5 REAL) | `.17`–`.29` | AUDIT: decorrelated-model audit; individual repairs use the rows listed above/below |
| Worked low-height integrality failure (`nhat_1(-2)` demands `pi^{-1}`) | `.28` | signed counterexample to unrestricted `m`; the next-rung repair is later withdrawn |
| Orchestrator re-computation of `(bound_1..bound_4) = (1,7,35,155)` vs heights `(5,21,85,341)` | `.35`–`.40` | arithmetic recount, independently re-run before transcription |
| S4's `K_i^×={1}` witness against the higher-rung `w` fence | `.25`, `.26`, `.31`–`.34` | signed vacuity disclosure: the witness makes every geometric law tautological and cannot discriminate the fence |
| `[GENTOW5-W(i)]` proof-side conditionality | `.25`, `.31`–`.34` | PROOF-ONLY: “the machine record does not discriminate this fence”; guarded by the source's explicit coverage-hole sentence |
| D1a → E12 → D3i certification chain (`INSUFFICIENT`/`NEW-ISSUE`/`DISCHARGED` labels grep-verified in the logs) | `.31`–`.35`, `.41` | AUDIT: decorrelated-model audit and discharge certification |

**Both-direction audit:** every row guards at least one in-range unit, and every in-range unit with a non-empty `TEETH` field appears in at least one row. Only `.09` and `.12` carry `TEETH: NONE`; they are pointer/status declarations outside the battery claim. Proof-only and audit units are explicitly classified rather than silently left blank. **Zero battery-row orphans; zero toothed-unit orphans.**

---

## 6. Boundary self-audit

GENTOW5 is tag-sparse prose (`\tag{` density 0.00), and this shard is entirely *records* — three repair rounds, an acceptance record and two dated appends. Two boundary rules were applied.

1. **One unit per numbered finding.** S8's four `PE2-F-*`, S9's three `PE3-F-*`, S10's two `PE4-F-*` and S11's five `A-F*` repairs each became one unit (`.02`–`.05`, `.07`–`.09`, `.10`–`.11`, `.18`+`.25`+`.27`+`.28`+`.29`). This is the note's own atomization: each finding names one target sentence, has one derivation and one disposition. Merging a round into a single unit would have destroyed the per-finding disposition that the teeth table needs.
2. **Sub-lemmas of a repair are their own units.** S11.1's replacement derivation is split into `.21`/`.22`/`.23` because the note itself numbers them (S11.1.1/2/3), they have *different* conditionalities (S11.1.2 is unconditional floor arithmetic; S11.1.1 and S11.1.3 consume clause (b)), and S12.1 later distinguishes them on exactly that line. The same rule split S12.2 into `.35`–`.39`: threshold correction, boxed inequality, recipe-range discharge, witness instance, refine consumers — five different claims with five different consumers.

Round heads (`.01`, `.06`, `.17`) are separate from their findings because they carry the byte-freeze assertions and the verdict counts, which the acceptance record then supersedes; grade/fence closers (`.09`'s tail, `.12`) are separate for the same reason. `.13`–`.16` split the acceptance record into verdict-box, chronology, companion fold and ledger: the first governs status corpus-wide, the third lands three brackets in shard 1, the fourth is a document-integrity record — three different downstream uses.

Merges deliberately NOT made: `.31` (the withdrawal + `𝒲_{≤n}` definition) is kept apart from `.32` (the four-item scope) because the definition is the conditionality vocabulary that shard 1's units cite, while the four items are the propagation; `.41` is kept apart from `.32` although it corrects it, because it is dated later and is the note's terminal correction.

---

## 7. SHARD NOTES

- **In-range supersession chains applied (resolution rules 3–5):** S12.2 ⊳ S11.4 (lift rung: `bound_i`, not `bound_{i+1}`); S12.1 ⊳ S11.2's unaffected-scope list (exact values, repo classes, `P`-membership, (c), (e) become conditional at n ≥ 3); post-D3i corrigendum ⊳ S12.1 item 2 (`ψ_j^{(ω_{j−1})}`). The acceptance record governs status for the whole note and is quoted in this shard's header.
- **Corrections landing on shard 1:** every `PE2-F-*`, `PE3-F-*`, `PE4-F-*` and `A-F*` item, plus S12.1's clause-by-clause conditionality and S12.2's range discharges, target base sentences homed in lines 1–1474. They are emitted here as records (their HOME) and are carried into the corrected base statements in `spec/EFF-GENTOW5-s1of2.md`. **No base statement is re-emitted in this shard.**
- **Range-edge audit:** line 1475 opens `## S8` (line 1474 is blank; S7 closes at 1473 in shard 1), and line 2313 closes the post-D3i corrigendum; line 2314 is blank and line 2315 opens the later T5 consumption append. **No source unit is cut at either edge.**
- **Terminal mathematical state:** the last correction is the post-D3i corrigendum (`.41`). The later T5 append is a non-superseding consumer record: it confirms the partial-withdrawal reading and records T5's use of the fence.
- **Numbering:** temporary IDs `EFF.GENTOW5.s2of2.01`–`.41`, to be reconciled with shard 1's `.01`–`.43` at the merge run.

---

## 8. Self-audit and OPEN-CALLS

### OPEN-CALL 1 — the accepted outer `ψ₁` leg is unnamed

The post-D3i corrigendum (`.41`) says “`ω₁ = the S11.3 unit (the outer ψ₁ leg handled separately as accepted)`”. Fixed-string grep finds `outer ψ₁ leg` exactly **1** time in this note and **0** times in every other openmath note; no supplier designation is given. S11.3 names the `ψ₂` residual re-scope, not a separately named outer-`ψ₁` theorem. No XREF is invented. **Decision needed:** identify the accepted source unit for the outer `ψ₁` leg, or make that acceptance self-contained in a later append.

### Resolved former calls

1. **WI perimeter:** resolved by the 2026-08-15 append. `[GENTOW5-W(i)]` occurs **24** times in `GENTOW5_WI_2026-08-10.md`, but the current GENTOW5 tail explicitly preserves `𝒲_{≤n}` on frozen GENTOW5 statements and records T5 as a consumer of that fence. Corpus certification is not silently installed as a textual discharge.
2. **Certification protocol:** resolved as two predicates. The HOME-range sentence remains an as-of protocol record; the external certification ledger is later reading evidence, not an edit to the frozen note. No mathematical unit depends on choosing one prose status label over the other.
3. **Floor chain:** resolved as two predicates, exactly as S12.1 states. An explicitly supplied floor inequality is usable as datum; its automatic derivation from clause (e) is conditional on `𝒲_{≤n}` at n≥3.

### Recorded source defects (flagged, not silently repaired)

1. **`.28`:** S11.4's bracket is addressed to “the S2.2 K_i-digit-lifts display”, but that display is homed in §S2.1. The referent is unique, so the bracket is applied to the §S2.1 display and the mis-pointer is recorded; S12.2, which supersedes the bracket, gives no section number.
2. **`.02`, `.25`:** the composite designation `LEMMA GENTOW2-B [r3 RESTATED]` does not occur verbatim in `GENTOW2_PROOF_2026-08-09.md` (count 0); both components do (`LEMMA GENTOW2-B` = 30, `[r3 RESTATED]` = 1). Recorded as the note's own compression, not emitted as a designation.
3. **`.27`:** the clause pointer `GENTOW2-A(c)` is not separately greppable (count 0); the parent `THEOREM GENTOW2-A` is verified (count 8). Carried descriptively.
4. **`.40`:** the provenance sentence attributes the finding labels “INSUFFICIENT finding 2” and “NEW-ISSUE finding 4” to D1a while naming the E12 log as the deriving run; grep confirms the labels live in `runs/cert/D1a_gentow5_output.log` (2 each) and are restated in `runs/cert2/E12_gentow5_brief.txt`, not in the E12 output log (0 each). The attribution as written is correct; the record is kept so the cross-read need not re-derive it.

### Fidelity audit

- Every CANONICAL STATEMENT is verbatim quotation or explicitly marked `[ASSEMBLED]`; no inverse, sign, quantifier, index, level, or implication direction was altered. Truncations are marked `…`.
- §S12's LaTeX displays are reproduced as LaTeX (the note switches notation there); §§S8–S11's ASCII displays are reproduced with their line structure. The only presentational changes are Markdown blockquote framing and backslash-escaping of `*` inside quoted prose (`.02`, `.03`, `.08`, `.22`, `.23`).
- No source table occurs in this range; nothing was prosified.
- All **24** XREF designations carry fixed-string counts ≥ 1, recorded inline and in §3.1. Two candidate designations with count 0 are explicitly NOT emitted as XREFs and are listed under recorded defects.
- Supersession is tracked as a chain, not a flat list: S11.4 is emitted as a unit **marked superseded** rather than deleted, because the note keeps it byte-intact and because part of it (the integrality failure instance) survives.
- Structural recount: **41** units, **41** FORM fields, **41** CANONICAL STATEMENT fields, **41** DERIVATION fields, **41** RESOLUTION TRACE fields, and **41** TEETH fields; zero retired `regression-record` types.
- Status, absorption and certification are kept as three distinct predicates: the acceptance record governs grade (ACCEPTED 2/2, ANNOTATED), S11.2/S12.1 govern mathematical conditionality, and the cert-log chain governs certification. The later T5 append adds a consumer edge without changing either theorem scope or acceptance.

EFF-GENTOW5-s2of2 COMPILED: 41 statements / 24 xrefs verified / 1 open calls
