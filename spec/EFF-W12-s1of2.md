# EFF-W12-s1of2 — CANONICAL EFFECTIVE-SPECIFICATION SHARD

**COMPILED-BY: opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).**

## 1. Shard header

**Source note:** `lean/notes/openmath/W12_PROOF_2026-08-08.md` — the project's central REDUCTION spine (THEOREM W-12.D).

**HOME range:** source lines 1–1271 inclusive (title/unit header · §S0 reconciliation · §S1 statement + the [r1]/[r3]/[r4] repair records + FIRING CHECK · §S2 proof of W-12.A with W12-L0/W12-L1 · §S3 drainage + the reduction proof · §S4 the weld interface [W12-H] · §S5 the J-D1 handoff · §S6 the eight honest boxes). Later text is used only to resolve material homed in that range.

**HEAD blob hash:** `9fbd5f9ddc5b60297a392f67ddc86cb29a516076` (clean in the working tree; last touched by commit `06958241`).

**Compilation context:** `spec/EFF_TEMPLATE_v2.md`; temporary IDs `EFF.W12.s1of2.<nn>`. Companion shard: `spec/EFF-W12-s2of2.md` (lines 1272–2453), which owns the battery, the arcs, the acceptance record and the 2026-08-12 dated appends that correct three statements homed here.

### Governing effective-text record

The acceptance record lives out of range, at the post-PE7 dated re-anchor (line 1956):

> “Provenance: passPE7 (report `W12_passPE7_report.md`, verdict commit fa3acb2: **CLEAN, 0C + 0G + 1 MINOR — the 2-clean counter COMPLETES 1/2 → 2/2; W-12 IS ACCEPTED, the note FROZEN, dated appends only**).”

and its freeze is re-asserted at that append's close:

> “Counter/freeze: W-12 stays ACCEPTED 2/2 (this append is the MINOR's prescribed cure, not a repair round; no text above this append touched; runner + artifacts byte-frozen at seal f669cb0; the note body before this append = 124,423 bytes, md5 42a7655e, re-verified as byte-prefix after appending).”

The post-acceptance appends state the same discipline (line 2009):

> “Everything above this heading is byte-untouched by this append.”

**Effective text for this shard = the base body of lines 1–1271 as written, READ AS CORRECTED by (i) the in-range dated brackets `[r1]`–`[r5]`, and (ii) the out-of-range 2026-08-12 dated appends, which correct three statements homed here.** The three corrections are load-bearing and are applied at their units:

1. the **level-0 decoration-orbit factor** `κ(T)` in W-12.A (lines 2032–2091);
2. the **all-degree order-1 history-transfer** obstruction (2012–2030) and its **discharge** by LEMMA W12-HT (2192–2453) — after which W-12.A's controlling formula is `(HT-global)`, not the S1 display;
3. the **rationality/uniformity of the core coefficient** `c_F` in W-12.D hypothesis (A1) (2093–2141);

plus a fourth, purely bibliographic: the **W12-BOX-1 dependency range** `(H-a)–(H-d)` → `(H-a)–(H-e)` (2143–2153).

### Scope split

**ABSORPTION/supply SET.** The note's own grade summary (line 316):

> “**GRADE SUMMARY: (iii) PROVED as stated; (i) PROVED at the order-1 layer of every degree (+ the named instances machine-sealed), CONDITIONAL at orders ≥ 2 on the displayed [W12-H]; (ii) theorem at n = 2 (consumed), exact-DBL-term + bounds at n = 3 (W-12.C PROVED as stated), precise conjecture in general. Attempt 0/2.**”

and the one-line hypothesis ledger at §S9 (out of range, quoted here because it fixes this shard's supply perimeter):

> “**One line: THEOREM W-12.A's hypothesis set = {classical Hensel/Ore/censuses}; THEOREM W-12.C's = {that + THEOREM W-11 @ its pins}; THEOREM W-12.D's = {nothing — an unconditional reduction}; the weld corpus enters only [W12-H] (the order-≥ 2 program) and §S5's display.**”

“Attempt 0/2” is superseded by the acceptance record (ACCEPTED 2/2).

**APPEND/consumption PROTOCOL scope.** Separate predicate, and explicitly asymmetric here: this note RECEIVES two verbatim annexes (from HEX3 and HMENU3, both homed in shard 2) that discharge two of its own boxes, and it OWES one correction outward, un-landed:

> “The HMENU3-side dated annex is drafted verbatim for application at `lean/notes/openmath/HMENU3_annex_draft_r5.md` (application to HMENU3_PROOF_2026-08-08.md is the orchestrator's, per the same annex-fence convention ANNEX/ANNEX 2 follow here).”

No consumption append is claimed landed on any supplier by this note.

### Resolution rules applied

1. Base body lines 1–1271 supplies the HOME material for this shard.
2. In-range dated brackets `[r1]`, `[r2]`, `[r3]`, `[r4]`, `[r5]` are applied at their sites in chronology; the later bracket governs the earlier text it names. Struck text (`~~…~~`) is quoted as struck and NOT carried as effective.
3. The out-of-range acceptance record governs status: every in-range “attempt 0/2 / counter 0/2 / PEn next” sentence is historical, superseded by **ACCEPTED 2/2**.
4. The 2026-08-12 dated obstruction + discharge govern THEOREM W-12.A: its effective count law is `(HT-global)` (LEMMA W12-HT, shard 2), with the S1 display recovered as “the depth-zero specialization”.
5. The 2026-08-12 dated κ(T) correction governs W-12.A's level-0 prefactor at every depth.
6. The 2026-08-12 dated (A1) correction governs W-12.D's hypothesis interface: `c_F(X) ∈ ℚ(X)` fixed for the family, evaluated at `X = q`.
7. The 2026-08-12 dated BOX-1 correction governs W12-BOX-1's dependency range.
8. `[W12-H]`, `(H-a)`–`(H-e)`, and `(A0)`/`(A1)`/`(A2)` are this note's hypothesis-interface vocabulary and are emitted as first-class units (`.47`, `.12`, `.13`) — they are what downstream capstone conditionality is written in.
9. External repo records — the CITE-SCOPE resolution and the SOL certification ledger — are **reading notes**, never edits (§8).

---

## 2. Statement inventory

### EFF.W12.s1of2.01  [changes-record]

**CANONICAL STATEMENT:** Title line and unit header

> “# W12 — THE GENERAL-n ASSEMBLY (the J-D block's terminal rung): the order-1 shape-generic count law PROVED at ALL degrees (THEOREM W-12.A), the general drainage law stated precisely with the n = 3 double-root term EXACT (THEOREM W-12.C partial; CONJECTURE W-12.B), and THE REDUCTION THEOREM (THEOREM W-12.D, PROVED): exact menu laws + drainage ⟹ ONE R_τ ∈ ℚ(q) per splitting type at every prime power, both characteristics, wild included — conditional structure displayed the way `montes_unconditional` displays its hypotheses”

> “**Unit:** W-12, the J-D block's terminal rung after THEOREM W-11(n = 2) (GRT_WELD_BLUEPRINT_2026-08-08 §S3.1 row W-12; execution-order step (8); WELD_SYNTHESIS_2026-08-05 §4(ii)). **Attempt grade 0/2** (**[r5, PE5 m2: the display that followed was the [r1]-era arc — SUPERSEDED; the CURRENT arc is the [r5] ARC at the end of this note, marked the same way as the [r1] and [r3] displays]** ~~arc: composed → PE1 NOT CLEAN 1C+3G+2m @ 2b47711 → r1 THIS REPAIR, note-only, [r1] tags, minimality contract — F1 (CRITICAL, W-12.A display) + F2/F3/F4 + m1/m2 repaired in place; counter 0/2; PE2 next~~).”

> “Per the effort directive (Asvin 2026-08-05) W-12 IS the complete-theorem target of the block: composed at the strength actually proved, honest boxes over reach, every supplier pinned as-of.”

**CONDITIONALITY:** “Attempt grade 0/2” is historical, superseded by the acceptance record (ACCEPTED 2/2, resolution rule 3). The struck arc display is not effective text; the `[r5]` ARC (shard 2) is the current one.

**DERIVATION:** Header record, no derivation.

**RESOLUTION TRACE:** Base lines 1–14; the arc display struck in place by `[r5]` PE5 m2; grade superseded at line 1956.

XREF: `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:the faithfulness handoff (J-D1)` — grep-verified count **1** (the W-12 row itself, blueprint line 302; the string `W-12` occurs **4** times there).

XREF: `docs/in-progress/WELD_SYNTHESIS_2026-08-05.md:(ii) J-D composition plan: BLUEPRINT ROUTE` — grep-verified count **1** (the cited `§4(ii)`; note the file's `§4. RECOMMENDATION` header carries no `W-12` string — the plan names W-10/W-11).

**TEETH:** NONE (header).

---

### EFF.W12.s1of2.02  [fence]

**CANONICAL STATEMENT:** Composition provenance (disclosed)

> “**Composition provenance (disclosed):** this is the FIFTH incarnation of the unit (four prior composer sessions died to API errors mid-draft; their partials are archived OUTSIDE the repo in /tmp/k2res_partial_archive/ and were treated as UNTRUSTED scaffolding — every statement kept here was re-derived from scratch in this session; the archived S7 bookkeeping totals failed re-derivation and are recomputed below; the archived drafts' own disclosed correction — a spurious (q^d−1)-per-interior-vertex factor in the census normalization of an earlier draft — was independently re-confirmed to be a necessary correction by the sweep argument of S2.2, which this session re-proved). This note was written and committed in increments (survival discipline); the SEAL commit is the one containing the final §S7 + the unrun runner.”

**CONDITIONALITY:** A provenance fence: the archived partials are declared untrusted and NOT a source; the spurious interior-vertex factor is named as a defect that the re-proof independently excludes.

**DERIVATION:** The re-confirmation named here is `.24`'s right-to-left sweep argument.

**RESOLUTION TRACE:** Base lines 15–26; untouched.

**NON-IMPORT (explicit):** the archived drafts are “UNTRUSTED scaffolding” and supply nothing.

**TEETH:** The sweep argument at `.24`, cross-checked against W-11's 2SIDED row and W-10's (2,1,1) row.

---

### EFF.W12.s1of2.03  [battery-frame]

**CANONICAL STATEMENT:** Instrument summary (header)

> “**Instrument:** sealed two-commit battery `verification/openmath/w12_checks.py` (23 cubic census rows = 7,105,774 cubics covered with 2,946,008 DBL/TRP lifts read individually; 8 quartic quadruple-center stratum rows = 580,550 members; 11 history-resolved quadratic rows = 69,053 polynomials; PARI/GP independent σ-multiset oracle on 40,645 cubics + 1,516 quartics + 85 constructed species ambiguity-witness pairs; the n = 3 drainage decomposition with the DBL term as a THEOREM row and U₃^TRP measured EXPLORATORY under a disclosed conservative convention; four teeth). Verdict §S10, appended at commit 2 FROM the committed artifacts.”

**CONDITIONALITY:** Two disclosed scope limits are carried by the summary itself: `U₃^TRP` is EXPLORATORY under a conservative convention (not a σ-decidedness claim), and the oracle is PARI-based on mixed-characteristic rows only (W12-BOX-6, `.52`).

**DERIVATION:** Instrument declaration; the row inventory and verdict are homed in shard 2 (§S7/§S10).

**RESOLUTION TRACE:** Base lines 26–35. Scope of the 85 witness pairs is later narrowed by `[r5]` MINOR 3 (shard 2): 70 are the S3.2 proof's pairs, 15 are the sealed `B = 0` pair that `[r4]` deleted from the proof.

**TEETH:** This unit names the battery; its inverse table is shard 2's.

---

### EFF.W12.s1of2.04  [scope-record]

**CANONICAL STATEMENT:** What W-12 is (one breath)

> “W-10 proved ONE count equality at ONE order-1 shape ((2,1,1) Eisenstein quadratics); W-11 proved the COMPLETE menu at n = 2 with the exact drainage law q^(−N). W-12 is the assembly rung the uniformity directive (Asvin 2026-08-03: ONE R_τ ∈ ℚ(q) per splitting type, all orders and all primes AT ONCE) actually needs: (i) the shape-generic count law — proved outright at the order-1 layer of EVERY degree (THEOREM W-12.A), with the orders-≥ 2 layer stated through the weld machinery as a displayed hypothesis box; (ii) the general menu-exhaustion/drainage law — stated precisely (CONJECTURE W-12.B), with W-11's q^N as the proved n = 2 instance, the n = 3 double-root stratum drained EXACTLY here (THEOREM W-12.C, via the block-transfer LEMMA W12-L1 consuming W-11's per-center law), and the triple-center residue boxed with its exact obstruction; (iii) THE REDUCTION THEOREM (W-12.D): (i) + (ii) imply one R_τ ∈ ℚ(q) per splitting type at every prime including wild — proved unconditionally AS a reduction, and it FIRES unconditionally at n = 2 (re-deriving W-11's densities through the general mechanism). The blueprint row's own J-D1 faithfulness-handoff composition display is §S5, at its own S-price.”

**CONDITIONALITY:** The clause-(i) claim “proved outright at the order-1 layer of EVERY degree” is exactly what the 2026-08-12 obstruction challenged and the W12-HT discharge restored (resolution rule 4).

**DERIVATION:** Orientation paragraph; derivations are §§S2–S3.

**RESOLUTION TRACE:** Base lines 37–54.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — grep-verified count **3**.

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:THEOREM W-10` — grep-verified count **2**.

**TEETH:** NONE (orientation).

---

### EFF.W12.s1of2.05  [scope-record]

**CANONICAL STATEMENT:** §S0 — the blueprint's W-12 row and the divergence box

> “**The blueprint's W-12 row, verbatim** (GRT_WELD_BLUEPRINT_2026-08-08 §S3.1):
>
> > | **W-12** | the faithfulness handoff (J-D1): under W-0..W-9 the corpus proves the (H1) residue-structure package at orders ≥ 2 on the welded class — the composition display, consuming the IFK faces downstream, owning nothing of them | J-D | **S** (composition; conditional on IFK downstream) | all above | (GR-B) RE-ACCEPTED print package at its own perimeter |”

> “**Divergence box (explicit).** The blueprint's W-12 row is the J-D1 composition display ONLY — an S-priced bookkeeping rung. The composing charge, under the standing uniformity directive (Asvin 2026-08-03: general uniform strategy, all-orders-all-primes AT ONCE, not a degree-by-degree crawl), directs W-12 at the general-n assembly that the J-D block is FOR. Both are delivered, separately graded: S1–S4 are the assembly (the new mathematics of this note, graded clause by clause); §S5 is the blueprint row's own composition display, executed at the accepted-supplier grades with every open residue named — a display, no new proof claimed there, "owning nothing of" the IFK faces exactly as the row prices it. The dependency column "all above" is honored in S9 (every consumed supplier pinned as-of); the (GR-B) partial is cited only inside §S5. No other divergence.”

**CONDITIONALITY:** The note delivers TWO separately graded things; the blueprint row itself is discharged only “AS THE DISPLAY IT PRICED” (`.50`).

**DERIVATION:** Charge-mandated reconciliation; no mathematics.

**RESOLUTION TRACE:** Base §S0, lines 58–82; untouched.

XREF: `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:the faithfulness handoff (J-D1)` — grep-verified count **1**. **Reading note:** the blueprint's section header is written `### S3.1 The twelve lemmas` (the string `§S3.1` has count **0** there); the row is at blueprint line 302.

**TEETH:** NONE (reconciliation).

---

### EFF.W12.s1of2.06  [scope-record]

**CANONICAL STATEMENT:** §S0 — Reconciliation with W-11 §S4.3 (the stated general-n program)

> “W-11 closed n = 2 and stated the general program as (P1) the node system, (P2) the per-node exhaustiveness identity with owed inputs (universal S_λ(q) censuses at g ≥ 2, the JA-GRID/JB-VTX position faces incl. JB row-12's open membership residue, the JC no-cancellation warrant at composite stages), (P3) the uniform drainage bound. THIS note executes the program's provable slice and composes the rung the program was for: (P2)'s census-times-lattice structure is clause (i) — and the S_λ(q) censuses at g ≥ 2 enter as EXPLICIT classical counting polynomials, re-derived and machine-checked at g = 2, 3 in both characteristics, so that owed input is DISCHARGED at the order-1 layer; (P3) is clause (ii); the assembly they feed is clause (iii), which S4.3 did not state and which is W-12's own theorem. (P1) appears as the organizing frame of S1's conventions (definitions, not theorems). The JB row-12 residue and the JC composite-stage warrant remain owed by the order-≥ 2 layer exactly as W-11 priced them (W12-BOX-1).”

**CONDITIONALITY:** One of W-11's three owed inputs (the `S_λ(q)` censuses at `g ≥ 2`) is discharged **at the order-1 layer only**; the other two stay owed at orders ≥ 2.

**DERIVATION:** Program-to-clause mapping; each mapped item's derivation is its own section.

**RESOLUTION TRACE:** Base §S0, lines 84–99.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:S4.3` — grep-verified count **10**.

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-VTX` — grep-verified count **77**. **Reading note:** W12 writes “JB row-12”; the hyphenated `row-12` has count **0** in GRTJB_PROOF, while `row 12` has count **9** — orthography, not a missing referent.

**TEETH:** The `g = 2, 3` censuses are machine-checked in both characteristics (`.25`, battery families W12-SHAPE/W12-QRT).

---

### EFF.W12.s1of2.07  [fence]

**CANONICAL STATEMENT:** §S0 — THE KEY DESIGN DECISION (three reasons the elementary route does not scale)

> “**THE KEY DESIGN DECISION (charge-mandated, reasoning displayed).** W-11 was proved at n = 2 by elementary classification — explicit Hensel/Eisenstein/Artin–Schreier case analysis of a 3-point polygon. That route does NOT scale to the general rung, for three separately fatal reasons, and the general clauses are therefore composed THROUGH the weld machinery:
>
> 1. **Letters leave the prime field.** At a branch with residual degree d ≥ 2 the residual censuses live over F_{q^d} inside the residue extension, and "count = census × lattice q-power" is meaningful shape-only because counts are blind to WHICH letters occur — LEMMA J-D0 (count-gauge-blindness, PROVED on its perimeter, pin 9387eb1), consumed as the frame of clause (i). The elementary route would re-prove J-D0's mechanism in every characteristic dialect at every shape (W-11 S2.1's census table already shows the loci diverging — Artin–Schreier vs square classes — while the counts agree).
> 2. **Composite stages appear.** At order ≥ 2 (repeated residual factors of degree ≥ 2 — realized already on this note's quartic rows, where the λ = (1²) residual opens a degree-2 key polynomial) there is no elementary recentering: the read runs through the OM engine with the carry calculus supplying no-cancellation/level-detection at wild composite stages (GRTJC's JC-PSIKER/JC-LOAD warrant, ACCEPTED 2/2 @ 83f47f4). Hand computation of residuals stops being a proof exactly there. The order-1 layer is proved outright below precisely because THERE the welded read reduces to monic-division digit calculus.
> 3. **The membership face at general shapes is the welded polygon.** W-10's H-3 and W-11 S3 could compute their grids outright because the abscissa grids are finite and tiny; the general order-≥ 2 membership faces are GRTJB's JB-VTX/JB-DEV (ACCEPTED 2/2 @ 83f47f4) with row-12's u ≥ 0 proviso residue OPEN. The general clause (i) at orders ≥ 2 must consume them; the order-1 layer (abscissa grids {0..m}, polygons computed outright per branch) does not — which is exactly where the PROVED/CONDITIONAL line is drawn in S1.”

> “So: clause (i)'s general form is stated with the weld suppliers as displayed hypotheses ([W12-H], montes_unconditional-style), while everything the direct digit calculus reaches — the order-1 layer at ALL degrees, the full n = 2 refinement tower (W-11 consumed, history-resolved here by LEMMA W12-L0), and the n = 3 double-root stratum (transported whole by LEMMA W12-L1) — is proved outright and machine-sealed.”

**CONDITIONALITY:** This is the note's own statement of WHERE the proved/conditional line falls, and it is the rationale for `[W12-H]` (`.47`).

**DERIVATION:** Three named failure modes of the elementary route, each with its supplier.

**RESOLUTION TRACE:** Base §S0, lines 101–141.

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — grep-verified count **4**.

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:JC-PSIKER` — grep-verified count **19**; `JC-LOAD` — count **31**.

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-DEV` — grep-verified count **63**.

**TEETH:** The quartic `λ = (1²)` stratum (`.31`) is the concrete order-2 frontier exhibit, volume law measured.

---

### EFF.W12.s1of2.08  [hypothesis]

**CANONICAL STATEMENT:** §S1 Conventions — the setting, the read, and the pinned σ-DECIDED predicate

> “Conventions. Fix a degree n ≥ 2. O a complete DVR with residue field F_q (either characteristic: mixed absolutely-unramified Z_p-type, v(p) = 1, or equal F_q[[t]]-type — the W-11 r2 pin inherited; as there, the pin is load-bearing only for p = 2 disc-spectrum displays, never for counts), π a uniformizer, window N ≥ 2; enumerate monic degree-n f over O/π^N (q^(nN) of them; unit: polynomials).”

> “The read is the recursive OM-convention read: level-0 factorization of f̄ over F_q; per repeated irreducible factor P̄ (degree d, multiplicity m ≥ 2), the Φ-adic branch development (Φ the read's fixed monic lift of P̄) and its principal Newton polygon; per side, the residual polynomial over F_{q^d}; separable residuals decide (Ore leaves); repeated residual roots of degree 1 ON AN e = 1 SIDE refine (recenter deeper), while on an e ≥ 2 side they open a key of degree e·d > d — an order-2 (composite) stage, exactly S2.5's QRT-G2(h;(1²)) row [r1: the sealed trichotomy misclassified this genre as "recenter deeper"; harmless at n = 3, where every e ≥ 2 side has g = 1 so no repeated residual can occur on one — PE1-verified in the completeness case tree, incl. the runner's never-firing `assert e == 1`]; repeated residual factors of degree ≥ 2 open order-2 (composite) stages.”

> “σ(f) = the splitting type = the multiset {(e_i, f_i)} of the étale algebra of a lift (Σ e_i f_i = n); f is σ-DECIDED at window N if every O-lift of f with disc ≠ 0 has the read's σ — pinned [r3, PE3 F1: the σ-pin] to W12-BOX-7's LIFT-CERTIFICATION notion: σ-DECIDED ⟺ the window digits force ONE σ across all disc ≠ 0 O-lifts (that σ is the read's output wherever the reader decides, and beyond the reader's window exit it is certified per stratum — the DBL side by W-11's PROVED SPLIT-TAIL leg; the TRP tail case is exactly the open tail-σ-certification lemma, HEX3-BOX-1). The read-anchored parse ("the conservative reader itself printed σ") is REJECTED: on a tail member (constant term window-hidden, reader exits) "the read's σ" is undefined, so that parse would count every tail member undecided — its computed price is recorded at the [r3] F1 record after the statement.”

> “[r4, PE4 R-1: the pinned predicate is TOTAL — its degenerate corner (a member with NO disc ≠ 0 lift, where "force ONE σ" would be false while the head clause is vacuously true) is EMPTY: disc of the generic monic degree-n polynomial is a nonzero polynomial in the coefficients (Π_{i<j}(x_i−x_j)² ≢ 0 over any field), the substitution a = f + π^N g is an invertible affine change of those coefficients, and a nonzero polynomial cannot vanish identically on O^n with O infinite — so every window class has a disc ≠ 0 lift, in every characteristic; at order-1 decided shapes every lift with disc ≠ 0 factors into distinct separable irreducibles (S2.3, and see its [r4] bracket for the wild equal-characteristic disc = 0 lifts that the quantifier correctly excludes).]”

> “A SHAPE T is the letter-free read datum: level-0 configuration (degrees + multiplicities), per-branch exact polygon, per-side residual factorization type λ, refinement history — never the letter values (J-D0 keying). ORDER 1 means: every key polynomial in the read has degree d (no composite stages opened).”

**CONDITIONALITY:** THE definitional pin of the whole note. Two notions were in play; the `[r3]` pin selects W12-BOX-7's lift-certification notion and REJECTS the read-anchored parse (whose price — divergence of the normalized residue at n = 3 — is `.16`). The predicate's totality is `[r4]` R-1. The SHAPE datum explicitly **includes refinement history** — the clause that the 2026-08-12 obstruction showed the S1 display did not honour (`.09`).

**DERIVATION:** The totality argument is quoted above (generic disc ≢ 0 + invertible affine substitution + a nonzero polynomial cannot vanish identically on an infinite `O`).

**RESOLUTION TRACE:** Base §S1, lines 145–193, with `[r1]`'s trichotomy correction, `[r3]`'s σ-pin and `[r4]`'s totality remark landed in place.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` — grep-verified count **11**; the open tail-σ-certification lemma named by the pin.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:SPLIT-TAIL` — grep-verified count **21**; the proved DBL-side certification leg.

**TEETH:** The runner's never-firing `assert e == 1` (PE1-verified) is the tooth for the `[r1]` trichotomy correction at n = 3.

---

### EFF.W12.s1of2.09  [lemma]

**CANONICAL STATEMENT:** THEOREM W-12.A — the order-1 shape-generic count law (clause (i))

> “**(i) [THEOREM W-12.A — the order-1 shape-generic count law] PROVED at all degrees n, all prime powers q, both characteristics, wild strata included.** Let T be an order-1 window-visible decided shape: level-0 configuration C = {(P̄_i, m_i)} (distinct monic irreducibles P̄_i of degree d_i, multiplicities m_i, Σ m_i d_i = n), and per repeated branch (m_i ≥ 2) an exact branch polygon P_i (all vertex heights ≤ N−1) with per-side residual factorization types λ_{i,S} over F_{q^{d_i}}, all residuals separable. Then the window-N count of monic f realizing T is EXACTLY
>
>     #T(N) = C₀(q) · Π_{i: m_i=1} q^{d_i(N−1)}
>             · Π_{i: m_i≥2} [ (Π_S S_{λ_{i,S}}(q^{d_i})) · q^{d_i·B_i(N)} ],   [r1]
>
>     B_i(N) = m_i·N − Σ_{j<m_i} ⌈P_i(j)⌉ − L_i,
>
> where C₀(q) is the classical level-0 configuration census, S_λ(Q) = #{monic degree-g polynomials over F_Q with nonzero constant term and factorization type λ} are the UNIVERSAL residual censuses, and L_i = #{lattice points j < m_i on the polygon P_i} — one q-polynomial per shape, counts factorizing cell by cell (every (configuration, residual-letter) cell has exactly Π_{i: m_i=1} q^{d_i(N−1)} · Π_{i: m_i≥2} q^{d_i B_i(N)} members [r1]), with NO value-layer hypothesis ((VD-m), (C-coll), (R-coll), (DMULT-s), PERIM-μ all absent, J-D0 frame) and NO dependence on the characteristic or on tame vs wild: dens_T := #T(N)/q^{nN} ∈ ℚ(q) is shape-only. σ(T) is read off by Ore's theorem: one étale piece (e_S, d_i·deg ψ) per side S and irreducible residual factor ψ of R_S. W-10(2,1,1) and every W-11 row are instances; SEVEN new cubic (triple-center) families + the quartic g = 2 families are derived in S2.4/S2.5 and machine-sealed (S7). **The order-≥ 2 layer (composite stages) is NOT covered: it is the displayed hypothesis box [W12-H] (S4.2) — the JC composite-stage warrant, the JB row-12 membership residue, the J-D1 (H1) package of §S5, the residue-tower censuses, and [r1] the order-≥ 2 GMN leaf/σ-decision theorem (H-e) are its named inputs (W12-BOX-1).**”

**CONDITIONALITY — the displayed law above is SUPERSEDED TWICE by out-of-range dated appends; both corrections are effective.**

(a) **Level-0 orbit factor** (2026-08-12):

> “In W-12.A's displayed count, the level-0 prefactor \(C_0(q)\) is corrected to \[ \kappa(T)\,C_0(q). \]”
>
> “\[ \kappa(T):= \prod_{d,m} \frac{r_{d,m}!}{\prod_D r_{d,m,D}!}. \]”
>
> “Thus the corrected depth-zero display is \[ \#T(N)= \kappa(T)C_0(q)\! \prod_{i:m_i=1}q^{d_i(N-1)} \prod_{i:m_i\ge2} \left[ \left(\prod_S S_{\lambda_{i,S}}(q^{d_i})\right) q^{d_iB_i(N)} \right]. \]”

(b) **Order-1 history coverage** (2026-08-12 obstruction, then discharge):

> “W-12.A's displayed count presently proves the depth-zero order-1 cell law, but does not prove its stated coverage of the full order-1 layer. An order-1 refinement history may contain earlier repeated residuals even though its terminal residual is separable.”

> “**W-12.A regains full order-1 coverage.** Its controlling formula is (HT-global), with complete histories, transfer normalization, and the dated level-0 orbit correction. The former display is the depth-zero specialization: there are no non-root \(D_v\)-terms and no internal history orbit.”

**Effective statement of THEOREM W-12.A = `(HT-global)`** (LEMMA W12-HT, shard 2):

> “\[ \boxed{ \#T(N)= \kappa_0(T)C_0(q) \prod_{i:m_i=1}q^{d_i(N-1)} \prod_{i:m_i\ge2}\mathcal H_i(T,N).} \tag{HT-global} \]”

with the in-range display recovered as its depth-zero case. The `[W12-H]` fence on the order-≥ 2 layer is unchanged by either correction (“Composite-stage and drainage boxes do not move”).

**DERIVATION:** Assembled in §S2: `.21` (level-0 product structure) × `.23`–`.24` (one branch: the digit calculus and the census normalization) × `.22` (the level-0 census), closed at `.27` (Ore leaves). At full generality the derivation is LEMMA W12-HT's five-step proof (shard 2), whose depth-zero specialization is the §S2 chain here.

**RESOLUTION TRACE:** Base §S1 clause (i), lines 197–230, with `[r1]`'s simple-branch repair landed in the display (`.15`); corrected by the two 2026-08-12 appends (resolution rules 4–5).

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — grep-verified count **4**; the frame that makes the law shape-only.

**READING NOTE (external, not an edit).** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` row **Q1 W12-2** retargets this clause's Ore citation: *“Ore's theorem … factors any `O`-lift `F`” | NS-1, NS-2 | re-cite [GN15] Thm 2.3”* — i.e. Guàrdia–Nart, *Genetics of polynomials over local fields*, Contemp. Math. 637 (2015), Theorem 2.3 (with eq. (2.1) for the `(e,f)` readout; [AGNPRW] Thm 4.4 + Prop 4.5 as the independent second leg), whose standing setting is an arbitrary discrete valued field. Verdict there: **COVERS-ALL-O**. The note's own text is compiled as written; the retarget is recorded, not applied.

**TEETH:** Battery families W12-LVL0, W12-SHAPE, W12-QRT (shard 2); teeth W12-T-SHAPE and W12-T-CENSUS4.

---

### EFF.W12.s1of2.10  [open-obligation]

**CANONICAL STATEMENT:** CONJECTURE W-12.B (DRAIN-n), stated precisely

> “* **CONJECTURE W-12.B (DRAIN-n), stated precisely.** For every n ≥ 2 there is c_n(q) ∈ ℚ(q), independent of the characteristic, with undecided(n, q, N) · q^{−(n−1)N} → c_n(q) as N → ∞ at every prime power q, where undecided(n, q, N) counts the window members NOT σ-DECIDED in the S1 Conventions' pinned lift-certification sense (W12-BOX-7's convention) — NOT the conservative-read residue, whose normalized mass DIVERGES linearly at n = 3 (THEOREM HEX3.A; the σ-scoping is load-bearing, [r3] F1 record below) — equivalently the normalized σ-undecided mass is c_n(q)·q^{−N}·(1 + o(1)) → 0 (hExhaust at degree n), and the decided window counts are given exactly by finitely many q-polynomial laws in the style of clause (i). PROVED instances and bounds: n = 2 is THEOREM W-11(iii) with the EXACT law q^N (c_2 = 1, zero error at every window); the general LOWER bound undecided(n, q, N) ≥ q^{(n−1)(N−1)} holds at every n ≥ 2 (S3.3) — so the conjectured rate is correct-in-order wherever the conjecture holds. GRADE: conjecture (the n ≥ 3 upper bounds are open).”

**CONDITIONALITY:** GRADE: conjecture. The quantity is σ-scoped to the pinned notion — under the rejected read-anchored parse the conjecture is FALSE at n = 3 (`.16`).

**DERIVATION:** Not derived; the proved instances/bounds are W-11(iii) (n = 2) and `.41` (the general lower bound).

**RESOLUTION TRACE:** Base §S1 clause (ii) first bullet, lines 232–249, with the `[r3]` σ-scoping landed in place. Out of range, §S10 P-6's `[r4]` F3 bracket states plainly that the battery's measured `U₃^conv` gives W-12.B **no** n = 3 corroboration in either direction.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — grep-verified count **11**; the exact conservative law whose normalized mass diverges.

**TEETH:** None that can confirm it; §S10 P-6 is EXPLORATORY and explicitly not this quantity.

---

### EFF.W12.s1of2.11  [lemma]

**CANONICAL STATEMENT:** THEOREM W-12.C (n = 3, partial)

> “* **THEOREM W-12.C (n = 3, partial). PROVED as stated.** For every prime power q, both characteristics, every N ≥ 2:
>
>       undecided(3, q, N) = (q−1)·q^{2N−1} + U₃^TRP(q, N),
>
>   where the first term — the σ-undecided mass of the double-root ⊗ simple-root level-0 stratum — is EXACT AND PROVED (LEMMA W12-L1 transporting W-11's exact per-center law q^{N−1}), and q^N ≤ U₃^TRP(q, N) ≤ q^{3N−2} (the triple-center stratum: lower bound by the constructed ambiguous species S3.2, upper bound = the whole TRP stratum, trivial). The EXACT U₃^TRP law is NOT derived: W12-BOX-3 displays its obstruction (the two-species n = 3 node calculus with reduced-window DBL re-entry), and the battery MEASURES it under a disclosed convention, EXPLORATORY grade. hExhaust at n = 3 is therefore NOT claimed; what is proved is the exact DBL drainage term + both bounds.”

**CONDITIONALITY:** Partial by construction. The bracket is later SHARPENED out of range by the BOX-3 annex (HEX3): “W-12.C's bracket sharpens to q^N ≤ U₃^σ ≤ q·u(q,N) with U₃^conv = q·u exactly.” The `[r4]` F3 bracket adds that post-pin this bracket “is uninformative about c₃ in BOTH directions”.

**DERIVATION:** The level-0 partition of `.36` (three separable patterns contribute 0; DBL contributes exactly `(q−1)q^{2N−1}` by W12-L1(c); TRP contributes `U₃^TRP`), with the lower bound from `.38` and the trivial upper bound from the stratum size.

**RESOLUTION TRACE:** Base §S1 clause (ii) second bullet, lines 250–265.

**TEETH:** Battery family W12-DRAIN3 (`DBL-undecided == (q−1)q^{2N−1}` on all 23 cubic rows) and tooth W12-T-DRAIN.

---

### EFF.W12.s1of2.12  [hypothesis]

**CANONICAL STATEMENT:** THEOREM W-12.D — the hypothesis interface (A0), (A1), (A2)

> “**(iii) [THEOREM W-12.D — THE REDUCTION THEOREM] PROVED, unconditional as a reduction.** Fix n and suppose, at every prime power q simultaneously:
>   (A0) [lift well-posedness] every window-decided member of a core family has ALL its disc ≠ 0 O-lifts of the read's type **[r4, PE4 F2(i): "the read's type" = the family's label σ_F — the reading that (A1)'s new σ-clause now fixes; under the r3 pin, read as the member's OWN forced σ this clause is a tautology, see the [r4] F2 record]**;
>   (A1) [exact core menu] there is a FINITE list of core families F — each with a splitting type σ_F **[r4, PE4 F2: and such that EVERY member of every class (F, x) is σ-DECIDED in the S1 Conventions' pinned lift-certification sense, with forced σ = σ_F — the σ-LABELING clause; this is what Step 4's lower bound consumes, and (A0) is then its (retained) well-posedness restatement]**, a parameter set P_F ⊆ ℤ^{d_F}_{≥0} that is a finite union of shifted products of arithmetic progressions, an affine visibility threshold ν_F, and a density law dens_F(x) = c_F(q)·q^{−ℓ_F(x)} with ℓ_F affine with strictly positive parameter coefficients — such that for every window N the classes (F, x) with x visible (ν_F(x) ≤ N) are PAIRWISE DISJOINT sets of window-N polynomials, each of EXACT count dens_F(x)·q^{nN}, with all data (families, c_F, ℓ_F, P_F, ν_F) independent of q and of the characteristic;
>   (A2) [drainage of the rest] r(N)/q^{nN} → 0, where r(N) := q^{nN} − Σ_{F, x visible at N} count(F, x) — everything not in a visible core family: the σ-undecided residue AND any window-boundary (tail) families.”

**CONDITIONALITY — (A1)'s final clause is CORRECTED out of range** (2026-08-12 dated correction, resolution rule 6). The correction quotes the span it replaces and supplies the replacement:

> “In W-12.D hypothesis (A1), replace
>
> > “a density law \(\operatorname{dens}_F(x)=c_F(q)q^{-\ell_F(x)}\) … with all data (families, \(c_F\), \(\ell_F\), \(P_F\), \(\nu_F\)) independent of \(q\) and of the characteristic”
>
> by
>
> > “a density law \[ \operatorname{dens}_F(x)=c_F(q)q^{-\ell_F(x)}, \] where a single rational function \(c_F(X)\in\mathbb Q(X)\) is fixed for the family and \(c_F(q)\) denotes its evaluation at \(X=q\); the family list, \(\ell_F\), \(P_F\), \(\nu_F\), and the rational expression \(c_F(X)\) are independent of the characteristic and of the chosen prime power \(q\).””

with the reason stated at the end of that append: “The \(n=2\) coefficients such as \(q-1\) and \((q-1)/(2q)\) now satisfy (A1) as evaluations of fixed rational functions, rather than as constants independent of \(q\).”

**Effective (A1) = the corrected clause.** (A0) is, post-`[r4]`, “redundant-but-retained”: `[r5]` MINOR 1 records that “(A0) is the same statement in its well-posedness phrasing, i.e. redundant-but-retained: it is not the load-bearing warrant at either bound”.

**DERIVATION:** Hypotheses, not derived. The σ-LABELING clause's necessity is proved by the degenerate instance at `.17`; its supply at each firing degree is the FIRING CHECK table `.18`.

**RESOLUTION TRACE:** Base §S1 clause (iii) hypotheses, lines 267–295, with `[r4]` F2's two brackets landed in place; (A1)'s coefficient clause replaced by the 2026-08-12 correction.

**TEETH:** The degenerate one-family instance (`.17`) is the tooth that forces the σ-LABELING clause; the FIRING CHECK is the coverage audit.

---

### EFF.W12.s1of2.13  [lemma]

**CANONICAL STATEMENT:** THEOREM W-12.D — the conclusion

> “THEN for every splitting type τ of degree n:
>
>     R_τ(q) := Σ_{F: σ_F = τ} Σ_{x ∈ P_F} c_F(q)·q^{−ℓ_F(x)}
>
> converges to ONE rational function in ℚ(q); it equals the N → ∞ limit of the decided-τ window mass AND the Haar splitting density μ_τ; it is the SAME expression at every prime power q, both characteristics, wild primes included; and Σ_τ R_τ(q) = 1.
> GRADE: PROVED (S3.4) as an unconditional reduction. At n = 2 its hypotheses are W-11's theorems — with the SPLIT-TAIL boundary family routed through (A2), see S3.4 — and it FIRES UNCONDITIONALLY, re-deriving split = inert = q/(2(q+1)), ram = 1/(q+1): the first unconditional instance of the GOAL's statement shape. At n = 3 the conditionality is exactly {(hMenu-3): the TRP refinement-family menu, W12-BOX-2} + {(hExhaust-3): the U₃^TRP upper bound, W12-BOX-3 — the other two legs of r(3,N), the σ-undecided DBL term AND the transported DBL SPLIT-TAIL boundary families (mass ⌊(N−1)/2⌋(q−1)²q^{2N−2}), are PROVED vanishing, S3.1 + S3.4 [r2]}. At n ≥ 4: those plus [W12-H] at composite stages (W12-BOX-1).”

**CONDITIONALITY:** PROVED **as a reduction** — the theorem itself is unconditional; its *firings* carry the per-degree conditionality listed above. Out of range, both n = 3 legs are DISCHARGED at composition grade by the two verbatim annexes (HEX3 → (hExhaust-3); HMENU3 → (hMenu-3)), leaving “conditional exactly on the arc grades of the W-11/W-12/HEX3/HMENU3 stack”.

**DERIVATION:** §S3.4's four steps: `.42` (rationality), `.43` (Steps 2–4), with the n = 2 instance at `.44`.

**RESOLUTION TRACE:** Base §S1 clause (iii) conclusion, lines 296–314, with `[r2]`'s boundary-tail leg landed in place.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:COROLLARY HM3.D` — grep-verified count **11**; the n = 3 firing that the ANNEX 2 discharge enables.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — grep-verified count **11**; the (hExhaust-3) discharge's law.

**TEETH:** The n = 2 instance is the non-vacuity check — it re-derives W-11's three densities through the general mechanism (`.44`).

---

### EFF.W12.s1of2.14  [scope-record]

**CANONICAL STATEMENT:** GRADE SUMMARY

> “**GRADE SUMMARY: (iii) PROVED as stated; (i) PROVED at the order-1 layer of every degree (+ the named instances machine-sealed), CONDITIONAL at orders ≥ 2 on the displayed [W12-H]; (ii) theorem at n = 2 (consumed), exact-DBL-term + bounds at n = 3 (W-12.C PROVED as stated), precise conjecture in general. Attempt 0/2.**”

**CONDITIONALITY:** “Attempt 0/2” superseded by ACCEPTED 2/2. Clause (i)'s “order-1 layer of every degree” is exactly the claim the 2026-08-12 obstruction suspended and the W12-HT discharge restored — the discharge's own closing sentence: “Thus ‘the order-1 layer at all degrees’ and ‘every W-11 row is an instance’ are again justified by the note's proved mechanisms.”

**DERIVATION:** Grade ledger.

**RESOLUTION TRACE:** Base line 316–320.

**TEETH:** §S10's “Consequence for the grade box” (shard 2) re-affirms these grades from the artifacts.

---

### EFF.W12.s1of2.15  [changes-record]

**CANONICAL STATEMENT:** `[r1]` F1 REPAIR RECORD (PE1 @ 2b47711, FINDING 1 CRITICAL, display-level)

> “The W-12.A display as sealed ran the product over {i : m_i ≥ 2} only, omitting the simple-branch factor Π_{i: m_i=1} q^{d_i(N−1)} — false for every shape with at least one simple branch — while the S2 proof establishes the CORRECTED law all along (S2.1's explicit simple-branch count q^{d_i(N−1)} each, assembled in S2.3): the display and the cell clause above are now ALIGNED TO THE PROOF, nothing re-proved. Verified against both PE1 counter-instances during this repair: (a) SEP-SPLIT at n = 2 (two simple branches) — the corrected display gives C₀·q^{2(N−1)} = ((q²−q)/2)·q^{2N−2} = W-11(ii)'s SEP law exactly (the sealed display gave the N-free C₀ alone); (b) DBL RAM(1) at (Zp, q = 2, N = 5) — the corrected display gives C₀·q^{N−1}·(q−1)q^{2N−3} = q(q−1)·q^{N−1}·(q−1)q^{2N−3} = 2·16·128 = 4096 == the committed artifact `w12_checks_results.json` row (Zp,2,5) dbl_keys[('RAM',(1,),())], re-read from the committed JSON this repair (the sealed display gave 256, short by exactly the simple-branch fiber q^{N−1} = 16 that LEMMA W12-L1(c) carries correctly). The corrected dens_T = C₀(q)·q^{−Σ_{i:m_i=1} d_i}·Π_{i:m_i≥2}[S_T·q^{−d_i(Σ_{j<m_i}⌈P_i(j)⌉ + L_i)}] is N-free, restoring the statement's own "dens_T ∈ ℚ(q) is shape-only" clause (internally contradicted by the sealed display).”

> “Ledger note: the 97122f2 adjudication entry transcribed the faulty display; it is ALREADY CORRECTED ledger-side (BRIDGE_ADJUDICATIONS_2026-07-30.md erratum block @ a0290f9) — this is the note-side pointer.”

**CONDITIONALITY:** Display-level: the proof already established the corrected law, so nothing is re-proved. The corrected `dens_T` is N-free, which is what makes the statement's own “shape-only” clause consistent.

**DERIVATION:** Two counter-instances computed against the committed artifact, quoted above.

**RESOLUTION TRACE:** Base lines 322–346; the repair is landed inside `.09`'s display.

XREF: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md:erratum` — grep-verified count **54** (the file carries an erratum-block convention; the specific block is pinned by commit `a0290f9`).

**TEETH:** The committed JSON row `(Zp,2,5) dbl_keys[('RAM',(1,),())] = 4096`, re-read at the repair.

---

### EFF.W12.s1of2.16  [changes-record]

**CANONICAL STATEMENT:** `[r3]` F1 REPAIR RECORD — the σ-pin, the rejected parse's computed price, and the consuming-surface sweep

> “As sealed(+r1+r2) the statement complex carried TWO non-equivalent definitions of CONJECTURE W-12.B's load-bearing quantity: S1's read-anchored sentence (whose "the read's σ" is undefined on a tail member — the S1 read description specifies no tail-certification rule — so that parse counts EVERY tail member undecided) vs W12-BOX-7's lift-certification "Decided" (the window digits force one σ across all disc ≠ 0 lifts). The two coincide at n = 2 ONLY because THEOREM W-11 proved its read certifies SPLIT-TAIL, and can disagree only on deep-tail TRP members (BOX-7's own fence); the [r3] pin — at the S1 definition and in the W-12.B bullet — selects BOX-7's notion, the one every PROVED and machine-checked surface already uses; nothing is re-proved.”

> “THE REJECTED PARSE'S PRICE (the PE3 verifier's computation, kept as the honest record of what the ambiguity would have cost): under the read-anchored/conservative parse undecided(3, q, N) contains the full conservative residue U₃^conv = q·u(q, N) (THEOREM HEX3.A, consumed by the BOX-3 annex), whose normalized mass q·u(q, N)·q^{−2N} DIVERGES linearly in N — the verifier's own transcription of HEX3.A (tied to all 23 committed U₃ values, 0 mismatches) evaluates at q = 2 to 0.50 (N = 3) → 0.86 (N = 10) → 2.53 (N = 50) → 8.78 (N = 200), asymptotic slope 1/24 — so NO c₃(q) exists and W-12.B is FALSE at n = 3 under that parse; even THEOREM W-12.C's displayed DBL constant (q−1)q^{2N−1} would inflate by the transported SPLIT-TAIL boundary mass ⌊(N−1)/2⌋(q−1)²q^{2N−2} (σ-DECIDED split-certified under the pin, undecided under the rejected parse).”

> “CONSUMING-SURFACE SWEEP (this repair; grep over every σ-DECIDED / σ-undecided / undecided / UNDECIDED surface of the note + the downstream citers): (a) consumers of the PINNED (BOX-7) notion, all consistent — THEOREM W-12.C's identity and the battery's dbl_undecided == (q−1)q^{2N−1} (W-11's certification-inclusive convention transported through W12-L1/W12-L0: S2.6, S2.7, S3.1, S7 W12-DRAIN3), the BOX-3 annex's bracket quantity U₃^σ, LEMMA W12-S2.1's branchwise decidedness and S2.3's decided shapes (Ore leaves), S3.4's (A2) routing (the transported SPLIT-TAIL boundary families enter r(N) as "σ-DECIDED split-certified" N-dependent mass — the certification named in the display), and HEX3 §S8.2's downstream corroboration remark (it routes the N-linear conservative mass to (A2)'s boundary families — the pinned parse); (b) parse-ROBUST surfaces (valid under BOTH notions) — LEMMA W12-S3.2's species and S3.3's general-n lower bound prove lift-DISAGREEMENT, and the decided-leaf statements ([W12-H](H-e) here and at GENIND's cite) have the read deciding AND certifying at once; (c) disclosed-convention MEASUREMENT surfaces (the conservative reader named explicitly, no σ-decidedness claim ridden) — the U₃^TRP EXPLORATORY battery row, the W12-ORACLE three-genre warrants (incl. the MINOR 1 sentence repaired in S7 below), and S3.4's conv-UNDECIDED tail parenthetical. NO surface consumes the rejected read-anchored parse (the Dfloor unit's σ-decided is its own self-contained every-lift definition, not a consumer of this display); the runner stays byte-frozen at seal f669cb0 — its docstring discloses the conservative convention as a MEASUREMENT convention, correct as sealed.”

**CONDITIONALITY:** The pin is definitional and note-wide. The class-(c) classification of the §S10 P-6 surface is later found INCOMPLETE by `[r4]` F3 (shard 2): “accurate about σ-decidedness, but the struck clause rode a W-12.B ORDER claim, which is the classification the sweep needed to catch”.

**DERIVATION:** The two parses are exhibited as non-equivalent, the rejected one is priced numerically from HEX3.A, and the sweep enumerates every consuming surface in three classes.

**RESOLUTION TRACE:** Base lines 348–399.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` — grep-verified count **11**.

**TEETH:** The verifier's HEX3.A transcription “tied to all 23 committed U₃ values, 0 mismatches”.

---

### EFF.W12.s1of2.17  [changes-record]

**CANONICAL STATEMENT:** `[r4]` F2 REPAIR RECORD — the missing σ-labeling hypothesis, with its necessity instance

> “As sealed(+r1+r2+r3), (A0)+(A1) attached σ_F to each core family as DATA and never said the family's members HAVE type σ_F, nor that they are σ-DECIDED at all: (A1) gave counts and disjointness only, and (A0) was conditioned on "every **window-decided** member" while Step 4's lower bound needs the conclusion for EVERY member of every visible core class (D_τ counts them all). Under the r3 pin (A0)'s "the read's type" reads as the member's own forced σ, making it the tautology "for every decided member, all disc ≠ 0 lifts have the σ they all have".”

> “THE DEGENERATE INSTANCE that the sealed hypotheses admit (PE4's, verified here): n = 2, any q, ONE family F = all window-N monic quadratics with d_F = 0, ℓ_F ≡ 0, ν_F ≡ 0, c_F = 1, and label σ_F := split. (A1) as sealed holds (a single class per window, exact count 1·q^{2N}, disjointness trivial, all data q- and characteristic-free); (A2) holds with r(N) ≡ 0; (A0) as sealed holds tautologously. The conclusion then gives R_split = 1, R_inert = R_ram = 0 — Σ_τ R_τ = 1 ✓ — while μ_split = q/(2(q+1)) ≠ 1, so the theorem's "it equals … the Haar splitting density μ_τ" clause is FALSE at that instance. The [r4] σ-LABELING clause excludes it exactly: that F contains σ-undecided members (W-11(iii)'s q^N residue) and members with forced σ = inert (SEP-INERT), so NO σ_F satisfies the clause. Nothing is re-proved: the intended reading was always S2.3's ("σ-DECIDED with σ read off the shape alone, and (A0)-strongly"), which is why the proof was morally fine and no corpus conclusion moves.”

**CONDITIONALITY:** This is a **strengthening of W-12.D's hypotheses**, not a weakening of its conclusion — the `[r4]` ARC records it as such: “the only statement-adjacent change is (A1) gaining a hypothesis clause, i.e. a STRENGTHENING of W-12.D's hypotheses, which every firing supplies”.

**DERIVATION:** A counter-model to the sealed hypothesis set, verified clause by clause, plus the exact reason the new clause excludes it.

**RESOLUTION TRACE:** Base lines 401–425; the clause itself is landed in `.12`'s (A1).

**TEETH:** The degenerate instance is the tooth; the FIRING CHECK (`.18`) is the coverage audit that no real firing is lost.

---

### EFF.W12.s1of2.18  [TABLE]

**CANONICAL STATEMENT:** [TABLE] FIRING CHECK — does every instance the corpus actually fires supply the new clause?

> “*FIRING CHECK (the charge: does every instance the corpus actually fires supply the new clause? — verified against the supplier notes at this repair, clause by clause).*”

| firing | families | the σ-labeling clause, at the supplier |
|---|---|---|
| **n = 2** (S3.4, fires unconditionally) | W-11's SEVEN-row menu, of which the six core families enter (A1); SPLIT-TAIL routes through (A2) | **SUPPLIED.** W-11(i) is a table whose third column IS σ per row (split/inert/ram) and whose header states the rows are "the decided leaves of the n = 2 read"; W-11(iii) makes {rows of (i)} ⊎ {σ-undecided residue} a PARTITION of all q^{2N} — so every member of every core class is decided, with σ = the row's label. Pinned (all disc ≠ 0 lifts) strength: S2.3's Ore/Hensel certification at the separable residual, the leg S3.4 already cites as "(A0) by W-11's decidedness (+ its sealed double-lift oracle leg)" |
| **n = 3** (HMENU3 COROLLARY HM3.D) | the 33-family cubic core menu (3 level-0 separable + 4 DBL-transported + THEOREM HM3.B's TRP families) | ~~**SUPPLIED VERBATIM.**~~ **SUPPLIED AT THE disc ≠ 0 FORM — which is the form (A1) needs [r5, PE5 F1].** … **What this row vouches for is the TRUE reading, and the only one consumed:** every menu member is conservative-DECIDED, and **every disc ≠ 0 lift** of every member has σ = the leaf table's entry … **HM3.C's *phrasing* ("EVERY lift", unrestricted) carries the same over-claim [r4]'s MINOR 2 struck from this note's own S2.3:** it is FALSE in equal characteristic 3 at the in-window b₁ = b₂ = 0 members of a TRP-RAM3(h) family with 3∤h … **The n = 3 firing SURVIVES unchanged** … |
| **n = 4** (GENH4 COROLLARY GENH4.D(ii)) | the degree-4 menu of [GENIND-H(4)] | **SUPPLIED.** THEOREM GENH4.C: "At every decided stage leaf of either genre (any history, any window), EVERY lift with disc ≠ 0 has the σ claimed by the leaf dictionary" + the explicit dictionary (E: RAM ↦ {(4,1)}, 2SIDED/SPLITEQ/SPLTAIL ↦ {(2,1),(2,1)}, INERT ↦ {(2,2)}; F: {(2,2)}/{(1,2),(1,2)}/{(1,4)}) — the dictionary IS the σ_F assignment, and the quantifier is over every lift of every leaf member |
| **n = 5** (GENHN, "P(5) FIRES OUTRIGHT") | every n = 5 genre (all μ = 2) | **SUPPLIED.** THEOREM GENHN.C: "At every decided leaf of every μ = 2 stage genre (all e₁ ≥ 1, f₁ ≥ 1 with e₁f₁ ≥ 2, all Q, both characteristics, any history, any window), EVERY lift with disc ≠ 0 has the σ claimed by the leaf dictionary" (stage-RAM ↦ {(2e₁, f₁)}, stage-2SIDED/SPLITEQ/SPLTAIL ↦ {(e₁,f₁),(e₁,f₁)}, stage-INERT ↦ {(e₁, 2f₁)}), with "(A0)-strong at every μ = 2 stage leaf" recorded at the end of its proof |
| **n ≥ 6** (GENHN's P(n)) | μ ≥ 3 stage leaves appear | **NOT supplied — and openly so:** the clause at μ ≥ 3 leaves IS the named open box [GENHN-HE(μ ≥ 3)] ("σ-decision at stage leaves of multiplicity μ ≥ 3, first live n = 6"). So the strengthening hides nothing: it names, at W-12.D's own hypothesis, the one thing that program already owes |

**CONDITIONALITY:** Coverage is complete through n = 5 and **openly absent at n ≥ 6**. The n = 3 row was re-worded at `[r5]` (the strike-through above is the note's own) — the row now vouches only for the disc ≠ 0 form, and the HMENU3-side phrasing correction is owed and drafted but **not landed** (`.02`'s protocol note; the draft is `lean/notes/openmath/HMENU3_annex_draft_r5.md`).

**DERIVATION:** Per-supplier verification against the supplier notes at the repair; each cell quotes its supplier's own statement.

**RESOLUTION TRACE:** Base lines 431–437 ([TABLE], transcribed as a table per template rule 5; the n = 3 cell is elided with `…` where its argument repeats `.27`'s counter-instance), with `[r5]` F1's rewording landed inside the n = 3 cell.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:THEOREM HM3.C` — grep-verified count **10**.

XREF: `lean/notes/openmath/GENH4_PROOF_2026-08-08.md:THEOREM GENH4.C` — grep-verified count **9**.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` — grep-verified count **11**.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:[GENHN-HE(μ ≥ 3)]` — grep-verified count **7**; the openly-unsupplied case.

**TEETH:** The n = 3 row's counter-instance (equal characteristic 3, `F = y³ + b₀`, `F′ ≡ 0`, disc = 0) is a signed non-applicability finding, not a machine row.

---

### EFF.W12.s1of2.19  [changes-record]

**CANONICAL STATEMENT:** STEP-4 RE-CHECK — does the proof now consume only the clause as stated?

> “*STEP-4 RE-CHECK (does the proof now consume only the clause as stated?).* Steps 1–3 use no σ-notion (Step 3 needs only that each family HAS a label, so the Σ_τ D_τ sum counts each family once — (A1) data). Step 4 lower bound: consumes exactly the clause (display above). Step 4 upper bound: a type-τ F with disc ≠ 0 truncating into a visible core class (F, x) forces σ_F = τ, because F is a disc ≠ 0 lift of its own truncation and the clause says every such lift has type σ_F — same clause, applied at F. Krasner-openness, the τ-partition of the étale locus and the disc = 0 null set are classical and displayed. No other σ-statement enters, and (A2) is untouched.”

**CONDITIONALITY:** Establishes that the new clause is exactly what Steps 4 consumes — no more, no less. `[r5]` MINOR 1 later routes both Step-4 bounds explicitly through it (`.43`).

**DERIVATION:** Step-by-step consumption audit.

**RESOLUTION TRACE:** Base lines 439–448.

**TEETH:** NONE (proof audit).

---

### EFF.W12.s1of2.20  [changes-record]

**CANONICAL STATEMENT:** `[r4]` F1/F3/m1/m2/R-1 INDEX

> “**[r4] F1/F3/m1/m2/R-1 INDEX (PE4 @ 26689da).** F1 (CRITICAL, the inseparable witness at S3.2's b₂ = 0 sub-species) is repaired AT THE SITE with its own [r4] record after LEMMA W12-S3.2; F3 at §S10 P-6; m1 at W12-BOX-7 (§S6); m2 at S2.3; R-1 (the pin's totality) at the S1 Conventions above.”

Followed by the design close:

> “The design honors the uniformity directive: the degree-by-degree crawl is quarantined into instances-as-evidence; the GENERAL claims are W-12.A (one proof for all degrees at order 1) and W-12.D (one proof for all n), so the remaining distance to "one R_τ ∈ ℚ(q) per splitting type at all primes" is exactly the displayed boxes — named, not hand-waved.”

**CONDITIONALITY:** An index; each item's content is at its named site (`.38`/`.40` for F1, shard 2 for F3, `.51` for m1, `.27` for m2, `.08` for R-1).

**DERIVATION:** Bookkeeping.

**RESOLUTION TRACE:** Base lines 450–460.

**TEETH:** NONE (index).

---

### EFF.W12.s1of2.21  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-S2.1 — the level-0 product structure (window-exact Hensel)

> “**LEMMA W12-S2.1.** The multiplication map (f_i)_i ↦ Π_i f_i is a bijection from Π_i {monic of degree m_i d_i over O/π^N with reduction P̄_i^{m_i}} onto {monic of degree n over O/π^N with reduction f̄}. Moreover σ(f) = ⊔_i σ(f_i) branchwise, and f is σ-decided iff every f_i is; the fibers transport counts multiplicatively.”

**CONDITIONALITY:** Requires the `P̄_i` distinct (pairwise coprime powers) and `O` complete. Both characteristics; no separability hypothesis.

**DERIVATION:** Quoted proof:

> “*Proof.* Both sides have q^{n(N−1)} elements (a monic polynomial with fixed reduction has N−1 free digits per coefficient; Σ m_i d_i = n). Injectivity is Hensel uniqueness at finite precision: suppose Π f_i ≡ Π f_i′ mod π^k with f_i ≡ f_i′ mod π^{k−1} for all i (k minimal where some pair diverges at level k; k ≥ 2 since the reductions agree). Write f_i′ = f_i + π^{k−1}A_i, deg A_i < m_i d_i. Expanding Π f_i′ mod π^k: Σ_i Ā_i · Π_{j≠i} P̄_j^{m_j} ≡ 0 in F_q[x]. For each i, every summand except the i-th is divisible by P̄_i^{m_i}; hence P̄_i^{m_i} divides Ā_i·Π_{j≠i}P̄_j^{m_j}, and coprimality gives P̄_i^{m_i} | Ā_i, forcing Ā_i = 0 by degree — contradicting minimality of k. Surjectivity: lift f to monic F over O; Hensel over the complete O factors F = Π F_i with F̄_i = P̄_i^{m_i}; reduce mod π^N. σ-transport: any lift F of f factors as Π F_i (Hensel), and by the injectivity just proved F_i mod π^N is determined: the lift-set of f is the branchwise product of the lift-sets of the f_i. The étale algebra of F is the product over branches, so σ(F) = ⊔ σ(F_i); decidedness and σ transfer branchwise. ∎”

**RESOLUTION TRACE:** Base §S2.1, lines 466–490; untouched by later rounds. Re-used by LEMMA W12-HT step 3 (shard 2) “now on the weighted side modules”.

**TEETH:** Battery family W12-BLOCK (the Hensel product identity and fiber bijection, pointwise on every DBL member).

---

### EFF.W12.s1of2.22  [lemma]

**CANONICAL STATEMENT:** §S2.1 — simple branches and the level-0 census

> “Simple branches (m_i = 1) are σ-decided at level 0 with the single étale piece (1, d_i) (Hensel: the lift factor is irreducible unramified of residue degree d_i), count q^{d_i(N−1)} each. The level-0 census C₀(q) = #{configurations f̄ of the given combinatorial type} is a classical product of irreducible-polynomial counts (instances used below: q for a linear center; q(q−1) for an ordered distinct linear pair; q(q−1)(q−2)/6 for three distinct linears; q·(q²−q)/2 for linear × irreducible quadratic; (q³−q)/3 for an irreducible cubic; these sum to q³ over the five cubic patterns — checked at q = 2: 2+2+2+2+0 = 8; at q = 3: 6+9+8+3+1 = 27). It remains to count one repeated branch.”

**CONDITIONALITY:** `C₀(q)` is the **undecorated** census — the 2026-08-12 orbit correction turns on exactly this: “S2.1's C₀(q) confirmed as the undecorated census (unordered within same-(d,m) classes)”, so a shape with two same-`(d, m)` branches carrying **distinct** decorations needs the factor `κ(T)` (`.09`(a)).

**DERIVATION:** Hensel for the simple branches; classical irreducible-polynomial counts for the census, with the closure check `Σ = q³` verified at `q = 2, 3`.

**RESOLUTION TRACE:** Base §S2.1, lines 492–501; corrected downstream by the κ(T) append.

**TEETH:** Battery family W12-LVL0 (the five cubic level-0 censuses + their sum `q³`, 0/138 in the verdict).

---

### EFF.W12.s1of2.23  [lemma]

**CANONICAL STATEMENT:** §S2.2 — the monic-division digit calculus and the membership conditions

> “Branch: f with f̄ = P̄^m, d = deg P̄, m ≥ 2; Φ the read's fixed monic lift of P̄ (by S2.1 we may take f = the branch factor, monic of degree md). Monic division gives the UNIQUE Φ-adic development
>
>     f = Φ^m + Σ_{j<m} a_j Φ^j,   a_j ∈ (O/π^N)[x]_{<d},
>
> and f ↦ (a_j)_{j<m} is a bijection onto the tuples with all ā_j = 0 (uniqueness of the development of P̄^m over F_q forces ā_j = 0 ⟺ f̄ = P̄^m). Each a_j is a free module of N digit-slots over the residue F_q-space F_q^d ≅ F_{q^d} (the class map b ↦ b mod P̄ is a linear bijection on representatives of degree < d); write digit_h(a_j) ∈ F_{q^d} for the slot at height h (the GMN order-1 residual-coefficient convention). v(a_j) := min coefficient valuation = the height of the lowest nonzero slot; the branch polygon is the lower hull of {(j, v(a_j))}_{j<m} ∪ {(m, 0)} (the order-1 φ-adic polygon).”

> “Membership in the shape T (exact polygon P with vertex heights ≤ N−1; per-side residual types λ_S), slot by slot:
> * j a VERTEX of P: v(a_j) = P(j) exactly and digit_{P(j)}(a_j) ≠ 0;
> * j an on-side lattice point (side S): v(a_j) ≥ P(j), with digit_{P(j)}(a_j) = the residual coefficient r_j ∈ F_{q^d} (possibly zero; priced jointly by λ_S);
> * every other j < m: P(j) ∉ ℤ (a lattice j on the hull boundary IS an on-side point), and the strict-above condition is v(a_j) ≥ ⌈P(j)⌉ — the automatic ceiling.”

> “Every pinned or priced slot sits at height ≤ P(0) ≤ N−1: in-window, no truncation error.”

**CONDITIONALITY:** Window-visibility (`vertex heights ≤ N−1`) is what makes the count truncation-free; the identification `F_q^d ≅ F_{q^d}` is the residue-class map at the fixed lift `Φ`.

**DERIVATION:** Uniqueness of monic division; the reduction constraint `ā_j = 0`; the polygon as the lower hull; the three slot regimes read off the polygon.

**RESOLUTION TRACE:** Base §S2.2, lines 505–531; re-used verbatim as step 1 of LEMMA W12-HT (shard 2): “This is S2.2's digit calculation and does not require separability.”

**TEETH:** Battery families W12-SHAPE and W12-QRT check the resulting laws in both directions.

---

### EFF.W12.s1of2.24  [lemma]

**CANONICAL STATEMENT:** §S2.2 — the branch count and the census normalization (sweep right-to-left)

> “Counting slots: slot j contributes N − ⌈P(j)⌉ free digits, minus one priced digit if j is a lattice point on the polygon (L of them), whence
>
>     #branch(N) = S_T(q^d) · q^{d·B(N)},   B(N) = mN − Σ_{j<m}⌈P(j)⌉ − L,
>
> with S_T(q^d) = #{residual-coefficient assignments: vertex digits ≠ 0, each side of type λ_S}.”

> “**The census normalization (sweep right-to-left).** Order the sides from the right; the rightmost side's right endpoint is (m, 0) with coefficient 1 (monic). Choosing its residual = a monic degree-g_S polynomial with nonzero constant term of type λ_S (S_{λ_S}(q^d) ways) fixes all its priced digits including its LEFT vertex value (a unit). Each next side to the left then has its right-vertex coefficient already fixed to a unit u; its residual is u·(monic of type λ_S) — again exactly S_{λ_S}(q^d) choices for the remaining digits, fixing its left vertex to a unit. The sweep spends exactly the L priced slots, whence
>
>     S_T(q^d) = Π_S S_{λ_S}(q^d)   — no extra unit factors.”

> “(Re-derivation cross-checks: W-11's 2SIDED row — two g = 1 sides — gives (q−1)², matching W-11's direct count (q−1)²·q^{2N−2−u−w₁} per node instance, NOT (q−1)³: interior-vertex units are already spent by the neighboring side's census. W-10's (2,1,1) row: one side, g = 1, L = 1, B = 2N−1−(1)−... P(0) = 1, P(1) = 1/2: B = 2N − 1 − 1 − 1 = 2N−3, count (q−1)q^{2N−3} per center — THEOREM W-10's law verbatim.)”

**CONDITIONALITY:** The “no extra unit factors” conclusion is exactly the correction the archived draft's spurious `(q^d−1)`-per-interior-vertex factor got wrong (`.02`); it is re-proved here and cross-checked at two independent rows.

**DERIVATION:** The right-to-left sweep quoted above, with the two cross-checks against W-11's 2SIDED row and W-10's (2,1,1) law.

**RESOLUTION TRACE:** Base §S2.2, lines 532–559; re-used as LEMMA W12-HT step 1 (“Its right-to-left sweep also applies unchanged”).

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:THEOREM W-10` — grep-verified count **2**.

**TEETH:** Tooth W12-T-CENSUS4 (`S_{(2)}` corrupted to `q(q−1)` must break QRT-G2(1,(2)) on every quartic row).

---

### EFF.W12.s1of2.25  [TABLE]

**CANONICAL STATEMENT:** [TABLE] §S2.2 — the universal residual censuses (Q = q^d)

> “The universal censuses used below (Q = q^d; classical, re-derived this session and machine-checked in both characteristics by the S7 battery):
>
>     g = 1:  S_{(1)} = Q−1.
>     g = 2:  S_{(1,1)} = (Q−1)(Q−2)/2,  S_{(2)} = Q(Q−1)/2,
>             S_{(1²)} = Q−1            [row sum Q(Q−1) ✓].
>     g = 3:  S_{(1,1,1)} = (Q−1)(Q−2)(Q−3)/6,  S_{(1,2)} = (Q−1)·Q(Q−1)/2,
>             S_{(3)} = (Q³−Q)/3,  S_{(1,1²)} = (Q−1)(Q−2),  S_{(1³)} = Q−1
>             [row sum Q²(Q−1) ✓; at Q = 2: 0+1+2+0+1 = 4 ✓;
>              at Q = 3: 0+6+8+2+2 = 18 ✓].”

> “THE LOCI DIFFER ACROSS CHARACTERISTICS (square classes vs Artin–Schreier traces; W-11 S2.1's table is the g = 2 instance); THE COUNTS DO NOT — J-D0's blindness at the residual level, which is the entire reason clause (i) can be stated shape-only.”

**CONDITIONALITY:** Classical counting polynomials; the characteristic-independence of the COUNTS (not the loci) is the J-D0 frame, and it is what discharges W-11's owed `g ≥ 2` census input at the order-1 layer (`.06`).

**DERIVATION:** Classical, re-derived in-session, with row-sum checks displayed and numeric checks at `Q = 2, 3`.

**RESOLUTION TRACE:** Base §S2.2, lines 562–575; the exact zeros (`S_{(1,1)}(2) = 0`, `S_{(1,1,1)}(q ≤ 3) = 0`) become real battery predictions at `.30`.

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — grep-verified count **4**.

**TEETH:** Battery checks the censuses in both characteristics; the exact zeros are checked exactly (P-2, P-3).

---

### EFF.W12.s1of2.26  [fence]

**CANONICAL STATEMENT:** §S2.2 — cell factorization and the lift-convention note

> “Cell factorization: for FIXED configuration and residual-letter assignment the remaining digits are free — every cell has exactly q^{d·B(N)} members (W-10's cell-by-cell template at every degree). Convention note: the count is stated for the read's OWN lift choice Φ; the formula is independent of which fixed monic lift the convention picks (the development bijection works verbatim for each), while the deeper question — whether different lift conventions select the same member SET at deep shapes — is the W-2/LIFTCORNER seam, not consumed here (W12-BOX-5).”

**CONDITIONALITY:** Independence is asserted for the FORMULA, explicitly not for the member SET at deep shapes.

**DERIVATION:** The development bijection of `.23` holds for each fixed monic lift.

**RESOLUTION TRACE:** Base §S2.2, lines 577–585.

**NON-IMPORT (explicit):** the lift-convention seam (W-2/LIFTCORNER) “not consumed here”.

**TEETH:** NONE (fence).

---

### EFF.W12.s1of2.27  [lemma]

**CANONICAL STATEMENT:** §S2.3 — Decidedness and σ (Ore leaves); clause (i) assembled

> “If every residual is separable, Ore's theorem (the order-1/regular case of the Montes read; Ore 1928, via GMN "Newton polygons of higher order", order-1 layer — classical, cited not re-proved) factors any O-lift F of the branch into one monic irreducible factor per (side S, irreducible residual factor ψ | R_S), with e = e_S (the denominator of S's slope in lowest terms) and residue degree d·deg ψ. All data the read consumes sit at heights ≤ N−1, so every lift of the window class shares them: the shape is σ-DECIDED with σ read off the shape alone, and (A0)-strongly (every disc ≠ 0 lift has this σ ~~— in fact every lift~~ **[r4, PE4 m2: the struck parenthetical is FALSE in equal characteristic at wild decided shapes, and nothing consumes it — (A0), (A1)'s [r4] σ-labeling clause and Step 4 all quantify over disc ≠ 0 lifts only. Counter-instance from the note's own family table: a TRP-RAM3(h) member with 3∤h whose b₁, b₂ vanish in-window admits the lift F = y³ + b₀ with v(b₀) = h, and in equal characteristic 3 that lift has F′ ≡ 0, hence disc = 0 and no σ at all; same at any wild side with e divisible by p and the intermediate slots empty (LINRAM2 / RAM2LIN / QRT-G2 in char 2). Such lifts are exactly what the disc ≠ 0 quantifier is for — same root cause as the [r4] F1 repair in S3.2]**). Combining S2.1 (product over branches) × S2.2 (each branch) × the level-0 census C₀(q): THEOREM W-12.A. ∎”

**CONDITIONALITY:** The quantifier is **disc ≠ 0 lifts only** — the unrestricted “every lift” is struck as FALSE in equal characteristic at wild decided shapes, with an explicit counter-instance. This is the σ-certification strength that W-12.D's (A1) clause needs and that the FIRING CHECK audits at every degree.

**DERIVATION:** Ore's theorem at separable residuals (cited, not re-proved) + the in-window pinning sentence (“All data the read consumes sit at heights ≤ N−1”) + the S2.1 × S2.2 × C₀ assembly.

**RESOLUTION TRACE:** Base §S2.3, lines 589–609, with `[r4]` m2's strike landed in place. The struck phrase's blast radius is swept at `[r5]`'s m2 table (shard 2), which finds HMENU3's HM3.C inheriting the same over-claim and HEX3 L80–81 carrying the same phrasing with its conclusion unaffected.

**READING NOTE (external, not an edit).** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` row **Q1 W12-2** targets exactly this sentence — *“Ore's theorem … factors any `O`-lift `F`”* — and retargets it to **[GN15] Theorem 2.3** (NS-1/NS-2), with `[GN15]` eq. (2.1) supplying the `(e, f)` readout and `[AGNPRW]` Thm 4.4 + Prop 4.5 as the independent second leg; verdict **COVERS-ALL-O** (arbitrary discrete valued field, any monic `g ∈ O_v[x]`, no separability needed). Recorded, not applied.

**TEETH:** Battery family W12-ORACLE (PARI σ-multiset per decided member, `disc = 0 ⟹ never decided`) and tooth W12-T-SIGMA.

---

### EFF.W12.s1of2.28  [TABLE]

**CANONICAL STATEMENT:** [TABLE] §S2.4 — the SEVEN new decided families at the triple center

> “At a TRP center (f̄ = (x−c̄)³; q centers; recenter g = f(x+c) with coefficients (b₂, b₁, b₀), all v ≥ 1; branch polygon = hull of {(0,u₀),(1,u₁),(2,u₂),(3,0)}, u_j := v(b_j)), the digit calculus of S2.2 evaluates to (all counts PER CENTER; whole space = × q centers; params ≥ 1; visibility u₀ ≤ N−1; ⌈2h/3⌉+⌈h/3⌉ = h+1 for 3∤h):”

| family | polygon / residual datum | count PER CENTER | σ | wild stratum |
|---|---|---|---|---|
| TRP-RAM3(h), 3∤h | one side (0,h)–(3,0), e = 3, g = 1 | (q−1)·q^{3N−2h−2} | {(3,1)} | p = 3 / char 3 |
| TRP-3LIN(m₁>m₂>m₃) | three sides, slopes m₁,m₂,m₃ | (q−1)³·q^{3N−3−m₁−2m₂−3m₃} | {(1,1)³} | — |
| TRP-LINRAM2(u₀,u₁), u₁ odd, 2u₀>3u₁ | vertex (1,u₁); right side e = 2 | (q−1)²·q^{3N−2−u₀−u₁−(u₁+1)/2} | {(1,1),(2,1)} | p = 2 / char 2 |
| TRP-VERT1(u₀,k;λ), u₀>3k, λ∈{(1,1),(2)} | vertex (1,2k); right side e = 1, g = 2 | (q−1)·S_λ(q)·q^{3N−3−u₀−3k} | {(1,1)}⊎σ(λ) | — |
| TRP-FULL(k;λ), λ∈{(1,1,1),(1,2),(3)} | one side (0,3k)–(3,0), e = 1, g = 3 | S_λ(q)·q^{3N−6k−3} | σ(λ) | — |
| TRP-RAM2LIN(u₀,t), u₀−t odd, u₀>3t | vertex (2,t); left side e = 2 | (q−1)²·q^{3N−2−u₀−t−(u₀+t+1)/2} | {(2,1),(1,1)} | p = 2 / char 2 |
| TRP-VERT2(u₀,t;λ), u₀−t even, u₀>3t, λ∈{(1,1),(2)} | vertex (2,t); left side e = 1, g = 2 | (q−1)·S_λ(q)·q^{3N−3−u₀−t−(u₀+t)/2} | σ(λ)⊎{(1,1)} | — |

**CONDITIONALITY:** Depth-0 (no refinement history), per center, window-visible (`u₀ ≤ N−1`). Three rows are wild strata (`p = 3` for RAM3; `p = 2` for LINRAM2/RAM2LIN) and are counted by the same laws as the tame rows.

**DERIVATION:** Each row is a direct S2.2 evaluation; the derivations are `.29`.

**RESOLUTION TRACE:** Base §S2.4, lines 611–627; untouched by later rounds (the κ(T) correction does not touch single-repeated-branch shapes: “κ(T) = 1 re-checked on every sealed and every consumed instance”).

**TEETH:** Battery family W12-SHAPE (both directions: an observed-but-unpredicted decided key is a violation, and so is a predicted-but-absent one) and tooth W12-T-SHAPE.

---

### EFF.W12.s1of2.29  [lemma]

**CANONICAL STATEMENT:** §S2.4 — the seven derivations and the σ(λ) dictionary

> “Derivations (each a direct S2.2 evaluation; heights listed are (⌈P(0)⌉, ⌈P(1)⌉, ⌈P(2)⌉)):
> * RAM3(h): heights (h, ⌈2h/3⌉, ⌈h/3⌉) summing to 2h+1; L = 1 (only j = 0 lattice); S_T = S_{(1)} = q−1. B = 3N − (2h+1) − 1.
> * 3LIN: heights (m₁+m₂+m₃, m₂+m₃, m₃), sum m₁+2m₂+3m₃; L = 3; S_T = (q−1)³.
> * LINRAM2(u₀,u₁): heights (u₀, u₁, (u₁+1)/2); L = 2 (j = 0, 1); S_T = (q−1)² (two g = 1 sides). Vertex-at-1 condition u₀−u₁ > u₁/2 ⟺ 2u₀ > 3u₁.
> * VERT1(u₀,k;λ): heights (u₀, 2k, k); L = 3; S_T = S_{(1)}·S_λ. Vertex condition u₀−2k > k ⟺ u₀ > 3k.
> * FULL(k;λ): heights (3k, 2k, k); L = 3; S_T = S_λ.
> * RAM2LIN(u₀,t): heights (u₀, (u₀+t+1)/2, t); L = 2 (j = 0, 2); S_T = (q−1)². Vertex-at-2 condition (u₀−t)/2 > t ⟺ u₀ > 3t.
> * VERT2(u₀,t;λ): heights (u₀, (u₀+t)/2, t); L = 3; S_T = S_λ·S_{(1)}.”

> “σ(λ) reads by Ore (S2.3): (1,1) ↦ {(1,1),(1,1)}; (2) ↦ {(1,2)}; (1,1,1) ↦ {(1,1)³}; (1,2) ↦ {(1,1),(1,2)}; (3) ↦ {(1,3)}; an e = 2 side of residual degree 1 ↦ {(2,1)}; the e = 3 side ↦ {(3,1)}.”

**CONDITIONALITY:** Each row's vertex condition is part of its family definition; the σ dictionary is Ore's readout at `.27`'s strength (disc ≠ 0 lifts).

**DERIVATION:** As displayed — heights, `L`, `S_T`, then `B(N) = mN − Σ⌈P(j)⌉ − L` from `.24`.

**RESOLUTION TRACE:** Base §S2.4, lines 629–647.

**TEETH:** An independent pre-runner brute force confirmed all seven laws per center at nine `(p, N)` pairs (`.30`'s machine line).

---

### EFF.W12.s1of2.30  [lemma]

**CANONICAL STATEMENT:** §S2.4 — Completeness at depth 0

> “**Completeness at depth 0:** every exact visible 4-point polygon falls in exactly one row or a REFINE/tail case: one side — slope h/3 with 3∤h (RAM3) xor integer slope k (FULL; decided iff λ separable, else refine); vertex at 1 only — right side of length 2: e = 2 (LINRAM2) xor e = 1 (VERT1 / refine at λ = (1²)); vertex at 2 only — left side of length 2: e = 2 (RAM2LIN) xor e = 1 (VERT2 / refine); vertices at 1 and 2 — 3LIN, always decided. So the seven families are the COMPLETE depth-0 decided TRP menu, and the battery enforces key-completeness (any unpredicted depth-0 decided key is a violation, both directions). Refinement leaves (repeated residual roots: λ ∈ {(1²)} on a g = 2 side, {(1,1²)}, {(1³)} on the g = 3 side) recurse deeper; their per-history laws are NOT derived here (W12-BOX-2: the n = 3 analogue of W-11's instance bracket, with TWO node species — see S3.1). The exact-zero rows are real predictions: S_{(1,1)}(2) = 0, S_{(1,1,1)}(q) = 0 for q ≤ 3 — the battery checks the zeros exactly. ∎”

> “[machine: W12-SHAPE — all seven laws, both directions, on every cubic row; re-derivation record: an independent throwaway brute-force (pre-runner, this session) confirmed all seven laws per center at (p,N) ∈ {(2,3),(2,4),(2,5),(2,7),(3,2),(3,3),(3,4),(5,2),(7,2)}, including the 22-key (2,7) row realizing TRP-3LIN(3,2,1).]”

**CONDITIONALITY:** Completeness is at **depth 0** only; the refinement leaves are explicitly not derived here (W12-BOX-2), and that gap is what ANNEX 2 (HMENU3) later discharges at composition grade.

**DERIVATION:** Case exhaustion over the possible vertex sets of a visible 4-point polygon, each case resolved by `e = 1` vs `e ≥ 2` and by residual separability.

**RESOLUTION TRACE:** Base §S2.4, lines 649–669.

**TEETH:** W12-SHAPE both directions + the exact-zero predictions; the independent pre-runner brute force at nine `(p, N)` pairs.

---

### EFF.W12.s1of2.31  [lemma]

**CANONICAL STATEMENT:** §S2.5 — the quartic g = 2 instance (first g ≥ 2 residual census row)

> “At a quadruple center (f̄ = (x−c̄)⁴; recentered coefficients (b₃,b₂,b₁,b₀), all v ≥ 1), the shape with ONE side (0,2h)–(4,0), h odd (slope h/2, e = 2, length 4, g = 2; lattice points j = 0, 2, 4; residual R(y) = y² + r₂y + r₀ over F_q, r₂ = digit_h(b₂), r₀ = digit_{2h}(b₀) ≠ 0): S2.2 gives, per center,
>
>     QRT-G2(h; λ):  S_λ(q)·q^{4N−5h−3},   λ ∈ {(1,1), (2)}:
>     σ = {(2,1),(2,1)} for λ = (1,1);  {(2,2)} for λ = (2) — wild at p = 2;
>     QRT-G2(h; (1²)) [NOT decided at order 1 — the composite-stage
>     frontier]: (q−1)·q^{4N−5h−3} members open a DEGREE-2 key (order 2).
>
> (Heights (2h, ⌈3h/2⌉ = (3h+1)/2, h, (h+1)/2), sum 5h+1; L = 2 (j = 0, 2); B = 4N − (5h+1) − 2.) The λ = (1²) row is displayed deliberately: it is the FIRST machine-measured composite-stage stratum with an exact volume law — the count is order-1 data (S2.2 needs no decidedness to price the locus), while its σ-resolution is exactly what [W12-H] owes (W12-BOX-1). The battery checks both decided laws (including the q = 2 exact zero for λ = (1,1)) and the (1²) volume. ∎”

**CONDITIONALITY:** The `(1²)` row is a **volume law without a σ-resolution** — the count is proved, the splitting type is owed to `[W12-H]`. This row is the note's concrete order-≥ 2 frontier exhibit.

**DERIVATION:** Direct S2.2 evaluation with the displayed heights, `L = 2`, and `B(N) = 4N − (5h+1) − 2`.

**RESOLUTION TRACE:** Base §S2.5, lines 673–690.

**READING NOTE:** the 2026-08-12 κ(T) append records that these sealed quartic rows are the QUADRUPLE center (one branch), so “no sealed row exercises two same-(d,m) branches with distinct decorations — the battery's GREEN is consistent with the defect”. The orbit correction therefore moves no committed number here.

**TEETH:** Battery family W12-QRT (both decided laws, the `q = 2` exact zero, and the `(1²)` volume) and tooth W12-T-CENSUS4.

---

### EFF.W12.s1of2.32  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-L0 (the history-resolved n = 2 law; W-11 refined)

> “**LEMMA W12-L0.** Fix n = 2, a center, a window N, and a refinement history H = (k₁ < ⋯ < k_t) (t ≥ 0; k₁ ≥ 1; refinement at depth k requires 2k ≤ N−1, so k_t ≤ M := ⌊(N−1)/2⌋; write s := k_t, s = 0 for t = 0). The window-N count PER CENTER of monic quadratics with history exactly H and the given leaf is (q−1)^t × the leaf count from ONE node instance C(2s+1, s+1) (W-11 S2 coordinates):
>
>     RAM(u)@H:        (q−1)·q^{N−1−u}·q^{N−(u+1)/2},  u odd, 2s+1 ≤ u ≤ N−1;
>     2SIDED(w,u−w)@H: (q−1)²·q^{2N−2−u−w},  s+1 ≤ w, 2w < u ≤ N−1;
>     SPLITEQ(k)@H:    ((q−1)(q−2)/2)·q^{2N−3k−2},  s+1 ≤ k ≤ M;
>     INERTDEEP(k)@H:  (q(q−1)/2)·q^{2N−3k−2},      s+1 ≤ k ≤ M;
>     SPLIT-TAIL(w)@H: (q−1)·q^{N−1−w},   s+1 ≤ w ≤ M;
>     UNDECIDED@H:     q^{N−1−M}.”

**CONDITIONALITY:** `n = 2` only — this is the lemma the 2026-08-12 obstruction cites as insufficient for the general order-1 claim (“W12-L0 supplies this only for \(n=2\)”), and whose `(q−1)^t` prefactor exhibits the missing history factor. Its own content is unaffected: LEMMA W12-HT “recovers” it (“This is W12-L0's \((q-1)^t\) factor and its six leaf laws”).

**DERIVATION:** Quoted proof:

> “*Proof.* Induction on t. Base t = 0 (root node C(1,1)): each formula is the digit count of its defining locus (W-11 S2.1/S2.4 conditions, both characteristics): RAM(u): v(A₀) = u exact + nonzero digit [(q−1)q^{N−1−u}] and v(A₁) ≥ (u+1)/2 [q^{N−(u+1)/2}]; 2SIDED: both exact-valuation pins [(q−1)²q^{(N−1−u)+(N−1−w)}]; SPLITEQ/INERTDEEP: v(A₀) = 2k with digit c₀ ≠ 0, v(A₁) ≥ k with digit_k = c₁, (c₁,c₀) priced by the W-11 residual census [(q−1)(q−2)/2 resp. q(q−1)/2 pairs, × q^{N−2k−1}·q^{N−k−1}]; SPLIT-TAIL(w): A₀ = 0 (v ≥ N over O/π^N) and v(A₁) = w exact + nonzero digit [(q−1)q^{N−1−w}]; UNDECIDED: A₀ = 0 and v(A₁) ≥ M+1 [q^{N−1−M}] — the constraint ranges embed the node constraints (u ≥ 2s+1, w ≥ s+1) so the per-instance formulas are s-independent on their stated ranges. Step t → t+1: W-11 S2.3 (consumed at pin, post-r2 text): for each of the q−1 letters z̄, the refine locus at depth k_{t+1} maps measure-isomorphically ONTO C(2k_{t+1}+1, k_{t+1}+1), in both characteristics; histories concatenate, counts multiply by (q−1). ∎”

**RESOLUTION TRACE:** Base §S2.6, lines 694–723.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:S2.3` — grep-verified count **8**; the refinement measure-isomorphism consumed as the induction step (LEMMA W12-HT generalizes exactly this: “This is W-11 S2.3's measure-isomorphism mechanism without the quadratic restriction”).

**TEETH:** Battery family W12-L0HIST (every `(kind, params, hist)` key against these closed forms, on 11 quadratic rows; and `Σ_H` against the sealed W-11 aggregate predictor).

---

### EFF.W12.s1of2.33  [lemma]

**CANONICAL STATEMENT:** §S2.6 — aggregation back to W-11, and the drainage consistency display

> “Summing W12-L0 over H returns W-11's aggregated rows (the instance bracket: Σ over histories ending at any s < k of (q−1)^t = 1 + Σ_{s=1}^{k−1}(q−1)q^{s−1} = q^{k−1} per leaf read at k — W-11 S2.5's bracket re-derived). Consistency display for drainage: undecided per center = Σ_H (q−1)^t·q^{N−1−M} = q^{N−1−M}·(1 + Σ_{s=1}^{M}(q−1)q^{s−1}) = q^{N−1−M}·q^M = q^{N−1} — W-11's exact law, history-resolved. Each history-resolved key is its own decided shape (refinement depth t as shape datum); at n = 2 the refinement tower never leaves key degree 1, which is why W12-L0 needs no [W12-H] input.”

**CONDITIONALITY:** The closing clause is the reason W12-L0 is `[W12-H]`-free: at n = 2 no composite stage ever opens.

**DERIVATION:** The two displayed geometric sums.

**RESOLUTION TRACE:** Base §S2.6, lines 725–735.

**TEETH:** W12-L0HIST's second leg (`Σ_H` vs the sealed W-11 aggregate predictor, key by key, on every cubic row's `(q, N)`).

---

### EFF.W12.s1of2.34  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-L1 (block transfer: the DBL stratum of cubics IS the n = 2 system)

> “**LEMMA W12-L1.** (a) [window Hensel split] (g, l) ↦ g·l is a bijection {monic quadratic g, ḡ = (x−c̄)²} × {monic linear l, l̄ = x−d̄} → {monic cubic f, f̄ = (x−c̄)²(x−d̄)} over O/π^N.
> (b) [read equivalence] The recursive read of f at the center c̄ equals the W-11 read of its block g: the same trichotomy case at every node, the same (u, w) parameters, unit-scaled letters, the same refinement history, the same decided/tail/undecided exit.
> (c) [σ and drainage transfer] σ(f) = σ_block(g) ⊎ {(1,1)}; f is σ-decided iff g is. Hence for every W-11 history-resolved key: #{DBL members over one pattern realizing it} = q^{N−1} × (the W12-L0 per-center count), and the σ-undecided DBL count over all patterns is EXACTLY q(q−1)·q^{N−1}·q^{N−1} = (q−1)·q^{2N−1}.”

**CONDITIONALITY:** Fixed level-0 pattern `f̄ = (x−c̄)²(x−d̄)` with `c̄ ≠ d̄` (the lemma's own fence, cited later at the ORACLE genre analysis: “W12-L1's own fence is c̄ ≠ d̄, S2.7”). Clause (c) consumes W-11 clause (iii) at pin.

**DERIVATION:** Quoted proof:

> “*Proof.* (a) is the two-branch case of LEMMA W12-S2.1. (b) Write g(x+c) = x² + B₁x + B₀ (v(B₁), v(B₀) ≥ 1) and l(x+c) = x − ρ̃ with ρ̃ = r − c (l = x − r, r ≡ d̄), res(ρ̃) = d̄ − c̄ =: ρ̄ ≠ 0 a unit. Then f(x+c) = x³ + a₂′x² + a₁′x + a₀′ with
>
>     a₂′ = B₁ − ρ̃,   a₁′ = B₀ − ρ̃B₁,   a₀′ = −ρ̃B₀,
>
> so v(a₂′) = 0, v(a₀′) = v(B₀) =: u with digit_u(a₀′) = −ρ̄·digit_u(B₀), and the PRINCIPAL part of f's polygon at c̄ is the hull of {(0,u),(1,v(a₁′)),(2,0)} (the point (3,0) contributes the slope-0 simple side = the l-branch). Case check against the block hull {(0,u),(1,w),(2,0)}, w := v(B₁):
> * 2w < u: v(ρ̃B₁) = w < u = v(B₀) ⟹ v(a₁′) = w exactly, digit −ρ̄·digit_w(B₁) — the same two one-point sides, same (w, u−w), letters unit-scaled by −ρ̄.
> * u odd, w ≥ (u+1)/2: v(a₁′) ≥ min(u, w) ≥ (u+1)/2 > u/2 — the same single RAM(u) side, letter −ρ̄·digit_u(B₀) ≠ 0.
> * u = 2k, w ≥ k: v(a₁′) ≥ k; since v(B₀) = 2k > k, digit_k(a₁′) = −ρ̄·digit_k(B₁) = −ρ̄·c₁; the abscissa-2 digit is res(a₂′) = −ρ̄, and digit_{2k}(a₀′) = −ρ̄·c₀. The side residual of f is therefore R_f(y) = −ρ̄·(y² + c₁y + c₀) = −ρ̄·R_g(y) — a UNIT multiple: same separability type, same roots, same refinement letter z̄ (J-D0's blindness literal at this seam: the letters move by a unit, the shape and the counts cannot).
> Refinement recenters both reads by the SAME s = ẑπ^k (ẑ a lift of the double residual root z̄): g(x+c+s) is W-11's refined block, and l(x+c+s) = x − (ρ̃ − s) with res(ρ̃ − s) = ρ̄ ≠ 0 still a unit (v(s) ≥ 1): the setup is preserved, the induction continues, and refinement depths strictly increase, so the two reads terminate together with equal histories. Tail exits: over O/π^N, v(B₀) ≥ N means B₀ = 0, whence a₁′ = −ρ̃B₁ EXACTLY: v(a₁′) = w with the SAME digit data, and the SPLIT-TAIL/UNDECIDED split (w ≤ M or not) transfers verbatim. (c) By (a) every O-lift F of f factors as G·L with G ≡ g, L ≡ l mod π^N (Hensel-factor F, reduce, apply (a)'s injectivity); L contributes the piece (1,1), and G ranges over exactly the lifts of g as F ranges over the lifts of f. So lift-σ-set(f) = lift-σ-set(g) ⊎ {(1,1)}: σ, decidedness, and (A0) well-posedness transfer. Counts: the fiber over g is the q^{N−1} monic linears with reduction x−d̄. Drainage: W-11 clause (iii) (consumed at pin 7020ceb/cb05127, post-r2 HEAD 31506b3) gives σ-undecided quadratic blocks = q^{N−1} per center; × q^{N−1} linears × q(q−1) patterns = (q−1)·q^{2N−1}. ∎”

**RESOLUTION TRACE:** Base §S2.7, lines 739–795. LEMMA W12-HT (shard 2) records it as “compatible”: “Its quadratic block is one child coordinate of (HT-fiber); the coprime linear branch supplies \(q^{N-1}\).”

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — grep-verified count **3**; clause (iii) consumed at pin for the drainage transfer.

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — grep-verified count **4**; the unit-scaled-letter blindness at this seam.

**TEETH:** Battery families W12-BLOCK (product identity + fiber bijection) and W12-L1X (the FRESH direct cubic read vs the SEALED W-11 classifier on the Hensel block, pointwise on every DBL member — 0/1,594,090 in the verdict).

---

### EFF.W12.s1of2.35  [fence]

**CANONICAL STATEMENT:** §S2.7 — what W12-L1 is an instance of

> “W12-L1 is the smallest instance of the S0 design decision: the general mechanism is TRANSPORT — blocks reduce to lower-degree systems with unit-scaled letters that counts never see — not per-degree re-derivation. It moves the ENTIRE proved W-11 menu (count laws, per-history structure via W12-L0, and the exact drainage term) into degree 3 at one stroke.”

**CONDITIONALITY:** A design statement about mechanism, not a count claim.

**DERIVATION:** Reading of `.34`.

**RESOLUTION TRACE:** Base §S2.7, lines 797–806.

**TEETH:** W12-BLOCK / W12-L1X as above.

---

### EFF.W12.s1of2.36  [lemma]

**CANONICAL STATEMENT:** §S3.1 — the n = 3 partition and the exact DBL term

> “undecided(3, q, N) partitions by level-0 pattern (S2.1: decidedness is branchwise): the three separable patterns contribute 0 (all branches simple ⟹ decided at level 0); the DBL patterns contribute EXACTLY (q−1)·q^{2N−1} (LEMMA W12-L1(c) — a THEOREM); the TRP pattern contributes U₃^TRP(q, N), for which no law is derived here. THEOREM W-12.C's identity is this partition. ∎(the exact term)”

**CONDITIONALITY:** The identity is exact; only its `U₃^TRP` summand is underived.

**DERIVATION:** Branchwise decidedness (`.21`) partitions by level-0 pattern; the DBL term is `.34`(c); the separable patterns contribute nothing since all their branches are simple.

**RESOLUTION TRACE:** Base §S3.1, lines 812–817.

**TEETH:** W12-DRAIN3 (`partition Σ == q^{3N}`; `DBL-undecided == (q−1)q^{2N−1}` on all 23 rows) and tooth W12-T-DRAIN.

---

### EFF.W12.s1of2.37  [open-obligation]

**CANONICAL STATEMENT:** §S3.1 — the obstruction to an exact `U₃^TRP` law (two node species)

> “The obstruction to an exact U₃^TRP law, displayed (W12-BOX-3): the TRP refinement tree has TWO node species — (α) the triple-cluster node (λ = (1³) at a FULL side: recentering keeps all three roots in one cluster, a genuine n = 3 node, analogous to W-11's C(2s+1, s+1) but with a 3-parameter state), and (β) the DBL-re-entry node (λ = (1,1²) at FULL, or (1²) at a VERT1/VERT2 g = 2 side: one root Hensel-splits off, and the remaining double cluster re-enters the n = 2 system of W-11/W12-L0 at a REDUCED window and shifted valuation frame). A closed form needs the (α)-species instance bracket (the n = 3 analogue of W-11's Σ(q−1)^t q^{s−1} identity) plus the (β)-species window-transfer law; neither is derived here. Additionally the TRP TAIL needs its own σ-certification lemma (the n = 3 SPLIT-TAIL analogue: a deep vertex can certify a split-off (1,1) piece even with b₀ hidden), also not derived. These three named lemmas are exactly (hMenu-3)/(hExhaust-3)'s distance.”

**CONDITIONALITY:** Three named missing lemmas. Out of range, ANNEX 2 (HMENU3) discharges the two species' transfer laws at composition grade (“both node species' transfer laws leaf-resolved: α self-similar with key shear, β into W12-L0 via the raw-key dictionary”), and the BOX-3 annex (HEX3) discharges the vanishing upper bound; the tail-σ-certification lemma stays open as HEX3-BOX-1.

**DERIVATION:** Species analysis of the TRP refinement tree.

**RESOLUTION TRACE:** Base §S3.1, lines 819–833.

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` — grep-verified count **11**; the still-open tail-σ-certification lemma.

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:THEOREM HM3.C` — grep-verified count **10**; the supplier that resolves both species.

**TEETH:** None — this is the note's honest statement that no closed form is preregistered for `U₃^TRP`.

---

### EFF.W12.s1of2.38  [lemma]

**CANONICAL STATEMENT:** LEMMA W12-S3.2 — the TRP lower bound via a constructed ambiguous species

> “**LEMMA W12-S3.2.** Every TRP member with b₁ = b₀ = 0 over O/π^N (after recentering; b₂ ∈ πO/π^N free) is σ-undecided: U₃^TRP(q, N) ≥ q·q^{N−1} = q^N.”

**CONDITIONALITY:** The statement and count are byte-unchanged across the `[r4]` repair — only the PROOF's witness construction changed (`.40`). The construction is now uniform in the characteristic.

**DERIVATION:** Quoted proof, at its `[r4]`-repaired form:

> “*Proof (constructed lifts, both characteristics, every q; **[r4, PE4 F1] ONE branch now — the b₂ = 0 sub-species is handled by the generic construction at t := N, and the sealed B = 0 branches, which are INSEPARABLE in equal characteristic 2 resp. 3, are DELETED; record and the every-characteristic separability display after the proof**).* Let t = v(b₂) ∈ [1, N−1] and B a lift of b₂ to O with v(B) = t; **[r4] when b₂ = 0 take B = π^N and t := N** — any lift of valuation ≥ N serves (B ≡ b₂ = 0 mod π^N), and NEVER B = 0.
> Lift 1 (split-directed): F_A = (x−c)³ + B(x−c)² + π^{2K+1}(x−c) with 2K+1 ≥ max(N, 2t+2). Then F_A = (x−c)·((x−c)² + B(x−c) + π^{2K+1}); the quadratic factor has polygon {(0, 2K+1), (1, t), (2, 0)} with 2t < 2K+1: two one-point sides — two roots in O at distinct valuations t and 2K+1−t: σ_A = {(1,1),(1,1),(1,1)}.
> Lift 2 (ramification-directed): F_B = (x−c)³ + B(x−c)² + π^L with L ≥ 3N and L − t odd (choosable). Polygon of the recentered cubic: {(0, L), (1, ∞), (2, t), (3, 0)}: vertex at 2 (since (L−t)/2 > t ⟸ L ≥ 3N > 3t at t ≤ N−1; **[r4] at t = N the parity clause supplies the strict inequality: L ≥ 3N with L − N odd forces L ≥ 3N+1 > 3N = 3t**); left side length 2, slope (L−t)/2 with odd numerator — an e = 2 irreducible block — plus the slope-t simple root: σ_B = {(2,1),(1,1)}.
> In every case F_A ≡ F_B ≡ the member mod π^N (all correction terms sit at heights ≥ N — at t = N the B-terms included), both lifts have disc ≠ 0 **[r4: proved below in EVERY characteristic; the sealed warrant "distinct irreducible factors, étale" is a characteristic-0 reflex — in char p an e = p side can be purely inseparable, which is exactly how the deleted branches failed]**, and σ_A ≠ σ_B (three unramified pieces vs an e = 2 block). So every member of the species is genuinely σ-ambiguous — two disc ≠ 0 lifts with different σ, i.e. undecided in the S1 pinned sense. Count: q centers × q^{N−1} free b₂ (b₂ = 0 included, now via t = N). ∎”

**RESOLUTION TRACE:** Base §S3.2, lines 837–871, with `[r4]` F1's three brackets landed in place.

**TEETH:** Battery family W12-DRAIN3 (“every species member classified undecided, count = q^N per row”) and W12-ORACLE's 85 constructed witness pairs — the latter scoped by `[r5]` MINOR 3 (shard 2) to the 70 `b₂ ≠ 0` pairs.

---

### EFF.W12.s1of2.39  [lemma]

**CANONICAL STATEMENT:** `[r4]` SEPARABILITY OF THE REPAIRED PAIR, EVERY CHARACTERISTIC

> “**[r4] SEPARABILITY OF THE REPAIRED PAIR, EVERY CHARACTERISTIC** (the warrant the sealed proof outsourced to "étale"; write y = x − c, so F_A = y·(y² + By + π^{2K+1}) and F_B = y³ + By² + π^L with v(B) = t ∈ [1, N], 2K+1 ≥ max(N, 2t+2), L ≥ 3N, L − t odd):
>
> * **F_A.** disc(y² + By + π^{2K+1}) = B² − 4π^{2K+1} has valuation EXACTLY 2t in every case: in equal characteristic 2 the second term vanishes (4 = 0) leaving B² ≠ 0; otherwise v(4π^{2K+1}) ≥ 2K+1 ≥ 2t+2 > 2t = v(B²). With Res(y, y²+By+π^{2K+1}) = π^{2K+1} ≠ 0, disc F_A = (B² − 4π^{2K+1})·π^{2(2K+1)} ≠ 0. The two O-roots come out characteristic-freely too: y = π^t z gives π^{2t}(z² + uz + π^{2K+1−2t}) with u := B/π^t a unit and 2K+1−2t ≥ 2, whose derivative 2z + u is a UNIT at both z ≡ 0 and z ≡ −u (in char 2 it IS u), so Hensel yields roots of valuations t and 2K+1−t as the polygon says. σ_A = {(1,1)³}.
> * **F_B.** y = π^t s gives π^{3t}·g(s), g(s) = s³ + us² + π^{L−3t} with u := B/π^t a unit and L − 3t ≥ 1 ODD (= (L−t) − 2t). Then g(−u) = π^{L−3t} and g′(−u) = 3u² − 2u² = u², a UNIT in EVERY characteristic (char 3: 3u²−2u² = u²; char 2: 3u² = u², 2u² = 0), so v(g(−u)) = L−3t > 0 = 2v(g′(−u)): Hensel gives one root s ≡ −u, i.e. ONE O-root of F_B at valuation t, and the complementary quadratic factor's roots sit at v(s) = (L−3t)/2 ∉ ℤ (odd numerator) — an irreducible e = 2 block, coprime to the O-root factor. σ_B = {(2,1),(1,1)}. Separability: in MIXED characteristic the fraction field has characteristic 0, so distinct irreducible factors are automatically étale; in EQUAL characteristic p, F_B(0) = π^L ≠ 0 and F_B′ = 3y² + 2By, so at p = 2, F_B′ = y² ⟹ gcd(F_B, F_B′) = 1; at p = 3, F_B′ = 2By ⟹ the same; at p ≥ 5 the roots of F_B′ are 0 and −2B/3 with F_B(−2B/3) = (4/27)B³ + π^L ≠ 0 (valuations 3t < L) ⟹ gcd = 1. Uniformly, disc F_B = −4B³π^L − 27π^{2L}: a unit times π^{2L} in equal char 2 (27 odd), a unit times B³π^L in equal char 3 (−4 = −1 ≠ 0) — nonzero in both.”

**CONDITIONALITY:** Unconditional in every characteristic, at the stated parameter constraints (`v(B) = t ∈ [1, N]`, `2K+1 ≥ max(N, 2t+2)`, `L ≥ 3N`, `L − t` odd).

**DERIVATION:** As displayed: discriminant valuations computed case-by-case, Hensel legs with unit derivatives exhibited in each characteristic, `gcd(F, F′) = 1` checked at `p = 2`, `p = 3`, `p ≥ 5` separately.

**RESOLUTION TRACE:** Base §S3.2, lines 873–904.

**TEETH:** The `[r4]` repair's fresh instrument: “for p = 2,3,5,7 at N = 2,3,4 … gcd(F, F′) = 1 and disc ≠ 0 in EVERY case, at the predicted valuations”, plus the mixed-characteristic re-check over `ℤ₂, ℤ₃, ℤ₅` (`.40`).

---

### EFF.W12.s1of2.40  [changes-record]

**CANONICAL STATEMENT:** `[r4]` F1 REPAIR RECORD — the deleted branches, and the honest battery-invisibility disclosure

> “*What the deleted branches did.* With B = 0 the same computations FAIL: Lift 1 becomes y(y² + π^{2K+1}) whose quadratic has disc = −4π^{2K+1} = 0 in equal characteristic 2 — it is (y + π^{(2K+1)/2})² over the closure, a purely inseparable e = 2 = p side, and gcd(F_A, F_A′) = y² + π^{2K+1} ≠ 1 — so the sealed σ_A = {(1,1),(2,1)} does not exist there; and Lift 2 becomes y³ + π^L whose derivative is ≡ 0 in equal characteristic 3 (disc = −27π^{2L} = 0, F_B = (y + π^{L/3})³), so the sealed σ_B = {(3,1)} does not exist there. The repaired construction never has B = 0.”

> “**[r4] F1 REPAIR RECORD (PE4 @ 26689da, FINDING 1 CRITICAL, proof-level; LEMMA W12-S3.2's STATEMENT and count are byte-unchanged).** What was at stake: for the q members per row with b₂ = 0 over F_q[[t]] with p ∈ {2,3} the sealed proof established nothing, so the bound degraded to U₃^TRP ≥ q^N − q there — denting THEOREM W-12.C's displayed q^N ≤ U₃^TRP(q,N) and the BOX-3 annex's inherited q^N ≤ U₃^σ in equal characteristic 2/3 ONLY. With B = π^N both stand at q^N in every characteristic, and nothing downstream moves (no count, no law, no other lemma consumed the B = 0 branches).”

> “**Battery-invisibility, stated honestly:** the σ-witness leg (W12-ORACLE) builds the pairs only on the mixed-characteristic ℤ_p rows (W12-BOX-6: "PARI legs are mixed-characteristic only"), and in mixed characteristic BOTH sealed B = 0 witnesses are perfectly good (disc(y²+p^{2K+1}) = −4p^{2K+1} ≠ 0, disc(y³+p^L) = −27p^{2L} ≠ 0) — so the defect was invisible to the sealed instrument BY CONSTRUCTION, not by an instrument bug; no battery number changes (W12-DRAIN3's q^N per row is a READER-verdict count, not a witness claim), and the runner + artifacts stay BYTE-FROZEN at seal f669cb0.”

> “**Machine evidence for the repaired pair, in the vein the frozen kit does not cover:** PE4's fresh leg showed the sealed witnesses inseparable over F₃[t] (F_B′ ≡ 0) and F₂[t] (gcd(F_A, F_A′) = y²+t⁵ ≠ 1) and the B = π^N pair separable in both — those equal-characteristic rows are now the machine evidence for this lemma. This repair re-verified the repaired pair independently (fresh instrument, sympy over GF(p)[t] and ℤ): for p = 2,3,5,7 at N = 2,3,4 with 2K+1 = 2N+3 and L = whichever of {3N+1, 3N+2} makes L−N odd, gcd(F, F′) = 1 and disc ≠ 0 in EVERY case, at the predicted valuations — disc F_A = t^{2N+2(2K+1)} in char 2 (t^18 at N = 2), disc F_B = t^{2L} in char 2 (t^14 at N = 2, L = 7) and −t^{3N+L} in char 3 (−t^13) — plus the Hensel legs: the quadratic's roots have valuations exactly N and 2K+1−N in F₂[[t]], and g(s) = s³+s²+t^{L−3N} has its unit-derivative root at s ≡ −1 in F_p[[t]] for p = 2,3,5 (residual 0 to precision t^{6N+12}), giving F_B's O-root at valuation N. Mixed characteristic re-checked over ℤ₂, ℤ₃, ℤ₅ (π = p, v(p) = 1): disc ≠ 0 throughout, valuations 2N+2(2K+1) for F_A and 2L (p = 2) / 3N+L (p = 3, 5) for F_B.”

> “The trivial upper bound: U₃^TRP ≤ #TRP stratum = q·q^{3(N−1)} = q^{3N−2}. Both W-12.C bounds stand. ∎”

**CONDITIONALITY:** A proof-level CRITICAL repair with statement and count byte-unchanged. The frozen instrument's 85 witness pairs remain scoped: they are true facts about the witnesses built, silent on the repaired pair (`[r5]` MINOR 3, shard 2).

**DERIVATION:** The failure of the deleted branches is exhibited explicitly in each bad characteristic; the repaired pair's warrant is `.39`.

**RESOLUTION TRACE:** Base §S3.2, lines 906–963, with the machine-scope bracket at the S3.2 machine line.

**TEETH:** The fresh equal-characteristic instrument (sympy over `GF(p)[t]` and `ℤ`) is the machine evidence; the frozen kit is disclosed as structurally blind here.

---

### EFF.W12.s1of2.41  [lemma]

**CANONICAL STATEMENT:** §S3.3 — the general-n lower bound

> “At every n ≥ 3: pick the level-0 pattern (x−c̄)²·h̄ with h̄ monic irreducible of degree n−2, h̄ ≠ x−c̄ (such h̄ exists over every F_q at every degree: for n−2 ≥ 2 irreducibles of that degree are non-linear; for n−2 = 1 take a second linear, q ≥ 2). By LEMMA W12-S2.1, decidedness is branchwise and the h̄-branch is simple (decided); by W-11's drainage law the double-root branch has q^{N−1} σ-undecided members per center. Fibering (S2.1 bijection):
>
>     undecided(n, q, N) ≥ q^{N−1}·q^{(n−2)(N−1)} = q^{(n−1)(N−1)}
>
> — one pattern already suffices (n = 2: W-11's law itself). ∎ (The census-weighted refinement — summing over admissible h̄ — follows the same way; the one-pattern form is all W-12.B's order-tightness needs.)”

**CONDITIONALITY:** A lower bound only; it establishes W-12.B's rate is correct-in-order **wherever the conjecture holds**, not that it holds.

**DERIVATION:** One level-0 pattern, branchwise decidedness (`.21`), W-11's per-center drainage, and the S2.1 fibering.

**RESOLUTION TRACE:** Base §S3.3, lines 967–979. Classified `[r3]`-parse-ROBUST (valid under both σ notions) at `.16`.

**TEETH:** Implied by W12-DRAIN3's species row at n = 3; no dedicated general-n row.

---

### EFF.W12.s1of2.42  [lemma]

**CANONICAL STATEMENT:** §S3.4 Step 1 — rationality

> “*Step 1 (rationality).* For one family F with P_F a shifted product Π_{i=1}^{d_F}(a_i + b_iℤ_{≥0}) and dens_F = c_F(q)·q^{−ℓ_F}, ℓ_F = m₀ + Σ m_ix_i with m_i > 0:
>
>     Σ_{x ∈ P_F} dens_F(x) = c_F(q)·q^{−m₀−Σm_ia_i}·Π_i (1 − q^{−m_ib_i})^{−1} ∈ ℚ(q)
>
> by d_F iterated geometric series (absolutely convergent: q ≥ 2, m_ib_i ≥ 1).”

with its two guards, both landed as dated brackets:

> “[r1 m1, two guards: coordinates with step b_i = 0 — point coordinates, which (A1)'s "arithmetic progressions" does not exclude — are absorbed (fold m_ia_i into m₀ and delete the coordinate) BEFORE applying the display, whose i-th factor would otherwise divide by zero while the sum is trivially finite; the product runs over the coordinates with b_i ≥ 1. And [r2, PE2 FINDING 3: the r1 clause claimed the m_i themselves are integers by a FALSE implication — ℓ(x) = (x+1)/2 on 1 + 2ℤ_{≥0} is integer-valued with strictly positive coefficient and m₁ = 1/2] the exponents the display actually uses ARE integers: ℓ_F integer-valued on P_F gives m_ib_i ∈ ℤ_{>0} (evaluate at x and at x + b_ie_i and subtract; positivity from m_i > 0, b_i ≥ 1) and m₀ + Σm_ia_i = ℓ_F(base point) ∈ ℤ — which is all the display needs (its ratio exponents are the m_ib_i, its leading exponent is ℓ_F(base)) — so each factor is a bona fide element of ℚ(q). Every in-note P_F has b_i ∈ {1, 2}; point families enter the n = 2 instance as d_F = 0 families.] Finite unions of shifted products: inclusion–exclusion (intersections are again shifted products or empty). Finitely many families: finite sums stay in ℚ(q). By (A1)'s q-independence clause the resulting R_τ is ONE rational expression, the same at every prime power and characteristic.”

**CONDITIONALITY:** The final sentence rests on (A1)'s q-independence clause — **which is exactly the clause the 2026-08-12 correction rewrites** (`.12`). The append re-derives Step 1 under the corrected hypothesis and reaches the same conclusion:

> “**Derivation of Step 1 under the corrected hypothesis.** … Therefore \[ \sum_{x\in P_F}\operatorname{dens}_F(x) = c_F(q)q^{-\ell_F(a)} \prod_i(1-q^{-m_ib_i})^{-1}, \] which is the evaluation at \(X=q\) of \[ c_F(X)X^{-\ell_F(a)} \prod_i(1-X^{-m_ib_i})^{-1}\in\mathbb Q(X). \] Finite unions follow by inclusion–exclusion, and the finite sum over families remains in \(\mathbb Q(X)\). This proves both rationality and the “same expression at every prime power” conclusion.”

**DERIVATION:** Iterated geometric series with the two guards (b_i = 0 absorption; integrality of the exponents actually used), then inclusion–exclusion and finite summation.

**RESOLUTION TRACE:** Base §S3.4, lines 983–1011, with `[r1]` m1 and `[r2]` FINDING 3 landed in place; the concluding q-independence step re-derived at the 2026-08-12 (A1) correction.

**TEETH:** The n = 2 instance's series are re-verified symbolically in-note (`.44`).

---

### EFF.W12.s1of2.43  [lemma]

**CANONICAL STATEMENT:** §S3.4 Steps 2–4 — the limit, the partition, and the classical tie

> “*Step 2 (R_τ is the decided-core limit).* D_τ(N) := Σ_{σ_F = τ, x visible} count(F, x) = q^{nN}·Σ_{x visible} dens_F(x) by (A1) exactness and disjointness. The visible sets {x : ν_F(x) ≤ N} increase to P_F (ν_F affine), so D_τ(N)/q^{nN} is a monotone partial-sum net of the positive convergent series of Step 1: D_τ(N)/q^{nN} → R_τ(q).”

> “*Step 3 (Σ_τ R_τ = 1).* Σ_τ D_τ(N) + r(N) = q^{nN} by (A1) disjointness and (A2)'s definition of r; divide by q^{nN}, let N → ∞, apply (A2).”

> “*Step 4 (the classical tie).* μ_τ := Haar density of {F ∈ O[x] monic degree n : disc F ≠ 0, splitting type τ} (well-defined: the τ-loci are open by Krasner on the étale locus and partition it; disc = 0 is a null set; Haar = the product measure on coefficients, and a window-N class is a union of cylinders of mass q^{−nN} each). Lower bound: the visible decided-τ classes at window N are disjoint cylinder unions all of whose disc ≠ 0 lifts have type τ (**[r4, PE4 F2] (A1)'s σ-LABELING clause: every member of every class (F, x) with σ_F = τ is σ-DECIDED with forced σ = τ, so all its disc ≠ 0 lifts have type τ — this is the whole content the lower bound consumes, and it is now hypothesised rather than read off (A0)'s "the read's type"; (A0) is the same statement in its well-posedness phrasing**): μ_τ ≥ D_τ(N)/q^{nN}. Upper bound: a type-τ F with disc ≠ 0 truncates into SOME window-N class — either a visible core class, which is then necessarily a τ one (by (A0) applied to F itself: F is a disc ≠ 0 lift of its own truncation **[r5, PE5 m1: route this through (A1)'s [r4] σ-LABELING clause, as the STEP-4 RE-CHECK in the [r4] FINDING-2 record already does — the clause says every disc ≠ 0 lift of every member of every visible core class has type σ_F, and that is what is applied here, at F over its own truncation. Post-[r4], (A0) is the same statement in its well-posedness phrasing, i.e. redundant-but-retained: it is not the load-bearing warrant at either bound]**), or into the rest: μ_τ ≤ (D_τ(N) + r(N))/q^{nN}. Let N → ∞: both bounds → R_τ(q) by Steps 2 and (A2): μ_τ = R_τ(q). ∎”

**CONDITIONALITY:** Both Step-4 bounds consume (A1)'s σ-LABELING clause and nothing else σ-flavoured (`.19`); (A0) is redundant-but-retained. The classical inputs (Krasner-openness, the τ-partition of the étale locus, the disc = 0 null set) are cited as classical and displayed.

**DERIVATION:** As quoted — monotone convergence for Step 2, the (A1)/(A2) partition for Step 3, and the two-sided cylinder estimate for Step 4.

**RESOLUTION TRACE:** Base §S3.4, lines 1013–1046, with `[r4]` F2's lower-bound bracket and `[r5]` m1's upper-bound routing landed in place.

**TEETH:** NONE (classical measure argument); its non-vacuity check is the n = 2 firing at `.44`.

---

### EFF.W12.s1of2.44  [instance-record]

**CANONICAL STATEMENT:** §S3.4 — the n = 2 instance (fires unconditionally), with the tail routed honestly

> “**The n = 2 instance (fires unconditionally), with the tail routed honestly.** Core families: SEP-SPLIT, SEP-INERT (point families), RAM(h) (P = 1 + 2ℤ_{≥0}, dens (q−1)q^{−h−1}, ν = h+1), 2SIDED(w₁,w₂) ({1 ≤ w₁ < w₂}: the shifted-product image (w₁,δ) ∈ (1+ℤ_{≥0})×(1+ℤ_{≥0}), w₂ = w₁+δ; dens (q−1)²q^{−w₁−w₂−2}), SPLITEQ(k), INERTDEEP(k) ({k ≥ 1}) — exact laws, disjointness, and q-uniform data by THEOREM W-11(i)(ii); (A0) by W-11's decidedness (+ its sealed double-lift oracle leg). SPLIT-TAIL is NOT a core family (its count (q−1)q^{N−1} per center per w is not dens·q^{2N} with N-free dens): it routes through (A2): r(N) = undecided + tail = q^N + q·⌊(N−1)/2⌋·(q−1)·q^{N−2} = O(N·q^N), and r(N)/q^{2N} → 0 by W-11 clause (iii) + the tail law. *(Display note: (A2) is phrased as drainage of the REST — not of the σ-undecided residue alone — exactly so that window-boundary families route through it; an (A1)-only reading would make the n = 2 instance-check incomplete.)* Steps 1–4 then re-derive, through the general mechanism:
>
>     R_split = (q−1)/(2q) + 1/(q²(q+1)) + (q−2)/(2q²(q+1)) = q/(2(q+1))
>               [SEP + 2SIDED + SPLITEQ]
>     R_inert = (q−1)/(2q) + 1/(2q(q+1))                    = q/(2(q+1))
>               [SEP + INERTDEEP]
>     R_ram   = Σ_{h odd} (q−1)q^{−h−1}                     = 1/(q+1)
>     Σ_τ R_τ = 1 ✓
>
> — W-11's densities recovered: the reduction is non-vacuous and instance-checked. (Series re-verified this session: Σ 2SIDED = (q−1)²q^{−2}·Σ_{w₁≥1}q^{−2w₁}/(q−1) = 1/(q²(q+1)); Σ SPLITEQ = (q−1)(q−2)/2 · q^{−2}/(q²−1) = (q−2)/(2q²(q+1)); Σ INERTDEEP = (q−1)/2 · q^{−1}/(q²−1) = 1/(2q(q+1)); the R_split bracket: (q−1)/(2q) + (2+q−2)/(2q²(q+1)) = ((q−1)(q+1)+1)/(2q(q+1)) = q/(2(q+1)).)”

**CONDITIONALITY:** Unconditional at n = 2 — the hypotheses are W-11's theorems. The display note is a load-bearing scoping remark: (A2) must drain the REST, not just the σ-undecided residue, or this very instance-check fails.

**DERIVATION:** The six core families with their laws from W-11(i)(ii), the tail routed to (A2), then Steps 1–4; every series re-verified symbolically in-session.

**RESOLUTION TRACE:** Base §S3.4, lines 1048–1078.

**READING NOTE:** the 2026-08-12 (A1) correction is what makes this instance *literally* satisfy (A1): the n = 2 coefficients `q−1` and `(q−1)/(2q)` are q-dependent, hence admissible only as evaluations of fixed rational functions `c_F(X)` — “the literal conflict with the q-dependent n = 2 coefficients confirmed” (that append's verification note).

**TEETH:** The three densities match W-11's proved values exactly; W12-L0HIST ties the history-resolved forms to the sealed W-11 predictor.

---

### EFF.W12.s1of2.45  [scope-record]

**CANONICAL STATEMENT:** §S3.4 — Conditionality at n ≥ 3, displayed montes-style

> “**Conditionality at n ≥ 3, displayed montes-style.** (hMenu-3) = the complete n = 3 core menu: the order-1 layer is supplied by W-12.A (S2.4's seven TRP families — note their parameter sets and laws are q-uniform shifted-product data, so (A1)-admissible — plus the DBL transport of the entire n = 2 menu via W12-L1/W12-L0); MISSING: the TRP refinement families (depth ≥ 1) — W12-BOX-2. (hExhaust-3) = (A2) at n = 3: the σ-undecided DBL part is proved (S3.1); and [r2, PE2 FINDING 2 — displaying the one remaining r(N) leg, previously undisplayed] the DBL BOUNDARY-TAIL families — the transported SPLIT-TAIL (σ-DECIDED split-certified; their count is N-dependent, dens would be (q−1)²q^{−N−2}, hence they lie in NO (A1)-admissible family) — route through (A2) exactly as SPLIT-TAIL does at n = 2, with vanishing mass ⌊(N−1)/2⌋·(q−1)²·q^{2N−2} (= q(q−1) patterns × W12-L1(c)'s q^{N−1} simple-branch fiber × W12-L0's SPLIT-TAIL row, per-w aggregate (q−1)²q^{2N−2}, over the ⌊(N−1)/2⌋ values of w; re-verified against the committed JSON on ALL 23 cubic rows this repair, e.g. (Zp,2,5): 256+128+128 = 512, exact zeros at N = 2 included), /q^{3N} → 0; MISSING: a vanishing U₃^TRP upper bound — W12-BOX-3 (whose conservative-convention bound also drains the TRP members σ-decided only by tail certification: those are conv-UNDECIDED by construction, so no TRP tail leg is separately owed). At n ≥ 4 additionally [W12-H] (W12-BOX-1) at composite stages. No other conditionality: (A0) at the order-1 decided shapes is S2.3's Ore argument **[r5, PE5 m1: stated exactly — what the order-1 decided shapes must supply is (A1)'s [r4] σ-LABELING clause (every member of every visible core class σ-DECIDED with forced σ = σ_F, i.e. at all its disc ≠ 0 lifts), since that is what BOTH Step-4 bounds consume; S2.3's Ore argument is what PROVES that clause at the order-1 layer, and (A0) is the same statement in its well-posedness phrasing]**.”

**CONDITIONALITY:** THIS unit is the conditionality vocabulary for n ≥ 3: exactly `{(hMenu-3)} + {(hExhaust-3)}` at n = 3, plus `[W12-H]` at n ≥ 4. Both n = 3 legs are DISCHARGED at composition grade by the two out-of-range annexes; the closing “No other conditionality” sentence is routed through (A1)'s σ-labeling clause by `[r5]` m1.

**DERIVATION:** Leg-by-leg accounting of `r(3, N)`: the DBL σ-undecided term is proved (`.36`), the DBL boundary-tail mass is computed and shown vanishing, and only the `U₃^TRP` upper bound is missing.

**RESOLUTION TRACE:** Base §S3.4, lines 1080–1109, with `[r2]` FINDING 2 and `[r5]` m1 landed in place.

**TEETH:** The boundary-tail mass re-verified against the committed JSON on all 23 cubic rows (worked example `(Zp,2,5): 256+128+128 = 512`, with the `N = 2` exact zeros).

---

### EFF.W12.s1of2.46  [scope-record]

**CANONICAL STATEMENT:** §S4.1 — Consumed at PROVED strength

> “* **THEOREM W-11(n = 2)** — the complete menu + exact drainage + the S2.3 refinement isomorphism: consumed at pin (S2.6, S2.7, S3.4 instance).
> * **THEOREM W-10(2,1,1)** — the digit-calculus template (S2.2 is its all-degrees generalization; the (2,1,1) row is the m = 2, d = 1, one-side instance) and the recentering mechanics.
> * **LEMMA J-D0** — the shape-keying/count-gauge-blindness FRAME: what makes clause (i) well-posed shape-only (S0 reason 1, S2.2's census remark, W12-L1(b)'s unit-scaled letters). The order-1 proofs are self-contained elementary arithmetic, so J-D0 is corroborated at every new instance and load-bearing for the general-form framing.
> * **Classical inputs**: Hensel (coprime lifting, S2.1), Ore's theorem / GMN order-1 (S2.3), the finite-field factorization censuses (S2.2, re-derived + machine-checked).”

**CONDITIONALITY:** J-D0 is carried as a FRAME, not as a consumed theorem in the order-1 proofs (“the order-1 proofs are self-contained elementary arithmetic”) — the note is explicit that J-D0 is corroborated by them and load-bearing only for the general-form framing.

**DERIVATION:** Supplier inventory.

**RESOLUTION TRACE:** Base §S4.1, lines 1113–1128.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:THEOREM W-11` — grep-verified count **3**; `S2.3` — count **8**.

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:THEOREM W-10` — grep-verified count **2**.

XREF: `lean/notes/openmath/JD0_PROOF_2026-08-08.md:LEMMA J-D0` — grep-verified count **4**.

**READING NOTE:** the classical-inputs row's “Ore's theorem / GMN order-1” is the `Q1 W12-2` retarget row of `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` (→ [GN15] Thm 2.3; verdict COVERS-ALL-O). Recorded, not applied.

**TEETH:** W12-PIN (md5 pins on the five frozen imports, incl. the W-11 instrument at `500aae15…`).

---

### EFF.W12.s1of2.47  [hypothesis]

**CANONICAL STATEMENT:** §S4.2 — THE DISPLAYED HYPOTHESIS BOX `[W12-H]` (orders ≥ 2), five named inputs

> “The general clause (i) at orders ≥ 2 — shapes with repeated residual factors of degree ≥ 2, i.e. towers whose key polynomials have degree > d — is CONDITIONAL on the following FIVE named inputs [r1: the sealed box said "on, exactly:" over FOUR members; PE1 F2 found the fifth (H-e) missing, and its further hunt found no sixth — the completeness of this list is PE1's verified negative, not asserted by fiat]:
> * **(H-a)** the JC composite-stage warrant (no-cancellation + level-detection of residual reads at wild composite stages; JC-PSIKER/JC-LOAD, GRTJC ACCEPTED 2/2 @ 83f47f4) — consumed as warrant, its own conditionality displayed there;
> * **(H-b)** the JB membership faces at unbounded abscissa grids (JB-VTX/JB-DEV; GRTJB ACCEPTED 2/2 @ 83f47f4 with row-12's u ≥ 0 proviso membership residue OPEN);
> * **(H-c)** the J-D1 (H1) residue-structure package of §S5 (the value-side dictionary at composite stages), conditional on the six weld notes' displayed boxes + the Σ-LAW residue;
> * **(H-d)** the universal residual censuses OVER RESIDUE TOWERS (S_λ over F_{q^d} with d the accumulated residue degree — the S2.2 censuses suffice level by level once (H-a)–(H-c) identify the reads);
> * **(H-e)** [r1, added at PE1 F2] the order-≥ 2 GMN LEAF/σ-DECISION theorem — the higher-order analogue of the Ore step clause (i) itself uses at order 1 (S2.3): separable order-r residual ⟹ σ-decided with (e, f) read off (the GMN order-r types theorem — a statement about exact polynomials over O — PLUS the (H-a)/(H-b)-leg in-window pinning of the consumed read data, the composite-stage analogue of S2.3's "All data the read consumes sit at heights ≤ N−1" sentence [r2, PE2 m1: the bare GMN cite under-priced the window-level statement]), which is exactly (A0) well-posedness at composite stages. S4.1's classical-inputs list is order-1 scoped ("Ore's theorem / GMN order-1"), so this input belongs HERE; W-12.D consumption at n ≥ 4 needs it at every composite-stage shape. If (H-c)'s FGMN-4.2 pairings are read as carrying it, that derivation is NOT displayed in this note — it is priced as its own member.”

> “No order-≥ 2 count law is CLAIMED here; [W12-H] is the priced route (W12-BOX-1). The λ = (1²) quartic stratum of S2.5 is the box's concrete frontier exhibit, volume law included.”

**CONDITIONALITY:** This IS the conditionality interface. Two facts about it are load-bearing downstream: the list's **completeness is PE1's verified negative** (no sixth input found), and `(H-e)` is **separately priced** — if (H-c) were read as carrying it, that derivation is not displayed here.

**DERIVATION:** Not derived — a hypothesis box, with each member's supplier and grade named.

**RESOLUTION TRACE:** Base §S4.2, lines 1132–1170, with `[r1]`'s fifth member and `[r2]` m1's window-level pricing landed in place. Out of range, the 2026-08-12 dated correction repairs W12-BOX-1's reference to this list from `(H-a)–(H-d)` to `(H-a)–(H-e)` (`.49`).

XREF: `lean/notes/openmath/GRTJC_PROOF_2026-08-08.md:JC-PSIKER` — grep-verified count **19**; `JC-LOAD` — count **31**.

XREF: `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md:JB-VTX` — grep-verified count **77**; `JB-DEV` — count **63**.

XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:Σ-LAW` — grep-verified count **14**; the residue (H-c) is conditional on.

**READING NOTE (external, not an edit).** `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` row **Q1 W12-3** targets `(H-e)` by name — *“(H-e) … order-≥2 GMN LEAF/σ-DECISION theorem” | NS-3 | re-cite [GN15] Thm 2.3 / [AGNPRW] Thm 4.4 + Prop 4.5”* — with NS-3's verdict **COVERS-ALL-O** ([GN15] Thm 2.3 being simultaneously the order-1 and order-r statement, since µ ranges over all inductive valuations). Note this retarget addresses the CITED SOURCE's generality, not `(H-e)`'s status as a hypothesis of this note: `(H-e)` also carries the in-window pinning leg, which is not a literature citation.

**TEETH:** The `λ = (1²)` quartic stratum (`.31`) is the frontier exhibit with a proved volume law and an open σ-resolution.

---

### EFF.W12.s1of2.48  [scope-record]

**CANONICAL STATEMENT:** §S5 — THE J-D1 FAITHFULNESS HANDOFF (the blueprint row's own content, at its S-price)

> “The blueprint's (J-D1), verbatim (GRT_WELD_BLUEPRINT_2026-08-08 §S2.4):
>
> > **(J-D1) THE FAITHFULNESS HANDOFF.** Under J-A/J-B/J-C, the accepted carry-law corpus proves the (H1) residue-structure package at orders ≥ 2: the anchored-march frame tie + residual dictionary ((GR-B)'s displayed content, both FGMN-4.2 pairings) hold at every realized composite stage of every classifier tower IN THE WELDED CLASS — i.e. GD-2/GD-3's one open input becomes a theorem there, and with it the GD-1 representative-admissibility and order-≥ 2 KEY1 members ((H1) members (b)/(d)) inherit the corpus's proofs where the dictionary reaches.”

> “**The composition, displayed (nothing re-proved).** All six weld notes are ACCEPTED 2/2 (ledger fold 17d2a32): GRTJA @ f131c53, GRTJB + GRTJC @ 83f47f4, GRTW2 @ adc6cf3, LIFTCORNER @ 08f61e9, WELDMASTER @ 66b3498. The W-0..W-9 rows therefore stand at those notes' displayed conditionality — the surviving open surface being W2-OPEN-2/OPEN-2a (since NARROWED to the Σ-LAW single lemma, OPEN2ATTACK verdict @ 4a970aa; forward direction at attempt grade GIVEN Σ-LAW) plus the notes' own boxed residues. THEREFORE, by the blueprint's own composition (displayed here, owned by the blueprint): the (H1) residue-structure package at orders ≥ 2 holds ON THE WELDED CLASS, conditional on exactly the union of the six notes' displayed boxes + the Σ-LAW residue. Consumers: the (H1) row's retirement path, then the IFK faces O-2/O-3 through the GD carriers — consumed DOWNSTREAM, owned by their own units, nothing of them owned here. What W-12's assembly takes from J-D1: (H-c) of [W12-H] — the order-≥ 2 layer's value-side warrant when that layer is composed; the order-1 layer proved in S2 needs NONE of it, which is why it could be proved outright now. (GR-B)'s RE-ACCEPTED print package is cited only as the row's named partial, at its own perimeter. This discharges the blueprint row AS THE DISPLAY IT PRICED (**S**, composition; conditional on IFK downstream). DULEMMA (@ 048cf6d/f819f26, perimeter e_m ≥ 2) is NOT consumed by any count law here (every order-1 count is a COUNT statement, not a (DMULT) statement — W-11 S3's fence inherited); it appears only in this weld-state display.”

**CONDITIONALITY:** A DISPLAY — “nothing re-proved”, and the (H1) conclusion is conditional on “exactly the union of the six notes' displayed boxes + the Σ-LAW residue”. The whole section is priced **S** (composition). Nothing in §§S2–S3 depends on it.

**DERIVATION:** The blueprint's own composition, executed at the accepted-supplier grades.

**RESOLUTION TRACE:** Base §S5, lines 1174–1209; untouched by later rounds.

XREF: `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:(J-D1) THE FAITHFULNESS HANDOFF` — grep-verified count **1**.

XREF: `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md:W2-OPEN-2` — grep-verified count **60**; `OPEN2ATTACK` — count **5**; `Σ-LAW` — count **14**.

XREF: `lean/notes/openmath/WELDMASTER_2026-08-08.md:WELD-M-PKG` — grep-verified count **5**; the WELDMASTER package cited in the six-note list.

XREF: `lean/notes/openmath/DULEMMA_PROOF_2026-08-08.md:DULEMMA` — grep-verified count **1**; declared NOT consumed by any count law.

**NON-IMPORT (explicit):** “DULEMMA … is NOT consumed by any count law here”; “Consumers: … consumed DOWNSTREAM, owned by their own units, nothing of them owned here.”

**TEETH:** NONE (composition display).

---

### EFF.W12.s1of2.49  [open-obligation]

**CANONICAL STATEMENT:** §S6 — W12-BOX-1 (orders ≥ 2 = `[W12-H]`)

> “* **W12-BOX-1 (orders ≥ 2 = [W12-H]).** No count law at composite stages is claimed; the route is priced in S4.2 ((H-a)–(H-d)) and its frontier is exhibited (S2.5's λ = (1²) quartic stratum: volume law proved, σ-resolution open). The general W-10 (every decided shape, every order) remains OPEN — W10-BOX-1 stands untouched.”

**CONDITIONALITY — the dependency range is CORRECTED out of range** (2026-08-12, resolution rule 7):

> “In W12-BOX-1, the reference
>
> > “the route is priced in S4.2 ((H-a)–(H-d))”
>
> is corrected to
>
> > “the route is priced in S4.2 ((H-a)–(H-e)).”
>
> S4.2 explicitly enumerates five inputs. In particular, `(H-e)` is the order-\(\ge2\) GMN leaf/σ-decision theorem together with the in-window pinning supplied by `(H-a)` and `(H-b)`; it is separately load-bearing for the composite-stage analogue of S2.3 and for W-12.D's σ-labeling requirement. The correction changes no mathematical conclusion; it restores the box's dependency record to the five-input list already displayed in S4.2.”

**Effective reading:** `(H-a)–(H-e)`.

**DERIVATION:** Bookkeeping repair against S4.2's own five-member list (`.47`).

**RESOLUTION TRACE:** Base §S6, lines 1213–1217; corrected at lines 2143–2153.

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:W10-BOX-1` — grep-verified count **1**; the general W-10 box declared untouched.

**TEETH:** The `λ = (1²)` quartic stratum's measured volume (W12-QRT) is the frontier exhibit.

---

### EFF.W12.s1of2.50  [open-obligation]

**CANONICAL STATEMENT:** §S6 — W12-BOX-2, W12-BOX-3, W12-BOX-4 (the menu and drainage boxes)

> “* **W12-BOX-2 (n ≥ 3 refinement families; (hMenu-3)).** The depth-≥ 1 TRP families are not enumerated: the n = 3 instance bracket needs TWO node species — (α) the triple-cluster node and (β) the DBL-re-entry node at reduced window (S3.1) — and neither species' transfer law is derived. W-12.D at n = 3 is conditional on this menu; it is the natural W-13 rung, with S2.4's depth-0 completeness as its floor.
> * **W12-BOX-3 (U₃^TRP; (hExhaust-3)).** The exact triple-center drainage law is not derived; obstruction: the same two-species node calculus, plus a TRP tail-σ-certification lemma (the n = 3 SPLIT-TAIL analogue: a visible deep vertex can certify a split-off (1,1) piece even with b₀ window-hidden), which this note's instrument deliberately does NOT attempt: the battery's TRP reader certifies NO tail σ (conservative convention, disclosed in the runner), so its measured U₃^TRP is an UPPER count for the σ-convention residue — EXPLORATORY grade, no closed form preregistered. The proved content is the pair of bounds (S3.2 + trivial).
> * **W12-BOX-4 (n ≥ 4 drainage).** No upper bound at any grade; lower bounds only (S3.3). W-12.B is a conjecture with two proved instances of its shape (n = 2 exact; n = 3 DBL term exact).”

**CONDITIONALITY:** BOX-2 and BOX-3 are the two `(hMenu-3)`/`(hExhaust-3)` legs of W-12.D's n = 3 firing. Both are **DISCHARGED at composition grade** by the two verbatim annexes homed in shard 2 (HEX3 → BOX-3; HMENU3 → BOX-2), leaving the residual tail-σ-certification lemma open as HEX3-BOX-1. BOX-4 is untouched: no n ≥ 4 upper bound at any grade.

**DERIVATION:** Each box names its own obstruction; the derivations of the obstructions are `.37` (two species) and `.30` (depth-0 floor).

**RESOLUTION TRACE:** Base §S6, lines 1218–1238; BOX-2 discharged at ANNEX 2, BOX-3 at the BOX-3 ANNEX (both shard 2).

XREF: `lean/notes/openmath/HMENU3_PROOF_2026-08-08.md:COROLLARY HM3.D` — grep-verified count **11**; the discharge's downstream payoff (five cubic `R_τ(q)`, `Σ = 1`).

XREF: `lean/notes/openmath/HEX3_PROOF_2026-08-08.md:COROLLARY HEX3.C` — grep-verified count **8**; the characteristic-independence corollary that explains the battery's cross-characteristic observation.

**TEETH:** W12-DRAIN3's `U₃^TRP` row is EXPLORATORY by construction — it is the note's own statement that this box has no confirming machine row.

---

### EFF.W12.s1of2.51  [definition]

**CANONICAL STATEMENT:** §S6 — W12-BOX-7 (σ-convention at the TRP tail), the pinned notion

> “* **W12-BOX-7 (σ-convention at the TRP tail).** Decided = certified on window digits for all disc ≠ 0 lifts; the DBL side inherits W-11's proved convention (incl. its SPLIT-TAIL certification); the **battery's [r4, PE4 m1: one scope word — post-r3 there is exactly ONE definitional notion, clause 1's lift certification, and the conservative reader is a MEASUREMENT convention (as the runner docstring itself discloses); the sealed "the TRP side uses …" read definitionally would assert UNDECIDED (this clause) and DECIDED (clause 1) at once for a lift-certified TRP deep-tail member]** TRP reader uses the BOX-3 conservative convention. The two conventions can disagree only on deep-tail TRP members; the battery reports the measured TRP residue per row.”

**CONDITIONALITY:** THE definitional anchor of the σ-pin (`.08`). Post-`[r4]` m1 there is exactly **one** definitional notion (clause 1's lift certification); the conservative reader is a MEASUREMENT convention only. Without that scope word the box would have asserted DECIDED and UNDECIDED simultaneously for a lift-certified TRP deep-tail member.

**DERIVATION:** The one-word scope repair is justified by the contradiction it removes, displayed in the bracket itself.

**RESOLUTION TRACE:** Base §S6, lines 1255–1266, with `[r4]` m1 landed in place.

**TEETH:** The runner docstring's own disclosure of the conservative convention as a measurement convention (“correct as sealed”, per `.16`'s sweep class (c)).

---

### EFF.W12.s1of2.52  [fence]

**CANONICAL STATEMENT:** §S6 — W12-BOX-5, W12-BOX-6, W12-BOX-8 (instrument, coverage, and no-symmetry fences)

> “* **W12-BOX-5 (classifier reimplementation; lift convention).** The battery's cubic/quartic readers are convention-faithful reimplementations (W10-BOX-3/W11-BOX-3 inherited); the engine tie rides the accepted JB-VTX face + the SEALED W-11 instrument consumed by md5-pinned import (the W12-L1X seam is machine-checked pointwise). The Lean `omCount` evaluator remains order-0; growing it is Phase-B code (W-11 S4.1's spec now extends to every degree via W-12.A). Lift-convention independence of the member SET at deep shapes is the W-2/LIFTCORNER seam, not consumed (S2.2 convention note).
> * **W12-BOX-6 (oracle coverage).** PARI legs are mixed-characteristic only; eq-char rows are SAME-class evidence; no mixed-characteristic prime-power rows exist in the frozen kit (W10-BOX-4/W11-BOX-4 inherited verbatim). Quartic rows enumerate the quadruple-center stratum only (the QRT laws are stratum laws; no quartic drainage/partition claim exists to test).
> * **W12-BOX-8 (no FE / no symmetry claim).** Nothing here touches `htameFE`; the n = 2 split = inert window symmetry is not asserted at n ≥ 3 (the τ-lattice is richer; no per-window symmetry is claimed or expected).”

**CONDITIONALITY:** BOX-6 is the fence that made the `[r4]` F1 defect structurally invisible to the sealed instrument (`.40`) — it is load-bearing evidence-scoping, not boilerplate.

**DERIVATION:** Instrument and coverage audit.

**RESOLUTION TRACE:** Base §S6, lines 1239–1254 and 1267–1270.

XREF: `lean/notes/openmath/W10_PROOF_2026-08-08.md:W10-BOX-3` — grep-verified count **1**; `W10-BOX-4` — count **1**.

XREF: `lean/notes/openmath/W11_PROOF_2026-08-08.md:W11-BOX-3` — grep-verified count **1**; `W11-BOX-4` — count **2**.

XREF: `lean/LeanUrat/OM/RealInstanceV2.lean:htameFE` — grep-verified count **9**; the capstone hypothesis this note explicitly does not touch.

**NON-IMPORT (explicit):** `htameFE` untouched; no `n ≥ 3` window symmetry claimed; the lift-convention member-set seam not consumed; no quartic drainage/partition claim exists.

**TEETH:** W12-PIN (md5-pinned imports) and the W12-L1X seam check.

---

## 3. Consumption tables

### 3.1 Verified import/XREF designations

Every designation below was checked with fixed-string `grep -cF` in the named target file (template rule 2).

| # | Target and designation | Count | Material consumed by W12 §§1–1271 |
|---:|---|---:|---|
| 1 | `W11_PROOF_2026-08-08.md:THEOREM W-11` | 3 | The n = 2 menu, drainage law, and the reduction's unconditional firing |
| 2 | `W11_PROOF_2026-08-08.md:S2.3` | 8 | The refinement measure-isomorphism (W12-L0's induction step) |
| 3 | `W11_PROOF_2026-08-08.md:S4.3` | 10 | The stated general-n program (P1)/(P2)/(P3) |
| 4 | `W11_PROOF_2026-08-08.md:SPLIT-TAIL` | 21 | The proved DBL-side tail certification; the (A2)-routed boundary family |
| 5 | `W11_PROOF_2026-08-08.md:W11-BOX-3` | 1 | Reimplementation fence inherited |
| 6 | `W11_PROOF_2026-08-08.md:W11-BOX-4` | 2 | Oracle-coverage fence inherited |
| 7 | `W10_PROOF_2026-08-08.md:THEOREM W-10` | 2 | The digit-calculus template; the (2,1,1) cross-check |
| 8 | `W10_PROOF_2026-08-08.md:W10-BOX-1` | 1 | The general-order W-10 box, declared untouched |
| 9 | `W10_PROOF_2026-08-08.md:W10-BOX-3` | 1 | Reimplementation fence inherited |
| 10 | `W10_PROOF_2026-08-08.md:W10-BOX-4` | 1 | Oracle-coverage fence inherited |
| 11 | `JD0_PROOF_2026-08-08.md:LEMMA J-D0` | 4 | Count-gauge-blindness FRAME (shape-only well-posedness) |
| 12 | `GRTJC_PROOF_2026-08-08.md:JC-PSIKER` | 19 | `(H-a)` composite-stage warrant |
| 13 | `GRTJC_PROOF_2026-08-08.md:JC-LOAD` | 31 | `(H-a)` composite-stage warrant |
| 14 | `GRTJB_PROOF_2026-08-08.md:JB-VTX` | 77 | `(H-b)` membership face; the engine tie in BOX-5 |
| 15 | `GRTJB_PROOF_2026-08-08.md:JB-DEV` | 63 | `(H-b)` membership face |
| 16 | `GRTW2_PROOF_2026-08-08.md:W2-OPEN-2` | 60 | The surviving open weld surface in §S5 |
| 17 | `GRTW2_PROOF_2026-08-08.md:OPEN2ATTACK` | 5 | Its narrowing verdict |
| 18 | `GRTW2_PROOF_2026-08-08.md:Σ-LAW` | 14 | The residue `(H-c)` and §S5 are conditional on |
| 19 | `WELDMASTER_2026-08-08.md:WELD-M-PKG` | 5 | The WELDMASTER member of the six-note weld list |
| 20 | `DULEMMA_PROOF_2026-08-08.md:DULEMMA` | 1 | Explicitly NOT consumed by any count law |
| 21 | `HEX3_PROOF_2026-08-08.md:THEOREM HEX3.A` | 11 | The exact conservative law (rejected-parse price; BOX-3 discharge) |
| 22 | `HEX3_PROOF_2026-08-08.md:HEX3-BOX-1` | 11 | The still-open tail-σ-certification lemma |
| 23 | `HEX3_PROOF_2026-08-08.md:COROLLARY HEX3.C` | 8 | The characteristic-independence corollary |
| 24 | `HMENU3_PROOF_2026-08-08.md:THEOREM HM3.C` | 10 | The n = 3 σ-labeling supplier (with its inherited phrasing defect) |
| 25 | `HMENU3_PROOF_2026-08-08.md:COROLLARY HM3.D` | 11 | The n = 3 firing of W-12.D |
| 26 | `GENH4_PROOF_2026-08-08.md:THEOREM GENH4.C` | 9 | The n = 4 σ-labeling supplier |
| 27 | `GENHN_PROOF_2026-08-08.md:THEOREM GENHN.C` | 11 | The n = 5 σ-labeling supplier |
| 28 | `GENHN_PROOF_2026-08-08.md:[GENHN-HE(μ ≥ 3)]` | 7 | The openly-unsupplied n ≥ 6 case |
| 29 | `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:the faithfulness handoff (J-D1)` | 1 | The blueprint's W-12 row, quoted verbatim |
| 30 | `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md:(J-D1) THE FAITHFULNESS HANDOFF` | 1 | The §S2.4 statement quoted verbatim in §S5 |
| 31 | `docs/in-progress/WELD_SYNTHESIS_2026-08-05.md:(ii) J-D composition plan: BLUEPRINT ROUTE` | 1 | The cited `§4(ii)` provenance |
| 32 | `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md:erratum` | 54 | The ledger-side erratum convention for the `[r1]` display fix |
| 33 | `lean/LeanUrat/OM/RealInstanceV2.lean:htameFE` | 9 | The capstone hypothesis BOX-8 declares untouched |
| 34 | `lean/LeanUrat/OM/RealInstanceV2.lean:montes_unconditional_exhaustive` | 5 | Named Lean tie target (S8/S9, shard 2) |
| 35 | `lean/LeanUrat/OM/RealInstanceV2.lean:hExhaust` | 5 | Named Lean tie target |
| 36 | `lean/LeanUrat/OM/OMCountV2.lean:omMenu_order0` | 1 | Named Lean tie target |

**Orthography reading notes (no invented designations).** (a) W12 writes “JB row-12”; `row-12` has count **0** in GRTJB_PROOF while `row 12` has count **9**. (b) W12 cites the blueprint as `§S3.1`; that string has count **0** there — the file's header reads `### S3.1 The twelve lemmas`, and the W-12 row is at blueprint line 302. Neither is a missing referent.

### 3.2 Reverse consumer edges: mathematical supply versus append protocol

| Consumer / supplier | Exact verified designation | Direction and supply | Mathematical status | Append/consumption-protocol status |
|---|---|---|---|---|
| HMENU3 | `THEOREM HM3.C` (10) | **Both ways.** W12 consumes HM3.C as the n = 3 σ-labeling supplier; W12 owes HMENU3 a phrasing correction | The n = 3 firing SURVIVES on the corrected disc ≠ 0 form; HM3.C's conclusion, HM3.A/B, HM3.D and all counts unchanged | **OWED AND NOT LANDED.** The correction is drafted at `lean/notes/openmath/HMENU3_annex_draft_r5.md` (file present); application “is the orchestrator's”. Verified at HEAD: `HMENU3_PROOF_2026-08-08.md` L216–219 still reads “so Ore certifies EVERY lift”. See OPEN-CALL 2 |
| HEX3 | `THEOREM HEX3.A` (11) | HEX3 **supplies** the BOX-3 annex | (hExhaust-3) discharged at composition grade; `U₃^σ ≤ U₃^conv ≤ N·q^{2N−1}` | Landed as a verbatim ANNEX in shard 2's range |
| HMENU3 | `COROLLARY HM3.D` (11) | HMENU3 **supplies** the BOX-2 annex | (hMenu-3) discharged at composition grade | Landed as verbatim ANNEX 2 in shard 2's range |
| GENH4 / GENHN | `THEOREM GENH4.C` (9), `THEOREM GENHN.C` (11) | W12 consumes as (A1)-clause suppliers at n = 4, 5 | SUPPLIED — both statements already read “EVERY lift **with disc ≠ 0**” | No append owed either way (the `[r5]` sweep marks both CLEAN) |
| GENHN | `[GENHN-HE(μ ≥ 3)]` (7) | Named non-supplier at n ≥ 6 | NOT supplied, openly | Nothing owed — it is the other program's existing open box |
| Six weld notes | `JB-VTX` (77), `JC-PSIKER` (19), `Σ-LAW` (14), `WELD-M-PKG` (5) | W12 consumes only in §S5's display and as `[W12-H]` inputs | “NO S2/S3 proof depends on them” | No append landed on any weld note |
| Lean capstone | `montes_unconditional_exhaustive` (5), `hExhaust` (5), `omMenu_order0` (1) | W12 supplies transcription targets | Cited as tie TARGETS only | “no Lean is changed by this unit” |

---

## 4. NON-IMPORTS

| Fence | Explicit material not imported or not proved in lines 1–1271 |
|---|---|
| Prior drafts | The four dead composer sessions' partials are “UNTRUSTED scaffolding”, archived outside the repo; every kept statement re-derived. |
| Orders ≥ 2 | “No order-≥ 2 count law is CLAIMED here; [W12-H] is the priced route.” The `λ = (1²)` quartic row has a proved volume law and an OPEN σ-resolution. |
| General W-10 | “The general W-10 (every decided shape, every order) remains OPEN — W10-BOX-1 stands untouched.” |
| Refinement families at n ≥ 3 | “The depth-≥ 1 TRP families are not enumerated … neither species' transfer law is derived.” |
| Exact `U₃^TRP` | “The exact triple-center drainage law is not derived … EXPLORATORY grade, no closed form preregistered.” |
| n ≥ 4 drainage | “No upper bound at any grade; lower bounds only.” |
| Read-anchored σ | The read-anchored parse of σ-DECIDED is REJECTED (it makes W-12.B false at n = 3). |
| Unrestricted lift quantifier | S2.3's “in fact every lift” is STRUCK: FALSE in equal characteristic at wild decided shapes. |
| `B = 0` witnesses | The sealed `B = 0` branches of S3.2 are DELETED as inseparable in equal characteristic 2 resp. 3. |
| Lift convention | “Lift-convention independence of the member SET at deep shapes is the W-2/LIFTCORNER seam, not consumed.” |
| DULEMMA | “NOT consumed by any count law here … it appears only in this weld-state display.” |
| Weld notes in §§S2–S3 | “consumed ONLY in §S5's composition display and as [W12-H]'s named inputs; NO S2/S3 proof depends on them.” |
| IFK faces | “consumed DOWNSTREAM, owned by their own units, nothing of them owned here.” |
| Value layer | Clause (i) carries “NO value-layer hypothesis ((VD-m), (C-coll), (R-coll), (DMULT-s), PERIM-μ all absent, J-D0 frame)”. |
| FE / symmetry | “Nothing here touches `htameFE`; the n = 2 split = inert window symmetry is not asserted at n ≥ 3.” |
| Lean | “no Lean is changed by this unit.” |
| Oracle coverage | “PARI legs are mixed-characteristic only … no mixed-characteristic prime-power rows exist in the frozen kit.” |

---

## 5. Teeth inverse table

| Battery row / tooth | Guarded unit(s) | Disposition |
|---|---|---|
| W12-PIN (5 md5-pinned frozen imports) | `.46`, `.52` | Bookkeeping check (evidence class NONE per the note's own labelling) |
| W12-LVL0 (five cubic level-0 censuses + sum `q³`) | `.22`, `.09` | Executable regression |
| W12-SHAPE (all seven depth-0 TRP laws, BOTH directions, exact zeros) | `.09`, `.28`, `.29`, `.30` | Executable regression with a completeness clause (unpredicted decided key = violation) |
| W12-QRT (QRT-G2 `(1,1)`/`(2)` laws + the `(1²)` frontier volume, both directions) | `.31`, `.49` | Executable regression |
| W12-L0HIST (every history-resolved key; `Σ_H` vs the sealed W-11 predictor) | `.32`, `.33`, `.44` | Executable regression against a frozen foreign instrument |
| W12-BLOCK (Hensel product identity + fiber bijection per DBL member) | `.21`, `.34` | Executable regression |
| W12-L1X (fresh direct cubic read vs the sealed W-11 classifier, pointwise) | `.34`, `.35`, `.52` | Executable cross-implementation regression |
| W12-DRAIN3 (partition `Σ = q^{3N}`; `DBL-undecided = (q−1)q^{2N−1}`; species count `q^N`; `U₃^TRP` measured) | `.11`, `.36`, `.38`, `.45` | Executable regression; the `U₃^TRP` leg EXPLORATORY under a disclosed convention |
| W12-ORACLE (PARI σ-multiset per decided member; `disc = 0 ⟹ never decided`; 85 witness pairs) | `.27`, `.38`, `.40` | Independent-engine regression (IND); witness-pair leg scoped to 70 of 85 by `[r5]` m3 |
| Tooth W12-T-SHAPE (TRP-RAM3 law corrupted must mismatch on every cubic row) | `.28`, `.29` | Planted mutant |
| Tooth W12-T-DRAIN (DBL drainage term corrupted must mismatch) | `.11`, `.36` | Planted mutant |
| Tooth W12-T-CENSUS4 (`S_{(2)}` with the `/2` dropped must break QRT-G2) | `.24`, `.25`, `.31` | Planted mutant |
| Tooth W12-T-SIGMA (QRT-G2 `(2)` σ mis-keyed must be caught by PARI) | `.27`, `.31` | Planted mutant, IND leg |
| Pre-runner independent brute force (9 cubic + 4 quartic rows) | `.29`, `.30`, `.31` | Independent re-derivation, disclosed pre-seal |
| `[r4]` fresh separability instrument (sympy over `GF(p)[t]` and `ℤ`; p = 2,3,5,7, N = 2,3,4) | `.38`, `.39`, `.40` | Executable regression on a FRESH instrument, covering exactly what the frozen kit structurally cannot |
| `[r1]` counter-instance re-read of `w12_checks_results.json` row `(Zp,2,5)` = 4096 | `.09`, `.15` | Committed-artifact re-read |
| `[r2]` boundary-tail mass re-verified on all 23 cubic rows | `.45` | Committed-artifact re-read |
| `[r3]` HEX3.A transcription tied to all 23 committed `U₃` values, 0 mismatches | `.16` | Cross-note numerical tie |
| The degenerate one-family instance (`R_split = 1 ≠ μ_split`) | `.12`, `.17` | Signed counter-model to the sealed hypothesis set |
| S2.3's equal-characteristic-3 counter-instance (`F = y³ + b₀`, `F′ ≡ 0`) | `.18`, `.27` | Signed non-applicability |
| The runner's never-firing `assert e == 1` (PE1-verified) | `.08` | Negative executable check |

**Both-direction audit:** every row guards at least one in-range unit, and every in-range unit with a non-empty `TEETH` field appears in at least one row. Units with `TEETH: NONE` (`.01`, `.04`, `.05`, `.19`, `.20`, `.26`, `.37`, `.43`, `.48`) are headers, reconciliations, proof audits, fences or composition displays. **Zero battery-row orphans; zero toothed-unit orphans.** Out-of-range teeth not counted here: the LEMMA W12-HT machine certificate (`verification/openmath/w12_history_law_check.py`, 1,196 per-key comparisons, four teeth), homed in shard 2, which guards the corrected form of `.09`.

---

## 6. Boundary self-audit

W12 is prose-proof with named theorems (`\tag{` density 0.00), so boundaries were chosen at changes of consumer, supplier perimeter, conditionality, or executable tooth. The governing choices:

1. **The statement complex `.09`–`.14` follows the note's own clause letters** (i)/(ii)/(iii) and grade summary, with ONE deliberate split inside clause (iii): `.12` (the (A0)/(A1)/(A2) hypothesis interface) is separated from `.13` (the conclusion). This is the shard's most consequential boundary: the hypotheses are the capstone-facing conditionality vocabulary, they are what the `[r4]` strengthening and the 2026-08-12 (A1) correction act on, and they are cited independently of the conclusion by every downstream firing.
2. **Repair records are units, not annotations** (`.15`–`.20`, `.40`). Each carries a counter-instance, a price computation, or a sweep that is evidence in its own right — the `[r3]` rejected-parse price and the `[r4]` degenerate instance are the two places where the note proves that its own definitions are load-bearing.
3. **The FIRING CHECK (`.18`) and the seven-family table (`.28`) are emitted as tables**, per template rule 5. Prosifying either would destroy the per-degree / per-family addressability the teeth table needs.
4. **§S2 is split along its proof seams** (`.21` product structure / `.22` census / `.23` digit calculus / `.24` branch count + sweep / `.25` censuses / `.26` cell factorization / `.27` Ore leaves) because LEMMA W12-HT (shard 2) re-uses precisely `.23`, `.24` and `.21` as its steps 1, 1 and 3 — the seams are the reuse boundaries.
5. **`.38`/`.39`/`.40` split LEMMA W12-S3.2 into statement+construction / separability warrant / repair record**, because the statement is byte-unchanged while the construction was replaced and the warrant is new: merging them would hide that a CRITICAL proof-level repair left the statement fixed.
6. **§S3.4 is split into Step 1 (`.42`) and Steps 2–4 (`.43`)** because only Step 1 is touched by the 2026-08-12 (A1) correction, and only Step 4 consumes the σ-labeling clause.
7. **The eight boxes become four units** (`.49` BOX-1 alone, because it is `[W12-H]`'s box and the one the dated correction repairs; `.50` BOX-2/3/4, the drainage family, discharged as a group by the two annexes; `.51` BOX-7 alone, because it is the definitional σ anchor; `.52` BOX-5/6/8, the instrument/coverage/no-claim fences). Grouping by *disposition*, not by number.

Merges deliberately NOT made: `.45` (conditionality at n ≥ 3) is kept apart from `.13` (the conclusion) because the annexes discharge `.45`'s legs without touching `.13`; `.47` (`[W12-H]`) is kept apart from `.49` (BOX-1) even though they name the same object, because one is the hypothesis list and the other is the honest-box record that the dated correction repairs.

---

## 7. SHARD NOTES

- **Cross-shard supersessions applied (resolution rules 3–7):** the post-PE7 acceptance record (status → ACCEPTED 2/2, note FROZEN); the 2026-08-12 κ(T) level-0 orbit correction (→ `.09`); the 2026-08-12 obstruction + the LEMMA W12-HT discharge (→ `.09`'s effective law `(HT-global)`, and `.14`'s coverage claim); the 2026-08-12 (A1) rationality correction (→ `.12`, `.42`, `.44`); the 2026-08-12 BOX-1 dependency-range correction (→ `.49`). In-range, the `[r1]`–`[r5]` brackets are applied at their own sites.
- **Range-edge audit:** line 1270 closes W12-BOX-8; line 1271 is blank and line 1272 opens `## S7. THE SEALED BATTERY`. **No source unit is cut at the edge.** The battery's family definitions, predictions and verdict are homed in shard 2; this shard cites individual battery rows only inside `TEETH` fields, using the row names S7 defines.
- **Outside-HOME material not inventoried:** §S7–§S10, the two verbatim annexes, the `[r5]` NOTICE + m2 sweep, the arcs, the PE6/PE7 dated records, and the 2026-08-12 adjudication/obstruction/corrections/discharge are NOT emitted here. Shard 2 owns them.
- **Protocol versus absorption:** the two received annexes are recorded as discharges of this note's boxes at *composition grade*; the one owed outward correction (HMENU3) is recorded as **not landed** and verified so at HEAD (OPEN-CALL 2).
- **Numbering:** temporary IDs `EFF.W12.s1of2.01`–`.52`, to be reconciled with shard 2's at the merge run.

---

## 8. Self-audit and OPEN-CALLS

### OPEN-CALL 1 — which text is THEOREM W-12.A's canonical statement in the effective spec

Three texts are in play for the same theorem: (a) the S1 display as repaired by `[r1]` (`.09`, in range); (b) that display with the level-0 orbit factor `κ(T)` (2026-08-12 correction); (c) `(HT-global)`, the history-resolved law of LEMMA W12-HT, which the discharge names as “its controlling formula”, with (b) as “the depth-zero specialization”. I have compiled (c) as effective, per the discharge's own words, and carried (a) as the depth-zero case. **The call is that the discharge's own ledger line does not declare itself final:** *“Ledger: row 12 → the obstruction is DISCHARGED; a final transcription-confirmation rides the next queue.”* — and the three A1-derived corrections carry *“the three corrections await sol discharge-confirmation”*. Whether the effective spec should present W-12.A as `(HT-global)` (my reading) or hold it at the κ(T)-corrected depth-zero display pending confirmation is a DAG/status decision above the compiler. **Reading note (external, not an edit):** `docs/SOL_CERTIFICATION_LEDGER_2026-08-12.md` row 12 records W-12 as **CERTIFIED 2026-08-12** — “A1 repairs discharged (D2a 3/3); the obstruction discharged by LEMMA W12-HT (machine certificate GREEN; transcription confirmed at TC1) — W-12.A at full order-1 coverage”, i.e. the ledger says both confirmations have since landed.

### OPEN-CALL 2 — the owed HMENU3 quantifier correction is drafted but NOT applied

The `[r5]` FIRING CHECK rewording (`.18`) and the `[r5]` NOTICE (shard 2) record that HMENU3's THEOREM HM3.C carries the same unrestricted “EVERY lift” over-claim that `[r4]` m2 struck from this note's S2.3, that the defect is INHERITED from the shared S2.3-era phrasing, and that the corrected clause is the disc ≠ 0 form. The correction is drafted at `lean/notes/openmath/HMENU3_annex_draft_r5.md` (**file present, verified**), with application declared “the orchestrator's”. **Verified at HEAD:** `HMENU3_PROOF_2026-08-08.md` lines 216–219 still read *“so Ore certifies EVERY lift (W-12 S2.3 at the terminal frame; W12-L1(c) transports the DBL certificates); σ_F = the leaf …”* — the annex has **not** been applied. Nothing mathematical turns on it (the n = 3 firing survives on the corrected form, and no count moves), but the corpus currently contains a statement W-12 has diagnosed as false in equal characteristic 3, and W-12's own FIRING CHECK cites that statement as its n = 3 supplier. **Decision needed:** land the drafted annex, or record the obligation in the spec's hypothesis-closure ledger.

### OPEN-CALL 3 — `(A0)` retained-but-redundant: keep or retire in the effective interface

Post-`[r4]`/`[r5]`, `(A0)` is “the same statement in its well-posedness phrasing, i.e. redundant-but-retained: it is not the load-bearing warrant at either bound”. The note keeps it as a hypothesis of W-12.D. A downstream formalization must choose: transcribe (A0) as a hypothesis (faithful to the note, but a provable-from-(A1) redundancy in the interface) or drop it (leaner, but a statement change). I compile it as retained. **This is a statement-shape decision for the blueprint, flagged rather than taken.**

### Recorded source defects and orthography (flagged, not silently repaired)

1. **`.05`, `.06`:** W12 cites the blueprint as `§S3.1` (count **0**; the file's header is `### S3.1 The twelve lemmas`) and GRTJB's `row-12` (count **0**; the file writes `row 12`, count **9**). Both referents are unique and verified; the orthography is recorded, not corrected.
2. **`.49`:** W12-BOX-1's `(H-a)–(H-d)` contradicted §S4.2's own five-input list; corrected out of range and applied here. The note's own verification records “no prior dated append correcting it”.
3. **`.02`:** the archived draft's spurious `(q^d−1)`-per-interior-vertex factor is recorded as a known-wrong alternative to `.24`'s sweep result, useful to a cross-reader as the exact shape of the error the sweep excludes.

### Fidelity audit

- Every CANONICAL STATEMENT is verbatim quotation or explicitly marked `[ASSEMBLED]`; no inverse, sign, quantifier, index, or implication direction was altered. Struck text is reproduced as struck (`~~…~~`) and never carried as effective. Truncations inside quotations are marked `…` (used once, inside `.18`'s n = 3 table cell, where the elided argument is quoted in full at `.27`).
- Two source tables (the FIRING CHECK, the seven TRP families) are emitted as tables and flagged `[TABLE]`; the universal censuses are emitted as a `[TABLE]` unit preserving the source's display block. No source table was prosified.
- All 36 XREF designations carry fixed-string counts ≥ 1, recorded inline and in §3.1. Two orthography mismatches are recorded as reading notes with the verified form; no zero-count string is emitted as an XREF.
- Three predicates are kept distinct throughout: **grade** (ACCEPTED 2/2, from the acceptance record), **mathematical conditionality** (`[W12-H]`, `(hMenu-3)`, `(hExhaust-3)`, the (A0)/(A1)/(A2) interface), and **append protocol** (two annexes received; one correction owed outward and not landed).
- The three 2026-08-12 corrections and the obstruction/discharge pair are applied as supersessions with their target spans quoted, per the note's own convention.
- CITE-SCOPE retargets ([GN15] Thm 2.3 for the Ore/GMN cites at `.09`, `.27`, `.46`, `.47`) are recorded as reading notes at their units and are **not** applied to the compiled text, per the charge.

EFF-W12-s1of2 COMPILED: 52 statements / 36 xrefs verified / 3 open calls



