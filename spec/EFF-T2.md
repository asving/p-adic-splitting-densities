# EFF-T2 — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

## 1. Merge header

**Source note:** `lean/notes/openmath/T2_SIGMA_LADDER_MASTER_2026-08-12.md` (4507 lines).

**HEAD blob hash:** `9cc9063028c598a90cd98a022ac07694e6dc8a2a` — quoted identically by all six
source shards' headers, and independently reconfirmed at merge time by a fresh
`git hash-object lean/notes/openmath/T2_SIGMA_LADDER_MASTER_2026-08-12.md`, which returned
the same value. The merge charge flagged that shard 1 was codex-compiled before later
commits touched the repo and that a hash drift was therefore possible; none was found —
`git status --porcelain` on the source note is empty at merge time — and the merge
proceeds without qualification on this point.

**Compilation context:** `spec/EFF_TEMPLATE_v2.md`.

**Merged from:** `spec/EFF-T2-s1of6.md` (source lines 1–2241, 44 statements, 37 xrefs, 0
open calls, **codex-compiled** — no `COMPILED-BY` flag in its own header), `spec/EFF-T2-s2of6.md`
(2242–2925, 13 statements, 37 xrefs, 0 open calls), `spec/EFF-T2-s3of6.md` (2926–3568, 9
statements, 44 xrefs, 0 open calls), `spec/EFF-T2-s4of6.md` (3569–4018, 15 statements, 33
xrefs, 0 open calls), `spec/EFF-T2-s5of6.md` (4019–4442, 15 statements, 30 xrefs, 0 open
calls), `spec/EFF-T2-s6of6.md` (4443–4507, 9 statements, 12 xrefs, 0 open calls). Shards
2–6 each carry the header flag **"COMPILED-BY: opus (2026-08-14, Asvin-authorized
substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset)."**; shard 1 carries
no such line, being the codex-compiled shard of this run. **This merge therefore carries
forward the mixed-provenance flag CODEX CROSS-READ OWED for 5 of its 6 source shards**
(shards 2–6; shard 1 is codex-compiled and does not owe a codex cross-read on its own
account). This file **supersedes all six shards as the citable unit for downstream
consumption.** The shard files are NOT deleted — they remain the run-of-record trace of
the sharded compilation, and shards 2–6 in particular carry the process/landmark
verification ledgers (source-line and master-internal-landmark grep re-runs) that this
merge summarizes rather than fully re-transcribes (§4) — but any consumer citing
`EFF.T2.*` from this point on cites the contiguous IDs below, not the shard-local
`EFF.T2.sKof6.NN` IDs.

### SHARD-MAP (contiguous renumbering)

Every shard's own local numbering is already contiguous from 1 in source order, and no
unit is reordered relative to its shard's own sequence or to another shard's. The
renumbering is therefore a pure per-shard additive offset — new ID = old local ID +
offset — verified exhaustively at merge time by machine (every `EFF.T2.sKof6.NN`
occurrence, every `shard N` + unit-list cross-reference, and every same-shard bare `.NN`
self-reference in every table of every shard, rewritten and re-checked against the
expected per-shard range; zero out-of-range results after correction of several
apostrophe-possessive and capitalized-`Shard N` edge cases the mechanical sweep first
missed and a second sweep caught).

| Shard | Old local range | Offset | New contiguous range | Statement count |
|---|---|---:|---|---:|
| `s1of6` | `EFF.T2.s1of6.01`–`.44` | +0 | `EFF.T2.01`–`.44` | 44 |
| `s2of6` | `EFF.T2.s2of6.01`–`.13` | +44 | `EFF.T2.45`–`.57` | 13 |
| `s3of6` | `EFF.T2.s3of6.01`–`.09` | +57 | `EFF.T2.58`–`.66` | 9 |
| `s4of6` | `EFF.T2.s4of6.01`–`.15` | +66 | `EFF.T2.67`–`.81` | 15 |
| `s5of6` | `EFF.T2.s5of6.01`–`.15` | +81 | `EFF.T2.82`–`.96` | 15 |
| `s6of6` | `EFF.T2.s6of6.01`–`.09` | +96 | `EFF.T2.97`–`.105` | 9 |

**Total: 105 statements.** Every `EFF.T2.sKof6.NN` occurrence — full-form citations, the
`shard N` + bare-`.NN` cross-references used throughout shards 2–6's process narrative,
and the bare same-shard self-references inside each shard's own TEETH/ledger/audit
tables — has been rewritten throughout the merged text below to the new contiguous ID
under this map, so no cross-reference inside any `DERIVATION`, `CONDITIONALITY`,
`RESOLUTION TRACE`, `TEETH`, ledger, or audit field still points at a retired
shard-local ID.

### Multi-leg exception units (9, flagged) — routed with a residual local emission

Merge rule 2 (§ Resolution rules, item 8) is the same one shard 1 of T1 used: a directive
whose destination is an earlier shard's base section is routed there and not re-emitted
— **except** when the directive is a multi-leg derivation with quoted source legs that
its shard-1 destination unit compresses to a single clause. That "exception (ii)" is
used at exactly **nine** units across shards 3–5, and each is verified below to attach to
exactly one shard-1 destination's `DERIVATION` field, as an extension of it, not a
parallel statement:

| Exception unit (new ID) | Old shard-local ID | Attaches to (shard-1 destination) | What it supplies that the destination compresses |
|---|---|---|---|
| `EFF.T2.59` | `s3of6.02` | `EFF.T2.19` | The master-side derivation of `(REF-HT)`: `(RISE)`⇒`(HT)` from `(SIDE-COUNT)`+`(SLOT-V)`+`(LIFT)` |
| `EFF.T2.60` | `s3of6.03` | `EFF.T2.19` | The per-instance `(RISE)` discharge map (r8 state; superseded in part by `EFF.T2.70`/`.71`, see below) |
| `EFF.T2.61` | `s3of6.04` | `EFF.T2.25` | The S1.8C `(MP1′)` adjudication: four pinned legs, the (i)–(vii) inventory, two reading directives |
| `EFF.T2.62` | `s3of6.05` | `EFF.T2.24` | S1.8B's composed-key entry composition (the one-clause LEMMA HE7-12(d) fold) |
| `EFF.T2.69` | `s4of6.03` | `EFF.T2.19` | The HE6 leg of the level-one `(RISE)` discharge (citation-completeness fix) |
| `EFF.T2.70` | `s4of6.04` | `EFF.T2.20` | The `ι_θ=id` argument and the print/coherent seam computation for `(IDX-TWIST)` |
| `EFF.T2.71` | `s4of6.05` | `EFF.T2.19` | The digit-forcing derivation (supersedes the r8-state passage quoted at `EFF.T2.60`) |
| `EFF.T2.72` | `s4of6.06` | `EFF.T2.20` | The bijection/covering argument and the two `(IDX-TWIST)` qualifiers (lift-choice; covering-height) |
| `EFF.T2.90` | `s5of6.09` | `EFF.T2.24` | The master-side degree-bound derivation replacing the imported `HETOW-KEY-BRIDGE` conjunct |

No shard-1 statement, display, clause, or instance box is re-emitted by any of these nine
units; each supplies argumentation its named destination's own `DERIVATION` field states
it compresses to one clause (verified against each shard's own "Merge flags" note, §7).

### Three cross-shard (non-shard-1) supersessions — verified to land exactly once

Per the merge charge, three amendments are physically drafted in one shard's line range
but amend an already-compiled EARLIER shard's unit (not shard 1's base text). Each is
confirmed below to leave exactly one effective statement at its target — the amending
shard's own text already recorded the replacement, and the target shard's unit already
recorded (in its own `CONDITIONALITY`) that it is superseded and where the effective form
lives, so no double-render and no stale parallel text survives the merge:

| Supersession | Physically drafted at | Amends | Verified disposition |
|---|---|---|---|
| r6 repair 6(b) → `EFF.T2.56` | `EFF.T2.62`'s round (old shard 3, physically lines 3213–3241) | `EFF.T2.56` (old `s2of6.12`, the r5 per-record pin-discipline justification map) | `EFF.T2.56`'s own `CONDITIONALITY` already quotes the replacement `HE7-PERT-TRANSPORT` justification sentence in full as the effective text; the superseded r5 wording is named as historical only. Lands once. |
| r9 repair 1(a)–(b) → `EFF.T2.60` | The r9 repair 1 round (old shard 4, physically lines 3689–3739; sub-parts compiled as `EFF.T2.70`/`.71`) | `EFF.T2.60` (old `s3of6.03`, the r8-state `(RISE)` discharge map) | `EFF.T2.60`'s own `CONDITIONALITY` names the two superseded passages and points to `EFF.T2.70` (the step sentence, replaced by r9 repair 1(a)'s `(IDX-TWIST)` derivation) and `EFF.T2.71` (the height-ground passage, replaced by r9 repair 1(b)'s height-and-digit derivation) for the effective form; what it retains unchanged — the assembly order, the level-two bullet, the non-circularity statement — is stated explicitly. Lands once, split correctly between the two units. |
| r12 repair 4(d) → `EFF.T2.71` | The r12 repair 4 round (old shard 5, physically lines 4387–4423; compiled as `EFF.T2.94`) | `EFF.T2.71` (old `s4of6.05`, the lift-freedom rider's `h(E)<λ` step) | `EFF.T2.71`'s own `CONDITIONALITY` states the completing clause was inserted downstream and quotes it inline at its effective position, flagged in-text as "[r12 repair 4(d), homed in shard 5]" (i.e. `EFF.T2.94`); no separate stale version of the incomplete rider survives. Lands once. |

### Header unification and blob-hash check

All six shards' front matter quotes the same governing status line:

> "**Status:** ACCEPTED note of record — the hostile arc is closed at 2/2 and the accepted
> text is byte-frozen; THE ACCEPTANCE RECORD AT THE END OF THIS NOTE GOVERNS (before
> acceptance the governing sections were the highest-numbered r-section and the post-pass
> rider blocks); the pass record, the folded riders, the pin-sweep result, the counter
> state, the four standing conditionalities, and the `(GRADE)` cap that still holds the
> S3.1/S3.2 composed instances at HE3's HEAD grade are recorded in that block."

and the same acceptance-record text of record:

> "The accepted T2 v2 of record is the effective text as of r12, plus the first post-pass
> rider block, plus the second post-pass rider block, plus post-pass rider 3 above, and
> consumers cite it as exactly that."

All six cite the **same HEAD blob hash**, `9cc9063028c598a90cd98a022ac07694e6dc8a2a`. No
divergence was found — this was the STOP condition the merge charge specified; it did
not trigger (see the header field above for the independent re-confirmation).

### Scope of record — mandatory two-predicate split (unified from all six shards)

**A. Mathematical absorption/supply set.** T2 is not an absorption note; per shard 1's
own scope declaration (`EFF.T2.01`) and reaffirmed unchanged in every later shard:

> "This note states and proves one mathematical master theorem, HE7.A, over the original
> complete DVR \(O\). It records five source instances:
> \[
> \mathrm{HE3.A},\qquad \mathrm{HE6},\qquad \mathrm{HE7{+}HE6R1},\qquad \mathrm{HETOW},
> \qquad \mathrm{GENTOW4}.
> \]"

Nothing in shards 2–6 adds to this supply set (each says so explicitly in its own scope
split); what they supply is the evidential/process apparatus underneath it — pin
adjudications, byte-exact delimiter verification, the per-instance discharge maps for
`(SEC-RANK)` and `(RISE)`, and the round-level status record culminating in shard 6's
acceptance block (`EFF.T2.97`–`.105`).

**B. Consumption/append-protocol scope**, stated identically in substance across all six
shard headers and again, governing, in the acceptance record proper (`EFF.T2.105`):

> "Consumption checks ride the next queue: re-price every downstream note that consumes
> T2 v2 under `(GRADE)` with \(g_{\mathrm{master}}=2/2\) — subject to the HE3 cap above —
> and re-run the standing S7 consumption check at the consuming sites."

These two predicates are never conflated below: the master theorem `HE7.A` and boundary
theorem `T2.KEY-BOUNDARY` (`EFF.T2.31`–`.32`) plus the five instance records
(`EFF.T2.33`–`.37`) are what T2 supplies mathematically, at grade 2/2 subject to the
open `(LB1)`/`(MP1)` obligations and the HE3 supplier cap; the acceptance record
(`EFF.T2.97`–`.104`) certifies that composed text as accepted; and downstream
consumption/re-pricing (`EFF.T2.105`) remains **outstanding, with nothing discharged
by any unit of any shard**.

### Resolution rules applied (merged; each shard's own rule-list is a restriction of this
one to its HOME range, so no rule is dropped, only consolidated)

1. The acceptance record (`EFF.T2.97`–`.105`) governs status over every earlier
   counter state, pin count, or obligation-set snapshot recorded in r1–r12 or the three
   post-pass rider blocks; those earlier states are historical, recorded because the
   arc's own audit trail depends on them, never cited as effective.
2. The accepted text is r1–r12's textual replacements/insertions/read-as
   rules/span re-declarations applied in chronology (later directives govern earlier
   text), plus the three post-pass rider blocks, plus the final acceptance fold. This is
   the text every statement below resolves against.
3. The two standing OPEN OBLIGATIONS are exactly `(LB1)` (level-one clause-4 block
   construction) and `(MP1)` (a level-one clause-5 peel at a **recentered** key); both
   fence reads and both are named at `EFF.T2.18` and `EFF.T2.23`, fenced again through
   §5 and §4.2 of the base text, and reaffirmed verbatim at `EFF.T2.101`.
4. `(SEC-RANK)` and `(RISE)` are CARRIER HYPOTHESES, not obligations — they fence no
   read, and any instance unable to supply them simply does not instantiate `HE7.A`. Their
   per-instance discharge maps are `EFF.T2.52` (`(SEC-RANK)`) and `EFF.T2.60`+`.69`–`.72`
   (`(RISE)`, in its final r9/r10-corrected form).
5. `(MP1′)` is NOT a fifth standing conditionality: it is RETIRED at old-`r6 repair 2`
   (`EFF.T2.61`) and its content is discharged in the resulting S1.8C
   (`EFF.T2.25`) from four pins already on both level-one records' Source-pin lines. It
   denotes a consequence of the pins, never an open obligation, at every point after its
   retirement.
6. `(REF-HT)` = stipulated `(RISE)` plus derived `(HT)`, \(k=\lambda\); the derivation
   direction is load-bearing (RISE ⇒ HT, never the reverse) and is what makes the r9-state
   per-instance discharge non-circular (`EFF.T2.59`–`.60`, corrected at `.69`–`.72`).
7. `(IDX-TWIST)` is a derived identity of the level-one instance, never a clause of the
   theorem, read with two qualifiers installed after its r9 introduction: exact equality
   holds only at the `(LIFT)`-compatible lift choice; at an arbitrary permitted choice it
   holds modulo increments of height \(>\kappa\); and its covering direction is stated at
   \(\kappa>D'h\) (DEFINITION HE6-1's own standing hypothesis), not at mere fullness
   (`EFF.T2.20`, `.70`, `.72`).
8. HOME is determined by an edit's destination section, not its physical shard-line
   position. A directive physically drafted in one shard's range that inserts, replaces,
   or supersedes material whose destination is an earlier shard's section resolves that
   earlier shard's unit and is not re-emitted as a separate statement — **except** the
   nine multi-leg-derivation exceptions named above, which attach as `DERIVATION`
   extensions of their named shard-1 destination rather than as parallel statements. The
   three genuine cross-shard (non-shard-1) supersessions named above are each verified to
   land at exactly one place.
9. The final pin inventory closes at **37 pins**, taxonomy \(20+4+13\), with **zero**
   synthetic markers and **zero** source edits, and a cured-consumption census of **ten**
   — set finally at old-r12/acceptance (`EFF.T2.95`–`.96`, `.101`) and unchanged by every
   later unit. The final five per-record Source-pin lines are composed at `EFF.T2.96`
   and are the effective supplier list attached to `EFF.T2.33`–`.37`.
10. `(GRADE)`(I) = \(\min(g_{\mathrm{master}},g_{\mathrm{carrier}},g_{\mathrm{frame}},
    g_{\mathrm{local}})\) is unchanged by acceptance; acceptance moves only
    \(g_{\mathrm{master}}: 0/2\to2/2\). HE3's supplied HEAD grade (attempt \(0/2\), clean
    count \(1/2\)) still caps `EFF.T2.33`–`.34` (the composite HE3+HE6 level-one
    instances) and any level-two chain that consumes an HE3 pin through S1.8C.
    **Acceptance of this note does not make those composed instances \(2/2\)**
    (`EFF.T2.38`, `.103`).
11. From the acceptance record forward the note is **byte-frozen**; later work may only
    append dated records below it, never rewrite the accepted text (`EFF.T2.104`). No
    unit of any shard reports a rewrite; the only in-place edit on record is the dateless
    front-matter status-line refresh the acceptance record itself licenses.

### Quotation and table discipline

Unchanged from all six shards: canonical statements are verbatim source quotations or
explicitly marked `[ASSEMBLED]`; source lines quoted for verification are reproduced
byte-exactly, including any leading `> ` or leading spaces; every source table is
transcribed as a table and marked `[TABLE]`; compiler-authored ledgers (XREF tables,
consumption ledgers, TEETH inverse tables, routing audits) are marked
`[TABLE — compiler ledger]` and are not source statement units.

---

## 2. NON-IMPORTS (consolidated from all six shards; dedup marked)

`[TABLE — consolidated from shard 1 §5, shard 2 §5, shard 3 §5, shard 4 §5, shard 5 §5,
shard 6 §5]`

| Fence | Effective prohibition | Source |
|---|---|---|
| Quotient-DVR migration | Do not replace the original coefficient DVR \(O\) by a stage order, integral closure, or \(O[x]/(\Phi)\). | s1 |
| Current-key irreducibility | Do not assume \(\Phi\), a test key, or a recentered key irreducible. Only residual labels and emitted certified boundary factors may require irreducibility. | s1 |
| Weak key-freeness | Do not replace `(KEY-FREE)` by \(\Phi\nmid F\), nor infer a single-key peel from a reducible boundary. | s1 |
| All-height lifts | Do not infer lift surjectivity outside the finite occupied full-height domain `(OCC)`. | s1 |
| Closure identification | Do not identify valued points in \(\overline K_0\) with residual embeddings in \(\overline k\). | s1 |
| Trivial cocycle | Do not replace the normalizer cocycle or its deeper residual-letter monomial by \(1\). | s1 |
| Raw/coherent equality | Do not identify raw and coherent residual coefficient strings; only the stated frame transformation and invariant factor data pass between them. | s1 |
| Silent origin deletion | Do not discard the \(Y^\nu\) factor in `(ORIGIN)` before recording it. | s1 |
| Parent multiplicity | Do not set block-owned \(k_{\lambda,r'}\) equal to the parent residual multiplicity \(m_{\lambda,r'}\). | s1 |
| Rank-only recursion | Do not infer termination correctness from well-founded descent without root preservation, partition, and polynomial-product transport. | s1 |
| GENTOW4 count laws | Do not import the mixed-multiplicity count tie, partial-side budgets, density laws, or whole-polynomial monicity/length transfer. | s1 |
| Fence erasure | Do not treat acceptance as discharging `(LB1)`, `(MP1)`, the HE3 cap, or downstream consumption checks. | s1 |
| Formal-artifact claim | Do not infer that a Lean signature, record, instance, or completed formal gate is present. | s1 |
| Wording-based pin resolution | Do not resolve a pin from its description when that description matches more than one source unit; adjudicate by consumption and record the declinations. | s2 |
| Declination over-reach | Do not read "unit X is declined as the supplier of consumption C" as "the master consumes nothing from X". `HE6-LIFT-1L` is declined for the slot law and pinned for \(q(k)\). | s2 |
| Slot law from a residual-assembly unit | Do not take a per-\(A\) slot law or the \(\eta^{-q}\) conversion from HE6's §S1 ϖ-normalizer CONVENTION; it states neither. | s2 |
| Reachability as evaluation | Do not take the evaluation of a given \(A\) from `HE6-LIFT-1L`, which describes the reachable residue *set*. | s2 |
| Pre-discharged pin gate | Do not infer that a quoted delimiter pair discharges S0.2 conditions 1 and 4, nor that a single quoted delimiter discharges condition 3. | s2 |
| `(SEC-RANK)` as a master theorem | Do not treat `(SEC-RANK)` as derived: the master reproduces no instance's argument, and an instance that cannot supply it does not instantiate HE7.A. | s2 |
| HE7-8 at a foreign key | Do not instantiate LEMMA HE7-8 at the composed key \(\Phi_2\); its hypothesis names the chain's base key. Route to `HETOW-A`(ii) / `GENTOW-4-A`(iii). | s2 |
| HE7-8 `[r3]` as a suite discharge | Do not read HE7-8's `[r3]` interleaving clause as supplying any item of the `(MID-PEEL)` input suite; it supplies occurrence and mass drop only. | s2 |
| Superseded parenthetical | Do not consume GENTOW-4.A(ii)'s "top coefficient NOT monic" parenthetical; the 2026-08-10 TOWERRAT2-C correction governs. | s2 |
| Sweep completeness | Do not read any recorded consumption-sweep enumeration as complete; each is recorded for the gate to re-run, not asserted final. | s2, s4, s5 |
| `(HT)` without `(RISE)` | Do not read `(REF-HT)` as a single stipulation or as a derived fact: `(HT)` is derived **from** `(RISE)`, and `(RISE)` is assumed. | s3 |
| `(RISE)` from the master | Do not derive `(RISE)` from the "new valid development" sentence, from `(SEC-RANK)`, or from an unnamed assertion "hypothesised by HE7.A". All three supports are withdrawn. | s3 |
| `(RISE)` as an obligation | Do not enter `(RISE)` in the open-obligation ledger: it fences no read and both instance families discharge it from pins already on their lines. | s3 |
| Textual carriage of the height | Do not treat `HE7_PROOF`:924/925 as legs that carry the refinement height; they are hypothesis-side corroboration of the configuration. | s3 |
| LEMMA HE3-2 | Do not consume LEMMA HE3-2 or its clause (b): its unit lies inside no span of `(PINS)`. In particular do not assert that its recentered key exists only at an integer slope. | s3 |
| Circular level-one discharge | Do not identify HE3's \(\Phi''\) with the master's \(\Phi_{\mathrm{new}}\) by importing `(HT)`; the instance's step must be exhibited first, at the index DEFINITION HE6-1's recipe fixes. | s3 |
| `(MP1′)` as a condition | Do not treat `(MP1′)` as an obligation or as a condition a state may carry; it is retired and denotes a consequence of the pins. | s3 |
| Frame inventory as demand list | Do not read S1.8C's (i)–(vii) as everything S1.2–S1.7 demand; they are demands on the RECORDS and reach \(\Phi''\) only through (vii). | s3 |
| HE3-only transport | Do not read the S1.8C transport as an HE3-only discharge: the record transported is the composite HE3+HE6 discharge, at whatever conditionality it carries at \(\Phi'\). | s3 |
| Sibling classes at the recentered key | Do not read an above-\(\lambda\) block's labels at \(\Phi''\); only the refined sub-block travels. | s3 |
| HE6 caveat (product-\(\ge2\) routing) | Do not consume anything behind `HE6-PROOF`'s §S7 caveat (an \(\ell\ge2\) side with a repeated residual factor); that configuration is the product-\(\ge2\) branch. | s3, s4 |
| S1.8B at \(\Phi_2\) | Do not apply S1.8B at the composed key directly; entry costs the one displayed composition, after which the chain is read at \(\Psi_{\kappa_2,\widetilde r}\). | s3 |
| Print label as digit | Do not read DEFINITION HE6-1's family index as this master's coherent digit; they differ by the fixed unit \(\eta^{q(\kappa)}\), which nothing forces to be \(1\). | s4 |
| Index-name matching | Do not match family members to recenterings at equal index names; match them through `(IDX-TWIST)`. | s4 |
| `(IDX-TWIST)` as a theorem clause | Do not treat `(IDX-TWIST)` as a hypothesis or conclusion of HE7.A; it is a derived identity of the level-one instance. | s4 |
| Arbitrary-lift equality | Do not read `(IDX-TWIST)` as a polynomial identity at an arbitrary permitted lift; at an arbitrary choice it holds modulo increments of height \(>\kappa\). | s4 |
| Fullness for covering | Do not state the covering direction at "a full height"; DEFINITION HE6-1 requires \(\kappa>D'h\), and a full \(\kappa\) in \([(D'-1)h,\,D'h]\) indexes no member. | s4 |
| Three-data binding | Do not say the height is bound by `(SIDE-COUNT)`, `(SLOT-V)` and `(LIFT)` alone: those three derive the implication only; the binding needs `(RISE)`. | s4 |
| `(REF-HT)` for branch selection | Do not cite either clause of `(REF-HT)` for which branch a state takes; that is S1.8's case split plus the lowest-terms convention. | s4 |
| T1 as a source | Do not consume `T1_GAUGE_COCYCLE_2026-08-12.md`: it is outside the six source files, covered by no pin, and cited once as methodological precedent only. | s4 |
| HE6-0 as disk criterion | Do not credit LEMMA HE6-0 with S1.7 clause 1; the disk-membership read is LEMMA HE6-1's own conclusion. | s4 |
| HE6.A statement as supplier | Do not read S3.2's conclusion display from THEOREM HE6.A; it is this master's own clause-2 output at the instance. | s4 |
| Lemma proofs at level one | Do not import HE6 §S3.3, §S4's evaluation proofs, or §S6.1; only the statement displays are consumed. | s4 |
| Uncorrected β-guard | Do not read LEMMA HE6-2's dichotomy under its as-written guard ("denominator dividing \(\ell\)"); at \(\delta\ne\kappa\) with \(\ell\delta\in\mathbb Z\) the named \(\beta\) is undefined. Read it under `HE6-BETA-GUARD`. | s5 |
| The source's own site check | Do not consume HE6's post-PE4 verdict on its downstream sites; only the corrected guard is consumed. | s5 |
| Naming as the gated relation | Do not enumerate consuming sites by where the master *names* a directive; consumption includes transitive routes through pinned proof text. | s5 |
| HE7-12 licence at \(w\ne0\) | Do not use LEMMA HETOW-2's closing "Either way LEMMA HE7-12 applies" in the \(w\ne0\) branch; C-A re-scopes it to \(w=0\). | s5 |
| `GENTOW-4-1`(c) as a degree bound | Do not read clause (c) as supplying \(\deg w<D''\); it states the value disjunct only. | s5 |
| Junk-augmented presentations | Do not treat an object carrying an \(x\)-degree-\(\ge D''\) term as the composed key; the instance boxes substitute a monic \(\Phi_2\) of degree \(D_2\). | s5 |
| Unchecked accumulated increment | Do not assume the degree bound for \(W=w+w_1+\dots+w_j\) from the bound on \(w\) alone; it is checked from `(LIFT)` and corroborated by HE7-12(d). | s5 |
| "Forgets that strength" | Do not read S3.1 as exporting no irreducibility: \(\Phi'\)-irreducibility is exported as the item-5 discharge, at the original key only, and enters no step of the master proof. | s5 |
| Citation as the ledger test | Do not read S5 item 3 as requiring a pin for every *cited* unit; four classes of cited-but-unpinned material are admissible. | s5 |
| \(L\) collision | Do not conflate the legal lift \(L_k(c)\) with the side length \(L_\lambda\); the argument decides. | s5 |
| HE7-L1's proof | Do not consume LEMMA HE7-L1's §S4.1 display; it lies inside no span and is named as corroboration only. | s5 |
| HETOW:837 (S-2 absorption append) | Do not read the S-2 absorption append as changing HETOW-4's supply; the lemma statement stays byte-frozen and authoritative and the append is not consumed. | s5 |
| Grade transitivity | Do not infer that a composed instance is \(2/2\) from the master's acceptance; \(g_{\mathrm{master}}=2/2\) only removes the master's factor from the minimum. | s6 |
| The HE3 cap | Do not read S3.1, S3.2, or any level-two chain consuming an HE3 pin through S1.8C, above HE3's HEAD grade \(0/2\) (clean count \(1/2\)). | s6 |
| Acceptance as clearance | Do not read acceptance as discharging `(LB1)`, `(MP1)`, or the two stipulated carrier hypotheses: "Acceptance is acceptance of the composition WITH this ledger, not clearance of it." | s6 |
| A fifth conditionality | Do not carry `(MP1′)` forward as an obligation; it is retired and denotes a consequence of the pins. | s6 |
| Battery evidence | Do not expect or cite a machine battery for T2: none is owed, and S7's gate is the pin sweep. | s6 |
| Downstream status | Do not infer that any downstream consumption check has passed or that any consumer has been re-priced; both are queued. | s6 |
| In-place edits | Do not edit the accepted text: from the acceptance record forward the note takes dated appends only, and a rewrite reopens the hostile arc. | s6 |
| Naming as consumption | Do not read the master's naming of a source unit as consumption; the M-B disposition (Rider 3.1, `EFF.T2.98`) turns on exactly that distinction. | s6 |
| Rider review status | Do not treat post-pass rider 3 as third-context reviewed; it is not, and the record says so. | s6 |
| Pass-2 nits | Do not treat pass 2's four non-counted nits as cured; they are recorded in the log and deliberately left. | s6 |
| **[DEDUP — s2/s4/s5 counter-state fences, restated per round; merged to one row]** Counter states | Do not cite any historical "RESET to 0 of 2" or "STANDS AT 1 OF 2" reading anywhere in r1–r12 or the first two post-pass rider blocks as status; the accepted counter is **2/2**, set finally at `EFF.T2.97`. | s2+s4+s5 |
| **[DEDUP — s2/s3/s4 pin-count/taxonomy fences, restated per round with that round's own historical numbers; merged to one row]** Superseded pin counts | Do not cite 26, 27, 29, 32, 35, or 36 pins, nor any taxonomy other than the final \(20+4+13\), nor the "eight"/"nine" cured-consumption census, as effective; the accepted final figures, set at `EFF.T2.95`–`.96` and confirmed at `.101`, are **37 pins, taxonomy \(20+4+13\), zero synthetic markers, zero source edits, census ten**. | s2+s3+s4 |

**Dedup count for this section: 2** (a three-shard counter-state trio and a three-shard
pin-count/taxonomy trio, each restating the same underlying fence with that round's own
historical numbers as the arc progressed; both merged to one row apiece, listing every
historical value a reader might otherwise mistake for effective).

## 3. Statement inventory (105 units, contiguous, in source order)

### EFF.T2.01  [scope-record]

**CANONICAL STATEMENT:**

> “This note states and proves one mathematical master theorem, HE7.A, over the original complete DVR \(O\).”

> “It contains no Lean signature, record declaration, or interface sketch. Formal encodings belong to the S-5 probe output and to stage 2 of the arc.”

**DERIVATION:** `[RECORD]` This is the note’s own scope declaration. The acceptance record changes the grade and text authority, not the declared mathematical/formal boundary.

**CONDITIONALITY:** The mathematical result is accepted with the honesty ledger and the four standing conditions in the acceptance record.

**RESOLUTION TRACE:** front matter lines 7–17; final acceptance record.

**TEETH:** S7 Stage-2 formal gate; S4.2 formal-instance exclusion.

---

### EFF.T2.02  [hypothesis]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S0.1/S1.1]`

> “Fix a complete DVR \(O\) with fraction field \(K_0\), uniformizer \(\pi\), finite residue field
> \[
> k_0=\mathbf F_Q,
> \]
> and normalized valuation \(v(\pi)=1\).”

> “The current key \(\Phi\in O[x]\) is required to be monic, with
> \[
> D=\deg\Phi>0.
> \]”

> \[
> \boxed{\Phi\text{ is monic; irreducibility is not assumed.}}
> \tag{NO-IRR}
> \]

> “A stage order, integral closure, or quotient may appear as auxiliary instance data, but it never replaces \(O\) as coefficient ring or ground DVR.”

**DERIVATION:** `[HYPOTHESIS / REDLINE]` These are carrier assumptions. The proof’s final sentence checks the redline:

> “No step assumes that \(\Phi\) is irreducible, that \(O[x]/(\Phi)\) is a DVR, or that the coefficient DVR has changed.”

**CONDITIONALITY:** \(O\) is fixed throughout every recursive child; a key is monic of positive degree but may be reducible.

**RESOLUTION TRACE:** base S0.1/S1.1; reaffirmed by S8 and the acceptance audit.

**TEETH:** S7 Pass 1(2), reducible-key boundary gate; Stage-2 fixed-original-\(O\) gate.

---

### EFF.T2.03  [table]

**CANONICAL STATEMENT:** `[TABLE / ASSEMBLED — compiler inventory of the effective S0.2 rows; source descriptions are not represented as verbatim quotations]`

The effective table has 37 existing-text spans:

| Source | Effective pin names |
|---|---|
| HE3 | `HE3-A-STMT`, `HE3-A-PROOF`, `HE3-DEF1`, `HE3-HE3-1L`, `HE3-HE3-6`, `HE3-R8-2`, `HE3-R8-3`, `HE3-R8-4`, `HE3-R8-5` |
| HE6 | `HE6-FAMILY`, `HE6-PROOF`, `HE6-SLOT-SEAM`, `HE6-PEEL-CONVENTION`, `HE6-LIFT-1L`, `HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-ACCOUNT`, `HE6-BETA-GUARD` |
| HE7 | `HE7-A-STMT`, `HE7-SLOT-TRANSFER`, `HE7-MIXED-13P`, `HE7-COCYCLE-2P-THROUGH-R1D`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT` |
| HE6R1 | `HE6R1-1`, `HE6R1-2`, `HE6R1-3` |
| HETOW | `HETOW-LABELS`, `HETOW-LABELS-1`, `HETOW-KEY-BRIDGE`, `HETOW-KEY-BRIDGE-C-A`, `HETOW-A`, `HETOW-NORMALIZER-4` |
| GENTOW4 | `GENTOW-4-1`, `GENTOW-4-A`, `GENTOW-4-2`, `GENTOW-ACCEPTANCE-FOLD` |

The governing convention is:

> “No source file is edited to install a pin.”

> “Failure of any condition makes that route fail closed. A line number, synthetic comment, prospective anchor, or text inserted after source acceptance is not a pin.”

> “No unpinned source material is used to manufacture a theorem hypothesis, to discharge a named obligation, or to certify an instance substitution.”

**DERIVATION:** `[ASSEMBLED — pin chronology]` r2 supplies the four validity conditions; r3 repairs five pin descriptions and splits `HETOW-LABELS`; r4, r5, r10, r11 and r12 add ten previously uncovered consumptions. Acceptance records the final 37-pin sweep and zero synthetic markers/source edits.

**CONDITIONALITY:** A pin is valid only when its named unit and delimiter resolution satisfy effective S0.2. Consumption, not mere citation, is the gated relation.

**RESOLUTION TRACE:** base S0.2 deleted by r2 repair 1; r3 repairs 1–3 and 9; r4 repairs 1, 5–8, 12–13; r5 repairs 1, 3–5, 8; r6/r7 inventory corrections; r10–r12 additions; Rider 3; acceptance.

**TEETH:** S7 pin gate and standing consumption sweep.

---

### EFF.T2.04  [hypothesis]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S1.1]`

> \[
> k_0\hookrightarrow K,\qquad [K:k_0]<\infty,
> \tag{FINITE-RES}
> \]

> \[
> \boxed{D=e_{\mathcal C}f_{\mathcal C}.}
> \tag{DEG-EF}
> \]

> “The carrier has an integer-normalized value \(d\), an inherited threshold \(T\in\mathbf Z\), and a class of points
> \[
> \operatorname{Pt}\subseteq\overline K_0.
> \]”

> “"Integer-normalized" is meant literally: \(d=c_{\mathcal C}\,v\) on \(\overline K_0\) for a positive integer \(c_{\mathcal C}\) the carrier fixes, \(v\) being the unique extension fixed above. So \(d\) is itself a valuation — \(d(AB)=d(A)+d(B)\), and \(d(A+B)\ge\min(d(A),d(B))\) with equality when the two values differ — under the convention \(d(0)=+\infty\) that matches S1.2's \(h(0)=+\infty\).”

> \[
> \iota_\xi:K\hookrightarrow\overline k,
> \qquad
> \iota_\xi|_{k_0}=\operatorname{id}_{k_0}.
> \tag{RES-COMP}
> \]

**DERIVATION:** `[HYPOTHESIS]` `(DEG-EF)` is explicitly not inferred from monicity. r12 spells out that \(d\) is a valuation and records the five instance constants \(e_1,e_1,\ell e_1,e_1e_2,e_1e_2\).

**CONDITIONALITY:** Valued points lie in \(\overline K_0\); residual digits and embeddings lie in \(\overline k\); the ambient fields are never identified.

**RESOLUTION TRACE:** base S1.1 plus r12 repair 4(b).

**TEETH:** Stage-2 finite-compatible-residue and `(DEG-EF)` gates; S7 Pass 1 theorem gate.

---

### EFF.T2.05  [hypothesis]

**CANONICAL STATEMENT:**

> “For every nonzero \(A\in O[x]\) with \(\deg A<D\), the carrier assigns
> \[
> h(A)\in\mathbf Z,
> \qquad
> \operatorname{dig}(A)\in K^\times,
> \]
> such that, for every \(\xi\in\operatorname{Pt}\),
> \[
> d(A(\xi))=h(A)
> \tag{SLOT-V}
> \]
> and
> \[
> \operatorname{res}\!\left(
> \frac{A(\xi)}{n(h(A))(\xi)}
> \right)
> =
> \iota_\xi(\operatorname{dig}(A)).
> \tag{SLOT-R}
> \]”

> “When total notation is useful, set
> \[
> h(0)=+\infty,\qquad \operatorname{dig}(0)=0.
> \]”

**DERIVATION:** `[HYPOTHESIS]` Exactness is carrier data. Outside `Pt`, only predecessor-key lower bounds are asserted.

**CONDITIONALITY:** \(A\ne0\), \(\deg A<D\), and \(\xi\in\operatorname{Pt}\) for exact slot formulas.

**RESOLUTION TRACE:** base S1.2; r12’s valuation disclosure supplies the ultrametric laws later derivations use.

**TEETH:** S7 HE6 seam gate; sub-threshold/pass-2 refusal indirectly through legal lifts.

---

### EFF.T2.06  [definition]

**CANONICAL STATEMENT:** `[ASSEMBLED — level-one notation and seam]`

> \[
> \boxed{
> \gamma_k(A)=
> \sum_{\substack{t\ge0\\i+e_1t<D'}}
> \operatorname{res}\!\left(
> a_{i+e_1t}
> \pi^{-(k-(i+e_1t)h)/e_1}
> \right)\eta^t.}
> \tag{GAMMA}
> \]

> \[
> \operatorname{res}\!\left(
> \frac{n(k)(\xi)}{\varpi(\xi)^k}
> \right)
> =
> \eta_\xi^{-q(k)}.
> \tag{Q-DEF}
> \]

> \[
> \boxed{
> \operatorname{res}\!\left(
> \frac{A(\xi)}{\varpi(\xi)^k}
> \right)
> =
> \iota_\xi(\gamma_k(A))\,\eta_\xi^{-q(k)}.}
> \tag{HE6-SEAM}
> \]

> “The coefficient normalizers inside \(\gamma_k(A)\) and the negative sign on \(q(k)\) are mandatory.”

**DERIVATION:** `[ASSEMBLED]` `HE3-HE3-1L` supplies the monomial cancellation giving the normalized coefficient residues. `HE6-LIFT-1L` defines the reciprocal print/coherent normalizer ratio, and `HE6-SLOT-SEAM` supplies the per-\(A\) evaluation with the corrected minus sign. XREFs X04, X12 and X14 locate these units.

**CONDITIONALITY:** Level-one instance notation only; \(q(k)\) is used on occupied heights. The bare unnormalized coefficient-residue sum is not an alternative formula.

**RESOLUTION TRACE:** base S1.2 plus r2 repair 7, r4 repairs 1 and 9, r5 repair 4, r9 repair 1, and r12 repair 4(c).

**TEETH:** S7 Pass 1(3), HE6 seam gate; print/coherent-frame hostile tooth.

---

### EFF.T2.07  [definition]

**CANONICAL STATEMENT:**

> “The carrier has exact-height normalizers
> \[
> n:\mathbf Z\longrightarrow K_0(x)^\times,
> \qquad
> n(0)=1,
> \]”

> \[
> \boxed{
> \tau_\xi(a,b)
> =
> \operatorname{res}\!\left(
> \frac{n(a)(\xi)n(b)(\xi)}
>      {n(a+b)(\xi)}
> \right).}
> \tag{COC-DEF}
> \]

> \[
> \tau(a,b)\tau(a+b,c)
> =
> \tau(b,c)\tau(a,b+c).
> \tag{COC}
> \]

**DERIVATION:** `[ASSEMBLED — effective S1.3]` Independence of \(\xi\) gives a unique \(\tau(a,b)\in K^\times\); cancellation of four normalizer factors proves `(COC)`. `HE7-COCYCLE-2P-THROUGH-R1D` supplies the corrected all-level instance chain (X22).

**CONDITIONALITY:** The normalizer heights and the residue’s membership in the image of \(\iota_\xi\) are carrier hypotheses.

**RESOLUTION TRACE:** base S1.3; r2/r3 pin resolution; no later formula replacement.

**TEETH:** S7 Pass 1(4), live-carry cocycle gate; Pass 2 deep-cocycle tooth.

---

### EFF.T2.08  [definition]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S1.3]`

> \[
> \boxed{
> \iota_\xi(\vartheta_s)
> =
> \operatorname{res}\!\left(
> \frac{n(u)(\xi)^s}{n(su)(\xi)}
> \right)}
> \tag{THETA-EVAL}
> \]

> \[
> \Theta_s=\vartheta_s^{-1}.
> \]

> \[
> \boxed{\tau(k,k')=\beta^c.}
> \tag{BETA}
> \]

> “It is not replaced by \(1\). At deeper levels the same construction gives a monomial in all preceding residual letters.”

**DERIVATION:** `[ASSEMBLED]` The effective paragraph defines \(\vartheta_s\) through its evaluations. At level two the quotient
\(n_2(k)n_2(k')/n_2(k+k')\) equals \((\Phi'^\ell/\varpi^u)^c\); taking its residue gives \(\beta^c\).

**CONDITIONALITY:** \(\vartheta_s\) is source-supplied and independent of \(\xi\). The deeper-level monomial is not specialized to 1.

**RESOLUTION TRACE:** base S1.3, replaced by r2 repair 7; cocycle-chain pin repaired by r3 repair 1.

**TEETH:** S7 Pass 1(4); Pass 2 multi-letter deep-cocycle tooth.

---

### EFF.T2.09  [hypothesis]

**CANONICAL STATEMENT:**

> “At a full height \(k\), every digit \(c\in K\) has an integral lift
> \[
> L_k(c)\in O[x],\qquad \deg L_k(c)<D,
> \]”

> \[
> h(L_k(c))=k,
> \qquad
> \operatorname{dig}(L_k(c))=c.
> \tag{LIFT}
> \]

> \[
> \boxed{
> H_{\mathrm{lift}}(B)
> \subseteq
> \{k:k\text{ is full}\}.}
> \tag{OCC}
> \]

> “There is no all-height lift hypothesis.”

**DERIVATION:** `[HYPOTHESIS]` `(OCC)` is the visible finite-domain obligation. The note distinguishes \(L_k(c)\) from the side length \(L_\lambda\); only the former has a digit argument.

**CONDITIONALITY:** Lift existence only at full heights, and only the finite set actually required by a theorem block must be full.

**RESOLUTION TRACE:** base S1.4; r12 repair 4(a) supplies the notation fence.

**TEETH:** S7 Pass 2 sub-threshold-lift refusal; Stage-2 legal-lift-domain gate.

---

### EFF.T2.10  [lemma]

**CANONICAL STATEMENT:**

> “For HE6,
> \[
> k\text{ is full}
> \Longleftrightarrow
> k\ge(i(k)+e_1(f_1-1))h,
> \]
> and \(k\ge(D'-1)h\) is uniformly sufficient.”

> “For HE7 level two, a sufficient condition is
> \[
> m(k)\ge(d_r-1)u+(D'-1)h,
> \tag{FULL2}
> \]
> with uniform sufficient bound
> \[
> k\ge(\ell d_r-1)u+\ell(D'-1)h.
> \tag{FULL2-U}
> \]”

**DERIVATION:** `[IMPORTED]` The effective pin rows `HE3-HE3-1L`, `HE6-LIFT-1L`, and `HE7-SLOT-TRANSFER` locate the supplied lift-domain proofs (X04, X14, X20).

**CONDITIONALITY:** These are instance-specific criteria, not an all-height carrier theorem.

**RESOLUTION TRACE:** base S1.4; r1 repair 2 corrects the HE3+HE6 `(OCC)` credit; r3/r5 repair the pin perimeters.

**TEETH:** S7 Pass 2 sub-threshold-lift tooth.

---

### EFF.T2.11  [hypothesis]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S1.5]`

> \[
> F=\Phi^\mu+\sum_{j<\mu}A_j\Phi^j,
> \qquad
> \deg A_j<D,
> \qquad
> \deg F=\mu D.
> \tag{DEV}
> \]

> \[
> \boxed{
> \gcd_{K_0[x]}(F,\Phi)=1.}
> \tag{KEY-FREE}
> \]

> \[
> \sum_{\lambda\in\operatorname{Sides}(P)}L_\lambda=\mu.
> \tag{HULL-LENGTH}
> \]

> \[
> T<d(\Phi(\rho))<\infty.
> \tag{WINDOW}
> \]

> “Any proxy, truncated, or tower-print development used by an instance must agree with the full development on every lower-hull side under consideration. In addition, omitted terms, collected terms, and key carries must lie strictly above those sides. These are the mathematical `WindowSafe` and `CapSafe` assertions; they are not inferred merely from the phrase “arising from a label.””

**DERIVATION:** `[ASSEMBLED]` `(KEY-FREE)` implies \(A_0\ne0\), so the hull spans abscissae 0 through \(\mu\), yielding `(HULL-LENGTH)`. Window/cap safety remain carrier or instance hypotheses.

**CONDITIONALITY:** \(F\) is monic separable; its roots form a designated Galois-stable class in `Pt`; proxy developments must agree on every consumed side.

**RESOLUTION TRACE:** base S1.5; key-boundary routes resolved by r2–r6.

**TEETH:** S7 reducible-key gate; Pass 2 dangerous-collected-term tooth.

---

### EFF.T2.12  [hypothesis]

**CANONICAL STATEMENT:**

> \[
> R_\lambda(Y)
> =
> \prod_{r'}r'(Y)^{m_{\lambda,r'}},
> \tag{RES-FACT}
> \]

> \[
> \boxed{
> \deg R_\lambda=\frac{L_\lambda}{e'},
> \qquad
> e'\sum_{r'}m_{\lambda,r'}\deg r'=L_\lambda.}
> \tag{RES-DEG}
> \]

**DERIVATION:** `[IMPORTED NEWTON-SIDE CALCULATION]` The note explicitly says `(RES-DEG)` is part of the Newton-side calculation and is the degree bridge used in the orbit count.

**CONDITIONALITY:** \(\lambda=u'/e'\) is in lowest terms; raw-origin factors are removed before factorization.

**RESOLUTION TRACE:** base S1.5; r4 repair 5 expands `HE3-DEF1` to include the coherent construction and type invariance.

**TEETH:** S7 Pass 1 theorem gate; Pass 2 missing-`(RES-DEG)` refusal.

---

### EFF.T2.13  [definition]

**CANONICAL STATEMENT:**

> \[
> \Gamma_s=c_s^{\mathrm{mult}}\vartheta_s,
> \qquad
> R_{\mathrm{can}}(Y)=w^mR_{\mathrm{mult}}(Y/w).
> \tag{FRAME}
> \]

> “Frame changes preserve factor degrees, multiplicities, separability, and transported root classes. Literal coefficient strings are not asserted to be invariant.”

**DERIVATION:** `[IMPORTED]` The expanded `HE3-DEF1` pin includes the coherent \(R_\lambda\) construction and the attached geometric-system type-invariance theorem (X03). `HETOW-NORMALIZER-4` supplies the tower-print bridge (X33).

**CONDITIONALITY:** The scalar and variable-change factors are nonzero; only factor type and transported classes are invariant.

**RESOLUTION TRACE:** base S1.6; r4 repair 5; HETOW pin repairs through r12.

**TEETH:** S7 HETOW frame gate; Pass 2 nonzero-origin/frame tooth.

---

### EFF.T2.14  [definition]

**CANONICAL STATEMENT:**

> “If the source’s first attained grid point is
> \[
> s_{\mathrm{act}}=s_{\min}+\nu e,
> \]
> then
> \[
> \boxed{
> R_{\mathrm{raw}}(Y)=Y^\nu aR_{\mathrm{norm}}(bY)}
> \tag{ORIGIN}
> \]
> for fixed \(a,b\in K^\times\). The factor \(Y^\nu\) is recorded and removed before the normalized residual is factored.”

**DERIVATION:** `[IMPORTED FRAME CONVERSION]` This is source/instance data, and its preservation claim follows from multiplication and invertible rescaling after the explicit monomial factor is removed.

**CONDITIONALITY:** A nonzero origin shift is not silently discarded.

**RESOLUTION TRACE:** base S1.6; unchanged formula, reinforced by S7.

**TEETH:** S7 Pass 1 HETOW frame gate; Pass 2 nonzero raw-origin shift.

---

### EFF.T2.15  [hypothesis]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S1.7]`

> \[
> \Psi_{\lambda,r'}\in O[x],
> \qquad
> \deg\Psi_{\lambda,r'}=De'\deg r'.
> \tag{TEST}
> \]

> “The test polynomial is not assumed irreducible.”

Its proved properties are:

> “1. its roots lie in the intended disk and carry the label defined by \(r'\);
>
> 2. for roots of \(F\), its generic evaluation value is attained away from that label class and rises strictly on that class;
>
> 3. resultant symmetry makes the target class nonempty;
>
> 4. the classes associated with the distinct \(r'\) are disjoint and exhaust the roots belonging to the side;
>
> 5. the label construction is Galois equivariant;
>
> 6. every point in the \(r'\)-class has local invariants divisible by \(e_{\mathcal C}e'\), \(f_{\mathcal C}\deg r'\);
>
> 7. all tests and coefficient lifts remain in \(O[x]\).”

**DERIVATION:** `[IMPORTED TEST PACKAGE]` `HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-PROOF`, `HE6-FAMILY`, and `HE6-LIFT-1L` jointly supply the level-one package; `HE6-BETA-GUARD` governs clause 2. XREFs X10–X11 and X14–X18 verify those units. At level two `HE7-A-STMT`, `HE7-MIXED-13P`, and `HE7-PERT-TRANSPORT` supply the corresponding package (X19, X21, X24).

**CONDITIONALITY:** These are carrier/instance obligations; passing from \(K\) to \(K[Y]/(r')\) enlarges only the finite label field and never base-changes \(O\).

**RESOLUTION TRACE:** base S1.7; r1 repair 2; r10/r11 pin closure; r12 acceptance.

**TEETH:** S7 theorem gate; HE6 seam; mixed-label and missing-supplier attacks.

---

### EFF.T2.16  [hypothesis]

**CANONICAL STATEMENT:**

> \[
> \boxed{
> \sum_{\rho:F(\rho)=0}\min(w_\rho,\kappa)
> =
> D\sum_{\lambda\in\operatorname{Sides}(P)}
> L_\lambda\min(\lambda,\kappa).}
> \tag{ACCOUNT}
> \]

> “This is the only side-accounting identity used by the master proof.”

**DERIVATION:** `[IMPORTED]` `HE6-ACCOUNT` contains the resultant identity, the root-to-slope regrouping, and the source identity `(†)`; after the HE3/HE6 substitutions these are `(ACCOUNT)`. XREF X17 verifies the supplying span. Rider 2 records the transitive use of `HE6-BETA-GUARD` inside that proof.

**CONDITIONALITY:** \(\kappa>T\) and outside the finite critical set in the master statement; HE6 proves the supplying identity on the wider range \(\kappa>D'h\).

**RESOLUTION TRACE:** base S1.7; r10 repair 1; r11 repair 1; Rider 2.

**TEETH:** S7 Pass 1 theorem gate; GENTOW4 perimeter gate; Pass 2 missing-`(RES-DEG)`/accounting attacks.

---

### EFF.T2.17  [lemma]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S1.7A]`

> \[
> F=\prod_\lambda F_\lambda,
> \tag{SIDE-PROD}
> \]

> \[
> F_\lambda=\prod_{r'}F_{\lambda,r'}.
> \tag{LABEL-PROD}
> \]

> \[
> F_{\lambda,r'}
> =
> \Phi^{\nu_{\lambda,r'}}
> +
> \sum_{j<\nu_{\lambda,r'}}A^{(\lambda,r')}_j\Phi^j,
> \tag{LABEL-DEV}
> \]

> \[
> R(F_{\lambda,r'};Y)
> =
> c_{\lambda,r'}r'(Y)^{k_{\lambda,r'}},
> \tag{LABEL-PURE}
> \]

> \[
> \boxed{
> k_{\lambda,r'}
> =
> \frac{\nu_{\lambda,r'}}{e'\deg r'}
> =
> \frac{\deg F_{\lambda,r'}}{De'\deg r'}
> \in\mathbf Z_{\ge1}.}
> \tag{LABEL-OWN}
> \]

> “This is the HE7-13′ block calculation. No equality between
> \[
> k_{\lambda,r'}
> \quad\text{and}\quad
> m_{\lambda,r'}
> \]
> from the parent residual factorization is assumed.”

**DERIVATION:** `[IMPORTED BLOCK THEOREM]` The carrier supplies the monic separable side and label blocks, their disjoint exhaustive root partitions, own developments, pure residuals, and product identities. `HE7-MIXED-13P` supplies this at level two (X21); `GENTOW-4-A` supplies the partial-tower bouquet (X35). The parent-multiplicity formula installed by r1 is deleted by r2.

**CONDITIONALITY:** The block theorem is carrier data. A nontrivial split strictly decreases represented degree. Level-one use is subject to `(LB1)` exactly where clause 4 constructs blocks.

**RESOLUTION TRACE:** r1 repair 1 replaced in full by r2 repair 2; r3 repairs 6–8; r4 repair 10.

**TEETH:** S7 Pass 2 mixed residual with two repeated classes; GENTOW4 per-block perimeter gate.

---

### EFF.T2.18  [open-obligation]

**CANONICAL STATEMENT:**

> \[
> \boxed{\operatorname{LB}_1(\mathrm{HE3{+}HE6}).}
> \tag{LB1}
> \]

> “It is the assertion that every level-one state whose clause-4 processing demands blocks — every state with at least two sides, and every side whose residual is mixed — has the monic side and label blocks of S1.7A, with their own full developments, single-side hulls, pure residuals, product identities, disjoint exhaustive root partitions, and inherited continuation data.”

> “Clauses 1 and 2 are not: their proofs run on the unsplit hull of \(F\) itself, so the HE3.A and HE6 instance records' clause-1 and clause-2 conclusions carry no `(LB1)` conditionality at any level-one state, multi-side states included. "Unconditional" is said here of `(LB1)` alone and of clauses 1–2 alone. Two level-one routes remain conditional, each where it is taken: the clause-4 route on `(LB1)`, and the clause-5 peel at a recentered key on `(MP1)` (S1.8A). No level-one route is asserted unconditional simpliciter.”

**DERIVATION:** `[SOURCE FENCE]` The note enumerates the HE3/HE6 pins and expressly says none proves `(LB1)`. `HE7-MIXED-13P` supplies the level-two analogue but is not used retroactively at level one.

**CONDITIONALITY:** Clauses 1–2 run directly on the unsplit hull and carry no `(LB1)` condition. Only a level-one clause-4 block construction does.

**RESOLUTION TRACE:** r2 repair 4; widened by r3 repair 6; scoped by r4 repair 10 and r6 repair 3; reaffirmed by acceptance.

**TEETH:** S7 mixed-residual and multi-side hostile cases; signed source non-applicability at level one.

---

### EFF.T2.19  [hypothesis]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective product-1 branch]`

> “If
> \[
> e'\deg r'=1,
> \]
> then \(e'=1\) and \(r'=Y-s\) for some \(s\in K\).”

> \[
> \boxed{
> \begin{aligned}
> \text{(RISE)}\quad & d\bigl(\Phi_{\mathrm{new}}(\rho)\bigr)>\lambda
> \quad\text{at every root \(\rho\) of the class being refined},\\[1mm]
> \text{(HT)}\quad & k=\lambda.
> \end{aligned}}
> \tag{REF-HT}
> \]

> \[
> \Phi_{\mathrm{new}}=\Phi-L_\lambda(s).
> \]

> “The two clauses of `(REF-HT)` are not independent stipulations: (HT) is forced by (RISE), and that forcing uses master data only. (RISE) itself is stipulated, and its status is recorded at the end of this passage.”

**DERIVATION:** `[ASSEMBLED — master implication and instance discharge]` For roots in the class, `(SIDE-COUNT)` gives \(d(\Phi(\rho))=\lambda\); `(SLOT-V)` and `(LIFT)` give \(d(L_k(s)(\rho))=k\). If \(k\ne\lambda\), the ultrametric equality yields
\(d(\Phi-L_k(s))=\min(\lambda,k)\le\lambda\), contradicting `(RISE)`; hence `(HT)`. At level one, `HE3-A-PROOF` supplies the rise at the actual stage-\(\alpha\) step and `HE6-FAMILY`/`HE6-PROOF` supply the HE6 leg (X02, X10–X11). At level two `HE7-PERT-TRANSPORT` supplies LEMMA HE7-13’s rise (X24).

**CONDITIONALITY:** `(RISE)` is a carrier hypothesis, not an open ledger obligation. `(OCC)` must hold at the determined integer height \(\lambda\).

**RESOLUTION TRACE:** base S1.8; r6 repair 1; r7 repair 1; r8 repairs 1 and 4; r9 repair 1; Rider 1; r12 repair 4(d).

**TEETH:** S7 finite-refinement/root-preservation attack; print/coherent index mutant; lift-choice mutant.

---

### EFF.T2.20  [regression-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective level-one print/coherent index]`

> \[
> \boxed{
> \Psi_{\kappa,Z-\sigma}
> =
> \Phi'-L_\kappa\bigl(\sigma\eta^{q(\kappa)}\bigr),
> \qquad
> \Phi'-L_\kappa(s)
> =
> \Psi_{\kappa,\,Z-s\eta^{-q(\kappa)}} .}
> \tag{IDX-TWIST}
> \]

> “(IDX-TWIST) is an equality of polynomials AT the compatible choice \(B_0=-L_\kappa(\sigma\eta^{q(\kappa)})\)”

> “Read at an arbitrary permitted choice, (IDX-TWIST) therefore holds MODULO increments of height \(>\kappa\), and what is choice-independent is exactly the pair \(h(-B_0)=\kappa\), \(\operatorname{dig}(-B_0)=\sigma\eta^{q(\kappa)}\)”

**DERIVATION:** `[ASSEMBLED]` `HE6-FAMILY` fixes the print residue \(-\sigma\); `(HE6-SEAM)` converts it to coherent digit \(-\sigma\eta^{q(\kappa)}\). Multiplication by the fixed unit \(\eta^{q(\kappa)}\) is a bijection, so the family covers every nonempty recentering. Rider 1 proves compatible-choice permittedness and bounds arbitrary-choice differences above \(\kappa\).

**CONDITIONALITY:** The covering direction requires \(\kappa>D'h\), not mere fullness. Literal polynomial equality uses the compatible lift choice.

**RESOLUTION TRACE:** r9 repair 1; Post-pass Rider 1; r10 repair 2.

**TEETH:** print/coherent-frame mutant; lift-choice qualifier tooth.

---

### EFF.T2.21  [hypothesis]

**CANONICAL STATEMENT:**

> “If
> \[
> e'\deg r'\ge2,
> \]
> the test polynomial becomes the monic key of a child carrier over the same \(O\). Its inherited invariants are
> \[
> e_{\mathrm{child}}=e_{\mathcal C}e',
> \qquad
> f_{\mathrm{child}}=f_{\mathcal C}\deg r',
> \]”

> \[
> \mu_{\mathrm{child}}
> \le
> \frac{\mu}{e'\deg r'}
> \le\frac{\mu}{2}.
> \tag{MASS}
> \]

**DERIVATION:** `[IMPORTED CONTINUATION]` The carrier supplies child blocks with pairwise disjoint exhaustive roots and product equal to the parent label class. `(DEG-EF)` gives the displayed child key degree. `HE6R1-1` supplies the widened descent condition at the level-two route (X25).

**CONDITIONALITY:** `(MASS)` is asserted for nonterminal children. Terminal children emit their factor and need no rank comparison.

**RESOLUTION TRACE:** base S1.8; r3 repair 3 governs the HE6R1-1 re-display; rank details resolved by r4.

**TEETH:** S7 Pass 2 recursion/root-preservation tooth; product-1/product-≥2 split.

---

### EFF.T2.22  [lemma]

**CANONICAL STATEMENT:**

> “At a multi-side state, first apply `(SIDE-PROD)`. At a mixed side, next apply `(LABEL-PROD)`. Every emitted label block is read from its own development and residual data.”

> “A block with
> \[
> k_{\lambda,r'}=1
> \]
> has separable residual \(c_{\lambda,r'}r'\) and is terminal by clause 2. A block with
> \[
> k_{\lambda,r'}\ge2
> \]
> is continued independently by the product-\(1\)/product-\(\ge2\) alternatives. No decision is made from the multiplicity of \(r'\) in the parent residual.”

**DERIVATION:** `[ASSEMBLED]` `(SIDE-PROD)` and `(LABEL-PROD)` give smaller valid states with disjoint exhaustive roots and product identities. The own residual `(LABEL-PURE)` decides terminality or continuation.

**CONDITIONALITY:** At level one, constructing the blocks invokes `(LB1)`; direct clauses 1–2 do not.

**RESOLUTION TRACE:** r2 repairs 2 and 8; r3 repairs 6–8.

**TEETH:** S7 Pass 2 mixed residual with two repeated label classes.

---

### EFF.T2.23  [open-obligation]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective mid-chain input fence]`

> “Before invoking the window, test whether
> \[
> \widetilde\Phi\mid G.
> \]
> In that case put
> \[
> G'=\frac{G}{\widetilde\Phi}.
> \tag{MID-PEEL}
> \]”

> \[
> \deg G'=D(\nu-1),
> \qquad
> \mu(G')=\nu-1.
> \tag{MID-MASS}
> \]

> \[
> \boxed{\operatorname{MP}_1(\mathrm{HE3{+}HE6}).}
> \tag{MP1}
> \]

> “It is the assertion that, at every level-one state whose current key is a recentered key dividing its represented block, the quotient \(G'\) satisfies `(WINDOW)`, carries its own full development with `(ACCOUNT)` and the S1.7 test assertions together with the occupied-height, lift, frame, origin and residual-degree data, and that the peeled recentered key admits a certified orbit/\((e,f)\) decomposition — items 2, 3, 4 and 5 of the suite.”

**DERIVATION:** `[ASSEMBLED]` Separability proves master-side key-freeness: a common irreducible divisor of \(G'\) and \(\widetilde\Phi\) would square-divide \(G\). The original-key level-one suite is supplied by `HE6-PEEL-CONVENTION` (X13); the child-key level-two suite by `HE6R1-3` (X27). No pin proves the recentered level-one key’s orbit/\((e,f)\) item, so `(MP1)` remains open.

**CONDITIONALITY:** If \(\nu=1\), \(G'=1\) and no successor exists. A proper nontrivial gcd routes through S1.9. The peel occurs before `(WINDOW)` so \(+\infty\) is never fed to Newton accounting.

**RESOLUTION TRACE:** r2 repair 3; r3 repairs 4–5; r4 repairs 2 and 4; r5–r8 refinements; acceptance.

**TEETH:** S7 reducible/recentered-key boundary attacks; signed source non-applicability for the open level-one case.

---

### EFF.T2.24  [lemma]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S1.8B]`

> “Let a level-two state have as current key a recentered key \(\Psi^{(j)}=\Psi-W\) dividing its represented block, \(\Psi=\Psi_{\lambda,r}\) being the DEFINITION HE6-1 key at which the α-refine chain began. Items 2–5 of the `(MID-PEEL)` input suite are supplied for that state, and the derivation has two steps, each read at the key the state actually carries.”

> “`HE7-PERT-TRANSPORT` clause (c) lists what survives”

**DERIVATION:** `[ASSEMBLED]` `(REF-HT)` gives each increment value \(\lambda_2>T_2\) and `(LIFT)` gives degree \(<D''\); `HE7-PERT-TRANSPORT` folds the sum and transports `HE6R1-3` to the recentered key. At a composed key, the source pins give the value disjunct. The remaining degree bound is master-side: \(\Phi_2\) and \(\Psi_{\kappa_2,\widetilde r}\) are monic of the same degree, so their difference has lower degree; sums of lower-degree increments remain lower-degree. `HETOW-KEY-BRIDGE-C-A` governs the withdrawn source licence (X31).

**CONDITIONALITY:** This is a level-two discharge. The level-one recentered-key peel remains `(MP1)`-conditional.

**RESOLUTION TRACE:** r5 repair 2; r6 repairs 1 and 6; r7–r8 `(REF-HT)` resolution; r12 repair 1.

**TEETH:** composed-key transport tooth; HETOW C-A dated-directive tooth; accumulated-degree tooth.

---

### EFF.T2.25  [lemma]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S1.8C]`

> “The name `(MP1′)` is retired.”

> “r5 named the assertion (i)–(vii) as an obligation on the ground that "no pinned unit certifies" it. That ground is withdrawn: `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY` and `HE6-PROOF` certify it between them, and all four are already on both level-one records' Source-pin lines.”

> “What is removed is the extra frame-level obligation, not the level-one fences.”

**DERIVATION:** `[ASSEMBLED]` `HE3-A-PROOF` transports the refined sub-block over the same stage ring; `HE6-SLOT-SEAM` is key-free in its slot variables; `HE6-FAMILY` constructs the test family at any current monic degree-\(D'\) key; `HE6-PROOF` licenses HE3’s stage-α assembly for the enlarged HE6 classes. `(IDX-TWIST)` supplies the correct print/coherent reindexing and Rider 1 supplies the compatible lift choice.

**CONDITIONALITY:** Only the refined sub-block travels to the recentered key. `(LB1)` and `(MP1)` retain their original triggers.

**RESOLUTION TRACE:** r5’s `(MP1′)` section replaced by r6 repair 2; corrected by r7–r10; reaffirmed by acceptance.

**TEETH:** level-one frame-transport hostile tooth; print/coherent-frame tooth.

---

### EFF.T2.26  [hypothesis]

**CANONICAL STATEMENT:**

> \[
> \boxed{
> \sigma_{\mathcal C}:\{\text{states}\}\longrightarrow W_{\mathcal C},
> \qquad
> W_{\mathcal C}\ \text{well-founded},
> \qquad
> \sigma_{\mathcal C}(S')<\sigma_{\mathcal C}(S)}
> \tag{SEC-RANK}
> \]

> “at every product-\(1\) linear recentering \(S\to S'\). Nothing is required of \(\sigma_{\mathcal C}\) at any other transition: it may rise, or be reset, freely. `(SEC-RANK)` is part of the root-preserving continuation assertions hypothesised by HE7.A; this master does not derive it, and any instance that cannot supply it does not instantiate HE7.A.”

**DERIVATION:** `[HYPOTHESIS / INSTANCE DISCHARGE]` This is carrier data, not master-derived. `HE3-A-PROOF` supplies the level-one finite refine-chain rank (X02); `HE7-REF-TERM` supplies it at a DEFINITION HE6-1 key (X23); `HETOW-A` and `GENTOW-4-A` supply finiteness at the composed key (X32, X35).

**CONDITIONALITY:** An instance without `(SEC-RANK)` does not instantiate HE7.A. It is not a named open obligation because every listed instance supplies it.

**RESOLUTION TRACE:** r4 repair 3; route corrected by r5 repair 1; acceptance ledger.

**TEETH:** S7 Pass 2 well-founded-but-root-losing mutant; refinement termination tooth.

---

### EFF.T2.27  [lemma]

**CANONICAL STATEMENT:**

> \[
> \boxed{
> \operatorname{rank}(S)
> =
> \bigl(\deg F_S,\ \mu_S,\ \sigma_{\mathcal C}(S)\bigr)}
> \tag{RANK}
> \]

> “Every permitted nonterminal transition therefore strictly decreases `(RANK)`, and no transition increases a component earlier than the one it decreases.”

**DERIVATION:** `[ASSEMBLED — six transition checks]` Side and label splits decrease represented degree; `(MID-PEEL)` decreases degree and mass; a product-≥2 child jump has non-increasing degree and strictly smaller mass by `(TEST)` and `(MASS)`; a product-1 recentering preserves degree and mass and decreases `(SEC-RANK)`; S1.9 residual blocks have smaller degree. Lexicographic products of the three well-founded orders are well founded.

**CONDITIONALITY:** Every transition must also preserve or partition roots and transport its polynomial product; rank descent alone is insufficient.

**RESOLUTION TRACE:** r4 repair 3; trigger completeness repaired by r5 repair 5; later rounds preserve the tuple.

**TEETH:** S7 Pass 2 well-founded-but-root-losing mutant.

---

### EFF.T2.28  [hypothesis]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S1.9]`

> \[
> G=\operatorname{monicGCD}_{K_0[x]}(F,\Phi).
> \]

> \[
> F=\prod_iP_i\prod_jB_j.
> \tag{BOUNDARY-PROD}
> \]

> “Every residual block \(B_j\) is a σ-block for the same carrier and satisfies the complete HE7.A input suite applicable to that block: its full development, point condition, key-freeness, window and cap safety, frame and origin data, occupied-height and lift conditions, residual-degree identity, accounting identity, test assertions, and root-preserving continuation assertions. Where a side or label split is invoked, the applicable S1.7A block theorem is also part of the residual block’s data.”

> “Nothing asserts that \(G=\Phi\), that \(\Phi\) is irreducible, that one factor \(\Phi\) is peeled, or that a peel lowers \(\mu\) by exactly one.”

**DERIVATION:** `[HYPOTHESIS]` The decomposition supplies terminal irreducible boundary factors, pairwise disjoint exhaustive roots, and smaller valid residual blocks. Separability makes each emitted boundary factor simple.

**CONDITIONALITY:** Raw non-key-free inputs do not enter HE7.A; every residual block must separately carry the full suite.

**RESOLUTION TRACE:** base S1.9; strengthened by r2 repair 5; proper-gcd route ordered by r6 repair 5.

**TEETH:** S7 reducible-key boundary gate; Pass 2 several-boundary-factor tooth.

---

### EFF.T2.29  [lemma]

**CANONICAL STATEMENT:** `[ASSEMBLED — proof intermediates]`

> \[
> n_\lambda=DL_\lambda
> \tag{SIDE-COUNT}
> \]

> \[
> e'\sum_{r'\mid R_\lambda}\deg r'=L_\lambda.
> \tag{DEG-SUM}
> \]

**DERIVATION:** `[VERBATIM LOGIC, assembled]` Immediately above \(T\), the left slope of `(ACCOUNT)` is \(\mu D\); the right is \(D\sum_{\lambda>\kappa}L_\lambda\). Since total side length is \(\mu\), every side has \(\lambda>T\). Comparing the jumps of the two piecewise-linear sides at \(\lambda\) yields `(SIDE-COUNT)`. For separable \(R_\lambda\), `(RES-DEG)` specializes to `(DEG-SUM)`.

**CONDITIONALITY:** `(ACCOUNT)`, `(HULL-LENGTH)`, finite window values, and separability for `(DEG-SUM)`.

**RESOLUTION TRACE:** effective S2 proof; unchanged by later rounds.

**TEETH:** S7 Pass 1 pure-mathematics theorem gate.

---

### EFF.T2.30  [lemma]

**CANONICAL STATEMENT:**

> \[
> |\Omega|
> =
> [K_0(\rho):K_0]
> =
> e(\rho/K_0)f(\rho/K_0).
> \tag{FUND}
> \]

> \[
> |S_{\lambda,r'}|=De'\deg r',
> \qquad
> e=e_{\mathcal C}e',
> \qquad
> f=f_{\mathcal C}\deg r'.
> \]

**DERIVATION:** `[ASSEMBLED — effective r2 proof]` Local forcing and `(DEG-EF)` make every orbit in the class have size at least \(De'\deg r'\). Summing over disjoint exhaustive classes and using `(SIDE-COUNT)` and `(DEG-SUM)` forces equality term by term. The full class therefore has room for exactly one orbit; equality in `(FUND)` forces equality in both local divisibilities.

**CONDITIONALITY:** \(K_0\) complete discretely valued; the orbit extension finite separable; \(R_\lambda\) separable; test-class nonemptiness/disjointness/exhaustion.

**RESOLUTION TRACE:** base S2 proof paragraph replaced by r2 repair 6.

**TEETH:** S7 Pass 1 pure-mathematics theorem gate.

---

### EFF.T2.31  [theorem]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective THEOREM HE7.A]`

> “**THEOREM HE7.A (σ-LADDER MASTER).**”

> “Let \(\mathcal C\) be a σ-ladder carrier over the fixed original complete DVR \(O\), satisfying `(NO-IRR)`, `(DEG-EF)`, `(FINITE-RES)`, `(RES-COMP)`, the exact slot and lift formulas, the normalizer-defined cocycle law, and the base-change-free test assertions of S1.”

> “Let \(F\) be a key-free σ-block with development
> \[
> F=\Phi^\mu+\sum_{j<\mu}A_j\Phi^j,
> \]
> and suppose its window, cap, frame, origin, residual-degree, accounting, and root-preserving continuation assertions hold.
>
> Then:
>
> 1. every side \(\lambda\) of the complete lower hull \(P\) satisfies
> \[
> \lambda>T,
> \qquad
> \sum_{\lambda\in\operatorname{Sides}(P)}L_\lambda=\mu;
> \]
>
> 2. if \(\lambda=u'/e'\) is in lowest terms and \(R_\lambda\) is separable, then every monic irreducible factor \(r'\mid R_\lambda\) determines a Galois-stable root class
> \[
> S_{\lambda,r'}
> \]
> with
> \[
> |S_{\lambda,r'}|
> =De'\deg r'.
> \]
> This class is one Galois orbit and therefore is the root set of one monic irreducible factor of \(F\). Its invariants are
> \[
> e=e_{\mathcal C}e',
> \qquad
> f=f_{\mathcal C}\deg r';
> \]
>
> 3. if \(r'\) is repeated, the continuation is decided by the product \(e'\deg r'\). Product \(1\) gives the certified linear recentering; product at least \(2\) gives the certified child carrier and the mass bound `(MASS)`;
>
> 4. a state with more than one side is first replaced by its side blocks \(F_\lambda\) using `(SIDE-PROD)`. A mixed side is then replaced by the monic blocks \(F_{\lambda,r'}\) using `(LABEL-PROD)`. Each label block has its own pure residual
> \[
> c_{\lambda,r'}r'^{\,k_{\lambda,r'}},
> \qquad
> k_{\lambda,r'}
> =
> \frac{\deg F_{\lambda,r'}}
>      {De'\deg r'}.
> \]
> The block is terminal when \(k_{\lambda,r'}=1\), and is continued by clause 3 when \(k_{\lambda,r'}\ge2\). No equality with the parent residual multiplicity is used;
>
> 5. if the current key divides its represented block, the algorithm performs `(MID-PEEL)` before asserting `(WINDOW)`. The test is applied after each of the two transitions that can destroy key-freeness — the product-\(1\) linear recentering and the product-\(\ge2\) child jump — and is not needed after any other, key-freeness being preserved by side and label splits, by `(MID-PEEL)` itself, and by the S1.9 key-boundary decomposition, whose residual blocks are key-free by definition. The quotient is key-free, its mass is smaller by one, and its represented degree is smaller by \(D\); the peeled boundary roots are discharged by their certified boundary/orbit decomposition, which is item 5 of the `(MID-PEEL)` input suite and is a hypothesis of this clause, not a consequence of the peel identity;
>
> 6. the recursive read terminates. Its terminal monic irreducible factors have pairwise disjoint root sets, their product is \(F\), and their ramification and residue degrees are obtained by multiplying the successive displayed \(e\)- and \(f\)-increments.”

**DERIVATION:** `[ASSEMBLED — effective S2 proof]` EFF.T2.29 proves clause 1 and the side count; .30 proves clause 2. EFF.T2.17–.22 give the split and continuation cases. .23 gives the key-divides case with its suite; .27 supplies well-founded induction. Each transition preserves or partitions roots and transports products, so induction gives exhaustion as well as termination.

**CONDITIONALITY:** Full carrier suite, including `(SEC-RANK)` and `(RISE)`; `(LB1)` when level-one clause 4 constructs blocks; `(MP1)` for a level-one clause-5 peel at a recentered key.

**RESOLUTION TRACE:** base theorem; clauses/proof replaced or amended by r1 repair 1, r2 repairs 2–6 and 8, r3 repairs 4–8, r4 repairs 2–4, r5–r12 and Riders 1–2; accepted at 2/2.

**TEETH:** All S7 mathematical hostile gates.

---

### EFF.T2.32  [theorem]

**CANONICAL STATEMENT:**

> “**THEOREM T2.KEY-BOUNDARY.**”

> “Let \(F\) be a monic separable input with a key-boundary decomposition `(BOUNDARY-PROD)`, and suppose every residual block \(B_j\) satisfies the full HE7.A hypothesis suite declared in S1.9.”

> “Adjoin the certified irreducible boundary factors \(P_i\), and apply HE7.A separately to each key-free residual block \(B_j\). The resulting irreducible factors have disjoint root sets and exhaust the roots of \(F\).”

**DERIVATION:** `[VERBATIM EFFECTIVE PROOF]`

> “The boundary decomposition already gives the polynomial product and the disjoint exhaustive partition into boundary and residual root classes. Each \(P_i\) is terminal by its orbit certificate. HE7.A factors every residual block without changing or losing its root class. Multiplying the resulting identities proves the assertion.”

**CONDITIONALITY:** Every residual block carries the complete HE7.A suite; no false one-key peel is inferred.

**RESOLUTION TRACE:** base S2.1 strengthened by r2 repair 5.

**TEETH:** S7 Pass 1 reducible-key gate; Pass 2 multiple-boundary-factor tooth.

---

### EFF.T2.33  [instance-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S3.1]`

> \[
> \boxed{
> \begin{aligned}
> K&=\mathbf F_{Q^{f_1}},\\
> \Phi&=\Phi',\\
> D&=D'=e_1f_1,\\
> (e_{\mathcal C},f_{\mathcal C})&=(e_1,f_1),\\
> d&=dv=e_1v,\\
> T&=D'h,\\
> \operatorname{dig}(A)&=\gamma_{dv(A)}(A),\\
> \gcd(h,e_1)&=1.
> \end{aligned}}
> \tag{HE3-INSTANCE}
> \]

> “Thus this record is a composite HE3+HE6 discharge of the master hypotheses; it is not an HE3-only discharge.”

> “The resulting dictionary is
> \[
> (e,f)=(e_1e_s,f_1f_s).
> \]”

**DERIVATION:** `[ASSEMBLED]` HE3 pins supply carrier, slots, lifts, development, hull/window/cap, label equivariance, and the stage-α continuation; HE6 pins supply the test package and `(ACCOUNT)`. XREFs X01–X18 verify the effective level-one perimeter. Original-key irreducibility is exported only to discharge item 5 of the peel suite; it is not a master premise.

**CONDITIONALITY:** Clause-4 block construction is `(LB1)`-conditional; a clause-5 peel at a recentered level-one key is `(MP1)`-conditional. The original-key peel is supplied by `HE6-PEEL-CONVENTION`.

**RESOLUTION TRACE:** base S3.1; r1 repair 2; r2/r3 level-one fences; all later pin/source and `(REF-HT)` repairs; r12 repair 2; acceptance grade cap.

**TEETH:** HE6 seam; level-one `(RISE)` discharge; level-one fence attacks.

---

### EFF.T2.34  [instance-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S3.2]`

> \[
> \boxed{
> \begin{aligned}
> K&=\mathbf F_{Q^{f_1}},\\
> \Phi&=\Phi',\\
> D&=D'=e_1f_1,\\
> (e_{\mathcal C},f_{\mathcal C})&=(e_1,f_1),\\
> d&=dv=e_1v,\\
> T&=D'h,\\
> \gcd(h,e_1)&=1.
> \end{aligned}}
> \tag{HE6-INSTANCE}
> \]

> \[
> \Psi_{\kappa,r}
> =
> {\Phi'}^{\ell d}
> +\sum_{t<d}B_t{\Phi'}^{\ell t}
> \in O[x],
> \qquad
> \deg\Psi_{\kappa,r}=D'\ell d.
> \]

> “For a separable residual factor \(r\),
> \[
> |S_{\lambda,r}|=D'\ell\deg r,
> \qquad
> (e,f)=(e_1\ell,f_1\deg r).
> \]”

**DERIVATION:** `[ASSEMBLED]` `HE6-FAMILY`, `HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-ACCOUNT`, and `HE6-PROOF` supply the family, seven assertions, root labels, accounting, and assembly. `HE6-BETA-GUARD` governs clause 2. XREFs X10–X18 verify the perimeter. EFF.T2.29–.31 then derive the orbit conclusion.

**CONDITIONALITY:** The same `(LB1)`/`(MP1)` level-one fences as .33. Repeated product-≥2 branches continue at level two; a one-round HE6 theorem does not justify an empty continuation.

**RESOLUTION TRACE:** base S3.2; r2–r12 supplier, frame, rank, and fence repairs; acceptance.

**TEETH:** HE6 seam and test-package gates; `(ACCOUNT)` supplier gate; print/coherent mutant.

---

### EFF.T2.35  [instance-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S3.3]`

> \[
> \boxed{
> \begin{aligned}
> K_{\mathcal C}&=K_2,\\
> \Phi&=\Psi_{\lambda,r},\\
> D&=D''=D'\ell d_r,\\
> (e_{\mathcal C},f_{\mathcal C})&=(e_1\ell,f_1d_r),\\
> d&=dv_2=\ell\,dv=\ell e_1v,\\
> T&=T_2=\ell d_ru.
> \end{aligned}}
> \tag{HE7-INSTANCE}
> \]

> “The key \(\Psi_{\lambda,r}\) is monic. Its irreducibility is not a premise.”

> \[
> |S_{\lambda_2,r_2}|=D''\ell_2\deg r_2,
> \qquad
> e=e_1\ell\ell_2,
> \qquad
> f=f_1d_r\deg r_2.
> \]

**DERIVATION:** `[ASSEMBLED]` `HE7-SLOT-TRANSFER` supplies slots/lifts; `HE7-COCYCLE-2P-THROUGH-R1D` supplies the live \(\beta^c\) twist; `HE7-MIXED-13P` supplies own label blocks; `HE7-REF-TERM` supplies `(SEC-RANK)`; `HE7-PERT-TRANSPORT` supplies `(RISE)` and recentered-key transport; `HE6R1-1`–`-3` supply descent, block projection, and peel. XREFs X19–X27 verify all units.

**CONDITIONALITY:** Residual labels are irreducible; the current key need not be. If the underlying level-one key was recentered, S1.8C transports the HE3+HE6 frame with its existing `(LB1)`/`(MP1)` triggers.

**RESOLUTION TRACE:** base S3.3; r2 repair 4; r3–r12 transport/pin/rank repairs; acceptance.

**TEETH:** live cocycle carry; mixed block; level-two peel; refine-chain termination.

---

### EFF.T2.36  [instance-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S3.4]`

> \[
> \boxed{
> \begin{aligned}
> K_{\mathcal C}&=K_2\cong\mathbf F_{Q^{f_1f_2}},\\
> \Phi&=\Phi_2,\\
> D&=D_2=D'e_2f_2,\\
> (e_{\mathcal C},f_{\mathcal C})&=(e_1e_2,f_1f_2),\\
> d&=dv_2=e_1e_2v,\\
> T&=T_2=e_2f_2u_2.
> \end{aligned}}
> \tag{HETOW-INSTANCE}
> \]

> \[
> R_{\lambda_2}(Z)
> =
> \tau(H_0)\widehat R_{\lambda_2}(Z/\delta),
> \qquad
> \delta=\tau(u_3)\in K^\times.
> \]

> \[
> e=e_1e_2\ell_2,
> \qquad
> f=f_1f_2\deg r_2.
> \]

**DERIVATION:** `[ASSEMBLED]` `HETOW-LABELS`/`-1` supply the carrier and transported letter; `HETOW-KEY-BRIDGE` supplies the value disjunct and key-family membership; `HETOW-KEY-BRIDGE-C-A` governs its HE7-12 licence; `HETOW-A` supplies the theorem at the composed key and `(SEC-RANK)`; `HETOW-NORMALIZER-4` supplies frame routing. XREFs X28–X33 verify these designations. The \(w\ne0\) degree bound is derived by cancellation of the leading terms of two monic equal-degree keys.

**CONDITIONALITY:** Any proper-gcd key boundary uses T2.KEY-BOUNDARY. Raw and coherent coefficient arrays are not identified. Any HE3-dependent recentered-level-one history retains the HE3 grade cap.

**RESOLUTION TRACE:** base S3.4; r3 pin split; r5 composed-key routing; r6/r12 scope repair; acceptance.

**TEETH:** HETOW frame gate; composed-key/C-A gate; origin-shift tooth.

---

### EFF.T2.37  [instance-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S3.5]`

> \[
> \boxed{
> \begin{aligned}
> K_{\mathcal C}&=K_2,\\
> \Phi&=\Phi_2,\\
> D&=D_2=D'e_2f_2,\\
> (e_{\mathcal C},f_{\mathcal C})&=(e_1e_2,f_1f_2),\\
> d&=dv_2=e_1e_2v,\\
> T&=T_2.
> \end{aligned}}
> \tag{GENTOW4-INSTANCE}
> \]

> \[
> \mu_2^*=\sum_{\lambda_2>T_2}L_{\lambda_2}(f),
> \qquad
> \deg f_S=D_2\mu_2^*.
> \]

> “The count-side mixed-multiplicity tie, partial-side budgets, and density laws are not conclusions of this σ-decision instance.”

**DERIVATION:** `[ASSEMBLED]` `GENTOW-4-A` supplies the bouquet blocks; `GENTOW-4-1` supplies projection/window/key bridge; `GENTOW-4-2` supplies the source unit while the master explicitly declines its unsupported parent-multiplicity use; `GENTOW-ACCEPTANCE-FOLD` supplies source grade. XREFs X34–X37 verify the units. `HE6R1-2`, `HE7-MIXED-13P`, `HE7-PERT-TRANSPORT`, and `HETOW-KEY-BRIDGE-C-A` supply the effective cross-source routes.

**CONDITIONALITY:** Per selected bouquet block; no whole-polynomial monicity or length transfer without proof; proper-gcd boundaries use T2.KEY-BOUNDARY.

**RESOLUTION TRACE:** base S3.5; r2 repairs 2/4; r4 repair 12; r5–r12 source-pin and composed-key repairs; acceptance.

**TEETH:** S7 GENTOW4 perimeter gate; mixed-multiplicity exclusion tooth.

---

### EFF.T2.38  [definition]

**CANONICAL STATEMENT:**

> \[
> \operatorname{grade}(I)
> =
> \min(
> g_{\mathrm{master}},
> g_{\mathrm{carrier}},
> g_{\mathrm{frame}},
> g_{\mathrm{local}}
> ).
> \tag{GRADE}
> \]

**DERIVATION:** `[DEFINITIONAL]` Acceptance sets \(g_{\mathrm{master}}=2/2\) but leaves the minimum rule unchanged.

**CONDITIONALITY:** HE3 is consumed at attempt grade 0/2 (clean count 1/2), so S3.1/S3.2 and any level-two chain consuming HE3 through S1.8C remain capped there.

**RESOLUTION TRACE:** base S4.1 plus acceptance record.

**TEETH:** S7 grade-laundering gate.

---

### EFF.T2.39  [fence]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S4.1/S4.2]`

> “The theorem assumes the explicit quantitative consequences `(ACCOUNT)`, `(RES-DEG)`, nonemptiness, exhaustion, and root-preserving continuation. These are source obligations, not conclusions obtained merely by naming a carrier.”

> “The master does not claim:
> - a complete-DVR structure on \(O[x]/(\Phi)\);
> - irreducibility of the current key;
> - that \(\Phi\nmid F\) is sufficient for key-freeness;
> - all-height lift surjectivity;
> - equality of raw and coherent residual coefficient arrays;
> - termination without root preservation and root partition;
> - the mixed-multiplicity product formula;
> - partial-side budget or density laws;
> - an unconditional level-one mid-chain peel at a recentered key;
> - an elaborated formal instance.”

**DERIVATION:** `[SOURCE HONESTY LEDGER]` These are explicit negative claims. Later rounds add `(MP1)` and retire `(MP1′)` without removing any listed negative edge.

**CONDITIONALITY:** Acceptance does not clear these fences.

**RESOLUTION TRACE:** base S4.2 plus r4/r5/r6 fence amendments and acceptance.

**TEETH:** all relevant S7 hostile gates; especially reducible key, lift domain, frame, and root-preservation.

---

### EFF.T2.40  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S5 re-composition ledger]`

The effective ledger includes:

> “1. The invalid reducible-key peel is replaced by `(KEY-FREE)` and the separate gcd/orbit boundary theorem.”

> “Every source unit this master CONSUMES lies inside a span of `(PINS)`, resolved by S0.2's existing-text delimiters”

> “11. The cocycle is defined as the residue of the normalizer quotient, so the HE7 \(\beta^c\) twist cannot be replaced by a trivial cocycle.”

> “14. Label-block terminality uses the block-owned exponent `(LABEL-OWN)`, never the parent residual multiplicity.”

Effective item 16 is:

> “Level-one reads demanding side or label blocks remain conditional on the named obligation `(LB1)`.”

> “17. Level-one clause-5 reads at a **recentered** key remain conditional on the named obligation `(MP1)`.”

**DERIVATION:** `[RECORD]` Each row points to the effective unit that closes or fences the former defect: .28/.32, .03, .07–.08, .17/.22, .18, and .23 respectively.

**CONDITIONALITY:** Consumption—not citation—is gated; supersession notices, declinations, non-operative directives, and boundary-fixing quotations may be cited unpinned exactly as r12 repair 3 records.

**RESOLUTION TRACE:** base S5 plus r2 repair 8, r4 repairs 2/4, r5 repairs 2/5, r6 repair 2, and r12 repair 3.

**TEETH:** S7 pin/consumption gate and theorem-assembly audit.

---

### EFF.T2.41  [table]

**CANONICAL STATEMENT:** `[TABLE — effective S6]`

| Hazard | Verdict | Mathematical closure |
|---|---|---|
| Hypothesis migration | **Closed for composition** | Key-freeness, finite windows, lift domains, accounting, residual degree, frame/origin changes, cap safety, and recursive root preservation are displayed hypotheses. |
| Instance-strength collapse | **Closed** | The key is monic only; \(D=e_{\mathcal C}f_{\mathcal C}\); lifts exist only at full heights; repeated branches split on \(e'\deg r'\). |
| Hidden perimeter enlargement | **Closed** | Every instance must prove its full-hull or projected-hull identity and its cap assertion. Mixed residuals are processed per block. |
| Convention seam | **Closed** | `(GAMMA)`, `(HE6-SEAM)`, `(COC-DEF)`, `(BETA)`, `(FRAME)`, `(ORIGIN)`, the HETOW bridge, and the \(c_g\)-translation govern all comparisons. |
| Grade laundering | **Closed for composition; open for acceptance** | `(GRADE)` takes the minimum of the master, carrier, frame, and local grades. |

**DERIVATION:** `[TABLE / RECORD]` Each closure row is justified by the statement families cited in its third column. Acceptance closes the master arc but retains `(GRADE)` and the source caps.

**CONDITIONALITY:** “Closed” is for the displayed composition perimeter, not a claim that `(LB1)` or `(MP1)` has been solved.

**RESOLUTION TRACE:** base S6 resolved by r2–r12 and acceptance.

**TEETH:** five hazard classes summarize the S7 hostile surface.

---

### EFF.T2.42  [acceptance-box]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S7 and final record]`

> “The v2 arc consists of two hostile passes over this post-composition text. A gap-or-worse repair resets the clean count.”

> “The S7 acceptance gate — two consecutive clean hostile passes over one effective text — is therefore MET”

> “That sweep was run whole at **37** pins by pass 2 — all 40 delimiter lines of the 20 quoted pairs resolved by exact-full-line search, each occurring exactly once and each first preceding its last, 4 first-only pins resolved at their quoted first delimiter, 13 description-only pins resolving to a unique unit head, and all spans within a file pairwise disjoint — and re-resolved to the same \(20+4+13=37\) inventory by pass 1, which additionally certified the new span `HETOW-KEY-BRIDGE-C-A` [548, 569] minimal under S0.2.”

**DERIVATION:** `[ACCEPTANCE RECORD]` `T2SOL5_output.log` records 0C+0G+0m; `T2P10_output.log` records 0C+0G+1m; Rider 3 folds the wording-only minor without reset. The acceptance record declares 2/2.

**CONDITIONALITY:** Acceptance is of the composition with `(LB1)`, `(MP1)`, `(SEC-RANK)`, `(RISE)`, `(GRADE)`, and the HE3 cap intact.

**RESOLUTION TRACE:** base S7; counters r1–r12; Riders 1–3; governing acceptance.

**TEETH:** all Pass 1 and Pass 2 hostile rows; pin sweep.

---

### EFF.T2.43  [fence]

**CANONICAL STATEMENT:**

> “Only after the mathematical passes are clean does the S-5 formal probe encode the theorem.”

> “Its HE7 construction may require irreducibility of residual labels and emitted boundary factors. It must generate no obligation asserting irreducibility of the current key.”

> “This v2 note does not claim that the formal gate has already passed.”

**DERIVATION:** `[PROTOCOL FENCE]` This is an explicit future-gate requirement, not a mathematical consequence or a completed Lean artifact.

**CONDITIONALITY:** Any later encoding must preserve original \(O\), separate valued/residue closures, finite compatible \(K/k_0\), `(DEG-EF)`, the live cocycle, lift domains, complete hulls, residual-degree accounting, boundary preprocessing, and root-preserving recursion.

**RESOLUTION TRACE:** base S7 Stage 2; unchanged by acceptance.

**TEETH:** Stage-2 formal gate.

---

### EFF.T2.44  [acceptance-box]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective S8 plus acceptance]`

> “**S-6 GO for the pure-mathematics master.**”

> “A reducible key boundary is handled by a separate gcd/orbit decomposition, never by a false one-factor peel.”

> \[
> \boxed{
> \text{Any later HE7 formalization that requires irreducibility of the current key is not a formalization of this theorem.}}
> \]

> “The master's own attempt grade moves \(0/2\to 2/2\),”

**DERIVATION:** `[ASSEMBLED]` EFF.T2.31 proves the key-free master, .32 proves the boundary theorem, .33–.37 discharge the five instance substitutions with their declared fences, and .42 supplies the acceptance gate.

**CONDITIONALITY:** The two open obligations and the HE3 supplier cap survive. Downstream consumption checks remain the next queue.

**RESOLUTION TRACE:** base S8; r1–r12; Riders 1–3; final acceptance.

**TEETH:** all theorem, perimeter, convention, grade, and pin gates.

---
### EFF.T2.45  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r4 round record: provenance, protocol, counter]`

> “*(Opus/Claude repair arm, against the r3 hostile pass of record `runs/comp13/T2P3_output.log` — 0 CRITICAL + 4 GAP + 8 minor; counter resets.)*”

> “**Verification protocol for this round.** Every delimiter line quoted below was checked on 2026-08-13 by exact-full-line search in the named accepted source file, and both the command and its count are recorded at the pin. No source file is edited by this round; the expected source edit count remains zero.”

> “r4 folds repairs for all four GAPs (A-3, B-1, B-2, D-1) and all eight minors (A-1, A-2, A-4, A-5, A-6, D-2, E-1, F-1) of the r3 hostile pass of record, plus the pin-inventory consequences. Two of these are theorem-statement changes: clause 5's trigger is widened to the case its own cited discharge is about (repair 2), and the rank paragraph now displays the tuple it previously only named (repair 3). Neither adds a conclusion; both add a hypothesis or a case whose mechanism the body already proves, and repair 3 makes an implicit carrier assumption explicit as `(SEC-RANK)`. Two named obligations are now open at level one: `(LB1)` for clause-4 block construction and `(MP1)` for the clause-5 peel at a recentered key.”

> “**The clean-pass counter is RESET to 0 of 2.**”

**DERIVATION:** `[ROUND RECORD]` The reset is the direct application of S7's stated rule, quoted by the counter itself: “A gap-or-worse repair resets the clean count”. The census (0C+4G+8m) is the pass log's, not the round's own grading; the round's claim is only that it folds every finding of that census.

**CONDITIONALITY:** Historical as to status. The acceptance record supersedes the counter (2/2) and the obligation set (`(LB1)` and `(MP1)` survive; `(MP1′)`, opened later at r5, is retired at r6). The two theorem-statement changes are **not** superseded: both stand in the accepted text. The zero-source-edit assertion is confirmed at acceptance (“**Zero source edits**”).

**RESOLUTION TRACE:** source lines 2262–2268 (header and protocol) and 2604–2608 (counter); superseded as to counter and obligation set by the acceptance record.

**TEETH:** S7 two-clean-pass acceptance gate; the r3 hostile pass of record as the battery event this round answers.

---

### EFF.T2.46  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r5 round record: provenance, protocol, root cause, counter]`

> “*(Opus/Claude repair arm, against the r4 hostile pass of record `runs/comp13/T2P4_output.log` — 0 CRITICAL + 2 GAP + 5 minor; counter resets.)*”

> “**Verification protocol for this round.** Every source delimiter line quoted below was checked on 2026-08-13 by exact-full-line search (`grep -cFx`) in the named accepted source file, and both the command and its count are recorded at the pin. No source file is edited by this round; the expected source edit count remains zero. Landmarks internal to this master are quoted from the **r4 effective text**, and their uniqueness is recorded in the form `sed -n '1,2608p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF '<string>'` → **1**; the line bound 2608 is the last line of the r4 round and excludes this round's own re-quotations, which would otherwise inflate every count.”

> “**The root cause both GAPs share.** Both r4 theorem-statement changes — the widened clause-5 trigger (r4 repair 2) and the carrier hypothesis `(SEC-RANK)` (r4 repair 3) — are consumed at keys that are not literally DEFINITION HE6-1 test polynomials: at the composed key \(\Phi_2\) (S3.4/S3.5), and at a **recentered** level-two key \(\Psi-W\) (every level-two α-refine, at every level-two record). The corpus object that carries the level-two package across such a key is **LEMMA HE7-12 (SLOT-DOMINATION)**, asserted at the composed key by **LEMMA HETOW-2** and at the partial-tower key by **LEMMA GENTOW-4.1(c)**. r4 named none of the first two and pinned only the third.”

> “Its substantive content is one object: the perturbation transport LEMMA HE7-12, previously consumed at two theorem-statement changes and named nowhere, is now pinned as `HE7-PERT-TRANSPORT` and cited at the two places that need it.”

> “Three named obligations are therefore open: `(LB1)` for clause-4 block construction at level one, `(MP1)` for the clause-5 peel at a recentered level-one key, and `(MP1′)` for reading over a recentered level-one key at any level.”

**DERIVATION:** `[ROUND RECORD]` The landmark convention is the round's own device for making master-internal supersession auditable: a superseded sentence is quoted byte-exactly and its uniqueness is certified under a line bound that excludes the quoting round. The bound 2608 is the last line of r4. Compilation re-ran nine of these landmark counts (§3, part B) and all returned 1.

**CONDITIONALITY:** Historical as to status. `(MP1′)` is retired at r6 repair 2 and never becomes a standing conditionality. The counter is superseded to 2/2. The pinning of `HE7-PERT-TRANSPORT` and `HETOW-KEY-BRIDGE` stands in the accepted text.

**RESOLUTION TRACE:** source lines 2612–2618 (header, protocol, root cause) and 2908–2912 (counter); `(MP1′)` superseded by r6 repair 2; counter superseded by the acceptance record.

**TEETH:** S7 acceptance gate; the r4 hostile pass of record; the standing S7 consumption sweep that this round's repair 4 re-runs.

---

### EFF.T2.47  [fence]

**CANONICAL STATEMENT:** `[ASSEMBLED — the HE6-SLOT-SEAM adjudication and its two signed declinations]`

> “The r2 description "the corrected normalized-slot/seam display" resolves against three distinct corrected slot/seam units of `HE6_PROOF_2026-08-08.md`, so condition 1 of S0.2 ("its named source unit occurs exactly once in the named file") could not be discharged. The pin is adjudicated by its consumption, not by its wording.”

> “**Adjudication.** Only **LEMMA HE6-0″ (THE SLOT LEMMA at (T1)/(T2) POINTS)** carries both consumed clauses in one unit: the exact height law at an arbitrary \(A\) and an arbitrary (T1)/(T2) point, and the \(\varpi\)-read residue \(\iota_\xi(\gamma)\eta_\xi^{-q}\) with the `[r2]` sign correction that this master's minus sign reproduces. Its own head calls it "the form this note actually consumes". The two competing candidates are declined for stated reasons, so that no later reader re-opens the choice:”

> “- HE6's §S1 **CONVENTION (ϖ-normalizers: twist-free)** fixes \(\varpi\) and constructs \(R_\lambda\). It is a Newton-side residual assembly — this master's `(RES-FACT)` input — and states no per-\(A\) slot law and no \(\eta^{-q}\) conversion. This master pins its \(R_\lambda\) construction at HE3 instead, through `HE3-DEF1` (repair 5). This unit is separately pinned by repair 4, for its peel clause only.
> - **LEMMA HE6-1L** with its **RIDER** is the reachability/lift lemma: it describes the *set* of residues realised at a height, i.e. this master's `(LIFT)`/`(OCC)` data, and its RIDER records the \(\varpi\)-vs-\(n(k)\) ratio as one fixed element of \(K\). It does not evaluate a given \(A\).”

The scope of a declination is fixed by r5 repair 4:

> “Declining a unit as the supplier of one consumption is not a declaration that the master consumes nothing from it. What it does supply, and what is pinned here, is the definition of \(q(k)\) and the \(\varpi\)-vs-\(n(k)\) normalizer ratio.”

**DERIVATION:** `[ADJUDICATION]` The rule applied is “adjudicated by its consumption, not by its wording”: the master's two consumptions at this pin are `(SLOT-V)` at an arbitrary \(A\) and the `(HE6-SEAM)` conversion, restated at S3.2, and exactly one HE6 unit carries both. The declinations are then *signed non-applicability*, each with its own reason and its own redirect — the CONVENTION to `HE3-DEF1` for \(R_\lambda\) and (later) to `HE6-PEEL-CONVENTION` for the peel clause; LEMMA HE6-1L to `HE6-LIFT-1L` for \(q(k)\) and `(LIFT)`/`(OCC)`. The full-height criterion is redirected to `HE3-HE3-1L`, “whose statement carries that threshold verbatim”.

**CONDITIONALITY:** The declination of LEMMA HE6-1L is scoped to the per-\(A\) slot law only; r5 repair 4 pins the same lemma for \(q(k)\) without reversing the declination. The declination of the CONVENTION is scoped to the slot/seam consumption only; r4 repair 13 pins it for the peel clause.

**RESOLUTION TRACE:** r4 repair 1 (2270–2305) as scoped by r5 repair 4 (2770–2772). Destination of the row replacement is the S0.2 `(PINS)` table (shard 1, EFF.T2.03, XREF X12); the adjudication and declinations are homed here.

**TEETH:** S7 pin gate condition 1 (unique named unit); HE6 seam gate; the standing consumption sweep that later re-pins the declined unit.

---

### EFF.T2.48  [convention]

**CANONICAL STATEMENT:** `[ASSEMBLED — the two-unit contiguous span declaration]`

> “This is a two-unit contiguous span, declared in the same form as `HE7-COCYCLE-2P-THROUGH-R1D` (r3 repair 1(b)): the pin is the run of consecutive complete units from the first delimiter to the last, and both endpoint units are complete. The source's own HEAD calls the pair "PINNED at DEFINITION 1 [r2] with the coboundary Remark", so the two-unit reading is the source's.”

Re-applied at r5 repair 1(b):

> “**(b) New pin `HE7-PERT-TRANSPORT`** — LEMMA HE7-12 together with LEMMA HE7-13, statements and proofs: a two-unit contiguous span, declared in the same form as `HE3-DEF1` (r4 repair 5) and `HE7-COCYCLE-2P-THROUGH-R1D` (r3 repair 1(b)).”

**DERIVATION:** `[CONVENTION EXTENSION]` S0.2's unit-boundary rule and r3 repair 2's nesting/over-capture rule define a pin as a span containing one complete named unit, possibly over-capturing others. The multi-unit declaration is the complementary case: the *named* object is a run of consecutive complete units, and completeness is asserted at both endpoints. The precedent chain is stated in the text itself (r3 repair 1(b) → r4 repair 5 → r5 repair 1(b)).

**CONDITIONALITY:** Both endpoint units must be complete, and S0.2 conditions 1–4 are still owed for the named run. This declaration licenses the span shape; it does not discharge the pin gate.

**RESOLUTION TRACE:** r4 repair 5 (2473) and r5 repair 1(b) (2652). Destination of both row texts is the S0.2 `(PINS)` table (shard 1); the convention is homed here.

**TEETH:** S7 pin gate conditions 1 and 4 (structural completeness and containment).

---

### EFF.T2.49  [table]

**CANONICAL STATEMENT:** `[TABLE — the r4 pin-derivation ledger; delimiter lines verbatim, counts re-run at compilation]`

| Pin | Named source unit (r4 designation) | First delimiter | Last delimiter |
|---|---|---|---|
| `HE6-SLOT-SEAM` | LEMMA HE6-0″ (THE SLOT LEMMA at (T1)/(T2) POINTS), statement and proof | `> **LEMMA HE6-0″ [r1, R5/F6] (THE SLOT LEMMA at (T1)/(T2) POINTS — the form` | `> restatement.**` |
| `HE3-DEF1` | DEFINITION 1 together with its attached [r2] CONSTRUCTION PIN | `> **DEFINITION 1 (the stage resolvent and its label set).**` | `not see it.]**` |
| `HE3-A-PROOF` | the proof unit belonging to THEOREM HE3.A (pair recorded inside r4 repair 3) | `### S6.3 PROOF OF THEOREM HE3.A` | `leaf's history, so THEOREM HE3.A is proved. ∎` |
| `HE3-R8-2` | the complete dated-correction unit | `### Dated correction (2026-08-12, post-R8) — R8-2: the unramified branch is repaired by split-component summation` | fixed by S0.2's boundary rule |
| `HE3-R8-3` | the complete dated-correction unit | `### Dated correction (2026-08-12, post-R8) — R8-3: the D′ = 1 case is direct` | fixed by S0.2's boundary rule |
| `HE3-R8-4` | the complete dated-correction unit | `### Dated correction (2026-08-12, post-R8) — R8-4: piecewise definition of ramified label classes` | fixed by S0.2's boundary rule |
| `HE3-R8-5` | the complete dated-correction unit | `### Dated correction (2026-08-12, post-R8) — R8-5: HE3-0 provenance correction` | `been updated to cite it.` |
| `HE6-PEEL-CONVENTION` | the HE6 §S1 CONVENTION [r1] on \(f\) (separability, \(\Phi'\nmid f\), and the original-key peel) | `> **CONVENTION [r1] (the two standing hypotheses on f — R2/F2 and R6/F7).**` | `> the peel is cleaner and is what is adopted.)` |
| `HE7-REF-TERM` | LEMMA HE7-8 ((REF-TERM)), statement and proof | `> **LEMMA HE7-8 ((REF-TERM) — α-refine chains are FINITE, characteristic-free).**` | `μ₂ ≥ 2 this makes disc f_S = 0. ∎` |

The designation correction that produced the four R8 rows is the round's own:

> “`grep -ic redline HE3_PROOF_2026-08-08.md` → **0**: the word never occurs in the source, and the source writes `R8-2`…`R8-5` with a hyphen, not `R8.2`…`R8.5`.”

**DERIVATION:** `[VERIFICATION RECORD]` Each pin is derived from a consumption, then closed by a delimiter pair: `HE6-SLOT-SEAM` by the adjudication of EFF.T2.47; `HE3-DEF1` because “The master consumes the construction and its type-invariance in three places” (S1.5's `(RES-FACT)`, S1.6's `(FRAME)`, and S1.6's frame-invariance sentence), which sit in the `[r2]` CONSTRUCTION PIN outside DEFINITION 1's blockquote; the R8 rows by their actual source designation; `HE6-PEEL-CONVENTION` and `HE7-REF-TERM` by the two consumptions r4 found outside every span (EFF.T2.55). Every delimiter line above was re-searched at compilation with exact-line matching and returned **1** in its named file (§3, part A).

**CONDITIONALITY:** Quoting a pair discharges S0.2 conditions 2 and 3 only; conditions 1 and 4 remain the S7 gate's work (EFF.T2.51). `HE3-R8-2`/`-3`/`-4` have a quoted **first** delimiter only. The pin **inventory count** stated by this round (29) is superseded to 37.

**RESOLUTION TRACE:** r4 repairs 1, 3, 5, 6 and 13 (2299–2304, 2398, 2470–2477, 2486–2498, 2578–2590). Destination of the `(PINS)` rows is S0.2 (shard 1, EFF.T2.03; XREFs X02, X03, X06–X09, X12, X13, X23).

**TEETH:** S7 pin gate (existence, uniqueness, ordering, containment); the standing S7 consumption sweep.

---

### EFF.T2.50  [table]

**CANONICAL STATEMENT:** `[TABLE — the r5 pin-derivation ledger; delimiter lines verbatim, counts re-run at compilation]`

| Pin | Named source unit (r5 designation) | First delimiter | Last delimiter |
|---|---|---|---|
| `HETOW-KEY-BRIDGE` | LEMMA HETOW-2 (composed key = key-family member up to an above-line perturbation), statement and proof | `> **LEMMA HETOW-2 (the composed key is a key-family member up to an` | `covers w = 0). ∎` |
| `HE7-PERT-TRANSPORT` | LEMMA HE7-12 (SLOT-DOMINATION) and LEMMA HE7-13, statements and proofs | `> **LEMMA HE7-12 [r2] (SLOT-DOMINATION — the §S5 package survives every` | `by one block (§S5.5), leaving the same conclusion for f_S′. ∎` |
| `HE6-LIFT-1L` | LEMMA HE6-1L ((LIFT), corrected) with its [r2] record, RIDER and non-propagation boxes | `> **LEMMA HE6-1L [r1; display corrected [r2], PE2 F-1] ((LIFT), corrected =` | `> q(0) = q(1) = 0; (3,1,2): T(1) = ∅), per PE2 F-1.` |

The reconciliation directive attached to the third pin is:

> “The source defines the ratio in the inverse direction from this master: `η_θ^{q(k)} := res(ϖ(θ)^k/n(k)(θ))`, with the RIDER's evaluation "ϖ(θ)^k/n(k)(θ) = (θ^{e₁}π^{−h})^{q} = η_θ^{q}". This master's `(Q-DEF)` writes \(\operatorname{res}(n(k)(\xi)/\varpi(\xi)^k)=\eta_\xi^{-q(k)}\), the reciprocal of the same nonzero element of \(K\), so the two agree on \(q(k)\) with no sign convention left free; the minus sign of `(HE6-SEAM)` is the same one LEMMA HE6-0″ `[r2]` corrected. The pin is declined as the supplier of a per-\(A\) slot law (r4 repair 1); it is consumed only for \(q(k)\), for the `(LIFT)`/`(OCC)` reachable set, and for the RIDER's universality of the twist.”

**DERIVATION:** `[VERIFICATION RECORD]` Each of the three pins cures a consumption the r4 sweep missed: LEMMA HETOW-2 is “the unit S3.4's text names”; LEMMA HE7-12 is consumed by the new S1.8B; LEMMA HE6-1L is “the only source unit defining” \(q(k)\), and “leaving the definition of a symbol that appears in a displayed theorem hypothesis outside every span … is exactly what S0.2's restored no-unpinned-material clause forbids.” The defining line inside the third span, `> where η_θ^{q(k)} := res(ϖ(θ)^k/n(k)(θ)) is the RIDER's fixed normalizer`, re-verified at 1 (§3, part A). All six delimiter lines re-verified at 1.

**CONDITIONALITY:** Same as .49: pairs discharge conditions 2–3 only. The inventory count this round states (32) is superseded to 37. The `(Q-DEF)` reconciliation is a reading directive at the pin, not an amendment to either text: “No pinned display is asserted to be wrong” is r4 repair 9's formulation of the same discipline.

**RESOLUTION TRACE:** r5 repairs 1(a), 1(b), 4(b) and 8 (2645–2657, 2774–2783, 2892–2898). Destination of the `(PINS)` rows is S0.2 (shard 1, EFF.T2.03; XREFs X14, X24, X30).

**TEETH:** S7 pin gate; the standing S7 consumption sweep; the HE6 seam/sign gate (the `(Q-DEF)` direction).

---

### EFF.T2.51  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — what a quoted delimiter discharges, and the two directional errors of the r4 inventory]`

> “Both delimiter lines of every pin **re-derived in this repair** are quoted byte-exactly from the accepted source and were verified by exact-full-line search on 2026-08-12: each occurs exactly once in its file, and each begin precedes its end. The remaining pins of `(PINS)` are description-only: their first and last delimiter lines are not quoted in this note, and the S7 pin gate must re-derive them from the description before checking conditions 1–4. Quoting a delimiter pair discharges conditions 2 and 3 in advance; it does not discharge conditions 1 and 4, which remain the gate's work.”

> “**Over-count:** `HE3-R8-2`, `HE3-R8-3` and `HE3-R8-4` were listed as carrying quoted pairs, but r4 repair 6 quotes only their **first** delimiter and fixes each **last** delimiter by S0.2's boundary rule ("the unit ends immediately before the next `###` unit of equal rank"), explicitly excepting only `HE3-R8-5`. A single quoted delimiter discharges condition 2 for that line alone; it discharges neither condition 3 nor condition 2 for the unquoted endpoint. **Under-count:** `HE3-A-PROOF` was omitted although r4 repair 3's own verification remark quotes and grep-verifies both of its delimiters, `### S6.3 PROOF OF THEOREM HE3.A` and `leaf's history, so THEOREM HE3.A is proved. ∎`.”

**DERIVATION:** `[BOOKKEEPING CORRECTION]` The first quotation replaces r3 repair 1's unrestricted claim, which “is false for 22 of the then-27 pins and would let a reader believe the S7 pin gate is already discharged.” The three-way taxonomy (quoted pair / first-only / description-only) is then forced by the discharge rule: a pin's taxonomy class is exactly which of conditions 2 and 3 are pre-discharged.

**CONDITIONALITY:** **The totals are superseded.** r4's “13 of 29” and r5's “14 of 32 … 14 pairs + 3 first-only + 15 description-only = 32” are historical; the accepted taxonomy is the acceptance record's “\(20+4+13=37\)”, reached through r7 repair 2, r10 repair 1, r11 repair 1 and r12 repair 1. What survives from this range is the discharge rule and the two named directional errors, which later rounds do not revisit.

**RESOLUTION TRACE:** r4 repair 7 (2502–2508) superseded within this shard by r5 repair 3 (2742–2758); totals superseded downstream (shards 3–5) and by the acceptance record (shard 6). The destination of the replaced sentence is r3 repair 1's paragraph (shard 1 range), which carries no shard-1 unit.

**TEETH:** S7 pin gate conditions 1–4; the pin-sweep leg of the acceptance gate.

---

### EFF.T2.52  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective "Honest status of the three (RANK) components": r4 repair 3's block with its second bullet replaced by r5 repair 1's two bullets]`

> “**Honest status of the three components.** Components one and two are derived above from the effective text; the four supporting facts the note previously lacked — the split's strict decrease, the peel's degree drop, the child jump's degree non-increase via `(TEST)` composed with `(MASS)`, and the recentering's degree/mass preservation via \(\deg L_k(s)<D\) — are now displayed with their sources. Component three is **not** derived: `(SEC-RANK)` is a named carrier hypothesis. Its instance status:”

> “- **Level one** (S3.1/S3.2): supplied inside the existing pin `HE3-A-PROOF`, whose §S6.3 stage-α passage reads "Termination: each refine strictly increases the floor λ and dv-heights are bounded by the leaf's window (GENHN-3(a)), so the chain is finite" — an \(\mathbf N\)-valued instance of `(SEC-RANK)` (window bound minus current floor).”

> “- **Level two at a DEFINITION HE6-1 key** (S3.3): supplied by **LEMMA HE7-8 ((REF-TERM))**, pinned as `HE7-REF-TERM` (r4 repair 13). HE7-8 is stated at the base key \(\Psi\) of the chain and quantifies over the whole chain \(\Psi^{(0)}=\Psi\), \(\Psi^{(j+1)}=\Psi^{(j)}-w_j\), which is S3.3's actual configuration: the record's key is \(\Psi_{\lambda,r}\), a DEFINITION HE6-1 member, so the lemma applies with no transfer. It discharges `(SEC-RANK)` in its well-foundedness form rather than by an \(\mathbf N\)-valued rank: it refutes infinite α-refine chains directly. Accordingly `(SEC-RANK)` is stated above with \(W_{\mathcal C}\) merely well-founded, not \(\mathbf N\); an instance may discharge it either way.
> - **Level two at the composed key** (S3.4/S3.5): **not** supplied by instantiating HE7-8, whose hypothesis names the chain's base key and whose base key here would have to be \(\Phi_2=\Psi_{\kappa_2,\widetilde r}-w\). It is supplied instead by the clause of each record's own already-listed pin that states the conclusion at \(\Phi_2\): `HETOW-A` clause (ii), "a repeated K₂-rational linear factor at integer λ₂ is a finite α-refine chain (LEMMA HE7-12/13, HE7-8)", under THEOREM HETOW.A's preamble "every clause below reads at the corrected key"; and `GENTOW-4-A` clause (iii), "a repeated K2-rational linear factor at integer lambda2 is a finite alpha-refine chain (HE7-12/13, HE7-8; the chain re-reads f itself through (ii) at each refined key, available by LEMMA HE7-12 with W + w)", stated of "f_S at the datum (kappa2, rtilde) with key Phi2". Both clauses cite LEMMA HE7-8 and LEMMA HE7-12 by name, so `HE7-REF-TERM` and `HE7-PERT-TRANSPORT` (repair 1 of r5) are listed at both records as the named supporting units; the transfer from \(\Psi_{\kappa_2,\widetilde r}\) to \(\Phi_2\) is performed inside those theorems' proofs, by `HETOW-KEY-BRIDGE` and by `GENTOW-4-1` clause (c), and is not performed by this master.”

> “No instance is claimed to discharge `(SEC-RANK)` by an argument this master reproduces.”

**DERIVATION:** `[ASSEMBLED — the re-route argument]` The re-route is justified by type, not by convenience:

> “`(SEC-RANK)` asks, of a state, for a well-founded \(W_{\mathcal C}\) and a \(\sigma_{\mathcal C}\) strictly decreasing at every **product-\(1\) linear recentering**. By S1.8 that transition is the branch \(e'\deg r'=1\), i.e. "\(e'=1\) and \(r'=Y-s\) for some \(s\in K\)" — integer slope, linear residual factor. At a level-two state of S3.4/S3.5 that is exactly the configuration the two pinned clauses quantify over, "a repeated K₂-rational linear factor at integer λ₂", and each asserts of it, **at the composed key**, that the α-refine chain it generates is FINITE”

and

> “Finiteness of every chain of the recentering relation **is** well-foundedness of that relation, and a well-founded relation carries an ordinal rank function; that rank is a legitimate \(\sigma_{\mathcal C}\) into a well-founded \(W_{\mathcal C}\), which is precisely the latitude r4 repair 3 wrote into `(SEC-RANK)` ("\(W_{\mathcal C}\) merely well-founded, not \(\mathbf N\)"). No step of this reads HE7-8 at a key other than the one its host theorem declares.”

Four source lines carry the two composed-key clauses and their key declarations; all four re-verified at 1 (§3, part A), and all four “lie strictly inside the existing spans `HETOW-A` and `GENTOW-4-A` respectively.”

**CONDITIONALITY:** `(SEC-RANK)` is a carrier hypothesis: “any instance that cannot supply it does not instantiate HE7.A.” It is **not** an open obligation — the acceptance record states it “fences no read”. The level-one discharge is `\(\mathbf N\)`-valued; the level-two ones are well-foundedness-form. The master reproduces none of the three arguments.

**RESOLUTION TRACE:** r4 repair 3's closing block (2396–2401); its second bullet replaced in full by r5 repair 1's two bullets (2659–2666), with the superseded string landmark-verified at 1 under bound 2608 (re-verified §3, part B). Statement HOME of `(SEC-RANK)` and `(RANK)` themselves is base S1.8 (shard 1, EFF.T2.26 and .71). Reaffirmed by the acceptance record's `(SEC-RANK)` bullet.

**TEETH:** S7 Pass 2 “a transition that is well-founded but fails to preserve roots, which must be rejected”; the refinement-termination tooth; the composed-key transport tooth.

---

### EFF.T2.53  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — effective clause-5 discharge routing (r5 repair 2's replacement of r4 repair 2's “Instance consequence”)]`

> “**Instance consequence.** The child-jump branch of the trigger is precisely LEMMA HE6R1-3's hypothesis, so r3 repair 4's cited discharge now discharges a case the theorem states. The recentering branch is **fenced at level one** by repair 4 as `(MP1)`, and is discharged at level two by S1.8B below — by LEMMA HE7-12(c)'s transport of LEMMA HE6R1-3 to the recentered key, **not** by the `[r3]` interleaving clause of LEMMA HE7-8, which asserts only that a mid-chain peel occurs and drops \(\mu_2\) by one and supplies no item of the input suite. That clause keeps exactly the role r3 repair 5 gave it: the \(\nu=1\) degenerate guard and the pigeonhole bounding how many peels may interleave one chain.”

The withdrawal is signed rather than patched:

> “**The `[r3]`-clause route is withdrawn, not defended.**”

**DERIVATION:** `[SUPERSESSION WITH REASON]` The r4 route failed on two independent legs, both recorded: HE7-8's `[r3]` clause asserts only “(a) that it happens and (b) that mass drops by one — precisely the two facts the master proves IN-master”, so it supplies no item of the suite; and HE6R1-3's hypothesis is the unrecentered \(\Psi\), its proof consuming “Every root ξ of g₀ is a root of Ψ = Ψ_{λ,r}, hence a level-2 point with level-1 label (λ, r) (LEMMA HE6-1)”. The replacement route is the S1.8B derivation, whose statement HOME is base S1.8.

**CONDITIONALITY:** Level-one recentered-key peels remain `(MP1)`-conditional after acceptance. The level-two discharge is conditional on the state's increment heights satisfying LEMMA HE7-12's hypothesis, which S1.8B step 1 supplies from `(REF-HT)` — itself installed later (r6–r8, shards 3–4), so this round's step 1 is the pre-`(REF-HT)` form of that argument.

**RESOLUTION TRACE:** r4 repair 2's closing paragraph (2331) replaced in full by r5 repair 2 (2682–2688); the superseded paragraph landmark-verified at 1 under bound 2608 (re-verified §3, part B). Statement HOME of clause 5, the suite and S1.8B is base S1.8/S2 (shard 1, EFF.T2.23, .68, .75). Reaffirmed by the acceptance record's `(MP1)` bullet.

**TEETH:** S7 reducible/recentered-key boundary attacks; Pass 2's sub-threshold and several-boundary-factor rows; the degenerate-guard tooth.

---

### EFF.T2.54  [fence]

**CANONICAL STATEMENT:** `[VERBATIM — the reading directive added at pin GENTOW-4-A]`

> “The span is THEOREM GENTOW-4.A in GENTOW4 §S3. Its clause (ii) carries the parenthetical "top coefficient NOT monic — the partial-side signature", which a later dated correction outside this span declares superseded: `### [TOWERRAT2-C annex, 2026-08-10] Dated correction: the 4.A(ii)` / `### "top coefficient NOT monic" parenthetical SUPERSEDED`. **The 2026-08-10 TOWERRAT2-C correction governs.** This master consumes from clause (ii) only \(\mu_2^*=\sum_{\lambda_2>T_2}L_{\lambda_2}\) and \(\deg f_S=D_2\mu_2^*\), never the top-coefficient parenthetical; S3.5 states the complementary restraint, "No whole-polynomial monicity or length hypothesis is transferred to \(f_S\) without proof". The pin is unchanged; the note is a reading directive.”

**DERIVATION:** `[SUPERSESSION NOTICE AT A PIN]` The practice is r3 repair 3's, extended: “r3 repair 3 established the practice of noting a competing or superseded display at the pin, and applied it at `HE6R1-1` and `HETOW-LABELS`. The same configuration exists at `GENTOW-4-A` and was left unnoted.” Both annex heading lines re-verified at 1 in `GENTOW4_PROOF_2026-08-09.md` (§3, part A).

**CONDITIONALITY:** The directive changes no span and no count; it fixes which sub-clause content may be read from a span that over-captures a superseded parenthetical. It is a declination, not a consumption — a distinction r12 repair 3 later makes general (“Consumption, not citation, is the gated relation”).

**RESOLUTION TRACE:** r4 repair 12 (2560–2566). Destination is the `(PINS)` row for `GENTOW-4-A` (shard 1, EFF.T2.03 and .81, XREF X35), neither of which carries the directive text.

**TEETH:** S7 GENTOW4 perimeter gate; the mixed-multiplicity/monicity exclusion tooth; the pin-note directive coherence audit run at pass 2 of record.

---

### EFF.T2.55  [table]

**CANONICAL STATEMENT:** `[TABLE / ASSEMBLED — the consumption sweep re-run and recorded at r5, with its residues]`

> “**The sweep, re-run and recorded.** So that the S7 gate can check rather than repeat it, here is the enumeration behind the claim, with its residues:”

| Consumption examined | Disposition recorded at r5 |
|---|---|
| LEMMA HETOW-3 | consumed by S3.4's “The full-side identity gives \(f_S=f\)”, covered inside `HETOW-A` clause (i), which states “f_S = f with μ₂ = μ₁/(e₂f₂) (HETOW-3)” |
| LEMMA GENTOW-4.1 | pinned as `GENTOW-4-1`, its clause (c) carrying the partial-tower transport |
| LEMMA HE7-13 | now inside `HE7-PERT-TRANSPORT` |
| DEFINITION HE6-1 | inside `HE6-FAMILY` |
| GENHN-3(a) | named only inside the sentence r4 repair 3 quotes from within `HE3-A-PROOF`, hence internal to a pinned span |
| HE3's bracketed `[r1-N1]` three-consecutive-slope supplement | “named by r4 repair 4(c) only in order to **decline** it, and a declination is not a consumption” |

> “This enumeration is recorded, not asserted complete; the gate re-runs it.”

**DERIVATION:** `[SWEEP RECORD]` The sweep exists because r4's own claim that exactly two consumptions lay outside every pin was falsified by the r4 pass: “at least two more remain, one of them named in the master's own instance text.” The cure is two-sided — pin the uncovered units (EFF.T2.50) and record the enumeration so the standing S7 check installed by r4 repair 13 (“Also enumerate every source display the master text quotes, names, or leans on … A consumption outside every span fails the gate”) can verify rather than repeat it.

**CONDITIONALITY:** Explicitly incomplete-by-declaration. The census of cured consumptions moves within this range from “Two consumptions were cured this way at r4” to “Four consumptions have been cured this way”, and downstream to **ten** at acceptance; the sweep itself is re-run at r10 repair 1(g), r11 and r12 repair 1(g), which reaffirm these six residues unchanged.

**RESOLUTION TRACE:** r5 repair 4 (2801–2802); the two superseded count sentences (S0.2's and r4 repair 13's opening) are replaced at 2785–2799 and landmark-verified at 1 under bound 2608 (re-verified §3, part B). The S0.2 sentence's destination is base S0.2 (shard 1, EFF.T2.03).

**TEETH:** the standing S7 consumption sweep (the tooth this unit is the answer to); S7 pin gate.

---

### EFF.T2.56  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the per-record Source-pin discipline and the r5 justification map]`

> “Rather than amend three lines and leave the reader to compose four rounds of edits, all five lines are set here in final form. Each supersedes every earlier setting of that line”

> “Justifications, one per addition. **S3.1/S3.2 `HE6-LIFT-1L`:** \(q(k)\) of `(Q-DEF)`, consumed by S1.2's `(HE6-SEAM)` and restated by S3.2's print-frame read, is defined only there (repair 4). **S3.2 `HE3-A-PROOF`:** r4 repair 3 routes S3.2's `(SEC-RANK)` to the stage-α termination clause inside that span. **S3.3 `HE7-PERT-TRANSPORT`:** S1.8B's level-two recentered-key discharge runs through LEMMA HE7-12(c) at every level-two record, S3.3 included. **S3.4 `HETOW-KEY-BRIDGE`:** S3.4's text names LEMMA HETOW-2 by name. **S3.4/S3.5 `HE7-REF-TERM`:** `HETOW-A`(ii) and `GENTOW-4-A`(iii) both name LEMMA HE7-8 in the clause the records consume. **S3.4/S3.5 `HE7-PERT-TRANSPORT`:** the same two clauses name LEMMA HE7-12, and S1.8B applies at these records too. **S3.4/S3.5 `HE7-MIXED-13P`:** clause 4 demands side and label blocks whenever \(P_2\) has at least two sides, and ANNEX-LEMMA HE7-13′ is their supplier. **S3.4/S3.5 `HE6R1-3`:** the clause-5 peel at \(\Phi_2\), available there by `HETOW-KEY-BRIDGE` and `GENTOW-4-1`(c) respectively; S3.4's standing restraint "Any key-boundary contribution is handled by T2.KEY-BOUNDARY, not by a purported single \(\Phi_2\)-peel" is untouched and continues to govern the **proper-gcd** case, which routes to S1.9 — `HE6R1-3` is listed for the exact-division case \(\Phi_2\mid f\) that clause 5 now states. **S3.5 `HE6R1-2`:** S3.5's text consumes it by name ("HE6R1-2 gives a constant \(c_g=dv_2(g(\xi))\)").”

**DERIVATION:** `[PER-RECORD DISCIPLINE]` The finding repaired is that “no record's declared pin set currently instantiates the master's full hypothesis suite after r4”, because r4 repair 13 “rewrote three of them and left three holes”. The discipline installed — each record's Source-pin line must list every pin that record's own consumptions require, and each addition must be justified by the consumption it covers — is what later rounds cite by name (“Under r5 repair 6's own per-record discipline …”, “exactly as r7 repair 5 says of its own four”).

**CONDITIONALITY:** **The five line settings are superseded**, in this order: r7 repair 5 adds S1.8C's four pins to the three level-two lines; r10 repair 1(f) adds `HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-ACCOUNT` to all five; r11 repair 1(e) adds `HE6-BETA-GUARD` to the three level-two lines; r12 repair 1(f) adds `HETOW-KEY-BRIDGE-C-A` to S3.4 and S3.5. The r5 wording “set here in final form” is therefore historical. What survives is the discipline and the justification map above, with **one justification superseded in place**: r6 repair 6(b) (shard 3) replaces the S3.4/S3.5 `HE7-PERT-TRANSPORT` justification quoted above by

> “**S3.4/S3.5 `HE7-PERT-TRANSPORT`:** the same two clauses name LEMMA HE7-12, and S1.8B applies at these records after the single composition its scope clause displays — \(W\leftarrow w+W\), with \(w\) the wrap perturbation supplied by `HETOW-KEY-BRIDGE` resp. `GENTOW-4-1`(c) and the fold by LEMMA HE7-12(d) — so that the chain is read at \(\Psi_{\kappa_2,\widetilde r}\), a DEFINITION HE6-1 key, and not at \(\Phi_2\).”

None of the other nine justifications is withdrawn by any later round.

**RESOLUTION TRACE:** r5 repair 6 (2838–2866); each of the five superseded prior settings landmark-verified at 1 under bound 2608. Line settings superseded in shards 3 (r7 repair 5, 3440–3468), 4 (r10 repair 1(f)) and 5 (r11, r12). Destination of the lines is S3.1–S3.5 (shard 1, EFF.T2.33–.37).

**TEETH:** S7 pin gate; the standing consumption sweep; the five-instance perimeter gate.

---

### EFF.T2.57  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r6 round header; BOUNDARY UNIT, repairs homed in shard 3]`

> “*(Opus/Claude repair arm, against the r5 hostile pass of record `runs/comp13/T2P5_output.log` — 0 CRITICAL + 2 GAP + 4 minor; counter resets.)*”

> “**Verification protocol for this round.** Every source line quoted below was checked on 2026-08-13 by exact-full-line search (`grep -cFx`) in the named accepted source file, with the count and the source line number recorded at the point of use. No source file is edited by this round; the expected source edit count remains zero. Landmarks internal to this master are quoted from the **r5 effective text**, and their uniqueness is recorded in the form `sed -n '1,2912p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<string>'` → **1**; the line bound 2912 is the last line of the r5 round and excludes this round's own re-quotations, which would otherwise inflate every count.”

> “**What the two GAPs share.** Both are about something the note named instead of settling. G-1: S1.8B's hypothesis needs "refinement height = side slope", and the index \(k\) of \(L_k(s)\) is unbound at every site of the effective text, so the height was asserted rather than derived, and the offered corroboration cited a line that does not carry it. G-2: `(MP1′)`'s load-bearing negative — that no pinned unit certifies a recentered level-one key as carrying a level-one frame — was asserted without adjudicating the obvious pinned candidate. Repair 1 binds the height from the master's own `(SIDE-COUNT)`, `(SLOT-V)` and `(LIFT)`, as `(REF-HT)`. Repair 2 performs the adjudication; the candidate wins, the fence is **discharged**, and one of the three open obligations is retired.”

**DERIVATION:** `[ROUND RECORD]` The landmark-bound convention advances from 2608 (r4's last line) to 2912 (r5's last line) by the same rule stated at .46. The round's own preview names the two GAPs it answers and the disposition of each; both are executed in repairs homed at lines 2926–3296 (shard 3).

**CONDITIONALITY:** **Boundary unit.** Only lines 2916–2925 are homed here; r6 repair 1 (`(REF-HT)`) begins at line 2926 and is compiled in shard 3, as are repairs 2–7 and the r6 counter. The preview's claim that `(MP1′)` is retired is executed there and confirmed by the acceptance record. This round's counter reset is superseded to 2/2.

**RESOLUTION TRACE:** source lines 2916–2925; the round's repairs and counter lie at 2926–3296 (shard 3).

**TEETH:** S7 acceptance gate; the r5 hostile pass of record.

---
### EFF.T2.58  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r6 round record (counter; this round's header is homed at EFF.T2.57)]`

> “r6 folds repairs for both GAPs (G-1P5, G-2P5) and all four minors (m-1P5 … m-4P5) of the r5 hostile pass of record, plus the four recorded nits. Its substantive content is two objects. First, `(REF-HT)`: the refinement height of the product-\(1\) recentering is bound to the side's own slope, derived from `(SIDE-COUNT)`, `(SLOT-V)` and `(LIFT)` rather than named, so that S1.8B's use of LEMMA HE7-12 no longer rests on an identification the master never made; the r5 claim that two independent textual legs carried it is withdrawn, and the source display is re-cited to `HE7_PROOF_2026-08-08.md`:924, the line that states the height, and demoted from a leg to a corroboration. Second, the `(MP1′)` adjudication: the r5 negative is withdrawn, and the assertion that a recentered level-one key reads over a level-one frame is DISCHARGED in the new S1.8C from four pins already on both level-one records' lines”

> “**Two named obligations are open**, both at level one: `(LB1)` for clause-4 block construction, and `(MP1)` for the clause-5 peel at a recentered key. r5's counter recorded three; that sentence is r5's own record of r5 and is left standing as such. The third, `(MP1′)`, is retired by repair 2 above.”

> “**The clean-pass counter is RESET to 0 of 2.**”

**DERIVATION:** `[ROUND RECORD]` The obligation count falls from three to two by repair 2's discharge, not by narrowing: the retired obligation's content becomes S1.8C, a supplied consequence of four already-listed pins. The counter reset follows S7's rule, quoted by the counter.

**CONDITIONALITY:** This round's own claim “No theorem-statement change is made by this round” is **superseded in substance** by r7's counter, which books `(REF-HT)`'s (RISE) clause as exactly such a change; the r6 sentence is left standing as r6's record of r6. The counter is superseded to 2/2. The two-obligation set survives to acceptance.

**RESOLUTION TRACE:** source lines 3285–3293; header at 2916–2925 (shard 2, `.57`); superseded in substance by r7's counter (3499–3509) and as to status by the acceptance record.

**TEETH:** S7 acceptance gate; the r5 hostile pass of record.

---

### EFF.T2.59  [lemma]

**CANONICAL STATEMENT:** `[ASSEMBLED — the effective derivation of (REF-HT): r6 repair 1(a) as amended by r7 repair 1(a)-(c). The (REF-HT) display itself is homed at base S1.8 (shard 1, EFF.T2.19); what is homed here is its derivation and the withdrawals it rests on.]`

> “The recentering at this branch is a REFINE step, and this master stipulates of a refine step both that it raise the key's value on the class it refines and that its increment sit at the side's own slope — the second a consequence of the first, derived below:”

> “The two clauses of `(REF-HT)` are not independent stipulations: (HT) is forced by (RISE), and that forcing uses master data only. (RISE) itself is stipulated, and its status is recorded at the end of this passage.”

> “Every root \(\rho\) of the class being refined satisfies \(d(\Phi(\rho))=\lambda\): by S1.7 clause 4 "the classes associated with the distinct \(r'\) are disjoint and exhaust the roots belonging to the side", and the roots belonging to side \(\lambda\) are exactly the \(DL_\lambda\) roots with \(w_\rho=\lambda\), by `(SIDE-COUNT)` as derived in the proof of clause 1. The increment satisfies \(\deg L_k(s)<D\) (S1.4) and the block's roots lie in \(\operatorname{Pt}\) (S1.5, "Its roots form a designated Galois-stable class contained in \(\operatorname{Pt}\)"), so `(SLOT-V)` applies to the increment at those roots and `(LIFT)` gives
> \[
> d\bigl(L_k(s)(\rho)\bigr)=h\bigl(L_k(s)\bigr)=k .
> \]”

> “If \(k\ne\lambda\), the two values \(d(\Phi(\rho))=\lambda\) and \(d(L_k(s)(\rho))=k\) differ, so the ultrametric inequality is an equality and
> \[
> d\bigl(\Phi_{\mathrm{new}}(\rho)\bigr)
> =
> d\bigl(\Phi(\rho)-L_k(s)(\rho)\bigr)
> =
> \min(\lambda,k)\le\lambda
> \]”

> “at every root of the class: at \(k>\lambda\) the value does not move at all, at \(k<\lambda\) it falls, and at \(k\le T\) it leaves the window. Only \(k=\lambda\) escapes the display, so **(RISE) forces (HT)**: a recentering that raises the key's value on the class it refines has its increment at the side's own slope and at no other height, and the index of \(L_k\) is thereby bound to the side datum. The implication is this master's own. The premise is not: (RISE) is a carrier assertion on the footing r4 repair 3 gave `(SEC-RANK)` — it is part of the root-preserving continuation assertions hypothesised by HE7.A, this master does not derive it, and any instance that cannot supply it does not instantiate HE7.A.”

Two consequences are recorded with the derivation:

> “First, `(OCC)` is now read at a determined height: the visible domain obligation for this transition is \(\lambda\in H_{\mathrm{lift}}(B)\), a legible integer-height demand precisely because \(e'=1\). Second, at \(e'\ge2\) the slope \(u'/e'\) is not an integer and no \(L_k\) sits at it; that is why the recentering branch is the product-\(1\) branch and the product-\(\ge2\) branch builds a child key instead.”

**DERIVATION:** `[MASTER-SIDE IMPLICATION]` Three master data compose: `(SIDE-COUNT)` fixes \(d(\Phi(\rho))=\lambda\) on the class; `(SLOT-V)` with `(LIFT)` fixes \(d(L_k(s)(\rho))=k\); the ultrametric equality-at-unequal-values then leaves \(\min(\lambda,k)\le\lambda\) at every \(k\ne\lambda\). Since (RISE) demands a value strictly above \(\lambda\), only \(k=\lambda\) survives. The direction of the implication is load-bearing: the derivation runs (RISE) ⇒ (HT) and never the reverse, which is what makes the level-one instance discharge non-circular (.60).

**CONDITIONALITY:** The implication is unconditional master-side; the premise (RISE) is a carrier hypothesis discharged per instance (.60). The `(OCC)` demand is at the determined height \(\lambda\). At \(e'\ge2\) the branch does not arise.

**RESOLUTION TRACE:** base S1.8 product-\(1\) sentence replaced by r6 repair 1(a) (2936–2967); necessity claim, display and case reading amended by r7 repair 1(a)–(c) (3315–3349); the same binding installed in the S2 clause-3 proof by r6 repair 1(b) (2969–2975). All four superseded strings landmark-verified at 1 under bound 3293 (§3, part B). Destination: base S1.8 and the S2 proof → shard 1, `.19` and `.31`.

**TEETH:** S7 Pass 1 pure-mathematics theorem gate; the finite-refinement/root-preservation attack; the sub-threshold-lift refusal (\(k\le T\) leaves the window).

---

### EFF.T2.60  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the “Honest status of (RISE)” map AT THE r8 STATE: r7 repair 1(c)'s two bullets with the level-one bullet replaced by r8 repair 1(a)–(b), plus r8 repair 1(d)'s non-circularity statement. Its two level-one passages are superseded by r9 repair 1 (shard 4) — see CONDITIONALITY; the level-two bullet, the assembly order and the non-circularity statement are effective as quoted.]`

> “**Honest status of (RISE).** Not derived by this master. Its instance status, recorded in the form r4 repair 3 used for `(SEC-RANK)`:”

**Level one** (effective, r8 repair 1(a)–(b)):

> “**Level one** (S3.1/S3.2): supplied at the instance's own refine step, inside the existing pins `HE3-A-PROOF` and — for S3.2's enlarged classes — `HE6-FAMILY` and `HE6-PROOF`. Both clauses are properties of that one step, and the step is exhibited before either clause is read. … That step is a recentering of this master's own form at an index its construction fixes and this master does not choose: at \(\ell=1\) DEFINITION HE6-1's family IS the family of these recenterings — `> monic of degree D″ := D′ℓd (each B_tΦ′^{ℓt} has degree < D′ℓd). For ℓ = 1` (`HE6_PROOF_2026-08-08.md`:209), `> this is HE3's recentered-key family enlarged in DEGREE; for ℓ ≥ 2 it is a` (210) — and that family's recipe puts the increment of the member indexed by \((\kappa,r)\) at the index's own height … At \((\ell,d)=(1,1)\) and \(r=Z-s\) that reads \(\Psi_{\kappa,Z-s}=\Phi'+B_0\) with \(u=\ell\kappa=\kappa\), \(\deg B_0<D'\), \(d(B_0)=\kappa\) and residue \(c_0=-s\): this master's \(\Phi-L_\kappa(s)\), at the family's own index \(\kappa\), with the recipe's standing \(\kappa>D'h=T\) placing it inside `(WINDOW)` before any clause of `(REF-HT)` is read. **No height is asserted of \(\kappa\) here, and none is needed to read the clause that follows.** (RISE) at that step is the passage's own conclusion, stated of \(\Phi''\) with no height in the reading.”

> “**(HT) at that same step**, on two grounds, neither of them the theorem's own (HT) clause. FIRST, reading no index at all. … At any index \(\kappa\ne\lambda\) the display leaves every root of the class at \(d=\min(\lambda,\kappa)\le\lambda\), so the class contributes nothing strictly above \(\lambda\), the sub-block does not travel, and the floor does not increase — which is not what the passage states of \(\Phi''\). Hence \(\kappa=\lambda\), and the step is \(\Phi-L_\lambda(s)\). This is this master's (RISE) \(\Rightarrow\) (HT) implication run AT the instance, on an instance-supplied premise whose reading used no height; it is not the theorem's (HT) clause imported to license that reading, and the direction of use is the safe one — the master's generality in \(k\) is INSTANTIATED here, not transferred. SECOND, and independently of the display: the passage forms its key at its own refine datum … so the member of DEFINITION HE6-1's family that the read uses at that node is the one indexed by \((\lambda,Z-s)\), whose increment sits at \(d=\lambda\) by the recipe above. This second ground is a **reading of the passage's index, not a quoted formula** … It is recorded as corroboration; the first ground carries the leg.”

**Level two and deeper** (r7 repair 1(c), unamended):

> “- **Level two and deeper** (S3.3, and S3.4/S3.5): supplied inside the existing pin `HE7-PERT-TRANSPORT`, whose LEMMA HE7-13 — `> **LEMMA HE7-13 [r2] (the strict slope increase along the refine chain —` (918), `> DERIVED, not assumed).** Let Ψ̃ = Ψ − W with W = 0 or as in LEMMA` (919) — states the level-two α-refine step with its increment at the node's own slope, `> s₂ ≠ 0). Let w be a (LIFT₂) polynomial at height λ₂ with residue s₂` (924), and derives the rise as that lemma's conclusion: `> Then EVERY root ρ of f_S has` (926), `>     dv₂(Ψ̃^{(1)}(ρ)) > λ₂    (possibly = ∞) ,                     (S5.8.2)` (928). LEMMA HE7-8, inside the pin `HE7-REF-TERM`, describes the same chain with the same convention, `> Ψ^{(j+1)} = Ψ^{(j)} − w_j with dv₂(w_j) = λ₂^{(j)} and` (1090). What these lines supply is the level-two carrier's own refine step, hypothesis-side — which is what an instance record needs and all it needs. They are NOT a derivation that a step must be this one”

> “The height binding that S1.8B Step 1 consumes at level two therefore rests on (RISE) as a carrier assertion discharged by these pins, together with this master's (RISE) \(\Rightarrow\) (HT) implication, and on no derivation of necessity. (RISE) is a carrier hypothesis, not a ledger obligation: it fences no instance read, and the open named obligations remain `(LB1)` and `(MP1)`.”

**Non-circularity** (effective, r8 repair 1(d)):

> “**Non-circularity, stated of the effective text.** The level-one discharge above establishes both clauses at the instance's own step and neither from the other: (RISE) is the passage's conclusion about \(\Phi''\), whose reading uses no height, and (HT) at that step follows at the instance from that conclusion through this master's own display, corroborated by the passage's index. S1.8C's configuration match invokes no clause of `(REF-HT)`, as r7 repair 4 rebuilt it and as the honest-status sentence now records.”

**DERIVATION:** `[HYPOTHESIS / INSTANCE DISCHARGE]` The r8 assembly order is the derivation: exhibit the instance's step first, as a member of DEFINITION HE6-1's family at the index that family's own recipe fixes; read (RISE) off the passage's conclusion with no height in the reading; then obtain (HT) at that step by instantiating the master's own min-rule display. Both level-one legs are inside pins already on both records' Source-pin lines, so no pin is added — “No Source-pin line is amended either: the three pins this round cites — `HE3-A-PROOF`, `HE6-FAMILY`, `HE6-PROOF` — already stand on both level-one records' lines”. Eleven source lines carry the two bullets; all re-verified at 1 (§3, part A).

**CONDITIONALITY:** **Two passages quoted above are superseded in shard 4 and are reproduced here only as the r8 state of the discharge.** r9 repair 1(a) (source 3689–3711) replaces the step sentence — the `\((\ell,d)=(1,1)\), \(r=Z-s\), residue \(c_0=-s\)` identification — because the family indexes its members by a \(\varpi\)-PRINT residue while this master indexes recenterings by the COHERENT digit; the effective form carries `(IDX-TWIST)` and is homed at shard 4. r9 repair 1(b) (3713–3739) replaces the height-ground passage by one that derives the step's height **and its digit** from the same rise; the effective form is likewise homed at shard 4, as is r8 repair 3's HE6 leg of the "(S3.1/S3.2)" scope. What survives r9 unchanged, and is effective as quoted here, is the **assembly order** — step exhibited first, (RISE) read with no height or index, both clauses derived at the instance — the level-two bullet, and the non-circularity statement. (RISE) is stipulated, never derived; the map records who supplies it, not a proof. The level-two lines are hypothesis-side descriptions, explicitly “NOT a derivation that a step must be this one”. The second level-one height ground is corroboration only, because the increment's height display belongs to LEMMA HE3-2, whose unit “is HE3 §S5 and lies inside no span of `(PINS)`”. The HE6 leg carries r6 repair 2's caveat: an \(\ell\ge2\) side with a repeated residual factor is routed to the product-\(\ge2\) branch and is not consumed here.

**RESOLUTION TRACE:** r7 repair 1(c) (3351–3357); level-one bullet and alternative-height sentence replaced in full by r8 repair 1(a)–(b) (3531–3545); non-circularity paragraph replaced by r8 repair 1(d) (3555–3561). Four superseded strings landmark-verified at 1 under bound 3509 (§3, part B). Destination: base S1.8's `(REF-HT)` passage → shard 1, `.19`, whose `DERIVATION` compresses this map to one clause. Reaffirmed verbatim in substance by the acceptance record's `(RISE)` bullet.

**TEETH:** S7 finite-refinement/root-preservation attack; the level-one `(RISE)` discharge tooth; the print/coherent and lift-choice mutants that later rounds add at the same step.

---

### EFF.T2.61  [lemma]

**CANONICAL STATEMENT:** `[ASSEMBLED — S1.8C, the (MP1′) adjudication and discharge: r6 repair 2's subsection as amended by r7 repairs 4 and 6 and r8 repair 1(c). The retirement statement is homed at base S1.8 (shard 1, EFF.T2.25); what is homed here is the adjudication that produces it.]`

The question settled:

> “When the level-one key beneath is itself a recentered \(\Phi''=\Phi'-L_\lambda(s)\), a prior question arises, and this subsection settles it: does a state read over \(\Phi''\) have a level-one frame at all?”

**What has to be supplied** (effective, r7 repair 6(a)):

> “For a state whose level-one key is \(\Phi''\), the level-one FRAME that S1.2–S1.7 are read over consists of (i) the same \((T1)/(T2)\) point set \(\operatorname{Pt}\); (ii) the same \(dv\); (iii) the same \(\varpi\); (iv) the same \(K\); (v) the same \(T=D'h\); (vi) DEFINITION HE6-1's test family over \(\Phi''\); and (vii) a \(\Phi''\)-development with its lower hull and its label read. That is the frame, and not an enumeration of everything S1.2–S1.7 demand: S1.3's normalizers and cocycle law, S1.4's full-height lift data, S1.5's `(WINDOW)` and `(RES-DEG)`, S1.6's `(FRAME)` and `(ORIGIN)`, and S1.7's seven proved test properties with `(ACCOUNT)` are demands on the RECORDS, and they reach \(\Phi''\) only as (vii) transports the records themselves.”

**The supplying text**, quoted from strictly inside `HE3-A-PROOF`:

> “> *Stage-α step.* If the read refines at (λ, s) (a residual root of
> > multiplicity m ≥ 2 — so the leaf is not decided at this node), then by
> > LEMMA HE3-2(b) the recentered key Φ″ has a polygon whose portion above
> > λ has length exactly m, the corresponding block of D′m roots is
> > S_{λ, Z−s} … and this block's
> > own labels are read at Φ″ …
> > Apply the inductive hypothesis to the sub-block: it is the
> > label-class of a multiplicity-m system over the SAME stage ring, with
> > the same (e₁, f₁), so its pieces compose into the dictionary as claimed.”

**The configuration match** (effective, r7 repair 4):

> “The passage's configuration contains this master's, exactly at the branch that recenters. "Refines at (λ, s)" with "a residual root of multiplicity m ≥ 2" is clause 3's repeated \(r'=Y-s\) with \(s\in K\); the slope at which the read refines is an integer here because \(e'=1\) forces \(\lambda=u'/e'=u'\), which is S1.8's product-\(1\) branch and is settled there independently of `(REF-HT)`; and nothing further is asserted of LEMMA HE3-2, whose own unit is HE3 §S5 and lies inside no span of `(PINS)`, so that only the lines quoted above are consumed”

**(i)–(v)**, the stage-data leg:

> “The passage places the refined system "over the SAME stage ring, with the same (e₁, f₁)". Each of (i)–(v) is a function of that datum and of nothing else.”

with `HE6-SLOT-SEAM`'s key-freeness quoted from inside its span — `> ξ be ANY point of K̄₀ satisfying (T1) and (T2). Then`, `> irreducible ψ of degree f₁); it never uses Φ′(ξ) = 0. ∎* **Codex PE1` — and the conclusion:

> “They are not "carried by" \(\Phi''\): nothing about them moves when the key does. That is why no pin was ever going to state them in the form `(MP1′)` demanded, and why the absence of such a pin was not evidence of a gap.”

**(vi)**, the family leg: the test data are chosen key-free (`> deg B_t < D′, dv(B_t) = (d−t)u and res(B_t(θ)/ϖ(θ)^{(d−t)u}) = c_t (and`), the assembly is a formula in the current monic degree-\(D'\) key (`>     Ψ_{κ,r} := Φ′^{ℓd} + Σ_{t<d} B_t·Φ′^{ℓt}  ∈ O[x],`), and

> “At \((\ell,d)=(1,1)\) the member \(\Psi_{\lambda,Z-s}=\Phi'+B_0\) IS the recentered key, \(B_0\) being the \(\varpi\)-frame form of \(-L_\lambda(s)\) under `(HE6-SEAM)`. A recentered level-one key is not a foreign object to HE6; it is one of HE6's own test polynomials.”

**(vii)** and the engine sentence (effective, r7 repair 6(b)):

> “What (vii) transports is the S3.1/S3.2 records, with the credit r1 repair 2 assigned them. … So what this passage carries to \(\Phi''\) is the HE3 leg — every hypothesis of THEOREM HE3.A, at the new key — while the universal test package and `(ACCOUNT)`, which are those records' HE6 leg, reach \(\Phi''\) through (vi) and through the HE6 paragraph below. The record transported is the composite HE3+HE6 discharge r1 repair 2 installed, and no more of it is claimed at \(\Phi''\) than is claimed at \(\Phi'\).”

**The HE6 record's leg**, quoted from inside `HE6-PROOF`:

> “> **This is HE3's LEMMA HE3-4 in full generality**, so HE3's THEOREM HE3.A
> > assembly (§S6.3 there: base read + stage-α + stage-CS + embedded genres) may
> > be run with HE3-4 replaced by THEOREM HE6.A — with the one caveat of §S7 for
> > histories containing an ℓ ≥ 2 side with a repeated residual factor.”

**Honest status** (effective, r8 repair 1(c)):

> “Derived master-side: the configuration match — which invokes no clause of `(REF-HT)`, resting instead on S1.8's own case split \(e'\deg r'=1\) and on \(e'=1\Rightarrow\lambda=u'/e'=u'\in\mathbf Z\) in lowest terms, as r7 repair 4 rebuilt it — the key-freeness of (i)–(vi) read off the pinned displays, and the composition of the passage with the S3.1/S3.2 substitutions. Consumed, not reproved: HE3's own inductive step, at HE3's own rigour, which S4.1 already grades … The adjudication does not claim the passage is beyond challenge. It claims something narrower and sufficient: the passage is the step without which THEOREM HE3.A is not proved at all, so a master that pins `HE3-A-PROOF` and consumes THEOREM HE3.A cannot simultaneously declare the frame that step reads over to be supplied by no pin.”

**What the discharge does NOT give:**

> “It does not touch `(MP1)`. Peeling a recentered level-one key still needs item 5 of the `(MID-PEEL)` input suite — the peeled key's certified orbit/\((e,f)\) decomposition — which requires \(\Phi''\) irreducible, asserted nowhere and the stated reason r4 declined `HE6-PEEL-CONVENTION` for that case. It does not touch `(LB1)`. And it is **relative**: it transports the S3.1/S3.2 records to \(\Phi''\) carrying whatever conditionality they carry at \(\Phi'\) … What is removed is the extra frame-level obligation, not the level-one fences.”

**Two reading directives:**

> “1. **Only the refined sub-block travels to \(\Phi''\).** The passage's own `[r1, F5]` bracket is explicit — "the above-λ blocks' labels are NOT readable at Φ″ — they are read at Φ′ (or at their own recenterings), where the induction reads them". … 2. **The discharge is invoked at the product-\(1\) branch and nowhere else.**”

**The retirement:**

> “**The name `(MP1′)` is retired.** r5 named the assertion (i)–(vii) as an obligation on the ground that "no pinned unit certifies" it. That ground is withdrawn: `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY` and `HE6-PROOF` certify it between them, and all four are already on both level-one records' Source-pin lines. The name is kept here only so that r5's text resolves — `(MP1′)` denotes (i)–(vii) — and it now denotes a consequence of the pins, not an obligation. No instance record carries it and no ledger item fences it.”

**DERIVATION:** `[ADJUDICATION WITH FOUR PINNED LEGS]` The negative that created `(MP1′)` (“no pinned unit certifies”) is tested against the obvious candidate and fails: `HE3-A-PROOF` carries the \(\Phi''\)-polygon, the \(\Phi''\)-label read, and the inductive application of THEOREM HE3.A to the sub-block over the same stage ring; `HE6-SLOT-SEAM` states its slot law with no key in it and its own correction record says the restatement exists so the law may be applied off the key; `HE6-FAMILY`'s recipe is key-free in its data and formulaic in its key, and identifies \(\Phi''\) as its \((\ell,d)=(1,1)\) member; `HE6-PROOF` licenses running HE3's stage-α with HE6's enlarged classes. Twenty-two source lines carry the four legs; all re-verified at 1 (§3, part A).

**CONDITIONALITY:** Relative, not absolute — the transport carries the records' existing `(LB1)`/`(MP1)` triggers unchanged. Consumed-not-reproved at HE3's own grade, which `(GRADE)` already minimises over (HE3 is capped at \(0/2\) at acceptance). The HE6 leg excludes the \(\ell\ge2\)-with-repeated-residual caveat. The two reading directives bound what may travel to \(\Phi''\).

**RESOLUTION TRACE:** r6 repair 2 (3007–3141), replacing r5 repair 2's `(MP1′)` subsection in full (both bounding strings landmark-verified at 1 under bound 2912); amended by r7 repair 4 (configuration clause, 3423–3431), r7 repair 6(a)–(b) (framing and engine sentence, 3477–3491), r8 repair 1(c) (honest status, 3547–3553), and r7 repair 3 (the stale `(MP1′)` disjunct in r5 repair 2's closing paragraph, 3405–3411). Consumption consequence: r7 repair 5 puts the four pins on the three level-two Source-pin lines, on the ground that S1.8C's closing sentence “puts a level-two state over that frame” — those line settings are superseded downstream (r10–r12) but the ground is not. Destination: base S1.8C → shard 1, `.25`. Reaffirmed by the acceptance record's `(MP1′)` sentence.

**TEETH:** the level-one frame-transport hostile tooth; S7 reducible/recentered-key rows; the print/coherent-frame tooth that r9 later adds at the same seam.

---

### EFF.T2.62  [lemma]

**CANONICAL STATEMENT:** `[VERBATIM — S1.8B's scope clause at a composed key (r6 repair 6(a)); destination base S1.8B, shard 1 EFF.T2.24]`

> “**Scope: entry at a composed key.** S1.8B is stated for a chain based at a DEFINITION HE6-1 key \(\Psi=\Psi_{\lambda,r}\). At S3.4/S3.5 the chain is based at the composed key \(\Phi_2\), which is not such a key, and entry costs one composition — performed by the records' own already-listed pins, not by this master. `HETOW-KEY-BRIDGE` gives \(\Phi_2=\Psi_{\kappa_2,\widetilde r}-w\) with \(\deg w<D''\) and "either w = 0 … or dv₂(w) > T₂", and `GENTOW-4-1` clause (c) gives the same at the partial tower. If \(w=0\), the base key IS a DEFINITION HE6-1 key and S1.8B applies literally. If \(w\ne0\), then \(w\) already satisfies LEMMA HE7-12's hypothesis at \(\Psi_{\kappa_2,\widetilde r}\), and Step 1 gives the same for each refine increment \(w_1,\dots,w_j\) by `(REF-HT)`; LEMMA HE7-12(d) folds the whole sum, so
>
> \[
> \Phi_2-W
> =
> \Psi_{\kappa_2,\widetilde r}-\bigl(w+w_1+\dots+w_j\bigr)
> \]
>
> is covered by ONE instance of clauses (a)–(c) at \(\Psi_{\kappa_2,\widetilde r}\). That is the composition `GENTOW-4-A`(iii) already displays as "available by LEMMA HE7-12 with W + w". Step 2 then runs unchanged, at \(\Psi_{\kappa_2,\widetilde r}\) and not at \(\Phi_2\).”

**DERIVATION:** `[ONE-CLAUSE COMPOSITION]` The seam repaired is that “S1.8B's own scope sentence excludes them and the composition is nowhere displayed”, while “Both bridge units ARE pinned … so the ingredients are present and the claim is true. What is missing is the one-clause composition”. The composition is a case split on the bridge's own disjunct (\(w=0\) or \(dv_2(w)>T_2\)) followed by LEMMA HE7-12(d)'s fold of \(w+w_1+\dots+w_j\) into a single application; the refine increments enter with their heights supplied by `(REF-HT)` (.59, .60). The reading is displayed by `GENTOW-4-A`(iii) itself as “available by LEMMA HE7-12 with W + w”.

**CONDITIONALITY:** The chain is read at \(\Psi_{\kappa_2,\widetilde r}\), never at \(\Phi_2\); the master performs no key transfer of its own. The \(w\ne0\) degree conjunct \(\deg w<D''\) is later re-derived master-side at r12 repair 1 (shard 5) after HETOW's C-A correction withdraws the source licence for it.

**RESOLUTION TRACE:** r6 repair 6(a) (3221–3231), appended to S1.8B at the anchor sentence landmark-verified at 1 under bound 2912; the corresponding justification sentence in r5 repair 6 re-pointed by r6 repair 6(b) (shard 2, `.56`). Destination: base S1.8B → shard 1, `.24`.

**TEETH:** the composed-key transport tooth; HETOW frame gate; the accumulated-degree tooth added at r12.

---

### EFF.T2.63  [table]

**CANONICAL STATEMENT:** `[TABLE — pin and inventory bookkeeping homed in this range]`

| Item | Effective operation at r6/r7 | Status now |
|---|---|---|
| `HE6-PROOF` delimiters | first `### S6.2 PROOF OF THEOREM HE6.A`, last `histories containing an ℓ ≥ 2 side with a repeated residual factor.`; the row description “the complete proof unit of THEOREM HE6.A” resolved to the `###` unit, ending before `### S6.3 Multiplicity ≥ 2 on an ℓ = 1 side (the stage-α node) is unaffected` | Effective; moves the pin from description-only to quoted-pair |
| `HE6-FAMILY` | booked as a **first-only** pin at its quoted first delimiter `> **DEFINITION HE6-1 (THE ENLARGED TEST FAMILY).** Let κ = u/ℓ ∈ ℚ in lowest` (`HE6_PROOF_2026-08-08.md`:201) | Effective |
| `HE6R1-3` row description | `LEMMA HE6R1-3` → `LEMMA HE6R1-3, statement and proof`, “bringing it into the form the r4/r5-era rows use”, because S1.8B consumes the lemma's proof through item (11) of LEMMA HE7-12's proof | Effective; unit unchanged, so condition 1 unaffected |
| Taxonomy | “Totals: 15 pairs + 4 first-only + 13 description-only = 32.” | **Superseded** to \(20+4+13=37\) |
| Pin count | 32, unchanged by r6, r7 and r8 (“no pin is added or removed”) | **Superseded** to 37 |

**DERIVATION:** `[BOOKKEEPING]` The `HE6-PROOF` pair is quoted because the S1.8C discharge leans on the closing paragraph of that span, so “the span's boundary is fixed here instead of being the gate's work”, following the practice r4 repair 6 set for `###`-headed units. `HE6-FAMILY`'s reclassification follows mechanically from r5 repair 3's taxonomy rule (.51 of shard 2): a round that quotes and grep-verifies a first delimiter must book the pin as first-only. Both delimiter lines and the `HE6-FAMILY` first delimiter re-verified at 1 (§3, part A); the two superseded totals sentences landmark-verified at 1 (§3, part B).

**CONDITIONALITY:** Counts are superseded downstream; the three per-pin operations are not. A first-only pin discharges S0.2 condition 2 for the quoted line alone; condition 3 remains the gate's work.

**RESOLUTION TRACE:** r6 repair 2's delimiter block (3118–3123), r6 repair 7(c) (3269–3277), r7 repair 2 (3369–3395). Destination of the rows and totals: base S0.2 and the S7 pin gate → shard 1, `.03` and `.42` (XREFs X11, X10, X27).

**TEETH:** S7 pin gate conditions 1–4; the pin sweep leg of the acceptance gate.

---

### EFF.T2.64  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r7 round record: provenance, protocol, GAP framing, counter]`

> “*(Opus/Claude repair arm, against the r6 hostile pass of record `runs/comp13/T2P6_output.log` — 0 CRITICAL + 1 GAP + 5 minor; counter resets.)*”

> “**What the GAP is, and what it is not.** The pass certified every positive leg of `(REF-HT)` — \(d(\Phi(\rho))=\lambda\) at every root of the class being refined, \(d(L_k(s)(\rho))=k\) uniformly in \(\rho\), \(e'=1\Rightarrow\lambda\in\mathbf Z\), the ultrametric case reading, and the exclusion of \(k\le T\) by `(WINDOW)` — together with the whole of the `(MP1′)` adjudication and retirement and the completeness of the two-legs withdrawal. What it refuted is one premise. The NECESSITY direction of `(REF-HT)` ran through "the recentering must raise the value on the class", and this master hypothesises no such thing”

> “**This round makes a theorem-statement change**, and one only: (RISE) joins the root-preserving continuation assertions hypothesised by HE7.A, and clause 3's product-\(1\) transition is thereby narrowed to the refine step at the side's own slope, with `(OCC)` read at \(\lambda\in H_{\mathrm{lift}}(B)\). A hypothesis is added; no case and no conclusion is added. r6's counter recorded "No theorem-statement change is made by this round"; that sentence is r6's own record of r6, left standing as such and superseded in substance by this paragraph.”

> “**Two named obligations remain open**, both at level one: `(LB1)` for clause-4 block construction, and `(MP1)` for the clause-5 peel at a recentered key. (RISE) is a carrier hypothesis, not a ledger obligation: it fences no instance read, and both instance families discharge it from pins already on their lines.”

> “**Landmark census for this round.** Sixteen master-internal landmark strings, on fifteen lines, each returning **1** … Eleven source lines, each returning **1** under `grep -cFx` … Six span delimiters re-verified at **1**”

> “**The clean-pass counter is RESET to 0 of 2.**”

**DERIVATION:** `[ROUND RECORD]` The round's shape follows from the pass's verdict: everything positive was certified, one premise refuted, so the cure “prices the premise instead of deriving it”. The statement-change booking is forced by S7's own accounting — a hypothesis added to the suite is a theorem-statement change even when no case or conclusion moves — and the round says so against its own predecessor's contrary sentence rather than silently amending it.

**CONDITIONALITY:** Counter superseded to 2/2. The statement change stands in the accepted text: the acceptance record lists `(RISE)` as one of the four standing conditionalities. The obligation set is final.

**RESOLUTION TRACE:** source lines 3297–3303 (header, protocol, framing) and 3497–3509 (counter). Its landmark census is re-run at §3, part B.

**TEETH:** S7 acceptance gate; the r6 hostile pass of record; the whole-round landmark census as its own audit tooth.

---

### EFF.T2.65  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r8 round header and GAP framing; BOUNDARY UNIT, repairs 2–4 and the counter homed in shard 4]`

> “*(Opus/Claude repair arm, against the r7 hostile pass of record `runs/comp13/T2P7_output.log` — 0 CRITICAL + 1 GAP + 2 minor, plus 2 recorded nits; counter resets.)*”

> “**What the GAP is, and what it is not.** The pass certified the whole of r7's architecture except its order of assembly at one instance. It certified that (RISE) \(\Rightarrow\) (HT) is the exact contrapositive of the min-rule display and is sound one way; that HE3's stage-α lines 1151/1152/1156 give (RISE) at level one and LEMMA HE7-13's 926/928 derive it at level two; that all four r7 withdrawals are orphan-free; that the statement change is hypothesis-only with all five instances pin-covered; and the whole of the strict assembly. What it refuted is the level-one discharge's assembly order. The master's product-\(1\) new key is \(\Phi_{\mathrm{new}}=\Phi-L_k(s)\) at an index \(k\) the display leaves free (S1.8, line 578, unamended by any round), while the passage's conclusion is about HE3's \(\Phi''\); r7's discharge read the second as the first without ever exhibiting the step that both are about, so the only visible route from the passage to the master's (RISE) ran through (HT) — the clause r7 derives from (RISE). Repair 1 rebuilds the discharge in the only order that is not a circle”

> “**Verification protocol for this round.** … No source file is edited by this round; the expected source edit count remains zero, and no pin is added or removed, so the expected pin count remains 32. No Source-pin line is amended either: the three pins this round cites — `HE3-A-PROOF`, `HE6-FAMILY`, `HE6-PROOF` — already stand on both level-one records' lines (S3.1, line 2858; S3.2, line 2859) and, since r7 repair 5, on the three level-two lines as well.”

One correction to the pass's own proposed cure is recorded, because the repair turns on it:

> “the report's one-sentence cure ("HE3's stage-α recenters at its own λ by construction") is **not** available as a quoted formula. The pinned span states the node's refine datum and names the key formed there; the increment's height is displayed only by LEMMA HE3-2, whose unit is HE3 §S5 and which r7 repair 4 fenced out of every consumption.”

**DERIVATION:** `[ROUND RECORD]` The circularity diagnosis is structural: the master's product-\(1\) display leaves \(k\) free, so identifying the passage's \(\Phi''\) with the master's \(\Phi_{\mathrm{new}}\) needs \(k=\lambda\), which is (HT) — the clause derived from (RISE). The only non-circular order therefore exhibits the instance's step independently of both clauses, which is what `.60` records.

**CONDITIONALITY:** **Boundary unit.** Lines 2926–3568 of this round comprise the header and repair 1 only; r8 repairs 2–4 and the counter begin at 3569 and are compiled in shard 4. This round's counter reset is superseded to 2/2.

**RESOLUTION TRACE:** source lines 3513–3519 (header, protocol, framing) and 3529 (the correction to the report's cure); repair 1 at 3523–3567 is compiled at `.60`; repairs 2–4 and the counter at 3569–3670 belong to shard 4.

**TEETH:** S7 acceptance gate; the r7 hostile pass of record; the non-circularity audit tooth.

---

### EFF.T2.66  [fence]

**CANONICAL STATEMENT:** `[TABLE / ASSEMBLED — the withdrawals register: claims of earlier rounds retracted inside this range, each quoted at its retraction]`

| Withdrawn claim | Retracted at | Governing retraction wording |
|---|---|---|
| That two independent textual legs carry the refine height (r5 repair 2's corroboration sentence) | r6 repair 1(c) | “That claim is **withdrawn**: both lines belong to LEMMA HE7-13's hypothesis-side description of the α-refine configuration, not to a derivation of it … They are recorded here as a **corroboration** of `(REF-HT)` … and the height itself is carried by `(REF-HT)`, a master-side derivation, and by nothing textual.” |
| The three earlier supports for the rise | r7 repair 1(c) | “Three earlier supports for the rise are **withdrawn**, and are used nowhere: the "new valid development" of the sentence below the recentering display, which asserts that a development exists and is valid and not that any value rises; `(SEC-RANK)`, which is asserted at every product-\(1\) recentering irrespective of \(k\) and which r4 repair 3's own fence declares underived here; and the attribution of the rise to an assertion "hypothesised by HE7.A", which named no displayed assertion” |
| That LEMMA HE3-2(b)'s recentered key exists only at an integer slope | r7 repair 4 | “the "only at an integer slope" claim is **withdrawn**: it is false of LEMMA HE3-2, which requires only \(\kappa>D'h\) and \(s\in K^\times\) and carries its own branch for a \(\kappa\) that is not a slope.” |
| That `(REF-HT)` enters S1.8C only at reading directive 2 | r8 repair 1(d) | “The claim that "`(REF-HT)` enters S1.8C only at reading directive 2" is **withdrawn** as false: three sites of S1.8C carry the \(\lambda\)-index upstream of the match … What is true, and is all the discharge needs, is that no claim made at those three sites depends on the index being \(\lambda\)” |
| That r6 made no theorem-statement change | r7 counter | “that sentence is r6's own record of r6, left standing as such and superseded in substance by this paragraph.” |
| The report's proposed one-sentence cure | r8 header | “**not** available as a quoted formula” (LEMMA HE3-2's display is fenced out of every consumption) |

**DERIVATION:** `[SIGNED NON-APPLICABILITY]` Each row is a retraction rather than a narrowing: the earlier text asserted something the effective text now denies, and each retraction states the ground of denial and where the load is carried instead. The register is compiled here because the retractions are scattered across four repairs and their common function — preventing a later reader from reviving a withdrawn support — is invisible from any one of them.

**CONDITIONALITY:** A withdrawal removes a support, never a conclusion: in every row the conclusion the withdrawn support was offered for survives on other grounds, named in the same repair. The r6-counter row is a supersession-in-substance only; the r6 sentence stands byte-unchanged as that round's own record.

**RESOLUTION TRACE:** r6 repair 1(c) (2999), r7 repair 1(c) (3349), r7 repair 4 (3431), r8 repair 1(d) (3561), r7 counter (3501), r8 header (3529). Each superseded target landmark-verified at 1 under its round's bound (§3, part B).

**TEETH:** the pass-level orphan check (“all four r7 withdrawals are orphan-free”); the standing S7 consumption sweep, which must not re-admit a withdrawn citation.

---
### EFF.T2.67  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r8 round record (counter; the r8 header is homed at EFF.T2.65)]`

> “r8 folds repairs for the single GAP (G-1P7), both minors (m-1P7, m-2P7) and both recorded nits of the r7 hostile pass of record. Its substantive content is one object, and it is an assembly order rather than a new claim: the level-one discharge of (RISE) now exhibits the instance's refine step BEFORE reading either clause off it.”

> “**No theorem-statement change is made by this round**, in the exact sense S7 counts: no display is amended, no hypothesis is added to or removed from HE7.A's suite, no case is added or dropped, and no conclusion is touched. (RISE) and (HT) read exactly as r7 set them; (RISE) remains STIPULATED, on r4 repair 3's `(SEC-RANK)` footing, and (HT) remains DERIVED from it by the min-rule display. r7's own statement change — (RISE) joining the root-preserving continuation assertions — stands as r7 booked it.”

> “**Two named obligations remain open**, both at level one: `(LB1)` for clause-4 block construction, and `(MP1)` for the clause-5 peel at a recentered key. (RISE) is a carrier hypothesis, not a ledger obligation”

> “**The clean-pass counter is RESET to 0 of 2.**”

**DERIVATION:** `[ROUND RECORD]` The round's own classification test is S7's: a statement change is an amendment to a display, the hypothesis suite, the case list or a conclusion. r8 changes none of those — it changes a *discharge*, one citation and four items of bookkeeping — so it books no statement change while r7, which added (RISE) to the suite, books one.

**CONDITIONALITY:** Historical as to counter. Its landmark census is **corrected inside this shard** by r9 repair 2 (“Twelve master-internal landmark strings, on eleven lines” → “on ten lines”; “Nine source lines” → “Eleven source lines”); the lists themselves “are themselves correct and unchanged”. The obligation set survives to acceptance.

**RESOLUTION TRACE:** source lines 3655–3667; header at 3513–3519 (shard 3, `.65`); census corrected at 3767–3789; counter superseded by the acceptance record.

**TEETH:** S7 acceptance gate; the r7 hostile pass of record; the round's own landmark census as an audit tooth.

---

### EFF.T2.68  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — what the three S1 data do and do not derive, and the removal of the last two (REF-HT) mis-citations]`

The four r6 sentences describing the binding as derived from three S1 data are booked together:

> “Four live sentences, all r6 round prose, make the same now-incomplete claim; r7 booked one of them. They are booked here together and on one uniform footing — each is r6's own record of r6, is left standing as such, and is superseded in substance by the (RISE)+(HT) architecture”

> “**What the correction is, once for all four.** The three S1 data derive the min-rule DISPLAY — \(d(\Phi(\rho))=\lambda\) on the class by `(SIDE-COUNT)`, \(d(L_k(s)(\rho))=k\) by `(SLOT-V)` + `(LIFT)`, hence \(d(\Phi_{\mathrm{new}}(\rho))=\min(\lambda,k)\le\lambda\) at \(k\ne\lambda\) — and that display is an IMPLICATION, converting (RISE) into (HT). It binds nothing on its own, because it is silent on whether any value rises: the three data are as true at \(k\ne\lambda\), where the class does not rise, as at \(k=\lambda\). The binding needs a fourth datum, the stipulated (RISE), which r7 displays and discharges per instance.”

The lead-in is corrected so that only (RISE) is stipulated:

> “The recentering at this branch is a REFINE step, and this master stipulates of a refine step ONE thing: that it raise the key's value on the class it refines. That its increment then sits at the side's own slope is not a second stipulation but a consequence of the first, derived below. Both are displayed, because both are consumed downstream:”

Reading directive 2 is re-cited to the support it actually has:

> “The passage's configuration is a repeated \(K\)-rational residual root at an integer slope; that is clause 3's product-\(1\) branch by S1.8's own case split, since a \(K\)-rational residual root has \(\deg r'=1\) and an integer \(\lambda=u'/e'\) in lowest terms forces \(e'=1\), so \(e'\deg r'=1\) — the only transition of `(RANK)` that recenters a key. Neither clause of `(REF-HT)` is used here: (RISE) and (HT) are about the step this branch performs, not about which branch is taken.”

> “**Consequential booking.** r7 repair 4's closing clause … is superseded on that clause alone: after (b) above, `(REF-HT)` governs neither the match nor the directive, and the rest of r7 repair 4's paragraph … stands unchanged.”

**DERIVATION:** `[BOOKKEEPING CORRECTION WITH A SUBSTANTIVE CORE]` The core is the once-for-all correction: an implication is not a binding. The three S1 data are symmetric in \(k\) and therefore cannot select \(k=\lambda\); only a premise asserting a rise can, and that premise is (RISE). The two citation cures follow from the same accounting: the lead-in must not present (HT) as stipulated, and reading directive 2's proposition (which branch is taken) is decided by S1.8's case split and the lowest-terms convention, not by either clause of `(REF-HT)`.

**CONDITIONALITY:** All four r6 sentences stand byte-unchanged as r6's own record; only their substance is superseded. After this unit, **no clause of `(REF-HT)` is a premise anywhere in S1.8C** — the completion of the withdrawal r8 repair 1(d) began.

**RESOLUTION TRACE:** r8 repair 2 (3569–3595), r8 repair 4(a)–(b) and its consequential booking (3619–3651). The four r6 sentences landmark-verified at 1 under bound 3509 at lines 2922, 2934, 3287, 3289; the three superseded strings at 3321, 3105, 3431 (§3, part B). Destination: base S1.8 lead-in and S1.8C directive 2 → shard 1, `.19` and `.25`.

**TEETH:** S7 Pass 1 theorem gate; the non-circularity audit tooth; the orphan check on withdrawn supports.

---

### EFF.T2.69  [changes-record]

**CANONICAL STATEMENT:** `[VERBATIM — the HE6 leg of the level-one (RISE) discharge, with its caveat routed (r8 repair 3); attaches to the discharge map at EFF.T2.60]`

> “**The S3.2 half of the scope.** S3.1 is HE3 and S3.2 is HE6, whose family is enlarged beyond HE3's, so the stage-α reading above has to be licensed for HE6's classes before the discharge may be scoped to both. It is, in the closing paragraph of the pinned proof unit of THEOREM HE6.A: `**This is HE3's LEMMA HE3-4 in full generality**, so HE3's THEOREM HE3.A` (`HE6_PROOF_2026-08-08.md`:663), `assembly (§S6.3 there: base read + stage-α + stage-CS + embedded genres) may` (664), `be run with HE3-4 replaced by THEOREM HE6.A — with the one caveat of §S7 for` (665), `histories containing an ℓ ≥ 2 side with a repeated residual factor.` (666) — the same quoted pair S1.8C already leans on, naming **stage-α** explicitly. The caveat is not consumed by this discharge: an \(\ell\ge2\) side with a repeated residual factor is \(e'\deg r'\ge2\), the product-\(\ge2\) child jump of clause 3, whereas the step under discharge is the product-\(1\) refine step, \(e'\deg r'=1\); S1.8C records the same routing for the frame discharge, and S3.2's own text sends that configuration to the level-two construction.”

**DERIVATION:** `[CITATION COMPLETENESS]` The defect was scope-versus-citation: the discharge was scoped to “(S3.1/S3.2)” but cited only `HE3-A-PROOF`. The licence exists inside a pin already on S3.2's line, so “this is a citation completeness defect, not a missing pin”. The caveat is disposed of by branch arithmetic — \(\ell\ge2\) with a repeated residual factor is exactly \(e'\deg r'\ge2\), which is not the branch under discharge — and the same routing is already recorded twice elsewhere (S1.8C, and S3.2's own continuation sentence).

**CONDITIONALITY:** The licence is for HE6's enlarged classes at the product-\(1\) step only. Nothing behind the §S7 caveat is consumed anywhere in the note.

**RESOLUTION TRACE:** r8 repair 3 (3599–3615); the superseded anchor sentence landmark-verified at 1 (line 3353) under bound 3509. The four HE6 lines re-verified at 1 (§3, part A). Destination: the level-one `(RISE)` discharge bullet in base S1.8 → shard 1 `.19`, with the derivation carried at shard 3 `.60` and here.

**TEETH:** the level-one `(RISE)` discharge tooth; the standing S7 consumption check (the licence lies inside `HE6-PROOF`).

---

### EFF.T2.70  [lemma]

**CANONICAL STATEMENT:** `[ASSEMBLED — the print/coherent seam and the derivation of (IDX-TWIST) (r9 repair 1(a)), with Rider 1's lift-choice qualifier and r10 repair 2's height qualification applied. The (IDX-TWIST) display itself is homed at base S1.8 (shard 1, EFF.T2.20); what is homed here is its derivation, its bijection argument and its two qualifiers.]`

The seam:

> “a residue in the RECIPE'S OWN frame, which is the print frame: line 204, quoted above, fixes \(B_0\) by \(\operatorname{res}(B_0(\theta)/\varpi(\theta)^{\kappa})\), the \(\varpi\)-read, and not by the coherent \(n(\kappa)\)-read of `(SLOT-R)`. This master's `(HE6-SEAM)` is the conversion between the two, \(\operatorname{res}(A(\xi)/\varpi(\xi)^{k})=\iota_\xi(\gamma_k(A))\eta_\xi^{-q(k)}\), and at \(\xi=\theta\) — a \((T1)/(T2)\) point, being the point at which the recipe states its own condition and at which `(GAMMA)` is written — the embedding \(\iota_\theta\) is the identity inclusion of \(K=\mathbf F_Q(\eta)\): it is a \(k_0\)-embedding by `(RES-COMP)`, \(k_0=\mathbf F_Q\) by S1.1, and \(\eta_\theta\mapsto\eta_\theta\) by S3.1's \(\iota_\xi(\eta_\theta)=\eta_\xi\) read at \(\xi=\theta\), so it is the identity on \(K=k_0(\eta)\). Hence \(-\sigma=\gamma_\kappa(B_0)\eta^{-q(\kappa)}\), so \(\operatorname{dig}(B_0)=\gamma_\kappa(B_0)=-\sigma\eta^{q(\kappa)}\)”

The non-triviality of the twist:

> “The print label and the coherent digit are the same element of \(K\) only when \(\eta^{q(\kappa)}=1\), and no hypothesis of this master or of its sources supplies that: `(Q-DEF)` posits \(q\) precisely because the twist can be nontrivial, and the minus sign of `(HE6-SEAM)` is declared mandatory at S1.2.”

The bijection, which is what makes the relabelling lossless:

> “**Nothing is lost by the mismatch, because the relabelling is a bijection.** \(\eta\in K^\times\) and \(q(\kappa)\in\mathbf Z\), so \(\eta^{q(\kappa)}\) is ONE fixed element of \(K^\times\), depending on \(\kappa\) alone and on neither the polynomial read nor the label — that is the universality of the RIDER's twist, the clause `HE6-LIFT-1L` is pinned for. Multiplication by it is a bijection of \(K\) fixing \(0\), and of \(K^\times\) onto itself. The family's labels at \((\ell,d)=(1,1)\) run over exactly \(K^\times\), because the recipe quantifies over EVERY monic irreducible \(r\in K[Z]\) with \(r(0)\ne0\) … and \(r=Z-\sigma\) is such an \(r\) exactly for \(\sigma\in K^\times\); this master's digits at a full height run over all of \(K\) (S1.4, "every digit \(c\in K\) has an integral lift"), with \(L_\kappa(0)=0\) the empty recentering, which is no transition. … What r8 asserted member-by-member at equal index NAMES is true after the relabelling and false before it.”

The exhibited step, with nothing asserted of it:

> “whichever member of the family the read forms, it is \(\Phi'-\Lambda\) with \(\Lambda:=-B_0\) integral, \(\deg\Lambda<D'=D\), \(h(\Lambda)=\kappa\) and \(\operatorname{dig}(\Lambda)\in K^\times\), and the recipe's standing \(\kappa>D'h=T\) places it inside `(WINDOW)` before any clause of `(REF-HT)` is read. **No height and no digit is asserted of that member here, and neither is needed to read the clause that follows.**”

S1.8C's family-member sentence, in its effective form:

> “At \((\ell,d)=(1,1)\) the recentered key IS a member of the family, and the member it is, is \(\Psi_{\lambda,\,Z-s\eta^{-q(\lambda)}}=\Phi'+B_0\) with \(B_0=-L_\lambda(s)\): the family indexes its members by the PRINT residue of \(B_0\) … this master indexes its recenterings by the COHERENT digit of the increment (`(SLOT-R)`), and the two differ by the fixed unit \(\eta^{q(\lambda)}\in K^\times\) of `(HE6-SEAM)` … The relabelling is a bijection of \(K^\times\), so the family covers every recentering of this master at that height, member for member; what it does not do is match them at equal index names.”

**DERIVATION:** `[SEAM COMPUTATION]` One conversion and one identification: `(HE6-SEAM)` converts the recipe's \(\varpi\)-residue into the coherent digit, and \(\iota_\theta=\mathrm{id}\) at the recipe's own point (three cited grounds: `(RES-COMP)`, S1.1's \(k_0=\mathbf F_Q\), S3.1's \(\iota_\xi(\eta_\theta)=\eta_\xi\)). The bijection argument then needs only that \(\eta^{q(\kappa)}\) is one fixed element of \(K^\times\) depending on \(\kappa\) alone — the universality clause `HE6-LIFT-1L` is pinned for — plus the two quantifier ranges (family labels over \(K^\times\); master digits over \(K\), with \(0\) the empty recentering).

**CONDITIONALITY:** Two qualifiers apply, both homed in this shard (`.72`): the equality is exact **at the compatible lift choice** and holds modulo increments of height \(>\kappa\) at an arbitrary permitted one, with the choice-independent content being the pair \(h(-B_0)=\kappa\), \(\operatorname{dig}(-B_0)=\sigma\eta^{q(\kappa)}\); and the covering direction is stated at **\(\kappa>D'h\)**, DEFINITION HE6-1's own standing hypothesis, not at mere fullness. `(IDX-TWIST)` is a derived identity of the level-one instance and no clause of the theorem.

**RESOLUTION TRACE:** r9 repair 1(a) (3689–3711) and 1(d) (3749–3755), replacing r8 repair 1(a)'s step sentence (landmark 3537) and S1.8C's family-member sentence (3085); qualified by Rider 1 (3829–3831) and r10 repair 2 (3999–4013). Destination: base S1.8 and S1.8C → shard 1, `.20` and `.25`.

**TEETH:** the print/coherent-frame mutant; the HE6 seam/sign gate; the lift-choice qualifier tooth; the covering-height tooth.

---

### EFF.T2.71  [lemma]

**CANONICAL STATEMENT:** `[ASSEMBLED — the effective level-one derivation of the step's height AND digit from (RISE) (r9 repair 1(b)), superseding the r8 height ground quoted at EFF.T2.60]`

> “At any index \(\kappa\ne\lambda\) the display leaves every root of the class at \(d=\min(\lambda,\kappa)\le\lambda\) … Hence \(\kappa=\lambda\). At \(\kappa=\lambda\) the display is silent, the two values being equal; there the same reading continues one notch finer, at the residues, and fixes the step's DIGIT as well — without consulting the family's print label.”

The coherent label read, quoted from strictly inside `HE3-A-PROOF`:

> “`note's frame, where the label of ρ is (λ, r) with r ∈ K[Z] read via the` (`HE3_PROOF_2026-08-08.md`:1114), `F_Q-embedding ι_ρ : K → k̄, η_θ ↦ η_ρ, and β_ρ := res(y_ρ/n(λ)(ρ)) at` (1115); the argument \(y_\rho\) is the key's own value, as the equivariance display inside the same span shows at \(g=\operatorname{id}\), `    β_{gρ} = res(Φ′(gρ)^{ℓ}/n(u)(gρ)) = ḡ(β_ρ)   (ℓ = 1: n(λ) read).` (1131, quoted with its four leading spaces), giving \(\beta_\rho=\operatorname{res}(\Phi(\rho)/n(\lambda)(\rho))\) at \(\ell=1\) with \(\Phi=\Phi'\) by `(HE3-INSTANCE)`; and the label condition itself is \(\iota_\rho(r)(\beta_\rho)=0\), `ι_{gρ}(r)(β_{gρ}) = ḡ(ι_ρ(r)(β_ρ)) = ḡ(0) = 0, and gρ carries the same` (1135)”

The forced digit:

> \[
> \boxed{
> d\bigl((\Phi-\Lambda)(\rho)\bigr)>\lambda
> \iff
> \iota_\rho\bigl(s-\operatorname{dig}(\Lambda)\bigr)=0
> \iff
> \operatorname{dig}(\Lambda)=s ,}
> \]

> “\(\iota_\rho\) being an injection of fields. The passage's rise therefore forces both readings at once: \(h(\Lambda)=\lambda\) and \(\operatorname{dig}(\Lambda)=s\), with \(s\) this master's own coherent residual root of `(RES-FACT)` — the digit at which S1.8 forms \(\Phi-L_\lambda(s)\) — while the family's print label at that same member is \(s\eta^{-q(\lambda)}\) by (IDX-TWIST) and plays no part in the derivation.”

The two riders that close it:

> “FIRST, the derived digit is automatically in \(K^\times\): a zero increment cannot raise \(d(\Phi(\rho))=\lambda\), and S1.2 gives \(\operatorname{dig}(A)\in K^\times\) at every nonzero slot. SECOND, the lift freedom is immaterial. \(\Lambda\) is the increment the instance's construction actually formed; \(L_\lambda(s)\) is the carrier's designated lift at the same height and digit (S1.4). Their difference \(E=\Lambda-L_\lambda(s)\) has \(\deg E<D\) and, read at the fixed height \(\lambda\), digit \(s-s=0\) … so \(E\) cannot have \(h(E)=\lambda\), since S1.2 gives a nonzero slot a digit in \(K^\times\); **[r12 repair 4(d), homed in shard 5:]** “nor can it have \(h(E)<\lambda\), because \(h(\Lambda)=\lambda\) and \(h(L_\lambda(s))=\lambda\) give \(d(\Lambda(\rho))=d(L_\lambda(s)(\rho))=\lambda\) by `(SLOT-V)`, whence \(d(E(\rho))\ge\lambda\) by the ultrametric inequality for \(d\) (S1.1), while a nonzero \(E\) of degree \(<D\) has \(d(E(\rho))=h(E)\) by `(SLOT-V)` again”; hence \(E=0\) or \(h(E)>\lambda\), and then \(d(E(\rho))>\lambda\) by `(SLOT-V)`. From \((\Phi-L_\lambda(s))(\rho)=(\Phi-\Lambda)(\rho)+E(\rho)\), both clauses hold at this master's own displayed step and not merely at a companion of it.”

The corroboration ground, in its effective frame:

> “so the member of DEFINITION HE6-1's family that the read uses at that node is the one whose COHERENT digit is the node's own \(s\) — its print label being \(s\eta^{-q(\lambda)}\) and not \(s\), by (IDX-TWIST) — and its increment sits at \(d=\lambda\) by the recipe above.”

**DERIVATION:** `[RESIDUE-LEVEL REFINEMENT OF THE MIN-RULE]` Above the value seam the min-rule display fixes the height; at \(k=\lambda\) it is silent, and the argument descends one level, to residues. Two reads in the same coherent frame — the label condition \(\iota_\rho(r)(\beta_\rho)=0\) at \(r=Z-s\), and `(SLOT-R)` on the increment — subtract to give the boxed equivalence, because \(d(n(\lambda)(\rho))=\lambda\) makes the quotient value-nonnegative with residue vanishing exactly when the value is positive. The two riders remove the only two degrees of freedom left: the digit's membership in \(K^\times\), and the difference between the instance's increment and the carrier's designated lift.

**CONDITIONALITY:** **One clause of the lift-freedom rider is completed downstream:** r12 repair 4(d) (shard 5, `.94`) inserts the step ruling out \(h(E)<\lambda\), quoted inline above in its effective position; it uses the ultrametric law for \(d\) that r12 repair 4(b) displays in S1.1. The derivation runs at the instance and instantiates the master's generality in \(k\) and in the digit rather than transferring the theorem's (HT) clause: “the direction of use is the safe one — the master's generality in \(k\), and in the digit, is INSTANTIATED here, not transferred.” It requires \(\rho\in\operatorname{Pt}\) and \(\deg\Lambda<D\) for `(SLOT-R)`. The premise remains (RISE), stipulated.

**RESOLUTION TRACE:** r9 repair 1(b)–(c) (3713–3747), replacing r8 repair 1(b)'s height ground and corroboration clause (both landmarked at line 3545 under bound 3667). Four HE3 lines re-verified at 1 with their recorded line numbers (§3, part A). Destination: base S1.8's level-one discharge → shard 1, `.19`; supersedes the passage quoted at shard 3 `.60`.

**TEETH:** the print/coherent-frame mutant (this is its cure); the level-one `(RISE)` discharge tooth; the lift-choice tooth.

---

### EFF.T2.72  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the two qualifiers on (IDX-TWIST): Rider 1's lift-choice clause and r10 repair 2's covering-height correction]`

Rider 1's inserted clause:

> “**Which lift the equality is read at.** (IDX-TWIST) is an equality of polynomials AT the compatible choice \(B_0=-L_\kappa(\sigma\eta^{q(\kappa)})\), and that choice is one DEFINITION HE6-1 permits: \(-L_\kappa(\sigma\eta^{q(\kappa)})\) has \(\deg<D=D'\) and \(h=\kappa\), hence \(d(B_0)=\kappa\), by S1.4's `(LIFT)`, and its print residue is \(\gamma_\kappa\bigl(-L_\kappa(\sigma\eta^{q(\kappa)})\bigr)\eta^{-q(\kappa)}=-\sigma\eta^{q(\kappa)}\eta^{-q(\kappa)}=-\sigma=c_0\) by the same `(HE6-SEAM)` read at \(\xi=\theta\) used just above — so the recipe's three conditions at line 204 are met, and the master's own recentering \(\Phi'-L_\kappa(\sigma\eta^{q(\kappa)})\) IS a member of the family at the label \(r=Z-\sigma\). For an ARBITRARY (LIFT)-permitted choice, line 204 fixes only the height and the print residue: two permitted \(B_0\) differ by an \(E\) with \(\deg E<D'\) and \(d(E)\ge\kappa\) whose digit at \(\kappa\) is \(\gamma_\kappa(B_0)-\gamma_\kappa(B_0')=0\) … so \(E=0\) or \(h(E)>\kappa\) … Read at an arbitrary permitted choice, (IDX-TWIST) therefore holds MODULO increments of height \(>\kappa\), and what is choice-independent is exactly the pair \(h(-B_0)=\kappa\), \(\operatorname{dig}(-B_0)=\sigma\eta^{q(\kappa)}\) that the seam read above produced.”

with its two directions distinguished:

> “The COVERING direction — every nonempty recentering \(\Phi'-L_\kappa(c)\) of this master at a height \(\kappa>D'h\) … is a member of the family, at the label \(r=Z-c\eta^{-q(\kappa)}\) and the permitted choice \(B_0=-L_\kappa(c)\) — is EXACT, by the permittedness just checked, and it is the direction S1.8C consumes. The CONVERSE reading — that an arbitrarily chosen member is literally the designated recentering — holds up to an increment of height \(>\kappa\), which is to say it holds exactly in the height-and-digit data that every consumer of it reads.”

r10 repair 2's height correction, quoted in the form it inserts:

> “at a height \(\kappa>D'h\) — DEFINITION HE6-1's own standing hypothesis (`HE6_PROOF_2026-08-08.md`:202), strictly stronger than fullness, since \(\kappa>D'h>(D'-1)h\) makes \(\kappa\) full by S1.4's uniform sufficient bound while a full \(\kappa\) in the band \((D'-1)h\le\kappa\le D'h\) indexes no member of the family — is a member of the family”

The four “member for member” sites are classified, none amended:

> “Line 3677 … and line 3755 … both state the COVERING direction, which the qualifier certifies as exact; they stand unchanged. Lines 3709 and 3797 state the identity of SETS …, and they are the two sentences the qualifier's closing clause scopes: exact at the compatible choice, and up to an increment of height \(>\kappa\) at an arbitrary permitted one.”

**DERIVATION:** `[QUALIFIER, NOT REPAIR]` DEFINITION HE6-1 constrains \(B_0\) by a height and a *print residue* only, while `(LIFT)` designates a lift by a height and a *digit*; the seam therefore yields the choice-independent pair, and polynomial equality only at the compatible choice. Permittedness of that choice is checked by computing its print residue back through `(HE6-SEAM)`. The height correction is a strict-inequality comparison: \(\kappa>D'h>(D'-1)h\) implies full, but a full \(\kappa\) in \([(D'-1)h,\;D'h]\) indexes no family member, so “full” was too weak a hypothesis for the covering claim.

**CONDITIONALITY:** Nothing downstream narrows: `(WINDOW)` puts every side slope strictly above \(T=D'h\), and S1.8C — the covering direction's only consumer — reads it at \(\lambda>T=D'h\). Both qualifiers are counter-neutral: Rider 1 folds a minors-only pass and resets nothing; r10 repair 2 is a minor inside a gap-bearing round. The level-one `(RISE)` discharge is explicitly **unchanged** by the lift qualifier, since it “consults neither the family's print label nor the recipe's lift”.

**RESOLUTION TRACE:** Rider 1 (3821–3839), inserted after the `(IDX-TWIST)` display (`> \tag{IDX-TWIST}` verified unique at line 3706 under bound 3805); r10 repair 2 (3999–4015), superseding the rider's own covering phrase (landmark 3831 under bound 3843). Destination: base S1.8 → shard 1, `.20`, whose `CONDITIONALITY` states both qualifiers in compressed form.

**TEETH:** the lift-choice qualifier tooth; the covering-height tooth; the consumer-census check (six consumption sites of `(IDX-TWIST)`, all choice-independent).

---

### EFF.T2.73  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r9 round record: provenance, the pass's certification list, and the counter]`

> “*(Opus/Claude repair arm, against the r8 hostile pass of record `runs/comp13/T2SOL_output.log` — this note's FIRST model-diverse pass (gpt-5.6-sol high) on the current architecture, returning 0 CRITICAL + 1 GAP + 1 minor; counter resets.)*”

> “**What the GAP is, and what it is not.** The pass certified the master core end to end and said so clause by clause: "`(ACCOUNT)` correctly yields clause 1 and `(SIDE-COUNT)`"; "`(RES-DEG)` plus the defect-free fundamental identity gives the termwise orbit count and exact \((e,f)\)"; "`(SIDE-PROD)`, `(LABEL-PROD)`, `(MID-PEEL)`, terminal reads, child jumps, and linear refinements form a complete recursive analysis under the stated block/continuation hypotheses"; "The clause-5 trigger analysis covers both key-changing transitions, while transition 6 returns key-free residual blocks by definition"; "`(RANK)=(\deg F,\mu,\sigma_{\mathcal C})` decreases correctly in every transition, with `(SEC-RANK)` honestly explicit"; "`(LB1)` and `(MP1)` remain fenced; I found no fence leakage"; and "S1.8B's level-two transport and composed-key \(W+w\) routing are coherent. The HE6-PROOF \(\ell\ge2\) caveat is correctly routed to the product-\(\ge2\) child branch."”

> “the abstract theorem remains true because `(RISE)` is an explicit carrier hypothesis; the instance discharge is the gap”

> “**No theorem-statement change is made by this round.** … The one new display, (IDX-TWIST), is a derived identity of the level-one instance, not a clause of the theorem. Two sentences of the r8 counter survive verbatim and are not booked: "DEFINITION HE6-1's family at \(\ell=1\) IS the family of HE3's recenterings" is a statement about the family as a SET, which (IDX-TWIST) confirms, and "its recipe puts the \((\ell,d)=(1,1)\) member's increment at the member's own index" is a statement about HEIGHTS, which the twist does not touch. What was false was only the matching of index names”

> “The finding is credited to that pass in full: it caught a print/coherent frame conflation that five same-arm passes did not.”

> “**The clean-pass counter is RESET to 0 of 2.**”

**DERIVATION:** `[ROUND RECORD]` The round's scope discipline is the certification list: everything the pass certified is named and left untouched, and the repair is confined to the one identification refuted. The credit sentence is a methodological record — the first model-diverse pass caught what five same-arm passes did not — which the acceptance record later generalises into its two-arm requirement.

**CONDITIONALITY:** Historical as to counter. Its own census (“Six master-internal landmark strings, on four lines … Five source lines … Two span delimiters”) is confirmed at compilation (§3). The three pins this round consumes were already on both level-one lines, so no Source-pin line is amended.

**RESOLUTION TRACE:** source lines 3671–3677 (header, protocol, framing) and 3793–3805 (counter); its correction of r8's census at 3767–3789 is recorded at `.67`.

**TEETH:** S7 acceptance gate; the r8 hostile pass of record (the first model-diverse one); the print/coherent mutant this round installs the cure for.

---

### EFF.T2.74  [fence]

**CANONICAL STATEMENT:** `[VERBATIM — the frame-authority fence: what supplies the transport law, and what is cited without being consumed (r9 repair 1(e))]`

> “**(e) The frame authority, and what is NOT cited.** The transport law consumed above is this master's own `(HE6-SEAM)`, whose supplier pin is `HE6-SLOT-SEAM` (LEMMA HE6-0″, adjudicated at r4 repair 1 for exactly the two clauses `(SLOT-V)` and the \(\varpi\)-read conversion, with the `[r2]` sign correction this master reproduces). No new pin and no new source is needed for it. The gauge-cocycle note T1 (`T1_GAUGE_COCYCLE_2026-08-12.md`, ACCEPTED 2/2 on 2026-08-13) books the same SHAPE of error at its own seam — its honesty ledger records that "raw print/canonical equality is iff \(z^\nu=1\), not iff \(\nu=0\)" — and that sentence is recorded here as methodological precedent ONLY: T1 is not among this master's six source files, no pin covers it, and nothing above consumes it. S0.2's no-unpinned-material clause is therefore respected in the strict sense it states.”

**DERIVATION:** `[NON-IMPORT DECLARATION]` Two claims, each with its own ground: the transport law is already pinned (so the r9 repair adds no source dependency), and the cross-note observation is precedent rather than premise (so S0.2's no-unpinned-material clause is not breached by naming a note outside the six sources). The distinction is the same one r12 repair 3 later generalises: “Consumption, not citation, is the gated relation.”

**CONDITIONALITY:** T1 is not a source of this note and carries no pin here. Anything a later reader wants from T1 must be re-derived or newly pinned; the precedent status of the quoted sentence gives it no evidential force in T2.

**RESOLUTION TRACE:** r9 repair 1(e) (3757). Cross-note reference is to `T1_GAUGE_COCYCLE_2026-08-12.md`, verified to exist and to carry the quoted honesty-ledger wording (§3, part C) — verification recorded because the sentence is quoted, notwithstanding that it is not consumed.

**TEETH:** the standing S7 consumption sweep (a named-but-not-consumed unit must be classified, not silently left); the print/coherent-frame mutant.

---

### EFF.T2.75  [acceptance-box]

**CANONICAL STATEMENT:** `[ASSEMBLED — post-pass rider block 1: the fold rule, the landmark convention, and the counter state it sets]`

> “**Dated rider (2026-08-13 — the single minor of the gpt-5.6-sol high hostile pass on the r9 effective text, `runs/comp13/T2SOL2_output.log`, returning 0 CRITICAL + 0 GAP + 1 minor. Folded per the campaign's minors-only precedent — T4's post-pass gloss-direction rider, T5's two post-pass-1 locator riders, and T1's five post-pass-1 riders, each folded on a 0C + 0G pass and each subsequently confirmed to 2/2. This note carries no earlier rider precedent, every previous round having been gap-or-worse; the T1 acceptance-fold rider style is followed here. NO r-section, no grade event, NO counter reset.)** The rider QUALIFIES one display and does nothing else.”

> “**Landmark convention (rider).** Counts are taken over the note AS IT STOOD BEFORE THIS BLOCK — lines 1–3805, i.e. through the last line of the r9 counter — because each landmark is necessarily quoted a second time here.”

> “This rider folds the single MINOR of a hostile pass that returned **0 CRITICAL + 0 GAP + 1 minor**. S7's reset rule is stated of gap-or-worse repairs only ("A gap-or-worse repair resets the clean count"), and a minors-only pass is a clean pass whose minors fold as post-pass riders (T4, T5, T1). Folding riders is not a repair round: **the clean-pass counter is NOT reset and STANDS AT 1 OF 2.** Pass of record: the gpt-5.6-sol high hostile pass on the r9 effective text, `runs/comp13/T2SOL2_output.log`, 2026-08-13 — this note's second model-diverse pass and its first clean one. Still owed at the S7 acceptance gate: the Opus/Claude-arm confirmation pass, the second of the two consecutive clean passes, taken over the r9 effective text PLUS this rider.”

**DERIVATION:** `[COUNTER-STATE RECORD]` The fold rule is read off S7's own wording: the reset rule is stated of gap-or-worse repairs, so a minors-only pass is a clean pass and folding its minor is not a repair round. The campaign precedent (T4, T5, T1) is cited as the practice, and the note records that it has no earlier rider precedent of its own. The landmark bound advances to 3805 because the rider necessarily re-quotes each landmark.

**CONDITIONALITY:** The 1-of-2 counter is superseded: the confirmation pass this block awaits (`T2P8`, r10's pass of record) returned 0C+1G+1m, so the counter resets again at r10 and reaches 2/2 only at post-pass rider 3. The qualifier this rider installs is itself qualified by r10 repair 2 (`.72`).

**RESOLUTION TRACE:** source lines 3809–3843; the rider's own landmark census (including the four “member for member” sites and the three `\Psi_{\kappa,Z-\sigma}` occurrences) re-run at §3, part B.

**TEETH:** S7 acceptance gate; the minors-only fold precedent; the consumer census of `(IDX-TWIST)`.

---

### EFF.T2.76  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r10 round record: provenance and the first end-to-end pin-gate run]`

> “*(Opus/Claude repair arm, against the Opus-arm confirmation pass of record `runs/comp13/T2P8_output.log`, taken over the r9 effective text PLUS the post-pass rider and returning 0 CRITICAL + 1 GAP + 1 minor; counter resets.)*”

> “**What the pass verified, and what this round does not touch.** The pass re-derived the rider's three claims from the byte-level source and upheld all three: the compatible choice \(B_0=-L_\kappa(\sigma\eta^{q(\kappa)})\) is `(LIFT)`-permitted, read against `HE6_PROOF_2026-08-08.md`:201–205; two permitted choices differ by height \(>\kappa\); and every downstream consumer of (IDX-TWIST) is choice-independent, the consumer census being complete at six sites (3709, 3739, 3747, 3755, 3759, 3797) across the rider's two classifying paragraphs. It then ran the full 32-pin gate end to end on the final text for the first time — 15 quoted pairs with all 30 delimiter lines at `grep -cFx` = 1, 4 first-only, 13 description-only, zero `T2V2PIN` lines in the six sources, zero source edits — and fourteen supersession landmarks across r1–r9 and the rider, including the `(MP1′)` retirement chain, with no orphan, no double-render and no ambiguous insertion point. None of that is touched below. The GAP is not in the master core, the r9 coherent-frame rebuild, or the rider's mathematics; it is in the pin table, at the two level-one instance records.”

**DERIVATION:** `[ROUND RECORD / GATE RESULT]` The gate run is the note's own S7 pin gate executed in full for the first time, and its result is stated in the gate's own four terms (pair resolution, taxonomy, synthetic-marker count, source-edit count). The round's scope follows from where the gate failed: not in the mathematics but in the pin table's coverage of two instance records.

**CONDITIONALITY:** The gate figures are at 32 pins and are superseded to 37 with taxonomy \(20+4+13\); the acceptance record's pass 2 re-runs the same gate whole at 37. The counter reset is superseded to 2/2.

**RESOLUTION TRACE:** source lines 3847–3853; the r10 counter (4019–4033) is homed in shard 5.

**TEETH:** S7 pin gate (this is the tooth firing); the standing consumption sweep; the acceptance gate.

---

### EFF.T2.77  [table]

**CANONICAL STATEMENT:** `[TABLE — the three new HE6 pins of r10, with their delimiters and S0.2 adjudications; delimiter lines verbatim and re-verified at compilation]`

| Pin | Named unit | First delimiter | Last delimiter |
|---|---|---|---|
| `HE6-TEST-PACKAGE` | the seven consecutive statement-display units LEMMA HE6-0′ through LEMMA HE6-5, HE6 §S1 (244–287) | `> **LEMMA HE6-0′ (the local forcing — HE3-0′ REPAIRED at ℓ ≥ 2).** If a root` | `> Galois-stable, at every f₁ (no f₁ = 1 restriction).` |
| `HE6-ROOT-LABEL` | COROLLARY HE6-2″, the bolded unit closing HE6 §S4 (517–521) | `**Corollary HE6-2″ (HE3-0(iii), re-proved in this convention).** Taking` | `of ρ; it is well defined because R_λ is a fixed element of K[Z].` |
| `HE6-ACCOUNT` | HE6 §S5, the proof unit of LEMMA HE6-3 and LEMMA HE6-4, carrying (RES) and (†) (525–604) | `## S5. LEMMA HE6-3 (slope counts, (SEP)-free) AND LEMMA HE6-4 (nonemptiness)` | `what replaces HE3-BOX-6's base change.` |

The three S0.2 adjudications, each recorded at its pin:

> “Condition 1: each of the seven is a "named statement display" — the unit type r3 repair 2 added to S0.2's list — and each occurs exactly once in that type; the same lemmas' proof units (§S3.2, §S3.3, §S4, §S5, §S6.1) are units of a different type, exactly as `HE3-A-STMT` and `HE3-A-PROOF` are two pins over one theorem.”

> “Condition 1: the designation "HE6-2″" is borne by exactly one unit, this one; its only other occurrence in the file, HE6:645, is a citation inside the `HE6-PROOF` span. S0.2's outermost-unit rule resolves the pin to the outermost unit bearing that designation … Condition 4: the unit runs from its bolded opening to the end of its statement and ends immediately before the next unit of equal or higher rank, `## S5.` at 525; the horizontal rule at 523 is a boundary marker and not unit content”

> “Condition 4: the span contains (RES) at 529, the generic-letter construction at 533–538, the ξ-side and ρ-side bullets at 540–547, the identity (†) at 551, parts (a) and (b) of LEMMA HE6-3's proof, the (SEP)-counterexample remark, the complete proof of LEMMA HE6-4 with its ∎, and the closing "why this is not the tautology it looks like" remark”

Two reading directives are attached at the new pins:

> “The span contains LEMMA HE6-2's statement guard "when δ has denominator dividing ℓ", which the source's own dated append re-scopes: `**Correction 2 (PE4 F-2 — LEMMA HE6-2's β-definedness guard).** The` (`HE6_PROOF_2026-08-08.md`:1036) directs that the guard be read as "when δ = κ". **The 2026-08-09 post-PE4 correction governs.** This master consumes from LEMMA HE6-2 only the dichotomy \(\varepsilon(\xi)>0\iff\delta=\kappa\) and \(\iota_\xi(r)(\beta)=0\) … which the correction leaves byte-unchanged”

> “The span contains the inference inside LEMMA HE6-3(a)'s proof that the source's own dated append replaces: `**Dated correction (2026-08-12, post-acceptance challenge F-2 — completion of LEMMA HE6-3(a)).** In the proof of LEMMA HE6-3(a), replace the inference` (`HE6_PROOF_2026-08-08.md`:1115) … **The 2026-08-12 correction governs.** Nothing this master consumes from the span is touched by it: the correction operates strictly below (†) at HE6:551, and this master derives its own clause 1 … from `(ACCOUNT)` in S2's proof rather than consuming LEMMA HE6-3(a). Recorded at the same pin: the phrase "that instance's pinned proof" in S1.7's closing sentence denotes this span together with `HE6-PROOF`.”

**DERIVATION:** `[PIN DERIVATION]` Each pin is derived from an itemised consumption (`.78`) and closed by a delimiter pair, with the S0.2 condition that was in doubt adjudicated explicitly: the multi-unit run for `HE6-TEST-PACKAGE` (the form r3 repair 1(b) and r4 repair 5 declared), the outermost-unit and horizontal-rule rules for `HE6-ROOT-LABEL`, and the `##`-unit boundary rule for `HE6-ACCOUNT`. All six delimiter lines re-verified at 1 at exactly the recorded line numbers (§3, part A).

**CONDITIONALITY:** The pin count this round sets (35) is superseded to 37. The two reading directives are declinations of superseded material, not consumptions; both are of the form r3 repair 3 and r4 repair 12 established.

**RESOLUTION TRACE:** r10 repair 1(b) (3879–3914). Destination of the rows: base S0.2 → shard 1, `.03` (XREFs X15, X16, X17).

**TEETH:** S7 pin gate conditions 1–4; the pin-note directive coherence audit; the standing consumption sweep.

---

### EFF.T2.78  [table]

**CANONICAL STATEMENT:** `[TABLE — the itemised level-one HE6 consumption map (r10 repair 1(a)): which pinned unit supplies each S1.7 clause and (ACCOUNT)]`

| Master demand | HE6 supplier (statement display unless noted) | Pin |
|---|---|---|
| S1.7 clause 1 — roots in the intended disk carrying \(r'\)'s label; S3.2's “ξ-side” | LEMMA HE6-1, `> **LEMMA HE6-1 (the ξ-side: EVERY root of a test polynomial carries the` (250) | `HE6-TEST-PACKAGE` |
| S1.7 clause 2 — generic value attained off the class, rising strictly on it | LEMMA HE6-2 (255) and LEMMA HE6-2′ (266) | `HE6-TEST-PACKAGE` |
| S1.7 clause 3 — resultant symmetry makes the class nonempty | LEMMA HE6-4 (280); the argument at (RES), `    (RES)   Σ_{ρ : f(ρ)=0} dv(g(ρ)) = e₁·v(±Res(f,g)) = Σ_{ξ : g(ξ)=0} dv(f(ξ)),` (529) | `HE6-TEST-PACKAGE`, `HE6-ACCOUNT` |
| S1.7 clause 4 — disjointness and exhaustion; the side total \(n_\lambda=D'L_\lambda\) | item 1 of THEOREM HE6.A's proof (644–648, already inside `HE6-PROOF`) with its premise COROLLARY HE6-2″ (517); LEMMA HE6-3 (271) | `HE6-PROOF`, `HE6-ROOT-LABEL`, `HE6-TEST-PACKAGE` |
| S1.7 clause 5 — Galois equivariance of labels | LEMMA HE6-5 (284) | `HE6-TEST-PACKAGE` |
| S1.7 clause 6 — local invariants divisible by \(e_{\mathcal C}e'\), \(f_{\mathcal C}\deg r'\) (“local forcing”) | LEMMA HE6-0′ (244) | `HE6-TEST-PACKAGE` |
| S1.7 clause 7 and \(\deg\Psi_{\lambda,r'}=De'\deg r'\) — integrality | DEFINITION HE6-1, with lift legality from LEMMA HE6-1L | `HE6-FAMILY`, `HE6-LIFT-1L` (already pinned) |
| `(ACCOUNT)` — the boxed side-accounting identity | (†), `    (†)   Σ_λ n_λ·min(λ, κ) = D′·h_F(κ) = D′·Σ_λ L_λ·min(λ, κ),` (551), with the root-to-slope passage at 545–547 | `HE6-ACCOUNT` |
| S1.7's closing sentence — “those arguments remain inside that instance's pinned proof” | the generic test (533), the ξ-side (540) and ρ-side (545) evaluations, resultant symmetry (529) | `HE6-ACCOUNT` (with `HE6-PROOF`) |

The `(ACCOUNT)` identification is stated with its own translation:

> “asserted there for EVERY rational \(\kappa>D'h\) — wider than the master's "\(\kappa>T\) outside the finite set of critical values". The master's left side sums over roots and (†)'s over slopes; the passage between them is displayed in the same proof … that is \(\sum_\rho\min(\lambda_\rho,\kappa)=\sum_\lambda n_\lambda\min(\lambda,\kappa)\) after dividing by \(\ell d_0\). With \(d=dv\), \(D=D'\), \(T=D'h\) and \(w_\rho=dv(\Phi'(\rho))\) by `(HE3-INSTANCE)`/`(HE6-INSTANCE)`, the two displays together are this master's `(ACCOUNT)` verbatim.”

and the two senses of “ξ-side/ρ-side” are disambiguated:

> “HE6 uses the words "ξ-side" and "ρ-side" in two senses — as the title of LEMMA HE6-1, which is S3.2's sense at item 1, and as the two sides of the resultant identity (RES), which is this sentence's sense … Both senses now resolve into pins, the first into `HE6-TEST-PACKAGE` and the second into `HE6-ACCOUNT`.”

**DERIVATION:** `[CONSUMPTION ITEMISATION]` The defect was that the level-one records credited HE6 with the test package and `(ACCOUNT)` while “Every one of those four ranges is disjoint from every one of the five pin spans”, so “the only side-accounting identity the master proof uses has, at both level-one instance records, no pinned supplier at all”. The cure itemises each demand, names its supplier line, and pins it. Four grounds of the finding are answered one by one: S0.2's no-unpinned-material clause, S5 ledger item 3, S1.7's closing sentence, and the standing S7 check.

**CONDITIONALITY:** No sentence of S1.7, S3.1 or S3.2 is amended — the two crediting sentences (base line 889 and r1 repair 2's line 1454) “are TRUE of the pin table this repair installs and false of the one it replaces”, and both are left standing. The `(ACCOUNT)` supplier is wider than the master's use, not narrower. The consumption reaches a recentered level-one key only through S1.8C's (vi)/(vii) transport, which is why the three pins also join the three level-two Source-pin lines.

**RESOLUTION TRACE:** r10 repair 1(a) items 1–9 (3867–3877) and 1(d) (3922–3927); Source-pin line consequences at 1(f) (3967–3989), superseded downstream by r11 repair 1(e) and r12 repair 1(f). Twelve HE6 source lines re-verified at 1 at their recorded numbers (§3, part A). Destination of the lines: S3.1–S3.5 → shard 1, `.33`–`.37`.

**TEETH:** S7 pin gate; the standing consumption sweep; the `(ACCOUNT)` supplier gate; the HE6 test-package gate.

---

### EFF.T2.79  [fence]

**CANONICAL STATEMENT:** `[VERBATIM — r10 repair 1(c): what the repair declines to pin, with the ground for each declination]`

> “- **LEMMA HE6-0** (the disk criterion, HE6:240–242), the unit immediately preceding the new span. This master names it only to fix a boundary … and consumes no disk criterion: what S1.7 clause 1 reads as "its roots lie in the intended disk" is LEMMA HE6-1's own conclusion that every root of \(\Psi_{\kappa,r}\) satisfies (T1)/(T2), inside the new span. Where HE6-0 is used, it is used inside HE6's own arguments … which is the source's business and not a master-side consumption.
> - **THEOREM HE6.A's statement display** (HE6:289–301). … This master names THEOREM HE6.A at two sites only: the `(PINS)` row description "the complete proof unit of THEOREM HE6.A", which names it to fix a boundary, and S4.1's grade line "HE6 is accepted \(2/2\)". S3.2's conclusion display \(|S_{\lambda,r}|=D'\ell\deg r\), \((e,f)=(e_1\ell,f_1\deg r)\) is this master's OWN clause-2 output at the instance, derived in S2's proof from `(SIDE-COUNT)`, `(RES-DEG)` and the test package — not consumed from HE6.A. Pinning it would cover no consumption. The asymmetry with HE3 is real and is adjudicated here rather than cured: `HE3-A-STMT` is pinned because S3.1's instance substitution reads THEOREM HE3.A's stated data, whereas S3.2's corresponding display is derived by this master and is not read from HE6.A.
> - **§S3.3** (the proof of LEMMA HE6-1), **§S4's two evaluation proofs**, and **§S6.1** (the proof of LEMMA HE6-5). What S3.2's line 889 credits to "HE6's ξ-side, evaluation formulas … and equivariance" are those lemmas' ASSERTIONS, now inside `HE6-TEST-PACKAGE`; this master consumes none of their proofs and reproves none of them.”

**DERIVATION:** `[SIGNED NON-APPLICABILITY]` Each declination applies the consumption test: a unit is pinned when the master reads a claim from it, not when the master names it. Boundary-fixing citations (LEMMA HE6-0, the `(PINS)` row description) and grade lines are naming, not consumption; a display the master derives itself (S3.2's conclusion) is not consumed from the source that also states it; and a lemma's proof is not consumed when only its assertion is read. The HE3/HE6 asymmetry is adjudicated on exactly this test rather than cured by adding a pin.

**CONDITIONALITY:** The declinations are scoped per consumption, as at shard 2 `.47`: declining LEMMA HE6-0 as a supplier of the disk criterion is not a statement that HE6-0 is unused inside HE6's own arguments. Should a later round read a claim from any declined unit, the declination would have to be revisited.

**RESOLUTION TRACE:** r10 repair 1(c) (3916–3920). Destination: the `(PINS)` table's coverage claim → shard 1, `.03`; the two crediting sentences (889, 1454) are located and left unamended.

**TEETH:** the standing S7 consumption sweep (a declination must be signed, not silent); S7 pin gate condition 1.

---

### EFF.T2.80  [table]

**CANONICAL STATEMENT:** `[TABLE — r10's inventory bookkeeping (repair 1(e))]`

| Quantity | Value set at r10 | Status |
|---|---|---|
| Pin count | 35 — “Pin arithmetic for the gate: 26 (r2) → 27 (r3 repair 1 splits `HETOW-LABELS`) → 29 (r4 repair 13 adds two) → 32 (r5 adds three) → **35** (r10 adds three).” | **Superseded** to 37 (r11 +1, r12 +1) |
| Taxonomy | “Totals: 18 pairs + 4 first-only + 13 description-only = 35.” | **Superseded** to \(20+4+13=37\) |
| Quoted-pair roster | “… `HE6-PROOF` (r6); and `HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-ACCOUNT` (r10) — **18 of 35**.” | Superseded as a count; the roster's membership stands |
| Cured-consumption census | “**Eight** consumptions have been cured this way.” — five at r4/r5, three at r10 | **Superseded** to nine (r11) and ten (r12/acceptance) |
| r4 repair 13's count clause | “so the count of cured consumptions reads two of five; the r9 + rider pass then found the r5 sweep incomplete in turn, and three further consumptions were cured at r10, so the count now reads two of eight.” | Superseded to “two of ten” |
| Synthetic markers / source edits | zero / zero | Effective; confirmed at acceptance |

A self-correction is recorded with the census:

> “(The superseded sentence also miscounted its own list, reading "Four" against the five cures it then names. The list is the authority; the corrected total counts those five together with this round's three.)”

**DERIVATION:** `[BOOKKEEPING]` Each figure is derived from the round's own three additions, and the arithmetic chain is stated so the gate can re-derive it rather than trust a total. The census correction applies the note's standing rule that an enumeration governs its own count.

**CONDITIONALITY:** Every count here is superseded downstream. The rule the round applies — list over total — is not.

**RESOLUTION TRACE:** r10 repair 1(e) (3929–3965); eleven superseded strings landmark-verified at 1 under bound 3843, at lines 2900 (×2), 3123, 3391, 2791, 2799, 2858, 2859, 3449, 3455, 3461. Destination: base S0.2 and the S7 pin gate → shard 1, `.03` and `.42`.

**TEETH:** S7 pin gate; the pin-sweep leg of the acceptance gate.

---

### EFF.T2.81  [table]

**CANONICAL STATEMENT:** `[TABLE / ASSEMBLED — the r10 re-run of the standing consumption sweep (repair 1(g))]`

| Class examined | Disposition |
|---|---|
| HE6 §S5 | pinned entire, as `HE6-ACCOUNT` |
| HE6 §S4 | COROLLARY HE6-2″ pinned as `HE6-ROOT-LABEL`; the two evaluation proofs not consumed |
| HE6 §S3.3, §S6.1 | not consumed; what is consumed is each lemma's statement display, all seven pinned as `HE6-TEST-PACKAGE` |
| r5's six residues (LEMMA HETOW-3, LEMMA GENTOW-4.1, LEMMA HE7-13, DEFINITION HE6-1, GENHN-3(a), HE3's `[r1-N1]`) | unchanged |
| HE6's six dated appends | PE4 Correction 2 and the 2026-08-12 F-2 “touch material now inside a new span and are noted at their pins”; PE4 Correction 1, 2026-08-12 F-1, F-3 and F-4 “touch nothing this master consumes” |
| Boundary-fixing and declining quotations (HE6:668 at master 3118; the GENTOW4 TOWERRAT2-C annex heading at master 2564) | “remain declinations, not consumptions, and are unaffected” |

> “This enumeration is recorded, not asserted complete; the gate re-runs it.”

**DERIVATION:** `[SWEEP RECORD]` The sweep is the standing S7 check (installed r4 repair 13) re-run at the two level-one records, in answer to the same check's own earlier incompleteness. Its new element is the **dated-append class**: each of HE6's six appends is tested for whether it touches material this master consumes — the test r11 later generalises as an asymmetry test and r12 applies to the five non-HE6 sources.

**CONDITIONALITY:** Declared incomplete by construction. Its dated-append leg is HE6-only; the other five sources are swept for the first time at r12 (shard 5).

**RESOLUTION TRACE:** r10 repair 1(g) (3991); the two source-side append lines (HE6:1036, 1115) re-verified at 1 (§3, part A).

**TEETH:** the standing S7 consumption sweep; the pin-note directive coherence audit.

---
### EFF.T2.82  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r10 counter; the r10 header and repairs are homed at EFF.T2.76–.81]`

> “r10 folds repairs for the single GAP (G-1) and the single minor (m-1) of the Opus-arm confirmation pass `runs/comp13/T2P8_output.log` … The finding is credited to that pass in full: it is the first end-to-end run of the S7 pin gate's standing consumption check on the final text, and running it is what produced the finding.”

> “**No theorem-statement change is made by this round.** … S1.7 — the section whose closing sentence the finding quotes — is not amended: what changes is the pin table that sentence refers to. The minor narrows one qualifier inside the post-pass rider by one condition, and every consumer of the qualified sentence already reads it above that condition.”

> “**Two named obligations remain open** … and no new fence is added: HE6 supplies `(ACCOUNT)` and every test assertion at the configuration the records read them in, so no consumption had to be re-routed or fenced.”

> “The rider's counter statement — "the clean-pass counter is NOT reset and STANDS AT 1 OF 2" — recorded the state after a minors-only pass, pending the Opus-arm confirmation pass it named as still owed; that pass returned a GAP, so the state is superseded here rather than amended. **The clean-pass counter is RESET to 0 of 2.**”

**DERIVATION:** `[ROUND RECORD]` The counter's own reasoning is the campaign rule applied twice: a minors-only pass leaves the count standing, and the very next gap-bearing pass resets it. The round books no statement change because the defect was in the pin table, not in any display — the same classification r11 and r12 will make.

**CONDITIONALITY:** Historical as to counter and pin count (35 → 37). The “no new fence” claim survives to acceptance: the obligation set never changes again.

**RESOLUTION TRACE:** source lines 4019–4031; header and repairs at 3847–4017 (shard 4); superseded as to status by the acceptance record.

**TEETH:** S7 acceptance gate; S7 pin gate (the tooth that produced the finding).

---

### EFF.T2.83  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r11 round record: provenance, what the pass verified, and the counter]`

> “*(Opus/Claude repair arm, against the model-diverse sol pass of record `runs/comp13/T2SOL3_output.log`, taken over the r10 effective text and returning 0 CRITICAL + 1 GAP + 0 minors; counter resets.)*”

> “**What the pass verified, and what this round does not touch.** The pass re-derived r10's three new spans at byte level and upheld all three … It checked the mathematics of the sharpest one independently: this master's `(ACCOUNT)` is HE6's identity (†) after the root-slope regrouping displayed at HE6:545–547, and HE6 proves (†) for every rational \(\kappa>D'h\), wider than the master's range. It confirmed that the 2026-08-12 F-2 correction at HE6:1115 reaches only LEMMA HE6-3(a), which this master rederives, hence no consumed material. It re-ran the pin inventory (\(18+4+13=35\); all eighteen pairs' delimiters and the four first-only delimiters unique; all thirteen description-only rows resolving uniquely; no `T2V2PIN` line in any of the six sources; source worktree clean) and the cured-consumption census (Four → Eight), and found both correct. Its independent theorem, rank and fence audit returned nothing. … The GAP is again in the pin table and not in the master core, the r9 coherent-frame rebuild, or the r10 mathematics: one source unit that r10's own pin note directs the reader to obey lies outside every span.”

> “**No theorem-statement change is made by this round.** … no mathematical claim of this master changes truth value: the correction narrows a supplier's guard to the case in which the master already reads it, so the consumed dichotomy is byte-unchanged and nothing had to be re-routed or fenced.”

> “**The clean-pass counter is RESET to 0 of 2.**”

**DERIVATION:** `[ROUND RECORD]` The round's shape is fixed by where the pass's verification stopped: three spans upheld, arithmetic upheld, mathematics upheld, and one directive found outside every span. The cure is therefore a pin, not an amendment — “cured by pinning rather than by amending any sentence”.

**CONDITIONALITY:** Historical as to counter and pin count (36 → 37). Its own census sentence (“Those are the only two sites.”) is superseded inside this shard by Rider 2.1 (`.86`).

**RESOLUTION TRACE:** source lines 4035–4041 (header, protocol, verification list) and 4150–4162 (counter).

**TEETH:** S7 acceptance gate; S7 pin gate; the standing consumption sweep.

---

### EFF.T2.84  [table]

**CANONICAL STATEMENT:** `[TABLE — the HE6-BETA-GUARD pin, its S0.2 adjudication and its reading directive]`

| Field | Content |
|---|---|
| Pin | `HE6-BETA-GUARD` — “HE6's post-PE4 **Correction 2**, the bolded unit closing the `### Dated acceptance record + corrections (2026-08-09, post-PE4)` section (1036–1047)” |
| Row | `&\texttt{HE6-BETA-GUARD}&\text{HE6's post-PE4 Correction 2 (LEMMA HE6-2's }\beta\text{-definedness guard, re-scoped to }\delta=\kappa\text{)}\\` |
| First delimiter | `**Correction 2 (PE4 F-2 — LEMMA HE6-2's β-definedness guard).** The` (HE6:1036) |
| Last delimiter | `lemma's conclusion and its consumers are unaffected by this re-scoping.` (HE6:1047) |
| Condition 1 | “the designation is borne by exactly one unit in the file … so no outermost-unit adjudication is needed” |
| Condition 4 | “the unit runs from its bolded opening line to the last nonblank content line before the section-separating horizontal rule at 1049, which is a boundary marker and not unit content … the next unit of equal or higher rank is `### Dated corrections (2026-08-12 — sol certification A3: the R6 chain challenge adjudicated at HEAD)` at 1051 … and the preceding sibling unit is Correction 1 … at 1022” |
| Operative directive inside the span | `the guard as **"when δ = κ"** — the defining case, where the element is a` (HE6:1041) |

The reading directive attached at the pin:

> “This pin is a reading directive for `HE6-TEST-PACKAGE`, not an independent assertion: it fixes the guard under which LEMMA HE6-2's statement display, inside that span, is read. This master consumes from it exactly one thing — that the \(\beta\) named in the display's dichotomy is confined to \(\delta=\kappa\), where it is a unit residue. The unit's remaining content, the source's own site check over HE6-3, HE6-4 and THEOREM HE6.A, is the source's business and is not consumed here.”

and the two citation sites it is cited at:

> “**The 2026-08-09 post-PE4 correction governs, and is itself pinned, as `HE6-BETA-GUARD` (r11).**”

> “(266). → `HE6-TEST-PACKAGE`, read under `HE6-BETA-GUARD`: the corrected guard is what confines the \(\beta\) of LEMMA HE6-2's dichotomy to \(\delta=\kappa\), where it is defined, while this master's "away from that label class" half of clause 2 is the contrapositive \(\delta\ne\kappa\Rightarrow\varepsilon(\xi)=0\), which names no \(\beta\).”

**DERIVATION:** `[PIN DERIVATION]` The pin exists because r10 “recorded the correction as a reading directive and cited it by opening line and line number without pinning it”, which the note's own standing check forbids: “A consumption outside every span fails the gate”, with r11's adjudication that “a directive the reader is told to obey is consumed material”. The span form is the bolded-unit-outside-a-blockquote configuration already adjudicated at HE3's `[r2]` CONSTRUCTION PIN and at `HE6-ROOT-LABEL`. All five source lines (1022, 1036, 1041, 1047, 1051) re-verified at 1 at their recorded numbers (§3, part A).

**CONDITIONALITY:** The pin is a reading directive, not an independent assertion: exactly one thing is consumed from it. The source's own downstream site check is explicitly not consumed — a classification Rider 2.1 later tests and upholds (`.86`). The pin count it sets (36) is superseded to 37 inside this shard.

**RESOLUTION TRACE:** r11 repair 1(b)–(c) (4057–4088). Destination of the row: base S0.2 → shard 1, `.03` (XREF X18).

**TEETH:** S7 pin gate conditions 1–4; the standing consumption sweep; the pin-note directive coherence audit.

---

### EFF.T2.85  [lemma]

**CANONICAL STATEMENT:** `[ASSEMBLED — why the β-guard correction is consumed although the consumed conclusion is byte-unchanged (r11 repair 1(a))]`

> “What this master reads off that display is one dichotomy, \(\varepsilon(\xi)>0\iff\delta=\kappa\) and \(\iota_\xi(r)(\beta)=0\), whose two halves are the clause's two halves. The display's own guard as written, "when \(\delta\) has denominator dividing \(\ell\)", admits \(\delta\ne\kappa\) with \(\ell\delta\in\mathbb Z\); at such a \(\delta\) the element whose residue \(\beta\) is has valuation \(\ell\delta-u\ne0\) — the source's own instance is \(\delta=2\), \(\kappa=5/2\), \(\ell=2\), \(u=5\), giving \(dv=-1\) — so \(\beta\) is undefined there, on part of the very domain over which "away from that label class" ranges. Reading the guard as "when \(\delta=\kappa\)" removes that: \(\beta\) is confined to the case in which the element is a unit and \(\beta\) a unit residue.”

> “The narrowing costs this master nothing, and that is why no fence is added and no consumption is re-routed. The half of clause 2 that consults \(\beta\) is the \(\Leftarrow\) direction, invoked only at \(\delta=\kappa\), which is inside the corrected guard; the half read away from the class is the contrapositive \(\delta\ne\kappa\Rightarrow\varepsilon(\xi)=0\), which names no \(\beta\) at all. So the conclusion this master takes is byte-unchanged under the correction — exactly as r10's note says — while the correction is nevertheless consumed, as the hypothesis under which that conclusion is well posed on the advertised domain. **Both statements are true at once, and the second is the one the pin table has to answer for.**”

**DERIVATION:** `[WELL-POSEDNESS ANALYSIS]` The argument separates the two halves of a consumed dichotomy by which of them names \(\beta\): the \(\Leftarrow\) half is invoked only where the corrected guard holds, and the \(\Rightarrow\) half names no \(\beta\). The correction therefore changes no consumed assertion while supplying the hypothesis that makes one of them well posed over the domain S1.7 clause 2 advertises. The counterexample instance (\(\delta=2\), \(\kappa=5/2\), \(\ell=2\), \(u=5\), \(dv=-1\)) is the source's own and shows the uncorrected guard genuinely admits an undefined \(\beta\).

**CONDITIONALITY:** No fence is added and no consumption is re-routed; the analysis is what licenses that. It is the general shape of the note's late-round cures — the same distinction (a directive that changes what is *read* versus one that changes whether a read is *well posed*) is what r11 repair 1(f) turns into the asymmetry test and r12 applies corpus-wide.

**RESOLUTION TRACE:** r11 repair 1(a) (4053–4055). Destination: none in base — the analysis exists to justify the pin, and no sentence of S1.7, S3.1, S3.2 or r10's crediting text is amended.

**TEETH:** the HE6 test-package gate; S7 Pass 1 theorem gate (clause 2's supplier must be well posed); the standing consumption sweep.

---

### EFF.T2.86  [table]

**CANONICAL STATEMENT:** `[TABLE / ASSEMBLED — the effective consuming-site census for HE6-BETA-GUARD: r11's two direct sites, widened by Rider 2.1 with the transitive route]`

| Route | Site | Status |
|---|---|---|
| Direct citation 1 | r10 repair 1(b)'s reading directive at `HE6-TEST-PACKAGE` (master 3892) | amended to name the pin |
| Direct citation 2 | r10 repair 1(a) item 2, the itemised clause-2 consumption (master 3870) | amended to read “under `HE6-BETA-GUARD`” |
| Transitive route (a) | `* ρ-side: by LEMMA HE6-2 (with r₀ never a label's factor)` (HE6:545), inside `HE6-ACCOUNT`, head of the passage r10 item 8 quotes for `(ACCOUNT)` | recorded |
| Transitive route (b) | `* ρ-side: by LEMMA HE6-2, Σ_ρ dv(Ψ(ρ)) = ℓd_r·Σ_λ′ n_λ′ min(λ′,λ) +` (HE6:589), inside the proof of LEMMA HE6-4 that r10 item 3 consumes | recorded |

The effective census sentence:

> “Those are the only two sites at which this master CITES the correction by name; they are not the only routes by which it is CONSUMED. One further route is TRANSITIVE, through the pinned span `HE6-ACCOUNT` … whose text invokes LEMMA HE6-2 at ARBITRARY roots at exactly two places. … Both run over roots \(\rho\) of \(f\) whose \(\delta=\lambda_\rho\) is in general \(\ne\kappa\), and both read the piecewise value \(\ell d\cdot\min(\delta,\kappa)\) there; that reading is well posed only under the corrected guard, which at \(\delta\ne\kappa\) yields \(\varepsilon(\rho)=0\) from the forward half of the dichotomy and names no \(\beta\) at all … So the census reads: TWO direct citation sites, plus a transitive route at the two source lines 545 and 589 inside `HE6-ACCOUNT`. Coverage is unaffected …: `HE6-BETA-GUARD` is pinned by (b), and by (e) it stands on all five Source-pin lines — the same five that already carry `HE6-ACCOUNT` — so wherever the transitive route runs, the guard is already declared alongside the span that runs it.”

The pin note is classified and left standing:

> “Its closing sentence … is about the source's own VERDICT on its downstream sites (`passPE4's site check, HE6-3/HE6-4/THEOREM HE6.A read ε through that`, HE6:1044 …), not about the corrected guard itself. That verdict remains unconsumed … The third name in that sentence's list, THEOREM HE6.A, adds no route: this master's only consumption of HE6.A's proof is item 1 at HE6:644–648 inside `HE6-PROOF`, which takes \(\beta_\rho\) from COROLLARY HE6-2″ (`HE6-ROOT-LABEL`) at the root's own slope — r11 (c)'s unit case, where \(\beta\) is defined without appeal to LEMMA HE6-2's guard.”

**DERIVATION:** `[CENSUS WIDENING]` The widening applies r11's own test one step further: “naming and consuming are not the same relation — the whole ground on which r11 itself pinned `HE6-BETA-GUARD` was that a directive the reader is told to obey is consumed material whether or not it is cited.” Since the master consumes `HE6-ACCOUNT`'s proof text and that text invokes LEMMA HE6-2 at roots off the label class, the guard is consumed there too. Coverage is untouched because the route lands on pins and lines that already carry the guard. Both source lines re-verified at 1 (§3, part A).

**CONDITIONALITY:** A census widening, not a repair: “this rider curing no consumption but recording a further route to one already cured.” The pin count stays 36 at this point (37 after r12), the taxonomy \(19+4+13\), the census nine, and r11 (e)/(f) stand unchanged.

**RESOLUTION TRACE:** r11 repair 1(c)'s census sentence (landmark at line 4088, bound 4162) replaced by Rider 2.1's cure (4186–4194); the pin note's closing sentence (4070) classified and **not** amended.

**TEETH:** the standing consumption sweep (naming-versus-consuming); the pin-note directive coherence audit; the `(ACCOUNT)` supplier gate.

---

### EFF.T2.87  [acceptance-box]

**CANONICAL STATEMENT:** `[ASSEMBLED — post-pass rider block 2: the fold rule, the landmark convention and the counter state]`

> “**Dated rider (2026-08-13 — the single minor of the gpt-5.6-sol high hostile pass on the r11 effective text, `runs/comp13/T2SOL4_output.log`, returning 0 CRITICAL + 0 GAP + 1 minor. Folded per the campaign's minors-only precedent — T4's post-pass gloss-direction rider, T5's two post-pass-1 locator riders, T1's five post-pass-1 riders, and this note's own first post-pass rider block above, each folded on a 0 CRITICAL + 0 GAP pass and none of them a grade event. NO r-section, no grade event, NO counter reset.)** The rider WIDENS one census sentence and does nothing else.”

> “no new source consumption is created — the two source lines the widened census names, HE6:545 and HE6:589, both lie inside the already-pinned span `HE6-ACCOUNT` [525,604], and 545 is already quoted verbatim by r10 repair 1(a) item 8.”

> “**Landmark convention (rider).** Counts are taken over the note AS IT STOOD BEFORE THIS BLOCK — lines 1–4162, i.e. through the last line of the r11 counter”

> “Folding riders is not a repair round: **the clean-pass counter is NOT reset and STANDS AT 1 OF 2.** Pass of record: the gpt-5.6-sol high hostile pass on the r11 effective text, `runs/comp13/T2SOL4_output.log`, 2026-08-13 — this note's fourth model-diverse pass and its second clean one. Still owed at the S7 acceptance gate: the Opus/Claude-arm confirmation pass, the second of the two consecutive clean passes, taken over the r11 effective text PLUS this rider.”

**DERIVATION:** `[COUNTER-STATE RECORD]` The fold rule is S7's reset rule read literally (stated of gap-or-worse repairs only), with the campaign precedent now including this note's own first rider block. The “no new source consumption” claim is checked rather than asserted: both named lines already lie inside a pinned span and one is already quoted.

**CONDITIONALITY:** The 1-of-2 counter is superseded: the confirmation pass this block awaits (`T2P9`, r12's pass of record) returned 0C+1G+2m, so the counter resets at r12 and reaches 2/2 only at post-pass rider 3 (shard 6).

**RESOLUTION TRACE:** source lines 4166–4202.

**TEETH:** S7 acceptance gate; the minors-only fold precedent.

---

### EFF.T2.88  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — the r12 round record: provenance, what the pass verified, the theorem-statement status, and the counter]`

> “*(Opus/Claude repair arm, against the Opus/Claude confirmation pass of record `runs/comp13/T2P9_output.log`, taken over the r11 effective text PLUS both post-pass rider blocks and returning 0 CRITICAL + 1 GAP + 2 minors, with five non-counted nits; counter resets.)*”

> “**What the pass verified, and what this round does not touch.** The pass read the master theorem statement AS EFFECTIVELY AMENDED — the hypothesis line, clauses 1–6, `(REF-HT)` = (RISE) + (HT) entering through the root-preserving continuation suite, and both triggers of clause 5 — assembled it whole and found it coherent, with every symbol bound before use, the one apparent hypothesis collision (clause 5 firing at \(d(\widetilde\Phi(\rho))=+\infty\), which `(WINDOW)` excludes) resolved in the right order by the existing text, and every clause's proof-supplier named; it re-ran (RISE) \(\Rightarrow\) (HT) and r9 repair 1(b)'s digit derivation rather than reading them, and both are sound. It read all seventeen effective S5 obligation items against the effective text and upheld sixteen … It checked the `(GRADE)` machinery and the status line, and found no sentence anywhere claiming a grade above \(0/2\). It re-ran S0.1's original-\(O\) redline against every r-round addition individually and found no violation. It re-verified eight pins at the bytes …, all eight supersession landmarks at the bound and the line each round declares, and recomputed the pin inventory and its taxonomy by enumeration rather than reading them off the totals — \(19+4+13=36\), matching r11 repair 1(d). … The GAP is again in the pin table and its consequences, and again on a dated source correction lying outside every span — this time found by the FIRST exhaustive dated-append sweep over the five NON-HE6 sources”

> “**Theorem-statement status of this round.** No display of the statement suite S1.2–S1.8 is amended in its assertions, no hypothesis is added to or removed from HE7.A's clause suite, no case is added or dropped, no conclusion is touched, and no mathematical claim of this master changes truth value. One item of CARRIER DATA is made explicit rather than left to a phrase … Repair 1's addition to S1.8B is a derivation, not a hypothesis: it replaces an imported conjunct by a two-line argument from displays already present.”

> “**Two named obligations remain open** … No fence is added by this round — the \(w\ne0\) branch is discharged, not fenced … the expected pin count is now **37**, with taxonomy \(20+4+13\) … The cured-consumption census stands at ten.”

> “**The clean-pass counter is RESET to 0 of 2.** … The r11 rider block's closing statement — that the counter stood at 1 of 2 with the Opus/Claude confirmation pass owed as pass 2 of 2 — is answered by that pass's verdict of 0 CRITICAL + 1 GAP + 2 minors and is superseded by this counter.”

**DERIVATION:** `[ROUND RECORD]` The round is the last of the arc, and its own accounting is what the acceptance record then quotes: statement verified whole as effectively amended, sixteen of seventeen S5 items upheld, inventory recomputed by enumeration, and a first-ever sweep class (non-HE6 dated appends) producing exactly one hit. The theorem-statement paragraph distinguishes three things carefully — a display amendment (none), a carrier-data addition (one, discharged in all five boxes), and a derivation replacing an import (one).

**CONDITIONALITY:** Historical as to counter only. Its pin count (37), taxonomy (\(20+4+13\)) and census (ten) are **final** and are what the acceptance record confirms.

**RESOLUTION TRACE:** source lines 4206–4212 (header, protocol, verification list) and 4427–4439 (counter). Confirmed by the acceptance record's arc paragraph and machine-evidence paragraph (shard 6).

**TEETH:** S7 acceptance gate; S7 pin gate; the standing consumption sweep; the dated-append sweep (new class).

---

### EFF.T2.89  [table]

**CANONICAL STATEMENT:** `[TABLE — the HETOW-KEY-BRIDGE-C-A pin, its S0.2 adjudication, the minimal-span argument, and its reading directive]`

| Field | Content |
|---|---|
| Pin | `HETOW-KEY-BRIDGE-C-A` — “HETOW's post-PE2 **correction C-A**, the bolded unit opening the `### Dated corrections (2026-08-09, post-PE2)` section (548–569)” |
| Row | `&\texttt{HETOW-KEY-BRIDGE-C-A}&\text{HETOW's post-PE2 correction C-A (LEMMA HETOW-2's F-2 paragraph: the withdrawn exemplar, and the re-scoping of the closing HE7-12 licence to }w=0\text{)}\\` |
| First delimiter | `**C-A (cures PE2 F-A — LEMMA HETOW-2's F-2 paragraph, §S2).** Two` (HETOW:548) |
| Last delimiter | `the withdrawn exemplar or the corner.` (HETOW:569) |
| Condition 1 | “the designation is borne by exactly one unit in the file — `grep -cF -- 'C-A (cures PE2 F-A'` → **1**, at line 548 — so no outermost-unit adjudication is needed” |
| Condition 4 | “the unit runs from its bolded opening line to its last content line before the next unit of equal rank, the sibling correction … (571), with 570 blank; nothing of equal or higher rank intervenes, the enclosing `###` heading standing at 539 … and the next unit of higher rank being `### Dated acceptance record + correction (2026-08-09, post-PE3)` (608)” |
| Governed sentence | `> T₂. Either way LEMMA HE7-12 [r2, r3] applies (its W = 0 split` (HETOW:261), inside `HETOW-KEY-BRIDGE` [198,262] |

Why the whole unit:

> “The finding's cure sketch named HETOW 557–569, the range of half (ii) alone. That range begins mid-sentence, at a line that is no unit boundary, and would fail S0.2 condition 4 … and the convention's requirement that a delimiter be the complete first nonblank line of a unit. The minimal span admissible under the convention is the bolded C-A unit, and it is the one declared.”

The reading directive attached at the pin:

> “This pin is a reading directive for `HETOW-KEY-BRIDGE`, not an independent assertion: it fixes the branch in which LEMMA HETOW-2's closing sentence, inside that span at HETOW 261–262, may be used as a licence for LEMMA HE7-12. The directive scopes that licence to \(w=0\) … This master obeys the directive and takes nothing from that closing sentence in the \(w\ne0\) branch: S1.8B's scope clause supplies \(\deg w<D''\) from the monicity of \(\Phi_2\) and \(\Psi_{\kappa_2,\widetilde r}\), and reads from `HETOW-KEY-BRIDGE` only the value disjunct "either w = 0 … or dv₂(w) > T₂", which the correction expressly leaves standing … Half (i) of the correction — the withdrawal of the F-2 exemplar — reaches nothing this master reads; and the \(\Psi\)-membership clause of LEMMA HETOW-2's statement, which this master does consume, is untouched by both halves.”

**DERIVATION:** `[PIN DERIVATION]` The gate failure is precise: “a dated directive governing a sentence INSIDE a pinned span, and telling the reader in which branch that sentence may be used, is consumed material under this note's own test”. The correction's reach is fixed from inside the unit itself — the accounting core is expressly left standing (564–565), and the correction's own 2026-08-09 consumer trace names two consumers, so “this master … is therefore an untraced third consumer”. Sixteen HETOW lines re-verified at 1 at their recorded numbers (§3, part A), including the three boundary witnesses 539, 571 and 608 which lie outside the span.

**CONDITIONALITY:** “The correction is pinned regardless, because pinning is owed for the directive itself and not only for the mathematics it would have blocked.” This is the last pin: the inventory closes at 37.

**RESOLUTION TRACE:** r12 repair 1(a) and 1(d) (4224, 4244–4259). Destination of the row: base S0.2 → shard 1, `.03` (XREF X31). Certified minimal under S0.2 by pass 1 of record at acceptance.

**TEETH:** S7 pin gate conditions 1–4; the dated-append sweep; the pin-note directive coherence audit.

---

### EFF.T2.90  [lemma]

**CANONICAL STATEMENT:** `[ASSEMBLED — the master-side degree bound replacing the imported conjunct in S1.8B's composed-key scope clause (r12 repair 1(b)–(c)); destination base S1.8B, shard 1 EFF.T2.24]`

> “LEMMA HE7-12's remaining hypothesis \(\deg w<D''\) is supplied here by this master, from the monicity of the two keys: \(\Phi_2\) is monic of degree \(D_2\) (S1.1's carrier requirement at `(HETOW-INSTANCE)`/`(GENTOW4-INSTANCE)`), \(\Psi_{\kappa_2,\widetilde r}\) is monic of degree \(D''\) (the same requirement at `(HE7-INSTANCE)`, read at the level-two datum \((\kappa_2,\widetilde r)\) that LEMMA HETOW-2's \(\Psi\)-membership clause and `GENTOW-4-1`(b) certify as one), and \(D''=D'\ell d_r=D'e_2f_2=D_2\) since the boxes' invariant entries force \(\ell=e_2\) and \(d_{\widetilde r}=f_2\); so \(w=\Psi_{\kappa_2,\widetilde r}-\Phi_2\) is \(0\) or of degree \(<D''\) by cancellation of leading terms.”

The over-read that is corrected in the same clause:

> “`GENTOW-4-1` clause (c) gives that same disjunct at the partial tower, in its own words "Phi2 = Psi_{kappa2,rtilde} − w with w = 0 or dv2(w) > T2"; reading that clause as giving "the same" INCLUDING a degree bound over-read it by one conjunct, since it states none.”

Why the corner cannot bite:

> “The corner C-A(ii) names is a PRESENTATION whose slot coefficient is augmented by above-height junk of \(x\)-degree \(\ge D'\); at \(e_2=1,\ t=f_2-1\) the moved piece lands at the leading slot \(e_2f_2\), which is exactly to say the presented object carries an \(x\)-degree-\(\ge D''\) term. Such an object is not monic of degree \(D_2\), and so is not the key that `(HETOW-INSTANCE)`/`(GENTOW4-INSTANCE)` substitute … The re-scoping therefore removes a licence this master no longer uses, and removes nothing this master needs.”

The accumulated increment:

> “**The accumulated increment, checked rather than assumed.** The composition S1.8B performs is \(W\leftarrow w+W\) with \(W=w_1+\dots+w_j\) the refine increments, so the degree bound is owed for the SUM and not only for \(w\). Each \(w_i\) is a legal lift, and S1.4's `(LIFT)` display bounds every legal lift by the current degree, \(\deg L_k(c)<D\), which at a level-two state is \(\deg w_i<D''\); a sum of finitely many polynomials of degree \(<D''\) has degree \(<D''\), the bound being the maximum and no cancellation being needed. That is also what the source states of the fold itself, inside `HE7-PERT-TRANSPORT`: `> (d) *(chains fold into one application)* if w₁, …, w_j each have degree` (842), `> < D″ and slot value > T₂ then W := w₁ + ⋯ + w_j has deg W < D″ and` (843). So no use site of the scope clause — entry increment, refine increment, or accumulated \(W\) — needs the re-scoped licence, and none of them meets the corner.”

**DERIVATION:** `[MASTER-SIDE DERIVATION REPLACING AN IMPORT]` Three master-side facts compose: both keys are monic by S1.1's carrier requirement as substituted in the instance boxes; their degrees coincide because the boxes' own invariant entries force \(\ell=e_2\) and \(d_{\widetilde r}=f_2\) (checked against the two \(T_2\) expressions agreeing at \(u=u_2\)); hence the difference of two monic polynomials of equal degree is \(0\) or of strictly smaller degree. LEMMA HE7-12's hypothesis line, `> with key Ψ (DEFINITION HE7-1), and let w ∈ O[x], w ≠ 0, with deg w < D″` (HE7:814), is the target being met. The accumulated-increment leg uses `(LIFT)`'s degree bound and is corroborated by HE7-12(d)'s own fold statement.

**CONDITIONALITY:** After r12 the \(w\ne0\) branch “consumes no re-scoped licence at all”; only the **value** disjunct is read from a source statement. The derivation is a derivation, not a hypothesis: “it replaces an imported conjunct by a two-line argument from displays already present.” It presupposes the instance boxes' monicity, which S3's own rule (“no instance may add a premise absent from the master or silently omit one of its hypotheses”) makes obligatory.

**RESOLUTION TRACE:** r12 repair 1(b)–(c) (4226–4242), replacing r6 repair 6(a)'s scope-clause passage (landmark at line 3223, bound 4202). Five source lines re-verified (HE7:814, 842, 843; GENTOW4:184, 185). Destination: base S1.8B → shard 1, `.24`, whose `DERIVATION` compresses this to one sentence.

**TEETH:** the composed-key transport tooth; the accumulated-degree tooth; HETOW's C-A dated-directive tooth; the GENTOW4 perimeter gate.

---

### EFF.T2.91  [table]

**CANONICAL STATEMENT:** `[TABLE / ASSEMBLED — the first exhaustive dated-append sweep over the five non-HE6 sources (r12 repair 1(g)), with the pass's dispositions adopted]`

> “The pass ran, for the first time, the r10/r11-style dated-append sweep outside HE6, testing each unit against r11 repair 1(f)'s asymmetry test (does obeying it change something this master reads?). Its enumeration is adopted and recorded here so that the gate can check rather than repeat it; the dispositions are the pass's, re-derived in this round only at the one hit.”

| Unit | Disposition |
|---|---|
| HE3:1577 (post-PE3, M-1 — §S1(iii)'s starved-corner parenthetical) | “not consumed; this master reads no \(|K^\times|\)-starvation clause” |
| HE3:1622 (the sol A5 umbrella over R8-1…R8-5) | “R8-2 through R8-5 are pinned (r4 repair 6), R8-1 is declined, and the heading carries no directive on consumed material” |
| HE7:2478 (post-annex-acceptance, riders M-1, M-A, M-B) | “M-1 is a run-record counter and M-A an oracle name, neither consumed; M-B is a provenance rider on THEOREM HE7.D's §S2 clause and COROLLARY HE7.B(ii)” — the ground of the M-B disposition is **re-grounded on consumption by post-pass rider 3** (shard 6); the disposition itself is unchanged |
| HE7:2501 (from HE6 PE2 F-1) | “it lands on LEMMA HE7-L1's §S4.1 display (HE7 379–393), which lies outside every span, and is not consumed” |
| HE6R1:790 (post-PE3, F-1 — the cocycle exponent is the PIN height) | “not consumed; S3.4/S3.5 already read the corrected form … and consume only the existence of a fixed nonzero scalar and cocycle unit, which the correction itself declares unchanged” |
| HE6R1:1031 (the R7 re-display of HE6R1-1's global bound) | “already noted at pin `HE6R1-1` by r3 repair 3; its companion routing of R7 finding 2 is count-side, which S4.1 excludes” |
| HETOW:539, correction C-A | “**the hit**, pinned above as `HETOW-KEY-BRIDGE-C-A`. Its siblings C-B … and C-C … are not consumed” |
| HETOW:608 (post-PE3, F-α — BOX-3's \(e_2f_2\ge4\) row) | “not consumed” |
| HETOW:656 (TOWERRAT-R1 / LEMMA HETOW-4) | “is itself the pinned `HETOW-NORMALIZER-4`, and the J-D0 row supersession is already noted at `HETOW-LABELS` by r3 repair 1(c)” |
| HETOW:837 (the 2026-08-12 S-2/LEMMA COCYCLE-TELESCOPE absorption append) | “not consumed … The append declares the pinned LEMMA HETOW-4 absorbed by S-2's LEMMA COCYCLE-TELESCOPE while stating that the lemma statement above stays byte-frozen and authoritative (857–859), and the one clause this master reads from it — \(\tau(k)=\eta^{-Q(m(k))}\), S3.4's per-height residue — is left with HETOW as source-local supply … Nothing is owed, and nothing is quoted from it here.” |
| GENTOW4:991 | “pinned as `GENTOW-ACCEPTANCE-FOLD`, and the TOWERRAT2-C annex is noted at `GENTOW-4-A` by r4 repair 12. GENTOW4's post-PE2 fold m-A (§S9, line 952) records the same \(w=0\) routing … it is named here as corroboration only, in the register r5 repair 4 fixed ("a declination is not a consumption").” |

> “This enumeration is recorded, not asserted complete; the gate re-runs it.”

**DERIVATION:** `[SWEEP RECORD]` The sweep's classifier is the asymmetry test, stated at r11 repair 1(f) and applied here to eleven units across five sources; exactly one changes something the master reads, and it is pinned. Two dispositions are cross-referenced rather than re-derived (HE6R1:1031 → r3 repair 3's pin note; HETOW:656 → the existing `HETOW-NORMALIZER-4` pin and r3 repair 1(c)'s note), and one is a nit disposition recorded rather than cured (HETOW:837).

**CONDITIONALITY:** Declared incomplete by construction. One row's *ground* is later corrected: post-pass rider 3 (shard 6) re-grounds the HE7:2478 / M-B entry on consumption rather than on naming, because the master does name both units once, at line 2136 — “the disposition itself is upheld on the consumption ground”.

**RESOLUTION TRACE:** r12 repair 1(g) (4329–4343); the HETOW:837 heading re-verified at 1 (§3, part A). Amended in its ground only by Rider 3.1 (4463–4469, shard 6).

**TEETH:** the standing S7 consumption sweep; the dated-append sweep as a class; the pin-note directive coherence audit.

---

### EFF.T2.92  [changes-record]

**CANONICAL STATEMENT:** `[VERBATIM — S3.1's export sentence corrected to what the effective text actually exports (r12 repair 2)]`

> “The source proves more than the master requests by having an irreducible local key, and the master proof does not use that strength: `(NO-IRR)` and S0.1's redline keep irreducibility of \(\Phi\) out of it, and S4.2 and S6 record the same of the current key at every level. The carrier data this record exports are monicity, degree and `(DEG-EF)`. One further export is not carrier data and not a master premise: irreducibility of the ORIGINAL level-one key \(\Phi'\), which r4 repair 4(b) takes from `HE6-PEEL-CONVENTION` — "the peeled factor Φ′ is irreducible of degree D′" — to discharge item 5 of the `(MID-PEEL)` input suite at a level-one state whose represented block is divided by \(\Phi'\) itself. That is a per-instance discharge of a clause-5 hypothesis, available at the original key only: a recentered \(\Phi''\) does not inherit it, which is why r4 repair 4(c) fences that configuration as `(MP1)`. It enters no step of the master proof.”

**DERIVATION:** `[HONESTY CORRECTION]` The base sentence claimed the instance “forgets that strength”, which stopped being true at r4 repair 4(b): the record does export \(\Phi'\)-irreducibility, as the item-5 discharge. The correction states both halves precisely — the master proof still uses none of it (so S0.1's redline, S4.2's exclusion and S6's “The key is monic only” all remain true as written), and the instance record does export it, at the original key only. The asymmetry with a recentered key is exactly what `(MP1)` fences.

**CONDITIONALITY:** The export is per-instance and original-key-only. Nothing else is amended: “S0.1's redline sentence, S4.2's exclusion of ‘irreducibility of the current key’ and S6's ‘The key is monic only’ are all statements about the master and remain true as written.”

**RESOLUTION TRACE:** r12 repair 2 (4351–4365), superseding base S3.1's sentence (landmark at line 832, bound 4202). Destination: base S3.1 → shard 1, `.33`, whose `DERIVATION` states the same fact in one clause (“Original-key irreducibility is exported only to discharge item 5 of the peel suite; it is not a master premise”).

**TEETH:** the reducible-key boundary gate; S4.2's exclusion list; the `(MP1)` fence; S0.1's original-\(O\)/no-irreducibility redline.

---

### EFF.T2.93  [fence]

**CANONICAL STATEMENT:** `[VERBATIM — S5 ledger item 3 restated on consumption, with the four defended out-of-span citation classes named (r12 repair 3)]`

> “3. Every source unit this master CONSUMES lies inside a span of `(PINS)`, resolved by S0.2's existing-text delimiters — a quoted first/last delimiter pair, a quoted first delimiter with the boundary rule, or a unique-unit description — and no source file is edited to install one, the expected synthetic-marker count being zero. Consumption, not citation, is the gated relation: S0.2's cure clause ("A source display that this master consumes but no pin covers …") and S7's standing check ("A consumption outside every span fails the gate") are both worded on it, and r11 repair 1(f)'s asymmetry test is how a directive is classified. Four classes of cited but unpinned material are admissible, and are admitted where they occur — supersession notices (r4 repair 12, GENTOW4's TOWERRAT2-C annex headings, quoted to record that the later correction governs); declinations (r4 repair 4(c) on HE3's bracketed `[r1-N1]` passage, under r5 repair 4's doctrine "a declination is not a consumption"); reading directives that fail the asymmetry test (HE6's 2026-08-12 F-2 append at HE6:1115, kept at `HE6-ACCOUNT` and deliberately not pinned, r11 repair 1(f)); and boundary-fixing quotations (HE6:1022, HE6:1051 and HE6:668, each quoted only to locate a span's edge and each strictly outside the span it bounds). A directive that does change something this master reads is not in those classes and is pinned: `HE6-BETA-GUARD` (r11) and `HETOW-KEY-BRIDGE-C-A` (r12).”

**DERIVATION:** `[LEDGER RESTATEMENT]` Two defects are cured at once: the item was worded on *citation* while every operative test of the note is worded on *consumption*, so “Under its literal wording the gate would fail on material the note has four times ruled admissible”; and its vocabulary (“paired begin/end pin”) was r1's marker convention, deleted wholesale by r2 repair 1. The restatement therefore states the operative relation, names the resolution forms S0.2 actually allows, and enumerates the four admissible citation classes with an instance of each.

**CONDITIONALITY:** The four classes are admissible **because** they fail the asymmetry test; a directive that passes it is pinned, and the two that did are named. r10 repair 1(d)'s earlier answer to this item “remains true under the restated wording, its four sections being consumed and pinned.”

**RESOLUTION TRACE:** r12 repair 3 (4369–4383), superseding base S5 item 3 (landmark at line 1194, bound 4202). Destination: base S5 → shard 1, `.40`, which quotes the restated item's operative clauses.

**TEETH:** the standing S7 consumption sweep; S7 pin gate; the pin-note directive coherence audit.

---

### EFF.T2.94  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — r12 repair 4's four nit cures]`

**(a) The two objects named \(L\):**

> “**Notation.** \(L_k(c)\), always written with its digit argument, is the legal lift of \(c\) at height \(k\) defined by this display, and \(L_\lambda(s)\) in S1.8, S1.8B and S1.8C is that object at \(k=\lambda\), \(c=s\). \(L_\lambda\) without an argument is a different object: the LENGTH of the side of slope \(\lambda\), fixed at `(HULL-LENGTH)` and read at clause 1's \(\sum L_\lambda=\mu\), at `(ACCOUNT)`, at `(DEG-SUM)` and at `(SIDE-COUNT)`'s \(n_\lambda=DL_\lambda\). The two share a letter and nothing else; neither ever appears in the other's form, and the argument decides which is meant.”

**(b) The value \(d\) displayed as carrier data** — inserted into S1.1 and quoted at shard 1 `.04`; its status is booked here:

> “This is an addition to what the carrier displays and is recorded as one; it is discharged as written in all five instance boxes (\(c_{\mathcal C}=e_1,\ e_1,\ \ell e_1,\ e_1e_2,\ e_1e_2\)), so no instance record is amended, and the property it displays was already in use at three steps — r6 repair 1(a)'s min display, r9 repair 1(b)'s residue subtraction, and the \(h(E)\ge\lambda\) step repair 4(d) now writes out.”

**(c) An unpinned unit listed under a “pinned” heading:**

> “(LEMMA HE6-0″, inside `HE6-SLOT-SEAM`; the same abbreviation occurs in LEMMA HE7-L1's proof at HE7 §S4.1, which lies inside no span of `(PINS)` and is named here as corroboration only, nothing being consumed from it)”

**(d) The elided \(h(E)<\lambda\) step**, completing the lift-freedom rider compiled at shard 4 `.71`:

> “nor can it have \(h(E)<\lambda\), because \(h(\Lambda)=\lambda\) and \(h(L_\lambda(s))=\lambda\) give \(d(\Lambda(\rho))=d(L_\lambda(s)(\rho))=\lambda\) by `(SLOT-V)`, whence \(d(E(\rho))\ge\lambda\) by the ultrametric inequality for \(d\) (S1.1), while a nonzero \(E\) of degree \(<D\) has \(d(E(\rho))=h(E)\) by `(SLOT-V)` again”

**DERIVATION:** `[NIT CURES, EACH WITH ITS GROUND]` (a) is a notation fence: two objects share the letter \(L\) and are always disambiguated by the presence of an argument, which was true but nowhere said. (b) makes explicit the valuation property already used at three named steps, and is possible without amending any instance because all five boxes already display their constant. (c) applies the consumption test to a corroborating citation. (d) closes the one gap in the lift-freedom argument by ruling out \(h(E)<\lambda\) from `(SLOT-V)` plus the ultrametric inequality that (b) has just made available — the two cures are connected, and that is why they are one repair.

**CONDITIONALITY:** (b) is the round's only addition to carrier data and is booked as such in the counter; it changes no instance record and no conclusion. (d) amends a clause of a derivation homed in shard 4, which was updated at compilation of this shard.

**RESOLUTION TRACE:** r12 repair 4(a)–(d) (4387–4423); four anchors landmark-verified at 1 under bound 4202 (lines 384, 157, 2522, 3739). Destinations: base S1.4 → shard 1 `.09`; base S1.1 → shard 1 `.04` (which quotes the \(d=c_{\mathcal C}v\) paragraph verbatim); r4 repair 9's parenthetical (shard 2 `.49` context); r9 repair 1(b) → shard 4 `.71`.

**TEETH:** S7 Pass 1 theorem gate (the ultrametric law is now displayed where it is used); the lift-choice tooth; the standing consumption sweep.

---

### EFF.T2.95  [table]

**CANONICAL STATEMENT:** `[TABLE — the final inventory bookkeeping (r11 repair 1(d), r12 repair 1(e))]`

| Quantity | r11 | r12 (final) |
|---|---|---|
| Pin count | 36 | **37** — “→ 32 (r5 adds three) → 35 (r10 adds three) → 36 (r11 adds one) → **37** (r12 adds one).” |
| Taxonomy | \(19+4+13=36\) | **\(20+4+13=37\)** — “The four first-only pins (`HE3-R8-2`, `HE3-R8-3`, `HE3-R8-4`, `HE6-FAMILY`) and the thirteen description-only pins are exactly as r7 repair 2 left them” |
| Quoted-pair roster | “… `HE6-BETA-GUARD` (r11) — **19 of 36**.” | “… `HE6-BETA-GUARD` (r11); and `HETOW-KEY-BRIDGE-C-A` (r12) — **20 of 37**.” |
| Cured-consumption census | “**Nine** consumptions have been cured this way.” (+ HE6's post-PE4 Correction 2) | “**Ten** consumptions have been cured this way.” (+ HETOW's post-PE2 correction C-A) |
| r4 repair 13's count clause | “two of nine” | “two of ten” |
| Synthetic markers / source edits | zero / zero | zero / zero — “a `grep -lF 'T2V2PIN'` over the six accepted sources returned no hits and the source worktree is clean” |

**DERIVATION:** `[BOOKKEEPING]` Each round adds exactly one pin carrying a quoted delimiter pair, so the pair count rises by one and the other two taxonomy classes are unchanged; the arithmetic chain is restated in full at each step so the gate can re-derive rather than trust it. The census advances by one at each round because each cure is of the census's own class — a consumed source unit no pin covered, cured by adding a pin.

**CONDITIONALITY:** **These are the final values.** The acceptance record confirms 37 with taxonomy \(20+4+13\), zero `T2V2PIN` lines, zero source edits, and a census of ten. Nothing after r12 amends them.

**RESOLUTION TRACE:** r11 repair 1(d) (4090–4138) and r12 repair 1(e) (4261–4309); nine superseded strings landmark-verified at 1 under bounds 4031 and 4202 (§3, part B). Destination: base S0.2 and the S7 pin gate → shard 1, `.03` and `.42`.

**TEETH:** S7 pin gate; the pin-sweep leg of the acceptance gate.

---

### EFF.T2.96  [table]

**CANONICAL STATEMENT:** `[TABLE / ASSEMBLED — the FINAL five Source-pin lines, composed from r10 repair 1(f) as amended by r11 repair 1(e) and r12 repair 1(f). Nothing after r12 amends them. Each line's constituent text is verbatim; the composition is the compiler's.]`

| Record | Effective Source pins |
|---|---|
| **S3.1** (in the r1 repair 2 replacement paragraph) | `HE3-A-STMT`, `HE3-A-PROOF`, `HE3-DEF1`, `HE3-HE3-1L`, `HE3-HE3-6`, `HE3-R8-2` through `HE3-R8-5`, `HE6-FAMILY`, `HE6-PROOF`, `HE6-SLOT-SEAM`, `HE6-PEEL-CONVENTION`, `HE6-LIFT-1L`, `HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-ACCOUNT`, and `HE6-BETA-GUARD`. |
| **S3.2** | `HE6-FAMILY`, `HE6-PROOF`, `HE6-SLOT-SEAM`, `HE6-PEEL-CONVENTION`, `HE6-LIFT-1L`, `HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-ACCOUNT`, `HE6-BETA-GUARD`, and `HE3-A-PROOF`. |
| **S3.3** | `HE7-A-STMT`, `HE7-SLOT-TRANSFER`, `HE7-MIXED-13P`, `HE7-COCYCLE-2P-THROUGH-R1D`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE6R1-1`, `HE6R1-2`, `HE6R1-3`, and — for a chain whose level-one key is itself recentered, by S1.8C — `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY`, `HE6-PROOF`, `HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-ACCOUNT` and `HE6-BETA-GUARD`. |
| **S3.4** | `HETOW-LABELS`, `HETOW-LABELS-1`, `HETOW-KEY-BRIDGE`, `HETOW-KEY-BRIDGE-C-A`, `HETOW-A`, `HETOW-NORMALIZER-4`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE7-MIXED-13P`, `HE6R1-3`, and — for a chain whose level-one key is itself recentered, by S1.8C — `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY`, `HE6-PROOF`, `HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-ACCOUNT` and `HE6-BETA-GUARD`. |
| **S3.5** | `GENTOW-4-1`, `GENTOW-4-A`, `GENTOW-4-2`, `GENTOW-ACCEPTANCE-FOLD`, `HETOW-KEY-BRIDGE-C-A`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE7-MIXED-13P`, `HE6R1-2`, `HE6R1-3`, and — for a chain whose level-one key is itself recentered, by S1.8C — `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY`, `HE6-PROOF`, `HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-ACCOUNT` and `HE6-BETA-GUARD`. |

The two additions homed here carry their own consumption grounds:

> “`HE6-BETA-GUARD` is consumed wherever `HE6-TEST-PACKAGE` is: it is that pin's reading directive at LEMMA HE6-2, and it travels with it under exactly the scoping r7 repair 5 and r10 repair 1(f) installed — at both level-one records, and at a level-two chain whose level-one key is itself recentered, where it is simply unconsumed over the original key \(\Phi'\).”

> “`HETOW-KEY-BRIDGE-C-A` is consumed wherever the composed-key bridge is read, which is at the two tower records and nowhere else: at S3.4 directly, as the reading directive of `HETOW-KEY-BRIDGE`, which stands on that line; and at S3.5 through S1.8B's scope clause … It is not consumed at S3.1, S3.2 or S3.3, which read no composed key.”

**DERIVATION:** `[COMPOSITION OF THREE ROUNDS' SETTINGS]` r10 repair 1(f) sets all five lines; r11 repair 1(e) appends `HE6-BETA-GUARD` by three search-and-replace instructions, one of whose search strings occurs three times (the three level-two lines) “and all three are amended identically”; r12 repair 1(f) inserts `HETOW-KEY-BRIDGE-C-A` into S3.4 and S3.5 only. The multi-occurrence arithmetic is verified rather than assumed: the r11 tail string returns **3** under r11's own bound 4031 (lines 3985, 3987, 3989) and **4** under r12's bound 4202 (adding 4140, r11's own quotation), exactly as r12 records — re-run at compilation (§3, part B).

**CONDITIONALITY:** The five lines are per-record declarations of what each instance's own consumptions require (r5 repair 6's discipline). Pins listed “for a chain whose level-one key is itself recentered” are simply unconsumed over the original key \(\Phi'\). The composition is the compiler's; each constituent phrase is verbatim from its round.

**RESOLUTION TRACE:** r10 repair 1(f) (3967–3989, shard 4) + r11 repair 1(e) (4140) + r12 repair 1(f) (4311–4325). Destination: base S3.1–S3.5 → shard 1, `.33`–`.37`, none of which carries the lines.

**TEETH:** the five-instance perimeter gate; S7 pin gate; the standing consumption sweep.

---
### EFF.T2.97  [acceptance-box]

**CANONICAL STATEMENT:** `[ASSEMBLED — post-pass rider block 3: fold rule, scope, landmark convention, and the counter state it SETS]`

> “**Dated rider (2026-08-13 — the single minor of the Opus/Claude confirmation hostile pass on the r12 effective text, `runs/comp13/T2P10_output.log`, returning 0 CRITICAL + 0 GAP + 1 minor, taken after the gpt-5.6-sol high hostile pass on the same effective text, `runs/comp13/T2SOL5_output.log`, returned 0 CRITICAL + 0 GAP + 0 minors. Folded per the campaign's minors-only precedent — T4's post-pass gloss-direction rider, T5's two post-pass-1 locator riders, T1's five post-pass-1 riders and its two final riders, and this note's own two post-pass rider blocks above, each folded on a 0 CRITICAL + 0 GAP pass and none of them a grade event. NO r-section, no grade event, NO counter reset.)** The rider RE-GROUNDS one disposition sentence and does nothing else.”

> “No display of the statement suite S1.2–S1.8 is amended, no hypothesis is added to or removed from HE7.A's suite, no pin is added or removed, no span, fence, obligation, Source-pin line or consumption check is touched, and no new source consumption is created; no source file is quoted or edited by this rider at all. The expected pin count stays **37** with taxonomy \(20+4+13\), the expected synthetic-marker count stays zero, the expected source edit count stays zero, and the cured-consumption census stays at ten.”

> “**Landmark convention (rider).** Counts are taken over the note AS IT STOOD BEFORE THIS BLOCK — lines 1–4439, i.e. through the last line of the r12 counter — because each landmark is necessarily quoted a second time here.”

> “**Counter state (SET BY THIS BLOCK).** … S7's reset rule is stated of gap-or-worse repairs only … and a minors-only pass is a clean pass whose minors fold as post-pass riders (T4, T5, T1, and this note's own two earlier rider blocks). Folding riders is not a repair round: the clean-pass counter is NOT reset, and with these two passes it **STANDS AT 2 OF 2**. The two passes are on model-diverse arms and both are fresh-context passes over the r12 effective text. The S7 acceptance gate — two consecutive clean hostile passes over one effective text — is therefore MET, and the ACCEPTANCE RECORD below is the operative record.”

**DERIVATION:** `[COUNTER-STATE RECORD]` The gate is S7's own: two consecutive clean hostile passes over one effective text. Both passes ran over the same r12 text, both returned 0 CRITICAL + 0 GAP, and the minors-only fold rule (read off S7's reset clause, which speaks of gap-or-worse repairs only) makes the second still a clean pass. Model diversity is a property of the pair, not a gate requirement, and is recorded as a fact about it.

**CONDITIONALITY:** The rider is wording-grade and self-describedly deletable: “it touches only this note's internal bookkeeping about itself, quotes no source, and could be deleted without altering a single claim of the mathematics.” It postdates both passes and “has not been read by a third fresh context” — the one honest gap in the acceptance evidence, and the record says so.

**RESOLUTION TRACE:** source lines 4443–4453 and 4473–4475. Both pass logs exist and both verdict lines re-verified at compilation (§3, part B).

**TEETH:** the S7 acceptance gate itself; the minors-only fold precedent.

---

### EFF.T2.98  [changes-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — Rider 3.1: the HE7:2478 / M-B disposition re-grounded on consumption]`

The finding:

> “**m-1 (MINOR, on r12's own text) — r12 repair 1(g)'s ground for the HE7:2478 disposition is false as written.** The text: "M-B is a provenance rider on THEOREM HE7.D's §S2 clause and COROLLARY HE7.B(ii), **and this master names neither.**" Why it is false: "The master names both, verbatim, at line 2136 (r3 repair 1(b)) … `grep -n 'HE7\.D\|HE7\.B'` over the master returns exactly two lines: 2136 and 4333 itself. The sentence is wrong in the note's **own vocabulary**: the standing S7 check r4 repair 13 installed is worded 'every source display the master text **quotes, names, or leans on**', so 'names' is a relation the gate tracks”

The acceptance of both legs:

> “On the first, the master does name both units, once, at line 2136, in r3 repair 1(b)'s identification of `HE7-COCYCLE-2P-THROUGH-R1D`'s endpoint — and naming is a relation the standing S7 consumption check tracks by its own wording, so a sweep entry that denies the naming is false in this note's vocabulary. On the second, the disposition it grounds is nonetheless correct, because the gated relation is consumption and not naming”

The cure:

> “M-B is a provenance rider on THEOREM HE7.D's §S2 clause and COROLLARY HE7.B(ii), and this master CONSUMES neither — it does NAME both, exactly once, in r3 repair 1(b)'s unit-identification parenthetical (line 2136), which says what the pinned endpoint `ANNEX-COROLLARY R1-d` re-proves and is drawn from HE7's own R1 heading, leaning on neither the §S2 clause nor the inductive-step clause; so obeying M-B changes nothing this master reads, the cocycle chain it does read for `(COC-DEF)`/`(BETA)` lying wholly inside `HE7-COCYCLE-2P-THROUGH-R1D` [2013, 2253], and the naming falls in the unit-identification / boundary-fixing class of the restated S5 item 3, whose governing sentence is "Consumption, not citation, is the gated relation".”

**DERIVATION:** `[RE-GROUNDING, DISPOSITION UNCHANGED]` The entry's verdict (M-B not consumed) survives because it rests on the asymmetry test, not on the naming census: obeying M-B changes nothing the master reads, since what the master reads from that source is the cocycle chain, wholly inside the pinned span. The false ground is replaced by the true one, and the naming is reclassified into one of the four admissible citation classes r12 repair 3 enumerates. “the entry's verdict — M-B not consumed — is unchanged, and so is everything downstream of it.”

**CONDITIONALITY:** Confined to one clause of one bullet in r12's sweep record. It amends the ground of the row compiled at shard 5 `.91`; that row's disposition stands.

**RESOLUTION TRACE:** source lines 4455–4471, superseding r12 repair 1(g)'s closing clause (landmark at line 4333, bound 4439). The naming census re-verified at compilation under the rider's own bound: exactly two lines, 2136 and 4333 (§3, part B).

**TEETH:** the standing S7 consumption check (“quotes, names, or leans on”); the pin-note directive coherence audit; the four admissible citation classes of S5 item 3.

---

### EFF.T2.99  [acceptance-box]

**CANONICAL STATEMENT:** `[VERBATIM — the arc: thirteen hostile passes, two arms, zero CRITICAL, and the compressed GAP history]`

> “**The arc.** Thirteen hostile passes of record across two arms carried this note from a composition draft to acceptance: eight Opus/Claude-arm passes (`runs/comp13/T2P3`–`T2P10`) and five gpt-5.6-sol-high passes (`runs/comp13/T2SOL`–`T2SOL5`), every gap-or-worse pass answered by a repair round r4–r12 and every minors-only pass by a post-pass rider block. Rounds r1–r3 answer earlier passes of the pre-comp13 arc and lie outside that count; their content, compressed, is the mixed-residual block theorem installed as S1.7A (r1), synthetic markers replaced by immutable existing-text spans in S0.2 (r2), and four defective pins re-derived as verbatim delimiter pairs with the `(MID-PEEL)` suite and the `(LB1)` widening (r3). **Zero CRITICAL findings across all thirteen.** The GAP history of the thirteen, compressed: the clause-5 trigger, the displayed well-founded rank, and the level-one `(MID-PEEL)` suite (r4); the perturbation transport LEMMA HE7-12, consumed at two statement changes and pinned nowhere (r5); the refinement height, asserted rather than bound, and `(MP1′)` (r6 — bound as `(REF-HT)`, and `(MP1′)` adjudicated and DISCHARGED); the rise that `(REF-HT)`'s necessity rested on, which no displayed assertion carried (r7 — split into stipulated (RISE) and derived (HT)); the level-one discharge's assembly order (r8); the print/coherent frame conflation at the HE6 family index, caught by the first model-diverse pass (r9 — (IDX-TWIST)); the level-one test package and `(ACCOUNT)` without pinned suppliers (r10 — three new HE6 spans); LEMMA HE6-2's β-definedness guard (r11 — `HE6-BETA-GUARD`); and HETOW's post-PE2 correction C-A with S1.8B's imported degree conjunct (r12 — `HETOW-KEY-BRIDGE-C-A`, and the conjunct re-derived master-side).”

**DERIVATION:** `[ARC RECORD]` One round per gap-or-worse pass, one rider per minors-only pass, is the arc's own bookkeeping rule; the count of thirteen is the count of passes of record, with r1–r3 excluded because they answer earlier passes. The compressed GAP list is a one-line-per-round index into the repair rounds compiled at shards 2–5, and it matches them: r4→shard 2, r5→shard 2, r6/r7→shard 3, r8→shards 3–4, r9/r10→shard 4, r11/r12→shard 5.

**CONDITIONALITY:** “Zero CRITICAL across all thirteen” is a statement about findings, not a claim of correctness; the standing conditionalities at `.101` are what remain open after it.

**RESOLUTION TRACE:** source line 4481. Log directory checked at compilation: the `runs/comp13/` T2 logs named here are present (§3, part B).

**TEETH:** the S7 two-clean-pass gate; each round's own pass of record.

---

### EFF.T2.100  [acceptance-box]

**CANONICAL STATEMENT:** `[VERBATIM — the two passes of record, and the rider that postdates them]`

> “- **Pass 1 of 2** — `runs/comp13/T2SOL5_output.log` (gpt-5.6-sol high, r12 effective text, 2026-08-13): **0 CRITICAL + 0 GAP + 0 minor**, the arc's first zero-findings verdict. It re-derived the r12 degree mathematics at all five instance boxes, verified `HETOW-KEY-BRIDGE-C-A`'s span byte-minimal under S0.2, re-resolved the pin inventory to \(20+4+13=37\), re-ran the six-source dated-append sweep, and attacked the `d = c_{\mathcal C}v` datum and the lift-difference step.
> - **Pass 2 of 2** — `runs/comp13/T2P10_output.log` (Opus/Claude confirmation, r12 effective text, 2026-08-13): **0 CRITICAL + 0 GAP + 1 minor**, the minor being bookkeeping on r12's own sweep record (the ground for the HE7:2478 disposition; the disposition itself is upheld on the consumption ground). It ran r12's assembly audit against the r1–r11 body and the seventeen-landmark set, the theorem statement as effectively amended with the `d = c_{\mathcal C}v` datum folded, the full S7 consumption sweep at 37 pins, an exhaustive 28-unit dated-append re-enumeration of all six sources, a pin-note directive coherence audit over the seven reading directives, and a master-side closure of the `(OCC)` demand at the refinement height at both levels. Its four non-counted nits are recorded in that log and are deliberately not cured here, so that later work need not re-raise them.”

> “**The clean-pass counter reaches 2 OF 2**, on model-diverse arms, over one effective text.”

> “**One rider postdates both passes.** Post-pass rider 3 above, folding pass 2's single minor, is wording-grade and one sentence long … Like T1's final riders it has not been read by a third fresh context; unlike them it touches only this note's internal bookkeeping about itself, quotes no source, and could be deleted without altering a single claim of the mathematics.”

**DERIVATION:** `[PASS RECORD]` Each pass is recorded with its arm, its text, its verdict and what it actually ran, so that the gate's satisfaction can be audited rather than taken. The two attack surfaces are complementary: pass 1 re-derived the round's new mathematics and re-resolved the inventory; pass 2 audited the assembly of the whole and re-ran the consumption sweep at 37 pins over all six sources.

**CONDITIONALITY:** Pass 2's four non-counted nits are live and deliberately uncured, recorded in its log. The rider that folds pass 2's minor is itself unreviewed by a third context — stated, not hidden.

**RESOLUTION TRACE:** source lines 4483–4490. Both verdict lines re-verified at compilation directly from the logs: `T2SOL5_output.log` → `VERDICT: CLEAN | FINDINGS: 0C + 0G + 0m`; `T2P10_output.log` → `VERDICT: CLEAN | FINDINGS: 0C + 0G + 1m` (§3, part B).

**TEETH:** the S7 acceptance gate; the 37-pin sweep; the 28-unit dated-append re-enumeration; the seven-directive coherence audit.

---

### EFF.T2.101  [table]

**CANONICAL STATEMENT:** `[TABLE — the four standing conditionalities, verbatim, plus the sentence excluding a fifth]`

> “**Standing conditionalities, displayed rather than discharged.** Acceptance is acceptance of the composition WITH this ledger, not clearance of it.”

| Item | Status, verbatim |
|---|---|
| `(LB1)` | “**OPEN at level one.** Every level-one state whose clause-4 processing constructs a block (any state with at least two sides, and any side whose residual is mixed) is `(LB1)`-conditional. Fenced at S1.7B, at the S3.1/S3.2 level-one fences, and at S5 item 16. Clauses 1–2 carry no `(LB1)` conditionality at any level-one state.” |
| `(MP1)` | “**OPEN at level one.** A level-one clause-5 mid-chain peel at a **recentered** key is `(MP1)`-conditional: item 5 of the `(MID-PEEL)` input suite needs \(\Phi''\) irreducible, which `HE6-PEEL-CONVENTION` supplies only for the ORIGINAL key \(\Phi'\). Fenced at S1.8A, in S4.2's exclusion list, and at S5 item 17. The original-key level-one peel is discharged by `HE6-PEEL-CONVENTION`; the level-two peel at a DEFINITION HE6-1 key by `HE6R1-3`, and at a recentered level-two key by `HE7-PERT-TRANSPORT`(c) carrying `HE6R1-3` (S1.8B).” |
| `(SEC-RANK)` | “a **CARRIER HYPOTHESIS**, not an obligation; it fences no read. Discharged per instance: level one inside `HE3-A-PROOF` (the stage-α termination clause); level two at a DEFINITION HE6-1 key by `HE7-REF-TERM` (LEMMA HE7-8); at the composed key by `HETOW-A`(ii) and `GENTOW-4-A`(iii), which state finiteness of the α-refine chain **at \(\Phi_2\)**, so the master performs no key transfer of its own.” |
| `(RISE)` | “**STIPULATED**, on `(SEC-RANK)`'s footing, as the first clause of `(REF-HT)`; (HT), \(k=\lambda\), is DERIVED from it by the min-rule display. Discharged per instance: level one at the instance's own refine step inside `HE3-A-PROOF`, with `HE6-FAMILY` and `HE6-PROOF` supplying the HE6 leg and its \(\ell\ge2\) caveat routed to the product-\(\ge2\) branch; level two and deeper inside `HE7-PERT-TRANSPORT` (LEMMA HE7-13's rise is that lemma's derived conclusion), with `HE7-REF-TERM` recording the same chain convention.” |

> “`(MP1′)` is NOT a fifth standing conditionality: it was RETIRED at r6 repair 2 and discharged in S1.8C from `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY` and `HE6-PROOF`. It denotes a consequence of the pins, not an obligation.”

**DERIVATION:** `[LEDGER]` The ledger separates two statuses that the arc kept distinct throughout: an **open obligation** fences reads and appears in S5/S4.2 (`(LB1)`, `(MP1)`), while a **carrier hypothesis** fences nothing and is discharged per instance (`(SEC-RANK)`, `(RISE)`). Each row names where it is fenced or where it is discharged, by pin. The fifth-item sentence closes the one name a reader of r5 would otherwise carry forward.

**CONDITIONALITY:** This is the whole of what acceptance leaves open on the mathematics. Any consumer of T2 inherits exactly these four rows; the two open obligations are the only ones that fence.

**RESOLUTION TRACE:** source lines 4492–4499. Cross-shard: `(LB1)` is homed at base S1.7B (shard 1 `.18`); `(MP1)` at S1.8A (shard 1 `.23`); `(SEC-RANK)`'s discharge map at shard 2 `.52`; `(RISE)`'s at shards 3 `.60` and 4 `.69`/`.71`; the `(MP1′)` retirement at shard 3 `.61`.

**TEETH:** every level-one fence attack; the refinement-termination tooth; the composed-key transport tooth; the fence-leakage check the r9 pass ran (“`(LB1)` and `(MP1)` remain fenced; I found no fence leakage”).

---

### EFF.T2.102  [acceptance-box]

**CANONICAL STATEMENT:** `[VERBATIM — machine evidence, and why no battery is owed]`

> “**Machine evidence, and why no battery is owed.** No battery obligation exists for T2: S4.1 states in terms that this note "does not rerun supplier batteries", and S7's gate is the **pin sweep**, not a machine leg. That sweep was run whole at **37** pins by pass 2 — all 40 delimiter lines of the 20 quoted pairs resolved by exact-full-line search, each occurring exactly once and each first preceding its last, 4 first-only pins resolved at their quoted first delimiter, 13 description-only pins resolving to a unique unit head, and all spans within a file pairwise disjoint — and re-resolved to the same \(20+4+13=37\) inventory by pass 1, which additionally certified the new span `HETOW-KEY-BRIDGE-C-A` [548, 569] minimal under S0.2. **Zero `T2V2PIN` lines in the six accepted sources**, reported by both passes. **Zero source edits**: `git status --porcelain lean/notes/openmath/` was empty at pass 2, and pass 1 records that it constructed the effective text first and made no edits. The cured-consumption census stands at **ten**.”

**DERIVATION:** `[GATE RESULT]` The absence of a battery is derived from the note's own scope declaration (S4.1) and from S7's gate definition, not asserted. The sweep is reported in the gate's own four terms — pair resolution, taxonomy, synthetic-marker count, source-edit count — and by two independent passes, one of which additionally certified the last pin's span minimal.

**CONDITIONALITY:** This is source-side evidence only. It certifies that every consumed source unit lies inside a resolvable span and that no source was edited; it certifies nothing about downstream consumers, whose checks remain queued (`.105`).

**RESOLUTION TRACE:** source line 4501. **Independently re-run at compilation (§3, part B):** zero `T2V2PIN` hits across the six sources; `git status --porcelain` empty for all six; both pass logs present with the stated verdicts.

**TEETH:** the S7 pin gate (the acceptance leg); the standing consumption sweep; the synthetic-marker and source-edit counts.

---

### EFF.T2.103  [table]

**CANONICAL STATEMENT:** `[VERBATIM — grade, stated honestly, and the HE3 cap it leaves in force]`

> “**Grade, stated honestly.** The master's own attempt grade moves \(0/2\to 2/2\), and the front-matter status line is refreshed in place to say so. `(GRADE)` is unchanged and still binds: \(\operatorname{grade}(I)=\min(g_{\mathrm{master}},g_{\mathrm{carrier}},g_{\mathrm{frame}},g_{\mathrm{local}})\). At the supplied source HEAD, HE6, HE7, HE6R1, HETOW and GENTOW4 are \(2/2\), while **HE3 is consumed at the grade stated by its supplied HEAD, which is attempt grade \(0/2\) (consecutive-clean count \(1/2\))** — so the two level-one records S3.1 and S3.2, and any level-two chain that consumes an HE3 pin through S1.8C, remain capped at HE3's grade. **Acceptance of this note does NOT make those composed instances \(2/2\).** It is acceptance of the composition, not an upgrade of the level-one supplier; \(g_{\mathrm{master}}=2/2\) removes the master's own factor from the minimum and nothing else.”

| Consumer | Effective grade after acceptance |
|---|---|
| The master `HE7.A` / `T2.KEY-BOUNDARY` as composition | \(2/2\) |
| S3.1 (HE3.A) and S3.2 (HE6) composed instances | capped at HE3's HEAD grade, \(0/2\) (clean count \(1/2\)) |
| A level-two chain consuming an HE3 pin through S1.8C | capped the same way |
| S3.3, S3.4, S3.5 not consuming an HE3 pin | \(\min\) over their own carrier/frame/local grades, master factor removed |

**DERIVATION:** `[GRADE MINIMUM]` `(GRADE)` is a minimum over four factors, so raising the master's factor removes it from the minimum and changes nothing where another factor is lower. HE3's HEAD grade is the lowest supplier factor, and S1.8C is the route by which a level-two chain can come to consume an HE3 pin — which is why the cap follows a chain's *history* and not its level.

**CONDITIONALITY:** The cap is a property of the supplied source HEAD; it lifts only if HE3's own arc closes, and nothing in this note can lift it.

**RESOLUTION TRACE:** source line 4503; the `(GRADE)` display is base S4.1 (shard 1, `.38`) and the supplier grades base S4.1's list; S1.8C's transport is shard 3 `.61`. The compiler table above is derived from the quoted paragraph and is marked as a compiler ledger by its position under the verbatim quotation.

**TEETH:** the grade-laundering hazard row of S6; the `(GRADE)` minimum; the acceptance gate.

---

### EFF.T2.104  [fence]

**CANONICAL STATEMENT:** `[VERBATIM — byte-freeze and the append-only regime]`

> “**Byte-freeze.** With this record the note is **BYTE-FROZEN**. The accepted T2 v2 of record is the effective text as of r12, plus the first post-pass rider block, plus the second post-pass rider block, plus post-pass rider 3 above, and consumers cite it as exactly that. From here the note takes dated appends only, each superseding its quoted sentence of record and each carrying its own landmark census, in the register r5–r12 used; the pin table, the two open obligations, the two stipulated carrier hypotheses and the `(GRADE)` machinery move only that way. Any change that would rewrite the accepted text reopens the hostile arc rather than editing the note. One in-place edit accompanies this fold and it is the only one: the front-matter status line, refreshed DATELESS so that it stays self-maintaining — every round-dependent fact lives in the governing block, and acceptance only moves which block that is.”

**DERIVATION:** `[FREEZE PROTOCOL]` The freeze defines the citable object (r12 + three rider blocks) and the only admissible future edit shape (a dated append with a quoted sentence of record and its own landmark census — the register the arc itself used from r5 on). The single in-place exception is made self-maintaining by removing the date from it, so that the freeze cannot be violated merely by the passage of time.

**CONDITIONALITY:** Every later change must be an append or a re-opened arc. In particular the pin table, the two open obligations, the two stipulated carrier hypotheses and `(GRADE)` may move only by dated append.

**RESOLUTION TRACE:** source line 4505. The front-matter status line quoted in every shard header is the one in-place edit this sentence licenses; the note is clean in the worktree at compilation (§3, part B).

**TEETH:** the byte-freeze itself is the tooth: any rewrite reopens the arc.

---

### EFF.T2.105  [changes-record]

**CANONICAL STATEMENT:** `[VERBATIM — the queued consumption protocol]`

> “**Next.** Consumption checks ride the next queue: re-price every downstream note that consumes T2 v2 under `(GRADE)` with \(g_{\mathrm{master}}=2/2\) — subject to the HE3 cap above — and re-run the standing S7 consumption check at the consuming sites.”

**DERIVATION:** `[PROTOCOL QUEUE]` Two distinct obligations are queued, matching the two predicates this compilation keeps apart: a **grade re-pricing** at every downstream consumer (with the HE3 cap still binding), and a **re-run of the standing S7 consumption check at the consuming sites** — the same check installed by r4 repair 13, now pointed outward instead of at T2's own sources.

**CONDITIONALITY:** **Nothing here is done.** No downstream note has been re-priced and no consuming-site check has been run. Any claim that a T2 consumer is at \(2/2\), or that its consumption of T2 has been checked, is unsupported by this note.

**RESOLUTION TRACE:** source line 4507. This is the note's final sentence; no unit of any shard reports either obligation as discharged.

**TEETH:** the standing S7 consumption check, pointed at consuming sites; `(GRADE)` at every consumer.

---
## 4. XREF verification ledger

T2's six shards carry two different kinds of grep-verified check, and this merge keeps
them as two different kinds of ledger rather than flattening them into one list:

- **The pin-designation ledger** (part A) is the note's actual mathematical supply
  chain — which named unit, in which of the six source proof notes, each pinned span of
  `(PINS)` resolves to. This is the ledger analogous to EFF-T1's XREF table, and it is
  reproduced here in full: **37 unique designations**, exactly the accepted final pin
  inventory's taxonomy \(20+4+13\).
- **The process/derivation verification ledgers** (part B) are shards 2–6's own
  audit trail: source-line and master-internal-landmark re-runs that verify the historical
  *narrative* of how each repair round arrived at those 37 pins (delimiter byte-checks,
  landmark supersession counts, per-round pass-log verdicts). These are not additional
  supply designations — every pin they touch is already one of the 37 in part A — so
  they are summarized by shard rather than fully re-transcribed; the shard files remain
  the run-of-record trace for anyone who needs a specific one.

### A. Pin-designation ledger (37 designations; source: `EFF.T2.03`'s XREF table,
carried through unchanged since shard 1 was compiled from the fully-resolved effective
text and already reflects every pin r1–r12 add)

**Method.** Each designation was checked with exact fixed-string search (`grep -cF`) in
the named source file at shard-1 compilation time. A count other than exactly 1 would
have been an `OPEN-CALL`; none occurred.

| # | Effective pin | Source file | Exact designation searched | Count |
|---:|---|---|---|---:|
| 1 | `HE3-A-STMT` | `HE3_PROOF_2026-08-08.md` | `THEOREM HE3.A (THE STAGE-σ RECURSION` | 1 |
| 2 | `HE3-A-PROOF` | `HE3_PROOF_2026-08-08.md` | `### S6.3 PROOF OF THEOREM HE3.A` | 1 |
| 3 | `HE3-DEF1` | `HE3_PROOF_2026-08-08.md` | `DEFINITION 1 (the stage resolvent and its label set)` | 1 |
| 4 | `HE3-HE3-1L` | `HE3_PROOF_2026-08-08.md` | `LEMMA HE3-1L [r1` | 1 |
| 5 | `HE3-HE3-6` | `HE3_PROOF_2026-08-08.md` | `LEMMA HE3-6 [r1]` | 1 |
| 6 | `HE3-R8-2` | `HE3_PROOF_2026-08-08.md` | `Dated correction (2026-08-12, post-R8) — R8-2:` | 1 |
| 7 | `HE3-R8-3` | `HE3_PROOF_2026-08-08.md` | `Dated correction (2026-08-12, post-R8) — R8-3:` | 1 |
| 8 | `HE3-R8-4` | `HE3_PROOF_2026-08-08.md` | `Dated correction (2026-08-12, post-R8) — R8-4:` | 1 |
| 9 | `HE3-R8-5` | `HE3_PROOF_2026-08-08.md` | `Dated correction (2026-08-12, post-R8) — R8-5:` | 1 |
| 10 | `HE6-FAMILY` | `HE6_PROOF_2026-08-08.md` | `DEFINITION HE6-1 (THE ENLARGED TEST FAMILY)` | 1 |
| 11 | `HE6-PROOF` | `HE6_PROOF_2026-08-08.md` | `### S6.2 PROOF OF THEOREM HE6.A` | 1 |
| 12 | `HE6-SLOT-SEAM` | `HE6_PROOF_2026-08-08.md` | `LEMMA HE6-0″ [r1, R5/F6]` | 1 |
| 13 | `HE6-PEEL-CONVENTION` | `HE6_PROOF_2026-08-08.md` | `CONVENTION [r1] (the two standing hypotheses on f` | 1 |
| 14 | `HE6-LIFT-1L` | `HE6_PROOF_2026-08-08.md` | `LEMMA HE6-1L [r1; display corrected` | 1 |
| 15 | `HE6-TEST-PACKAGE` | `HE6_PROOF_2026-08-08.md` | `LEMMA HE6-0′ (the local forcing` | 1 |
| 16 | `HE6-ROOT-LABEL` | `HE6_PROOF_2026-08-08.md` | `Corollary HE6-2″ (HE3-0(iii), re-proved in this convention)` | 1 |
| 17 | `HE6-ACCOUNT` | `HE6_PROOF_2026-08-08.md` | `## S5. LEMMA HE6-3 (slope counts, (SEP)-free) AND LEMMA HE6-4 (nonemptiness)` | 1 |
| 18 | `HE6-BETA-GUARD` | `HE6_PROOF_2026-08-08.md` | `Correction 2 (PE4 F-2 — LEMMA HE6-2's β-definedness guard)` | 1 |
| 19 | `HE7-A-STMT` | `HE7_PROOF_2026-08-08.md` | `THEOREM HE7.A (THE LEVEL-2 READ DECIDES` | 1 |
| 20 | `HE7-SLOT-TRANSFER` | `HE7_PROOF_2026-08-08.md` | `(SLOT₂) [PROVED, §S3]` | 1 |
| 21 | `HE7-MIXED-13P` | `HE7_PROOF_2026-08-08.md` | `ANNEX-LEMMA HE7-13′ (mixed residual nodes` | 1 |
| 22 | `HE7-COCYCLE-2P-THROUGH-R1D` | `HE7_PROOF_2026-08-08.md` | `ANNEX-DEF HE7-2′ (the corrected level recursion` | 1 |
| 23 | `HE7-REF-TERM` | `HE7_PROOF_2026-08-08.md` | `LEMMA HE7-8 ((REF-TERM)` | 1 |
| 24 | `HE7-PERT-TRANSPORT` | `HE7_PROOF_2026-08-08.md` | `LEMMA HE7-12 [r2] (SLOT-DOMINATION` | 1 |
| 25 | `HE6R1-1` | `HE6R1_RECON_2026-08-08.md` | `LEMMA HE6R1-1 (the widened jump condition descends` | 1 |
| 26 | `HE6R1-2` | `HE6R1_RECON_2026-08-08.md` | `LEMMA HE6R1-2 [r1′] (block projection)` | 1 |
| 27 | `HE6R1-3` | `HE6R1_RECON_2026-08-08.md` | `LEMMA HE6R1-3 (the level-2 peel)` | 1 |
| 28 | `HETOW-LABELS` | `HETOW_RECON_2026-08-09.md` | `## S1. THE INSTANTIATION MAP` | 1 |
| 29 | `HETOW-LABELS-1` | `HETOW_RECON_2026-08-09.md` | `LEMMA HETOW-1 (label translation)` | 1 |
| 30 | `HETOW-KEY-BRIDGE` | `HETOW_RECON_2026-08-09.md` | `LEMMA HETOW-2 (the composed key is a key-family member` | 1 |
| 31 | `HETOW-KEY-BRIDGE-C-A` | `HETOW_RECON_2026-08-09.md` | `C-A (cures PE2 F-A` | 1 |
| 32 | `HETOW-A` | `HETOW_RECON_2026-08-09.md` | `THEOREM HETOW.A ([GENHN-HE(μ₂)]` | 1 |
| 33 | `HETOW-NORMALIZER-4` | `HETOW_RECON_2026-08-09.md` | `LEMMA HETOW-4 (the normalizer bridge)` | 1 |
| 34 | `GENTOW-4-1` | `GENTOW4_PROOF_2026-08-09.md` | `LEMMA GENTOW-4.1.` | 1 |
| 35 | `GENTOW-4-A` | `GENTOW4_PROOF_2026-08-09.md` | `THEOREM GENTOW-4.A (partial inner sides` | 1 |
| 36 | `GENTOW-4-2` | `GENTOW4_PROOF_2026-08-09.md` | `LEMMA GENTOW-4.2 (tie, PURE-POWER sides)` | 1 |
| 37 | `GENTOW-ACCEPTANCE-FOLD` | `GENTOW4_PROOF_2026-08-09.md` | `### Dated acceptance record (2026-08-10, post-PE3)` | 1 |

**Result: 37 designations verified uniquely; 0 unverifiable; 0 compiler `OPEN-CALL`s.**
This is the final inventory: the taxonomy is 20 quoted delimiter pairs (rows verified
with byte-exact first/last lines inside shards 2–5's process ledgers — `HE6-SLOT-SEAM`,
`HE3-DEF1`, `HETOW-KEY-BRIDGE`, `HE7-PERT-TRANSPORT`, `HE6-LIFT-1L`, `HE6-PROOF`,
`HE6-TEST-PACKAGE`, `HE6-ROOT-LABEL`, `HE6-ACCOUNT`, `HE6-BETA-GUARD`,
`HETOW-KEY-BRIDGE-C-A`, and nine more), 4 first-only pins (`HE3-R8-2/-3/-4`,
`HE6-FAMILY`), and 13 description-only pins resolving to a unique unit head.

### B. Process/derivation verification ledgers (summarized per shard; full detail in the
shard files' own §3/§4)

| Shard (new range) | Source lines re-verified | Master-internal landmarks re-verified | Designations/claims classified | Negative/zero-count claims confirmed |
|---|---:|---:|---:|---|
| `EFF.T2.45`–`.57` (old s2) | 37 (all at count 1) | 9 | 11 designation-occurrence checks | `redline` in `HE3_PROOF` → 0 |
| `EFF.T2.58`–`.66` (old s3) | 44 (all at count 1) | 20 | — | — |
| `EFF.T2.67`–`.81` (old s4) | 33 (all at count 1, line numbers confirmed) | 18 | 1 cross-note reference (T1, named-not-consumed) | — |
| `EFF.T2.82`–`.96` (old s5) | 30 (all at count 1, line numbers confirmed) | 18 (incl. 2 multi-occurrence censuses: 3 at bound 4031, 4 at bound 4202) | — | — |
| `EFF.T2.97`–`.105` (old s6) | 0 (this block quotes no source line) | — | 4 designation-level checks | `T2V2PIN` sweep over six sources → 0 hits; `git status --porcelain` → empty; both pass-log verdict lines reproduced exactly |

Every count above was independently re-run at each shard's own compilation time
(2026-08-14); zero drift from the note's own recorded values was found by any shard.

### C. Merge-level sample re-verification (12 of the pin-designation ledger's grep counts
+ 6 of the 105 statement quotes, re-run fresh at merge time against the working tree)

| Designation / claim | Recorded count | Re-verified count | Match |
|---|---:|---:|---|
| `HE3_PROOF_2026-08-08.md:THEOREM HE3.A (THE STAGE-σ RECURSION` | 1 | 1 | ✓ |
| `HE7_PROOF_2026-08-08.md:ANNEX-DEF HE7-2′ (the corrected level recursion` | 1 | 1 | ✓ |
| `HETOW_RECON_2026-08-09.md:C-A (cures PE2 F-A` | 1 | 1 | ✓ |
| `HE6_PROOF_2026-08-08.md:LEMMA HE6-0″ [r1, R5/F6] (THE SLOT LEMMA...` first delim | 1 | 1 | ✓ |
| `HE6_PROOF_2026-08-08.md:DEFINITION HE6-1 (THE ENLARGED TEST FAMILY). Let κ...` | 1 | 1 | ✓ |
| `HE7_PROOF_2026-08-08.md:LEMMA HE7-13 [r2] (the strict slope increase...` first delim | 1 | 1 | ✓ |
| `HE6_PROOF_2026-08-08.md:(RES) Σ_ρ dv(g(ρ)) = e₁·v(±Res(f,g)) = Σ_ξ dv(f(ξ)),` | 1 | 1 | ✓ |
| `HE6_PROOF_2026-08-08.md:Correction 2 (PE4 F-2 — LEMMA HE6-2's β-definedness guard).` | 1 | 1 | ✓ |
| `HETOW_RECON_2026-08-09.md:C-A (cures PE2 F-A — LEMMA HETOW-2's F-2 paragraph, §S2).` | 1 | 1 | ✓ |
| `HE7_PROOF_2026-08-08.md:with key Ψ (DEFINITION HE7-1), and let w ∈ O[x], w ≠ 0,...` | 1 | 1 | ✓ |
| `T2V2PIN` sweep over the six accepted sources | 0 hits | 0 hits | ✓ |
| `LEMMA HE7-12` occurrence count in `HE7_PROOF_2026-08-08.md` | 23 | 23 | ✓ |

| Statement | Quoted fragment | Found at source line | Match |
|---|---|---:|---|
| `EFF.T2.31` (THEOREM HE7.A) | "THEOREM HE7.A (σ-LADDER MASTER)." | 648 | ✓ |
| `EFF.T2.59` ((RISE) forces (HT)) | "(RISE) forces (HT)" | 3349 | ✓ |
| `EFF.T2.75` (rider fold, post-pass rider 1) | "returning 0 CRITICAL + 0 GAP + 1 minor. Folded per the" | 3811 | ✓ |
| `EFF.T2.89` (HETOW-KEY-BRIDGE-C-A pin derivation) | "The correction is pinned regardless, because pinning is owed for the directive itself and not only for the mathematics it would have blocked." | 4222 | ✓ |
| `EFF.T2.101` (standing conditionalities) | "`(LB1)` — OPEN at level one." / "`(MP1)` — OPEN at level one." | 4494 / 4495 | ✓ |
| `EFF.T2.56` (per-record pin discipline, withdrawal) | "The `[r3]`-clause route is withdrawn, not defended." | 2682 | ✓ |

**All 12 sampled XREF counts and all 6 sampled statement quotes match exactly; zero
drift introduced by sharding, renumbering, or merge.**

---
## 5. Status and supply/consumption ledger

Per the merge charge, the governing block — shard 6's acceptance-record material,
`EFF.T2.97`–`.105` — heads this section, since it is the note's own stated authority
over every status question below it. The per-instance mathematical supply table (from
shard 1's base inventory) follows as §5.2.

### 5.1 Governing acceptance ledger (shard 6 only; `EFF.T2.97`–`.105`)

`[TABLE — compiler ledger, not source wording; this is the ONLY shard whose units are
all effective and none historical — every other shard resolves into it]`

| Item | Effective status | Surviving condition/fence | Consumption-protocol status |
|---|---|---|---|
| Post-pass rider 3 fold + counter (`EFF.T2.97`) | Effective; sets the clean-pass counter to **2/2** | Rider is wording-grade and unread by a third fresh context — the one honest gap in the acceptance evidence, stated by the record itself | n/a |
| Rider 3.1 re-grounding (`EFF.T2.98`) | Effective | The HE7:2478/M-B disposition (recorded at `EFF.T2.91`) is unchanged; only its *ground* moves from naming to consumption | Amends `EFF.T2.91`'s ground in place |
| The arc (`EFF.T2.99`) | Effective | Zero CRITICAL across thirteen passes is a findings statement, not a correctness claim | n/a |
| The two passes of record (`EFF.T2.100`) | Effective | Pass 2's four non-counted nits are live and deliberately uncured | Pass 2 ran the 37-pin sweep (source-side only) |
| Four standing conditionalities (`EFF.T2.101`) | **Effective and final** | `(LB1)`/`(MP1)` fence reads; `(SEC-RANK)`/`(RISE)` are carrier hypotheses that fence nothing; `(MP1′)` explicitly not a fifth | Inherited by every downstream consumer |
| Machine evidence (`EFF.T2.102`) | Effective; independently re-verified at this merge (§4.C) | Source-side only — pin sweep, zero synthetic markers, zero source edits | Downstream unchecked |
| Grade (`EFF.T2.103`) | Effective | HE3's HEAD grade (\(0/2\), clean count \(1/2\)) caps S3.1/S3.2 and any HE3-consuming chain; **not** transitive from \(g_{\mathrm{master}}=2/2\) | Re-pricing queued |
| Byte-freeze (`EFF.T2.104`) | Effective | Dated appends only from here forward; any rewrite reopens the hostile arc | n/a |
| Next queue (`EFF.T2.105`) | Effective; **nothing discharged** | Both queued obligations (grade re-pricing; standing S7 consumption check at consuming sites) outstanding | This unit IS the consumption-protocol status |

**Reverse-XREF audit (governing).** The acceptance record names **no** downstream
consumer note or designation — it addresses "every downstream note that consumes T2 v2"
generically. There is therefore no source-backed consumer designation to grep-verify and
no reverse-XREF row to invent, at this or any other shard's own supply ledger (every
shard's §4 reverse-XREF audit reaches the identical finding independently).

### 5.2 Per-item mathematical supply (shard 1's base inventory, `EFF.T2.01`–`.44`; the
mathematical content §5.1's grade and conditionality rows govern)

`[TABLE — compiler ledger, not source wording]`

| Item | Mathematical supply status | Surviving condition/fence | Consumption-protocol status |
|---|---|---|---|
| `HE7.A` (`EFF.T2.31`) | Accepted master theorem, grade 2/2 | Full carrier suite; `(LB1)` on the level-one clause-4 route; `(MP1)` on the recentered level-one clause-5 route | Downstream repricing and standing S7 checks remain queued |
| `T2.KEY-BOUNDARY` (`EFF.T2.32`) | Accepted boundary theorem | Every residual block carries the full HE7.A suite | Same downstream queue |
| HE3.A instance (`EFF.T2.33`) | Supplied by the composite HE3+HE6 perimeter | `(LB1)`/`(MP1)` where triggered; HE3 attempt-grade cap 0/2 (clean count 1/2) | Not upgraded by master acceptance |
| HE6 instance (`EFF.T2.34`) | Supplied | Same level-one fences and HE3-dependent cap | Not upgraded by master acceptance |
| HE7+HE6R1 instance (`EFF.T2.35`) | Supplied | Carrier `(SEC-RANK)` and `(RISE)` discharged by pins; inherited level-one fences if its history consumes them | Consumer must re-run its own check |
| HETOW instance (`EFF.T2.36`) | Supplied | C-A governs the source licence; degree bound derived master-side (`EFF.T2.90`); inherited source caps remain | Consumer must re-run its own check |
| GENTOW4 instance (`EFF.T2.37`) | Supplied per selected bouquet block | No count-side mixed-multiplicity tie, partial-side budget, or density-law import | Consumer must re-run its own check |
| Formal encoding | Not supplied by this note | Must preserve the original-\(O\), no-current-key-irreducibility interface | S-5 probe/stage 2 remains future protocol |

The two source-level open obligations, `(LB1)` and `(MP1)`, are part of the accepted
theorem's conditionality ledger. They are not `OPEN-CALL`s caused by unresolved compiler
XREFs.

---

## 6. TEETH inverse table (unified across all six shards)

T2 has no numbered "battery" table — shard 6 records why (`EFF.T2.102`: "S4.1 states in
terms that this note 'does not rerun supplier batteries', and S7's gate is the pin
sweep, not a machine leg"). Its inverse is therefore the union of every shard's own S7
hostile-tooth/pin-gate/consumption-sweep rows — each shard names its teeth by category,
not by a numbered checklist — with same-category rows from different shards merged and
every guarded-unit list re-expressed in the merged IDs. `[TABLE — compiler inverse]`

| Tooth / hostile demand | Disposition in effective text | Guarded unit(s) (union, merged IDs) |
|---|---|---|
| Original-\(O\), no-current-key-irreducibility, formal-interface gate | Closed mathematically; formal encoding remains future protocol | `EFF.T2.01, .02, .04, .43, .44` |
| 37-pin exact-resolution and consumption gate (incl. S7 pin-gate conditions 1–4 wherever re-run) | Closed at \(20+4+13\); zero synthetic pins/source edits; conditions 1–4 individually re-checked at every new pin | `EFF.T2.03, .15, .24, .25, .33–.37, .40, .42, .47–.51, .54, .56, .63, .76, .77, .80, .84, .89, .95, .96, .102` |
| Pure theorem/accounting/local-forcing gate (S7 Pass 1 pure-mathematics theorem gate) | Closed subject to displayed carrier inputs | `EFF.T2.04, .05, .12, .15, .16, .29–.31, .59, .94` |
| HE6 seam, sign, print/coherent index, β-guard gate | Closed with compatible-choice qualifier; β-guard well-posedness separately closed | `EFF.T2.05, .06, .10, .15, .20, .33, .34, .50, .70, .71, .72, .74, .84, .85` |
| Live cocycle and deeper-letter carry | Closed; cocycle not trivialized | `EFF.T2.07, .08, .35` |
| Full-height and sub-threshold-lift refusal | Closed by `(OCC)` and instance bounds | `EFF.T2.09, .10, .19` |
| Reducible/recentered-key boundary (incl. the `(MP1)` fence and its per-round rows) | Closed by `(KEY-FREE)`/boundary theorem except the explicit `(MP1)` route; `(MP1)` untouched by any frame discharge | `EFF.T2.02, .11, .23, .28, .32, .39, .53, .61, .92` |
| Frame, nonzero origin, normalizer bridge (incl. composed-key transport / HETOW-GENTOW4 frame gates) | Closed at invariant-factor level | `EFF.T2.13, .14, .20, .25, .36, .62, .90` |
| Mixed residual, repeated companion classes, block-owned exponent | Closed generically; level-one construction remains `(LB1)`-conditional | `EFF.T2.17, .18, .21, .22` |
| Mid-chain peel and composed-key transport | Level two discharged; recentered level one remains `(MP1)`-conditional | `EFF.T2.23, .24, .62` |
| Termination with root preservation (refinement-termination; non-circularity of an instance discharge) | Closed with carrier `(SEC-RANK)`; RANK components honestly separated; assembly order fixed so no circularity | `EFF.T2.21, .26, .27, .52, .59, .60, .65, .66, .68, .71` |
| Complete hull, `(RES-DEG)`, side count, orbit forcing | Closed | `EFF.T2.11, .12, .16, .29–.31` |
| Five-instance perimeter | Closed with stated fences and supplier caps; each record's pin line instantiates its own suite | `EFF.T2.33–.37, .56, .96` |
| Grade-laundering refusal | Closed for accepted master; minima and source caps survive | `EFF.T2.38, .41, .42, .44, .103` |
| Honesty/exclusion/re-composition ledger | Closed for composition, not erased | `EFF.T2.39–.41` |
| Two-pass acceptance and later formal gate | Mathematical acceptance met; consumption/formal protocols remain separate | `EFF.T2.42–.44` |
| Print/coherent frame mutant and its two qualifiers (lift-choice; covering-height) | Seam displayed; family reindexed; discharge rebuilt so the print label is never read; both qualifiers checked | `EFF.T2.69, .70, .71, .72` |
| S1.8C level-one frame transport / `(MP1′)` retirement | Adjudicated and discharged from four already-listed pins; obligation retired | `EFF.T2.61` |
| HE7-8 foreign-key / composed-key `(SEC-RANK)` re-route | Re-routed to `HETOW-A`(ii)/`GENTOW-4-A`(iii); no key transfer performed by the master | `EFF.T2.52, .62` |
| `(ACCOUNT)` supplier gate / HE6 test-package gate | The only side-accounting identity, and each of the seven S1.7 clauses, now has a pinned supplier | `EFF.T2.78` |
| `HE6-BETA-GUARD` well-posedness and its transitive consumption route | Correction pinned; conclusion byte-unchanged; census widened by Rider 2.1 to the transitive `HE6-ACCOUNT` route | `EFF.T2.84, .85, .86` |
| `HETOW-KEY-BRIDGE-C-A` and the master-side degree-bound derivation | Correction pinned regardless of mathematical impact; imported conjunct replaced by a two-line master-side argument | `EFF.T2.89, .90` |
| Dated-append sweep, all three legs (HE6 six-append; five non-HE6-source eleven-unit; final 28-unit re-enumeration) | HE6 leg: one hit, pinned; five-source leg: exactly one hit, pinned; final pass-2 re-enumeration of all six sources | `EFF.T2.84, .85, .89, .91, .100` |
| Pin-note directive coherence audit | Every reading directive at a pin (β-guard, C-A, TOWERRAT2-C, `(Q-DEF)`) audited and classified, not left silent | `EFF.T2.50, .54, .77, .84, .89, .93, .100` |
| Standing S7 consumption sweep (every round; naming vs. consumption distinguished) | Run and recorded across every round; declinations signed; a directive obeyed is consumed even if unnamed | `EFF.T2.03, .06, .11, .12, .47, .55, .61, .66, .79, .81, .91, .93, .98` |
| Orphan check on withdrawals | All six withdrawn supports registered with their surviving grounds | `EFF.T2.66` |
| Fence-leakage attacks on the four standing conditionalities | Displayed with their fences and per-instance discharges; the r9 pass's own fence-leakage check upheld | `EFF.T2.101` |
| Byte-freeze / append discipline | Accepted text fixed; append-only regime declared | `EFF.T2.104` |
| Downstream consumption (queued, nothing claimed) | Explicitly queued at the governing block | `EFF.T2.105` |
| Zero synthetic markers / zero source edits | Re-reported by every pass and independently re-run at this merge (§4.C) | `EFF.T2.102` |
| S7 acceptance gate (two consecutive clean hostile passes over one effective text) | Counter reset by every gap-bearing round, held (not reset) by every minors-only rider, superseded to **2/2** at the governing block | `EFF.T2.45, .46, .57, .58, .64, .65, .67, .73, .75, .76, .82, .83, .87, .88, .97, .99, .100` |

**Forward check:** all 105 statement units carry a nonempty `TEETH` field and appear in
at least one row above (verified by cross-listing every shard's own zero-orphan claim,
each independently confirmed in its own §6, and by construction of the merged rows
above directly from each shard's own table with no unit dropped in the merge).

**Inverse check:** every row above names at least one statement unit carrying the
corresponding response.

**Zero-orphan result (unified):** 0 statement teeth orphaned; 0 inverse teeth orphaned;
0 of 0 numbered battery rows orphaned (T2 owes no battery, consistently across all six
shards' own zero-orphan findings).

---
## 7. HOME-ROUTING AUDIT

Shards 2–6 each carry their own `## 7. HOME routing audit` table (or, for shard 1, a
`## 7. BOUNDARY SELF-AUDIT` in the absence of any incoming routing, since shard 1 is the
base-text destination every later shard resolves into). This merge does not re-render
all five tables verbatim — they remain the run-of-record trace in the shard files — but
verifies their aggregate claim and reconciles the parts that require compiler judgment:
the physical-block accounting, the nine multi-leg exceptions, and the three genuine
cross-shard (non-shard-1) supersessions.

### 7.1 Physical-block accounting (aggregate, cross-checked against each shard's own
self-audit line)

| Shard (new range) | Physical blocks in HOME range | Homed locally | Routed (to shard 1's base text, or — for the three flagged cases in §7.3 — to an earlier process shard) |
|---|---:|---:|---:|
| `EFF.T2.45`–`.57` (old s2) | 27 | 13 | 14 |
| `EFF.T2.58`–`.66` (old s3) | 18 | 9 | 9 (includes the 2 blocks amending old-s2 material, r6 repairs 4 and 6(b)) |
| `EFF.T2.67`–`.81` (old s4) | 20 | 15 | 5 (includes the 1 block amending old-s3 material, r9 repair 1) |
| `EFF.T2.82`–`.96` (old s5) | 24 | 15 | 9 (includes the 1 block — r12 repair 4, compiled as `EFF.T2.94` — that also amends old-s4 material via its sub-part (d)) |
| `EFF.T2.97`–`.105` (old s6) | 11 | 11 | 0 — the only shard of the six with no routed block, which is what it means for a block to be governing |
| **Total** | **100** | **63** | **37** |

Every physical block of every shard's charged range is accounted for in exactly one of
the columns above — each shard's own self-audit states this independently ("All N
physical blocks of the range accounted for"). Some physical blocks (notably `EFF.T2.94`,
r12 repair 4) carry mixed routing — part to shard 1's base text, one sub-part to an
earlier process shard — without contradiction, since "routed" and "homed locally" are
assessed per sub-part inside that block's own `RESOLUTION TRACE`, not per physical line
range; no discrepancy was found reconciling any tally against the destination units it
names.

### 7.2 The nine flagged multi-leg exceptions — verified to land exactly once

Reproduced from §1 (the SHARD-MAP section) for completeness of this audit: `EFF.T2.59`,
`.60`, `.61`, `.62` (old s3, 4 exceptions), `EFF.T2.69`, `.70`, `.71`, `.72` (old s4, 4
exceptions), and `EFF.T2.90` (old s5, 1 exception) are each a "physical block" that is
**not** purely routed — its statement content lives locally (since it carries a
multi-leg quoted-source derivation its shard-1 destination compresses to one clause) —
and each was cross-checked against its named destination's own `DERIVATION` field to
confirm the destination does NOT also carry the multi-leg content (no duplication) and
DOES name the compression explicitly (no gap): `EFF.T2.19` compresses `.59`/`.60`/`.69`/`.71`;
`EFF.T2.20` compresses `.70`/`.72`; `EFF.T2.24` compresses `.62`/`.90`; `EFF.T2.25`
compresses `.61`. Zero duplicates, zero gaps.

### 7.3 The three cross-shard (non-shard-1) supersessions — verified to land exactly once

Reproduced from §1: r6 repair 6(b) → `EFF.T2.56`; r9 repair 1 → `EFF.T2.60`; r12 repair
4(d) → `EFF.T2.71`. Each amending unit's own text already states the replacement in
full (not merely a pointer), and each amended unit's `CONDITIONALITY` field already
names the superseding unit and states precisely what survives unchanged — so the merge
introduces no new edit at either end; it only re-confirms, under the new contiguous IDs,
that the amendment is recorded once, at the amended unit, and not silently duplicated at
the amending unit as well. Checked and confirmed for all three (§1).

### 7.4 No shard-1 unit carries stale pre-supersession text

This is a structural guarantee, not a search result: shard 1 (`EFF.T2.01`–`.44`) was
compiled directly from the **fully-resolved effective text** — i.e., after every r1–r12
round and all three post-pass rider blocks were already applied to the base S0–S8
sections — so its units were never in a position to go stale relative to a later
shard's supersession. The forty-four base units already display final-state wording
(for example `EFF.T2.19`'s conditionality already reads "(RISE) is a carrier
hypothesis, not an open ledger obligation", the r9/r10-corrected form, not any
intermediate r6/r7 wording). Confirmed by reading all forty-four `EFF.T2.01`–`.44` units
in full against the corresponding passages of the six process shards: no divergence
found. What the nine exception units and three cross-shard supersessions supply is
argumentation and historical narrative *underneath* that already-final wording, never a
correction *to* it.

---

## 8. Boundary self-audit (shard-edge unit integrity)

Every shard's own §7/§8 "BOUNDARY SELF-AUDIT" states, independently, that no statement
unit is physically split by its shard's leading or trailing edge — where a repair round
straddles a shard boundary (r6 at the s2/s3 edge, r8 at the s3/s4 edge, r10 at the
s4/s5 edge), the round's header and early repairs are compiled as a flagged **boundary
unit** in the earlier shard, and its later repairs and counter are compiled as ordinary
units in the following shard, with each half naming the other by (now-renumbered) ID:

| Straddling round | Header/early repairs (boundary unit) | Later repairs/counter |
|---|---|---|
| r6 | `EFF.T2.57` (header, old s2of6.13) | `EFF.T2.58`–`.66` (repairs 1–7 + counter, old s3) |
| r8 | `EFF.T2.65` (header + repair 1, old s3of6.08) | `EFF.T2.68`–`.69` (repairs 2–4 + counter, old s4) |
| r10 | (header + repairs 1–2 compiled whole in old s4, `EFF.T2.77`–`.81`) | `EFF.T2.82` (counter, old s5) |

No fourth straddling case exists: r12 is complete within `EFF.T2.82`–`.96` (old s5), and
post-pass rider 3 plus the acceptance record open a fresh, whole block at `EFF.T2.97`
(old s6) — the trailing edge of `EFF.T2.96` falls between whole blocks, not mid-round.
Every shard's own leading/trailing-edge statement is consistent with every adjacent
shard's, and no statement unit anywhere in the merged inventory is a partial fragment of
another.

---
## 9. Self-audit and OPEN-CALLS

### Open calls

**Zero.** Every one of the six shards' own compile lines records `0 open calls`
(`EFF.T2.44`'s shard: 0/37; old s2: 0/37; old s3: 0/44; old s4: 0/33; old s5: 0/30; old
s6: 0/12), and a body-level sweep of all six source shards for the literal string
`OPEN-CALL` finds it used only inside each shard's own XREF-method sentence ("A count
other than exactly 1 ... would have been an `OPEN-CALL`; none occurred") and its own
XREF-result line — never as a live, numbered, unresolved item. No shard carries a
`FOR-0x` phase-routing tag (a corpus-wide grep for `FOR-0` across all six shards returns
nothing), unlike EFF-T3's `FOR-0d`. **There is therefore nothing to carry forward under
this heading.** This is a different position from EFF-T1, whose merge carried forward
five named OPEN-CALLs verbatim; T2 has none.

What T2 does carry forward, and what must not be mistaken for an OPEN-CALL, are its two
named **open mathematical obligations**: `(LB1)` (`EFF.T2.18`) and `(MP1)`
(`EFF.T2.23`), both reaffirmed at the governing block (`EFF.T2.101`). These are
conditionalities on the accepted theorem, not compiler XREF failures — shard 1 says so
explicitly ("The two source-level open obligations are part of the accepted theorem's
conditionality ledger. They are not `OPEN-CALL`s caused by unresolved compiler XREFs"),
and every later shard's own resolution rules repeat the distinction.

### Fidelity audit (merge-level, in addition to each shard's own)

- All 105 canonical statement units carry mandatory `DERIVATION`, `CONDITIONALITY`,
  `RESOLUTION TRACE`, and `TEETH` fields, verbatim-or-`[ASSEMBLED]` per the template.
- Every source table is marked `[TABLE]`; no source table was prosified at merge time.
- The 37 unique pin designations of the primary XREF ledger (§4.A) all have fixed-string
  counts of exactly 1; a 12-item cross-shard sample (§4.C) was re-grepped fresh at merge
  time against the working tree and matched exactly; a 6-statement quote sample (§4.C)
  was re-checked byte-for-byte against the source note by line number and matched
  exactly. Zero drift.
- No shard's numbering collides with another's after the SHARD-MAP renumbering (§1); no
  cross-reference inside any `DERIVATION`/`CONDITIONALITY`/`RESOLUTION
  TRACE`/`TEETH`/ledger/audit field still points at a retired `EFF.T2.sKof6.NN` ID —
  verified by an exhaustive machine sweep of the merged text (§1's SHARD-MAP note), which
  also caught and corrected several apostrophe-possessive (`shard N's`), sentence-initial
  capitalized (`Shard N`), and compound (`shards 3 X and 4 Y`) cross-reference forms that
  a first mechanical pass missed.
- The nine multi-leg exception units and three genuine cross-shard supersessions each
  resolve to exactly one place in the merged inventory (§7.2–7.3); no material is
  duplicated or dropped.
- Absorption status (mathematical supply, §5.2) and the append/consumption protocol
  (§5.1, and the "Consumption-protocol status" column throughout) are kept as distinct
  predicates everywhere, matching all six source shards' own discipline.
- The two standing open obligations (`(LB1)`, `(MP1)`) and the two carrier hypotheses
  that fence nothing (`(SEC-RANK)`, `(RISE)`) are kept distinct throughout, per resolution
  rules 3–4 (§1); `(MP1′)` is never stated as an effective conditionality anywhere in the
  merged text, per resolution rule 5.
- The final pin inventory (37; taxonomy \(20+4+13\); zero synthetic markers; zero source
  edits; cured-consumption census ten) and the final five Source-pin lines (`EFF.T2.96`)
  are stated once, as final, and are not contradicted by any earlier-round snapshot
  anywhere in the merged text — every earlier snapshot is explicitly marked historical at
  its own unit.

---

EFF-T2 MERGED: 105 statements / 37 pin designations verified (plus 6 shards' own
process-verification ledgers, summarized §4.B) / 0 open calls
