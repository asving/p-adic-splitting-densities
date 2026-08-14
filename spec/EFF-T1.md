# EFF-T1 — CANONICAL EFFECTIVE-SPECIFICATION (MERGED)

## 1. Merge header

**Source note:** `lean/notes/openmath/T1_GAUGE_COCYCLE_2026-08-12.md` (4416 lines).

**HEAD blob hash:** `445599d6b92289182252199bd6e6618c4d84092e` — independently confirmed identical
across all three source shards' headers and by `git hash-object` against the working-tree
file at merge time. No divergence found; the merge proceeds.

**Compilation context:** `spec/EFF_TEMPLATE_v2.md`.

**Merged from:** `spec/EFF-T1-s1of3.md` (lines 1–3102, 48 statements, 17 xrefs, 5 open
calls), `spec/EFF-T1-s2of3.md` (lines 3103–4193, 2 statements, 14 xrefs, 0 open calls),
`spec/EFF-T1-s3of3.md` (lines 4194–4416, 5 statements, 10 xrefs, 0 open calls). **This
file supersedes the three shards as the citable unit for all downstream consumption.**
The shard files are NOT deleted — they remain the run-of-record trace of the sharded
compilation — but any consumer citing `EFF.T1.*` from this point on cites the IDs below,
not the shard-local `EFF.T1.sKof3.*` IDs.

### SHARD-MAP (old shard-local ID → new contiguous ID)

| Old ID | New ID | Old ID | New ID | Old ID | New ID |
|---|---|---|---|---|---|
| EFF.T1.s1of3.01 | EFF.T1.01 | EFF.T1.s1of3.17 | EFF.T1.17 | EFF.T1.s1of3.33 | EFF.T1.33 |
| EFF.T1.s1of3.02 | EFF.T1.02 | EFF.T1.s1of3.18 | EFF.T1.18 | EFF.T1.s1of3.34 | EFF.T1.34 |
| EFF.T1.s1of3.03 | EFF.T1.03 | EFF.T1.s1of3.19 | EFF.T1.19 | EFF.T1.s1of3.35 | EFF.T1.35 |
| EFF.T1.s1of3.04 | EFF.T1.04 | EFF.T1.s1of3.20 | EFF.T1.20 | EFF.T1.s1of3.36 | EFF.T1.36 |
| EFF.T1.s1of3.05 | EFF.T1.05 | EFF.T1.s1of3.21 | EFF.T1.21 | EFF.T1.s1of3.37 | EFF.T1.37 |
| EFF.T1.s1of3.06 | EFF.T1.06 | EFF.T1.s1of3.22 | EFF.T1.22 | EFF.T1.s1of3.38 | EFF.T1.38 |
| EFF.T1.s1of3.07 | EFF.T1.07 | EFF.T1.s1of3.23 | EFF.T1.23 | EFF.T1.s1of3.39 | EFF.T1.39 |
| EFF.T1.s1of3.08 | EFF.T1.08 | EFF.T1.s1of3.24 | EFF.T1.24 | EFF.T1.s1of3.40 | EFF.T1.40 |
| EFF.T1.s1of3.09 | EFF.T1.09 | EFF.T1.s1of3.25 | EFF.T1.25 | EFF.T1.s1of3.41 | EFF.T1.41 |
| EFF.T1.s1of3.10 | EFF.T1.10 | EFF.T1.s1of3.26 | EFF.T1.26 | EFF.T1.s1of3.42 | EFF.T1.42 |
| EFF.T1.s1of3.11 | EFF.T1.11 | EFF.T1.s1of3.27 | EFF.T1.27 | EFF.T1.s1of3.43 | EFF.T1.43 |
| EFF.T1.s1of3.12 | EFF.T1.12 | EFF.T1.s1of3.28 | EFF.T1.28 | EFF.T1.s1of3.44 | EFF.T1.44 |
| EFF.T1.s1of3.13 | EFF.T1.13 | EFF.T1.s1of3.29 | EFF.T1.29 | EFF.T1.s1of3.45 | EFF.T1.45 |
| EFF.T1.s1of3.14 | EFF.T1.14 | EFF.T1.s1of3.30 | EFF.T1.30 | EFF.T1.s1of3.46 | EFF.T1.46 |
| EFF.T1.s1of3.15 | EFF.T1.15 | EFF.T1.s1of3.31 | EFF.T1.31 | EFF.T1.s1of3.47 | EFF.T1.47 |
| EFF.T1.s1of3.16 | EFF.T1.16 | EFF.T1.s1of3.32 | EFF.T1.32 | EFF.T1.s1of3.48 | EFF.T1.48 |
| EFF.T1.s2of3.01 | EFF.T1.49 | EFF.T1.s2of3.02 | EFF.T1.50 | | |
| EFF.T1.s3of3.01 | EFF.T1.51 | EFF.T1.s3of3.02 | EFF.T1.52 | EFF.T1.s3of3.03 | EFF.T1.53 |
| EFF.T1.s3of3.04 | EFF.T1.54 | EFF.T1.s3of3.05 | EFF.T1.55 | | |

Shard 1's offset is 0 (its own numbering is already contiguous from 1); shard 2 carries
a +48 offset; shard 3 carries a +50 offset. Every `EFF.T1.sKof3.NN` occurrence — full-form
and the bare `.NN` shorthand used inside each shard's own tables — has been rewritten
throughout the merged text below to the new ID under this map, so no cross-reference
inside a DERIVATION, CONDITIONALITY, RESOLUTION TRACE, TEETH, or ledger field points at a
retired shard-local ID. The two exceptions are deliberate and unchanged: `EFF.T1.s3of3.md`
lines referring to "shard-1 units `.02` and `.44`" and "shard-1 `.47`" already named
shard 1's (offset-0) IDs and are reproduced as `EFF.T1.02`/`.44`/`.47` unchanged.

### Header unification and blob-hash check

All three shards' front matter quotes the same governing status line and the same
acceptance-record text:

> "**Status:** ACCEPTED note of record — the hostile arc is closed at 2/2 and the
> accepted text is byte-frozen; THE ACCEPTANCE RECORD AT THE END OF THIS NOTE GOVERNS."

> "The accepted T1 of record is the effective text as of r13, plus the post-pass rider
> block, plus Riders 6 and 7, and consumers cite it as exactly that."

All three shards cite **the same HEAD blob hash**, `445599d6b92289182252199bd6e6618c4d84092e`.
No divergence was found (this was the STOP condition per the merge charge; it did not
trigger).

### Scope of record — mandatory two-predicate split (unified from all three shards)

**A. Mathematical absorption/supply set.** Per shard 1's R13-1 quote and shard 2's
EFF.T1.50:

> "After this retirement the effective text contains exactly ONE authoritative A-row
> status list: §3's A1 block (two rows) together with the A2–A7 pinned-span blocks."

**B. Consumption/append-protocol scope**, stated identically (word-for-word) in all
three shard headers and again in the acceptance record proper (EFF.T1.54):

> "Consumption checks of the seven annexes against the accepted text, and the absorbed
> notes' dated appends, ride the next queue (the T3/T4/T5 pattern)."

These two predicates are never conflated anywhere below: §3 (via A1 + the A2–A7 blocks,
`EFF.T1.24–.32`) determines what T1 supplies mathematically; the note's own hostile-pass
acceptance (`EFF.T1.51–.52`) certifies that text as accepted; and the seven-annex
consumption/append protocol (tracked per-annex in §5 below) remains outstanding under
all three predicates simultaneously.

### Resolution rules applied (merged; each shard's own rule-list is a restriction of this
one to its HOME range, so no rule is dropped, only consolidated)

1. The accepted effective text is 2026-08-12 base §§1–7, plus r1–r13 textual
   replacements/insertions/read-as rules/span re-declarations applied in chronology
   (later directives govern earlier text), plus the post-pass rider block, plus Riders
   6–7, plus the final acceptance fold. This is the text every statement below resolves
   against.
2. R13-1 retires the base §3 absorption table through its final row, relocates A1, and
   leaves the A2–A7 pinned-span blocks authoritative (`EFF.T1.24–.32`); the disposition
   of every retired row is the exhaustive ledger `EFF.T1.49` plus its status-authority
   companion `EFF.T1.50`.
3. R13-2/R13-3 remove the duplicate unfenced C4-support and clearance readings; only
   their supplier-fenced forms survive (`EFF.T1.17`, `.21`).
4. R13-4 through R13-6 fix strict-assembly boundaries without changing formulas.
5. Riders 1–4 repair referents and enumerations; Rider 2 restores the `Verbatim`
   definition for A1 (`EFF.T1.24`).
6. R13-8 plus Riders 5–7 govern the grade-data value group and battery check 10
   (`EFF.T1.02`, `.44`) — physically drafted in the shard-3 range but HOME-routed to
   shard 1, per rule 9 below.
7. R13-7 supersedes honesty-ledger item 4 — physically drafted at the shard-2/shard-3
   boundary but HOME-routed to base §5 (`EFF.T1.46`, items 2/4/19/22).
8. §6 is a historical changes record (`EFF.T1.47`). Under R13-1(d), it never overrides
   §3's authoritative absorption status; where the two conflict, §3 governs.
9. **HOME is determined by an edit's destination section, not its physical line
   position.** A directive physically drafted in one shard's line range that inserts,
   replaces, or supersedes material whose destination is an earlier shard's section
   resolves that earlier shard's unit and is not re-emitted as a separate statement.
   Three units are split across a shard boundary this way; §7 below verifies each
   resolves to exactly one place in the merged inventory.
10. The acceptance record (`EFF.T1.51–.55`) supersedes every intermediate counter state
    (the r13 reset to 0/2, the post-pass 1/2 counter) and is the final status authority,
    with one permitted in-place edit (the dateless front-matter status line).

### Quotation and table discipline

Unchanged from all three shards: canonical statements are verbatim source quotations or
explicitly marked `[ASSEMBLED]`; every source table is transcribed as a table and marked
`[TABLE]`; compiler-authored ledgers (XREF tables, consumption ledgers, TEETH inverse
tables, routing audits) are marked `[TABLE — compiler ledger]` and are not source
statement units.

---

## 2. NON-IMPORTS (consolidated from all three shards; dedup marked)

`[TABLE — consolidated from shard 1 §4, shard 2 §5, shard 3 §5]`

| Fence | Explicit material not imported or not proved by T1 | Source |
|---|---|---|
| Carrier | "The carrier contains no letter recursion, cocycle identity, corrected-key formula, read dictionary, print-origin bridge, or weld coherence theorem." | s1 |
| General C1 | No arbitrary-depth canonical-letter monomiality without `(H-JA-CONJ)_i`. | s1 |
| C3 reads | No multiplicativity theorem for all homogeneous initial forms; no scalar codomain or nonvanishing without their independent site obligations. | s1 |
| C3 factor patterns | No conversion from residual factor pattern to p-adic splitting type; the surrounding tower correctness theorem is external and unnamed (OPEN-CALL 4). | s1 |
| C4 | No whole-polynomial harness/print comparison from C4-origin alone. | s1 |
| C6 | No universal full `K_1` slot at `M≤D'h`; no polygon clearance without `(H-GENHN-CLEAR)`. | s1 |
| C7 | No single map across M0–M4, no cross-face compatibility theorem, no gauge uniqueness, and no character-torsor classification. | s1 |
| A2 (absorption content) | No HETOW-4(c)–(d), side assembly, routing, or common refinement polynomial. | s1 |
| A2 (relocation scope) | The old `Verbatim` classification does not import HETOW's local bridge, function `m`, canonical range, binary carry, or `τ` identification into T1. | s2 |
| A3 (absorption content) | No budgets, floors, fibration, counts, separation, or field-root inequality. | s1 |
| A3 (relocation scope) | T1 does not import the budget floors or the wider GENTOW1/GENHN-2′/HE6 conclusions from the corrected-coefficient pin. | s2 |
| A4 (absorption content) | No shadow/composed-grid comparison, floors, faithful-band theorem, attainment, or perturbation theorem. | s1 |
| A4 (relocation scope) | The two gauge displays do not import THEOREM GENTOW-3 as a whole. | s2 |
| A5 (absorption content) | No all-sides slope bound, point-set identification, routing/refinement package, frame peels, or splitting contribution; no equation `Φ_2=Ψ_{κ_2,\widetilde r}-w` from T1. | s1 |
| A5 BOX-3 | The absorption claim is withdrawn (narrowed at R13-1); T1 absorbs nothing from BOX-3. | s2 |
| A5 support | `(C4-origin)` does not import whole-polynomial support comparison without `(H-JA-RES-CONJ)`. | s2 |
| A6 (absorption content) | No GENTOW6 fullness/grid/extraction/noncancellation/attainment theorem; scalar-read provenance is HE6, not GENTOW6. | s1 |
| A6 (relocation scope) | The scalar-read formulas are not imported from GENTOW6; their provenance is HE6 F-1. No wider GENTOW-6.3 conclusion follows. | s2 |
| A7 (absorption content) | No proof of the supplier identity `u(β_t)=Θ(t)w^{f_3-t}`; no theorem-wide absorption from the pins. | s1 |
| A7 (relocation scope) | T1 does not prove `u(β_t)=Θ(t)w^{f_3-t}` and does not import general factor-pattern preservation into the pinned GENTOW2-B span. | s2 |
| §6 | Historical annex-effect prose is not an authority for absorption status. | s2 |
| Final riders (acceptance) | Their fold imports no new formula, pin, hypothesis, consumption check, or absorption status. | s3 |
| Review grade | 2/2 does not import a nonexistent third hostile review of Riders 6–7. | s3 |
| PASS 2 provenance | PASS 2 does not supply a byte-level reopening of supplier HEAD files. | s3 |
| Battery ambiguity | The alternate Reading A row is not imported as a failure; Rider 7 makes the two readings extensionally agree. | s3 |
| Historical evidence | The 2026-08-10 sealed run is not imported as certification of the accepted revision. | s3 |
| Acceptance versus hypotheses | Acceptance does not clear the honesty ledger, the sitewise read bundle, the depth-`i≥3` telescope fence, the live lift domain, or the WELD scope fence. | s3 |
| Protocol **[DEDUP — s1/s2/s3 each asserted this in different wording; merged to one row]** | No accepted downstream consumption-check or dated-append result rides on mathematical absorption, note-acceptance, or §3 status alone; all seven annex consumptions and the absorbed notes' dated appends ride the next queue. | s1+s2+s3 |

**Dedup count for this section: 1** (the three near-identical "Protocol" closing rows
in shard 1 §4, shard 2 §5, and shard 3 §5 assert the same negative edge in different
words and are merged into the single row above).


## 3. Statement inventory (55 units, contiguous, in source order)

### EFF.T1.01  [hypothesis]

**CANONICAL STATEMENT:** [ASSEMBLED — effective §1.1 carrier, base lines 22–53 plus R1-1/R5-3]

> “Fix a discretely valued base field with uniformizer \(\pi\), residue field \(\mathbf F_Q\), and a MacLane/Okutsu tower with level-\(i\) residue field \(K_i\). At level \(1\), fix
> \[
> e_1,f_1,h\ge1,\qquad \gcd(e_1,h)=1,\qquad D'=e_1f_1,
> \]
> with
> \[
> dv_1(x)=h,\qquad dv_1(\pi)=e_1,
> \qquad
> \eta=\operatorname{res}\!\left(\frac{x^{e_1}}{\pi^h}\right),
> \qquad
> K_1=\mathbf F_Q(\eta).
> \]”

> “Fix also the chosen \(\mathbf F_Q\)-basis
> \[
> 1,\eta,\ldots,\eta^{f_1-1}
> \]
> of \(K_1\).”

> “For every integer height \(k\), let
> \[
> \widehat n_1(k)=x^{i(k)}\pi^{a(k)},\qquad
> 0\le i(k)<e_1,\qquad i(k)h+a(k)e_1=k.
> \]”

> “A full integral \(K_1\)-digit slot is asserted below only on the proved live domain \(k>D'h\). No full \(K_1\)-slot is asserted at \(k\le D'h\).”

**CONDITIONALITY:** The displayed valued-field and tower data are hypotheses; the full level-one digit slot is restricted to `k>D'h`.

**DERIVATION:** [ASSEMBLED — resolved effective proof] The carrier definitions are assumptions. The normalizer has exact height because its defining exponents satisfy `i(k)h+a(k)e_1=k`; the live-domain lift is derived in EFF.T1.20.

**RESOLUTION TRACE:** Base §1.1; R5-3 reattaches the basis sentence. No later round changes these values.

**TEETH:** §4.2 check 1 guards the live-domain boundary.

---

### EFF.T1.02  [hypothesis]

**CANONICAL STATEMENT:** [ASSEMBLED — general carrier after R1-2, R3-1, R4-1/R4-2, R8-1, R11-5, R12-1/R12-2, R13-5/R13-8, Rider 6]

> “At a general level \(i\), fix exact-height normalizers \(\widehat n_i(m)\) in the prescribed bounded-exponent tower normal form, with the height-zero normalization
> \[
> \boxed{\widehat n_i(0)=1.}
> \tag{C2-zero-normalizer}
> \]”

> “Fix also the stage element \(\pi_{i+1}\) with
> \[
> \boxed{dv_i(\pi_{i+1})=1.}
> \tag{C1-stage-uniformizer}
> \]”

> “Fix also a monic stage key \(\Phi_i\), put \(d_i:=\deg\Phi_i>0\), and assume the stage-height identity
> \[
> \boxed{dv_i\!\left(\Phi_i^{e_{i+1}}\right)=u_{i+1}.}
> \tag{C1-stage-key-height}
> \]”

> “Fix also, as part of the same stage data,
> \[
> \psi_{i+1}(y)=y^{f_{i+1}}-\sum_{t<f_{i+1}}c_ty^t\in K_i[y],
> \qquad c_0\ne0.
> \]”

> “Whenever a lift is invoked, assume that \(m\) lies in its stated integral domain” and
> \[
> \operatorname{res}\!\left(\frac{\operatorname{lift}_i(d;m)}{\widehat n_i(m)}\right)=d,
> \quad
> dv_i(\operatorname{lift}_i(d;m))=m\ (d\in K_i^\times),
> \quad
> \operatorname{lift}_i(0;m)=0,
> \quad dv_i(0)=+\infty.
> \tag{C3-lift-residue/C3-lift-height/C3-zero-lift}
> \]

> “Every lift used as a coefficient in (C3-key) is additionally required to lie in the standard bounded coefficient space”
> \[
> \boxed{\deg(\operatorname{lift}_i(d;m))<\deg\Phi_i.}
> \tag{C3-lift-coefficient-space}
> \]

> “Throughout, \(\mu_i\) is the level-\(i\) valuation of the MacLane/Okutsu tower, and \(e(\mu_i)\) is its ramification index over the base valuation — cumulative, so \(e(\mu_1)=e_1\) and \(e(\mu_{i+1})=e_{i+1}\,e(\mu_i)\); the per-stage index over \(\mu_{i-1}\) is \(e_i\), not \(e(\mu_i)\).”

> “Heights at level \(i\) — the arguments \(m\) of \(\widehat n_i(m)\), and the values of \(dv_i\) at every NONZERO-ARGUMENT site consumed in this note — are integers in the normalization \(dv_i=e(\mu_i)\cdot v\), where \(v\) is the base-normalized TERMINAL valuation of the tower.”

> “Grades … lie in the grade group
> \[
> \Lambda_i=\frac1{e(\mu_i)}\mathbb Z,
> \]
> with height-to-grade conversion \(\widehat\beta=e(\mu_i)\beta\).”

> “\(dv_i=e(\mu_i)\cdot v\) takes values in
> \[
> e(\mu_i)\Lambda_r=\frac{e(\mu_i)}{e(\mu_r)}\mathbb Z\supseteq\mathbb Z.
> \]”

> “Every \(dv_i\)-value consumed AT A NONZERO ARGUMENT in the effective text is nevertheless an integer, in one of four classes; the one consumed non-finite value is the zero convention \(dv_i(0)=+\infty\) of class (iii) below, disclosed there and excluded from this integrality claim by the present scoping.”

> “(i) Typed stage and lift heights: \(dv_i(\pi_{i+1})=1\) and \(dv_i(\pi_{i+1}^{u_{i+1}})=u_{i+1}\) (C1-stage-uniformizer); \(dv_i(\widehat n_i(m))=m\) by exact height; \(dv_i(\operatorname{lift}_i(d;m))=m\) (C3-lift-height); \(dv_i(\widehat k_t)=su_{i+1}\). (ii) Stage-key powers, which are consumed ONLY as \(\Phi_i^{e_{i+1}t}\): \(dv_i(\Phi_i^{e_{i+1}t})=tu_{i+1}\) by (C1-stage-key-height). No clause of this note takes \(dv_i\) of a bare \(\Phi_i^{k}\) with \(e_{i+1}\nmid k\). (iii) Value-zero factors, \(dv_i(g)=0\), and the zero convention \(dv_i(0)=+\infty\) (C3-zero-lift). (iv) The level-one grid, where \(dv_1(x)=h\) and \(dv_1(\pi)=e_1\) are integers and (C5)/(C6) apply \(dv_1\) only to nonzero elements of degree \(<D'=\deg\Phi_1\) (R3-2's \(A\ne0\); R8-1's \(\deg\Phi_1=D'\)), which are level-1-free, so \(\mu_1=v\) there by the clause above. The re-scoped clause therefore costs no consumer, and the grade clause above is unaffected: grades are attached to the integer heights, so \(\bar\kappa_i=u_{i+1}/e(\mu_i)\) and \(\beta_t=(f_{i+1}-t)\bar\kappa_i\) lie in \(\Lambda_i\) as stated.”

**CONDITIONALITY:** Exact lift height requires a nonzero digit; zero uses valuation `+∞`. The integrality claim covers only consumed nonzero arguments. Coefficient lifts must satisfy both the residue/height contract and the independent degree bound.

**DERIVATION:** [ASSEMBLED] R4-1 derives `dv_i(Φ_i^{e_{i+1}s})=su_{i+1}` from the stage-key identity. R12-1 verifies the terminal binding on the GENTOW2 witness by `4·2·21/8=21=u_3` and falsifies the `v=μ_2` reading by `20<21`. R13-8 derives the stated value group from `v∈Λ_r`; Rider 6 removes the zero argument from the integer claim.

**RESOLUTION TRACE:** Base §1.1, replaced or extended by r1, r3, r4, r8, r11, r12, r13, and Rider 6. R13-5 reattaches `ψ`; R13-8 and Rider 6 govern the final value-group wording.

**TEETH:** §4.2 checks 1, 7, and 10.

---

### EFF.T1.03  [hypothesis]

**CANONICAL STATEMENT:** [ASSEMBLED — effective consumed-read bundle from R5-1, R7-1, R8-2, R11-1]

At each consumed B-law site:

> \[
> \boxed{R_{i+1,s\bar\kappa_i}(N^s)=R_{i+1,\bar\kappa_i}(N)^s}
> \tag{C3-ladder-multiplicativity}
> \]

> \[
> \boxed{R_{i+1,\beta}(Xg)=R_{i+1,\beta}(X)\operatorname{res}(g)}
> \tag{C3-graded-scalar-covariance}
> \]

> \[
> \boxed{R_{i+1,\beta}(0)=0}
> \tag{C3-zero-read}
> \]

> \[
> \boxed{R_{i+1,\bar\kappa_i}(\widehat n_i(u_{i+1}))\ne0}
> \tag{C3-ladder-nonvanishing}
> \]

> \[
> \boxed{R_{i+1,\beta}(\text{consumed grade-}\beta\text{ slice})\subseteq K_i.}
> \tag{C3-read-codomain}
> \]

Put

> \[
> \bar\kappa_i=\frac{u_{i+1}}{e(\mu_i)},
> \qquad N_i:=\widehat n_i(u_{i+1}),
> \qquad w_i=R_{i+1,\bar\kappa_i}(N_i).
> \]

At a site carrying codomain and nonvanishing:

> \[
> \boxed{w_i\in K_i^\times.}
> \tag{C3-ladder-unit}
> \]

> “These are site obligations, or may be discharged by a named per-grade residual-read supplier; they are not assertions about every homogeneous initial form.”

**CONDITIONALITY:** All five clauses are sitewise. Zero digits use `C3-zero-read`, not a value-zero factor of residue zero.

**DERIVATION:** [ASSEMBLED — resolved effective proof] These are hypotheses, not derived conclusions. The note's countermodels prove independence: a read vanishing on every positive-grade component defeats nonvanishing; the initial-form read into `gr(μ_i)` satisfies the other displayed read axioms but defeats the scalar codomain.

**RESOLUTION TRACE:** R5-1 installs multiplicativity/covariance; R7-1 adds zero; R8-2 adds nonvanishing; R11-1 adds codomain and makes the unit gate two-clause.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:(R-FGMN)` — grep-verified count **1**; supplies the `i=2` codomain typing.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B′` — grep-verified count **8**.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` — grep-verified count **10**.

**TEETH:** §4.2 checks 5, 8, and 9.

---

### EFF.T1.04  [definition]

**CANONICAL STATEMENT:** [ASSEMBLED — effective C1 setup]

> \[
> \eta_{i+1}=\operatorname{res}\!\left(\frac{\Phi_i^{e_{i+1}}}{\widehat n_i(u_{i+1})}\right),
> \qquad
> z_{i+1}=\operatorname{res}\!\left(\frac{\Phi_i^{e_{i+1}}}{\pi_{i+1}^{u_{i+1}}}\right).
> \]

> \[
> \boxed{z_1:=\eta.}
> \tag{C1-base-letter}
> \]

**CONDITIONALITY:** The stage heights in EFF.T1.02 type both value-zero residues.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Exact height, `C1-stage-uniformizer`, and `C1-stage-key-height` give all three numerator/denominator heights equal to `u_{i+1}`.

**RESOLUTION TRACE:** Base §1.1 plus R1-1, R3-1, and R4-1.

**TEETH:** §4.2 check 10 guards the stage-height typing.

---

### EFF.T1.05  [lemma]

**CANONICAL STATEMENT:** [ASSEMBLED — C1-general after R2-1]

> \[
> \boxed{z_{i+1}=\eta_{i+1}\rho_i,\qquad
> \rho_i=\operatorname{res}\!\left(\frac{\widehat n_i(u_{i+1})}{\pi_{i+1}^{u_{i+1}}}\right).}
> \tag{C1-general}
> \]

> “No arbitrary-depth canonical-letter monomial assertion follows from the T1 carrier.”

At a site carrying the imported hypothesis:

> \[
> \boxed{\rho_i=J_i(z_1,\ldots,z_i).}
> \tag{C1-JA-specialization}
> \]

**CONDITIONALITY:** `C1-general` is unconditional on the carrier. `C1-JA-specialization` requires `(H-JA-CONJ)_i` from an external JA supplier.

**DERIVATION:** [ASSEMBLED] The three defining fractions have value zero, and residue multiplicativity gives `z_{i+1}=η_{i+1}ρ_i`. The specialization is exactly the imported hypothesis; T1 supplies no further derivation.

**RESOLUTION TRACE:** Base C1 and proof §2.1; R2-1 withdraws arbitrary-depth reduction; R3-1/R4-1 type the quotient.

**TEETH:** §7 attack 1; no dedicated battery row.

---

### EFF.T1.06  [lemma]

**CANONICAL STATEMENT:**

> \[
> \boxed{z_2=\eta_2z_1^{-\lfloor\ell_1u_2/e_1\rfloor}.}
> \tag{C1-level-2}
> \]

**CONDITIONALITY:** Level `2`, with `π_2=x^{ℓ_1}π^{ℓ'_1}`, `ℓ_1h+ℓ'_1e_1=1`, `0≤ℓ_1<e_1`.

**DERIVATION:** [ASSEMBLED — effective §2.1] Congruences give `i(u)=ℓ_1u-e_1⌊ℓ_1u/e_1⌋`; the value-zero equation gives the matching `π` exponent, so the quotient is `(x^{e_1}/π^h)^{-⌊ℓ_1u/e_1⌋}`. Taking residues and using `z_1=η` proves the formula.

**RESOLUTION TRACE:** Base C1-level-2 and proof; R1-1 supplies `z_1` and repairs the proof's final sentence.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.1` — grep-verified count **42**; consumer pin.

**TEETH:** §7 attacks 1 and 8.

---

### EFF.T1.07  [definition]

**CANONICAL STATEMENT:**

> \[
> \operatorname{wrap}(a,b)=\left\lfloor\frac{i(a)+i(b)}{e_1}\right\rfloor\in\{0,1\},
> \]
> \[
> \boxed{\widehat n_1(a)\widehat n_1(b)=\widehat n_1(a+b)
> \left(\frac{x^{e_1}}{\pi^h}\right)^{\operatorname{wrap}(a,b)}.}
> \tag{C2-wrap}
> \]

**CONDITIONALITY:** Level `1` normalized section.

**DERIVATION:** [ASSEMBLED — resolved effective proof] The reduced exponent satisfies `i(a)+i(b)=i(a+b)+e_1 wrap(a,b)`; height additivity supplies the corresponding `π` exponent.

**RESOLUTION TRACE:** Base C2 and proof §2.2; untouched by later rounds.

**TEETH:** §4.2 check 2 and the wrong-sign/misindexed teeth.

---

### EFF.T1.08  [lemma]

**CANONICAL STATEMENT:**

> \[
> \tau_i(a,b)=\frac{\widehat n_i(a)\widehat n_i(b)}{\widehat n_i(a+b)},
> \]
> \[
> \tau_i(0,a)=\tau_i(a,0)=1,
> \qquad
> \boxed{\tau_i(a,b)\tau_i(a+b,c)=\tau_i(b,c)\tau_i(a,b+c).}
> \tag{C2-cocycle}
> \]

**CONDITIONALITY:** All displayed heights and sums must be defined.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Associativity compares the two parenthesizations of three normalizers. `\widehat n_i(0)=1` gives both endpoints.

**RESOLUTION TRACE:** Base C2 and proof; R1-2 supplies the height-zero normalization and endpoint derivation.

**TEETH:** Misindexed telescope tooth.

---

### EFF.T1.09  [definition]

**CANONICAL STATEMENT:** [ASSEMBLED — C2-vartheta plus R9-2 fence]

> \[
> \boxed{\vartheta_{i,s}=\operatorname{res}\!\left(
> \frac{\widehat n_i(u_{i+1})^s}{\widehat n_i(su_{i+1})}\right)\in K_i^\times.}
> \tag{C2-vartheta}
> \]

> “The membership \(\vartheta_{i,s}\in K_i^\times\) displayed in (C2-vartheta) is proved only at \(i\in\{1,2\}\).”

At depth `i≥3`, every consumer must carry:

> \[
> \mathrm{(H\!-!VARTHETA\!-!RES)}_i:\quad
> \operatorname{res}\!\left(
> \frac{\widehat n_i(u_{i+1})^s}{\widehat n_i(su_{i+1})}\right)\in K_i
> \qquad(s\ge0).
> \]

**CONDITIONALITY:** The quotient and residue exist from exact-height arithmetic. `K_i^×` membership is unconditional only for `i=1,2`, and supplier-dependent for `i≥3`.

**DERIVATION:** [ASSEMBLED — resolved effective proof] The quotient has value zero. At `i=1`, EFF.T1.10 gives a power of `η`; at `i=2`, GENTOW2-B″ supplies the letter calculation. At larger depth, membership is precisely the named imported hypothesis.

**RESOLUTION TRACE:** Base C2-vartheta; R9-2 installs the depth fence; acceptance confirms its propagation to C3 and C7.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` — grep-verified count **10**.

**TEETH:** §4.2 checks 5, 8, 9; §7 attack 5.

---

### EFF.T1.10  [lemma]

**CANONICAL STATEMENT:** [ASSEMBLED — C2-recursion and level-one specialization]

> \[
> \boxed{\vartheta_{i,0}=\vartheta_{i,1}=1,\qquad
> \vartheta_{i,s+1}=\vartheta_{i,s}\operatorname{res}(\tau_i(su_{i+1},u_{i+1})).}
> \tag{C2-recursion}
> \]

> \[
> \boxed{\vartheta_{1,s}=\eta^{\lfloor s\,i(u_2)/e_1\rfloor}.}
> \tag{C2-level-1}
> \]

For `s=f_2-t`:

> \[
> W(t)=\left\lfloor\frac{(f_2-t)i(u_2)}{e_1}\right\rfloor,
> \qquad \vartheta_{1,f_2-t}=\eta^{W(t)}.
> \]

> “The exponent has the displayed positive sign.”

**CONDITIONALITY:** For all defined nonnegative ladder exponents; the last formula is level `1`.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Factor `N(u)^{s+1}/N((s+1)u)` through `N(su)`. At level one, reducing `s i(u_2)` modulo `e_1` yields the floor count.

**RESOLUTION TRACE:** Base C2/proof; R1-2 proves the endpoints. R9-2 fences only field membership at depth, not the residue recursion.

**TEETH:** §4.2 check 2; positive-wrap, wrong-sign, and misindexed-telescope teeth.

---

### EFF.T1.11  [definition]

**CANONICAL STATEMENT:**

For `s=f_{i+1}-t`:

> \[
> \boxed{\Gamma_t=c_t^{\mathrm{mult}}\vartheta_{i,s},\qquad
> c_t^{\mathrm{mult}}=\Gamma_t\vartheta_{i,s}^{-1}.}
> \tag{C3-dictionary}
> \]

**CONDITIONALITY:** `\vartheta_{i,s}` must be a `K_i`-unit under EFF.T1.09.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Dividing a height-`su` element first by `\widehat n_i(su)` and then by `\widehat n_i(u)^s` gives `c^{mult}=Γ res(\widehat n_i(su)/\widehat n_i(u)^s)=Γ\vartheta^{-1}`.

**RESOLUTION TRACE:** Base C3 and proof §2.3; R9-2 adds the depth-`≥3` typing fence.

**TEETH:** §4.2 checks 2 and 5; inverse-orientation tooth.

---

### EFF.T1.12  [definition]

**CANONICAL STATEMENT:** [ASSEMBLED — corrected key after R4-1/R4-2, R8-1, R9-2]

> \[
> \boxed{\Phi_{i+1}=\Phi_i^{e_{i+1}f_{i+1}}-
> \sum_{t<f_{i+1}}\widehat k_t\Phi_i^{e_{i+1}t}.}
> \tag{C3-key}
> \]

> \[
> \boxed{\widehat k_t=\operatorname{lift}_i\!\left(
> c_t\vartheta_{i,f_{i+1}-t};(f_{i+1}-t)u_{i+1}\right),
> \qquad \deg\widehat k_t<\deg\Phi_i.}
> \tag{C3-corrected-lift/C3-corrected-coefficient-bound}
> \]

For `c_t≠0`:

> \[
> \boxed{dv_i(\widehat k_t\Phi_i^{e_{i+1}t})=f_{i+1}u_{i+1}.}
> \tag{C3-common-height}
> \]

For `c_t=0`, `\widehat k_t=0` and no finite height is assigned.

**CONDITIONALITY:** Lift-domain and bounded-coefficient hypotheses; `(H-VARTHETA-RES)_i` at depth `i≥3`.

**DERIVATION:** [ASSEMBLED — resolved effective proof] The dictionary makes the multiplicative coefficient exactly `c_t`. Lift height plus stage-key height gives common height. The coefficient degree bound makes every lower term's degree strictly below the monic leading term, including `e_{i+1}=1`, `t=f_{i+1}-1`.

**RESOLUTION TRACE:** Base C3; R4-1/R4-2 supply typed heights and zero branch; R8-1 supplies coefficient space and degree proof; R9-2 supplies the depth fence.

**TEETH:** §4.2 checks 7, 8, 9, and 10.

---

### EFF.T1.13  [lemma]

**CANONICAL STATEMENT:**

When `M_t=(f_2-t)u_2>D'h`:

> \[
> \boxed{\widehat k_t=L_{M_t}(c_t\eta^{W(t)}).}
> \tag{C3-level-1-key}
> \]

> “Its multiplicative coefficient is exactly \(c_t\).”

> “The naive and corrected recipes agree in slot \(t\) exactly when
> \[
> c_t(\vartheta_{i,f_{i+1}-t}-1)=0.
> \]”

**CONDITIONALITY:** Level `1`, live lift domain `M_t>D'h`.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Substitute EFF.T1.10 into the corrected lift; EFF.T1.11 cancels `η^{W(t)}` in the multiplicative read.

**RESOLUTION TRACE:** Base C3; live-domain and zero-branch fences from r4/r6/r7 remain in force.

**TEETH:** §4.2 checks 1 and 2; gauge-naive and wrong-sign teeth.

---

### EFF.T1.14  [lemma]

**CANONICAL STATEMENT:** [ASSEMBLED — effective B-law]

> \[
> \boxed{\Theta_i(t)=\vartheta_{i,f_{i+1}-t}^{-1}
> =\operatorname{res}\!\left(
> \frac{\widehat n_i((f_{i+1}-t)u_{i+1})}
> {\widehat n_i(u_{i+1})^{f_{i+1}-t}}\right).}
> \tag{C3-Theta}
> \]

> \[
> \boxed{\beta_t=(f_{i+1}-t)\bar\kappa_i.}
> \tag{C3-slot-grade}
> \]

At sites discharging the read bundle:

> \[
> \boxed{u(\beta_t)=\Theta_i(t)w_i^{f_{i+1}-t}.}
> \tag{C3-B-law}
> \]

**CONDITIONALITY:** EFF.T1.03, plus EFF.T1.09 for the telescope scalar.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Ladder multiplicativity gives `R(N^s)=w_i^s`; scalar covariance applied to `N^s=M_s(N^s/M_s)` gives `w_i^s=R(M_s)\vartheta_{i,s}`; invert the telescope.

**RESOLUTION TRACE:** Base C3/proof; R5-1 makes covariance and slot grade explicit; R7-1 handles zero components; R11-1 adds scalar codomain.

**TEETH:** §4.2 check 5 and inverse-orientation tooth.

---

### EFF.T1.15  [lemma]

**CANONICAL STATEMENT:** [ASSEMBLED — canonical read and three-read conclusion]

> \[
> \boxed{R_{i+1,\beta_t}(\text{slot }t)=
> w_i^{f_{i+1}-t}\Theta_i(t)\Gamma_t.}
> \tag{C3-canonical-read}
> \]

At a corrected key and a site carrying the full read bundle:

> \[
> \boxed{
> \begin{aligned}
> \text{multiplicative residual}&=\psi_{i+1}(y),\\
> \text{coherent digits}&=(c_t\vartheta_{i,f_{i+1}-t})_{t<f_{i+1}},\\
> \text{canonical residual}&=\psi_{i+1}^{(w_i)}(y):=
> w_i^{f_{i+1}}\psi_{i+1}(y/w_i).
> \end{aligned}}
> \tag{C3-three-reads}
> \]

> “The map \(P(y)\longmapsto w_i^{\deg P}P(y/w_i)\) transports factorizations bijectively and preserves degrees, multiplicities, irreducibility, and a nonzero constant term.”

**CONDITIONALITY:** Both `C3-read-codomain` and `C3-ladder-nonvanishing` are required for `w_i∈K_i^×`; all other read obligations also apply. Zero coherent digits use `C3-zero-read`.

**DERIVATION:** [ASSEMBLED — resolved effective proof] EFF.T1.14 times the coherent digit gives the slot read. At the corrected key, `Γ_t=c_t\vartheta` and `Θ=\vartheta^{-1}` cancel slotwise. Unit substitution is a polynomial automorphism.

**RESOLUTION TRACE:** Base C3/proof, as replaced and fenced by r7, r8, r11, and ledger item 4's r13 form.

**TEETH:** §4.2 checks 5, 8, and 9; inverse-orientation tooth.

---

### EFF.T1.16  [lemma]

**CANONICAL STATEMENT:** [ASSEMBLED — effective C4 opening from R2-5]

For `e>0`, `ℓ,β∈ℤ`, `z∈K^×`, let

> \[
> s_{\min}(\beta)=\operatorname{rem}_e(\ell\beta),\qquad
> t_{\min}(\beta)=\frac{\ell\beta-s_{\min}(\beta)}e,
> \qquad \varepsilon(\beta)=z^{-t_{\min}(\beta)}.
> \]

If `s_act=s_min(β)+νe`, `ν≥0`, then

> \[
> \boxed{z^{t_{\mathrm{Def}}}=z^\nu\varepsilon(\beta),
> \qquad \varepsilon(\beta)=z^{t_{\mathrm{Def}}-\nu}.}
> \tag{C4-origin}
> \]

> “Raw equality \(z^{t_{\mathrm{Def}}}=\varepsilon(\beta)\) holds exactly when \(z^\nu=1\); it holds in particular when \(\nu=0\).”

**CONDITIONALITY:** Typed modular-origin data above.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Substitute `s_act=s_min+νe` into `t_Def=(s_act-ℓβ)/e` to obtain `t_Def=ν-t_min`, then exponentiate by `z`.

**RESOLUTION TRACE:** Base C4/proof; R2-5 types the data; R13-2 affects only the later support paragraph.

**TEETH:** §4.2 check 3; §7 attacks 1 and 6.

---

### EFF.T1.17  [lemma]

**CANONICAL STATEMENT:** [ASSEMBLED — sole live C4-support after R2-2/R12-5/R13-2]

Under the named supplier hypothesis

> \[
> \mathrm{(H\!-!JA\!-!RES\!-!CONJ)}:\quad
> H(y)=y^\nu Q(y),\qquad P(y)=aQ(by),\qquad a,b\in K^\times,
> \]

where `K` is the ambient residue field of the comparison level:

> \[
> \boxed{\operatorname{Supp}_y(H)=\nu+\operatorname{Supp}_y(P),
> \qquad \deg H=\deg P+\nu.}
> \tag{C4-support}
> \]

> “Neither the polynomial identities nor their support consequences follow from (C4-origin) alone.”

**CONDITIONALITY:** The external whole-polynomial conjugation hypothesis; nonzero `H,P,Q`.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Multiplication by `y^ν` translates support; multiplication by a unit and substitution by a unit preserve it.

**RESOLUTION TRACE:** R2-2 replaces the base unfenced support claim; R12-5 binds `K`; R13-2 declares the full replacement span so this box renders once.

**TEETH:** §4.2 check 3; §7 attacks 1 and 6.

---

### EFF.T1.18  [lemma]

**CANONICAL STATEMENT:** [ASSEMBLED — effective C5 after R3-2/R11-5]

For `0≠A(x)=\sum_{j<D'}a_jx^j`, `k=dv_1(A)`, `i=i(k)`:

> \[
> \boxed{\gamma_k(A)=
> \sum_{\substack{t\ge0\\i+e_1t<D'}}
> \operatorname{res}\!\left(a_{i+e_1t}\pi^{-(k-(i+e_1t)h)/e_1}\right)\eta^t.}
> \tag{C5-gamma}
> \]

For each level-one tower point `ξ` with the specified embedding `ι_ξ` satisfying `res(ξ^{e_1}/π^h)=ι_ξ(η)`:

> \[
> \boxed{\operatorname{res}\!\left(\frac{A(\xi)}{n(k)(\xi)}\right)=
> \iota_\xi(\gamma_k(A)).}
> \tag{C5-normalizer-read}
> \]

> \[
> \boxed{\operatorname{res}\!\left(\frac{A(\xi)}{\varpi(\xi)^k}\right)=
> \iota_\xi(\gamma_k(A))\eta_\xi^{-q(k)}.}
> \tag{C5-varpi-read}
> \]

**CONDITIONALITY:** `A≠0`; compatible level-one residue embedding.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Terms outside the congruence class or above height `k` vanish. Direct division turns each tying term into its normalized coefficient residue times `η_ξ^t`; summing gives the first read. Compose with EFF.T1.19 for the `varpi` read.

**RESOLUTION TRACE:** Base C5/proof; R3-2 adds `A≠0` and the embedding; R11-5 reads all un-subscripted `dv` here as `dv_1`.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:F-1 — normalized slot coefficients in LEMMA HE6-0″` — grep-verified count **1**.

**TEETH:** §4.2 check 4; §7 attack 2.

---

### EFF.T1.19  [lemma]

**CANONICAL STATEMENT:**

> \[
> \boxed{\frac{n(k)}{\varpi^k}=
> \left(\frac{x^{e_1}}{\pi^h}\right)^{-q(k)}.}
> \tag{C5-monomial-ratio}
> \]

> \[
> \boxed{q(a+b)=q(a)+q(b)+\operatorname{wrap}(a,b).}
> \tag{C5-carry}
> \]

**CONDITIONALITY:** Level-one normalizers; `q(k)=(i_0k-i(k))/e_1`.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Exponent subtraction gives the monomial ratio. For carry, multiply the difference by `e_1` and use `i(a)+i(b)-i(a+b)=e_1 wrap(a,b)`.

**RESOLUTION TRACE:** Base C5 and proof; R2 adds the monomial-ratio corollary.

**TEETH:** A2 consumption regression; §4.2 check 4 guards the `-q(k)` sign.

---

### EFF.T1.20  [lemma]

**CANONICAL STATEMENT:** [ASSEMBLED — effective C6 after R2-3, R7-2, R11-5]

Fix a residue section `σ:F_Q→\widehat O`, `res(σ(a))=a`, `σ(0)=0`. For `M>D'h`, write `λ=\sum_{r=0}^{f_1-1}λ_rη^r` and define

> \[
> \boxed{L_M(\lambda)=\sum_{r=0}^{f_1-1}
> \widetilde{\lambda_r}x^{i(M)+e_1r}\pi^{a-rh}.}
> \tag{C6-lift}
> \]

Then `L_M(λ)∈\widehat O[x]`, `deg L_M(λ)<D'`; for `λ≠0`, `dv_1(L_M(λ))=M`; and

> \[
> \boxed{\operatorname{res}\!\left(
> \frac{L_M(\lambda)(\theta)}{n(M)(\theta)}\right)=\iota_\theta(\lambda).}
> \tag{C6-residue}
> \]

For `λ≠0`:

> \[
> \boxed{L_M(\lambda)\text{ is an }x\text{-free monomial}
> \iff i(M)=0\text{ and }\lambda\in\mathbf F_Q.}
> \tag{C6-x-free}
> \]

**CONDITIONALITY:** `M>D'h`; compatible `θ,ι_θ`; exact height only for `λ≠0`; `L_M(0)=0` has empty support and valuation `+∞`.

**DERIVATION:** [ASSEMBLED] `i+e_1r≤D'-1` and `a-rh≥0` prove degree and integrality. Nonzero coefficient representatives are units, so every present term has height `M`; injectivity of `ι_θ` prevents height-`M` cancellation. Distinct nonnegative `x` exponents prove the x-free equivalence.

**RESOLUTION TRACE:** Base C6/proof; R2-3 types evaluation; R7-2 fixes the residue section and rewrites the proof; R11-5 sets `dv=dv_1`; R13-4 resolves the general lift-contract boundary.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-LIFT` — grep-verified count **9**.

**TEETH:** §4.2 checks 1, 7, and 10.

---

### EFF.T1.21  [hypothesis]

**CANONICAL STATEMENT:** [ASSEMBLED — sole live clearance form after R2-4/R13-3/Rider 3]

> “The exact-lift theorem above contains no definition of \(\Phi'\), its monomial valuations, or the outer polygon side. Consequently it proves no clearance estimate by itself.”

> “At the composed GENHN application, clearance may be used only after citing:
> \[
> \mathrm{(H\!-\!GENHN\!-\!CLEAR)}:
> \quad
> r=f_2-t,\qquad M=ru_2,\qquad u_2>e_2D'h,
> \]
> that supplier proves that every product of a monomial of
> \[
> L_{ru_2}\!\bigl(c_t\eta^{W(t)}\bigr)
> \]
> with a monomial of \(\Phi'^{e_2t}\) clears the outer side by at least
> \[
> \frac{r(u_2-e_2D'h)}{e_1}>0,
> \]
> and that collection and \(\Phi'\)-carry can only cancel terms or move them upward.”

**CONDITIONALITY:** Entirely an external GENHN supplier interface, not a T1 consequence.

**DERIVATION:** [ASSEMBLED — resolved effective proof] None internal: “Any subsequent outer-side clearance assertion is an invocation of \(\mathrm{(H\!-!GENHN\!-!CLEAR)}\); it is not derived in T1.”

**RESOLUTION TRACE:** R2-4 replaces the base clearance claim; R13-3 extends the replacement to the conditional lead-in; Rider 3 repairs only the enumeration.

**TEETH:** §7 attacks 3 and 8.

---

### EFF.T1.22  [table]

**CANONICAL STATEMENT:** [TABLE] [ASSEMBLED — effective C7 table after r2, r8, r10, r11]

| Package field | T1 datum available to that field |
|---|---|
| \(M0\), division chains | Common tower and canonical division-chain anchor; no new identity is proved here. |
| \(M1\) | The unconditional value-zero ratio and level-two letter formula in (C1); arbitrary-depth letter monomiality only under \(\mathrm{(H\!-\!JA\!-\!CONJ)}_i\). |
| \(M2\) | The dictionary and canonical read in (C3), plus (C4-origin); support transport only under \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\). The graded-read bundle consumed by the canonical read and its factor-pattern transport is, in full: (C3-ladder-multiplicativity), (C3-slot-grade), (C3-graded-scalar-covariance), (C3-zero-read), (C3-ladder-nonvanishing), and (C3-read-codomain). Corrected-key coefficients additionally use (C3-lift-coefficient-space). At depth \(i\ge3\), the scalars \(\vartheta_{i,s}\), their inverses \(\Theta_i(t)\), and the corrected digits \(c_t\vartheta_{i,f_{i+1}-t}\) are \(K_i\)-scalars only under \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) \((i\ge3)\). |
| \(M3\) | The cocycle/telescope (C2) and canonical twist in (C3), only on the scored stratum. At depth \(i\ge3\), the \(K_i^\times\)-valued telescope is available only under \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) \((i\ge3)\). |
| \(M4\) | The exact-height formulas (C5)–(C6), at W2-C3’s accepted fence; polygon clearance only under \(\mathrm{(H\!-\!GENHN\!-\!CLEAR)}\). |

**CONDITIONALITY:** Each row carries exactly the fences displayed in that row; the table does not merge field types.

**DERIVATION:** [ASSEMBLED — resolved effective proof] The table is an interface declaration. Its entries are the dependency projection of EFF.T1.05–.21; R10/R11 prove completeness by adding the previously omitted depth and read fences.

**RESOLUTION TRACE:** Base C7 table; r2 replaces M1/M2/M4; r8 extends M2; r10 replaces M2/M3; r11 gives the final M2 row.

XREF: `lean/notes/openmath/WELDMASTER_2026-08-08.md:WELD-M-PKG` — grep-verified count **5**.

XREF: `lean/notes/openmath/WELDMASTER_2026-08-08.md:W2-C3` — grep-verified count **8**.

**TEETH:** §4.2 check 6; §7 attack 4.

---

### EFF.T1.23  [fence]

**CANONICAL STATEMENT:**

> \[
> \boxed{\begin{gathered}
> \text{T1 organizes five named fields around one tower cocycle;}\\
> \text{it proves no cross-face coherence theorem.}
> \end{gathered}}
> \tag{C7-scope}
> \]

> “It also proves no uniqueness of the gauge and makes no classification of the fiber of gauges having a fixed coboundary.”

**CONDITIONALITY:** Scope fence, unconditional.

**DERIVATION:** [ASSEMBLED — effective §2.7] WELD-M-PKG is constructed field by field; none of C1–C6 supplies a single heterogeneous map, a compatibility square, or uniqueness. Therefore only the organization claim follows.

**RESOLUTION TRACE:** Base C7 and proof; R3-3 removes the unsupported character-torsor classification.

**TEETH:** §4.2 check 6; §7 attack 4.

---

### EFF.T1.24  [absorption-record]

**CANONICAL STATEMENT:** [ASSEMBLED — effective §3 protocol after R13-1 and Rider 2]

> “Under the revised blueprint’s non-row-annex provision, an A-row absorbs only the closed sub-display quoted in that row. A theorem or lemma identifier is a span locator; it does not mean that T1 implies the entire containing statement.”

> “Each row must have the form
> \[
> \text{specified T1 clause}\Longrightarrow\text{quoted pinned subclaim}.
> \]”

> “If the containing result needs geometry, routing, membership, extraction, or a site theorem not supplied by T1, the row is labeled ‘supplies the gauge input to,’ and the residual obligation is named explicitly.”

For A1 only:

> “‘Verbatim’ means that, after replacing local names by the displayed T1 names, the certified local mathematical display is an immediate specialization with no added hypothesis or conclusion.”

**CONDITIONALITY:** This is the mathematical absorption/supply protocol. It does not assert that downstream dated appends have landed.

**DERIVATION:** [ASSEMBLED — resolved effective proof] R13-1 retires the contradictory base table and declares the A1 rows plus A2–A7 blocks to be the sole authoritative status list; Rider 2 restores the `Verbatim` definition at its only live use.

**RESOLUTION TRACE:** R2 replacement §3; R13-1(a,b,d); Rider 2.

**TEETH:** §7 attack 8, the consumption sweep.

---

### EFF.T1.25  [table]

**CANONICAL STATEMENT:** [TABLE] [ASSEMBLED — relocated A1 table with R2-4 amendment]

| Annex | Local site | T1 conclusion | Mode and specialization |
|---|---|---|---|
| A1 GENHN | GENHN-LIFT | C6 | **Verbatim** on \(M>D'h\): same component formula, integrality, degree, exact height, and residue. |
| A1 GENHN | Corrected T(b)\('\) coefficient | C2, C3, C6 | **Verbatim** with \(M=(f_2-t)u_2\): \(L_M(c_t\eta^{W(t)})\). T1 absorbs the corrected coefficient and its exact-lift properties. The clearance sentence is retained only by the explicit citation \(\mathrm{(H\!-\!GENHN\!-\!CLEAR)}\), not as a T1 consequence. |

**CONDITIONALITY:** The first row is on `M>D'h`. The second also retains the external clearance fence.

**DERIVATION:** [ASSEMBLED — resolved effective proof] EFF.T1.20 proves the first row. EFF.T1.10, .13, and .20 prove the corrected coefficient; EFF.T1.21 separates the clearance supplier.

**RESOLUTION TRACE:** Base A1 rows; r2 leaves A1 passed; R2-4 narrows clearance; R13-1 relocates both rows; Rider 2 restores `Verbatim`.

XREF: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md:GENHN-LIFT` — grep-verified count **9**.

**TEETH:** §4.2 checks 1, 2, and 7; §7 attack 8.

---

### EFF.T1.26  [absorption-record]

**CANONICAL STATEMENT:** [ASSEMBLED — effective A2 after R5-2, R6-2, R11-4, R12-4]

The pinned HETOW displays are:

> \[
> \boxed{
> \frac{\widehat n_2(k)}{n_2(k)}
> =
> \frac{\widehat n(m(k))}{\varpi^{m(k)}}
> =
> \left(\frac{x^{e_1}}{\pi^h}\right)^{-Q(m(k))}
> }
> \]

> \[
> \boxed{
> \operatorname{res}\!\left(
> \frac{\widehat n_2(k)(\xi)}{n_2(k)(\xi)}
> \right)
> =
> \eta_\xi^{-Q(m(k))}
> =
> \iota_\xi\!\left(\eta^{-Q(m(k))}\right).
> }
> \]

With T1's non-pinned symbol \(c_2^{\mathrm{HET}}\) for HETOW's pinned \(w_2\), the third pin is

> \[
> \boxed{
> \frac{\tau(k)\tau(k')}{\tau(k+k')}
> =
> \eta^{
> \operatorname{wrap}_1(m(k),m(k'))
> +
> w_2\left(
> Q(u_2)+
> \operatorname{wrap}_1(m(k)+m(k'),u_2)
> \right)
> }.
> }
> \]

T1's effective consumption check is:

> \[
> \boxed{\mathrm{(H\!-!HETOW\!-!LOCAL)}
> +\text{ T1 (C5-monomial-ratio) + (C5-carry)}
> \Longrightarrow\text{ the three pinned HETOW displays}.}
> \]

The supplier interface includes

> \[
> 0\le s(a)<e_2,
> \qquad
> c_2^{\mathrm{HET}}=
> \left\lfloor\frac{s(k)+s(k')}{e_2}\right\rfloor\in\{0,1\},
> \]

and the level-two bridge, the function `m`, and the identification of `τ`.

> “T1 does not absorb HETOW-4(c)–(d). The side-assembly brackets, telescoping coefficient identity, side-letter equality, routing transport, and common refinement polynomial remain HETOW/HE7 supplier conclusions.”

**CONDITIONALITY:** `(H-HETOW-LOCAL)` is external and essential; the linear carry formula is asserted only for the binary carry.

**DERIVATION:** [ASSEMBLED — resolved effective proof] The supplier bridge plus C5-monomial-ratio proves the ratio pins. Two applications of C5-carry in the two binary cases prove the exponent in the `τ` ratio. T1 supplies only the level-one algebra.

**RESOLUTION TRACE:** R2 A2 block; R5-2 installs the supplier interface and proof; R6-2 adds binary carry; R11-4 renames it; R12-4 prevents duplicated substitution text.

XREF: `lean/notes/openmath/HETOW_RECON_2026-08-09.md:LEMMA HETOW-4` — grep-verified count **3**.

**TEETH:** §7 attacks 5 and 8.

---

### EFF.T1.27  [absorption-record]

**CANONICAL STATEMENT:** [ASSEMBLED — effective A3 after R6-1/R9-3]

> \[
> M_t=(f_2-t)u_2>D'h,
> \qquad \Gamma_t=c_t\eta^{W(t)},
> \qquad \widehat k_t=L_{M_t}(\Gamma_t).
> \]

> \[
> \boxed{\begin{aligned}
> c_t\ne0&\Longrightarrow dv_1(\widehat k_t)=M_t,\\
> c_t=0&\Longrightarrow \Gamma_t=0,\ \widehat k_t=0,\ dv_1(\widehat k_t)=+\infty,
> \end{aligned}}
> \]

and in both branches

> \[
> \boxed{c_t^{\mathrm{mult}}=\Gamma_t\eta^{-W(t)}=c_t.}
> \]

> “T1 **supplies the gauge input to** LEMMA GENTOW-1.”

**CONDITIONALITY:** Level one; live lift domain; exact height only for `c_t≠0`.

**DERIVATION:** [ASSEMBLED — resolved effective proof] C2-level-1 plus C3-dictionary plus the zero-lift and C6 contracts.

**RESOLUTION TRACE:** R2 A3; R6-1 supplies zero branch; R9-3 declares the read statement assembled and corrects the local `Γ_t` naming.

XREF: `lean/notes/openmath/GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-1` — grep-verified count **7**.

**TEETH:** §4.2 checks 1 and 2; §7 attacks 2, 3, and 8.

---

### EFF.T1.28  [absorption-record]

**CANONICAL STATEMENT:**

> \[
> M_t=(f_2-t)u_2>D'h,
> \qquad
> \widehat k_t=L_{M_t}(c_t\eta^{W(t)}),
> \]

and, for nonzero `λ`,

> \[
> \boxed{L_M(\lambda)\text{ is an }x\text{-free monomial}
> \iff i(M)=0\text{ and }\lambda\in\mathbf F_Q.}
> \]

> “T1 **supplies the corrected-key and \(x\)-free inputs to** THEOREM GENTOW-3.”

**CONDITIONALITY:** Live lift domain; nonzero digit for the x-free equivalence.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Direct specialization of C3-level-1-key and C6-x-free.

**RESOLUTION TRACE:** R2 A4 block; no later formula change.

XREF: `lean/notes/openmath/GENTOW3_PROOF_2026-08-09.md:THEOREM GENTOW-3` — grep-verified count **10**.

**TEETH:** §4.2 check 1; §7 attacks 3 and 8.

---

### EFF.T1.29  [absorption-record]

**CANONICAL STATEMENT:** [ASSEMBLED — effective A5]

> \[
> \boxed{\Phi_2=\Phi'^{e_2f_2}-\sum_{t<f_2}
> L_{(f_2-t)u_2}(c_t\eta^{W(t)})\Phi'^{e_2t}}
> \]

on `(f_2-t)u_2>D'h`, and separately

> \[
> \boxed{z^{t_{\mathrm{Def}}}=z^\nu\varepsilon(\beta).}
> \]

> “Any support comparison additionally cites \(\mathrm{(H\!-!JA\!-!RES\!-!CONJ)}\).”

> “T1 **supplies the gauge input to** GENTOW-4.1(c)/S3.”

**CONDITIONALITY:** Live lift domain; support comparison requires its external JA supplier.

**DERIVATION:** [ASSEMBLED — resolved effective proof] C2-level-1, C3-level-1-key, and C6 prove the key display; C4-origin proves the attained-origin equation.

**RESOLUTION TRACE:** R2 A5; R13-1 withdraws the former BOX-3 and S4 absorption rows rather than restoring them here.

XREF: `lean/notes/openmath/GENTOW4_PROOF_2026-08-09.md:LEMMA GENTOW-4.1` — grep-verified count **4**.

**TEETH:** §4.2 checks 1–3; §7 attacks 1, 3, 6, and 8.

---

### EFF.T1.30  [absorption-record]

**CANONICAL STATEMENT:** [ASSEMBLED — effective A6 after R6-1/R9-1]

The scalar-read pin is HE6 F-1 and consists of EFF.T1.18. The lift pin is GENTOW6 S6.1:

> \[
> L_M(\lambda)=\sum_{r=0}^{f_1-1}
> \widetilde{\lambda_r}x^{i(M)+e_1r}\pi^{a-rh},
> \qquad M>D'h,
> \]

with

> \[
> \boxed{\operatorname{Supp}_xL_M(\lambda)=
> \{i(M)+e_1r:0\le r<f_1,\ \lambda_r\ne0\}.}
> \]

Every present summand has height `M`; `λ≠0` gives lift height `M`, while `λ=0` gives empty support and valuation `+∞`.

> “T1 **supplies the normalized scalar-read and exact-lift inputs to** THEOREM GENTOW-6.3.”

**CONDITIONALITY:** Scalar reads require the HE6 embedding hypotheses; lift is on `M>D'h`; exact height only for nonzero `λ`.

**DERIVATION:** [ASSEMBLED — resolved effective proof] C5-gamma and its two reads prove the scalar pin; C6 proves the lift, support, and zero/nonzero split.

**RESOLUTION TRACE:** R2 A6; R6-1 adds support/zero branch; R9-1 reattributes scalar provenance to HE6 and keeps GENTOW6 only for the lift/consumer.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:F-1 — normalized slot coefficients in LEMMA HE6-0″` — grep-verified count **1**.

XREF: `lean/notes/openmath/GENTOW6_PROOF_2026-08-09.md:S6.1` — grep-verified count **15**.

XREF: `lean/notes/openmath/GENTOW6_PROOF_2026-08-09.md:THEOREM GENTOW-6.3` — grep-verified count **10**.

**TEETH:** §4.2 checks 1, 4, 7, and 10; §7 attacks 2, 3, and 8.

---

### EFF.T1.31  [absorption-record]

**CANONICAL STATEMENT:** [ASSEMBLED — effective A7 after r8/r9/r11/r13]

**SPAN PIN 1:**

> \[
> \boxed{z_2=\eta_2z_1^{-\lfloor\ell_1u_2/e_1\rfloor}.}
> \]

**SPAN PIN 2:**

> \[
> \boxed{\psi_3^{(w)}(y)=w^{f_3}\psi_3(y/w).}
> \]

The pinned consequences are only monicity after renormalization and preservation of degree, irreducibility, and nonzero constant term for the pinned monic irreducible target. General factor-pattern preservation is T1's own gated conclusion, not part of that pin.

> “T1 only **supplies the gauge algebra to** the preceding B-law display.”

The accepted supplier's per-grade conclusion is

> \[
> u(\beta_t)=\Theta(t)w^{f_3-t}.
> \]

T1 may cancel `Γ_t=c_t\vartheta` against `Θ=\vartheta^{-1}`, “but it does not prove the supplier identity itself. Thus the B-law is no longer labeled ‘absorbed verbatim.’”

**CONDITIONALITY:** Full sitewise read bundle, including codomain and nonvanishing; bounded coefficient space; depth fence where applicable.

**DERIVATION:** [ASSEMBLED — resolved effective proof] C1-base-letter+C1-level-2 prove pin 1. C3-three-reads and its unit substitution prove pin 2. The B-law supplier identity is external; only the slotwise cancellation is internal.

**RESOLUTION TRACE:** R2 A7; r5/r8/r11 progressively complete the supplier bundle; R9-4 narrows pin 2; R13-6 preserves and re-anchors the supplier display; Rider 4 restores the unchanged opener in the block order.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.1` — grep-verified count **42**.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B′` — grep-verified count **8**.

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` — grep-verified count **10**.

**TEETH:** §4.2 checks 5, 7–9; inverse-orientation tooth; §7 attacks 5, 7, and 8.

---

### EFF.T1.32  [fence]

**CANONICAL STATEMENT:** [ASSEMBLED — effective supporting context]

> “GENTOW5’s definitions of \(w\) and \(\psi^{(w)}\) are absorbed verbatim; its dictionary is absorbed with the \(\Gamma/\gamma_k\) notation separation.”

> “GRTJA’s JA-EPS-CORR is absorbed verbatim in (C4), including the exact root-of-unity criterion \(z^\nu=1\).”

> “WELD-M-PKG is not absorbed as a stronger theorem: (C7) is only an interface map and scope fence.”

> “HE6-0″ is absorbed with adapted names but with its corrected normalized coefficient formula verbatim.”

> “The B-law rows” — read by Rider 1 as the effective A7 B-law block — consume the full read bundle; at `i=2` GENTOW2 supplies it, while at `i≥3` an explicit level-general supplier is required.

**CONDITIONALITY:** All named supplier perimeters remain in force.

**DERIVATION:** [ASSEMBLED — resolved effective proof] This is a dependency and non-strengthening record derived from EFF.T1.15, .18, .23, and .31.

**RESOLUTION TRACE:** Base supporting context preserved by R13-1; effective paragraph from R8-2 as amended by R11-1; Rider 1 fixes its referent.

XREF: `lean/notes/openmath/GENTOW5_WI_2026-08-10.md:[GENTOW5-W(i)]` — grep-verified count **9**.

XREF: `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md:JA-EPS-CORR` — grep-verified count **3**.

XREF: `lean/notes/openmath/WELDMASTER_2026-08-08.md:WELD-M-PKG` — grep-verified count **5**.

XREF: `lean/notes/openmath/HE6_PROOF_2026-08-08.md:LEMMA HE6-0″` — grep-verified count **6**.

**TEETH:** §7 attacks 2, 4, 5, 6, and 8.

---

### EFF.T1.33  [table]

**CANONICAL STATEMENT:** [TABLE] — inherited exact frames

| Frame | Essential axes |
|---|---|
| X | \(p=3\), \(e_1=2,f_1=1,h=1,\eta=2,u_2=3\); corrected versus naive p-adic split. |
| FR-G | The GENTOW4 partial-side witness and separator regression. |
| F4-JOINT | \(K_1=\mathbf F_4\), \(e_1=2,f_1=2,h=1,\eta=w=\omega\), live wrap, quadratic and \(\mu=3\) legs. |
| LP/LD | Recorded GENTOW2 letter and inverse-cocycle geography. |

**CONDITIONALITY:** “The 2026-08-10 sealed battery remains historical evidence, not a certification of this revised text.”

**DERIVATION:** [ASSEMBLED — resolved effective proof] This is a recorded battery-frame table, not a mathematical derivation. Acceptance expressly rests on the later 10/10 re-run, not this inherited run.

**RESOLUTION TRACE:** Base §4.1; acceptance preserves it as inherited evidence only.

**TEETH:** Supports the planted gauge, sign, indexing, and orientation mutations; not itself a passed acceptance leg.

---

### EFF.T1.34  [battery-row]

**CANONICAL STATEMENT:** [ASSEMBLED — F4-JOINT predictions]

> \[
> R_{\mathrm{corr}}=y^2+y+\omega,\qquad
> R_{\mathrm{naive}}=y^2+y+1,\qquad
> \psi^{(w)}=y^2+\omega y+1.
> \]

At its `μ=3` leg:

> \[
> (\vartheta_0,\vartheta_1,\vartheta_2,\vartheta_3)=(1,1,\omega,\omega),
> \]
> \[
> (\Gamma_2,\Gamma_1,\Gamma_0)=(1,\omega,\omega),
> \qquad
> (u(\beta_2),u(\beta_1),u(\beta_0))=(\omega,\omega,\omega^2),
> \]
> and the full canonical coefficient vector is `(ω,ω²,1)`, giving `(y+ω)^3`.

**CONDITIONALITY:** Finite graded-carrier model, not an explicit p-adic realization.

**DERIVATION:** [ASSEMBLED — resolved effective proof] The values are the note's corrected inherited predictions; the full orientation row applies `Θ=\vartheta^{-1}` to every slot.

**RESOLUTION TRACE:** Base §4.1; later records do not change the values.

**TEETH:** Positive wrap, gauge-naive, wrong-sign, misindexed telescope, inverse orientation.

---

### EFF.T1.35  [battery-row]

**CANONICAL STATEMENT:** “**GENHN-LIFT boundary.** Check integrality, degree, height, and residue for several \(M>D'h\), including \(f_1\ge2\),” and include the low-height counterexample `(e_1,f_1,h,M)=(1,2,1,0)`.

**CONDITIONALITY:** Executable regression instruction.

**DERIVATION:** [ASSEMBLED — resolved effective proof] It directly exercises EFF.T1.20's four conclusions and its strict live-domain fence.

**RESOLUTION TRACE:** Base §4.2 check 1; accepted at the later 10/10 re-run.

**TEETH:** Guards EFF.T1.01, .13, .20, .25, .27–.30.

---

### EFF.T1.36  [battery-row]

**CANONICAL STATEMENT:** “**Positive-wrap sign.** Re-run the corrected/naive and wrong-sign teeth. Exact coefficient equality, not merely factor pattern, must be scored.”

**CONDITIONALITY:** Executable regression instruction.

**DERIVATION:** [ASSEMBLED — resolved effective proof] EFF.T1.10 derives the positive floor exponent; EFF.T1.11–.13 use it in the corrected coefficient.

**RESOLUTION TRACE:** Base §4.2 check 2; accepted at the 10/10 re-run.

**TEETH:** Guards EFF.T1.07, .10–.13, .25, .27, .29.

---

### EFF.T1.37  [battery-row]

**CANONICAL STATEMENT:** “**JA origin.** For \(\nu=0\), verify raw and canonical factors agree. For \(\nu>0\) and \(z^\nu\ne1\), verify the raw equality fails by exactly \(z^\nu\). Add a root-of-unity case with \(\nu>0\) and \(z^\nu=1\). Score the support and degree translation by \(\nu\).”

**CONDITIONALITY:** Support/degree scoring additionally requires `(H-JA-RES-CONJ)`.

**DERIVATION:** [ASSEMBLED — resolved effective proof] EFF.T1.16 gives the exact factor; EFF.T1.17 gives support only under the supplier comparison.

**RESOLUTION TRACE:** Base §4.2 check 3; accepted at the 10/10 re-run.

**TEETH:** Guards EFF.T1.16–.17 and .29.

---

### EFF.T1.38  [battery-row]

**CANONICAL STATEMENT:** “**HE6 coefficient normalization.** Use a tying coefficient of positive valuation for which \(\operatorname{res}(a_j)=0\) but the normalized coefficient residue is nonzero. Score (C5-normalizer-read), (C5-varpi-read), and the \(-q(k)\) sign.”

**CONDITIONALITY:** Executable regression instruction.

**DERIVATION:** [ASSEMBLED — resolved effective proof] EFF.T1.18 shows why the bare residue fails and EFF.T1.19 supplies the negative exponent.

**RESOLUTION TRACE:** Base §4.2 check 4; accepted at the 10/10 re-run.

**TEETH:** Guards EFF.T1.18–.19, .26, and .30.

---

### EFF.T1.39  [battery-row]

**CANONICAL STATEMENT:** “**Full orientation tooth.** With \(\Theta\) intentionally replaced by \(\vartheta\), score all three entries of the canonical \(\mu=3\) vector, not only the \(s=2\) B-unit.”

**CONDITIONALITY:** Executable mutant.

**DERIVATION:** [ASSEMBLED — resolved effective proof] EFF.T1.14 proves `Θ=\vartheta^{-1}`; EFF.T1.34 supplies all three expected entries.

**RESOLUTION TRACE:** Base §4.2 check 5; accepted and explicitly reported firing.

**TEETH:** Guards EFF.T1.03, .09, .11, .14–.15, .31, .34.

---

### EFF.T1.40  [battery-row]

**CANONICAL STATEMENT:** [ASSEMBLED — effective check 6 after R4-3]

> “**Weld scope lint.** Build the lint target from assertion-bearing T1 prose after excluding this numbered check, quoted rejected formulations, and matches lying within the scope of an explicit negation.”

Fail on affirmative “one transport map,” “unique gauge,” or unnamed cross-field compatibility; independently confirm the `M3` scored-stratum and `M4` W2-C3 fences.

**CONDITIONALITY:** The check's own specification, quotations, and explicit negations are nonmatches.

**DERIVATION:** [ASSEMBLED — resolved effective proof] EFF.T1.22–.23 establish exactly the negative assertions being linted.

**RESOLUTION TRACE:** Base check 6 replaced by R4-3; accepted in self-excluding form.

**TEETH:** Guards EFF.T1.22–.24 and .32.

---

### EFF.T1.41  [battery-row]

**CANONICAL STATEMENT:** “**General coefficient-space bound.** For every corrected-key coefficient, score \(\deg\widehat k_t<\deg\Phi_i\),” reject a higher-degree/higher-value perturbation that still passes height and residue, and score strict degree below the leading term.

**CONDITIONALITY:** Executable regression instruction.

**DERIVATION:** [ASSEMBLED — resolved effective proof] EFF.T1.12 proves the composed polynomial shape from the independent coefficient-space contract.

**RESOLUTION TRACE:** R8 check 7 appended to §4.2; first scored in the accepted re-run.

**TEETH:** Guards EFF.T1.02, .12, .20, .30–.31.

---

### EFF.T1.42  [battery-row]

**CANONICAL STATEMENT:** “**Ladder nonvanishing.** Instantiate a mock residual read that is zero on every positive-grade homogeneous component while satisfying” the other read axioms; reject it precisely by `C3-ladder-nonvanishing` and reject `y/w_i` without that clause.

**CONDITIONALITY:** Executable countermodel.

**DERIVATION:** [ASSEMBLED — resolved effective proof] The mock shows independence of nonvanishing; EFF.T1.15 requires a unit for polynomial substitution.

**RESOLUTION TRACE:** R8 check 8 appended; first scored in the accepted re-run.

**TEETH:** Guards EFF.T1.03, .09, .12, .15, .31.

---

### EFF.T1.43  [battery-row]

**CANONICAL STATEMENT:** “**Read codomain.** Instantiate the initial-form mock read \(g\mapsto\operatorname{in}(g)\in\operatorname{gr}(\mu_i)\). Confirm that it passes check 8 … and is rejected precisely by (C3-read-codomain).”

**CONDITIONALITY:** Executable countermodel.

**DERIVATION:** [ASSEMBLED — resolved effective proof] The initial-form read supplies a nonzero homogeneous output but not a `K_i` scalar, separating codomain from nonvanishing.

**RESOLUTION TRACE:** R11 check 9 appended; first scored in the accepted re-run.

**TEETH:** Guards EFF.T1.03, .09, .12, .15, .31.

---

### EFF.T1.44  [battery-row]

**CANONICAL STATEMENT:** [ASSEMBLED — effective check 10 after R13-8 and Riders 5–7]

> “**Grade-data value group.** Instantiate a witness tower with \(e_{i+1}\nmid u_{i+1}\) … and confirm that \(dv_i(\Phi_i)=u_{i+1}/e_{i+1}\notin\mathbb Z\) while \(dv_i(\Phi_i^{e_{i+1}})=u_{i+1}\in\mathbb Z\).”

Score only consumed values. The instruction excludes its own specification, value-group witnesses, quotations/records, and the zero argument. `dv_i(0)=+∞` passes under class (iii), not the nonzero-argument integrality clause.

**CONDITIONALITY:** The first fail clause is restricted to consumed nonzero arguments; literal exclusions and the consumption criterion now score the same set.

**DERIVATION:** [ASSEMBLED — resolved effective proof] EFF.T1.02 derives the actual value group and four consumed classes. Rider 6 handles zero; Rider 7 makes the exclusion list exhaustive.

**RESOLUTION TRACE:** R13-8 check 10; Rider 5 self-exclusion; Rider 6 zero scope; Rider 7 quotation/record scope. The accepted battery reports this check passing.

**TEETH:** Guards EFF.T1.02, .04, .12, .20, .30.

---

### EFF.T1.45  [battery-row]

**CANONICAL STATEMENT:**

> “The four original planted teeth remain mandatory:
> - gauge-naive;
> - wrong-sign;
> - misindexed telescope; and
> - inverse-orientation confusion.
>
> Every tooth must fire.”

**CONDITIONALITY:** Acceptance requires all four mutants to fire.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Each mutant negates a proved orientation or indexing clause: corrected versus naive in C3, positive sign in C2, recursion indices in C2, or `Θ=\vartheta^{-1}` in C3.

**RESOLUTION TRACE:** Base §4.2; acceptance reports all four firing.

**TEETH:** Guards EFF.T1.07–.15, .27, .29, .31, .34, .36, .39.

---

### EFF.T1.46  [fence]

**CANONICAL STATEMENT:** [ASSEMBLED — verbatim effective honesty-ledger items 1–22]

> 1. At arbitrary depth, T1 proves only the value-zero ratio in (C1-general). A preceding-letter monomial description requires the named supplier hypothesis \(\mathrm{(H\!-\!JA\!-\!CONJ)}_i\). The level-two formula is proved directly and is unconditional.

> 2. The B-law is conditional on the sitewise graded read facts (C3-ladder-multiplicativity), (C3-slot-grade), and (C3-graded-scalar-covariance). For a zero coherent digit, the displayed homogeneous component is zero and its read is governed separately by (C3-zero-read). The assertion \(w_i\in K_i^\times\), and hence the unit-rescaling and factor-pattern argument, additionally require BOTH independent site obligations (C3-read-codomain) (placing \(w_i\in K_i\)) and (C3-ladder-nonvanishing) (making it nonzero); neither alone yields a unit. T1 proves none of these facts for all homogeneous initial forms.

> 3. \(\vartheta_{i,s}\) is the building/dictionary orientation, while
> \[
> \Theta_i(t)=\vartheta_{i,f-t}^{-1}
> \]
> is the B-law orientation.

> 4. The canonical residual is
> \[
> \psi^{(w)}=w^f\psi(y/w).
> \]
> This preserves factor patterns, not literal coefficients. Both the displayed identity and its factor-pattern conclusion are asserted only at sites carrying BOTH independent site obligations (C3-read-codomain) (placing \(w_i\in K_i\), so that \(y\mapsto y/w_i\) is defined on \(K_i[y]\)) and (C3-ladder-nonvanishing) (making \(w_i\ne0\), so that division by \(w_i\) is available); neither alone yields a unit, and without both neither the automorphism nor the unit-substitution argument is asserted (§2.3, R8-2 as amended by R11-1). Preservation of irreducible-factor degrees and multiplicities is T1's own factor-pattern conclusion at such a site, NOT part of the pinned GENTOW2-B span (R9-4).

> 5. The canonical minimal-grid factor and raw print factor differ by \(z^\nu\). The exponent identity (C4-origin) does not imply a comparison of whole residual polynomials. The support and degree formulas require \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\).

> 6. The full integral level-one lift is proved here on \(M>D'h\). No universal full \(K_1\)-slot is claimed at lower heights.

> 7. The HE6 digit is \(\gamma_k(A)\) with coefficient normalizers. It is different from the coherent corrected-key digit \(\Gamma_t\).

> 8. Under the stated carrier, \(\eta=1\) forces \(K_1=\mathbf F_Q\) and \(f_1=1\); these are not independent specialization axes. The condition \(\eta=1\) removes the level-one wrap correction, but it does not by itself make arbitrary digits \(x\)-free, because (C6-x-free) still requires \(i(M)=0\).

> 9. Gauge-invariant residual factor patterns become splitting types only through the surrounding tower correctness theorem.

> 10. T1 does not prove note-specific budgets, floors, fullness counts, separator inequalities, polygon geometry, or extraction and attainment claims. In particular, outer-side clearance is available only through the named supplier input \(\mathrm{(H\!-\!GENHN\!-\!CLEAR)}\).

> 11. WELD-M-PKG is five heterogeneously typed fields assembled into one named record. T1 proves neither a single cross-face map nor compatibility beyond the package’s displayed anchors.

> 12. Gauge uniqueness is not asserted. T1 defines no gauge space, coefficient action, or character group and therefore asserts no character-torsor classification of fixed-coboundary gauges.

> 13. F4-JOINT remains a finite graded-carrier model, not an explicit p-adic realization. Its formal sigma values are not PARI measurements.

> 14. The explicit joint p-adic realization remains open and is not required for the algebraic lemma.

> 15. The general residue letters and the common-height composed-key calculation use the explicit stage identity
> \[
> dv_i\!\left(\Phi_i^{e_{i+1}}\right)=u_{i+1}.
> \]
> Exact lift height is asserted only for nonzero digits. A zero digit is lifted to zero, has residue zero after normalization, and contributes no finite-height key term.

> 16. Exact lift height is asserted only for a nonzero digit. In particular, a corrected-key coefficient with \(c_t=0\) is the zero lift, has valuation \(+\infty\), and contributes an empty support rather than a finite-height key term.

> 17. The pinned A2 HETOW carry formula uses the supplier range
> \[
> 0\le s(a)<e_2,
> \]
> which makes T1’s carry
> \[
> c_2^{\mathrm{HET}}=\left\lfloor\frac{s(k)+s(k')}{e_2}\right\rfloor
> \]
> binary. T1 does not assert the displayed linear-in-\(c_2^{\mathrm{HET}}\) formula for a nonbinary carry. SYMBOL NOTE: the accepted `HETOW` and the pinned displays write \(w_2\) for this carry; T1 writes \(c_2^{\mathrm{HET}}\) to avoid collision with the carrier’s ladder unit \(w_i\) (whose \(i=2\) instance \(w_2\in K_2^\times\) is unrelated). Precedent: the R9-3 \(\gamma_t/\Gamma_t\) note.

> 18. Exact height and normalized residue do not determine an admissible corrected-key representative. Every coefficient used in (C3-key) must also satisfy
> \[
> \deg\widehat k_t<\deg\Phi_i.
> \]
> Higher-degree, higher-value perturbations are excluded by the coefficient-space contract.

> 19. The displayed residual-read axioms do not imply that the base ladder read is a nonzero \(K_i\)-scalar. The status \(w_i\in K_i^\times\) is asserted only at sites carrying BOTH (C3-read-codomain) and (C3-ladder-nonvanishing) — at \(i=2\) supplied by the accepted GENTOW2 package (S5.1 (R-FGMN) for the codomain, LEMMA GENTOW2-B\('\)/B\(''\) for nonvanishing), at \(i\ge3\) by an explicitly cited level-general analogue carrying both clauses.

> 20. The A6 scalar-read displays — the \(\gamma_k(A)\) definition and the \(n(k)\)/\(\varpi\)-reads — are HE6 F-1’s displays, transcribed; the accepted `GENTOW6` contains no \(\gamma_k(A)\) and no \(\varpi\)-read display. The locator `md5=05fc38817b8c75297267bb57089e898f` pins THEOREM GENTOW-6.3, the consumer. Every SPAN PIN md5 is a normalized one-line span at a declared commit, per the §3 convention paragraph.

> 21. \(\vartheta_{i,s}\in K_i^\times\) is proved at \(i\in\{1,2\}\) only. At \(i\ge3\), that membership — and with it the typing of (C3-corrected-lift), the formation of (C3-key), and the nonzero-digit common-height argument — is asserted only at sites carrying \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\).

> 22. The canonical residual read is scalar-valued only by the site obligation (C3-read-codomain); no displayed read axiom forces it — the initial-form read into \(\operatorname{gr}(\mu_i)\) is the standing counterexample (§4.2 check 9). \(w_i\in K_i^\times\) requires BOTH (C3-read-codomain) and (C3-ladder-nonvanishing). At \(i=2\) both are supplied by the accepted GENTOW2 package (S5.1 (R-FGMN) and LEMMA GENTOW2-B\('\)/B\(''\)); at \(i\ge3\) both ride the same named level-general residual-read supplier package, unproved here.

**CONDITIONALITY:** These are scope fences and standing conditionalities, not extra conclusions.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Each item restates the limiting clause or counterexample attached to EFF.T1.02–.23 and .26–.44. Items 2, 4, 19, and 22 use the independent mock reads; items 5 and 10 are exact supplier separations; items 13–14 are provenance/coverage fences.

**RESOLUTION TRACE:** Base §5 with item replacements in r1, r2, r3, r5, r7, r8, r11, r12, and r13, plus appended items 15–22. This is the effective 1–22 ledger.

**TEETH:** All §4.2 checks and all four planted mutants; see inverse table.

---

### EFF.T1.47  [changes-record]

**CANONICAL STATEMENT:** [TABLE] [ASSEMBLED — effective §6 record; status authority remains §3]

| Revision | Driver | Annex effect |
|---|---|---|
| Replaced the conditional old C4 lift by (C6) on the uniform live domain \(M>D'h\), including integrality, residue, degree, and clearance. | GENHN-LIFT and the later occupied-height tightening | A1 GENHN becomes verbatim; A4 GENTOW3 and A6 GENTOW6 are absorbed with the live-domain fence. |
| Made \(L_{(f_2-t)u_2}(c_t\eta^{W(t)})\) the level-one corrected coefficient, with positive wrap exponent. | GENHN-LIFT application and HETOW wrap correction | A1 and A2 are verbatim; A3, A5, and A6 specialize with notation adaptation. |
| Renamed coherent digits from \(\gamma_t\) to \(\Gamma_t\). | HE6’s corrected, reserved \(\gamma_k(A)\) | A3, A5, A6, and the GENTOW5 dictionary rows are notational adaptations; no formula changes. |
| Added the normalized coefficient formula (C5-gamma) and the \(\eta^{-q(k)}\) canonical-normalizer factor. | HE6 F-1 | A6’s scalar-reading site is materially adapted; the old bare-residue formula is rejected rather than absorbed. |
| Added (C4-origin) and the \(\nu\)-translated support/degree law. | JA-EPS-CORR and JA-MIN-CORR | A5 bridge consumption is adapted: tower \(\vartheta\)-cancellation survives, but raw print equality carries \(z^\nu\). |
| Stated raw print/canonical equality as iff \(z^\nu=1\), with \(\nu=0\) only a sufficient special case. | JA-EPS-CORR | Prevents a new false “iff \(\nu=0\)” strengthening. |
| Added the five-row package interface and boxed no-cross-face-coherence fence. | WELD-M-PKG | No local annex is strengthened. T1 organizes M0–M4 citations but does not absorb or reprove the package as one map. |
| Withdrew any gauge-uniqueness implication and made no classification of fixed-coboundary gauge fibers. | WELDMASTER C6 F-1/F-2 and T1P2 finding G3 | Scope correction across all annex consumers; formulas C1–C6 are unchanged. |
| Narrowed the residual-read carrier assumption to the ladder monomials consumed at B-law sites. | Earlier T1 G-2 plus WELD package-scoping discipline | A5/A7/GENTOW5 B-law rows remain supplier-dependent rather than globally assumed. |
| Corrected F4-JOINT \(\psi^{(w)}\) to \(y^2+\omega y+1\) in the draft body. | Sealed P-J2 diagnosis | A7 factor-pattern absorption remains verbatim; the exact-value defect is removed. |
| Required the orientation tooth to score the full three-slot vector. | Sealed instrument disclosure F-5 | Verification-only change; no annex statement changes. |
| Reclassified the sealed 2026-08-10 run as inherited evidence rather than certification of the revised statement. | Revision integrity | All seven annex consumptions must be rechecked against this text. |
| Defined \(z_1=\eta\), normalized \(\widehat n_i(0)=1\), and corrected the A5 residue-one specialization to record \(\eta=1\Rightarrow f_1=1\) under the carrier. | T1A hostile pass, findings G1–G3, 2026-08-12 r1 | Repairs the level-two letter formula and normalized cocycle endpoints; A5 is adapted rather than falsely marked verbatim. |
| Removed the unsupported arbitrary-depth unit reduction; made harness/print polynomial conjugation and GENHN clearance explicit supplier inputs; typed the modular-origin data; fixed the \(C6\) evaluation embedding; and re-scoped A2–A7 to closed gauge spans with named residual obligations. | T1P and T1CC2, 2026-08-12 r2 | Repairs 1 CRITICAL, 3 GAP, and 1 MINOR finding; prevents theorem-wide absorption from gauge-input rows. |
| Required \(dv_i(\pi_{i+1})=1\) at general depth; required \(A\ne0\) and a compatible C5 residue embedding; and removed the untyped character-torsor assertion. | T1P2, 2026-08-12 r3 | Repairs 3 GAP and 1 MINOR findings without strengthening the mathematical conclusions. |
| Added the general stage-key height identity; separated the nonzero exact-height lift contract from the zero-lift convention; and made the weld lint exclude its own specification, quotations, and negated scope fences. | T1P3, 2026-08-12 r4 | Repairs 2 GAP and 1 MINOR findings and types the letter residues, composed-key heights, and vanishing-coefficient branch. |
| Stated the graded scalar-covariance and slot-grade conventions used by the C3 ladder reads; imported the missing level-two bridge and carry structure through \(\mathrm{(H\!-\!HETOW\!-\!LOCAL)}\); and reattached the level-one basis sentence. | T1P5, 2026-08-12 r5 | Repairs 2 GAP and 1 MINOR findings without promoting either the sitewise residual-read law or the local HETOW construction to an unconditional T1 theorem. |
| Propagated the zero-lift branch into the A3 and A6 absorption pins, and imported the canonical \(s\)-range and binary second-level carry required by the A2 derivation. | T1P7, 2026-08-12 r6 | Repairs 2 GAP findings: no finite exact height is assigned to a zero coefficient, and the HETOW carry proof now states and uses \(w_2\in\{0,1\}\). |
| Added the zero-homogeneous-component branch to the C3 canonical read and fixed a residue section for all coefficient representatives in \(L_M\). | T1P8, 2026-08-12 r7 | Repairs 1 GAP and 1 MINOR finding: zero coherent digits now satisfy the canonical-read and three-reads formulas without a nonexistent value-zero representative, and \(L_M\) is a literally defined section-dependent function. |
| Imported the GENTOW2 bounded coefficient space into the general corrected-key lift contract and made base-ladder nonvanishing an explicit certified-site obligation. | T1P9, 2026-08-12 r8 | Repairs 2 GAP findings: higher-degree higher-value perturbations are excluded, so the composed polynomial retains its monic bounded \(\Phi_i\)-adic shape; and \(w_i\in K_i^\times\), division by \(w_i\), and factor-pattern transport are asserted only where nonvanishing is supplied. |
| Re-attributed the A6 scalar-read pin to HE6 F-1 (`GENTOW6` has no \(\gamma_k\)/\(\varpi\) display); fenced (C2-vartheta)’s \(K_i^\times\) membership behind \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) at depth \(i\ge3\) and threaded the fence through (C3-corrected-lift)/(C3-key)/the R4-1 nonvanishing step; fixed the A3 \(\gamma_t\) naming; scoped the A7 PIN 2 consequence list to the pinned span; documented the md5 pin normalization convention; refreshed the front-matter status line. | model-diverse pass of record, 2026-08-12 r9 (Fable arm) | Repairs 2 GAP and 4 MINOR findings: absorption provenance now names the actual supplier note, and depth-\(\ge3\) residue membership is an explicit named supplier hypothesis rather than an unproved boxed claim. |
| Propagated \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) (depth \(i\ge3\)) into (C7)’s \(M2\) and \(M3\) interface rows, completing the r9 fence at the WELD-M-PKG interface. | T1P10, 2026-08-12 r10 (Fable arm) | Repairs 1 GAP finding: the “only as follows” table now carries the depth-\(\ge3\) residue-membership hypothesis on both fields that consume it; formulas C1–C6 and all other rows unchanged. |
| Declared the read codomain ((C3-read-codomain)) and threaded it through the \(w_i\) unit inference, the \(y/w_i\) automorphism, \(\psi_{i+1}^{(w_i)}\), the A7 B-law row, and a new §4.2 codomain tooth; completed the (C7) \(M2\) fence list with the full graded-read bundle; made the front-matter status line self-maintaining (in-place edit of record); renamed the HETOW carry to \(c_2^{\mathrm{HET}}\); defined the grade data \(\mu_i\), \(e(\mu_i)\), \(\Gamma_i=\frac{1}{e(\mu_i)}\mathbb Z\) and fixed unsubscripted \(dv\) to \(dv_1\). | Fable hostile pass, 2026-08-12 r11 (Fable arm) | Repairs 2 GAP and 3 MINOR findings: scalar output of the residual read is now an explicit named obligation with a verified \(i=2\) supplier citation rather than an inference from nonvanishing, and the WELD-M-PKG \(M2\) interface names its complete read fence. |
| Bound the grade-data normalization \(v\) to the base-normalized terminal tower valuation, with the GENTOW2 witness displayed (\(dv_2(\Phi_2^{e_3})=4\cdot2\cdot\tfrac{21}{8}=21=u_3\); the \(v=\mu_2\) reading gives \(20<21\) and falsifies (C1-stage-key-height)); renamed the grade group to \(\Lambda_i\) (GENTOW2's \(\Gamma_i\); translation noted); superseded honesty-ledger items 2 and 19 with the two-clause \(w_i\in K_i^\times\) gate ((C3-read-codomain) + (C3-ladder-nonvanishing)); re-declared the R6-2 replacement span through the original substitution sentence; bound \(K\) in (C4)/\(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\) to the ambient residue field of the level under comparison (A5: \(K=K_2\)). | Fable hostile pass, 2026-08-12 r12 (Fable arm) | Repairs 1 GAP and 4 MINOR findings: the height normalization now names its valuation — the terminal reading verified and the \(\mu_i\) reading falsified on the GENTOW2 witness — and the remaining loose symbols (\(\Gamma\), \(K\)) and the one-clause ledger gate are bound to their typed referents. |
| Retired the base §3 absorption-map TABLE by declaring the r2 “Replacement §3” span through its final row, relocating the two A1 rows byte-unchanged into a new **A1 — GENHN** block (R2-4's amendment re-anchored there) and recording the disposition of all fifteen retired rows, so that exactly one authoritative A-row status list survives (§3's A1 rows + the A2–A7 pinned-span blocks; §6's annex-effect column is historical record only); re-declared the R2-2 span through the closing (C4) sentence pair, so the (C4-support) box renders exactly once, inside the \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\) fence; re-declared the R2-4 span back to “If the tower additionally has”, so no unfenced outer-side clearance survives; re-declared the R4-2 span through the trailing level-one sentence and reattached the general-stage-data \(\psi_{i+1}\) display (R5-3 mechanism); declared the R8-2 A7 span narrow and re-anchored the retained supplier display \(u(\beta_t)=\Theta(t)w^{f_3-t}\); superseded honesty-ledger item 4 with the two-clause \(w_i\in K_i^\times\) gate; and re-scoped the grade-data integrality clause to the consumed sites, declaring the true codomain \(dv_i\in e(\mu_i)\Lambda_r=\frac{e(\mu_i)}{e(\mu_r)}\mathbb Z\supseteq\mathbb Z\) with the \(dv_2(\Phi_2)=\tfrac{21}{2}\) instance and a new §4.2 check 10. | Opus/Claude hostile pass, `runs/comp13/T1P11_output.log`, 2026-08-13 r13 (Claude arm) | Repairs 3 GAP and 5 MINOR findings, all strict-assembly or ledger-coherence: the effective text no longer asserts any absorption or clearance that the same section denies, every declared span now reaches its actual end, and the height normalization states the value group it actually has. No formula, pin, consumption check, or supplier fence is changed. |

**CONDITIONALITY:** [TABLE] This is a historical changes record. Per R13-1(d), any conflict with §3 is resolved in favor of §3.

**DERIVATION:** [ASSEMBLED — resolved effective proof] Each row records the corresponding replacement/repair family; it is not a fresh mathematical proof and does not enlarge absorption.

**RESOLUTION TRACE:** Base §6 plus every appended r-round record; R13-1(d) fixes its non-authoritative status for absorption.

**TEETH:** NONE directly; the rows document why checks 1–10 exist.

---

### EFF.T1.48  [acceptance-box]

**CANONICAL STATEMENT:**

> “The acceptance gate remains two clean hostile passes plus the revised machine battery. The historical 2026-08-10 run does not count as either clean pass.”

The hostile plan attacks normalization composition, HE6/C3 digit typing, the lift boundary, weld scope, the B-law supplier perimeter, the root-of-unity exception, sign/inverse conventions, and all A1–A7 consumptions.

**CONDITIONALITY:** Protocol gate. The later acceptance record discharges it at 2/2 and 10/10.

**DERIVATION:** [ASSEMBLED — resolved effective proof] The gate is stipulated in §7. The final acceptance record reports two clean model-diverse passes and `923` scored rows with no failure.

**RESOLUTION TRACE:** Base §7; r13 resets the counter; rider blocks advance it to 2/2; acceptance declares the gate met.

**TEETH:** Every battery row EFF.T1.35–.45 and the eight hostile attacks.

---

### EFF.T1.49  [table]

**CANONICAL STATEMENT:** `[TABLE — verbatim effective R13-1(c)]`

> “Each retired row asserted an ABSORPTION STATUS; retiring it therefore withdraws a claim and cannot strengthen the note. Where the row's content is carried by an effective A-block, this is a relocation of status into the block that already re-scoped it; where it is not, the claim is WITHDRAWN and that is said.”

| Retired base row | Where its content now lives |
|---|---|
| A2 HETOW · Wrap/carry preamble | A2 block: the three pinned HETOW displays, the \(\mathrm{(H\!-\!HETOW\!-\!LOCAL)}\) supplier interface (R5-2, R6-2), the boxed consumption check, and the closing scope sentence. The "Verbatim" label is withdrawn: the block's own scope sentence names the bridge, \(m\), the canonical range \(0\le s(a)<e_2\), the binary carry \(c_2^{\mathrm{HET}}\in\{0,1\}\) (R11-4) and the identification of \(\tau\) as imported HETOW facts. |
| A2 HETOW · Telescope and corrected key | A2 block, same displays and consumption check; the positive \(\eta^{W(t)}\) sign is (C2)/(C3) carrier text and is unaffected. |
| A3 GENTOW1 · Corrected coefficient pin | A3 block: the SPAN PIN displays, the R6-1 zero-coefficient branch, the R9-3 \(\gamma_t/\Gamma_t\) naming note, and the boxed consumption check. |
| A3 GENTOW1 · Value-blind budgets/floors | A3 block, **Residual obligation**: "Equal exact height only says that an already-established value-blind budget is unchanged by the gauge correction," with the budget floors themselves left to the GENTOW1/GENHN-2\('\)/HE6 suppliers. |
| A4 GENTOW3 · Gauge-annex corrected key | A4 block: the pinned corrected-key display on the live domain, with its consumption check. |
| A4 GENTOW3 · \(x\)-free rescope | A4 block: the pinned \(x\)-free display \(\iff i(M)=0\) and \(\lambda\in\mathbf F_Q\), with its consumption check; the withdrawal of full-slot claims below \(D'h\) is carrier text (§1.1) and ledger item 6. |
| A5 GENTOW4 · S0 naive key | A5 block: the pinned S3 corrected-key bridge on the displayed live domain \((f_2-t)u_2>D'h\); the corrected-versus-naive digit distinction is (C3) carrier text. |
| A5 GENTOW4 · 4.1(c)/S3 bridge | A5 block: the same pin plus the separately pinned attained-origin equation \(z^{t_{\mathrm{Def}}}=z^\nu\varepsilon(\beta)\) and the sentence "Any support comparison additionally cites \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\)." |
| A5 GENTOW4 · BOX-3 no-\(\eta\) axis | WITHDRAWN as an absorption claim (narrowing). No A5-block equivalent is supplied and none is claimed; the live instrument requirement in its neighbourhood is §4.2 check 5 (full orientation tooth, all three entries of the canonical \(\mu=3\) vector) together with the standing gauge-naive and inverse-orientation teeth. T1 now absorbs nothing from GENTOW4's BOX-3 statement. |
| A5 GENTOW4 · S4 residue-one relation (as replaced by R1-3) | Honesty-ledger item 8 (r1 form), which carries the content in full: "Under the stated carrier, \(\eta=1\) forces \(K_1=\mathbf F_Q\) and \(f_1=1\); these are not independent specialization axes. The condition \(\eta=1\) removes the level-one wrap correction, but it does not by itself make arbitrary digits \(x\)-free, because (C6-x-free) still requires \(i(M)=0\)." R1-3's row-replacement directive is hereby HISTORICAL: its target row no longer exists in the effective text. R1-3's other repair (ledger item 8) is untouched and remains the live carrier of the correction. |
| A6 GENTOW6 · Corrected coefficient/full support | A6 block: R6-1's actual-support display \(\operatorname{Supp}_xL_M(\lambda)\), the exact-height statement for \(\lambda\ne0\), and the zero branch. |
| A6 GENTOW6 · 6.3 scalar read | A6 block: the **SPAN PIN (scalar read; provenance HE6 F-1)** as re-attributed by R9-1, the \(\gamma_k(A)\) displays, the retained GENTOW6 S6.1 lift pin, and ledger item 20. |
| A7 GENTOW2 · S5.1 letter formula | A7 block: **SPAN PIN 1** (the level-two letter display) with its consumption check. |
| A7 GENTOW2 · S5.2 B-law | A7 block: the **B-law classification** in its effective R5-1 / R8-2 / R11-1 form, together with the retained supplier display re-anchored by R13-6 below. This row's "Verbatim" label is precisely what the block retires. |
| A7 GENTOW2 · Factor-pattern invariance | A7 block: **SPAN PIN 2** with R9-4's scoped consequence list (irreducible-factor degrees and multiplicities are NOT in the pinned span), and honesty-ledger item 4 in its R13-7 form. |

**DERIVATION:** `[LEDGER / STATUS NARROWING]` R13-1(a) retires the base table through its final row. R13-1(b) relocates A1. The table above then gives an exhaustive row-by-row disposition: a claim is either carried by an effective A-block or withdrawn. Its opening rule proves that retirement cannot strengthen T1. Verified designations X01–X14 locate the supplier/consumer perimeter used by these dispositions; quoted local-site descriptions not promoted to XREFs remain verbatim source wording.

**CONDITIONALITY:** Every surviving A-block retains its displayed supplier hypotheses, live domains, zero branches, and read fences. This table carries absorption status only; it does not certify the downstream append protocol.

**RESOLUTION TRACE:** Effective R13-1(c), source lines 4028–4048. Rider 1 changes only the referent of “The B-law rows”; Rider 2 restores the `Verbatim` definition at relocated A1; Rider 4 corrects R13-6's order list. None changes a disposition row.

**TEETH:** §4.2 check 5 and the gauge-naive/inverse-orientation teeth guard the withdrawn A5 BOX-3 classification; §7 attack 8 guards the complete disposition sweep.

---

### EFF.T1.50  [scope-record]

**CANONICAL STATEMENT:**

> “After this retirement the effective text contains exactly ONE authoritative A-row status list: §3's A1 block (two rows) together with the A2–A7 pinned-span blocks. §6's "Annex effect" column is a historical change log of the 2026-08-10 \(\to\) revision delta, not an absorption-status list — the R12-2 precedent for §6 ("The r11 §6 row's … is a historical record of what r11 wrote and stays byte-unchanged") applies to every §6 row. Where a §6 annex-effect phrase (for example "A1 and A2 are verbatim") disagrees with a §3 A-block, THE §3 BLOCK GOVERNS, and the §6 rows stay byte-unchanged as record.”

> “In §7's eighth attack, "the corresponding T1 row" reads as the corresponding §3 A-row (A1) or A-block (A2–A7). No attack is added or removed.”

**DERIVATION:** `[STATUS AUTHORITY]` R13-1(a) removes the only competing base table; R13-1(b) relocates A1; EFF.T1.49 accounts for every retired A2–A7 row. Hence the stated §3 list is unique. Treating §6 as historical prevents its stale annex-effect prose from restoring a retired status.

**CONDITIONALITY:** This governs the mathematical absorption/supply predicate. The append/consumption predicate remains outstanding under the acceptance record.

**RESOLUTION TRACE:** Verbatim R13-1(d)–(e), source lines 4050–4058. The acceptance record later confirms byte-freeze and places consumption re-checks/appends in the next queue.

**TEETH:** §7 attack 8, consumption sweep.


---

### EFF.T1.51  [acceptance-box]

**CANONICAL STATEMENT:** `[ASSEMBLED — verbatim pass record and governing acceptance classification]`

> “PASS 1: Opus/Claude-arm hostile pass on r13, 0C + 0G + 5m (`runs/comp13/T1P12_output.log`), its five minors folded as the post-pass rider block above → PASS 2: sol confirmation (gpt-5.6-sol high, `runs/comp13/T1SOL_output.log`), 0C + 0G + 1m, its single minor folded as Rider 6 above.”

> “Both passes are minors-only, and by the campaign's minors-only precedent — T4's post-pass \(\mathfrak M\)-gloss-direction rider and T5's two post-pass-1 locator riders, each folded on a 0C + 0G pass and each subsequently confirmed to 2/2 — each counts as a clean pass. Two consecutive clean fresh-context passes on model-diverse arms: **THE GAUGE-COCYCLE NOTE IS ACCEPTED at 2/2.**”

**DERIVATION:** `[ACCEPTANCE PROTOCOL]` Base §7 requires two consecutive clean hostile passes plus the revised battery. The final-rider counter records that, with PASS 2, the counter stands at 2/2. The acceptance record then applies the note’s stated minors-only precedent to the two recorded `0C + 0G` passes. X01–X04 verify the raw pass-log verdicts and finding counts; those logs say `NOT CLEAN` under their own strict templates, while the later governing acceptance record supplies the campaign-level clean-pass classification.

**CONDITIONALITY:** Accepted with EFF.T1.53’s three explicit qualifications and EFF.T1.55’s unchanged honesty-ledger conditions. This is T1-note acceptance, not certification that any downstream annex append landed.

**RESOLUTION TRACE:** Final-rider counter, source lines 4393–4395; governing acceptance record, lines 4400–4402. It supersedes the reset at 4257–4259 and the 1/2 counter at 4328–4330.

**TEETH:** NONE. The pass leg is paired with the independent battery leg EFF.T1.52; no individual machine tooth proves the hostile-pass verdict.

---

### EFF.T1.52  [battery-row]

**CANONICAL STATEMENT:**

> “**The battery leg of the gate is discharged.** §7 requires "two clean hostile passes plus the revised machine battery". The revised battery was re-run against the effective text of 2026-08-13 (r13 plus the post-pass riders): **10/10 PASS, 923 scored rows, 0 failing** (`runs/comp13/T1_battery_r13.log`), with checks 7, 8, 9 and 10 scored for the FIRST time (they had never been run), check 6 in its R4-3 self-excluding form, and all four planted teeth — naive gauge, wrong sign, misindexed telescope, inverse orientation — firing as required. The 2026-08-10 sealed run's status is unchanged: inherited evidence only, and no part of this acceptance rests on it.”

**DERIVATION:** `[EXECUTABLE EVIDENCE]` X05 verifies `BATTERY: 10/10 PASS`; X06 verifies `TOTAL SCORED ROWS: 923   FAILING: 0`; X07 verifies the planted-teeth row. The final-rider counter records the gate as met, and the acceptance record adopts this run as the revised battery leg.

**CONDITIONALITY:** Rider 7 resolves check 10’s alternate-reading ambiguity by making the literal exclusion list and consumption criterion score the same set. Per EFF.T1.53, the final Riders 6–7 were not reviewed by a third hostile arm. The historical 2026-08-10 run contributes no acceptance credit.

**RESOLUTION TRACE:** R13 initially says checks 7–10 were owed; Riders 5–7 repair the check-10 scoring scope; the final-rider counter at 4395 records 10/10; the acceptance paragraph at 4404 is governing.

**TEETH:** §4.2 checks 1–10 and all four planted mutants: gauge-naive, wrong-sign, misindexed telescope, inverse orientation.

---

### EFF.T1.53  [fence]

**CANONICAL STATEMENT:** `[ASSEMBLED — verbatim acceptance qualifications plus the governing non-change guarantee]`

> “No formula, no display, no value, no class, no span boundary in effect, no pin, no fence, no hypothesis, no honesty-ledger item and no consumption check is changed, and no absorption status moves.”

> “1. **The two final riders postdate both passes and are unreviewed by a further hostile arm.** Rider 6 cures PASS 2's minor; Rider 7 cures the battery's single alternate-reading ambiguity. Both are wording-grade: one scope insertion at the two sites that state the integrality claim, and two exclusion sentences appended to a battery instruction. The non-change guarantee at the head of that block governs. They were identified CONVERGENTLY by two independent instruments — a hostile reader and a literal scorer, from opposite directions — which is why they fold as riders rather than opening an r14; but the folded text itself has not been read by a third fresh context.”

> “2. **PASS 2's pin audit was note-internal.** The sol arm's repository shell launcher failed before command execution, so it could not reopen the HEAD supplier files at byte level; its pin audit used the closed source spans disclosed in the note, on which it reports the A2–A7 pin algebra closing (the A2 binary carry, the A6 normalized coefficient signs, A7's \(\Theta=\vartheta^{-1}\)), together with the \(w_i\) codomain and nonvanishing obligations, the depth-\(\ge3\) \((\mathrm{H\!-\!VARTHETA\!-\!RES})_i\) fence into (C3) and (C7) \(M2\)/\(M3\), and the JA/GENHN/HETOW supplier fences. The byte-level leg of the pins is supplied by the earlier passes that did reopen the sources and by the battery — not by PASS 2.”

> “3. **The battery's AMBIGUITY row is not a failing row.** Check 10 reported five sites falling outside every class under the literal exclusion-list reading (Reading A) that pass under the consumption-scoped reading (Reading B, scored as primary): four in R13-8's own Finding C-1 prose, one in the §6 record row. Rider 7 widens the exclusion so the two readings score the same set; the verdict it qualifies was already PASS.”

**DERIVATION:** `[RECORD / EVIDENCE FENCE]` These are limitations recorded by the governing acceptance block, not conclusions inferred by the compiler. The final-rider non-change guarantee explains why the post-pass edits were folded as wording-grade riders; it does not manufacture a third review or a byte-level PASS 2 audit.

**CONDITIONALITY:** Every use of EFF.T1.51–.02 carries all three qualifications. In particular, “accepted 2/2” must not be paraphrased as “final riders independently reviewed” or “PASS 2 reopened supplier HEAD files.”

**RESOLUTION TRACE:** Final-rider scope record, source lines 4335–4345; governing acceptance qualifications, lines 4406–4410. No later text removes them.

**TEETH:** §4.2 check 10’s alternate-reading row, as an evidence-grade qualification rather than a mathematical guard.

---

### EFF.T1.54  [scope-record]

**CANONICAL STATEMENT:** `[ASSEMBLED — final text authority, freeze, and append protocol]`

> “**The accepted text is BYTE-FROZEN from this fold forward.** The accepted T1 of record is the effective text as of r13, plus the post-pass rider block, plus Riders 6 and 7, and consumers cite it as exactly that. Later work appends dated consumption records or a further dated append BELOW this block; it does not rewrite the accepted text. Any change that would rewrite it opens a new hostile arc rather than an edit.”

> “**One in-place edit accompanies this fold, and it is the only one.** The front-matter status line is refreshed IN PLACE — on the R11-3 precedent, which likewise applied its cure in place while every other repair appends — to record that the acceptance block, not the highest-numbered r-section, is now the governing section. The replacement stays DATELESS, so R11-3's self-maintaining property survives unbroken: the governing block carries every round-dependent fact, and acceptance only moves which block that is. Apart from that one line, nothing above the start of the final-rider block is touched by this fold; everything else here appends.”

> “Consumption checks of the seven annexes against the accepted text, and the absorbed notes' dated appends, ride the next queue (the T3/T4/T5 pattern).”

**DERIVATION:** `[STATUS AUTHORITY]` The acceptance record explicitly defines the accepted text, permits only the dateless status-line refresh in place, and distinguishes later append-only records from rewrites. The last sentence places the seven-annex consumption/append protocol outside the completed T1 acceptance gate.

**CONDITIONALITY:** A later append may record consumption without rewriting this text. Any mathematical rewrite opens a new hostile arc. The mathematical §3 status list remains effective, but no downstream consumption PASS or dated append is inferred.

**RESOLUTION TRACE:** Governing acceptance record, source lines 4412–4416. It replaces R11-3’s former “highest-numbered r-section governs” status rule with acceptance-block authority while preserving the dateless self-maintaining form.

**TEETH:** NONE. This is the final text/protocol authority.

---

### EFF.T1.55  [fence]

**CANONICAL STATEMENT:** `[ASSEMBLED — line 4416 resolved against effective honesty-ledger item 1]`

> “**Standing conditionalities, unchanged and displayed.** The lemma is accepted WITH its honesty ledger, not cleared of it:”

> “1. At arbitrary depth, T1 proves only the value-zero ratio in (C1-general). A preceding-letter monomial description requires the named supplier hypothesis \(\mathrm{(H\!-\!JA\!-\!CONJ)}_i\). The level-two formula is proved directly and is unconditional.”

> “the B-law is conditional on the stated sitewise residual-read facts and on its GENTOW2-B\(''\)/GENTOW5-W(i) supplier perimeter; the full integral \(K_1\)-lift is proved on the live domain \(M>D'h\) only; WELD-M-PKG remains five heterogeneously typed fields with no cross-face coherence, no single map and no gauge uniqueness; raw print/canonical equality is iff \(z^\nu=1\), not iff \(\nu=0\); the \((\mathrm{H\!-\!VARTHETA\!-\!RES})_i\) fence at depth \(i\ge3\) reaches (C3) and (C7)'s \(M2\)/\(M3\) rows; and \(dv_i\) is NOT integer-valued in general — integrality holds exactly at the consumed nonzero-argument sites enumerated in the grade-data paragraph, the codomain being \(dv_i\in e(\mu_i)\Lambda_r=\frac{e(\mu_i)}{e(\mu_r)}\mathbb Z\supseteq\mathbb Z\). Consumption checks of the seven annexes against the accepted text, and the absorbed notes' dated appends, ride the next queue (the T3/T4/T5 pattern).”

**DERIVATION:** `[ASSEMBLED — resolved acceptance fence]` The acceptance record reaffirms, rather than re-proves, the effective C1, C3, C4, C6, C7, grade-data, honesty-ledger, and §3 perimeter clauses inventoried by shards 1–2. Its general-depth parenthetical is not carried into the effective statement: R2-1 explicitly withdrew arbitrary-depth reduction, effective ledger item 1 says only the value-zero ratio is unconditional, and the acceptance record declares both that these conditions are “unchanged” and that the accepted text is not rewritten. X08–X10 verify the three external designations named in the remaining final fence. The local hypothesis `(H-VARTHETA-RES)_i` occurs 17 times in the T1 note; its finer external supplier remains the shard-1 hypothesis-closure concern and is not invented here.

**CONDITIONALITY:** All clauses are conjunctive standing limits on the accepted theorem. Acceptance removes none of them. The final sentence is the consumption/append predicate, not part of the mathematical absorption predicate.

**RESOLUTION TRACE:** Governing acceptance record, source line 4416, resolved against R2-1 and effective honesty-ledger item 1; then R13-8 and Riders 6–7 govern the grade-data wording and R13-1 governs §3 status authority. The stale general-depth gloss is excluded, not silently retained.

**TEETH:** §4.2 check 1 guards the lift domain; checks 3, 5, 6, 8, 9, and 10 guard respectively the root-of-unity, B-law orientation, weld scope, ladder nonvanishing, read codomain, and value-group fences.

---

## 4. XREF verification ledger (consolidated, deduplicated)

Every designation below was checked with fixed-string grep (`grep -cF '<designation>' <file>`)
in the named target; counts shown were re-verified at merge time for the 10-item sample in
§8 and match every shard's recorded count exactly. Rows sourced from more than one shard
record the same target/designation/count triple in each source and are merged into one row,
marked DEDUP with the shard IDs that duplicated it.

| # | Target and designation | Count | Material / role | Source shard(s) | Dedup |
|---:|---|---:|---|---|---|
| 1 | `GENTOW2_PROOF_2026-08-09.md:(R-FGMN)` | 1 | Scalar codomain of the `i=2` residual read | s1 | — |
| 2 | `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B′` | 8 | Per-grade unit/read supplier; A7 perimeter | s1 | — |
| 3 | `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` | 10 | Telescope specialization, nonvanishing, A7 B-law supplier | s1, s3(X08) | **DEDUP** |
| 4 | `GENTOW2_PROOF_2026-08-09.md:S5.1` | 42 | Level-two letter pin | s1, s2(X12) | **DEDUP** |
| 5 | `HE6_PROOF_2026-08-08.md:F-1 — normalized slot coefficients in LEMMA HE6-0″` | 1 | Exact A6 scalar-read provenance | s1, s2(X09) | **DEDUP** |
| 6 | `HE6_PROOF_2026-08-08.md:LEMMA HE6-0″` | 6 | Supporting-context absorption perimeter | s1, s2(X05) | **DEDUP** |
| 7 | `GENHN_PROOF_2026-08-08.md:GENHN-LIFT` | 9 | A1/C6 exact lift | s1, s2(X01) | **DEDUP** |
| 8 | `HETOW_RECON_2026-08-09.md:LEMMA HETOW-4` | 3 | A2 pinned ratios / local supplier structure | s1, s2(X02) | **DEDUP** |
| 9 | `GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-1` | 7 | A3 consumer theorem | s1, s2(X03) | **DEDUP** |
| 10 | `GENTOW3_PROOF_2026-08-09.md:THEOREM GENTOW-3` | 10 | A4 consumer theorem | s1, s2(X06) | **DEDUP** |
| 11 | `GENTOW4_PROOF_2026-08-09.md:LEMMA GENTOW-4.1` | 4 | A5 consumer lemma | s1, s2(X07) | **DEDUP** |
| 12 | `GENTOW6_PROOF_2026-08-09.md:S6.1` | 15 | A6 lift pin | s1, s2(X10) | **DEDUP** |
| 13 | `GENTOW6_PROOF_2026-08-09.md:THEOREM GENTOW-6.3` | 10 | A6 consumer theorem | s1, s2(X11) | **DEDUP** |
| 14 | `GENTOW5_WI_2026-08-10.md:[GENTOW5-W(i)]` | 9 | Level-general B-law supplier perimeter | s1, s3(X09) | **DEDUP** |
| 15 | `GRTJA_PROOF_2026-08-08.md:JA-EPS-CORR` | 3 | C4 exact root-of-unity origin correction | s1 | — |
| 16 | `WELDMASTER_2026-08-08.md:WELD-M-PKG` | 5 | Five-field package interface | s1, s3(X10) | **DEDUP** |
| 17 | `WELDMASTER_2026-08-08.md:W2-C3` | 8 | Accepted M4 fence | s1 | — |
| 18 | `GENTOW1_PROOF_2026-08-09.md:GENHN-2′` | 1 | A3 residual budget/floor supplier named by the row | s2 (X04) | — |
| 19 | `GENTOW4_PROOF_2026-08-09.md:GENTOW4-BOX-3` | 3 | Withdrawn A5 BOX-3 absorption claim | s2 (X08) | — |
| 20 | `GENTOW2_PROOF_2026-08-09.md:S5.2` | 22 | A7 B-law site | s2 (X13) | — |
| 21 | `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B` | 30 | A7 pinned B-span/per-grade supplier family (distinct from B′/B″, rows 2–3) | s2 (X14) | — |
| 22 | `runs/comp13/T1P12_output.log:VERDICT: NOT CLEAN` | 1 | PASS 1 raw verdict | s3 (X01) | — |
| 23 | `runs/comp13/T1P12_output.log:FINDINGS: 0C + 0G + 5m` | 1 | PASS 1 findings; acceptance folds the minors under the campaign precedent | s3 (X02) | — |
| 24 | `runs/comp13/T1SOL_output.log:VERDICT: NOT CLEAN` | 1 | PASS 2 raw verdict | s3 (X03) | — |
| 25 | `runs/comp13/T1SOL_output.log:FINDINGS: 0C + 0G + 1m` | 1 | PASS 2 findings; Rider 6 folds the minor | s3 (X04) | — |
| 26 | `runs/comp13/T1_battery_r13.log:BATTERY: 10/10 PASS` | 1 | Revised battery verdict | s3 (X05) | — |
| 27 | `runs/comp13/T1_battery_r13.log:TOTAL SCORED ROWS: 923   FAILING: 0` | 1 | Scored-row total | s3 (X06) | — |
| 28 | `runs/comp13/T1_battery_r13.log:the four planted teeth each fire` | 1 | Planted-mutant result | s3 (X07) | — |

**Total unique XREF designations: 28. Duplicate instances removed: 13** (10 rows
duplicated between shard 1 and shard 2 — X01,X02,X03,X05,X06,X07,X09,X10,X11,X12 of
shard 2 — plus 3 rows duplicated between shard 1 and shard 3 — X08,X09,X10 of shard 3).
No zero-count or descriptive string is emitted as an XREF; no designation was invented.

### Sample re-verification (10 of 28, grep-rerun at merge time against the working tree)

| Designation | Recorded count | Re-verified count | Match |
|---|---:|---:|---|
| `GENTOW2_PROOF_2026-08-09.md:S5.1` | 42 | 42 | ✓ |
| `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B″` | 10 | 10 | ✓ |
| `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B′` | 8 | 8 | ✓ |
| `GENHN_PROOF_2026-08-08.md:GENHN-LIFT` | 9 | 9 | ✓ |
| `HETOW_RECON_2026-08-09.md:LEMMA HETOW-4` | 3 | 3 | ✓ |
| `GENTOW1_PROOF_2026-08-09.md:LEMMA GENTOW-1` | 7 | 7 | ✓ |
| `GENTOW1_PROOF_2026-08-09.md:GENHN-2′` | 1 | 1 | ✓ |
| `GENTOW4_PROOF_2026-08-09.md:GENTOW4-BOX-3` | 3 | 3 | ✓ |
| `GENTOW2_PROOF_2026-08-09.md:S5.2` | 22 | 22 | ✓ |
| `GENTOW2_PROOF_2026-08-09.md:LEMMA GENTOW2-B` | 30 | 30 | ✓ |

All 10 sampled counts match exactly; no drift introduced by sharding or merge.

### Sample statement-quote re-verification (5 of 55, checked verbatim against the source note)

| Statement | Quoted fragment | Found at source line | Match |
|---|---|---:|---|
| EFF.T1.02 (`C2-zero-normalizer`) | `\widehat n_i(0)=1` | 1321 | ✓ |
| EFF.T1.52 (battery leg) | "10/10 PASS, 923 scored rows, 0 failing" | 4404 | ✓ |
| EFF.T1.50 (status authority) | "exactly ONE authoritative A-row status list" | 4052 | ✓ |
| EFF.T1.54 (freeze/authority) | "The accepted T1 of record is the effective text as of r13" | 4412 | ✓ |
| EFF.T1.54 (byte-freeze) | "BYTE-FROZEN from this fold forward" | 4412 | ✓ |

All 5 sampled quotes are byte-identical to the source note at the cited lines; no
drift introduced.

---

## 5. Local supply/consumption ledger

### 5.1 Per-annex mathematical supply (merged from shard 1 §3.2 and shard 2 §4 — same
seven annexes described from two angles; merged pairwise, each merge marked DEDUP)

| Annex/consumer | Verified designation(s) | T1 supply (EFF unit) | Mathematical status | Surviving fence / withdrawal | Append/consumption-protocol status |
|---|---|---|---|---|---|
| A1 GENHN **[DEDUP: s1 row 1 + s2 A1 row]** | `GENHN-LIFT` (9) | EFF.T1.20, .25 | Two relocated `Verbatim` rows | Exact lift on `M>D'h`; clearance only through `(H-GENHN-CLEAR)` | Outstanding after acceptance |
| A2 HETOW **[DEDUP: s1 row 2 + s2 A2 row]** | `LEMMA HETOW-4` (3) | EFF.T1.19, .26 | Pinned A2 block governs; old `Verbatim` labels withdrawn; clauses (c)–(d) not absorbed | `(H-HETOW-LOCAL)` supplies bridge, range, binary carry, local identifications | Outstanding after acceptance |
| A3 GENTOW1 **[DEDUP: s1 row 3 + s2 A3 row]** | `LEMMA GENTOW-1` (7); `GENHN-2′` (1) | EFF.T1.27 | Supplies gauge input only | Zero branch and residual budgets/floors remain external | Outstanding after acceptance |
| A4 GENTOW3 **[DEDUP: s1 row 4 + s2 A4 row]** | `THEOREM GENTOW-3` (10) | EFF.T1.28 | Supplies corrected-key and x-free inputs only | Live lift domain; no theorem-wide absorption | Outstanding after acceptance |
| A5 GENTOW4 **[DEDUP: s1 row 5 + s2 A5 rows]** | `LEMMA GENTOW-4.1` (4); `GENTOW4-BOX-3` (3, withdrawn) | EFF.T1.29 | Pinned corrected-key/origin input only; BOX-3 absorption withdrawn; S4 status carried only by honesty item 8 | Support comparison requires `(H-JA-RES-CONJ)` | Outstanding after acceptance |
| A6 GENTOW6 **[DEDUP: s1 row 6 + s2 A6 row]** | `THEOREM GENTOW-6.3` (10); `S6.1` (15); HE6 `F-1` (1) | EFF.T1.18, .20, .30 | Supplies normalized scalar-read and exact-lift inputs only | Scalar read is HE6 F-1; lift is GENTOW6 S6.1; zero/nonzero split retained | Outstanding after acceptance |
| A7 GENTOW2 **[DEDUP: s1 row 7 + s2 A7 rows]** | `S5.1` (42); `S5.2` (22); `LEMMA GENTOW2-B′` (8); `LEMMA GENTOW2-B″` (10); `LEMMA GENTOW2-B` (30) | EFF.T1.06, .15, .31 | Letter/rescaling pins plus gauge algebra only; pin 2 has narrowed consequence list | B-law supplier identity remains external to T1 | Outstanding after acceptance |

**Dedup count for this section: 7** (every annex row is the union of one shard-1 row
and one-or-more shard-2 rows describing the same A-block from a different angle;
no information from either source is dropped — the union keeps the fuller designation
list and the fuller fence description of each pair).

### 5.2 Note-level acceptance/protocol ledger (shard 3 only — a different predicate,
not a duplicate of §5.1: this table is about the note's OWN hostile-pass/battery
gate, not about what individual annexes receive from T1)

| Predicate / object | Effective local status | Governing unit | What is not implied |
|---|---|---|---|
| T1 hostile-pass gate | **2/2 accepted** under the note's minors-only precedent | EFF.T1.51 | Does not erase the three acceptance qualifications (EFF.T1.53) |
| Revised T1 battery | **10/10 PASS; 923 rows; 0 failing; four planted teeth fired** | EFF.T1.52 | Historical 2026-08-10 run supplies no acceptance credit |
| Mathematical A1–A7 status | **Unchanged by final riders and acceptance**; authoritative list remains §3 (EFF.T1.50) | EFF.T1.53–.55 | No new absorption is created here |
| A1–A7 consumption checks | **Outstanding; next queue** | EFF.T1.54–.55 | T1 acceptance is not a downstream consumption PASS |
| Absorbed-note dated appends | **Outstanding; next queue** | EFF.T1.54–.55 | No append is declared landed |
| Accepted text | **Byte-frozen**; append-only records may follow | EFF.T1.54 | A rewrite requires a new hostile arc |

---

## 6. TEETH inverse table (unified; every row's guarded-unit list is the UNION across
whichever shard(s) named that battery row/tooth)

| Battery row / hostile tooth | Guarded unit(s) (union) | Disposition |
|---|---|---|
| §4.2(1), GENHN-LIFT boundary | .01, .13, .20, .25, .27–.30, .52, .55 | Executable regression; 10/10 accepted battery |
| §4.2(2), positive-wrap sign | .07, .10–.13, .25, .27, .29, .52 | Executable regression; accepted battery PASS |
| §4.2(3), JA origin/root of unity | .16–.17, .29, .52, .55 | Executable regression with supplier-fenced support leg; accepted battery PASS |
| §4.2(4), HE6 normalization | .18–.19, .26, .30, .52 | Executable regression; accepted battery PASS |
| §4.2(5), full orientation | .03, .09, .11, .14–.15, .31, .34, .49, .52, .55 | Executable inverse-orientation mutant; accepted battery PASS |
| §4.2(6), weld scope lint | .22–.24, .32, .52, .55 | Executable self-excluding document lint; accepted battery PASS |
| §4.2(7), coefficient space | .02, .12, .20, .30–.31, .52 | Executable higher-degree perturbation regression; first scored in accepted run |
| §4.2(8), ladder nonvanishing | .03, .09, .12, .15, .31, .52, .55 | Executable zero-positive-grade mock-read regression; first scored in accepted run |
| §4.2(9), read codomain | .03, .09, .12, .15, .31, .52, .55 | Executable initial-form mock-read regression; first scored in accepted run |
| §4.2(10), value group | .02, .04, .12, .20, .30, .52, .53, .55 | Executable regression with Riders 5–7 exclusions; first scored in accepted run |
| gauge-naive mutant | .10–.13, .27, .29, .34, .49, .52 | Planted mutant; acceptance says fired |
| wrong-sign mutant | .07, .10–.13, .27, .29, .34, .52 | Planted mutant; acceptance says fired |
| misindexed-telescope mutant | .07–.10, .14, .34, .52 | Planted mutant; acceptance says fired |
| inverse-orientation mutant | .11, .14–.15, .31, .34, .39, .49, .52, .55 | Planted mutant; acceptance says fired |
| §7 attack 8, consumption sweep **[new row, shard 2 only — not one of the 14 §4.2/mutant keys above]** | .49–.50 | Executable regression |

**Zero-orphan check (unified):** every EFF unit that carries a TEETH entry in its own
statement block appears in at least one row above, or in the hostile-plan gate
`EFF.T1.48`, or is itself a protocol/provenance record explicitly exempted from the
battery-row count (`EFF.T1.49`'s own row for A5 BOX-3 aside, and shard 3's `.51`, `.53`,
`.54`, which are pass-verdict/qualification/authority records rather than mathematical
claims guarded by the numbered battery). **Zero battery-row orphans; zero toothed-unit
orphans**, consistent with all three shards' own zero-orphan claims.

---

## 7. Boundary-unit resolution (merge rule 4)

Each shard's SHARD NOTES section names the units whose editing directive is physically
drafted in its own line range but whose destination HOME is elsewhere. Three such units
are named across the three shards; each is verified below to appear **exactly once** in
the merged statement inventory, assembled whole at its destination:

| Split unit | Physically drafted at | Destination HOME | Appears once, at | Cross-shard agreement |
|---|---|---|---|---|
| R7-2 (residue section fix for `L_M`, C6 proof) | Shard 2 range (source lines 3103–3196) | Base C6, §1.1 (shard 1) | **EFF.T1.20** | Shard 1 §7 and shard 2 §7 both name this exact routing; shard 2 does not re-emit a duplicate statement, only a routing-table row |
| R13-7 (supersede honesty-ledger item 4) | Shard 2 range (source lines 4178–4193) | Base §5 (shard 1) | **EFF.T1.46** (ledger items 2/4/19/22) | Shard 2 §7 HOME routing audit names this destination; shard 1's resolution rules and `.46`'s RESOLUTION TRACE both incorporate it; shard 3 does not re-touch it |
| R13-8 (re-scope grade data; add check 10) | Shard 3 range (source lines 4194–4250) | Base §1.1 and §4.2 (shard 1) | **EFF.T1.02** and **EFF.T1.44** | Shard 2 SHARD NOTES and shard 3's own HOME routing audit both state "resolved in shard-1 units `.02` and `.44`"; shard 1's resolution rules item 6 and `.02`/`.44`'s own RESOLUTION TRACE fields independently confirm r13/R13-8 is folded in |

No fourth candidate was found: shard 1's own SHARD NOTES additionally flags R7-2 as the
only leading-edge boundary case in its own range, and shard 3's SHARD NOTES confirms its
own leading edge (line 4194, R13-8) and trailing edge (line 4416, complete) are both
whole. **All three named boundary units resolve to exactly one destination each; zero
boundary-unit duplicates and zero boundary-unit gaps.**

---

## 8. Self-audit and OPEN-CALLS (carried forward verbatim from shard 1; shards 2–3
introduced none)

None of shard 1's five OPEN-CALLs carries an explicit `FOR-0x` phase-routing tag in the
source shard (unlike, e.g., EFF-T3's `FOR-0d`); they are reproduced here exactly as
written, with no tag invented at merge time.

### OPEN-CALL 1 — source designation for `(H-JA-CONJ)_i`

T1 names "the accepted JA conjugation formula" but gives no grep-verifiable external
theorem designation. The hypothesis is retained by its T1-local tag and is not assigned
an invented XREF.

### OPEN-CALL 2 — source designation for `(H-JA-RES-CONJ)`

T1 names "the accepted harness/print conjugation formula" but gives no exact external
unit designation. `JA-EPS-CORR` verifies the origin correction, not necessarily this
whole-polynomial supplier; no conflation is made.

### OPEN-CALL 3 — source designation for `(H-GENHN-CLEAR)`

T1 calls it the accepted `T(b)'(i)` site, but fixed-string grep for that designation in
`GENHN_PROOF_2026-08-08.md` returns zero. `GENHN-LIFT` is verified for the lift and is
not invented as the clearance theorem.

### OPEN-CALL 4 — unnamed surrounding tower correctness theorem

The note requires it to convert residual factor patterns to p-adic splitting types but
names neither a file nor a theorem designation. This is a hypothesis-closure obligation,
not an XREF. (This is the same open obligation EFF-T3 routes as its own `FOR-0d — NEEDS
ASVIN`; T1 states it but does not itself carry the routing tag.)

### OPEN-CALL 5 — level-general residual-read supplier

At `i≥3`, the note requires a supplier carrying read codomain, nonvanishing, and the
other sitewise read laws, and separately `(H-VARTHETA-RES)_i`; it names no
grep-verifiable external unit. `GENTOW5-W(i)` verifies the stated perimeter but does not
by itself resolve the finer source-unit mapping.

### Fidelity audit (merge-level, in addition to each shard's own)

- All 55 canonical statement units carry mandatory DERIVATION, CONDITIONALITY,
  RESOLUTION TRACE, and TEETH fields, verbatim-or-`[ASSEMBLED]` per the template.
- Every source table is marked `[TABLE]`; no source table was prosified at merge time.
- All 28 unique external XREF designations have fixed-string counts ≥1; a 10-designation
  sample was re-grepped at merge time and matched exactly (§4).
- A 5-quote sample was re-checked verbatim against the source note by line number and
  matched exactly (§4).
- No shard's numbering collides with another's after the SHARD-MAP renumbering; no
  cross-reference inside any DERIVATION/CONDITIONALITY/RESOLUTION TRACE/TEETH field
  still points at a retired `EFF.T1.sKof3.NN` ID (verified by exhaustive regex sweep of
  the merged text).
- The three shard-boundary units (R7-2, R13-7, R13-8) each resolve to exactly one place
  in the merged inventory (§7); no boundary material was duplicated or dropped.
- Absorption status (§3 mathematical supply, §5.1) and the append/consumption protocol
  (§5.2, and the "Outstanding after acceptance" column throughout §5.1) are kept as
  distinct predicates everywhere, matching all three source shards' own discipline.

### Open calls carried forward with FOR-0d routing

Per the merge charge: **the five OPEN-CALLs above carry forward verbatim and unresolved.**
None is discharged by the act of merging. OPEN-CALL 4 (the unnamed surrounding tower
correctness theorem) is the T1-side half of the same trust-boundary decision that
EFF-T3 routes to Phase 0d (`FOR-0d — NEEDS ASVIN`); the two notes name the identical gap
independently rather than one importing it from the other. OPEN-CALLs 1, 2, 3, and 5 are
hypothesis-closure/consumption obligations for Phase 0c (the GENTOW5/JA/GENHN supplier
perimeter), consistent with the routing already used for EFF-T3's own `X18` supplier-
perimeter open item.

---

EFF-T1 MERGED: 55 statements / 28 xrefs verified / 5 open calls
