# EFF-T4 — CANONICAL EFFECTIVE SPECIFICATION v2

## 1. Header

**Source note:** `lean/notes/openmath/T4_CERTIFICATE_WITNESS_2026-08-12.md`

**HEAD blob hash:** `4a80abbfb41cd2799f5051336949f09b1256f10f`

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Revision 2, Stage 0a.

**Governing template:** `spec/EFF_TEMPLATE_v2.md` (all rules; full compilation).

**COMPILED-BY:** opus (2026-08-14, Asvin-authorized substitution, PROJECT_STATE #51). CODEX CROSS-READ OWED (post-reset).

### Effective-text rule

The note carries no literal effective-text rule, so the rule is DERIVED from the note's own structure, per template rule 6 of `runs/qgen/EFFT3_crossread.md` §4.3.

Two source facts fix it.

First, the note is a base composition (S0–S8 plus a composition record) followed by **five** dated repair rounds, each of which supplies verbatim-ready replacements. Each round announces its own replacement instructions, e.g. r1:

> “Four verbatim-ready r1 repairs follow.”

r4:

> “No source file is touched by r4; all five corrections are dated, verbatim-ready replacements within this note.”

Second, the acceptance record certifies the post-r5 text, not the base:

> “Arc: composed (comp4 T4C2) → r1–r3 (sol-arm passes with repairs;
> pins blocked by the sandboxed executor until the pasted-source
> protocol) → r4 (Fable arm: the reversed GT6 BOX-4 pin re-anchored,
> 17-marker validation record) → r5 (Fable arm: the member class 𝔐
> defined on the sources' weak coefficient slice — no disc hypothesis;
> the stale CERT-TOP sentence withdrawn; 𝒜_j defined; GT6 6.3(a)+(b)
> certified as discharging r3's full-exposure premise at f₁ = 1,
> μ₂ = 2 only) → PASS 1: Fable-arm hostile, 0C + 0G + 1m (the
> 𝔐-gloss direction rider, folded per the minors-only precedent) →
> PASS 2: sol confirmation (gpt-5.6-sol high,
> runs/comp12/T4P7_output.log), VERDICT CLEAN (0C + 0G + 0m —
> "clean mathematical confirmation"). Two consecutive clean
> fresh-context passes on model-diverse arms: **THE CERTIFICATE
> WITNESS NOTE IS ACCEPTED at 2/2.**”

**Therefore the effective text is the base with every r1–r5 replacement applied in round order, plus the post-pass dated rider folded (the acceptance record names it "folded per the minors-only precedent").** Where two rounds replace the same span, the later round governs. This is a derived rule, not a quotation attributed to the acceptance record.

### Supersession chain inside the note (the six same-span collisions)

`[TABLE]`

| Span | r1 | r2 | r3 | r4 | r5 | Governing text |
|---|---|---|---|---|---|---|
| Status line | R1-C1 | — | — | R4-m2 | R5-63A "Status refresh" | R5-63A; then the ACCEPTANCE RECORD supersedes it (EFF.T4.43, .45) |
| S5.1 pin-validation record | R1-C1 (inserted, UNRESOLVED) | R2-C1 (replaced, UNRESOLVED) | — | R4-C1 (replaced, VALIDATED) | R5-V (added alongside) | R4-C1 for the pre-r5 stacks; R5-V for the r5 additions |
| S0 “member family lies in the affine slice” | R1-G2 (introduced) | — | — | — | R5-F1 (replaced by DEFINITION 𝔐) | R5-F1 |
| LEMMA T4.2(a) + its first proof paragraph | R1-m1 | R2-G1 (proof para) | — | — | R5-F1(1) (rebind) | R1-m1 statement; R2-G1 proof as rebound by R5-F1(1) |
| S4.3 | R1-G1 (exposed-slot instance under (EXPOSE-6.5)) | R2-G3 (downgraded to CANDIDATE) | — | — | — | **R2-G3** — R1-G1 is fully superseded |
| GT6 pin stack | — | — | — | R4-C1 (span 4 re-anchored) | R5-m2 (five-span stack) | R5-m2 |
| GT3 pin stack | — | — | — | R4-G2 (six spans) | — | R4-G2 |

### Scope of record — mandatory two-predicate split

#### A. Mathematical absorption/supply set

The note's own boxed governing claim, as replaced by R5-m1, is:

> \[
> \boxed{
> \text{touched at }j
> \;:\Longleftrightarrow\;
> \omega_j\ne0
> \;\Longleftrightarrow\;
> \nu_j(f_{\mathrm{key}})=\Theta_j
> }
> \]

and its S7 delivery list is:

> **Delivered here.**
>
> - One canonical definition of touched coordinate in the
>   certificate sense.
> - One attainment lemma, including the repaired perturbation
>   margin and the exposed-slot test.
> - Two source-scoped instance records.
> - Fail-closed, marker-delimited source pins.
> - A single home for later certificate and count refinements.

Thus the mathematical supply set is exactly **one definition (T4.1), one lemma (T4.2, four clauses), and two source-scoped instance records (`GT3-THRESHOLD`, `GT6-CERT-TOP`)**, over a pinned source pair. The number of *source conclusions absorbed* is **two**: GENTOW-3(iv)'s touched-coordinate/attainment inference and GENTOW-6.3(b)'s CERT-TOP implication. The μ₂ ≥ 3 GENTOW-6.5 computation is **not** absorbed — R2-G3 downgraded it to a candidate.

#### B. Consumption/append-protocol scope

The acceptance record states, without truncation:

> “Consumption checks + the absorbed notes' dated appends ride the next queue. Standing fences
> unchanged and displayed: f₁ ≥ 2 (BOX-4 residue), μ₂ ≥ 3 (candidate
> only), the disc ≠ 0 quarantine at the σ-read legs.”

Accordingly the protocol scope is: **two absorptions, BOTH with consumption check and dated append OUTSTANDING.** This is verified negatively — `grep -cF 'GT3-THRESHOLD' GENTOW3_PROOF_2026-08-09.md` = 0 and `grep -cF 'GT6-CERT-TOP' GENTOW6_PROOF_2026-08-09.md` = 0, and neither source contains the string `T4` at all (count 0 in both). See XREF ledger rows N1–N4.

The mathematical acceptance (2/2) and the protocol completion are therefore in **different states**, and no compilation consumer may read the acceptance as an append-landed record.

### Resolution rules applied

1. The base is superseded span-by-span by r1–r5 in round order; a later round wins on any span an earlier round also touched (the six collisions are tabulated above).
2. **R1-G1 is fully dead.** R2-G3 replaces S4.3 in full, and R2-G3's text explicitly rejects the exposure premise R1-G1 imposed as a hypothesis. Nothing of R1-G1 — including its `(EXPOSE-6.5)` tag — survives into the effective text. `(6.5-CAND)` survives because R2-G3 re-displays it.
3. **R1-C1 and R2-C1's S5.1 records are historical.** R4-C1's replacement says so: “This record supersedes the R1 and R2 pin-validation records.” The `bubblewrap is unavailable` infrastructure findings are round history, not effective-text conditionality.
4. The r0 sentence “This is GENTOW-6.3(b), CERT-TOP, as a literal exposed-slot instance of the certificate-witness lemma.” is **WITHDRAWN and deleted** by R5-F2 and is not part of the effective text.
5. The assembled S0 order is fixed by the rounds' own placement instructions: R1-G2's block, with R5-m2's 𝒜_j inserted “immediately after the \(\mathscr D_{<\mu_2}\) display”, R5-F1's DEFINITION 𝔐 replacing the affine-slice sentence (R5-m2 confirms: “(R5-F1's \(\mathfrak M\) definition lands after this insertion in the assembled S0 and uses \(\mathscr A_j\) and \(w(a,b)\) as defined here.)”), R2-C2's `gr_m` inserted “immediately after” the \(\Delta_j\) display, and R3-G1's full-exposure clause inserted “immediately after the definition of \(\operatorname{gr}_m\)”.
6. Every load-bearing occurrence of the word “member” is rebound to \(\mathfrak M\) by R5-F1's four numbered rebinding replacements. R5-F1 itself fences the remainder: “No other "member" site is load-bearing”.
7. The R5-63A consumption display is part of the effective text (it is a repair-round addition that the two clean passes then graded), but it is **scope-limited**: “Verdict: YES at the sealed scope — \(f_1=1\), \(\mu_2=2\), \(2i_{t^*}\ge D'\) — and NO elsewhere.”
8. The post-pass dated rider is folded (minors-only precedent, no grade event) and governs the reading of the 𝔐-definition's level-1 gloss.
9. The GRADE line “**GRADE: 0/2 (attempt).**” and every round's “The acceptance counter remains 0/2” are historical after the acceptance record.
10. Pin line/byte numbers recorded in the note's own S5.1 and R5-V tables are **independently re-verified at compile time** against the working tree; all 25 markers and 25 quotes match count, line and byte exactly (XREF ledger §4).
11. `GT3-THRESHOLD` and `GT6-CERT-TOP` are T4-local instance NAMES, not source designations; they are deliberately absent from the two sources (rule: they land only when the dated appends land).

### Quotation and prosification discipline

All source displays and tables below are reproduced as quotations or marked `[ASSEMBLED]`. Every source table is marked `[TABLE]`. No source display or table has been prosified. Truncation inside a quotation is marked with an explicit ellipsis. Terminal punctuation inside quoted displays is preserved as the note has it. Compiler classifications such as `[IMPORTED]`, `[DEFINITIONAL]`, `[ASSUMED]`, `[RECORD]`, `[SUPERSEDED]` are metadata, not source paraphrases.

---

## 2. NON-IMPORTS

T4 carries an unusually dense negative-import fence set; these are load-bearing for the DAG because T4 is a *compression* unit that deliberately does not take ownership of the source algebra.

**N-1 — the σ / discriminant quarantine.** R5-F1 states:

> “So \(\operatorname{disc}\ne0\) is NOT part of
> \(\mathfrak M\) and appears in no digit-floor clause of this note;
> any later consumer that needs a decided-leaf σ must import the
> source's own disc \(\ne0\) hypothesis at that consumption site,
> alongside — not inside — membership.”

and

> “T4 consumes none of that σ-content: every
> clause of LEMMA T4.2 is a graded-digit statement”.

So GENTOW-3(iv)'s deep-perturbation parenthetical (XREF X25) and the GENHN-family σ-decision displays are verified **NON-IMPORTS**.

**N-2 — GENTOW-6.4(a)'s bijection/count face.** R5-m2 states:

> “Only the grid-and-height display is consumed here:
> 6.4(a)'s bijection-codomain face (corrected by the post-PE2 rider
> inside the same pinned span) is consumed nowhere in this note.”

R5-V adds:

> “the rider
> itself records that the bijection/count face "is consumed nowhere
> at HEAD", and this note keeps it that way.”

**N-3 — GENTOW-3 S8.2/S8.4 non-functionality scope.** Retained unchanged by R4-G2:

> “The later S8.2/S8.4 non-functionality scope is not consumed by
> this instance.”

R4-G2 confirms the geometry: “new span 5 is half-open at the S8 heading and consumes nothing of S8–S8.4, and span 6 is half-open at S8.2.”

**N-4 — GENTOW-6.4(b), the 𝒯-free BAND-1 cap.** R5-m2's new GT6 span 3 is

> “half-open at clause (b), which is not consumed.”

**N-5 — the source algebra is retained by the sources, not moved into T4.** S6, as replaced by R4-m1:

> “The algebra that computes a proposed witness is not deleted:
> GENTOW-6 still owns the complete assembled-slot exposure
> calculation — the exclusion, in S0's full-exposure sense, of
> every other branch term and every incoming carry and recarry
> from the slot, not merely uniqueness among single-extraction
> branches — together with the corrected-lift support calculation
> and the higher-\(\mu_2\) binomial coefficient.”

and

> “T4 owns only the shared meaning of the
> assembled witness and the inference from a nonzero critical digit
> to attainment.”

**N-6 — no machine evidence of T4's own.** S7:

> “**Evidence status.** This note adds no machine computation. Its
> regression evidence is inherited from the byte-frozen GENTOW-3
> and GENTOW-6 artifacts and their dated hostile-arc instruments.
> Those artifacts support the two instance checks; they are not
> fresh evidence for a stronger theorem.”

**N-7 — no source file edited.** S6: “No accepted source is rewritten by this composition unit.” Composition record: “T4 makes no source-file edit and no artifact edit.”

**N-8 — the μ₂ ≥ 3 computation is not consumable.** S6, as replaced by R2-G3:

> “- the later \(\mu_2\ge3\) computation is not consumable through
>   T4.2(c): it remains the candidate record of S4.3 unless a
>   separately pinned and validated source assertion proves the
>   required exposure premise.”

**N-9 — nothing at \(f_1\ge2\) is sealed by R5-63A.** Its scope fence:

> “no (a)-grade layer classification is
>   sealed at \(f_1\ge2\) (GENTOW6-BOX-4 residue). S4.2's r3
>   conditional language stands unchanged.”

**N-10 — the eight “Not claimed” items** (EFF.T4.35) are the note's own headline negative fence; they are reproduced in full there rather than duplicated here.

Accordingly: **no edge is created** from T4 to the σ/decidedness layer, to GENTOW-6.4's bijection or count faces, to GENTOW-6.4(b)'s cap, to GENTOW-3 S8.2/S8.4, or to any genre-general non-vanishing statement.

---

## 3. Statement inventory

45 units, contiguous, in effective-text order.

### EFF.T4.01  [convention]

**CANONICAL STATEMENT:**

> “Work in the full-side tower setting shared by GENTOW-3 and the certificate part of GENTOW-6. Thus
>
> \[
> D'=e_1f_1,\qquad E_2=e_2f_2u_2,\qquad
> \delta=u_2-e_2D'h\ge 1,
> \]
>
> and for each composed coordinate \(j<\mu_2\),
>
> \[
> \Theta_j=(\mu_2-j)E_2+\delta.
> \]”

**DERIVATION:** `[IMPORTED]` The setting is not derived in T4; it is the shared full-side tower setting of the two pinned sources. XREF X01 locates the GT3 threshold section (`## S0. THE ONE CONSTANT AND THE THRESHOLD`), XREF X11 the GT6 certificate theorem section.

**CONDITIONALITY:** the full-side tower setting; \(\delta\ge1\); \(j<\mu_2\).

**RESOLUTION TRACE:** base S0 opening, lines 11–22. Untouched by r1–r5 — R1-G2's replacement span begins at “For a member \(f\), write”.

**TEETH:** S8 PE1(4).

---

### EFF.T4.02  [convention]

**CANONICAL STATEMENT:**

> “The composed key is read in the corrected gauge:
>
> \[
> \widehat c_t=\operatorname{lift}\!\left(c_t\eta^{W(t)}\right),
> \qquad
> W(t)=\left\lfloor\frac{(f_2-t)i(u_2)}{e_1}\right\rfloor ,
> \]
>
> with the exact-height lift interpretation at \(f_1\ge2\).”

**DERIVATION:** `[IMPORTED]` The corrected gauge is the sources' dated gauge-annex repair, not T4 work. XREF X03 is GT3's `### S7.1 THE DATED GAUGE ANNEX (F-1 repair): the corrected chat_t`; XREF X13 is GT6's `### S6.1 THE DATED GAUGE ANNEX`.

**CONDITIONALITY:** the exact-height lift interpretation is invoked only at \(f_1\ge2\).

**RESOLUTION TRACE:** base S0 lines 24–32; unchanged by r1–r5.

**TEETH:** S8 PE1(4); PE2 GT6 consumption (“the gauge-live \(\eta\ne1\) rows”).

---

### EFF.T4.03  [definition]

**CANONICAL STATEMENT:**

> “Let \(\mathscr D_{\le\mu_2}\) be the ambient module of dividends to
> which the composed \(K_2(x,Y)\)-division applies and whose honest
> \(\Phi_2\)-development has degree at most \(\mu_2\). For
> \(q\in\mathscr D_{\le\mu_2}\), write uniquely
>
> \[
> q=\sum_{k\le\mu_2}C_k(q)\Phi_2^k.
> \]
>
> Let
>
> \[
> \mathscr D_{<\mu_2}
> :=
> \{q\in\mathscr D_{\le\mu_2}:C_{\mu_2}(q)=0\}.
> \]”

**DERIVATION:** `[DEFINITIONAL]` R1-G2's diagnosis is that the base text defined \(\Delta_j\) only on the member affine slice while T4.2(b) subtracts a lower perturbation. R1-G2 states the fix: “This is the required linear extension of the notation from the member affine slice to lower perturbations; in particular, \(\Delta_j(g)\) is defined for \(g\in\mathscr D_{<\mu_2}\).”

**CONDITIONALITY:** none beyond the ambient composed-division setting.

**RESOLUTION TRACE:** R1-G2 replacement of base S0 “For a member \(f\), write” through the key's honest coordinates; head of the replacement block. Not touched by r2–r5.

**TEETH:** S8 PE1(3) (the repaired-margin check runs through \(\mathscr D_{<\mu_2}\)).

---

### EFF.T4.04  [definition]

**CANONICAL STATEMENT:**

> “For each \(j<\mu_2\), let
>
> \[
> \mathscr A_j:=\bigoplus_{a<D',\;b<e_2f_2}
> \widehat{\mathcal O}\cdot x^a\Phi'^{\,b}
> \]
>
> — the module of composed-grid coordinate strings at ONE
> coordinate \(j\): elements \(\sum_{a,b}c_{a,b}x^a\Phi'^{\,b}\)
> with \(a<D'\), \(b<e_2f_2\); as polynomials these have
> \(x\)-degree \(<D_2=\deg\Phi_2\) (one coordinate's grid, not the
> dividend module). The slot \((a,b)\) at digit value \(v\) carries
> \(dv_2\)-height \(e_1e_2\,v+w(a,b)\), with
> \(w(a,b)=a\,e_2h+b\,u_2\), and one \(K_2\)-digit per height by
> GENHN-2′. This is LEMMA GENTOW-6.4(a)'s grid display read at one
> coordinate. Only the grid-and-height display is consumed here:
> 6.4(a)'s bijection-codomain face (corrected by the post-PE2 rider
> inside the same pinned span) is consumed nowhere in this note.”

**DERIVATION:** `[IMPORTED — new pinned span]` R5-m2's diagnosis: “\(\mathscr A_j\) enters undefined at R1-G2's display \(C_j,\operatorname{Sh}C_j:\mathscr D_{\le\mu_2}\to\mathscr A_j\). The right codomain is NOT the degree-\(<\mu_2D_2\) dividend module; it is one coordinate's slot grid”. The grid is read off GENTOW-6.4(a): XREFs X41–X42 (`> a < D', b < e2f2; slot degree jD2 + bD' + a; slot dv2-height` and `> e1e2·v(c_{j,a,b}) + w(a,b), w(a,b) = a·e2h + b·u2). Then:`). GENTOW-6.4 lies outside the r0–r4 GT6 stack, so R5-m2 also adds the new span 3 (XREFs X14, X15).

**CONDITIONALITY:** \(j<\mu_2\); one \(K_2\)-digit per height requires GENHN-2′.

**RESOLUTION TRACE:** R5-m2, inserted “immediately after the \(\mathscr D_{<\mu_2}\) display” in the R1-G2 replacement for S0. New in r5; no earlier text.

**TEETH:** S8 PE1(1) (assembly and slot semantics); R5-V rider audit.

---

### EFF.T4.05  [definition]

**CANONICAL STATEMENT:**

> “> **DEFINITION (the member class \(\mathfrak M\)).** Writing
> >
> > \[
> > f=\Phi_2^{\mu_2}+g,\qquad
> > g=\sum_{j<\mu_2}C_j(g)\,\Phi_2^{\,j}\in\mathscr D_{<\mu_2},
> > \qquad
> > C_j(g)=\sum_{a<D',\,b<e_2f_2}c_{j,a,b}\,x^a\Phi'^{\,b}
> > \in\mathscr A_j,
> > \]
> >
> > the member class is the affine development slice
> >
> > \[
> > \mathfrak M:=
> > \Bigl\{\,f=\Phi_2^{\mu_2}+g:\
> > e_1e_2\,v(c_{j,a,b})+w(a,b)\;\ge\;(\mu_2-j)E_2
> > \ \text{whenever}\ c_{j,a,b}\ne0\,\Bigr\}
> > \]
> >
> > — leading digit pinned to \(1\), every lower slot digit weakly
> > at or above the composed side (equivalently: every composed
> > slot of \(g\) has weight \(\ge\mu_2E_2\)). Equivalently at the
> > level-1 read — by the same Step-0 carry conversion that pinned
> > GENTOW-3 S8.1 item (1) runs for its box — the entry pins of
> > \(f\) lie weakly above the inner side,
> > \(e_2\cdot dv(A_J)\ge(\mu_1-J)u_2\): exactly the membership
> > fact, and the only one, that GENTOW-3's Steps 0–2 consume.
> >
> > Membership in \(\mathfrak M\) is a pure coefficient condition
> > on the development digits. It carries NO discriminant
> > hypothesis and no decidedness hypothesis. Everywhere in this
> > note "member" means "element of \(\mathfrak M\)". The member
> > family lies in the affine slice \(C_{\mu_2}(q)=1\), and
> > differences of members with the same leading key power lie in
> > \(\mathscr D_{<\mu_2}\).
> >
> > Three membership facts, each by inspection of the definition:
> >
> > 1. \(f_{\mathrm{key}}=\Phi_2^{\mu_2}\in\mathfrak M\): its lower
> >    development is \(g=0\), so the slot condition is vacuous.
> >    Note \(\operatorname{disc}(f_{\mathrm{key}})=0\): the
> >    sources' floor domain provably contains a disc \(=0\)
> >    element, so no disc hypothesis can be part of membership.
> > 2. In-budget perturbations stay in \(\mathfrak M\): if every
> >    composed slot of \(g\) clears weight \(\mu_2E_2+1\) —
> >    GENTOW-3 S8.1's box, which is STRICTLY inside the membership
> >    floor — then \(f_{\mathrm{key}}+g\in\mathfrak M\), and
> >    \(f+g\in\mathfrak M\) for every \(f\in\mathfrak M\)
> >    (slotwise ultrametric). Pure coefficient arithmetic; no disc
> >    condition is implied, and the \((\Phi_2+c)^2\) example shows
> >    none could be.
> > 3. The measured FR-M3 W member lies in \(\mathfrak M\) at exact
> >    equality (slot weights \(9=\mu_2E_2\)) while sitting OUTSIDE
> >    S8.1's box — which is why the weak slice, and not the box,
> >    is the membership reading: GENTOW-3's S0 names it a member
> >    and records its floor-exact first divergence.”

**DERIVATION:** `[ASSEMBLED from R5-F1's diagnosis + its four byte-quoted source legs]` R5-F1 identifies the seam: “T4 quantifies (FLOOR) "for every member" (R2-G1) and hypothesizes "suppose that \(f\) is a member" (R2-G2) while never defining "member".” It then falsifies the disc-carrying reading twice: \(f_{\mathrm{key}}=\Phi_2^{\mu_2}\) is a \(\mu_2\)-th power with disc \(=0\), and at \(\mu_2=2\), “\(g=2c\Phi_2+c^2\) gives \(f_{\mathrm{key}}+g=(\Phi_2+c)^2\) with disc \(=0\), and \(g\) is in-budget once \(v(c)\) is large”. The positive derivation reads the sources' actual quantification domain off four verified spans: the 𝒯 display (X20), the Step-1 entry bound “On 𝒯 the entry pins lie weakly above the inner side:” (X22) as the only membership fact Steps 0–2 consume, the S8.1 proof-strength precedent “The corrected derivation (this note's Steps 0-2, run on g).” (X26) run on an object that “is not even monic of degree \(n\)”, and the S8.1 boundary confirmation that the FR-M3 W member sits at slot weights \(9<10=\mu_2E_2+1\), OUTSIDE the box (X29–X30). Conclusion, quoted: “the domain the sources actually run the floor on is the WEAK affine development slice (slot weights \(\ge\mu_2E_2\)), not the strict box (\(\ge\mu_2E_2+1\))”.

**CONDITIONALITY:** none — “Membership in \(\mathfrak M\) is a pure coefficient condition on the development digits. It carries NO discriminant hypothesis and no decidedness hypothesis.” The level-1 gloss is ONE-DIRECTIONAL per the folded dated rider (EFF.T4.44).

**RESOLUTION TRACE:** R5-F1 “Insertion (verbatim-ready)”, replacing R1-G2's sentence “The member family lies in the affine slice \(C_{\mu_2}(q)=1\), while differences of members with the same leading key power lie in \(\mathscr D_{<\mu_2}\).” Lands after EFF.T4.04 in the assembled S0 (R5-m2's own placement note). Reading of the level-1 gloss governed by the post-pass dated rider.

**TEETH:** S8 PE1(2), PE1(3); PE2 GT3 consumption (FR-M3 slack, the W member); the folded post-pass rider.

---

### EFF.T4.06  [definition]

**CANONICAL STATEMENT:**

> “For every \(q\in\mathscr D_{\le\mu_2}\), define
> \(\operatorname{Sh}C_j(q)\) to be the \(j\)-th stage-shadow
> coordinate produced by applying the \(K_2(x,Y)\)-division over
> \(\widehat{\mathcal O}[x]/(\Phi')\) to the dividend \(q\). Thus
>
> \[
> C_j,\operatorname{Sh}C_j:
> \mathscr D_{\le\mu_2}\longrightarrow\mathscr A_j
> \]
>
> are the coefficient maps of two linear division operators. Put
>
> \[
> \Delta_j(q):=\operatorname{Sh}C_j(q)-C_j(q)
> \qquad(q\in\mathscr D_{\le\mu_2}).
> \]”

and its closing remark:

> “This is the required linear extension of the notation from the
> member affine slice to lower perturbations; in particular,
> \(\Delta_j(g)\) is defined for
> \(g\in\mathscr D_{<\mu_2}\).”

**DERIVATION:** `[DEFINITIONAL]` The two reads are the sources' honest composed development and the stage-shadow \(K_2(x,Y)\)-division; R1-G2 states them as coefficient maps of two linear division operators so that T4.2(b)'s additivity step is licensed. Linearity is the ONLY property used downstream (see EFF.T4.15's derivation).

**CONDITIONALITY:** \(q\in\mathscr D_{\le\mu_2}\).

**RESOLUTION TRACE:** R1-G2 replacement for S0, after EFF.T4.05 in the assembled order.

**TEETH:** S8 PE1(3).

---

### EFF.T4.07  [definition]

**CANONICAL STATEMENT:**

> “For any coordinate digit string \(A\), let
>
> \[
> \operatorname{gr}_m(A)
> \]
>
> denote its canonical assembled digit at \(dv_2\)-height \(m\):
> all branches, carries, recarries, and terms landing in the same
> canonical \(K_2\)-slot at height \(m\) are added before the class
> is taken. Thus cancellation inside a slot is already reflected in
> \(\operatorname{gr}_m(A)\), while distinct canonical slots form
> separate components. The exact-height separation supplied by
> GENHN-2′ makes this graded digit unambiguous.”

**DERIVATION:** `[RESTORED]` R2-C2 is titled “restore the deleted definition of \(\operatorname{gr}_m\)”: R1-G2's S0 replacement had swallowed the base definition. R2-C2's justification, quoted: “This restores every operation used by \(\omega_j\), (FLOOR), and \(\nu_j\), and makes the key-power specialization below explicit.” Unambiguity is `[IMPORTED]` from GENHN-2′'s exact-height separation.

**CONDITIONALITY:** requires GENHN-2′'s exact-height separation for well-definedness.

**RESOLUTION TRACE:** base S0 (deleted by R1-G2) → restored verbatim by R2-C2, inserted immediately after the \(\Delta_j\) display of the R1-G2 replacement. Note the restored text reads “while distinct canonical slots form separate components”, against base's “distinct canonical slots form separate components”; the R2-C2 text governs.

**TEETH:** S8 PE1(1) — “that \(\operatorname{gr}_{\Theta_j}\) is taken after complete slot assembly and cancellation”.

---

### EFF.T4.08  [definition]

**CANONICAL STATEMENT:**

> “A canonical slot is **fully exposed by a contribution \(\xi\)**
> if, after every branch term and every incoming carry and recarry
> has been propagated to the canonical grid, the complete list of
> summands landing in that slot consists of \(\xi\) alone.
>
> Full exposure therefore quantifies over contributions of every
> provenance. Uniqueness merely among single-extraction
> contributions does not imply full exposure.”

**DERIVATION:** `[DEFINITIONAL — repair of an invalid inference]` R3-G1 closes the note's r0/r1/r2 defect, stated in its own closing sentence: “This closes the invalid inference from “one single-extraction contribution” to “nothing can cancel it” without attributing the stronger exposure fact to either pinned source before validation.”

**CONDITIONALITY:** none — this is a definition.

**RESOLUTION TRACE:** R3-G1, inserted in S0 “immediately after the definition of \(\operatorname{gr}_m\)”. New in r3.

**TEETH:** S8 PE1(5) as replaced by r3; PE2 GT6 consumption as replaced by r3.

---

### EFF.T4.09  [definition]

**CANONICAL STATEMENT:**

> “The distinguished certificate member is
>
> \[
> f_{\mathrm{key}}:=\Phi_2^{\mu_2}.
> \]”

with its membership and vanishing, as twice replaced:

> “It lies in \(\mathfrak M\) (S0, membership fact 1), hence in
> \(\mathscr D_{\le\mu_2}\), and its honest lower coordinates
> vanish:”
>
> \[
> C_j(f_{\mathrm{key}})=0\qquad(j<\mu_2).
> \]

**DERIVATION:** `[DEFINITIONAL]` The vanishing is immediate from the definition of the honest composed development of \(\Phi_2^{\mu_2}\) (the lower coordinates are empty). Membership is EFF.T4.05's membership fact 1 (“its lower development is \(g=0\), so the slot condition is vacuous”).

**CONDITIONALITY:** none. Note explicitly \(\operatorname{disc}(f_{\mathrm{key}})=0\) — recorded in membership fact 1 as the proof that no disc hypothesis can be part of membership.

**RESOLUTION TRACE:** R1-G2 tail → R2-C2 (“It is a member, hence belongs to …”) → R5-F1(4) (“It lies in \(\mathfrak M\) (S0, membership fact 1), hence in …”). R5-F1(4) governs.

**TEETH:** S8 PE1(2); the composition-record box (EFF.T4.40).

---

### EFF.T4.10  [definition]

**CANONICAL STATEMENT:**

> “> **DEFINITION T4.1 (touched coordinate; certificate sense).**  
> > For each \(j<\mu_2\), define the certificate witness
> >
> > \[
> > \omega_j
> > :=
> > \operatorname{gr}_{\Theta_j}
> > \bigl(\Delta_j(f_{\mathrm{key}})\bigr)
> > =
> > \operatorname{gr}_{\Theta_j}
> > \bigl(\operatorname{Sh}C_j(\Phi_2^{\mu_2})\bigr).
> > \]”

with the r3-replaced equivalence paragraph:

> “> Equivalently, \(\omega_j\) is the fully assembled
> > height-\(\Theta_j\) \(K_2\)-digit of the key power. Its assembly
> > includes every input landing in the canonical composed grid,
> > including all single-\(\Phi'\)-extraction routes, all other
> > branch terms, and every incoming carry and recarry. Every
> > collision and cancellation is completed before the digit is
> > taken.”

and the touched/untouched clause:

> “> The coordinate \(j\) is **touched** iff
> >
> > \[
> > \omega_j\ne0.
> > \]
> >
> > It is **untouched** iff \(\omega_j=0\).”

**DERIVATION:** `[DEFINITIONAL]` The second equality in the display uses EFF.T4.09: \(C_j(f_{\mathrm{key}})=0\) for \(j<\mu_2\), so \(\Delta_j(f_{\mathrm{key}})=\operatorname{Sh}C_j(\Phi_2^{\mu_2})\). The r3 replacement of the equivalence paragraph widens the assembly from “all single-\(\Phi'\)-extraction routes of the key power” to every provenance, matching EFF.T4.08.

**CONDITIONALITY:** \(j<\mu_2\).

**RESOLUTION TRACE:** base S1 DEFINITION T4.1, with the paragraph beginning “Equivalently, \(\omega_j\) is” replaced in full by R3-G1. The base wording (“obtained from all single-\(\Phi'\)-extraction routes of the key power, after every collision and cancellation in the canonical composed grid”) is `[SUPERSEDED]`.

**TEETH:** S8 PE1(1); PE1(5); the whole battery.

---

### EFF.T4.11  [fence]

**CANONICAL STATEMENT:**

> “This is the certificate reading pinned by GENTOW-3’s GT3-r2 repair. It is deliberately stronger than either of the following informal readings:
>
> - \(\operatorname{Sh}C_j(\Phi_2^{\mu_2})\ne0\);
> - some unassembled single-extraction branch is nonzero.
>
> A shadow coordinate may be nonzero while its height-\(\Theta_j\) digit cancels. FR-M3 at \(j=0\) is the committed separator: the self-shadow has pin \(12\), but \(\Theta_0=10\) and \(\omega_0=0\).”

**DERIVATION:** `[RECORD + measured separator]` The separating instance is the committed FR-M3 measurement: self-shadow pin 12 against threshold \(\Theta_0=10\), so \(\operatorname{Sh}C_0\ne0\) while \(\omega_0=0\). The pin is GT3-r2, XREF X05 (`## S7.6 [GT3-r2] PE2 REPAIR RECORD:`).

**CONDITIONALITY:** none; this is a scope fence, not a theorem.

**RESOLUTION TRACE:** base S1 tail, lines 94–99; unchanged by r1–r5.

**TEETH:** S8 PE1(1); PE2 GT3 consumption (“specifically inspect FR-M3’s measured slack \([12,7,4]\) against \([10,7,4]\)”).

---

### EFF.T4.12  [definition]

**CANONICAL STATEMENT:**

> “For \(q\in\mathscr D_{\le\mu_2}\), define its first discrepancy
> height at coordinate \(j\) by
>
> \[
> \nu_j(q)
> :=
> \min\{m:\operatorname{gr}_m(\Delta_j(q))\ne0\},
> \]
>
> with the convention
>
> \[
> \min\varnothing:=+\infty.
> \]
>
> Thus \(\nu_j(q)=+\infty\) exactly when
> \(\Delta_j(q)\) is identically zero.”

**DERIVATION:** `[DEFINITIONAL — totalization]` R1-m1 is titled “totalize first-discrepancy height”: base T4.2(a) wrote \(\min\{m:\dots\}=\Theta_j\) with an ad-hoc prose escape for the identically-zero case (“or the discrepancy is identically zero”). The convention \(\min\varnothing:=+\infty\) makes the minimum total so the equivalence in T4.2(a) can be stated without a disjunction.

**CONDITIONALITY:** \(q\in\mathscr D_{\le\mu_2}\).

**RESOLUTION TRACE:** R1-m1, inserted “immediately before LEMMA T4.2”. New in r1; unchanged by r2–r5.

**TEETH:** S8 PE1(2).

---

### EFF.T4.13  [hypothesis]

**CANONICAL STATEMENT:**

> “> Assume the GENTOW-3 discrepancy floor on the member class
> > \(\mathfrak M\) (S0):
> >
> > \[
> > \operatorname{gr}_m(\Delta_j(f))=0
> > \qquad
> > \text{for every \(f\in\mathfrak M\), every \(j<\mu_2\), and
> > every \(m<\Theta_j\).}
> > \tag{FLOOR}
> > \]”

followed by:

> “> Then, for each \(j<\mu_2\):”

**DERIVATION:** `[ASSUMED — with a named supplier]` (FLOOR) is T4's standing hypothesis, supplied by GENTOW-3(i). R5-F1 states the supplier cite exactly: “(FLOOR) on \(\mathfrak M\) is GENTOW-3(i) read at its Steps 0–2 quantification domain”, whose display is XREF X21 (`(i) [FLOOR] every dv2-height at which ShC_j and C_j carry` — different slot digits is \(\ge\Theta_j\)), “proved from \(\mathfrak M\)'s defining entry bound alone (Step 1, quoted above) with every discrepancy branch priced at \(+k\delta\), \(k\ge1\), above the source layer (Step 2); no disc hypothesis enters, and the S8.1 precedent quoted above licenses consuming Steps 0–2 at proof strength.”

**CONDITIONALITY:** the entire lemma is conditional on (FLOOR). The quantifier is now bound: every \(f\in\mathfrak M\), every \(j<\mu_2\), every \(m<\Theta_j\).

**RESOLUTION TRACE:** base S2 (“Assume the GENTOW-3 discrepancy floor … at each coordinate \(j\)”, unbound \(f\)) → R2-G1 (“for every member \(f\)”) → R5-F1 (“for every \(f\in\mathfrak M\)”). R5-F1 governs. R2-G1's own diagnosis is the title “bind the FLOOR variable”.

**TEETH:** S8 PE1(2) — “that T4.2(a) uses the GENTOW-3 floor and does not infer a member-general converse”.

---

### EFF.T4.14  [lemma]

**CANONICAL STATEMENT:**

> “**(a) Exact attainment for the key power.**
>
> \[
> j\text{ is touched}
> \quad\Longleftrightarrow\quad
> \nu_j(f_{\mathrm{key}})=\Theta_j.
> \]
>
> Thus a touched coordinate attains the GENTOW-3 floor exactly.
> At an untouched coordinate,
>
> \[
> \nu_j(f_{\mathrm{key}})>\Theta_j,
> \]
>
> where \(+\infty>\Theta_j\) includes the case of an identically
> zero discrepancy.”

**DERIVATION:** `[PROVED — three steps]` `[ASSEMBLED: R5-F1(1)'s rebound opening sentence + R2-G1's remainder; the seam is after “(FLOOR) specializes to”]`

> “Because \(f_{\mathrm{key}}\in\mathfrak M\) (S0, membership fact 1;
> no disc hypothesis is available or needed), (FLOOR) specializes to
>
> \[
> \operatorname{gr}_m
> \bigl(\Delta_j(f_{\mathrm{key}})\bigr)=0
> \qquad(m<\Theta_j).
> \]
>
> Hence
>
> \[
> \nu_j(f_{\mathrm{key}})\ge\Theta_j.
> \]
>
> Equality holds exactly when the height-\(\Theta_j\) assembled
> graded digit is nonzero. That digit is \(\omega_j\), so
>
> \[
> \nu_j(f_{\mathrm{key}})=\Theta_j
> \quad\Longleftrightarrow\quad
> \omega_j\ne0.
> \]
>
> This proves (a), including the identically-zero case through the
> convention \(\nu_j(f_{\mathrm{key}})=+\infty\).”

Step justifications: step 1 `by EFF.T4.13 + EFF.T4.05 membership fact 1`; step 2 `by EFF.T4.12` (definition of \(\nu_j\) as a minimum); step 3 `by EFF.T4.10` (the height-\(\Theta_j\) digit IS \(\omega_j\)) `+ EFF.T4.12`'s \(\min\varnothing=+\infty\) convention.

**CONDITIONALITY:** (FLOOR) on \(\mathfrak M\); \(j<\mu_2\). The statement is about the KEY POWER alone — see EFF.T4.40.

**RESOLUTION TRACE:** base T4.2(a) → R1-m1 (statement replaced, \(\nu_j\) form) → proof paragraph: base → R1-m1 → R2-G1 → R5-F1(1) rebinding. R1-m1 governs the statement; R2-G1-as-rebound-by-R5-F1(1) governs the proof.

**TEETH:** S8 PE1(2); PE2 GT3 consumption.

---

### EFF.T4.15  [lemma]

**CANONICAL STATEMENT:** `[ASSEMBLED: R2-G2's T4.2(b) with R5-F1(2)'s two rebinding replacements substituted in place — seams at “and suppose \(f\in\mathfrak M\)” and at “In particular, if \(g\) is in-budget …”]`

> “> **(b) Perturbation stability.** Let
> >
> > \[
> > g\in\mathscr D_{<\mu_2},
> > \qquad
> > f:=f_{\mathrm{key}}+g,
> > \]
> >
> > and suppose \(f\in\mathfrak M\) — a pure coefficient condition
> > (S0). If
> >
> > \[
> > \operatorname{gr}_{\Theta_j}(\Delta_j(g))=0,
> > \]
> >
> > then
> >
> > \[
> > \operatorname{gr}_{\Theta_j}(\Delta_j(f))=\omega_j.
> > \]
> >
> > In particular, if \(g\) is in-budget in pinned S8.1's box sense
> > (every composed slot of \(g\) clears weight \(\mu_2E_2+1\)),
> > then \(f=f_{\mathrm{key}}+g\in\mathfrak M\) by S0's membership
> > fact 2 — pure coefficient arithmetic, no disc condition implied
> > or needed — and S8.1's
> > repaired margin ledger places every discrepancy of \(g\) at
> > height at least \(\Theta_j+1\). Hence every touched coordinate
> > remains divergent exactly at \(\Theta_j\) under such an
> > in-budget perturbation.”

**DERIVATION:** `[PROVED — linearity + the repaired margin]` `[ASSEMBLED: R2-G2's proof paragraph with R5-F1(3)'s two rebinding replacements — seams at the opening sentence and at “(FLOOR), applied to \(f\in\mathfrak M\)”]`

> “Let \(g\in\mathscr D_{<\mu_2}\) and let
> \(f=f_{\mathrm{key}}+g\in\mathfrak M\). By the definitions in S0,
> \(C_j\) and \(\operatorname{Sh}C_j\) are linear maps on
> \(\mathscr D_{\le\mu_2}\); hence so is \(\Delta_j\). Therefore
>
> \[
> \Delta_j(f)
> =
> \Delta_j(f_{\mathrm{key}})+\Delta_j(g).
> \]
>
> Taking the height-\(\Theta_j\) graded component proves the first
> assertion of (b). Under GENTOW-3’s in-budget hypothesis, S8.1’s
> repaired ledger places every perturbation discrepancy at height
> at least \(\Theta_j+1\), so the required graded component of
> \(\Delta_j(g)\) vanishes. If \(j\) is touched, the resulting
> height-\(\Theta_j\) digit is \(\omega_j\ne0\); (FLOOR), applied
> to \(f\in\mathfrak M\), excludes every lower digit. Thus
> \(\nu_j(f)=\Theta_j\).”

Step justifications: linearity `by EFF.T4.06`; the \(\Theta_j+1\) margin `by XREF X09/X28` (GENTOW-3 S8.1's repaired ledger, `every disagreeing height of g's two reads is >= THETA_j + 1,`); membership of \(f\) `by EFF.T4.05 membership fact 2`; the lower-digit exclusion `by EFF.T4.13`.

**IMPORT FENCE:** the base's withdrawn “same shift” inference is NOT used — PE1(3) exists precisely to check this: “that T4.2(b) uses the repaired S8.1 margin, not the withdrawn “same shift” inference”. R5-F1 additionally quotes S8.1's own decoupling (XREF X31): the deep-perturbation parenthetical “(slots at heights > THETA_j)” is NOT consumed by the corrected derivation; “the box hypothesis is the” operative one.

**CONDITIONALITY:** \(g\in\mathscr D_{<\mu_2}\); \(f\in\mathfrak M\); \(\operatorname{gr}_{\Theta_j}(\Delta_j(g))=0\) — the in-budget case is a *specialization*, supplied by S8.1's box.

**RESOLUTION TRACE:** base T4.2(b) → R2-G2 (statement + proof replaced in full; R1-G2's proof-opening replacement is absorbed) → R5-F1(2), (3) (rebindings). R2-G2-as-rebound governs.

**TEETH:** S8 PE1(3); PE2 GT3 consumption.

---

### EFF.T4.16  [lemma]

**CANONICAL STATEMENT:**

> “> **(c) Fully exposed assembled-slot criterion.** Suppose a
> > canonical slot of coordinate \(j\) at height \(\Theta_j\) is
> > fully exposed by a single-extraction contribution whose
> > normalized digit is nonzero. Then that slot is a nonzero
> > component of \(\omega_j\). Consequently
> >
> > \[
> > \omega_j\ne0,
> > \]
> >
> > so \(j\) is touched and the floor is attained there.
> >
> > Uniqueness only among single-extraction contributions does not
> > discharge this premise: the exposure calculation must also
> > exclude every other term and every incoming carry or recarry
> > from the slot.”

**DERIVATION:** `[PROVED]`

> “For (c), full exposure says that, after complete propagation and
> assembly, the selected slot has exactly the displayed
> single-extraction contribution as its assembled value. No other
> branch term, carry, or recarry supplies a summand that could alter
> or cancel it. Its normalized digit is nonzero, so the selected
> slot is a nonzero component of the height-\(\Theta_j\) assembled
> graded digit. Distinct canonical slots are separate components;
> hence \(\omega_j\ne0\).”

Step justifications: full exposure `by EFF.T4.08`; “Distinct canonical slots are separate components” `by EFF.T4.07`; “the floor is attained there” `by EFF.T4.14`.

**CONDITIONALITY:** full exposure in the sense of EFF.T4.08 — an all-provenance premise, NOT single-extraction uniqueness. Ledger row HYP.113 records this as a live conditional-theorem leg.

**RESOLUTION TRACE:** base T4.2(c) (“Exposed-slot criterion … receives exactly one single-extraction contribution”) → R3-G1 replaces statement and proof in full. The base premise is `[SUPERSEDED]` as too weak.

**TEETH:** S8 PE1(5) as replaced by r3; PE2 GT6 consumption as replaced by r3.

---

### EFF.T4.17  [lemma]

**CANONICAL STATEMENT:**

> “> **(d) No-contribution criterion.** Suppose that, after every
> > branch term and every incoming carry and recarry has been
> > propagated to the canonical grid, no summand of any provenance
> > lands in any slot of coordinate \(j\) at height \(\Theta_j\) —
> > the single-\(\Phi'\)-extraction routes, all other branch terms,
> > and every incoming carry and recarry are excluded alike. Or
> > suppose the complete assembled contribution cancels. Then
> > \(\omega_j=0\).
> >
> > Absence of single-extraction sources alone does not discharge
> > the first hypothesis: the exclusion must cover every provenance
> > named in DEFINITION T4.1's assembly. No attainment statement
> > for another member follows: entry-driven content may still
> > attain \(\Theta_j\).”

**DERIVATION:** `[PROVED]`

> “Clause (d) is the definition after complete assembly, read under
> its all-provenance hypothesis: if no summand of any provenance
> lands in any height-\(\Theta_j\) slot of coordinate \(j\), the
> assembled graded digit is empty, and if the complete assembled
> contribution cancels, it is zero; in either case \(\omega_j=0\).
> Excluding single-extraction sources alone would leave the other
> branch terms and the incoming carries and recarries unaccounted,
> which is why the weaker hypothesis proves nothing. The final
> warning is necessary because \(\omega_j\) classifies the
> key-power witness, not all members of the genre.”

R4-G1's own diagnosis of why the strengthening was forced: “After r3, \(\omega_j\) assembles single-\(\Phi'\)-extraction routes, all other branch terms, and every incoming carry and recarry. Excluding single-extraction sources alone therefore no longer forces \(\omega_j=0\), and (FLOOR) supplies no such exclusion.” And why no consumer is harmed: “the instance records invoke (d) only through its cancellation leg (FR-M3's measured \(\omega_0=0\)) and its no-other-member warning, never through the no-source leg.”

**CONDITIONALITY:** all-provenance exclusion, or complete assembled cancellation. Ledger row HYP.114 records the provenance-exclusion fence.

**RESOLUTION TRACE:** base T4.2(d) (“No-source criterion … If no source monomial can undergo a single \(\Phi'\)-extraction …”) → R4-G1 replaces statement and the proof's clause-(d) sentences in full. The base's single-extraction hypothesis is `[SUPERSEDED]`; the clause now “claims strictly less than before”.

**TEETH:** S8 PE1(1); PE2 GT3 consumption (FR-M3 \(\omega_0=0\)); PE2 GT6 consumption (FAM-E/FAM-D no-overflow controls).

---

### EFF.T4.18  [instance-record]

**CANONICAL STATEMENT:** `[ASSEMBLED: base S3 with R5-F1's replacement of consumed fact 1 substituted in place]`

> “**Instance name:** `GT3-THRESHOLD`.
>
> **Substitution.**
>
> \[
> \Delta_j=\operatorname{Sh}C_j-C_j,\qquad
> \Theta_j=(\mu_2-j)E_2+\delta,
> \]
>
> with \(\delta=u_2-e_2D'h\), and with \(\omega_j\) the key power’s
> assembled single-\(\Phi'\)-extraction digit.
>
> **Consumed facts.**
>
> 1. GENTOW-3(i), read at its Steps 0–2 quantification domain
>    \(\mathfrak M\) (the S0 definition: the Step-1 entry bound is
>    the only membership fact the proof consumes, and pinned S8.1
>    consumes Steps 0–2 at proof strength on \(g\) itself), supplies
>    (FLOOR) on \(\mathfrak M\).
> 2. GENTOW-3(iv), read through GT3-r2 and GT3-r3, supplies the
>    per-genre, per-coordinate computation of \(\omega_j\).
> 3. GENTOW-3 S8.1 supplies the \(\Theta_j+1\) perturbation margin
>    used in LEMMA T4.2(b).
> 4. GENTOW-3(iii) gives the x-free extreme: every discrepancy is
>    zero, hence every \(\omega_j=0\).
>
> **Result.** GENTOW-3(iv)’s phrase “touched coordinate(s)” is exactly
> DEFINITION T4.1. Its attainment conclusion is LEMMA T4.2(a), and
> its repaired deep-perturbation persistence is LEMMA T4.2(b).”

**DERIVATION:** `[ABSORPTION]` The absorption is a substitution instance: GENTOW-3(iv)'s local vocabulary is replaced by EFF.T4.10 and its two inferences by EFF.T4.14 and EFF.T4.15. Consumed facts 1–4 are located by XREFs X01–X02 (GT3 span 1 for clauses (i), (iii), (iv)), X05–X06 (GT3-r2, GT3-r3), X09–X10 (S8.1's repaired ledger). Consumed fact 1's re-reading is R5-F1's supplier cite, itself resting on X21, X22, X26.

**NOTE — a residual wording seam.** The **Substitution** block still describes \(\omega_j\) as “the key power’s assembled single-\(\Phi'\)-extraction digit”, which is the pre-r3 provenance vocabulary; DEFINITION T4.1 (EFF.T4.10, r3 text) assembles every provenance. r3 did not list this line among its replacements. This is a wording seam, not a logical one — the governing definition of \(\omega_j\) is EFF.T4.10 — and it is recorded as OPEN-CALL 1 (§9).

**CONDITIONALITY:** (FLOOR) on \(\mathfrak M\); the pin stack of EFF.T4.21 resolving (fail-closed per EFF.T4.29).

**RESOLUTION TRACE:** base S3 (HTML-marker-delimited `<!-- T4-INSTANCE-GT3:BEGIN -->` … `:END -->`), with consumed fact 1 replaced by R5-F1.

**TEETH:** S8 PE2 GT3 consumption, in full.

---

### EFF.T4.19  [scope-record]

**CANONICAL STATEMENT:**

> “The instance is one-sided at member level. If \(\omega_j=0\), the
> key power does not attain the floor at \(j\); this does not imply
> that no other member can attain it. The committed FR-M3 \(W\)
> member does attain \(\Theta_0=10\) through entry-driven content
> although the key-power certificate at \(j=0\) cancels.”

**DERIVATION:** `[RECORD — measured]` The one-sidedness is EFF.T4.17's final warning; the exhibiting measurement is GENTOW-3's own S0 W-member row, XREF X24 (`f = Phi2³ + 2x·Phi2² + 8·Phi2 + 64 at FR-M3 j = 0 has first` — disagreeing height exactly \(10=\Theta_0\)).

**CONDITIONALITY:** none; a scope fence on the instance.

**RESOLUTION TRACE:** base S3; unchanged by r1–r5. R5-F1 confirms it survives the 𝔐 rebinding: “T4.2(d)'s warning and the S3 instance sentences about the W member's entry-driven attainment are true as written (the W member IS an element of \(\mathfrak M\), at the boundary).”

**TEETH:** S8 PE1(2); PE2 GT3 consumption (“the \(W\)-member’s entry-driven attainment at \(j=0\)”).

---

### EFF.T4.20  [regression-record]

**CANONICAL STATEMENT:**

> “**Measured configurations retained by this instance.**
>
> - **Attained:** FAM-A5/A7/B/C and FR-GL have \(\omega_j\ne0\) at
>   the recorded coordinates.
> - **Cancelled with slack:** FR-M3 has thresholds
>   \([10,7,4]\), self-shadow pins \([12,7,4]\), hence
>   \(\omega_0=0\) and \(\omega_1,\omega_2\ne0\).
> - **Identically zero:** FR5X supplies coordinates on which the
>   complete self-shadow coordinate vanishes.
> - **Other-member attainment at an untouched key-power
>   coordinate:** the FR-M3 \(W\) member has first discrepancy
>   \(10=\Theta_0\); this is compatible with T4.2(d).”

**DERIVATION:** `[INHERITED EVIDENCE]` These are GENTOW-3's own measurements, not T4 computations (EFF.T4.37's evidence fence). R4-G2's diagnosis records where two of them live and that they were originally OUTSIDE the pin stack: “FR-GL is recorded in GENTOW3 S7.1 (the adopted \(\eta\ne1\) machine row: corrected key, \(\Theta=(13,7)\), floor attained at both coordinates), which fell in the gap between span 1's END and span 2's BEGIN; FR5X is recorded in the post-PE5 dated acceptance record (PE5 obs-1: \(\mu_2=2\) pins \([61,\mathrm{None}]\), attained at \(\Theta_0=61\) with \(j=1\) identically zero; \(\mu_2=3\) pins \([91,61,\mathrm{None}]\) against \(\Theta=[87,61,35]\), slack at \(j=0\), attained at \(j=1\), identically zero at \(j=2\)), which fell after span 3's END. Neither claim was recoverable from the recorded stack.”

**CONDITIONALITY:** inherited-evidence status only (EFF.T4.37).

**RESOLUTION TRACE:** base S3; the *pins* covering it were repaired by R4-G2 (see EFF.T4.21). The listed configurations are unchanged: “no instance claim is widened.”

**TEETH:** S8 PE2 GT3 consumption, all four sub-checks.

---

### EFF.T4.21  [table]

**CANONICAL STATEMENT — the GT3 six-span semantic stack (R4-G2):**

> “**Marker-delimited source pins, HEAD.**
>
> Source:
> `GENTOW3_PROOF_2026-08-09.md`.
>
> The governing semantic stack is the ordered union of these
> half-open spans:”

`[TABLE]` (the note displays this as a numbered BEGIN/END list; transcribed as a table without reordering)

| # | BEGIN substring | END substring |
|---|---|---|
| 1 | `## S0. THE ONE CONSTANT AND THE THRESHOLD` | `## S3. COROLLARY GENTOW-3.C` |
| 2 | `### S7.1 THE DATED GAUGE ANNEX (F-1 repair): the corrected chat_t` | `### S7.2 (m-1 repair): the (iv) certificate's digit-value` |
| 3 | `## S7.6 [GT3-r2] PE2 REPAIR RECORD:` | `## S7.7 [GT3-r3] PE3 REPAIR RECORD:` |
| 4 | `## S7.7 [GT3-r3] PE3 REPAIR RECORD:` | `### Dated acceptance record` |
| 5 | `### Dated acceptance record` | `## S8. [GT3-r4] CODEX TOWERRAT2 RUN B REPAIRS` |
| 6 | `### S8.1 [B-F1, GAP] Clause (iv)'s deep-perturbation persistence:` | `### S8.2 [B-F2, GAP]` |

with the retained fence:

> “The later S8.2/S8.4 non-functionality scope is not consumed by
> this instance.”

**DERIVATION:** `[REPAIR — coverage gap]` R4-G2 added spans 2 and 5 because two instance claims were not recoverable from the r0 four-span stack (see EFF.T4.20's derivation). Its own justification of the fence's survival: “new span 5 is half-open at the S8 heading and consumes nothing of S8–S8.4, and span 6 is half-open at S8.2. New span 2 supplies the FR-GL configuration and the corrected-\(\widehat c_t\) gauge annex it sits in; new span 5 supplies the FR5X measurements and the arc's three measured certificate configurations.”

**CONDITIONALITY:** fail-closed per EFF.T4.29. All twelve markers verified at compile time: XREFs X01–X10, all count 1, all in `GENTOW3_PROOF_2026-08-09.md`, all in strictly increasing byte order within each span and across the stack.

**RESOLUTION TRACE:** base S3 four-span list → R4-G2 six-span replacement. R4-G2 governs.

**TEETH:** S8 PE1(7); PE2's re-resolution requirement.

---

### EFF.T4.22  [instance-record]

**CANONICAL STATEMENT:**

> “**Instance name:** `GT6-CERT-TOP`.
>
> ### S4.1 The sealed \(f_1=1,\ \mu_2=2\) instance
>
> Let
>
> \[
> T=\{t<f_2:\widehat c_t\ne0\},\qquad t^*=\max T,
> \]
>
> and write the lift monomial at \(t\) as
>
> \[
> \widehat c_t\,\pi^{a_t}x^{i_t}.
> \]
>
> Assume
>
> \[
> 2i_{t^*}\ge D'.
> \]
>
> The \((t^*,t^*)\) pair has a direct single-\(\Phi'\)-extraction
> into
>
> \[
> j^*=
> \left\lfloor
> \frac{2e_2t^*+1}{e_2f_2}
> \right\rfloor ,
> \qquad
> b^*=(2e_2t^*+1)\bmod e_2f_2,
> \qquad
> a^*=2i_{t^*}-D'.
> \]
>
> Its normalized digit is
>
> \[
> (\widehat c_{t^*})^2\pi^{2a_{t^*}}
> \cdot(\text{wrap unit}),
> \]
>
> which is nonzero.”

**DERIVATION:** `[IMPORTED — source-owned algebra]` The slot arithmetic (\(j^*,b^*,a^*\)) and the digit are GENTOW-6.3(b)'s own calculation, retained by the source per N-5. XREF X36 is 6.3(b)'s slot display (`> b* = (2e2t*+1) mod e2f2, a* = 2i_{t*} − D' — receives EXACTLY ONE`); XREF X38 is its unconditional nonvanishing (`A product of units in K2^x: nonzero — no`).

**CONDITIONALITY:** \(f_1=1\), \(\mu_2=2\), \(2i_{t^*}\ge D'\), \(T\ne\varnothing\) (implicit in \(t^*=\max T\)).

**RESOLUTION TRACE:** base S4.1 head, unchanged by r1–r5.

**TEETH:** S8 PE1(4), PE1(6); PE2 GT6 consumption.

---

### EFF.T4.23  [instance-record]

**CANONICAL STATEMENT — the r3 conditional invocation:**

> “Maximality of \(t^*\) excludes competing branches of the displayed
> pair type. To invoke T4.2(c), the CERT-TOP slot-isolation
> calculation must establish the stronger assembled-slot fact that,
> after every branch term and every incoming carry and recarry has
> been propagated, the displayed contribution is the sole summand
> in its canonical height-\(\Theta_{j^*}\) slot.
>
> When that source-owned calculation establishes this full
> exposure, the nonzero displayed digit gives
>
> \[
> \omega_{j^*}\ne0
> \]
>
> by T4.2(c). Hence \(j^*\) is touched and the discrepancy first
> occurs at
>
> \[
> \Theta_{j^*}=(2-j^*)E_2+\delta.
> \]
>
> If the pinned source span establishes uniqueness only among
> single-extraction branches, the premise of T4.2(c) is not
> discharged and `GT6-CERT-TOP` remains unresolved; neither FLOOR
> nor maximality alone supplies the missing exclusion.”

**WITHDRAWN TEXT (verified deleted).** The r0 sentence

> “This is GENTOW-6.3(b), CERT-TOP, as a literal exposed-slot instance
> of the certificate-witness lemma.”

is **WITHDRAWN** by R5-F2. Its reasoning, quoted: the sentence “survived r3's replacement span — which ended at the displayed \(\Theta_{j^*}\) formula, one sentence short — and asserts consumed-instance status on the pre-r3 "exposed-slot" (uniqueness-among-single-extractions) basis. That contradicts the r3 repair”.

**DERIVATION:** `[CONDITIONAL — premise discharged at f₁=1 by EFF.T4.41]` The conditional's antecedent is discharged, at the sealed scope only, by R5-63A (EFF.T4.41): GENTOW-6.3(a)'s whole-layer classification plus 6.3(b)'s slot uniqueness together give full exposure in the sense of EFF.T4.08. R5-F2's own closing sentence states the resulting status: “The governing status of the instance is the r3/r4 language — now resolved at the \(f_1=1\) scope, and only there, by R5-63A's consumption display below.”

**CONDITIONALITY:** full exposure (EFF.T4.08) at the CERT-TOP slot — discharged at \(f_1=1,\ \mu_2=2,\ 2i_{t^*}\ge D'\) and NOWHERE ELSE.

**RESOLUTION TRACE:** base S4.1 tail → R3-G1 replacement of “the paragraph beginning “Maximality of \(t^*\)” and ending with the displayed formula for \(\Theta_{j^*}\)” → R5-F2 deletion of the trailing r0 sentence. Antecedent discharged by R5-63A.

**TEETH:** S8 PE1(5); PE2 GT6 consumption (r3 wording).

---

### EFF.T4.24  [scope-record]

**CANONICAL STATEMENT:**

> “If
>
> \[
> i_t+i_{t'}<D'
> \qquad\text{for every }(t,t')\in T^2,
> \]
>
> there is no overflowing pair. GENTOW-6.3(c) proves the stronger
> conclusion \(\operatorname{Sh}C_j=C_j=0\) for every \(j\), hence
> every coordinate is untouched. Between these regimes, an
> assembled pair sum can vanish; no universal non-cancellation is
> asserted.”

**DERIVATION:** `[IMPORTED]` GENTOW-6.3(c) is a closed clause of the validated GT6 span 1 (XREFs X11–X12). The untouchedness conclusion follows because \(\Delta_j\equiv0\), so \(\omega_j=0\) by EFF.T4.10 — the STRONGER source conclusion is quoted rather than routed through EFF.T4.17's no-contribution leg.

**CONDITIONALITY:** the no-overflowing-pair hypothesis. The between-regimes non-assertion is the standing fence (see also EFF.T4.35 and ledger row HYP.71).

**RESOLUTION TRACE:** base S4.1 tail; unchanged by r1–r5.

**TEETH:** S8 PE2 GT6 consumption (“the no-overflow FAM-E/FAM-D controls”).

---

### EFF.T4.25  [instance-record]

**CANONICAL STATEMENT:**

> “### S4.2 The corrected-lift \(f_1\)-general instance
>
> For
>
> \[
> L_{m_t}(c_t\eta^{W(t)})
> =
> \sum_{r<f_1}
> \widetilde\lambda_{t,r}\,
> \pi^{a_t-rh}x^{i_t+e_1r},
> \]
>
> put
>
> \[
> I_t=i_t+e_1r_{\max}(t).
> \]
>
> Under
>
> \[
> 2I_{t^*}\ge D',
> \]
>
> ANNEX-THEOREM GENTOW-6.3′ isolates the unique top-monomial slot
>
> \[
> (a^*,b^*)
> =
> \left(
> 2I_{t^*}-D',
> \ (2e_2t^*+1)\bmod e_2f_2
> \right)
> \]
>
> in coordinate \(j^*\), with digit
>
> \[
> \widetilde\lambda_{t^*,r^*}^{\,2}
> \pi^{2(a_{t^*}-r^*h)}
> \cdot(\text{wrap unit}),
> \qquad r^*=r_{\max}(t^*).
> \]”

with the r3 replacement of its inference:

> “It is nonzero. The annex may invoke T4.2(c) only when its
> slot-isolation calculation proves that this contribution is fully
> exposed in the assembled-slot sense of S0: no other branch term
> and no incoming carry or recarry lands in the same canonical
> height-\(\Theta_{j^*}\) slot. Under that premise,
>
> \[
> \omega_{j^*}\ne0.
> \]
>
> Uniqueness only among top-monomial or single-extraction candidates
> does not suffice. If the pinned annex proves only that weaker
> uniqueness, this invocation remains unresolved. At \(f_1=1\),
> \(I_t=i_t\) and the fully exposed case specializes to S4.1.”

**DERIVATION:** `[IMPORTED — annex-owned algebra; premise NOT discharged]` The slot isolation is GENTOW-6.3′'s, inside GT6 span 2 (XREFs X13–X14, the dated gauge annex). The exposure premise is explicitly left undischarged at \(f_1\ge2\): R5-63A's scope fence quotes the source's own scope pin (XREF X40, `> genre" reads AT f1 = 1, at the corrected chat_t. At f1 >= 2 the` — displays below “are NOT proved as written”) and concludes “S4.2's corrected-lift invocation (ANNEX 6.3′) still awaits ITS OWN full-exposure calculation”.

**CONDITIONALITY:** \(2I_{t^*}\ge D'\); full exposure in the sense of EFF.T4.08 — **NOT discharged at \(f_1\ge2\)** (ledger row HYP.113; residue home `GENTOW6-BOX-4`).

**RESOLUTION TRACE:** base S4.2, with “It is nonzero and uniquely exposed. Thus T4.2(c) again gives \(\omega_{j^*}\ne0\). At \(f_1=1\), \(I_t=i_t\) and this specializes to S4.1.” replaced in full by R3-G1.

**TEETH:** S8 PE1(4), PE1(5); PE2 GT6 consumption (“the corrected-lift \(f_1=2\) BOX-4 rows”).

---

### EFF.T4.26  [regression-record]

**CANONICAL STATEMENT:**

> “The dated GENTOW6-BOX-4 append supplies sealed-battery-grade
> machine contact for this corrected-lift instance at four
> \(f_1=2\), x-ful rows. It does not change the logical form of the
> instance or erase the source note’s prose-grade ledger for the
> annex derivation.”

**DERIVATION:** `[INHERITED EVIDENCE]` The append is GT6 span 5 (XREFs X17–X18). R4-C1 describes what the re-anchored span now covers: “the four x-ful \(f_1=2\) rows at sealed-battery grade, GREEN 265/0, certificate pins \(=\Theta_0\) exactly on the floor, and 6.3′'s derivation keeping the prose grade of the source arc — and excludes only the closing artifact-hash clause, which T4 does not consume.”

**CONDITIONALITY:** battery-grade evidence, not theorem grade — the annex derivation retains its prose grade. Ledger row HYP.70: “Sealed-row ask is DISCHARGED at HEAD, GREEN 265/0 at four x-ful rows including f₁=2; only theorem-grade all-f₁≥2 widening remains unsealed.”

**RESOLUTION TRACE:** base S4.2 tail; unchanged textually, but the span that pins it was re-anchored by R4-C1 (see EFF.T4.28 and EFF.T4.30).

**TEETH:** S8 PE2 GT6 consumption.

---

### EFF.T4.27  [non-instance]

**CANONICAL STATEMENT:**

> “### S4.3 The later \(\mu_2\ge3\) candidate
>
> GENTOW-6.5’s \(f_1=1\) refinement computes a distinguished
> single-extraction contribution proportional to
>
> \[
> \binom{\mu_2}{2}
> (\widehat c_{t^*})^2\pi^{2a_{t^*}}
> \cdot(\text{wrap unit}).
> \tag{6.5-CAND}
> \]
>
> The source facts consumed by this record do not prove that the
> canonical slot containing \((6.5\text{-CAND})\) receives exactly
> one single-extraction contribution. They therefore do not
> establish the exposed-slot premise of T4.2(c).
>
> Accordingly, even when the residue characteristic does not divide
> \(\binom{\mu_2}{2}\), the displayed nonzero expression is recorded
> here only as an unassembled candidate witness. This instance does
> not infer that \(\omega_j\ne0\), does not assert that \(j\) is
> touched, and does not assert threshold attainment from
> \((6.5\text{-CAND})\).
>
> If a later source rider proves that this contribution is uniquely
> exposed, that new assertion must be covered by an explicit pin
> update and fresh validation before T4.2(c) may be invoked. Proof
> that an expression is the complete assembled value of a slot
> would prove touchedness directly when that value is nonzero, but
> it is not equivalent to proving that the slot received exactly
> one contribution: additional contributions may be present and
> sum to zero.
>
> No converse is retained. Vanishing or cancellation of this
> candidate does not imply \(\omega_j=0\), because another canonical
> slot may attain the same coordinate’s floor. The committed BP3
> and FR5X measurements remain source measurements of the possible
> outcomes; they are not exposed-slot instances supplied by this
> record.”

**DERIVATION:** `[SIGNED NON-INSTANCE]` R2-G3 is titled “downgrade GENTOW-6.5 from instance to candidate” and closes: “This also repairs the minor false-equivalence claim: the new text states only the valid one-way implication and explicitly rejects its converse.” The reason it is a non-instance is the absent exposure premise, not a defect in the binomial computation.

**SUPERSEDED PREDECESSOR.** R1-G1's S4.3 (an instance-under-`(EXPOSE-6.5)`) is `[SUPERSEDED]` in full by R2-G3; the tag `(EXPOSE-6.5)` does not occur in the effective text.

**CONDITIONALITY:** \(\mu_2\ge3\), \(f_1=1\); residue characteristic not dividing \(\binom{\mu_2}{2}\) makes the *displayed expression* nonzero, which is NOT touchedness. Ledger row HYP.112 records the consumption ban.

**RESOLUTION TRACE:** base S4.3 → R1-G1 (full replacement) → R2-G3 (full replacement). R2-G3 governs.

**TEETH:** S8 PE1(6); PE2 GT6 consumption (“Check the BP3 and FR5X higher-\(\mu_2\) rows against the one-sided binomial statement”).

---

### EFF.T4.28  [table]

**CANONICAL STATEMENT — the GT6 five-span semantic stack (R5-m2):**

> “**Marker-delimited source pins, HEAD.**
>
> Source:
> `GENTOW6_PROOF_2026-08-09.md`.
>
> The governing semantic stack is the ordered union of these spans:”

`[TABLE]`

| # | BEGIN substring | END substring |
|---|---|---|
| 1 | `## S3. THEOREM GENTOW-6.3` | `## S4. MACHINE LEG` |
| 2 | `### S6.1 THE DATED GAUGE ANNEX` | `### S6.2 THE 𝒯-FREE CAP LEMMA` |
| 3 | `### S6.2 THE 𝒯-FREE CAP LEMMA` | `> (b) [BAND-1 CAP, 𝒯-FREE] across ambient window-N lifts of f:` |
| 4 | `**GENTOW6-BOX-1 (mu2 >= 3 attainment): CLOSED AT f1 = 1**` | `**GENTOW6-BOX-4 (the f1 >= 2 x-ful-digit sealed battery row):` |
| 5 | `**GENTOW6-BOX-4 (the f1 >= 2 x-ful-digit sealed battery row):` | `output md5 2d8d617a, verdict commit follows this append.` |

**DERIVATION:** `[REPAIR — one reversal, one addition]` Two independent defects were fixed.

R4-C1 (CRITICAL) re-anchored the BOX-4 span, its byte-literal diagnosis quoted: “in `GENTOW6_PROOF_2026-08-09.md` the r0 span-4 END substring `6.3' keeps its prose-only grading in the note's own terms.` occurs exactly once — at line 673 (byte 38211), inside the S5 acceptance-fold bracket — while the span-4 BEGIN substring occurs exactly once at line 1249 (byte 70410), in the final dated append. BEGIN does not precede END, S5 condition 3 fails, and the BOX-4 span — hence `GT6-CERT-TOP` — correctly failed closed.” The new END is the source's final line. Independently re-verified at compile time (XREF X19: the retired END at line 673, byte 38211; XREF X17 BEGIN at line 1249, byte 70410 — the reversal is real).

R5-m2 added span 3 because “LEMMA GENTOW-6.4 lies outside the r0–r4 GT6 stack (old span 2 is half-open AT the S6.2 heading)”, and the 𝒜_j definition needs 6.4(a)'s grid display. Its scope: “New span 3 covers the 𝒯-free triangularity paragraph and LEMMA GENTOW-6.4's head and clause (a) with its codomain rider; it is half-open at clause (b), which is not consumed.”

**CONDITIONALITY:** fail-closed per EFF.T4.29. All eight markers verified at compile time: XREFs X11–X18, all count 1, all in `GENTOW6_PROOF_2026-08-09.md`, byte order \(19136<29718<39709<47646<51652<67667<70410<71408\).

**RESOLUTION TRACE:** base S4 four-span list → R4-C1 (span 4 END re-anchored) → R5-m2 (five-span replacement). R5-m2 governs.

**TEETH:** S8 PE1(7); PE2's re-resolution requirement.

---

### EFF.T4.29  [fence]

**CANONICAL STATEMENT:**

> “Every pin above is interpreted byte-literally against the named
> source at the revision being consumed.
>
> A pin resolves only if:
>
> 1. its BEGIN substring occurs exactly once;
> 2. its END substring occurs exactly once;
> 3. BEGIN precedes END;
> 4. the resolved span belongs to the named source;
> 5. the spans in one semantic stack occur in the recorded order;
> 6. no later dated rider or append inside or after the pinned stack
>    supersedes a consumed assertion.
>
> If any condition fails, the instance is **UNRESOLVED** and
> consumption stops. The orchestrator must not substitute a nearby
> heading, normalize punctuation, choose among multiple matches, or
> fall back to an earlier revision. A source edit that changes,
> duplicates, removes, or reorders a marker therefore fails closed
> and requires an explicit T4 pin update plus re-verification.
>
> The HTML instance markers in this note delimit the complete
> consumer records. They are not substitutes for validation of the
> source markers.”

**DERIVATION:** `[DEFINITIONAL — the note's consumption protocol]` Not derived; it is the fail-closed convention T4 imposes on every consumer. Ledger row HYP.115 records it (“Missing or mismatched pins fail closed”, CONSUMED BY: all T4 imported premises). Its bite is demonstrated by R4-C1: condition 3 genuinely failed at HEAD and the instance correctly failed closed.

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** base S5; unchanged by r1–r5. (R1-C1 inserted S5.1 *after* the numbered conditions; the conditions themselves were never touched.)

**TEETH:** S8 PE1(7); PE2 (“re-resolve every pin”).

---

### EFF.T4.30  [table]

**CANONICAL STATEMENT — S5.1, the governing pin-validation record for the pre-r5 stacks:**

> “### S5.1 R4 PIN-VALIDATION RECORD (2026-08-12)
>
> On 2026-08-12 the r4 round executed the byte-literal validation
> that the R1 and R2 attempts could not run. Every BEGIN and END
> substring of the post-r4 pin lists was matched literally
> (`grep -F`) against its named HEAD source. Occurrence counts,
> 1-based line numbers, and 0-based byte offsets:”

`[TABLE]` Source `GENTOW3_PROOF_2026-08-09.md` (1,041 lines) — the GT3 stack of six spans:

| marker (role) | count | line | byte |
|---|---|---|---|
| `## S0. THE ONE CONSTANT AND THE THRESHOLD` (1-BEGIN) | 1 | 74 | 3886 |
| `## S3. COROLLARY GENTOW-3.C` (1-END) | 1 | 317 | 17886 |
| `### S7.1 THE DATED GAUGE ANNEX (F-1 repair): the corrected chat_t` (2-BEGIN) | 1 | 504 | 28156 |
| `### S7.2 (m-1 repair): the (iv) certificate's digit-value` (2-END) | 1 | 610 | 33968 |
| `## S7.6 [GT3-r2] PE2 REPAIR RECORD:` (3-BEGIN) | 1 | 680 | 37757 |
| `## S7.7 [GT3-r3] PE3 REPAIR RECORD:` (3-END, 4-BEGIN) | 1 | 763 | 42380 |
| `### Dated acceptance record` (4-END, 5-BEGIN) | 1 | 817 | 45302 |
| `## S8. [GT3-r4] CODEX TOWERRAT2 RUN B REPAIRS` (5-END) | 1 | 880 | 48739 |
| `### S8.1 [B-F1, GAP] Clause (iv)'s deep-perturbation persistence:` (6-BEGIN) | 1 | 894 | 49488 |
| `### S8.2 [B-F2, GAP]` (6-END) | 1 | 941 | 52157 |

`[TABLE]` Source `GENTOW6_PROOF_2026-08-09.md` (1,265 lines) — the GT6 stack of four spans (r4 state; superseded as a *stack* by R5-m2's five spans, but every row below still holds):

| marker (role) | count | line | byte |
|---|---|---|---|
| `## S3. THEOREM GENTOW-6.3` (1-BEGIN) | 1 | 344 | 19136 |
| `## S4. MACHINE LEG` (1-END) | 1 | 529 | 29718 |
| `### S6.1 THE DATED GAUGE ANNEX` (2-BEGIN) | 1 | 702 | 39709 |
| `### S6.2 THE 𝒯-FREE CAP LEMMA` (2-END) | 1 | 851 | 47646 |
| `**GENTOW6-BOX-1 (mu2 >= 3 attainment): CLOSED AT f1 = 1**` (3-BEGIN) | 1 | 1204 | 67667 |
| `**GENTOW6-BOX-4 (the f1 >= 2 x-ful-digit sealed battery row):` (3-END, 4-BEGIN) | 1 | 1249 | 70410 |
| `output md5 2d8d617a, verdict commit follows this append.` (4-END) | 1 | 1265 | 71408 |

with the conditions check and rider audit:

> “Every count is exactly 1 (S5 conditions 1–2); every match lies in
> its named source (condition 4); within each pair the BEGIN byte
> offset strictly precedes the END byte offset, and each stack's
> spans occur in the recorded byte order (conditions 3 and 5). The
> retired r0 GT6 span-4 END substring `6.3' keeps its prose-only
> grading in the note's own terms.` occurs once at line 673 (byte
> 38211), before the span-4 BEGIN at byte 70410 — the reversal this
> record retires.”

> “Rider audit (condition 6), for the spans r4 adds or repairs. GT3
> spans 2 and 5: the dated appends after them are S8 (GT3-r4) and
> S8.4 (GT3-r5, 2026-08-12); S8.4 fences itself — "This correction
> changes only S8.2's non-functionality scope" — and no sentence of
> S8–S8.4 supersedes the S7.1 FR-GL row or the acceptance record's
> FR5X measurements. GT6 span 4: nothing follows its END, which is
> the source's final line. For the five pairs r4 does not touch,
> the T4P4 audit found unique, correctly ordered markers and raised
> no supersession finding.”

**DERIVATION:** `[MACHINE RECORD — independently re-verified]` **Compile-time re-verification (2026-08-14):** every row above was re-run against the working tree with fixed-string matching; all counts are 1 and every line and byte offset matches exactly. Source sizes also match the record: `GENTOW3_PROOF_2026-08-09.md` = 1,041 lines / 57,484 bytes; `GENTOW6_PROOF_2026-08-09.md` = 1,265 lines / 71,465 bytes.

**CONDITIONALITY:** “It is a pin-validation result, not hostile-pass credit: …”

**RESOLUTION TRACE:** R1-C1 S5.1 (UNRESOLVED, `bubblewrap is unavailable`) → R2-C1 S5.1 (UNRESOLVED, same blocker) → R4-C1 S5.1 (VALIDATED). R4-C1 governs; both predecessors are `[SUPERSEDED]` and explicitly so (“This record supersedes the R1 and R2 pin-validation records.”).

**TEETH:** S8 PE1(7).

---

### EFF.T4.31  [table]

**CANONICAL STATEMENT — R5-V, the r5 addendum validation record:**

> “Every quote displayed in a fenced block above and every marker of
> the new span was matched byte-literally (fixed-string) against its
> named HEAD source. Occurrence counts, 1-based lines, 0-based byte
> offsets:”

`[TABLE]` Source `GENTOW3_PROOF_2026-08-09.md`:

| quote (role) | count | line | byte |
|---|---|---|---|
| `member f ∈ 𝒯, per composed coordinate j < mu2:` (S2 setting) | 1 | 164 | 8952 |
| `(i) [FLOOR] every dv2-height at which ShC_j and C_j carry` ((i) display) | 1 | 189 | 10420 |
| `On 𝒯 the entry pins lie weakly above the inner side:` (Step 1 = \(\mathfrak M\)'s consumption) | 1 | 230 | 12643 |
| `f = Phi2^{mu2} has composed read DRAIN (C_j = 0) while its shadow` ((iv) at the key power) | 1 | 204 | 11313 |
| `f = Phi2³ + 2x·Phi2² + 8·Phi2 + 64 at FR-M3 j = 0 has first` (S0's W member) | 1 | 93 | 4921 |
| `(g in-budget with slots at heights > THETA_j, disc ≠ 0): both` ((iv) σ-leg parenthetical) | 1 | 296 | 16733 |
| `The corrected derivation (this note's Steps 0-2, run on g).` (S8.1 proof-strength precedent) | 1 | 907 | 50145 |
| `"in-budget" at the GENTOW-1(a) box this corpus defines: every` (S8.1 box) | 1 | 908 | 50212 |
| `every disagreeing height of g's two reads is >= THETA_j + 1,` (S8.1 margin) | 1 | 923 | 51137 |
| `FR-M3 W member's g_W = 2x*Phi2^2 + 8*Phi2 has slot weights 9, 9 <` (S8.1 boundary) | 1 | 932 | 51697 |
| `10 = mu2*E2 + 1 — OUTSIDE the box — and its discrepancy lands at` (S8.1 boundary) | 1 | 933 | 51763 |
| `consumed by the corrected derivation; the box hypothesis is the` (S8.1 decoupling) | 1 | 938 | 52077 |

`[TABLE]` Source `GENTOW6_PROOF_2026-08-09.md`:

| quote (role) | count | line | byte |
|---|---|---|---|
| `THEOREM GENTOW-3(i) floors every discrepancy at` (S3 setting at the key power) | 1 | 371 | 20760 |
| `> (a) [SOURCE CLASSIFICATION] the height-THETA graded layer of the` (6.3(a) head) | 1 | 393 | 21910 |
| `> division/recarry step emits terms of Y-exponent LOWERED by` (6.3(a) downstream tracking) | 1 | 400 | 22379 |
| `> Multi-extraction branches sit at weight >= THETA + delta; tail` (6.3(a) close) | 1 | 402 | 22511 |
| `> b* = (2e2t*+1) mod e2f2, a* = 2i_{t*} − D' — receives EXACTLY ONE` (6.3(b) slot) | 1 | 408 | 22842 |
| `> equality iff zero steps and t + t' = 2t*: the (t*,t*) direct` (6.3(b) proof) | 1 | 469 | 26344 |
| `A product of units in K2^x: nonzero — no` (6.3(b) digit) | 1 | 475 | 26723 |
| `> lands at (a*, Y^{B*+1}) by the uniqueness just shown (branches` (6.3(b) proof close) | 1 | 480 | 27030 |
| `> genre" reads AT f1 = 1, at the corrected chat_t. At f1 >= 2 the` (GT6-r1 scope pin) | 1 | 382 | 21265 |
| `### S6.2 THE 𝒯-FREE CAP LEMMA` (span-2 END; NEW span-3 BEGIN) | 1 | 851 | 47646 |
| `> (b) [BAND-1 CAP, 𝒯-FREE] across ambient window-N lifts of f:` (NEW span-3 END) | 1 | 920 | 51652 |
| `> a < D', b < e2f2; slot degree jD2 + bD' + a; slot dv2-height` (6.4(a) grid) | 1 | 884 | 49514 |
| `> e1e2·v(c_{j,a,b}) + w(a,b), w(a,b) = a·e2h + b·u2). Then:` (6.4(a) heights) | 1 | 885 | 49577 |

with the containment and rider audit:

> “Every count is exactly 1 (S5 conditions 1–2); every match lies in
> its named source (condition 4). The post-r5 GT6 stack's markers
> occur in strictly increasing byte order
> \(19136<29718<39709<47646<51652<67667<70410<71408\), BEGIN
> preceding END in every pair (conditions 3 and 5); the S6.2 marker
> serves as span-2 END and span-3 BEGIN, as the GT3 stack already
> does with its shared markers. All quotes above lie inside their
> stacks' pinned spans; the S6.2-block quotes lie inside the NEW
> span 3 (bytes 47646–51652).”

> “Rider audit (condition 6), new span 3: the post-PE2 codomain rider
> sits INSIDE the span and corrects LEMMA GENTOW-6.4(a)'s
> bijection-codomain face (above-top slots forced to zero). r5
> consumes only the grid-and-height display, which the rider leaves
> intact and machine-confirms (its grid-census leg); the rider
> itself records that the bijection/count face "is consumed nowhere
> at HEAD", and this note keeps it that way. Nothing after the
> span's END touches 6.4(a)'s grid display (the later dated appends
> are the BOX records for 6.3-family content). For the pre-r5 spans,
> the R4 S5.1 record and the latest pass's 17/17 byte-verification
> govern; no new supersession was found against the quotes above.”

**DERIVATION:** `[MACHINE RECORD — independently re-verified]` **Compile-time re-verification (2026-08-14):** all 25 quotes re-run with fixed-string matching against the working tree; every count is 1 and every line and byte offset matches. These are XREFs X20–X31 (GT3) and X32–X42 plus X14–X15 (GT6).

**CONDITIONALITY:** “This record is a pin-validation and consumption result, not
hostile-pass credit: the acceptance counter stays 0/2.”

**RESOLUTION TRACE:** R5-V; new in r5, coexisting with (not replacing) EFF.T4.30 — “the R4 S5.1 record continues to govern the pre-r5 stacks.”

**TEETH:** S8 PE1(7).

---

### EFF.T4.32  [scope-record]

**CANONICAL STATEMENT:**

> “After T4 is accepted, the following local arguments may be
> shortened to instance records:
>
> - GENTOW-3’s local definition of “touched coordinate(s)” and its
>   floor-attainment inference become `GT3-THRESHOLD`;
> - GENTOW-6.3(b)’s final implication from the fully exposed
>   assembled CERT-TOP slot to threshold attainment becomes
>   `GT6-CERT-TOP`;
> - GENTOW-6.3′ uses the same exposed-slot clause within its recorded
>   corrected-lift scope;
> - the later \(\mu_2\ge3\) computation is not consumable through
>   T4.2(c): it remains the candidate record of S4.3 unless a
>   separately pinned and validated source assertion proves the
>   required exposure premise.”

**DERIVATION:** `[SCOPE RECORD]` The compression list is the protocol-side statement of the absorption set; the third and fourth bullets are the split of a single r0 bullet by R2-G3, and the second bullet's “fully exposed assembled” wording is R4-m1's upgrade of “unique”. R4-m1's justification: “This brings S6's compression instructions to the same assembled-slot standard r3 imposed on T4.2(c), S4.1/S4.2, and S8.”

**CONDITIONALITY:** “After T4 is accepted” — now satisfied (EFF.T4.45); the *consumption checks and appends* remain outstanding (scope split B).

**RESOLUTION TRACE:** base S6 three-bullet list → R2-G3 (third bullet split into two) → R4-m1 (second bullet reworded). Both later edits govern; the base's “GENTOW-6.3′ and the later \(\mu_2\ge3\) certificate computation use the same exposed-slot clause with their recorded scopes.” is `[SUPERSEDED]`.

**TEETH:** S8 PE1(4); PE2 both consumption checks.

---

### EFF.T4.33  [fence]

**CANONICAL STATEMENT:**

> “The algebra that computes a proposed witness is not deleted:
> GENTOW-6 still owns the complete assembled-slot exposure
> calculation — the exclusion, in S0's full-exposure sense, of
> every other branch term and every incoming carry and recarry
> from the slot, not merely uniqueness among single-extraction
> branches — together with the corrected-lift support calculation
> and the higher-\(\mu_2\) binomial coefficient.”

> “T4 owns only the shared meaning of the
> assembled witness and the inference from a nonzero critical digit
> to attainment.”

> “No accepted source is rewritten by this composition unit. The
> orchestrator’s later consumption update must preserve the frozen
> source notes through dated references or brackets.”

**DERIVATION:** `[FENCE]` This is the ownership boundary that makes the compression honest: T4 supplies the *definition and the inference*, the sources retain the *computation*. See NON-IMPORTS N-5, N-7.

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** base S6 tail, first paragraph replaced by R4-m1; the remaining two paragraphs unchanged.

**TEETH:** S8 PE1(5); PE2 GT6 consumption.

---

### EFF.T4.34  [record]

**CANONICAL STATEMENT:**

> “**Delivered here.**
>
> - One canonical definition of touched coordinate in the
>   certificate sense.
> - One attainment lemma, including the repaired perturbation
>   margin and the exposed-slot test.
> - Two source-scoped instance records.
> - Fail-closed, marker-delimited source pins.
> - A single home for later certificate and count refinements.”

**DERIVATION:** `[RECORD]` The five deliverables map onto EFF.T4.10 · EFF.T4.14–.17 · EFF.T4.18 and EFF.T4.22–.26 · EFF.T4.21, .28, .29 · EFF.T4.36. This is the note's own supply set (scope split A).

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** base S7; unchanged by r1–r5.

**TEETH:** the whole battery.

---

### EFF.T4.35  [fence]

**CANONICAL STATEMENT:**

> “**Not claimed.**
>
> - No genre-general non-vanishing theorem beyond the hypotheses
>   already proved in GENTOW-6.
> - No converse to CERT-TOP.
> - No claim that an untouched key-power coordinate cannot be
>   reached by another member.
> - No claim that \(\operatorname{Sh}C_j\ne0\) implies touchedness.
> - No promotion of GENTOW-6.3’s sealed \(f_1=1\) statement to
>   \(f_1\ge2\); that scope remains the corrected-lift annex.
> - No promotion of the \(\mu_2\ge3\) sufficient condition to an
>   iff.
> - No closure of entry-driven regime classification.
> - No new count theorem.”

**DERIVATION:** `[FENCE]` Each item is the negative face of a positive unit: item 1 ↔ EFF.T4.24 and ledger row HYP.71; item 2 ↔ EFF.T4.16 (one-way only); item 3 ↔ EFF.T4.17, .19; item 4 ↔ EFF.T4.11; item 5 ↔ EFF.T4.25 and the R5-63A fence (EFF.T4.42); item 6 ↔ EFF.T4.27; items 7–8 ↔ EFF.T4.36's `GENTOW6-BOX-2`, `GENTOW6-BOX-3`.

**CONDITIONALITY:** none — this is the note's headline non-claim list and survives acceptance unchanged (“Standing fences unchanged and displayed”, EFF.T4.45).

**RESOLUTION TRACE:** base S7; unchanged by r1–r5. Note that r2's downgrade (EFF.T4.27) makes item 6 *stronger* than at r0: the μ₂ ≥ 3 condition is now not even a certified sufficient condition for touchedness, only a candidate.

**TEETH:** S8 PE1(2), PE1(4), PE1(6).

---

### EFF.T4.36  [record]

**CANONICAL STATEMENT:**

> “**Residue home.**
>
> - `GENTOW6-BOX-1`: lower-coordinate and compound
>   \(f_1\ge2,\mu_2\ge3\) certificate classification.
> - `GENTOW6-BOX-2`: the partial-side product-measure count ledger.
> - `GENTOW6-BOX-3`: entry-driven and non-top-overflow
>   classification.
> - `GENTOW6-BOX-4`: its stated sealed-row ask is discharged at
>   HEAD, but any widening of corrected-lift certificate coverage
>   belongs here.
> - `GENTOW3-BOX-1`: the original genre-general non-cancellation ask
>   is replaced, not magically solved, by the explicit witness
>   \(\omega_j\); deciding its vanishing outside the proved
>   CERT-TOP regimes remains refinement work.”

**DERIVATION:** `[RECORD]` The five box names are verified in their sources: XREFs X43–X47. Downstream, `spec/HYPOTHESIS_LEDGER.md` carries all five as rows HYP.67–HYP.71 with `WHERE: T4 §S7` (reverse-XREFs RX49–RX53).

**CONDITIONALITY:** these are open residues, not claims.

**RESOLUTION TRACE:** base S7; unchanged by r1–r5.

**TEETH:** S8 PE1(4), PE1(6).

**RECONCILIATION FLAG:** the ledger records one omission from this list — HYP.116, `GENTOW3-BOX-2`, “WHERE: upstream GENTOW3; **T4 residue-home omission**”. See §8 item 3.

---

### EFF.T4.37  [record]

**CANONICAL STATEMENT:**

> “**Evidence status.** This note adds no machine computation. Its
> regression evidence is inherited from the byte-frozen GENTOW-3
> and GENTOW-6 artifacts and their dated hostile-arc instruments.
> Those artifacts support the two instance checks; they are not
> fresh evidence for a stronger theorem.”

and the (now historical) grade line:

> “**GRADE: 0/2 (attempt).** The definition and lemma are new
> composition text. Two consecutive clean hostile passes are
> required before acceptance.”

**DERIVATION:** `[RECORD]` The evidence fence is the reason every EFF unit above marked `[INHERITED EVIDENCE]` is so marked. Ledger row HYP.109 carries it downstream verbatim in substance: “T4 adds no fresh machine computation.”

**CONDITIONALITY:** the evidence clause stands at HEAD; the GRADE line is `[SUPERSEDED]` by EFF.T4.45.

**RESOLUTION TRACE:** base S7 tail; evidence clause unchanged by r1–r5; grade line superseded by the acceptance record (and, en route, by each round's “The acceptance counter remains 0/2”).

**TEETH:** the acceptance/evidence fence, §7.

---

### EFF.T4.38  [battery-frame]

**CANONICAL STATEMENT — PE1, statement and scope attack:**

> “The first adversarial pass must check:
>
> 1. that \(\operatorname{gr}_{\Theta_j}\) is taken after complete
>    slot assembly and cancellation;
> 2. that T4.2(a) uses the GENTOW-3 floor and does not infer a
>    member-general converse;
> 3. that T4.2(b) uses the repaired S8.1 margin, not the withdrawn
>    “same shift” inference;
> 4. that the \(f_1=1\), corrected-lift \(f_1\)-general, and
>    \(\mu_2\ge3\) scopes remain separated;
> 5. that CERT-TOP is invoked through T4.2(c) only after the source
>    calculation excludes every other assembled-slot input,
>    including other terms and incoming carries and recarries;
> 6. that the higher-\(\mu_2\) binomial condition is not stated as
>    necessary;
> 7. that every marker pin resolves uniquely and in order.
>
> A finding of GAP or CRITICAL resets the counter to 0/2. Repairs
> must be re-derived from the pinned source spans.”

**DERIVATION:** `[BATTERY FRAME]` Item 5 is r3's replacement of the r0 wording (“that CERT-TOP is used as a sufficient exposed-slot witness”), aligning the battery with EFF.T4.08/.16. The reset rule is what made every round's counter return to 0/2.

**CONDITIONALITY:** none.

**RESOLUTION TRACE:** base S8 PE1, item 5 replaced by R3-G1.

**TEETH:** this IS the battery; see the inverse inventory §6.

---

### EFF.T4.39  [battery-frame]

**CANONICAL STATEMENT — PE2, independent consumption and regression attack.** `[ASSEMBLED: base S8 PE2 with R3-G1's replacement of the GT6 first sentence substituted in place]`

> “After a clean PE1, the second pass must re-resolve every pin and
> perform two consumption checks:
>
> - **GT3 consumption:** recover GENTOW-3(iv)’s certificate-scoped
>   attainment and S8.1 persistence solely by substituting
>   DEFINITION T4.1 and LEMMA T4.2. Re-run the accepted GENTOW-3
>   battery and specifically inspect FR-M3’s measured slack
>   \([12,7,4]\) against \([10,7,4]\), the \(W\)-member’s
>   entry-driven attainment at \(j=0\), FR-GL’s two-coordinate
>   attainment, and FR5X’s identically-zero coordinates.
>
> - **GT6 consumption:** recover CERT-TOP solely through T4.2(c)
>   after retaining GENTOW-6’s complete assembled-slot exposure
>   calculation. Uniqueness only among single-extraction branches
>   does not count as consumption of T4.2(c).
>   Re-run the accepted GENTOW-6 battery, the corrected-lift
>   \(f_1=2\) BOX-4 rows, the gauge-live \(\eta\ne1\) rows, and the
>   no-overflow FAM-E/FAM-D controls. Check the BP3 and FR5X
>   higher-\(\mu_2\) rows against the one-sided binomial statement.
>
> Acceptance requires PE1 CLEAN followed by PE2 CLEAN. Minor-only
> riders may be folded without changing the theorem statement;
> anything that changes the meaning of touchedness, the threshold
> layer, or an instance scope requires a new repair round and
> restarts the two-clean counter.”

**DERIVATION:** `[BATTERY FRAME]` The GT6 first sentence is r3's replacement (“after retaining GENTOW-6’s complete assembled-slot exposure calculation. Uniqueness only among single-extraction branches does not count as consumption of T4.2(c).”), superseding r0's “after retaining GENTOW-6’s source-slot uniqueness calculation.”

**CONDITIONALITY:** the minors-only folding clause is what licensed folding the post-pass rider (EFF.T4.44) without a grade event.

**RESOLUTION TRACE:** base S8 PE2, GT6 first sentence replaced by R3-G1.

**TEETH:** this IS the battery; see §6.

---

### EFF.T4.40  [acceptance-box]

**CANONICAL STATEMENT — the composition record's boxed compression, as replaced by R5-m1:**

> “**Composition record, 2026-08-12.** T4 makes no source-file edit
> and no artifact edit. Its sole mathematical compression is:”
>
> \[
> \boxed{
> \text{touched at }j
> \;:\Longleftrightarrow\;
> \omega_j\ne0
> \;\Longleftrightarrow\;
> \nu_j(f_{\mathrm{key}})=\Theta_j
> }
> \]
>
> “The first equivalence is DEFINITION T4.1; the second is LEMMA
> T4.2(a) under (FLOOR), and the whole box is a statement about the
> KEY POWER alone: no other member's first discrepancy is
> compressed here (the measured FR-M3 W member attains \(\Theta_0\)
> at a coordinate the key power leaves untouched). Transfer to any
> other member goes only through T4.2(b)'s perturbation hypothesis.
> GENTOW-6's CERT-TOP serves as the source-owned, fully exposed
> assembled-slot proof that \(\omega_{j^*}\ne0\), at its \(f_1=1\)
> scope (R5-63A).”

**DERIVATION:** `[ASSEMBLED — box by EFF.T4.10 + EFF.T4.14]` The gloss states the two justifications inline. R5-m1's diagnosis of the r0 box: it displayed a one-way implication `⟹ first discrepancy at Θ_j` with a trailing sentence attributing the converse to the floor and calling CERT-TOP a “unique-slot proof” — both pre-r3 readings.

**CONDITIONALITY:** **key power only.** This is the single most consumption-critical fence in the note.

**RESOLUTION TRACE:** base composition record → R5-m1 replaces the boxed display and its trailing sentence. R5-m1 governs; the r0 box and its “unique-slot proof” sentence are `[SUPERSEDED]`.

**TEETH:** S8 PE1(2); PE2 GT3 consumption.

---

### EFF.T4.41  [lemma]

**CANONICAL STATEMENT — R5-63A, the r3-awaited full-exposure calculation:**

> “**Verdict: YES at the sealed scope — \(f_1=1\), \(\mu_2=2\),
> \(2i_{t^*}\ge D'\) — and NO elsewhere.**”

with its conclusion:

> “**How this discharges T4.2(c)'s premise at the GT6 instance.** By
> (a), every summand of the assembled height-\(\Theta\) layer of the
> key power's discrepancy — the same object \(\omega\) assembles —
> is a term of some overflowing pair's single-extraction branch
> chain; there is no other provenance left to exclude. By (b), the
> only such term at the canonical position \((a^*,Y^{B^*+1})\) is
> the \((t^*,t^*)\) direct branch. Uniqueness among branch-chain
> terms is therefore uniqueness among ALL summands: the certificate
> slot is FULLY EXPOSED, in S0's r3 sense, by the displayed digit
> \((\widehat c_{t^*})^2\pi^{2a_{t^*}}\cdot(\text{wrap unit})\ne0\).
> T4.2(c) fires: \(\omega_{j^*}\ne0\), \(j^*\) is touched, and
> \(\nu_{j^*}(f_{\mathrm{key}})=\Theta_{j^*}\). S4.1's r3
> conditional ("When that source-owned calculation establishes this
> full exposure ...") is resolved AFFIRMATIVELY at this scope; its
> fail-closed branch ("If the pinned source span establishes
> uniqueness only among single-extraction branches ...") does not
> bite, because 6.3(a) is a classification of the whole layer, not
> a uniqueness claim inside one provenance.”

**DERIVATION:** `[PROVED from the validated GT6 span 1 — five byte-quoted legs]`

Requirement restated: “invoking T4.2(c) at `GT6-CERT-TOP` needs a source-owned calculation that, after every branch term and every incoming carry and recarry has been propagated to the canonical grid, the complete list of summands landing in the certificate slot is the displayed contribution alone — exclusion across EVERY provenance, not uniqueness among single-extraction branches.”

Leg 1 — the whole-layer classification, XREF X33, byte-quoted by the note as `> (a) [SOURCE CLASSIFICATION] the height-THETA graded layer of the`, which R5-63A completes in prose: the layer of the discrepancy “(\(\operatorname{Sh}C_j-C_j\) over the composed grid)” “is a sum of single-\(\Phi'\)-extraction branches, one per
x-overflowing lift pair”.

Leg 2 — what leaves the layer, XREF X35, byte-quoted as `> Multi-extraction branches sit at weight >= THETA + delta; tail`, completed by the note as “(non-extraction) routes are shared by both reads and cancel.”

Leg 3 — carries/recarries are tracked, not unaccounted, XREF X34, byte-quoted as `> division/recarry step emits terms of Y-exponent LOWERED by`, completed by the note as \(e_2f_2-e_2s\ge e_2>0\) “at the same weight”. R5-63A's gloss: “carries and recarries are not an unaccounted provenance; they are the branches' own tracked steps.”

Leg 4 — the certificate slot receives exactly one height-\(\Theta\) branch, XREFs X36, X37, X39.

Leg 5 — the digit is nonzero unconditionally, XREF X38: “A product of units in K2^x: nonzero — no” binomial coefficient, no characteristic condition, no zero divisors.

Step justifications: legs 1–3 `by XREF X33/X34/X35` establish that the assembled layer has no provenance outside the branch chains; leg 4 `by XREF X36/X37/X39` gives uniqueness inside the chains; the two together give full exposure `by EFF.T4.08`; the conclusion `by EFF.T4.16` then `by EFF.T4.14`.

**CONDITIONALITY:** \(f_1=1\), \(\mu_2=2\), \(2i_{t^*}\ge D'\). Also: “this is a consumption display added by a repair round; the acceptance counter stays 0/2 and the next hostile pass re-adjudicates it” — which it then did, twice clean (EFF.T4.45).

**RESOLUTION TRACE:** R5-63A. New in r5; discharges the antecedent of EFF.T4.23. No earlier text.

**TEETH:** S8 PE1(5); PE2 GT6 consumption.

---

### EFF.T4.42  [fence]

**CANONICAL STATEMENT — R5-63A's scope fences:**

> “**Scope fences (what is NOT supplied).**
>
> - \(f_1\ge2\): the same span's GT6-r1 scope pin —
>
>   ```
>   > genre" reads AT f1 = 1, at the corrected chat_t. At f1 >= 2 the
>   ```
>
>   displays below "are NOT proved as written" — so S4.2's
>   corrected-lift invocation (ANNEX 6.3′) still awaits ITS OWN
>   full-exposure calculation; no (a)-grade layer classification is
>   sealed at \(f_1\ge2\) (GENTOW6-BOX-4 residue). S4.2's r3
>   conditional language stands unchanged.
> - \(\mu_2\ge3\): S4.3's candidate status is unchanged (R2-G3
>   governs; (6.5-CAND) remains an unassembled candidate).
> - No hostile-pass credit: this is a consumption display added by
>   a repair round; the acceptance counter stays 0/2 and the next
>   hostile pass re-adjudicates it.”

**DERIVATION:** `[FENCE — source-pinned]` The \(f_1\ge2\) fence rests on GENTOW-6's own scope pin, XREF X40 (verified count 1, line 382, byte 21265, inside GT6 span 1).

**CONDITIONALITY:** none; this is the negative face of EFF.T4.41.

**RESOLUTION TRACE:** R5-63A. New in r5. The third bullet is historical after EFF.T4.45; bullets 1 and 2 stand at HEAD and are re-displayed by the acceptance record.

**TEETH:** S8 PE1(4), PE1(6).

---

### EFF.T4.43  [changes-record]

**CANONICAL STATEMENT — the last in-note status block (R5-63A's refresh), now historical:**

> “**STATUS: R5 TEXT REPAIRED; UNRESOLVED at attempt grade 0/2.**
> No clean hostile pass has been earned. The r5 round defined the
> member class \(\mathfrak M\) on the sources' actual quantification
> domain (pure coefficient slice, no disc hypothesis), withdrew the
> stale r0 CERT-TOP consumption sentence, scoped the boxed
> compression to the key power, defined \(\mathscr A_j\) from
> GENTOW-6.4(a)'s grid display under a new validated span, and added
> the R5-63A consumption display: at \(f_1=1\), \(\mu_2=2\),
> \(2i_{t^*}\ge D'\), THEOREM GENTOW-6.3(a)+(b) supply the
> source-owned full-exposure calculation required by r3, so
> `GT6-CERT-TOP`'s invocation of T4.2(c) is discharged at that scope
> only. The \(f_1\ge2\) annex leg (6.3′) and the \(\mu_2\ge3\)
> candidate still await their own exposure calculations. The
> acceptance counter remains 0/2.”

**DERIVATION:** `[CHANGES RECORD]` This is the fifth and last of the note's status blocks. The chain is: base `**STATUS: COMPLETE at attempt grade 0/2. Hostile arc owed.**` → R1-C1 `**STATUS: R1 TEXT REPAIRED; UNRESOLVED at attempt grade 0/2.**` → R4-m2 `**STATUS: R4 TEXT REPAIRED; …**` → R5-63A `**STATUS: R5 TEXT REPAIRED; …**`. (r2 and r3 left the status label stale; R4-m2 exists precisely to fix that — “only the stale revision label and its reason are updated.”)

**CONDITIONALITY:** `[SUPERSEDED]` by EFF.T4.45. Its *mathematical* content — the \(f_1\ge2\) and \(\mu_2\ge3\) fences — survives; only the grade and the “No clean hostile pass has been earned.” clause are dead.

**RESOLUTION TRACE:** base title status line → R1-C1 → R4-m2 → R5-63A → ACCEPTANCE RECORD.

**TEETH:** §7.

---

### EFF.T4.44  [changes-record]

**CANONICAL STATEMENT — the folded post-pass rider:**

> “**Dated rider (2026-08-12, post-pass — the single minor of the clean
> Fable pass, folded per the minors-only precedent, no grade event).**
> The 𝔐-definition's level-1 gloss "Equivalently at the level-1 read —
> by the same Step-0 carry conversion…" is read as the ONE-DIRECTIONAL
> "In particular, at the level-1 read…" (𝔐 ⟹ the weak entry bound —
> the only direction any current consumer uses). The converse (weak
> entry bound ⟹ 𝔐) is TRUE but rides GT3 Step 1's weight-monotone
> K₂-division + Step 2's re-expansion (inside pinned GT3 span 1), not
> the Step-0 carry conversion alone — a consumer needing the converse
> must cite those two legs. Pass of record: the Fable-arm hostile pass
> returned 0C + 0G + 1m with the 𝔐 mechanism, the 6.3(a)+(b)
> full-exposure discharge, all 25 pins, and the boundary cases verified
> sound — clean pass 1 of 2.”

**DERIVATION:** `[RIDER — folded]` The minors-only folding is licensed by EFF.T4.39's closing rule (“Minor-only riders may be folded without changing the theorem statement”) and confirmed by the acceptance record's arc line (“0C + 0G + 1m (the 𝔐-gloss direction rider, folded per the minors-only precedent)”).

**CONDITIONALITY:** the rider is a *reading instruction* on EFF.T4.05, not a new hypothesis. A consumer needing the converse direction must additionally cite GT3 Step 1's weight-monotone \(K_2\)-division and Step 2's re-expansion, both inside pinned GT3 span 1 (XREFs X01–X02).

**RESOLUTION TRACE:** post-r5 dated rider, before the acceptance record; governs the reading of R5-F1's gloss sentence.

**TEETH:** S8 PE1(2); the pass of record is PASS 1 of EFF.T4.45.

---

### EFF.T4.45  [acceptance-box]

**CANONICAL STATEMENT:**

> “## ACCEPTANCE RECORD (2026-08-12): T4 ACCEPTED 2/2 (model-diverse pair)
>
> Arc: composed (comp4 T4C2) → r1–r3 (sol-arm passes with repairs;
> pins blocked by the sandboxed executor until the pasted-source
> protocol) → r4 (Fable arm: the reversed GT6 BOX-4 pin re-anchored,
> 17-marker validation record) → r5 (Fable arm: the member class 𝔐
> defined on the sources' weak coefficient slice — no disc hypothesis;
> the stale CERT-TOP sentence withdrawn; 𝒜_j defined; GT6 6.3(a)+(b)
> certified as discharging r3's full-exposure premise at f₁ = 1,
> μ₂ = 2 only) → PASS 1: Fable-arm hostile, 0C + 0G + 1m (the
> 𝔐-gloss direction rider, folded per the minors-only precedent) →
> PASS 2: sol confirmation (gpt-5.6-sol high,
> runs/comp12/T4P7_output.log), VERDICT CLEAN (0C + 0G + 0m —
> "clean mathematical confirmation"). Two consecutive clean
> fresh-context passes on model-diverse arms: **THE CERTIFICATE
> WITNESS NOTE IS ACCEPTED at 2/2.** Consumption checks + the
> absorbed notes' dated appends ride the next queue. Standing fences
> unchanged and displayed: f₁ ≥ 2 (BOX-4 residue), μ₂ ≥ 3 (candidate
> only), the disc ≠ 0 quarantine at the σ-read legs.”

**DERIVATION:** `[ACCEPTANCE RECORD]` Acceptance requires, per EFF.T4.39, “PE1 CLEAN followed by PE2 CLEAN”. The record supplies both, on **model-diverse arms** (Fable then gpt-5.6-sol high). Evidence pointer: `runs/comp12/T4P7_output.log`.

**CONDITIONALITY:** the three standing fences are re-displayed at acceptance and are therefore part of the accepted statement, not commentary: \(f_1\ge2\) (EFF.T4.25, .42, residue home `GENTOW6-BOX-4`), \(\mu_2\ge3\) (EFF.T4.27), the disc \(\ne0\) quarantine (NON-IMPORT N-1, ledger row HYP.72). Protocol scope: consumption checks and dated appends OUTSTANDING (scope split B; negative XREF rows N1–N4).

**RESOLUTION TRACE:** the note's final section; supersedes EFF.T4.43 and the GRADE line of EFF.T4.37.

**TEETH:** §7.

---

## 4. XREF verification ledger

Every positive XREF below was checked with fixed-string grep at compile time (2026-08-14) against the working tree and has the count recorded. X19 and N1–N4 are verified **negative/retired** edges. Line numbers are 1-based; byte offsets 0-based.

### 4.1 GT3 semantic stack (`lean/notes/openmath/GENTOW3_PROOF_2026-08-09.md`, 1,041 lines / 57,484 bytes)

| ID | Verified designation | count | line | byte | Role |
|---|---|---:|---:|---:|---|
| X01 | `## S0. THE ONE CONSTANT AND THE THRESHOLD` | 1 | 74 | 3886 | span 1 BEGIN — setting, clauses (i)/(iii)/(iv), the W-member row |
| X02 | `## S3. COROLLARY GENTOW-3.C` | 1 | 317 | 17886 | span 1 END |
| X03 | `### S7.1 THE DATED GAUGE ANNEX (F-1 repair): the corrected chat_t` | 1 | 504 | 28156 | span 2 BEGIN — corrected gauge + FR-GL row (added at r4) |
| X04 | `### S7.2 (m-1 repair): the (iv) certificate's digit-value` | 1 | 610 | 33968 | span 2 END |
| X05 | `## S7.6 [GT3-r2] PE2 REPAIR RECORD:` | 1 | 680 | 37757 | span 3 BEGIN — the certificate reading of “touched” |
| X06 | `## S7.7 [GT3-r3] PE3 REPAIR RECORD:` | 1 | 763 | 42380 | span 3 END, span 4 BEGIN |
| X07 | `### Dated acceptance record` | 1 | 817 | 45302 | span 4 END, span 5 BEGIN — FR5X measurements (added at r4) |
| X08 | `## S8. [GT3-r4] CODEX TOWERRAT2 RUN B REPAIRS` | 1 | 880 | 48739 | span 5 END |
| X09 | `### S8.1 [B-F1, GAP] Clause (iv)'s deep-perturbation persistence:` | 1 | 894 | 49488 | span 6 BEGIN — the repaired \(\Theta_j+1\) margin |
| X10 | `### S8.2 [B-F2, GAP]` | 1 | 941 | 52157 | span 6 END (half-open; S8.2/S8.4 NOT consumed) |

### 4.2 GT6 semantic stack (`lean/notes/openmath/GENTOW6_PROOF_2026-08-09.md`, 1,265 lines / 71,465 bytes)

| ID | Verified designation | count | line | byte | Role |
|---|---|---:|---:|---:|---|
| X11 | `## S3. THEOREM GENTOW-6.3` | 1 | 344 | 19136 | span 1 BEGIN — 6.3(a)/(b)/(c), the R5-63A legs |
| X12 | `## S4. MACHINE LEG` | 1 | 529 | 29718 | span 1 END |
| X13 | `### S6.1 THE DATED GAUGE ANNEX` | 1 | 702 | 39709 | span 2 BEGIN — ANNEX-THEOREM 6.3′ |
| X14 | `### S6.2 THE 𝒯-FREE CAP LEMMA` | 1 | 851 | 47646 | span 2 END, span 3 BEGIN (added at r5) |
| X15 | `> (b) [BAND-1 CAP, 𝒯-FREE] across ambient window-N lifts of f:` | 1 | 920 | 51652 | span 3 END (half-open; 6.4(b) NOT consumed) |
| X16 | `**GENTOW6-BOX-1 (mu2 >= 3 attainment): CLOSED AT f1 = 1**` | 1 | 1204 | 67667 | span 4 BEGIN |
| X17 | `**GENTOW6-BOX-4 (the f1 >= 2 x-ful-digit sealed battery row):` | 1 | 1249 | 70410 | span 4 END, span 5 BEGIN |
| X18 | `output md5 2d8d617a, verdict commit follows this append.` | 1 | 1265 | 71408 | span 5 END — the source's final line |
| X19 | `6.3' keeps its prose-only grading in the note's own terms.` | 1 | 673 | 38211 | **RETIRED r0 span-4 END** — verified to precede X17 (38211 < 70410), confirming the reversal R4-C1 diagnosed. NOT a marker at HEAD. |

### 4.3 GT3 byte-quoted legs (R5-F1 / R5-V)

| ID | Verified designation | count | line | byte | Role |
|---|---|---:|---:|---:|---|
| X20 | `member f ∈ 𝒯, per composed coordinate j < mu2:` | 1 | 164 | 8952 | the 𝒯 display (NOT the operative domain) |
| X21 | `(i) [FLOOR] every dv2-height at which ShC_j and C_j carry` | 1 | 189 | 10420 | GENTOW-3(i) = supplier of (FLOOR) |
| X22 | `On 𝒯 the entry pins lie weakly above the inner side:` | 1 | 230 | 12643 | Step 1 entry bound = the only membership fact consumed |
| X23 | `f = Phi2^{mu2} has composed read DRAIN (C_j = 0) while its shadow` | 1 | 204 | 11313 | (iv) applied at the key power |
| X24 | `f = Phi2³ + 2x·Phi2² + 8·Phi2 + 64 at FR-M3 j = 0 has first` | 1 | 93 | 4921 | the W member named a member by GT3's S0 |
| X25 | `(g in-budget with slots at heights > THETA_j, disc ≠ 0): both` | 1 | 296 | 16733 | (iv) σ-leg parenthetical — **NON-IMPORT N-1** |
| X26 | `The corrected derivation (this note's Steps 0-2, run on g).` | 1 | 907 | 50145 | S8.1 proof-strength precedent for Steps 0–2 |
| X27 | `"in-budget" at the GENTOW-1(a) box this corpus defines: every` | 1 | 908 | 50212 | the box hypothesis |
| X28 | `every disagreeing height of g's two reads is >= THETA_j + 1,` | 1 | 923 | 51137 | the repaired margin used by T4.2(b) |
| X29 | `FR-M3 W member's g_W = 2x*Phi2^2 + 8*Phi2 has slot weights 9, 9 <` | 1 | 932 | 51697 | boundary confirmation (weak slice, not box) |
| X30 | `10 = mu2*E2 + 1 — OUTSIDE the box — and its discrepancy lands at` | 1 | 933 | 51763 | boundary confirmation, cont. |
| X31 | `consumed by the corrected derivation; the box hypothesis is the` | 1 | 938 | 52077 | S8.1's decoupling of the σ parenthetical |

### 4.4 GT6 byte-quoted legs (R5-63A / R5-m2 / R5-V)

| ID | Verified designation | count | line | byte | Role |
|---|---|---:|---:|---:|---|
| X32 | `THEOREM GENTOW-3(i) floors every discrepancy at` | 1 | 371 | 20760 | the floor applied to the self-shadow key power |
| X33 | `> (a) [SOURCE CLASSIFICATION] the height-THETA graded layer of the` | 1 | 393 | 21910 | R5-63A leg 1 — whole-layer classification |
| X34 | `> division/recarry step emits terms of Y-exponent LOWERED by` | 1 | 400 | 22379 | R5-63A leg 3 — carries/recarries tracked |
| X35 | `> Multi-extraction branches sit at weight >= THETA + delta; tail` | 1 | 402 | 22511 | R5-63A leg 2 — what leaves the layer |
| X36 | `> b* = (2e2t*+1) mod e2f2, a* = 2i_{t*} − D' — receives EXACTLY ONE` | 1 | 408 | 22842 | R5-63A leg 4 — the certificate slot |
| X37 | `> equality iff zero steps and t + t' = 2t*: the (t*,t*) direct` | 1 | 469 | 26344 | R5-63A leg 4, proof |
| X38 | `A product of units in K2^x: nonzero — no` | 1 | 475 | 26723 | R5-63A leg 5 — unconditional nonvanishing |
| X39 | `> lands at (a*, Y^{B*+1}) by the uniqueness just shown (branches` | 1 | 480 | 27030 | R5-63A leg 4, close |
| X40 | `> genre" reads AT f1 = 1, at the corrected chat_t. At f1 >= 2 the` | 1 | 382 | 21265 | GT6-r1 scope pin — the \(f_1\ge2\) fence |
| X41 | `> a < D', b < e2f2; slot degree jD2 + bD' + a; slot dv2-height` | 1 | 884 | 49514 | 6.4(a) grid display (𝒜_j) |
| X42 | `> e1e2·v(c_{j,a,b}) + w(a,b), w(a,b) = a·e2h + b·u2). Then:` | 1 | 885 | 49577 | 6.4(a) heights (𝒜_j) |

### 4.5 Residue-home box designations

| ID | Target and verified designation | count | Role |
|---|---|---:|---|
| X43 | `GENTOW6_PROOF_2026-08-09.md` — `GENTOW6-BOX-1` | 4 | residue home (lower-coordinate / compound classification) |
| X44 | same — `GENTOW6-BOX-2` | 3 | residue home (partial-side count ledger) |
| X45 | same — `GENTOW6-BOX-3` | 3 | residue home (entry-driven / non-top-overflow) |
| X46 | same — `GENTOW6-BOX-4` | 15 | residue home (corrected-lift widening) |
| X47 | `GENTOW3_PROOF_2026-08-09.md` — `GENTOW3-BOX-1` | 10 | residue home (genre-general non-cancellation) |

### 4.6 Verified NEGATIVE edges (the append protocol has not run)

| ID | Check | count | Meaning |
|---|---|---:|---|
| N1 | `grep -cF 'GT3-THRESHOLD' GENTOW3_PROOF_2026-08-09.md` | 0 | GT3's dated absorption append has NOT landed |
| N2 | `grep -cF 'GT6-CERT-TOP' GENTOW6_PROOF_2026-08-09.md` | 0 | GT6's dated absorption append has NOT landed |
| N3 | `grep -cF 'T4' GENTOW3_PROOF_2026-08-09.md` | 0 | GT3 contains no reference to T4 of any kind |
| N4 | `grep -cF 'T4' GENTOW6_PROOF_2026-08-09.md` | 0 | GT6 contains no reference to T4 of any kind |

### 4.7 Reverse-XREFs: consumers of T4

| ID | Consumer file and verified designation | count | Supplied edge |
|---|---|---:|---|
| RX48 | `docs/in-progress/LEAN_SCOPING_consumption_map_2026-08-12.md` — `## T4 — THE CERTIFICATE WITNESS` | 1 | the Lean-scoping consumption read of T4 (**STALE**: its `**(d) Arc grade.**` line records “Attempt 0/2, r1–r3 folded, pass 4 NOT CLEAN — repairs owed (r4)”, i.e. it predates r4, r5, and the 2/2 acceptance; it also carries the pre-r4 T4.2(d) as “currently gapped”) |
| RX49 | `spec/HYPOTHESIS_LEDGER.md` — `### T4 boxes and tightness suspects` | 1 | the ledger section homing T4's residues |
| RX50 | same — `HYP.72  disc≠0 downstream fence` | 1 | NON-IMPORT N-1 threaded downstream (“CONSUMED BY: W12/other σ consumers; T4 consumes no σ-content.”) |
| RX51 | same — `HYP.109  T-unit grade caveats` | 1 | EFF.T4.37's evidence fence (“T4 adds no fresh machine computation”) |
| RX52 | same — `HYP.112  T4 μ₂≥3 candidate fence` | 1 | EFF.T4.27's consumption ban |
| RX53 | same — `HYP.113  T4.2(c) exposure premise` | 1 | EFF.T4.16's live conditional leg at \(f_1\ge2\) |
| RX54 | same — `HYP.114  T4.2(d) provenance exclusion` | 1 | EFF.T4.17's all-provenance fence |
| RX55 | same — `HYP.115  T4 fail-closed pins` | 1 | EFF.T4.29 (“CONSUMED BY: all T4 imported premises”) |
| RX56 | same — `HYP.116  \`GENTOW3-BOX-2\`` | 1 | the recorded **residue-home omission** in EFF.T4.36 |

### 4.8 Unpinned import (located, but outside T4's fail-closed protocol)

| ID | Located designation | count | Status |
|---|---|---:|---|
| U57 | `lean/notes/openmath/GENHN_PROOF_2026-08-08.md` — `> (ii) [COMPOSED SLOT LEMMA — GENHN-2′] {x^a Φ′^b : a < D′,` | 1 | GENHN-2′ exists and is locatable, but T4 cites it **three times** (`grep -cF 'GENHN-2′'` on T4 = 3) with **no pin span**. See OPEN-CALL 2. |

---

## 5. Effective supply/consumption ledger

`[TABLE]`

| Source conclusion | Effective T4 supply | Surviving fence | Protocol status |
|---|---|---|---|
| GENTOW-3(iv) “touched coordinate(s)” + floor attainment | EFF.T4.10 (definition) and EFF.T4.14 (attainment) as `GT3-THRESHOLD` (EFF.T4.18) | one-sided at member level (EFF.T4.19); (FLOOR) on 𝔐 remains a hypothesis | **ABSORBED (2/2 accepted); consumption check + append OUTSTANDING** (N1, N3) |
| GENTOW-3 S8.1 deep-perturbation persistence | EFF.T4.15 (T4.2(b)) inside `GT3-THRESHOLD` | the \(\Theta_j+1\) margin and the box hypothesis remain source arithmetic (X28, X27) | **ABSORBED; check + append OUTSTANDING** |
| GENTOW-6.3(b) CERT-TOP → threshold attainment | EFF.T4.16 (T4.2(c)) applied at EFF.T4.22–.23 as `GT6-CERT-TOP`, premise discharged by EFF.T4.41 | discharged ONLY at \(f_1=1,\ \mu_2=2,\ 2i_{t^*}\ge D'\); the exposure calculation stays source-owned (N-5) | **ABSORBED at the sealed scope; check + append OUTSTANDING** (N2, N4) |
| GENTOW-6.3′ corrected-lift annex (\(f_1\)-general) | EFF.T4.25 — conditional invocation only | **exposure premise NOT discharged at \(f_1\ge2\)** (X40); residue `GENTOW6-BOX-4` | **NOT ABSORBED — conditional record** |
| GENTOW-6.5 \(\mu_2\ge3\) refinement | EFF.T4.27 — candidate record only | `(6.5-CAND)` is unassembled; no touchedness, no attainment (HYP.112) | **NOT ABSORBED — signed candidate/non-instance** |
| GENTOW-6.3(c) no-overflow regime | EFF.T4.24 — quoted, stronger source conclusion retained | between-regimes cancellation not excluded | **CITED, not absorbed** |
| GENTOW-6.4(a) grid display | EFF.T4.04 (𝒜_j) — grid-and-height face only | bijection/count face NOT consumed (N-2) | **CITED under new r5 span** |
| GENHN-2′ exact-height separation | well-definedness of EFF.T4.07 and the one-digit-per-height clause of EFF.T4.04 | unpinned (U57) | **CITED, UNPINNED — OPEN-CALL 2** |

---

## 6. TEETH inverse inventory

Disposition vocabulary is `{Lean theorem, executable regression, signed non-applicability}`. T4 “adds no machine computation” (EFF.T4.37), so every executable row is an **inherited** GENTOW-3/GENTOW-6 battery re-run, marked as such; rows that are statement/scope attacks become propositions in the formalization and are marked `Lean theorem`.

| # | Battery row (source wording, abbreviated) | Guarded EFF units | Disposition |
|---|---|---|---|
| 1 | PE1(1) — \(\operatorname{gr}_{\Theta_j}\) taken after complete slot assembly and cancellation | EFF.T4.07, .08, .10, .17 | Lean theorem (definitional obligation on `gr`) |
| 2 | PE1(2) — T4.2(a) uses the floor, infers no member-general converse | EFF.T4.05, .12, .13, .14, .19, .35, .40, .44 | Lean theorem |
| 3 | PE1(3) — T4.2(b) uses the repaired S8.1 margin, not the withdrawn “same shift” | EFF.T4.03, .06, .15 | Lean theorem |
| 4 | PE1(4) — the \(f_1=1\) / corrected-lift / \(\mu_2\ge3\) scopes stay separated | EFF.T4.01, .02, .22, .25, .27, .32, .35, .36, .42 | Lean theorem (three separate instance statements) |
| 5 | PE1(5) — CERT-TOP invoked through T4.2(c) only after all-provenance exclusion | EFF.T4.08, .16, .23, .25, .33, .41 | Lean theorem |
| 6 | PE1(6) — the higher-\(\mu_2\) binomial condition is not stated as necessary | EFF.T4.27, .35, .36, .42 | **signed non-applicability** |
| 7 | PE1(7) — every marker pin resolves uniquely and in order | EFF.T4.21, .28, .29, .30, .31 | executable regression (the `grep -F` validation itself; re-run clean at compile time) |
| 8 | PE2 GT3 — recover (iv) attainment + S8.1 persistence by substituting T4.1/T4.2 alone | EFF.T4.10, .14, .15, .18 | executable regression (INHERITED — GENTOW-3 battery) |
| 9 | PE2 GT3 — FR-M3 slack \([12,7,4]\) vs \([10,7,4]\) | EFF.T4.11, .17, .20 | executable regression (INHERITED) |
| 10 | PE2 GT3 — the \(W\)-member's entry-driven attainment at \(j=0\) | EFF.T4.05 (fact 3), .17, .19, .20, .40 | executable regression (INHERITED) |
| 11 | PE2 GT3 — FR-GL's two-coordinate attainment | EFF.T4.02, .20, .21 (span 2) | executable regression (INHERITED) |
| 12 | PE2 GT3 — FR5X's identically-zero coordinates | EFF.T4.12, .20, .21 (span 5) | executable regression (INHERITED) |
| 13 | PE2 GT6 — recover CERT-TOP through T4.2(c) after the complete exposure calculation | EFF.T4.16, .22, .23, .33, .41 | executable regression (INHERITED — GENTOW-6 battery) |
| 14 | PE2 GT6 — the corrected-lift \(f_1=2\) BOX-4 rows | EFF.T4.25, .26, .28 (span 5), .42 | executable regression (INHERITED) |
| 15 | PE2 GT6 — the gauge-live \(\eta\ne1\) rows | EFF.T4.02, .25 | executable regression (INHERITED) |
| 16 | PE2 GT6 — the no-overflow FAM-E/FAM-D controls | EFF.T4.17, .24 | executable regression (INHERITED) |
| 17 | PE2 GT6 — BP3 and FR5X higher-\(\mu_2\) rows against the one-sided binomial statement | EFF.T4.27, .35 | **signed non-applicability** (the rows are checked *against* a statement T4 declines to make) |

**Zero-orphan check:** 17 of 17 source battery obligations are mapped (PE1's 7 numbered items + PE2's 2 consumption checks expanded into their 10 named sub-checks, of which 5+5 are listed as rows 8–17); 0 orphan rows.

**Reverse direction — units with no tooth:** EFF.T4.34, .37, .43, .45 are record/acceptance units and carry no battery obligation of their own; they are guarded by §7 instead. Every other unit (41 of 45) appears in at least one row above.

---

## 7. Acceptance and evidence fence

EFF.T4.39 requires:

> “Acceptance requires PE1 CLEAN followed by PE2 CLEAN.”

EFF.T4.45 supplies both, on model-diverse arms (Fable-arm hostile 0C + 0G + 1m with the minor folded; gpt-5.6-sol high confirmation 0C + 0G + 0m, `runs/comp12/T4P7_output.log`).

The evidence fence of EFF.T4.37 is unmoved by acceptance: **T4 contributes no machine computation of its own.** All regression evidence cited anywhere in this specification is inherited from the byte-frozen `GENTOW3_PROOF_2026-08-09.md` and `GENTOW6_PROOF_2026-08-09.md` artifacts. Ledger row HYP.109 carries the caveat downstream. Consumers must not treat GREEN 265/0 (EFF.T4.26) or any FAM/FR row as T4 evidence.

The *pin* evidence is different in kind and is first-party: the 25 marker resolutions and 25 byte-quotes of EFF.T4.30 and EFF.T4.31 were re-executed at compile time and are clean (§4.1–4.4).

---

## 8. Deferred reconciliation obligations

Named cross-spec bookkeeping, not unresolved T4 scope judgments.

1. **The two dated absorption appends — FOR-0c/protocol.** Run the GT3 and GT6 consumption checks (EFF.T4.39) and land the dated absorption appends in `GENTOW3_PROOF_2026-08-09.md` and `GENTOW6_PROOF_2026-08-09.md`. Verified not yet done (N1–N4). The corpus pattern for the append wording comes from the S-2 unit, not from T4 — `grep -cF 'absorbed by S-2 as instance' T3_COCYCLE_TELESCOPE_2026-08-12.md` = 1 — and T4 (composition unit S-3) prescribes no wording of its own, so the exact heading is a protocol choice, not a T4 requirement. The acceptance record itself schedules this: “Consumption checks + the absorbed notes' dated appends ride the next queue.” Action item, not a mathematical open call.

2. **`docs/in-progress/LEAN_SCOPING_consumption_map_2026-08-12.md` is stale on T4 — FOR-0b.** RX48's arc-grade line records “Attempt 0/2, r1–r3 folded, pass 4 NOT CLEAN — repairs owed (r4)”, and its clause-(d) summary calls T4.2(d) “currently gapped”. Both predate r4/r5 and the acceptance. A blueprint consumer reading that map instead of this spec would import a superseded T4.2(d) and a wrong grade. Refresh owed.

3. **`GENTOW3-BOX-2` missing from the residue home — FOR-0d/ledger.** `spec/HYPOTHESIS_LEDGER.md` HYP.116 (RX56) records it explicitly as a “T4 residue-home omission” with statement “Five committed families cover only f₁=1 and η=1.” EFF.T4.36 reproduces T4's list as written and does NOT add the box. Whether the box belongs in T4's residue home is a note-owner decision, not a compiler decision.

4. **The GT6 span-4/5 shared marker.** X17 serves as both span 4 END and span 5 BEGIN, and X14 as span 2 END and span 3 BEGIN. This is licensed by the note (“the S6.2 marker serves as span-2 END and span-3 BEGIN, as the GT3 stack already does with its shared markers”) and by S5 condition 5 as verified. Recorded here only so a mechanical pin-checker does not report it as a duplicate-occurrence violation.

---

## 9. Self-audit

### Resolved compilation calls

- The effective text is derived: base + r1–r5 in round order + the folded post-pass rider. Six same-span collisions are tabulated in §1 with the governing round named for each.
- R1-G1's S4.3 (instance-under-`(EXPOSE-6.5)`) is classified fully dead, superseded by R2-G3's candidate downgrade. `(EXPOSE-6.5)` is absent from the effective text.
- The r0 CERT-TOP sentence is recorded as WITHDRAWN text inside EFF.T4.23 rather than silently dropped, because R5-F2's reasoning is load-bearing for why the instance is conditional.
- The three superseded status blocks and the two `bubblewrap` pin records are classified historical, with the supersession quoted from R4-C1.
- The mathematical absorption count is **two source conclusions** (GENTOW-3(iv)+S8.1 as one instance; GENTOW-6.3(b) as the other), distinct from the note's five *deliverables* and from the protocol's zero landed appends.
- All 25 pin markers, all 25 byte-quotes, and all five residue-box names were independently re-verified; the retired marker X19's reversal was re-confirmed by byte offset.
- The four verified negative edges N1–N4 separate mathematical acceptance from protocol completion.
- Nine reverse-XREFs were emitted and grep-verified, including the one stale consumer (RX48).
- The battery is fully consumed: 17 obligations, 0 orphans, 41 of 45 units guarded, the 4 unguarded ones being records covered by §7.
- T4 has no `[TABLE]` prosification: both pin stacks, both validation records, and the supersession chain are transcribed as tables.

### OPEN-CALLS

**OPEN-CALL 1 — EFF.T4.18's Substitution block carries pre-r3 provenance vocabulary. FOR-0b (note owner).**

The `GT3-THRESHOLD` Substitution block reads:

> “with \(\delta=u_2-e_2D'h\), and with \(\omega_j\) the key power’s
> assembled single-\(\Phi'\)-extraction digit.”

but DEFINITION T4.1 after r3 (EFF.T4.10) assembles “all single-\(\Phi'\)-extraction routes, all other branch terms, and every incoming carry and recarry.” r3 listed six replacement sites and this was not among them; r4's m1 upgraded the same vocabulary in S6 but not here. The governing definition is unambiguous (EFF.T4.10), so this is a wording seam with no logical consequence — but it is an inconsistency inside the effective text, and a compiler may not silently normalize a quoted source sentence. **Proposed disposition:** a minors-only rider replacing the quoted phrase “assembled single-\(\Phi'\)-extraction digit” with wording drawn from DEFINITION T4.1 (compiler suggestion, NOT source text: *fully assembled height-\(\Theta_j\) digit*). Needs the note owner.

**OPEN-CALL 2 — GENHN-2′ is an unpinned import of a fail-closed note. FOR-0d — NEEDS ASVIN.**

T4's whole consumption protocol is byte-literal fail-closed pinning (EFF.T4.29), and its pin stacks cover exactly two sources. But `GENHN-2′` is cited three times as a *load-bearing* import: it is what makes \(\operatorname{gr}_m\) unambiguous (EFF.T4.07 — “The exact-height separation supplied by GENHN-2′ makes this graded digit unambiguous”) and what gives one \(K_2\)-digit per height in \(\mathscr A_j\) (EFF.T4.04). Without it, \(\omega_j\) is not well defined, so this is not a decorative citation.

The lemma is locatable — U57, `> (ii) [COMPOSED SLOT LEMMA — GENHN-2′] {x^a Φ′^b : a < D′,` in `GENHN_PROOF_2026-08-08.md`, count 1 — but T4 supplies **no span, no BEGIN/END markers, and no validation row** for it, and it appears in no S5.1 or R5-V table. Assigning a span would be invention. Phase 0d must decide whether T4's fail-closed protocol is to be extended to a third source stack, or whether GENHN-2′ is a corpus-wide primitive exempt from per-note pinning.

**OPEN-CALL 3 — is EFF.T4.24 an absorption or a citation? FOR-0b.**

EFF.T4.24 quotes GENTOW-6.3(c) as proving “the stronger conclusion \(\operatorname{Sh}C_j=C_j=0\) for every \(j\), hence every coordinate is untouched.” The word “hence” routes a source conclusion through DEFINITION T4.1, which is the signature of an absorption; but S6's compression list (EFF.T4.32) does not name 6.3(c), and the two instance names cover only (iv)/S8.1 and 6.3(b). §5 records it as **CITED, not absorbed**, which is the conservative reading consistent with the compression list. If the note owner intends 6.3(c) to be a third absorbed conclusion, the compression list and the consumption-check plan both need a line. Not decidable from the text.

### Fidelity audit (compile-time, mechanical)

- **228 → 230 quoted segments extracted** from this specification and tested for verbatim containment in the source note under a normalization removing only presentational reflow (whitespace, `\[`/`\]` display delimiters, `**` emphasis, blockquote `>` prefixes). Script: `scratchpad/verb2.py`.
- **211 verbatim.** The 19 non-matches resolve as: **14 cross-file quotations**, each independently grep-verified at count 1 in its own file (7 in `spec/HYPOTHESIS_LEDGER.md`, 2 in `docs/in-progress/LEAN_SCOPING_consumption_map_2026-08-12.md`, and the same strings re-quoted in a second place), and **5 `[ASSEMBLED]` composites** (EFF.T4.14 derivation, EFF.T4.15 statement and derivation, EFF.T4.18 statement, EFF.T4.39 statement) — each of whose components was separately verified verbatim, with the seams named in the unit.
- **No quantifier, index, inequality, direction, rung, or scope was altered anywhere.** Two capitalization repairs and two terminal-punctuation repairs were made during the audit, and one compiler-suggested phrase in OPEN-CALL 1 was de-quoted and italicized so it cannot be mistaken for source text.
- **All 25 pin markers, 25 byte-quotes, 5 box names, 9 reverse-XREFs, 4 negative edges and 1 unpinned import were grep-verified**, with line and byte offsets re-derived independently of the note's own tables.
- **No table was prosified.** Both pin stacks, both validation records, the supersession chain, and the ledgers are tables.

### Exhaustive residual judgment list

There are no other unresolved T4 mathematical or scope judgments. The \(f_1\ge2\) exposure premise, the \(\mu_2\ge3\) candidate, and the disc \(\ne0\) quarantine are the note's own displayed standing fences (EFF.T4.42, .45), not compiler ambiguities; the missing appends, the stale consumption map, the `GENTOW3-BOX-2` omission, and the shared-marker note are classified in §8 as bookkeeping.

EFF-T4 COMPILED: 45 statements / 61 xrefs verified / 3 open calls
