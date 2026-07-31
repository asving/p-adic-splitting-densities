# CUC pass 1 — hostile verification of `CU_cluster_phaseB.md` (fresh context, 2026-07-31)

**Charge.** Read ONLY `lean/notes/openmath/CU_cluster_phaseB.md` (standalone). For each CU
unit: does the citation target, AS QUOTED in the document, genuinely supply the displayed
statement? Audit the §9 CU-2t proof against its own §9.7 eight-point charge; audit the
§6.1 OB2/D-11 audit; audit the §0 pending-verdict registry for honesty. Quote-and-classify
(CRITICAL ERROR vs JUSTIFICATION GAP); fix nothing. A ∀-by-example is CRITICAL.

**Standalone constraint, stated up front.** The document is a citation/re-label unit: most
consumed statements are QUOTED or pinpointed, and where quoted I checked the displayed use
against the quote. What I cannot do from this file alone is confirm quote fidelity against
the homes (O-2a rev 5, O-1thr rev 3/4, O5triple rev 3, O-14a′ rev 3, the tree, O3design,
GMN pins). Every "as quoted" below carries that caveat. The document is sufficiently
self-contained to be verified at this level — no standalone-failure finding — with one
symbol-level exception (F5 below).

**VERDICT: UNSOUND** — one CRITICAL ERROR in the §9 CU-2t proof (clause (iii) injectivity,
F1), with its enabling definitional gap in clause (ii) (F2), plus eight justification
gaps. The shear is narrow and displayed below: Lemma CU-2t clauses (i) and (ii)'s main
forcing content (the polygon read and the verdict value/correctness), the CU-2/CU-5/CU-7
re-label attributions, and the §6.1 audit survive at their displayed conditionality.

---

## Findings (most severe first)

### F1 — CRITICAL ERROR — §9.3(iii): the Θ^τ injectivity claim is false as printed

Quote (statement): "Define Θ^τ(𝐇°, ν) := Θ(𝐇°) ⌢ (λ_{k'+1}, ⊥) … and is INJECTIVE on
DEC seam objects over a fixed f: equal images force equal Θ(𝐇°), Lemma R recovers 𝐇°,
and (i)+(ii) reconstruct the terminal datum from (f, c)."

Quote (hypothesis row, §9.3): "let (𝐇°, ν) be a seam object with Cons_f(𝐇°), in a DEC
configuration."

Θ^τ, by its own definition, does not read ν (λ_{k'+1} is a function of (f, c) by clause
(i)). The hypothesis row constrains only 𝐇° and the configuration; nothing printed
constrains ν beyond its §9.1 typing ("ν the branch's terminal machine record" /
verdict-carrying = "announces an invariant pair (E, F) ∈ ℕ²" — announces *an* pair, not
the true one). Counterexample within the printed hypotheses: two seam objects (𝐇°, ν₁),
(𝐇°, ν₂) with ν₁, ν₂ verdict-carrying records announcing different pairs. Both satisfy
the hypothesis row; Θ^τ maps them to the same image. Injectivity on pairs fails.

The proof's "(i)+(ii) reconstruct the terminal datum" conflates the forced datum
T(f, 𝐇°) (which IS single-valued, by (i)/(ii)) with the record ν. Bridging datum → record
would require either (a) the consistency predicate of F2 as an explicit hypothesis, or
(b) run-anchoring ν via (T-VERD) plus a pinned field inventory for terminal records —
neither is cited in (iii)'s proof ((T-DEC)/(T-VERD) live in §9.4, and no field inventory
for ν exists in the file). Downstream consumption exists: §9.5 "Lemma R's consumer audit
(any future consumer needing full-𝐇 injectivity now has the verdict-carrying case
supplied by Θ^τ, §9.3(iii))." Stop-checking scope: only that consumer line depends on it;
clauses (i), (ii)-main, (iv) do not.

### F2 — JUSTIFICATION GAP — §9.3(ii), uniqueness tail: undefined consistency predicate (borderline circular)

Quote: "so any two verdict-carrying terminal data consistent with the same (f, 𝐇°)
coincide — no free choice" and, in the proof: "a verdict-carrying terminal datum
consistent with (f, 𝐇°) must announce its branch's invariant pair."

"Consistent with (f, 𝐇°)" is defined nowhere in the document for terminal records. The
document itself forecloses the two candidate homes: Lemma R as quoted (§9.1) — "Cons_f
constrains no terminal field"; and §9.0 — "the Cons^τ-SET died with the O3design
replacement." If "consistent" is read as "announces the branch's true invariant pair,"
the uniqueness clause is circular (true by definition, zero content). A non-circular
reading exists — record-consistency := the (t-i) tie to the level-(k'+1) GMN read, per
§9.2's shape description — under which the clause is provable from (i)/(ii); but that
predicate is never displayed as a definition, so the obligation is open, not closed.
Note the blast radius: §2's headline conclusion "so no free choice of terminal record
exists at a verdict-carrying leaf" rests exactly on this clause plus F1's clause (iii).
The forcing of the DATUM (read entry + verdict values, clauses (i)/(ii)-main) is
unaffected.

### F3 — JUSTIFICATION GAP — §1 (CU-2 statement) contradicted by the unit's own §9.1 carrier note; left unrescoped

Quote (§1): "Every history 𝐇 emitted by a complete run of the engine's stage flow on f
is a well-formed element of the carrier 𝔈 satisfying Cons_f."

Quote (§9.1): "at a saturated prefix (μ_{k'} = 1) appending ν would VIOLATE W3's interior
clause" — and OL-4 as quoted: "a run emits at most one terminal record, last."

On a (τ-irr)-decided branch a complete run emits a terminal record after a saturated
prefix; if the emitted history includes that record, it is NOT 𝔈-legal by the document's
own finding. §9.1 explicitly rescopes §2's display ("§2's display '𝐇 = (𝐇°; ν)' is
therefore to be read as the seam PAIR") but §1's universal statement is never rescoped
(append-only discipline acknowledged; still, §1 remains the displayed statement of
record for CU-2 and its grade line says "RE-LABEL, complete"). The recoverable reading —
the well-formed 𝔈 element is the continuing part 𝐇°, records dressed per continuing
node only — must be imported from §9.1 by the reader. Statement-precision defect in a
document whose whole job is precise statements.

### F4 — JUSTIFICATION GAP — §9.4/§9.5: the "zero new open inputs" pricing claim vs the two new GD-4 rows

Quote (§9.4): "they are NOT in OL-4's printed clause list (which covers W-laws + (c0)
only) — a displayed SCOPE NOTE owed to the GD-4 owner: GD-4 gains the two terminal rows.
NO new open family is created."

Quote (§9.5): "Zero new open inputs beyond the GD families already on the mandatory
path — exactly the §D2.3 pricing."

(T-DEC) and (T-VERD) are two genuinely new unproved obligations (the document concedes
they are outside every printed clause list on file). "No new open FAMILY" is technically
true; "zero new open inputs … exactly the §D2.3 pricing" is not — §D2.3 priced "OPEN
(one lemma) over the GD residue," and the residue grew by two rows to make the emitted-
side tie (§9.4) close. Honestly displayed as a scope note, but the pricing sentence
overstates; §2's own pricing ("P(O-2a r5) + TB-CAP's D-12r perimeter + the GD residue via
2(B)'s hypothesis") also did not include these rows.

### F5 — JUSTIFICATION GAP — §§3, 4, 5: T_can(·) undefined in the displayed statements

CU-3's statement (§3): "…has a monic separable witness g in its level-N digit cylinder
with the corresponding history in T_can(g)." CU-4 (F4-S, §4): "𝐇 is verdict-carrying in
T_can(f)." Meanwhile §9.0: "No global T_can definition rides on it (the Cons^τ-SET died
with the O3design replacement)." No successor definition of T_can appears anywhere in the
document; the closest hint is K-OB-B's DES-6 re-key (§5: membership via ∃ dressing with
Cons_f, "membership ⇒ 𝐇 ∈ T_can(f) is DEFINITIONAL"), which suggests T_can(f) = the
Cons_f-dressed histories, but that is an inference, not a display. The load-bearing
predicate of two units' displayed statements is an undefined symbol within the file, in
a consolidation that records the death of its old definition.

### F6 — JUSTIFICATION GAP — §4 (F4-S assembly): acceptance ⇒ emission is unsupplied

Quote (assembly display): "F4-S = record-only acceptance (O-1thr §1.4) + CU-2 (the
accepted history is Cons_f) + 2(B) (verdict-carrying)."

CU-2, per its own §1 statement, applies to histories EMITTED by a complete run on f.
F4-S's hypothesis is only "Cert accepts (x_f, 𝐇)"; that the accepted 𝐇 is a run
(𝐇 ∈ Run_N(x_f)) is part of F4-S's CONCLUSION. The only displayed supply that could
bridge acceptance → run-membership is O-1thr Thm 3 (F1) ("T's chains are ALL AND ONLY the
realized pruned runs"), which is scoped to "any box fibering a decided ns-free T" with
the (E-N) caveat expressly OPEN ("can a level-N box fiber a thr > N tree?"). So the
displayed supply rows do not close F4-S as stated; the grade line "the walk is routine
given its inputs" understates this. Mitigation on record: the document itself grades CU-4
as ASSEMBLY, unwalked, and flags it "so the walk gets an owner rather than being silently
presumed" — the gap is displayed at the grade level but not at the supply-row level.

### F7 — JUSTIFICATION GAP — §0 registry vs §§4, 7: O-1thr Theorem 3's post-V24 survival never attested

Registry quote (O-1thr row): "V24 on rev 3: UNSOUND — 1 critical (REAL≡ non-halt
circularity) + gaps … sheared core + Thm 1 + (M6c) perimeter SURVIVED; rev-4 repairs
landed."

CU-4 consumes O-1thr Theorem 3 heavily ("(F1)… (F4) — both transported cylinder-exactly
by Theorem 3(a)"; Theorem 3(c) in the (E-N) caveat), and CU-7 (I-1)(a) rides the same
package. The survival list names only "sheared core + Thm 1 + (M6c)". Whether Theorem 3
is inside the "sheared core" is not stated anywhere in the file. Since V24's one critical
was a non-halt circularity and CU-4's consumed clause (F4) is precisely "interior chains
do not halt," the omission is load-bearing, not cosmetic. P(O-1thr r4) is displayed
everywhere it should be, so this is a registry-honesty gap (survived-set imprecision),
not a hidden conditionality.

### F8 — JUSTIFICATION GAP — §7 (I-1)(a): perimeter of the lift g unchecked

Quote: "For every monic separable lift g of the decided box x: … CU-2 applied to THE RUN
ON g then gives Cons_g."

CU-2's statement (§1) is under the standing perimeter (§0: "f monic separable ns-free of
degree n over O"). Nothing displayed shows that an arbitrary monic separable lift g of a
decided box is ns-free. Either ns-freeness of all lifts of such boxes is a fact of the
homes (not quoted here), or the (I-1)(a) discharge quantifies CU-2 outside its displayed
perimeter. Exactly the quantifier/perimeter-slip class the checklist exists for; one
displayed sentence would close it.

### F9 — JUSTIFICATION GAP — §6 (CU-6/OB2): the carrier→published-sense scope transport is priced as "one transcription"

Quote: "An OM factorization assigns each irreducible factor a saturated type; the O-2
dictionary's clause (i) — realized in O-2a as Theorem 2(B)'s invariant matching … plus
the BNS §2 definitional transcription … gives: ∼_OM preserves the per-factor (e, f) data."

Theorem 2(B), as quoted in this document (§9.1), is a statement about the ENGINE CARRIER
(hypothesis row Cons_f + OL-1, saturation at the last continuing node of a dressed
history). OB2's ∼_OM quantifies over "a COMMON OM factorization in the published sense"
(BNS). Transporting 2(B)'s invariant matching from carrier chains to published-sense OM
factorizations needs a types↔carrier bridge; the document prices this as "one
transcription + bookkeeping" while elsewhere stating that dictionary work of this shape
(K-DICT-OB1) "is consumed ONLY by D-16" (§7). Possibly the intended route is that the
(e, f)-from-type-data content is pure GMN literature (Def 3.9 + Cor 3.8) and needs no
carrier at all — but then the citation should be to the GMN pins, not to "O-2a clause
(i)". Either way, the displayed route has an unpriced scope step. The transcription duty
itself IS flagged ("complete modulo the BNS §2 transcription duty") — the gap is that the
duty as described (definitional transcription of Defs 1.7/3.1–3.2) may not cover the
transport.

### F10 — JUSTIFICATION GAP — §3 factor (a): the realizer's consumed conclusion is never displayed

CU-3's F3′ needs: ∃ monic separable g in the level-N cylinder realizing the history. The
(a) display characterizes O-14a′ Thms 1–3 (flank closed from bare coherence, the
`RRE(p, ZMod p)` instance, the (CR2) refutation quarantine) but never states the
witness-producing clause itself — in particular nothing displayed supplies SEPARABILITY
of the witness g, which F3′'s statement asserts. As a spot-read of "citation target
supplies the stated statement," this one cannot be confirmed from the document's own
quotes; the other factors ((b) D-14 pinning via O-1thr Thm 1 as quoted + CEIL-UB
one-directional, (c) definitional (O6)) do match their quotes.

### F11 — MINOR (record hygiene) — impossible chronology as written

Header: "consolidated Phase-B unit (Fable 'CUC', 2026-07-31)". Sources line: "Sources
(all read this session): `docs/MATH_COMPLETION_TREE_2026-08-01.md` …
`SYNTHESIS_PASS4_2026-08-01.md`". §9: "appended 2026-08-02". A unit dated 07-31 cannot
have read, that session, files dated 08-01, and carries an appendix dated 08-02 under an
07-31 header. Presumably forward-dated filenames/wave labels; should be regularized, as
the registry's audit trail leans on dates.

---

## Per-unit citation spot-reads (the charge's first item)

- **CU-2 (§1):** citation = O-2a rev 5 Thm 2(D) + (A)–(C), run-length induction quoted
  from O3adj §2 ("no-phantom is not a new induction at all…"). Internally the re-label is
  coherent and the residue (OL-1..6, G-EMIT falsifier, GD23 head) is fully displayed.
  Defect: F3 (statement overclaims 𝔈-membership vs §9.1). The OL-6 sole-consumer
  deviation note is properly displayed and propagated to §8.
- **CU-2t (§2, superseded by §9):** see the dedicated audit below. §2's own honesty at
  the time of writing ("OPEN (one lemma) — the honest flag") was exemplary.
- **CU-3 (§3):** factors (b), (c) match their quotes; factor (a) is F10. Governance
  claims (re-key executed, LC-COH consumed by nothing) are tree-level citations, taken as
  cited. Conditionality (P(O-1thr r4) for D-14; realizer leg unconditional + Lean-core)
  correctly displayed. The (CR2) refutation is displayed, not hidden — good.
- **CU-4 (§4):** the supply audit is unusually honest (Dfloor correctly identified as a
  CONSUMER, not a supplier; the (E-N) caveat displayed; NAME COLLISION on (F1)/(F4)
  displayed). Defects: F6 (F4-S assembly hole), F5 (T_can), F7 (Thm 3 survival). Grade
  "RE-LABEL-AS-ASSEMBLY … walk unwalked" is the right grade; "walk routine" is not yet
  earned.
- **CU-5 (§5):** K-OB-A's three legs match their quotes exactly (Thm 1 per site +
  `skeleton_finite` + the ONE CEIL-UB direction — the one-directionality is respected).
  K-OB-B is definitional-plus-CU-1 as displayed (P(CU-1 r2) shown). K-OB-E's fold into
  GD-4 and K-OB-C's strike are dispositions with named tree warrants. Clean.
- **CU-6 (§6):** F9. Conditionality and the BNS numbering hazard displayed.
- **CU-7 (§7):** the interface discharge lines each name displayed content, and the
  faithfulness legs (I-2) are honestly labeled OPEN GD content ("CU-7 discharges the
  interface's ATTRIBUTION, not these lemmas"). The attribution correction is argued from
  displayed content (single-polynomial (I-1); K-DICT-OB1 consumed only by D-16) and obeys
  the other-unit-file discipline. Defect: F8 (perimeter of g). Quote fidelity of the two
  superseded O5triple lines is unverifiable standalone.

## The §9.7 eight-point charge, point by point

1. **W3 carrier note vs O-2a (C1) verbatim:** UNCHECKABLE standalone — W3/W5 are
   paraphrased, not quoted. Internally the note is coherent and correctly labeled as this
   unit's reading; but it generates F3 against §1. Needs the home for quote fidelity.
2. **Lemma 2.17/Def 1.8 consumption:** PASS as quoted. The pin explicitly includes the
   −∞ side in the polygon (Def 1.8 quote) and gives length = ω (2.17(2)) and −∞-length =
   ord_φ f (2.17(3)); the proof of (i) uses exactly these, and "total length 1 ⇒ exactly
   one side" is correct. The (τ-hen) j₀ = 1 sub-case correctly books only the −∞ branch
   and concedes ω₁ = a₀ may exceed 1.
3. **ω = μ via (c2):** internally consistent; rests on the pinned ω-definition and "the
   identification O-2a's Theorem 2(B) proof displays" — consumed at P(O-2a r5),
   unverifiable further from here. No internal contradiction found.
4. **2(B) at its displayed hypothesis row:** PASS for (ii)-main — Cons_f + OL-1 displayed,
   saturation guard k' ≥ 1 noted, the k' = 1 unconditional instance correctly carved out,
   no realization semantics imported. The uniqueness TAIL of (ii) is F2.
5. **(T-DEC)/(T-VERD) engine-bookkeeping grade:** the classification is plausible and the
   O-1thr §1.4 corroboration is correctly firewalled (not consumed, no P(O-1thr r4));
   but F4 — the "zero new open inputs / exactly the §D2.3 pricing" sentence overstates.
6. **Corollary CU-2t-deep quarantine:** PASS. Displayed OUT of the lemma's grade,
   (REP-IRR) named with its unpinned-literature flag, owner routed. Genuine quarantine.
7. **j₀ ≤ 1 at every level:** PASS. φ_{k'+1} monic nonconstant, so φ² | f gives f a
   repeated root, contradicting disc f ≠ 0; φ-irreducibility indeed unused.
8. **Θ^τ collision with Θ-images:** the trailing-⊥ SEPARATION half PASSES (⊥ is not a
   ψ̂ value, by typing). The INJECTIVITY half is F1 — CRITICAL.

Also checked (falsifier-first duty, §9.6): properly cited as evidence, NOT as proof — no
∀-by-example move anywhere in the document. DEC-case coverage of F1/F3/F5 is mapped
honestly, and the unexercised Corollary corner is flagged as such.

## The §6.1 OB2/D-11 audit

SOUND as an audit, conditional on quote fidelity (unverifiable standalone). Given the
three quoted texts: the D-11 node text contains no ∼_OM quantifier; the distinction drawn
(σ-constancy across ONE continuation event's cylinder — served by O5triple Thm E + D-15 —
vs σ-invariance across ∼_OM classes in different cylinders) is real and decides the
question as posed; the O3design row's ancestry is correctly traced to a D-16-shaped
rationale. The governance handling is conservative and correct: CU-6 stays root-side
pending DELTA-3 sign-off, and the re-open trigger (if D-11's eventual PROOF pools
OM-equivalent instances) is displayed. No finding.

## The §0 pending-verdict registry

Honest in structure: every UNSOUND verdict on file is named as such (O-1thr V24, CU-1
V27, GD23 V26); running passes (V28, V29) are labeled RUNNING; every CONDITIONAL-ON-PASS
key in §§1–9 resolves to exactly one registry row (checked: P(O-2a r5), P(O-1thr r4),
P(O5t r3), P(CU-1 r2), P(GD23 r2) — all rows exist and are consumed consistently,
including §9.5's deliberate NON-consumption of P(O-1thr r4)). The VERIFIED-homes list and
the TB-CAP perimeter constant are carried consistently into §9's (iv). Defects: F7 (the
O-1thr survived-set omits Theorem 3 while two units consume it) and F11 (chronology).

## Summary of the shear

- **UNSOUND drivers:** F1 (critical, §9.3(iii)); F2 as its definitional root.
- **Survives at displayed conditionality:** Lemma CU-2t clauses (i), (ii)-main, (iv); the
  §9.4 tie modulo F4's pricing correction; CU-2/CU-5/CU-7 attributions modulo F3/F8;
  CU-3 modulo F5/F10; CU-4's grade (assembly, unwalked) modulo F5/F6/F7; CU-6 modulo F9;
  the §6.1 audit in full.
- **Repair shape (not executed here, per charge):** define record-consistency (the (t-i)
  tie) as a displayed predicate; restate (ii)-uniqueness and (iii)-injectivity over
  consistent (or run-emitted + (T-VERD)-pinned) records; rescope §1's statement to the
  continuing part; fix the §9.5 pricing sentence; attest or shear O-1thr Thm 3 in the
  registry; display the realizer's witness clause and g's perimeter.

**VERDICT: UNSOUND** (1 critical, 9 gaps, 1 minor; core forcing content and the audit
machinery survive as itemized).

*Verifier: fresh-context hostile pass (CUC pass 1), 2026-07-31. No file other than this
report was written; the reviewed document was not edited.*
