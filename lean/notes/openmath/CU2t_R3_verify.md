# CU-2t R3 hostile verification (unit CU2tp, 2026-07-31; fresh context)

**Object verified:** `lean/notes/openmath/CU_cluster_phaseB.md` §9 (the R3 text)
+ §§10–11, at repo HEAD (R3 = commit 81589e9). **Charge:** the §9.7 items
(1)–(8) (item (5) at the split row names) PLUS the §11 items (9)–(12), with
special attention to the (T-READ) no-other-supplier display, the
(T-DEC-dec)/(T-DEC-cor) split (corner fencing), and the per-half consumption
of the §9.4 tie. **Discipline:** quote-and-classify; nothing fixed.

**Sources consulted (verbatim, fresh reads):**
`O2a_phaseB_verifybrief_rev5.md` ((C1)–(C4), Lemma R, Theorem 1 §3, OL-1..6
§4, Theorem 2 §5, falsifiers §6) · `docs/GMN_citations.md` (Lemma 2.17 /
Def 1.8 / §2.1 ω-definition pins) · `docs/MATH_COMPLETION_TREE_2026-08-01.md`
(§D2.2 GD-4 row, §D2.3 CU-2t bullet, §D3.5) ·
`docs/ROOT_ASSEMBLY_2026-08-02.md` (Step 11, §3.3 GD-4/GD-6 row) ·
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (the 85670f7 adjudication
entry, read via `git show`) · `O1thr_phaseB_verifybrief_rev4.md` §1.4
(corroboration quotes only) · git history of the tree, ROOT, and CU files.

---

## VERDICT: SOUND-WITH-GAPS — 0 critical errors, 2 justification gaps, 1 minor

The lemma core (§§9.2–9.3) stands as at the R2 pass (byte-stable, re-audited
here at the charge's pressure points, nothing new found). Both R3 repairs
that carry logic — the (T-READ) row with its no-other-supplier display and
per-half tie consumption (G1), and the (T-DEC-dec)/(T-DEC-cor) split (G2) —
are VERIFIED correct as displayed. The two gaps sit in the R3 text's
*classification and record-keeping* layer: (G-α) the (T-READ) row's
"engine bookkeeping, not GMN mathematics" GD-4 grading is not justified by
the row's own content, and (G-β) the §9.4/§9.5 claim that the tree-side
two-row folds were "already executed" is contradicted by the tree text and
by §9.5's own item (1). Neither infects the lemma, the tie's logic, or the
three-row pricing arithmetic (all verified).

---

## 1. Findings (quote-and-classify)

### G-α — JUSTIFICATION GAP: (T-READ)'s GD-4 "not GMN mathematics" classification is unsupported by the row's content

> §9.4 (Pricing): "All three are GD-4-family instances (D2.2:
> 'emission/record discipline — engine bookkeeping, not GMN mathematics',
> proof-by-construction routes on record)"

and the row itself:

> §9.4 (T-READ): "the emitted terminal record's shape/position fields
> (e, h, ℓ, s, u), with sel = ⊥, are the (c1)-shape datum of the
> level-(k'+1) polygon side … Engine READ bookkeeping: the terminal
> record's shape fields are written FROM the level-(k'+1) polygon read the
> engine performs at the decided configuration"

Classification: **justification gap** (family/grade attribution; the
obligation itself is displayed, new, and unproved either way — the tie's
logic is unaffected).

The row asserts conformance of emitted fields to a GMN object (a side of
N_{k'+1}^−(f) read through ι) — exactly the statement TYPE of O-2a's
OL-2-min and OL-5, which O-2a rev 5 §4 declares as open MATHEMATICAL
conformance lemmas (intended proof routes through the O-3 conformance-unit
family, NOT proof-by-construction on record). The tree's own GD-4 charter
(§D2.2, verified verbatim) is "emission/record discipline (engine
bookkeeping, not GMN mathematics): W1–W5 …, domains, level-0 (c0), AUX …"
and flags K-OB-E as "the one semantic clause" — (T-READ) is a second
semantic clause entering under that charter unflagged. Sharper, verified
against O-2a §4:

* At k' ≥ 1 (DEC(τ-irr)): OL-2-min's premise reads "suppose the engine's
  stage read at level i + 1 on f over c emits the record (e, h, ℓ, s, u, …)"
  — NOT restricted to continuing records — so the mathematical half of
  (T-READ) (read-conformance at level k'+1 over c = Θ(𝐇°), a Cons_f chain of
  order k' ≥ 1) is an OL-2-min INSTANCE, i.e. already-priced GD-2-family
  residue; the genuinely new bookkeeping half is the missing TERMINAL
  binding clause (OL-6 explicitly exempts it: "Terminal records need no
  binding clause"). This decomposition is nowhere displayed.
* At k' = 0 (DEC(τ-hen)): no such decomposition exists — OL-5's premise is
  "emits the CONTINUING record ν₁" and its scope note says "Histories whose
  first node is terminal need no level-1 clause" — so the level-1 leg of
  (T-READ) is new mathematics-grade conformance content with NO sibling
  anywhere in the OL residue.

Consequence if left as-is: the GD-4 owner receives a read-semantics
obligation under a bookkeeping label with a "proof-by-construction" route
that cannot discharge its (RC-read) content; the honest routing is either a
displayed decomposition (terminal-binding row [GD-4] + OL-2-min instance
[GD-2] at k' ≥ 1, + a new OL-5-terminal sibling [GD-5-family] at k' = 0) or
a re-grade of (T-READ) as the scope note's SECOND semantic clause. The
count "three new unproved obligations on the mandatory path" survives
either reading; the FAMILY attribution ("no new open family") is what the
gap touches.

### G-β — JUSTIFICATION GAP: the "executed at the two-row count" claim is false for the tree; §9.5 contradicts its own item (1)

> §9.5: "Note: the R2-owed touches were meanwhile EXECUTED at the two-row
> count (tree §D3.5/§D2.3; ROOT r4 Step 11 + its §3.3 GD-4/GD-6 row), so
> (1)–(3) are now AMENDMENTS of executed text, not first executions"

> §9.4: "R2 priced TWO (and those two were already folded downstream: tree
> §D3.5/§D2.3, ROOT r4 Step 11 + its §3.3 GD-4/GD-6 row)"

Classification: **justification gap** (record-keeping accuracy of the owed
touches; no mathematical content rides on it).

Verified against the repo: the tree
(`docs/MATH_COMPLETION_TREE_2026-08-01.md`) is byte-stable since DELTA 3
(commit aa00747, which PRECEDES the R2 commit 567814d; corroborated by
`TREE_COMPLETENESS_AUDIT_2026-08-02.md`: "tree byte-stable since DELTA 3").
Its two touch-sites carry pre-R2 wording:

* §D3.5: "**zero new open inputs**; the two engine-bookkeeping terminal
  rows (T-DEC)/(T-VERD) are displayed GD-4-family instances" — the rev-1
  ZERO-count pricing (it names two rows but prices them at zero new
  inputs), exactly as §9.5's own item (1) admits ("which predates even the
  R2 correction");
* §D2.3's CU-2t bullet: "Status: OPEN (one lemma) over the GD residue" —
  no row count at all, and not even the PROVED-UNVERIFIED regrade.

Only the ROOT was executed at the two-row count (verified: ROOT r4 =
ea0336f, Step 11 "including the two NEW GD-4 terminal rows
(T-DEC)/(T-VERD)"; §3.3 GD-4/GD-6 row "two genuinely NEW unproved
mandatory-path GD-4 obligations"). So of the enumerated touches, (3)'s
ROOT half is a genuine amendment; (1) amends a ZERO-count tree sentence
(as item (1) itself correctly demands — "rewritten, not just
incremented"); (2) is a FIRST execution against §D2.3, not an amendment.
The note's blanket "(1)–(3) are now AMENDMENTS of executed text" misleads
the orchestrator it is addressed to: against §D2.3 there is no two-row
text to amend. (Also noted: R2's §10 F4 owed-touch list — "tree GD-4 row,
tree §D2.3 pricing line, ledger CU-2t line, GD-4 owner brief" — did not
include the ROOT at all; the ROOT folds were wave-14 events, so "the
R2-owed touches were meanwhile EXECUTED" is doubly imprecise: what was
executed was mostly not what R2 owed, and what R2 owed was mostly not
executed.)

What IS verified correct in the same block: the 0 → 2 → 3 arithmetic
(rev-1 zero-count = tree §D3.5's surviving sentence; R2 two-count = §10 F4
row + the pre-85670f7 ledger line "RESIDUE GREW BY TWO GD-4 ROWS" + both
ROOT folds; R3 three-count = the 85670f7 adjudication entry, read via
`git show`: "G1 = the missing (T-READ) third row (pricing undercount by
one — the GD-4 residue is THREE rows, not two; ROOT touch owed)"), and the
five touches are correctly enumerated and correctly marked OWED-not-executed
at R3.

### M-γ — MINOR: the §9.1 carrier note's "𝔈-legal in the (τ-hen) case" is loose (a₀ ≥ 2 required)

> §9.1: "so it is 𝔈-legal in the (τ-hen) case below (k' = 0; Theorem 1
> case (ii)'s shape), but at a saturated prefix (μ_{k'} = 1) appending ν
> would VIOLATE W3's interior clause."

Classification: **minor** (display looseness; corrected two sections later).

W3 as printed in O-2a (C1) is "μ_i ≥ 2 for all i < k; **and a₀ ≥ 2 if
k ≥ 1**" — so at k' = 0 the concatenation (ρ₀; ν) is 𝔈-legal only when
a₀ ≥ 2; the a₀ = 1 sub-case of DEC(τ-hen) (the Hensel booking) has no
𝔈-legal concatenation either. §9.2 displays this correctly ("W3 permits a
terminal NODE here only at a₀ ≥ 2; at a₀ = 1 the seam object is (ρ₀) plus
the machine record — the carrier note applies"), so the sentence is
loose-in-§9.1, not wrong-in-§9: read alone it suggests the whole (τ-hen)
case is concatenation-legal.

---

## 2. Per-charge-item record (all items executed; quotes checked against the named sources)

**(1) W3 carrier note vs O-2a rev 5 (C1) — PASS (with M-γ).** W3/W5 quoted
accurately ((C1) verbatim: "W3 (interior non-completeness): μ_i ≥ 2 for all
i < k; and a₀ ≥ 2 if k ≥ 1"; "W5: sel_i ≠ ⊥ for all i < k"). The arithmetic
is right: appending terminal ν to a length-k' prefix makes the saturated
node INTERIOR (i = k' < k = k'+1), so μ_{k'} = 1 violates W3. The seam-pair
reading is correctly attributed to THIS unit: O-2a's own §2 texts (Lemma R's
non-recovery display "if ν … is terminal and (𝐇°; ν) is well-formed and
Cons_f…", and (t-i)'s "the terminal node") treat terminal records as 𝔈
nodes. Independently confirmed: the G3 dichotomy is GENUINE — O-2a Theorem
2(D) as printed asserts the emitted history is "a well-formed element of 𝔈
(OL-4)", and OL-4(b) demands "interior selections have μ_i ≥ 2"; at a
(τ-irr)-decided run whose emitted history includes the terminal record,
this is unsatisfiable, so 2(D)-as-printed either means the continuing part
(reading (a)) or needs repair (reading (b)) — exactly the §1-flag/touch-(5)
routing. Correctly undecidable from the CU file.

**(2) Lemma 2.17 / Def 1.8 consumption — PASS.** The pins exist verbatim in
`docs/GMN_citations.md`: "**Lemma 2.17** (gmn.txt:1795). … (2) the length
of N_r^−(f) is ω_r(f); (3) the side of slope −∞ of N_r^−(f) has length
ord_{φ_r}(f). With: **ω_{i+1}(P) := ord_{ψ_i}(R_i(P))** (§2.1 displayed
definition, gmn.txt:1093) and **Definition 1.8** ('principal φ-polygon …
including the side of slope −∞', gmn.txt:427)." So length-of-N^− DOES
include the −∞ side, exactly as §9.3(i) consumes it (total length 1 ⇒ one
side; the j₀ ∈ {0,1} dichotomy via 2.17(3)); the (τ-hen) j₀ = 1 case
correctly books ONLY the −∞ branch and displays that ω₁(f) = a₀ may exceed
1 (the finite sides are other children). The "a polygon has at most one
−∞ side" step is Def 1.8's structure — fine.

**(3) ω = μ identification — PASS.** Rests on exactly: (c2) at i = k'
(giving ord_{ψ̂_{k'}}(R_{λ_{k'}}(f)) = μ_{k'}), the pinned §2.1
ω-definition (giving that this IS ω_{k'+1}(f)), and representative status
of φ_{k'+1} for the level-(k'+1) read (OL-1 at k' ≥ 1 — displayed in the
lemma's bracket and in §9.5's conditionality line; the "(D4)" half of the
proof's bracket covers only the k' = 0 base, harmless here since (i)'s
τ-irr leg has k' ≥ 1). The identical identification is displayed inside
O-2a's Theorem 2(B) proof ("ω_{k'+1}(f) = ord_{ψ̂_{k'}}(R_{λ_{k'}}(f)) =
μ_{k'} by (c2)"), as §9.3 claims.

**(4) Theorem 2(B) consumption — PASS.** O-2a §5 states (B) at hypothesis
row "[Cons_f + OL-1]" with saturation "asserted for k' ≥ 1 ONLY";
DEC(τ-irr) has k' ≥ 1, and §9.3(ii) consumes (B) on the all-continuing 𝐇°
with the row displayed verbatim. No run/realization semantics enter (the
seam object is run-free; the emitted-side tie is separately priced in
§9.4). The k' = 1 instance's UNCONDITIONAL claim checks: Theorem 1 is
stated and proved without OL-1, and its (D1) saturation clause is Cor 1.20
with (e, f) = (e₁, f₀f₁) = (accE₁, accF₁). The (τ-hen) legs consume
(D3)/(L3+) (verified present in O-2a §3's Theorem-1 proof: "the side of
slope −∞ has length E_∞ = 1 and carries the exact factor φ₁, which is
irreducible with (e, f) = (1, f₀)") and LIT-3 as pinned.

**(5) The four rows' grading — PARTIAL, see G-α.** (T-DEC-dec): control-flow
discipline; corroboration quotes verified in O-1thr rev 4 §1.4 ("IrrHalts(H)
:= the recorded identity [μ_last = 1]"; "irrVerdict is the verdict pair
(accE(H), accF(H))" — record-only), and correctly marked CORROBORATION ONLY
(no P(O-1thr r4) added). (T-VERD): accumulator arithmetic of the record
stream — genuinely bookkeeping. (T-DEC-cor)'s exhaustiveness clause: an
engine-scan claim (bookkeeping) — and verified CONSUMED BY NOTHING in the
lemma (the tie's antecedent conditions on decided sites, so no
exhaustiveness input is needed; it rides the scope note as stated).
(T-READ): the grading gap G-α above.

**(6) (REP-IRR) quarantine — PASS.** (REP-IRR) occurs only inside Corollary
CU-2t-deep, which is explicitly "NOT part of Lemma CU-2t's grade"; §9.5's
conditional-on list (P(O-2a r5) · D-12r · GD residue + three rows) excludes
it; the R3 fence sends corner-booked records to the Corollary "at the
Corollary's own conditionality ((REP-IRR) + GD-8's booking conformance)";
§9.6 honestly records the corner as UNexercised by any falsifier; and §11's
"What R3 does NOT change" preserves the quarantine. No leak found.

**(7) j₀ ≤ 1 separability at every level — PASS.** φ_{k'+1} = Lift_{k'}(c)
is monic of degree m_{k'+1} ≥ 1, hence has a root in K̄; φ² | f then forces
that root to be a multiple root of f, contradicting disc f ≠ 0.
Irreducibility of φ is indeed unused, as the §9.2 bracket claims ("the (D3)
argument verbatim, φ-irreducibility not used" — checked against the (D3)
original, which is the same argument at φ₁). Sound at every level.

**(8) Θ^τ vs Θ-image separation — PASS.** 𝔗's entries are (λ_i, ψ̂_i) with
ψ̂_i monic irreducible ≠ z ((C2) verbatim); ⊥ is not such a value, so a
Θ^τ-image (last entry (λ, ⊥, (E, F))) can never equal a Θ-image of an
all-continuing history of any length; strip-and-compare in (iii-a) is
valid (last-position determinacy of the appended entry). No collision.

**(9) (T-READ) per-half consumption + silent suppliers — PASS (the R3 G1
repair is correct), with G-α's classification caveat.** The
no-other-supplier display is verified complete: (i) Cons_f constrains no
terminal field — (C4) verbatim: "Cons_f places NO constraint on the fields
of a terminal last node"; (ii) (T-DEC-dec) speaks only of emission sites,
(T-VERD) only of the verdict pair — confirmed against the rows' texts. The
deeper sweep the display compresses was re-run independently against the
FULL OL residue: OL-5 covers only "the continuing record ν₁"; OL-6's
binding exempts terminal records explicitly; OL-2-min is a stage-read
hypothetical that no clause binds the emitted terminal record to (that
binding is exactly (T-READ)'s bookkeeping half, G-α). So NOTHING else on
file supplies (RC-read) for an emitted record — the row is genuinely
load-bearing, and the displayed junk-shape-fields failure scenario is the
correct counterfactual. Per-half attribution is EXACT: the read-entry half
consumes (T-READ) + clause (i) (unique-side single-valuedness); the verdict
half was re-derived here from (T-VERD) + clause (ii) alone — it nowhere
touches the shape fields, so it survives without (T-READ), as displayed.
(Reading note, no finding: "survives on those alone" means among the
terminal supply rows — both halves ride the common upstream
(T-DEC-dec)/(T-PREFIX) consumption, which the same sentence's chain
displays.)

**(10) The (T-DEC-dec)/(T-DEC-cor) split — PASS (the R3 G2 repair is
correct).** The corner (k' ≥ 1, μ_{k'} ≥ 2, j₀ = 1 at level k'+1) is
verifiably NOT a DEC configuration (DEC(τ-irr) needs μ_{k'} = 1; DEC(τ-hen)
needs k' = 0), T(f, 𝐇°) is undefined there by §9.2's "defined only on DEC
configurations", and the tie's conclusion explicitly excludes corner
bookings ("fenced to the Corollary by (T-DEC-cor) and are NOT covered by
this tie"). R2's self-contradiction ("ONLY at a decided configuration"
while admitting the corner) is genuinely eliminated: the split makes
(T-DEC-dec) a positive discipline claim at decided sites and (T-DEC-cor) a
fence + a displayed, unconsumed exhaustiveness obligation. The fence is
CONSISTENT with the Corollary's displayed conditionality (same two extra
conditions, (REP-IRR) + GD-8 booking conformance, named in both places; the
Corollary moreover does NOT claim an emitted-corner-record tie — only the
configuration's forcing shape — and the fence does not overclaim one).
Scoping completeness: the tie needs no site-exhaustiveness because its
antecedent is conditioned on decided sites; the exhaustiveness clause
(decided + corner = all verdict-carrying sites) is correctly displayed as
riding the scope note, consumed by nothing here. One residual observation
(no finding, GD-4/GD-8 territory as routed): the exhaustiveness clause is
itself a substantive engine claim — e.g. it excludes verdict-carrying
emissions at k' = 0, a₀ ≥ 2, j₀ = 0 sites — and its refutable surface is
correctly recorded in §11's falsifier-duty paragraph as owed WITH the row.

**(11) The §9.2a (c1) quotation + 5-tuple type-check — PASS (the R3 G4
repair is correct).** The quotation is VERBATIM against O-2a rev 5 (C4)
(diffed word-for-word), with exactly the declared omission (the trailing
"[REV 2 — V10-C7: …]" provenance bracket). The type-check is right: (c1)'s
shape datum at a level is exactly (e, h) = lowest-terms slope data,
ℓ = d(S), (s, u) = the initial point in the integer frame — five fields;
sel sits OUTSIDE (c1) ((C1) types it as the residual-selection coordinate;
W1/W2 govern it only when ≠ ⊥, and its content is read against (c2)), so
"sel = ⊥ in place of a selection" type-checks; the j₀ = 1 branches
correctly route through the §9.2 slope-−∞ convention (whose (L3+) basis in
Theorem 1 (D3) was checked at item (4)).

**(12) The 0 → 2 → 3 pricing + five touches — PARTIAL, see G-β.** The
arithmetic and its documentary trail are verified correct end-to-end
(rev-1 zero-count, R2 two-count, R3 three-count; the 85670f7 ledger entry
says exactly what §9.5 claims it says: "the GD-4 residue is THREE rows,
not two"). The five touches are correctly enumerated, correctly marked
OWED-not-executed, and touch (1)'s demand (rewrite §D3.5's superseded
sentence, don't increment) is correct and necessary. The
executed-fold-amendment characterization of (1)–(3) is the G-β gap: true
for the ROOT half of (3), false for the tree ((1) amends a zero-count
sentence; (2) is a first execution).

**§9.6 falsifier citations (rider on the charge) — PASS.** Checked against
O-2a rev 5 §6 verbatim: F1 = 3432 order-1-decided of 3600, 0 mismatches
(Hensel (1, f₀) + Cor-1.20 (e₁, f₀g₁) vs PARI ground truth); F3 = Family A
(4,1) 9/9 + Family B wild (4,2) 3/3 = 12/12 at order-2 saturation; F5 =
871 forced-j₀ = 1 samples, 0 mismatches on the 827 decided. All three
DEC-case attributions (τ-hen a₀ = 1 / τ-irr k' ∈ {1,2} / τ-hen j₀ = 1)
are accurate.

---

## 3. What this pass does NOT re-adjudicate

The byte-stable cores re-confirmed CONFIRMED-SOUND by the R2 pass (clauses
(i)/(ii)/(iv), the §9.3 proof block, the Corollary's internal argument)
were re-read at the charge's pressure points only (items (2)–(4), (6)–(8));
no new defect surfaced there. P(O-2a r5) itself, TB-CAP/T-6's own grade and
the D-12r perimeter, the GD residue rows OL-1..6, and the §0 registry are
consumed as conditionality keys, not re-verified — per the standing
pending-verdict discipline.

## 4. Disposition recommendation (verifier's, non-binding)

G-α and G-β are both LIGHT repairs confined to §9.4/§9.5's pricing prose
(plus M-γ's one §9.1 clause): no proof body, no statement, no tie logic is
touched by either. G-α wants one displayed sentence re-grading (or
decomposing) (T-READ)'s semantic half and syncing the "no new open FAMILY"
claim; G-β wants the "meanwhile EXECUTED / AMENDMENTS" note corrected to
match the actual tree/ROOT state (ROOT executed at two rows; tree not
executed since DELTA 3). Since the CU2tpass R2 verdict already stands at
SOUND-WITH-GAPS and every R3 logic repair verified CORRECT here, a further
full pass after these two prose repairs looks unnecessary; a spot-check of
the two edited paragraphs would serve.

*Verifier: unit CU2tp (fresh context, hostile charge). Nothing in the
target file or any source was edited by this pass.*
