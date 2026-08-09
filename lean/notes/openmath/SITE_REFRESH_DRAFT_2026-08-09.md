# SITE REFRESH DRAFT — 2026-08-09 (DRAFT ONLY; website repo NOT touched)

**Unit:** HE7-FINALIZE + SITE-REFRESH-PREP. **Status:** draft update plan for the
public uniformity map + paper at asving.github.io/uniformity/, per the standing
public-exposition-updates policy (refresh at major milestones; honest badge
vocabulary; the ORCHESTRATOR reviews, applies, and pushes — this unit made ZERO
edits in ~/asving.github.io; `git pull --ff-only` run first, already up to date
at the weld refresh a536084, 2026-08-07).

**Site state read:** `uniformity/index.html` (5,488 lines; 11 stages + story +
theorem headline + amber panel), `uniformity/paper.html` (407 lines; ends at the
weld section + honest-boundary restatement + sources), `uniformity/story.json`
(source data: headline / story / stages / openSurface / theoremU*), and
`uniformity/maps.json` (18 module-group graph entries). NOTE FOR THE APPLIER:
index.html carries the stages inline (stage 4, the weld, was added directly in
HTML); story.json's `stages` list (10 entries) already lags the HTML (11 stages)
— whichever pipeline is used (memory says /tmp/graph_build → uniformity/), the
edits below are specified against index.html as the rendered ground truth, with
story.json mirror edits listed where its fields duplicate the HTML.

---

## 0. The four pending milestones since the last refresh (a536084, weld)

1. **STAGE ONE COMPOSED-COMPLETE** (repo commit b49e111, 2026-08-08). Every named
   box of the uniformity theorem chain — W-12.D (reduction) ∘ GENIND.B (induction)
   ∘ GENHN.A/B (general stage laws) ∘ HE6.A(r1) (fractional-height test family) ∘
   HE7.A ((SLOT₂)+(LIFT₂) + the terminating ladder) — is CLOSED AT COMPOSITION
   GRADE. Reconciliation: the Codex-widened box is a literal instance of HE7
   (HE6R1_RECON, seal 4f5ebaa, verdict 850e77e; 682 PARI jobs, 0 mis-decisions).
   Content: one R_τ ∈ ℚ(q) per splitting type, every degree, every prime
   including wild, Σ_τ R_τ = 1, equal to the Haar density — at composition grade.
2. **THE DISTRIBUTION SUITE** (notes BCFGTIE_2026-08-08.md, MOMENTS_2026-08-08.md).
   E_n(q) = q/(q+1) (monic, every n ≥ 2) and E_n^proj = 1 exactly; the full PGF
   recursion; moment stabilization M_k(n) = M_k(2k); the limiting law (iid
   geometric discs); exact ties against the repo's committed BCFG transcription
   rows at small n (compared rows through n ≤ 7 across the suite). Both notes at
   attempt grade 0/2 with sealed batteries GREEN (BCFGTIE: 93 checks, 0 fails,
   4/4 teeth).
3. **HOSTILE-ARC FIRST ACCEPTANCES.** HE7 ACCEPTED 2/2 INCLUDING ITS ANNEX STACK
   — the program's first acceptance AND its first complete challenge-to-discharge
   cycle (body PE2 8f5f2a6 + PE3 111ac7f; Codex ratification returned CHALLENGE
   with 1 CRITICAL at the level ≥ 3 displays; ANNEX R repaired it in full;
   annex passes 4a613d8 + a472155 both CLEAN; first machine σ at a fired level-3
   node anywhere: n=16 79/79 PARI, n=24 μ₃=3 48/48, plus a triple-oracle leg;
   note FULLY FROZEN at ca3754d). GENH4 BODY ACCEPTED 2/2 (PE4 e15308d + PE5
   11dbd23, frozen at 4b0d946) — but its own Codex ratification is a CHALLENGE
   (5c8d2fd) and its annex-stack pass #1 was NOT clean (a8dec16): annex repair
   owed. The refresh must carry both halves.
4. **TAMEK** (note TAMEK_2026-08-08.md; Asvin-directed). Roots in a fixed tame
   K/ℚ_p: X_K = #Hom(ℚ_p[x]/f → K). The embedding count is elementary (TK-0:
   divisibility + one congruence between twist letters); X_K is the corpus's
   first letter-sensitive statistic, visible already at the mean; the
   Cohen–Lenstra-style mean conjecture was REFUTED by its own preregistered
   sealed falsifier (battery 202/207 with the 5 fails = CONJ-MEAN firing, 4/4
   teeth) and REPLACED by a corrected exact law (S4.R) matching all 17 sealed
   unramified (cell, n) measurement points; the unramified-K mean law is exact
   at every computed n (closed forms displayed per cell). Attempt grade 0/2.

---

## 1. Badge vocabulary for this refresh (the honesty frame, fixed up front)

The site already defines "accepted" (consecutive clean fresh-context hostile
passes, two model families, dated record). This refresh adds lower grades and
must never blur them:

- **machine-checked** — Lean kernel; reserved for the unchanged set (degree-2
  theorem unconditional; order-0 capstone; the mapped Lean corpus). NOTHING in
  this refresh adds to it.
- **accepted (2/2)** — the existing definition. Newly applicable to: HE7 (incl.
  annex stack), GENH4 (BODY only).
- **composition grade** — composed end-to-end with every named box closed and
  machine-instanced, but the adversarial bar NOT yet passed on every box;
  explicitly BELOW accepted. Applies to the stage-one theorem chain.
- **attempt grade (0/2)** — proofs composed + sealed preregistered battery
  green; no hostile pass yet. Applies to BCFGTIE, MOMENTS, TAMEK.
- **boxed** — a fenced open lemma (existing usage; unchanged).
- **PROHIBITED in every new sentence:** novelty claims on the distribution
  results — novelty is UNSEARCHED; and any "BCFG says/confirms" phrasing — the
  BCFG faithful cite is OWED-EXTERNAL, so every comparison sentence must say
  "the repo's committed BCFG transcription" (arXiv:2101.09590 may be cited as
  the conjecture source, which the page already does by author names).

---

## 2. Changes to uniformity/index.html (the map)

### 2.1 The dateline (line 66, `p.post-date`)
Append before the closing tag: ", and stage 5 (the composed chain and the
distribution of the root count) with the refreshed story added August 9, 2026"
— renumbering note: the new stage is inserted as stage 5 AFTER the weld (stage
4), so old stages 5–11 become 6–12 (pure renumber, no text change; the weld
stage precedent shows dated stages are accepted practice).

### 2.2 The theorem headline (line 71; mirror in story.json `headline`)
UNCHANGED in its certified-unconditionally / certified-conditionally sentences
(the Lean boundary did not move). ADD one sentence before the final amber-panel
pointer:

> "As of August 8, 2026, the informal proof chain behind that conditional
> certification is COMPOSED END-TO-END at every degree and every prime,
> including wild — at composition grade, a grade this page keeps strictly below
> 'accepted': every named box is closed and machine-instanced, and the
> adversarial-verification program that upgrades boxes to accepted is running,
> with the first two acceptances in (the story dates them)."

### 2.3 The story: four new dated paragraphs
Inserted after the current last narrative paragraph (the 2026-08-04 engine
acceptance) and before the closing "The formalization's contribution" paragraph.
Mirror in story.json `story`. Full proposed text:

**[P1 — stage one composed-complete, dated August 8, 2026]**
> "On August 8, 2026, the program crossed the line it had been walking toward
> since the weld: stage one — the mathematics of the uniformity theorem — is
> composed-complete. The theorem chain now has a name at every joint: a
> reduction (W-12.D) feeds an induction (GENIND.B), whose stage laws (GENHN.A/B)
> consume a fractional-height test-family theorem (HE6.A) and the two-level
> slot-and-lift theorem with its terminating ladder (HE7.A) — and the last
> reconciliation, checking that a verifier-widened configuration is a literal
> instance of the general theorem, closed with 682 exact PARI jobs and zero
> mis-decisions. Composed through this chain: one rational function of the
> residue-field size per splitting type, at every fixed degree and every prime
> including the wild ones, the functions summing to 1 identically and equal to
> the Haar density. The grade is the honest headline: COMPOSITION GRADE means
> every box is closed, written, and machine-instanced — it does not mean
> accepted. The bar this project holds is the hostile-arc program (fresh-context
> adversarial passes, two model families, two consecutive cleans), and at
> composition day the boxes stood at grades from 0/2 upward. En route, the same
> week produced the quartic and quintic density tables and the distribution
> results of the next paragraph."

**[P2 — the distribution suite, dated August 8, 2026]**
> "Two companion notes turned the density machinery on the simplest random
> variable it governs: the number of p-adic roots of a random degree-n
> polynomial. The expected count is q/(q+1) for every degree n ≥ 2 in the monic
> model — degree-independent — and exactly 1 in the projective model; the full
> probability generating function obeys a cluster recursion; every fixed moment
> stabilizes in degree (the k-th moment is constant once n ≥ 2k); and as the
> degree grows the law converges to an explicit limit with an independent-discs
> reading. Where rows exist to compare, the suite ties the repository's
> committed transcription of the Bhargava–Cremona–Fisher–Gajović tables exactly
> (compared rows through degree 7). Two honesty flags, stated as loudly as the
> results: these notes are at ATTEMPT GRADE (proofs composed, sealed
> preregistered batteries green — 93 exact checks with all four planted
> falsifiers caught on the expectation note — but no hostile pass yet), and
> NO NOVELTY IS CLAIMED for any of it: the literature search has not been done,
> and the external citation against the published BCFG paper is still owed —
> every comparison above is a statement about the repository's committed
> transcription, not about the paper."

**[P3 — the first acceptances + the challenge-to-discharge cycle, dated
August 9, 2026]**
> "The hostile-arc program recorded its first acceptances, and — more useful to
> a reader gauging the bar — its first complete challenge-to-discharge cycle.
> HE7, the two-level slot-and-lift theorem at the top of the chain, passed two
> consecutive clean fresh-context passes; then the decorrelated-model
> ratification sweep, reading surfaces no earlier pass had audited, returned a
> CHALLENGE: one finding graded critical, scoped exactly to the note's level-3
> proof displays (first live at degree 16, a region with zero machine coverage
> at the time). The acceptance was annotated, not revoked; the repair became a
> dated annex re-basing the offending recursion with an explicit cocycle; the
> repaired region received the first machine verification at a fired level-3
> node anywhere in the program (79 of 79 degree-16 members against PARI, then
> 48 of 48 at degree 24, plus a triple-oracle leg retiring the shared-oracle
> blind spot); and the annex stack itself then passed two clean passes. The
> note is now fully frozen, corrections as dated appends only. GENH4 — the
> quartic-degree discharge — has its BODY accepted at the same 2/2 bar, with
> the symmetric honesty: its own ratification sweep returned a challenge, and
> its annex stack's first pass was not clean, so its annex repair is still
> owed. Acceptance on this page is a property of a named text at a named date,
> and challenges after acceptance are part of the record, not exceptions to it."

**[P4 — TAMEK, dated August 9, 2026]**
> "A reader-posed question opened a new statistic: fix a tame extension K of
> ℚ_p and count the roots of a random polynomial that land in K. The embedding
> count itself is elementary — tame fields coordinatize as (ramification,
> residue degree, twist letter), and containment is a divisibility plus one
> congruence between letters. The finding is that this statistic SEES the twist
> letter, already at the mean: two tame quartic fields of the same shape over
> ℚ₃, differing only in letter, have measurably different expected root counts
> — the first letter-sensitive statistic in the program, where plain root
> counts are provably letter-blind. The Cohen–Lenstra-style guess for the mean
> was refuted by the note's own preregistered falsifier — the sealed battery
> returned 202 of 207 with all five failures exactly the falsifier firing —
> and replaced by a corrected exact law that matches all seventeen sealed
> unramified measurement points; for unramified K the mean law is exact in
> closed form. Attempt grade: sealed battery green, no hostile pass yet;
> no novelty claim (unsearched)."

### 2.4 New stage 5: "Stage one composed-complete: the theorem chain, its arcs, and the distribution of the root count (added 2026-08-09)"
Inserted after stage 4 (the weld), same `<details class="stage">` pattern; old
stages 5–11 renumber to 6–12. Like stage 4, this stage is prose-note territory:
NO Lean badges — grades carried in node text, opening sentence of the stage body
states "none of this stage is Lean; the machine-checked results are exactly what
they were before it" (reuse stage 4's closing formula). Nodes (each = one
`<details class="node">` with a summary line + note text; grades per §1):

- **The composed chain** — the five named boxes and the reconciliation verdict
  (682 PARI jobs / 0 mis-decisions); grade: composition grade, with the grade
  definition inline. Frontier sentence: the hostile-arc program is the bar; the
  per-note board (which notes stand at 2/2, 1/2, 0/2) lives in the repo's dated
  record, and the page names only the two acceptances explicitly (HE7; GENH4
  body) to avoid a stale-grade table on a static page.
- **HE7 accepted, challenge discharged** — the P3 content in node form: 2/2 body,
  CHALLENGE, ANNEX R, first level-3 machine σ (79/79 n=16; 48/48 n=24 μ₃=3;
  triple oracle), annex stack 2/2, fully frozen.
- **GENH4 body accepted** — 2/2 body; challenge + annex repair owed, stated in
  the same sentence as the acceptance; the eleven quartic densities rest on
  frozen text whose supplier stack still carries live 0/2 notes (W-12, HEX3,
  GENIND) — conditionality displayed, not footnoted.
- **The expected number of roots** — E_n = q/(q+1) monic all n ≥ 2, E^proj = 1;
  attempt grade; battery 93/0 with 4/4 teeth; transcription + novelty caveats
  verbatim from §1.
- **The whole distribution** — PGF recursion, M_k(n) = M_k(2k), sum rule,
  limiting iid-geometric-discs law; attempt grade; same caveats.
- **Roots in a fixed tame field** — TAMEK node: TK-0, letter-sensitivity at the
  mean, CONJ-MEAN refuted by preregistered falsifier + corrected exact law
  S4.R (17/17 sealed unramified points), unramified closed forms; attempt
  grade; the refutation-by-own-falsifier told as the methodological point.

### 2.5 The amber panel (story.json `openSurface` + its HTML rendering)
One dated append line (no existing sentence edited):

> "Dated note (2026-08-09): the informal theorem chain at general degree is now
> composed end-to-end (composition grade — see stage 5); this is NOT a Lean
> event: the machine-checked set on this panel is unchanged, and the full
> uniformity theorem remains not machine-checked."

### 2.6 story.json mirrors
`headline` += the §2.2 sentence; `story` += the four §2.3 paragraphs;
`openSurface` += the §2.5 line; `stages` list: add the stage-5 entry if the
build pipeline consumes it (verify against /tmp/graph_build before editing —
the list is already one stage behind the HTML, so the applier should either
sync it fully or confirm it is dead data). maps.json: NO change (Lean module
graph; nothing in this refresh is a Lean module).

---

## 3. Changes to uniformity/paper.html

### 3.1 New section after the weld section, before "Sources"
Title: **"Stage one: the chain composed, the first acceptances, and what the
machinery says about root counts (August 8–9, 2026)"**. Four paragraphs =
tightened versions of P1–P4 (same facts, same grades, same caveats; the paper's
register). Plus one closing paragraph restating the honest boundary:

> "The honest boundary, restated after this milestone. Composition grade is
> below accepted, and accepted is below machine-checked; this section added
> nothing to the machine-checked set. The chain's boxes are queued through the
> hostile-arc program; HE7 (including its annexes) and GENH4's body are the
> two acceptances so far, GENH4's annex repair is owed, and the distribution
> and fixed-field results stand at attempt grade with sealed batteries green
> and no hostile pass yet. No novelty is claimed for the distribution or
> fixed-field results — the literature comparison is unsearched and the
> external BCFG citation is owed; every BCFG comparison in this section is
> against the repository's committed transcription."

### 3.2 The existing honest-boundary paragraph (end of the weld section)
UNCHANGED (it is the weld section's own dated boundary; the new section carries
its own). The page-top dateline gains "updated August 9, 2026".

### 3.3 Sources
ADD: Bhargava, Cremona, Fisher, Gajović — arXiv:2101.09590 — with the explicit
caveat "(cited as the conjecture's source; the development's numeric
comparisons are against a transcription committed in the repository, and the
faithful-citation check against the published tables is still owed)". [If the
orchestrator prefers not to cite until the faithful-cite lands, the fallback is
to keep the author-name mention with no bibliography entry — either is honest;
the caveated entry is recommended since the conjecture attribution is already
on the page.]

---

## 4. New results added, each with its honest grade (summary table)

| result | where it lands | grade on the page |
|---|---|---|
| Theorem chain composed end-to-end (all degrees, all primes) | headline sentence + P1 + stage-5 node | composition grade (defined inline; explicitly below accepted) |
| HE7 (SLOT₂/LIFT₂ + ladder) | P3 + stage-5 node | ACCEPTED 2/2 incl. annex stack; challenge discharged; frozen |
| GENH4 (quartic discharge) | P3 + stage-5 node | body ACCEPTED 2/2; challenge + annex repair owed (displayed) |
| E_n = q/(q+1) (monic, n ≥ 2); E^proj = 1 | P2 + stage-5 node | attempt grade 0/2; battery 93/0; no novelty claim |
| PGF, M_k(n) = M_k(2k), limiting law | P2 + stage-5 node | attempt grade 0/2; no novelty claim |
| BCFG-transcription ties (rows compared, n ≤ 7) | P2 caveat sentence | tie to COMMITTED TRANSCRIPTION only; external cite OWED |
| TAMEK: X_K letter-sensitive; CL guess refuted; exact unramified law | P4 + stage-5 node | attempt grade 0/2; refutation = preregistered falsifier firing |

## 5. What does NOT change

1. The headline's two certification sentences (unconditional degree-2;
   conditional general-degree) — the Lean boundary did not move.
2. The amber panel's PROVED / PROVED-CONDITIONALLY census (append-only per §2.5).
3. Stages 1–4 and old 5–11 (renumber only), including the weld stage and all
   node texts, badges, and acceptance records.
4. The two capstone axiom-footprint claims and every "machine-checked" sentence
   — the standing repo invariant: NEVER describe the full theorem as
   machine-checked; this refresh adds no Lean content.
5. maps.json (no new Lean modules) and the badge legend (no new badge classes;
   grades ride in node text as in stage 4).
6. The existing sources except the one caveated BCFG addition (§3.3).
7. The 2212.00294 attribution and framing sentences.

## 6. Execution checklist for the applier (orchestrator)

1. `cd ~/asving.github.io && git pull --ff-only` (again, at apply time).
2. Apply §2 to index.html (+ story.json mirrors), §3 to paper.html.
3. Renumber-check: stage numbers 1–12 monotone; internal anchors (`id=` slugs)
   unchanged — only the displayed `stageno` digits move.
4. Fresh-reader pass per the standing policy: run the Codex minimal-context
   exposition review on the four new story paragraphs + the new paper section
   BEFORE pushing (broadcast-writing discipline; the caveat sentences must
   survive editing).
5. Verify no new sentence contains "novel", "first proof", "new result" (grep),
   and no "BCFG" without "transcription" within its sentence except the
   attribution/citation lines.
6. Single commit, message pattern: "Uniformity map + paper: stage one
   composed-complete + first acceptances + distribution suite + TAMEK
   (2026-08-09) — honest grades throughout". Push.

*Draft prepared 2026-08-09; repo copy at
lean/notes/openmath/SITE_REFRESH_DRAFT_2026-08-09.md.*
