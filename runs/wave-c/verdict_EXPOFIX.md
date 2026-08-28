# VERDICT — UNIT EXPOFIX: all 28 EXPOAUD findings fixed in the site working tree (2026-08-28)

**Charge:** fix the 28 numbered findings of `runs/wave-c/verdict_EXPOAUD.md` in the
website repo's working tree (`~/asving.github.io`: `uniformity/index.html`,
`uniformity/paper.html`, `index.html`). **Nothing committed or pushed in either repo** —
the orchestrator reviews and pushes. `git pull` was NOT needed: the branch was already
up to date with origin and the draft was safe in the working tree (checked before touching
anything).

**Ground truth consulted:** `docs/PROJECT_STATE.md` §§2–4, `docs/LOG.md` 2026-08-27/28
entries, and the Lean sources directly:
`leanfinal/Uniformity/Density/GenuineDensity.lean` (the "NOT the Haar measure … not
formalized" docstring, lines 263–265), `ChapI/I10_I15_I18.lean` (the real field list +
the honesty-fence ledger: `w1` no-field debt, `TypeOfFaithful` unbound `True`-bodied
carrier, lines 50–80 and 164–216), `ChapI/IFC7.lean` (section variables incl.
`[Finite (ResidueField O)] [IsAdicComplete …]`), `ChapC/C133mh9.lean` /
`C133mh15.lean` / `C132kp6b.lean` (section variables; `h2`/`hq` definitions),
`ChapC/C133mh14.lean` + `C133mh15.lean` (the transport's sole non-core axiom is
`exists_dvDissection` — ONE dissection leg, not the pair), `ChapC/C66b.lean` (the
retirement theorem is proved by `C133h0leg.fgmn_dv_exact_mul_full`).

**The countermodel count (finding 5), adjudicated against LOG 2026-08-28:** A-I.6
(`AI6_probe.lean`, ¬CapstoneHypotheses 4, compiled Lean-core) and A-I.7 (`REX_probe.lean`,
the mp1 leg at Λ = −1, compiled Lean-core) are the TWO compiled countermodels; A-I.8 was
a structural source-faithfulness stop-line (DWR: the GN-selected factor can never equal
the recentered key), NOT a machine refutation. Every "three compiled countermodels /
three machine-forced repairs" claim was rewritten to "three amendments — two forced by
compiled countermodels, one by a structural source-faithfulness finding."

## Per-finding disposition (all 28: FIXED unless noted)

| # | Finding (short) | Disposition |
|---|---|---|
| 1 | Haar-density scope overclaimed | FIXED — the formal sense ("the proved limit of the proportions of coefficient boxes consistent with the type; the Haar identification is not formalized — it would need measurability of the locus") is now stated at every publicity site: root blurb, map headline ¶ ("one scope note on the word density"), the as-of-08-28 ¶, the stage-13 intro, the UniformityStatement node (quoting the source caveat), the cubic group oneliner + role + five-formulas note, the amber dated update, and the paper milestone ("formally the density *is* exactly that limit"). |
| 2 | "same task" / "reduction" — no converse shown | FIXED — group (a) role now says "machine-checked sufficient condition … one direction only, no converse is formalized, an assembly, not an equivalence and not an exact reduction"; "one direction only / one-way / no converse" added to the map headline ¶, stage intro, assembly node, group title ("stated — with a one-way assembly from open hypotheses"), amber update, paper milestone + boundary ("a sufficient condition, not an equivalence"), root blurb ("one-way implication"). All "reduction/reduces to" wording about the capstone removed. |
| 3 | "eleven fields itemize exactly" false (w1 no field; TypeOfFaithful omitted; WLE exporter) | FIXED — the CapstoneHypotheses node now ends: "two ledger items the eleven fields do NOT capture … a fourth True-bodied carrier vocabulary (TypeOfFaithful) is owed with no binding field, and one named debt (w1, from amendment A-I.1) has no field at all"; deepTwist status now includes "plus a per-level exporter still to be built"; every "itemize(d) exactly" replaced by "fields, together with a recorded ledger of debts that have no field yet, state what remains" (map ¶73, amber, paper, root blurb); the closing "exact distance" claim replaced (see 19). |
| 4 | Placeholder count internally inconsistent ("four fields") | FIXED — canonical formula used everywhere (stage intro, amber update, paper boundary): TWO fields literally `True` (jd0, genhnBox2) + FOUR named carrier vocabularies with `True` bodies (three bound by fields — windowPinning/genhnHE/genhnTow1 — one, TypeOfFaithful, not yet bound) + the no-field debt w1. Matches I10_I15_I18.lean's honesty fence verbatim. |
| 5 | "three compiled countermodels" FALSE | FIXED — "two compiled countermodels and one structural adjudication — three amendments, not three refutations" everywhere: stage intro, group (a) oneliner, the refuters node title + note (explicit tally sentence added), map ¶73, amber, paper milestone. The node's A-I.8 sentence (already correct) retained. |
| 6 | Trichotomy excludes A-I.8's amendment kind | FIXED — stage intro + paper now read: "proved, refuted by a compiled countermodel, or amended by a recorded, adjudicated statement change (two … forced by compiled countermodels and one by a structural source-faithfulness finding)"; "and nothing else" dropped. |
| 7 | Duplicate stage number 6 | FIXED — the new stage renumbered **13** (`stageno` 13; existing stages 1–12 untouched). All cross-references updated: post-date line, headline ¶ (×2), as-of ¶ (×2), amber update (×2), legend/tally, paper boundary. `grep 'stage 6\b'` over all three files: zero hits. `id="second-formalization"` unchanged (no anchors depend on a number). |
| 8 | "Exact Lean statement" promise violated | FIXED — (a) the how-to-read ¶ now discloses the stage-13 record nodes and abridged blocks; (b) section-variable context added as comment lines to `genuineDensity_three_exact` (incl. Finite residue + adic completeness), `theoremA`, `blockFrontier_of_context` (incl. π), `s2Mu3_calculus_nonempty` (defines h2, hq); (c) the CapstoneHypotheses block relabeled "Abridged field skeleton — NOT the exact Lean text: the ⋯ elide the configuration binders…"; (d) all three record blocks (amendments, retirement, depth-4) relabeled "The record (repository-internal paths …)". |
| 9 | `proved` badge on the amendment-loop process bundle | FIXED by rescoping, not by badge change — node retitled "The refuters: two compiled countermodels force repairs…; a third amendment from a source-faithfulness stop-line" and the note now states: "The proved badge on this node certifies exactly the two refuter theorems and the byte-unchanged assembly theorems through the amendments; the amendment history itself is a dated repository record, not a theorem." The badge now names machine-checked Lean-core theorems that exist. |
| 10 | `proved` badge on trusted-base node certifies repo facts | FIXED by splitting the node — the retirement node (badge proved) is scoped: "the proved badge … certifies the two Lean facts — the retirement theorem (statement bytes unchanged, Lean-core footprint) and the outright-proved would-be cite; what the allowlist now contains is the next node's record, not a theorem"; its record block shows C66b.lean + the proving theorem (verified against source). The allowlist moved to a NEW node wearing **cited axiom**. |
| 11 | `conditional` badge on blockFrontier misleading | FIXED — new legend badge **proved + cite** ("machine-checked; the axiom printout is Lean core plus named, audited literature axioms — a dependence through the axiom graph, not an explicit hypothesis of the statement"); blockFrontier wears it, with the note explaining the distinction from `conditional` and why it is the costlier kind of dependence. `uniformity_of_capstoneHypotheses` keeps `conditional` (legend-honest: explicit displayed hypothesis). Also corrected en passant: the footprint is ONE dissection leg (`exists_dvDissection`), not "the cite pair" (draft error, verified against C133mh14/15). |
| 12 | Tally undercounts the trusted base | FIXED — tally rewritten: "…and 5 cited-axiom nodes — 4 in the first development plus stage 13's allowlist node, which alone carries the second library's six declared axiom constants, so the global trusted base to count is the first development's four cited items PLUS those six." Counts recomputed from the actual badges: 357 total = 144 proved, 66 conditional, 1 proved + cite, 15 notes, 6 measured, 22 open, 98 definitions, 5 cited-axiom nodes (stage-13 badges machine-inventoried: 6/1/1/1/2/1). |
| 13 | "everything else it has landed prints Lean core" false | FIXED — stage intro now: "the specifically named results of this stage — the cubic theorem, Theorem A, the depth-2 calculus, the capstone assembly — print Lean core alone, while results that consume a cite print Lean core plus that cite (one is shown below)"; the allowlist node adds "these six propagate into the axiom printouts of downstream results that consume them." |
| 14 | "six audited citations each with a faithfulness record" unsupported | FIXED — everywhere: "six declared literature axioms — six axiom constants, not six independent bibliographic results: two are the two legs of one dissection theorem, one a composite record — five with completed faithfulness records, the sixth (the termination cite) still being authored" (allowlist node, paper, amber; map ¶73 carries "one audit record still being authored"). "Owner review row" jargon → "the project's human-review queue" (see 25). |
| 15 | Root-blurb ring scope omits finite residue field | FIXED — "with finite residue field" inserted at the root blurb, the map headline degree-3 sentence, and the cubic group role. (Paper milestone and amber already carried it; verified.) |
| 16 | Depth-2 calculus presented as supplying deepTwist | FIXED — everywhere the calculus is now "a first concrete prototype of the kind of tower demanded, not yet a supplier of the field" / "an input to that campaign, not a partial inhabitant": the CapstoneHypotheses deepTwist line, the calculus group oneliner + role (which also now names r ≥ 4 + the per-level exporter), and the paper ("an input to that campaign rather than a discharge of the field, which demands greater depth"). |
| 17 | Quadratic "a proved special case" of the cubic | FIXED — map: "the quadratic theorem is an input to the cubic proof, not a special case of it" (exact degree-2 values proved in the same library, consumed as an inner tower). Paper wording ("whose exact values the cubic proof consumes as an inner tower") was already correct — verified, untouched. |
| 18 | "every statement … signed" + bare 1,240 | FIXED — stage intro + paper: "the statements the campaign runs on were first signed — 1,240 named statements …, of which 491 are definitions or hypothesis-carrying interfaces rather than provable propositions, and a handful of obligations are carried as recorded debts because their vocabulary cannot yet be written." |
| 19 | "at full strength"/"exact distance" headline emphasis | FIXED — every "at full strength" is now in the same sentence as the density-sense scope and the one-way/uninhabited status; group (a) retitled ("stated — with a one-way assembly from open hypotheses"); the amber close replaced: "its statement is a formal object a proof assistant checks, and the remaining distance is typed and recorded — most of it as fields of one structure, the rest as named debts in the ledger" (no more "exact distance"). |
| 20 | "not provably empty" as certified positive | FIXED — replaced everywhere (map ¶73, stage intro, amber implicitly) by the checkable content: "the two compiled refutations that repaired its statement apply only to its retired earlier forms, no refutation of the current form is known, and no nonemptiness result is proved either." |
| 21 | Paper's stale "Exact status" section | FIXED — the paragraph now opens with a dated supersession note ("Status as written on August 10, 2026 — since partially superseded: on August 28 the degree-3 case was proved unconditionally in a second formalization, in that library's stated density sense — see the final milestone entry") and the n = 3 sentence carries an inline pointer "(since proved outright in the second formalization — August 28 entry below)". |
| 22 | "not proved — at any grade" ambiguous vs. corpus milestones | FIXED — paper boundary now scopes: the second library's full-strength statement "is not proved at any grade beyond degree 3," and the prose-note corpus "addresses a different, per-prime statement and remains where those entries left it — accepted at the hostile bar, not machine-checked." |
| 23 | Two conditional results conflated | FIXED — root blurb: "in a second library (separate from the map's earlier per-prime conditional theorem, which stands unchanged)"; map ¶73: "a certificate separate from those above (neither consumes the other)"; stage intro: "a broader ring scope … though a separate certificate: the density notions differ as just noted, so neither subsumes the other"; amber update names both separateness clauses. |
| 24 | Current boundary buried under the obsolete one | FIXED — a reading note now opens the amber panel, immediately after its heading: the paragraphs below are the first development (unchanged); the second library's boundary is the dated update at the end. The historical text itself is untouched (it is dated record). |
| 25 | Private campaign vocabulary unexplained | FIXED — glosses added at use sites: "live indices" (indices the development's own witnesses realize), mp1 (one of the ladder record's four named demands), "same-realization record" (quantified over data exported by the same tower realization), drainage (undecided mass vanishes, tying inner/outer readings), "dv-graded" (the level-by-level graded refinement of the tower valuation), "normalized twist" (unit-normalized residual read that cancels the carry), "support line" (the Newton-polygon line the block sits on), "payoff rows" → "the first consequences in the dependent lemma family", "S2 probe tower" → "the project's pinned 2-adic test tower (called S2)", "μ₃ chain" (internal name for the depth-2 program; μ₂ its depth-1 predecessor), "corrected triple" → "the parameter triple (2, 1, 21), corrected mid-campaign", "star fired" → "its headline theorem landed", "formal controls" (deliberately wrong candidates the checks must reject), "level-2 twin" → "level-2 analogue", "owner review row" → "human-review queue". "Socket" does not occur in the draft (checked). |
| 26 | Internal paths not auditable | FIXED — all three record blocks and the audit-file lines are labeled "repository-internal paths — the campaign repository is not yet public; listed as provenance, not as links." Paths retained as provenance (removing them would delete the record; labeling is the honest middle). |
| 27 | "wild case OPEN" beside unconditional cubics | FIXED — headline now: "wild case OPEN at general degree (degrees two and three carry the machine-checked results below, each with its stated scope)" — deliberately points at the results-with-scope rather than claiming the BCFG conjecture (a Haar statement) settled at degree 3, which finding 1's scope caveat forbids. |
| 28 | "certified architecture for every degree" undefined | FIXED — paper post-date now: "unconditionally for quadratics and (since August 28, 2026) cubics; at general degree the theorem is now a formal Lean statement, proved one-way from a single named, still-open hypothesis structure (see the final milestone entry for exactly what that does and does not certify)." |

## Errors found in the draft beyond the audit (fixed while touching the lines)

* The blockFrontier node claimed its one axiom is "the dv-dissection cite **pair**" —
  false: C133mh14/15 consume `exists_dvDissection` only (one leg). Fixed in the node and
  in the allowlist node's propagation sentence.
* The allowlist node's new text was checked against `C66b.lean` before writing: the
  retirement theorem is proved by `C133h0leg.fgmn_dv_exact_mul_full` (import verified).

## Checks run

* `grep` sweeps: zero hits for every flagged phrase ("three machine-forced", "three
  compiled", "itemize(d) exactly", "are the same task", "not provably empty", "certified
  architecture", "proved special case", "first live supplier", "owner review row",
  "everything else it has landed", "coefficient ring at once" without finite-residue,
  "six audited literature citations", `stage 6\b`).
* Tag balance (details/summary/div/p/pre/code/strong/em/span) on all three files: clean.
* Stage-13 details/div nesting: balanced; badge inventory machine-read and matches the
  new tally arithmetic exactly (357 = 144+66+1+15+6+22+98+5).
* `git diff --stat`: exactly the three intended files (index.html 1 ¶; uniformity/index.html
  ~201 insertions; uniformity/paper.html 13 insertions). No commits, no pushes, either repo.

## For the orchestrator (carry-overs from EXPO's caveats, unchanged by this unit)

* `maps.json`/`story.json` still don't know about stage 13 (the generator pipeline
  `/tmp/graph_build` is absent) — if the generator is ever re-run it will drop the stage.
* The codex fresh-reader pass EXPO recommended has effectively been performed by EXPOAUD;
  a final quick codex skim of the REWRITTEN stage-13 prose before push is still cheap
  insurance if the window allows.
