#!/usr/bin/env python3
"""2026-08-03 update: the carry-cocycle ladder stage + refreshed honest boundary.
Splices the new stage/prose/openSurface into story.json and the CocycleLadder
corpus into maps.json. Statuses per PROJECT_STATE r38 + the ledger blocks."""
import json, pathlib, sys

BASE = pathlib.Path('/tmp/graph_build')
story = json.load(open(BASE / 'story.json'))
maps = json.load(open(BASE / 'maps.json'))
corpus = json.load(open(BASE / 'cocycle_corpus.json'))

# ---------- 1. the new stage, inserted after carry-algebra ----------
new_stage = {
 "id": "carry-cocycle-ladder",
 "title": "The carry-cocycle ladder (added 2026-08-03)",
 "summary": ("Everything in this stage is new since this page was built (July 30, 2026) and is dated 2026-08-03. "
  "It is also of a different kind than the other stages: these are results of the project's proof-note pipeline — "
  "mathematical prose proofs accepted under an adversarial-verification bar, and sealed exact-numerics batteries — "
  "not Lean theorems; the badges distinguish this honestly ('accepted' means: consecutive clean hostile passes by "
  "verifiers reading in fresh contexts, at least two different model families among them, every failed pass and "
  "erratum on the dated record). The content: at every depth of the wild tower, the failure of anchor values to "
  "multiply is measured by one explicit carry cocycle, and one uniform integer recursion gives that cocycle at "
  "every depth so far examined. The depth-2 law is proved and accepted; the depth-3 law is proved and accepted off "
  "one displayed corner of parameter space; depths 4 through 6 are measured — zero violations in over 390,000 exact "
  "checks; and the all-orders theorem is composed by induction on the depth, its generic layers proved, its entire "
  "remaining distance two named lemma families plus a lift residual. The mechanism, converged on by five "
  "decorrelated numeric methods with zero splits, is the stage's centerpiece: modulo a single honest top carry, "
  "the whole cocycle is a gauge artifact of the ε-chain normalization. One caveat governs everything here: the "
  "laws are proved on a pinned model class (standard-lift harness towers), and the weld identifying that model "
  "with the classifier's actual Okutsu–Montes objects is itself still open — the last two nodes of this stage "
  "record two closed repair accounts (the read functional corrected at source; the Lean corpus's last banked "
  "unproved statement proved, bringing the banked count to zero)."),
 "corpora": ["CocycleLadder"],
 "mathHighlight": ("c_{n+1}(\\gamma,\\gamma') \\;=\\; \\bar z^{\\,\\delta}\\, z_n^{D_n}\\cdots z_1^{D_1} "
  "\\;=\\; \\bar z^{\\,\\delta}\\cdot \\partial F_n,\\qquad F_n(\\gamma)=\\prod_{j=1}^{n}\\varepsilon_j(\\beta_j(\\gamma))"
  "\\qquad(\\text{one gauge, one honest top carry})")
}
ids = [s['id'] for s in story['stages']]
assert 'carry-cocycle-ladder' not in ids
story['stages'].insert(ids.index('carry-algebra') + 1, new_stage)

# ---------- 2. stale stage-summary sentences ----------
def sub_stage(sid, old, new):
    for s in story['stages']:
        if s['id'] == sid:
            assert old in s['summary'], (sid, old)
            s['summary'] = s['summary'].replace(old, new)
            return
    raise KeyError(sid)

sub_stage('carry-algebra',
  "the two hard-core corpora carry the still-open construction duties (two and nine named unproved statements respectively).",
  "the two hard-core corpora carry the still-open construction duties (their remaining named unproved statements are counted in the amber panel's dated census). The carry-cocycle laws proved on this algebra's model class since this page was first built are the next stage.")
sub_stage('transfer-assembly',
  "Six named unproved statements remain in this corpus, each with a written record.",
  "The corpus's named unproved statements, each with a written record, are counted in the amber panel's dated census.")
sub_stage('resummation-solve',
  "Four named unproved statements remain in the value-layer corpus.",
  "The value-layer corpus's named unproved statements — several deliberately re-opened after audits caught statement defects — are counted in the amber panel's dated census.")

# ---------- 3. story prose: two new paragraphs before the closing one ----------
paras = story['story'].split('\n\n')
assert paras[-1].startswith('The formalization')
pA = ("Since this page was first built (July 30, 2026), the campaign's center of gravity has moved from the Lean "
 "scaffolding to the open mathematics of the deep wild tower, and one object now organizes everything found there: "
 "the carry cocycle. At each depth of the classifier's tower, every eligible index carries an anchor — a canonical "
 "monomial witness whose leading value the analysis tracks — and the leading value of a product of anchors differs "
 "from the anchor of the sum by an explicit correction. The discovery of the August arc is that this correction "
 "obeys one law at every depth: it is a single monomial in the level letters, its exponents produced by one integer "
 "recursion in the carry data — a top carry, then one division per level, each level's denominator cured by its own "
 "level's carry correction through a Bézout pair, never a cross-level denominator. At depth two the law is proved "
 "and accepted (\"accepted\" on this page always means: survived the project's adversarial-verification bar — "
 "consecutive clean hostile passes by verifiers reading in fresh contexts, drawn from at least two different model "
 "families, with every failed pass and every erratum on the dated record). At depth three it is proved and accepted "
 "off one explicitly displayed corner of parameter space — a corner that is empty unless the innermost ramification "
 "index is at least three, and on which the law is verified true in all 132 probed instances. At depths four, five, "
 "and six it is measured: sealed, preregistered exact-numerics batteries — 362,624 checks at depth four alone, over "
 "390,000 across the three depths — found zero violations.")
pB = ("The mechanism behind the law is simpler than the law, and it is the new centerpiece of this story. Five "
 "decorrelated numeric methods — a sealed battery, an independent reimplementation, a from-data symbolic fit, a "
 "cohomological probe, a degeneration ladder — converged on the same reading with zero splits: apart from a single "
 "top carry, the entire cocycle is a gauge artifact. Normalize every anchor by its ε-chain — the product of one "
 "explicitly computable unit per level — and the whole intricate correction collapses to one honest carry at the "
 "top of the tower; every constant of the recursion is the exponent bookkeeping of that normalization. The strategy "
 "for all orders then writes itself: prove, at each level, that the anchor's value equals its ε-chain (routine), "
 "and that products develop with exactly the top carry (the one hard step). The all-orders theorem is composed on "
 "exactly this plan, by induction on the depth: its generic layers are proved, and its entire remaining distance is "
 "two named families of open lemmas — a per-level multiplication engine, and the law on the excluded corners — plus "
 "a lift-normalization residual. That composed note has not yet passed its own hostile arc, and this page does not "
 "count it as accepted. One honest caveat governs the whole arc: the laws are proved on a model class — the "
 "standard-lift harness towers, a pinned calculus with the classifier's shape — and the weld identifying the "
 "model's objects with the classifier's actual Okutsu–Montes data is itself still open. The same window also closed "
 "two long-standing accounts: a source-level re-derivation of the engine's read functional showed that two compiled "
 "obstruction walls were transcription artifacts of one doubly-scaled clause, with a three-token repair, accepted "
 "end-to-end; and the Lean corpus's last banked unproved statement — a Newton-polygon hull-stability bound — was "
 "proved outright, statement byte-unchanged, bringing the banked count to zero.")
story['story'] = '\n\n'.join(paras[:-1] + [pA, pB, paras[-1]])

# ---------- 4. openSurface rebuild ----------
op = story['openSurface'].split('\n\n')
labels = [p.split(' ')[0] for p in op]
assert labels[0].startswith('PROVED,') and op[4].startswith('OPEN')
# 4a. extend the machine-checked PROVED paragraph with the banked retirement
op[0] = op[0].rstrip('.') + ("; and — new on 2026-08-03 — the classifier's Newton-polygon hull-stability bound, "
 "formerly this panel's one banked unproved statement, now proved outright with its statement byte-unchanged "
 "(Lean-core footprint; every capstone footprint verified unchanged).")
# 4b. new paragraph: accepted proof notes (insert after PROVED CONDITIONALLY)
accepted = ("PROVED IN ACCEPTED PROOF NOTES (mathematical prose proofs, adversarially verified, NOT machine-checked; "
 "an 'accepted' note has survived the campaign's verification bar — consecutive clean hostile passes by verifiers "
 "reading in fresh contexts, at least two different model families among them, every failed pass and erratum dated "
 "and recorded): the depth-2 carry-cocycle law (accepted 2026-08-03; scope: the standard-lift harness tower class; "
 "residual: the lift-normalization law open exactly on one named stratum); the depth-3 law (accepted 2026-08-03 off "
 "the displayed DCX corner, which is empty when the innermost ramification index is at most two — on the corner the "
 "law is a named open lemma, instance-true in all 132 probed cases); and the source-level re-derivation of the "
 "engine's read functional (accepted after a fourteen-pass, ten-revision arc: two compiled obstruction walls "
 "diagnosed as transcription artifacts of one doubly-scaled clause, repaired by a three-token change whose "
 "application carried its own hostile pass). These live on the model class of stage 3; the weld to the classifier's "
 "actual objects is open, below.")
# 4c. new paragraph: measured (insert after VERIFIED COMPUTATIONALLY)
measured = ("MEASURED (large-scale exact numerics under sealed, preregistered batteries — instance evidence, never "
 "consumed as a proof step): the depth-4 carry-cocycle law, zero violations in 362,624 exact checks (72 fresh "
 "towers, 4 coefficient rings) plus a 2,896-check subwindow-restriction gate; first depth-5 data, roughly 5,300 "
 "checks with zero violations (the five-read law exact in all 544 probed cases); first depth-6 data, 22,369 checks "
 "on 9 fresh instances via a verifier-owned reimplementation, zero violations. The general statements at these "
 "depths are conjectures.")
# 4d. rewrite OPEN
open_new = ("OPEN — the Lean tree (each an explicitly marked unproved statement; the dated census of 2026-08-03 "
 "counts 34 repo-wide — 33 in the main library plus one tracked scratch probe — down from the 46 this panel listed "
 "when the page was built): the remaining statements concentrate in the counting-campaign corpora (branch tree, "
 "value layer, and the capstone's slot layer — some deliberately re-opened after audits caught statement defects, "
 "and some recorded as false at their pinned test tables, a documented blueprint defect awaiting a design decision "
 "rather than missing mathematics), the two hard-core corpora, and the scaffold layer; the classifier tree itself "
 "is at zero, and the banked count is zero — the banked bound this panel formerly listed was proved outright (see "
 "the first paragraph).\n\n"
 "OPEN — the mathematics of stage 3 (the exact distance of the all-orders carry-cocycle program, each item named "
 "and priced in the notes): the engine family (RM-m) for every middle level m ≥ 2 (the level-1 case is proved); the "
 "corner family (W-MULT-DCX-m) — the multiplication law on the excluded corners, instance-true everywhere probed; "
 "the lift residual (ITER-LAW-LIFT), open exactly on one named stratum, with two measured companion conjectures; "
 "the acceptance arc of the composed all-orders note itself; and the semantic weld — identifying the model class "
 "the accepted laws live on with the classifier's actual Okutsu–Montes objects (its Lean-facing counterpart is the "
 "standing order-two-and-deeper classifier-faithfulness obligation).")
op[4] = open_new
# 4e. conjectures paragraph: add the new measured laws
op[5] = op[5].rstrip('.') + ("; and, new since 2026-08-03: the carry-cocycle laws at depths four and beyond and "
 "the all-orders recursion past its proved generic layers — measured with zero violations, not accepted, recorded "
 "as conjectures.")
story['openSurface'] = '\n\n'.join([op[0], op[1], accepted, op[2], op[3], measured, op[4], op[5]])

# ---------- 5. maps.json: append the new corpus ----------
assert not any(m['corpus'] == 'CocycleLadder' for m in maps)
maps.append(corpus)

json.dump(story, open(BASE / 'story.json', 'w'), ensure_ascii=False, indent=1)
json.dump(maps, open(BASE / 'maps.json', 'w'), ensure_ascii=False, indent=1)
print('story stages:', [s['id'] for s in story['stages']])
print('maps corpora:', len(maps), '| openSurface paras:', len(story['openSurface'].split('\n\n')))
print('story paras:', len(story['story'].split('\n\n')))
