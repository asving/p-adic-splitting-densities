#!/usr/bin/env python3
"""2026-08-07 update: the weld stage (six GRT-weld notes ALL ACCEPTED 2026-08-06/07).
Splices the new stage into story.json (after carry-cocycle-ladder) and the GRTWeld
corpus into maps.json; applies dated corrections to the now-resolved stage-3 weld
caveat and to the openSurface paragraphs. Statuses per the six ACCEPTANCE RECORDs,
JD0_PROOF, HIGHLEVEL_INTERPRETATION, and PROJECT_STATE checkpoints 2026-08-06/07."""
import json, pathlib

BASE = pathlib.Path('/tmp/graph_build')
story = json.load(open(BASE / 'story.json'))
maps = json.load(open(BASE / 'maps.json'))
corpus = json.load(open(BASE / 'grtweld_corpus.json'))

# ---------- 1. the new stage, inserted after carry-cocycle-ladder ----------
new_stage = {
 "id": "grt-weld",
 "title": "The weld: the model class is the classifier's own calculus — six notes, all accepted (added 2026-08-07)",
 "summary": (
  "Added 2026-08-07 — the milestone: the weld is in. Every carry law of the previous stage was proved on a "
  "pinned model class (the standard-lift harness towers), with one standing caveat — identifying that model "
  "with the classifier's actual Okutsu–Montes objects was open. That identification is now a package of six "
  "proof notes, each accepted after two consecutive clean fresh-context hostile passes with sealed machine "
  "batteries (the six arcs together: 51 hostile passes, 37 repair rounds, every failed pass and erratum dated "
  "on the record); the consolidation, THEOREM WELD-M, is one master transport whose five faces are the four "
  "accepted junctions plus covariance, and its new content is the headline: the carry cocycle is proved a "
  "coboundary up to one honest top carry, with the normalizing gauge canonical — constructed from the cocycle "
  "alone and forced by an H¹ = 0 uniqueness computation. Accepted is not machine-checked: these are "
  "adversarially verified prose proofs, the weld carries exactly one open lemma (W2-OPEN-2, accepted as a "
  "fenced box), the J-D counting block is still in progress, and the Lean boundary is unchanged — the order-0 "
  "capstone is machine-checked, the full-density theorem is not. "
  "The shape of the package, note by note: four junction notes match the two calculi piece by piece — W-2, the "
  "lift junction (which representative polynomial the model tower stands for, and how everything covaries with "
  "that choice); J-A, the dictionary junction (type data to tower data, four operator equalities and a per-slot "
  "character-gauge law); J-B, the tree junction (Newton polygons and gradings transport level-to-level by an "
  "explicit affine shear — and the carry cancels in print coordinates); J-C, the carry-algebra junction (anchor "
  "multiplication lands in a twisted group algebra whose factor set IS the carry cocycle). A fifth note "
  "discharges the lift corner — the one stratum where the lift-normalization law had stood open — and its arc "
  "is the campaign's honesty specimen: the first hostile pass exhibited an explicit counter-instance to the "
  "induction as first stated, and the accepted proof is the rebuilt one, counter-instance displayed. The sixth "
  "note, THEOREM WELD-M, consolidates by citation and adds the coboundary theorem. "
  "Why a cocycle at all — the story for a general reader: a wild tower grows the value group in stages, so "
  "every exponent splits into digits in a mixed-radix positional notation, and adding exponents produces "
  "carries. Those carries are exactly the classical 2-cocycle ('factor set') presenting the value-group "
  "extension — measured on committed towers, the section carry's class is the fundamental class, the generator "
  "of H²(ℤ/E, ℤ) (scratch-instrument grade, disclosed as such). And over a finite residue field the class of "
  "the wild part provably dies — H²(ℤ/E, K*) has order gcd(E, |K|−1), prime to p at a wild tower — which is "
  "the high-level explanation of the campaign's whole method: at wild primes there is nothing at "
  "cohomology-class level to compute, all wild information lives at cochain level, so the proof must run a "
  "ledger of explicit cochains with fences rather than a cohomology computation. "
  "What stays open is displayed, not hidden: W2-OPEN-2 (canonical-lift covariance above twist junctions — the "
  "weld's one open lemma, accepted as a fenced box, not as a theorem); a handful of fenced evidence cells named "
  "inside the notes; and the J-D counting block connecting the welded algebra to the density bookkeeping — its "
  "opening lemma J-D0 (stratum counts never see the value layer) is proved at attempt grade with a sealed "
  "68,523-check zero-violation battery, hostile arc not yet begun. And none of this stage is Lean: the "
  "machine-checked results are exactly what they were before it."),
 "corpora": ["GRTWeld"],
}

ids = [s['id'] for s in story['stages']]
pos = ids.index('carry-cocycle-ladder') + 1
if 'grt-weld' not in ids:
    story['stages'].insert(pos, new_stage)

# ---------- 2. dated correction: the stage-3 weld caveat is resolved ----------
st3 = next(s for s in story['stages'] if s['id'] == 'carry-cocycle-ladder')
st3['title'] = 'The carry-cocycle ladder (added 2026-08-03; updated 2026-08-04; weld caveat resolved 2026-08-07)'
assert st3['summary'].endswith('bringing the banked count to zero).')
st3['summary'] += (
  " (Updated 2026-08-07: the caveat that governed this stage — the weld to the classifier's actual "
  "Okutsu–Montes objects — is resolved at its displayed conditionality: six weld notes are now accepted, "
  "carrying one open lemma and an in-progress counting block; the next stage records the exact state.)")

# ---------- 3. dated corrections in the CocycleLadder corpus prose ----------
cl = next(m for m in maps if m['corpus'].strip() == 'CocycleLadder' or m['corpus'].startswith('CocycleLadder'))
old_tail = 'the weld to the classifier’s actual Okutsu–Montes objects is one of the displayed open items.'
old_tail2 = "the weld to the classifier's actual Okutsu–Montes objects is one of the displayed open items."
if cl['role'].endswith(old_tail) or cl['role'].endswith(old_tail2):
    cl['role'] += (" [Update 2026-08-07: that weld is since ACCEPTED at its displayed conditionality — six "
                   "notes, two clean fresh-context hostile passes each, one open lemma (W2-OPEN-2) — see the "
                   "next stage.]")
else:
    cl['role'] += (" [Update 2026-08-07: the weld caveat above is since resolved — six accepted notes, one "
                   "open lemma (W2-OPEN-2); see the next stage.]")
cl['oneLiner'] += ' The weld itself: accepted 2026-08-07 (next stage).'

# ---------- 4. the GRTWeld corpus into maps.json ----------
if not any(m['corpus'].startswith('GRTWeld') for m in maps):
    maps.append(corpus)

# ---------- 5. openSurface: append the weld paragraph + dated brackets ----------
paras = story['openSurface'].split('\n\n')

# 5a. PROVED IN ACCEPTED PROOF NOTES (para index 2): append the weld sentences.
assert paras[2].startswith('PROVED IN ACCEPTED PROOF NOTES')
paras[2] += (
  " NEW ON 2026-08-06/07 — the semantic weld, the standing caveat of everything in this list, is now itself "
  "six accepted notes: the lift-corner discharge (nine hostile passes, seven repair rounds; sealed runner "
  "25,409 checks, zero violations; its first pass refuted the stated descent with an explicit counter-instance "
  "and the accepted proof is the rebuilt lexicographic induction); the J-B tree junction (ten passes, eight "
  "repairs; independent re-derivation legs of 326,206 and 106,562 checks, zero violations; two post-acceptance "
  "errata folded as a dated annex); the J-C carry-algebra junction (eight passes, six repairs; the twisted-"
  "group-algebra isomorphism exhaustively machine-confirmed, 669 of 669); the W-2 lift junction (six passes, "
  "four repairs; a 566-junction resultant leg, 560 outside the sealed roster; a 17-theorem Lean-verified "
  "side-appendix); THEOREM WELD-M (ten passes, seven repairs; an 18,707-check battery with six planted "
  "falsifiers all caught) — one transport with five faces, proved by citing the accepted junctions, whose new "
  "content is that the carry cocycle is a COBOUNDARY up to one honest top carry, with the gauge canonical, "
  "forced by an H¹ = 0 uniqueness computation; and the J-A dictionary junction (eight passes, five repairs; "
  "independent generating-function and Galois-descent re-derivations, 385,057 and 5,519 checks, zero "
  "violations; sealed runner 10,311 checks across 17 families). The package carries exactly one open lemma "
  "(W2-OPEN-2, accepted as a fenced box, not as a theorem) plus the in-progress J-D counting block; it is "
  "adversarially verified prose, NOT machine-checked, and changes nothing in the Lean panels above.")

# 5b. OPEN — the mathematics of stage 3 (para index 7): dated update bracket.
assert paras[7].startswith('OPEN — the mathematics of stage 3')
paras[7] += (
  " [Dated updates. 2026-08-04: the engine family (RM-m) CLOSED on its displayed scope as THEOREM RM-GEN — "
  "the stage-3 engine node carries the exact state; the corner family's account is reduced to one boxed open "
  "lemma. 2026-08-06: the lift residual (ITER-LAW-LIFT) DISCHARGED at the accepted lift-corner note. "
  "2026-08-07: the semantic weld standing over the stage is ACCEPTED at its displayed conditionality — six "
  "notes, one open lemma (W2-OPEN-2), the J-D counting block in progress (see the weld stage). What the weld "
  "does NOT change: it is prose-note grade, so its Lean-facing counterpart — the standing order-two-and-deeper "
  "classifier-faithfulness obligation — still stands in full.]")

# 5c. CONJECTURES (para index 8): dated bracket on the stage-3 families.
assert paras[8].startswith('CONJECTURES')
paras[8] += (
  " [Dated update 2026-08-04/07: of the two stage-3 families, the engine family (RM-m) is since an accepted "
  "theorem (RM-GEN) on its displayed scope; the corner family (W-MULT-DCX-m) remains open, reduced to one "
  "boxed lemma; and the weld, listed under OPEN above, is since accepted — its residue is W2-OPEN-2 and the "
  "J-D counting block.]")

story['openSurface'] = '\n\n'.join(paras)

json.dump(story, open(BASE / 'story.json', 'w'), indent=1, ensure_ascii=False)
json.dump(maps, open(BASE / 'maps.json', 'w'), indent=1, ensure_ascii=False)
print('spliced: stage grt-weld at position', pos + 1, '| corpora:', len(maps), '| stages:', len(story['stages']))
