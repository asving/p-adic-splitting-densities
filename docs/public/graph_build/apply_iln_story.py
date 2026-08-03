#!/usr/bin/env python3
"""[ILN] acceptance fold into story.json (ledger a46578e; bracket in ITERLAWN_PROOF S0).

Edits: (1) mechanism paragraph un-staled; (2) one NEW story paragraph — the all-orders
theorem accepted on the model class; (3) stage-3 summary upgraded; (4) openSurface:
accepted-notes row added, measured row un-staled, stage-3 open rows collapsed to the
two-family display, conjectures row un-staled. NO change to headline / theoremU*.
"""
import json, pathlib

BASE = pathlib.Path('/tmp/graph_build')
story = json.load(open(BASE / 'story.json'))

def rep1(s, old, new):
    assert s.count(old) == 1, 'NOT UNIQUE/FOUND: %r' % old[:80]
    return s.replace(old, new)

# ---- (1) the mechanism paragraph: retire the not-yet-accepted sentence ----
story['story'] = rep1(
    story['story'],
    "The all-orders theorem is composed on exactly this plan, by induction on the depth: "
    "its generic layers are proved, and its entire remaining distance is two named families "
    "of open lemmas — a per-level multiplication engine, and the law on the excluded corners "
    "— plus a lift-normalization residual. That composed note has not yet passed its own "
    "hostile arc, and this page does not count it as accepted. One honest caveat governs the "
    "whole arc:",
    "The all-orders theorem is composed on exactly this plan, by induction on the depth — "
    "and that composition has now survived its own hostile arc; the next paragraph records "
    "the acceptance. One honest caveat governs the whole arc:")

# ---- (2) the NEW paragraph: the acceptance, inserted before the closing paragraph ----
NEWPARA = (
    "Later on August 3, 2026, the composed all-orders theorem was accepted on the model "
    "class. Its hostile arc ran seven rounds, ending in a round where both verifiers — "
    "different model families, reading in fresh contexts — returned clean on the same text. "
    "The scope as accepted is exactly the composed plan: one integer recursion gives the "
    "carry cocycle at every depth $n \\ge 1$ on the standard-lift harness class; the generic "
    "layers (integrality, positivity, the window, the cocycle identity, the descent, the "
    "ε-chain family at every rung, the multiplication law's main case) are proved outright; "
    "the remaining cases close modulo the two named open families displayed inside the "
    "statement. Two facts about the arc deserve record. First, across all seven rounds the "
    "verifiers found zero mathematical errors: every finding after round one was completeness "
    "bookkeeping in the note's own honesty apparatus — the ledger of what depends on what. "
    "Second, the question that actually stalled acceptance — is every dependency-flavored "
    "sentence in the note enumerated and adjudicated? — was closed by machine: hand censuses "
    "kept diverging in both directions, so a program scanned the pinned text and mapped all "
    "194 pattern hits to adjudicated classes, and the second verifier then reproduced that "
    "census with independently written code — 194 versus 194, per-pattern identical, empty "
    "symmetric difference. That is a verification-methodology first for this project: an "
    "acceptance question converted from a reader claim into a machine fact. What remains open "
    "on the model class is now short and fully displayed: the per-level multiplication engine "
    "(RM-$m$) for middle levels $m \\ge 2$, the corner law (W-MULT-DCX-$m$) — instance-true "
    "everywhere probed — the fenced non-consumed corners, the lift residual on one named "
    "stratum, and, standing over all of it, the weld from the model class to the classifier's "
    "actual objects.")
story['story'] = rep1(
    story['story'],
    "bringing the banked count to zero.\n\nThe formalization's contribution is a typed boundary:",
    "bringing the banked count to zero.\n\n" + NEWPARA +
    "\n\nThe formalization's contribution is a typed boundary:")

# ---- (3) the stage-3 summary ----
st3 = [s for s in story['stages'] if s['id'] == 'carry-cocycle-ladder'][0]
st3['summary'] = rep1(
    st3['summary'],
    "and the all-orders theorem is composed by induction on the depth, its generic layers "
    "proved, its entire remaining distance two named lemma families plus a lift residual.",
    "and the all-orders theorem — one recursion for every depth — is proved by induction on "
    "the depth and accepted (2026-08-03; seven model-diverse rounds, zero mathematical "
    "findings in all seven, the completeness census closed by machine), its remaining cases "
    "closing modulo two named lemma families displayed inside the statement: those two "
    "families, plus the fenced corners and a lift residual, are the entire remaining "
    "distance on the model class.")

# ---- (4) openSurface ----
osf = story['openSurface']

# 4a. accepted-notes row: add [ILN]
osf = rep1(
    osf,
    "and the source-level re-derivation of the engine's read functional",
    "the all-orders carry-cocycle theorem (ITER-LAW-n) (accepted 2026-08-03 after a "
    "seven-round arc ending in a model-diverse double-clean, the enumeration-completeness "
    "question closed by machine — one integer recursion giving the cocycle at every depth "
    "n ≥ 1 on the standard-lift harness class, generic layers proved outright, remaining "
    "cases closing modulo the two displayed open families of the stage-3 frontier); "
    "and the source-level re-derivation of the engine's read functional")

# 4b. measured row: the deeper depths are no longer bare conjectures
osf = rep1(
    osf,
    "zero violations. The general statements at these depths are conjectures.",
    "zero violations. Since the all-orders acceptance (2026-08-03) the general statements "
    "at these depths are no longer bare conjectures: they are rungs of the accepted "
    "theorem, conditional on its two displayed open families; the batteries remain "
    "instance evidence and are never consumed as proof steps.")

# 4c. stage-3 open rows: collapse to the two-family display; the acceptance arc is done
osf = rep1(
    osf,
    "OPEN — the mathematics of stage 3 (the exact distance of the all-orders carry-cocycle "
    "program, each item named and priced in the notes): the engine family (RM-m) for every "
    "middle level m ≥ 2 (the level-1 case is proved); the corner family (W-MULT-DCX-m) — the "
    "multiplication law on the excluded corners, instance-true everywhere probed; the lift "
    "residual (ITER-LAW-LIFT), open exactly on one named stratum, with two measured companion "
    "conjectures; the acceptance arc of the composed all-orders note itself; and the semantic "
    "weld — identifying the model class the accepted laws live on with the classifier's "
    "actual Okutsu–Montes objects (its Lean-facing counterpart is the standing "
    "order-two-and-deeper classifier-faithfulness obligation).",
    "OPEN — the mathematics of stage 3 (with the all-orders theorem accepted, the entire "
    "remaining distance on the model class collapses to two named lemma families, each "
    "priced in the notes): the engine family (RM-m) for every middle level m ≥ 2 (the "
    "level-1 case is proved); and the corner family (W-MULT-DCX-m) — the multiplication law "
    "on the excluded corners, instance-true everywhere probed. Two smaller accounts ride "
    "alongside: the fenced non-consumed corners, and the lift residual (ITER-LAW-LIFT), open "
    "exactly on one named stratum, with two measured companion conjectures. Standing over "
    "the whole stage: the semantic weld — identifying the model class the accepted laws "
    "live on with the classifier's actual Okutsu–Montes objects (its Lean-facing "
    "counterpart is the standing order-two-and-deeper classifier-faithfulness obligation). "
    "The acceptance arc of the all-orders note, formerly listed here, closed 2026-08-03.")

# 4d. conjectures row: the all-orders recursion is out; the two families are in
osf = rep1(
    osf,
    "and, new since 2026-08-03: the carry-cocycle laws at depths four and beyond and the "
    "all-orders recursion past its proved generic layers — measured with zero violations, "
    "not accepted, recorded as conjectures.",
    "and the two open families of the stage-3 frontier — the engine family (RM-m) at "
    "m ≥ 2 and the corner law (W-MULT-DCX-m), instance-true everywhere probed, conjectured "
    "true in general; the all-orders recursion itself, formerly listed here as a "
    "conjecture, is since 2026-08-03 an accepted theorem conditional on exactly those "
    "families.")

story['openSurface'] = osf

json.dump(story, open(BASE / 'story.json', 'w'), indent=1, ensure_ascii=False)
print('story.json updated:', len(json.dumps(story)), 'chars')
