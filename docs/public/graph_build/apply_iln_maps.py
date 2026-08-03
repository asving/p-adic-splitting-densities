#!/usr/bin/env python3
"""[ILN] acceptance fold into maps.json, CocycleLadder corpus (ledger a46578e).

(1) cc-iterlawn: open -> proved-note (accepted 2026-08-03; scope + the two open
    families in the note field). (2) cc-machine-census: NEW method node inserted
    after cc-iterlawn. (3) cc-twofamilies: stays open, reworded as THE FRONTIER.
(4) cc-measured456 (the rung ladder): gains the rung ledger as accepted (rungs
    4/5 measured) and the post-acceptance status of the deep rungs. (5) cc-gauge
    note: strategy-of-record -> executed plan. (6) corpus oneLiner/role refreshed.
"""
import json, pathlib

BASE = pathlib.Path('/tmp/graph_build')
maps = json.load(open(BASE / 'maps.json'))
cl = [m for m in maps if m['corpus'] == 'CocycleLadder'][0]
byid = {n['id']: n for n in cl['nodes']}

def rep1(s, old, new):
    assert s.count(old) == 1, 'NOT UNIQUE/FOUND: %r' % old[:80]
    return s.replace(old, new)

# ---- (1) cc-iterlawn: the acceptance upgrade ----
n = byid['cc-iterlawn']
n['status'] = 'proved-note'
n['title'] = 'The all-orders theorem (ITER-LAW-n): proved on the model class — accepted 2026-08-03'
n['math'] = rep1(
    n['math'],
    "Stated at every rung $n \\ge 1$ and proved by induction on the rung, on an honest "
    "perimeter: proved level-generic are",
    "Stated at every rung $n \\ge 1$ and proved by induction on the rung, on a fully "
    "displayed perimeter: proved level-generic are")
n['note'] = (
    "Proved (note) — adversarially verified through seven model-diverse rounds; the "
    "completeness census closed by machine (the next node). Accepted 2026-08-03 at the "
    "two-clean bar: in round seven both verifiers — different model families, fresh "
    "contexts — returned clean on the same text; across all seven rounds they found zero "
    "mathematical errors (every post-round-one finding was completeness bookkeeping in the "
    "note's own honesty apparatus). Scope as accepted: the recursion for ALL depths n ≥ 1 "
    "on the (n+1)-read standard-lift harness class, generic layers proved outright, with "
    "the two open families displayed inside the statement — (RM-m) at middle levels m ≥ 2 "
    "(m = 1 proved inside the depth-3 acceptance) and (W-MULT-DCX-m) on the excluded "
    "corners — plus the fenced non-consumed corners; the consumed depth-2/depth-3 packages "
    "ride through. Rung ledger as accepted: rung 1 accepted · rung 2 accepted off its "
    "corner · rungs 3/4/5 measured, instance evidence only.")
n['gate'] = (
    "Not machine-checked: an accepted mathematical proof note on the pinned model class. "
    "Its remaining cases close MODULO the two displayed open families (RM-m, m ≥ 2) and "
    "(W-MULT-DCX-m) — the frontier node below; the weld to the classifier's actual "
    "objects stays open.")
n['lean'] = rep1(
    n['lean'],
    "Status: composed 2026-08-03 by induction on the rung; generic layers proved;\n"
    "Cases II closed MODULO (RM-(n−1)), off DCX-(n); hostile arc OWED — not accepted.",
    "Status: ACCEPTED 2026-08-03 (round-7 double-clean: Codex PC6 + Fable PE7 on the\n"
    "same text; zero mathematical findings across all seven rounds; the census\n"
    "question closed by machine, 194/194 reproduced by an independent scanner).\n"
    "Scope: all n ≥ 1 on (n+1)-read standard-lift towers; generic layers proved;\n"
    "Cases II close MODULO (RM-m, m ≥ 2), off DCX-(n) (outer bound proved);\n"
    "residuals = the two displayed families + the fenced corners; the accepted\n"
    "depth-2/depth-3 packages ride through.")
n['srcLabel'] = 'The exact statement (from the accepted note)'
n['kind'] = 'accepted proof note (adversarially verified, seven rounds)'

# ---- (2) cc-machine-census: NEW node ----
census = {
    'id': 'cc-machine-census',
    'title': 'The machine census: an acceptance question closed by program',
    'status': 'definition',
    'math': (
        "The all-orders note's acceptance stalled not on mathematics but on a completeness "
        "question: does the note anywhere claim a dependency it does not have, and is every "
        "dependency-flavored sentence of the pinned text enumerated and adjudicated? Hand "
        "censuses kept diverging — round five's closed sentence mis-counted the pinned text "
        "in both directions. Round six replaced the reader with a program: eight widened "
        "lexical patterns run over the pinned note produced 194 raw hits on 147 lines, every "
        "hit mapped to an adjudicated class (88 at table-row sites, 21 in seven content-true "
        "site families, 53 verification apparatus, 8 quoted external record, 18 non-genre, "
        "6 positive displays), zero unadjudicated. In round seven the second verifier wrote "
        "its own scanner from the pattern specification alone — independent code, fresh "
        "context — and reproduced the census exactly: 194 of 194 hits, 147 of 147 lines, "
        "per-pattern identical, empty symmetric difference. The substantive result, "
        "confirmed four times independently and last by machine: zero false dependency "
        "claims exist anywhere in the note."),
    'note': (
        "A verification-methodology first for this project: an acceptance-blocking question "
        "converted from a reader claim into a machine fact, then reproduced by a second, "
        "independently written scanner. Enumeration completeness is exactly the kind of "
        "bookkeeping that hand passes get wrong in both directions; the machine census is "
        "now the enumeration of record, superseding all hand censuses."),
    'lean': (
        "THE MACHINE CENSUS (errata round 6; the enumeration of record):\n"
        "  8 widened patterns over the pinned text → 194 raw hits / 147 lines\n"
        "  194/194 mapped, ZERO unadjudicated\n"
        "  classes: 88 row-site · 21 site-families F1–F7 (all content-true)\n"
        "           53 apparatus · 8 quoted · 18 non-genre · 6 positive\n"
        "PE7 (the second verifier's own scanner, written from the patterns alone):\n"
        "  194 vs 194 exact — per-pattern identical, empty symmetric difference\n"
        "Zero FALSE dependency claims: confirmed 4× independently (last by program)."),
    'srcLabel': 'The verdict lines (from the census of record)',
    'file': 'verification/openmath/iterlawn_pe7_census.py',
    'kind': 'verification method (the census question closed by program)',
}
idx = [i for i, nd in enumerate(cl['nodes']) if nd['id'] == 'cc-iterlawn'][0]
assert 'cc-machine-census' not in byid
cl['nodes'].insert(idx + 1, census)

# ---- (3) cc-twofamilies: THE FRONTIER ----
n = byid['cc-twofamilies']
n['title'] = 'THE FRONTIER: two named lemma families — the entire remaining distance on the model class'
n['math'] = rep1(
    n['math'],
    "A proof of these two families closes the recursion at every depth on the model class.",
    "With the all-orders theorem accepted, these two families ARE the entire remaining "
    "mathematical distance on the model class: prove them (with the fenced corners) and "
    "the recursion is unconditional at every depth.")
n['note'] = (
    "Since the all-orders acceptance (2026-08-03) this node is the frontier: everything "
    "above it on the model class is proved modulo exactly what is displayed here. It is "
    "short: two families and a lift residual, each named, each priced, none hidden inside "
    "a 'routine' step. The weld below is the one account beyond the model class.")

# ---- (4) cc-measured456: the rung ladder ----
n = byid['cc-measured456']
n['note'] = (
    "Measured means measured: sealed batteries are instance evidence and are never "
    "consumed as a proof step anywhere in the development. In the accepted all-orders "
    "note's rung numbering these depths are rungs 3, 4, and 5, and the rung ledger as "
    "accepted reads: rung 1 accepted · rung 2 accepted off its corner · rung 3 measured "
    "green · rungs 4/5 measured — instance evidence only. Since the acceptance, the law "
    "at these depths is no longer a bare conjecture: it is the accepted theorem's rung, "
    "conditional on the two open families of the frontier node.")
n['gate'] = (
    "No unconditional proof exists at depths ≥ 4: the accepted all-orders theorem covers "
    "them modulo the displayed open families (RM-m, m ≥ 2) and (W-MULT-DCX-m); the "
    "batteries below remain instance evidence, never proof steps.")
n['lean'] = n['lean'] + (
    "\nRung ledger as accepted 2026-08-03 (rung n = the (n+1)-read law):\n"
    "  rung 1 ACCEPTED · rung 2 ACCEPTED-OFF-DCX · rung 3 MEASURED GREEN\n"
    "  rungs 4/5 measured (5-read diag; 6-read verifier reimplementation)")

# ---- (5) cc-gauge: strategy-of-record -> the executed plan ----
n = byid['cc-gauge']
n['note'] = rep1(
    n['note'],
    "As an all-orders mechanism it is the strategy of record, converged on by five "
    "decorrelated numeric methods with zero splits (convergence judgment dated 2026-08-03);",
    "As an all-orders mechanism it was the strategy of record — converged on by five "
    "decorrelated numeric methods with zero splits (convergence judgment dated 2026-08-03) "
    "— and the accepted all-orders theorem (previous nodes) is proved on exactly this plan;")

# ---- (6) corpus header ----
cl['oneLiner'] = (
    "One carry law at every depth of the wild tower — proved and accepted at depths 2–3 "
    "and, as of 2026-08-03, for all orders on the model class (modulo two displayed open "
    "families); measured through depth 6; the entire remaining distance displayed in the "
    "frontier node.")
cl['role'] = rep1(
    cl['role'],
    "The laws below say this correction is one monomial with exponents given by one integer "
    "recursion, at every depth probed,",
    "The laws below say this correction is one monomial with exponents given by one integer "
    "recursion, at every depth — proved and accepted at depths 2 and 3, accepted for all "
    "orders (2026-08-03) modulo two displayed open families, measured through depth 6 —")

json.dump(maps, open(BASE / 'maps.json', 'w'), indent=1, ensure_ascii=False)
print('maps.json updated; CocycleLadder nodes =', len(cl['nodes']))
