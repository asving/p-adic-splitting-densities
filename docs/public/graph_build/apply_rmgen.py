#!/usr/bin/env python3
"""2026-08-04 public-map refresh: THEOREM RM-GEN accepted.

Edits maps.json (CocycleLadder corpus) + story.json in /tmp/graph_build:
  - new node cc-rmgen (proved-note): THEOREM RM-GEN, the generic (RM-m) engine
  - new node cc-pooltruth (measured): the pool-identification story (arc in progress
    => 'proved (note)' would violate the legend; 'measured' is the honest badge)
  - cc-iterlawn upgraded: COR-A applied ((ITER-LAW-n) unconditional-on-(RM) on T-class(n))
  - cc-twofamilies rewritten: the frontier is now (SURV-(m+1))/(EMPTY-(m+1)); Q3/Q4 unchanged
  - corpus oneLiner/role refreshed; stage title/summary updated; one new story paragraph
Sources: lean/notes/openmath/RMENGINE_2026-08-08.md (acceptance bracket + S7.1 COR-A),
lean/notes/openmath/WMULTDCX_2026-08-08.md (header + W-r1 bracket), docs/PROJECT_STATE.md
(the 2026-08-04 campaign block).
"""
import json, pathlib

BASE = pathlib.Path('/tmp/graph_build')

# ---------------------------------------------------------------- maps.json
maps = json.load(open(BASE / 'maps.json'))
mp = [m for m in maps if m.get('corpus') == 'CocycleLadder']
assert len(mp) == 1, 'CocycleLadder corpus not found exactly once'
mp = mp[0]

# ---- corpus oneLiner + role
assert 'modulo two displayed open families' in mp['oneLiner']
mp['oneLiner'] = ("One carry law at every depth of the wild tower — proved and accepted at depths 2–3 "
                  "and for all orders on the model class (2026-08-03); the induction's hard engine family "
                  "closed at every level on its displayed scope (THEOREM RM-GEN, accepted 2026-08-04); "
                  "measured through depth 6; the frontier is now one boxed lemma before the uniform corner "
                  "law, then the fenced corners and the weld.")

old = 'Everything in this stage is dated 2026-08-03 and lives'
assert old in mp['role']
mp['role'] = mp['role'].replace(old, 'Everything in this stage is dated 2026-08-03/04 and lives')
old = ('proved and accepted at depths 2 and 3, accepted for all orders (2026-08-03) modulo two displayed '
       'open families, measured through depth 6')
assert old in mp['role']
mp['role'] = mp['role'].replace(old,
       'proved and accepted at depths 2 and 3, accepted for all orders (2026-08-03) modulo displayed '
       'open families — the harder of them, the read-multiplication engine, closed 2026-08-04 as '
       'THEOREM RM-GEN — measured through depth 6')

nodes = mp['nodes']
byid = {n['id']: n for n in nodes}

# ---- cc-iterlawn: COR-A applied
iln = byid['cc-iterlawn']
iln['note'] += (" UPGRADE (COR-A, fired 2026-08-04 at THEOREM RM-GEN's acceptance — the engine node "
                "below): the (RM-m) conditionality is DISCHARGED on the tower sub-class T-class(n); there "
                "(ITER-LAW-n) off DCX-(n) is unconditional for every n ≥ 3 modulo only the accepted "
                "packages' own head declarations, and at n = 1, 2 the accepted depth-2/depth-3 statements "
                "stand verbatim with no T-condition. Off T-class(n) the engine calls stay conditional on "
                "the fenced corner.")
iln['gate'] = ("Not machine-checked: an accepted mathematical proof note on the pinned model class. Since "
               "THEOREM RM-GEN's acceptance (2026-08-04) the (RM-m) family is CLOSED on T-class(n): the "
               "remaining conditionality there is the note's own non-(RM) residuals — the corner law "
               "on the excluded corners (reduced, two nodes below, to one boxed lemma), the fenced "
               "non-consumed corners, the lift residual. Off T-class(n) (d₀ ≥ 2 with a flat or "
               "e₀ = 1 level) the engine calls stay conditional on the fenced corner; the weld to the "
               "classifier's actual objects stays open.")
iln['lean'] += ("\n\nUPGRADE (COR-A, 2026-08-04, fired at RM-GEN acceptance): on\n"
                "T-class(n) := d₀ = 1 ∨ (e₀ ≥ 2 ∧ e_i ≥ 2 for all i ≤ n−2), "
                "the S7 rows-5/6/8\n(RM-m) calls are DISCHARGED — (ITER-LAW-n) off DCX-(n) is "
                "UNCONDITIONAL\nthere for every n ≥ 3 (n = 1, 2: the accepted [IL]†/[IL3]† "
                "statements\nverbatim, no T-condition).")

# ---- new node: cc-rmgen
cc_rmgen = {
 "id": "cc-rmgen",
 "title": "THEOREM RM-GEN: the generic read-multiplication engine, every level — accepted 2026-08-04",
 "status": "proved-note",
 "math": ("The engine the all-orders induction was waiting on, closed level-generically: the four (RM-$m$) "
          "box clauses — the product-with-correction re-development inside the level-$m$ read — hold "
          "for every $m \\ge 1$ on the displayed scope T-scope$(m)$: either $d_0 = 1$ (degenerate flat reads "
          "admitted) or $e_0 \\ge 2$ with every middle $e_i \\ge 2$. The proof is a depth calculus: a finite "
          "cell tree for the development, exact line quanta on the promotion edge, a $\\mathfrak{z}$-"
          "multiplicativity kernel, and a generic termination measure that drops strictly at every promotion. "
          "Mid-arc the theorem got stronger, not weaker: a round-one verifier finding forced the corner-fence "
          "mechanism to be recomputed, and the repair extended the theorem to the $d_0 = 1$ flat corners with "
          "the full derivation displayed — the accepted scope includes them. Off the scope ($d_0 \\ge 2$ "
          "with a flat or $e_0 = 1$ level) the corners stay fenced, the fence's infeasibility machine-confirmed."),
 "note": ("Proved (note) — accepted 2026-08-04 at the two-clean bar: in round seven both verifiers "
          "— different model families, fresh contexts, the same pinned text — returned '0 critical, "
          "0 gaps: CLEAN'. Arc totals: seven rounds, twelve hostile passes (six Codex, six Fable); the proof "
          "sections byte-stable from the first revision on (one citation parenthetical aside); zero critical "
          "findings survived adjudication anywhere in the arc — the two critical-flagged round-one "
          "findings were both adjudicated text-layer (a lemma used but not displayed; a display-local fence "
          "slip) and repaired, with the no-weakening claim verified against the literal git diff. The theorem "
          "entered its arc countermodel-first: a sealed adversarial battery had already failed to break the "
          "four clauses, 405 of 405 instances. Machine referees rode the whole arc: a verifier's "
          "implementation forced from the text alone, 67 zero-violation engine calls on fresh flat towers, a "
          "1080-shape scope sweep, 225 machine confirmations of the fence's infeasibility."),
 "gate": ("Not machine-checked: an accepted mathematical proof note on the pinned model class. The scope is "
          "exactly T-scope(m) — the d₀ ≥ 2 flat corners remain fenced. The same note's level-m "
          "uniform carry law LAW-DCX-(m+1) remains a sealed conjecture at m ≥ 2, and its heuristic "
          "pool-identification row was refuted as literally worded after acceptance (the erratum is on the "
          "note; the row was consumed by nothing proved, verified by all twelve arc passes) — the "
          "corrected identification is the next node."),
 "lean": ("THEOREM RM-GEN (accepted 2026-08-04; campaign 2026-08-08):\n"
          "  the four (RM-m) box clauses hold LEVEL-GENERICALLY for every m ≥ 1 on\n"
          "  T-scope(m) := d₀ = 1  ∨  (e₀ ≥ 2 ∧ e_i ≥ 2 for all 1 ≤ i ≤ m−1)\n"
          "  — the d₀ = 1 flat corners INCLUDED (the round-1 branch-(b) extension);\n"
          "  the d₀ ≥ 2 flat corners FENCED (infeasibility machine-confirmed)\n\n"
          "Arc: 7 rounds, 12 hostile passes (6 Codex + 6 Fable); round-7 verdicts,\n"
          "both on the pinned text a0e266c, verbatim:\n"
          "  RMENGINE-PC7 FINDINGS: 0 critical, 0 gaps / VERDICT: CLEAN\n"
          "  RMENGINE-PE7 FINDINGS: 0 critical, 0 gaps / VERDICT: CLEAN\n\n"
          "COR-A FIRES at acceptance: on T-class(n) := d₀ = 1 ∨ (e₀ ≥ 2 ∧ e_i ≥ 2,\n"
          "i ≤ n−2), the (RM-m) calls of (ITER-LAW-n) are DISCHARGED — see the\n"
          "all-orders node above.  Still open in this note: LAW-DCX-(m+1), sealed\n"
          "conjecture at m ≥ 2 (row-11c erratum → the corrected PID†, next node)."),
 "srcLabel": "The verdict lines (from the acceptance record)",
 "file": "lean/notes/openmath/RMENGINE_2026-08-08.md",
 "kind": "accepted proof note (adversarially verified, seven rounds, twelve passes)"
}

# ---- new node: cc-pooltruth
cc_pooltruth = {
 "id": "cc-pooltruth",
 "title": "The pool identification: refuted as worded, corrected, proved layer by layer — one boxed residual",
 "status": "measured",
 "math": ("The corner law LAW-DCX-$(m+1)$ rests on a pool identification: that the promotion count at each "
          "level equals the floor $\\lfloor \\mathrm{pool}_l / e_{l-1} \\rfloor$. Going into the engine arc "
          "this was graded an honest heuristic (the ledger's row 11c), and the sealed adversarial stress "
          "battery then did its job twice over. The law itself: CONFIRMED — 0 divergences over 10,484 "
          "adversarial pairs. The literal floor identification: REFUTED — 72 instance-keyed divergences, "
          "physical promotion counts exceeding the floor (the floor caps the pool variable, not tree paths), "
          "the divergence set reproduced set-exactly by two independent instruments. The corrected "
          "identification PID$^\\dagger$: the floor is the exact maximum of the promotion count on the "
          "dump-free principal subtree — a cap always, attained under displayed hypotheses — proved "
          "layer by layer (path ledger, cellwise depth threshold, dump-free cap, principal cascade) on the "
          "two-stage priority tree, every displayed intermediate machine-checked against the sealed battery's "
          "exact selection: 412 traced rows, 858 cells, 11 predicted-zero families all green. The single "
          "residual is boxed as one open lemma, (SURV-$(m+1)$), with a conjecture-grade design route: "
          "deadness = cell-absence, consistent with all 126 traced dead rows carrying zero cells."),
 "note": ("Badged MEASURED, not proved (note), by this map's own legend: 'proved (note)' is reserved for "
          "notes ACCEPTED under the hostile-arc bar, and this note's arc is in progress — acceptance "
          "counter 0 of 2 clean (round one returned one critical, against a prose claim the note's own "
          "artifacts refute; the claim was withdrawn and rewritten; rounds two and three returned zero "
          "criticals). What is certified today is exactly the sealed content: the law confirmed on 10,484 "
          "adversarial pairs, the literal identification refuted by 72 divergences, and the corrected "
          "proof's machine-checked intermediates. The refutation inside the victory is the discipline "
          "working: the refuted row was consumed by nothing proved — verified by all twelve engine-arc "
          "passes — so the erratum cost no accepted clause."),
 "lean": ("LAW-DCX-(m+1) sealed stress (seal d3950f2 / verdict d774ecb):\n"
          "  LAW lines:  0 / 10,484 adversarial pairs — NO countermodel\n"
          "  PID-MAX:   72 instance-keyed divergences — the literal floor\n"
          "             identification REFUTED as worded (row-11c erratum)\n\n"
          "PID† (the corrected identification; the W-MULT-DCX composer unit):\n"
          "  W-D1 … W-D7 + the assembled identification — PROVED at attempt grade;\n"
          "  machine-checked intermediates: 412 traced rows (the sealed battery's\n"
          "  exact selection) · 858 Q¹ cells · 11 predicted-0 families ALL GREEN\n"
          "  arc: 0/2 clean (PE1 NOT-CLEAN → W-r1 repair; rounds 2–3: 0 critical)\n\n"
          "Residual, boxed: (SURV-(m+1)) — residue survival of the depth-graded\n"
          "parts; design route (EMPTY-(m+1)), conjecture-grade: deadness =\n"
          "cell-absence (126/126 traced dead rows carry ZERO Q¹ cells)."),
 "srcLabel": "The stress verdict and the boxed residual (from the composer note)",
 "file": "lean/notes/openmath/WMULTDCX_2026-08-08.md",
 "kind": "sealed stress verdict + attempt-grade corrected proof (hostile arc in progress)"
}

# ---- cc-twofamilies rewritten as the new frontier (id kept for stability)
tf = byid['cc-twofamilies']
tf['title'] = "THE FRONTIER: one boxed lemma layer — (SURV)/(EMPTY) — before the uniform carry law"
tf['status'] = "open"
tf['math'] = ("The frontier moved, and shrank. At the last refresh it was two named lemma families; THEOREM "
              "RM-GEN closed the first — (RM-$m$) for every $m \\ge 1$ on its displayed scope — and "
              "the pool-truth unit reduced the second to a single boxed lemma. What now stands between the "
              "corpus and the uniform carry law LAW-DCX-$(m+1)$ is one layer: (SURV-$(m+1)$), residue "
              "survival/cancellation of the depth-graded parts, with the conjecture-grade (EMPTY-$(m+1)$) "
              "route as design input — deadness = cell-absence, the reduction independently re-derived "
              "valid twice. Behind it, unchanged from the last refresh: the fenced corners — the "
              "$d_0 \\ge 2$ flat fence (infeasibility machine-confirmed), the DEV-1 $e_0 = 1 \\wedge d_0 \\ge 2$ "
              "corner, the (TAIL-STAB) compose — and the lift residual (ITER-LAW-LIFT), open exactly at "
              "$g_0 = 1 \\wedge \\delta_1 = 1$ with two measured companion conjectures. Standing over all of "
              "it, the one account beyond the model class: the semantic weld (next node).")
tf['note'] = ("Since the engine's acceptance (2026-08-04) this node is the frontier again, and it is shorter "
              "than it has ever been: one boxed lemma before the corner law at every depth, then the corners "
              "and the lift residual, then the weld. Each item named, each priced, none hidden inside a "
              "'routine' step.")
tf['lean'] = ("(SURV-(m+1))  [residue survival of the depth-graded parts]: OPEN, boxed —\n"
              "   THE last layer before LAW-DCX-(m+1), the uniform carry law;\n"
              "   design route (EMPTY-(m+1)), conjecture-grade: deadness = cell-absence\n"
              "   (reduction independently re-derived VALID twice)\n\n"
              "CLOSED since the last refresh:\n"
              "   (RM-m), every m ≥ 1 on T-scope(m) — THEOREM RM-GEN, accepted 2026-08-04\n"
              "   (m = 1 was proved inside [IL3]†; m ≥ 2 was THE resisting leg)\n\n"
              "UNCHANGED (Q3/Q4 of the standing queue):\n"
              "   the fenced corners: the d₀ ≥ 2 flat fence (machine-confirmed) ·\n"
              "   the DEV-1 e₀ = 1 ∧ d₀ ≥ 2 corner · the (TAIL-STAB) compose\n"
              "   (ITER-LAW-LIFT): OPEN exactly at g₀ = 1 ∧ δ₁ = 1;\n"
              "   LIFT-DEV-3 / LIFT-DEV-4: measured conjectures (sealed cycles owed)\n"
              "   the GRT semantic weld: GRT-2 = grTie proper OPEN, priced L")
tf['srcLabel'] = "The named open items (from the standing frontier)"
tf['file'] = "lean/notes/openmath/WMULTDCX_2026-08-08.md"
tf['kind'] = "the standing frontier (named, priced open items)"

# ---- insert the two new nodes right before the frontier node
idx = next(i for i, n in enumerate(nodes) if n['id'] == 'cc-twofamilies')
assert 'cc-rmgen' not in byid and 'cc-pooltruth' not in byid
nodes[idx:idx] = [cc_rmgen, cc_pooltruth]

json.dump(maps, open(BASE / 'maps.json', 'w'), indent=1, ensure_ascii=False)
print('maps.json: CocycleLadder now', len(nodes), 'nodes')

# ---------------------------------------------------------------- story.json
story = json.load(open(BASE / 'story.json'))

st = story['stages'][2]
assert st['id'] == 'carry-cocycle-ladder'
st['title'] = 'The carry-cocycle ladder (added 2026-08-03; updated 2026-08-04)'
old = 'are the entire remaining distance on the model class.'
assert old in st['summary']
st['summary'] = st['summary'].replace(old, old +
    " (Updated 2026-08-04: the harder of those two families — the per-level read-multiplication "
    "engine — is now itself an accepted theorem, RM-GEN, twelve hostile passes over seven rounds "
    "with zero critical findings surviving adjudication; the corner-law account is reduced to one "
    "boxed open lemma; the frontier nodes below carry the exact new state.)")

new_para = (
    "On August 4, 2026, the harder of the two open families closed. The engine at the heart of the "
    "all-orders induction — the law that re-develops a product inside each level's read, the step "
    "every middle level had been waiting on — is now a theorem: its four clauses hold at every level "
    "$m \\ge 1$ on an explicitly displayed scope, proved by a depth calculus of finite cell trees, exact "
    "quanta on the promotion edge, a multiplicativity kernel, and a termination measure. Its hostile arc "
    "ran seven rounds and twelve passes, six by each of two model families, ending in a round where both "
    "verifiers returned clean on the same pinned text, and the arc practiced everything the earlier "
    "acceptances preached. Countermodels came first: the clauses entered the arc only after a sealed "
    "adversarial battery had failed to break them in 405 of 405 instances, and when a round-one finding "
    "forced the corner-fence mechanism to be recomputed, the repair came back stronger — the theorem "
    "now covers a corner family first thought fenced — with the no-weakening claim verified against "
    "the literal git diff. Machine referees stood beside the readers throughout: an implementation forced "
    "from the text alone re-derived the engine, and sealed sweeps confirmed the extended scope and the "
    "remaining fence's infeasibility. The arc even carried a refutation inside the victory: one row of "
    "the note's own honesty ledger, a heuristic pool identification consumed by nothing proved, was "
    "refuted as literally worded by the very stress battery built for its corner law — seventy-two "
    "divergences against a law otherwise confirmed on 10,484 adversarial pairs — and the corrected "
    "identification has since been proved layer by layer at attempt grade, its own arc still in progress, "
    "the whole account reduced to a single boxed open lemma. With the engine accepted, the all-orders "
    "recursion sheds its engine conditionality on the matching tower class; what stands between this "
    "corpus and the uniform carry law at every depth is that one boxed lemma, then the fenced corners, "
    "then the weld.")

paras = story['story'].split('\n\n')
assert paras[-1].startswith("The formalization's contribution"), paras[-1][:60]
paras.insert(len(paras) - 1, new_para)
story['story'] = '\n\n'.join(paras)

json.dump(story, open(BASE / 'story.json', 'w'), indent=1, ensure_ascii=False)
print('story.json: stage updated +', len(paras), 'story paragraphs')
