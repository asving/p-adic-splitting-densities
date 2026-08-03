#!/usr/bin/env python3
"""Assemble the public expandable proof graph from the cartography JSON."""
import json, html, pathlib

BASE = pathlib.Path('/tmp/graph_build')
story = json.load(open(BASE / 'story.json'))
maps = json.load(open(BASE / 'maps.json'))

# Normalize corpus keys in maps to short names
def short(name):
    n = name.strip()
    for k in ['OM', 'capstone-chain', 'root-engine', 'CocycleLadder', 'MovesRBase', 'MovesGr', 'MovesSp',
              'MovesC', 'MovesS', 'MovesX', 'MovesD', 'MovesT', 'MovesV', 'MovesU',
              'HC1', 'HC2', 'Moves']:
        if n == k or n.startswith(k + ' ') or n.startswith(k + '('):
            return k
    return n

byc = {short(m['corpus']): m for m in maps}

STAGE_CORPORA = {
    'classifier-tree': ['OM', 'capstone-chain'],
    'carry-algebra': ['Moves', 'MovesC', 'MovesRBase', 'MovesGr', 'HC1', 'HC2'],
    'carry-cocycle-ladder': ['CocycleLadder'],
    'species-alphabet': ['MovesSp'],
    'branch-mass-laws': ['MovesD'],
    'transfer-assembly': ['MovesT'],
    'resummation-solve': ['MovesS', 'MovesV'],
    'exhaustion': ['MovesX'],
    'squeeze-theorem-u': ['MovesU'],
    'measure-route': ['root-engine'],
}

CORPUS_LABEL = {
    'OM': 'The classifier engine (OM)',
    'capstone-chain': 'The order-0 and degree-2 capstones (OM/RealInstance)',
    'Moves': 'The residual and landing engine (Moves)',
    'MovesC': 'Coordinates, masses, Theorem C (MovesC)',
    'MovesRBase': 'Base relations (MovesRBase)',
    'MovesGr': 'The graded-ring bridge (MovesGr)',
    'HC1': 'Hard core 1: the tower and carry algebra (HC1)',
    'HC2': 'Hard core 2: the existence bridge (HC2)',
    'MovesSp': 'The species alphabet (MovesSp)',
    'MovesD': 'Shapes, charts and mass laws (MovesD)',
    'MovesT': 'The branch tree and transfer recursion (MovesT)',
    'MovesS': 'The rational-function solve (MovesS)',
    'MovesV': 'Tables, ledgers and values (MovesV)',
    'MovesX': 'The exhaustion bounds (MovesX)',
    'MovesU': 'Theorem U: the capstone (MovesU)',
    'root-engine': 'The measure route and the trusted base (root modules)',
    'CocycleLadder': 'The carry-cocycle ladder (accepted proof notes and sealed numeric batteries, 2026-08-03)',
}

extra_stage = {
    'id': 'measure-route',
    'title': 'The independent measure route and the trusted base',
    'summary': ('A second, independent route expresses the densities through p-adic measure '
                'theory and the Denef–Igusa cell decomposition (entering as a cited axiom, '
                'used on this route only). The root modules also hold the shared vocabulary '
                '(rational-function carriers, the goal interfaces) and the axiom census that '
                'pins the trusted base of every capstone.'),
    'corpora': ['root-engine'],
}
stages = story['stages'] + [extra_stage]

BADGE = {
    'proved': ('proved', 'st-proved', 'machine-checked from Lean core axioms alone'),
    'proved-conditional': ('conditional', 'st-cond', 'machine-checked from named, displayed hypotheses'),
    'open': ('open', 'st-open', 'an explicitly fenced unproved goal'),
    'definition': ('definition', 'st-def', 'a definition or interface (nothing to prove)'),
    'cited-axiom': ('cited axiom', 'st-axiom', 'a literature result imported as a named, audited axiom'),
    'proved-note': ('proved (note)', 'st-note', 'proved in a mathematical proof note ACCEPTED under the campaign’s adversarial-verification bar (consecutive clean hostile passes by verifiers in fresh contexts, at least two model families) — not machine-checked'),
    'measured': ('measured', 'st-meas', 'a precisely stated law confirmed by large-scale exact numerics under sealed, preregistered batteries — instance evidence, never a proof step'),
}

def esc(s):
    return html.escape(s or '', quote=False)

def node_html(nd):
    label, cls, _ = BADGE.get(nd.get('status', 'definition'), BADGE['definition'])
    gate = nd.get('gate', '')
    parts = []
    parts.append('<details class="node"><summary><span class="badge %s">%s</span> %s</summary>' %
                 (cls, label, esc(nd['title'])))
    parts.append('<div class="node-body">')
    if nd.get('note'):
        parts.append('<p class="note">%s</p>' % esc(nd['note']))
    parts.append('<p class="math">%s</p>' % esc(nd['math']))
    if gate:
        parts.append('<p class="gate"><strong>Hypotheses this rests on:</strong> %s</p>' % esc(gate))
    parts.append('<details class="leansrc"><summary>%s</summary>' % esc(nd.get('srcLabel', 'The Lean statement')))
    parts.append('<pre><code>%s</code></pre>' % html.escape(nd['lean']))
    parts.append('<p class="file">%s &mdash; %s</p></details>' % (esc(nd['file']), esc(nd.get('kind', ''))))
    parts.append('</div></details>')
    return '\n'.join(parts)

def corpus_html(cname):
    m = byc.get(cname)
    if not m:
        return ''
    counts = {}
    for nd in m['nodes']:
        counts[nd.get('status', '?')] = counts.get(nd.get('status', '?'), 0) + 1
    csum = ' &middot; '.join('%d %s' % (v, BADGE.get(k, (k,))[0]) for k, v in sorted(counts.items()))
    parts = []
    parts.append('<details class="corpus"><summary><strong>%s</strong> <span class="csum">%s</span><br><span class="oneliner">%s</span></summary>' %
                 (esc(CORPUS_LABEL.get(cname, cname)), csum, esc(m['oneLiner'])))
    parts.append('<div class="corpus-body"><p class="role">%s</p>' % esc(m['role']))
    if m.get('corpusDeps'):
        parts.append('<p class="deps">Builds on: %s</p>' % esc(', '.join(m['corpusDeps'])))
    for nd in m['nodes']:
        parts.append(node_html(nd))
    parts.append('</div></details>')
    return '\n'.join(parts)

stage_blocks = []
for i, st in enumerate(stages, 1):
    parts = []
    parts.append('<details class="stage" id="%s"><summary><span class="stageno">%d</span> <strong>%s</strong></summary>' %
                 (st['id'], i, esc(st['title'])))
    parts.append('<div class="stage-body"><p>%s</p>' % esc(st['summary']))
    if st.get('mathHighlight'):
        parts.append('<div class="highlight">$$%s$$</div>' % st['mathHighlight'])
    for c in STAGE_CORPORA.get(st['id'], st.get('corpora', [])):
        parts.append(corpus_html(c))
    parts.append('</div></details>')
    stage_blocks.append('\n'.join(parts))

total_nodes = sum(len(m['nodes']) for m in maps)
status_totals = {}
for m in maps:
    for nd in m['nodes']:
        s = nd.get('status', '?')
        status_totals[s] = status_totals.get(s, 0) + 1

story_paras = ''.join('<p>%s</p>' % esc(p) for p in story['story'].split('\n\n'))
open_paras = ''.join('<p>%s</p>' % esc(p) for p in story['openSurface'].split('\n\n'))

legend = ''.join('<span class="badge %s">%s</span> %s<br>' % (cls, label, desc)
                 for label, cls, desc in BADGE.values())

page = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>The Uniformity Theorem, Mapped - Asvin G</title>
<link rel="stylesheet" href="../css/style.css">
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css">
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/contrib/auto-render.min.js"
 onload="renderMathInElement(document.body, {delimiters: [{left: '$$', right: '$$', display: true}, {left: '$', right: '$', display: false}]});"></script>
<style>
.gwrap { max-width: 950px; margin: 0 auto; padding: 0 1rem; }
details.stage { border: 1px solid #ccc; border-radius: 8px; margin: 0.8rem 0; padding: 0.4rem 0.9rem; background: #fafafa; }
details.stage > summary { font-size: 1.15rem; cursor: pointer; padding: 0.4rem 0; }
.stageno { display: inline-block; background: #333; color: #fff; border-radius: 50@PCT@; width: 1.6em; height: 1.6em; text-align: center; line-height: 1.6em; font-size: 0.9rem; margin-right: 0.4em; }
details.corpus { border-left: 3px solid #888; margin: 0.7rem 0 0.7rem 0.6rem; padding: 0.3rem 0.8rem; background: #fff; }
details.corpus > summary { cursor: pointer; }
.oneliner { color: #555; font-style: italic; font-size: 0.95rem; }
.csum { color: #777; font-size: 0.85rem; margin-left: 0.5em; }
details.node { margin: 0.55rem 0 0.55rem 0.8rem; border-left: 2px solid #ddd; padding: 0.15rem 0.7rem; }
details.node > summary { cursor: pointer; font-weight: 600; }
.node-body { margin: 0.4rem 0 0.2rem 0.2rem; }
.note { color: #444; }
.math { }
.gate { background: #fff8e6; border-left: 3px solid #d9a400; padding: 0.4rem 0.6rem; font-size: 0.95rem; }
details.leansrc { margin-top: 0.4rem; }
details.leansrc > summary { cursor: pointer; color: #2a6; font-size: 0.92rem; }
details.leansrc pre { background: #f4f4f4; border: 1px solid #e0e0e0; border-radius: 6px; padding: 0.7rem; overflow-x: auto; font-size: 0.82rem; line-height: 1.35; }
.file { color: #888; font-size: 0.8rem; }
.badge { display: inline-block; border-radius: 4px; padding: 0.05em 0.5em; font-size: 0.75rem; font-weight: 700; vertical-align: middle; margin-right: 0.35em; }
.st-proved { background: #d9f2d9; color: #1d6b1d; }
.st-cond { background: #fff1cc; color: #8a6400; }
.st-open { background: #fde2e2; color: #a12727; }
.st-def { background: #e8e8e8; color: #444; }
.st-axiom { background: #e6e0f5; color: #4b3a8a; }
.st-note { background: #d9e9f5; color: #14527d; }
.st-meas { background: #d9f2ee; color: #0e6b5c; }
.highlight { background: #eef4fb; border-radius: 6px; padding: 0.5rem 0.8rem; margin: 0.6rem 0; overflow-x: auto; }
.capstone { border: 2px solid #345; border-radius: 8px; padding: 0.6rem 1rem; background: #f4f7fa; margin: 1rem 0; }
.opensurface { border: 1px solid #d9a400; border-radius: 8px; background: #fffdf2; padding: 0.6rem 1rem; margin: 1.2rem 0; }
.controls { margin: 0.8rem 0; }
.controls button { margin-right: 0.6rem; padding: 0.25rem 0.7rem; cursor: pointer; }
.controls input { padding: 0.25rem 0.5rem; width: 16em; }
.howto { background: #f0f0f0; border-radius: 6px; padding: 0.5rem 0.9rem; font-size: 0.95rem; }
</style>
</head>
<body>
<header>
  <img src="../images/banner.jpg" alt="Grothendieck-Riemann-Roch" class="banner">
  <div class="container">
    <div class="site-title">
      <h1><a href="../index.html">Asvin G</a></h1>
      <p class="tagline">Wir m&uuml;ssen wissen, wir werden wissen</p>
    </div>
    <nav><ul>
      <li><a href="../index.html">About</a></li>
      <li><a href="../blog.html">Blog</a></li>
      <li><a href="../claude/index.html">Claude</a></li>
      <li><a href="../book-reviews.html">Book Reviews</a></li>
    </ul></nav>
  </div>
</header>
<main class="gwrap">
<h1>The Uniformity Theorem for p-adic Splitting Densities, Mapped</h1>
<p class="post-date">The Lean 4 formalization as an expandable graph &mdash; every node carries the formal statement and its mathematical translation. Companion to <a href="paper.html">the expository account</a>. Built July 2026; stage 3 (the carry-cocycle ladder) and the refreshed honest boundary added August 3, 2026.</p>

<div class="howto"><strong>How to read this page.</strong> The page has four levels. The <em>story</em> below reads on its own. Each numbered <em>stage</em> expands to a summary of one step of the proof. Inside a stage, each <em>module group</em> expands to its role and its main results. Each <em>result</em> expands to a plain-mathematics translation, and one further click shows the exact Lean statement. Status badges say what kind of certificate each node carries; the legend is at the bottom, and the honest boundary of the whole development is in the amber panel.</div>

<h2>The theorem</h2>
<p>%(headline)s</p>

<h2>The story</h2>
%(story)s

<div class="capstone">
<h3>The capstone, exactly</h3>
<p>%(thmmath)s</p>
<details class="leansrc"><summary>The Lean statement of Theorem U</summary>
<pre><code>%(thmlean)s</code></pre>
<p class="file">lean/LeanUrat/MovesU/U10_theoremU.lean &mdash; axioms: propext, Classical.choice, Quot.sound (Lean core only)</p>
</details>
</div>

<h2>The proof, stage by stage</h2>
<div class="controls">
<button onclick="setAll(true)">Expand everything</button>
<button onclick="setAll(false)">Collapse everything</button>
<input id="q" placeholder="Filter results by title..." oninput="doFilter()">
</div>
%(stages)s

<div class="opensurface">
<h3>The honest boundary</h3>
%(open)s
</div>

<h3>Legend</h3>
<p>%(legend)s</p>
<p class="file">This map shows %(total)s selected results: %(ptot)s proved (machine-checked), %(ctot)s conditional (machine-checked implications), %(ntot)s proved in accepted proof notes (adversarially verified, not machine-checked), %(mtot)s measured (sealed exact numerics), %(otot)s open, %(dtot)s definitions, %(atot)s cited axioms. The Lean-backed nodes are a selection from roughly 970 public theorems and definitions in the development; selection favors load-bearing results, interfaces, and honest negative results (compiled countermodels).</p>

<p class="file">Provenance: the mathematics extends <a href="https://arxiv.org/abs/2212.00294">A Chebotarev Density Theorem over Local Fields</a> (Asvin G, Yifan Wei, John Yin). The formalization was carried out in Lean 4 with Mathlib by Claude (Anthropic) orchestrating fleets of proving and adversarially verifying agents, with independent statement audits by a second model family (OpenAI Codex), under the direction of Asvin G. Page generated from the formal development; translations audited for faithfulness to the Lean statements.</p>
</main>
<footer><div class="container"><p>&copy; Asvin G</p></div></footer>
<script>
function setAll(open) {
  document.querySelectorAll('main details').forEach(d => d.open = open);
}
function doFilter() {
  const q = document.getElementById('q').value.toLowerCase();
  document.querySelectorAll('details.node').forEach(d => {
    const t = d.querySelector('summary').textContent.toLowerCase();
    const hit = !q || t.includes(q);
    d.style.display = hit ? '' : 'none';
    if (q && hit) {
      d.open = false;
      let p = d.parentElement;
      while (p) { if (p.tagName === 'DETAILS') p.open = true; p = p.parentElement; }
    }
  });
}
</script>
</body>
</html>
"""

subs = {
    'headline': esc(story['headline']),
    'story': story_paras,
    'thmmath': esc(story['theoremUMath']),
    'thmlean': html.escape(story['theoremULean']),
    'stages': '\n'.join(stage_blocks),
    'open': open_paras,
    'legend': legend,
    'total': str(total_nodes),
    'ptot': str(status_totals.get('proved', 0)),
    'ctot': str(status_totals.get('proved-conditional', 0)),
    'otot': str(status_totals.get('open', 0)),
    'dtot': str(status_totals.get('definition', 0)),
    'atot': str(status_totals.get('cited-axiom', 0)),
    'ntot': str(status_totals.get('proved-note', 0)),
    'mtot': str(status_totals.get('measured', 0)),
}
out = page
for k, v in subs.items():
    out = out.replace('%(' + k + ')s', v)
out = out.replace('@PCT@', '%')

dest = pathlib.Path('/tmp/graph_build/index.html')
dest.write_text(out)
print('wrote', dest, len(out), 'bytes')
