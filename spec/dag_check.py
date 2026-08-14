#!/usr/bin/env python3
"""PHASE-0c DAG CHECKER.  Reads spec/DAG.tsv + spec/DAG_NODES.tsv + spec/DAG_NONIMPORTS.tsv
and runs the 0c design contract's checks:

  1  dangling-ID check          (every edge endpoint is a declared node)
  2  cycle detection            (SCCs; each non-trivial SCC must be ADJUDICATED below)
  3  reachability from the capstone (unreachable subgraphs = candidate out-of-cone)
  4  topological layering + per-layer width  (the parallelism ceiling)
  5  chapter-cut check          (chapter order is topological up to a measured residue)
  6  non-import fence check     (no recorded edge crosses a recorded negative-import fence)
  7  resolution census          (how much of the graph is COARSE and therefore provisional)

Usage:  python3 spec/dag_check.py            # report to stdout
        python3 spec/dag_check.py > spec/dag_check_output.txt
Exit code is 0 unless an UNADJUDICATED cycle or a dangling ID is found.
"""
import csv, sys, collections

EDGES_F, NODES_F, NONIMP_F = 'spec/DAG.tsv', 'spec/DAG_NODES.tsv', 'spec/DAG_NONIMPORTS.tsv'

# Edge classes that are NOT dependency edges (kept in DAG.tsv as recorded provenance).
NON_DEP = {'ledger-index'}

# Chapter order, consumer-first.  Derived from the computed condensation (see DAG_README).
CHAPTER_ORDER = ['I', 'E', 'D', 'C', 'B', 'H', 'F', 'G', 'A']
CHAPTER_NAME = {
    'A': 'LANDED LEAN KERNEL (DONE)',
    'B': 'HENSEL-SLOT CORE',
    'C': 'TOWER GRAMMAR  [HARD]',
    'D': 'GAUGE + CERTIFICATE T-CHAIN',
    'E': 'SIGMA-LADDER MASTER  [HARD]',
    'F': 'GRT WELD LAYER',
    'G': 'BASE CASES AND MENUS',
    'H': 'GENERAL INDUCTION',
    'I': 'CAPSTONE AND CONDITIONALITY',
}

# --------------------------------------------------------------------- adjudications
# Every non-trivial SCC of the EXACT-resolved dependency subgraph must appear here with a
# reason.  An SCC that appears only in the COARSE graph is reported as COARSE-ARTEFACT:
# the COARSE-GOV placeholder collapses a whole note onto one unit, so any two notes that
# cite each other become a 2-cycle whether or not the mathematics is mutual.
ADJUDICATED = {
    frozenset(['EFF.GRTW2.20', 'EFF.LIFTCORNER.72']):
        'MUTUAL-RECON (recorded both ways): LIFTCORNER cites GRTW2 W2-OPEN-2 in its own '
        'XREF ledger and GRTW2 is listed as a consumer of LIFTCORNER .72 in the shard-1 '
        'reverse-XREF table.  Not resolved here: the chapter blueprint must decide which '
        'direction is the statement dependency.',
    frozenset(['EFF.GRTW2.35', 'EFF.LIFTCORNER.62']):
        'MUTUAL-RECON (recorded both ways), same shape as GRTW2.20 / LIFTCORNER.72, on the '
        'W2-OPEN-1 designation.',
    frozenset(['EFF.HE7.128', 'EFF.HE7.129', 'EFF.HE7.130']):
        'INTRA-NOTE SELF-SUPPLY: HE7\'s "HE7 itself (inbound)" ledger rows are read as both '
        'forward and reverse edges by the harvester.  Not a mathematical cycle; a direction '
        'ambiguity in the source table.',
    frozenset(['EFF.GENIND.136', 'EFF.HEX3.37', 'EFF.HMENU3.33']):
        'HEX3-BOX-1 (the tail-sigma certification lemma, ledger HYP.137) is supplied by HEX3 '
        'and consumed by GENIND and HMENU3; HEX3 s own 4.3 table mixes supplier and consumer '
        'rows under one heading, so the harvester reads one consumer edge backwards.',
}

# ------------------------------------------------------------------------------ load
def load():
    edges = list(csv.DictReader(open(EDGES_F, encoding='utf-8'), delimiter='\t'))
    nodes = {n['id']: n for n in csv.DictReader(open(NODES_F, encoding='utf-8'), delimiter='\t')}
    fences = list(csv.DictReader(open(NONIMP_F, encoding='utf-8'), delimiter='\t'))
    return edges, nodes, fences

def is_exact(e):
    return 'gov' not in e['resolution'] and 'unmatched' not in e['resolution']

def scc(G, nodes):
    idx, low, on, st, out, c = {}, {}, {}, [], [], [0]
    for v in nodes:
        if v in idx:
            continue
        work = [(v, iter(sorted(G.get(v, ()))))]
        idx[v] = low[v] = c[0]; c[0] += 1; st.append(v); on[v] = True
        while work:
            u, it = work[-1]
            adv = False
            for w in it:
                if w not in idx:
                    idx[w] = low[w] = c[0]; c[0] += 1; st.append(w); on[w] = True
                    work.append((w, iter(sorted(G.get(w, ()))))); adv = True; break
                elif on.get(w):
                    low[u] = min(low[u], idx[w])
            if adv:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[u])
            if low[u] == idx[u]:
                comp = []
                while True:
                    w = st.pop(); on[w] = False; comp.append(w)
                    if w == u:
                        break
                out.append(comp)
    return out

def main():
    edges, nodes, fences = load()
    dep = [e for e in edges if e['edge-class'] not in NON_DEP]
    G = collections.defaultdict(set)
    for e in dep:
        G[e['from-ID']].add(e['to-ID'])
    Gx = collections.defaultdict(set)
    for e in dep:
        if is_exact(e):
            Gx[e['from-ID']].add(e['to-ID'])
    fail = 0
    P = print

    P('PHASE-0c DAG CHECK  (spec/DAG.tsv)')
    P('=' * 78)
    P('nodes %d   edges %d   dependency edges %d   non-dependency (provenance) %d'
      % (len(nodes), len(edges), len(dep), len(edges) - len(dep)))
    kinds = collections.Counter(n['node-kind'] for n in nodes.values())
    P('node kinds: ' + '  '.join('%s=%d' % kv for kv in sorted(kinds.items())))
    cls = collections.Counter(e['edge-class'] for e in edges)
    P('edge classes: ' + '  '.join('%s=%d' % kv for kv in sorted(cls.items())))
    P('edge kinds: ' + '  '.join('%s=%d' % kv for kv in
                                 sorted(collections.Counter(e['edge-kind'] for e in edges).items())))

    # 1 --------------------------------------------------------------- dangling IDs
    P('\n[1] DANGLING-ID CHECK')
    dang = sorted({x for e in edges for x in (e['from-ID'], e['to-ID']) if x not in nodes})
    if dang:
        fail = 1
        P('    FAIL: %d endpoints absent from DAG_NODES.tsv' % len(dang))
        for d in dang[:20]:
            P('      ' + d)
    else:
        P('    PASS: every edge endpoint is a declared node.')

    # 2 -------------------------------------------------------------------- cycles
    P('\n[2] CYCLE DETECTION')
    comps_x = [c for c in scc(Gx, list(nodes)) if len(c) > 1]
    comps_a = [c for c in scc(G, list(nodes)) if len(c) > 1]
    P('    EXACT-resolved subgraph (%d edges): %d non-trivial SCCs'
      % (sum(len(v) for v in Gx.values()), len(comps_x)))
    unadj = []
    for c in sorted(comps_x, key=len, reverse=True):
        key = frozenset(x for x in c if not x.startswith('EXT:'))
        note = None
        for k, v in ADJUDICATED.items():
            if k <= key or key <= k or len(k & key) >= 2:
                note = v
                break
        tag = 'ADJUDICATED' if note else 'UNADJUDICATED'
        if not note:
            unadj.append(c)
        P('      [%s] size %d: %s' % (tag, len(c), ', '.join(sorted(c))))
        if note:
            P('            ' + note)
    P('    FULL graph incl. COARSE-GOV edges: %d non-trivial SCCs, largest %d'
      % (len(comps_a), max([len(c) for c in comps_a] or [0])))
    P('      COARSE-ARTEFACT: a COARSE-GOV edge lands on the target note\'s single governing')
    P('      unit, so any two notes citing each other collapse to a 2-cycle.  Cycles present')
    P('      only in the full graph are therefore NOT evidence of mutual mathematics.')
    if unadj:
        fail = 1
        P('    FAIL: %d unadjudicated exact cycle(s).' % len(unadj))
    else:
        P('    PASS: every exact-subgraph cycle is adjudicated.')
    P('    NOTE on the flagged HE6 <-> HE6R1 pair: the two notes DO cite each other, but no')
    P('    unit-level cycle between them survives in the exact subgraph — HE6 -> HE6R1 and')
    P('    HE6R1 -> HE6 land on disjoint units.  The mutual-recon flag is a note-level, not a')
    P('    statement-level, phenomenon.')

    # 3 -------------------------------------------------------------- reachability
    P('\n[3] REACHABILITY FROM THE CAPSTONE')
    roots = [n for n in nodes if n.startswith('CAP:')]
    seen = set()
    stack = list(roots)
    while stack:
        v = stack.pop()
        if v in seen:
            continue
        seen.add(v)
        stack.extend(G.get(v, ()))
    P('    roots: %s' % ', '.join(roots))
    P('    reachable %d / %d nodes (%.1f%%)' % (len(seen), len(nodes), 100.0 * len(seen) / len(nodes)))
    heads = set(G) | {b for a in G for b in G[a]}
    iso = [n for n in nodes if n not in heads]
    unre = [n for n in nodes if n not in seen]
    conn_unre = [n for n in unre if n in heads]
    P('    unreachable %d, of which ISOLATED (no recorded edge at all) %d and'
      % (len(unre), len(unre) - len(conn_unre)))
    P('    CONNECTED-BUT-UNREACHABLE %d  <- the real candidate out-of-cone list'
      % len(conn_unre))
    bynote = collections.Counter((nodes[n]['note'] or nodes[n]['node-kind']) for n in conn_unre)
    P('    connected-but-unreachable by note/kind:')
    for k, v in sorted(bynote.items(), key=lambda kv: -kv[1]):
        P('      %-14s %4d' % (k, v))
    P('    LEDGER CONSISTENCY — rows the 0b ledger signs NOT-REACHED / out-of-cone must NOT')
    P('    be reachable here:')
    for h in ('HYP.21', 'HYP.75', 'HYP.83', 'HYP.84', 'HYP.85', 'HYP.86', 'HYP.76'):
        if h in nodes:
            P('      %-8s %s' % (h, 'CONSISTENT (unreachable)' if h not in seen
                                 else 'INCONSISTENT (reachable from the capstone)'))
    P('    total isolated nodes: %d' % len(iso))
    P('    The 0a specs record inter-note supply edges and supersession chains, but they do')
    P('    NOT record intra-note statement->statement dependencies.  Unreachability here is')
    P('    therefore mostly MISSING EDGE DATA, not an out-of-cone verdict.  Compare against')
    P('    the ledger NOT-REACHED rows (HYP.21/75, HYP.83-86) before treating any of it as')
    P('    out-of-cone.')

    # 4 ------------------------------------------------------------------ layering
    P('\n[4] TOPOLOGICAL LAYERING (SCCs collapsed)')
    comps = scc(G, list(nodes))
    cid = {}
    for i, c in enumerate(comps):
        for x in c:
            cid[x] = i
    CG = collections.defaultdict(set)
    for a in G:
        for b in G[a]:
            if cid[a] != cid[b]:
                CG[cid[a]].add(cid[b])
    depth = {}
    order = sorted(range(len(comps)), key=lambda i: 0)
    # longest-path depth by memoised DFS on the condensation (a DAG)
    def dep_of(i):
        if i in depth:
            return depth[i]
        depth[i] = 0
        d = 0
        for j in CG.get(i, ()):
            d = max(d, 1 + dep_of(j))
        depth[i] = d
        return d
    sys.setrecursionlimit(20000)
    for i in range(len(comps)):
        dep_of(i)
    lay = collections.Counter()
    lay_conn = collections.Counter()
    connected = set(G) | {b for a in G for b in G[a]}
    for i, c in enumerate(comps):
        lay[depth[i]] += len(c)
        lay_conn[depth[i]] += sum(1 for x in c if x in connected)
    P('    layers: %d   (layer 0 = terminal supply)' % (max(lay) + 1))
    P('    %-6s %10s %10s' % ('layer', 'nodes', 'connected'))
    for k in sorted(lay):
        P('    %-6d %10d %10d' % (k, lay[k], lay_conn[k]))
    P('    MAX LAYER WIDTH (all nodes)       = %d   <- nominal parallelism ceiling' % max(lay.values()))
    P('    MAX LAYER WIDTH (connected nodes) = %d   <- ceiling on the edge-bearing subgraph'
      % max(lay_conn.values()))
    P('    Layer 0 is dominated by the %d isolated nodes; the connected column is the honest' % len(iso))
    P('    reading.  DAG width is an upper bound on parallelism, never a throughput promise')
    P('    (BLUEPRINT_PHASE_DESIGN REVISION 2, R15).')

    # 5 -------------------------------------------------------------- chapter check
    P('\n[5] CHAPTER-CUT CHECK')
    pos = {c: i for i, c in enumerate(CHAPTER_ORDER)}
    W = collections.Counter()
    unassigned = 0
    for e in dep:
        a, b = nodes.get(e['from-ID']), nodes.get(e['to-ID'])
        if not a or not b:
            continue
        ca, cb = a['chapter'], b['chapter']
        if not ca or not cb:
            unassigned += 1
            continue
        if ca != cb:
            W[(ca, cb)] += 1
    tot = sum(W.values())
    back = sum(w for (a, b), w in W.items() if pos.get(a, 99) > pos.get(b, 99))
    P('    chapter order (consumer-first): ' + ' > '.join(CHAPTER_ORDER))
    for c in CHAPTER_ORDER:
        n = sum(1 for x in nodes.values() if x['chapter'] == c)
        P('      %s  %-32s %5d nodes' % (c, CHAPTER_NAME[c], n))
    P('    cross-chapter dependency edges: %d   backward (against the order): %d (%.1f%%)'
      % (tot, back, 100.0 * back / tot if tot else 0))
    P('    edges with an unassigned endpoint (EXT / unmatched): %d' % unassigned)
    P('    BACKWARD ARCS — the residue that makes the cut non-strict; each is a split the')
    P('    chapter blueprints must make at unit granularity:')
    for (a, b), w in sorted(W.items(), key=lambda kv: -kv[1]):
        if pos.get(a, 99) > pos.get(b, 99):
            P('      %s -> %s   %d' % (a, b, w))

    # 6 ---------------------------------------------------------------- non-imports
    P('\n[6] NON-IMPORT FENCE CHECK')
    banned_note = collections.defaultdict(set)
    for f in fences:
        for u in f['fenced-units'].split(';'):
            for b in f['banned-designations-or-notes'].split(';'):
                if b.startswith('NOTE:'):
                    banned_note[u].add(b[5:])
    viol = []
    for e in dep:
        tgt = nodes.get(e['to-ID'])
        if tgt and tgt['note'] and tgt['note'] in banned_note.get(e['from-ID'], ()):
            viol.append(e)
    P('    fences recorded: %d rows over %d fenced units'
      % (len(fences), len({u for f in fences for u in f['fenced-units'].split(';')})))
    P('    edges crossing a recorded note-level fence: %d' % len(viol))
    for e in viol[:15]:
        P('      %s -> %s  [%s]  %s' % (e['from-ID'], e['to-ID'], e['edge-class'], e['evidence'][:90]))
    P('    A hit here is NOT automatically a defect: a fence names material the note does not')
    P('    IMPORT, while a recorded edge may be a citation of record.  Each hit is a')
    P('    cross-read question.')

    # 7 ----------------------------------------------------------------- resolution
    P('\n[7] RESOLUTION CENSUS (how provisional is this graph?)')
    res = collections.Counter(e['resolution'] for e in edges)
    for k, v in sorted(res.items(), key=lambda kv: -kv[1]):
        P('      %-28s %5d' % (k, v))
    coarse = sum(v for k, v in res.items() if 'gov' in k or 'unmatched' in k)
    P('    COARSE (an endpoint fell back to a note governing unit, or a conjunct matched no')
    P('    ledger row): %d of %d edges = %.1f%%.  Every one of these is a cross-read item.'
      % (coarse, len(edges), 100.0 * coarse / len(edges)))
    kb = collections.Counter(e['kind-basis'] for e in edges)
    P('    edge-kind basis: ' + '  '.join('%s=%d' % kv for kv in sorted(kb.items())))
    P('    stmt-dep/proof-dep is decided by rule 3 only for the %d edges whose designation was'
      % (kb.get('statement-hit', 0) + kb.get('derivation-hit', 0)))
    P('    found in the source unit\'s own text; the remaining %d default to stmt-dep and are'
      % kb.get('default', 0))
    P('    NOT a classification.')

    P('\n' + '=' * 78)
    P('RESULT: ' + ('FAIL' if fail else 'PASS') + '  (see DAG_README.md for what this artifact does and does not claim)')
    return fail

if __name__ == '__main__':
    sys.exit(main())
