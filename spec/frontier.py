#!/usr/bin/env python3
"""DAG frontier: which blueprint nodes are open, and which are ready to work.

Run from the repo root: `python3 spec/frontier.py`

WHAT IT MEASURES, and its two known limits — read these before quoting numbers.

* "LANDED" here means only that a per-node `leanfinal/Uniformity/Chap*/<node>.lean`
  FILE EXISTS. It does NOT mean the node's signed statement is proved. Several nodes
  (C.72, C.114, H.122, C.27, C.40) have green, Lean-core, `sorry`-free files whose
  SIGNED statements are not landed — carriers, degenerate strata, carried binders, or
  outright refutations. For proved-vs-carrier-vs-placeholder counts use the
  SIGNED-NAME CENSUS instead: `spec/census_driver.py` +
  `docs/SIGNED_NAME_CENSUS_2026-08-20.md`.
* The DAG treats a node as satisfied when its file exists, so a node can appear
  frontier-ready while resting on an unproved supplier. C.36/C.57/C.58/C.75 looked
  ready off landed-but-BLOCKED C.35/C.53/C.72. Cross-check the per-node records.

BUG HISTORY (fixed here, kept as a warning): the first version matched a basename to a
node with `^([A-Z])(\\d+)` and DROPPED alphabetic suffixes, so `C14a.lean` mapped to node
`C.14` and nodes C.14a / C.56a / C.109a / B.42a / G.30a read as OPEN although landed and
wired — the landed count was understated by 8. This is the same class as the recorded
`C109iii/iv/v` multi-char-suffix defect. Suffixes are preserved below.
"""

import re
import glob
import os
import collections


def blueprint_nodes():
    """node id -> the heading's trailing text (kind tags, title)."""
    nodes = {}
    for f in glob.glob('blueprint/CHAP-*.md'):
        for m in re.finditer(r'^### NODE ([A-Z])\.(\d+[a-z]*)\s*(.*)$',
                             open(f).read(), re.M):
            nodes[f'{m.group(1)}.{m.group(2)}'] = m.group(3).strip()
    return nodes


def landed_nodes(nodes):
    """Node ids with a leanfinal file. Preserves alphabetic suffixes (see BUG HISTORY)."""
    landed, unmapped = set(), []
    for f in glob.glob('leanfinal/Uniformity/Chap*/*.lean'):
        b = os.path.basename(f)[:-5]
        m = re.match(r'^([A-Z])(\d+)([a-zA-Z]*)$', b)
        if not m:
            unmapped.append(b)
            continue
        L, num, suf = m.group(1), m.group(2), m.group(3)
        for c in (f'{L}.{num}{suf}', f'{L}.{int(num):02d}{suf}', f'{L}.{int(num)}{suf}',
                  f'{L}.{num}', f'{L}.{int(num):02d}', f'{L}.{int(num)}'):
            if c in nodes:
                landed.add(c)
                break
        else:
            unmapped.append(b)
    return landed, unmapped


def edges():
    """consumer -> {suppliers}, over BP.* endpoints only. `from` depends on `to`."""
    e = collections.defaultdict(set)
    for f in glob.glob('spec/DAG_BLUEPRINT_*.tsv'):
        for line in open(f):
            p = line.rstrip('\n').split('\t')
            if len(p) >= 3 and p[0].startswith('BP.') and p[1].startswith('BP.'):
                e[p[0][3:]].add(p[1][3:])
    return e


def main():
    nodes = blueprint_nodes()
    landed, unmapped = landed_nodes(nodes)
    dep = edges()
    op = [n for n in nodes if n not in landed]
    print(f'nodes {len(nodes)}  LANDED(file-exists) {len(landed)}  OPEN {len(op)}')
    per = collections.Counter(n[0] for n in op)
    tot = collections.Counter(n[0] for n in nodes)
    print('OPEN/chapter:', {c: f'{per.get(c, 0)}/{tot[c]}' for c in sorted(tot)})
    print(f'lean files with no blueprint node: {len(unmapped)} {sorted(unmapped)[:12]}')

    key = lambda x: (x[0], int(re.match(r'[A-Z]\.(\d+)', x).group(1)), x)
    front, near = [], []
    for n in sorted(op, key=key):
        missing = sorted(d for d in dep.get(n, ()) if d in nodes and d not in landed)
        if not missing:
            front.append(n)
        elif len(missing) == 1:
            near.append((n, missing[0]))
    print(f'\nFRONTIER (every dependency has a file) {len(front)}:')
    for n in front:
        print(f'  {n:9s} {nodes[n][:66]}')
    print(f'\nNEAR(1) (one dependency missing) {len(near)}:')
    for n, m in near:
        print(f'  {n:9s} <- {m:9s} {nodes[n][:52]}')


if __name__ == '__main__':
    main()
