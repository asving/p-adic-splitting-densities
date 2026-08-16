#!/usr/bin/env python3
"""One-shot generator for spec/DAG_BLUEPRINT_D.tsv (CHAP-D composer, 2026-08-15).
Edge lists are hand-audited against blueprint/CHAP-D_gauge_tchain.md's DEPENDS/SOURCE
fields. 9-column contract, consumer -> supplier.

AMENDMENT A-D.1 (2026-08-16, chapter-D stub-gate defect-repair round): five intra edges
added and one re-annotated, from the re-signed DEPENDS fields of the amendment
(see `intra_note` below). Intra edges 162 -> 167, rows 337 -> 342; still ACYCLIC, critical
path still 9 nodes, layer widths 10,9,13,7,8,6,6,4,5 -> 10,9,13,6,8,6,6,5,5 (D.39/D.40/
D.41/D.43 each drop one layer deeper). Run from the repo root: `python3 spec/gen_dag_d.py`."""
import csv, sys

GENTOW2_EXT = 'EXT:GENTOW2_PROOF_2026-08-09.md'

# --- intra-chapter DEPENDS edges: node -> [suppliers] --------------------------------
intra = {
 2:[1], 3:[2], 4:[1], 5:[1,2,4], 6:[4], 7:[1], 8:[2,4,5,7], 9:[5,8], 10:[6,8],
 11:[2], 12:[1,2], 14:[13], 15:[13,14], 16:[13], 17:[1,7,13], 18:[8,13,16,17],
 19:[12,13,15,17], 20:[7], 21:[13,15,17,19,20], 24:[13], 25:[13,24], 26:[13,24,25],
 27:[14,15], 28:[16,18,24,25], 29:[1,7], 32:[4,8,10,29], 33:[8,10,31,32], 35:[34],
 36:[20,21,22,23,29,30,31,32,33,34], 37:[7,8], 38:[8,10,37], 39:[1,7,8,12],
 40:[12,39], 41:[34,40], 42:[10,35,38], 43:[11,12,39,40,41], 44:[37,38],
 46:[45], 47:[46], 48:[46], 49:[46,47,48], 50:[46,47,48,49], 51:[48,49], 52:[48],
 53:[45,46,47,48,49,50,51,52], 54:[45,46,47,48,49,51], 55:[44], 56:[44], 57:[55],
 58:[10,34,35,44], 59:[34], 60:[55,59], 61:[29,44,55], 62:[1,7], 63:[55,62],
 65:[13,14,16,17,18,28,32,35,58], 66:[10,13,14,15,16,18,27,28,45,48],
 67:[6,8,10,12,17,38,39,40],
}

# --- A-D.1 per-edge evidence riders (the five added edges + the one re-annotated) ---------
intra_note = {
 (17,13): 'A-D.1/D-D2: DEFINITIONAL dependency, not merely a lemma dependency -- '
          "levelOneArena's exact_height field is discharged from iexp_aexp_spec, so the def's "
          'axiom footprint carries it; D.13 must LAND before D.17',
 (21,17): 'A-D.1/D-D8: edge was UNDECLARED -- the conclusion applies (levelOneArena ...).res, '
          "so D.21's STATEMENT depends on D.17 (statability, not only proof)",
 (39,8):  "A-D.1/D-D3: compData's real body applies A.mem_ker_div (D.08's proved helper)",
 (66,16): 'A-D.1/D-F1: leg 5 (FRAME-H2) scores a Wfloor table',
 (66,27): "A-D.1: leg 1's binary-carry grid executes D.27",
 (67,6):  "A-D.1: leg 4 IS the D.06 orientation table's arithmetic",
}

# --- transcription/SOURCE edges: node -> [EFF ids] -----------------------------------
src = {
 1:['EFF.T1.01','EFF.T1.02','EFF.T3.01'], 2:['EFF.T1.08','EFF.T3.02'],
 3:['EFF.T1.08','EFF.T3.02'], 4:['EFF.T1.09','EFF.T1.14','EFF.T3.03','EFF.T3.04'],
 5:['EFF.T1.10','EFF.T3.03'], 6:['EFF.T1.14','EFF.T3.04','EFF.T3.19'],
 7:['EFF.T1.01','EFF.T1.02','EFF.T1.03'], 8:['EFF.T1.09','EFF.T1.10','EFF.T3.03'],
 9:['EFF.T1.10','EFF.T3.03'], 10:['EFF.T3.04'], 11:['EFF.T3.15'],
 12:['EFF.T3.12','EFF.T3.16'], 13:['EFF.T1.01'], 14:['EFF.T1.07'], 15:['EFF.T1.19'],
 16:['EFF.T1.10'], 17:['EFF.T1.01','EFF.T1.04'], 18:['EFF.T1.10'],
 19:['EFF.T1.19','EFF.T1.26'], 20:['EFF.T1.04','EFF.T1.05'],
 21:['EFF.T1.06','EFF.T1.31'], 22:['EFF.T1.16','EFF.T1.29','EFF.T1.32'],
 23:['EFF.T1.17'], 24:['EFF.T1.20','EFF.T1.30'],
 25:['EFF.T1.20','EFF.T1.25','EFF.T1.30'], 26:['EFF.T1.18','EFF.T1.20','EFF.T1.30'],
 27:['EFF.T1.26'], 28:['EFF.T1.13','EFF.T1.27','EFF.T1.28'],
 29:['EFF.T1.03','EFF.T5.04','EFF.T5.09'], 30:['EFF.T1.02','EFF.T1.12'],
 31:['EFF.T1.11','EFF.T3.05'], 32:['EFF.T1.14','EFF.T5.11'],
 33:['EFF.T1.15','EFF.T1.31','EFF.T5.18'],
 34:['EFF.T1.15','EFF.T3.18','EFF.T5.05','EFF.T5.08'], 35:['EFF.T5.06'],
 36:['EFF.T1.22','EFF.T1.23'],
 37:['EFF.T3.06','EFF.T3.07','EFF.T3.08','EFF.T3.09','EFF.T3.10','EFF.T3.11'],
 38:['EFF.T3.14'], 39:['EFF.T3.12','EFF.T3.13'], 40:['EFF.T3.17'], 41:['EFF.T3.18'],
 42:['EFF.T3.19'], 43:['EFF.T3.20'], 44:['EFF.T3.21'], 45:['EFF.T4.01'],
 46:['EFF.T4.03','EFF.T4.04','EFF.T4.05','EFF.T4.06','EFF.T4.07','EFF.T4.08',
     'EFF.T4.09','EFF.T4.13'],
 47:['EFF.T4.12'], 48:['EFF.T4.09','EFF.T4.10','EFF.T4.11'], 49:['EFF.T4.14'],
 50:['EFF.T4.15'], 51:['EFF.T4.16'], 52:['EFF.T4.17','EFF.T4.19'],
 53:['EFF.T4.18','EFF.T4.19','EFF.T4.20','EFF.T4.21'],
 54:['EFF.T4.22','EFF.T4.23','EFF.T4.41'],
 55:['EFF.T3.22','EFF.T5.13','EFF.T5.29'], 56:['EFF.T5.12','EFF.T5.15'],
 57:['EFF.T5.14','EFF.T5.15'], 58:['EFF.T5.18','EFF.T5.19','EFF.T5.20'],
 59:['EFF.T3.24','EFF.T5.09','EFF.T5.32'],
 60:['EFF.T3.23','EFF.T5.30','EFF.T5.31'],
 61:['EFF.T5.07','EFF.T5.09','EFF.T5.10','EFF.T5.16','EFF.T5.28'],
 62:['EFF.T1.09','EFF.T5.10'], 63:['EFF.T3.22'], 64:['EFF.T3.30'],
 65:['EFF.T1.33','EFF.T1.34','EFF.T1.36'],
 66:['EFF.T1.33','EFF.T4.11','EFF.T4.20'], 67:['EFF.T3.29','EFF.T3.30'],
}

# --- chapter-B consumption (committed node IDs, GC-13(b)) ----------------------------
bdep = { 25:['BP.B.07','BP.B.08','BP.B.11','BP.B.14','BP.B.15'],
         26:['BP.B.21','BP.B.22'] }

# --- GC-13 placeholders: (node, target-in-DAG, evidence-tail) ------------------------
placeholders = [
 (6,  GENTOW2_EXT, 'contiguous EFF.GENTOW2.25/.34/.41/.42 [supplied-by: chapter C] — the theta orientation records; harvest predates spec/EFF-GENTOW2.md'),
 (7,  GENTOW2_EXT, 'contiguous EFF.GENTOW2.42 [supplied-by: chapter C] — gamma-calculus letter-group arena, DECISION D-1 i=2 licence'),
 (9,  GENTOW2_EXT, 'contiguous EFF.GENTOW2.41 [supplied-by: chapter C] — top-slot anchor'),
 (10, GENTOW2_EXT, 'contiguous EFF.GENTOW2.25/.41 [supplied-by: chapter C] — single-argument convention'),
 (42, GENTOW2_EXT, 'contiguous EFF.GENTOW2.43 (B-doubleprime) + .34 (B-prime(3)) [supplied-by: chapter C] — the ABS-G2 port construction'),
 (56, GENTOW2_EXT, 'contiguous EFF.GENTOW2.43/.34 [supplied-by: chapter C] — WF-law_2 unconditional supplier'),
 (61, GENTOW2_EXT, 'contiguous EFF.GENTOW2.34/.43 [supplied-by: chapter C] — i=2 nonvanishing supplier'),
 (27, 'EFF.HETOW.22', 'gov placeholder — (H-HETOW-LOCAL) supplier fields [supplied-by: chapter C]'),
 (43, 'EFF.HETOW.22', 'gov placeholder — ABS-HE4 instantiation data [supplied-by: chapter C]'),
 (53, 'EFF.GENTOW3.18', 'gov placeholder — (FLOOR)=GENTOW-3(i) at the member class + omega computations + S8.1 margin [supplied-by: chapter C]; spans per EFF.T4.21'),
 (54, 'EFF.GENTOW6.12', 'gov placeholder — GT6-CERT-TOP data + R5-63A exposure legs X33-X39 [supplied-by: chapter C]'),
 (44, 'EFF.GENTOW5.s1of2.06', 'gov placeholder — GENTOW5_WI S2 certified package, T3 XREF X18 PERIMETER-UNRESOLVED [supplied-by: chapter C]'),
 (61, 'EFF.GENTOW5.s1of2.06', 'gov placeholder — S11.2 proved fixed-unit list + S11.3 letter-power unit [supplied-by: chapter C]'),
 (64, 'EFF.GENTOW5.s1of2.06', 'gov placeholder — outer psi_1 statement / perimeter resolution [supplied-by: chapter C]'),
]

# --- structural ledger edges ---------------------------------------------------------
hyp = [
 (51,'HYP.113','T4.2(c) full-exposure premise — live conditional-theorem leg, disclosed not discharged'),
 (52,'HYP.114','T4.2(d) provenance-exclusion fence — disclosed not discharged'),
 (55,'HYP.63','W_{<=i} CARRY — carrier declared, never discharged'),
 (61,'HYP.66','WFRAME OPEN-3 avatar fence — recorded'),
 (61,'HYP.99','T5 two-clause staleness — recorded, typed away in D.29, note-owner repair NOT executed'),
 (64,'HYP.39','JD0-BOX-2 routing check: zero T-unit cites, routed to chapter I — disclosure, not discharge'),
]

rows = []
def add(frm, to, ev, res='from:exact,to:exact'):
    rows.append([f'BP.D.{frm:02d}', to, 'stmt-dep', 'D', 'OPEN', 'blueprint', res,
                 'blueprint', f'source=blueprint | CHAP-D NODE D.{frm:02d} {ev}'])

for n in sorted(intra):
    for m in intra[n]:
        ev = 'DEPENDS'
        if (n, m) in intra_note:
            ev += ' [' + intra_note[(n, m)] + ']'
        add(n, f'BP.D.{m:02d}', ev)
for n in sorted(src):
    for t in src[n]:
        add(n, t, 'SOURCE (transcription)')
for n in sorted(bdep):
    for t in bdep[n]:
        add(n, t, 'DEPENDS (chapter-B committed node, GC-13(b))')
for n, t, ev in placeholders:
    res = 'from:exact,to:gov' if not t.startswith('EXT:') else 'from:exact,to:ext'
    add(n, t, f'DEPENDS (GC-13 placeholder): {ev}', res)
for n, t, ev in hyp:
    add(n, t, f'ledger interface: {ev}')

# sanity: all targets exist in DAG_NODES.tsv or are BP.D.* (self-declared)
known = set()
with open('spec/DAG_NODES.tsv') as f:
    for line in f:
        known.add(line.split('\t')[0])
missing = sorted({r[1] for r in rows} - known - {f'BP.D.{i:02d}' for i in range(1,69)})
if missing:
    print('WARNING dangling targets:', missing, file=sys.stderr)

with open('spec/DAG_BLUEPRINT_D.tsv', 'w', newline='') as f:
    w = csv.writer(f, delimiter='\t', lineterminator='\n')
    for r in rows:
        w.writerow(r)
print(f'{len(rows)} rows written; targets: '
      f'{sum(1 for r in rows if r[1].startswith("BP.D"))} intra, '
      f'{sum(1 for r in rows if r[1].startswith("EFF.T"))} EFF.T*, '
      f'{sum(1 for r in rows if r[1].startswith("BP.B"))} BP.B, '
      f'{sum(1 for r in rows if r[1].startswith("EXT:") or r[1].startswith("EFF.GENTOW") or r[1].startswith("EFF.HETOW"))} placeholders, '
      f'{sum(1 for r in rows if r[1].startswith("HYP."))} HYP')
