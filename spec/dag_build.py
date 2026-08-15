#!/usr/bin/env python3
"""PHASE-0c GLOBAL DAG BUILDER (draft) — assembles spec/DAG.tsv, spec/DAG_NODES.tsv and
spec/DAG_NONIMPORTS.tsv from the 0a effective specs, the 0b hypothesis ledger, the
certain-nodes list, and the landed leanfinal declarations.

DISCIPLINE (per the 0c charge): this script ASSEMBLES RECORDED EDGES.  It never infers a
mathematical dependency from prose.  Every edge carries the file + table row it came from
in its EVIDENCE column, and every unresolved endpoint is flagged COARSE rather than
guessed at.  Run from the repo root:  python3 spec/dag_build.py

Outputs (all committed):
  spec/DAG.tsv            edges: from-ID, to-ID, edge-kind, chapter, status, + provenance
  spec/DAG_NODES.tsv      nodes: id, kind, note, unit-type, class, chapter, status
  spec/DAG_NONIMPORTS.tsv recorded negative-import fences (checked by dag_check.py)

BLUEPRINT MERGE (added 2026-08-15, CHAP-G §11 orchestrator item).  The outputs are opened in
'w' mode, so a rebuild used to DISCARD the edge rows a chapter blueprint had appended by hand.
Every `spec/DAG_BLUEPRINT_*.tsv` is now the DURABLE copy of one chapter's edges and is merged
back on EVERY rebuild: harvested rows first, then the blueprint files in filename order and
in-file order, de-duplicated on (from-ID, to-ID).  Their `BP.<CH>.<nn>` endpoints get node rows
whose unit-type is read off the chapter blueprint's own `### NODE <CH>.<nn> [kind]` headings.
"""
import re, os, sys, json, collections

SPEC = 'spec'
LEDGER = 'spec/HYPOTHESIS_LEDGER.md'
CERTAIN = 'spec/CERTAIN_NODES_2026-08-14.md'
LEANDIR = 'leanfinal/Uniformity'

# ---------------------------------------------------------------- canonical spec files
MERGED = ['GENH4','GENHN','GENIND','GRTJB','GRTJC','GRTW2','HE3','HE7','LIFTCORNER','T1','T2']
SINGLES = ['GENTOW1','GENTOW3','GENTOW4','GENTOW6','GRTJA','HE6','HE6R1','HETOW','HEX3',
           'HMENU3','JD0','SIGMALAW','T3','T4','T5','W11','WELDMASTER']
SHARDED = {'GENTOW5': ['EFF-GENTOW5-s1of2.md','EFF-GENTOW5-s2of2.md'],
           'W12':     ['EFF-W12-s1of2.md','EFF-W12-s2of2.md']}
CANON = {n: ['EFF-%s.md' % n] for n in MERGED + SINGLES}
CANON.update(SHARDED)
# shard files of MERGED notes: harvested too (several merges summarise their XREF ledger
# and leave the per-row detail in the shards), with shard-local IDs remapped by the
# merge's own SHARD-MAP.
import glob as _glob
SHARDS_OF = {n: sorted(os.path.basename(p) for p in _glob.glob(os.path.join(SPEC, 'EFF-%s-s*.md' % n)))
             for n in MERGED}

MATH_TYPES = {'theorem','lemma','corollary','proposition','definition','hypothesis',
              'convention','instance-record','absorption-record','non-instance',
              'open-obligation','derivation','hypothesis-box','open-box',
              'lemma-statement','imported','table','battery-frame'}

# --------------------------------------------------------------------- unit inventory
class Unit(object):
    __slots__ = ('id','note','file','typ','line','body','stmt','deriv','cond')

def load_units():
    units, srcfile, filetxt = collections.OrderedDict(), {}, {}
    for note, files in CANON.items():
        for fn in files:
            txt = open(os.path.join(SPEC, fn), encoding='utf-8').read()
            filetxt[fn] = txt
            m = (re.search(r'\*\*Source note:\*\*\s*`([^`]+)`', txt) or
                 re.search(r'`(lean/notes/openmath/[A-Za-z0-9_.\-]+\.md)`', txt))
            if m:
                srcfile[note] = os.path.basename(m.group(1))
            lines = txt.split('\n')
            heads = []
            for i, l in enumerate(lines):
                mm = re.match(r'^### (EFF\.[A-Za-z0-9]+(?:\.s\dof\d)?\.\d+)\s*(?:\[([^\]]*)\])?', l)
                if mm:
                    heads.append((i, mm))
            for k, (i, mm) in enumerate(heads):
                j = heads[k+1][0] if k+1 < len(heads) else len(lines)
                u = Unit()
                u.id, u.note, u.file, u.line = mm.group(1), note, fn, i+1
                u.typ = (mm.group(2) or '?').strip()
                u.body = '\n'.join(lines[i:j])
                sm = re.search(r'\*\*CANONICAL STATEMENT.*?\*\*', u.body)
                dm = re.search(r'\*\*DERIVATION.*?\*\*', u.body)
                cm = re.search(r'\*\*CONDITIONALITY.*?\*\*', u.body)
                rm = re.search(r'\*\*RESOLUTION TRACE.*?\*\*', u.body)
                u.stmt = (u.body[sm.end():dm.start()] if (sm and dm and dm.start() > sm.end())
                          else (u.body[sm.end():] if sm else u.body))
                end = (cm.start() if (cm and dm and cm.start() > dm.start())
                       else (rm.start() if (rm and dm and rm.start() > dm.start()) else len(u.body)))
                u.deriv = u.body[dm.end():end] if dm else ''
                u.cond = (u.body[cm.end():rm.start()] if (cm and rm and rm.start() > cm.start())
                          else (u.body[cm.end():] if cm else ''))
                units[u.id] = u
    return units, srcfile, filetxt

UNITS, SRCFILE, FILETXT = load_units()
NOTE_UNITS = collections.defaultdict(list)
for _u in UNITS.values():
    NOTE_UNITS[_u.note].append(_u)
FILE_BY_NOTE = {v: k for k, v in SRCFILE.items()}

# ------------------------------------------------------- shard-local ID remapping
def shard_map(note):
    """shard index -> additive offset, read off the merge's own SHARD-MAP, plus any
    explicit per-unit mapping rows.  Returns (offsets, explicit)."""
    txt = FILETXT.get('EFF-%s.md' % note, '')
    offsets, explicit = {}, {}
    for m in re.finditer(r'\|\s*`s(\d)of\d`\s*\|[^|]*\|\s*\+?(\d+)\s*\|', txt):
        offsets[int(m.group(1))] = int(m.group(2))
    for m in re.finditer(r'[Ss]hard (\d)(?:\'s offset is|\s+carries a)\s*\*\*\+?(\d+)\*\*', txt):
        offsets.setdefault(int(m.group(1)), int(m.group(2)))
    for m in re.finditer(r'\|\s*(EFF\.%s\.s(\d)of\d\.(\d+))\s*\|\s*(EFF\.%s\.(\d+))\s*\|'
                         % (note, note), txt):
        explicit[m.group(1)] = m.group(4)
    return offsets, explicit
SHARD_OFFSETS = {n: shard_map(n) for n in MERGED}

def remap(note, sid):
    """EFF.<note>.sKofM.NN  ->  merged EFF.<note>.NN'  (or None if unmappable)."""
    offs, expl = SHARD_OFFSETS.get(note, ({}, {}))
    if sid in expl:
        return expl[sid]
    m = re.match(r'EFF\.%s\.s(\d)of\d\.(\d+)$' % re.escape(note), sid)
    if not m:
        return None
    k, nn = int(m.group(1)), int(m.group(2))
    if k not in offs:
        return None
    cand = 'EFF.%s.%02d' % (note, nn + offs[k])
    return cand if cand in UNITS else None

def governing(note):
    """Documented placeholder rule for COARSE targets: the note's first [theorem] unit,
    else its first [lemma], else its first [definition], else unit .01."""
    us = NOTE_UNITS[note]
    for want in ('theorem', 'lemma', 'definition'):
        for u in us:
            if u.typ == want:
                return u.id
    return us[0].id if us else None
GOV = {n: governing(n) for n in CANON}

# ------------------------------------------------ designation -> unit resolution
_DCACHE = {}
JUNK = re.compile(r'[=\[\]{}⟨⟩←→⇒\\$]|^\s*$|^[\d.,%\s/–—-]+$|^[0-9a-f]{7,}$')
def looks_like_designation(d):
    d = d.strip()
    if not d or len(d) > 64 or len(d) < 2:
        return False
    if JUNK.search(d):
        return False
    if d.endswith('.md') or d.startswith('.'):
        return False
    if d.count(' ') > 6:
        return False
    return bool(re.search(r'[A-Za-z]', d))

def resolve_desig(note, desig):
    """(unit_id, how) with how in {stmt, body, gov}.  'stmt' = the designation occurs in
    some unit's CANONICAL STATEMENT (the definition site, by the earliest-math-unit rule);
    'body' = only elsewhere in a unit; 'gov' = unresolved -> the note's governing unit."""
    d = desig.strip().strip('`').strip()
    key = (note, d)
    if key in _DCACHE:
        return _DCACHE[key]
    out = (GOV.get(note), 'gov')
    if d and note in NOTE_UNITS:
        hs, hb = [], []
        for u in NOTE_UNITS[note]:
            if d in u.stmt:
                hs.append(u)
            elif d in u.body:
                hb.append(u)
        def rank(u, txt):
            # the definition site names the object early: in the unit's own ### heading,
            # or near the head of its CANONICAL STATEMENT.  Prefer that over a unit that
            # merely mentions the designation deep in a consumption audit.
            head = u.body.split('\n', 1)[0]
            return (0 if d in head else 1,
                    0 if u.typ in MATH_TYPES else 1,
                    txt(u).find(d))
        if hs:
            out = (min(hs, key=lambda u: rank(u, lambda x: x.stmt)).id, 'stmt')
        elif hb:
            out = (min(hb, key=lambda u: rank(u, lambda x: x.body)).id, 'body')
    _DCACHE[key] = out
    return out

# ------------------------------------------------------------------ section slicing
SEC_EDGE = re.compile(r'(XREF|consumption|supply|consumer edge)', re.I)
SEC_NONIMP = re.compile(r'NON-IMPORT', re.I)
SUB_SKIP = re.compile(r'(md5|artifact|hash|arithmetic|fidelity|near-miss|pin verification|'
                      r'commit pin|freeze|self-audit|open-call)', re.I)

def sections(fn):
    txt = FILETXT[fn]
    marks = [(m.start(), m.group(0)) for m in re.finditer(r'^## .*$', txt, re.M)]
    out = []
    for i, (s, h) in enumerate(marks):
        e = marks[i+1][0] if i + 1 < len(marks) else len(txt)
        out.append((h, txt[s:e]))
    return out

ANYMD = re.compile(r'([A-Za-z0-9_\-./]+\.md)')
UNITREF = re.compile(r'`\.(\d{1,3})`')
FULLID = re.compile(r'\b(EFF\.[A-Za-z0-9]+(?:\.s\dof\d)?\.\d+)\b')
BT = re.compile(r'`([^`]+)`')
HYPREF = re.compile(r'\b(HYP\.\d{1,3})\b')
REVERSE_HINT = re.compile(r'reverse|who consumes|consumer note|consumer file|consumers of|'
                          r'reverse consumer', re.I)

def note_of_file(fname):
    b = os.path.basename(fname)
    if b in FILE_BY_NOTE:
        return FILE_BY_NOTE[b]
    m = re.match(r'EFF-([A-Za-z0-9]+)(?:-s\dof\d)?\.md$', b)   # a 0a spec cited by name
    if m and m.group(1).upper() in CANON:
        return m.group(1).upper()
    stem = b.split('_')[0].upper()
    return stem if stem in CANON else None

# ------------------------------------------------------------------------- edge sink
EDGES = []
def add(frm, to, src, ev, fres, tres, desig='', srcunit=None):
    if not frm or not to or frm == to:
        return
    kind = 'stmt-dep'
    kflag = 'default'
    if srcunit is not None and desig:
        # rule 3: statement reference -> stmt-dep, derivation-only reference -> proof-dep.
        # Try the designation as cited, then with a leading kind-word stripped (sources
        # cite both "LEMMA HE3-1" and "HE3-1" for the same object).
        cands = [desig]
        bare = re.sub(r'^(?:ANNEX-)?(?:LEMMA|THEOREM|COROLLARY|DEFINITION|PROPOSITION|CLAIM|'
                      r'BOX|REMARK)\s+', '', desig).strip()
        if bare and bare != desig:
            cands.append(bare)
        for cd in cands:
            if len(cd) < 3:
                continue
            if cd in srcunit.stmt or cd in srcunit.cond:
                kind, kflag = 'stmt-dep', 'statement-hit'
                break
            if cd in srcunit.deriv:
                kind, kflag = 'proof-dep', 'derivation-hit'
                break
    EDGES.append(dict(frm=frm, to=to, kind=kind, kflag=kflag, src=src,
                      res='from:%s,to:%s' % (fres, tres),
                      ev=re.sub(r'\s+', ' ', ev)[:200]))

# ---------------------------------------------------------- 1. XREF / consumption tables
def load_shard_texts():
    for note, fns in SHARDS_OF.items():
        for fn in fns:
            if fn not in FILETXT:
                FILETXT[fn] = open(os.path.join(SPEC, fn), encoding='utf-8').read()
load_shard_texts()

def harvest_tables():
    plan = [(n, f, None) for n, fs in CANON.items() for f in fs]
    for note, fns in SHARDS_OF.items():
        for fn in fns:
            k = int(re.search(r'-s(\d)of\d\.md$', fn).group(1))
            plan.append((note, fn, k))
    for note, fn, shard in plan:
            def home_id(nn):
                if shard is None:
                    return 'EFF.%s.%s' % (note, nn.zfill(2))
                return remap(note, 'EFF.%s.s%dof%d.%s'
                             % (note, shard, len(SHARDS_OF[note]), nn.zfill(2)))
            for head, body in sections(fn):
                if not SEC_EDGE.search(head):
                    continue
                cur_sub, last_file, colnames = head, None, []
                for ln in body.split('\n'):
                    if ln.startswith('#'):
                        cur_sub, last_file, colnames = ln, None, []
                        continue
                    if not ln.startswith('|') or re.match(r'^\|[\s:\-\|]+\|\s*$', ln):
                        continue
                    if SUB_SKIP.search(cur_sub):
                        continue
                    cells = [c.strip() for c in ln.strip().strip('|').split('|')]
                    low = ' '.join(cells).lower()
                    if ('designation' in low and 'count' in low) or \
                       (len(''.join(cells)) < 170 and 'count' in low and
                            any(k in low for k in ('consumer','supplier','target','file','unit'))):
                        colnames = [c.lower() for c in cells]
                        continue
                    if all(len(c) < 3 for c in cells):
                        continue
                    reverse = bool(REVERSE_HINT.search(cur_sub)) or ('consumer' in ' '.join(colnames))
                    row = ' | '.join(cells)
                    homes = [home_id(n) for n in UNITREF.findall(row)]
                    homes += [remap(note, i) if '.s' in i else i for i in FULLID.findall(row)]
                    homes = [h for h in homes if h and h in UNITS and UNITS[h].note == note]
                    targets = []
                    for m in BT.finditer(row):
                        tok = m.group(1)
                        if '.md:' in tok:
                            f, d = tok.split('.md:', 1)
                            targets.append((note_of_file(f + '.md'), d, f + '.md'))
                        elif tok.endswith('.md'):
                            last_file = tok
                    if not targets:
                        fcell = None
                        for c in cells:
                            mm = ANYMD.search(c)
                            if mm:
                                fcell = mm.group(1)
                                break
                        if fcell is None and last_file:
                            fcell = last_file
                        if fcell is None:
                            for c in cells[:3]:
                                cc = c.strip('*` ').upper()
                                if cc in CANON:
                                    fcell = SRCFILE.get(cc, cc)
                                    break
                        if fcell:
                            last_file = fcell
                            tn = note_of_file(fcell)
                            ds = [t for t in BT.findall(row) if looks_like_designation(t)]
                            if ds:
                                targets += [(tn, d, fcell) for d in ds]
                            elif tn:
                                targets.append((tn, '', fcell))
                    for tn, d, evf in targets:
                        if d and not looks_like_designation(d):
                            continue
                        if tn is None:
                            hy = HYPREF.search(d + ' ' + row) if 'HYPOTHESIS_LEDGER' in evf else None
                            tid = hy.group(1) if hy else 'EXT:' + os.path.basename(evf)
                            how = 'ledger' if hy else 'ext'
                        else:
                            tid, how = resolve_desig(tn, d)
                        if reverse:
                            frm = tid
                            for h in (homes or [GOV[note]]):
                                add(frm, h, 'reverse-xref',
                                    '%s | %s | %s' % (fn, cur_sub.strip('# '), row),
                                    how, 'exact' if homes else 'gov', d, None)
                        else:
                            # a note citing its own row in the hypothesis ledger records
                            # provenance, not a dependency: class it 'ledger-index' and
                            # keep the ledger->unit direction as the dependency edge.
                            cls = 'ledger-index' if tid.startswith('HYP.') else 'xref'
                            for h in (homes or [GOV[note]]):
                                add(h, tid, cls,
                                    '%s | %s | %s' % (fn, cur_sub.strip('# '), row),
                                    'exact' if homes else 'gov', how, d, UNITS.get(h))

# ---------------------------------------- 2. recorded supersession edges (rules 24, 25)
def harvest_supersession():
    for uid, u in UNITS.items():
        for fld in ('TARGETS', 'CHAIN'):
            for m in re.finditer(r'\*\*%s:?\*\*(.{0,700}?)(?:\n\n|\*\*[A-Z])' % fld, u.body, re.S):
                blob = m.group(1)
                for tgt in FULLID.findall(blob):
                    if tgt in UNITS:
                        add(uid, tgt, 'supersession',
                            '%s | %s: %s' % (u.file, fld, re.sub(r'\s+', ' ', blob)[:120]),
                            'exact', 'exact')
                for sm in re.finditer(r'\bs(\d)of(\d)\.?\s*`?\.(\d{1,3})`?', blob):
                    cand = 'EFF.%s.s%sof%s.%s' % (u.note, sm.group(1), sm.group(2), sm.group(3).zfill(2))
                    if cand in UNITS:
                        add(uid, cand, 'supersession',
                            '%s | %s (shard-local)' % (u.file, fld), 'exact', 'exact')

# ------------------------------------------------------- 3. hypothesis-ledger layer
LEDGER_TXT = open(LEDGER, encoding='utf-8').read()

def hyp_rows():
    rows = {}
    lines = LEDGER_TXT.split('\n')
    starts = [(i, re.match(r'^(HYP\.\d{1,3})\s+(.*)$', l)) for i, l in enumerate(lines)]
    starts = [(i, m) for i, m in starts if m]
    for k, (i, m) in enumerate(starts):
        j = starts[k+1][0] if k + 1 < len(starts) else len(lines)
        body = '\n'.join(lines[i:j])
        rows[m.group(1)] = dict(title=m.group(2).strip(), body=body, line=i + 1)
    return rows
HYPS = hyp_rows()

LEAN_DECLS = set()
for root, _, fs in os.walk(LEANDIR):
    if '.lake' in root:
        continue
    for f in fs:
        if f.endswith('.lean'):
            for m in re.finditer(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure|instance)\s+'
                                 r'([A-Za-z_][A-Za-z0-9_.\']*)', open(os.path.join(root, f), encoding='utf-8').read(), re.M):
                LEAN_DECLS.add(m.group(1))

CAPSTONES = ['UniformityStatement', 'UniformityStatementDecided']
LEAN_NODES = set()

def harvest_ledger():
    # 3a. Display A conjuncts -> HYP rows (the capstone's honest conditionality)
    da = LEDGER_TXT.split('### Display A')[1].split('### Display B')[0]
    disp = da.split('⇒')[0]
    body = '\n'.join(re.sub(r'--.*$', '', l) for l in disp.split('\n'))
    body = body[body.find('[') + 1:]
    conj = set()
    for piece in re.split(r'∧', body):
        t = ' '.join(piece.split()).strip(' []')
        t = re.sub(r'^\(|\)$', '', t).strip()
        if 2 <= len(t) <= 60 and re.search(r'[A-Za-z𝒲]', t):
            conj.add(t)
    conj.update(['NS7', 'LB1', 'MP1'])
    for m in HYPREF.findall(disp):
        for cap in CAPSTONES:
            add('CAP:' + cap, m, 'ledger-cond', 'HYPOTHESIS_LEDGER Display A (frozen)',
                'exact', 'exact')
    def offcone(h):
        b = HYPS[h]['body']
        return bool(re.search(r'\*\*(?:DISCHARGED|CLOSED)\b', b) or
                    re.search(r'NOT-REACHED|OUT of the cone|verified UNREACHABLE|'
                              r'OUT-OF-PATH-BY-POLICY', b))
    for t in sorted(conj):
        keys = [t] + re.findall(r'[A-Za-z][A-Za-z0-9\-_.()≥μ]{2,}', t)[:2]
        hits = []
        for k in keys:
            live = [h for h, r in HYPS.items() if not offcone(h)]
            hits = ([h for h in live if k in HYPS[h]['title']] or
                    [h for h in live if k in HYPS[h]['body']])
            if hits:
                break
        if hits:
            for h in hits[:3]:
                for cap in CAPSTONES:
                    add('CAP:' + cap, h, 'ledger-cond',
                        'HYPOTHESIS_LEDGER Display A conjunct %s' % t, 'exact', 'exact')
        else:
            for cap in CAPSTONES:
                add('CAP:' + cap, 'COND:' + t, 'ledger-cond',
                    'HYPOTHESIS_LEDGER Display A conjunct %s (no HYP row matched)' % t,
                    'exact', 'unmatched')
    # 3a'. the ledger's own scope sentence makes every surviving row a capstone-path
    # condition: "surviving conditions on the path from leanfinal's UniformityStatement".
    # Rows the ledger itself stamps CLOSED / DISCHARGED / MERGED / OUT-OF-PATH are not
    # conditions any more and get no capstone edge.
    for h, r in HYPS.items():
        b = r['body']
        closed = re.search(r'\*\*(?:DISCHARGED|CLOSED)\b', b) or \
                 re.search(r'PROPOSED DISPOSITION:\s*\*?\*?(?:MERGED|CLOSED|OUT-OF-PATH)', b)
        # the ledger's own NOT-REACHED / out-of-cone signatures also remove a row from the
        # capstone's cone (weld-face audit COR-WFA-*, ORPHAN-1 COR-ORPH-*)
        offcone = re.search(r'NOT-REACHED|OUT of the cone|verified UNREACHABLE|OUT-OF-PATH-BY-POLICY', b)
        if closed or offcone:
            continue
        for cap in CAPSTONES:
            add('CAP:' + cap, h, 'ledger-path',
                'HYPOTHESIS_LEDGER scope: surviving condition on the capstone path (%s)' % h,
                'exact', 'exact')
    # 3b. each HYP row -> where its obligation lives, and what discharged it
    for h, r in HYPS.items():
        mw = re.search(r'WHERE:\s*(.*)', r['body'])
        where = mw.group(1) if mw else ''
        for fm in ANYMD.finditer(where):
            tn = note_of_file(fm.group(1))
            ds = [d for d in BT.findall(r['title'] + ' ' + where) if looks_like_designation(d)]
            if tn:
                done = False
                for d in ds:
                    tid, how = resolve_desig(tn, d)
                    add(h, tid, 'ledger-loc', 'HYPOTHESIS_LEDGER %s WHERE: %s' % (h, where[:110]),
                        'exact', how)
                    done = True
                if not done:
                    add(h, GOV[tn], 'ledger-loc',
                        'HYPOTHESIS_LEDGER %s WHERE: %s' % (h, where[:110]), 'exact', 'gov')
        for dm in re.finditer(r'\*\*(?:DISCHARGED|CLOSED)[^*]*\*\*:?(.{0,400})', r['body'], re.S):
            for d in BT.findall(dm.group(1)):
                for cand in re.findall(r'[A-Za-z_][A-Za-z0-9_.\']*', d):
                    base = cand.split('.')[-1]
                    if base in LEAN_DECLS or cand in LEAN_DECLS:
                        LEAN_NODES.add(base)
                        add(h, 'lean:' + base, 'ledger-discharge',
                            'HYPOTHESIS_LEDGER %s DISCHARGED stamp' % h, 'exact', 'exact')

# ------------------------------------------------------ 4. certain-nodes DONE layer
def harvest_certain():
    txt = open(CERTAIN, encoding='utf-8').read()
    for m in re.finditer(r'^### (CN-\d\d) \| `([^`]+)`', txt, re.M):
        cn, decl = m.group(1), m.group(2)
        base = decl if decl in LEAN_DECLS else decl.split('.')[-1]
        if base in LEAN_DECLS:
            LEAN_NODES.add(base)
        else:
            base = None
        blk = txt[m.end():m.end() + 2500]
        if base:
            for h in set(HYPREF.findall(blk)):
                add(h, 'lean:' + base, 'cn-discharge',
                    '%s %s -> %s' % (CERTAIN, cn, h), 'exact', 'exact')
    for cap in CAPSTONES:
        if cap in LEAN_DECLS:
            LEAN_NODES.add(cap)

# --------------------------------------------------------- 5. NON-IMPORT fences
NONIMPORTS = []
def harvest_nonimports():
    for note, files in CANON.items():
        for fn in files:
            for head, body in sections(fn):
                if not SEC_NONIMP.search(head):
                    continue
                for ln in body.split('\n'):
                    if not ln.startswith('|') or re.match(r'^\|[\s:\-\|]+\|\s*$', ln):
                        continue
                    cells = [c.strip() for c in ln.strip().strip('|').split('|')]
                    low = ' '.join(cells).lower()
                    if 'fence' in low and ('not' in low or 'material' in low):
                        continue
                    row = ' | '.join(cells)
                    homes = ['EFF.%s.%s' % (note, n.zfill(2)) for n in UNITREF.findall(row)]
                    homes += [i for i in FULLID.findall(row) if i in UNITS]
                    banned = set()
                    for c in cells:
                        neg = re.search(r'\bnot\b|\bno\b|never|exclud|absent|free of', c, re.I)
                        for d in BT.findall(c):
                            if looks_like_designation(d):
                                banned.add(d)
                        if neg:                      # only a cell that states a prohibition
                            for tn in CANON:         # can ban a whole note
                                if re.search(r'\b%s\b' % re.escape(tn), c):
                                    banned.add('NOTE:' + tn)
                    if banned:
                        NONIMPORTS.append(dict(note=note, file=fn,
                                               units=';'.join(sorted(set(homes))) or GOV[note],
                                               banned=';'.join(sorted(banned)),
                                               row=re.sub(r'\s+', ' ', row)[:220]))

# ---------------------------------------------------------------------------- run
harvest_tables()
harvest_supersession()
harvest_ledger()
harvest_certain()
harvest_nonimports()

# --------------------------------------------------------------------- deduplicate
best = {}
RANK = {'exact': 3, 'stmt': 3, 'ledger': 3, 'body': 2, 'ext': 1, 'gov': 0, 'unmatched': 0}
def score(e):
    f, t = e['res'].replace('from:', '').replace('to:', '').split(',')
    return RANK.get(f, 0) + RANK.get(t, 0) + (1 if e['kflag'] != 'default' else 0)
for e in EDGES:
    k = (e['frm'], e['to'])
    if k not in best or score(e) > score(best[k]):
        if k in best and best[k]['kflag'] != 'default' and e['kflag'] == 'default':
            e = dict(e, kind=best[k]['kind'], kflag=best[k]['kflag'])
        best[k] = e
EDGELIST = sorted(best.values(), key=lambda e: (e['frm'], e['to']))

# ------------------------------------------------------------------- node universe
NODES = collections.OrderedDict()
def node(nid, kind, note='', typ='', cls='', st='OPEN', extra=''):
    if nid not in NODES:
        NODES[nid] = dict(id=nid, kind=kind, note=note, typ=typ, cls=cls, status=st,
                          chapter='', extra=extra)
for u in UNITS.values():
    node(u.id, 'eff-unit', u.note, u.typ,
         'math' if u.typ in MATH_TYPES else 'record', 'OPEN',
         '%s:%d' % (u.file, u.line))
for h, r in HYPS.items():
    st = 'OPEN'
    if re.search(r'\*\*(?:DISCHARGED|CLOSED)', r['body']):
        st = 'OPEN-LEDGER-CLOSED'
    node(h, 'hyp', '', '', 'hypothesis', st, '%s:%d' % (LEDGER, r['line']))
for d in sorted(LEAN_NODES):
    node('lean:' + d, 'lean-decl', '', '', 'lean', 'DONE', LEANDIR)
for cap in CAPSTONES:
    node('CAP:' + cap, 'capstone', '', '', 'capstone', 'OPEN',
         'leanfinal/Uniformity/Density/Statement.lean')
def fallback_node(nid):
    k = ('ext' if nid.startswith('EXT:') else
         'cond-unmatched' if nid.startswith('COND:') else
         'lean-decl' if nid.startswith('lean:') else 'unknown')
    node(nid, k, '', '', k, 'DONE' if k == 'lean-decl' else 'OPEN')
for e in EDGELIST:
    for nid in (e['frm'], e['to']):
        if nid not in NODES:
            fallback_node(nid)

# -------------------------------------------------- BLUEPRINT EDGE FILES (durable merge)
# A chapter blueprint writes its own edges into spec/DAG_BLUEPRINT_<CH>.tsv under the same
# 9-column contract.  That file is the durable copy; this merge is what makes it survive a
# rebuild (CHAP-G §11 orchestrator item).  Deterministic by construction: files in sorted
# filename order, rows in file order, first occurrence of an (from,to) pair wins, and the
# harvested rows always come first.
BLUEPRINT_GLOB = 'spec/DAG_BLUEPRINT_*.tsv'
BLUEPRINT_DIR = 'blueprint'
BP_ID = re.compile(r'^BP\.([A-Za-z0-9]+)\.(\d+)$')
EDGE_HEADER = ['from-ID', 'to-ID', 'edge-kind', 'chapter', 'status',
               'edge-class', 'resolution', 'kind-basis', 'evidence']

def merge_blueprints():
    """Rows of every spec/DAG_BLUEPRINT_*.tsv, verbatim, minus any (from,to) pair already
    recorded by the harvest or by an earlier blueprint file."""
    rows, seen = [], {(e['frm'], e['to']) for e in EDGELIST}
    for path in sorted(_glob.glob(BLUEPRINT_GLOB)):
        for ln in open(path, encoding='utf-8').read().split('\n'):
            if not ln.strip():
                continue
            cells = ln.split('\t')
            if cells[0] == EDGE_HEADER[0]:            # tolerate an optional header line
                continue
            if len(cells) != len(EDGE_HEADER):
                sys.stderr.write('WARN %s: skipping %d-column row (contract is %d): %s\n'
                                 % (path, len(cells), len(EDGE_HEADER), ln[:90]))
                continue
            key = (cells[0], cells[1])
            if key in seen:
                continue
            seen.add(key)
            rows.append(cells)
    return rows
BLUEPRINT_EDGES = merge_blueprints()

def blueprint_meta(ch):
    """(unit-type by node ID, source file) for chapter <ch>'s BP nodes, read off the chapter
    blueprint's own '### NODE <CH>.<nn> [kind]' headings.  ('', {}) if the chapter file is
    absent — the row shape stays identical, only the unit-type cell goes empty."""
    hits = sorted(_glob.glob(os.path.join(BLUEPRINT_DIR, 'CHAP-%s_*.md' % ch)))
    if not hits:
        return {}, ''
    txt = open(hits[0], encoding='utf-8').read()
    kinds = {}
    for m in re.finditer(r'^#+\s*NODE\s+%s\.(\d+)\s*\[([A-Za-z][A-Za-z\-]*)\]'
                         % re.escape(ch), txt, re.M):
        kinds['BP.%s.%s' % (ch, m.group(1))] = m.group(2)
    return kinds, hits[0]

# chapters in play: one per spec/DAG_BLUEPRINT_<CH>.tsv, plus any BP.<CH>.* an edge names.
_BPMETA, _BPNODES = {}, set()
for _p in sorted(_glob.glob(BLUEPRINT_GLOB)):
    _m = re.match(r'DAG_BLUEPRINT_([A-Za-z0-9]+)\.tsv$', os.path.basename(_p))
    if _m:
        _BPMETA.setdefault(_m.group(1), blueprint_meta(_m.group(1)))
for _cells in BLUEPRINT_EDGES:
    for _nid in (_cells[0], _cells[1]):
        _m = BP_ID.match(_nid)
        if _m:
            _BPNODES.add(_nid)
            _BPMETA.setdefault(_m.group(1), blueprint_meta(_m.group(1)))
# a chapter may declare a node that carries no edge at all (chapter G's G.78 gate is one);
# the blueprint's own NODE headings are the node list, the edge file only the edge list.
for _ch, (_kinds, _src) in _BPMETA.items():
    _BPNODES.update(_kinds)

# BLUEPRINT NODE STATUS (added 2026-08-15, chapter-G closing tail).  A blueprint node's status
# is READ OFF ITS OWN EDGE ROWS in spec/DAG_BLUEPRINT_<CH>.tsv rather than hardcoded OPEN: the
# node is DONE exactly when every one of its outgoing (consumer-side) rows is marked DONE, i.e.
# when the chapter records every dependency of that node as discharged.  A node the chapter
# declares but gives no edge (G.78, the axiom-footprint census gate) has no row to read, so it
# is listed explicitly below.  Deterministic and idempotent, like the merge itself.
BLUEPRINT_EDGELESS_DONE = {'BP.G.78'}
_BP_OUT = collections.defaultdict(list)
for _cells in BLUEPRINT_EDGES:
    if BP_ID.match(_cells[0]):
        _BP_OUT[_cells[0]].append(_cells[4])

def bp_status(nid):
    rows = _BP_OUT.get(nid)
    if not rows:
        return 'DONE' if nid in BLUEPRINT_EDGELESS_DONE else 'OPEN'
    return 'DONE' if all(s == 'DONE' for s in rows) else 'OPEN'

for _nid in sorted(_BPNODES, key=lambda x: (BP_ID.match(x).group(1), int(BP_ID.match(x).group(2)))):
    _ch = BP_ID.match(_nid).group(1)
    _kinds, _src = _BPMETA[_ch]
    node(_nid, 'blueprint-node', 'CHAP-%s' % _ch, _kinds.get(_nid, ''), 'blueprint',
         bp_status(_nid), _src)
for _cells in BLUEPRINT_EDGES:                 # blueprint endpoints outside the harvest
    for _nid in (_cells[0], _cells[1]):
        if _nid not in NODES:
            fallback_node(_nid)

# ------------------------------------------------------------------ THE CHAPTER CUT
# Read off the computed condensation, not off the v1 B-J design cut (which the 0c charge
# records as known non-topological).  Method and residue: spec/DAG_README.md, and
# check [5] of spec/dag_check.py.  Consumer-first order: I > E > D > C > B > H > F > G > A.
CHAPTER_OF_NOTE = {
    'HE3': 'B', 'HE6': 'B', 'HE6R1': 'B', 'HE7': 'B',
    'GENTOW1': 'C', 'GENTOW3': 'C', 'GENTOW4': 'C', 'GENTOW5': 'C', 'GENTOW6': 'C', 'HETOW': 'C',
    'T1': 'D', 'T3': 'D', 'T4': 'D', 'T5': 'D',
    'T2': 'E',
    'GRTJA': 'F', 'GRTJB': 'F', 'GRTJC': 'F', 'GRTW2': 'F',
    'WELDMASTER': 'F', 'LIFTCORNER': 'F', 'SIGMALAW': 'F',
    'HMENU3': 'G', 'HEX3': 'G', 'W11': 'G', 'JD0': 'G',
    'GENIND': 'H', 'GENHN': 'H', 'GENH4': 'H', 'W12': 'H',
}
def chapter_of(n):
    if n['kind'] == 'eff-unit':
        return CHAPTER_OF_NOTE.get(n['note'], '')
    if n['kind'] == 'blueprint-node':
        m = BP_ID.match(n['id'])          # BP.<CH>.<nn> carries its chapter in its ID
        return m.group(1) if m else ''
    if n['kind'] == 'lean-decl':
        return 'A'
    if n['kind'] in ('capstone', 'hyp', 'cond-unmatched'):
        return 'I'
    return ''          # EXT nodes are outside the cut, by construction
for _n in NODES.values():
    _n['chapter'] = chapter_of(_n)

if __name__ == '__main__':
    with open('spec/DAG.tsv', 'w', encoding='utf-8') as fh:
        fh.write('\t'.join(EDGE_HEADER) + '\n')
        for e in EDGELIST:
            ch = NODES[e['frm']]['chapter']
            st = 'DONE' if NODES[e['to']]['status'] == 'DONE' and NODES[e['frm']]['status'] == 'DONE' else 'OPEN'
            fh.write('\t'.join([e['frm'], e['to'], e['kind'], ch, st, e['src'],
                                e['res'], e['kflag'], e['ev']]) + '\n')
        for cells in BLUEPRINT_EDGES:      # durable blueprint rows, verbatim, after the harvest
            fh.write('\t'.join(cells) + '\n')
    with open('spec/DAG_NODES.tsv', 'w', encoding='utf-8') as fh:
        fh.write('id\tnode-kind\tnote\tunit-type\tclass\tchapter\tstatus\tsource\n')
        for n in NODES.values():
            fh.write('\t'.join([n['id'], n['kind'], n['note'], n['typ'], n['cls'],
                                n['chapter'], n['status'], n['extra']]) + '\n')
    with open('spec/DAG_NONIMPORTS.tsv', 'w', encoding='utf-8') as fh:
        fh.write('note\tspec-file\tfenced-units\tbanned-designations-or-notes\trecorded-row\n')
        for r in NONIMPORTS:
            fh.write('\t'.join([r['note'], r['file'], r['units'], r['banned'], r['row']]) + '\n')
    print('nodes %d  edges %d (harvested %d + blueprint %d from %d file(s))  '
          'non-import fences %d'
          % (len(NODES), len(EDGELIST) + len(BLUEPRINT_EDGES), len(EDGELIST),
             len(BLUEPRINT_EDGES), len(sorted(_glob.glob(BLUEPRINT_GLOB))), len(NONIMPORTS)))
