#!/usr/bin/env python3
"""k2close_enum.py — K2-CLOSE unit B, leg 1a: the glued-system SHAPE enumeration
at g0 = 2 (machine enumeration only; the case ANALYSIS is a later unit).

Sources (authority): SURVK2_PROOF_2026-08-08.md at a8914944 — Lemma K2-L3 (the
complete legal-drain inventory at g0 = 2), K2-L1/L2 (window normal form, budget
n <= 2g0-1 = 3), K2-L6 (nu = t - M constant per fiber), K2-L7 (fibers = complete
legal chains, shared-arrival model = the K2-FIB in-vivo battery, 0 violations
on all 332 rows INCLUDING the glued ones), the (K2-RES)(a) box (glue = level-0
dump variants: books differing by e0*delta at level 0 against level-0 mass
delta).  Realized data for the cross-check: survk2_instrument_results.json
grprec (md5-pinned) + qdrows (e0), tied to survk2_derive_checks_results.json
counters and the PE1 duplicate-book census.

WHAT IS ENUMERATED.  A glued system = one bottom-line group holding r >= 2
fibers (fiber key = (interior book, promotion totals)); the fibers are level-0
dump VARIANTS of one interior correction (the (K2-RES)(a) mechanism).  A SHAPE
is the finite combinatorial type of such a group after the S6 normalization
extended group-wise: strip the level-0 multiset common to ALL cells, rebase
seeds at the group minimum, read up to GLOBAL sign.  Shape datum per fiber:
the multiset of (dt, K-hat, sign) cells WITH placement multiplicity, plus the
fiber's mass offset delta_f = nu-hat_f - min nu-hat (K2-L6 invariant).  Group
datum: size n, fiber count r, sign vector, duplicate-book flag, PARITY of n.

THE CHAIN MODEL (= K2-L7 / K2-FIB's rec_chain, abstracted).  A fiber's cells
are all legal drain assignments over its window chain at shared arrivals:
  windows = [root-carry c_init] -> seed window and dump window in either
  order (the root window never fires at g0 = 2: sigma1 <= 2(e0-1) < P0, K2-L2);
  arrivals in UNITS (n = j0 div e0; PE1's raw-j0 double-enumerator certified
  the unit abstraction at every sub-e0 residue);
  drains per window from the K2-L3 inventory (self-tested below against the
  displayed 8-row table; unique legal order per (K, p) per budget);
  the parked remainder (< 2 units, K2-L1(a)) carries to the next window;
  cells keyed (t, K-total); multiplicity = # per-window (K_w, p_w) placements
  (correction-placement AND promotion-placement duplicates both count — the
  K2-L3(i) bracket witness and the S7(e) shape respectively).

ENUMERATION BUDGET (each cap derived or declared, displayed):
  B1 window budget n <= 3            [K2-L2, proved]
  B2 arrival units a in {0,1,2}      [derived: reduced dumps/D-cells <= P0
                                      raw => <= 2 units; seed slice a_s+t <= 2]
  B3 root carry c_init in {0,1}      [derived: sigma1 < P0 => <= 1 unit]
  B4 windows per chain W <= 2 (+root carry) = ONE dumping interior correction
                                     [DECLARED: all realized glued books have
                                      |I| = 1; >= 2 dumping corrections is the
                                      beyond-budget stratum, listed as such]
  B5 fibers per glue family r <= 3   [derived from B4: dump arrival units
                                      a_d in {0,1,2} => <= 3 distinct variants]
  B6 promo total p <= 2              [derived: 2p <= max unit supply 5]
  B7 seeds t in {0,1}, avail T in {{0},{0,1}}  [g0 = 2; {1}-only == {0}-only
                                      shifted, absorbed by a_s range]
  B8 availability A = {0,1} main table [(R2)/K2-L8]; A = {0} annex (the odd-
     characteristic corner) enumerated separately.

LAWS (LAW-KEYED cross-check battery, run with --xcheck):
  GLUE-COVER  every realized glued beta_min bottom group normalizes into the
              enumerated table (exact shape-key match).
  GLUE-EDGE   realized glued books are level-0 dump variants: identical
              (i, k, dj0) edge multisets, level-0 dump offset = e0 * d(nu-hat),
              larger dump <-> larger nu-hat.
  GLUE-SGN    every realized cell has sgn = (-1)^(|K| + |I|) (K2-L4 shadow).
  GLUE-NU     nu-hat constant per realized fiber (K2-L6 shadow).
  GLUE-CENSUS rows/groups/towers == the committed census (29 / 38 / 14+14+1);
              derive-checks counters glued_groups = 38, nonreg_rows = 29.
  GLUE-DUP    realized duplicate-book fibers == the PE1 probe-E census (1
              fiber, 2 same-sign cells, SDW4G2F[2635,2635] slot (4,0,0,0));
              its group matches a dup-flagged enumerated shape.
  CTRL-MUT    mutation controls with teeth: 5 genres x all realized glued
              groups; every mutant must FAIL to match its assigned shape.

PREDICTIONS (sealed at commit 1, BEFORE the battery): P1 GLUE-COVER 38/38;
P2 GLUE-EDGE 38/38; P3 GLUE-CENSUS exact; P4 GLUE-DUP exact (1 fiber, odd
group); P5 the parity datum as computed by the enumerator at commit 1 (see
the table's PARITY section — whatever it prints is the sealed claim);
P6 CTRL-MUT 5 x 38 = 190/190 catches.

DISCLOSURE: the composer read grprec/qdrows during DESIGN (record formats,
book encoding, e0) — disclosed; the enumeration itself consumes only the
K2-L3 inventory + the displayed budget caps, never the realized rows.

Usage: python3 k2close_enum.py --enum   (commit-1 artifact: the shape table)
       python3 k2close_enum.py --xcheck (commit-2 artifact: the verdict)
"""
import sys, os, json, time, hashlib, collections, itertools, ast

HERE = os.path.dirname(os.path.abspath(__file__))
TABLE_MD = os.path.join(HERE, "k2close_shape_table.md")
RESULTS = os.path.join(HERE, "k2close_enum_results.json")

PINS = {
    "survk2_instrument_results.json":   "1ac516df8292ac5d57a88e430de3d1e4",
    "survk2_derive_checks_results.json": "6d1e5987bfd58737366f311245046d6c",
    "survk2_pe1_ext_results.json":      "20843c595c1cb5f9633cfb9dc82b343c",
}

VIOL = []
def viol(fam, msg):
    VIOL.append((fam, msg)); print(f"VIOLATION [{fam}] {msg}")

def md5(path):
    return hashlib.md5(open(path, "rb").read()).hexdigest()

# ---------- Part 0: the K2-L3 drain inventory (independent) + self-test ------
# Events at unit budget u >= 2 (= j0 >= P0 at g0 = 2): C0 consumes 2 units,
# C1 consumes 1, promotion consumes 2.  A drain is COMPLETE (runs until u < 2,
# K2-L1(a)).  Junk-free (no Y-variants).  avail = available level-0 digit
# indices (K2-L8: 0 always in A; main table A = {0,1}, annex A = {0}).
def complete_drains(n, avail, pmax):
    """All complete drains from opening budget n.  Returns dict
    (K_multiset, p, rem) -> number of legal event orders."""
    out = collections.Counter()
    def rec(u, K, p):
        if u < 2:
            out[(tuple(sorted(K)), p, u)] += 1
            return
        for k in sorted(avail):
            rec(u - (2 - k), K + [k], p)
        if p < pmax:
            rec(u - 2, K, p + 1)
    rec(n, [], 0)
    return out

def selftest_inventory():
    """The K2-L3 display, re-derived: 8 drain rows at A = {0,1}, unique legal
    order per (K, p) per budget, the (units 2, p 0) exchange at n = 3 the
    unique multi-member class."""
    A = {0, 1}
    inv2 = complete_drains(2, A, 2)
    inv3 = complete_drains(3, A, 2)
    want2 = {((1,), 0, 1), ((0,), 0, 0), ((), 1, 0)}
    want3 = {((1, 1), 0, 1), ((0,), 0, 1), ((), 1, 1),
             ((0, 1), 0, 0), ((1,), 1, 0)}
    assert set(inv2) == want2, f"n=2 inventory mismatch: {set(inv2)}"
    assert set(inv3) == want3, f"n=3 inventory mismatch: {set(inv3)}"
    assert all(v == 1 for v in inv2.values()), "n=2 order-multiplicity"
    assert all(v == 1 for v in inv3.values()), "n=3 order-multiplicity"
    for n in (0, 1):
        inv = complete_drains(n, A, 2)
        assert set(inv) == {((), 0, n)}, f"n={n} should be drainless"
    # the unique in-window branch: classes by (units consumed, p)
    cls = collections.defaultdict(list)
    for (K, p, rem) in inv3:
        cls[(3 - rem, p)].append(K)
    multi = {c: Ks for c, Ks in cls.items() if len(Ks) > 1}
    assert multi == {(2, 0): [(1, 1), (0,)]} or \
        multi == {(2, 0): [(0,), (1, 1)]}, f"exchange class wrong: {multi}"
    print("SELFTEST inventory: the K2-L3 8-row display re-derived exactly; "
          "unique legal order per (K,p); unique exchange class (n=3,u=2,p=0)")

# ---------- Part 1: fiber chains and glued-system shapes ----------------------
def mass(K):
    return sum(2 - k for k in K)

def fiber_cells(c_init, order, a_s0, p, r0, T, a_d, avail):
    """Complete chain over the window profile: root carry c_init, then the
    seed and dump windows in `order` ('SD' seed-first / 'DS' dump-first),
    unit arrivals a_s0 (+t) and a_d; promo total p, final remainder r0,
    seeds T.  Returns dict (t, K_total) -> placement multiplicity."""
    cells = collections.Counter()
    for t in sorted(T):
        a_s = a_s0 + t
        if a_s > 2:            # B2: reduced D-cells => seed arrival <= 2 units
            continue
        arrivals = [a_d, a_s] if order == 'DS' else [a_s, a_d]
        def rec(ix, carry, Kacc, pacc, placement):
            if ix == len(arrivals):
                if pacc == p and carry == r0:
                    cells[(t, tuple(sorted(Kacc)), placement)] += 1
                return
            n = carry + arrivals[ix]
            assert n <= 3, f"budget breach n={n} (B1/K2-L2)"
            for (Kw, pw, rem), norder in \
                    complete_drains(n, avail, p - pacc).items():
                assert norder == 1, "order-multiplicity inside a window"
                rec(ix + 1, rem, Kacc + list(Kw), pacc + pw,
                    placement + ((Kw, pw),))
        rec(0, c_init, [], 0, ())
    agg = collections.Counter()
    for (t, K, placement) in cells:
        agg[(t, K)] += 1
    return agg

def normalize_group(fibers):
    """fibers: list of dicts (t, K_tuple, sgn) -> mult.  Returns the canonical
    shape key: strip the group-common level-0 multiset, rebase t at the group
    min, per fiber sort cells and compute the nu-hat offset (K2-L6), sort
    fibers, quotient by GLOBAL sign.  Raises AssertionError if nu-hat is not
    fiber-constant (structure breach)."""
    allcells = [c for f in fibers for c in f]
    common = None
    for (t, K, s) in allcells:
        c = collections.Counter(K)
        common = c if common is None else (common & c)
    tmin = min(t for (t, K, s) in allcells)
    def build(flip):
        fkeys = []
        nus = []
        items_all = []
        for f in fibers:
            items = tuple(sorted(
                ((t - tmin, tuple(sorted((collections.Counter(K) - common)
                                         .elements())),
                  (-s if flip else s)), m)
                for (t, K, s), m in f.items()))
            nuset = {mass(Kh) - dt for ((dt, Kh, s), m) in items}
            assert len(nuset) == 1, f"nu-hat not fiber-constant: {items}"
            nus.append(nuset.pop())
            items_all.append(items)
        numin = min(nus)
        for items, nu in zip(items_all, nus):
            fkeys.append((items, nu - numin))
        return tuple(sorted(fkeys))
    return min(build(False), build(True))

def shape_attrs(key):
    """Derived attributes of a normalized shape key."""
    n = sum(m for (items, d) in key for (cell, m) in items)
    r = len(key)
    signs = sorted(s for (items, d) in key
                   for ((dt, K, s), m) in items for _ in range(m))
    dup = any(m >= 2 for (items, d) in key for (cell, m) in items)
    deltas = tuple(d for (items, d) in key)
    return dict(n=n, r=r, parity=("odd" if n % 2 else "even"),
                signs=signs, dup=dup, deltas=deltas)

def enumerate_shapes(avail, tag):
    """The full enumeration under the B1-B8 budget for availability `avail`.
    Returns dict shape_key -> dict(attrs + witness contexts)."""
    shapes = {}
    n_systems = 0
    for c_init, order, a_s0, p, r0 in itertools.product(
            (0, 1), ('DS', 'SD'), (0, 1, 2), (0, 1, 2), (0, 1)):
        for T in ((0,), (0, 1)):
            fibs = {}
            for a_d in (0, 1, 2):
                f = fiber_cells(c_init, order, a_s0, p, r0, set(T), a_d,
                                avail)
                if f:
                    fibs[a_d] = f
            for rsz in (2, 3):
                for S in itertools.combinations(sorted(fibs), rsz):
                    group = []
                    for a in S:
                        group.append({(t, K, (-1) ** len(K)): m
                                      for (t, K), m in fibs[a].items()})
                    key = normalize_group(group)
                    n_systems += 1
                    ctx = (c_init, order, a_s0, p, r0, T, S)
                    if key not in shapes:
                        shapes[key] = dict(shape_attrs(key), witness=[ctx])
                    elif len(shapes[key]["witness"]) < 2:
                        shapes[key]["witness"].append(ctx)
    print(f"ENUM[{tag}]: {n_systems} raw glued systems -> "
          f"{len(shapes)} distinct shapes")
    return shapes

def sorted_ids(shapes, prefix):
    """Stable IDs: sort keys by (n, r, repr)."""
    order = sorted(shapes, key=lambda k: (shapes[k]["n"], shapes[k]["r"],
                                          repr(k)))
    return {k: f"{prefix}-{i+1:02d}" for i, k in enumerate(order)}, order

# ---------- Part 2: the shape table (commit-1 artifact) -----------------------
def fmt_cell(cell, m):
    (dt, K, s) = cell
    ks = "{" + ",".join(str(k) for k in K) + "}"
    return f"(dt={dt},K={ks},{'+' if s > 0 else '-'})" + \
        (f"x{m}" if m > 1 else "")

def fmt_key(key):
    parts = []
    for (items, d) in key:
        cells = " ".join(fmt_cell(c, m) for (c, m) in items)
        parts.append(f"[d={d}| {cells}]")
    return "  ".join(parts)

def write_table():
    selftest_inventory()
    main = enumerate_shapes({0, 1}, "A={0,1}")
    annex = enumerate_shapes({0}, "A={0}")
    ids_m, order_m = sorted_ids(main, "GS")
    ids_a, order_a = sorted_ids(annex, "AS")
    dup_par = collections.Counter(
        (main[k]["dup"], main[k]["parity"]) for k in main)
    dup_shapes = [ids_m[k] for k in order_m if main[k]["dup"]]
    dup_even = [ids_m[k] for k in order_m
                if main[k]["dup"] and main[k]["parity"] == "even"]
    dup_odd = [ids_m[k] for k in order_m
               if main[k]["dup"] and main[k]["parity"] == "odd"]
    L = []
    A = L.append
    A("# k2close_shape_table.md — glued-system shapes at g0 = 2 "
      "(MACHINE-GENERATED)")
    A("")
    A("Generated by `k2close_enum.py --enum` (K2-CLOSE unit B leg 1a). "
      "DO NOT EDIT BY HAND.")
    A("Sources, chain model, budget caps B1-B8, laws, and the sealed "
      "predictions P1-P6: the runner's docstring (authoritative copy).")
    A("Shape key notation: one `[d=..| ...]` block per fiber; `d` = the "
      "fiber's level-0 mass offset delta (nu-hat difference, K2-L6); each "
      "cell `(dt,K,s)xm` = seed offset, stripped level-0 multiset, sign, "
      "placement multiplicity m (m >= 2 = a DUPLICATE BOOK inside the "
      "fiber).  Keys are canonical up to GLOBAL sign.")
    A("")
    A(f"## Main table: A = {{0,1}} — {len(main)} shapes")
    A("")
    A("| ID | n | r | parity | dup | signs | shape key |")
    A("|---|---|---|---|---|---|---|")
    for k in order_m:
        at = main[k]
        A(f"| {ids_m[k]} | {at['n']} | {at['r']} | {at['parity']} | "
          f"{'DUP' if at['dup'] else '-'} | "
          f"{''.join('+' if s > 0 else '-' for s in at['signs'])} | "
          f"`{fmt_key(k)}` |")
    A("")
    A(f"## Annex: A = {{0}} (the odd-characteristic corner) — "
      f"{len(annex)} shapes")
    A("")
    A("| ID | n | r | parity | dup | signs | shape key |")
    A("|---|---|---|---|---|---|---|")
    for k in order_a:
        at = annex[k]
        A(f"| {ids_a[k]} | {at['n']} | {at['r']} | {at['parity']} | "
          f"{'DUP' if at['dup'] else '-'} | "
          f"{''.join('+' if s > 0 else '-' for s in at['signs'])} | "
          f"`{fmt_key(k)}` |")
    A("")
    A("## PARITY (the sealed P5 datum, computed from the enumeration alone)")
    A("")
    A(f"- (dup, parity) census over the main table: "
      f"{ {f'{d}/{p}': c for (d, p), c in sorted(dup_par.items())} }")
    A(f"- shapes carrying a duplicate-book fiber: {len(dup_shapes)} "
      f"({', '.join(dup_shapes)})")
    if dup_even:
        A(f"- ODD GROUP SIZE IS **NOT** FORCED for duplicate-book shapes: "
          f"even-n dup shapes exist in-budget: {', '.join(dup_even)}.")
        A(f"  (odd-n dup shapes: {', '.join(dup_odd)}.)  The realized "
          f"dup fiber's odd-group placement is therefore INSTANCE "
          f"SELECTION, not an enumeration law — the case-analysis unit "
          f"must treat even dup groups as live shapes.")
    else:
        A("- ODD GROUP SIZE **IS** FORCED for duplicate-book shapes in "
          "this budget: every dup-flagged shape has odd n.")
    A("")
    A("## Beyond-budget strata (listed, NOT enumerated)")
    A("")
    A("- >= 2 dumping interior corrections (W >= 3 windows): cap B4.")
    A("- g0 >= 3 (budget n <= 5, the S7(d) candidates): out of scope.")
    A("- Y-carrying / junk continuations: excluded by (R0)/K2-L5(a) at "
      "beta_min as consumed by the note.")
    A("")
    A("## Coverage verdict")
    A("")
    A("PENDING — appended by `k2close_enum.py --xcheck` (commit 2).")
    A("")
    open(TABLE_MD, "w").write("\n".join(L) + "\n")
    print(f"WROTE {TABLE_MD}: {len(main)} main + {len(annex)} annex shapes")
    return main, annex, ids_m, ids_a

# ---------- Part 3: the LAW-KEYED cross-check battery (commit-2) --------------
def parse_cell(c):
    K = tuple(sorted(int(e[1]) for e in c['ce'] if e[0] == '0'))
    book = tuple(sorted((int(e[0]), int(e[1]), ast.literal_eval(e[2]),
                         int(e[3])) for e in c['ce'] if e[0] != '0'))
    return (c['t'], K, c['sgn']), book

def load_realized():
    """Extract the realized glued beta_min bottom groups from the pinned
    grprec.  Returns list of dicts."""
    for f, want in PINS.items():
        got = md5(os.path.join(HERE, f))
        if got != want:
            viol("PIN", f"{f}: {got} != {want}")
    inst = json.load(open(os.path.join(HERE,
                                       "survk2_instrument_results.json")))
    e0map = {(r['tower'], tuple(r['key'])): r['e0'] for r in inst['qdrows']}
    out, seen = [], set()
    for rec in inst['grprec']:
        fibers = collections.defaultdict(collections.Counter)
        for c in rec['cells']:
            cell, book = parse_cell(c)
            fibers[book][cell] += 1
            if c['sgn'] != (-1) ** (len(cell[1]) + len(book)):
                viol("GLUE-SGN", f"{rec['tower']}{rec['key']} "
                     f"slot {rec['slot']}: sgn law fails at {cell}")
        if len(fibers) < 2:
            continue
        gid = (rec['tower'], tuple(rec['key']), tuple(rec['slot']))
        assert gid not in seen, f"duplicate group record {gid}"
        seen.add(gid)
        out.append(dict(gid=gid, tower=rec['tower'],
                        e0=e0map[(rec['tower'], tuple(rec['key']))],
                        n=rec['n'], signed=rec['signed'],
                        fibers=dict(fibers)))
    return out

def glue_edge_law(g):
    """GLUE-EDGE + GLUE-NU on one realized group."""
    ok = True
    nus, lvl0s, skel = [], [], []
    for book, f in sorted(g['fibers'].items()):
        nuset = {mass(K) - t for (t, K, s) in f}
        if len(nuset) != 1:
            viol("GLUE-NU", f"{g['gid']}: nu-hat not constant in book "
                 f"{book}")
            return False
        nus.append(nuset.pop())
        lvl0s.append(sum((e[2][0] if len(e[2]) else 0) for e in book))
        skel.append(tuple((e[0], e[1], e[3]) for e in book))
    if len(set(skel)) != 1:
        viol("GLUE-EDGE", f"{g['gid']}: books differ beyond dump vectors: "
             f"{skel}"); ok = False
    for i in range(1, len(nus)):
        if lvl0s[i] - lvl0s[0] != g['e0'] * (nus[i] - nus[0]):
            viol("GLUE-EDGE", f"{g['gid']}: dump offset "
                 f"{lvl0s[i] - lvl0s[0]} != e0*d(nu) = "
                 f"{g['e0']} * {nus[i] - nus[0]}"); ok = False
    return ok

def mutants(fibers):
    """The five CTRL-MUT genres on a realized group (list-of-dicts form)."""
    fl = [dict(f) for f in fibers]
    b0 = sorted(fl[0])
    c0 = b0[0]
    m = []
    f = [dict(x) for x in fl]                      # MUT-SGN
    f[0].pop(c0); f[0][(c0[0], c0[1], -c0[2])] = 1
    m.append(("MUT-SGN", f))
    f = [dict(x) for x in fl]                      # MUT-K
    f[0].pop(c0); f[0][(c0[0], tuple(sorted(c0[1] + (1,))), c0[2])] = 1
    m.append(("MUT-K", f))
    f = [dict(x) for x in fl]                      # MUT-DROP
    if f[0][c0] > 1: f[0][c0] -= 1
    else: f[0].pop(c0)
    m.append(("MUT-DROP", [x for x in f if x]))
    f = [dict(x) for x in fl]                      # MUT-MERGE
    f[0].pop(c0)
    f[1][c0] = f[1].get(c0, 0) + 1
    m.append(("MUT-MERGE", [x for x in f if x]))
    f = [dict(x) for x in fl]                      # MUT-DUP
    f[0][c0] += 1
    m.append(("MUT-DUP", f))
    return m

def xcheck():
    t0 = time.time()
    sealed = open(TABLE_MD).read()
    main, annex, ids_m, ids_a = write_table()
    if open(TABLE_MD).read() != sealed:
        viol("SEAL", "regenerated table differs from the committed one")
    realized = load_realized()
    # GLUE-CENSUS
    rows = collections.Counter()
    for g in realized: rows[(g['tower'], g['gid'][1])] = 1
    trows = collections.Counter(t for (t, k) in rows)
    if len(realized) != 38 or sum(rows.values()) != 29 or \
       dict(trows) != {"SDG2BF": 14, "SDG2BZ": 14, "SDW4G2F": 1}:
        viol("GLUE-CENSUS", f"groups {len(realized)}, rows "
             f"{sum(rows.values())}, towers {dict(trows)}")
    dc = json.load(open(os.path.join(
        HERE, "survk2_derive_checks_results.json")))
    if dc['counters'].get('glued_groups') != 38 or \
       dc['counters'].get('nonreg_rows') != 29:
        viol("GLUE-CENSUS", f"derive-checks counters disagree: "
             f"{dc['counters']}")
    pe1 = json.load(open(os.path.join(HERE, "survk2_pe1_ext_results.json")))
    if not any("duplicate-book fibers on the full traced roster: 1" in s
               for s in pe1['findings']):
        viol("GLUE-CENSUS", "PE1 probe-E census string not found")
    # GLUE-EDGE / GLUE-NU / GLUE-COVER
    matches, unmatched = collections.Counter(), []
    assign = {}
    for g in realized:
        glue_edge_law(g)
        try:
            key = normalize_group(list(g['fibers'].values()))
        except AssertionError as e:
            viol("GLUE-COVER", f"{g['gid']}: normalization breach: {e}")
            continue
        if key in ids_m:
            matches[ids_m[key]] += 1
            assign[g['gid']] = (ids_m[key], key)
        else:
            unmatched.append(g['gid'])
            viol("GLUE-COVER", f"{g['gid']}: no enumerated shape matches "
                 f"{fmt_key(key)}")
    # GLUE-DUP
    dups = []
    for g in realized:
        for book, f in g['fibers'].items():
            for cell, mlt in f.items():
                if mlt >= 2:
                    dups.append((g, cell, mlt))
    dup_rep = []
    if len(dups) != 1:
        viol("GLUE-DUP", f"{len(dups)} duplicate-book fibers, expected 1")
    for (g, cell, mlt) in dups:
        sid = assign.get(g['gid'], ("?",))[0]
        flag = sid != "?" and main[assign[g['gid']][1]]['dup']
        par = "odd" if g['n'] % 2 else "even"
        if not flag:
            viol("GLUE-DUP", f"{g['gid']}: dup fiber but shape {sid} "
                 f"not dup-flagged")
        if g['gid'] != ("SDW4G2F", (2635, 2635), (4, 0, 0, 0)) or \
           mlt != 2 or cell[2] != -1:
            viol("GLUE-DUP", f"unexpected dup witness {g['gid']} {cell}")
        dup_rep.append(dict(gid=list(map(list, g['gid'][1:2])) and
                            [g['gid'][0], list(g['gid'][1]),
                             list(g['gid'][2])],
                            shape=sid, mult=mlt, group_n=g['n'],
                            group_parity=par, cell_sign=cell[2]))
    # CTRL-MUT
    mut_stats = collections.Counter()
    for g in realized:
        if g['gid'] not in assign: continue
        _, key0 = assign[g['gid']]
        for genre, fl in mutants(list(g['fibers'].values())):
            caught, why = False, ""
            if len(fl) < 2:
                caught, why = True, "not glued"
            else:
                try:
                    km = normalize_group(fl)
                    if km != key0:
                        caught = True
                        why = ("no shape" if km not in ids_m
                               else f"other shape {ids_m[km]}")
                except AssertionError:
                    caught, why = True, "structure breach"
            mut_stats[(genre, caught)] += 1
            if not caught:
                viol("CTRL-MUT", f"{g['gid']} {genre}: mutant still "
                     f"matches its shape — NO TEETH")
    return dict(main=main, annex=annex, ids_m=ids_m, ids_a=ids_a,
                realized=realized, matches=matches, unmatched=unmatched,
                assign=assign, dup_rep=dup_rep, mut_stats=mut_stats,
                trows=trows, elapsed=time.time() - t0)

def write_verdict(R):
    """Replace the PENDING coverage section of the table with the verdict."""
    matched = sum(R['matches'].values())
    total = len(R['realized'])
    L = []
    A = L.append
    A("## Coverage verdict")
    A("")
    v = "ALL MATCHED" if not R['unmatched'] and matched == total \
        else "MISMATCHES PRESENT"
    A(f"**GLUE-COVER: {matched}/{total} realized glued groups matched — "
      f"{v}.**  Violations recorded: {len(VIOL)}.")
    A("")
    A("Realized census per shape ID (main table):")
    A("")
    A("| ID | realized groups |")
    A("|---|---|")
    for sid in sorted(R['matches']):
        A(f"| {sid} | {R['matches'][sid]} |")
    A("")
    A(f"- rows {sum(1 for _ in set((g['tower'], g['gid'][1]) for g in R['realized']))} "
      f"(towers {dict(R['trows'])}); groups {total} — the committed census.")
    for d in R['dup_rep']:
        A(f"- realized duplicate-book fiber: {d['gid']} -> shape "
          f"{d['shape']} (dup-flagged), mult {d['mult']}, cell sign "
          f"{'-' if d['cell_sign'] < 0 else '+'}, group n = {d['group_n']} "
          f"({d['group_parity']}).")
    mut_total = sum(R['mut_stats'].values())
    mut_caught = sum(v for (g, c), v in R['mut_stats'].items() if c)
    A(f"- CTRL-MUT: {mut_caught}/{mut_total} mutants caught "
      f"({'TEETH CONFIRMED' if mut_caught == mut_total else 'TOOTHLESS'}).")
    A("")
    txt = open(TABLE_MD).read()
    head = txt.split("## Coverage verdict")[0]
    open(TABLE_MD, "w").write(head + "\n".join(L) + "\n")
    print(f"VERDICT WRITTEN: {v}; {matched}/{total}; "
          f"CTRL-MUT {mut_caught}/{mut_total}")

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "--enum"
    if mode == "--enum":
        write_table()
        print(f"FINAL: enum-only run, violations {len(VIOL)}")
        return
    R = xcheck()
    write_verdict(R)
    res = dict(
        final=not VIOL,
        violations=[list(v) for v in VIOL],
        n_shapes_main=len(R['main']), n_shapes_annex=len(R['annex']),
        coverage=dict(matched=sum(R['matches'].values()),
                      total=len(R['realized']),
                      unmatched=[list(map(str, u)) for u in R['unmatched']]),
        matches={sid: R['matches'][sid] for sid in sorted(R['matches'])},
        rows=sum(1 for _ in set((g['tower'], g['gid'][1])
                                for g in R['realized'])),
        towers={t: c for t, c in sorted(R['trows'].items())},
        dup=R['dup_rep'],
        parity=dict(
            dup_shapes_main=[R['ids_m'][k] for k in R['main']
                             if R['main'][k]['dup']],
            dup_even=[R['ids_m'][k] for k in R['main']
                      if R['main'][k]['dup']
                      and R['main'][k]['parity'] == 'even'],
            dup_odd=[R['ids_m'][k] for k in R['main']
                     if R['main'][k]['dup']
                     and R['main'][k]['parity'] == 'odd']),
        mut={f"{g}|{'caught' if c else 'MISSED'}": v
             for (g, c), v in sorted(R['mut_stats'].items())},
        elapsed=R['elapsed'])
    json.dump(res, open(RESULTS, "w"), indent=1)
    print(f"WROTE {RESULTS}")
    print(f"FINAL: {'GREEN' if res['final'] else 'RED'} "
          f"({len(VIOL)} violations)")

if __name__ == "__main__":
    main()
