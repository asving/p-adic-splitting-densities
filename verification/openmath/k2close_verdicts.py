#!/usr/bin/env python3
"""k2close_verdicts.py — K2-CLOSE unit B, leg 1b: the PER-SHAPE PROTECTION
VERDICT column over the committed shape table (43 main + 10 annex shapes),
computed mechanically, plus the realized beta_min SYSTEM census on the 29
glued rows (the K2-THM-B instance leg).

CONSUMES READ-ONLY: k2close_enum.py (imported; enumeration re-run in-process
and guarded against the committed table: 43/10 shapes, GS-02/GS-08/GS-16
realized) and the md5-pinned instrument artifacts (k2close_enum.PINS).

THE RESIDUE MODEL (K2-L4 + the (K2-RES)(a) glue box + GLUE-EDGE).  A glued
shape's cell (fiber f, seed offset dt, stripped level-0 multiset K, sign s,
multiplicity m) has residue class the MONOMIAL
    x_dt * prod_{k in K} psibar_k * rho_f
in the free nonzero generators x_0, x_1 (seed digit residues res(c_{D_t}),
W-D2(iv)+), psibar_0, psibar_1 (level-0 digit residues res(C_k)), and ONE
rho_f PER FIBER (the fiber's dump-variant interior residue product: books of
one glued group share their interior skeleton — GLUE-EDGE, 38/38 — and
differ only in level-0 dump vectors, so the common part strips and each
fiber keeps one free nonzero ratio).  Signed count of the cell: s*m.  The
group-common stripped factor and the global sign multiply every class alike
and never affect protection.  A RESIDUE ASSIGNMENT is a homomorphism from
the exponent lattice Z^(4+r) to K0^*; its COINCIDENCE PATTERN is the
partition of the shape's distinct cell monomials by equal value.

PATTERNS = SUBGROUPS (the state space).  A realizable pattern P determines
H_P := <mu_i - mu_j : i ~P j> and is CLOSED: i ~P j iff mu_i - mu_j in H_P.
Conversely every closed partition is realized: pick an integer weight
functional w vanishing on H_P; cross ratios nu not in span_Q(H_P) get
w(nu) != 0 generically (assignment x = z^w, z of large order, ANY
characteristic); a cross ratio nu in span_Q(H_P) \\ H_P forces a root of
unity — such states are flagged TORSION (realizable only where K0^* has the
torsion; kept — conservative for every safety verdict).  The state space =
closure of the discrete partition under (merge two blocks; close under
H-membership); BFS below enumerates it exactly.

PROTECTION (SD-L6/SD-L7 discipline, consumed at attempt grade).  Per state,
the class vector = per-block net signed counts; the group is PROTECTED
there iff the nonzero nets are exactly {+1} or {-1} or {+1,-1} (survives
netting char-free).  DEAD = all nets 0 (Sigma sgn*res == 0 identically).
ANNEX EXTENSION (A={0} forces ODD residue characteristic, K2-L8): a single
nonzero class of net +-2^k also survives (odd char never divides 2^k) —
tagged PROT2K, annex only.

THE VERDICT COLUMN:
  PROTECTED    every reachable state protected — survival unconditional.
  CONDITIONAL  some state protects, some does not — survival conditional on
               the (I1/I3/glue) identity configuration; witnesses emitted.
  NOVEL        NO state protects — the SD-L7 calculus can never certify the
               group alone; a new mechanism is needed (prose unit).
TOTAL INVARIANT (machine-checked): T = sum s*m is partition-blind, so a
protected state needs T in {0,+1,-1} (annex: also +-2^k) — shapes violating
that are NOVEL a priori (the even-dup imbalance genre).

CORNER SAFETY (the K2-THM-B input; main table only — the annex has no
psibar_1, and K2-L11's mass-balance kills all annex pure-digit identities).
I1: x_0 = x_1*psibar_1, I3: psibar_0 = psibar_1^2 are TOWER-level, shared
by every group of a row.  Corner c in {I1,!I1} x {I3,!I3}: corner-safe(c)
:= every state consistent with c (base H0 = <imposed>, states whose H
contains a negated identity pruned — such patterns force the identity and
lie outside c) is protected.  Single-book forms cover corners per K2-THM-A:
S all four; P1 the !I1 corners; P2 the !I3 corners; T1 the I1-or-I3 three.

ID-CLOSURE (machine shadow of Lemma K2-L11): for EVERY visited state H,
H ∩ {rho-free vectors} <= <I1, I3>.  (Proof in the note: the mass-balance
functional phi = 2*e_ps0 + e_ps1 - e_x1 and the x-degree functional vanish
on every fiber-balanced difference, and <I1,I3> is exactly their common
kernel on antisymmetric x-part; box (b)'s x0*ps0 = x1*ps1^3 is I1+I3.)

SEALED PREDICTIONS (hand-derived from the total invariant BEFORE first run):
  PV-1  no shape is verdict-PROTECTED (>=3 cells: generic state unprotected;
        2 cells have T=0 or |T|=2, so full-merge is DEAD or generic fails).
  PV-2  NOVEL includes exactly-by-invariant GS-11, GS-19, GS-20, GS-21,
        GS-30, GS-34, GS-35 (|T|=2, all even-n dup shapes) and AS-10 (T=3);
        T=0 shapes may add machine-found NOVELs (GS-40 hand-suspected: its
        I1/I3 linkage seems to force every {+1,-1} split to cascade dead).
  PV-3  GS-02, GS-08, GS-16 (all realized shapes) CONDITIONAL; GS-08 and
        GS-16 I3-corner-safe; GS-02 safe on NO corner (glue kill everywhere).
  PV-4  every realized glued group's in-vivo signed vector is SD-L7
        protected or its row holds another protected bottom group (K2-PROT
        shadow); realized GS-02 vectors are (-1,+1) — glue identity FAILS
        in vivo on all 28.
  PV-5  ID-CLOSURE: zero violations over all visited states.

Usage: python3 k2close_verdicts.py   (writes k2close_verdict_table.md +
       k2close_verdicts_results.json; deterministic, exact integer algebra).

    [SHAKEDOWN REPAIR + PV-4 DISPOSITION, 2026-08-08 campaign (wallclock
    2026-08-04), pre-commit, on record.  (i) First run exposed a CODE BUG:
    analyze_shape did not pass annex=annex into explore(), so the annex
    PROT2K criterion was unreachable and AS-03/AS-08 were misgraded NOVEL
    against their own full_merge=PROT2K readout — repaired (the only code
    change), verdicts now AS-03/AS-08 CONDITIONAL.  (ii) PV-4's middle
    clause is FALSIFIED BY THE PINNED DATA (a finding, not a law breach —
    verified directly against survk2_instrument_results.json grprec before
    any reclassification): the realized glue assignments are residue-
    DEGENERATE — every one of the 38 realized glued groups carries a
    SINGLE in-vivo residue class (the full-merge state; the roster's digit
    residues all coincide), so the 28 GS-02 groups net 0 (DEAD in vivo,
    their rows carried by co-located S groups) and the ten |T| = 1 groups
    (9 GS-08 + 1 SDW4G2F GS-16) net exactly T = +-1.  The sealed PV-4 text
    is left byte-untouched; prediction misses are reported as MISS,
    separately from law violations (FINAL judges laws only).  Machine law
    GLUE-DEGEN added to pin the finding: all 38 glued groups single-class,
    28 dead + 10 net +-1, every glued row protected in vivo.]
"""
import sys, os, json, time, collections, itertools
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import k2close_enum as KE

TABLE_MD = os.path.join(HERE, "k2close_verdict_table.md")
RESULTS = os.path.join(HERE, "k2close_verdicts_results.json")
STATE_CAP = 300000

VIOL = []
def viol(fam, msg):
    VIOL.append((fam, msg)); print(f"VIOLATION [{fam}] {msg}")

MISS = []   # sealed-prediction misses: findings, NOT law violations
def miss(k, msg):
    MISS.append((k, msg)); print(f"SEALED-PRED MISS [{k}] {msg}")

# ---------- exact integer/rational lattice kit --------------------------------
def _egcd(a, b):
    if b == 0:
        return (a, 1, 0) if a >= 0 else (-a, -1, 0)
    g, x, y = _egcd(b, a % b)
    return g, y, x - (a // b) * y

class Lat:
    """Integer lattice, row basis in echelon form (distinct leading columns)."""
    def __init__(self, dim, rows=None):
        self.dim = dim
        self.rows = dict(rows) if rows else {}
    def clone(self):
        return Lat(self.dim, self.rows)
    def add(self, v):
        v = list(v)
        c0 = 0
        while True:
            c = next((i for i in range(c0, self.dim) if v[i]), None)
            if c is None:
                return
            r = self.rows.get(c)
            if r is None:
                if v[c] < 0:
                    v = [-a for a in v]
                self.rows[c] = tuple(v)
                return
            g, x, y = _egcd(r[c], v[c])
            newr = tuple(x * a + y * b for a, b in zip(r, v))
            v = [(r[c] // g) * b - (v[c] // g) * a for a, b in zip(r, v)]
            self.rows[c] = newr
            c0 = c + 1
    def contains(self, v):
        v = list(v)
        for c in range(self.dim):
            if v[c] == 0:
                continue
            r = self.rows.get(c)
            if r is None or v[c] % r[c] != 0:
                return False
            q = v[c] // r[c]
            v = [a - q * b for a, b in zip(v, r)]
        return True
    def contains_q(self, v):
        v = [Fraction(a) for a in v]
        for c in range(self.dim):
            if v[c] == 0:
                continue
            r = self.rows.get(c)
            if r is None:
                return False
            q = v[c] / r[c]
            v = [a - q * b for a, b in zip(v, r)]
        return True
    def basis(self):
        return [self.rows[c] for c in sorted(self.rows)]

def vsub(a, b):
    return tuple(x - y for x, y in zip(a, b))

# ---------- the residue model of a shape --------------------------------------
def shape_model(key):
    """key = normalized shape key from k2close_enum.  Returns (monos, nets,
    labels, D): one monomial per distinct (fiber, dt, K) cell entry, exponent
    coords (x0, x1, ps0, ps1, rho_1..rho_r); net = sign * multiplicity."""
    r = len(key)
    D = 4 + r
    monos, nets, labels = [], [], []
    for f, (items, d) in enumerate(key):
        for (cell, m) in items:
            dt, K, s = cell
            assert dt in (0, 1), f"dt out of range: {dt}"
            v = [0] * D
            v[dt] += 1
            for k in K:
                v[2 + k] += 1
            v[4 + f] = 1
            monos.append(tuple(v))
            nets.append(s * m)
            labels.append(f"f{f+1}(dt={dt},{{{','.join(map(str, K))}}},"
                          f"{'+' if s > 0 else '-'}{'x%d' % m if m > 1 else ''})")
    assert len(set(monos)) == len(monos), "monomial collision inside a shape"
    return monos, nets, labels, D

def ivec(D, name):
    v = [0] * D
    if name == "I1":
        v[0], v[1], v[3] = 1, -1, -1        # x0 - x1 - ps1
    else:
        v[2], v[3] = 1, -2                  # ps0 - 2*ps1
    return tuple(v)

# ---------- states: closed partitions -----------------------------------------
def closure(blocks, base, monos, D):
    """Close a partition under H-membership, H = <base ∪ same-block diffs>.
    Returns (canonical blocks tuple, Lat H)."""
    blocks = [set(b) for b in blocks]
    while True:
        L = Lat(D)
        for v in base:
            L.add(v)
        for b in blocks:
            bs = sorted(b)
            for i in bs[1:]:
                L.add(vsub(monos[i], monos[bs[0]]))
        merged = False
        for i in range(len(blocks)):
            for j in range(i + 1, len(blocks)):
                d = vsub(monos[min(blocks[j])], monos[min(blocks[i])])
                if L.contains(d):
                    blocks[i] |= blocks[j]
                    del blocks[j]
                    merged = True
                    break
            if merged:
                break
        if not merged:
            key = tuple(sorted(tuple(sorted(b)) for b in blocks))
            return key, L

def protection(blocks, nets, annex):
    nz = sorted(n for n in (sum(nets[i] for i in b) for b in blocks) if n)
    if not nz:
        return "DEAD"
    if nz in ([1], [-1], [-1, 1]):
        return "PROT"
    if annex and len(nz) == 1 and abs(nz[0]) & (abs(nz[0]) - 1) == 0:
        return "PROT2K"
    return "UNPROT"

def digit_sublattice(L, D):
    """Generators of {v in H : rho-coords (indices >= 4) all zero}."""
    B = L.basis()
    k = len(B)
    if k == 0:
        return []
    r = D - 4
    KL = Lat(r + k)
    for i, row in enumerate(B):
        KL.add(list(row[4:]) + [1 if j == i else 0 for j in range(k)])
    out = []
    for c, kr in KL.rows.items():
        if c >= r:
            coeffs = kr[r:]
            out.append(tuple(sum(coeffs[i] * B[i][t] for i in range(k))
                             for t in range(D)))
    return out

def idclosure_ok(L, D, cat):
    return all(cat.contains(v) for v in digit_sublattice(L, D))

def state_tags(blocks, L, monos, D):
    """(torsion flag, digit-part readout of H) for a state."""
    tors = False
    reps = [min(b) for b in blocks]
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            d = vsub(monos[reps[j]], monos[reps[i]])
            if L.contains_q(d):
                tors = True
    dg = digit_sublattice(L, D)
    names = []
    for v in dg:
        a, b = v[0], v[2]           # I1-coeff = x0 coord, I3-coeff = ps0 coord
        names.append(f"I1^{a}*I3^{b}" if any(v) else "1")
    return tors, sorted(set(names))

def render_state(blocks, labels, nets):
    parts = []
    for b in blocks:
        net = sum(nets[i] for i in b)
        parts.append("{" + " ".join(labels[i] for i in sorted(b)) +
                     f" | net {net:+d}}}")
    return "  ".join(parts)

def explore(monos, nets, D, base=(), exclude=(), annex=False, mode="exists",
            cap=STATE_CAP, cat=None, idc=None):
    """BFS over closed partitions.  mode 'exists': stop at first PROT state;
    mode 'universal': stop at first non-PROT state.  Returns dict."""
    start, L0 = closure([{i} for i in range(len(monos))], list(base), monos, D)
    res = dict(n_states=0, capped=False, prot=None, bad=None, torsion=0,
               dead=None, corner_empty=False)
    if any(L0.contains(v) for v in exclude):
        # cannot happen (closure only merges H-forced pairs; H stays <base>)
        res["corner_empty"] = True
        return res
    seen = {start}
    stack = [(start, L0)]
    while stack:
        blocks, L = stack.pop()
        res["n_states"] += 1
        p = protection(blocks, nets, annex)
        good = p in ("PROT", "PROT2K")
        if idc is not None and not idclosure_ok(L, D, cat):
            idc.append(render_state(blocks, [str(m) for m in monos], nets))
        tors, dgn = state_tags(blocks, L, monos, D)
        if tors:
            res["torsion"] += 1
        rec = dict(blocks=[list(b) for b in blocks], prot=p,
                   torsion=tors, digit=dgn)
        if good and res["prot"] is None:
            res["prot"] = rec
            if mode == "exists":
                return res
        if not good and res["bad"] is None:
            res["bad"] = rec
            if mode == "universal":
                return res
        if p == "DEAD" and res["dead"] is None:
            res["dead"] = rec
        if res["n_states"] >= cap:
            res["capped"] = True
            return res
        for i in range(len(blocks)):
            for j in range(i + 1, len(blocks)):
                nb = [set(b) for b in blocks]
                nb[i] |= nb[j]
                del nb[j]
                nkey, NL = closure(nb, list(base), monos, D)
                if nkey in seen:
                    continue
                if any(NL.contains(v) for v in exclude):
                    seen.add(nkey)      # outside the corner; prune subtree
                    continue
                seen.add(nkey)
                stack.append((nkey, NL))
    return res

# ---------- Part A: the per-shape verdict --------------------------------------
def is2k(m):
    return m >= 1 and m & (m - 1) == 0

def pattern_class(nets):
    s = tuple(sorted(nets))
    return min(s, tuple(sorted(-n for n in nets)))

def analyze_shape(sid, key, annex, idc_viols):
    monos, nets, labels, D = shape_model(key)
    T = sum(nets)
    cat = Lat(D)
    cat.add(ivec(D, "I1"))
    cat.add(ivec(D, "I3"))
    n = len(monos)
    gen_key, gen_L = closure([{i} for i in range(n)], [], monos, D)
    gen_prot = protection(gen_key, nets, annex)
    full_key, full_L = closure([set(range(n))], [], monos, D)
    full_prot = protection(full_key, nets, annex)
    rec = dict(id=sid, annex=annex, n_cells=sum(abs(x) for x in nets),
               n_monos=n, r=len(key), T=T,
               pattern=list(pattern_class(nets)),
               generic=gen_prot, full_merge=full_prot, labels=labels)
    # protected-state existence
    if not annex and abs(T) >= 2:
        rec.update(prot_exists=False, prot_wit=None,
                   novel_cert=f"total-invariant |T|={abs(T)}>=2 (main)",
                   free_states=None, free_capped=False)
    elif annex and abs(T) >= 2 and not is2k(abs(T)):
        rec.update(prot_exists=False, prot_wit=None,
                   novel_cert=f"annex total-invariant T={T} not 0/+-1/+-2^k",
                   free_states=None, free_capped=False)
    else:
        r1 = explore(monos, nets, D, annex=annex, mode="exists", cat=cat,
                     idc=idc_viols)
        rec.update(free_states=r1["n_states"], free_capped=r1["capped"])
        if r1["prot"]:
            w = r1["prot"]
            rec.update(prot_exists=True, novel_cert=None,
                       prot_wit=dict(state=render_state(
                           [set(b) for b in w["blocks"]], labels, nets),
                           digit=w["digit"], torsion=w["torsion"]))
        elif not r1["capped"]:
            rec.update(prot_exists=False, prot_wit=None,
                       novel_cert=f"exhaustive ({r1['n_states']} states, "
                                  f"no protected state)")
        else:
            rec.update(prot_exists=None, prot_wit=None,
                       novel_cert="STATE CAP HIT — unresolved")
    # non-protected-state existence (kill witness)
    r2 = explore(monos, nets, D, annex=annex, mode="universal", cat=cat,
                 idc=idc_viols)
    if r2["bad"]:
        w = r2["bad"]
        rec["kill_wit"] = dict(prot=w["prot"], state=render_state(
            [set(b) for b in w["blocks"]], labels, nets),
            digit=w["digit"], torsion=w["torsion"])
    else:
        rec["kill_wit"] = None if not r2["capped"] else "CAP"
    # verdict
    if rec["prot_exists"] is None:
        rec["verdict"] = "UNRESOLVED"
    elif not rec["prot_exists"]:
        rec["verdict"] = "NOVEL"
    elif rec["kill_wit"] is None:
        rec["verdict"] = "PROTECTED"
    else:
        rec["verdict"] = "CONDITIONAL"
    # corner safety (main table only; annex has no I1/I3 content)
    if not annex:
        corners = {}
        I1, I3 = ivec(D, "I1"), ivec(D, "I3")
        for cname, base, excl in (("c11", [I1, I3], []),
                                  ("c10", [I1], [I3]),
                                  ("c01", [I3], [I1]),
                                  ("c00", [], [I1, I3])):
            rr = explore(monos, nets, D, base=base, exclude=excl,
                         mode="universal", cat=cat, idc=idc_viols)
            corners[cname] = dict(
                safe=(rr["bad"] is None and not rr["capped"]),
                n_states=rr["n_states"], capped=rr["capped"],
                bad=None if not rr["bad"] else dict(
                    prot=rr["bad"]["prot"],
                    state=render_state([set(b) for b in rr["bad"]["blocks"]],
                                       labels, nets)))
        rec["corners"] = corners
    else:
        rec["corners"] = None
    return rec

# ---------- Part C: the realized beta_min systems on the glued rows -----------
FORM_CORNERS = {"S": {"c00", "c01", "c10", "c11"},
                "P1": {"c00", "c01"},        # protected iff !I1
                "P2": {"c00", "c10"},        # protected iff !I3
                "T1": {"c01", "c10", "c11"}} # protected iff I1 or I3

def classify_form(cnt):
    """cnt: dict (t, K, sgn) -> mult for a single-book bottom group.
    Returns S/P1/P2/T1/OTHER after the S6 normalization."""
    if any(m != 1 for m in cnt.values()):
        return "OTHER"
    cells = list(cnt)
    common = None
    for (t, K, s) in cells:
        c = collections.Counter(K)
        common = c if common is None else (common & c)
    tmin = min(t for (t, K, s) in cells)
    for flip in (1, -1):
        norm = sorted((t - tmin,
                       tuple(sorted((collections.Counter(K) - common)
                                    .elements())), s * flip)
                      for (t, K, s) in cells)
        if norm == [(0, (), 1)]:
            return "S"
        if norm == [(0, (), 1), (1, (1,), -1)]:
            return "P1"
        if norm == [(0, (0,), -1), (0, (1, 1), 1)]:
            return "P2"
        if norm == [(0, (1,), -1), (1, (0,), -1), (1, (1, 1), 1)]:
            return "T1"
    return "OTHER"

def load_rows():
    for f, want in KE.PINS.items():
        got = KE.md5(os.path.join(HERE, f))
        if got != want:
            viol("PIN", f"{f}: {got} != {want}")
    inst = json.load(open(os.path.join(HERE,
                                       "survk2_instrument_results.json")))
    rows = collections.defaultdict(list)
    for rec in inst["grprec"]:
        fibers = collections.defaultdict(collections.Counter)
        for c in rec["cells"]:
            cell, book = KE.parse_cell(c)
            fibers[book][cell] += 1
        rows[(rec["tower"], tuple(rec["key"]))].append((rec, fibers))
    return rows

def sdl7_invivo(signed):
    nz = sorted(s for s in signed if s)
    return nz in ([1], [-1], [-1, 1])

def census(shape_recs, ids_m):
    rows = load_rows()
    glued_rows = {rk: grps for rk, grps in rows.items()
                  if any(len(f) >= 2 for (_, f) in grps)}
    if len(glued_rows) != 29:
        viol("SYS-CENSUS", f"{len(glued_rows)} glued rows, expected 29")
    shape_corners = {r["id"]: {c for c, v in (r["corners"] or {}).items()
                               if v["safe"]}
                     for r in shape_recs if not r["annex"]}
    out = []
    for rk in sorted(glued_rows):
        grps = glued_rows[rk]
        groups, covered = [], set()
        prot_vivo = False
        for (rec, fibers) in sorted(grps, key=lambda g: g[0]["slot"]):
            if len(fibers) >= 2:
                try:
                    key = KE.normalize_group([dict(f) for f in
                                              fibers.values()])
                    kind = ids_m.get(key, "UNMATCHED")
                except AssertionError as e:
                    kind = "BREACH"
                if kind in ("UNMATCHED", "BREACH"):
                    viol("SYS-SHAPE", f"{rk} slot {rec['slot']}: {kind}")
                cov = shape_corners.get(kind, set())
            else:
                kind = classify_form(dict(list(fibers.values())[0]))
                cov = FORM_CORNERS.get(kind, set())
            covered |= cov
            pv = sdl7_invivo(rec["signed"])
            prot_vivo = prot_vivo or pv
            groups.append(dict(slot=rec["slot"], kind=kind, n=rec["n"],
                               signed=rec["signed"], sdl7_vivo=pv,
                               corners=sorted(cov)))
        out.append(dict(tower=rk[0], key=list(rk[1]), n_groups=len(groups),
                        groups=groups, corners_covered=sorted(covered),
                        class_closed=(covered == {"c00", "c01", "c10",
                                                  "c11"}),
                        prot_in_vivo=prot_vivo))
    # GLUE-DEGEN (law, added at the shakedown disposition): every realized
    # glued group is single-class in vivo (the full-merge state); the 28
    # T=0 groups are DEAD, the 10 |T|=1 groups net exactly +-1; every glued
    # row still protected in vivo (via co-located groups).
    gl = [g for row in out for g in row["groups"]
          if g["kind"].startswith("GS")]
    ok = (len(gl) == 38 and all(len(g["signed"]) == 1 for g in gl)
          and sum(1 for g in gl if g["signed"] == [0]) == 28
          and sum(1 for g in gl if abs(g["signed"][0]) == 1) == 10
          and all(row["prot_in_vivo"] for row in out))
    if not ok:
        viol("GLUE-DEGEN", "in-vivo degeneracy census broke: "
             f"{collections.Counter(tuple(g['signed']) for g in gl)}")
    return out

# ---------- table writer and main ---------------------------------------------
def md_safe(s, cap=110):
    s = s.replace("|", "/")
    return s if len(s) <= cap else s[:cap - 3] + "..."

def corner_str(rec):
    if rec["corners"] is None:
        return "—"
    return "".join(("Y" if rec["corners"][c]["safe"] else "n")
                   for c in ("c11", "c10", "c01", "c00"))

def evidence(rec):
    if rec["verdict"] == "NOVEL":
        return md_safe("NOVEL: " + rec["novel_cert"])
    ev = []
    if rec["prot_wit"]:
        d = rec["prot_wit"]
        ev.append("prot[" + ",".join(d["digit"]) +
                  ("|tors" if d["torsion"] else "") + "]: " + d["state"])
    if isinstance(rec["kill_wit"], dict):
        d = rec["kill_wit"]
        ev.append(f"kill({d['prot']})[" + ",".join(d["digit"]) + "]: " +
                  d["state"])
    return md_safe("  //  ".join(ev), 220)

def write_table(recs, cens, pv, elapsed):
    L = []
    A = L.append
    A("# k2close_verdict_table.md — per-shape protection verdicts at g0 = 2 "
      "(MACHINE-GENERATED)")
    A("")
    A("Generated by `k2close_verdicts.py` (K2-CLOSE unit B leg 1b).  DO NOT "
      "EDIT BY HAND.")
    A("Residue model, state space, protection criterion, corner semantics, "
      "and the sealed predictions PV-1..PV-5: the runner's docstring "
      "(authoritative copy).  Corners column = c11(I1&I3) c10(I1&!I3) "
      "c01(!I1&I3) c00(!I1&!I3), Y = corner-safe.")
    A("")
    for annex, title in ((False, "Main table: A = {0,1}"),
                         (True, "Annex: A = {0} (odd characteristic)")):
        rs = [r for r in recs if r["annex"] == annex]
        A(f"## {title} — {len(rs)} shapes")
        A("")
        A("| ID | cells | r | T | generic pattern | generic | verdict | "
          "corners | states | evidence |")
        A("|---|---|---|---|---|---|---|---|---|---|")
        for r in rs:
            A(f"| {r['id']} | {r['n_cells']} | {r['r']} | {r['T']:+d} | "
              f"{tuple(r['pattern'])} | {r['generic']} | **{r['verdict']}** "
              f"| {corner_str(r)} | {r['free_states'] or '-'} | "
              f"{evidence(r)} |")
        A("")
    A("## Tallies")
    A("")
    for annex, tag in ((False, "main"), (True, "annex")):
        t = collections.Counter(r["verdict"] for r in recs
                                if r["annex"] == annex)
        A(f"- {tag}: {dict(sorted(t.items()))}")
    novel = sorted(r["id"] for r in recs if r["verdict"] == "NOVEL")
    A(f"- NOVEL set: {', '.join(novel)}")
    A(f"- ID-CLOSURE states checked over all runs: every visited H has "
      f"digit part inside <I1,I3> (violations would be listed; none => "
      f"Lemma K2-L11 machine shadow GREEN).")
    A("")
    A("## Pattern classes (the prose grouping key: canonical generic net "
      "multiset)")
    A("")
    pcs = collections.defaultdict(list)
    for r in recs:
        pcs[(r["annex"], tuple(r["pattern"]))].append(
            f"{r['id']}({r['verdict'][:4]})")
    for (annex, pc), members in sorted(pcs.items(),
                                       key=lambda kv: (kv[0][0],
                                                       len(kv[0][1]),
                                                       kv[0][1])):
        A(f"- {'annex' if annex else 'main '} {pc}: {', '.join(members)}")
    A("")
    A("## Realized beta_min systems on the 29 glued rows (instance leg)")
    A("")
    A("| tower | key | groups (slot:kind:vector) | corners covered | "
      "class-closed | protected in vivo |")
    A("|---|---|---|---|---|---|")
    for row in cens:
        gs = "; ".join(f"{tuple(g['slot'])}:{g['kind']}:{g['signed']}"
                       for g in row["groups"])
        A(f"| {row['tower']} | {row['key']} | {md_safe(gs, 160)} | "
          f"{','.join(row['corners_covered'])} | "
          f"{'YES' if row['class_closed'] else 'NO'} | "
          f"{'yes' if row['prot_in_vivo'] else 'NO'} |")
    A("")
    closed = sum(1 for r in cens if r["class_closed"])
    A(f"- class-closed rows (all four corners covered by the system): "
      f"{closed}/{len(cens)}; the rest are protected IN VIVO only "
      f"(their kill identities fail on the instance) — K2-THM-B residual.")
    A("")
    A("## In-vivo degeneracy (GLUE-DEGEN, machine law added at shakedown)")
    A("")
    A("- All 38 realized glued groups are residue-DEGENERATE in vivo: a "
      "SINGLE class each (the full-merge state — the roster's digit "
      "residues all coincide).  The 28 GS-02 (T=0) groups net 0 = DEAD in "
      "vivo (their rows carried by co-located S groups); the 9 GS-08 + 1 "
      "GS-16 (|T|=1) groups net exactly +-1 = the full-merge anchor.  The "
      "instance roster therefore probes ONLY the full-merge corner of the "
      "state space — it is NO evidence about generic glue ratios.")
    A("")
    A("## Sealed-prediction verdicts (misses are findings, not violations)")
    A("")
    for k, v in pv.items():
        A(f"- {k}: {'GREEN' if v[0] else 'MISS'} — {v[1]}")
    A("")
    A(f"FINAL: laws {'GREEN' if not VIOL else 'RED'} ({len(VIOL)} "
      f"violations); sealed predictions "
      f"{sum(1 for v in pv.values() if v[0])}/{len(pv)} green "
      f"({', '.join(k for k, v in pv.items() if not v[0]) or 'none'} "
      f"missed); {elapsed:.1f}s.")
    open(TABLE_MD, "w").write("\n".join(L) + "\n")
    print(f"WROTE {TABLE_MD}")

def main():
    t0 = time.time()
    KE.selftest_inventory()
    main_sh = KE.enumerate_shapes({0, 1}, "A={0,1}")
    annex_sh = KE.enumerate_shapes({0}, "A={0}")
    ids_m, order_m = KE.sorted_ids(main_sh, "GS")
    ids_a, order_a = KE.sorted_ids(annex_sh, "AS")
    if len(main_sh) != 43 or len(annex_sh) != 10:
        viol("GUARD", f"shape counts {len(main_sh)}/{len(annex_sh)} != 43/10")
    er = json.load(open(os.path.join(HERE, "k2close_enum_results.json")))
    if er.get("matches") != {"GS-02": 28, "GS-08": 9, "GS-16": 1}:
        viol("GUARD", f"committed matches changed: {er.get('matches')}")
    idc = []
    recs = []
    for k in order_m:
        recs.append(analyze_shape(ids_m[k], k, False, idc))
        print(f"  {recs[-1]['id']}: {recs[-1]['verdict']} "
              f"(T={recs[-1]['T']:+d}, corners {corner_str(recs[-1])})")
    for k in order_a:
        recs.append(analyze_shape(ids_a[k], k, True, idc))
        print(f"  {recs[-1]['id']}: {recs[-1]['verdict']} "
              f"(T={recs[-1]['T']:+d})")
    if idc:
        viol("ID-CLOSURE", f"{len(idc)} states outside <I1,I3>: {idc[:3]}")
    cens = census(recs, ids_m)
    # sealed-prediction verdicts
    bid = {r["id"]: r for r in recs}
    pv = {}
    pv["PV-1"] = (not any(r["verdict"] == "PROTECTED" for r in recs),
                  "no verdict-PROTECTED shape")
    core = {"GS-11", "GS-19", "GS-20", "GS-21", "GS-30", "GS-34", "GS-35",
            "AS-10"}
    novel = {r["id"] for r in recs if r["verdict"] == "NOVEL"}
    pv["PV-2"] = (core <= novel,
                  f"invariant-core in NOVEL; extras (allowed): "
                  f"{sorted(novel - core)}")
    pv["PV-3"] = (all(bid[i]["verdict"] == "CONDITIONAL"
                      for i in ("GS-02", "GS-08", "GS-16"))
                  and all(bid[i]["corners"][c]["safe"]
                          for i in ("GS-08", "GS-16")
                          for c in ("c01", "c11"))
                  and not any(v["safe"]
                              for v in bid["GS-02"]["corners"].values()),
                  "GS-02/08/16 CONDITIONAL; 08/16 I3-corner-safe; "
                  "GS-02 safe nowhere")
    gs02 = [g for row in cens for g in row["groups"] if g["kind"] == "GS-02"]
    pv["PV-4"] = (len(gs02) == 28
                  and all(sorted(x for x in g["signed"] if x) == [-1, 1]
                          for g in gs02)
                  and all(r["prot_in_vivo"] for r in cens),
                  f"{len(gs02)} GS-02 groups all (-1,+1) in vivo; all 29 "
                  f"rows protected in vivo")
    pv["PV-5"] = (not idc, "ID-CLOSURE zero violations")
    for k, v in pv.items():
        if not v[0]:
            miss(k, v[1])
    elapsed = time.time() - t0
    write_table(recs, cens, pv, elapsed)
    res = dict(final=not VIOL, violations=[list(v) for v in VIOL],
               pred_misses=[list(m) for m in MISS],
               tallies={tag: dict(collections.Counter(
                   r["verdict"] for r in recs if r["annex"] == annex))
                   for annex, tag in ((False, "main"), (True, "annex"))},
               novel=sorted(novel), predictions={k: list(v)
                                                 for k, v in pv.items()},
               shapes=recs, census=cens, elapsed=elapsed)
    json.dump(res, open(RESULTS, "w"), indent=1, default=str)
    print(f"WROTE {RESULTS}")
    print(f"FINAL: laws {'GREEN' if not VIOL else 'RED'} ({len(VIOL)} "
          f"violations); predictions "
          f"{sum(1 for v in pv.values() if v[0])}/{len(pv)} green; "
          f"{elapsed:.1f}s")

if __name__ == "__main__":
    main()
