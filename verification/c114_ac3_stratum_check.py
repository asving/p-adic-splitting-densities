#!/usr/bin/env python3
"""
A-C.3 certification: the RE-SIGNED C.114 count laws `(HT-branch)` / `(HT-global)`
(blueprint CHAP-C_tower_grammar.md NODE C.114, amendment A-C.3, 2026-08-16).

WHY THIS FILE EXISTS.  A-C.2 machine-refuted BOTH frozen C.114 axioms
(`leanfinal/Uniformity/ChapC/C111_C114_REFUTATION.lean.txt`): the frozen realization
stratum reads none of `kappa`, `kappa0`, `s`, the non-root `sideType`s, nor the
child-completeness of the tree, while `htBranchCount`/`htGlobalCount` read all of
them, so κ-separated one-node trees (and κ₀-separated EMPTY shapes) give equinumerous
strata with formula values 1 vs 2.  A-C.2 WITHDREW the two axioms and recorded a
DESIGNED CLAUSE LIST for the re-sign, with the standing warning that the re-sign needs
its OWN certification leg before signing.  This file is that leg.

WHAT IS CHECKED (exact counts, brute force over O = Z/p^N, key degree d = 1):

  [LAW]   stratum(t, N) == htBranchCount(Q, census, t, N)  for every enumerated tree,
          where stratum(t,N) = #{ level-N classes f : f realizes t } under the
          A-C.3 refined `htRealizes`, and the tree satisfies the A-C.3 tree
          well-formedness (clauses TWF/WF/ROOT0/CONS/COMPL/FENCE/KAPPA/VIS below).
          Trees: depth 0, depth-1 chain, depth-2 chain, depth-1 branching with two
          children on ONE side (q=3: the κ=1 and κ=2 geometries) and on TWO sides
          (q=2).  [GLOBAL] does the same for `htGlobalCount` on two-branch shapes
          (κ₀ = 1 and κ₀ = 2), at fixed branch keys with DISTINCT residues.

  [SEP]   the two A-C.2 refutation geometries are SEPARATED by the clause list:
          the κ-separated one-node trees `⟨[vK k]⟩` and the κ₀-separated empty
          shapes `⟨[], k⟩` fail the κ-rule / κ₀-rule for k ≠ 1, so the re-signed
          statement never speaks about them; at k = 1 it does, and is TRUE there.

  [TOOTH] per-clause mutation teeth: for each clause C of the designed list, an
          enumerated instance that satisfies every clause EXCEPT C and on which
          stratum ≠ formula.  A clause with no tooth is DEAD WEIGHT and is reported
          as such (the charge's flag).

MODEL AND ITS EXACTNESS.  O is modelled by Z/p^N and a level-N class of `f` is a
coefficient tuple mod p^N; `Φ = x` (key degree d = 1, so the Φ-adic development of a
polynomial at the key `x − w` is its Taylor expansion at `w`).  All the clauses read
only valuations `< N` and residual digits, so they are functions of the level-N data.
The one clause that is a priori NOT level-N readable is the divisibility
`G_child ∣ G_parent`.  In every instance below the children of a node either
(a) exhaust it (`Σ_u m_u = m_v`, so `G_v = ∏_u G_u` EXACTLY and the level-N reading
`f ≡ ∏ G_u (mod p^N)` is equivalent to the existence of a genuine O-realization in the
same level-N class — take the exact product as the witness), or (b) are the single
unfractured child (`m_u = m_v`, so `G_u = G_v` and divisibility is trivial).  So the
model is exact for the enumerated instances; nothing here relies on lifting a mod-p^N
factorization.

Exit 0 iff every check passes.  Run:  python3 c114_ac3_stratum_check.py
"""

import itertools
import os
import sys
from math import factorial, gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c109_ac2_cell_check as ac2  # the A-C.2 machinery (reused verbatim)

# ---------------------------------------------------------------------------
# caches over the A-C.2 primitives (factor_type re-sieves on every call)
# ---------------------------------------------------------------------------

_FT_CACHE = {}


def factor_type(F, c):
    key = (F.p, F.d, F.g, tuple(tuple(x) for x in c))
    v = _FT_CACHE.get(key)
    if v is None:
        v = ac2.factor_type(F, c)
        _FT_CACHE[key] = v
    return v


_CENSUS_CACHE = {}


def side_census(F, lam):
    key = (F.p, F.d, F.g, lam)
    v = _CENSUS_CACHE.get(key)
    if v is None:
        v = ac2.side_census(F, lam)
        _CENSUS_CACHE[key] = v
    return v


# ---------------------------------------------------------------------------
# the node / tree datum (the leanspec carriers, transcribed)
# ---------------------------------------------------------------------------

class Node:
    """`HTNode`: m, s, Pceil (list of length m+1), L, sides {(u,l): lam}, kappa."""

    def __init__(self, m, s, Pceil, L, sides, kappa=1):
        self.m = m
        self.s = s
        self.Pceil = list(Pceil)
        self.L = L
        self.sides = dict(sides)
        self.kappa = kappa

    def key(self):
        return (self.m, self.s, tuple(self.Pceil), self.L,
                tuple(sorted(self.sides.items())), self.kappa)

    def __eq__(self, other):
        return isinstance(other, Node) and self.key() == other.key()

    def __hash__(self):
        return hash(self.key())

    def __repr__(self):
        return (f"Node(m={self.m},s={self.s},P={self.Pceil},L={self.L},"
                f"sides={self.sides},kappa={self.kappa})")

    def B(self, N):
        """`HTNode.B` with the ℕ-truncated subtractions of the Lean def."""
        x = self.m * N
        x = max(0, x - sum(self.Pceil[j] for j in range(self.m)))
        return max(0, x - self.L)

    def D(self, N):
        return sum(max(N - ((self.m - j) * self.s + 1), 0) for j in range(self.m))


class Tree:
    """`HTTree`: nodes (list) + parent (list; parent[0] unused, root = 0)."""

    def __init__(self, nodes, parent):
        self.nodes = list(nodes)
        self.parent = list(parent)

    def children(self, i):
        return [u for u in range(1, len(self.nodes)) if self.parent[u] == i]

    def desc(self, i):
        out, frontier = [i], [i]
        while frontier:
            nxt = []
            for v in frontier:
                for u in self.children(v):
                    out.append(u)
                    nxt.append(u)
            frontier = nxt
        return sorted(out)


# ---------------------------------------------------------------------------
# THE A-C.3 CLAUSE LIST — tree-side well-formedness
# ---------------------------------------------------------------------------

def clause_TWF(t):
    """`HTTree.WF`: parent i < i for 0 < i < len (acyclic index encoding)."""
    return all(t.parent[i] < i for i in range(1, len(t.nodes)))


def clause_WF(t):
    """per-node `HTNode.WF` (A-C.2's five clauses, via the A-C.2 chord tests)."""
    for v in t.nodes:
        if v.Pceil[v.m] != 0:
            return False
        okc, L, sides = ac2.lean_WF_data(v.Pceil, v.m)
        if not okc or L != v.L:
            return False
        if set(sides) != set(v.sides):
            return False
        for s, lam in v.sides.items():
            if sum(dd * mm for dd, mm in lam) != sides[s]:
                return False
    return True


def clause_ROOT0(t):
    """`s_root = 0` (EFF.W12.83: "previous center depth s_v (zero at the root)")."""
    return t.nodes[0].s == 0


def clause_CONS(t):
    """non-root nodes are CONSERVATIVE for their own depth (EFF.W12.83: "the child is
    the degree-d_i conservative node of multiplicity m_u and depth s_u")."""
    for i in range(1, len(t.nodes)):
        v = t.nodes[i]
        for j in range(v.m):
            if v.Pceil[j] < (v.m - j) * v.s + 1:
                return False
    return True


def clause_COMPL(t):
    """child-count-vs-type completeness (EFF.W12.83: "Its children are precisely the
    repeated linear factors (Y−z)^{m_u} on e = 1 sides.  If the side has slope −s_u,
    the child is the ... node of multiplicity m_u and depth s_u")."""
    for i in range(len(t.nodes)):
        v = t.nodes[i]
        ch = [t.nodes[u] for u in t.children(i)]
        # every child sits on an e = 1 side of v, at that side's slope
        for c in ch:
            if (c.s, 1) not in v.sides or c.m < 2:
                return False
        # exact counts against the side types
        for (u, l), lam in v.sides.items():
            if l != 1:
                continue
            for a in range(2, max([1] + [mm for _, mm in lam]) + 1):
                want = sum(1 for (dd, mm) in lam if dd == 1 and mm == a)
                got = sum(1 for c in ch if c.s == u and c.m == a)
                if want != got:
                    return False
    return True


def clause_FENCE(t):
    """the order-1 fence (EFF.W12.83: "Repeated factors of degree > 1, and repeated
    factors on e > 1 sides, open composite stages and are outside this order-1
    statement")."""
    for v in t.nodes:
        for (u, l), lam in v.sides.items():
            for (dd, mm) in lam:
                if mm >= 2 and (dd > 1 or l > 1):
                    return False
    return True


def clause_VIS(t, N):
    """window visibility (EFF.W12.83's standing hypothesis "window-visible ... key",
    and .86 step 5's `m_v s_v + 1 ≤ P_v(0) ≤ N − 1`)."""
    return all(v.Pceil[j] < N for v in t.nodes for j in range(v.m + 1))


def same_hist(t, u, up):
    """subtree isomorphism (the first-order form: a bijection of descendant sets
    fixing the roots, preserving node data, commuting with `parent`)."""
    du, dv = t.desc(u), t.desc(up)
    if len(du) != len(dv):
        return False
    if u == up:
        return True
    for perm in itertools.permutations(dv):
        sig = dict(zip(du, perm))
        if sig[u] != up:
            continue
        if any(t.nodes[w] != t.nodes[sig[w]] for w in du):
            continue
        if all(sig[t.parent[w]] == t.parent[sig[w]] for w in du if w != u):
            return True
    return False


def clause_KAPPA(t):
    """the (HT-orbit) κ-rule at tree level, DIVISION-FREE (the C.112 precedent):
    κ_v · ∏_{H ∈ history classes of v's children} (#H)!
        = ∏_{g ∈ (side, multiplicity) groups of v's children} (#g)!
    (EFF.W12.83: κ_v = ∏_{S,a} r_{v,S,a}! / ∏_H r_{v,S,a,H}!)."""
    for i in range(len(t.nodes)):
        ch = t.children(i)
        classes = []
        for u in ch:
            for cl in classes:
                if same_hist(t, u, cl[0]):
                    cl.append(u)
                    break
            else:
                classes.append([u])
        groups = {}
        for u in ch:
            groups.setdefault((t.nodes[u].s, t.nodes[u].m), []).append(u)
        lhs = t.nodes[i].kappa
        for cl in classes:
            lhs *= factorial(len(cl))
        rhs = 1
        for g in groups.values():
            rhs *= factorial(len(g))
        if lhs != rhs:
            return False
    return True


ALL_TREE_CLAUSES = ("TWF", "WF", "ROOT0", "CONS", "COMPL", "FENCE", "KAPPA", "VIS")


def tree_wf(t, N, off=()):
    checks = {
        "TWF": lambda: clause_TWF(t),
        "WF": lambda: clause_WF(t),
        "ROOT0": lambda: clause_ROOT0(t),
        "CONS": lambda: clause_CONS(t),
        "COMPL": lambda: clause_COMPL(t),
        "FENCE": lambda: clause_FENCE(t),
        "KAPPA": lambda: clause_KAPPA(t),
        "VIS": lambda: clause_VIS(t, N),
    }
    return all(fn() for name, fn in checks.items() if name not in off)


def tree_wf_report(t, N):
    return {name: tree_wf(t, N, off=tuple(c for c in ALL_TREE_CLAUSES if c != name))
            for name in ALL_TREE_CLAUSES}


# ---------------------------------------------------------------------------
# polynomial layer over O = Z/p^N with key degree d = 1
# ---------------------------------------------------------------------------

def taylor(pN, f, w, m):
    """the (x − w)-adic development of f, coefficients a_0..a_m (each a constant)."""
    return ac2.dev(pN, [(-w) % pN, 1], f, m)


def heights(p, N, f, w, m):
    """npHgt(x − w, f, j) for j = 0..m; None encodes ⊤ (a level-N zero)."""
    return [ac2.gauss_val(p, N, a) for a in taylor(p ** N, f, w, m)]


def assemble(pN, w, coeffs):
    """f = Σ_j coeffs[j] (x − w)^j, coeffs[m] = 1 (monic)."""
    out = [0]
    base = [1]
    K = [(-w) % pN, 1]
    for c in coeffs:
        if c:
            term = [(c * b) % pN for b in base]
            if len(term) > len(out):
                out = out + [0] * (len(term) - len(out))
            for i, x in enumerate(term):
                out[i] = (out[i] + x) % pN
        base = _polymul(pN, base, K)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def _polymul(pN, a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % pN
    return out


def in_cell(F, p, N, f, w, node):
    """`monicPoly a ∈ htCell π (x − w) node` — the A-C.2 re-signed three-way law."""
    m, P = node.m, node.Pceil
    devs = taylor(p ** N, f, w, m)
    nph = [ac2.gauss_val(p, N, a) for a in devs]
    for j in range(m + 1):
        h = nph[j]
        if h is not None and h < P[j]:
            return False
        if ac2.lean_IsVertex(P, m, j) and h != P[j]:
            return False
    for (u, l), lam in node.sides.items():
        r = ac2.side_reads(F, p, N, [(-w) % p ** N, 1], devs, m, u, l)
        if r is None:
            return False
        _, _, _, res = r
        if not res:
            return False
        if factor_type(F, ac2.monic_normalize(F, res)) != lam:
            return False
    return True


def centers(p, N, wparent, s):
    """all w with gaussVal(K − K_parent) = s exactly, K = x − w (d = 1)."""
    pN = p ** N
    if s >= N:
        return []
    return [(wparent + t) % pN for t in range(0, pN, p ** s) if (t // p ** s) % p != 0]


# ---------------------------------------------------------------------------
# THE A-C.3 REFINED `htRealizes` (per-clause switchable)
# ---------------------------------------------------------------------------
# realization clauses:
#   CELL  — per-node membership `G i ∈ htCell π (K i) (node i)` at the RECENTERED key
#   TYPE  — the side-type half of CELL at NON-ROOT nodes (split out for the teeth)
#   SPIN  — `gaussVal (K i − K (parent i)) = s_i`
#   DIST  — sibling distinctness: `gaussVal (K u − K u') = s` for u ≠ u' on one side
ALL_REAL_CLAUSES = ("CELL", "TYPE", "SPIN", "DIST")


def cell_ok(F, p, N, f, w, node, is_root, off):
    if "CELL" in off:
        return True
    if "TYPE" in off and not is_root:
        stripped = Node(node.m, node.s, node.Pceil, node.L, {}, node.kappa)
        return in_cell(F, p, N, f, w, stripped)
    return in_cell(F, p, N, f, w, node)


def realizes(F, p, N, t, i, G, w, off=(), cluster_choices=None):
    """does (G at key x − w) realize the subtree of t at i?  `cluster_choices(G, m)`
    supplies the candidate monic degree-m divisors of G (exhaustive)."""
    node = t.nodes[i]
    if not cell_ok(F, p, N, G, w, node, i == 0, off):
        return False
    ch = t.children(i)
    if not ch:
        return True
    cands = []
    for c in ch:
        nc = t.nodes[c]
        ws = centers(p, N, w, nc.s) if "SPIN" not in off else \
            [x % p ** N for x in range(p ** N)]
        lst = []
        for wc in ws:
            for Gc in cluster_choices(G, nc.m):
                if realizes(F, p, N, t, c, Gc, wc, off, cluster_choices):
                    lst.append((tuple(Gc), wc))
        if not lst:
            return False
        cands.append((c, lst))
    # a system of representatives with sibling distinctness + distinct clusters
    return _match(F, p, N, t, i, cands, 0, [], off)


def _match(F, p, N, t, i, cands, k, chosen, off):
    if k == len(cands):
        return True
    c, lst = cands[k]
    for (Gc, wc) in lst:
        ok = True
        for (c2, Gc2, wc2) in chosen:
            if Gc == Gc2:
                ok = False
                break
            if "DIST" not in off and t.nodes[c].s == t.nodes[c2].s:
                d = (wc - wc2) % p ** N
                if ac2.val_p(p, N, d) != t.nodes[c].s:
                    ok = False
                    break
        if ok and _match(F, p, N, t, i, cands, k + 1, chosen + [(c, Gc, wc)], off):
            return True
    return False


# ---------------------------------------------------------------------------
# the formulas (leanspec `htBranchCount` / `htGlobalCount`, transcribed)
# ---------------------------------------------------------------------------

def htBranchCount(Q, census, t, N):
    pref = 1
    for v in t.nodes:
        f = v.kappa
        for s, lam in v.sides.items():
            f *= census(lam)
        pref *= f
    e = max(0, sum(v.B(N) for v in t.nodes)
            - sum(t.nodes[i].D(N) for i in range(1, len(t.nodes))))
    return pref * Q ** e


def htGlobalCount(shape, q, censuses, N):
    kappa0, branches = shape
    out = kappa0
    for i, (d, m, tr) in enumerate(branches):
        out *= q ** (d * (N - 1)) if m == 1 else htBranchCount(q ** d, censuses[i], tr, N)
    return out


# ---------------------------------------------------------------------------
# enumeration of the root cell and of the stratum
# ---------------------------------------------------------------------------

def enum_cell(F, p, N, w, node):
    """all monic f of degree node.m (d = 1) with f ∈ htCell π (x − w) node."""
    pN = p ** N
    m, P = node.m, node.Pceil
    ranges = []
    for j in range(m):
        step = p ** min(P[j], N)
        ranges.append(range(0, pN, step) if step <= pN else [0])
    out = []
    for tup in itertools.product(*ranges):
        f = assemble(pN, w, list(tup) + [1])
        if in_cell(F, p, N, f, w, node):
            out.append(tuple(f))
    return out


def divisor_factory(F, p, N, t):
    """cluster candidates: for the enumerated instances a child either exhausts its
    parent (`m_u = m_v`, cluster = the parent) or the children exhaust the parent
    jointly (`Σ m_u = m_v`), so candidates are the monic divisors of the given degree
    whose root-level polygon is the child's slope segment.  Exhaustive by
    construction: every monic degree-`a` divisor with that polygon is tried."""
    pN = p ** N
    cache = {}

    def choices(G, a):
        key = (tuple(G), a)
        v = cache.get(key)
        if v is not None:
            return v
        degG = len(G) - 1
        if a == degG:
            v = [list(G)]
        else:
            v = []
            for cand in _monic_of_degree(pN, a):
                q, r = ac2.opoly_divmod(pN, list(G), list(cand))
                if not r:
                    v.append(list(cand))
        cache[key] = v
        return v

    return choices


_MON_CACHE = {}


def _monic_of_degree(pN, a):
    key = (pN, a)
    v = _MON_CACHE.get(key)
    if v is None:
        v = [list(tup) + [1] for tup in itertools.product(range(pN), repeat=a)]
        _MON_CACHE[key] = v
    return v


def stratum(F, p, N, t, off=(), root_key=0, root_cell=None, choices=None):
    """#{ level-N classes f : f realizes t at the key x − root_key }."""
    if choices is None:
        choices = divisor_factory(F, p, N, t)
    if root_cell is None:
        # the root cell membership is part of `realizes`; enumerating it first is a
        # pure speed-up (every stratum member lies in it when CELL is on)
        root_cell = enum_cell(F, p, N, root_key, t.nodes[0]) if "CELL" not in off \
            else _all_monic(p, N, t.nodes[0].m)
    n = 0
    for f in root_cell:
        if realizes(F, p, N, t, 0, list(f), root_key, off, choices):
            n += 1
    return n


def _all_monic(p, N, m):
    return [tuple(list(tup) + [1]) for tup in itertools.product(range(p ** N), repeat=m)]


# ---------------------------------------------------------------------------
# reporting
# ---------------------------------------------------------------------------

FAIL = 0
CHECKS = 0


def check(name, cond, detail=""):
    global FAIL, CHECKS
    CHECKS += 1
    if not cond:
        FAIL += 1
    print(f"[{'PASS' if cond else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))
    return cond


if __name__ == "__main__":
    print("skeleton only — instances land in the next commit")
