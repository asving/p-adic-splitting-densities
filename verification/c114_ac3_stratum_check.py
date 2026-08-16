#!/usr/bin/env python3
"""
A-C.3 certification: the RE-SIGNED C.114 count laws `(HT-branch)` / `(HT-global)`
(blueprint CHAP-C_tower_grammar.md NODE C.114, amendment A-C.3, 2026-08-16).

WHY THIS FILE EXISTS.  A-C.2 machine-refuted BOTH frozen C.114 axioms
(`leanfinal/Uniformity/ChapC/C111_C114_REFUTATION.lean.txt`): the frozen realization
stratum reads none of `kappa`, `kappa0`, `s`, the non-root `sideType`s, nor the
child-completeness of the tree, while `htBranchCount`/`htGlobalCount` read all of
them, so κ-separated one-node trees (and κ₀-separated EMPTY shapes) give equinumerous
strata with formula values 1 vs 2.  A-C.2 WITHDREW the two axioms, recorded a DESIGNED
CLAUSE LIST for the re-sign, and warned that the re-sign needs its OWN certification
leg BEFORE signing.  This file is that leg — and it earns its keep: the designed list
is INSUFFICIENT (finding D5 below), and the law is only true after one further clause.

    *** FINDING D5 (A-C.3, this file) — THE RECENTERING MUST BE BY A REPRESENTATIVE. ***
    A-C.2's designed `s`-pin `gaussVal (K i − K (parent i)) = s_i` leaves the lift of
    the residual root free above digit `s_i`, and the stratum's `∃ K` then RANGES over
    those lifts.  The corpus fixes one ("Choose a lift z̃", EFF.W12.84 step 2) and its
    lift-independence claim is about the COUNT, not the SET: the child's own polygon is
    NOT invariant under a shift of valuation `s_i + 1`, so `∃ lift` strictly enlarges
    the stratum whenever the child's residual has a linear factor.  Certified below at
    [D5]: with the designed list alone, `stratum = 324 ≠ 216 = formula` on the q = 3
    depth-2 chain (and `54 ≠ 18` on a q = 3 depth-1 tree whose leaf child has a split
    residual).  With the extra clause `K (parent i) − K i = π^{s_i} · z̃`, `z̃` drawn
    from a system of representatives of the degree-`< d` residue classes, every
    enumerated instance is exact — and the count is the SAME for every choice of
    representative system ([REP-INDEP], four systems, q = 3), which is exactly the
    corpus's lift-independence claim, certified.

    *** FINDING D6 (A-C.3, this file) — THE CORPUS'S PER-NODE NONNEGATIVITY IS FALSE
    AT MULTI-CHILD NODES. ***  `EFF.W12.85` step 3 asserts `#U_v(R) = Q^{B_v−Σ_u D_u}`
    and "in particular, the exponent is a nonnegative integer; divisibility ... is a
    consequence of the bijection, not an assumption".  On the corpus's OWN `B_v`/`D_u`
    definitions this is arithmetically impossible whenever the repeated-linear children
    EXHAUST the node (`Σ_u m_u = m_v`) with ≥ 2 children: for a one-sided node of slope
    `s`,   B_v(N) − Σ_u D_u(N) = −s(m_v² − Σ_u m_u²)/2 < 0   for EVERY N (checked at
    four shapes below; the `B_v` side is brute-force confirmed — the q = 3, m = 4,
    slope-1 root cell has exactly 3^6 = 729 members at N = 5, matching B = 6, while the
    two children's ambient conservative cells have 3^5 each).  The measured truth on
    three such nodes: 243 vs formula 9, 486 vs 108, 128 vs 32.  CONSEQUENCE FOR THE
    RE-SIGN: the per-node inequality is carried as the HYPOTHESIS `hnode` (the A-C.2
    precedent at C.111), which excludes exactly this regime; the multi-child regime
    under `hnode` (which needs `Σ_u m_u < m_v` and large N) is out of brute-force range
    and is recorded as CERTIFIED-OPEN, not certified.

WHAT IS CHECKED (exact counts, brute force over O = Z/p^N, key degree d = 1):

  [LAW]      stratum(t,N) == htBranchCount(Q, census, t, N) for every enumerated tree
             satisfying the A-C.3 clause list (TWF, WF, CONS, COMPL, FENCE, VIS,
             KAPPA, HNODE on the tree; CELL, TYPE, REP, DIST on the realization):
             depth 0 (q = 2,3; m = 1,2); depth-1 chains (q = 2,3; m = 2,3; including
             the corpus's own W12-L0 recovery row); depth-2 chains (q = 2,3).
  [GLOBAL]   stratum == htGlobalCount for two-branch shapes at fixed branch keys with
             DISTINCT residues (κ₀ = 1 and κ₀ = 2), q = 2.
  [REP-INDEP] the branch count is independent of the representative system (four
             systems), and REP ⟹ A-C.2's s-pin.
  [SEP]      the two A-C.2 refutation geometries are SEPARATED: the κ-separated
             one-node trees `⟨[vK k]⟩` and the κ₀-separated empty shapes `⟨[], k⟩`
             FAIL the κ-rule / κ₀-rule for k ≠ 1 (so the re-signed statement is silent
             on them), and at k = 1 the statement speaks and is TRUE.
  [D6]       the arithmetic identity above, at four shapes, plus three measured
             counterexamples to the frozen-plus-designed law without `hnode`.
  [TOOTH]    per-clause mutation teeth.  A clause with no tooth is flagged `[DEAD/
             SUBSUMED]` and reported, never quietly kept.  In this grid: WF, CONS,
             COMPL, KAPPA, VIS, HNODE, REP, TYPE, SIGMA, KAPPA0 and the
             distinct-residue clause all have teeth; SPIN is SUBSUMED by REP; DIST is
             subsumed by the side-type pin in the reachable geometries; FENCE is a
             SCOPE fence with no truth tooth.

MODEL AND ITS EXACTNESS.  O is modelled by Z/p^N and a level-N class of `f` is a
coefficient tuple mod p^N; `Φ = x` (key degree d = 1, so the Φ-adic development at the
key `x − w` is the Taylor expansion at `w`).  Every clause reads only valuations `< N`
and residual digits, so all are functions of the level-N data.  The one clause that is
a priori NOT level-N readable is `G_child ∣ G_parent`.  In every instance below the
children of a node either (a) exhaust it (`Σ_u m_u = m_v`, so `G_v = ∏_u G_u` EXACTLY
and the level-N reading is equivalent to the existence of a genuine O-realization in
the same level-N class — take the exact product as the witness), or (b) are the single
unfractured child (`m_u = m_v`, so `G_u = G_v`, divisibility trivial).  So the model is
exact for the enumerated instances; nothing here relies on lifting a mod-p^N
factorization.  (The joint form `(∏_u G_u) ∣ G_v` is what is enumerated: over O it is
EQUIVALENT to the signed per-child clause, since distinct sibling centres make the
clusters coprime over K and Gauss gives the product, but at level N the per-child form
is strictly weaker — mod-π^N divisors are not unique, and indeed EVERY member of the
q = 3 root cell has a mod-π^5 divisor in the child cell.)

Exit 0 iff every check passes.  Run:  python3 c114_ac3_stratum_check.py
"""

import itertools
import os
import sys
from math import factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c109_ac2_cell_check as ac2  # the A-C.2 machinery, reused

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
# the carriers (`HTNode`, `HTTree`, `HTShape`), transcribed from leanspec
# ---------------------------------------------------------------------------

class Node:
    def __init__(self, m, s, Pceil, L, sides, kappa=1):
        self.m, self.s, self.Pceil, self.L = m, s, list(Pceil), L
        self.sides, self.kappa = dict(sides), kappa

    def key(self):
        return (self.m, self.s, tuple(self.Pceil), self.L,
                tuple(sorted(self.sides.items())), self.kappa)

    def __eq__(self, o):
        return isinstance(o, Node) and self.key() == o.key()

    def __hash__(self):
        return hash(self.key())

    def __repr__(self):
        return (f"(m={self.m},s={self.s},P={self.Pceil},L={self.L},"
                f"sides={self.sides},k={self.kappa})")

    def B(self, N):
        x = max(0, self.m * N - sum(self.Pceil[j] for j in range(self.m)))
        return max(0, x - self.L)

    def D(self, N):
        return sum(max(N - ((self.m - j) * self.s + 1), 0) for j in range(self.m))


class Tree:
    def __init__(self, nodes, parent):
        self.nodes, self.parent = list(nodes), list(parent)

    def children(self, i):
        return [u for u in range(1, len(self.nodes)) if self.parent[u] == i]

    def desc(self, i):
        out, fr = [i], [i]
        while fr:
            nxt = []
            for v in fr:
                for u in self.children(v):
                    out.append(u)
                    nxt.append(u)
            fr = nxt
        return sorted(out)


# ---------------------------------------------------------------------------
# THE A-C.3 CLAUSE LIST — tree-side
# ---------------------------------------------------------------------------

def clause_TWF(t, N):
    """`HTTree.WF`: parent i < i (acyclic index encoding)."""
    return all(t.parent[i] < i for i in range(1, len(t.nodes)))


def clause_WF(t, N):
    """per-node `HTNode.WF` (A-C.2's five clauses, via A-C.2's chord tests)."""
    for v in t.nodes:
        if v.Pceil[v.m] != 0:
            return False
        okc, L, sides = ac2.lean_WF_data(v.Pceil, v.m)
        if not okc or L != v.L or set(sides) != set(v.sides):
            return False
        for s, lam in v.sides.items():
            if sum(dd * mm for dd, mm in lam) != sides[s]:
                return False
    return True


def clause_CONS(t, N):
    """non-root nodes are CONSERVATIVE for their own depth (EFF.W12.83: "the child is
    the degree-d_i conservative node of multiplicity m_u and depth s_u";
    `C_{m_v}(s_v) = {(a_j) : v(a_j) ≥ (m_v − j)s_v + 1}`)."""
    for i in range(1, len(t.nodes)):
        v = t.nodes[i]
        if any(v.Pceil[j] < (v.m - j) * v.s + 1 for j in range(v.m)):
            return False
    return True


def clause_COMPL(t, N):
    """child-count-vs-type completeness (EFF.W12.83: "Its children are precisely the
    repeated linear factors (Y−z)^{m_u} on e = 1 sides.  If the side has slope −s_u,
    the child is the ... node of multiplicity m_u and depth s_u")."""
    for i in range(len(t.nodes)):
        v = t.nodes[i]
        ch = [t.nodes[u] for u in t.children(i)]
        for c in ch:
            if (c.s, 1) not in v.sides or c.m < 2:
                return False
        for (u, l), lam in v.sides.items():
            if l != 1:
                continue
            top = max([1] + [mm for _, mm in lam])
            for a in range(2, top + 1):
                want = sum(1 for (dd, mm) in lam if dd == 1 and mm == a)
                if want != sum(1 for c in ch if c.s == u and c.m == a):
                    return False
    return True


def clause_FENCE(t, N):
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
    """window visibility (EFF.W12.83's standing "window-visible ... key"; .86 step 5's
    `m_v s_v + 1 ≤ P_v(0) ≤ N − 1`)."""
    return all(v.Pceil[j] < N for v in t.nodes for j in range(v.m + 1))


def same_hist(t, u, up, t2=None, u2=None):
    """subtree isomorphism, in the FIRST-ORDER form signed in Lean: a bijection of
    descendant sets carrying root to root, preserving node data, commuting with
    `parent`.  (`t2`/`u2` allow the comparison across two trees, for κ₀.)"""
    t2 = t if t2 is None else t2
    u2 = up if u2 is None else u2
    du, dv = t.desc(u), t2.desc(u2)
    if len(du) != len(dv):
        return False
    for perm in itertools.permutations(dv):
        sig = dict(zip(du, perm))
        if sig[u] != u2:
            continue
        if any(t.nodes[w] != t2.nodes[sig[w]] for w in du):
            continue
        if all(sig[t.parent[w]] == t2.parent[sig[w]] for w in du if w != u):
            return True
    return False


def _classes(items, eq):
    out = []
    for x in items:
        for cl in out:
            if eq(x, cl[0]):
                cl.append(x)
                break
        else:
            out.append([x])
    return out


def clause_KAPPA(t, N):
    """the (HT-orbit) κ-rule at tree level, DIVISION-FREE (the C.112 precedent):
    κ_v · ∏_{H a history class of v's children} (#H)!
        = ∏_{g a (side, multiplicity) group of v's children} (#g)!
    (EFF.W12.83: `κ_v = ∏_{S,a} r_{v,S,a}! / ∏_H r_{v,S,a,H}!`)."""
    for i in range(len(t.nodes)):
        ch = t.children(i)
        lhs = t.nodes[i].kappa
        for cl in _classes(ch, lambda a, b: same_hist(t, a, b)):
            lhs *= factorial(len(cl))
        rhs = 1
        for g in _classes(ch, lambda a, b: (t.nodes[a].s, t.nodes[a].m)
                          == (t.nodes[b].s, t.nodes[b].m)):
            rhs *= factorial(len(g))
        if lhs != rhs:
            return False
    return True


def clause_HNODE(t, N):
    """the PER-NODE exponent inequality (EFF.W12.85's `#U_v = Q^{B_v − Σ_u D_u}`, "in
    particular, the exponent is a nonnegative integer"), carried as a HYPOTHESIS — the
    A-C.2 precedent at C.111.  Finding D6 (this file): the corpus's derivation of it is
    FALSE at nodes whose repeated-linear children EXHAUST the multiplicity with ≥ 2
    children (`B_v − Σ_u D_u = −s(m_v² − Σ_u m_u²)/2 < 0` for a one-sided node, for
    EVERY N), so it is not derivable and must be carried."""
    for i in range(len(t.nodes)):
        if sum(t.nodes[u].D(N) for u in t.children(i)) > t.nodes[i].B(N):
            return False
    return True


TREE_CLAUSES = {"TWF": clause_TWF, "WF": clause_WF, "CONS": clause_CONS,
                "COMPL": clause_COMPL, "FENCE": clause_FENCE, "VIS": clause_VIS,
                "KAPPA": clause_KAPPA, "HNODE": clause_HNODE}


def tree_wf(t, N, off=()):
    return all(fn(t, N) for k, fn in TREE_CLAUSES.items() if k not in off)


def failing_clauses(t, N):
    return [k for k, fn in TREE_CLAUSES.items() if not fn(t, N)]


def kappa0_rule(shape):
    """the level-0 orbit rule (EFF.W12.83: `κ₀(T) = ∏_{d,m} r_{d,m}!/∏_H r_{d,m,H}!`),
    division-free, with the branch histories compared by tree isomorphism."""
    kappa0, branches = shape
    lhs = kappa0
    for cl in _classes(range(len(branches)),
                       lambda a, b: branches[a][0] == branches[b][0]
                       and branches[a][1] == branches[b][1]
                       and same_hist(branches[a][2], 0, 0, branches[b][2], 0)):
        lhs *= factorial(len(cl))
    rhs = 1
    for g in _classes(range(len(branches)),
                      lambda a, b: (branches[a][0], branches[a][1])
                      == (branches[b][0], branches[b][1])):
        rhs *= factorial(len(g))
    return lhs == rhs


# ---------------------------------------------------------------------------
# polynomial layer over O = Z/p^N, key degree d = 1
# ---------------------------------------------------------------------------

def _polymul(pN, a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % pN
    return out


def taylor(pN, f, w, m):
    return ac2.dev(pN, [(-w) % pN, 1], f, m)


def assemble(pN, w, coeffs):
    out, base, K = [0], [1], [(-w) % pN, 1]
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


def in_cell(F, p, N, f, w, node, with_types=True):
    """`monicPoly a ∈ htCell π (x − w) node` (A-C.2's re-signed three-way law)."""
    m, P = node.m, node.Pceil
    devs = taylor(p ** N, f, w, m)
    nph = [ac2.gauss_val(p, N, a) for a in devs]
    for j in range(m + 1):
        h = nph[j]
        if h is not None and h < P[j]:
            return False
        if ac2.lean_IsVertex(P, m, j) and h != P[j]:
            return False
    if not with_types:
        return True
    for (u, l), lam in node.sides.items():
        r = ac2.side_reads(F, p, N, [(-w) % p ** N, 1], devs, m, u, l)
        if r is None:
            return False
        _, _, _, res = r
        if not res or factor_type(F, ac2.monic_normalize(F, res)) != lam:
            return False
    return True


def enum_cell(F, p, N, w, node, with_types=True):
    pN = p ** N
    m, P = node.m, node.Pceil
    ranges = [range(0, pN, p ** min(P[j], N)) for j in range(m)]
    out = []
    for tup in itertools.product(*ranges):
        f = assemble(pN, w, list(tup) + [1])
        if in_cell(F, p, N, f, w, node, with_types):
            out.append(tuple(f))
    return out


def reps_digit(p, N, offs=None):
    """a SYSTEM OF REPRESENTATIVES of the nonzero residue classes (d = 1): one lift
    per class, `rep[z] ≡ z (mod p)`.  `offs` perturbs the system (used by
    [REP-INDEP])."""
    offs = offs or {}
    return [(z + p * offs.get(z, 0)) % p ** N for z in range(1, p)]


def centers(p, N, wparent, s, reps, spin=True, rep=True):
    """the admissible recentered keys `K = x − w` below `x − wparent`."""
    pN = p ** N
    if rep:
        if s >= N:
            return []
        return [(wparent + r * p ** s) % pN for r in reps]
    if spin:                      # A-C.2's designed s-pin ALONE (finding D5)
        if s >= N:
            return []
        return [(wparent + t) % pN for t in range(0, pN, p ** s)
                if (t // p ** s) % p != 0]
    return [w % pN for w in range(pN)]


# ---------------------------------------------------------------------------
# the A-C.3 refined `htRealizes`, bottom-up
# ---------------------------------------------------------------------------
# realization clauses:
#   CELL — per-node membership `G i ∈ htCell π (K i) (node i)` at the recentered key
#   TYPE — the side-type half of CELL at NON-ROOT nodes (split out for the teeth)
#   SPIN — `gaussVal (K i − K (parent i)) = s_i`
#   REP  — `K (parent i) − K i = π^{s_i} · z̃`, `z̃` a REPRESENTATIVE  [finding D5]
#   DIST — sibling distinctness `gaussVal (K u − K u') = s` for u ≠ u' on one side

def realizing(F, p, N, t, i, w, off, reps, memo):
    """all monic G of degree m_i (d = 1) that realize the subtree at i, at key x − w."""
    key = (i, w)
    if key in memo:
        return memo[key]
    node = t.nodes[i]
    if "CELL" in off:
        base = [tuple(assemble(p ** N, w, list(tp) + [1]))
                for tp in itertools.product(range(p ** N), repeat=node.m)]
    else:
        base = enum_cell(F, p, N, w, node,
                         with_types=not ("TYPE" in off and i != 0))
    ch = t.children(i)
    if not ch:
        memo[key] = base
        return base
    cand = []
    for c in ch:
        lst = []
        for wc in centers(p, N, w, t.nodes[c].s, reps,
                          spin="SPIN" not in off, rep="REP" not in off):
            for Gc in realizing(F, p, N, t, c, wc, off, reps, memo):
                lst.append((Gc, wc))
        cand.append((c, lst))
    pN = p ** N
    out = []
    for G in base:
        if _match(p, N, t, cand, 0, [], list(G), off, pN):
            out.append(G)
    memo[key] = out
    return out


def _match(p, N, t, cand, k, chosen, G, off, pN):
    if k == len(cand):
        # the JOINT divisibility `(∏_u G_u) ∣ G_v`.  Over O this is EQUIVALENT to the
        # signed per-child clause `G u ∣ G v`: distinct sibling centres (DIST) put the
        # clusters' root sets at disjoint distances, so the G_u are pairwise coprime
        # over K and Gauss gives the product; at level N the per-child form is strictly
        # weaker (mod-π^N divisors are not unique), so the joint form is the faithful
        # level-N surrogate and is what is enumerated here.
        P = [1]
        for (_, Gc, _) in chosen:
            P = _polymul(pN, P, list(Gc))
        if len(P) > len(G):
            return False
        _, r = ac2.opoly_divmod(pN, list(G), P)
        return not r
    c, lst = cand[k]
    for (Gc, wc) in lst:
        ok = True
        for (c2, Gc2, wc2) in chosen:
            if "DIST" not in off:
                if Gc == Gc2:
                    ok = False
                    break
                if t.nodes[c].s == t.nodes[c2].s:
                    if ac2.val_p(p, N, (wc - wc2) % pN) != t.nodes[c].s:
                        ok = False
                        break
        if not ok:
            continue
        if len(Gc) - 1 != len(G) - 1:
            _, r = ac2.opoly_divmod(pN, list(G), list(Gc))
            if r:
                continue
        elif list(Gc) != list(G):
            continue
        if _match(p, N, t, cand, k + 1, chosen + [(c, Gc, wc)], G, off, pN):
            return True
    return False


def stratum(F, p, N, t, off=(), reps=None):
    reps = reps if reps is not None else reps_digit(p, N)
    return len(realizing(F, p, N, t, 0, 0, off, reps, {}))


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


def global_stratum(F, p, N, shape, wkeys, off=(), reps=None, sigma=True):
    """#{ level-N classes f : ∃ σ (an assignment of the shape's branch slots to the
    given keys, preserving (d,m)) and ∃ G, f = ∏ G_i with `G_i ≡ Φ_i^{m_i} (mod π)`
    and G_i realizing branch σ(i)'s tree at key Φ_i }."""
    reps = reps if reps is not None else reps_digit(p, N)
    _, branches = shape
    n = len(branches)
    pN = p ** N
    lists = [[realizing(F, p, N, branches[j][2], 0, wkeys[i], off, reps, {})
              for j in range(n)] for i in range(n)]
    perms = [pm for pm in itertools.permutations(range(n))
             if all((branches[pm[i]][0], branches[pm[i]][1])
                    == (branches[i][0], branches[i][1]) for i in range(n))]
    if not sigma:
        perms = [tuple(range(n))]
    out = set()
    for pm in perms:
        for combo in itertools.product(*[lists[i][pm[i]] for i in range(n)]):
            if not all(_residue_ok(p, N, combo[i], wkeys[i], branches[pm[i]][1])
                       for i in range(n)):
                continue
            f = [1]
            for g in combo:
                f = _polymul(pN, f, list(g))
            out.add(tuple(f))
    return len(out)


def _residue_ok(p, N, G, w, m):
    """`(G).map residue = ((x − w).map residue)^m`."""
    pN = p ** N
    tgt = [1]
    for _ in range(m):
        tgt = _polymul(pN, tgt, [(-w) % pN, 1])
    return all((a - b) % p == 0 for a, b in
               itertools.zip_longest(list(G), tgt, fillvalue=0))


# ---------------------------------------------------------------------------
# reporting
# ---------------------------------------------------------------------------

FAIL = 0
CHECKS = 0
DEAD = []


def check(name, cond, detail=""):
    global FAIL, CHECKS
    CHECKS += 1
    if not cond:
        FAIL += 1
    print(f"[{'PASS' if cond else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))
    return cond


# ---------------------------------------------------------------------------
# the instances
# ---------------------------------------------------------------------------

def cen(F):
    return lambda lam: side_census(F, lam)


def law(name, F, p, N, t, expect_clauses_clean=True):
    fc = failing_clauses(t, N)
    if expect_clauses_clean:
        check(f"{name}: clause list clean", not fc, f"failing={fc}")
    fo = htBranchCount(F.Q, cen(F), t, N)
    st = stratum(F, p, N, t)
    check(f"LAW {name}", fo == st, f"formula={fo} stratum={st} q={F.Q} N={N}")
    return fo, st


def T_depth0(p, lam=((2, 1),)):
    return Tree([Node(2, 0, [2, 1, 0], 2, {(1, 1): lam}, 1)], [0])


def T_chain1(lam=((2, 1),)):
    return Tree([Node(2, 0, [2, 1, 0], 2, {(1, 1): ((1, 2),)}, 1),
                 Node(2, 1, [4, 2, 0], 2, {(2, 1): lam}, 1)], [0, 0])


def T_chain2():
    return Tree([Node(2, 0, [2, 1, 0], 2, {(1, 1): ((1, 2),)}, 1),
                 Node(2, 1, [4, 2, 0], 2, {(2, 1): ((1, 2),)}, 1),
                 Node(2, 2, [5, 3, 0], 1, {(5, 2): ((1, 1),)}, 1)], [0, 0, 1])


U_IRR = Node(2, 1, [4, 2, 0], 2, {(2, 1): ((2, 1),)}, 1)
U_E2 = Node(2, 1, [3, 2, 0], 1, {(3, 2): ((1, 1),)}, 1)


def T_branch_same(kappa2):
    root = Node(4, 0, [4, 3, 2, 1, 0], 4, {(1, 1): ((1, 2), (1, 2))}, 2 if kappa2 else 1)
    return Tree([root, U_IRR, U_E2 if kappa2 else U_IRR], [0, 0, 0])


def T_branch_two_sides():
    root = Node(4, 0, [6, 4, 2, 1, 0], 4,
                {(2, 1): ((1, 2),), (1, 1): ((1, 2),)}, 1)
    u2 = Node(2, 2, [6, 3, 0], 2, {(3, 1): ((2, 1),)}, 1)   # on the slope-2 side
    u1 = Node(2, 1, [4, 2, 0], 2, {(2, 1): ((2, 1),)}, 1)   # on the slope-1 side
    return Tree([root, u2, u1], [0, 0, 0])


def T_chain1_m3():
    """root m=3, one triple root at depth 1; leaf residual (linear)·(irreducible
    quadratic) — an m > 2 chain instance."""
    return Tree([Node(3, 0, [3, 2, 1, 0], 3, {(1, 1): ((1, 3),)}, 1),
                 Node(3, 1, [6, 4, 2, 0], 3, {(2, 1): ((1, 1), (2, 1))}, 1)], [0, 0])


def vK(k):
    """the A-C.2 refutation geometry: the one-node tree differing only in `kappa`."""
    return Tree([Node(0, 0, [0], 0, {}, k)], [0])


BR_A = Tree([Node(2, 0, [2, 1, 0], 2, {(1, 1): ((2, 1),)}, 1)], [0])
BR_B = Tree([Node(2, 0, [1, 1, 0], 1, {(1, 2): ((1, 1),)}, 1)], [0])


def main():
    print("=" * 78)
    print("A-C.3 certification: the re-signed C.114 count laws, stratum vs formula")
    print("=" * 78)

    # ---------------- [LAW] depth 0 ----------------
    print("\n-- [LAW] depth-0 trees (the C.109 cell, now inside the tree statement)")
    for p in (2, 3):
        F = ac2.FQ(p)
        law(f"depth0 q={p} m=2 irreducible-quadratic residual", F, p, 5, T_depth0(p))
        t = Tree([Node(1, 0, [2, 0], 1, {(2, 1): ((1, 1),)}, 1)], [0])
        law(f"depth0 q={p} m=1 steep side", F, p, 5, t)

    # ---------------- [LAW] depth-1 chains ----------------
    print("\n-- [LAW] depth-1 chains (one unfractured child; the corpus's own"
          " W12-L0 recovery instance is the q=3 split-residual row)")
    for p, lam in ((2, ((2, 1),)), (3, ((2, 1),)), (3, ((1, 1), (1, 1)))):
        F = ac2.FQ(p)
        law(f"chain1 q={p} leaf-type={lam}", F, p, 5, T_chain1(lam))
    F = ac2.FQ(2)
    law("chain1 q=2 m=3 (triple root, mixed leaf type)", F, 2, 7, T_chain1_m3())

    # ---------------- [LAW] depth-2 chain ----------------
    print("\n-- [LAW] depth-2 chains")
    for p in (2, 3):
        F = ac2.FQ(p)
        law(f"chain2 q={p}", F, p, 6, T_chain2())

    # ---------------- [REP-INDEP] ----------------
    print("\n-- [REP-INDEP] the count does not depend on the representative system"
          " (the corpus's lift-independence claim, certified)")
    p, N = 3, 6
    F = ac2.FQ(p)
    t = T_chain2()
    base = htBranchCount(F.Q, cen(F), t, N)
    vals = [stratum(F, p, N, t, reps=reps_digit(p, N, offs))
            for offs in ({}, {1: 1}, {1: 4, 2: 7}, {1: 26, 2: 13})]
    check("REP-INDEP chain2 q=3: four representative systems agree with the formula",
          all(v == base for v in vals), f"formula={base} strata={vals}")
    check("REP ⟹ the A-C.2 s-pin: every representative recentring has gaussVal = s",
          all(ac2.val_p(3, 6, (w - 0) % 3 ** 6) == s
              for s in (1, 2) for w in centers(3, 6, 0, s, reps_digit(3, 6))))

    # ---------------- [GLOBAL] ----------------
    print("\n-- [GLOBAL] two-branch shapes at distinct branch residues (q=2)")
    p, N = 2, 4
    F = ac2.FQ(p)
    wkeys = [0, 1]                        # residues x and x+1 — DISTINCT
    for kap0, brs, nm in (
            (1, [(1, 2, BR_A), (1, 2, BR_A)], "kappa0=1 (equal histories)"),
            (2, [(1, 2, BR_A), (1, 2, BR_B)], "kappa0=2 (distinct histories)")):
        shape = (kap0, brs)
        check(f"GLOBAL {nm}: κ₀-rule holds", kappa0_rule(shape))
        fo = htGlobalCount(shape, F.Q, [cen(F)] * 2, N)
        st = global_stratum(F, p, N, shape, wkeys)
        check(f"GLOBAL {nm}", fo == st, f"formula={fo} stratum={st}")

    # ---------------- [SEP] the two refutation geometries ----------------
    print("\n-- [SEP] the A-C.2 refutation geometries are separated by the clause list")
    for k in (1, 2):
        fc = failing_clauses(vK(k), 3)
        check(f"SEP kappa-separated one-node tree vK({k}): "
              + ("clause list CLEAN" if k == 1 else "the κ-rule REJECTS it"),
              (fc == []) == (k == 1) and (k == 1 or fc == ["KAPPA"]), f"failing={fc}")
    law("SEP vK(1) (the geometry the re-sign DOES speak about)", ac2.FQ(2), 2, 3, vK(1))
    for k in (1, 2):
        check(f"SEP kappa0-separated empty shape ⟨[],{k}⟩: "
              + ("the κ₀-rule holds" if k == 1 else "the κ₀-rule REJECTS it"),
              kappa0_rule((k, [])) == (k == 1))
    check("SEP empty shape ⟨[],1⟩: formula = stratum = 1",
          htGlobalCount((1, []), 2, [], 4) == 1
          == global_stratum(ac2.FQ(2), 2, 4, (1, []), []))

    # ---------------- [D6] the SOURCE-level finding ----------------
    print("\n-- [D6] FINDING: EFF.W12.85's per-node nonnegativity is FALSE at nodes"
          "\n         whose repeated-linear children EXHAUST the multiplicity"
          " (≥ 2 children).")
    for m, parts, s, lab in ((4, [2, 2], 1, "m=4, two double roots, slope 1"),
                             (6, [2, 2, 2], 1, "m=6, three double roots, slope 1"),
                             (4, [2, 2], 3, "m=4, two double roots, slope 3"),
                             (6, [3, 3], 2, "m=6, two triple roots, slope 2")):
        P = [(m - j) * s for j in range(m + 1)]
        v = Node(m, 0, P, m, {}, 1)
        ok = all(v.B(N) - sum(Node(a, s, [(a - j) * s for j in range(a + 1)], a,
                                   {}, 1).D(N) for a in parts)
                 == -s * (m * m - sum(a * a for a in parts)) // 2
                 for N in range(m * s + 2, m * s + 12))
        check(f"[D6] identity B_v − Σ_u D_u = −s(m² − Σ m_u²)/2 < 0 ({lab})",
              ok and -s * (m * m - sum(a * a for a in parts)) // 2 < 0)
    F3, F2 = ac2.FQ(3), ac2.FQ(2)
    for nm, F, p, N, t in (("q=3 one side, κ=1", F3, 3, 5, T_branch_same(False)),
                           ("q=3 one side, κ=2", F3, 3, 5, T_branch_same(True)),
                           ("q=2 two sides", F2, 2, 7, T_branch_two_sides())):
        fc = failing_clauses(t, N)
        fo = htBranchCount(F.Q, cen(F), t, N)
        st = stratum(F, p, N, t)
        check(f"[D6] measured: exhausting 2-child node ({nm}) fails ONLY the per-node"
              f" inequality, and the law is FALSE there",
              fc == ["HNODE"] and fo != st,
              f"failing={fc} formula={fo} TRUE stratum={st}")
    check("[D6] the hypothesis `hnode` is therefore LOAD-BEARING, not derivable",
          True, "three measured counterexamples above; the signed statement carries it")

    # ---------------- [TOOTH] per-clause mutation teeth ----------------
    print("\n-- [TOOTH] per-clause mutation teeth (a clause with no tooth is DEAD)")
    tooth("WF", "L−1 at the root (the A-C.2 free-`L` disease, inside the tree)",
          F3, 3, 5,
          Tree([Node(2, 0, [2, 1, 0], 1, {(1, 1): ((1, 2),)}, 1), U_IRR], [0, 0]),
          ("WF",))
    tooth("CONS", "child polygon under its conservative floor", F3, 3, 5,
          Tree([T_chain1().nodes[0], Node(2, 1, [2, 1, 0], 2, {(1, 1): ((2, 1),)}, 1)],
               [0, 0]), ("CONS",))
    tooth("COMPL", "a child at a depth that is NOT a side slope of its parent", F2, 2, 6,
          Tree([Node(2, 0, [2, 1, 0], 2, {(1, 1): ((1, 2),)}, 1),
                Node(2, 2, [5, 3, 0], 1, {(5, 2): ((1, 1),)}, 1)], [0, 0]), ("COMPL",))
    tooth("KAPPA", "kappa=2 on a childless node (the A-C.2 refutation geometry)",
          F3, 3, 5, Tree([Node(2, 0, [2, 1, 0], 2, {(1, 1): ((2, 1),)}, 2)], [0]),
          ("KAPPA",))
    tooth("VIS", "child polygon outside the window (N=4)", F3, 3, 4,
          T_chain1(((2, 1),)), ("VIS",))
    tooth("HNODE", "exhausting 2-child node (finding D6)", F3, 3, 5,
          T_branch_same(False), ("HNODE",))

    # REP  (finding D5)
    t = T_chain2()
    fo = htBranchCount(F3.Q, cen(F3), t, 6)
    st = stratum(F3, 3, 6, t, off=("REP",))
    check("[D5] TOOTH REP: A-C.2's s-pin ALONE (∃ over every lift) breaks the law",
          st != fo, f"formula={fo} stratum(no REP)={st}")
    t1 = T_chain1(((1, 1), (1, 1)))
    fo1 = htBranchCount(F3.Q, cen(F3), t1, 5)
    st1 = stratum(F3, 3, 5, t1, off=("REP",))
    check("[D5] TOOTH REP (depth 1, split leaf residual): the same failure one level up",
          st1 != fo1, f"formula={fo1} stratum(no REP)={st1}")

    # TYPE (the non-root side-type pin)
    t = T_chain1(((2, 1),))
    fo = htBranchCount(F3.Q, cen(F3), t, 5)
    st = stratum(F3, 3, 5, t, off=("TYPE",))
    check("TOOTH TYPE: dropping the non-root side-type pin breaks the law",
          st != fo, f"formula={fo} stratum(no TYPE)={st}")

    # SPIN — subsumed by REP, and with REP off it is the D5 tooth; report the status
    t = T_chain1(((2, 1),))
    fo = htBranchCount(F3.Q, cen(F3), t, 5)
    st = stratum(F3, 3, 5, t, off=("SPIN", "REP"))
    if st == fo:
        DEAD.append(("SPIN", "subsumed by REP (a representative recentring has "
                     "gaussVal = s by construction); no independent tooth in this grid"))
    check("SPIN status: subsumed by REP (reported, not silently kept)", True,
          f"formula={fo} stratum(no SPIN, no REP)={st}")

    # DIST — only bites at multi-child nodes, i.e. in the D6-excluded regime
    t = T_branch_same(False)          # two IDENTICAL children: without DIST one
    fo_d = stratum(F3, 3, 5, t)       # cluster can serve both slots
    st_d = stratum(F3, 3, 5, t, off=("DIST",))
    if st_d == fo_d:
        DEAD.append(("DIST", "SUBSUMED in this grid by the parent's side-TYPE pin "
                     "(distinct residual roots ⇒ distinct centres ⇒ distinct "
                     "clusters); reachable multi-child geometries are exhausting, "
                     "where a shared cluster forces f = G² and leaves the type pin "
                     "unsatisfiable.  Retained on source grounds (EFF.W12.85 step 4: "
                     "\"its repeated roots are distinguished by their values\") and "
                     "for the NON-exhausting regime, which is out of brute-force "
                     "range"))
    check("DIST status: subsumed in this grid (reported, not silently kept)", True,
          f"true stratum={fo_d} stratum(no DIST)={st_d}")

    # FENCE
    fen = Tree([Node(4, 0, [4, 3, 2, 1, 0], 4, {(1, 1): ((2, 2),)}, 1)], [0])
    fc = failing_clauses(fen, 5)
    fo = htBranchCount(F3.Q, cen(F3), fen, 5)
    st = stratum(F3, 3, 5, fen)
    check("FENCE instance fails exactly the fence", fc == ["FENCE"], f"failing={fc}")
    if st == fo:
        DEAD.append(("FENCE", f"repeated degree-2 residual: stratum={st} = formula "
                     f"(a SCOPE fence, retained on source grounds)"))
    check("FENCE status: reported (scope fence, no truth tooth in this grid)", True,
          f"formula={fo} stratum={st}")

    # GLOBAL teeth
    p, N = 2, 4
    F = ac2.FQ(p)
    shape2 = (2, [(1, 2, BR_A), (1, 2, BR_B)])
    fo = htGlobalCount(shape2, F.Q, [cen(F)] * 2, N)
    check("TOOTH SIGMA: dropping the branch-assignment ∃ breaks the κ₀ law",
          global_stratum(F, p, N, shape2, [0, 1], sigma=False) != fo,
          f"formula={fo} stratum(no σ)="
          f"{global_stratum(F, p, N, shape2, [0, 1], sigma=False)}")
    shape_bad = (1, [(1, 2, BR_A), (1, 2, BR_B)])
    check("TOOTH KAPPA0: κ₀=1 where the rule demands 2 breaks the law",
          not kappa0_rule(shape_bad)
          and htGlobalCount(shape_bad, F.Q, [cen(F)] * 2, N)
          != global_stratum(F, p, N, shape2, [0, 1]),
          f"formula(bad κ₀)={htGlobalCount(shape_bad, F.Q, [cen(F)] * 2, N)} "
          f"stratum={global_stratum(F, p, N, shape2, [0, 1])}")
    shape1 = (1, [(1, 2, BR_A), (1, 2, BR_A)])
    fo1 = htGlobalCount(shape1, F.Q, [cen(F)] * 2, N)
    st_same = global_stratum(F, p, N, shape1, [0, 2])   # SAME residue x on both keys
    check("TOOTH DISTINCT-RESIDUES: two branches at the same residue break the law",
          st_same != fo1, f"formula={fo1} stratum(same residue)={st_same}")

    print("\n" + "=" * 78)
    for nm, why in DEAD:
        print(f"[DEAD/SUBSUMED] clause {nm}: {why}")
    print(f"RESULT: {CHECKS} checks, {FAIL} failures"
          + (f", {len(DEAD)} clause(s) flagged" if DEAD else ""))
    return 1 if FAIL else 0


def tooth(clause, why, F, p, N, t, expect_failing):
    """a mutation tooth: the tree violates exactly `expect_failing`, and on it the
    formula and the true stratum DISAGREE (so the clause is load-bearing)."""
    fc = failing_clauses(t, N)
    check(f"TOOTH {clause} ({why}): violates exactly {list(expect_failing)}",
          sorted(fc) == sorted(expect_failing), f"failing={fc}")
    fo = htBranchCount(F.Q, cen(F), t, N)
    st = stratum(F, p, N, t)
    if fo != st:
        check(f"TOOTH {clause} ({why}): KILLS the law", True,
              f"formula={fo} stratum={st}")
    else:
        DEAD.append((clause, f"{why}: stratum={st} = formula"))
        check(f"TOOTH {clause} ({why}): NO TOOTH — reported as DEAD WEIGHT", True,
              f"formula={fo} stratum={st}")


if __name__ == "__main__":
    sys.exit(main())
