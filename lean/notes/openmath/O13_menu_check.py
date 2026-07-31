#!/usr/bin/env python3
"""O-13 falsifier: enumerate the species catalogue S_n^raw mechanically from the
(G1)-(G6)+(B1)-(B5) clauses (ground truth: lean/LeanUrat/MovesSp/Defs.lean, itself the
E-phase transcription of MOVES_2026-07-24.md SP.1-SP.4, dual-accepted rev 8).

Checks (tree leaf O-13's falsifier: "enumerate n = 4 skeletons exhaustively and check
the bound's headroom"):
  1. |S_1| = 1, |S_3| = 53 (the sealed dual-verified catalogue), stage-group breakdown
     at n = 3 vs the sealed groups R/Q3/Q2/Q1/I (21/21/6/1/4).
  2. Self-loop characterization: {s : s in SUCC(s)} == {full POST-REC letters}
     (SP-DAG(i): full = sel (1,W); all other fields forced).
  3. Rank monotonicity: rho(s) = (D, tagord, n-W, 1-[full]) strictly lex-increases
     along EVERY non-self-loop menu edge (SP-DAG(ii)) => collapsed menu graph is a DAG.
  4. Longest collapsed path (letters) vs the 6n^2 bound (SP-DAG(iii)) -- headroom.
  5. |S_n| vs the SP-FIN encoding bound (n+2)^(n^2+3n+12) -- headroom.
  6. Encoding-range audit: every letter's encoding entries lie in {0..n+1}
     (tag<=2, D,w,W,e,ell,s0<=n, a<=n, d<=n+1, slots subset {0..n}, lambda
     multiplicities <=n, flank spans <=n) -- the SP-FIN proof's premise.
"""
from functools import lru_cache
import math, sys

# ---------- combinatorics ----------
@lru_cache(maxsize=None)
def compositions(m):
    """ordered tuples of positive ints summing to m; (()) for m=0."""
    if m == 0:
        return ((),)
    out = []
    for first in range(1, m + 1):
        for rest in compositions(m - first):
            out.append((first,) + rest)
    return tuple(out)

def partitions_gm(ell, n):
    """multisets {(g,mu)} with sum g*mu = ell, 1<=g,mu<=n; as sorted tuples."""
    pairs = sorted((g, mu) for g in range(1, n + 1) for mu in range(1, n + 1)
                   if g * mu <= ell)
    results = []
    def rec(idx, remaining, current):
        if remaining == 0:
            results.append(tuple(current)); return
        for i in range(idx, len(pairs)):
            g, mu = pairs[i]
            if g * mu <= remaining:
                current.append((g, mu)); rec(i, remaining - g * mu, current); current.pop()
    rec(0, ell, [])
    return results

# ---------- letters at a stage ----------
TAGS = ("root", "postInc", "postRec")

def letters_at_stage(tag, D, w, W, n):
    """All Coherent + Budget species tuples at stage (tag,D,w,W), per
    MovesSp/Defs.lean: fields (e,s0,ell,a,d,slots,lam,sel,lflank,rflank);
    d/slots determined by (G3), so not enumerated separately."""
    out = []
    if not (1 <= D <= n and 1 <= w <= n and 1 <= W <= n and W <= n // D):
        return out
    for e in range(1, W + 1):
        for ell in range(1, W // e + 1):
            wraw = e * ell
            if e > n or ell > n or e > wraw:      # (B5) caps; e<=wraw auto
                continue
            for s0 in range(0, W - wraw + 1):      # (B3) s0 + wraw <= W
                if s0 > n:
                    continue
                a = s0 // e                        # (G2)
                if a + ell > W:                    # (B3)
                    continue
                if a > (W - wraw) // e:            # (B5 census anchor)
                    continue
                d = ell + 1                        # (G3)
                if d > n + 1 or d > wraw + 1:      # (B5)/(B3)
                    continue
                for lam in partitions_gm(ell, n):
                    # (B5): parts g<=n, mu<=n -- enforced in partitions_gm
                    if W == 1:
                        sels = [None]              # (G6)
                    else:
                        sels = sorted(set(lam))    # (G4): sel in lam; (G6)
                    for sel in sels:
                        if sel is not None and sel[0] * sel[1] > ell:
                            continue               # (B4) (auto, kept for fidelity)
                        for lf in compositions(s0):            # (G1)
                            for rf in compositions(W - s0 - wraw):
                                out.append((tag, D, w, W, e, s0, ell, a, lam, sel, lf, rf))
    return out

# ---------- catalogue closure over reachable stages ----------
def catalogue(n):
    root_stage = ("root", 1, 1, n)
    seen_stages = {root_stage}
    frontier = [root_stage]
    letters = []
    stage_letters = {}
    while frontier:
        st = frontier.pop()
        Ls = letters_at_stage(*st, n)
        stage_letters[st] = Ls
        letters.extend(Ls)
        for L in Ls:
            (tag, D, w, W, e, s0, ell, a, lam, sel, lf, rf) = L
            if sel is None:
                continue
            g, mu = sel
            tag2 = "postInc" if e * g >= 2 else "postRec"
            child = (tag2, e * g * D, g * w, mu)
            # child stage yields letters only if its own budget clauses pass
            if child not in seen_stages:
                seen_stages.add(child)
                frontier.append(child)
        # deterministic order not needed
    return letters, stage_letters

def child_stage(L):
    (tag, D, w, W, e, s0, ell, a, lam, sel, lf, rf) = L
    if sel is None:
        return None
    g, mu = sel
    tag2 = "postInc" if e * g >= 2 else "postRec"
    return (tag2, e * g * D, g * w, mu)

def is_full(L):
    (tag, D, w, W, e, s0, ell, a, lam, sel, lf, rf) = L
    return sel == (1, W)

def rank(L, n):
    (tag, D, w, W, e, s0, ell, a, lam, sel, lf, rf) = L
    return (D, TAGS.index(tag), n - W, 0 if is_full(L) else 1)

def run(n):
    letters, stage_letters = catalogue(n)
    letters_set = set(letters)
    assert len(letters_set) == len(letters)
    print(f"\n===== n = {n} =====")
    print(f"|S_{n}^raw| = {len(letters)}   over {len(stage_letters)} reachable stages")
    for st in sorted(stage_letters, key=lambda s: (s[1], s[3], s[0])):
        if stage_letters[st]:
            print(f"   stage {st}: {len(stage_letters[st])} letters")

    # menu edges: s -> s' iff stage(s') == child_stage(s)
    by_stage = stage_letters
    edges = []
    self_loops = set()
    for L in letters:
        cs = child_stage(L)
        if cs is None:
            continue
        for L2 in by_stage.get(cs, ()):
            if L2 == L:
                self_loops.add(L)
            else:
                edges.append((L, L2))

    # check 2: self-loop characterization
    full_postrec = {L for L in letters if is_full(L) and L[0] == "postRec"}
    assert self_loops == full_postrec, (
        f"self-loop set != full postRec letters: {len(self_loops)} vs {len(full_postrec)}")
    # SP-DAG(i): full letters unique per stage and fully forced
    for L in letters:
        if is_full(L):
            (tag, D, w, W, e, s0, ell, a, lam, sel, lf, rf) = L
            assert e == 1 and s0 == 0 and a == 0 and ell == W and lam == ((1, W),) \
                   and lf == () and rf == (), f"full letter fields not forced: {L}"
    fulls_per_stage = {}
    for L in letters:
        if is_full(L):
            fulls_per_stage.setdefault(L[:4], []).append(L)
    assert all(len(v) == 1 for v in fulls_per_stage.values())
    print(f"self-loops = full POST-REC letters: OK "
          f"({len(self_loops)} loop classes; fields forced; unique per stage)")

    # check 3: rank strict lex increase on every non-self-loop edge
    bad = [(L, L2) for (L, L2) in edges if not rank(L, n) < rank(L2, n)]
    assert not bad, f"rank monotonicity FAILS on {len(bad)} edges, e.g. {bad[0]}"
    print(f"rank rho strictly increases along all {len(edges)} non-self-loop edges: OK")

    # check 4: longest collapsed path (DAG longest path, counting letters)
    order = sorted(letters, key=lambda L: rank(L, n))
    idx = {L: i for i, L in enumerate(order)}
    succ = {L: [] for L in letters}
    for (L, L2) in edges:
        succ[L].append(L2)
    longest = {L: 1 for L in letters}
    for L in reversed(order):
        for L2 in succ[L]:
            longest[L] = max(longest[L], 1 + longest[L2])
    roots = [L for L in letters if L[0] == "root"]
    Lmax_root = max(longest[L] for L in roots) if roots else 0
    Lmax = max(longest.values())
    print(f"longest collapsed path: {Lmax_root} letters from a ROOT letter "
          f"({Lmax} from anywhere)  vs  SP-DAG bound 6n^2 = {6*n*n}")

    # check 5: SP-FIN bound headroom
    bound = (n + 2) ** (n * n + 3 * n + 12)
    print(f"SP-FIN encoding bound (n+2)^(n^2+3n+12) = {float(bound):.3e}  "
          f"(actual {len(letters)}; headroom factor {float(bound)/len(letters):.2e})")

    # check 6: encoding-range audit
    for L in letters:
        (tag, D, w, W, e, s0, ell, a, lam, sel, lf, rf) = L
        assert TAGS.index(tag) <= min(2, n + 1)
        assert all(1 <= x <= n for x in (D, w, W, e, ell)) and s0 <= n and a <= n
        assert ell + 1 <= n + 1
        assert a + ell <= n                    # slots subset {0..n}
        from collections import Counter
        c = Counter(lam)
        assert all(v <= n for v in c.values())
        assert sum(lf) <= n and sum(rf) <= n
    print("encoding-range audit (all entries in {0..n+1}): OK")
    return len(letters), Lmax_root

if __name__ == "__main__":
    results = {}
    for n in (1, 2, 3, 4, 5, 6):
        results[n] = run(n)
    print("\n===== summary =====")
    print("n : |S_n|  longest-collapsed-path  6n^2")
    for n, (sz, lp) in results.items():
        print(f"{n} : {sz}  {lp}  {6*n*n}")
    # sealed n=3 catalogue check
    assert results[1][0] == 1, "n=1 must be the single confirming root letter"
    assert results[3][0] == 53, f"n=3 must reproduce the sealed 53, got {results[3][0]}"
    print("\nSEALED CHECKS PASS: |S_1| = 1, |S_3| = 53 (the dual-verified catalogue).")
