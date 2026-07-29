#!/usr/bin/env python3
"""ESCAPE-probe layer (a) -- the SYMBOLIC CLOSED-CLASS REFUTER (E0's genuine falsifier).

Charge (MOVES_2026-07-24.md PROBE ROSTER (a), ~L12220): from the sealed active kernel
at q = p, build A's directed transition graph and its strongly-connected components;
any CLOSED class -- TOTAL ROW MASS INSIDE THE CLASS = 1 on every member, i.e. zero
one-step terminal mass AND zero branching/split exit mass AND no A-edges leaving
(rev 2 / pass-1 finding 7: split mass is an exit appearing as a ROW DEFICIT, never as
an A-column or terminal column) -- refutes E0 at that p OUTRIGHT (row-stochastic on the
class, hence rho(A) = 1), finitely and conclusively.

KERNEL SOURCE (corpus transition tables): MOVES_2026-07-24.md SS-RESUM S1 (the sealed
n = 3 block solve; gate RESUM-n3 PASSED 2026-07-27, CASE_RESUMN3_SEALED_PREDICTIONS.md)
built on the SV-TABLES V.6.1-V.6.3 rosters = lean/LeanUrat/MovesV/DefsGate.lean closed
forms (TH3/TH12/TH3c/T21/T3; Tsplit/Tinert/Tdbl/Tw2/Tvv). K-columns = the (c=1, m=1)
outcomes ONLY (same-size single-child): blk2 m2/o_double, blk3 A/triple. The split legs
(A dbl+simple, C_even double, D_even double) are ROW-DEFICIT exits toward blk2 entries.

SCOPE (the probe narrows no quantifier of E0 -- per-pool q0 = p^delta, CL-1): pools
q0 = p, delta = 1, p in {2,3,5,7}, n in {2,3}. "No closed class" leaves E0 OPEN;
a closed class would REFUTE it at that p.
"""
import sys
from fractions import Fraction as F
import sympy as sp

q = sp.symbols('q')
D3s, D6s = q**3 - 1, q**6 - 1
FINDINGS = []
def chk(name, cond, detail=""):
    tag = "PASS" if cond else "FINDING"
    if not cond: FINDINGS.append(name)
    print(f"[{tag}] {name}  {detail}")

# ---- the resummed row tables (S1; heights summed geometrically, entry-conditional) ----
# cell = (name, resummed symbolic mass, type, target); types: TERM / SPLIT(exit) / KCOL
BLK2 = [
    ("m2.o_split",  ((q-1)*(q-2)/2) / D3s, "TERM",  None),
    ("m2.o_inert",  (q*(q-1)/2)     / D3s, "TERM",  None),
    ("m2.o_double", (q-1)           / D3s, "KCOL",  "blk2"),
    ("m_w2",        (q-1)*q**2      / D3s, "TERM",  None),
    ("m_vv",        (q-1)           / D3s, "TERM",  None),
]
BLK3 = [
    ("A.3dist",     ((q-1)*(q-2)*(q-3)/6) / D6s, "TERM",  None),
    ("A.linquad",   (q*(q-1)**2/2)        / D6s, "TERM",  None),
    ("A.irr",       ((q**3-q)/3)          / D6s, "TERM",  None),
    ("A.dblsimple", ((q-1)*(q-2))         / D6s, "SPLIT", "blk2"),
    ("A.triple",    (q-1)                 / D6s, "KCOL",  "blk3"),
    ("B",           ((q-1)*(q**5+q**3))   / D6s, "TERM",  None),
    ("C_odd",       ((q-1)*q**4)          / D6s, "TERM",  None),
    ("C_even.dist", ((q-1)*(q-2)/2)       / D6s, "TERM",  None),
    ("C_even.irr",  (q*(q-1)/2)           / D6s, "TERM",  None),
    ("C_even.dbl",  (q-1)                 / D6s, "SPLIT", "blk2"),
    ("D_odd",       ((q-1)**2*q**2)   / (D3s*D6s), "TERM",  None),
    ("D_even.dist", ((q-1)**2*(q-2)/2)/ (D3s*D6s), "TERM",  None),
    ("D_even.irr",  (q*(q-1)**2/2)    / (D3s*D6s), "TERM",  None),
    ("D_even.dbl",  ((q-1)**2)        / (D3s*D6s), "SPLIT", "blk2"),
    ("E",           ((q-1)**2)        / (D3s*D6s), "TERM",  None),
]
ROOT = [  # initial vector (V.6.1 / DefsGate root roster), masses over pool q^3
    ("root.m_H3",   (q*(q-1)*(q-2)/6) / q**3, "TERM", None),
    ("root.m_H12",  (q**2*(q-1)/2)    / q**3, "TERM", None),
    ("root.m_H<3>", ((q**3-q)/3)      / q**3, "TERM", None),
    ("root.m_2+1",  (q*(q-1))         / q**3, "ENTRY", "blk2"),
    ("root.m_3",    q                 / q**3, "ENTRY", "blk3"),
]

print("=" * 72)
print("0. Symbolic guards: the resummed rows are honest probability rows")
print("=" * 72)
# m_w2 resummation displayed: sum_{k0 odd>=1} (q-1) q^{-(3k0-1)/2}; with k0 = 2j+1
# the summand is (q-1) q^{-(3j+1)}: first term a = (q-1)/q, ratio r = q^{-3} (geometric,
# |r| < 1 at every pool q0 >= 2), so the sum is a/(1-r).
j = sp.symbols('j', integer=True, nonnegative=True)
summand = (q-1)*q**(-sp.Rational(1,2)*(3*(2*j+1)-1))
a_ = summand.subs(j, 0); r_ = sp.simplify(summand.subs(j, j+1)/summand)
chk("m_w2 summand: a = (q-1)/q, ratio = q^-3 (geometric)",
    sp.simplify(a_ - (q-1)/q) == 0 and sp.simplify(r_ - q**-3) == 0)
chk("m_w2 geometric resummation a/(1-r) = (q-1)q^2/(q^3-1)",
    sp.simplify(a_/(1-r_) - (q-1)*q**2/D3s) == 0)
chk("blk2 row sum = 1 identically", sp.simplify(sum(e for _, e, _, _ in BLK2) - 1) == 0)
chk("blk3 row sum = 1 identically", sp.simplify(sum(e for _, e, _, _ in BLK3) - 1) == 0)
chk("root vector sum = 1 identically", sp.simplify(sum(e for _, e, _, _ in ROOT) - 1) == 0)
k2 = (q-1)/D3s; k3 = (q-1)/D6s
chk("kappa_2 = 1/(q^2+q+1)", sp.simplify(k2 - 1/(q**2+q+1)) == 0)
chk("det(I-K_2) = q(q+1)/(q^2+q+1)", sp.simplify((1-k2) - q*(q+1)/(q**2+q+1)) == 0)
chk("det(I-K_3) = (q^6-q)/(q^6-1)", sp.simplify((1-k3) - (q**6-q)/(q**6-1)) == 0)

def ev(expr, p):  # exact Fraction evaluation
    r = sp.Rational(sp.nsimplify(expr.subs(q, p)))
    return F(int(r.p), int(r.q))

print("=" * 72)
print("1. Sealed pool values (RESUM-n3 S3/S4) + tame extensions p = 5, 7")
print("=" * 72)
sealed = {2: (F(1,7), F(6,7), F(1,63), F(62,63), F(8,441)),
          3: (F(1,13), F(12,13), F(1,364), F(363,364), F(27,4732)),
          4: (F(1,21), F(20,21), F(1,1365), F(1364,1365), F(64,28665))}
Jexpr = ((q-1)*(q-2)+(q-1))/D6s + (q-1)**2/(D3s*D6s)
for p in (2, 3, 4):
    got = (ev(k2,p), ev(1-k2,p), ev(k3,p), ev(1-k3,p), ev(Jexpr,p))
    chk(f"q0={p}: (K_2, det, K_3, det, J) match sealed", got == sealed[p], f"{got}")
for p in (5, 7):
    print(f"       q0={p} (recorded): K_2={ev(k2,p)}, K_3={ev(k3,p)}, J={ev(Jexpr,p)}")

print("=" * 72)
print("2. Active-cell scan vs the sealed S3 entry-vanishing list")
print("=" * 72)
SEALED_VANISH = {2: {"root.m_H3", "m2.o_split", "A.3dist", "A.dblsimple",
                     "C_even.dist", "D_even.dist"},
                 3: {"A.3dist"}, 5: set(), 7: set()}
for p in (2, 3, 5, 7):
    dead = {nm for nm, e, _, _ in ROOT + BLK2 + BLK3 if ev(e, p) == 0}
    chk(f"p={p}: vanishing cells == sealed list", dead == SEALED_VANISH[p],
        f"dead={sorted(dead)}")

print("=" * 72)
print("3. THE REFUTER: SCC scan + closed-class test, per (p, n)")
print("=" * 72)
def tarjan(nodes, adj):
    idx, low, onstk, stk, out, cnt = {}, {}, set(), [], [], [0]
    def strong(v):
        idx[v] = low[v] = cnt[0]; cnt[0] += 1
        stk.append(v); onstk.add(v)
        for w in adj.get(v, ()):
            if w not in idx:
                strong(w); low[v] = min(low[v], low[w])
            elif w in onstk:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = set()
            while True:
                w = stk.pop(); onstk.discard(w); comp.add(w)
                if w == v: break
            out.append(comp)
    for v in nodes:
        if v not in idx: strong(v)
    return out

for p in (2, 3, 5, 7):
    for n in (2, 3):
        states = ["blk2"] if n == 2 else ["blk2", "blk3"]
        rows = {"blk2": BLK2, "blk3": BLK3}
        A, term, splitx = {}, {}, {}
        for s in states:
            A[s], term[s], splitx[s] = {}, F(0), F(0)
            for nm, e, ty, tgt in rows[s]:
                m = ev(e, p)
                if m == 0: continue          # inactive cell: dropped (ACTIVE kernel)
                if ty == "KCOL": A[s][tgt] = A[s].get(tgt, F(0)) + m
                elif ty == "SPLIT": splitx[s] += m   # row-deficit exit
                else: term[s] += m
        adj = {s: [t for t in A[s] if t in states] for s in states}
        sccs = tarjan(states, adj)
        refuted = False
        for comp in sccs:
            closure = {s: sum((A[s].get(t, F(0)) for t in comp), F(0)) for s in comp}
            closed = all(c == 1 for c in closure.values())
            if closed: refuted = True
            print(f"   p={p} n={n} SCC {sorted(comp)}: in-class row mass "
                  f"{ {s: str(c) for s, c in closure.items()} } -> "
                  f"{'CLOSED' if closed else 'open (row deficit > 0)'}")
        rho = max(sum(A[s].values(), F(0)) for s in states)  # A diagonal here: rho = max row sum
        chk(f"p={p} n={n}: NO closed class (E0 not refuted at this pool)", not refuted,
        f"max A-row mass rho(A) <= {rho} < 1; exits: " +
        "; ".join(f"{s}: term={term[s]}, split={splitx[s]}" for s in states))
        assert rho < 1

print("=" * 72)
n_f = len(FINDINGS)
if n_f == 0:
    print("ESCAPE-PROBE-A VERDICT: ALL PASS -- no closed class at any tested pool; "
          "E0 UNREFUTED (and still OPEN: per-pool q0 = p^delta quantifier untouched)")
else:
    print(f"ESCAPE-PROBE-A VERDICT: {n_f} FINDING(S): {FINDINGS}")
sys.exit(0 if n_f == 0 else 1)
