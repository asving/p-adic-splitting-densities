# Falsifier for the REPAIRED npVertices_stable_of_hull_preserved + sub-lemmas.
# Mirrors lean/LeanUrat/OM/NewtonPolygon.lean definitions EXACTLY.
from fractions import Fraction as F
from itertools import product
import random

def pairSlope(P, R):
    d = F(R[0]) - F(P[0])
    if d == 0: return F(0)          # Lean junk-0 (Rat division by zero = 0)
    return (F(R[1]) - F(P[1])) / d

def pairLine(P, R, x):
    return F(P[1]) + pairSlope(P, R) * (x - F(P[0]))

def validLines(S):
    out = []
    for P in S:
        for R in S:
            if all(pairLine(P, R, F(Q[0])) <= F(Q[1]) for Q in S):
                out.append((P, R))
    return out

def npHeight(S, x):
    return max(pairLine(P, R, x) for (P, R) in validLines(S))

def hullAbscissae(S):
    dots = [P for P in S if F(P[1]) == npHeight(S, F(P[0]))]
    return sorted(set(P[0] for P in dots))

def hullDotAt(S, i):
    h = npHeight(S, F(i))
    # floor.toNat
    import math
    return (i, max(0, math.floor(h)))

def npVerticesFull(S):
    return [hullDotAt(S, i) for i in hullAbscissae(S)]

def collinear3(A, B, C):
    return (B[0]-A[0])*(C[1]-A[1]) == (C[0]-A[0])*(B[1]-A[1])

def dropCollinear(l):
    if len(l) <= 2: return list(l)
    a = l[0]
    tail = dropCollinear(l[1:])
    if len(tail) >= 2:
        b, c = tail[0], tail[1]
        if collinear3(a, b, c):
            return [a] + tail[1:]
        return [a] + tail
    return [a] + tail

def npVertices(S):
    return dropCollinear(npVerticesFull(S))

def check_instance(S, Sp):
    """S, Sp nonempty sets of (nat,nat). Returns violation string or None."""
    V_p = npVertices(sorted(Sp))
    # hpres
    if not all(P in S for P in V_p): return None
    # habove
    if not all(npHeight(sorted(Sp), F(P[0])) <= F(P[1]) for P in S): return None
    # habs
    absp = set(Q[0] for Q in Sp)
    if not all(P[0] in absp for P in S): return None
    V_s = npVertices(sorted(S))
    if V_s != V_p:
        return f"VIOLATION S={sorted(S)} S'={sorted(Sp)} vS={V_s} vS'={V_p}"
    return "ok"

random.seed(0)
n_checked = 0
n_applicable = 0
for trial in range(4000):
    # random S' then S built to satisfy-ish hypotheses (random; hyp re-checked)
    nabs = random.randint(1, 5)
    absc = random.sample(range(0, 7), nabs)
    Sp = set()
    for a in absc:
        for _ in range(random.randint(1, 2)):
            Sp.add((a, random.randint(0, 4)))
    Sp = sorted(Sp)
    Vp = npVertices(Sp)
    # S: vertices of S' + random dots at S'-abscissae with heights >= hull
    S = set(Vp)
    for _ in range(random.randint(0, 4)):
        a = random.choice([q[0] for q in Sp])
        h = npHeight(Sp, F(a))
        import math
        lo = math.ceil(h)
        S.add((a, lo + random.randint(0, 3)))
    r = check_instance(sorted(S), Sp)
    n_checked += 1
    if r == "ok": n_applicable += 1
    elif r is not None:
        print(r); break
else:
    print(f"repaired statement: {n_applicable} applicable instances, 0 violations (of {n_checked} trials)")

# sub-lemma: survivor-corner — dropCollinear output on sorted input has no collinear consecutive triple
bad = 0; tot = 0
random.seed(1)
for trial in range(4000):
    n = random.randint(3, 8)
    xs = sorted(random.sample(range(0, 12), n))
    l = [(x, random.randint(0, 5)) for x in xs]
    d = dropCollinear(l)
    tot += 1
    for i in range(len(d) - 2):
        if collinear3(d[i], d[i+1], d[i+2]):
            bad += 1
            print("CORNER VIOLATION", l, d); break
print(f"survivor-corner: {tot} sorted lists, {bad} violations")
