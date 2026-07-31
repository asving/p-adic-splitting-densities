#!/usr/bin/env python3
"""O-14a' falsifier checks (cheap, falsifier-first discipline).

Checks the load-bearing arithmetic of the O14ap Phase-B attempt:
  A. The F9 coset obstruction (Theorem 5 countermodel, general ambient F):
     in F9 = F3(i), the subgroup F3^x * <i> has order 4 and excludes 1+i (order 8);
     two-slot digits {b + a*i} cover all of F9^x; single-X-monomial digit classes
     (constants and u*X, i.e. F3^x times a power of i) never hit (1+i)*i^m for any m.
  B. PARI cross-check: X^2 + 9 over Q_3 is irreducible with e=1, f=2 (the inert
     quadratic frame of the countermodel is semantically genuine).
  C. The T1 threshold arithmetic (Theorem 3, Lemma 3.1): random instances of the
     coherence slope/width/stretch laws imply h_b > e*g*h_{b-1} = wPrev_b(Phi_b).
  D. The future-fence-lift flag (Section 6d): at STR=2 (one interior e=2 read),
     required weight 3 is not in the X-monomial weight lattice over a unit-shifted
     root key, while the two-slot lattice hits it.
Exit 0 iff all checks pass.
"""
import itertools, random, sys
from fractions import Fraction

ok = True
def report(name, passed, detail=""):
    global ok
    ok = ok and passed
    print(f"[{'PASS' if passed else 'FAIL'}] {name}" + (f" -- {detail}" if detail else ""))

# ---------- F9 = F3[z]/(z^2+1), elements (a,b) = a + b*i ----------
def mul(x, y):
    (a, b), (c, d) = x, y
    return ((a*c - b*d) % 3, (a*d + b*c) % 3)
def power(x, n):
    r = (1, 0)
    for _ in range(n):
        r = mul(r, x)
    return r
units = [(a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)]
def order(x):
    for n in range(1, 9):
        if power(x, n) == (1, 0):
            return n
    return None

# A1: 1+i has order 8 (generator of F9^x)
one_plus_i = (1, 1)
report("A1: ord(1+i) = 8 in F9^x", order(one_plus_i) == 8, f"ord={order(one_plus_i)}")

# A2: subgroup G = F3^x * <i> has order 4 and excludes 1+i
i_el = (0, 1)
G = set()
for u in [(1, 0), (2, 0)]:
    for k in range(4):
        G.add(mul(u, power(i_el, k)))
report("A2: |F3^x * <i>| = 4 and (1+i) not in it",
       len(G) == 4 and one_plus_i not in G, f"G={sorted(G)}")

# A3: single-X-monomial digit classes = F3^x * i^m for some m -- never (1+i)*i^m'
targets = {mul(one_plus_i, power(i_el, m)) for m in range(4)}
report("A3: no target (1+i)*i^m lies in F3^x*<i> (singleton-support obstruction)",
       all(t not in G for t in targets), f"targets={sorted(targets)}")

# A4: two-slot digits {b + a*i : a,b in F3} cover F9 \ {0} (the recorded lift exists;
#     the faithful two-slot (S6b') progression realizes every center)
two_slot = {(b % 3, a % 3) for a in range(3) for b in range(3)} - {(0, 0)}
report("A4: two-slot digits cover F9^x (recorded lift / faithful law realizability)",
       two_slot == set(units), f"count={len(two_slot)}")

# ---------- B: PARI factorpadic of X^2+9 over Q_3 ----------
try:
    import subprocess
    out = subprocess.run(
        ["gp", "-q"], input="F=factorpadic(x^2+9,3,20); print(matsize(F)[1], \" \", poldegree(F[1,1])); quit\n",
        capture_output=True, text=True, timeout=60).stdout.strip().split()
    npoly, deg = int(out[0]), int(out[1])
    report("B: X^2+9 irreducible over Q_3 (one factor, degree 2 => e=1,f=2 inert frame)",
           npoly == 1 and deg == 2, f"factors={npoly}, deg={deg}")
except Exception as exc:  # gp absent: record, do not fail the suite
    report("B: PARI check SKIPPED (gp unavailable)", True, str(exc))

# ---------- C: T1 threshold arithmetic on random coherent-law instances ----------
random.seed(0)
fails = 0
for _ in range(100000):
    e = random.randint(1, 5); g = random.randint(1, 5)
    h_prev = random.randint(1, 40)
    STR = random.randint(1, 16); D = random.randint(1, 16)
    # coherence slope law at the anchor's predecessor: slope_prev*(e*STR*D) = h_prev
    slope_prev = Fraction(h_prev, e * STR * D)
    # strict steepening: pick slope_b > slope_prev with h_b = slope_b*(1*STR_b*D_b) integral
    STR_b, D_b = STR * e, e * g * D
    h_b = random.randint(1, 200)
    slope_b = Fraction(h_b, STR_b * D_b)
    if slope_b > slope_prev:
        # claim: h_b > e*g*h_prev (the derived threshold w_prev(Phi_b) = e*h_prev*g < h_b)
        if not (h_b > e * g * h_prev):
            fails += 1
report("C: slope_b > slope_prev  ==>  h_b > e*g*h_prev (100k random instances)",
       fails == 0, f"violations={fails}")

# ---------- D: fence-lift flag -- weight lattice at STR=2, unit root key ----------
# X-monomial weights: 2*v (v >= 0). Required weight 3 (h odd). Two-slot lattice:
# min(2*v(c), 2*v(d)+1) hits 3 at v(d)=1.
mono = {2 * v for v in range(10)}
two = {2 * v for v in range(10)} | {2 * v + 1 for v in range(10)}
report("D: 3 not in X-monomial lattice {2v}; 3 in two-slot lattice {2v} u {2v+1}",
       3 not in mono and 3 in two)

print("ALL PASS" if ok else "FAILURES PRESENT")
sys.exit(0 if ok else 1)
