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

# ==================== ROUND-2 CHECKS (V11 repair; rev-2 sections 5.3-5.6) ====================

# ---------- E: the threaded slot law (THR) at the HK23-gate numbers ----------
# Compiled two-level tower over p=2: base w0 = Gauss; frame sigma1 = ramifiedStage-like:
# pair (2,5), key fq (deg 2), (STR): w1(B) = 2*wPrev1(B) on C_fq; the (n1) slot-minimum of
# a (2,5) read over sigma1 weighs slot j as 2*w1(B_j) + 5j = 4*wPrev1(B_j) + 5j.
e_read, h_read, estar = 2, 5, 2
agree = [(Wk, j) for Wk in range(1, 60) for j in range(4)
         if e_read * Wk + j * h_read == e_read * (estar * Wk) + j * h_read]
report("E1: rev-1 slot weight e*W_k+j*h != threaded e*estar*W_k+j*h at estar=2 (all W_k>=1)",
       not agree, f"agreements={agree[:3]}")
report("E2: at estar=1 the rev-1 and threaded weights coincide",
       all(e_read * Wk + j * h_read == e_read * (1 * Wk) + j * h_read
           for Wk in range(60) for j in range(4)))
# E3: the (n1) regrade scale at the stretched frame is un-MacLane: u(p) = 2*w1(p) = 4,
# u(fq) = 2*w1(1) + 5 = 5 (slope 5/4), while the frame's own w has w1(p) = 2, w1(fq) = 5
# (slope 5/2) -- no single rescaling matches both.
u_p, u_fq = 2 * 2, 2 * 0 + 1 * 5
w1_p, w1_fq = 2, 5
report("E3: regrade slope 5/4 vs frame slope 5/2 at the stretched gate frame",
       Fraction(u_fq, u_p) == Fraction(5, 4) and Fraction(w1_fq, w1_p) == Fraction(5, 2)
       and Fraction(u_fq, u_p) != Fraction(w1_fq, w1_p))

# ---------- F: the stretched-frame display void (Prop 5.6 / brief Prop 5.4.3) ----------
# (n2) demands sigma.w(t_k) = h*(g-k); (STR) at a stretched frame forces sigma.w-values of
# coefficients into e*Z; gcd(e,h)=1 makes these clash exactly when e does not divide (g-k).
import math
viol = 0
for _ in range(20000):
    e = random.randint(2, 7)
    h = random.choice([x for x in range(1, 60) if math.gcd(x, e) == 1])
    g = random.randint(1, 8)
    k = random.randint(0, g - 1)
    if (((g - k) % e != 0)) != ((h * (g - k)) % e != 0):
        viol += 1
report("F1: e | h*(g-k) iff e | (g-k) at gcd(e,h)=1 (20k random)", viol == 0, f"violations={viol}")
report("F2: gate instance -- stretched frame (e,h)=(2,5), onward g=1, k=0: weight 5 not in 2Z",
       (5 * 1) % 2 != 0)

# ---------- G: sharpness at g = 3 (Prop 5.4.2) over F27 = F3[z]/(z^3 - z - 1) ----------
# Theta_m(P) = zbar^m * P(zbar) on {P : deg < 3}: bijective for every m; the full-support
# target Theta_m(1 + z + z^2) is missed by every one-slot and every two-slot digit set.
def f27_mul(x, y):
    c = [0] * 5
    for i2 in range(3):
        for j2 in range(3):
            c[i2 + j2] = (c[i2 + j2] + x[i2] * y[j2]) % 3
    # reduce: z^3 = z + 1, z^4 = z^2 + z
    return ((c[0] + c[3]) % 3, (c[1] + c[3] + c[4]) % 3, (c[2] + c[4]) % 3)
# sanity: z^3 - z - 1 has no root in F3 (irreducible cubic)
report("G0: z^3 - z - 1 irreducible over F3 (no roots)",
       all((a ** 3 - a - 1) % 3 != 0 for a in range(3)))
f27_all = [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]
zb = (0, 1, 0)
zpow = [(1, 0, 0)]
for _ in range(26):
    zpow.append(f27_mul(zpow[-1], zb))
g_ok = True
for m in range(26):
    zm = zpow[m]
    theta = {P: f27_mul(zm, P) for P in f27_all}      # Theta_m(P) = zbar^m * P(zbar)
    if len(set(theta.values())) != 27:                 # bijectivity (injective on 27)
        g_ok = False
    target = theta[(1, 1, 1)]                          # full-support c~_S
    one_slot = {f27_mul(zpow[(m + k) % 26], (u, 0, 0)) for k in range(3) for u in (1, 2)}
    two_slot = set()
    for ka in range(3):
        for kb in range(ka + 1, 3):
            for ua in (1, 2):
                for ub in (1, 2):
                    Pa = [0, 0, 0]; Pa[ka] = ua; Pa[kb] = ub
                    two_slot.add(theta[tuple(Pa)])
    if target in one_slot or target in two_slot:
        g_ok = False
report("G1: for every offset m: Theta_m bijective; full-support target missed by all "
       "one- and two-slot digit sets (exhaustive, F27, g=3)", g_ok)

# ---------- H (round 3): WITHDRAWAL certificate for rev 2's "definitional void" ----------
# V15 critical finding: Prop 5.4.3's arithmetic obstruction fires only when SOME nonzero
# psi_k has e not dividing (g-k); descend polynomials whose every nonzero lower exponent
# satisfies k = g (mod e) EVADE it. Rev 3 withdraws the void/exhaustiveness consequence;
# these checks certify the evading class is real and populated (falsifier-first for the
# withdrawal, not for a new positive claim).
def irreducible_by_roots(coeffs, p):
    # coeffs lowest-first, monic, degree 2 or 3: irreducible over F_p iff no root in F_p
    assert len(coeffs) - 1 in (2, 3) and coeffs[-1] == 1
    return all(sum(c * pow(a, i3, p) for i3, c in enumerate(coeffs)) % p != 0
               for a in range(p))

# H1: the displayed evading instance (the verifier's counterexample): e = 2, g = 2,
# psi = z^2 + 1 over F_3 -- irreducible, and its only nonzero lower coefficient (k = 0)
# has e | (g - k), so the stretched-frame display obstruction does NOT fire on it.
psiH = (1, 0, 1)
h1_irr = irreducible_by_roots(psiH, 3)
h1_evades = all((2 - k) % 2 == 0 for k in range(2) if psiH[k] != 0)
report("H1: z^2+1 irreducible over F3; every nonzero lower exponent k = g (mod e=2) "
       "-- Prop 5.4.3 obstruction does not fire (void claim WITHDRAWN)",
       h1_irr and h1_evades)

# H2: the evading class is populated at several (e = g, p): monic irreducible z^g + c0
# (all lower support in the class k = 0 = g mod e) exists for each configuration.
h2_ok = True
h2_counts = []
for (e3, p3) in [(2, 3), (2, 5), (3, 7)]:
    g3 = e3
    found = sum(1 for c0 in range(1, p3)
                if irreducible_by_roots(tuple([c0] + [0] * (g3 - 1) + [1]), p3))
    h2_counts.append(((e3, p3), found))
    h2_ok = h2_ok and found > 0
report("H2: evading class populated (irreducible z^g + c0, g = e) at (e,p) in "
       "{(2,3),(2,5),(3,7)}", h2_ok, f"counts={h2_counts}")

print("ALL PASS" if ok else "FAILURES PRESENT")
sys.exit(0 if ok else 1)
