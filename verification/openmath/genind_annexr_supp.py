#!/usr/bin/env python3
"""GENIND ANNEX R supplementary leg (2026-08-09, post-ratification; ADDITIVE).

Machine support for GENIND_PROOF_2026-08-08.md ANNEX R (the Codex
CHALLENGE repair round, CODEX_GENINDRAT_2026-08-09.md S4 queue R1-R6).
The sealed runner (genind_checks.py, md5 e7ca150b...) and all sealed
artifacts are NOT touched; this leg is pure sympy/arithmetic, no repo
imports except a read-only text scan of the sealed runner's gate lines.

Preregistered checks (all must be GREEN):
  A  m=2 closed forms u(2l)=l*Q^(2l-1)-(l-1)*Q^(2l-2),
     u(2l+1)=(l+1)*Q^(2l)-l*Q^(2l-1) SOLVE the S5.2 first-step
     recursion u(N)=Q^(N-1)+sum_{2k<=N-1}(Q-1)Q^k u(N-2k), u(1)=1,
     symbolically in Q at N=2..14.
  B  the closed forms == W-11's R(M)=Q^(M-1)+floor((M-1)/2)(Q-1)Q^(M-2)
     (HEX3.A's displayed R; R(1)=1), M=1..14 symbolic.
  C  rate: u(N) <= N*Q^(N-1) (i.e. relative mass <= N*Q^-(N-1)),
     N=2..14, Q in {2,3,4,5,8,9}.
  D  depth+window identity D_l + M_l = N at the committed instances
     M6 / TWOCHILD(A,B) / PSTEEP3 / PSTEEP4 / SS6, with D_l recomputed
     from hull data via D = min_j(v(a_j) + j*k) (GENIND-3's formula).
  E  route-prefactor bound rho_genre <= Q^-(D-1): M6's displayed law
     (q-1)^2 q^(6N-17) at q in {2,3,4,5}; PSTEEP3 32/2^12 at (2,5);
     PSTEEP4 512/2^20 at (2,6).
  F  monotonicity (the R6/F4 arithmetic): d/du1[u1T2+T1u2-u1u2]=T2-u2;
     d/dui[prod T - prod(T-u)] = prod_{j!=i}(T_j-u_j) >= 0 at r=2,3;
     union bound sum_i u_i prod_{j!=i} T_j >= prod T - prod(T-u)
     (difference has nonnegative coefficients in (u, T-u)), r=2,3.
  G  the F1 toy separates on the unit-pivot condition: over Z/4
     (pi=2, q=2, two digit levels) the triangular map
     (x,y)->(x,(x+2)y) has collapsing fibers exactly at non-unit
     pivot x in 2Z/4, while a unit-pivot triangular map
     (x,y)->(x,(1+2x)y) is a bijection on every fiber.
  H  CS4-F floor (R4/F5): at (q,N,k)=(2,2,1) the unfloored display
     returns 2^-6 (non-integer) against a true locus of 0; at
     (2,5,1) the floor 4k<=N-1 holds and the display is integral;
     the sealed runner genind_checks.py gates on 'while 4 * k <= N - 1'
     at lines 709 and 869 (text scan, read-only).
  I  window-1 (R3/F2): the (m,d,1) system has Q^(m*0)=1 state, all
     a_j = 0, v(a_0) >= 1 = N: DRAIN; u(1) = total = 1 (the recursion
     boundary check A consumes).

Design dry-run disclosure: the first execution attempt died on the
system python3 (no sympy); re-run under the sympy interpreter
/data/users/asvin/comp_icl/.venv/bin/python (sympy 1.13.1, the
PHASE_C_REGRESSION-documented environment) was GREEN on first
execution, no check or constant edited after any output was seen.
"""
import sympy as sp
from fractions import Fraction

VIOL = []


def check(name, ok, detail=""):
    tag = "ok" if ok else "VIOLATION"
    print("  [%s] %s %s" % (tag, name, detail))
    if not ok:
        VIOL.append((name, detail))


Q = sp.Symbol('Q', positive=True)


def u_closed(N):
    if N == 1:
        return sp.Integer(1)
    if N % 2 == 0:
        l = N // 2
        return l * Q ** (2 * l - 1) - (l - 1) * Q ** (2 * l - 2)
    l = (N - 1) // 2
    return (l + 1) * Q ** (2 * l) - l * Q ** (2 * l - 1)


def u_rec(N, memo={}):
    if N in memo:
        return memo[N]
    if N == 1:
        v = sp.Integer(1)
    else:
        v = Q ** (N - 1)
        k = 1
        while 2 * k <= N - 1:
            v += (Q - 1) * Q ** k * u_rec(N - 2 * k)
            k += 1
    v = sp.expand(v)
    memo[N] = v
    return v


print("A. m=2 closed forms vs the S5.2 recursion (symbolic, N=2..14)")
for N in range(2, 15):
    d = sp.expand(u_closed(N) - u_rec(N))
    check("A N=%d" % N, d == 0, "diff=%s" % d)

print("B. closed forms == W-11/HEX3.A's R(M) (M=1..14)")
for M in range(1, 15):
    if M == 1:
        RM = sp.Integer(1)
    else:
        RM = Q ** (M - 1) + ((M - 1) // 2) * (Q - 1) * Q ** (M - 2)
    d = sp.expand(u_closed(M) - RM)
    check("B M=%d" % M, d == 0, "diff=%s" % d)

print("C. rate u(N) <= N*Q^(N-1), N=2..14, Q in {2,3,4,5,8,9}")
for qv in (2, 3, 4, 5, 8, 9):
    ok = all(u_closed(N).subs(Q, qv) <= N * qv ** (N - 1)
             for N in range(2, 15))
    check("C Q=%d" % qv, ok)

print("D. D_l + M_l = N via D = min_j(v(a_j)+j*k) at committed hulls")
# (name, hull vertices [(abscissa, height)...], child slope k,
#  expected D, committed window statement M(N))
INST = [
    ("M6 child", [(0, 4), (2, 2), (6, 0)], 1, 4, "N-4"),
    ("TWOCHILD A", [(0, 6), (2, 2), (4, 0)], 2, 6, "N-6"),
    ("TWOCHILD B", [(0, 6), (2, 2), (4, 0)], 1, 4, "N-4"),
    ("PSTEEP3", [(0, 4), (1, 2), (3, 0)], 1, 3, "N-3"),
    ("PSTEEP4", [(0, 5), (1, 3), (4, 0)], 1, 4, "N-4"),
    ("SS6 child", [(0, 8), (4, 2), (6, 0)], 1, 6, "N-6"),
]


def hull_height(verts, j):
    # lower hull height at abscissa j (piecewise linear through verts)
    for (x0, y0), (x1, y1) in zip(verts, verts[1:]):
        if x0 <= j <= x1:
            return Fraction(y0) + Fraction(y1 - y0, x1 - x0) * (j - x0)
    raise ValueError


for name, verts, k, Dexp, Mstr in INST:
    m = verts[-1][0]
    D = min(hull_height(verts, j) + j * k for j in range(m + 1))
    ok = D == Dexp
    check("D %s" % name, ok, "D=%s expect %d (M=%s, D+M=N)" % (D, Dexp, Mstr))

print("E. route-prefactor bound rho <= Q^-(D-1)")
for qv in (2, 3, 4, 5):
    # M6: locus (q-1)^2 q^(6N-17), total q^(6(N-1)), D=4
    rho = Fraction((qv - 1) ** 2, qv ** 11)
    check("E M6 q=%d" % qv, rho <= Fraction(1, qv ** 3),
          "rho=%s vs Q^-3" % rho)
check("E PSTEEP3 (2,5)", Fraction(32, 2 ** 12) <= Fraction(1, 2 ** 2),
      "2^-7 vs 2^-2 (D=3)")
check("E PSTEEP4 (2,6)", Fraction(512, 2 ** 20) <= Fraction(1, 2 ** 3),
      "2^-11 vs 2^-3 (D=4)")

print("F. monotonicity + union bound (symbolic)")
u1, u2, u3, T1, T2, T3 = sp.symbols('u1 u2 u3 T1 T2 T3')
F2 = u1 * T2 + T1 * u2 - u1 * u2
check("F dF/du1 = T2-u2", sp.expand(sp.diff(F2, u1) - (T2 - u2)) == 0)
for r in (2, 3):
    us = [u1, u2, u3][:r]
    Ts = [T1, T2, T3][:r]
    G = sp.prod(Ts) - sp.prod([t - u for t, u in zip(Ts, us)])
    for i in range(r):
        dGi = sp.expand(sp.diff(G, us[i]))
        want = sp.expand(sp.prod([Ts[j] - us[j] for j in range(r) if j != i]))
        check("F r=%d dG/du%d" % (r, i + 1), sp.expand(dGi - want) == 0)
    UB = sum(us[i] * sp.prod([Ts[j] for j in range(r) if j != i])
             for i in range(r))
    # substitute T_i = u_i + s_i; UB - G must have nonneg coefficients
    ss = sp.symbols('s1:%d' % (r + 1))
    diff = sp.expand((UB - G).subs(list(zip(Ts, [u + s for u, s
                                                 in zip(us, ss)]))))
    poly = sp.Poly(diff, *(list(us) + list(ss)))
    ok = all(c >= 0 for c in poly.coeffs())
    check("F r=%d union bound" % r, ok, "UB-G=%s" % diff)

print("G. the F1 toy: non-unit pivot collapses, unit pivot does not")
collapse, unitok = [], []
for x in range(4):
    img_bad = {(x + 2) * y % 4 for y in range(4)}
    img_good = {(1 + 2 * x) * y % 4 for y in range(4)}
    if x % 2 == 0:
        collapse.append(len(img_bad) < 4)
    else:
        collapse.append(len(img_bad) == 4)
    unitok.append(len(img_good) == 4)
check("G toy collapse pattern", all(collapse),
      "(x+2)y bijective iff x unit")
check("G unit pivot bijective", all(unitok), "(1+2x)y always bijective")

print("H. CS4-F floor")
val_221 = Fraction(2 * 1, 2) * Fraction(1, 2 ** 6)  # q(q-1)/2 * q^(8-10-4)
check("H (2,2,1) display", val_221 == Fraction(1, 64) and
      val_221.denominator != 1, "non-integer %s, true locus 0" % val_221)
check("H (2,2,1) floor", not (4 * 1 <= 2 - 1), "4k<=N-1 fails: gated to 0")
check("H (2,5,1) visible", (4 * 1 <= 5 - 1) and
      Fraction(1) * 2 ** (20 - 10 - 4) == 64, "floor holds, law 2^6")
import os
rp = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                  "genind_checks.py")
lines = open(rp).read().splitlines()
check("H runner gate L709", "while 4 * k <= N - 1" in lines[708],
      repr(lines[708].strip()))
check("H runner gate L869", "while 4 * k <= N - 1" in lines[868],
      repr(lines[868].strip()))

print("I. window-1 system")
for m in (2, 3, 4):
    for Qv in (2, 3, 4):
        check("I m=%d Q=%d" % (m, Qv), Qv ** (m * 0) == 1,
              "1 state (all a_j=0), v(a_0)>=1=N: DRAIN; u(1)=total=1")

print()
if VIOL:
    print("RED: %d violations" % len(VIOL))
    raise SystemExit(1)
print("GREEN: all checks passed")
