#!/usr/bin/env python3
"""GENIND ANNEX R scoped hostile pass — FRESH out-of-battery leg (2026-08-10).

Verifier-owned instrument (GENIND_ANNEXR_pass_report.md). The sealed
runner (genind_checks.py, e7ca150b) and the annex supp leg
(genind_annexr_supp.py, 42fd603e) are NOT touched; this leg stresses
the annex's NEWEST claims strictly OUTSIDE the committed battery
ranges. Dual oracles per check where available: sympy symbolic AND
exact Fraction/int arithmetic (independent code paths).

PREREGISTERED (sealed before the run; every check must be GREEN):
  P1  m=2 closed forms u(2l)=l*Q^(2l-1)-(l-1)*Q^(2l-2),
      u(2l+1)=(l+1)*Q^(2l)-l*Q^(2l-1) solve the S5.2 SUM recursion
      u(N)=Q^(N-1)+sum_{2k<=N-1}(Q-1)Q^k u(N-2k), u(1)=1:
      (a) symbolic in Q at N=2..40 (battery leg A stopped at 14);
      (b) exact ints at Q=7 and Q=27, N=2..40 (battery leg C used
      Q in {2,3,4,5,8,9}; 27 = non-prime prime-power, first here).
  P2  rate u(N) <= N*Q^(N-1) exact at Q in {7,27}, N=2..40
      (= ANNEX-THEOREM GENIND.C' with (K,B,c)=(1,1,1) at m=2).
  P3  R1.3's alpha recomposition WIRING, symbolic (m=2..6, c(m)=
      m(m-1)/2 per body L125): the alpha(k) relative-mass factor
      (Q-1)Q^(-k*m(m+1)/2) (body L137) times the child-total
      renormalization Q^(mk) equals (Q-1)Q^(-k*c(m)) EXACTLY —
      i.e. m(m+1)/2 - m == c(m); and sum_{k>=1}(Q-1)Q^(-kc)
      = (Q-1)/(Q^c-1) <= 1 iff c >= 1, with EQUALITY at c=1
      (m=2 ground sharpness). TOOTH T-P3: at c=0 the sum diverges
      (the wiring is load-bearing, not decorative).
  P4  GENIND-C1(ii)/R6 arithmetic BEYOND the supp leg's r=2,3:
      at r=4 and r=5, dG/du_i = prod_{j!=i}(T_j-u_j) symbolically,
      and UB - G = sum_i u_i prod_{j!=i}T_j - [prod T - prod(T-u)]
      has nonnegative coefficients in (u_i, s_i:=T_i-u_i).
  P5  CS4-F floor at fresh points (R4; supp leg H used (2,2,1) and
      (2,5,1) only): (q,N,k)=(3,6,2): 4k=8 > N-1=5 -> genre gated
      to 0 while the unfloored display returns the INTEGER 3
      (q(q-1)/2 * q^(24-20-4) = 3) — the floor is load-bearing even
      where the non-integrality signature is silent; (2,9,2):
      4k=8 <= 8 visible, law 2^(36-20-4) = 2^12 = 4096 integral;
      sealed-runner gate expression re-evaluated at both points
      agrees with the floor arithmetic.

Teeth armed: T-P3 above; T-P5 = the (3,6,2) integer-valued unfloored
display (a checker keyed on non-integrality alone MUST miss it; this
leg must catch it via the floor).
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


def u_closed_sym(N):
    if N == 1:
        return sp.Integer(1)
    if N % 2 == 0:
        l = N // 2
        return l * Q ** (2 * l - 1) - (l - 1) * Q ** (2 * l - 2)
    l = (N - 1) // 2
    return (l + 1) * Q ** (2 * l) - l * Q ** (2 * l - 1)


def u_rec_sym(N, memo={}):
    if N in memo:
        return memo[N]
    if N == 1:
        v = sp.Integer(1)
    else:
        v = Q ** (N - 1)
        k = 1
        while 2 * k <= N - 1:
            v += (Q - 1) * Q ** k * u_rec_sym(N - 2 * k)
            k += 1
    v = sp.expand(v)
    memo[N] = v
    return v


# independent integer-oracle path (no sympy)
def u_closed_int(N, q):
    if N == 1:
        return 1
    if N % 2 == 0:
        l = N // 2
        return l * q ** (2 * l - 1) - (l - 1) * q ** (2 * l - 2)
    l = (N - 1) // 2
    return (l + 1) * q ** (2 * l) - l * q ** (2 * l - 1)


def u_rec_int(N, q, memo):
    if N in memo:
        return memo[N]
    if N == 1:
        v = 1
    else:
        v = q ** (N - 1)
        k = 1
        while 2 * k <= N - 1:
            v += (q - 1) * q ** k * u_rec_int(N - 2 * k, q, memo)
            k += 1
    memo[N] = v
    return v


print("P1a. closed forms solve the SUM recursion, symbolic N=2..40")
bad = [N for N in range(2, 41)
       if sp.expand(u_closed_sym(N) - u_rec_sym(N)) != 0]
check("P1a N=2..40 symbolic", not bad, "bad=%s" % bad)

print("P1b. exact-int oracle at Q=7, Q=27 (out-of-battery), N=2..40")
for q in (7, 27):
    memo = {}
    bad = [N for N in range(2, 41)
           if u_closed_int(N, q) != u_rec_int(N, q, memo)]
    check("P1b Q=%d" % q, not bad, "bad=%s" % bad)

print("P2. rate u(N) <= N*Q^(N-1) at Q in {7,27}, N=2..40")
for q in (7, 27):
    bad = [N for N in range(2, 41) if u_closed_int(N, q) > N * q ** (N - 1)]
    check("P2 Q=%d" % q, not bad, "bad=%s" % bad)

print("P3. R1.3 alpha recomposition wiring (m=2..6) + tooth")
kk = sp.Symbol('k', positive=True, integer=True)
for m in range(2, 7):
    cm = sp.Rational(m * (m - 1), 2)
    lhs = (Q - 1) * Q ** (-kk * sp.Rational(m * (m + 1), 2)) * Q ** (m * kk)
    rhs = (Q - 1) * Q ** (-kk * cm)
    check("P3 m=%d recompose" % m, sp.simplify(lhs - rhs) == 0,
          "m(m+1)/2 - m = %s = c(m)" % cm)
c = sp.Symbol('c', positive=True)
S = sp.summation((Q - 1) * Q ** (-kk * c), (kk, 1, sp.oo))
S = sp.simplify(S)
check("P3 sum closed form", sp.simplify(S - (Q - 1) / (Q ** c - 1)) == 0,
      "sum=%s" % S)
for cv, qv in [(1, 7), (1, 27), (2, 7), (3, 27)]:
    val = Fraction(qv - 1, qv ** cv - 1)
    check("P3 sum c=%d Q=%d <= 1" % (cv, qv), val <= 1,
          "=%s%s" % (val, " (EQUALITY, m=2 sharp)" if val == 1 else ""))
# TOOTH T-P3: c=0 diverges (partial sums unbounded)
psum = sum(Fraction(7 - 1, 7 ** 0) for _ in range(50))
check("P3 TOOTH c=0 diverges", psum > 10 ** 2,
      "50 terms already %s" % psum)

print("P4. C1(ii)/R6 arithmetic at r=4,5 (supp leg stopped at r=3)")
us = sp.symbols('u1:6')
Ts = sp.symbols('T1:6')
ss = sp.symbols('s1:6')
for r in (4, 5):
    u, T, s = us[:r], Ts[:r], ss[:r]
    G = sp.prod(T) - sp.prod([t - x for t, x in zip(T, u)])
    okd = True
    for i in range(r):
        want = sp.prod([T[j] - u[j] for j in range(r) if j != i])
        if sp.expand(sp.diff(G, u[i]) - want) != 0:
            okd = False
    check("P4 r=%d dG/du_i" % r, okd)
    UB = sum(u[i] * sp.prod([T[j] for j in range(r) if j != i])
             for i in range(r))
    diff = sp.expand((UB - G).subs(list(zip(T, [x + y for x, y
                                                in zip(u, s)]))))
    poly = sp.Poly(diff, *(list(u) + list(s)))
    check("P4 r=%d UB-G nonneg" % r, all(cf >= 0 for cf in poly.coeffs()),
          "%d monomials" % len(poly.coeffs()))

print("P5. CS4-F floor at fresh points + gate-expression agreement")
q, N, k = 3, 6, 2
disp = Fraction(q * (q - 1), 2) * Fraction(q) ** (4 * N - 10 * k - 4)
gate = (4 * k <= N - 1)
check("P5 (3,6,2) unfloored display INTEGER", disp == 3,
      "display=%s (integer! T-P5)" % disp)
check("P5 (3,6,2) floor gates to 0", not gate, "4k=8 > N-1=5")
q, N, k = 2, 9, 2
disp = Fraction(q * (q - 1), 2) * Fraction(q) ** (4 * N - 10 * k - 4)
gate = (4 * k <= N - 1)
check("P5 (2,9,2) visible + law", gate and disp == 4096,
      "law 2^12 = %s" % disp)

print()
if VIOL:
    print("RED: %d violations" % len(VIOL))
    raise SystemExit(1)
print("GREEN: all checks passed")
