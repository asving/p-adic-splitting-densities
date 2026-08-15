#!/usr/bin/env python3
"""A-H.2 numeric leg — the repaired `rate_close` (blueprint node H.71), exact rationals.

Amendment A-H.2 repairs the fleet-refuted `rate_close` with two changes:
  (α-0)   `halpha` sums only over the α-ADMISSIBLE multiplicities, `m*(k+1) < N`
          (EFF.GENIND.09's window condition `mμ ≤ N−1`, restored);
  (α-rate) the hypothesis `hmc : m < c` is added (H.30's geometric bound then fires
          at the recomposed slope γ = c − m ≥ 1).

This script certifies, with exact `fractions.Fraction` arithmetic:

  PART 1  The repaired inequality at the intended instantiations. The MAXIMAL family
          solving the three-leg recursion with equality (head = Q^-(N-1), the windowed
          α-sum, β = K'·N^(m+B')·Q^-(N-c'-1), ℕ-truncated exponents throughout) is
          computed for (Q, m) ∈ {2,3} × {2,3} with c = m(m+1)/2 (the normalized α-locus
          slope, so (m,c) ∈ {(2,3),(3,6)}; γ = c − m = clusterC m ∈ {1,3}), across
          K'/B'/c'/n₀ choices, N ≤ 90 — and checked against the PROOF's explicit
          conclusion  u(M) ≤ (1 + K')·M^(m+B'+1)·Q^-(M ∸ (c'+1)).
          Any bounded-below solution of the leg inequalities is ≤ the maximal family,
          so this certifies the conclusion for the whole species at these cells.

  PART 2  Both refuting witnesses of the ORIGINAL statement fail the repaired
          hypotheses (α-0: hmc `1 < 1` false AND windowed halpha false at N = 1;
          α-rate: hmc `2 < 1` false AND windowed halpha false at N = 2).

  PART 3  Sharpness of `hmc`: at c = m (the boundary the rejected candidate `m ≤ c`
          would admit) the repaired-minus-hmc statement is FALSE — two families
          satisfying every other repaired field force K → ∞:
            (Q,m,c,n₀) = (3,1,1,2), u(N) = (9/10)^N   and
            (Q,m,c,n₀) = (3,2,2,2), u(N) = (11/20)^N.
          Legs are verified exactly for N ≤ 400; the forced K is printed at four M.
"""

from fractions import Fraction as F

def trunc(e: int) -> int:
    """ℕ-truncated subtraction result (callers pass a possibly-negative int)."""
    return e if e > 0 else 0

def qinv(Q: int, e: int) -> F:
    """(Q^e)⁻¹ for e ≥ 0."""
    return F(1, Q ** e)

FAIL = 0

def check(cond: bool, msg: str):
    global FAIL
    if not cond:
        FAIL += 1
        print(f"  FAIL: {msg}")

# ---------------------------------------------------------------- PART 1
print("PART 1 — maximal-family certification of the repaired rate_close")
print("         conclusion checked: u(M) <= (1+K')*M^(m+B'+1)*Q^-(M-(c'+1)) [ℕ-trunc]")

NMAX = 90
worst_ratio_report = []
cells = 0
for Q in (2, 3):
    for m in (2, 3):
        c = m * (m + 1) // 2           # the normalized α-locus slope (A-H.2 adjudication)
        assert m < c, "hmc must hold at the intended instantiation"
        for Kp in (F(0), F(3)):
            for (Bp, cp) in ((0, 0), (1, 2)):
                for n0 in (4, 9):
                    B, chat = m + Bp + 1, cp + 1
                    K = 1 + Kp
                    u = {}
                    worst = F(0)
                    for N in range(1, NMAX + 1):
                        head = qinv(Q, N - 1)
                        beta = Kp * F(N) ** (m + Bp) * qinv(Q, trunc(N - cp - 1))
                        alpha = sum(
                            ((Q - 1) * qinv(Q, c * (k + 1)) * u[N - m * (k + 1)]
                             for k in range(n0) if m * (k + 1) < N),
                            F(0),
                        )
                        u[N] = head + alpha + beta
                        bound = K * F(N) ** B * qinv(Q, trunc(N - chat))
                        check(u[N] <= bound,
                              f"Q={Q} m={m} c={c} K'={Kp} B'={Bp} c'={cp} n0={n0} N={N}: "
                              f"u={float(u[N]):.4g} > bound={float(bound):.4g}")
                        worst = max(worst, u[N] / bound)
                    cells += 1
                    if Kp == 0 and Bp == 0 and n0 == 4:
                        worst_ratio_report.append((Q, m, c, float(worst)))
print(f"  {cells} instantiation cells x {NMAX} windows: all conclusion checks passed"
      if FAIL == 0 else f"  violations above: {FAIL}")
for Q, m, c, w in worst_ratio_report:
    print(f"  tightness (K'=B'=c'=0, n0=4): Q={Q} m={m} c={c}  max u/bound = {w:.4f}")

# ---------------------------------------------------------------- PART 2
print("PART 2 — the two refuting witnesses fail the repaired hypotheses")

# (α-0) witness: Q=2, m=c=1, n0=1, u D N = D * 2^-N, alpha = u.
m0, c0 = 1, 1
check(not (m0 < c0), "(α-0) witness should fail hmc (1 < 1)")
D = 1
alpha_at_1 = F(D, 2)                    # alpha D 1 = u D 1 = D/2
windowed_rhs_at_1 = F(0)                # m*(k+1) < 1 impossible: empty sum
check(alpha_at_1 > windowed_rhs_at_1, "(α-0) witness should fail windowed halpha at N=1")
print("  (α-0)  Q=2 m=1 c=1: hmc fails (1<1 false); windowed halpha fails at N=1 "
      f"({float(alpha_at_1)} > {float(windowed_rhs_at_1)})")

# (α-rate) witness: Q=2, m=2, c=1, n0=4, u D N = (9/10)^N, alpha = u.
m1, c1 = 2, 1
check(not (m1 < c1), "(α-rate) witness should fail hmc (2 < 1)")
alpha_at_2 = F(9, 10) ** 2              # alpha D 2 = u D 2
windowed_rhs_at_2 = F(0)                # 2*(k+1) < 2 impossible: empty sum
check(alpha_at_2 > windowed_rhs_at_2, "(α-rate) witness should fail windowed halpha at N=2")
print("  (α-rate) Q=2 m=2 c=1: hmc fails (2<1 false); windowed halpha fails at N=2 "
      f"({float(alpha_at_2)} > {float(windowed_rhs_at_2)})")

# ---------------------------------------------------------------- PART 3
print("PART 3 — sharpness of hmc: at c = m (candidate `m ≤ c` boundary) the statement is FALSE")

for (Q, m, c, n0, r, name) in (
    (3, 1, 1, 2, F(9, 10), "u=(9/10)^N"),
    (3, 2, 2, 2, F(11, 20), "u=(11/20)^N"),
):
    assert m <= c and not (m < c)
    B, chat = m + 0 + 1, 0 + 1          # K' = B' = c' = 0, beta = 0
    # verify every repaired field EXCEPT hmc, exactly, for N <= 400:
    #   alpha := windowed sum (halpha holds with equality); head := u - alpha clipped at 0
    #   (hsplit holds by construction); hhead needs u - alpha <= Q^-(N-1).
    ok = True
    for N in range(1, 401):
        uN = r ** N
        S = sum(((Q - 1) * qinv(Q, c * (k + 1)) * r ** (N - m * (k + 1))
                 for k in range(n0) if m * (k + 1) < N), F(0))
        if uN - S > qinv(Q, N - 1):
            ok = False
            check(False, f"c=m cell (Q={Q},m={m}): hhead fails at N={N}")
            break
    if ok:
        print(f"  (Q,m,c,n0)=({Q},{m},{c},{n0}), {name}: every repaired field except hmc "
              f"verified exactly for N ≤ 400")
    forced = []
    for M in (50, 100, 200, 400):
        # conclusion would need  r^M <= K * M^B * Q^-(M-1)  =>  K >= r^M * Q^(M-1) / M^B
        forced.append((M, r ** M * F(Q) ** (M - 1) / F(M) ** B))
    check(forced[-1][1] > forced[-2][1] > forced[-3][1] > 10 ** 6,
          f"c=m cell (Q={Q},m={m}): forced K should diverge")
    pretty = ", ".join(f"M={M}: K ≥ {float(k):.3e}" for M, k in forced)
    print(f"    forced K diverges: {pretty}")

print()
print("A-H.2 NUMERIC LEG: ALL CHECKS PASSED" if FAIL == 0
      else f"A-H.2 NUMERIC LEG: {FAIL} FAILURES")
raise SystemExit(0 if FAIL == 0 else 1)
