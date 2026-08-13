#!/usr/bin/env python3
"""n2_census_check.py — independent numeric check of the UNIFORMITY-CHECK-N2 censuses.

Brute-force enumeration of monic quadratics f = x^2 + a1 x + a0 over Z/p^N, of the two
certificate families proved in `leancheck/UniformityCheck/{RamCensus,InertCensus}.lean`:

  RAM(j)   : some centre g has v(F(g)) = 2j+1 EXACTLY (with 2j+2 <= N) and v(F'(g)) >= j+1
  INERT(k) : some centre g has 2k+1 <= N, F(g) = p^(2k) b0, F'(g) = p^k b1 with
             y^2 - b1 y + b0 irreducible mod p   (the anisotropic residual form)

and comparison with the closed forms proved in Lean:

  #RAM(j)   = (q-1) * q^(2N-2j-2)
  #INERT(k) = A     * q^(2N-2k-2),   A = #{(b0,b1) : y^2-b1y+b0 irreducible} = q(q-1)/2

plus the totals (at N = 2M, the levels the Lean proof uses, both normalise to
(1-q^(-2M))/(q+1) and (q/(2(q+1)))(1-q^(-2M)) — the W-11 limit values 1/(q+1) and q/(2(q+1))),
the disjointness of the families (the parameter is determined by the class), and the mutual
disjointness of RAM and INERT.
"""
import sys

def val(x, N, p):
    """v(x) for x in Z/p^N, capped at N."""
    if x % (p ** N) == 0:
        return N
    v = 0
    x %= p ** N
    while x % p == 0:
        x //= p
        v += 1
    return v

def check(p, N):
    q = p
    mod = p ** N
    A = q * (q - 1) // 2
    # residue-level irreducibility table
    irred = {}
    for b1 in range(p):
        for b0 in range(p):
            irred[(b0, b1)] = all((y * y - b1 * y + b0) % p != 0 for y in range(p))
    assert sum(1 for v in irred.values() if v) == A, "residue count"

    ram = {}      # class -> j
    inert = {}    # class -> k
    for a0 in range(mod):
        for a1 in range(mod):
            for g in range(mod):
                F = (g * g + a1 * g + a0) % mod
                D = (2 * g + a1) % mod
                vF, vD = val(F, N, p), val(D, N, p)
                # RAM
                if vF % 2 == 1 and vF + 1 <= N and 2 * vD >= vF + 1:
                    j = (vF - 1) // 2
                    if 2 * j + 2 <= N:
                        prev = ram.get((a0, a1))
                        assert prev is None or prev == j, "RAM parameter not unique"
                        ram[(a0, a1)] = j
                # INERT
                for k in range((N - 1) // 2 + 1):
                    if 2 * k + 1 <= N and vF >= 2 * k and vD >= k:
                        b0 = (F // p ** (2 * k)) % p
                        b1 = (D // p ** k) % p
                        if irred[(b0, b1)]:
                            prev = inert.get((a0, a1))
                            assert prev is None or prev == k, "INERT parameter not unique"
                            inert[(a0, a1)] = k
    assert not (set(ram) & set(inert)), "RAM and INERT overlap"

    ok = True
    for j in range((N - 2) // 2 + 1):
        got = sum(1 for v in ram.values() if v == j)
        want = (q - 1) * q ** (2 * N - 2 * j - 2)
        ok &= (got == want)
        print(f"  p={p} N={N}  RAM(j={j}):   {got:8d}  formula (q-1)q^(2N-2j-2) = {want:8d}"
              f"  {'OK' if got == want else 'MISMATCH'}")
    for k in range((N - 1) // 2 + 1):
        got = sum(1 for v in inert.values() if v == k)
        want = A * q ** (2 * N - 2 * k - 2)
        ok &= (got == want)
        print(f"  p={p} N={N}  INERT(k={k}): {got:8d}  formula A*q^(2N-2k-2)    = {want:8d}"
              f"  {'OK' if got == want else 'MISMATCH'}")
    box = q ** (2 * N)
    # ram runs over 2j+2 <= N  (floor(N/2) terms); inert over 2k+1 <= N (ceil(N/2) terms)
    nram, nin = N // 2, (N + 1) // 2
    ram_t, in_t = len(ram), len(inert)
    ram_w = (box - q ** (2 * N - 2 * nram)) // (q + 1)
    in_w = A * (box - q ** (2 * N - 2 * nin)) // (q * q - 1)
    ok &= (ram_t == ram_w and in_t == in_w)
    print(f"  p={p} N={N}  totals: ram {ram_t}/{box} (W-11 {ram_w}), inert {in_t}/{box} "
          f"(W-11 {in_w})  {'OK' if ram_t == ram_w and in_t == in_w else 'MISMATCH'}")
    return ok

if __name__ == "__main__":
    allok = True
    for p, N in [(2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (5, 2)]:
        allok &= check(p, N)
    print("ALL CHECKS PASSED" if allok else "FAILURES PRESENT")
    sys.exit(0 if allok else 1)
