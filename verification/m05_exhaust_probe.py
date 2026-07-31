#!/usr/bin/env python3
"""M05-exhaust numeric probes (drainage / exhaustiveness of splitting-type classification).

T1  TAIL BOUND: exact mu{ v_p(disc f) >= m } for monic degree-n f over Z_p
    (Haar; computed exhaustively at level m -- disc mod p^m is a function of the
    coefficients mod p^m since disc is a Z-polynomial in the coefficients),
    checked against the claimed bound
        mu{ v_p(disc) >= m }  <=  (n-1) * p^{-max(0, ceil((m - n*v_p(n))/(n-1)))}.

T2  SEMANTIC (KRASNER) ENVELOPE: u(N) := fraction of level-N classes NOT certified
    decided by the Krasner criterion 2*v_p(disc)+1 <= N (v read off any class rep;
    well-defined class-wise whenever v < N).  Checks: u(N) monotone nonincreasing,
    and u(N) <= tail bound at m = ceil((N+1)/2)  (since undecided => v >= (N+1)/2 or
    disc == 0 mod p^N, and ceil((N+1)/2) <= N so the event is class-measurable).
"""
import itertools, math, sys
from sympy import symbols, Poly, discriminant, lambdify

def vp_int(x, p):
    if x == 0:
        return None
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

_DISC_CACHE = {}
def disc_coeff_funcs(n):
    """Return (k, funcs): disc of x^n + a_{n-1}x^{n-1}+...+a_0, viewed as a polynomial
    in a_0 of degree k, as integer-coefficient functions of the tail (a_1..a_{n-1})."""
    if n in _DISC_CACHE:
        return _DISC_CACHE[n]
    x = symbols('x')
    a = symbols(f'a0:{n}')
    f = Poly(x**n + sum(a[i]*x**i for i in range(n)), x)
    D = Poly(discriminant(f), a[0])          # polynomial in a0
    coeffs = D.all_coeffs()                  # leading first
    k = len(coeffs) - 1
    tail = a[1:]
    funcs = [lambdify(tail, c, modules="math") for c in coeffs]
    _DISC_CACHE[n] = (k, funcs)
    return k, funcs

def count_disc_divisible(n, p, m):
    """#{a in (Z/p^m)^n : disc(a) == 0 mod p^m}, exact."""
    mod = p**m
    k, funcs = disc_coeff_funcs(n)
    cnt = 0
    for tail in itertools.product(range(mod), repeat=n-1):
        cs = [int(fn(*tail)) % mod for fn in funcs]   # leading first, degree k in a0
        for a0 in range(mod):
            acc = 0
            for c in cs:
                acc = (acc * a0 + c) % mod
            if acc == 0:
                cnt += 1
    return cnt

def tail_bound(n, p, m):
    w = n * (vp_int(n, p) or 0)
    e = max(0, math.ceil((m - w) / (n - 1)))
    return (n - 1) / p**e

def T1():
    print("=== T1: mu{v_p(disc)>=m} vs bound (n-1) p^{-ceil((m - n v_p(n))/(n-1))} ===")
    CASES = [(2,2,8),(2,3,6),(2,5,4),(2,7,3),(3,2,6),(3,3,4),(3,5,2),(4,2,5),(4,3,3),(4,5,2)]
    allok = True
    for n, p, mmax in CASES:
        for m in range(1, mmax+1):
            tot = (p**m)**n
            cnt = count_disc_divisible(n, p, m)
            frac, bnd = cnt/tot, tail_bound(n, p, m)
            ok = frac <= bnd + 1e-15
            allok &= ok
            print(f"  n={n} p={p} m={m}: mu={cnt}/{tot} = {frac:.4e}   bound={bnd:.4e}   {'PASS' if ok else 'FAIL'}")
            sys.stdout.flush()
    print(f"T1 overall: {'ALL PASS' if allok else 'FAILURES PRESENT'}")

def T2():
    print("\n=== T2: semantic (Krasner) envelope u(N) -- undecided iff disc==0 mod p^N or 2v+1>N ===")
    for n, p, Nmax in [(3,2,6),(2,3,5),(2,2,10),(2,5,4)]:
        k, funcs = disc_coeff_funcs(n)
        prev = None
        for N in range(1, Nmax+1):
            mod = p**N
            undec = 0
            for tail in itertools.product(range(mod), repeat=n-1):
                cs = [int(fn(*tail)) % mod for fn in funcs]
                for a0 in range(mod):
                    acc = 0
                    for c in cs:
                        acc = (acc * a0 + c) % mod
                    v = vp_int(acc, p)
                    if v is None or 2*v + 1 > N:
                        undec += 1
            tot = mod**n
            u = undec/tot
            m = (N + 1) // 2 if N % 2 == 1 else N // 2  # ceil(N/2): 2v+1>N <=> v >= ceil(N/2)
            bnd = tail_bound(n, p, m)
            mono = "" if prev is None else ("  dec" if u <= prev + 1e-15 else "  INCREASE!")
            ok = u <= bnd + 1e-15
            print(f"  n={n} p={p} N={N}: u(N)={undec}/{tot} = {u:.4e}   bnd@m={m}: {bnd:.4e}   {'PASS' if ok else 'FAIL'}{mono}")
            sys.stdout.flush()
            prev = u
        print()

if __name__ == "__main__":
    T1()
    T2()
