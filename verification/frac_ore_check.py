#!/usr/bin/env python3
"""Decorrelated numerical check: fractional-slope Ore with twist (MOVES note rev 2 B1 draft).

Setting: degree-1 key phi = x, slope -h/e in lowest terms, p prime.
Doubled weight on Z_p[x]:   w(f) = min_i ( e*v_p(c_i) + i*h )   over nonzero coeffs c_i.
Side residual: with gamma = w(f), min-slots S = { i : e*v_p(c_i) + i*h = gamma },
i0 = min S,  R(f)(z) = sum_{i in S} digit(c_i) * z^{(i-i0)/e}  in F_p[z],
where digit(c) = (c / p^{v_p(c)}) mod p.
(Exponents are integral: for i,i' in S, e*(v-v') = (i'-i)*h and gcd(h,e)=1 => e | i'-i.)

Claims under test, for random pairs (f,g):
  (W)  w(fg) = w(f) + w(g)
  (R)  R(fg) = z^eps * R(f)*R(g) with eps in {0,1}; empirical eps rule to be REPORTED.

Implementation note: coefficients are sampled as exact integer lifts of Z/p^12 elements
(with extra p-divisibility mixed in), and fg is computed EXACTLY in Z[x], so v_p and
digits are exact -- no p^12 truncation artifacts in the product.
"""

import random
from collections import Counter

PREC = 12  # coefficients sampled from [0, p^12)


def vp(n, p):
    """p-adic valuation of a nonzero integer."""
    assert n != 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def w_i0_R(coeffs, p, h, e):
    """Return (gamma, i0, R) for a nonzero integer polynomial, or None if zero.

    R is a dict {k: digit} representing sum digit * z^k over F_p, digits nonzero.
    """
    slots = []
    for i, c in enumerate(coeffs):
        if c != 0:
            v = vp(c, p)
            slots.append((i, v, e * v + i * h))
    if not slots:
        return None
    gamma = min(wt for (_, _, wt) in slots)
    mins = [(i, v) for (i, v, wt) in slots if wt == gamma]
    i0 = min(i for (i, _) in mins)
    R = {}
    for i, v in mins:
        assert (i - i0) % e == 0, "non-integral residual exponent (should be impossible, gcd(h,e)=1)"
        d = (coeffs[i] // p**v) % p
        assert d != 0
        R[(i - i0) // e] = d
    return gamma, i0, R


def polymul_Z(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    out[i + j] += ai * bj
    return out


def polymul_Fp(A, B, p):
    """Multiply two residuals given as {exponent: digit} dicts, over F_p; drop zeros."""
    out = {}
    for i, ai in A.items():
        for j, bj in B.items():
            out[i + j] = (out.get(i + j, 0) + ai * bj) % p
    return {k: v for k, v in out.items() if v != 0}


def rand_coeff(p, rng):
    """Random Z/p^12 lift; mixes in extra p-divisibility and occasional zeros."""
    r = rng.random()
    if r < 0.08:
        return 0
    if r < 0.48:
        return rng.randrange(1, p**PREC)  # generic element
    # forced extra divisibility: unit * p^v, v in 1..6
    v = rng.randrange(1, 7)
    u = rng.randrange(1, p ** (PREC - v))
    while u % p == 0:
        u = rng.randrange(1, p ** (PREC - v))
    return u * p**v


def rand_poly(p, rng):
    deg = rng.randrange(2, 7)
    while True:
        c = [rand_coeff(p, rng) for _ in range(deg + 1)]
        if any(c):
            return c


def R_str(R):
    if not R:
        return "0"
    return " + ".join(
        (f"{d}" if k == 0 else (f"{d}*z^{k}" if d != 1 else f"z^{k}")) if k != 1 or d != 1 else "z"
        for k, d in sorted(R.items())
    )


def main():
    rng = random.Random(20260722)
    N_PAIRS = 2000
    configs = [(p, h, e) for p in (2, 3) for (h, e) in ((1, 2), (2, 3), (3, 2))]

    grand_w_viol = 0
    grand_R_viol = 0
    examples_printed = 0

    print(f"{N_PAIRS} random pairs per (p,h,e) config; degrees 2..6; coeff lifts of Z/p^{PREC}.")
    print()

    for (p, h, e) in configs:
        w_viol = 0
        R_viol_list = []
        eps_counter = Counter()          # observed eps values (or 'NONE' if no eps in {0,1} works)
        delta_i0_counter = Counter()     # i0(fg) - i0(f) - i0(g)
        i0sum_mod_e_vs_eps = Counter()   # ((i0f+i0g) mod e, eps)
        multi_slot_pairs = 0             # pairs where some residual has >1 term (nontrivial tests)

        for trial in range(N_PAIRS):
            f = rand_poly(p, rng)
            g = rand_poly(p, rng)
            fg = polymul_Z(f, g)

            gf, i0f, Rf = w_i0_R(f, p, h, e)
            gg, i0g, Rg = w_i0_R(g, p, h, e)
            gfg, i0fg, Rfg = w_i0_R(fg, p, h, e)

            if len(Rf) > 1 or len(Rg) > 1 or len(Rfg) > 1:
                multi_slot_pairs += 1

            # Claim (W)
            if gfg != gf + gg:
                w_viol += 1

            # Claim (R): find eps in {0,1} with R(fg) = z^eps * Rf*Rg
            Rprod = polymul_Fp(Rf, Rg, p)
            eps_found = None
            for eps in (0, 1):
                shifted = {k + eps: v for k, v in Rprod.items()}
                if shifted == Rfg:
                    eps_found = eps
                    break
            delta = i0fg - i0f - i0g
            delta_i0_counter[delta] += 1
            if eps_found is None:
                R_viol_list.append((f, g, fg))
                eps_counter["NONE"] += 1
            else:
                eps_counter[eps_found] += 1
                i0sum_mod_e_vs_eps[((i0f + i0g) % e, eps_found)] += 1

            # print a few worked examples (prefer nontrivial residuals)
            if (
                examples_printed < 3
                and len(Rf) > 1
                and len(Rg) > 1
                and trial > 10
            ):
                examples_printed += 1
                print(f"--- worked example {examples_printed}: p={p}, slope -{h}/{e} ---")
                print(f"  f  coeffs (asc) = {f}")
                print(f"  g  coeffs (asc) = {g}")
                print(f"  fg coeffs (asc) = {fg}")
                print(f"  w(f)={gf}, i0(f)={i0f}, R(f) = {R_str(Rf)}")
                print(f"  w(g)={gg}, i0(g)={i0g}, R(g) = {R_str(Rg)}")
                print(f"  w(fg)={gfg} (claim: {gf}+{gg}={gf+gg}), i0(fg)={i0fg} (i0f+i0g={i0f+i0g})")
                print(f"  R(f)*R(g) mod {p} = {R_str(Rprod)}")
                print(f"  R(fg)            = {R_str(Rfg)}   eps={eps_found}")
                print()

        grand_w_viol += w_viol
        grand_R_viol += len(R_viol_list)

        print(f"[p={p}, slope -{h}/{e}]  pairs={N_PAIRS}  "
              f"w-violations={w_viol}  R-violations={len(R_viol_list)}  "
              f"pairs-with-multiterm-residual={multi_slot_pairs}")
        print(f"    eps observed: {dict(eps_counter)}")
        print(f"    delta_i0 = i0(fg)-i0(f)-i0(g): {dict(delta_i0_counter)}")
        print(f"    ((i0f+i0g) mod e, eps) tally: {dict(i0sum_mod_e_vs_eps)}")
        if R_viol_list:
            fex, gex, fgex = R_viol_list[0]
            print(f"    first R-violation: f={fex} g={gex} fg={fgex}")
        print()

    print(f"TOTAL over {len(configs)} configs x {N_PAIRS} pairs = {len(configs)*N_PAIRS} pairs:")
    print(f"  w-multiplicativity violations: {grand_w_viol}")
    print(f"  residual-multiplicativity violations (no eps in {{0,1}} works): {grand_R_viol}")


if __name__ == "__main__":
    main()
