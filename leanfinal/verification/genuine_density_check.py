#!/usr/bin/env python3
"""
genuine_density_check.py — numeric cross-check of the Part-1 genuine density (n = 2).

WHAT THIS CHECKS
----------------
`Uniformity/Density/GenuineDensity.lean` defines, for a complete DVR `O` with residue
cardinality q, degree n and splitting type sigma,

    decidedSeq sigma N = #{ classes c in (O/m^N)^n : EVERY monic degree-n lift of c
                            has splitting type sigma } / q^(n*N)
    decidedDensity     = lim_{N -> infinity} decidedSeq   (a proved monotone limit)

(Post-rewire naming, unit UNIFORMITY-P4, 2026-08-13: the name `genuineDensity` now denotes
the OTHER proved limit, lim_N possibleSeq -- the proportion of classes CONSISTENT with sigma.
At n = 2 the two are equal by theorem (`genuineDensity_eq_decidedDensity_two`, via
`drainage_two`), so every number this script checks is a number about both.)

This script computes `decidedSeq` EXACTLY for O = Z_p, n = 2, small p and N, by brute
force, and compares the numbers with the W-11 corpus
(`../../lean/notes/openmath/W11_PROOF_2026-08-08.md`), whose closed forms are

    undecided count at level N   = q^N                              (exact drainage law)
    ram-decided count            = (q^(2N) - q^(2N-2K)) / (q+1),  K = floor(N/2)
    split-decided = inert-decided = (q^(2N) - q^N - ram) / 2
    limit densities: split = inert = q / (2(q+1)),  ram = 1/(q+1)

DECISION PROCEDURE (exact, not sampled)
---------------------------------------
Over Z_p the splitting type of a monic quadratic x^2 + a1 x + a0 is a function of the
discriminant d = a1^2 - 4 a0 alone:

  * d = 0                                 -> split (perfect square, two equal linear factors)
  * v = v_p(d) odd                        -> ram
  * v even, u = d / p^v :
        p odd : u a QR mod p              -> split       else -> inert
        p = 2 : u = 1 mod 8               -> split
                u = 5 mod 8               -> inert
                u = 3, 7 mod 8            -> ram  (Q_2(sqrt 3), Q_2(sqrt 7) are ramified)

`classify(d mod p^M, p, M)` returns a type only when the answer is forced by d mod p^M
(needs M - v >= 1 for odd p, M - v >= 3 for p = 2, and d != 0 mod p^M); otherwise it
returns None. A class mod p^N is declared sigma-DECIDED iff every one of its refinements
mod p^(N+K) is classified and gives sigma. Since `classify` is sound, and every lift's
d mod p^(N+K) is realized by some (s,t) mod p^K, the counts produced are exact whenever
no refinement comes back None inside a would-be-decided class (reported as `amb`: every undecided class must visibly carry >= 2 distinct types).

Run:  python3 genuine_density_check.py
"""

from fractions import Fraction


def vp(d, p, M):
    """p-adic valuation of a nonzero residue d mod p^M (0 <= d < p^M, d != 0)."""
    v = 0
    while d % p == 0:
        d //= p
        v += 1
    return v, d


def classify(d, p, M):
    """Splitting type forced by d mod p^M, or None if not forced."""
    if d == 0:
        return None                      # v >= M: d could be 0 (split) or anything deeper
    v, u = vp(d, p, M)
    if v % 2 == 1:
        return "ram"
    if p == 2:
        if M - v < 3:
            return None
        r = u % 8
        if r == 1:
            return "split"
        if r == 5:
            return "inert"
        return "ram"                     # r in {3, 7}
    # p odd: u mod p decides
    if M - v < 1:
        return None
    leg = pow(u % p, (p - 1) // 2, p)
    return "split" if leg == 1 else "inert"


def decided_counts(p, N, K):
    """Exact level-N decided counts for monic quadratics over Z_p, using precision N+K."""
    M = N + K
    pN, pK, pM = p ** N, p ** K, p ** M
    counts = {"split": 0, "inert": 0, "ram": 0}
    undecided = 0
    ambiguous = 0            # undecided classes that VISIBLY carry >= 2 distinct types
    for a0 in range(pN):
        for a1 in range(pN):
            types = set()
            for s in range(pK):
                a1p = a1 + pN * s
                base = a1p * a1p
                for t in range(pK):
                    d = (base - 4 * (a0 + pN * t)) % pM
                    types.add(classify(d, p, M))
            if types == {"split"} or types == {"inert"} or types == {"ram"}:
                counts[types.pop()] += 1
            else:
                undecided += 1
                if len(types - {None}) >= 2:
                    ambiguous += 1
    return counts, undecided, ambiguous


def w11_prediction(q, N):
    """W-11 closed forms for the level-N decided counts."""
    K = N // 2
    total = q ** (2 * N)
    undec = q ** N
    ram = (total - q ** (2 * N - 2 * K)) // (q + 1)
    rest = total - undec - ram
    assert rest % 2 == 0, "split/inert counts must be equal"
    return {"split": rest // 2, "inert": rest // 2, "ram": ram}, undec


def limit_densities(q):
    return {
        "split": Fraction(q, 2 * (q + 1)),
        "inert": Fraction(q, 2 * (q + 1)),
        "ram": Fraction(1, q + 1),
    }


def main():
    print("=" * 92)
    print("GENUINE DENSITY CROSS-CHECK  —  n = 2, O = Z_p  (exact enumeration vs W-11)")
    print("=" * 92)
    plan = [(2, [1, 2, 3, 4], 6), (3, [1, 2, 3], 3), (5, [1, 2], 2)]
    all_ok = True
    for p, levels, K in plan:
        q = p
        lim = limit_densities(q)
        print()
        print(f"--- p = q = {p}   (W-11 limits: split = inert = {lim['split']}, "
              f"ram = {lim['ram']}; undecided mass = q^-N) ---")
        print(f"{'N':>2} {'box':>8} | {'split':>8} {'inert':>8} {'ram':>8} {'undec':>8} "
              f"| {'W11 split':>9} {'W11 ram':>8} {'W11 und':>8} | amb | match | decidedSeq(split)")
        for N in levels:
            counts, undec, ambig = decided_counts(p, N, K)
            pred, pundec = w11_prediction(q, N)
            box = q ** (2 * N)
            ok = (counts == pred and undec == pundec and ambig == undec)
            all_ok = all_ok and ok
            seq = Fraction(counts["split"], box)
            print(f"{N:>2} {box:>8} | {counts['split']:>8} {counts['inert']:>8} "
                  f"{counts['ram']:>8} {undec:>8} | {pred['split']:>9} {pred['ram']:>8} "
                  f"{pundec:>8} | {ambig:>3} | {'YES' if ok else 'NO ':>5} | {seq} "
                  f"= {float(seq):.6f}")
        print(f"    sanity: sum of the three limit densities = "
              f"{lim['split'] + lim['inert'] + lim['ram']}")
        print(f"    Lean gate `gate_split_lower`: 1/q^2 = {Fraction(1, q * q)} "
              f"<= density(split) = {lim['split']}  ->  "
              f"{'CONSISTENT' if Fraction(1, q * q) <= lim['split'] else 'VIOLATED'}")
    print()
    print("=" * 92)
    print("ALL CHECKS PASSED" if all_ok else "SOME CHECKS FAILED")
    print("=" * 92)
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
