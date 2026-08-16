#!/usr/bin/env python3
"""REFUTATION of the ∀-lift-pair clause (i) of blueprint nodes H.115 and H.116 (§17.2).

Found 2026-08-16 by the chapter-H §17 transcription fleet (T-1, wave 3, bundle 2) while
transcribing H.115/H.116; recorded here as an executable artifact, exact integer arithmetic
over Z_5, no dependencies.

------------------------------------------------------------------------------------------
WHAT IS REFUTED
------------------------------------------------------------------------------------------
Both nodes state their extraction spec with the centre `w` UNIVERSALLY quantified:

  H.115 (alphaChild_spec)   forall (a : Fin m -> O) (w : O),
                              proj O m N a = c.1 -> residue O w = z ->
                              exists b, (forall i, b i in maximalIdeal O)
                                /\ (monicPoly a).comp (C (pi^k) * (X + C w))
                                     = C (pi^(m*k)) * monicPoly b
                                /\ proj O m (N - m*k) b = (alphaChild pi c h).1

  H.116 (betaChild_spec)    same shape, with the factorisation
                              = C (pi^D) * (monicPoly b * H'),  D = betaContent c k,
                            and  proj O mu (N - D) b = (betaChild pi c h (N - D)).1

`alphaChild pi c h` / `betaChild pi c h M` are FUNCTIONS of the class `c` (and of pi, k, z, M);
`h` is a Prop and carries no data.  So each spec asserts that the extracted child class is
INDEPENDENT of the lift pair (a, w).  It is not: it depends on the centre w BEYOND its residue.

Changing the centre from w to w' = w + d, d in the maximal ideal, is a Taylor shift of the
recentred polynomial,   g_{w'}(y) = g_w(y + d),   so the child's coefficients move by
   b'_j - b_j  =  sum_{i>j} b_i * binom(i,j) * d^(i-j)   +   binom(mu,j) * d^(mu-j),
whose j = mu-1 term is  mu*d  in m \ m^2.  The child is therefore well defined only MODULO m,
i.e. at window 1 -- while the spec reads it at window N - m*k (resp. N - D), which is >= 2 as
soon as m*k <= N - 2.

The transport the blueprint's PROOF field cites for well-definedness -- H.109's lemma half,
"class-determined below the window" -- gives exactly ONE extra digit: `recentre_transport`
concludes  pi^(D+1) | (g_{w'} - g_w).coeff j.  That is enough to make "b i in maximalIdeal O"
lift-independent, and NOT enough to pin the child class at the stated window.

The certifying battery is consistent with this: OM2_genindb_battery.py's `extract_child` uses
`RB.lift_res(z)`, the CANONICAL lift of z -- a coherent centre choice, a function of z alone.
Every P1(d)/P1(f) result (fibres exact + onto, per-genre composition) is a statement about THAT
map and stands.  The ∀-w quantifier is a transcription strengthening the battery never tested.

------------------------------------------------------------------------------------------
CONSEQUENCE (not fixed here -- owner decision)
------------------------------------------------------------------------------------------
Clauses (ii)/(iii) of H.115 and clause (ii) of H.116 are NOT refuted, but they are not
statements about an arbitrary `Exists.choose` body either: `card_alphaFiber`'s exact
`Q^(k*c(m))` FAILS for an incoherent choice function (a choice that sends many parents to the
same child inflates a fibre).  Both nodes need the centre pinned in the DEF, e.g.

    alphaChild pi c h  :=  built at  w := (residue_surj z).choose,  a := (exists_proj_eq c.1).choose

and clause (i) restated with the centre quantified accordingly (`forall a, exists w` / the
canonical w), matching the battery.  Signatures are frozen, so the fleet returned BLOCKED.
"""

import sys

P = 5

def vp(n):
    if n == 0:
        return 10 ** 9
    v = 0
    while n % P == 0:
        n //= P
        v += 1
    return v

def pmul(A, B):
    """polynomials as coefficient lists, low degree first"""
    C = [0] * (len(A) + len(B) - 1)
    for i, x in enumerate(A):
        for j, y in enumerate(B):
            C[i + j] += x * y
    return C

def comp_linear(A, s, t):
    """A(y) |-> A(s*y + t), by Horner"""
    out = [0]
    for co in reversed(A):
        out = pmul(out, [t, s])
        out[0] += co
    return out

def beta_content(a, m, N, k):
    """H.108: D = min_{j<=m} ( min(v(a_j), N) + j*k ), the j=m term being m*k."""
    return min([min(vp(a[j]), N) + j * k for j in range(m)] + [m * k])

def divide_monic(h, b):
    """exact division of h by the monic b (both low-degree-first); returns (quotient, remainder)"""
    num = h[:]
    q = [0] * (len(h) - len(b) + 1)
    for i in range(len(q) - 1, -1, -1):
        q[i] = num[i + len(b) - 1]
        for j, cv in enumerate(b):
            num[i + j] -= q[i] * cv
    return q, num

FAILED = []

def check(name, ok, detail=""):
    print(("PASS  " if ok else "FAIL  ") + name + (("   " + detail) if detail else ""))
    if not ok:
        FAILED.append(name)

# ==========================================================================================
# H.115 -- alpha.   f = (x - 5)^2 over Z_5 :  m = 2, N = 4, k = 1, z = residue 1
# ==========================================================================================

def refute_h115():
    print("\n=== H.115 alphaChild_spec: O = Z_5, f = (x-5)^2, m = 2, N = 4, k = 1, z = 1 ===")
    m, N, k = 2, 4, 1
    f = pmul([-5, 1], [-5, 1])                    # x^2 - 10x + 25
    a = f[:m]                                     # the class c: a_0 = 25, a_1 = -10  (mod 5^4)
    check("c is a cluster state (every coefficient in m)", all(vp(t) >= 1 for t in a),
          "v_p(a) = %s" % [vp(t) for t in a])
    check("c is NON-drain (resOrd(a_0) = 2 <= N-1 = 3)", vp(a[0]) <= N - 1)
    # m = 2 < 4, so H.117 (isCSState_four_le, LANDED) gives  not IsCSState  for free.
    D = beta_content(a, m, N, k)
    check("betaContent c k = m*k (H.112 alpha_content)", D == m * k, "D = %d" % D)

    kids = {}
    for w in (1, 6, 11, -4):
        g = comp_linear(f, P ** k, P ** k * w)
        # HasChildAt pi c m k z, at this lift pair (H.109's three clauses)
        ok1 = all(co % P ** D == 0 for co in g)
        ok2 = all(g[j] % P ** (D + 1) == 0 for j in range(m))
        ok3 = g[m] % P ** (D + 1) != 0
        check("HasChildAt clauses hold at w = %d (residue %d)" % (w, w % P), ok1 and ok2 and ok3)
        b = [g[j] // P ** D for j in range(m)]
        check("  b lies in m (so the child IS a cluster state)", all(vp(t) >= 1 for t in b))
        # the unique b of the spec's factorisation, read at the stated window N - m*k
        kids[w] = tuple(bb % P ** (N - m * k) for bb in b)
        print("      w = %3d -> g = %s -> b = %s -> child mod 5^%d = %s"
              % (w, g, b, N - m * k, list(kids[w])))

    check("REFUTED: the child class DEPENDS on the centre within its residue class",
          len(set(kids.values())) > 1,
          "distinct children over lift pairs of the SAME (c, z): %s" % sorted(set(kids.values())))
    # the well-definedness that DOES hold: one digit, exactly what recentre_transport gives
    check("(and only one digit is class-determined: all children agree mod 5^1)",
          len({tuple(x % P for x in v) for v in kids.values()}) == 1)

# ==========================================================================================
# H.116 -- beta.   f = (x-5)^2 (x-10) over Z_5 :  m = 3, N = 6, k = 1, z = 1, mu = 2
# ==========================================================================================

def refute_h116():
    print("\n=== H.116 betaChild_spec: O = Z_5, f = (x-5)^2(x-10), m = 3, N = 6, k = 1, "
          "z = 1, mu = 2 ===")
    m, N, k, mu = 3, 6, 1, 2
    f = pmul(pmul([-5, 1], [-5, 1]), [-10, 1])    # x^3 - 20x^2 + 125x - 250
    a = f[:m]
    check("c is a cluster state (every coefficient in m)", all(vp(t) >= 1 for t in a),
          "v_p(a) = %s" % [vp(t) for t in a])
    check("c is NON-drain (resOrd(a_0) = 3 <= N-1 = 5)", vp(a[0]) <= N - 1)
    D = beta_content(a, m, N, k)
    M = N - D
    check("child window M = N - betaContent c k is >= 2", M >= 2, "D = %d, M = %d" % (D, M))

    kids = {}
    for w in (1, 6):
        g = comp_linear(f, P ** k, P ** k * w)
        ok1 = all(co % P ** D == 0 for co in g)
        ok2 = all(g[j] % P ** (D + 1) == 0 for j in range(mu))
        ok3 = g[mu] % P ** (D + 1) != 0
        check("HasChildAt pi c 2 1 1 clauses hold at w = %d (residue %d)" % (w, w % P),
              ok1 and ok2 and ok3)
        h = [co // P ** D for co in g]            # the content-divided frame, g / pi^D
        # ALL monic degree-mu factors of h: Z_5[y] is a UFD and h = (y+w-1)^2 (y+w-2) with the
        # three monic irreducible factors listed, so the monic quadratic factors are exactly the
        # two root-subsets below (H' is forced monic of degree 1: degrees add, leading coeffs
        # multiply to 1).
        cands = {"(y+w-1)^2": pmul([w - 1, 1], [w - 1, 1]),
                 "(y+w-1)(y+w-2)": pmul([w - 1, 1], [w - 2, 1])}
        admissible = []
        for name, bp in cands.items():
            q, rem = divide_monic(h, bp)
            exact = all(x == 0 for x in rem)
            in_m = all(vp(bp[j]) >= 1 for j in range(mu))
            print("      w = %d  factor %-16s b = %-12s exact = %s  b in m = %s"
                  % (w, name, bp[:mu], exact, in_m))
            if exact and in_m:
                admissible.append(tuple(bp[j] % P ** M for j in range(mu)))
        check("  exactly ONE monic degree-mu factor has all coefficients in m at w = %d" % w,
              len(admissible) == 1, "admissible children: %s" % admissible)
        kids[w] = admissible[0]

    check("REFUTED: the beta child class DEPENDS on the centre within its residue class",
          kids[1] != kids[6],
          "w=1 -> %s   vs   w=6 -> %s  (mod 5^%d)" % (list(kids[1]), list(kids[6]), M))

if __name__ == "__main__":
    refute_h115()
    refute_h116()
    print("\n%d check(s) failed" % len(FAILED) if FAILED else
          "\nAll checks pass: both ∀-lift-pair specs are refuted by explicit witnesses.")
    sys.exit(1 if FAILED else 0)
