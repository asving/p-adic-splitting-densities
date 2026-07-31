#!/usr/bin/env python3
"""O9 rev 4 falsifier K7: the (ADM) value-vs-FULL dichotomy at r = 1, d = 2.

Pass 3 (O9_pass3_verify.md, Finding 1, CRITICAL) refuted rev 3's (ADM):
VALUE-attainment (G_{beta_k} != 0, i.e. dim >= 1) is strictly weaker than
what Sec 5.1 / 6.3 / 6.4 consume -- fiber-uniformity of the digit read
ONTO F_{r+1}, which by the proved LED(ii)/(iii) forces FULL attainment
dim_{F_q} G_{beta_k} = s(beta_k + 1) - s(beta_k) = d.  At a PARTIALLY
attained on-line slot (0 < dim < d) the read's image is a proper
F_q-subspace (LED-top(ii)'s phenomenon on the FULL ledger) and CEN-W's
display overcounts by (q+1)/q per such slot.  Rev 4 restates (ADM) at
FULL attainment.  This script machine-checks the verifier's displayed
countermodel AND the rev-4 predicate, per the falsifier-first rule --
including, at last, a d >= 2 VALUE gate: a datum where the FULL (ADM)
HOLDS and CEN-W's display must equal brute-force truth exactly.

Instance (the pass-3 countermodel type T2): r = 1, f0 = 1, e1 = 1,
f1 = 2, h1 = 2 (lambda_1 = -2): m = 2, d = 2, e = 1; ledger {1, phi1}
with weights {0, 2} (w(phi1) = e1*V1 + h1 = 2, V1 = 0 per the pinned
(P3)); Vhat = e1*f1*w(phi1) = 4.  w on {deg < 2} from the pinned
recursion (P1)/(P2), one step: w(c0 + c1*phi1) = min(v(c0), v(c1) + 2).

Checks (p in {2, 3}):
  CH1  lattice layer at T2: attained w-set == {v + wt}; measured
       dim G_beta == #{j : wt(j) = beta mod e, wt(j) <= beta} (LED(iii))
       at every beta; FULL (dim = d) <=> beta >= 2 <=> the displayed
       r = 1 full-attainment inequality; beta in {0, 1} PARTIAL
       (0 < dim = 1 < d = 2) yet VALUE-attained -- rev 3's (ADM) admits
       them, rev 4's does not.
  CH2  the pass-3 countermodel D1 = (0,6)->(1,5), lambda = {(1,1)},
       free box, N = 7 ((DET): 6 <= eN - 1 = 6): brute-force truth
       = q^14 (q^2-1)(q-1)  [49152 / 76527504]; the rev-3 display
       q^13 (q^2-1)^2  [73728 / 102036672] is REFUTED (ratio (q+1)/q);
       rev 4 fences D1 OUT ((ADM) FULL fails at slot 1: dim G_1 = 1 < 2
       though beta_1 = 1 is value-attained -- rev 3 asserted the display
       there).  CH2b: p = 2 corroborated by the naive joint pair loop.
       CH2c: localization -- slot 0 (FULL) matches its displayed
       per-slot factor (q^d-1) q^{mN-s-d}; slot 1 (PARTIAL) matches the
       rev-4 Sec 5.1 image-subspace law (q^{dim}-1) q^{mN-s-dim}, NOT
       the onto-F_{r+1} law (q^d-1) q^{mN-s-d}.
  CH3  the d >= 2 POSITIVE CONTROL D2 = (0,7)->(1,6), same type, N = 8
       ((DET): 7 <= eN - 1 = 7; (ADM) FULL HOLDS: betas (7,2), both
       dim = 2 = d): brute-force census == q^{E'} (q^d-1) M_{(1,1)}(q^d)
       = q^14 (q^2-1)^2 EXACTLY  [147456 / 306110016].  Membership is
       purely valuation-level (d(S) = 1 vertices force type {(1,1)};
       vertex nonvanishing <=> exact w).  CH3b: p = 2 naive pair loop.
  CH4  K6 regression under the FULL predicate (the m = 3, d = 1, f1 = 1
       types, where FULL <=> VALUE): the h1 = 2 countermodel datum still
       evaluates 0 = 0; the h1 = 1 positive control still p^4 (p-1)^2.
  CH5  the r = 1 FULL inequality
           beta >= h1*( ((h1^{-1} beta) mod e1) + (f1 - 1)*e1 )
       <=> #{class members with wt <= beta} == d = f0*f1, all beta <= 40,
       at 7 (e1, h1, f1, f0) tuples; the f1 = 1 collapse to rev 3's
       VALUE inequality; (CLASS-d): every class mod e1 contains exactly
       d ledger indices.  CH5b: at T2 the FULL threshold is 2 while the
       VALUE threshold is 0 -- beta_1 = 1 passes VALUE, fails FULL.

Independence note (disclosed): all census layers share the one-step
pinned w-recursion with the formula side (as in K6); the naive loops and
the v-census convolution independently check the slot-product structure
and every count, not w itself.  CH2c is an arithmetic-consistency
display of the Sec 5.1 image law against LED(ii); the enumeration is the
independent leg.
"""
import itertools

NFAIL = 0


def check(name, cond, detail=""):
    global NFAIL
    tag = "PASS" if cond else "FAIL"
    if not cond:
        NFAIL += 1
    print(f"  [{tag}] {name}{('  ' + detail) if detail else ''}")


def vcap(x, p, N):
    if x % p ** N == 0:
        return N
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def s_of(beta, weights, e):
    """s(beta) = sum_j max(0, ceil((beta - wt_j)/e))  (LED(ii))."""
    return sum(max(0, (beta - wt + e - 1) // e) for wt in weights)


def dim_crit(beta, weights, e):
    """LED(iii): dim G_beta = #{j : wt = beta mod e AND wt <= beta}."""
    return sum(1 for wt in weights if (beta - wt) % e == 0 and wt <= beta)


def thr_val(beta, e1, h1):
    """rev-3 VALUE threshold: minimal weight in beta's class."""
    j1s = (pow(h1, -1, e1) * beta) % e1 if e1 > 1 else 0
    return h1 * j1s


def thr_full(beta, e1, h1, f1):
    """rev-4 FULL threshold: maximal weight in beta's class."""
    j1s = (pow(h1, -1, e1) * beta) % e1 if e1 > 1 else 0
    return h1 * (j1s + (f1 - 1) * e1)


# ---------------- T2: m = 2, d = 2, e = 1, weights {0, 2} ----------------
W2 = [0, 2]


def w2(c0, c1, p, N):
    return min(vcap(c0, p, N), vcap(c1, p, N) + 2)


def vcensus(p, N):
    cv = [0] * (N + 1)
    for c in range(p ** N):
        cv[vcap(c, p, N)] += 1
    return cv


def slot_counts_T2(p, N):
    """#{(c0,c1) mod p^N : w = beta} for all beta, by v-census convolution
    (exact: w depends only on (v(c0), v(c1)); cv by direct enumeration)."""
    cv = vcensus(p, N)
    cnt = {}
    for a in range(N + 1):
        for b in range(N + 1):
            beta = min(a, b + 2)
            cnt[beta] = cnt.get(beta, 0) + cv[a] * cv[b]
    return cnt


def naive_slot_counts_T2(p, N):
    cnt = {}
    for c0 in range(p ** N):
        for c1 in range(p ** N):
            beta = w2(c0, c1, p, N)
            cnt[beta] = cnt.get(beta, 0) + 1
    return cnt


def ch1_lattice(p, N):
    d, e, m = 2, 1, 2
    eN = e * N
    cnt = slot_counts_T2(p, N)
    ge = {b: sum(v for k, v in cnt.items() if k >= b) for b in range(eN + 1)}
    attained = sorted(k for k, v in cnt.items() if v > 0 and k < eN)
    expect = sorted({v + wt for wt in W2 for v in range(N + 1)}
                    & set(range(eN)))
    check(f"CH1 attained w-set == {{v+wt}} on [0,{eN - 1}] (p={p})",
          attained == expect, f"attained={attained}")
    ok = True
    for beta in range(eN):
        led = p ** (m * N - s_of(beta, W2, e))
        dc = dim_crit(beta, W2, e)
        if ge[beta] != led or ge[beta] != ge[beta + 1] * p ** dc:
            ok = False
            print(f"      beta={beta}: cnt={ge[beta]} led={led} dim_crit={dc}")
    check(f"CH1 LED(ii) counts + dim G_beta == LED(iii) criterion (p={p})", ok)
    full = [beta for beta in range(eN) if dim_crit(beta, W2, e) == d]
    ineq = [beta for beta in range(eN)
            if beta >= thr_full(beta, 1, 2, 2)]
    check(f"CH1 FULL <=> beta >= 2 <=> displayed r=1 inequality (p={p})",
          full == ineq == list(range(2, eN)))
    check(f"CH1 beta in {{0,1}} PARTIAL (dim 1) yet VALUE-attained (p={p})",
          all(dim_crit(b, W2, e) == 1 and b >= thr_val(b, 1, 2)
              for b in (0, 1)))


def census_T2(p, N, betas, cnt=None):
    if cnt is None:
        cnt = slot_counts_T2(p, N)
    return cnt.get(betas[0], 0) * cnt.get(betas[1], 0)


def naive_pair_census_T2(p, N, betas):
    """Naive joint loop over ((Z/p^N)^2)^2: exact w at both slots."""
    tot = 0
    rng = range(p ** N)
    slot0 = [(c0, c1) for c0 in rng for c1 in rng
             if w2(c0, c1, p, N) == betas[0]]
    for _ in slot0:
        for c0 in rng:
            for c1 in rng:
                if w2(c0, c1, p, N) == betas[1]:
                    tot += 1
    return tot


def run_T2_datum(p, N, verts, name):
    d, e, m = 2, 1, 2
    Vhat = 4
    (k0, U0), (k1, U1) = verts
    betas = [U0 - k0 * Vhat, U1 - k1 * Vhat]
    assert max(U0 - k0 * Vhat, U1 - k1 * Vhat) <= e * N - 1, "DET violated"
    cnt = slot_counts_T2(p, N)
    truth = census_T2(p, N, betas, cnt)
    L = 2
    Ep = sum(m * N - s_of(b, W2, e) for b in betas) - d * L
    M11 = p ** d - 1                    # M_{(1,1)}(p^d)
    display = p ** Ep * (p ** d - 1) * M11
    adm_val = all(dim_crit(b, W2, e) >= 1 for b in betas)
    adm_full = all(dim_crit(b, W2, e) == d for b in betas)
    print(f"   {name} p={p}, N={N}, datum (0,{U0})->(1,{U1}): betas={betas},"
          f" E'={Ep}, display={display}, truth={truth},"
          f" (ADM)value={adm_val}, (ADM)FULL={adm_full}")
    return betas, truth, display, adm_val, adm_full, cnt, Ep


def main():
    print("== CH1: T2 lattice layer ==")
    ch1_lattice(2, 7)
    ch1_lattice(3, 5)

    for p in (2, 3):
        print(f"== CH2: pass-3 countermodel D1, p={p} ==")
        N = 7
        betas, truth, display, adm_val, adm_full, cnt, Ep = \
            run_T2_datum(p, N, [(0, 6), (1, 5)], "D1")
        q = p
        mN = 2 * N
        check("CH2 truth == q^14 (q^2-1)(q-1) (enumerated)",
              truth == q ** 14 * (q ** 2 - 1) * (q - 1), f"truth={truth}")
        check("CH2 rev-3 display REFUTED ((ADM)value admits D1)",
              adm_val and display != truth and Ep == 13,
              f"display={display} vs truth={truth}, ratio (q+1)/q")
        check("CH2 display * q == truth * (q+1)  [the (q+1)/q ratio]",
              display * q == truth * (q + 1))
        check("CH2 rev-4 fences D1 OUT ((ADM) FULL fails: dim G_1 = 1 < 2)",
              not adm_full and dim_crit(betas[1], W2, 1) == 1)
        # CH2c localization
        s0, s1 = s_of(betas[0], W2, 1), s_of(betas[1], W2, 1)
        d0, d1 = dim_crit(betas[0], W2, 1), dim_crit(betas[1], W2, 1)
        check("CH2c slot 0 (FULL) == (q^d-1) q^{mN-s-d}",
              cnt[betas[0]] == (q ** 2 - 1) * q ** (mN - s0 - 2))
        check("CH2c slot 1 (PARTIAL) == image law (q^dim-1) q^{mN-s-dim}"
              " != onto law (q^d-1) q^{mN-s-d}",
              cnt[betas[1]] == (q ** d1 - 1) * q ** (mN - s1 - d1)
              and cnt[betas[1]] != (q ** 2 - 1) * q ** (mN - s1 - 2))
        if p == 2:
            check("CH2b naive joint pair loop agrees",
                  naive_pair_census_T2(p, N, betas) == truth)

        print(f"== CH3: d >= 2 positive control D2, p={p} ==")
        N = 8
        betas, truth, display, adm_val, adm_full, cnt, Ep = \
            run_T2_datum(p, N, [(0, 7), (1, 6)], "D2")
        check("CH3 (ADM) FULL HOLDS (betas (7,2), both dim = d = 2)",
              adm_full and betas == [7, 2])
        check("CH3 census == q^{E'} (q^d-1) M_{(1,1)}(q^d) == q^14 (q^2-1)^2",
              truth == display == q ** 14 * (q ** 2 - 1) ** 2 and Ep == 14,
              f"census={truth}")
        if p == 2:
            check("CH3b naive joint pair loop agrees",
                  naive_pair_census_T2(p, N, betas) == truth)

    # CH4: K6 regression (m = 3, d = 1, f1 = 1) under the FULL predicate
    print("== CH4: K6 regression under (ADM) FULL ==")
    for p in (2, 3):
        for h1, expect_zero in ((2, True), (1, False)):
            e1, N, m, d, e = 3, 3, 3, 1, 3
            wphi1 = h1
            weights = [j * wphi1 for j in range(m)]
            Vhat = 3 * wphi1
            betas = [8, 7 - Vhat]

            def w3(c):
                return min(3 * vcap(c[j], p, N) + j * wphi1 for j in range(m))
            box = itertools.product(range(p ** N), repeat=m)
            cnt = {}
            for c in box:
                cnt[w3(c)] = cnt.get(w3(c), 0) + 1
            truth = cnt.get(betas[0], 0) * cnt.get(betas[1], 0)
            adm_full = all(dim_crit(b, weights, e) == d for b in betas)
            Ep = sum(m * N - s_of(b, weights, e) for b in betas) - d * 2
            display = p ** Ep * (p ** d - 1) * (p - 1)
            pred = display if adm_full else 0
            check(f"CH4 h1={h1}, p={p}: FULL<=>VALUE (f1=1) and pred==truth",
                  pred == truth and (truth == 0) == expect_zero
                  and all((dim_crit(b, weights, e) == d)
                          == (dim_crit(b, weights, e) >= 1)
                          for b in range(9)),
                  f"pred={pred}, truth={truth}")

    # CH5: the r = 1 FULL inequality + (CLASS-d)
    print("== CH5: the r = 1 FULL-attainment inequality ==")
    tuples = ((1, 2, 2, 1), (3, 2, 1, 1), (3, 1, 1, 1), (3, 2, 2, 1),
              (3, 2, 2, 2), (4, 3, 2, 1), (5, 2, 3, 1))
    for e1, h1, f1, f0 in tuples:
        d = f0 * f1
        weights = [j1 * h1 for j1 in range(e1 * f1) for _ in range(f0)]
        ok_full = all((dim_crit(b, weights, e1) == d)
                      == (b >= thr_full(b, e1, h1, f1)) for b in range(41))
        ok_val = all((dim_crit(b, weights, e1) >= 1)
                     == (b >= thr_val(b, e1, h1)) for b in range(41))
        ok_classd = all(sum(1 for wt in weights if wt % e1 == c) == d
                        for c in range(e1))
        collapse = (f1 != 1) or all(thr_full(b, e1, h1, f1)
                                    == thr_val(b, e1, h1) for b in range(41))
        check(f"CH5 (e1,h1,f1,f0)=({e1},{h1},{f1},{f0}): FULL ineq <=> "
              f"count==d; VALUE ineq regression; (CLASS-d); f1=1 collapse",
              ok_full and ok_val and ok_classd and collapse)
    check("CH5b T2: FULL threshold 2 > 1 = beta_1 >= 0 = VALUE threshold",
          thr_full(1, 1, 2, 2) == 2 and thr_val(1, 1, 2) == 0)

    print(f"\nRESULT: {'ALL PASS' if NFAIL == 0 else f'{NFAIL} FAILURES'}")
    return NFAIL


if __name__ == "__main__":
    raise SystemExit(main())
