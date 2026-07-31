#!/usr/bin/env python3
"""O9 rev 3 falsifier K6: the (ADM) class-vs-value dichotomy at r = 1.

Pass 2 (O9_pass2_verify.md, Finding 1, CRITICAL) refuted rev 2's (ADM):
its displayed mod-e clause ("beta_k mod e in {wt(j) mod e}") was asserted
"equivalently G_{beta_k} != 0", which is FALSE -- value-attainment also
needs wt(j) <= beta_k for the witnessing ledger index j.  Rev 3 redefines
(ADM) by VALUE-attainment.  This script machine-checks the verifier's
displayed countermodel AND the corrected reading, per the falsifier-first
rule (the countermodel datum must now evaluate 0 = 0).

Instance (the pass-2 countermodel type): r = 1, f0 = f1 = 1, e1 = 3,
h1 = 2 (lambda_1 = -2/3): m = 3, d = 1, e = 3; ledger {1, phi1, phi1^2},
weights {0, 2, 4} (w(phi1) = e1*V1 + h1 = 2, V1 = 0 per the pinned (P3));
Vhat = e1*f1*w(phi1) = 6.  w on {deg < 3} is computed from the pinned
recursion (P1)/(P2)/(P3) directly:  w(c0 + c1*phi1 + c2*phi1^2)
= min_j (3*v_pi(c_j) + 2*j)  -- NOT via Lemma TRI as a black box.
Sibling positive-control type: h1 = 1 (weights {0, 1, 2}, Vhat = 3).

Checks (p in {2, 3}):
  CH1  attained w-set on ({deg<3} \\ 0) mod pi^N is exactly {e*v + wt}
       within [0, eN-1]; at h1 = 2, beta = 1 is CLASS-attained (4 = 1 mod
       3) but VALUE-unattained.
  CH2  #{w >= beta} = p^{mN - s(beta)} (LED(ii)) and the measured
       dim G_beta = #{j : wt(j) = beta mod e AND wt(j) <= beta} -- the
       corrected LED(iii) criterion; in particular G_1 = 0 at h1 = 2.
  CH3  countermodel datum D = (0,8)->(1,7), lambda = {(1,1)}, free box,
       N = 3 ((DET): 8 <= eN-1 = 8): brute-force census = 0 (p = 2 also
       by the fully naive loop over all 2^18 coefficient pairs); rev-3
       prediction ((ADM) fails => padding 0) PASSES 0 = 0; rev-2 mod-e
       reading admits D and its CEN-W display p^8 (p-1)^2 != 0 is REFUTED.
  CH4  positive control, h1 = 1, same face data (beta = (8, 4), (ADM)
       holds): census == p^{E'} (p-1)^2 = p^4 (p-1)^2 exactly (16 / 324).
       Membership at this datum is purely valuation-level: d(S) = 1, so
       type {(1,1)} <=> both vertex digits nonzero <=> exact w at both
       slots (any invertible per-slot twist preserves nonzeroness).
  CH5  the r = 1 decidable inequality  beta >= h1*((h1^{-1} beta) mod e1)
       <=> value-attainment, for all beta <= 30, both types; failure
       exhibited at (h1 = 2, beta = 1): threshold 4 > 1.
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


def make_w(p, N, e1, wphi1, m=3):
    """w on triples (c0..c_{m-1}) mod p^N from the pinned recursion:
    min_j (e1*v_pi(c_j) + j*wphi1), v capped at N (>= eN territory)."""
    def w(c):
        return min(e1 * vcap(c[j], p, N) + j * wphi1 for j in range(m))
    return w


def s_of(beta, weights, e):
    """s(beta) = sum_j max(0, ceil((beta - wt_j)/e))  (LED(ii))."""
    return sum(max(0, (beta - wt + e - 1) // e) for wt in weights)


def value_attained(beta, weights, e):
    return any((beta - wt) % e == 0 and wt <= beta for wt in weights)


def class_attained(beta, weights, e):
    return any((beta - wt) % e == 0 for wt in weights)


def run_type(p, N, e1, h1, verts):
    print(f"== type e1={e1}, h1={h1}, p={p}, N={N}: "
          f"weights and box layer ==")
    V1 = 0
    wphi1 = e1 * V1 + h1
    e, m, d = e1, 3, 1
    weights = [j * wphi1 for j in range(m)]
    Vhat = e1 * 1 * wphi1          # e1*f1*w(phi1), f1 = 1
    eN = e * N
    w = make_w(p, N, e1, wphi1)
    box = list(itertools.product(range(p ** N), repeat=m))

    # CH1: attained w-set on nonzero elements
    attained = sorted({w(c) for c in box if any(c)} & set(range(eN)))
    expect = sorted({e * v + wt for wt in weights for v in range(N + 1)}
                    & set(range(eN)))
    check(f"CH1 attained w-set == {{e*v+wt}} on [0,{eN - 1}]",
          attained == expect, f"attained={attained}")

    # CH2: LED(ii) counts + measured graded dims vs corrected criterion
    ok2 = True
    for beta in range(eN):
        cnt = sum(1 for c in box if w(c) >= beta)
        cnt1 = sum(1 for c in box if w(c) >= beta + 1)
        led = p ** (m * N - s_of(beta, weights, e))
        dim_meas = 0
        q = cnt // cnt1
        while q > 1:
            q //= p
            dim_meas += 1
        dim_crit = sum(1 for wt in weights
                       if (beta - wt) % e == 0 and wt <= beta)
        if cnt != led or cnt % cnt1 or cnt // cnt1 != p ** dim_crit:
            ok2 = False
            print(f"      beta={beta}: cnt={cnt} led={led} "
                  f"dim_meas={dim_meas} dim_crit={dim_crit}")
    check("CH2 #{{w>=beta}}==p^(mN-s) and dim G_beta == corrected criterion",
          ok2)
    if h1 == 2:
        g1 = sum(1 for c in box if w(c) >= 1) == sum(
            1 for c in box if w(c) >= 2)
        check("CH2b G_1 = 0 (s(2) = s(1)): 1 class-attained, value-unattained",
              g1 and class_attained(1, weights, e)
              and not value_attained(1, weights, e))

    # Census layer for the single-face datum verts = [(0,U0),(1,U1)]
    (k0, U0), (k1, U1) = verts
    betas = [U0 - 0 * Vhat, U1 - 1 * Vhat]
    assert max(betas) <= eN - 1, "DET violated"
    n_exact = [sum(1 for c in box if w(c) == b) for b in betas]
    census_slotprod = n_exact[0] * n_exact[1]

    # E' and the CEN-W free-box display
    L = 2
    Eprime = sum(m * N - s_of(b, weights, e) for b in betas) - d * L
    M_11 = p - 1                       # M_{(1,1)}(p^d), d = 1
    display = p ** Eprime * (p ** d - 1) * M_11

    adm_new = all(value_attained(b, weights, e) for b in betas)
    adm_old = all(class_attained(b, weights, e) for b in betas)
    pred_new = display if adm_new else 0
    pred_old = display if adm_old else 0
    print(f"   datum (0,{U0})->(1,{U1}): Vhat={Vhat}, betas={betas}, "
          f"E'={Eprime}, display={display}, (ADM)new={adm_new}, "
          f"(ADM)mod-e={adm_old}, census={census_slotprod}")
    return (betas, census_slotprod, pred_new, pred_old, display,
            weights, e, Vhat, w)


def naive_pair_census(p, N, w, betas):
    """Fully naive loop over ((Z/p^N)^3)^2: exact w at both slots."""
    cnt = 0
    rng = range(p ** N)
    for c0 in itertools.product(rng, repeat=3):
        if w(c0) != betas[0]:
            continue
        for c1 in itertools.product(rng, repeat=3):
            if w(c1) == betas[1]:
                cnt += 1
    return cnt


def main():
    for p in (2, 3):
        # --- countermodel type h1 = 2: datum (0,8)->(1,7), betas (8,1) ---
        (betas, census, pred_new, pred_old, display, weights, e, Vhat, w) \
            = run_type(p, 3, 3, 2, [(0, 8), (1, 7)])
        check("CH3 countermodel census == 0 (empty by the valuation layer)",
              census == 0)
        check("CH3 rev-3 prediction ((ADM) fails => padding 0) == truth",
              pred_new == 0 == census, f"pred={pred_new}")
        check("CH3 rev-2 mod-e reading REFUTED (admits D, display != 0)",
              pred_old == display != 0,
              f"mod-e display={pred_old} vs truth 0")
        if p == 2:
            naive = naive_pair_census(p, 3, w, betas)
            check("CH3b naive 2^18-pair loop agrees (census 0)",
                  naive == 0, f"naive={naive}")

        # --- positive control h1 = 1: same face, betas (8,4), (ADM) holds --
        (betas, census, pred_new, pred_old, display, weights, e, Vhat, w) \
            = run_type(p, 3, 3, 1, [(0, 8), (1, 7)])
        check("CH4 (ADM) holds and census == p^E' (p-1)^2 == display",
              pred_new == display == census != 0,
              f"census={census}, display={display}")
        if p == 2:
            naive = naive_pair_census(p, 3, w, betas)
            check("CH4b naive 2^18-pair loop agrees",
                  naive == census, f"naive={naive}")

    # CH5: the r = 1 decidable inequality <=> value-attainment
    for e1, h1, f1 in ((3, 2, 1), (3, 1, 1), (4, 3, 2), (5, 2, 1)):
        weights = [j * h1 for j in range(e1 * f1)]  # j0-part weight 0
        hinv = pow(h1, -1, e1)
        ok = all(value_attained(b, weights, e1)
                 == (b >= h1 * ((hinv * b) % e1)) for b in range(31))
        check(f"CH5 r=1 inequality <=> value-attainment (e1={e1}, h1={h1}, "
              f"f1={f1})", ok)
    thr = 2 * ((pow(2, -1, 3) * 1) % 3)
    check("CH5b countermodel: threshold at beta=1 is 4 > 1",
          thr == 4)

    print(f"\nRESULT: {'ALL PASS' if NFAIL == 0 else f'{NFAIL} FAILURES'}")
    return NFAIL


if __name__ == "__main__":
    raise SystemExit(main())
