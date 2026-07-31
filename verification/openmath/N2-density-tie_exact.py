#!/usr/bin/env python3
"""N2-density-tie (part 1/3): EXACT side — R_sigma tables + symbolic gates + n=2 exact census.

CONJECTURE UNDER TEST (M04 = BK.series_tie, lean/LeanUrat/MovesU/BridgeKernels.lean:223,
same field as SolveSeam.series_tie, lean/LeanUrat/MovesU/DefsLedger.lean:573):

    series_tie : forall sigma : SplittingType n,
      F.seriesSum sigma = ENNReal.ofReal (C.chain.Rval (vmap C.T sigma) (p : Q))

EXACT MAPPING Lean -> computation (the fidelity contract):

  * `SplittingType n` (MovesU/Defs.lean:30) = multiset of pairs (e_i, f_i), entries >= 1,
    Sigma e_i * f_i = n.  Computed here as sorted tuples of (e,f) — same encoding as
    om_density_engine and quartic_oracle.full_type.

  * `F.seriesSum sigma` (Defs.lean: FiberSeries.seriesSum = sum' over trees T of mass(T),
    mass = Haar mass of the canonical fiber of T): via the seam identities
    (TreeSeam.count_tie, DefsLedger.lean:235: X.decided sigma N = p^{nN} * slice mass) this
    is lim_N decided_sigma(N)/p^{nN} over the level-N box `Box p n N = Fin n -> ZMod (p^N)`
    — the n FREE COEFFICIENTS OF A MONIC DEGREE-n POLYNOMIAL (Defs.lean:36).  So the
    measured object is the Haar density, over MONIC degree-n polynomials with Z_p
    coefficients (coefficients uniform in Z_p^n), of the set with splitting type sigma.
    ==> The ensemble is MONIC (not projective).  This is confirmed by the W6q census
    ledger (verification/census_n2_uniform.py, tied to the Lean W6q blueprint): its n=2
    targets R_ram = 1/(q+1), R_inert = R_split = q/(2(q+1)) are exactly the MONIC
    alpha(2, sigma; q) of the engine (gate G2 below re-proves this symbolically).

  * `C.chain.Rval (vmap C.T sigma) p`: an abstract field of the UCarriers chain, pinned by
    the chain laws (rsh_interp) to the evaluation at q = p of the fixed rational function
    R_sigma(q) that the solve produces.  Its INTENDED INSTANCE (docs/HUMAN_PROOF.md,
    definitions section: alpha(n, sigma; q) = the monic density; the projective
    rho(n, sigma; q) is the M1-bridged companion) is realized computationally by
    om_density_engine:  alpha_full(n)[sigma] (monic) resp. rho(n)[sigma] (projective).
    We compute BOTH exactly (sympy rational functions in q, cluster laws beta_4/beta_5
    from the curated caches results/beta{4,5}.json, exactly as reconcile_om_bcfg.py does)
    and evaluate at q = p in {2,3,5} as exact Fractions.

  SO the computable surrogate of M04 tested by this unit is:

      density_{Haar, monic deg-n / Z_p}( splitting type = sigma )  =  alpha(n, sigma; p)

  for n in {2,3,4,5}, p in {2,3,5} (all wild pairs p <= n included), with the projective
  companion  density_{P^n(Q_p)}(sigma) = rho(n, sigma; p)  tested as the global sanity
  (it is the ensemble reconcile_om_bcfg.py reconciles against BCFG).

FLAGGED SIMPLIFICATIONS (honesty ledger):
  (S1) `Rval` is abstract data in Lean; we test its intended instance (the engine's
       R_sigma), not the Lean term itself.  If the empirical densities match alpha, the
       conjecture's VALUE claim is confirmed for the instance the project intends to build.
  (S2) `seriesSum`'s tree decomposition is not reproduced; we test its value (the sigma
       density), which is exactly what series_tie pins.  ENNReal.ofReal is trivial here
       (densities lie in [0,1] — gate G5 checks 0 <= alpha_sigma(p) <= 1).
  (S3) The n=2 exact census (this file) uses the discriminant square-class classifier,
       not the Lean OM canonical classifier; ANY sound classifier gives the exact
       sandwich decided_sigma(N) <= true density <= decided_sigma(N) + envelope(N), so
       the interval test on the VALUE is faithful even though the classifier differs.

WHAT THIS SCRIPT DOES:
  1. Exact tables alpha(n)[sigma](q), rho(n)[sigma](q) for n = 2..5 (sympy, exact).
  2. Symbolic gates:
       G1  sum_sigma alpha = 1 and sum_sigma rho = 1 (n = 2..5);
       G2  alpha(2) == W6q Lean-ledger anchors {ram 1/(q+1), inert = split q/(2(q+1))};
       G3  rho(3) == the five paper/cert_crosschecks section-10 densities;
       G4  (record) alpha(n) != rho(n) — the two ensembles genuinely differ;
       G5  0 <= alpha_sigma(p) <= 1 and 0 <= rho_sigma(p) <= 1 for p in {2,3,5}.
  3. n=2 EXACT census over the full box mod p^N ((p,N) = (2,20), (3,12), (5,8)):
     count ALL p^{2N} monic quadratic classes (x^2 + a1 x + a0), classified
     split/inert/ram/undecided by the disc square-class oracle, and check EXACTLY
     (Fraction arithmetic)
         decided_sigma(N)/p^{2N}  <=  alpha(2,sigma;p)  <=  decided_sigma(N)/p^{2N} + env(N)
     with envelope width ~1e-5.  The count is exact but collapsed: the type depends on
     (a1,a0) only through d = a1^2 - 4 a0, and for each a1 the fiber structure of
     a0 |-> d is uniform (p odd: bijection; p = 2: d uniform on {d = 1 mod 4} for odd a1
     and d = 4u, u uniform mod 2^{N-2}, for even a1 — each with constant fiber 4).  The
     collapsed weighted count is GATED against the direct p^{2N} double loop at small N
     (exact equality of all four counters) before being used at large N.
     This is the exhaustive-enumeration leg of the charge (no sampling, no floats).
  4. Writes results/N2-density-tie_R_exact.json (exact rational values, both ensembles,
     all (n,p)) for the MC comparison script.

Run:  PYTHONPATH=~/.local/lib/python3.10/site-packages python3 N2-density-tie_exact.py
      (from verification/openmath/; ~6 min, pure CPU, no PARI needed)
"""
import sys, os, time, json
from fractions import Fraction
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
VERIF = os.path.dirname(HERE)
sys.path.insert(0, VERIF)
os.chdir(VERIF)  # engine + beta caches expect verification/ as cwd

import sympy as sp
import om_density_engine as E

q = E.q
T0 = time.time()
def log(m):
    print(f"[{time.time()-T0:7.1f}s] {m}", flush=True)

FAIL = []
def gate(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}  {detail}", flush=True)
    if not ok:
        FAIL.append(name)

# ---------------------------------------------------------------- exact tables
def loadbeta(e):
    return {eval(k): sp.cancel(sp.sympify(v, locals={'q': q}))
            for k, v in json.load(open(f'results/beta{e}.json')).items()}

BET = {1: {((1, 1),): sp.Integer(1)}, 2: E.beta(2), 3: E.beta(3),
       4: loadbeta(4), 5: loadbeta(5)}
log("cluster laws beta_1..beta_5 loaded (2,3 from engine anchors; 4,5 curated caches)")

def cluster_law(m, delta):
    """L_m^{(delta)}: beta_m at q^delta, f-degrees scaled by delta (M1 base change)."""
    out = {}
    for tau, prob in BET[m].items():
        pr = sp.cancel(prob.subs(q, q ** delta))
        mapped = tuple(sorted((e, f * delta) for (e, f) in tau))
        out[mapped] = sp.cancel(out.get(mapped, sp.Integer(0)) + pr)
    return out

def density(n, projective):
    """alpha_full(n) (projective=False) / rho(n) (projective=True), replicating
    om_density_engine.alpha_full / .rho but with the cached high-order betas
    (exactly the reconcile_om_bcfg.py approach)."""
    norm = E.Pn_count(n) if projective else q**n
    cfg_fn = E._proj_config_count if projective else E._affine_config_count
    acc = defaultdict(lambda: sp.Integer(0))
    for pattern in E._divisor_patterns(n):
        cfg = cfg_fn(pattern)
        dists = [{((1, d),): sp.Integer(1)} if m == 1 else cluster_law(m, d)
                 for (d, m) in pattern]
        agg = {(): sp.Integer(1)}
        for dist in dists:
            new = defaultdict(lambda: sp.Integer(0))
            for ta, pa in agg.items():
                for tb, pb in dist.items():
                    new[E.type_union([ta, tb])] += pa * pb
            agg = dict(new)
        for t, pr in agg.items():
            acc[t] += cfg * pr
    return {t: sp.cancel(v / norm) for t, v in acc.items()}

ALPHA, RHO = {}, {}
for n in range(2, 6):
    ALPHA[n] = density(n, False)
    RHO[n] = density(n, True)
    log(f"n={n}: {len(ALPHA[n])} monic types, {len(RHO[n])} projective types")

# ---------------------------------------------------------------- gates
# G1: exhaustiveness sum = 1
for n in range(2, 6):
    gate(f"G1 sum_sigma alpha({n}) == 1", sp.simplify(sum(ALPHA[n].values()) - 1) == 0)
    gate(f"G1 sum_sigma rho({n})   == 1", sp.simplify(sum(RHO[n].values()) - 1) == 0)

# G2: n=2 monic anchors == the W6q Lean-ledger values (census_n2_uniform.py header)
w6q = {((2, 1),): 1/(q+1), ((1, 2),): q/(2*(q+1)), ((1, 1), (1, 1)): q/(2*(q+1))}
for t, v in w6q.items():
    gate(f"G2 alpha(2)[{t}] == W6q ledger {v}",
         sp.simplify(ALPHA[2][t] - v) == 0, f"engine: {sp.factor(ALPHA[2][t])}")

# G3: rho(3) == paper / cert_crosschecks section-10 densities
Phi = q**4 + q**3 + q**2 + q + 1
paper3 = {((1, 1), (1, 1), (1, 1)): (q**2+1)**2/(6*Phi),
          ((1, 1), (1, 2)):         (q**4+1)/(2*Phi),
          ((1, 3),):                (q**4-q**2+1)/(3*Phi),
          ((1, 1), (2, 1)):         (q**3+q)/Phi,
          ((3, 1),):                q**2/Phi}
for t, v in paper3.items():
    gate(f"G3 rho(3)[{t}] == paper", sp.simplify(RHO[3][t] - v) == 0)

# G4 (record): the ensembles genuinely differ
for n in range(2, 6):
    diff = any(sp.simplify(ALPHA[n].get(t, 0) - RHO[n].get(t, 0)) != 0
               for t in set(ALPHA[n]) | set(RHO[n]))
    log(f"G4 record: alpha({n}) != rho({n}) as rational functions: {diff}")

# G5: evaluations at p in {2,3,5} are genuine probabilities (ENNReal.ofReal fidelity)
PRIMES = (2, 3, 5)
def evalp(table, p):
    return {t: Fraction(int(sp.Rational(sp.cancel(v.subs(q, p))).p),
                        int(sp.Rational(sp.cancel(v.subs(q, p))).q))
            for t, v in table.items()}

VAL = {"monic": {}, "proj": {}}
ok5 = True
for n in range(2, 6):
    VAL["monic"][n], VAL["proj"][n] = {}, {}
    for p in PRIMES:
        va, vr = evalp(ALPHA[n], p), evalp(RHO[n], p)
        VAL["monic"][n][p], VAL["proj"][n][p] = va, vr
        if not all(0 <= x <= 1 for x in list(va.values()) + list(vr.values())):
            ok5 = False
        if sum(va.values()) != 1 or sum(vr.values()) != 1:
            ok5 = False
gate("G5 all alpha_sigma(p), rho_sigma(p) in [0,1] and sum exactly 1 (p=2,3,5, n=2..5)", ok5)

# ---------------------------------------------------------------- n=2 exact census
# Disc square-class classifier (verbatim logic of census_n2_uniform.qp_type, W6q suite),
# stated on the discriminant d = a1^2 - 4 a0 directly.
def v_p(x, p, cap):
    if x == 0:
        return cap
    v = 0
    while x % p == 0:
        x //= p; v += 1
    return v

def qp_type_d(d, p, N):
    """split/inert/ram/undecided for a monic quadratic with disc = d (mod p^N)."""
    if d == 0:
        return 'und'
    v = v_p(d, p, N)
    if p == 2:
        if v >= N - 3:
            return 'und'
        u = (d >> v) % 8
        if v % 2 == 1:
            return 'ram'
        return 'split' if u == 1 else ('inert' if u == 5 else 'ram')
    if v >= N - 1:
        return 'und'
    u = (d // p ** v) % p
    if v % 2 == 1:
        return 'ram'
    return 'split' if pow(u, (p - 1) // 2, p) == 1 else 'inert'

def census_direct(p, N):
    """Direct O(p^{2N}) double loop over the whole level-N box (ground truth gate)."""
    M = p ** N
    cnt = {'split': 0, 'inert': 0, 'ram': 0, 'und': 0}
    for a1 in range(M):
        s = a1 * a1
        for a0 in range(M):
            cnt[qp_type_d((s - 4 * a0) % M, p, N)] += 1
    return cnt

def census_fast(p, N):
    """Exact collapsed census (counts over the p^{2N} box, computed in O(p^N)).

    p odd: 4 invertible, so for each of the p^N values of a1 the map a0 -> d is a
      bijection of Z/p^N; weight p^N per d-value.
    p = 2: (i) a1 odd (2^{N-1} values): 4*a0 mod 2^N covers 4Z/2^N with fiber 4, so
      d = a1^2 - 4 a0 is uniform on the coset {d = 1 mod 4} (2^{N-2} values, fiber 4).
      (ii) a1 = 2t even (2^{N-1} values): d = 4(t^2 - a0) = 4u with u = (t^2 - a0)
      mod 2^{N-2} uniform (fiber 4), independent of t.
      Both weights: 2^{N-1} * 4 per d-value.  Gated against census_direct at small N."""
    M = p ** N
    cnt = {'split': 0, 'inert': 0, 'ram': 0, 'und': 0}
    if p != 2:
        for d in range(M):
            cnt[qp_type_d(d, p, N)] += M
        return cnt
    w = (1 << (N - 1)) * 4
    for k in range(M // 4):                    # odd a1: d = 1 mod 4
        cnt[qp_type_d(4 * k + 1, 2, N)] += w
    for u in range(M // 4):                    # even a1: d = 4u
        cnt[qp_type_d((4 * u) % M, 2, N)] += w
    return cnt

# gate the collapsed census against the direct double loop at small N
for p, Nsmall in ((2, 8), (3, 4), (5, 3)):
    gate(f"census collapse == direct double loop (p={p}, N={Nsmall})",
         census_fast(p, Nsmall) == census_direct(p, Nsmall))

T2 = {'split': ((1, 1), (1, 1)), 'inert': ((1, 2),), 'ram': ((2, 1),)}
CENSUS = {}
for p, N in ((2, 20), (3, 12), (5, 8)):
    cnt = census_fast(p, N)
    tot = p ** (2 * N)
    assert sum(cnt.values()) == tot
    box = {k: Fraction(v, tot) for k, v in cnt.items()}
    env = box['und']
    CENSUS[p] = {"N": N, "counts": cnt, "env": str(env)}
    log(f"census n=2 p={p} N={N}: decided masses "
        + ", ".join(f"{k}={box[k]}" for k in ('split', 'inert', 'ram'))
        + f", envelope={env} (~{float(env):.2e})")
    for name, t in T2.items():
        R = VAL["monic"][2][p][t]
        lo, hi = box[name], box[name] + env
        gate(f"census n=2 p={p} sigma={name}: alpha(2;{p})={R} in interval",
             lo <= R <= hi,
             f"[{float(lo):.10f}, {float(hi):.10f}], R={float(R):.10f}, width {float(env):.2e}")

# ---------------------------------------------------------------- dump exact values
def typekey(t):
    return json.dumps(sorted([list(x) for x in t]))

out = {"meta": {
        "conjecture": "M04 BK.series_tie (BridgeKernels.lean:223 / DefsLedger.lean:573)",
        "surrogate": "density_{Haar, monic deg-n/Z_p}(sigma) = alpha(n,sigma;p); "
                     "projective companion rho as global sanity",
        "primes": list(PRIMES), "ns": list(range(2, 6))},
       "monic": {}, "proj": {}, "census_n2": CENSUS,
       "symbolic": {"monic": {}, "proj": {}}}
for n in range(2, 6):
    out["monic"][n] = {p: {typekey(t): str(v) for t, v in VAL["monic"][n][p].items()}
                       for p in PRIMES}
    out["proj"][n] = {p: {typekey(t): str(v) for t, v in VAL["proj"][n][p].items()}
                      for p in PRIMES}
    out["symbolic"]["monic"][n] = {typekey(t): str(sp.factor(v)) for t, v in ALPHA[n].items()}
    out["symbolic"]["proj"][n] = {typekey(t): str(sp.factor(v)) for t, v in RHO[n].items()}

dst = os.path.join(VERIF, "results", "N2-density-tie_R_exact.json")
json.dump(out, open(dst, "w"), indent=1)
log(f"exact tables written to {dst}")

print()
print("=" * 72)
print(f"EXACT SIDE: {len(FAIL)} gate failures" + (f": {FAIL}" if FAIL else " — all gates PASS"))
print("=" * 72)
sys.exit(1 if FAIL else 0)
