"""BCFGTIE battery — the expectation recursion, the closed form E_n = q/(q+1),
the BCFG moment tie, and the SEVENTEEN quintic densities (GENH5-DENS).

Unit: BCFGTIE 2026-08-08 (Asvin's computability question).  Note:
lean/notes/openmath/BCFGTIE_2026-08-08.md (sealed predictions in S10 there).

SUPPLIERS (pinned as-of HEAD 0a1f409):
  om_density_engine.py                     md5 7240a916060c360d4433ca8a802d315d
  reconcile_om_bcfg.py (standing check)    md5 5401a09dfa872d858d04cab6f2ab863f
  results/beta4.json                       md5 7fa70670148e92d2ee75ab24d774d1fe
  results/beta5.json                       md5 139d06f028612299c122d831cfd92bbe
  results/beta6.json                       md5 323354674db4b65885b4d54559bd61ba
  results/bcfg_distribution_final.json     md5 63cb388f78f4a54f3495cb659c43306a
                                           (BCFG = arXiv:2101.09590 per verification/README.md)

STRUCTURE (checks C1..C8 + teeth T1..T4):
  C1  eps_m := E[#(1,1)-factors under the cluster law beta_m] == 1/(q+1), m=2..6, symbolic.
  C2  MONIC E_n by the level-0 telescope (I) == q/(q+1), n=2..6, symbolic;
      cross-route: E_n by full type-sum over the affine assembly (independent path
      through the same betas) == telescope, n=2..6.
  C3  PROJECTIVE E_n^proj == 1 (n=2..6, symbolic, both routes); BCFG raw1 rows == 1.
  C4  Deep-count law P_m(j): closed form vs exact finite enumeration (symbolic m<=5,
      exact-rational q in {2,3,5,7} at m=6,7); sum_j P_m(j) == 1 (m<=10, symbolic);
      KEY IDENTITY  q*P_m(0) - P_m(1) == q-1  (m<=10, symbolic).
  C5  Lemma-B machine tie:  eps_m(engine) == sum_j P_m(j) * E_j  (m=2..6, symbolic)
      with E_0=0, E_1=1, E_j the telescope values.
  C6  Quintic densities rho(5): SEVENTEEN types; Sigma == 1 symbolic; per-pattern
      partial sums cross-foot (sum over types of each pattern's contribution == cfg/b5,
      all 17 patterns); root-count aggregation == the committed BCFG n=5 rows;
      numeric sanity 0 < R_tau < 1 at q in {2,3,4,5,7,8,9,11,13}.
  C7  Full reconcile re-run hook (run reconcile_om_bcfg.py separately; C7 here re-does
      the dist comparison n=2..6 in-process from the same JSON).
  C8  Menu-growth table (#types(n), #patterns(n), n<=10) for the complexity display.
  T1  TOOTH: min-argmin mutant deep-count law P~ — KEY identity must FAIL (m=3,4).
  T2  TOOTH: eps-mutant q/(q+1)^2 — telescope vs cross-route must FAIL at n=2.
  T3  TOOTH: density mutant, swap R_{(1,1)^5} <-> R_{(1,5)} — Sigma=1 PASSES but the
      BCFG root-aggregation must FAIL (r=5 and r=0 rows move).
  T4  TOOTH: density mutant, bump one entry by q^{-9} — Sigma=1 must FAIL.

Run:  python3 bcfgtie_checks.py            (exit 0 iff all checks pass and all teeth bite)
Artifacts: bcfgtie_results.json + stdout log.
"""
import sys, os, time, json, math
from collections import defaultdict
from fractions import Fraction
from itertools import product as iproduct

HERE = os.path.dirname(os.path.abspath(__file__))
VERIF = os.path.dirname(HERE)
sys.path.insert(0, VERIF)

import sympy as sp
import om_density_engine as E

q = E.q
T0 = time.time()
LOG = []
def log(m):
    line = f"[{time.time()-T0:7.1f}s] {m}"
    print(line, flush=True)
    LOG.append(line)

FAILS = []
CHECKS = 0
def check(name, ok):
    global CHECKS
    CHECKS += 1
    log(f"  {'PASS' if ok else '*** FAIL ***'}  {name}")
    if not ok:
        FAILS.append(name)

def eqz(expr):
    """Robust symbolic == 0 for rational functions of q."""
    c = sp.cancel(sp.together(expr))
    if c == 0:
        return True
    s = sp.simplify(c)
    return s == 0

# ---------------------------------------------------------------- betas ----
def loadbeta(e):
    fn = os.path.join(VERIF, 'results', f'beta{e}.json')
    return {eval(k): sp.cancel(sp.sympify(v, locals={'q': q}))
            for k, v in json.load(open(fn)).items()}

BET = {1: {((1, 1),): sp.Integer(1)}, 2: E.beta(2), 3: E.beta(3),
       4: loadbeta(4), 5: loadbeta(5), 6: loadbeta(6)}
for e in BET:
    assert all(sp.simplify(sum(BET[e].values()).subs(q, p)) == 1 for p in [2, 3, 5, 7]), \
        f"beta{e} sum != 1"
log("betas 1..6 loaded, sum=1 sanity ok")

def Ncount(tau):
    return sum(1 for ef in tau if ef == (1, 1))

# ---------------------------------------------------------------- C1: eps ----
log("== C1: cluster-law root yields eps_m ==")
EPS = {m: sp.cancel(sum(p * Ncount(t) for t, p in BET[m].items())) for m in BET}
target_eps = 1 / (q + 1)
check("eps_1 == 1", eqz(EPS[1] - 1))
for m in range(2, 7):
    check(f"eps_{m} == 1/(q+1)   [got {sp.cancel(EPS[m])}]", eqz(EPS[m] - target_eps))

# ------------------------------------------------- assemblies (cached betas) ----
def cluster_scaled(m, delta):
    out = {}
    for tau, prob in BET[m].items():
        pr = sp.cancel(prob.subs(q, q ** delta))
        mt = tuple(sorted((e, f * delta) for (e, f) in tau))
        out[mt] = sp.cancel(out.get(mt, sp.Integer(0)) + pr)
    return out

def assemble(n, projective):
    """Full type distribution at degree n (affine/monic or projective), cached betas."""
    acc = defaultdict(lambda: sp.Integer(0))
    for pattern in E._divisor_patterns(n):
        cfg = (E._proj_config_count(pattern) if projective
               else E._affine_config_count(pattern))
        dists = []
        for (delta, m) in pattern:
            if m == 1:
                dists.append({((1, delta),): sp.Integer(1)})
            else:
                dists.append(cluster_scaled(m, delta))
        agg = {(): sp.Integer(1)}
        for dist in dists:
            new = defaultdict(lambda: sp.Integer(0))
            for t0, p0 in agg.items():
                for t1, p1 in dist.items():
                    new[E.type_union([t0, t1])] += p0 * p1
            agg = dict(new)
        for t, p in agg.items():
            acc[t] += cfg * p
    norm = E.Pn_count(n) if projective else q ** n
    return {t: sp.cancel(v / norm) for t, v in acc.items()}

def pattern_partials(n, projective):
    """Per-pattern total mass (should be cfg/norm each; cross-foot audit)."""
    out = {}
    for pattern in E._divisor_patterns(n):
        cfg = (E._proj_config_count(pattern) if projective
               else E._affine_config_count(pattern))
        norm = E.Pn_count(n) if projective else q ** n
        out[pattern] = sp.cancel(cfg / norm)
    return out

# ---------------------------------------------------------------- C2: monic ----
log("== C2: MONIC E_n — telescope (I) vs full type-sum ==")
def telescope_monic(n, eps):
    return sp.cancel(q * (sum((1 - 1/q) * q**(-k) * eps[k] for k in range(1, n))
                          + q**(-n) * eps[n]))

EMON = {}
for n in range(2, 7):
    EMON[n] = telescope_monic(n, EPS)
    check(f"E_{n} (telescope) == q/(q+1)   [got {EMON[n]}]", eqz(EMON[n] - q/(q+1)))
for n in range(2, 7):
    alpha = assemble(n, projective=False)
    tot = sp.cancel(sum(alpha.values()))
    check(f"monic assembly n={n}: Sigma == 1", eqz(tot - 1))
    e_route2 = sp.cancel(sum(p * Ncount(t) for t, p in alpha.items()))
    check(f"E_{n} cross-route (type-sum) == telescope", eqz(e_route2 - EMON[n]))

# ------------------------------------------------------------ C3: projective ----
log("== C3: PROJECTIVE E_n == 1; BCFG raw1 rows ==")
B = json.load(open(os.path.join(VERIF, 'results', 'bcfg_distribution_final.json')))
def bget(sec, n, r):
    k = f"{n},{r}"
    return sp.cancel(sp.sympify(B[sec][k], locals={'q': q})) if k in B[sec] else None

RHO = {}
for n in range(2, 7):
    RHO[n] = assemble(n, projective=True)
    check(f"proj assembly n={n}: Sigma == 1", eqz(sum(RHO[n].values()) - 1))
    eproj = sp.cancel(sum(p * Ncount(t) for t, p in RHO[n].items()))
    check(f"E_{n}^proj (type-sum) == 1", eqz(eproj - 1))
    # telescope route: E^proj = (q+1) * sum_k eps_k q^(n-k) / b_n
    bn = E.Pn_count(n)
    et = sp.cancel((q + 1) * sum(EPS[k] * q**(n - k) for k in range(1, n + 1)) / bn)
    check(f"E_{n}^proj (telescope) == 1", eqz(et - 1))
    braw = bget('raw', n, 1)
    check(f"BCFG raw1 row n={n} == 1 (committed)", braw is not None and eqz(braw - 1))

# ------------------------------------------------------- C4: deep-count law ----
log("== C4: deep-count law P_m(j) ==")
def P_geq(s):     # P(u >= s), u = v(a_i)-1 under the cluster conditioning
    return q ** (-max(s, 0))
def P_eq(s):
    return (1 - 1/q) * q ** (-s) if s >= 0 else sp.Integer(0)

def Pmj(m, j):
    """Closed form: P(exactly j of the m cluster roots have valuation >= 1)."""
    if j == m:
        return q ** sp.Integer(-(m * (m - 1) // 2))
    tot = sp.Integer(0)
    for mu in range(j + 1, m):
        term = P_eq(mu - j - 1)
        for k in range(0, j):
            term *= P_geq(mu - k - 1)          # ties allowed left of j (max-argmin)
        for k in range(j + 1, m):
            term *= P_geq(mu - k)              # strict right of j
        tot += term
    return sp.cancel(tot)

def Pmj_brute(m, qval=None):
    """Exact enumeration: u_i in {0..m} with u_i=m meaning 'u_i >= m' (all event
    thresholds are <= m-1, so the cap is exact).  Symbolic if qval is None."""
    if qval is None:
        one, Q = sp.Integer(1), q
    else:
        one, Q = Fraction(1), Fraction(qval)
    out = defaultdict(lambda: 0 * one)
    for u in iproduct(range(m + 1), repeat=m):
        w = one
        for s in u:
            w *= (1 - 1/Q) * Q**(-s) if s < m else Q**(-m)
        tvals = [i + u[i] + 1 for i in range(m)] + [m]
        mn = min(tvals)
        j = max(i for i, t in enumerate(tvals) if t == mn)
        out[j] += w
    return out

for m in range(2, 11):
    check(f"sum_j P_{m}(j) == 1", eqz(sum(Pmj(m, j) for j in range(m + 1)) - 1))
    check(f"KEY IDENTITY q*P_{m}(0) - P_{m}(1) == q-1",
          eqz(q * Pmj(m, 0) - Pmj(m, 1) - (q - 1)))
for m in range(2, 6):
    br = Pmj_brute(m)
    ok = all(eqz(Pmj(m, j) - br.get(j, sp.Integer(0))) for j in range(m + 1))
    check(f"P_{m}(j) closed form == brute enumeration (symbolic, all j)", ok)
for m in (6, 7):
    for p in (2, 3, 5, 7):
        br = Pmj_brute(m, qval=p)
        ok = all(Fraction(str(sp.nsimplify(Pmj(m, j).subs(q, p)))) == br.get(j, Fraction(0))
                 for j in range(m + 1))
        check(f"P_{m}(j) closed form == brute enumeration (q={p}, exact rational)", ok)

# --------------------------------------------------------- C5: Lemma-B tie ----
log("== C5: Lemma B machine tie  eps_m == sum_j P_m(j) E_j ==")
EJ = {0: sp.Integer(0), 1: sp.Integer(1)}
for jj in range(2, 7):
    EJ[jj] = EMON[jj]
for m in range(2, 7):
    rhs = sp.cancel(sum(Pmj(m, j) * EJ[j] for j in range(m + 1)))
    check(f"eps_{m} (engine) == sum_j P_{m}(j) E_j   [rhs={rhs}]", eqz(EPS[m] - rhs))

# ------------------------------------------------------- C6: quintic table ----
log("== C6: THE SEVENTEEN QUINTIC DENSITIES (projective rho(5)) ==")
rho5 = RHO[5]
check("n=5 type count == 17", len(rho5) == 17)
# per-pattern partial-sum cross-foot: for each of the 17 patterns, its total
# contribution over all types must equal cfg/b5 exactly (cluster laws are mass 1).
b5 = E.Pn_count(5)
pat_ok = True
pat_partials = {}
for pattern in E._divisor_patterns(5):
    cfg = E._proj_config_count(pattern)
    dists = []
    for (delta, m) in pattern:
        dists.append({((1, delta),): sp.Integer(1)} if m == 1 else cluster_scaled(m, delta))
    tot = sp.Integer(1)
    for d in dists:
        tot = sp.cancel(tot * sum(d.values()))
    contrib = sp.cancel(cfg * tot / b5)
    pat_partials[str(pattern)] = str(contrib)
    if not eqz(contrib - cfg / b5):
        pat_ok = False
check("per-pattern partial sums: contribution == cfg/b5, all 17 patterns", pat_ok)
check("sum of pattern partials == 1",
      eqz(sum(E._proj_config_count(p) for p in E._divisor_patterns(5)) / b5 - 1))
# root-count aggregation vs committed BCFG rows
dist5 = defaultdict(lambda: sp.Integer(0))
for t, v in rho5.items():
    dist5[Ncount(t)] += v
for r in range(0, 6):
    bc = bget('dist', 5, r)
    om = sp.cancel(dist5.get(r, sp.Integer(0)))
    check(f"P(5,{r}) OM == BCFG committed", bc is not None and eqz(om - bc))
# numeric sanity at prime powers
num_ok = True
for p in (2, 3, 4, 5, 7, 8, 9, 11, 13):
    vals = {t: sp.Rational(sp.nsimplify(v.subs(q, p))) for t, v in rho5.items()}
    if not all(0 < v < 1 for v in vals.values()) or sum(vals.values()) != 1:
        num_ok = False
check("numeric sanity: 0 < R_tau < 1 and Sigma == 1 exactly at 9 prime powers", num_ok)
QUINTIC = {str(t): str(sp.cancel(v)) for t, v in sorted(rho5.items())}
for t, v in sorted(rho5.items()):
    log(f"    R_{t} = {sp.factor(sp.cancel(v))}")

# ------------------------------------------------------ C7: BCFG dist tie ----
log("== C7: full dist tie n=2..6 vs committed BCFG rows (in-process) ==")
all_match = True
for n in range(2, 7):
    dist = defaultdict(lambda: sp.Integer(0))
    for t, v in RHO[n].items():
        dist[Ncount(t)] += v
    for r in range(0, n + 1):
        bc = bget('dist', n, r)
        om = sp.cancel(dist.get(r, sp.Integer(0)))
        ok = eqz(om - (bc if bc is not None else sp.Integer(0)))
        if not ok:
            all_match = False
check("ALL P(n,r) n=2..6 match committed BCFG rows", all_match)

# ------------------------------------------------------- C8: menu growth ----
log("== C8: menu growth (computability display) ==")
GROWTH = {}
for n in range(2, 11):
    ntypes = len(E._enumerate_cluster_types(n))
    npats = len(E._divisor_patterns(n))
    GROWTH[n] = (ntypes, npats)
    log(f"    n={n}: #types = {ntypes}, #divisor patterns = {npats}")
check("#types(4) == 11 (GENH4's ELEVEN)", GROWTH[4][0] == 11)
check("#types(5) == 17", GROWTH[5][0] == 17)

# ----------------------------------------------------------------- teeth ----
log("== TEETH ==")
def Pmj_mut(m, j):
    """T1 mutant: min-argmin convention (strictness swapped)."""
    if j == m:
        # j = m under min-argmin: all t_k > ... strict everywhere below m
        tot = sp.Integer(1)
        for k in range(0, m):
            tot *= P_geq(m - k)
        return sp.cancel(tot)
    tot = sp.Integer(0)
    for mu in range(j + 1, m + 1):
        term = P_eq(mu - j - 1)
        for k in range(0, j):
            term *= P_geq(mu - k)              # strict LEFT of j now
        for k in range(j + 1, m):
            term *= P_geq(mu - k - 1)          # ties allowed RIGHT of j
        tot += term
    return sp.cancel(tot)

t1 = all(not eqz(q * Pmj_mut(m, 0) - Pmj_mut(m, 1) - (q - 1)) for m in (3, 4))
check("T1 bites: min-argmin mutant FAILS the KEY identity (m=3,4)", t1)

eps_mut = dict(EPS); eps_mut[2] = q / (q + 1)**2
t2 = not eqz(telescope_monic(2, eps_mut) - q/(q+1))
check("T2 bites: eps-mutant q/(q+1)^2 breaks E_2 == q/(q+1)", t2)

k_split = tuple(sorted([(1, 1)] * 5)); k_inert = ((1, 5),)
mut = dict(rho5); mut[k_split], mut[k_inert] = mut[k_inert], mut[k_split]
sig_ok = eqz(sum(mut.values()) - 1)
d5m = defaultdict(lambda: sp.Integer(0))
for t, v in mut.items():
    d5m[Ncount(t)] += v
t3 = sig_ok and (not eqz(d5m[5] - bget('dist', 5, 5))) and (not eqz(d5m[0] - bget('dist', 5, 0)))
check("T3 bites: swap mutant passes Sigma=1 but FAILS BCFG rows r=0,5", t3)

mut2 = dict(rho5); mut2[k_inert] = mut2[k_inert] + q**(-9)
t4 = not eqz(sum(mut2.values()) - 1)
check("T4 bites: bump mutant FAILS Sigma == 1", t4)

# ------------------------------------------------------------- artifacts ----
verdict = "GREEN" if not FAILS else "RED"
out = {
    "unit": "BCFGTIE_2026-08-08",
    "verdict": verdict, "checks": CHECKS, "fails": FAILS,
    "eps": {str(m): str(EPS[m]) for m in EPS},
    "E_monic": {str(n): str(EMON[n]) for n in EMON},
    "quintic_densities": QUINTIC,
    "pattern_partials_n5": pat_partials,
    "menu_growth": {str(n): GROWTH[n] for n in GROWTH},
    "elapsed_s": round(time.time() - T0, 1),
    "log": LOG,
}
json.dump(out, open(os.path.join(HERE, 'bcfgtie_results.json'), 'w'), indent=1)
log(f"DONE {verdict}: {CHECKS} checks, {len(FAILS)} fails -> bcfgtie_results.json")
sys.exit(0 if verdict == "GREEN" else 1)
