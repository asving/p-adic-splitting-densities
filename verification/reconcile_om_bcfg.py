"""Reconcile OM-engine root-count distribution vs BCFG.
Self-contained: recompute OM rho(n) for n=2..6 (betas: n=2,3 from anchors; 4,5,6 cached),
aggregate to P(n,r;q) by root count, compare to BCFG's P(n,r;q) symbolically.
Also compares moments. Reports sum_r=1 per n."""
import sys, time, json
import sympy as sp
from collections import defaultdict
import om_density_engine as E
q = E.q
T0 = time.time()
def log(m): print(f"[{time.time()-T0:7.1f}s] {m}", flush=True)

# ---- load betas ----
def loadbeta(e):
    return {eval(k): sp.cancel(sp.sympify(v, locals={'q': q}))
            for k, v in json.load(open(f'results/beta{e}.json')).items()}
BET = {1: {((1, 1),): sp.Integer(1)}, 2: E.beta(2), 3: E.beta(3),
       4: loadbeta(4), 5: loadbeta(5), 6: loadbeta(6)}
log("betas loaded (1..6)")

# sanity: every beta sums to 1
for e in BET:
    s = sum(BET[e].values())
    chk = all(sp.simplify(s.subs(q, p)) == 1 for p in [2, 3, 5, 7])
    assert chk, f"beta{e} sum!=1"
log("beta sum=1 sanity PASS")

def cluster_law_proj_fast(m, delta):
    out = {}
    for tau, prob in BET[m].items():
        pr = sp.cancel(prob.subs(q, q ** delta))
        mapped = tuple(sorted((e, f * delta) for (e, f) in tau))
        out[mapped] = sp.cancel(out.get(mapped, sp.Integer(0)) + pr)
    return out

def rhoN(n):
    Pn = E.Pn_count(n)
    acc = defaultdict(lambda: sp.Integer(0))
    for pattern in E._divisor_patterns(n):
        cfg = E._proj_config_count(pattern)
        point_dists = []
        for (delta, m) in pattern:
            if m == 1:
                point_dists.append({((1, delta),): sp.Integer(1)})
            else:
                point_dists.append(cluster_law_proj_fast(m, delta))
        agg = {(): sp.Integer(1)}
        for dist in point_dists:
            new = defaultdict(lambda: sp.Integer(0))
            for t0, p0 in agg.items():
                for t1, p1 in dist.items():
                    new[E.type_union([t0, t1])] += p0 * p1
            agg = dict(new)
        for t, p in agg.items():
            acc[t] += cfg * p
    return {t: sp.cancel(v / Pn) for t, v in acc.items()}

def Ncount(tau):
    return sum(1 for (e, f) in tau if (e, f) == (1, 1))

# ---- compute OM distribution P(n,r;q) for n=2..6 ----
OM_dist = {}
OM_sum = {}
OM_moments = {}
for n in range(2, 7):
    r = rhoN(n)
    # exhaustive sum gate
    tot = sp.cancel(sum(r.values()))
    OM_sum[n] = tot
    dist = defaultdict(lambda: sp.Integer(0))
    for t, v in r.items():
        dist[Ncount(t)] += v
    dist = {rr: sp.cancel(v) for rr, v in dist.items()}
    OM_dist[n] = dist
    # moments
    def falling(rr, d):
        p = sp.Integer(1)
        for i in range(d):
            p *= (rr - i)
        return p
    mom = {}
    for d in range(0, n + 1):
        mom[f"fac{d}"] = sp.cancel(sum(v * falling(rr, d) for rr, v in dist.items()))
    for k in range(1, 5):
        mom[f"raw{k}"] = sp.cancel(sum(v * sp.Integer(rr) ** k for rr, v in dist.items()))
    OM_moments[n] = mom
    log(f"OM n={n}: {len(r)} types, support r={sorted(dist)}, sum_types={tot}")

# ---- load BCFG ----
B = json.load(open('results/bcfg_distribution_final.json'))
def bget(sec, n, r):
    k = f"{n},{r}"
    if k in B[sec]:
        return sp.cancel(sp.sympify(B[sec][k], locals={'q': q}))
    return None
log("BCFG loaded")

# ---- compare P(n,r;q) ----
print("\n===== P(n,r;q) comparison (OM vs BCFG), exact symbolic diff =====")
all_match = True
rows = []
for n in range(2, 7):
    maxr = n
    for rr in range(0, maxr + 1):
        om = OM_dist[n].get(rr, sp.Integer(0))
        bc = bget('dist', n, rr)
        if bc is None:
            bc = sp.Integer(0)  # absent => 0
        diff = sp.simplify(om - bc)
        eq = (diff == 0)
        if not eq:
            all_match = False
        rows.append((n, rr, eq, om, bc, diff))
        print(f"n={n} r={rr}: EQUAL={eq}  diff={diff}")
print(f"\nALL P(n,r) MATCH: {all_match}")

# ---- sum_r = 1 ----
print("\n===== sum_r P(n,r;q) = 1 (OM) and (BCFG) =====")
for n in range(2, 7):
    om_s = sp.simplify(sum(OM_dist[n].values()))
    # BCFG sum
    bc_terms = [bget('dist', n, rr) for rr in range(0, n + 1)]
    bc_terms = [t for t in bc_terms if t is not None]
    bc_s = sp.simplify(sum(bc_terms))
    print(f"n={n}: OM sum_r={om_s}  | BCFG sum_r={bc_s}  | OM types-sum={sp.simplify(OM_sum[n])}")

# ---- moments comparison ----
print("\n===== Moments comparison =====")
for n in range(2, 7):
    print(f"--- n={n} ---")
    for k in range(1, 5):
        om = OM_moments[n][f"raw{k}"]
        bc = bget('raw', n, k)
        eq = (bc is not None) and (sp.simplify(om - bc) == 0)
        print(f"  E[N^{k}]: OM={om} | BCFG={'(none)' if bc is None else bc} | EQUAL={eq}")
    for d in range(1, n + 1):
        om = OM_moments[n][f"fac{d}"]
        bc = bget('fac', n, d)
        eq = (bc is not None) and (sp.simplify(om - bc) == 0)
        print(f"  E[(N)_{d}]: OM={om} | BCFG={'(none)' if bc is None else bc} | EQUAL={eq}")

# Save machine-readable
out = {
    "OM_dist": {f"{n},{rr}": str(OM_dist[n].get(rr, sp.Integer(0))) for n in range(2,7) for rr in range(0,n+1)},
    "matches": {f"{n},{rr}": bool(eq) for (n, rr, eq, *_ ) in rows},
    "all_match": bool(all_match),
}
json.dump(out, open('results/reconcile_om_bcfg.json', 'w'), indent=1)
log("DONE_RECONCILE")
