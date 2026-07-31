#!/usr/bin/env python3
"""N2-density-tie (part 3/3): STATISTICS + VERDICT — exact R_sigma(p) vs empirical
splitting-type densities.

CONJECTURE UNDER TEST: M04 = BK.series_tie (BridgeKernels.lean:223 / DefsLedger.lean:573).
Surrogate + fidelity contract: see N2-density-tie_exact.py's header.  This part joins
  results/N2-density-tie_R_exact.json      (exact alpha/rho values, Fractions)
  results/N2-density-tie_mc_monic.json     (PARI-oracle counts, monic ensemble = the
                                            Lean Box measure -> tests alpha = Rval)
  results/N2-density-tie_mc_proj.json      (projective ensemble -> tests rho, the
                                            reconcile_om_bcfg-reconciled companion)
and reports, per (n, p, sigma):

  z = (obs - N*R) / sqrt(N*R*(1-R))   for cells with expected count N*R >= RARE_MIN;
  cells with N*R < RARE_MIN are pooled into one RARE bucket per (n,p) (z on the pooled
  binomial), so no normal approximation is applied where it is invalid;
  any observed type with R = 0 (impossible per the engine) is an immediate flag.

DECISION RULE (per the unit charge): any sigma off by more than 4 standard errors =>
MIXED/REFUTED with the data; otherwise the configuration passes.  A per-(n,p)
chi-square over the binned cells is reported as a second, aggregate view (p-value via
the regularized upper incomplete gamma, mpmath).

Run:  python3 N2-density-tie_report.py   (from verification/openmath/, after parts 1+2)
"""
import json, math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(os.path.dirname(HERE), "results")
RARE_MIN = 25.0
FLAG_SE = 4.0

from mpmath import gammainc


def chi2_sf(x, df):
    if df <= 0:
        return float('nan')
    return float(gammainc(df / 2.0, x / 2.0, regularized=True))


def canon(key):
    """canonical type key from either GP or python json: sorted tuple of (e,f)."""
    return tuple(sorted(tuple(x) for x in json.loads(key)))


def fr(s):
    from fractions import Fraction
    return Fraction(s)


EX = json.load(open(os.path.join(RES, "N2-density-tie_R_exact.json")))

overall_flags = []
summary_rows = []

for ensemble, mcfile, exkey, rname in (
        ("monic (Lean Box measure)", "N2-density-tie_mc_monic.json", "monic",
         "alpha(n,sigma;p)"),
        ("projective P^n(Q_p)", "N2-density-tie_mc_proj.json", "proj",
         "rho(n,sigma;p)")):
    path = os.path.join(RES, mcfile)
    if not os.path.exists(path):
        print(f"[skip] {path} missing — run N2-density-tie_mc.py first")
        continue
    MC = json.load(open(path))
    print("=" * 78)
    print(f"ENSEMBLE: {ensemble}   —   exact target {rname}")
    print("=" * 78)
    for cfg in sorted(MC, key=lambda s: (int(s.split(',')[0]), int(s.split(',')[1]))):
        n, p = map(int, cfg.split(','))
        rec = MC[cfg]
        N = sum(rec["counts"].values())
        R = {canon(k): fr(v) for k, v in EX[exkey][str(n)][str(p)].items()}
        obs = {canon(k): v for k, v in rec["counts"].items()}
        wild = "WILD (p<=n)" if p <= n else "tame"
        print(f"\n--- n={n} p={p}  [{wild}]  N={N}  seed={rec['seed']} "
              f"maxvdisc={rec['maxvdisc']} ---")
        print(f"{'sigma':40s} {'R exact':>12s} {'expected':>10s} {'observed':>9s} "
              f"{'z':>7s}")
        impossible = {t: c for t, c in obs.items() if t not in R}
        chi2, df = 0.0, 0
        rareR, rareO = 0.0, 0
        flags = []
        for t in sorted(R, key=lambda t: -R[t]):
            Rf = float(R[t]); exp = Rf * N; o = obs.get(t, 0)
            if exp < RARE_MIN:
                rareR += Rf; rareO += o
                print(f"{str(t):40s} {Rf:12.3e} {exp:10.1f} {o:9d}   RARE->pooled")
                continue
            se = math.sqrt(N * Rf * (1 - Rf))
            z = (o - exp) / se
            chi2 += (o - exp) ** 2 / (N * Rf); df += 1
            mark = "  <-- FLAG >4SE" if abs(z) > FLAG_SE else ""
            print(f"{str(t):40s} {Rf:12.6f} {exp:10.1f} {o:9d} {z:7.2f}{mark}")
            if abs(z) > FLAG_SE:
                flags.append((t, Rf, o, z))
        # pooled rare bucket (binomial z on the pooled mass; guards the normal approx)
        if rareR > 0 or rareO > 0:
            exp = rareR * N
            if exp >= 5:
                se = math.sqrt(N * rareR * (1 - rareR))
                z = (rareO - exp) / se
                chi2 += (rareO - exp) ** 2 / max(N * rareR, 1e-12); df += 1
                mark = "  <-- FLAG >4SE" if abs(z) > FLAG_SE else ""
                print(f"{'RARE pool':40s} {rareR:12.3e} {exp:10.1f} {rareO:9d} "
                      f"{z:7.2f}{mark}")
                if abs(z) > FLAG_SE:
                    flags.append(("RARE pool", rareR, rareO, z))
            else:
                # tiny pooled mass: exact Poisson-style bound instead of z
                lam = exp
                tail_ok = rareO <= lam + 6 * math.sqrt(lam + 1) + 6
                print(f"{'RARE pool':40s} {rareR:12.3e} {exp:10.1f} {rareO:9d} "
                      f"   (Poisson check {'ok' if tail_ok else 'FLAG'})")
                if not tail_ok:
                    flags.append(("RARE pool (poisson)", rareR, rareO, float('nan')))
        for t, c in impossible.items():
            print(f"{str(t):40s} {'R = 0':>12s} {0.0:10.1f} {c:9d}   "
                  f"<-- FLAG impossible type observed")
            flags.append((t, 0.0, c, float('inf')))
        pval = chi2_sf(chi2, df - 1) if df > 1 else float('nan')
        print(f"    chi2 = {chi2:.1f} on {df-1} dof  ->  p = {pval:.3g}")
        status = "PASS" if not flags else "FLAGGED"
        summary_rows.append((ensemble.split()[0], n, p, N, len(R), status,
                             max((abs(z) for *_ , z in flags), default=0.0), pval))
        for t, Rf, o, z in flags:
            overall_flags.append((ensemble.split()[0], n, p, t, Rf, o, z))

print()
print("=" * 78)
print("SUMMARY  (flag rule: any sigma cell off by > 4 SE)")
print("=" * 78)
print(f"{'ensemble':10s} {'n':>2s} {'p':>2s} {'N':>8s} {'#types':>6s} {'status':>8s} "
      f"{'chi2 p':>8s}")
for ens, n, p, N, nt, status, _, pval in summary_rows:
    print(f"{ens:10s} {n:2d} {p:2d} {N:8d} {nt:6d} {status:>8s} {pval:8.3g}")
nflag = len(overall_flags)
ncfg = len(summary_rows)
print(f"\nTOTAL: {ncfg} (ensemble, n, p) configurations; {nflag} flagged cells")
if overall_flags:
    print("FLAGGED CELLS (candidate refutations — re-examine before concluding):")
    for ens, n, p, t, Rf, o, z in overall_flags:
        print(f"  {ens} n={n} p={p} sigma={t}: R={Rf:.6g}, obs={o}, z={z:.2f}")
    sys.exit(2)
print("VERDICT INPUT: no sigma off by > 4 SE in any configuration.")
