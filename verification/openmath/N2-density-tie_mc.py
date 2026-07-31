#!/usr/bin/env python3
"""N2-density-tie (part 2/3): MONTE-CARLO side — empirical splitting-type densities
via the PARI factorpadic oracle, driven through the `gp` binary.

CONJECTURE UNDER TEST: M04 = BK.series_tie (BridgeKernels.lean:223 / DefsLedger.lean:573)
— see N2-density-tie_exact.py's header for the full Lean -> computation mapping.  The
computable surrogate: the Haar density of splitting type sigma over MONIC degree-n
polynomials with Z_p coefficients equals alpha(n, sigma; p) (the intended instance of the
chain's Rval); the projective ensemble against rho(n, sigma; p) is the global sanity.

WHAT THIS SCRIPT DOES: for each (n, p) in {2,3,4,5} x {2,3,5} it samples NSAMP
polynomials and classifies each with the SAME oracle logic as the repo's calibrated
verification/quartic_oracle.py (PARI factorpadic for the irreducible factors; per
nonlinear factor (e,f) via idealprimedec of nfinit([G,[p]]) on the Krasner lift G,
with a unit-discriminant fast path v_p(disc G) = 0 => (e,f) = (1,d), valid since
disc(field) | disc(G)).  cypari2 is not installed for this python, so the identical
pipeline runs inside PARI/GP 2.17.4 (~/.local/bin/gp) — one gp process per (n,p),
counts aggregated in-process, only the count table crosses the pipe.

ENSEMBLES:
  monic: f = x^n + sum_{i<n} c_i x^i, c_i uniform in [0, p^K) (Haar on Z_p truncated to
    K digits; the splitting type depends on digits beyond K only when v_p(disc) is of
    order K, probability O(p^{-K/2}) per sample — <= 3e-8 at the chosen K >= 24).
  proj : (c_0..c_n) uniform in [0, p^K)^{n+1}, rejected (and resampled) if all c_i = 0
    mod p — exactly the primitive-vector Haar measure whose pushforward is the uniform
    measure on P^n(Q_p).  A.s. c_n != 0, and the binary form's type is the type of the
    degree-n polynomial f; f is made monic WITHOUT changing the splitting type by the
    root scaling g(y) = c_n^{n-1} f(y/c_n) (theta -> c_n*theta, same etale algebra),
    so the calibrated monic oracle path applies verbatim.

PER-SAMPLE RIGOR GUARD: before factoring we compute disc(f) exactly (integer) and bump
the factorpadic/lift precision to 2*v_p(disc)+20 whenever the default would be lower
(Krasner-safe).  disc = 0 (probability ~p^-K) would be counted in a DEGENERATE bucket.
Per-sample checksum sum e_i f_i = n is asserted inside gp.

OUTPUT: results/N2-density-tie_mc_<ensemble>.json  {"n,p": {nsamp, seed, counts{typekey:
count}, elapsed_ms, maxvdisc, nbump, nreject}}.  Statistics happen in part 3/3
(N2-density-tie_report.py).

Run:  python3 N2-density-tie_mc.py --ensemble monic --nsamp 150000
      python3 N2-density-tie_mc.py --ensemble proj  --nsamp 100000
(from verification/openmath/; each full grid run stays under ~20 min)
"""
import argparse, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
VERIF = os.path.dirname(HERE)
GP = os.path.expanduser("~/.local/bin/gp")

# truncation depth K (p-adic digits of each sampled coefficient) and base factorpadic
# precision per prime: chosen so p^K >= 2^24 (truncation bias ~p^-K per sample).
KDIG = {2: 50, 3: 32, 5: 24}

GP_TEMPLATE = r"""
default(parisizemax, 256000000);
\\ the projective ensemble's scaled polynomials (coefficients up to p^{K(n-1)}, Krasner
\\ lifts up to p^{2 v(disc)+20}) overflow the default float precision inside
\\ idealprimedec ("precision too low in get_norm") — raise it globally (cheap: only
\\ slow-path factors reach nfinit).
default(realbitprecision, 12800);
eftype(g, p, prec) = {
  \\ (e,f) of Q_p[x]/(g), g monic irreducible over Q_p with t_PADIC coefficients:
  \\ the quartic_oracle.py logic verbatim (Krasner lift + idealprimedec), plus the
  \\ unit-disc fast path (v(disc G)=0 => unramified => (1,d), as disc(K)|disc(G)).
  my(d = poldegree(g));
  if(d == 1, return([1,1]));
  my(G = liftall(g));
  if(valuation(poldisc(G), p) == 0, return([1, d]));
  my(nf = nfinit([G, [p]]));
  my(dec = idealprimedec(nf, p));
  for(i = 1, #dec, if(dec[i].e * dec[i].f == d, return([dec[i].e, dec[i].f])));
  error("eftype: no prime with e*f = deg");
}
classify(f, n, p, prec) = {
  \\ splitting type of monic degree-n f (integer coefficients) as sorted [[e,f],...]
  my(D = poldisc(f));
  if(D == 0, return([0]));                       \\ DEGENERATE marker (measure ~0)
  my(vD = valuation(D, p), pr2 = prec, bumped = 0);
  if(2*vD + 8 > pr2, pr2 = 2*vD + 20; bumped = 1);
  my(fac = factorpadic(f, p, pr2));
  my(t = List(), s = 0);
  for(i = 1, matsize(fac)[1],
    my(ef = eftype(fac[i,1], p, pr2));
    s += ef[1] * ef[2] * fac[i,2];
    for(j = 1, fac[i,2], listput(t, ef)));
  if(s != n, error("checksum sum e*f != n"));
  [1, vecsort(Vec(t)), vD, bumped];
}
run(n, p, K, prec, NS, ens) = {
  my(M = Map(), t0 = getabstime(), maxv = 0, nbump = 0, ndeg = 0, nrej = 0);
  for(s = 1, NS,
    my(f);
    if(ens == 0,                                  \\ monic ensemble
      f = x^n + sum(i = 0, n-1, random(p^K) * x^i)
    ,                                             \\ projective ensemble
      my(c, okp = 0);
      while(!okp,
        c = vector(n+1, i, random(p^K));
        \\ reject non-primitive vectors (all c_i = 0 mod p) — the exact conditioning of
        \\ the P^n(Q_p) measure — and the measure-p^-K sliver c_n = 0 exactly (needed
        \\ for the monic scaling; bias ~p^-K per sample, flagged in the header).
        if(c[n+1] == 0 || vecmax(apply(z -> z % p, c)) == 0, nrej++, okp = 1));
      f = y^n + sum(i = 0, n-1, c[i+1] * c[n+1]^(n-1-i) * y^i));
    my(r = classify(f, n, p, prec));
    if(r[1] == 0, ndeg++; next);
    if(r[3] > maxv, maxv = r[3]);
    nbump += r[4];
    my(key = Str(r[2]));
    if(mapisdefined(M, key), mapput(M, key, mapget(M, key)+1), mapput(M, key, 1)));
  print("ELAPSED_MS|", getabstime() - t0);
  print("SUMMARY|maxvdisc|", maxv);
  print("SUMMARY|nbump|", nbump);
  print("SUMMARY|ndegenerate|", ndeg);
  print("SUMMARY|nreject|", nrej);
  my(mat = Mat(M));
  for(i = 1, matsize(mat)[1], print("COUNT|", mat[i,1], "|", mat[i,2]));
}
setrand(@SEED@);
run(@N@, @P@, @K@, @PREC@, @NS@, @ENS@);
quit;
"""


def run_config(n, p, nsamp, ensemble, seed):
    K = KDIG[p]
    # NOTE: delimited tokens (@X@) — plain names collided (ENSVAL ends in NSVAL),
    # which silently ran the wrong ensemble in an early smoke test.
    script = (GP_TEMPLATE
              .replace("@SEED@", str(seed)).replace("@N@", str(n))
              .replace("@P@", str(p)).replace("@K@", str(K))
              .replace("@PREC@", str(K)).replace("@NS@", str(nsamp))
              .replace("@ENS@", "0" if ensemble == "monic" else "1"))
    assert "@" not in script
    t0 = time.time()
    r = subprocess.run([GP, "-q", "-s", "64000000"], input=script,
                       capture_output=True, text=True, timeout=3600)
    if r.returncode != 0 or "COUNT|" not in r.stdout:
        print(r.stdout[-2000:]); print(r.stderr[-2000:])
        raise RuntimeError(f"gp failed for n={n} p={p} {ensemble}")
    counts, meta = {}, {"elapsed_wall_s": round(time.time() - t0, 1)}
    for line in r.stdout.splitlines():
        if line.startswith("COUNT|"):
            _, key, c = line.split("|")
            counts[json.dumps(json.loads(key))] = int(c)
        elif line.startswith("SUMMARY|"):
            _, k, v = line.split("|")
            meta[k] = int(v)
        elif line.startswith("ELAPSED_MS|"):
            meta["elapsed_ms"] = int(line.split("|")[1])
    assert sum(counts.values()) + meta["ndegenerate"] == nsamp
    return {"nsamp": nsamp, "seed": seed, "K": K, "counts": counts, **meta}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ensemble", choices=["monic", "proj"], required=True)
    ap.add_argument("--nsamp", type=int, default=150000)
    ap.add_argument("--seed0", type=int, default=20260731)
    ap.add_argument("--ns", type=int, nargs="*", default=[2, 3, 4, 5])
    ap.add_argument("--ps", type=int, nargs="*", default=[2, 3, 5])
    a = ap.parse_args()
    dst = os.path.join(VERIF, "results", f"N2-density-tie_mc_{a.ensemble}.json")
    out = json.load(open(dst)) if os.path.exists(dst) else {}
    T0 = time.time()
    for n in a.ns:
        for p in a.ps:
            seed = a.seed0 + 1000 * n + p
            res = run_config(n, p, a.nsamp, a.ensemble, seed)
            out[f"{n},{p}"] = res
            wild = "WILD" if p <= n else "tame"
            print(f"[{time.time()-T0:7.1f}s] {a.ensemble} n={n} p={p} ({wild}): "
                  f"{res['nsamp']} samples, {len(res['counts'])} types, "
                  f"maxvdisc={res['maxvdisc']}, nbump={res['nbump']}, "
                  f"gp {res['elapsed_ms']/1000:.1f}s", flush=True)
            json.dump(out, open(dst, "w"), indent=1)
    print(f"done -> {dst}")


if __name__ == "__main__":
    main()
