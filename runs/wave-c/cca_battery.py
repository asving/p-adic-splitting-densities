"""CCA battery (2026-08-30): decorrelated numeric check of IFCG31's m=4 carrier claims,
via GP/PARI (factorpadic + idealprimedec), mirroring verification/quartic_oracle.py's
(e,f)-refinement logic in GP script (cypari2 unavailable on this box; gp 2.17.4 is).

Tests over Z_p, p in {2,3,5}:
  T1. box31a = {v0>=2, v1=1, v2>=1, v3>=1}: EVERY sampled lift of every sampled class
      has full type {(1,1),(3,1)} — including invisible-corner samples (a0 = 0 or
      v(a0) huge) and boundary heights.
  T2. box31b = {v0>=3, v1=2, v2>=2, v3>=1}: same decided type {(1,1),(3,1)}.
  T3. forcedBox = {v1>=2} & ({v0=2} | {v0>=3, v2=1}): EVERY sampled lift has at least
      one factor with EVEN e (never an all-odd type — in particular never
      {(1,1),(3,1)} and never unramified); genre variety tabulated (the honest fence).

Monic quartic f = X^4 + a3 X^3 + a2 X^2 + a1 X + a0; v_i = v_p(a_i).
"""
import random
import subprocess
import sys
from collections import Counter

random.seed(20260830)
PREC = 40
GP = "/data/users/asvin/.local/bin/gp"
NSAMP = 80  # per (p, test)

GP_HEADER = r"""
ef(g, p) = {
  my(d = poldegree(g));
  if(d == 1, return([1,1]));
  my(G = liftall(g));
  my(nf = nfinit([G, [p]]));
  my(dec = idealprimedec(nf, p));
  for(i=1, #dec,
    my(pr = dec[i]);
    if(pr.e * pr.f == d, return([pr.e, pr.f])));
  my(pr = dec[1]); [pr.e, pr.f]
}
fulltype(f, p, prec) = {
  my(fac = factorpadic(f, p, prec));
  my(res = List());
  for(i=1, matsize(fac)[1],
    for(j=1, fac[i,2], listput(res, ef(fac[i,1], p))));
  vecsort(Vec(res))
}
"""


def rand_unit(p):
    return random.randrange(1, p) + p * random.randrange(0, p ** 6)


def coeff(p, v_exact=None, v_min=None):
    if v_exact is not None:
        return p ** v_exact * rand_unit(p)
    v = random.randrange(v_min, v_min + 9)
    if random.random() < 0.15:
        return 0  # vanishing-coefficient corner (a_i = 0)
    return p ** v * rand_unit(p)


def sample(test, p):
    if test == "T1":
        return (coeff(p, v_min=2), coeff(p, v_exact=1), coeff(p, v_min=1),
                coeff(p, v_min=1))
    if test == "T2":
        return (coeff(p, v_min=3), coeff(p, v_exact=2), coeff(p, v_min=2),
                coeff(p, v_min=1))
    if random.random() < 0.5:  # E1: v0 = 2, v1 >= 2
        return (coeff(p, v_exact=2), coeff(p, v_min=2), coeff(p, v_min=1),
                coeff(p, v_min=1))
    # E2: v0 >= 3, v1 >= 2, v2 = 1
    return (coeff(p, v_min=3), coeff(p, v_min=2), coeff(p, v_exact=1),
            coeff(p, v_min=1))


def run():
    jobs = []  # (test, p, coeffs)
    for test in ("T1", "T2", "T3"):
        for p in (2, 3, 5):
            for _ in range(NSAMP):
                jobs.append((test, p, sample(test, p)))
    lines = [GP_HEADER]
    for k, (test, p, (a0, a1, a2, a3)) in enumerate(jobs):
        f = f"x^4 + ({a3})*x^3 + ({a2})*x^2 + ({a1})*x + ({a0})"
        lines.append(f'print("RES {k} ", fulltype({f}, {p}, {PREC}));')
    script = "\n".join(lines)
    out = subprocess.run([GP, "-q", "-f"], input=script, capture_output=True,
                         text=True, timeout=3000)
    if out.returncode != 0:
        print("GP FAILED:", out.stderr[:2000])
        sys.exit(2)
    results = {}
    for ln in out.stdout.splitlines():
        if ln.startswith("RES "):
            _, k, rest = ln.split(" ", 2)
            raw = eval(rest)  # GP prints e.g. "[[1, 1], [3, 1]]" or "[[4, 1]]" or "[4, 1]"
            if raw and isinstance(raw[0], int):
                raw = [raw]
            results[int(k)] = tuple(sorted(tuple(x) for x in raw))
    fails = []
    genres = Counter()
    for k, (test, p, coeffs) in enumerate(jobs):
        t = results.get(k)
        if t is None:
            fails.append((test, p, coeffs, "MISSING"))
            continue
        if test in ("T1", "T2"):
            if t != ((1, 1), (3, 1)):
                fails.append((test, p, coeffs, t))
        else:
            genres[(p, t)] += 1
            if not any(e % 2 == 0 for (e, f) in t):
                fails.append((test, p, coeffs, t))
    for test in ("T1", "T2", "T3"):
        n = sum(1 for j in jobs if j[0] == test)
        bad = [f for f in fails if f[0] == test]
        claim = "all {(1,1),(3,1)}" if test != "T3" else "all have even e"
        print(f"{test}: {n} samples, {claim}: {'PASS' if not bad else 'FAIL'}")
    print("T3 genre table (p, type) -> count:")
    for kk, v in sorted(genres.items()):
        print(f"   p={kk[0]}  {kk[1]}: {v}")
    if fails:
        print("FAILURES (first 20):")
        for f in fails[:20]:
            print("  ", f)
        sys.exit(1)
    print("ALL PASS")


if __name__ == "__main__":
    run()
