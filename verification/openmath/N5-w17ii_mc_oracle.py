#!/usr/bin/env python3
"""N5-w17ii (script 3/3): PARI/gp ORACLE validation of the instance census.

Role in the unit: N5-w17ii_instance.py builds the chain weights shWeightH(sigma,h)
by exhaustive class enumeration with CLASSICAL DECISION RULES (Hensel / Newton
polygon / disc square-class).  Those rules and the class-decidedness claims are
the trust base of the instance verdict; this script validates them against the
independent PARI factorpadic oracle (the repo's calibrated ground-truth route,
cf. verification/quartic_oracle.py -- here driven through the gp binary since
cypari2 is not installed on this box; same PARI calls: factorpadic +
idealprimedec for nonlinear (e,f)).

Three parts:
  O1. CALIBRATION: the 9 known cases from quartic_oracle.py's __main__ through
      the gp pipeline; assert the classically known types (incl. Q_2(zeta_8)
      = (4,1) totally ramified).
  O2. RULE + DECIDEDNESS VALIDATION (>= 10^4 oracle polys per (n,p) config):
      sample random classes at the census base level N; for each class our rules
      DECIDE, oracle-check (a) the canonical lift's type == the rule's sigma,
      (b) THREE random lifts perturbed at level N (coeff += p^N * random) have
      the SAME type and the same disc valuation h -- this tests exactly the
      class-decidedness (Krasner-side) claim that the census rests on.
      Triple-pattern classes are oversampled (they exercise the NP recursion).
  O3. MONTE CARLO DISTRIBUTION (30000 samples per (n,p)): random monic polys
      with coefficients uniform mod p^25, oracle type + height h = v_p(disc);
      compare (a) per-(sigma,h) frequencies against the census's EXACT visible
      weights, (b) per-sigma totals against the OM-engine WshVal (the clause
      (ii) tie beyond the exact frontier), both at 5-sigma tolerance.
      FLAG: MC coefficients live mod p^25, not Z_p; the bias is bounded by the
      measure of classes undecided at level 25 (~ p^-20, far below MC noise).

Consumes: results_N5-w17ii_census.json (written by script 2).
"""

import json
import math
import os
import random
import re
import subprocess
import sys
import time
from fractions import Fraction as Fr
from collections import defaultdict

HERE = "/data/users/asvin/math-and-lean/p-adic-splitting-densities/verification/openmath"
GP = os.path.expanduser("~/.local/bin/gp")
sys.path.insert(0, HERE)

import importlib
inst = importlib.import_module("N5-w17ii_instance".replace("-", "_")) \
    if False else None
# hyphenated module name: load by path
import importlib.util
spec = importlib.util.spec_from_file_location(
    "n5inst", os.path.join(HERE, "N5-w17ii_instance.py"))
n5inst = importlib.util.module_from_spec(spec)
spec.loader.exec_module(n5inst)

T0 = time.time()
FAIL = []


def check(name, cond, detail=""):
    tag = "PASS" if cond else "FAIL"
    if not cond:
        FAIL.append(name)
    print(f"  [{tag}] {name}" + (f" -- {detail}" if detail else ""), flush=True)
    return cond


def log(m):
    print(f"[{time.time()-T0:7.1f}s] {m}", flush=True)


GP_HEADER = r"""
allocatemem(512*1024*1024);
qclass(D, p) = {
  my(v = valuation(D, p), u);
  if (v % 2 == 1, return ([2,1]));
  u = lift(D / p^v);
  if (p == 2,
    if (u % 8 == 5, return ([1,2]), return ([2,1])),
    if (kronecker(u, p) == -1, return ([1,2]), return ([2,1])));
}
efof(g, p) = {
  my(d = poldegree(g), G, K, dec);
  if (d == 1, return ([1,1]));
  if (d == 2, return (qclass(poldisc(g), p)));
  G = liftall(g);
  K = nfinit([G, [p]]);
  dec = idealprimedec(K, p);
  for (k = 1, #dec,
    if (dec[k][3]*dec[k][4] == d, return ([dec[k][3], dec[k][4]])));
  return ([dec[1][3], dec[1][4]]);
}
fulltype(f, p, prec) = {
  my(fac = factorpadic(f, p, prec), types = []);
  for (j = 1, matsize(fac)[1],
    my(ef = efof(fac[j,1], p));
    for (m = 1, fac[j,2], types = concat(types, [ef])));
  vecsort(types);
}
"""


def run_gp(body):
    script = GP_HEADER + "\n" + body + "\nquit\n"
    r = subprocess.run([GP, "-q", "-f"], input=script, capture_output=True,
                       text=True, timeout=900)
    if r.returncode != 0:
        print(r.stderr[:2000])
        raise RuntimeError("gp failed")
    return r.stdout


def parse_sigma(s):
    """gp vecsort output like [[1,1],[2,1]] -> ((1,1),(2,1)) sorted."""
    pairs = re.findall(r"\[(\d+),\s*(\d+)\]", s)
    return tuple(sorted((int(e), int(f)) for e, f in pairs))


# ===========================================================================
print("=" * 78)
print("O1. calibration: the 9 quartic_oracle.py cases through the gp pipeline")
print("=" * 78)
CAL = [("x^4+4", 2, ((2, 1), (2, 1))),      # (x^2-2x+2)(x^2+2x+2), both ramified
       ("x^4+12", 2, None),
       ("x^4+4*x+4", 2, None),
       ("x^4-2", 2, ((4, 1),)),             # Eisenstein
       ("x^4+1", 2, ((4, 1),)),             # Q_2(zeta_8) totally ramified (repo cal.)
       ("x^2-2", 2, ((2, 1),)),
       ("x^2-5", 2, ((1, 2),)),             # 5 = 5 mod 8: unramified
       ("x^3-2", 3, ((3, 1),)),             # Eisenstein
       ("x^2-3", 3, ((2, 1),))]
body = "\n".join(f'print("CAL{i} ", fulltype({f}, {p}, 60));'
                 for i, (f, p, _) in enumerate(CAL))
out = run_gp(body)
got = {}
for line in out.splitlines():
    m = re.match(r"CAL(\d+)\s+(.*)", line.strip())
    if m:
        got[int(m.group(1))] = parse_sigma(m.group(2))
ok = True
for i, (f, p, exp) in enumerate(CAL):
    g = got.get(i)
    deg = 4 if "x^4" in f else (3 if "x^3" in f else 2)
    okdeg = g is not None and sum(e * ff for e, ff in g) == deg
    okexp = (exp is None) or (g == exp)
    ok &= okdeg and okexp
    print(f"    {f:12s}/Q_{p}: oracle={g} expected={exp if exp else '(record)'}"
          f"{'' if okdeg and okexp else '  *** MISMATCH ***'}")
check("O1: calibration types (sum ef = deg everywhere; all known cases exact)", ok)

# ===========================================================================
print()
print("=" * 78)
print("O2. rule + class-decidedness validation against the oracle")
print("=" * 78)
for p in (2, 3, 5):
    n5inst.TAB2[p] = n5inst.reduction_table(p, 2)
    n5inst.TAB3[p] = n5inst.reduction_table(p, 3)

rng = random.Random(20260731)
CONFIGS = [(2, 2, 8), (2, 3, 6), (2, 5, 5),      # (n, p, level N for sampling)
           (3, 2, 7), (3, 3, 5), (3, 5, 4)]

for (n, p, N) in CONFIGS:
    M = p ** N
    samples = []          # (coeffs_of_poly_variants, expected_sigma, expected_h)
    npats = defaultdict(int)
    tries = 0
    # plain random classes + oversampled TRIPLE-pattern classes (n=3)
    want_plain, want_triple = 2600, 800
    got_plain = got_triple = 0
    while (got_plain < want_plain or (n == 3 and got_triple < want_triple)) \
            and tries < 400000:
        tries += 1
        force_triple = (n == 3 and got_triple < want_triple and tries % 2 == 0)
        if force_triple:
            t = rng.randrange(p)
            # class with reduction (x-t)^3: fix (a,b,c) mod p, free higher digits
            a = (-3 * t) % p + p * rng.randrange(p ** (N - 1))
            b = (3 * t * t) % p + p * rng.randrange(p ** (N - 1))
            c = (-t ** 3) % p + p * rng.randrange(p ** (N - 1))
            coeffs = (a, b, c)
        else:
            coeffs = tuple(rng.randrange(M) for _ in range(n))
        r = n5inst.decide_class(coeffs, p, N, n)
        if r[0] != 'D':
            continue
        code = (n5inst.TAB3[p] if n == 3 else n5inst.TAB2[p])[
            tuple(cc % p for cc in coeffs)]
        if force_triple:
            if code[0] != 'TRIPLE':
                continue
            got_triple += 1
        else:
            got_plain += 1
        npats[code[0]] += 1
        variants = [coeffs]
        for _ in range(3):
            variants.append(tuple(cc + M * rng.randrange(p ** 12)
                                  for cc in coeffs))
        samples.append((variants, r[1], r[2]))
    log(f"n={n} p={p}: {len(samples)} decided classes sampled at level {N} "
        f"(patterns {dict(npats)}), {4*len(samples)} oracle polys")
    # gp batch
    lines = []
    idx = 0
    for variants, sig, h in samples:
        for coeffs in variants:
            if n == 2:
                fstr = f"x^2+({coeffs[0]})*x+({coeffs[1]})"
            else:
                fstr = f"x^3+({coeffs[0]})*x^2+({coeffs[1]})*x+({coeffs[2]})"
            lines.append(f'print("S{idx} ", fulltype({fstr}, {p}, 80), '
                         f'" H", valuation(poldisc({fstr}), {p}));')
            idx += 1
    out = run_gp("\n".join(lines))
    res = {}
    for line in out.splitlines():
        m = re.match(r"S(\d+)\s+(.*)\s+H(\d+)", line.strip())
        if m:
            res[int(m.group(1))] = (parse_sigma(m.group(2)), int(m.group(3)))
    bad_sig = bad_h = missing = 0
    idx = 0
    first_bad = None
    for variants, sig, h in samples:
        for v_i, coeffs in enumerate(variants):
            r = res.get(idx)
            idx += 1
            if r is None:
                missing += 1
                continue
            osig, oh = r
            if osig != sig:
                bad_sig += 1
                if first_bad is None:
                    first_bad = (coeffs, sig, osig, h, oh)
            # height check: SEP classes have h = 0 = v(disc); all decided classes
            # must show the class height on every lift
            if oh != h:
                bad_h += 1
                if first_bad is None:
                    first_bad = (coeffs, sig, osig, h, oh)
    if first_bad:
        print(f"    FIRST MISMATCH: coeffs={first_bad[0]} rule sigma={first_bad[1]} "
              f"oracle {first_bad[2]}; rule h={first_bad[3]} oracle {first_bad[4]}")
    check(f"O2 n={n} p={p}: rule sigma == oracle sigma AND h == v_p(disc) on "
          f"canonical + 3 perturbed lifts x {len(samples)} classes",
          bad_sig == 0 and bad_h == 0 and missing == 0,
          f"{4*len(samples)} oracle polys, mismatches sigma={bad_sig} h={bad_h} "
          f"missing={missing}")
    if n == 3:
        check(f"O2 n={n} p={p}: TRIPLE-pattern (NP recursion) coverage >= 100",
              npats.get('TRIPLE', 0) >= 100, f"{npats.get('TRIPLE', 0)} classes")

# ===========================================================================
print()
print("=" * 78)
print("O3. Monte Carlo distribution vs exact census weights and engine WshVal")
print("=" * 78)
CEN = json.load(open(os.path.join(HERE, "results_N5-w17ii_census.json")))
SMC = 30000
for (n, p, _) in CONFIGS:
    key = f"{n},{p}"
    frontier = CEN[key]["frontier"]
    wexact = {}
    for sigs, h, w in CEN[key]["harvested"]:
        if h < frontier:
            wexact[(eval(sigs), h)] = Fr(w)
    weng = {eval(k): Fr(v) for k, v in CEN[key]["engine"].items()}
    body = f"""
setrand({20260731 + n * 10 + p});
{{
for (i = 1, {SMC},
  my(co = vector({n}, k, random({p}^25)), f, D);
  if ({n} == 2, f = x^2 + co[1]*x + co[2], f = x^3 + co[1]*x^2 + co[2]*x + co[3]);
  D = poldisc(f);
  if (D == 0, next);
  print("M ", fulltype(f, {p}, 80), " H", valuation(D, {p}));
);
}}
"""
    out = run_gp(body)
    cnt_sh = defaultdict(int)
    cnt_s = defaultdict(int)
    tot = 0
    for line in out.splitlines():
        m = re.match(r"M\s+(.*)\s+H(\d+)", line.strip())
        if m:
            sig, h = parse_sigma(m.group(1)), int(m.group(2))
            cnt_sh[(sig, h)] += 1
            cnt_s[sig] += 1
            tot += 1
    # (a) per-(sigma,h) on the visible grid
    bad = []
    for (sig, h), w in sorted(wexact.items(), key=lambda kv: (kv[0][1], str(kv[0]))):
        obs = cnt_sh.get((sig, h), 0) / tot
        wf = float(w)
        tolerance = 5 * math.sqrt(max(wf * (1 - wf), 1e-9) / tot) + 2 / tot
        if abs(obs - wf) > tolerance:
            bad.append((sig, h, obs, wf))
    check(f"O3 n={n} p={p}: MC per-(sigma,h) frequencies match the exact census "
          f"weights on all {len(wexact)} visible cells (5-sigma)",
          not bad, f"N_MC={tot}" + (f"; first bad {bad[0]}" if bad else ""))
    # (b) per-sigma totals vs engine (the tie beyond the frontier)
    bad2 = []
    for sig, wv in sorted(weng.items(), key=str):
        obs = cnt_s.get(sig, 0) / tot
        wf = float(wv)
        tolerance = 5 * math.sqrt(max(wf * (1 - wf), 1e-9) / tot) + 2 / tot
        if abs(obs - wf) > tolerance:
            bad2.append((sig, obs, wf))
    check(f"O3 n={n} p={p}: MC per-sigma totals match engine WshVal for all "
          f"sigma (clause (ii) tie, full height spectrum; 5-sigma)",
          not bad2, f"first bad {bad2[0]}" if bad2 else "")

print()
print("=" * 78)
if FAIL:
    print(f"RESULT: {len(FAIL)} CHECK(S) FAILED:")
    for f in FAIL:
        print("  -", f)
    sys.exit(1)
print("RESULT: ALL ORACLE CHECKS PASS (O1-O3)")
