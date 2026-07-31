#!/usr/bin/env python3
"""O12 — (REG-p) emptiness at the intended instance: the falsifier scan.

LEAF (docs/MATH_COMPLETION_TREE_2026-08-01.md, O-12): at the intended OM
instance, for every n, the (REG-p) failing prime set is EMPTY — equivalently
(via the Lean-formalized M17 Theorem A, `MovesU/RegPFinite.lean
regP_failing_eq`): the real zero/pole locus B contains NO prime power >= 2.
By M17 Lemma C.2 + the prime-power closure (p^{delta*m} is again a prime
power), the whole leaf reduces to:

  (*)  for every block e in [1,n] and every prime power Q >= 2:
       D_{Phi_e}(Q) != 0 and N_{Phi_e}(Q) != 0,   Phi_e = det(1 - K_e),
  (**) every static entry denominator divides q^b * prod_c (q^c - 1)
       (the subring R = Q[q, 1/q, 1/(q^c-1)]), whose rational roots are
       {0, +-1} — never a prime power >= 2.

THE ATTEMPT's Theorem 1 claims: at the intended instance (the beta cluster-law
block system, the mathematical content of verification/om_density_engine.py),
the block-e kernel is the SCALAR self-loop kappa_e = q^{-(E_e - 1)},
E_e = e(e+1)/2, acting diagonally on the type index; hence
N_{Phi_e} = (q^{E_e-1} - 1)^{m_e} with rational roots in {+-1}.

WHAT THIS SCRIPT TESTS (each labeled CONFIRMS/REFUTES):

 A. [engine structure] For e = 2..EMAX: the linear-coefficient extraction on
    FULLMONIC(e): for every cluster type t, d FULLMONIC(e)[t] / d beta_e[t]
    == q^{1-e} EXACTLY, and == 0 for every other unknown beta_e[t'].  Combined
    with resc = q^{-e(e-1)/2}: kappa_e = q^{-(E_e-1)}.
    REFUTES Theorem 1's kernel structure if any coefficient differs.
 B. [det closure] Rational roots of the det numerators on record:
    engine q^{E_e-1} - 1 (e = 2..8); MOVESS n=2 gate q^3 - 1; RESUM-n3
    q^3 - q and q^6 - q; real-n2 q^3 - 1.  Expect roots subset of {0,+-1};
    ANY rational root >= 2 REFUTES the leaf.  Plus direct positivity
    N(Q) > 0 at every prime power 2 <= Q <= QMAX.
 C. [solve denominators + mass law] For e = 2..EMAX_SOLVE: the assembled
    beta_e[t]: reduced denominator rational roots subset {0,+-1}; at every
    prime power Q in PP: defined, value in [0,1], sum_t beta_e[t](Q) == 1
    EXACTLY (the substochasticity/mass evidence), and kappa_e(Q),
    kappahat_e(Q) = (Q-1)/(Q^{E_e}-1) both in (0,1).
 D. [full pipeline, n <= NMAX] rho(n,sigma;q): reduced denominator rational
    roots subset {0,+-1}; sum_sigma rho = 1 symbolically; values at prime
    powers in [0,1].  (Supports the master denominator theorem R.)

Exact rational arithmetic throughout (sympy).  Results JSON-dumped to
O12_regp_results.json.
"""
import os
import sys
import json
import math
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import sympy as sp
from om_density_engine import (q, beta, rho, _fullmonic_linear,
                               _enumerate_cluster_types)

EMAX = 6          # engine-structure check range
EMAX_SOLVE = 5    # assembled-solve check range
NMAX = 5          # full-pipeline range
QMAX = 200000     # direct prime-power positivity scan bound
PP = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 25, 27, 32, 49, 64, 81, 125, 128]

FINDINGS = []
RESULTS = {}


def chk(name, cond, detail=""):
    tag = "PASS" if cond else "FINDING"
    if not cond:
        FINDINGS.append(f"{name}  {detail}")
    print(f"[{tag}] {name}  {detail}", flush=True)


def rational_roots(poly):
    """All rational roots of a sympy Poly/expr in q (exact)."""
    p = sp.Poly(sp.expand(poly), q)
    if p.total_degree() == 0:
        return set()
    return set(sp.roots(p, filter='Q').keys())


def prime_powers(bound):
    sieve = list(range(bound + 1))
    for i in range(2, bound + 1):
        if sieve[i] == i:
            for j in range(2 * i, bound + 1, i):
                if sieve[j] == j:
                    sieve[j] = i
    out = []
    for m in range(2, bound + 1):
        p0 = sieve[m]
        k = m
        while k % p0 == 0:
            k //= p0
        if k == 1:
            out.append(m)
    return out


def evalQ(expr, Q):
    """Exact rational value of expr at q=Q; None if pole."""
    numden = sp.fraction(sp.cancel(sp.together(expr)))
    dv = numden[1].subs(q, Q)
    if dv == 0:
        return None
    nv = numden[0].subs(q, Q)
    r = sp.Rational(nv, dv)
    return Fraction(int(r.p), int(r.q))


print("=" * 72)
print("A. Engine kernel structure: d FULLMONIC(e)[t]/d beta_e[t] == q^(1-e)")
print("=" * 72)
struct_ok = {}
for e in range(2, EMAX + 1):
    types = _enumerate_cluster_types(e)
    syms = {t: sp.Symbol(f"_b{i}") for i, t in enumerate(types)}
    FM = _fullmonic_linear(e, syms)
    ok = True
    for t in types:
        expr = sp.expand(FM.get(t, sp.Integer(0)))
        cself = sp.cancel(sp.diff(expr, syms[t]))
        if sp.simplify(cself - q ** (1 - e)) != 0:
            ok = False
            chk(f"A e={e} t={t} self-coefficient", False, f"got {cself}")
        for t2 in types:
            if t2 == t:
                continue
            cx = sp.cancel(sp.diff(expr, syms[t2]))
            if cx != 0:
                ok = False
                chk(f"A e={e} t={t} cross-coefficient vs {t2}", False, f"got {cx}")
    chk(f"A e={e}: FULLMONIC linear structure diagonal, coeff q^(1-e), "
        f"kappa_{e} = q^-(E-1), E-1 = {e*(e+1)//2 - 1}", ok)
    struct_ok[e] = ok
RESULTS['A_structure'] = struct_ok

print("=" * 72)
print("B. Det-numerator rational roots + prime-power positivity")
print("=" * 72)
DETS = {}
for e in range(2, 9):
    c = e * (e + 1) // 2 - 1
    DETS[f"engine_e{e}"] = q ** c - 1
DETS["movesS_n2_gate"] = q ** 3 - 1          # det = (q^3-1)/q^3
DETS["real_n2_block2"] = q ** 3 - 1          # Phi_2 = (q^3-1)/q^3 (n2_det)
DETS["resum_blk2"] = q ** 3 - q              # det = (q^3-q)/(q^3-1)
DETS["resum_blk3"] = q ** 6 - q              # det = (q^6-q)/(q^6-1)
pps = prime_powers(QMAX)
det_ok = {}
for name, N in DETS.items():
    rr = rational_roots(N)
    bad = [r for r in rr if r >= 2]
    chk(f"B {name}: rational roots {sorted(rr)} subset of {{0,+-1}}",
        all(r in (0, 1, -1) for r in rr), f"bad: {bad}")
    Np = sp.Poly(N, q)
    viol = [Q for Q in pps if Np.eval(Q) <= 0]
    chk(f"B {name}: N(Q) > 0 at ALL {len(pps)} prime powers 2<=Q<={QMAX}",
        not viol, f"violations: {viol[:5]}")
    det_ok[name] = (not bad) and (not viol)
RESULTS['B_dets'] = det_ok

print("=" * 72)
print("C. Assembled solve beta_e: denominators, positivity, exact mass law")
print("=" * 72)
solve_ok = {}
for e in range(2, EMAX_SOLVE + 1):
    bet = beta(e)
    ok = True
    total = sp.Integer(0)
    for t, f in bet.items():
        fc = sp.cancel(sp.together(f))
        den = sp.fraction(fc)[1]
        rr = rational_roots(den)
        bad = [r for r in rr if r >= 2]
        if bad:
            ok = False
            chk(f"C e={e} t={t}: denominator roots", False,
                f"roots {sorted(rr)}, bad {bad}, den = {sp.factor(den)}")
        total += fc
    chk(f"C e={e}: ALL {len(bet)} type-denominator rational roots in {{0,+-1}}", ok)
    mass = sp.simplify(sp.cancel(total - 1))
    chk(f"C e={e}: symbolic mass law sum_t beta_e[t] == 1", mass == 0,
        f"residual {mass}")
    ok = ok and (mass == 0)
    E = e * (e + 1) // 2
    for Q in PP:
        s = Fraction(0)
        neg = []
        for t, f in bet.items():
            v = evalQ(f, Q)
            if v is None:
                ok = False
                chk(f"C e={e} t={t} Q={Q}: POLE at prime power", False)
                continue
            if v < 0 or v > 1:
                neg.append((t, v))
            s += v
        if neg:
            ok = False
            chk(f"C e={e} Q={Q}: values outside [0,1]", False, f"{neg[:3]}")
        if s != 1:
            ok = False
            chk(f"C e={e} Q={Q}: sum != 1", False, f"sum {s}")
        kap = Fraction(1, Q ** (E - 1))
        kaph = Fraction(Q - 1, Q ** E - 1)
        if not (0 < kap < 1 and 0 < kaph < 1):
            ok = False
            chk(f"C e={e} Q={Q}: kernel value outside (0,1)", False)
    chk(f"C e={e}: pool scan over {len(PP)} prime powers "
        f"(defined, in [0,1], sum 1, kappa/kappahat in (0,1))", ok)
    solve_ok[e] = ok
RESULTS['C_solve'] = solve_ok

print("=" * 72)
print("D. Full pipeline rho(n): denominators + checksum + prime-power values")
print("=" * 72)
rho_ok = {}
for n in range(2, NMAX + 1):
    R = rho(n)
    ok = True
    for t, f in R.items():
        den = sp.fraction(sp.cancel(sp.together(f)))[1]
        rr = rational_roots(den)
        bad = [r for r in rr if r >= 2]
        if bad:
            ok = False
            chk(f"D n={n} sigma={t}: denominator roots", False,
                f"bad {bad}, den = {sp.factor(den)}")
    chk(f"D n={n}: ALL {len(R)} rho denominators have rational roots in "
        f"{{0,+-1}}", ok)
    mass = sp.simplify(sum(R.values()) - 1)
    chk(f"D n={n}: sum_sigma rho == 1 symbolically", mass == 0, f"res {mass}")
    ok = ok and (mass == 0)
    for Q in PP[:10]:
        s = Fraction(0)
        for t, f in R.items():
            v = evalQ(f, Q)
            if v is None or v < 0 or v > 1:
                ok = False
                chk(f"D n={n} sigma={t} Q={Q}: bad value {v}", False)
            else:
                s += v
        if s != 1:
            ok = False
            chk(f"D n={n} Q={Q}: sum {s} != 1", False)
    chk(f"D n={n}: prime-power value scan", ok)
    rho_ok[n] = ok
RESULTS['D_rho'] = rho_ok

print("=" * 72)
verdict = "CONFIRMED" if not FINDINGS else "REFUTED/FINDINGS"
print(f"O12 falsifier scan: {verdict}; findings: {len(FINDINGS)}")
for f in FINDINGS:
    print("  *", f)
RESULTS['findings'] = FINDINGS
RESULTS['verdict'] = verdict
out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   'O12_regp_results.json')
with open(out, 'w') as fh:
    json.dump(RESULTS, fh, indent=1, default=str)
print(f"results -> {out}")
