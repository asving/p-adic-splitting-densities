#!/usr/bin/env python3
"""O-11 (SERIES-TIE) falsifier — run BEFORE the assembly note is finalized.

Node: tree DELTA-1 D-9 / DELTA-2 path step 8 — the per-sigma tree-series =
R_sigma value tie (the [3t] <-> [3] solve seam; Lean row
MovesU/BridgeKernels.lean:223 `series_tie`).

SEALED PREDICTIONS (written before first run):

V1 (the F1 test at the REAL pack; kills the note if it fails):
    om_density_engine.alpha_full(2) — the real n=2 solve of the S-area
    engine (block recursion + cluster laws, the same pipeline RESUM-n3
    gates at n=3) — is IDENTICALLY the true triple
    (split, inert, ram) = (q/(2(q+1)), q/(2(q+1)), 1/(q+1))
    of padic_types.monic_quad_pred (oracle-validated 2026-06).  M04
    Finding F1 refuted the DEVICE chain `n2Chain` as a discharge site
    (device triple has a zero entry); the assembly note binds the row to
    the REAL pack, so the real pack's solve MUST reproduce the true
    triple.  Any mismatch = the note's K3/value leg is dead on arrival.

V2 (the n=3 anchor, same pipeline): alpha_full(3) == monic_cubic_pred
    identically (all five types), and sum over types == 1 in Q(q).
    (RESUM-n3's 65/65 gate is the sealed precedent; this re-runs the
    symbolic identity end-to-end in this environment.)

T1 (M04 test T1 — the (D_sigma) limit form at the real n=2 classifier,
    which Corollary 1.1 makes equivalent to the row given count_tie):
    exact enumeration of (b, c) in (Z/p^N)^2 for p in {2,3,5}, N up to
    (10, 6, 4); sound decision rule on the discriminant d = b^2 - 4c
    (p odd: decided iff v_p(d) < N, type by parity of v and QR of the
    unit part; p = 2: decided iff v_2(d) <= N - 3, type by unit mod 8).
    CONFIRMS iff for every sigma: dmass_sigma(N) := decided_sigma(N)/p^{2N}
    is NONDECREASING in N, the two-sided bracket
    dmass_sigma(N) <= rho_sigma(p) <= dmass_sigma(N) + env(N) holds at
    every N (env(N) := 1 - sum_sigma dmass_sigma(N)), and env decays
    geometrically (env(N_max) < 0.02).  Any realized violation REFUTES
    (D_sigma) at the real classifier and kills the row.

Run:  uv run --with sympy python o11_seriestie_check.py
      (T1 is pure stdlib; V1/V2 need sympy.)
Exit nonzero on any FAIL.
"""
import sys
from fractions import Fraction as Fr

sys.path.insert(0, __file__.rsplit('/', 2)[0])  # verification/ on path

FAILS = []


def report(name, ok, detail=""):
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")
    if not ok:
        FAILS.append(name)


# ---------------- V1/V2: the symbolic value ties at the real pack ---------
def value_ties():
    import sympy as sp
    import om_density_engine as e
    import padic_types as pt

    # V1: n = 2
    a2 = {e.CODE_N2[t]: sp.simplify(v) for t, v in e.alpha_full(2).items()}
    true2 = {'split': e.q / (2 * (e.q + 1)), 'inert': e.q / (2 * (e.q + 1)),
             'ram': 1 / (e.q + 1)}
    for t in ('split', 'inert', 'ram'):
        d = sp.simplify(a2[t] - true2[t])
        report(f"V1 n=2 {t}", d == 0, f"engine - true = {d}")
    report("V1 n=2 sum=1", sp.simplify(sum(a2.values()) - 1) == 0)
    # cross-check numerically vs the Fraction oracle at 4 primes
    for P in (2, 3, 5, 7):
        pred = pt.monic_quad_pred(P)
        ok = all(sp.Rational(pred[t]) == sp.nsimplify(a2[t].subs(e.q, P))
                 for t in a2)
        report(f"V1 n=2 numeric p={P}", ok)

    # V2: n = 3
    a3 = {e.CODE_N3[t]: sp.simplify(v) for t, v in e.alpha_full(3).items()}
    q = e.q
    d = q ** 5 - 1
    true3 = {  # transcribed line-for-line from padic_types.monic_cubic_pred
        '111': q ** 3 * (q - 1) * (q * q - q + 1) / (6 * (q + 1) * d),
        '12':  q ** 3 * (q ** 3 - 1) / (2 * (q + 1) * d),
        '3':   q ** 3 * (q * q - 1) / (3 * d),
        '1r1': q * (q - 1) * (q ** 3 + q + 1) / ((q + 1) * d),
        '1c':  (q - 1) * (q * q + 1) / d,
    }
    for t in a3:
        vals = all(Fr(pt.monic_cubic_pred(P)[t])
                   == Fr(int(sp.nsimplify(a3[t].subs(q, P)).p),
                         int(sp.nsimplify(a3[t].subs(q, P)).q))
                   for P in (2, 3, 5, 7))
        sym = sp.simplify(a3[t] - true3[t]) == 0
        report(f"V2 n=3 {t}", vals and sym)
    report("V2 n=3 sum=1", sp.simplify(sum(a3.values()) - 1) == 0)


# ---------------- T1: the (D_sigma) limit form, exact enumeration ---------
def vp(x, p, cap):
    if x == 0:
        return cap
    v = 0
    while x % p == 0 and v < cap:
        x //= p
        v += 1
    return v


def decide(b, c, p, N):
    """Sound decision of the splitting type of x^2+bx+c from (b,c) mod p^N.
    Returns 'split'/'inert'/'ram' or None (undecided)."""
    pn = p ** N
    d = (b * b - 4 * c) % pn
    v = vp(d, p, N)
    if p == 2:
        if v > N - 3:
            return None
        u = (d // 2 ** v) % 8
        if v % 2 == 1:
            return 'ram'
        return {1: 'split', 5: 'inert'}.get(u, 'ram')
    if v >= N:
        return None
    u = (d // p ** v) % p
    if v % 2 == 1:
        return 'ram'
    return 'split' if pow(u, (p - 1) // 2, p) == 1 else 'inert'


def t1():
    sweeps = {2: 10, 3: 6, 5: 4}
    for p, Nmax in sweeps.items():
        rho = {'split': Fr(p, 2 * (p + 1)), 'inert': Fr(p, 2 * (p + 1)),
               'ram': Fr(1, p + 1)}
        prev = {t: Fr(0) for t in rho}
        env = Fr(1)
        for N in range(1, Nmax + 1):
            pn = p ** N
            cnt = {t: 0 for t in rho}
            for b in range(pn):
                for c in range(pn):
                    t = decide(b, c, p, N)
                    if t:
                        cnt[t] += 1
            dm = {t: Fr(cnt[t], pn * pn) for t in rho}
            env = 1 - sum(dm.values())
            mono = all(dm[t] >= prev[t] for t in rho)
            brk = all(dm[t] <= rho[t] <= dm[t] + env for t in rho)
            report(f"T1 p={p} N={N} monotone+bracket", mono and brk,
                   f"env={float(env):.2e}")
            prev = dm
        report(f"T1 p={p} env decays", env < Fr(1, 50), f"env(N={Nmax})={float(env):.2e}")


if __name__ == '__main__':
    try:
        value_ties()
    except ImportError:
        report("V1/V2 (sympy missing)", False, "run under uv --with sympy")
    t1()
    print(f"\n{'ALL PASS' if not FAILS else 'FAILURES: ' + ', '.join(FAILS)}")
    sys.exit(1 if FAILS else 0)
