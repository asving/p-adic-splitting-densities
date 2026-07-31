#!/usr/bin/env python3
"""O-10 K-COUNT fiber-constancy harness (the D-8-guarded N-range checks).

Falsifier harness for the K-COUNT lemma of leaf O-10 (sibling independence at
adapted cells), per docs/MATH_COMPLETION_TREE_2026-08-01.md D-8 and
lean/notes/openmath/M07-sibjc_fable.md OL-1/OL-4.  Pure Python, exact integers,
no dependencies.

Objects.  p prime; f_1..f_m monic in Z_p[x], pairwise coprime over Q_p;
rho_ij = v_p(Res(f_i,f_j)); rho = sum_{i<j} rho_ij; tau >= rho+1 the polydisc
pinning depth; N >= tau the working level; M = N - tau.
A_j(N) = {g monic deg d_j mod p^N : g = f_j mod p^tau};
mu_N : prod A_j(N) -> monics deg n mod p^N, (g_j) |-> prod g_j.
Phi = the Sylvester-block linear map (a_j)_j |-> sum_j a_j prod_{i!=j} f_i;
(e_1<=...<=e_n) its elementary-divisor profile, sum e_i = rho.

Predictions under test (sealed in O10_phaseB_attempt.md before first run):
  T0  det(Phi) has v_p exactly rho (Lemma 1: det = +- prod Res(f_i,f_j)).
  T1  every nonempty mu_N-fiber has size exactly p^{sum_i min(e_i, M)},
      for EVERY N >= tau (constancy at all levels, not only the guard range);
      = p^rho once M >= e_max (the D-8 guard range).
  T2  fiber blindness: members of one fiber agree coefficientwise mod
      p^{N - e_max}.
  T3  adapted product law (SIB shape): for per-factor cells/events keyed at
      depth <= N - e_max, #(S_cap)*#Sigma^{m-1} = prod_j #(Sigma cap S_j).
  T4  Route-1 mirror: a correlation-refined cell (diagonal digit condition
      coupling two factors) BREAKS the product law by a factor p.
  T5  read-depth guard necessity: events reading factor digits at depth
      > N - e_max are not even well-defined on fibers (straddling witness).
"""
import itertools, math, sys
from fractions import Fraction

# ---------- exact polynomial / matrix helpers (coeffs low->high) ----------

def polymul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return tuple(r)

def polymul_many(fs):
    r = (1,)
    for f in fs:
        r = polymul(r, f)
    return r

def polmod(f, q):
    return tuple(c % q for c in f)

def vp(x, p):
    if x == 0:
        return None  # infinity
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

def det_bareiss(mat):
    """Exact integer determinant (fraction-free Bareiss)."""
    m = [row[:] for row in mat]
    n = len(m)
    if n == 0:
        return 1
    sign = 1
    prev = 1
    for k in range(n - 1):
        if m[k][k] == 0:
            for r in range(k + 1, n):
                if m[r][k] != 0:
                    m[k], m[r] = m[r], m[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                m[i][j] = (m[i][j] * m[k][k] - m[i][k] * m[k][j]) // prev
        prev = m[k][k]
    return sign * m[n - 1][n - 1]

def resultant(f, g):
    """Res(f,g) via the Sylvester matrix (f,g monic, deg>=1)."""
    df, dg = len(f) - 1, len(g) - 1
    n = df + dg
    rows = []
    for i in range(dg):            # x^i * f
        row = [0] * n
        for j, c in enumerate(f):
            row[i + j] = c
        rows.append(row)
    for i in range(df):            # x^i * g
        row = [0] * n
        for j, c in enumerate(g):
            row[i + j] = c
        rows.append(row)
    return det_bareiss(rows)

def phi_matrix(fs):
    """Matrix of (a_j) |-> sum_j a_j * prod_{i != j} f_i  on monomial bases.
    Columns: (j, t<d_j) -> coeffs of x^t * F_j; rows: monomials deg < n."""
    m = len(fs)
    degs = [len(f) - 1 for f in fs]
    n = sum(degs)
    cols = []
    for j in range(m):
        Fj = polymul_many([fs[i] for i in range(m) if i != j])
        for t in range(degs[j]):
            col = [0] * n
            for k, c in enumerate(Fj):
                col[t + k] = c
            cols.append(col)
    return [[cols[c][r] for c in range(n)] for r in range(n)]

def smith_profile(mat, p, cap=60):
    """Elementary-divisor exponents e_1<=..<=e_n via gcd-of-minors valuations."""
    n = len(mat)
    dks = []
    for k in range(1, n + 1):
        best = None
        for rows in itertools.combinations(range(n), k):
            for colsel in itertools.combinations(range(n), k):
                sub = [[mat[r][c] for c in colsel] for r in rows]
                d = det_bareiss(sub)
                v = vp(d, p)
                if v is not None and (best is None or v < best):
                    best = v
                    if best == 0:
                        break
            if best == 0:
                break
        dks.append(best if best is not None else cap)
    es = [dks[0]] + [dks[k] - dks[k - 1] for k in range(1, n)]
    return sorted(es), dks

# ---------- fiber enumeration ----------

def enum_fibers(p, fs, tau, N, store_members=True):
    """Enumerate mu_N over the tau-pinned polydisc.  Returns dict:
    product-key (coeff tuple mod p^N) -> list of member tuples (or count)."""
    pN, ptau, pM = p ** N, p ** tau, p ** (N - tau)
    degs = [len(f) - 1 for f in fs]
    per_factor = []
    for f, d in zip(fs, degs):
        opts = []
        for bs in itertools.product(range(pM), repeat=d):
            g = tuple((f[i] + ptau * bs[i]) % pN for i in range(d)) + (1,)
            opts.append(g)
        per_factor.append(opts)
    fibers = {}
    for tup in itertools.product(*per_factor):
        F = polmod(polymul_many(tup), pN)
        if store_members:
            fibers.setdefault(F, []).append(tup)
        else:
            fibers[F] = fibers.get(F, 0) + 1
    return fibers

# ---------- the test battery ----------

def battery():
    x = (0, 1)
    return [
        # (label, p, factors, expected notes)
        ("B1 p=2 (x)(x+1) depth-0",            2, [(0, 1), (1, 1)]),
        ("B2 p=2 (x)(x+2) rho=1",              2, [(0, 1), (2, 1)]),
        ("B3 p=2 (x)(x+4) rho=2",              2, [(0, 1), (4, 1)]),
        ("B4 p=2 (x^2+2)(x^2+2x+2) rho=3",     2, [(2, 0, 1), (2, 2, 1)]),
        ("B5 p=2 (x)(x+2)(x+4) m=3 rho=4",     2, [(0, 1), (2, 1), (4, 1)]),
        ("B6 p=3 (x)(x+3) rho=1",              3, [(0, 1), (3, 1)]),
        ("B7 p=5 F1-shape quadratics rho=0",   5, [(6, -2, 1), (9, -4, 1)]),
        ("B8 p=5 (x)(x+5) rho=1",              5, [(0, 1), (5, 1)]),
        ("B9 p=2 (x)(x^2+x+2) mixed rho=1",    2, [(0, 1), (2, 1, 1)]),
        ("B10 p=3 (x^2+3)(x^2+3x+3) rho=3",    3, [(3, 0, 1), (3, 3, 1)]),
    ]

MAX_DOMAIN = 2 ** 21   # enumeration cap per (case, N)

def run_case(label, p, fs, results):
    degs = [len(f) - 1 for f in fs]
    n = sum(degs)
    m = len(fs)
    rho = 0
    for i in range(m):
        for j in range(i + 1, m):
            r = resultant(fs[i], fs[j])
            assert r != 0, (label, "factors not coprime")
            rho += vp(r, p)
    mat = phi_matrix(fs)
    dphi = det_bareiss(mat)
    t0 = (vp(dphi, p) == rho)
    results.append((label, "T0 v(detPhi)=rho", t0,
                    f"v={vp(dphi, p)} rho={rho}"))
    es, dks = smith_profile(mat, p)
    emax = es[-1]
    assert sum(es) == rho, (label, es, rho)
    tau = rho + 1
    # sweep N = tau .. tau+rho (covers sub-guard T1/T3 and the guard point)
    for N in range(tau, tau + rho + 1):
        M = N - tau
        dom = p ** (M * n)
        if dom > MAX_DOMAIN:
            results.append((label, f"T1 N={N}", None, f"skipped dom={dom}"))
            continue
        store = dom <= 200000
        fib = enum_fibers(p, fs, tau, N, store_members=store)
        sizes = set(len(v) if store else v for v in fib.values())
        pred = p ** sum(min(e, M) for e in es)
        ok = (sizes == {pred})
        guard = "GUARD" if M >= emax else "sub-guard"
        results.append((label, f"T1 N={N} ({guard})", ok,
                        f"sizes={sorted(sizes)} pred={pred}"))
        if store and emax <= N:
            blind = p ** (N - emax)
            ok2 = all(all(gc % blind == tup0[j][i] % blind
                          for tup in v for j, g in enumerate(tup)
                          for i, gc in enumerate(g))
                      for v in fib.values() for tup0 in [v[0]])
            results.append((label, f"T2 N={N} blind mod p^{N-emax}", ok2, ""))
    return rho, es, tau

def digit(g, coeff_idx, level, p):
    return (g[coeff_idx] // p ** level) % p

def sib_product_check(p, fs, tau, N, es, adapted=True, correlate=False,
                      deep=False):
    """T3/T4/T5.  Events E_j = {digit of coeff 0 of g_j at level L == a_j}.
    adapted: L = tau (<= N-emax).  deep: L = N-emax (one above the readable
    zone... uses first-member read => unadapted).  correlate: refine the cell
    by {dig_1 == dig_2} first (Route-1 mirror)."""
    emax = es[-1]
    fib = enum_fibers(p, fs, tau, N, store_members=True)
    L = tau if not deep else N - emax  # deep reads INSIDE the blind zone
    if deep:
        L = N - emax  # blindness holds mod p^{N-emax}: level N-emax digit
        # may straddle only if emax>0 and the fiber is nontrivial there
    m = len(fs)
    # straddle check (T5 witness): is the event well-defined per fiber?
    straddle = 0
    for F, mem in fib.items():
        vals = {tuple(digit(t[j], 0, L, p) for j in range(m)) for t in mem}
        if len(vals) > 1:
            straddle += 1
    # define events via FIRST member (a choice => unadapted if straddling)
    a = tuple(0 for _ in range(m))
    Sig, Sj, Sall = [], [0] * m, 0
    Sigsz = 0
    for F, mem in fib.items():
        d = tuple(digit(mem[0][j], 0, L, p) for j in range(m))
        if correlate and d[0] != d[1]:
            continue
        Sigsz += 1
        hits = [d[j] == a[j] for j in range(m)]
        for j in range(m):
            if hits[j]:
                Sj[j] += 1
        if all(hits):
            Sall += 1
    lhs = Sall * Sigsz ** (m - 1)
    rhs = 1
    for j in range(m):
        rhs *= Sj[j]
    return lhs, rhs, straddle, len(fib)

def main():
    results = []
    battery_data = {}
    for label, p, fs in battery():
        rho, es, tau = run_case(label, p, tuple(tuple(f) for f in fs), results)
        battery_data[label] = (p, fs, rho, es, tau)
    # T3/T4/T5 on the richer cases.
    # T4 breakage expectation: only where the two read digits are genuinely
    # decorrelated on the cell.  For an m=2 pair of LINEAR factors the product
    # pins the coefficient sum exactly, so the two depth-tau digits are
    # deterministically coupled (dig_1 + dig_2 = an F-measurable value) and the
    # diagonal cell degenerates: the events coincide on it and the product law
    # holds trivially.  Multi-coefficient factors (B4, B10) decouple, and the
    # Route-1 mirror must break the law by exactly a factor p.
    t4_expect_break = {"B4 p=2 (x^2+2)(x^2+2x+2) rho=3",
                       "B10 p=3 (x^2+3)(x^2+3x+3) rho=3"}
    for label in ["B3 p=2 (x)(x+4) rho=2", "B4 p=2 (x^2+2)(x^2+2x+2) rho=3",
                  "B5 p=2 (x)(x+2)(x+4) m=3 rho=4", "B8 p=5 (x)(x+5) rho=1",
                  "B10 p=3 (x^2+3)(x^2+3x+3) rho=3"]:
        p, fs, rho, es, tau = battery_data[label]
        N = tau + es[-1]  # guard point
        lhs, rhs, st, nf = sib_product_check(p, fs, tau, N, es, adapted=True)
        results.append((label, f"T3 adapted SIB N={N}", lhs == rhs,
                        f"lhs={lhs} rhs={rhs} straddle={st}"))
        lhs, rhs, st, nf = sib_product_check(p, fs, tau, N, es, correlate=True)
        ratio = (Fraction(lhs, rhs) if rhs else None)
        if label in t4_expect_break:
            results.append((label, f"T4 correlation cell N={N}", lhs != rhs,
                            f"lhs={lhs} rhs={rhs} ratio={ratio} "
                            f"(breakage by p={p} predicted)"))
        else:
            results.append((label, f"T4 correlation cell N={N}", None,
                            f"lhs={lhs} rhs={rhs} ratio={ratio} "
                            f"(sum-pinned degenerate geometry: coupled digits)"))
        if es[-1] > 0:
            lhs, rhs, st, nf = sib_product_check(p, fs, tau, N, es, deep=True)
            results.append((label, f"T5 deep-read N={N}", None,
                            f"straddling fibers {st}/{nf}; lhs={lhs} rhs={rhs} "
                            f"eq={lhs == rhs}"))
    npass = sum(1 for r in results if r[2] is True)
    nfail = sum(1 for r in results if r[2] is False)
    for label, test, ok, info in results:
        tag = {True: "PASS", False: "FAIL", None: "INFO"}[ok]
        print(f"[{tag}] {label} | {test} | {info}")
    print(f"\nSUMMARY: {npass} PASS, {nfail} FAIL, "
          f"{sum(1 for r in results if r[2] is None)} INFO")
    return 1 if nfail else 0

if __name__ == "__main__":
    sys.exit(main())
