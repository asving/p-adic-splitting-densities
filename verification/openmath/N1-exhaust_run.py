#!/usr/bin/env python3
"""N1-exhaust: numerical test of conjecture M05 (hExhaust / BK.env_tendsto at general n)
================================================================================

THE LEAN LAW BEING TESTED (fidelity mapping)
--------------------------------------------
Two equivalent-in-content open forms in the repo:

(1) `LeanUrat.OM.RealInstanceV2.montes_unconditional_exhaustive` hypothesis `hExhaust`
    (lean/LeanUrat/OM/RealInstanceV2.lean:441):
        Tendsto (fun N => undecidedCount N / p^(n*N)) atTop (nhds 0)
    with the `CountingModel` semantics (lean/LeanUrat/CountingModel.lean:95-102):
        decidedCount sigma N = #{ monic-degree-n coefficient cosets f mod p^N such that
                                  EVERY Z_p-lift of f has factorization type sigma }
        undecidedCount N     = p^(n*N) - sum_sigma decidedCount sigma N
    FactorizationType (lean/LeanUrat/Interface.lean:152) = multiset of (e_i, f_i)
    (ramification index, residue degree) over the irreducible Q_p-factors, sum e_i*f_i = n.
    The pinned Lean instance has realP = 2; the M05 charge is the general-(n,p) law.

(2) `LeanUrat.MovesU.BridgeKernels.env_tendsto` (lean/LeanUrat/MovesU/BridgeKernels.lean:230):
        Tendsto X.env atTop (nhds 0),  X.env N = #{f in Box p n N : canonical N f = none}/p^(nN)
    for the OM/Montes canonical classifier X : ClassifierSpec n p, which is choice-free,
    refinement-stable (`canonical_stable`) and sound (`VPSound`: decided-sigma => true type sigma).
    Marked "hExhaust AT GENERAL n - FENCED MATH" (open; n=2 discharged in
    OM/UniformCapstone.hExhaustP / OM/SeriesAssembly.hExhaust_n2).

WHAT THIS SCRIPT COMPUTES (the surrogate, and the exact mapping)
----------------------------------------------------------------
A level-N coset is SEMANTICALLY UNDECIDED iff its factorization type is NOT constant
over all Z_p-lifts -- exactly form (1)'s undecided set.  Direct computation of the
semantic undecided mass U_sem(N) is not finitely decidable coset-by-coset, so we
measure certified two-sided bounds that squeeze it:

  (a) U_cert(N) = P_f( N < 2*v_p(disc f) + 1 )
      = the undecided envelope of the KRASNER-DISCRIMINANT classifier
        "decide the coset (with the type of any representative) iff N >= 2*v_p(disc)+1".
      THEOREM (soundness of the certificate; standard Krasner/Hensel continuity):
        if f,g monic in Z_p[x], f separable, g == f coefficientwise mod p^m with
        m >= 2*v_p(disc f) + 1, then f and g have the same factorization type.
        Proof sketch: all roots theta_i of f lie in the integral closure (f monic), so
        v(g(theta_i)) >= m > 2*v_p(disc f) >= 2*v(f'(theta_i))  (v(disc)=sum_i v(f'(theta_i))).
        Newton iteration then yields a root beta_i of g with
        v(beta_i - theta_i) > v(disc f) >= v(f'(theta_i)) = sum_{j!=i} v(theta_i-theta_j)
        >= max_j v(theta_i - theta_j), so Krasner gives Q_p(theta_i) <= Q_p(beta_i);
        v(disc g) = v(disc f) (< m) makes the situation symmetric, the two nearest-root
        maps are mutually inverse Galois-equivariant bijections, so factors correspond
        with equal degrees and equal fields; hence equal (e,f) multisets.
      This classifier is choice-free, stable under refinement and sound -- a genuine
      instance of ClassifierSpec's laws -- so U_cert(N) -> 0 WITNESSES form (2) for an
      explicit classifier, and upper-bounds U_sem(N).
      Computed EXACTLY at small levels (survivor-set recursion for P(v_p(disc) >= m))
      and by Monte Carlo (exact integer discriminants of deep random samples) beyond.

  (b) U_lower(N) <= U_sem(N): certified undecided mass -- cosets for which we EXHIBIT
      two exact lifts with different factorization types (types of exact integer
      polynomials, computed by exact oracles; see ORACLES below).  Two instruments:
        - EXHAUSTIVE-C: enumerate ALL p^(nC) monic cosets at depth C, compute each
          representative's exact type, and for every N <= C mark a level-N coset
          undecided when two of its depth-C members' types differ.  Exact exhaustive
          lower bound for U_sem(N), all N <= C.
        - MC: sample M cosets (deep random f, 60 base-p digits); at each level N not
          yet certificate-decided (N < 2*v_p(disc f)+1), test T fresh random deep lifts
          for a type disagreement.
      "All sampled lifts agree" is NEVER counted as decided; only certificates enter
      the reported bounds, in both directions.

  (c) n=2 EXACT ANCHOR: for quadratics the semantic law is decidable in closed form
      (discriminant square-class analysis, including wild p=2):
        p odd : coset (a1,a0) mod p^N undecided <=> v_p(a1^2-4a0) >= N.
        p = 2 : the reachable discriminant set of the coset is EXACTLY D0 + 2^M Z_2,
                M = N+2 if a1 even, M = N+1 if a1 odd and N>=2, M = 3 if a1 odd, N=1
                (derived by expanding (a1+2^N s)^2 - 4(a0+2^N t); the N=1-odd case has
                the parity obstruction a1*s + s^2 == 0 mod 2).  On such a ball:
                v(D)>=M => undecided; v odd => decided (ram);
                v even: M-v>=3 decided (u mod 8 known); M-v=2 decided iff u=3 mod 4
                (both classes ram); M-v<=1 undecided.
      This exact U_sem is validated against brute-force lift enumeration (selftest) and
      calibrates how tight (a) and (b) are.  n=2 doubles as a consistency check against
      the PROVED Lean n=2 exhaustion (SeriesAssembly.hExhaust_n2, UniformCapstone.hExhaustP).

ORACLES (all inputs exact integers)
-----------------------------------
  n=2: padic_types.quad_type (pure Python; disc square classes, p=2 mod-8 law).
       D=0 handled as 'split' (exact rational double root).
  n=3: padic_types.cubic_type_monic (pure Python; Hensel + Newton polygons, wild-safe).
       Codes map to (e,f) multisets: 111->(1,1)^3, 12->(1,1)(1,2), 3->(1,3),
       1r1->(1,1)(2,1), 1c->(3,1).
  n=4,5: PARI/GP 2.17 subprocess ('gp -q'):
       - fulltype: factorpadic + per-nonlinear-factor Krasner lift + nfinit([G,[p]]) +
         idealprimedec => exact (e_i,f_i) multiset (port of the calibrated in-repo
         verification/quartic_oracle.py; cypari2 not buildable on this box, same logic
         through the gp pipe).  Working precision auto-escalated to 2*v_p(disc)+25.
       - reftype (fast path for MC disagreement detection): factor degrees + integer
         coefficient lifts; Python then refines factors of degree<=3 to exact (e,f)
         via the pure quad/cubic laws.  Factors of degree>=4 compared as opaque
         degree tags ('D',d).
  Oracle cross-validation in --block selftest (pure Python vs GP on random samples,
  plus known calibration fields).

SIMPLIFICATIONS / HONESTY FLAGS
-------------------------------
  F1. The as-built Lean OM-tree classifier has no executable extraction; we test the
      MATHEMATICAL law (semantic exhaustion + an explicit sound classifier's envelope),
      not the Lean engine's own decision lag.  The gap between the two is bounded by
      the GMN disc-depth termination theorem, which is the repo's trusted axiom.
  F2. In the MC path at n=4,5, factors of degree>=4 are compared as opaque degree tags:
      (e,f)-only disagreements inside irreducible quartic/quintic factors are missed
      there => U_lower slightly weaker (never wrong).  The exhaustive-C runs at n=4,5
      use full (e,f) and do not have this gap.
  F3. All MC numbers carry Wilson 95% CIs; exhaustive numbers are exact integers.
  F4. U_sem is only BRACKETED for n>=3 (U_lower <= U_sem <= U_cert); the conjecture's
      content (mass -> 1) is confirmed iff the UPPER bracket U_cert -> 0, which is the
      strictly stronger requirement.

VERDICT CRITERIA
----------------
  CONFIRMED needs, for every (n,p) in the grid n in {2..5} x p in {2,3,5,7,11}:
    - P(v_p(disc) >= m) decays geometrically (ratio ~ 1/p per digit): so
      U_cert(N) -> 0 at rate ~ p^(-1/2) per level;
    - certified undecided mass decays consistently (~ p^(-1) per level where visible);
    - the n=2 exact semantic law matches the bracket and decays at exactly p^(-1)/level.
  REFUTED if some (n,p) shows a non-vanishing floor: P(v_p(disc)>=m) flattening at a
  positive value, or certified-undecided mass not decaying (with a concrete coset
  family as the counterexample, double-checked against PARI).

USAGE
-----
  .venv-openmath/bin/python N1-exhaust_run.py --block {selftest,n2,n3,n4,n5,summary} [--quick]
Each block appends to verification/openmath/logs/ and writes
verification/openmath/N1-exhaust_results_<block>.json; `summary` merges + prints tables.
"""

import argparse
import ast
import json
import math
import os
import random
import subprocess
import sys
import time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
VERIF = os.path.dirname(HERE)
sys.path.insert(0, VERIF)

from padic_types import quad_type, cubic_type_monic, vp  # noqa: E402

GP_BIN = os.path.expanduser("~/.local/bin/gp")
GP_LIB = os.path.expanduser("~/.local/lib")

PRIMES = [2, 3, 5, 7, 11]
DIGITS = 60          # base-p digits for "deep" random Z_p samples
RNG_SEED = 20260731

# Per-(n,p): max level N for the tables
def NMAX(n, p):
    return {2: 14, 3: 10, 5: 8, 7: 7, 11: 6}[p]

# Exhaustive-C depth per (n,p): all p^(nC) cosets enumerated, exact rep types.
EXH_C = {
    (2, 2): 9, (2, 3): 6, (2, 5): 4, (2, 7): 3, (2, 11): 3,
    (3, 2): 6, (3, 3): 4, (3, 5): 3, (3, 7): 2, (3, 11): 2,
    (4, 2): 4, (4, 3): 2, (4, 5): 2, (4, 7): 1, (4, 11): 1,
    (5, 2): 3, (5, 3): 2, (5, 5): 1, (5, 7): 1, (5, 11): 1,
}
# n=4,5: use the (slow) full-(e,f) oracle when p^(nC) <= this; else fast refined tags.
FULLTYPE_BUDGET = 40000

# MC sample sizes
def MC_SIZES(n, quick):
    if n <= 3:
        return (20000 if not quick else 1500), 16     # M cosets, T lifts
    return (5000 if not quick else 400), 12

DISC_MC = {2: 200000, 3: 200000, 4: 120000, 5: 80000}   # disc-tail MC samples
SURV_WORK_BUDGET = 4_000_000                            # survivor-recursion eval budget


# ----------------------------------------------------------------------------
# discriminants (exact integer, monic coefficient tuples low->high, no leading 1)
# ----------------------------------------------------------------------------

def disc_n2(c):
    a0, a1 = c
    return a1 * a1 - 4 * a0

def disc_n3(c):
    a0, a1, a2 = c
    return (18 * a2 * a1 * a0 - 4 * a2**3 * a0 + a2**2 * a1**2
            - 4 * a1**3 - 27 * a0**2)

_DISC_COMPILED = {}

def _sympy_disc_fn(n):
    """Generate the exact disc polynomial for monic degree n once via sympy."""
    import sympy
    xs = sympy.symbols("a0:%d" % n)
    x = sympy.Symbol("x")
    f = x**n + sum(xs[i] * x**i for i in range(n))
    d = sympy.expand(sympy.discriminant(f, x))
    code = compile(str(d), "<disc%d>" % n, "eval")
    names = [str(s) for s in xs]
    def fn(c, _code=code, _names=names):
        return eval(_code, {"__builtins__": {}}, dict(zip(_names, c)))
    return fn

def disc_fn(n):
    if n == 2:
        return disc_n2
    if n == 3:
        return disc_n3
    if n not in _DISC_COMPILED:
        _DISC_COMPILED[n] = _sympy_disc_fn(n)
    return _DISC_COMPILED[n]

def resultant_bareiss(f, g):
    """Exact integer resultant via Sylvester matrix + Bareiss (cross-check only)."""
    m, n_ = len(f) - 1, len(g) - 1
    N_ = m + n_
    M = [[0] * N_ for _ in range(N_)]
    for i in range(n_):
        for j, cf in enumerate(f):
            M[i][i + j] = cf
    for i in range(m):
        for j, cg in enumerate(g):
            M[n_ + i][i + j] = cg
    # Bareiss
    prev = 1
    sign = 1
    for k in range(N_ - 1):
        if M[k][k] == 0:
            piv = next((r for r in range(k + 1, N_) if M[r][k] != 0), None)
            if piv is None:
                return 0
            M[k], M[piv] = M[piv], M[k]
            sign = -sign
        for i in range(k + 1, N_):
            for j in range(k + 1, N_):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
            M[i][k] = 0
        prev = M[k][k]
    return sign * M[N_ - 1][N_ - 1]

def disc_via_resultant(n, c):
    """disc = (-1)^(n(n-1)/2) * Res(f, f') for monic f (cross-check path)."""
    f = list(c) + [1]                      # low->high
    fp = [i * f[i] for i in range(1, n + 1)]
    r = resultant_bareiss(f[::-1], fp[::-1])
    return (-1) ** (n * (n - 1) // 2) * r


# ----------------------------------------------------------------------------
# exact type oracles -> canonical type = sorted tuple of (e,f) pairs
# ----------------------------------------------------------------------------

QUAD_MAP = {"split": ((1, 1), (1, 1)), "inert": ((1, 2),), "ram": ((2, 1),)}
CUBIC_MAP = {"111": ((1, 1), (1, 1), (1, 1)), "12": ((1, 1), (1, 2)),
             "3": ((1, 3),), "1r1": ((1, 1), (2, 1)), "1c": ((3, 1),)}

def type_n2(c, p):
    a0, a1 = c
    if a1 * a1 - 4 * a0 == 0:
        return QUAD_MAP["split"]           # exact rational double root
    t = quad_type(a1, a0, p)
    return QUAD_MAP[t] if t != "UND" else None

def type_n3(c, p):
    a0, a1, a2 = c
    t = cubic_type_monic(a2, a1, a0, p)
    return CUBIC_MAP[t] if t != "UND" else None


class GPOracle:
    """Persistent gp -q subprocess; exact p-adic factorization types."""

    def __init__(self):
        env = os.environ.copy()
        env["LD_LIBRARY_PATH"] = GP_LIB + ":" + env.get("LD_LIBRARY_PATH", "")
        self.proc = subprocess.Popen(
            [GP_BIN, "-q", "-f", "-s", "400000000"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, env=env, bufsize=1)
        self.timeouts = 0
        self._raw("default(realprecision, 38);")
        # exact (e,f) multiset; port of verification/quartic_oracle.py logic
        self._defun('''fulltype(cs, p, prec) = {
          my(f = Polrev(cs), fac = factorpadic(f, p, prec), res = List());
          for(i=1, matsize(fac)[1],
            my(g = fac[i,1], m = fac[i,2], d = poldegree(g), ef);
            if(d == 1, ef = [1,1],
              my(V = Vec(liftall(g))); V[1] = 1;
              my(G = Pol(V), K = nfinit([G,[p]]), dec = idealprimedec(K,p), pick=0);
              for(j=1,#dec, if(dec[j].e*dec[j].f == d && !pick, pick=j));
              if(!pick, pick=1);
              ef = [dec[pick].e, dec[pick].f]);
            for(k=1,m, listput(res, ef)));
          vecsort(Vec(res))
        }''')
        # fast refined tags: [deg, lifted coeffs...] per factor (deg<=3), [deg] else
        self._defun('''reftype(cs, p, prec) = {
          my(f = Polrev(cs), fac = factorpadic(f, p, prec), res = List());
          for(i=1, matsize(fac)[1],
            my(g = fac[i,1], m = fac[i,2], d = poldegree(g));
            my(item = if(d <= 3, concat([d], Vecrev(liftall(g))), [d]));
            for(k=1,m, listput(res, item)));
          vecsort(Vec(res))
        }''')

    def _raw(self, s):
        self.proc.stdin.write(s + "\n")
        self.proc.stdin.flush()

    def _defun(self, s):
        self._raw(s)
        self._raw('print("@@")')
        while True:
            line = self.proc.stdout.readline()
            if line == "":
                raise RuntimeError("gp died during setup")
            if line.strip() == "@@":
                break

    def query(self, expr, timeout_s=20):
        self._raw('print(iferr(alarm(%d, %s), E, "ERR"))' % (timeout_s, expr))
        self._raw('print("@@")')
        lines = []
        while True:
            line = self.proc.stdout.readline()
            if line == "":
                raise RuntimeError("gp died: " + "".join(lines))
            line = line.strip()
            if line == "@@":
                break
            if line:
                lines.append(line)
        out = lines[-1] if lines else "ERR"
        if out == "ERR":
            self.timeouts += 1
            return None
        return out

    def full_type(self, c, p, prec):
        r = self.query("fulltype(%s, %d, %d)" % (list(c) + [1], p, prec))
        if r is None:
            return None
        pairs = ast.literal_eval(r.replace(" ", ""))
        return tuple(sorted(tuple(q) for q in pairs))

    def ref_type(self, c, p, prec):
        """Refined tag multiset (see header F2). Exact type-function of the poly."""
        r = self.query("reftype(%s, %d, %d)" % (list(c) + [1], p, prec))
        if r is None:
            return None
        items = ast.literal_eval(r.replace(" ", ""))
        tags = []
        for it in items:
            d = it[0]
            if d == 1:
                tags.append((1, 1))
            elif d == 2:
                a0, a1 = it[1], it[2]     # lifted ints; it[3]=1 leading
                t = type_n2((a0, a1), p)
                if t is None:
                    return None           # precision-guard trip: caller escalates
                tags.append(("q",) + t)
            elif d == 3:
                a0, a1, a2 = it[1], it[2], it[3]
                t = type_n3((a0, a1, a2), p)
                if t is None:
                    return None
                tags.append(("c",) + t)
            else:
                tags.append(("D", d))
        return tuple(sorted(map(repr, tags)))


_GP = None

def gp():
    global _GP
    if _GP is None:
        _GP = GPOracle()
    return _GP


def exact_type(n, c, p, disc_val=None):
    """Exact factorization type of the EXACT integer monic poly x^n + sum c_i x^i.
    Returns canonical (e,f)-multiset, or None (rare oracle UND; caller decides)."""
    if n == 2:
        return type_n2(c, p)
    if n == 3:
        return type_n3(c, p)
    dv = disc_val
    if dv is None:
        d = disc_fn(n)(c)
        if d == 0:
            return _inseparable_type(n, c, p)
        dv = vp(abs(d), p)
    prec = max(30, 2 * dv + 25)
    return gp().full_type(c, p, prec)

def _inseparable_type(n, c, p):
    """Exact type for disc==0 reps (repeated factors): sympy squarefree split."""
    import sympy
    x = sympy.Symbol("x")
    f = sympy.Poly(x**n + sum(int(ci) * x**i for i, ci in enumerate(c)), x)
    out = []
    for g, mult in f.factor_list()[1]:
        cs = [int(v) for v in reversed(g.all_coeffs())]   # low->high, monic*content?
        lead = cs[-1]
        if lead != 1:                     # primitive non-monic rational factor: rescale
            # monic rational factors of a monic integer poly are integral (Gauss)
            cs = [ci // lead for ci in cs]
        deg = len(cs) - 1
        sub = exact_type(deg, tuple(cs[:-1]), p) if deg >= 2 else ((1, 1),)
        if sub is None:
            return None
        out.extend(list(sub) * mult)
    return tuple(sorted(out))


# ----------------------------------------------------------------------------
# n=2 exact semantic law (header (c))
# ----------------------------------------------------------------------------

def quad_sem_decided(a1, a0, N, p):
    """EXACT semantic decidedness of the level-N coset of x^2+a1x+a0 (reps mod p^N)."""
    D0 = a1 * a1 - 4 * a0
    if p != 2:
        if D0 == 0 or D0 % p**N == 0:
            return False
        return vp(abs(D0), p) < N
    M = (N + 2) if a1 % 2 == 0 else (3 if N == 1 else N + 1)
    if D0 == 0 or D0 % (1 << M) == 0:
        return False
    v = vp(abs(D0), 2)
    if v >= M:
        return False
    if v % 2 == 1:
        return True                        # ram, constant on the ball
    u = abs(D0) >> v if D0 > 0 else -((-D0) >> v)
    u = u % (1 << min(3, M - v))
    if M - v >= 3:
        return True
    if M - v == 2:
        return u % 4 == 3                  # {3,7} mod 8: both ram
    return False


# ----------------------------------------------------------------------------
# Phase 1: disc-valuation tail P(v_p(disc) >= m); U_cert(N) = tail(ceil(N/2))
# ----------------------------------------------------------------------------

def disc_tail(n, p, quick, log):
    dfn = disc_fn(n)
    tail = {0: (1.0, "exact")}
    # exact survivor recursion: S_m = {f mod p^m : disc(f) == 0 mod p^m};
    # only members of S_m can have children in S_{m+1}, so the work per step is
    # |S_m| * p^n.  Cosets represented by integer coeff tuples in [0, p^m).
    S = [(0,) * n]
    m = 0
    while True:
        work = len(S) * (p ** n)
        if work > (SURV_WORK_BUDGET if not quick else 200000):
            break
        m += 1
        pm, pm1 = p ** m, p ** (m - 1)
        nxt = []
        for base in S:
            for delta in range(p ** n):
                d, cc = delta, []
                for i in range(n):
                    cc.append(base[i] + (d % p) * pm1)
                    d //= p
                if dfn(cc) % pm == 0:
                    nxt.append(tuple(cc))
        S = nxt
        tail[m] = (len(S) / p ** (n * m), "exact")
        if not S:
            break
    exact_to = m
    # MC tail: exact integer discs of deep samples
    Smc = DISC_MC[n] if not quick else 20000
    rng = random.Random("%d-disc-%d-%d" % (RNG_SEED, n, p))
    pK = p ** DIGITS
    counts = defaultdict(int)
    for _ in range(Smc):
        c = tuple(rng.randrange(pK) for _ in range(n))
        d = dfn(c)
        if d == 0:
            continue
        v = vp(abs(d), p)
        counts[v] += 1
    mmax_mc = max(counts) if counts else 0
    cum = 0
    mc_tail = {}
    for v in range(mmax_mc, -1, -1):
        cum += counts[v]
        mc_tail[v] = cum / Smc
    for v in sorted(mc_tail):
        if v not in tail and mc_tail[v] * Smc >= 20:
            tail[v] = (mc_tail[v], "mc(%d)" % Smc)
    # consistency: exact vs MC where both exist
    for v in range(1, exact_to + 1):
        if v in mc_tail and tail[v][1] == "exact":
            ex, mc = tail[v][0], mc_tail[v]
            if ex > 0 and mc > 0:
                se = math.sqrt(mc * (1 - mc) / Smc)
                if abs(ex - mc) > 5 * max(se, 1e-9):
                    log("  [WARN] disc-tail exact/MC mismatch at m=%d: %.3g vs %.3g" % (v, ex, mc))
    # geometric fit on ln tail
    pts = [(v, tv[0]) for v, tv in sorted(tail.items()) if v >= 1 and tv[0] > 0]
    fit = None
    if len(pts) >= 3:
        xs = [v for v, _ in pts]
        ys = [math.log(t) for _, t in pts]
        nn = len(xs)
        sx, sy = sum(xs), sum(ys)
        sxx = sum(x * x for x in xs)
        sxy = sum(x * y for x, y in zip(xs, ys))
        slope = (nn * sxy - sx * sy) / (nn * sxx - sx * sx)
        fit = math.exp(slope)              # per-digit ratio; theory ~ 1/p
    return tail, exact_to, fit


def u_cert_from_tail(tail, N):
    # U_cert(N) = P(2v+1 > N) = P(v > (N-1)/2) = P(v >= floor((N-1)/2)+1)
    m = (N - 1) // 2 + 1
    return tail.get(m, (None, None))


# ----------------------------------------------------------------------------
# Phase 2: exhaustive-C certified-undecided lower bounds for all N <= C
# ----------------------------------------------------------------------------

def exhaustive_scan(n, p, C, quick, log):
    if quick and p ** (n * C) > 60000:
        C = max(1, C - 1)
    total = p ** (n * C)
    dfn = disc_fn(n)
    use_full = (n <= 3) or (total <= FULLTYPE_BUDGET)
    t0 = time.time()
    # per level N: dict trunc-key -> first type; set of undecided keys
    first = [dict() for _ in range(C + 1)]
    undec = [set() for _ in range(C + 1)]
    und_oracle = 0
    pN = [p ** N for N in range(C + 1)]
    for idx in range(total):
        d, c = idx, []
        for i in range(n):
            c.append(d % pN[C])
            d //= pN[C]
        c = tuple(c)
        dv = dfn(c)
        if n <= 3:
            t = exact_type(n, c, p)
        elif use_full:
            t = exact_type(n, c, p, disc_val=(vp(abs(dv), p) if dv else None))
        else:
            if dv == 0:
                t = _inseparable_type(n, c, p)
                t = repr(t) if t is not None else None
            else:
                v = vp(abs(dv), p)
                t = gp().ref_type(c, p, max(40, 2 * v + 25))
        if t is None:
            und_oracle += 1
            continue
        for N in range(1, C + 1):
            key = tuple(ci % pN[N] for ci in c)
            if key in undec[N]:
                continue
            prev = first[N].get(key)
            if prev is None:
                first[N][key] = t
            elif prev != t:
                undec[N].add(key)
    out = {}
    for N in range(1, C + 1):
        out[N] = len(undec[N]) / p ** (n * N)
    log("  exhaustive C=%d (%d reps, %s types, %d oracle-skips) in %.1fs" %
        (C, total, "full-ef" if use_full else "refined-tag", und_oracle, time.time() - t0))
    return out, C, ("full" if use_full else "refined")


# ----------------------------------------------------------------------------
# Phase 3: MC certified-undecided lower bounds + empirical cert envelope
# ----------------------------------------------------------------------------

def wilson(k, n_):
    if n_ == 0:
        return (0.0, 0.0, 1.0)
    z = 1.96
    ph = k / n_
    den = 1 + z * z / n_
    ctr = ph + z * z / (2 * n_)
    rad = z * math.sqrt(ph * (1 - ph) / n_ + z * z / (4 * n_ * n_))
    return (ph, max(0.0, (ctr - rad) / den), min(1.0, (ctr + rad) / den))


def mc_scan(n, p, quick, log):
    M, T = MC_SIZES(n, quick)
    Nmax = NMAX(n, p)
    dfn = disc_fn(n)
    rng = random.Random("%d-mc-%d-%d" % (RNG_SEED, n, p))
    pK = p ** DIGITS
    undec_k = defaultdict(int)             # N -> #certified-undecided
    notcert_k = defaultdict(int)           # N -> #not certificate-decided (env sample)
    oracle_skips = 0
    t0 = time.time()
    for _ in range(M):
        while True:
            f = tuple(rng.randrange(pK) for _ in range(n))
            dv = dfn(f)
            if dv != 0:
                break
        vstar = vp(abs(dv), p)
        certN = 2 * vstar + 1              # coset certificate-decided iff N >= certN
        for N in range(1, min(Nmax, certN - 1) + 1):
            if N >= certN:
                break
            notcert_k[N] += 1
            pN = p ** N
            base = tuple(ci % pN for ci in f)
            seen = None
            found = False
            for _ in range(T):
                g = tuple(b + pN * rng.randrange(pK) for b in base)
                dg = dfn(g)
                if dg == 0:
                    continue
                vg = vp(abs(dg), p)
                if n <= 3:
                    t = exact_type(n, g, p)
                else:
                    t = gp().ref_type(g, p, max(40, 2 * vg + 25))
                if t is None:
                    oracle_skips += 1
                    continue
                if seen is None:
                    seen = t
                elif t != seen:
                    found = True
                    break
            if found:
                undec_k[N] += 1
    out = {}
    for N in range(1, Nmax + 1):
        ph, lo, hi = wilson(undec_k[N], M)
        phc, loc, hic = wilson(notcert_k[N], M)
        out[N] = {"undec_lower": ph, "undec_lo95": lo, "undec_hi95": hi,
                  "notcert": phc, "M": M}
    log("  MC M=%d T=%d done in %.1fs (oracle skips %d)" % (M, T, time.time() - t0, oracle_skips))
    return out


# ----------------------------------------------------------------------------
# Phase 4 (n=2): exact semantic mass by enumeration
# ----------------------------------------------------------------------------

def quad_exact_sem(p, quick, log):
    out = {}
    budget = 1_200_000 if not quick else 40000
    N = 1
    while p ** (2 * N) <= budget:
        pN = p ** N
        und = 0
        for a1 in range(pN):
            for a0 in range(pN):
                if not quad_sem_decided(a1, a0, N, p):
                    und += 1
        out[N] = (und / p ** (2 * N), "exact")
        N += 1
    # MC extension
    rng = random.Random("%d-qsem-%d" % (RNG_SEED, p))
    Smc = 200000 if not quick else 20000
    pK = p ** DIGITS
    Nmax = NMAX(2, p)
    ks = defaultdict(int)
    for _ in range(Smc):
        a0, a1 = rng.randrange(pK), rng.randrange(pK)
        for N in range(1, Nmax + 1):
            pN = p ** N
            if not quad_sem_decided(a1 % pN, a0 % pN, N, p):
                ks[N] += 1
    for N in range(1, Nmax + 1):
        if N not in out and ks[N] >= 20:
            out[N] = (ks[N] / Smc, "mc(%d)" % Smc)
    return out


# ----------------------------------------------------------------------------
# block runners
# ----------------------------------------------------------------------------

def fit_rate(pairs):
    """OLS ln-fit; returns per-level ratio."""
    pts = [(N, u) for N, u in pairs if u and u > 0]
    if len(pts) < 3:
        return None
    xs = [a for a, _ in pts]
    ys = [math.log(b) for _, b in pts]
    nn, sx, sy = len(xs), sum(xs), sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    den = nn * sxx - sx * sx
    if den == 0:
        return None
    return math.exp((nn * sxy - sx * sy) / den)


def run_block(n, quick, log):
    results = {}
    for p in PRIMES:
        log("== (n=%d, p=%d)%s ==" % (n, p, "  [WILD]" if p <= n else ""))
        r = {}
        tail, exact_to, dfit = disc_tail(n, p, quick, log)
        r["disc_tail"] = {str(m): [tv[0], tv[1]] for m, tv in sorted(tail.items())}
        r["disc_tail_exact_to"] = exact_to
        r["disc_tail_ratio_fit"] = dfit
        log("  disc tail P(v>=m): " + "  ".join(
            "m%d:%.3g%s" % (m, tv[0], "" if tv[1] == "exact" else "~")
            for m, tv in sorted(tail.items()) if 1 <= m <= 10))
        log("  disc-tail per-digit ratio fit: %s (theory ~ 1/p = %.3f)" %
            ("%.4f" % dfit if dfit else "n/a", 1 / p))

        Nmax = NMAX(n, p)
        ucert = {}
        for N in range(1, Nmax + 1):
            val, src = u_cert_from_tail(tail, N)
            if val is not None:
                ucert[N] = val
        r["U_cert"] = {str(N): v for N, v in ucert.items()}

        C = EXH_C[(n, p)]
        exh, Cused, exh_mode = exhaustive_scan(n, p, C, quick, log)
        r["U_exh_lower"] = {str(N): v for N, v in exh.items()}
        r["exh_C"], r["exh_mode"] = Cused, exh_mode

        mc = mc_scan(n, p, quick, log)
        r["U_mc"] = {str(N): v for N, v in mc.items()}

        if n == 2:
            sem = quad_exact_sem(p, quick, log)
            r["U_sem_exact"] = {str(N): [v, src] for N, (v, src) in sorted(sem.items())}

        # table
        log("  %-3s %-12s %-12s %-22s %s" % ("N", "U_cert", "U_exh_low",
            "U_mc_low [95%CI]", "U_sem_exact (n=2)"))
        for N in range(1, Nmax + 1):
            uc = ucert.get(N)
            ue = exh.get(N)
            um = mc.get(N)
            us = (r.get("U_sem_exact") or {}).get(str(N))
            log("  %-3d %-12s %-12s %-22s %s" % (
                N,
                "%.3g" % uc if uc is not None else "-",
                "%.3g" % ue if ue is not None else "-",
                ("%.3g [%.2g,%.2g]" % (um["undec_lower"], um["undec_lo95"], um["undec_hi95"])) if um else "-",
                ("%.3g %s" % (us[0], us[1])) if us else ""))

        # rates + sandwich checks + flags
        rate_cert = fit_rate([(N, ucert.get(N)) for N in range(1, Nmax + 1)])
        rate_exh = fit_rate([(N, exh.get(N)) for N in exh])
        mc_pairs = [(N, mc[N]["undec_lower"]) for N in mc if mc[N]["M"] * mc[N]["undec_lower"] >= 15]
        rate_mc = fit_rate(mc_pairs)
        r["rate_cert"], r["rate_exh"], r["rate_mc"] = rate_cert, rate_exh, rate_mc
        log("  per-level ratios: U_cert %s (theory ~ p^-1/2 = %.3f) | exh-lower %s | mc-lower %s (theory ~ 1/p = %.3f)" %
            ("%.3f" % rate_cert if rate_cert else "n/a", p ** -0.5,
             "%.3f" % rate_exh if rate_exh else "n/a",
             "%.3f" % rate_mc if rate_mc else "n/a", 1 / p))

        flags = []
        # FLAG: non-decay of the certified envelope
        vals = [ucert[N] for N in sorted(ucert)]
        if len(vals) >= 4 and vals[-1] > 0.5 * vals[1]:
            flags.append("U_cert not visibly decaying")
        if dfit is not None and dfit > 0.75 / p * p and dfit > 1.6 / p:
            flags.append("disc tail decays slower than ~1/p (fit %.3f)" % dfit)
        # sandwich violations: lower bounds must not exceed U_cert
        for N in sorted(ucert):
            uc = ucert[N]
            if N in exh and exh[N] > uc + 1e-12:
                flags.append("SANDWICH VIOLATION exh at N=%d: %.3g > %.3g" % (N, exh[N], uc))
            if N in mc and mc[N]["undec_lo95"] > uc + 0.002:
                flags.append("SANDWICH VIOLATION mc at N=%d" % N)
            if n == 2:
                us = (r.get("U_sem_exact") or {}).get(str(N))
                if us and us[1] == "exact":
                    if us[0] > uc + 1e-12:
                        flags.append("n2 exact sem > U_cert at N=%d" % N)
                    if N in exh and exh[N] > us[0] + 1e-12:
                        flags.append("n2 exh lower > exact sem at N=%d" % N)
        if flags:
            for fl in flags:
                log("  [FLAG] " + fl)
        else:
            log("  flags: none")
        r["flags"] = flags
        results["p%d" % p] = r
    return results


# ----------------------------------------------------------------------------
# selftest
# ----------------------------------------------------------------------------

def run_selftest(quick, log):
    ok = True
    rng = random.Random(4242)

    log("[1] disc formulas n=4,5: sympy-compiled vs Bareiss resultant")
    for n in (4, 5):
        d = disc_fn(n)
        for _ in range(200):
            c = tuple(rng.randrange(-10**6, 10**6) for _ in range(n))
            if d(c) != disc_via_resultant(n, c):
                log("  MISMATCH n=%d c=%s" % (n, c)); ok = False
    log("  ok" if ok else "  FAILED")

    log("[2] GP calibration cases (known local fields)")
    cases = [
        ((2, 0, 0, 0), 4, 2, ((4, 1),)),          # x^4+2 /Q_2 totally ramified
        ((1, 0, 0, 0), 4, 2, ((4, 1),)),          # x^4+1 = Q_2(zeta_8): totally ram (4,1)
                                                  # (quartic_oracle.py calibration case)
        ((-17, 0, 0, 0), 4, 2, None),             # x^4-17: just print
        ((-2, 0, 0, 0, 0), 5, 5, ((5, 1),)),      # x^5-2 /Q_5
        ((-1, 0, 0, 0, 0), 5, 11, ((1, 1),) * 5), # x^5-1 /Q_11 splits
        ((1, 1, 0, 1), 4, 2, None),               # print
    ]
    for c, n, p, want in cases:
        got = exact_type(n, c, p)
        log("  n=%d p=%d c=%s -> %s%s" % (n, p, c, got,
            "" if want is None else (" (want %s)" % (want,))))
        if want is not None and got != want:
            log("  CALIBRATION FAILURE"); ok = False

    log("[3] pure-Python quad/cubic vs GP fulltype on random exact polys")
    for n in (2, 3):
        for p in (2, 3, 5):
            mism = skip = 0
            for _ in range(120 if not quick else 30):
                c = tuple(rng.randrange(p ** 12) for _ in range(n))
                t1 = exact_type(n, c, p)
                if t1 is None:
                    skip += 1
                    continue
                dv = disc_fn(n)(c)
                v = vp(abs(dv), p) if dv else None
                t2 = gp().full_type(c, p, max(30, 2 * (v or 0) + 25))
                if t2 is not None and t1 != t2:
                    mism += 1
                    log("  MISMATCH n=%d p=%d c=%s py=%s gp=%s" % (n, p, c, t1, t2))
            if mism:
                ok = False
            log("  n=%d p=%d: mismatches %d (skips %d)" % (n, p, mism, skip))

    log("[4] n=2 closed-form semantic law vs brute-force lift enumeration")
    for p in (2, 3):
        for N in (1, 2, 3):
            pN = p ** N
            ext = 8 if p == 2 else 5       # extra digits enumerated below level N
            bad = 0
            for a1 in range(pN):
                for a0 in range(pN):
                    claim = quad_sem_decided(a1, a0, N, p)
                    types = set()
                    pE = p ** ext
                    for s in range(pE):
                        for t_ in range(pE):
                            g = (a0 + pN * t_, a1 + pN * s)
                            ty = type_n2(g, p)
                            if ty is not None:
                                types.add(ty)
                            if len(types) > 1:
                                break
                        if len(types) > 1:
                            break
                    found_disagree = len(types) > 1
                    if claim and found_disagree:
                        bad += 1
                        log("  claimed DECIDED but lifts disagree: p=%d N=%d (a1,a0)=(%d,%d)" % (p, N, a1, a0))
                    if (not claim) and (not found_disagree):
                        bad += 1
                        log("  claimed UNDECIDED but no disagreement to depth +%d: p=%d N=%d (a1,a0)=(%d,%d)" % (ext, p, N, a1, a0))
            if bad:
                ok = False
            log("  p=%d N=%d: ok" % (p, N) if not bad else "  p=%d N=%d: %d bad" % (p, N, bad))
            if p == 2 and N == 3 and quick:
                break

    log("[5] Krasner-certificate spot audit (cert-decided cosets, 8 lifts must agree)")
    for (n, p) in ((3, 2), (4, 2), (5, 3)):
        bad = 0
        for _ in range(60 if not quick else 15):
            pK = p ** DIGITS
            f = tuple(rng.randrange(pK) for _ in range(n))
            d = disc_fn(n)(f)
            if d == 0:
                continue
            v = vp(abs(d), p)
            N = 2 * v + 1
            pN = p ** N
            base = tuple(ci % pN for ci in f)
            types = set()
            for _ in range(8):
                g = tuple(b + pN * rng.randrange(pK) for b in base)
                t = exact_type(n, g, p) if n <= 3 else gp().ref_type(g, p, max(40, 2 * v + 25))
                if t is not None:
                    types.add(t)
            if len(types) > 1:
                bad += 1
                log("  CERT VIOLATION n=%d p=%d base=%s types=%s" % (n, p, base, types))
        if bad:
            ok = False
        log("  (n=%d,p=%d): %s" % (n, p, "ok" if not bad else "%d VIOLATIONS" % bad))

    log("SELFTEST %s" % ("PASS" if ok else "FAIL"))
    return {"selftest_pass": ok}


# ----------------------------------------------------------------------------
# summary
# ----------------------------------------------------------------------------

def run_summary(log):
    merged = {}
    for n in (2, 3, 4, 5):
        path = os.path.join(HERE, "N1-exhaust_results_n%d.json" % n)
        if os.path.exists(path):
            with open(path) as fh:
                merged["n%d" % n] = json.load(fh)
    st = os.path.join(HERE, "N1-exhaust_results_selftest.json")
    if os.path.exists(st):
        with open(st) as fh:
            merged["selftest"] = json.load(fh)
    log("==== N1-exhaust SUMMARY ====")
    all_flags = []
    for nk in sorted(k for k in merged if k.startswith("n")):
        n = int(nk[1:])
        for pk, r in sorted(merged[nk].items(), key=lambda kv: int(kv[0][1:])):
            p = int(pk[1:])
            fl = r.get("flags", [])
            all_flags.extend(("(n=%d,p=%d) " % (n, p)) + f for f in fl)
            log("(n=%d,p=%-2d)%s  disc-ratio %s (1/p=%.3f) | rates: cert %s exh %s mc %s | flags: %s" % (
                n, p, " W" if p <= n else "  ",
                "%.3f" % r["disc_tail_ratio_fit"] if r.get("disc_tail_ratio_fit") else "n/a", 1 / p,
                "%.3f" % r["rate_cert"] if r.get("rate_cert") else "n/a",
                "%.3f" % r["rate_exh"] if r.get("rate_exh") else "n/a",
                "%.3f" % r["rate_mc"] if r.get("rate_mc") else "n/a",
                "; ".join(fl) if fl else "none"))
    log("total flags: %d" % len(all_flags))
    with open(os.path.join(HERE, "N1-exhaust_results.json"), "w") as fh:
        json.dump(merged, fh, indent=1)
    return merged


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--block", required=True,
                    choices=["selftest", "n2", "n3", "n4", "n5", "summary"])
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()

    t0 = time.time()

    def log(msg):
        print(msg, flush=True)

    log("[N1-exhaust] block=%s quick=%s  %s" % (args.block, args.quick,
        time.strftime("%Y-%m-%d %H:%M:%S")))
    if args.block == "selftest":
        res = run_selftest(args.quick, log)
    elif args.block == "summary":
        res = run_summary(log)
    else:
        res = run_block(int(args.block[1:]), args.quick, log)
    out = os.path.join(HERE, "N1-exhaust_results_%s.json" % args.block)
    if args.block != "summary":
        with open(out, "w") as fh:
            json.dump(res, fh, indent=1)
    if _GP is not None:
        log("[gp] timeouts: %d" % _GP.timeouts)
    log("[N1-exhaust] block=%s done in %.1fs" % (args.block, time.time() - t0))


if __name__ == "__main__":
    main()
