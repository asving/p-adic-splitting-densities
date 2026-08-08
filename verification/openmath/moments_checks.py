"""MOMENTS battery — the FULL DISTRIBUTION of the root-count variable X_n:
the probability-generating-function (PGF) recursion, the moment-stabilization
theorem M_k(n) = M_k(2k) for n >= 2k, the sum rule, and the limiting law.

Unit: MOMENTS 2026-08-08 (Asvin's follow-up to BCFGTIE: "how much access to the
distribution of the number-of-roots random variable do we have?").
Note: lean/notes/openmath/MOMENTS_2026-08-08.md (preregistered predictions in S9 there).

SUPPLIERS (pinned as-of HEAD 70645d9):
  BCFGTIE_2026-08-08.md  Lemma A (level-0 telescope), Lemma B (deep/shallow split),
                         Lemma C (the deep-count law P_m(j)), KEY IDENTITY, E_n=q/(q+1)
  results/bcfg_distribution_final.json   md5 63cb388f78f4a54f3495cb659c43306a
                         (BCFG = arXiv:2101.09590 per verification/README.md;
                          citation grade OWED-EXTERNAL beyond the committed rows)
  results/bcfg_n7.json                   the committed n=7 rows
  reconcile_om_bcfg.py                   the standing OM-vs-BCFG reconciliation (n<=6)

THE OBJECT.  X_n = #{roots in O of a random degree-n member} = #(1,1)-factors.
  monic model:      f = x^n + a_{n-1}x^{n-1} + ... + a_0, coefficients Haar on O.
  projective model: uniform effective divisor of degree n on P^1 (b_n = |P^n(F_q)| of them).
  F_n(t) := E[t^{X_n}]   (monic)        F^p_n(t) := E[t^{X_n}]  (projective)
  phi_m(t) := E[t^{Y_m}], Y_m = root count of a size-m cluster (all m roots at one
              rational residue point).   Psi(v,t) := (1-v) * sum_m phi_m(t) v^m.

THE RECURSION UNDER TEST (derived in the note, S2-S4):
  (PGF-CLU)   phi_m(t) = sum_{j=0}^{m} P_m(j) F_j(t)          [P_m(j) = BCFGTIE Lemma C]
  (PGF-MON)   sum_n F_n(t) u^n      = Psi(u/q, t)^q     / (1-u)
  (PGF-PRJ)   sum_n b_n F^p_n(t)u^n = Psi(u,   t)^{q+1} / ((1-u)(1-qu))

STRUCTURE (checks C1..C9 + teeth T1..T5):
  C1  P_m(j): closed form vs INDEPENDENT exact finite enumeration of the Newton-polygon
      support line (m<=6 symbolic, m=7 at q in {2,3,5}); sum_j P_m(j)=1; P_m(m-1)=0;
      KEY IDENTITY q P_m(0) - P_m(1) = q-1.
  C2  (GEOM-J)  c(j,mu) = q^j c(0,mu) for all 0<=j<mu (mu<=10, symbolic) and
      (MASS)    sum_{j<mu} c(j,mu) = d_mu - d_{mu+1},  d_m := q^{-m(m-1)/2}.
  C3  The PGF recursion is a probability law: F_n(1)=1, all coefficients in [0,1],
      P(X_n = n-1) = 0 (n>=2, the "one root short" impossibility), F_1 = t;
      F_2 = (q t^2 + q + 2)/(2(q+1)); reproduces E_n = q/(q+1) and E^p_n = 1 (BCFGTIE).
  C4  (INF=GEO)  Psi(1,t) = Psi(1/q,t): the geometric-multiplicity mixture of cluster
      laws equals the infinite-cluster law.  Weight form: G(j) = P_inf(j), telescoping
      identity checked symbolically for j<=8; consequence D_k(1) = D_k(1/q).
  C5  STABILIZATION: M_k(n) := E[(X_n)_k] equals M_k(2k) for all 2k <= n <= NMAX and
      differs at n = 2k-1 (n_0(k) = 2k exactly), k=1..4.  Projective: M^p_k(n) constant
      for n >= 2k, and equal to the k-th factorial moment of the limit.
  C6  SUM RULE: sum_{i=0}^{n} q^i M_k(i) = b_n M_k(n) for all n >= 2k.
  C7  BCFG TIE: per-r rows dist(n,r) for n=2..7 (projective), and the moment rows
      fac(n,d), binom(n,d), raw(n,k), n=2..7.  Rows fac(7,d>=2)/binom(7,*)/raw(7,k>=2)
      and the per-r n=7 rows are consumed by NO standing check (blind targets).
  C8  Psi_k(v) is a polynomial of degree <= 2k (the mechanism behind C5), k<=4.
  C9  Limiting law: F_inf = g^q, F^p_inf = g^{q+1} with g = Psi(1/q,t); M_k(inf) =
      M_k(2k); P(X_n=r) -> P(X_inf=r) with the explicit q^{-N} tail bound.
  T1  TOOTH mis-level self-similarity: phi_m = sum_j P_m(j) phi_j (cluster re-entry
      instead of full-monic re-entry).  Normalization PASSES, the mean must FAIL.
  T2  TOOTH point-count off by one: monic master with q+1 points.  Normalization
      PASSES, the mean must FAIL.
  T3  TOOTH min-argmin deep count (BCFGTIE's T1): sum_j P~_m(j)=1 PASSES, the KEY
      IDENTITY and the mean must FAIL.
  T4  TOOTH mean-preserving output transfer on the projective law (+d at r=0, -2d at
      r=1, +d at r=2): normalization and E^p_n=1 PASS, fac2 and the BCFG rows must FAIL.
  T5  TOOTH comonotone points: Psi(u,t^{q+1}) in place of Psi(u,t)^{q+1} (the q+1
      rational points perfectly correlated instead of independent).  Normalization AND
      the mean PASS at every n, fac2 and the BCFG rows must FAIL.  T5 is the tooth that
      shows the second moment tests the level-0 independence step, which the first
      moment cannot see.

Run:  .venv-openmath/bin/python moments_checks.py            (full battery, exit 0 iff green)
      .venv-openmath/bin/python moments_checks.py --prereg   (predictions only; DOES NOT
                                                              open any BCFG cache file)
Artifacts: moments_results.json (+ moments_prereg.json in --prereg mode) + stdout log.
"""
import sys, os, time, json
from fractions import Fraction
from itertools import product as iproduct

HERE = os.path.dirname(os.path.abspath(__file__))
VERIF = os.path.dirname(HERE)
sys.path.insert(0, VERIF)

import sympy as sp

PREREG = ('--prereg' in sys.argv)
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
    return ok

TEETH = {}
def tooth(name, bites, detail=""):
    TEETH[name] = bool(bites)
    log(f"  TOOTH {name}: {'BITES' if bites else '*** DOES NOT BITE ***'} {detail}")

qs, t = sp.symbols('q t')

def SIMP(e):
    """Fast canonical form for rational functions of q: SIMP(x) == 0 iff x == 0.
    cancel() is a canonical-form routine on Q(q), so the == 0 test is exact; the
    simplify() fallback only ever runs on a nonzero canonical form."""
    e = sp.sympify(e)
    if e == 0:
        return sp.Integer(0)
    z = sp.cancel(sp.together(e))
    if z == 0:
        return sp.Integer(0)
    return z

# =====================================================================================
# 0. Engine: the PGF recursion at a given q (symbolic or exact rational)
# =====================================================================================

class Eng:
    """Builds F_n (monic), phi_m (cluster), F^p_n (projective) to degree N."""

    def __init__(self, qv, N, phi_mode='monic', point_shift=0, argmin='max'):
        self.q = qv
        self.N = N
        self.sym = bool(getattr(qv, 'free_symbols', set()))
        self.dom = 'QQ(q)' if self.sym else 'QQ'
        self.phi_mode = phi_mode          # 'monic' (true) | 'cluster' (tooth T1)
        self.point_shift = point_shift    # 0 (true) | 1 (tooth T2)
        self.argmin = argmin              # 'max' (true) | 'min' (tooth T3)
        self.Z = sp.Poly(0, t, domain=self.dom)
        self.ONE = sp.Poly(1, t, domain=self.dom)
        self._pm = {}
        self.build()

    # ---- small helpers -------------------------------------------------------------
    def P_(self, e):
        return sp.Poly(sp.sympify(e), t, domain=self.dom)

    def red(self, P):
        """cancel each t-coefficient (keeps the rational functions small)"""
        if not self.sym:
            return P
        return self.P_(sp.cancel(sp.together(P.as_expr())))

    def d(self, m):
        return self.q ** sp.Rational(-m * (m - 1), 2)

    def c(self, j, mu):
        """c(j,mu) = P(min_i t_i = mu with (max-)argmin at j), from the raw product form."""
        q = self.q
        ge = lambda s: q ** (-s) if s > 0 else sp.Integer(1)      # P(u >= s), u >= 0 geometric
        eq = lambda s: (1 - sp.Rational(1, 1) / q) * q ** (-s)     # P(u = s)
        if not (0 <= j < mu):
            return sp.Integer(0)
        term = eq(mu - j - 1)
        if self.argmin == 'max':
            for k in range(0, j):
                term *= ge(mu - k - 1)          # ties allowed left of the argmax
            for k in range(j + 1, mu):
                term *= ge(mu - k)              # strict right of it
        else:                                   # TOOTH T3: min-argmin
            for k in range(0, j):
                term *= ge(mu - k)
            for k in range(j + 1, mu):
                term *= ge(mu - k - 1)
        return sp.cancel(term)

    def PM(self, m):
        """P_m(j), j=0..m: the deep-count law of a size-m cluster (BCFGTIE Lemma C)."""
        if m in self._pm:
            return self._pm[m]
        if m == 0:
            out = {0: sp.Integer(1)}
        elif m == 1:
            out = {1: sp.Integer(1)}
        else:
            out = {m: self.d(m)}
            for j in range(0, m):
                s = sp.Integer(0)
                for mu in range(j + 1, m):
                    s += self.c(j, mu)
                out[j] = sp.cancel(s)
        self._pm[m] = out
        return out

    # ---- truncated v-series with t-polynomial coefficients -------------------------
    def tmul(self, A, B):
        N = self.N
        C = [self.Z] * (N + 1)
        for i, a in enumerate(A):
            if i > N or a.is_zero:
                continue
            for j, b in enumerate(B):
                if i + j > N:
                    break
                if b.is_zero:
                    continue
                C[i + j] = C[i + j] + a * b
        return C

    def tpow(self, A, e):
        """A^e for a series A with A[0] = 1 and a possibly symbolic exponent e."""
        N = self.N
        X = [self.Z] + list(A[1:N + 1]) + [self.Z] * (N - len(A[1:N + 1]))
        X = X[:N + 1]
        L = [self.Z] * (N + 1)
        Xp = [self.ONE] + [self.Z] * N
        for k in range(1, N + 1):
            Xp = self.tmul(Xp, X)
            ck = sp.Rational((-1) ** (k - 1), k)
            for i in range(N + 1):
                L[i] = L[i] + Xp[i] * ck
        Y = [self.P_(e) * L[i] for i in range(N + 1)]
        Ex = [self.ONE] + [self.Z] * N
        Yp = [self.ONE] + [self.Z] * N
        for k in range(1, N + 1):
            Yp = self.tmul(Yp, Y)
            ck = sp.Rational(1, int(sp.factorial(k)))
            for i in range(N + 1):
                Ex[i] = Ex[i] + Yp[i] * ck
        return Ex

    # ---- the build ------------------------------------------------------------------
    def build(self):
        q, N = self.q, self.N
        npts = q + self.point_shift            # monic model: q rational points on A^1
        self.F = {0: self.ONE, 1: self.P_(t)}
        self.phi = {0: self.ONE, 1: self.P_(t)}
        for n in range(2, N + 1):
            P = self.PM(n)
            base = self.phi if self.phi_mode == 'cluster' else self.F
            known = self.Z
            for j in P:
                if j < n:
                    known = known + self.P_(P[j]) * base[j]
            # phi_n = known + P[n] * (F_n or phi_n);   F_n = F_{n-1} + q^{-n}[v^n]Psi^q
            Phi = [self.phi[m] for m in range(0, n)] + [known]
            Psi = [Phi[0]] + [Phi[m] - Phi[m - 1] for m in range(1, n + 1)]
            Psi = Psi + [self.Z] * (N - n)
            A = self.tpow(Psi[:N + 1], npts)
            const = A[n] * self.P_(q ** (-n))
            slope = q ** (-n) * npts * P[n]     # the only linear-in-unknown route to v^n
            if self.phi_mode == 'cluster':
                # phi_n = known + P[n] phi_n  ->  phi_n known first, then F_n
                self.phi[n] = self.red(known * self.P_(1 / (1 - P[n])))
                Phi = [self.phi[m] for m in range(0, n + 1)]
                Psi = [Phi[0]] + [Phi[m] - Phi[m - 1] for m in range(1, n + 1)]
                Psi = Psi + [self.Z] * (N - n)
                A = self.tpow(Psi[:N + 1], npts)
                self.F[n] = self.red(self.F[n - 1] + A[n] * self.P_(q ** (-n)))
            else:
                self.F[n] = self.red((self.F[n - 1] + const) * self.P_(1 / (1 - slope)))
                self.phi[n] = self.red(known + self.P_(P[n]) * self.F[n])
        # the true Psi series (from the finished phi's) and its powers
        Phi = [self.phi[m] for m in range(0, N + 1)]
        self.Psi = [Phi[0]] + [self.red(Phi[m] - Phi[m - 1]) for m in range(1, N + 1)]
        self.A = self.tpow(self.Psi, npts)                 # Psi^q      (monic numerator)
        self.Ap = self.tpow(self.Psi, q + 1)               # Psi^{q+1}  (projective)
        # projective:  b_n F^p_n = sum_{i<=n} [v^i](Psi^{q+1}) b_{n-i}
        self.b = [sp.cancel((q ** (k + 1) - 1) / (q - 1)) for k in range(0, N + 1)]
        self.Fp = {}
        for n in range(0, N + 1):
            acc = self.Z
            for i in range(0, n + 1):
                acc = acc + self.Ap[i] * self.P_(self.b[n - i])
            self.Fp[n] = self.red(acc * self.P_(1 / self.b[n]))

    # ---- readouts -------------------------------------------------------------------
    def coeffs(self, P, n):
        cs = list(reversed(P.all_coeffs()))          # index = t-degree
        cs = [sp.cancel(sp.sympify(c)) for c in cs]
        cs = cs + [sp.Integer(0)] * (n + 1 - len(cs))
        return cs[:n + 1]

    def fac_mom(self, P, n, k):
        """E[(X)_k] from the coefficient list of a PGF polynomial."""
        cs = self.coeffs(P, n)
        acc = sp.Integer(0)
        for r, c in enumerate(cs):
            f = sp.Integer(1)
            for i in range(k):
                f *= (r - i)
            acc += c * f
        return sp.cancel(acc)

    def dt_series(self, S, k):
        """k-th t-derivative at t=1 of a v-series of t-polys -> list of v-coefficients."""
        out = []
        for c in S:
            e = c.as_expr()
            for _ in range(k):
                e = sp.diff(e, t)
            out.append(sp.cancel(e.subs(t, 1)))
        return out


# =====================================================================================
# 1. C1/C2 — the deep-count law and its two exponent identities
# =====================================================================================
log("=" * 78)
log("C1/C2  the deep-count law P_m(j), (GEOM-J) and (MASS)")
log("=" * 78)

E = Eng(qs, 2)   # cheap instance just for P_m / c(j,mu)

def brute_PM(qv, m):
    """INDEPENDENT exact computation by forward dynamic programming over the support
    line -- uses NO part of the Lemma C closed form.  u_i := v(a_i)-1 >= 0 iid with
    P(u >= s) = q^{-s}; t_i := i+u_i+1 (i<m), t_m := m; the deep count is
    j = max argmin_i t_i (i ranging over 0..m).  For each i, u_i is enumerated exactly
    on 0..m-i-1 (so t_i in i+1..m) plus one lumped state u_i >= m-i (then t_i > m and
    can never be the argmin, because t_m = m).  DP state = (current min, its max index).
    INF is encoded as m+1."""
    INF = m + 1
    st = {(INF, -1): sp.Integer(1)}
    for i in range(0, m):
        nxt = {}
        cap = m - i
        opts = [(i + u + 1, (1 - sp.Rational(1, 1) / qv) * qv ** (-u)) for u in range(0, cap)]
        opts.append((INF, qv ** (-cap)))
        for (mn, arg), w in st.items():
            for (ti, wi) in opts:
                if ti < mn:
                    k = (ti, i)
                elif ti == mn:
                    k = (ti, i)          # ties resolve to the LARGER index
                else:
                    k = (mn, arg)
                nxt[k] = nxt.get(k, sp.Integer(0)) + w * wi
        st = {k: sp.cancel(v) for k, v in nxt.items()}
    out = {j: sp.Integer(0) for j in range(0, m + 1)}
    for (mn, arg), w in st.items():
        j = m if mn >= m else arg        # t_m = m closes the line
        out[j] = out[j] + w
    return {j: sp.cancel(v) for j, v in out.items()}

ok_bf = True
for m in range(2, 7):
    A = E.PM(m)
    B = brute_PM(qs, m)
    for j in range(0, m + 1):
        if SIMP(A.get(j, 0) - B.get(j, 0)) != 0:
            ok_bf = False
            log(f"    mismatch m={m} j={j}: closed={A.get(j,0)} brute={B.get(j,0)}")
check("C1a  P_m(j) closed form == independent exact enumeration, m=2..6 SYMBOLIC", ok_bf)

ok7 = True
for qv in [sp.Integer(2), sp.Integer(3), sp.Integer(5)]:
    Eq = Eng(qv, 2)
    A = Eq.PM(7)
    B = brute_PM(qv, 7)
    for j in range(0, 8):
        if SIMP(A.get(j, 0) - B.get(j, 0)) != 0:
            ok7 = False
check("C1b  P_7(j) closed form == exact enumeration at q in {2,3,5}", ok7)

ok_sum = all(SIMP(sum(E.PM(m).values()) - 1) == 0 for m in range(2, 11))
check("C1c  sum_j P_m(j) = 1, m=2..10 symbolic", ok_sum)
ok_mm1 = all(SIMP(E.PM(m)[m - 1]) == 0 for m in range(2, 11))
check("C1d  P_m(m-1) = 0, m=2..10 symbolic", ok_mm1)
ok_key = all(SIMP(qs * E.PM(m)[0] - E.PM(m)[1] - (qs - 1)) == 0 for m in range(2, 11))
check("C1e  KEY IDENTITY q P_m(0) - P_m(1) = q-1, m=2..10 symbolic", ok_key)

ok_gj = True
for mu in range(1, 11):
    for j in range(0, mu):
        if SIMP(E.c(j, mu) - qs ** j * E.c(0, mu)) != 0:
            ok_gj = False
check("C2a  (GEOM-J)  c(j,mu) = q^j c(0,mu), all 0<=j<mu<=10 symbolic", ok_gj)

ok_mass = True
for mu in range(1, 11):
    S = sum(E.c(j, mu) for j in range(0, mu))
    if SIMP(S - (E.d(mu) - E.d(mu + 1))) != 0:
        ok_mass = False
check("C2b  (MASS)  sum_{j<mu} c(j,mu) = d_mu - d_{mu+1}, mu<=10 symbolic", ok_mass)

# (INF=GEO) weight identity: G(j) = P_inf(j)  <=>  the telescope
#   q^j sum_{mu>j} c(0,mu)(1 - q^{-mu-1}) = (1-1/q) q^{-j} d_j
ok_tele = True
for j in range(0, 9):
    J = j + 14
    lhs = qs ** j * sum(E.c(0, mu) * (1 - qs ** (-mu - 1)) for mu in range(j + 1, J + 1))
    tail = qs ** j * (1 - sp.Rational(1, 1) / qs) * qs ** (1 - sp.Rational((J + 1) * (J + 2), 2))
    rhs = (1 - sp.Rational(1, 1) / qs) * qs ** (-j) * E.d(j)
    if SIMP(lhs + tail - rhs) != 0:
        ok_tele = False
        log(f"    telescope fails at j={j}: {SIMP(lhs + tail - rhs)}")
check("C4a  (INF=GEO) weight telescope  G(j) = P_inf(j), j=0..8 symbolic (exact tail)", ok_tele)

# =====================================================================================
# 2. C3/C5/C6/C8 — build the PGFs and read the moments off
# =====================================================================================
NSYM = int(os.environ.get('MOM_NSYM', '7'))
NNUM = int(os.environ.get('MOM_NNUM', '10'))
log("=" * 78)
log(f"C3  building the PGF recursion: symbolic q to n={NSYM}, exact q to n={NNUM}")
log("=" * 78)

ES = Eng(qs, NSYM)
log(f"  symbolic build done (n<={NSYM})")

ok_norm = all(SIMP(ES.F[n].as_expr().subs(t, 1) - 1) == 0 for n in range(0, NSYM + 1))
ok_normp = all(SIMP(ES.Fp[n].as_expr().subs(t, 1) - 1) == 0 for n in range(0, NSYM + 1))
check(f"C3a  F_n(1) = 1 and F^p_n(1) = 1, n<={NSYM} symbolic", ok_norm and ok_normp)

ok_F2 = SIMP(ES.F[2].as_expr() - (qs * t ** 2 + qs + 2) / (2 * (qs + 1))) == 0
check("C3b  F_2(t) = (q t^2 + q + 2)/(2(q+1))  [hand-derived, preregistered]", ok_F2)

ok_gap = True
for n in range(2, NSYM + 1):
    if SIMP(ES.coeffs(ES.F[n], n)[n - 1]) != 0:
        ok_gap = False
    if SIMP(ES.coeffs(ES.Fp[n], n)[n - 1]) != 0:
        ok_gap = False
check(f"C3c  P(X_n = n-1) = 0 (monic and projective), n=2..{NSYM}", ok_gap)

ok_pos = True
for qv in [2, 3, 4, 5, 7, 8, 9, 11, 13]:
    for n in range(1, NSYM + 1):
        for P in (ES.F[n], ES.Fp[n]):
            cs = [SIMP(c.subs(qs, qv)) for c in ES.coeffs(P, n)]
            if any(c < 0 or c > 1 for c in cs) or SIMP(sum(cs) - 1) != 0:
                ok_pos = False
check(f"C3d  all coefficients in [0,1] and sum to 1 at 9 prime powers, n<={NSYM}", ok_pos)

E_mon = {n: ES.fac_mom(ES.F[n], n, 1) for n in range(1, NSYM + 1)}
E_prj = {n: ES.fac_mom(ES.Fp[n], n, 1) for n in range(1, NSYM + 1)}
ok_mean = all(SIMP(E_mon[n] - qs / (qs + 1)) == 0 for n in range(2, NSYM + 1))
ok_meanp = all(SIMP(E_prj[n] - 1) == 0 for n in range(1, NSYM + 1))
check(f"C3e  BCFGTIE recovered: E_n = q/(q+1) (n=2..{NSYM}) and E^p_n = 1 (n=1..{NSYM})",
      ok_mean and ok_meanp)

eps = {m: ES.fac_mom(ES.phi[m], m, 1) for m in range(1, NSYM + 1)}
ok_eps = all(SIMP(eps[m] - 1 / (qs + 1)) == 0 for m in range(2, NSYM + 1))
check(f"C3f  BCFGTIE recovered: eps_m = 1/(q+1), m=2..{NSYM} (cluster mean)", ok_eps)

# ---- Psi_k polynomiality (C8) and D_k(1) = D_k(1/q) (C4b) --------------------------
log("=" * 78)
log("C8/C4b  Psi_k polynomial of degree <= 2k;  D_k(1) = D_k(1/q)")
log("=" * 78)
KMAX = 4
Psi_k = {k: ES.dt_series(ES.Psi, k) for k in range(1, KMAX + 1)}
D_k = {k: ES.dt_series(ES.A, k) for k in range(1, KMAX + 1)}
Dp_k = {k: ES.dt_series(ES.Ap, k) for k in range(1, KMAX + 1)}

ok_poly = True
deg_obs = {}
for k in range(1, KMAX + 1):
    nz = [i for i, c in enumerate(Psi_k[k]) if SIMP(c) != 0]
    deg_obs[k] = max(nz) if nz else -1
    if 2 * k <= NSYM and deg_obs[k] > 2 * k:
        ok_poly = False
check(f"C8a  deg_v Psi_k <= 2k for every k with 2k <= {NSYM} "
      f"(observed degrees {deg_obs})", ok_poly)

ok_D = True
for k in range(1, KMAX + 1):
    if 2 * k > NSYM:
        continue
    for S in (D_k[k], Dp_k[k]):
        at1 = sp.cancel(sum(S[:2 * k + 1]))
        atq = sp.cancel(sum(S[i] * qs ** (-i) for i in range(0, 2 * k + 1)))
        if SIMP(at1 - atq) != 0:
            ok_D = False
check(f"C4b  D_k(1) = D_k(1/q) and D^p_k(1) = D^p_k(1/q) for 2k <= {NSYM}", ok_D)

# ---- moments, stabilization, sum rule ---------------------------------------------
log("=" * 78)
log("C5/C6  factorial moments, stabilization threshold, sum rule")
log("=" * 78)
M = {}
Mp = {}
for k in range(1, KMAX + 1):
    for n in range(0, NSYM + 1):
        M[(k, n)] = ES.fac_mom(ES.F[n], n, k) if n >= 1 else sp.Integer(0)
        Mp[(k, n)] = ES.fac_mom(ES.Fp[n], n, k) if n >= 1 else sp.Integer(0)
    log(f"  k={k}: M_k(n) n=0..{NSYM} computed")

n0 = {}
ok_stab = True
for k in range(1, KMAX + 1):
    if 2 * k + 1 > NSYM:
        continue
    same = all(SIMP(M[(k, n)] - M[(k, 2 * k)]) == 0 for n in range(2 * k, NSYM + 1))
    moved = SIMP(M[(k, 2 * k - 1)] - M[(k, 2 * k)]) != 0
    n0[k] = 2 * k if (same and moved) else None
    if not (same and moved):
        ok_stab = False
check(f"C5a  MONIC stabilization at n_0(k) = 2k exactly, for 2k < {NSYM} "
      f"(n_0 = {n0})", ok_stab)

ok_stabp = True
n0p = {}
for k in range(1, KMAX + 1):
    if 2 * k + 1 > NSYM:
        continue
    same = all(SIMP(Mp[(k, n)] - Mp[(k, 2 * k)]) == 0 for n in range(2 * k, NSYM + 1))
    n0p[k] = 2 * k if same else None
    if not same:
        ok_stabp = False
check(f"C5b  PROJECTIVE M^p_k(n) constant for n >= 2k (n_0^p <= 2k = {n0p})", ok_stabp)

ok_sr = True
for k in range(1, KMAX + 1):
    for n in range(2 * k, NSYM + 1):
        lhs = sp.cancel(sum(qs ** i * M[(k, i)] for i in range(0, n + 1)))
        rhs = sp.cancel(ES.b[n] * M[(k, n)])
        if SIMP(lhs - rhs) != 0:
            ok_sr = False
            log(f"    sum rule fails k={k} n={n}")
check(f"C6a  SUM RULE  sum_{{i<=n}} q^i M_k(i) = b_n M_k(n) for all n>=2k, k<={KMAX}", ok_sr)

# the sum rule solves for the stabilized value from strictly lower degrees
ok_solve = True
for k in range(1, KMAX + 1):
    if 2 * k > NSYM:
        continue
    pred = sp.cancel((qs - 1) / (qs ** (2 * k) - 1) * sum(qs ** i * M[(k, i)]
                                                          for i in range(k, 2 * k)))
    if SIMP(pred - M[(k, 2 * k)]) != 0:
        ok_solve = False
check(f"C6b  M_k(2k) = (q-1)/(q^{{2k}}-1) * sum_{{i=k}}^{{2k-1}} q^i M_k(i) "
      f"(the closed-form solve), k<={KMAX}", ok_solve)

# ---- exact-q extension to higher n (stabilization beyond the symbolic reach) -------
log("=" * 78)
log(f"C5c  exact-q extension to n={NNUM} (q in 2,3,5): stabilization for k<=4")
log("=" * 78)
NUMQ = [sp.Integer(2), sp.Integer(3), sp.Integer(5)]
ok_ext = True
ext_rec = {}
for qv in NUMQ:
    Eq = Eng(qv, NNUM)
    for k in range(1, KMAX + 1):
        vals = [Eq.fac_mom(Eq.F[n], n, k) for n in range(0, NNUM + 1)]
        valsp = [Eq.fac_mom(Eq.Fp[n], n, k) for n in range(0, NNUM + 1)]
        ext_rec[f"q={qv},k={k}"] = [str(v) for v in vals]
        ext_rec[f"proj q={qv},k={k}"] = [str(v) for v in valsp]
        if 2 * k <= NNUM:
            if not all(v == vals[2 * k] for v in vals[2 * k:]):
                ok_ext = False
                log(f"    monic NOT stable q={qv} k={k}: {vals}")
            if not all(v == valsp[2 * k] for v in valsp[2 * k:]):
                ok_ext = False
                log(f"    proj NOT stable q={qv} k={k}: {valsp}")
            if vals[2 * k - 1] == vals[2 * k]:
                ok_ext = False
                log(f"    n_0 < 2k at q={qv} k={k}")
    log(f"  q={qv} done to n={NNUM}")
check(f"C5c  M_k(n)=M_k(2k) for 2k<=n<={NNUM} and M_k(2k-1) != M_k(2k), k<=4, q in 2,3,5",
      ok_ext)

# =====================================================================================
# 3. C9 — the limiting law
# =====================================================================================
log("=" * 78)
log("C9  the limiting law F_inf = g^q, F^p_inf = g^{q+1},  g = Psi(1/q,t)")
log("=" * 78)
# g truncated at m <= NSYM; the omitted mass is exactly q^{-NSYM} (a PGF-coefficient bound)
g_trunc = sp.Integer(0)
for m in range(0, NSYM + 1):
    g_trunc += (1 - sp.Rational(1, 1) / qs) * qs ** (-m) * ES.phi[m].as_expr()
ok_g1 = SIMP(g_trunc.subs(t, 1) - (1 - qs ** (-NSYM - 1))) == 0
check(f"C9a  truncated g(1) = 1 - q^{{-{NSYM+1}}} (the exact omitted mass)", ok_g1)

ok_lim = True
for k in range(1, KMAX + 1):
    if 2 * k > NSYM:
        continue
    # k-th factorial moment of the limit = D_k(1/q) (monic) resp. D^p_k(1/q)
    lim_mon = sp.cancel(sum(D_k[k][i] * qs ** (-i) for i in range(0, 2 * k + 1)))
    lim_prj = sp.cancel(sum(Dp_k[k][i] * qs ** (-i) for i in range(0, 2 * k + 1)))
    if SIMP(lim_mon - M[(k, 2 * k)]) != 0:
        ok_lim = False
    if SIMP(lim_prj - Mp[(k, 2 * k)]) != 0:
        ok_lim = False
check(f"C9b  M_k(inf) = M_k(2k) and M^p_k(inf) = M^p_k(2k), k<={KMAX} symbolic", ok_lim)

# =====================================================================================
# 4. TEETH
# =====================================================================================
log("=" * 78)
log("TEETH T1..T5")
log("=" * 78)
NT = 5
ETrue = Eng(qs, NT)
true_mean = [sp.cancel(ETrue.fac_mom(ETrue.F[n], n, 1)) for n in range(0, NT + 1)]
true_meanp = [sp.cancel(ETrue.fac_mom(ETrue.Fp[n], n, 1)) for n in range(0, NT + 1)]
true_fac2p = [sp.cancel(ETrue.fac_mom(ETrue.Fp[n], n, 2)) for n in range(0, NT + 1)]

# T1: cluster re-entry instead of full-monic re-entry
T1 = Eng(qs, NT, phi_mode='cluster')
t1_norm = all(SIMP(T1.F[n].as_expr().subs(t, 1) - 1) == 0 for n in range(0, NT + 1))
t1_mean_bad = any(SIMP(T1.fac_mom(T1.F[n], n, 1) - qs / (qs + 1)) != 0
                  for n in range(2, NT + 1))
tooth("T1 mis-level self-similarity (phi_m = sum_j P_m(j) phi_j)",
      t1_norm and t1_mean_bad,
      f"[normalization passes={t1_norm}; mean E_2={sp.cancel(T1.fac_mom(T1.F[2],2,1))} "
      f"vs q/(q+1)]")

# T2: q+1 points in the monic master
T2 = Eng(qs, NT, point_shift=1)
t2_norm = all(SIMP(T2.F[n].as_expr().subs(t, 1) - 1) == 0 for n in range(0, NT + 1))
t2_mean_bad = any(SIMP(T2.fac_mom(T2.F[n], n, 1) - qs / (qs + 1)) != 0
                  for n in range(2, NT + 1))
tooth("T2 point-count off by one (q+1 points in the monic master)",
      t2_norm and t2_mean_bad, f"[normalization passes={t2_norm}]")

# T3: min-argmin deep count
T3 = Eng(qs, NT, argmin='min')
t3_sum = all(SIMP(sum(T3.PM(m).values()) - 1) == 0 for m in range(2, 6))
t3_key_bad = any(SIMP(qs * T3.PM(m)[0] - T3.PM(m)[1] - (qs - 1)) != 0
                 for m in range(3, 6))
t3_mean_bad = any(SIMP(T3.fac_mom(T3.F[n], n, 1) - qs / (qs + 1)) != 0
                  for n in range(2, NT + 1))
tooth("T3 min-argmin deep count", t3_sum and t3_key_bad and t3_mean_bad,
      f"[sum_j P~=1 passes={t3_sum}; KEY fails={t3_key_bad}; mean fails={t3_mean_bad}]")

# T4: mean-preserving output transfer on the projective law
delta = qs ** (-7)
t4_ok_norm, t4_ok_mean, t4_bad_fac2 = True, True, False
for n in range(2, NT + 1):
    cs = ETrue.coeffs(ETrue.Fp[n], n)
    cs[0] = cs[0] + delta
    cs[1] = cs[1] - 2 * delta
    cs[2] = cs[2] + delta
    if SIMP(sum(cs) - 1) != 0:
        t4_ok_norm = False
    m1 = sp.cancel(sum(r * c for r, c in enumerate(cs)))
    if SIMP(m1 - 1) != 0:
        t4_ok_mean = False
    m2 = sp.cancel(sum(r * (r - 1) * c for r, c in enumerate(cs)))
    if SIMP(m2 - true_fac2p[n]) != 0:
        t4_bad_fac2 = True
tooth("T4 mean-preserving output transfer (+d,-2d,+d at r=0,1,2)",
      t4_ok_norm and t4_ok_mean and t4_bad_fac2,
      f"[Sigma=1 passes={t4_ok_norm}; E^p=1 passes={t4_ok_mean}; fac2 moves={t4_bad_fac2}]")

# T5: comonotone points -- Psi(u,t^{q+1}) instead of Psi(u,t)^{q+1}
# Substituting t -> t^{q+1} in a PGF keeps normalization and multiplies every factorial
# moment of order 1 by (q+1); the second factorial moment changes.
t5_norm, t5_mean, t5_fac2_bad = True, True, False
for n in range(1, NT + 1):
    # b_n F~^p_n = sum_i [v^i]Psi(v,t^{q+1}) b_{n-i}; read the moments through
    # d/dt of Psi(u,t^{q+1}) at t=1 = (q+1) Psi_1(u), and the 2nd derivative
    # = (q+1)q Psi_1(u) + (q+1)^2 Psi_2(u).
    P1 = ETrue.dt_series(ETrue.Psi, 1)
    P2 = ETrue.dt_series(ETrue.Psi, 2)
    m1 = sp.cancel(sum((qs + 1) * P1[i] * ETrue.b[n - i] for i in range(0, n + 1))
                   / ETrue.b[n])
    d2 = [sp.cancel((qs + 1) * qs * P1[i] + (qs + 1) ** 2 * P2[i]) for i in range(0, n + 1)]
    m2raw = sp.cancel(sum(d2[i] * ETrue.b[n - i] for i in range(0, n + 1)) / ETrue.b[n])
    if SIMP(m1 - 1) != 0:
        t5_mean = False
    if SIMP(m2raw - true_fac2p[n]) != 0:
        t5_fac2_bad = True
tooth("T5 comonotone points (Psi(u,t^{q+1}) for Psi(u,t)^{q+1})",
      t5_mean and t5_fac2_bad,
      f"[E^p_n = 1 still passes at every n={t5_mean}; fac2 moves={t5_fac2_bad}]")

# =====================================================================================
# 5. PREDICTIONS (written before any BCFG cache file is opened)
# =====================================================================================
PRED = {
    "F_n_monic": {str(n): str(sp.cancel(ES.F[n].as_expr())) for n in range(1, NSYM + 1)},
    "F_n_proj": {str(n): str(sp.cancel(ES.Fp[n].as_expr())) for n in range(1, NSYM + 1)},
    "dist_proj": {f"{n},{r}": str(c) for n in range(2, NSYM + 1)
                  for r, c in enumerate(ES.coeffs(ES.Fp[n], n))},
    "dist_monic": {f"{n},{r}": str(c) for n in range(2, NSYM + 1)
                   for r, c in enumerate(ES.coeffs(ES.F[n], n))},
    "fac_proj": {f"{n},{d}": str(sp.cancel(ES.fac_mom(ES.Fp[n], n, d)))
                 for n in range(2, NSYM + 1) for d in range(1, n + 1)},
    "fac_monic": {f"{n},{d}": str(sp.cancel(ES.fac_mom(ES.F[n], n, d)))
                  for n in range(2, NSYM + 1) for d in range(1, n + 1)},
    "raw_proj": {}, "binom_proj": {},
    "M_monic": {f"{k},{n}": str(M[(k, n)]) for k in range(1, KMAX + 1)
                for n in range(0, NSYM + 1)},
    "M_proj": {f"{k},{n}": str(Mp[(k, n)]) for k in range(1, KMAX + 1)
               for n in range(0, NSYM + 1)},
    "n0_monic": {str(k): (None if n0.get(k) is None else int(n0[k])) for k in n0},
    "Psi_k": {str(k): [str(c) for c in Psi_k[k]] for k in Psi_k},
    "ext_exact_q": ext_rec,
}
for n in range(2, NSYM + 1):
    cs = ES.coeffs(ES.Fp[n], n)
    for kk in range(1, 5):
        PRED["raw_proj"][f"{n},{kk}"] = str(sp.cancel(sum(c * sp.Integer(r) ** kk
                                                          for r, c in enumerate(cs))))
    for dd in range(1, n + 1):
        PRED["binom_proj"][f"{n},{dd}"] = str(sp.cancel(
            sum(c * sp.binomial(r, dd) for r, c in enumerate(cs))))

if PREREG:
    json.dump({"predictions": PRED, "log": LOG,
               "note": "PREREG MODE: no BCFG cache file was opened by this process."},
              open(os.path.join(HERE, 'moments_prereg.json'), 'w'), indent=1)
    log("PREREG MODE: predictions written to moments_prereg.json; no cache read. DONE.")
    sys.exit(0 if not FAILS else 1)

# =====================================================================================
# 6. C7 — the BCFG tie (cache opened only past this line)
# =====================================================================================
log("=" * 78)
log("C7  BCFG tie (the committed transcription; citation grade OWED-EXTERNAL)")
log("=" * 78)
B = json.load(open(os.path.join(VERIF, 'results', 'bcfg_distribution_final.json')))
B7 = json.load(open(os.path.join(VERIF, 'results', 'bcfg_n7.json')))

def bget(sec, key):
    if sec in B and key in B[sec]:
        return sp.cancel(sp.sympify(B[sec][key], locals={'q': qs}))
    return None

rows = {"dist": [], "fac": [], "binom": [], "raw": []}
ok_dist = True
for n in range(2, min(NSYM, 7) + 1):
    cs = ES.coeffs(ES.Fp[n], n)
    for r in range(0, n + 1):
        bc = bget('dist', f"{n},{r}")
        if bc is None:
            bc = sp.Integer(0)
        eq = SIMP(cs[r] - bc) == 0
        rows["dist"].append((n, r, bool(eq)))
        if not eq:
            ok_dist = False
            log(f"    dist MISMATCH n={n} r={r}: ours={cs[r]} bcfg={bc}")
check(f"C7a  per-r rows dist(n,r) == our projective F^p_n coefficients, n=2..{min(NSYM,7)}",
      ok_dist)

ok_mom = True
for sec, fn in (("fac", lambda n, d: ES.fac_mom(ES.Fp[n], n, d)),
                ("binom", lambda n, d: sum(c * sp.binomial(r, d)
                                           for r, c in enumerate(ES.coeffs(ES.Fp[n], n)))),
                ("raw", lambda n, d: sum(c * sp.Integer(r) ** d
                                         for r, c in enumerate(ES.coeffs(ES.Fp[n], n))))):
    for n in range(2, min(NSYM, 7) + 1):
        dmax = 4 if sec == "raw" else n
        for d in range(1, dmax + 1):
            bc = bget(sec, f"{n},{d}")
            if bc is None:
                continue
            eq = SIMP(sp.cancel(fn(n, d)) - bc) == 0
            rows[sec].append((n, d, bool(eq)))
            if not eq:
                ok_mom = False
                log(f"    {sec} MISMATCH n={n} d={d}: ours={sp.cancel(fn(n,d))} bcfg={bc}")
check(f"C7b  moment rows fac/binom/raw == ours, n=2..{min(NSYM,7)} (all d)", ok_mom)

# the never-consumed n=7 rows, called out separately
blind = []
if NSYM >= 7:
    for d in range(2, 8):
        bc = bget('fac', f"7,{d}")
        if bc is not None:
            blind.append(("fac", 7, d, bool(SIMP(ES.fac_mom(ES.Fp[7], 7, d) - bc) == 0)))
    for d in range(1, 8):
        bc = bget('binom', f"7,{d}")
        if bc is not None:
            ours = sum(c * sp.binomial(r, d) for r, c in enumerate(ES.coeffs(ES.Fp[7], 7)))
            blind.append(("binom", 7, d, bool(SIMP(sp.cancel(ours) - bc) == 0)))
    for kk in range(2, 5):
        bc = bget('raw', f"7,{kk}")
        if bc is not None:
            ours = sum(c * sp.Integer(r) ** kk for r, c in enumerate(ES.coeffs(ES.Fp[7], 7)))
            blind.append(("raw", 7, kk, bool(SIMP(sp.cancel(ours) - bc) == 0)))
    for r in range(0, 8):
        bc = bget('dist', f"7,{r}")
        if bc is None:
            bc = sp.Integer(0)
        blind.append(("dist", 7, r, bool(SIMP(ES.coeffs(ES.Fp[7], 7)[r] - bc) == 0)))
    check(f"C7c  BLIND n=7 rows (consumed by NO standing check): {len(blind)} rows all equal",
          all(x[3] for x in blind))

# bcfg_n7.json independent copy
ok_n7b = True
if NSYM >= 7 and 'dist' in B7:
    for r in range(0, 8):
        if str(r) in B7['dist']:
            bc = sp.cancel(sp.sympify(B7['dist'][str(r)], locals={'q': qs}))
            if SIMP(ES.coeffs(ES.Fp[7], 7)[r] - bc) != 0:
                ok_n7b = False
    check("C7d  bcfg_n7.json per-r rows == ours (n=7, second committed copy)", ok_n7b)

# teeth vs the cache: T4/T5 must break the rows they are designed to break
if NSYM >= 3:
    csm = ES.coeffs(ES.Fp[3], 3)
    mut = list(csm)
    mut[0] = mut[0] + delta
    mut[1] = mut[1] - 2 * delta
    mut[2] = mut[2] + delta
    bad = any(SIMP(mut[r] - (bget('dist', f"3,{r}") or sp.Integer(0))) != 0
              for r in range(0, 4))
    tooth("T4/cache  mutant fails the committed BCFG dist rows at n=3", bad)

# =====================================================================================
# 7. verdict
# =====================================================================================
log("=" * 78)
res = {
    "checks": CHECKS, "fails": FAILS, "teeth": TEETH,
    "predictions": PRED,
    "bcfg_rows": {k: [list(x) for x in v] for k, v in rows.items()},
    "blind_n7": [list(x) for x in blind],
    "n0_monic": {str(k): (None if n0.get(k) is None else int(n0[k])) for k in n0},
    "elapsed_s": round(time.time() - T0, 1),
    "log": LOG,
}
json.dump(res, open(os.path.join(HERE, 'moments_results.json'), 'w'), indent=1)
log(f"CHECKS={CHECKS}  FAILS={len(FAILS)}  TEETH_BITING={sum(TEETH.values())}/{len(TEETH)}")
if FAILS:
    log("FAILED: " + "; ".join(FAILS))
ok = (not FAILS) and all(TEETH.values())
log("VERDICT: " + ("GREEN" if ok else "RED"))
sys.exit(0 if ok else 1)
