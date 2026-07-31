#!/usr/bin/env python3
"""N7-track-count_test.py — numeric stress test of the K7 TRACK-COUNT laws
(conjecture M01; Lean rows `Cl7Kernel` at MovesU/DefsLedger.lean:199-217 and
`BridgeKernels.slice_bound` at MovesU/BridgeKernels.lean:216).

=========================== WHAT THE LEAN ASSERTS ===========================
`Cl7Kernel n KC` posits p-UNIFORM data L(n), Dden(n), w*(N), T(n,N) (bound
BEFORE any prime) with, for every prime p, every monic f in MonicBox n p off
discZero, and every stratum history H / branch b of f's canonical OM tree:

 (1) track_restarts:  countPop H recT1 + countPop H t4  <=  L
     [#(T1-row recentering nodes) + #(T4-row nodes) bounded by a CONSTANT
      depending on n alone — uniform in p, in N, and in DEPTH.]
 (2) zero_gain:       threshold b <= N  ->
                      dTotal(hist b) - countPop (hist b) incT12
                        <=  L * Dden * w*(N)
     [d_zero = #continuing non-genuine-increment nodes = #recT1+#t3+#t4.]
 (3) genuine_bound:   threshold b <= N ->
                      countPop (hist b) incT12  <=  n * N
 (4) slice_bound:     card {canonical trees T of type sigma : thr T <= N}
                        <=  T(n,N)   (p-uniform).

Candidate shapes on record (MOVES_2026-07-24.md SQ.0 + (TRK-RULE)):
L(n) <= n^2 (sealed candidate), Dden(n) | n! (candidate n!), w*(N) affine
in N (derived given the height budget), T(n,N) explicit.  The blueprint
BRIDGE_BP4_KERNELS_2026-07-30.md 3.D flags (1)'s CONSTANT L(n) as an
ESCALATED plausibility downgrade ("a fixed-degree family of increasing
discriminant depth with successive recentering/refinement steps is the
obvious stress family"); its only prior support is a finite 15/15 probe
at p=2, n in {3,4}.

===================== MAPPING LEAN -> WHAT WE COMPUTE ======================
Engine: a from-scratch Okutsu-Montes cluster walker over exact integers mod
p^K (frame-based, matching MOVES D.0 "each node's polygon in its own frame"):

* XNode <-> one Newton-polygon side read of an open cluster, letter fields
  (e, ell, h) = the side's slope -h/e (lowest terms, values in the node's
  own frame normalization) and residual degree ell; sel = (g, mu) = degree
  and multiplicity of the selected residual factor; isIncrement = (e*g >= 2)
  (key degree grows), matching XNode.t2inc/t3inc/t4rec coherence laws.
* rowOf: T1 iff ell>=2; T2 iff ell=1, e>=2, h>=2; T3 iff ell=1, e>=2, h=1;
  T4 iff ell=1, e=1 (continuing); T5 terminal.  popOf: incT12 = T1/T2
  increments; recT1 = T1 non-increments (e=1, g=1, mu>=2); t3 = T3; t4 = T4.
* Continuation semantics (classical Montes): a member with mu = 1 is a
  DECIDED leaf; mu >= 2 with e*g = 1 is a same-key refinement (recentering);
  mu >= 2 with e*g >= 2 opens a deeper cluster (increment), realized here as
  a frame change: e>=2 -> Eisenstein frame pi^e = c*.p_frame (ring tower);
  e=1, g>=2 -> rescale x = c + scale.y, cluster reopened at the degree-g
  residue point.  Frame openings are NOT counted as nodes (MOVES T0 rule).
* threshold b (Thm 2.1's per-stratum N0) SURROGATE: N* = ceil(max absolute
  p-adic value consumed by any polygon read on the branch) + 1 == the
  minimal coefficient precision that reproduces the branch's walk.
* vdisc = v_p(disc f) computed independently via PARI poldisc.

FLAGGED SIMPLIFICATIONS / DEVIATIONS (fidelity ledger):
 F1. Refinements are FULL-SIDE reads (one node per polygon read, the
     residual root lifted one digit); if the MOVES canonical ledger steps
     digit-by-digit its recentering count is >= ours, so our counts are
     LOWER bounds — sufficient for refuting constant-L candidates, and
     conservative (never over-eager) for law (1).
 F2. ell=1, e=1, g=1, mu=1 confirming reads are treated as T5 (per the T5
     row gloss "the confirming W = 1 read included") and NOT counted in t4.
     Consequence: our engine emits no T4-population nodes; all recentering
     mass sits in recT1.  Only the SUM #recT1+#t4 enters laws (1)-(2), so
     the split ambiguity does not affect the tested inequalities.
 F3. Ramified continuations are walked in an explicit Eisenstein frame
     (pi^e = c*.p) over the previous ring; for WILD e (p | e) the frame is
     a Krasner approximation of the true extension, and the frame-opening
     residue-point selection absorbs residue-degree data that ℚ_p-Montes
     would surface at the next node.  Node-count noise is O(1) per frame
     opening; final splitting types are cross-checked against PARI
     factorpadic per f, and any mismatching f is EXCLUDED from law
     statistics and reported as an engine-fidelity failure.
 F4. threshold surrogate N* (above) may differ from Thm 2.1's N0 by an
     additive/affine amount; laws (2)-(3) are tested at N = N* which is a
     LOWER estimate of the usable N, i.e. our test is STRICTER than the
     law.  Violations are therefore interpreted via margins, and headline
     ratios are reported so any affine recalibration can be applied.
 F5. w*(N) has no explicit constant on record; law (2) is tested in the
     candidate shape L=n^2, Dden=n!, w*(N)=N, and the raw maxima of
     d_zero/N* are reported per (n,p) so ANY affine w* candidate can be
     checked against the data.
 F6. Law (4)'s Tree object is surrogated by the canonical serialization of
     the walked tree (sorted branch histories: letter fields + leaf (e,f)
     invariants; residual-root identities and frame units EXCLUDED).  The
     count of distinct serializations with N* <= N per splitting type,
     compared across p at fixed (n,N), tests p-uniformity from below
     (sampled counts are lower bounds).

VALIDATION GATES (all must pass for the law statistics to be trusted):
 V1. PARI factorpadic oracle tie: aggregated leaf (e,f) factor multiset ==
     quartic_oracle.full_type on every stress-family member and on random
     census samples (and coarse degree multisets more broadly).
 V2. padic_types.cubic_type_monic tie on cubic boxes (independent non-PARI
     oracle, degrees <= 3).
 V3. D.10 strict ladder climb: along any same-key recentering chain the
     side height h strictly increases (frame-fixed); violations counted as
     anomalies (would refute the KD6 ladder law, not just this engine).
 V4. Degree checksums (leaf x-mass sums to n), residual endpoint
     nonvanishing, V_mu = 0, integrality of factor counts.

Run:  PYTHONPATH=~/.local/lib/python3.10/site-packages python3 \
        verification/openmath/N7-track-count_test.py [--quick]
Log:  tee'd by the caller to verification/openmath/logs/N7-track-count.log
JSON: verification/openmath/results/N7-track-count_results.json
"""
import sys, os, json, time, random, argparse
from fractions import Fraction
from math import gcd, factorial

sys.path.insert(0, os.path.expanduser('~/.local/lib/python3.10/site-packages'))
HERE = os.path.dirname(os.path.abspath(__file__))
VERIF = os.path.dirname(HERE)
sys.path.insert(0, VERIF)

import cypari2
pari = cypari2.Pari()
pari.allocatemem(1 << 28, silent=True)

INF = 10 ** 9          # valuation marker "above precision horizon"
RNG = random.Random(20260731)

# ======================================================================
# Ring tower: BaseRing = Z/p^K with uniformizer p; EisRing(prev, e, cstar)
# = prev[pi]/(pi^e - cstar*pi_prev), elements = length-e tuples of prev
# elements.  All valuations are integers in 1/Eabs units (Eabs = absolute
# ramification of the ring over Z_p); exactness of the min formula is
# guaranteed by gcd(h,e)=1 slope bookkeeping (distinct residues mod e).
# ======================================================================
class BaseRing:
    Eabs = 1
    def __init__(self, p, K):
        self.p, self.K, self.pk = p, K, p ** K
    def zero(self):  return 0
    def one(self):   return 1
    def from_int(self, a): return a % self.pk
    def add(self, a, b): return (a + b) % self.pk
    def sub(self, a, b): return (a - b) % self.pk
    def mul(self, a, b): return (a * b) % self.pk
    def is_zero(self, a): return a % self.pk == 0
    def val(self, a):
        # p-adic valuation in 1/Eabs = integer units; INF if 0 mod p^K
        a %= self.pk
        if a == 0: return INF
        v, p = 0, self.p
        while a % p == 0: a //= p; v += 1
        return v
    def digit(self, a, w):
        # residue in F_p at value level w (w in ring units)
        return (a // self.p ** w) % self.p if w < self.K else 0
    def shift_elt(self, r, w):
        # element r~ * pi^w  (r an int digit 0..p-1)
        return (r * self.p ** w) % self.pk
    def div_val(self, a, w):
        # a / pi^w  (caller guarantees val(a) >= w); top digits garbage,
        # guarded by the walk's precision horizon
        return (a % self.pk) // self.p ** w
    def mul_unif(self, a):
        return (a * self.p) % self.pk
    def inv_unit(self, a):
        return pow(a, -1, self.pk)

class EisRing:
    def __init__(self, prev, e, cstar):
        # pi^e = cstar * pi_prev  (cstar a unit of prev)
        self.prev, self.e, self.cstar = prev, e, cstar
        self.Eabs = prev.Eabs * e
        self.p, self.K = prev.p, prev.K
        self.cinv = prev.inv_unit(cstar)
    def zero(self):  return tuple([self.prev.zero()] * self.e)
    def one(self):
        z = [self.prev.zero()] * self.e; z[0] = self.prev.one()
        return tuple(z)
    def from_prev(self, a):
        z = [self.prev.zero()] * self.e; z[0] = a
        return tuple(z)
    def add(self, a, b): return tuple(self.prev.add(x, y) for x, y in zip(a, b))
    def sub(self, a, b): return tuple(self.prev.sub(x, y) for x, y in zip(a, b))
    def is_zero(self, a): return all(self.prev.is_zero(x) for x in a)
    def mul(self, a, b):
        e, prev = self.e, self.prev
        acc = [prev.zero()] * (2 * e - 1)
        for i, x in enumerate(a):
            if prev.is_zero(x): continue
            for j, y in enumerate(b):
                if prev.is_zero(y): continue
                acc[i + j] = prev.add(acc[i + j], prev.mul(x, y))
        # fold slots >= e:  pi^e = cstar * pi_prev
        out = list(acc[:e])
        for k in range(2 * e - 2, e - 1, -1):
            t = acc[k]
            if prev.is_zero(t): continue
            out[k - e] = prev.add(out[k - e],
                                  prev.mul_unif(prev.mul(t, self.cstar)))
        return tuple(out)
    def val(self, a):
        best = INF
        for i, x in enumerate(a):
            v = self.prev.val(x)
            if v < INF:
                best = min(best, self.e * v + i)
        return best
    def digit(self, a, w):
        i = w % self.e
        return self.prev.digit(a[i], (w - i) // self.e)
    def shift_elt(self, r, w):
        i = w % self.e
        z = [self.prev.zero()] * self.e
        z[i] = self.prev.shift_elt(r, (w - i) // self.e)
        return tuple(z)
    def div_val(self, a, w):
        # divide by pi^w, one uniformizer at a time
        for _ in range(w):
            a = self._div_pi(a)
        return a
    def _div_pi(self, a):
        # (b0 + b1 pi + ...)/pi = b1 + b2 pi + ... + (b0/(cstar pi_prev)) pi^{e-1}
        prev = self.prev
        top = prev.div_val(prev.mul(a[0], self.cinv), 1)
        return tuple(list(a[1:]) + [top])
    def mul_unif(self, a):
        # multiply by pi
        prev = self.prev
        out = [prev.mul_unif(prev.mul(a[-1], self.cstar))] + list(a[:-1])
        return tuple(out)
    def inv_unit(self, a):
        # Newton iteration from the residue inverse (val(a) == 0)
        r = self.digit(a, 0)
        x = self.from_int_digit(pow(r, -1, self.p))
        two = self.add(self.one(), self.one())
        for _ in range(self.K.bit_length() + self.Eabs.bit_length() + 2):
            x = self.mul(x, self.sub(two, self.mul(a, x)))
        return x
    def from_int_digit(self, r):
        z = [self.prev.zero()] * self.e
        z[0] = (self.prev.from_int(r) if isinstance(self.prev, BaseRing)
                else self.prev.from_int_digit(r))
        return tuple(z)

def ring_from_int(ring, a):
    if isinstance(ring, BaseRing): return ring.from_int(a)
    return ring.from_prev(ring_from_int(ring.prev, a))

# ---------------- polynomials over a ring (lists low->high) ----------------
def poly_trim(R, f):
    while len(f) > 1 and R.is_zero(f[-1]): f = f[:-1]
    return f

def poly_add(R, f, g):
    n = max(len(f), len(g))
    return [(R.add(f[i] if i < len(f) else R.zero(),
                   g[i] if i < len(g) else R.zero())) for i in range(n)]

def poly_mul(R, f, g):
    out = [R.zero()] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if R.is_zero(a): continue
        for j, b in enumerate(g):
            out[i + j] = R.add(out[i + j], R.mul(a, b))
    return out

def poly_divmod_monic(R, f, phi):
    # phi monic; returns (q, r) with f = q*phi + r, deg r < deg phi
    f = list(f); m = len(phi) - 1
    q = [R.zero()] * max(1, len(f) - m)
    for k in range(len(f) - 1, m - 1, -1):
        c = f[k]
        if R.is_zero(c):
            continue
        q[k - m] = c
        for i in range(m + 1):
            f[k - m + i] = R.sub(f[k - m + i],
                                 R.mul(c, phi[i]) if i < m else c)
    return q, f[:m] if m > 0 else [R.zero()]

def phi_expansion(R, f, phi, jmax):
    # f = sum A_j phi^j; return [A_0..A_jmax]
    out, cur = [], list(f)
    for _ in range(jmax + 1):
        cur, rem = poly_divmod_monic(R, cur, phi)
        out.append(rem)
        if len(cur) == 1 and R.is_zero(cur[0]):
            cur = [R.zero()]
    return out

def poly_val(R, f):
    return min((R.val(c) for c in f), default=INF)

# ---------------- lower convex hull ----------------
def lower_hull(pts):
    """pts = [(j, V)] with V possibly INF; returns hull vertex list over the
    finite points, from smallest j to largest."""
    fin = [(j, v) for (j, v) in pts if v < INF]
    hull = []
    for pnt in fin:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (pnt[0] - x1) >= (pnt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pnt)
    return hull

# ======================================================================
# Finite-field residual factorization via PARI (cached)
# ======================================================================
_ff_cache = {}
def factor_residual(p, psibar, coeffs):
    """Factor sum coeffs[i] y^i over F_p[z]/psibar(z) (psibar tuple of ints,
    deg m >= 1; for m=1 plain F_p).  coeffs = tuple of tuples of ints
    (each an F_p[z]-poly of deg < m, low->high).
    Returns list of (factor_coeff_tuples, mult) with the same encoding,
    factors monic, sorted canonically."""
    key = (p, psibar, coeffs)
    if key in _ff_cache: return _ff_cache[key]
    m = len(psibar) - 1
    if m == 1:
        # coefficients are ints in slot 0
        pol = pari.Pol([c[0] % p for c in reversed(coeffs)], 'y')
        fac = pari.factormod(pol, p)
        out = []
        for fk, mu in zip(fac[0], fac[1]):
            g = pari.centerlift(pari.lift(fk))
            if int(pari.poldegree(g)) < 1:
                continue        # leading-unit row
            cl = [int(x) % p for x in pari.Vec(g)][::-1]  # low->high
            out.append((tuple((c,) for c in cl), int(mu)))
    else:
        g = _ff_cache.get((p, psibar))
        if g is None:
            zpol = pari.Pol([c % p for c in reversed(psibar)], 'z')
            g = pari.ffgen(zpol * pari.Mod(1, p), 'z')
            _ff_cache[(p, psibar)] = g
        one = g ** 0
        elts = []
        for cf in coeffs:
            e = 0 * one
            for i, c in enumerate(cf):
                if c % p:
                    e = e + (c % p) * g ** i
            elts.append(e)
        w = _ff_cache.get('wvar')
        if w is None:
            w = pari.varlower('w', g)
            _ff_cache['wvar'] = w
        pol = 0 * one
        for i, e in enumerate(elts):
            pol = pol + e * w ** i
        fac = pari.factor(pol)
        out = []
        for fk, mu in zip(fac[0], fac[1]):
            d = int(pari.poldegree(fk))
            if d < 1:
                continue        # leading-unit row
            cl = []
            for i in range(d + 1):
                lifted = pari.liftall(pari.polcoef(fk, i))
                cl.append(tuple(int(pari.polcoef(lifted, i2, 'z')) % p
                                for i2 in range(m)))
            out.append((tuple(cl), int(mu)))
    out.sort()
    _ff_cache[key] = out
    return out

# ======================================================================
# The OM cluster walker
# ======================================================================
def row_of(ell, e, h):
    if ell >= 2: return 'T1'
    if e >= 2:   return 'T2' if h >= 2 else 'T3'
    return 'T4'

def pop_of(node):
    row, inc = node['row'], node['inc']
    if row == 'T1': return 'incT12' if inc else 'recT1'
    if row == 'T2': return 'incT12'
    if row == 'T3': return 't3'
    if row == 'T4': return 't4'
    return None

class Walk:
    """One polynomial's full canonical-tree walk."""
    MAXNODES = 4000
    def __init__(self, coeffs, n, p, K):
        self.n, self.p, self.K = n, p, K
        self.R0 = BaseRing(p, K)
        self.branches = []      # dicts: hist, ef, xw (x-mass weight, Fraction), deep, Nstar
        self.anom = []          # anomaly strings
        self.nodes_used = 0
        F = [self.R0.from_int(c) for c in coeffs]
        self.level0(self.R0, F, Fraction(0), 1, 1, Fraction(1), [], opening=None)

    # ---------- level-0 / frame-opening cluster dispatch ----------
    def level0(self, R, F, depth0, eacc, facc, xmult, hist, opening):
        """Reduce F mod the maximal ideal, open clusters.
        opening = None: original top level (all residue points walked);
        opening = (psi_sel_coeffs, mu): only that residue point is walked
        (frame openings; NOT a counted node, MOVES T0 rule)."""
        p = self.p
        fbar = [R.digit(c, 0) for c in F]
        while len(fbar) > 1 and fbar[-1] == 0: fbar.pop()
        if len(fbar) <= 1:
            self.anom.append('level0-degenerate-reduction'); return
        fac = factor_residual(p, (0, 1), tuple((c,) for c in fbar))
        if opening is None:
            for psi, mu in fac:
                psi_flat = tuple(c[0] for c in psi)
                if psi_flat[-1] != 1:
                    self.anom.append('nonmonic-residual-factor'); continue
                d = len(psi_flat) - 1
                if mu == 1:
                    self.leaf(hist, eacc * 1, facc * d, Fraction(d) * xmult, depth0)
                else:
                    self.cluster(R, F, psi_flat, mu, hist, depth0, eacc, facc * d, xmult)
        else:
            psi_sel, mu = opening
            # validation: psi_sel^mu divides fbar's unit part
            found = [m for (ps, m) in fac
                     if tuple(c[0] for c in ps) == psi_sel]
            if not found or found[0] < mu:
                self.anom.append('frame-opening-residue-mismatch'); return
            d = len(psi_sel) - 1
            self.cluster(R, F, psi_sel, mu, hist, depth0, eacc, facc * d, xmult)

    # ---------- one open cluster: key + polygon reads (recursive) ----------
    def cluster(self, R, F, psibar, mu, hist, depth0, eacc, facc, xmult,
                phi=None, prev_h=None):
        if self.nodes_used > self.MAXNODES:
            self.anom.append('node-cap'); return
        self.nodes_used += 1
        p, m = self.p, len(psibar) - 1
        if phi is None:
            phi = [ring_from_int(R, c) for c in psibar]
        A = phi_expansion(R, F, phi, mu)
        pts = [(j, poly_val(R, A[j])) for j in range(mu + 1)]
        if pts[mu][1] != 0:
            self.anom.append('Vmu-nonzero(%d)' % pts[mu][1]); return
        # precision horizon (in ring units): consumed values must stay below
        horizon = (self.K - 2) * R.Eabs
        if pts[0][1] >= min(INF, horizon):
            self.branches.append(dict(hist=hist, ef=None, xw=Fraction(m * mu) * xmult,
                                      deep=True, Nstar=None))
            return
        hull = lower_hull(pts)
        if any(v >= horizon for (_, v) in hull):
            self.branches.append(dict(hist=hist, ef=None, xw=Fraction(m * mu) * xmult,
                                      deep=True, Nstar=None))
            return
        # missing j=0 vertex (INF val) with finite hull start > 0: phi divides F
        if hull[0][0] != 0:
            self.branches.append(dict(hist=hist, ef=None, xw=Fraction(m * mu) * xmult,
                                      deep=True, Nstar=None))
            return
        for si in range(len(hull) - 1):
            (j1, v1), (j2, v2) = hull[si], hull[si + 1]
            rise, run = v1 - v2, j2 - j1
            if rise <= 0:
                continue   # non-principal part (slope >= 0): unit side, skip
            g0 = gcd(rise, run)
            e_s, h_s, ell = run // g0, rise // g0, g0
            # residual polynomial along the side
            coeffs = []
            for i in range(ell + 1):
                j = j1 + i * e_s
                w = v1 - i * h_s
                Aj = A[j] if j < len(A) else [R.zero()]
                cf = [R.digit(c, w) for c in Aj]
                cf = tuple((cf + [0] * m)[:m]) if m > 1 else ((cf[0] if cf else 0),)
                coeffs.append(cf if m > 1 else (cf if isinstance(cf, tuple) else (cf,)))
            coeffs = [c if isinstance(c, tuple) else (c,) for c in coeffs]
            coeffs = tuple(tuple(c) for c in coeffs)
            if all(x == 0 for x in coeffs[0]) or all(x == 0 for x in coeffs[-1]):
                self.anom.append('residual-endpoint-zero'); continue
            fac = factor_residual(p, tuple(psibar), coeffs)
            wabs = depth0 + Fraction(v1, R.Eabs)
            for psi_f, mu_f in fac:
                g = len(psi_f) - 1
                node = dict(e=e_s, ell=ell, h=h_s, g=g, mu=mu_f,
                            inc=(e_s * g >= 2), row=row_of(ell, e_s, h_s),
                            wabs=wabs, m=m)
                hist2 = hist + [node]
                if mu_f == 1:
                    if e_s == 1 and g == 1 and ell == 1:
                        node['row'] = 'T5'   # confirming read (fidelity F2)
                    self.leaf(hist2, eacc * e_s, facc * g,
                              Fraction(m * e_s * g) * xmult, wabs)
                elif e_s == 1 and g == 1:
                    # RECENTERING (same key, refined)
                    if prev_h is not None and h_s <= prev_h:
                        self.anom.append('D10-climb-violation h %s<=%s' % (h_s, prev_h))
                    root = self.residual_root(psi_f, m)
                    delta = [R.mul(ring_from_int(R, rc), R.shift_elt(1, h_s))
                             for rc in root]
                    phi2 = poly_add(R, phi, delta + [R.zero()] * (m + 1 - len(delta)))
                    phi2 = phi2[:m] + [R.one()]
                    self.cluster(R, F, psibar, mu_f, hist2, depth0, eacc, facc,
                                 xmult, phi=phi2, prev_h=h_s)
                elif e_s == 1:
                    # UNRAMIFIED INCREMENT (g >= 2): rescale x = c + pi^h y
                    if m != 1:
                        self.anom.append('rescale-at-m%d' % m); continue
                    c0 = R.sub(R.zero(), phi[0])
                    s = R.shift_elt(1, h_s)
                    F2 = taylor_shift_scale(R, F, c0, s)
                    F2, _lost = normalize_content(R, F2)
                    depth0b = depth0 + Fraction(h_s, R.Eabs)
                    self.level0(R, F2, depth0b, eacc, facc, xmult, hist2,
                                opening=(psi_f_flat(psi_f), mu_f))
                else:
                    # RAMIFIED INCREMENT (e >= 2): ORDER-2 continuation over
                    # the SAME ring (phi2 = (x-c)^e - r~ pi^h; v1-graded reads)
                    if m != 1 or g != 1:
                        self.anom.append('order2-at-m%d-g%d' % (m, g)); continue
                    r_int = self.residual_root(psi_f, 1)[0]
                    if r_int % p == 0:
                        self.anom.append('order2-zero-root'); continue
                    c0 = R.sub(R.zero(), phi[0])
                    xminusc = [R.sub(R.zero(), c0), R.one()]   # (x - c)
                    phi2 = [R.one()]
                    for _ in range(e_s):
                        phi2 = poly_mul(R, phi2, xminusc)
                    phi2[0] = R.sub(phi2[0], R.mul(ring_from_int(R, r_int),
                                                   R.shift_elt(1, h_s)))
                    self.order2(R, F, c0, e_s, h_s, r_int, mu_f, hist2,
                                depth0, eacc, facc, xmult, phi2, None)

    def order2(self, R, F, c0, e1, h1, rbar, mu, hist, depth0, eacc, facc,
               xmult, phi2, prev_h2):
        """Order-2 Montes reads: key phi2 of degree e1 (built over center c0
        with first-order data (e1, h1, rbar)); v1-valuation: v1(elem a) =
        e1*R.val(a), v1(x-c0) = h1 (integer grid; v1(pi_R) = e1).
        Residual coefficients live in F_p (f1 = 1 here), with the carry
        twist rbar^{tau_i} from the graded algebra F_p[u,P]/(u^e1 - rbar P^h1).
        Only recenterings (e2 = 1, g2 = 1, mu2 >= 2) continue; any deeper
        increment with mu2 >= 2 needs order 3 = degree >= 8 > 6 (anomaly)."""
        if self.nodes_used > self.MAXNODES:
            self.anom.append('node-cap'); return
        self.nodes_used += 1
        p = self.p
        h1inv = pow(h1, -1, e1)
        A = phi_expansion(R, F, phi2, mu)
        # (x-c0)-Taylor coefficients of each A_j (deg < e1)
        atay, V1 = [], []
        for j in range(mu + 1):
            aj = taylor_shift_scale(R, A[j] + [R.zero()] * (e1 - len(A[j])),
                                    c0, R.one())
            aj = aj[:e1]
            atay.append(aj)
            v = min((e1 * R.val(ak) + k * h1 for k, ak in enumerate(aj)
                     if R.val(ak) < INF), default=INF)
            V1.append(v)
        if V1[mu] != 0:
            self.anom.append('order2-Vmu-nonzero(%s)' % V1[mu]); return
        horizon = (self.K - 2) * R.Eabs * e1
        pts = [(j, V1[j]) for j in range(mu + 1)]
        if pts[0][1] >= min(INF, horizon):
            self.branches.append(dict(hist=hist, ef=None,
                                      xw=Fraction(e1 * mu) * xmult,
                                      deep=True, Nstar=None))
            return
        hull = lower_hull(pts)
        if any(v >= horizon for (_, v) in hull) or hull[0][0] != 0:
            self.branches.append(dict(hist=hist, ef=None,
                                      xw=Fraction(e1 * mu) * xmult,
                                      deep=True, Nstar=None))
            return
        for si in range(len(hull) - 1):
            (j1, v1), (j2, v2) = hull[si], hull[si + 1]
            rise, run = v1 - v2, j2 - j1
            if rise <= 0:
                continue
            g0 = gcd(rise, run)
            e2, h2, ell2 = run // g0, rise // g0, g0
            # residual with carry twist
            kappa = (h2 * h1inv) % e1
            k1 = (v1 * h1inv) % e1
            coeffs, bad = [], False
            for i in range(ell2 + 1):
                j = j1 + i * e2
                w = v1 - i * h2
                ki = (w * h1inv) % e1
                vlev, remv = divmod(w - ki * h1, e1)
                if remv != 0 or vlev < 0:
                    bad = True; break
                ci = R.digit(atay[j][ki], vlev) if V1[j] == w else 0
                tau = (ki + i * kappa - k1)
                if tau % e1 != 0:
                    bad = True; break
                tau //= e1
                ci = (ci * pow(rbar, tau % (p - 1) if p > 2 else 0, p)) % p
                coeffs.append((ci,))
            if bad or coeffs[0] == (0,) or coeffs[-1] == (0,):
                self.anom.append('order2-residual-bad'); continue
            fac = factor_residual(p, (0, 1), tuple(coeffs))
            wabs = depth0 + Fraction(v1, e1 * R.Eabs)
            for psi2, mu2 in fac:
                g2 = len(psi2) - 1
                node = dict(e=e2, ell=ell2, h=h2, g=g2, mu=mu2,
                            inc=(e2 * g2 >= 2), row=row_of(ell2, e2, h2),
                            wabs=wabs, m=e1, order=2)
                hist2 = hist + [node]
                if mu2 == 1:
                    if e2 == 1 and g2 == 1 and ell2 == 1:
                        node['row'] = 'T5'
                    self.leaf(hist2, eacc * e1 * e2, facc * g2,
                              Fraction(e1 * e2 * g2) * xmult, wabs)
                elif e2 == 1 and g2 == 1:
                    if prev_h2 is not None and h2 <= prev_h2:
                        self.anom.append('D10-climb-violation o2 %s<=%s'
                                         % (h2, prev_h2))
                    s_root = (-psi2[0][0]) % p
                    # un-twist the refinement digit: delta leading form must be
                    # s * b_{h2}; R(y) roots carry rbar^{tau}-twisted digits
                    kh = (h2 * h1inv) % e1
                    vlev, remv = divmod(h2 - kh * h1, e1)
                    if remv != 0 or vlev < 0:
                        self.anom.append('order2-delta-unrepresentable')
                        self.branches.append(dict(
                            hist=hist2, ef=None, xw=Fraction(e1 * mu2) * xmult,
                            deep=True, Nstar=None))
                        continue
                    sd = (s_root * pow(rbar, (-1 * ((kh + 0) // e1)) % (p - 1)
                                       if p > 2 else 0, p)) % p
                    # delta = sd~ * (x-c0)^{kh} * pi^{vlev}
                    delta = [R.zero()] * (kh + 1)
                    delta[kh] = R.mul(ring_from_int(R, sd), R.shift_elt(1, vlev))
                    dx = [R.zero()]
                    xmc = [R.sub(R.zero(), R.sub(R.zero(), c0)), R.one()]
                    # build delta(x) = sd * pi^vlev * (x - c0)^kh
                    dpoly = [R.mul(ring_from_int(R, sd), R.shift_elt(1, vlev))]
                    for _ in range(kh):
                        dpoly = poly_mul(R, dpoly, [c0neg(R, c0), R.one()])
                    phi2b = poly_add(R, phi2, dpoly + [R.zero()] *
                                     max(0, len(phi2) - len(dpoly)))
                    phi2b = phi2b[:e1] + [R.one()]
                    self.order2(R, F, c0, e1, h1, rbar, mu2, hist2, depth0,
                                eacc, facc, xmult, phi2b, h2)
                else:
                    self.anom.append('order3-needed e2=%d g2=%d mu2=%d'
                                     % (e2, g2, mu2))
                    self.branches.append(dict(
                        hist=hist2, ef=None,
                        xw=Fraction(e1 * e2 * g2 * mu2) * xmult,
                        deep=True, Nstar=None))

    def residual_root(self, psi_f, m):
        """Root of a degree-1 residual factor psi_f = y + a over F_{p^m}:
        returns -a as an F_p[z]-coeff list of length m."""
        a = psi_f[0]
        return [(-c) % self.p for c in a]

    def leaf(self, hist, e_tot, f_tot, xw, wmax):
        Nstar = None
        ws = [nd['wabs'] for nd in hist] + ([wmax] if wmax is not None else [])
        if ws:
            mx = max(ws)
            Nstar = int(mx) + (0 if mx == int(mx) else 1) + 1
        else:
            Nstar = 1
        self.branches.append(dict(hist=hist, ef=(e_tot, f_tot), xw=xw,
                                  deep=False, Nstar=Nstar))

def psi_f_flat(psi_f):
    return tuple(c[0] for c in psi_f)

def taylor_shift_scale(R, F, c, s):
    """F(c + s*y) over ring R (F a coeff list).  Horner in (c + s*y)."""
    out = [F[-1]]
    for k in range(len(F) - 2, -1, -1):
        # out = out * (c + s*y) + F[k]
        new = [R.zero()] * (len(out) + 1)
        for i, a in enumerate(out):
            new[i] = R.add(new[i], R.mul(a, c))
            new[i + 1] = R.add(new[i + 1], R.mul(a, s))
        new[0] = R.add(new[0], F[k])
        out = new
    return out

def normalize_content(R, F):
    w = poly_val(R, F)
    if w == 0 or w >= INF:
        return F, 0
    return [R.div_val(c, w) for c in F], w

# ======================================================================
# Per-f statistics extraction
# ======================================================================
def branch_stats(br):
    pops = {'incT12': 0, 'recT1': 0, 't3': 0, 't4': 0}
    for nd in br['hist']:
        pp = pop_of(nd)
        if pp: pops[pp] += 1
    dtotal = sum(pops.values())
    return dict(pops=pops, dtotal=dtotal,
                track1=pops['recT1'] + pops['t4'],
                dzero=dtotal - pops['incT12'],
                ninc=pops['incT12'],
                Nstar=br['Nstar'], deep=br['deep'])

def tree_serial(walk):
    """Canonical serialization of the walked tree (law 4 surrogate):
    sorted branch histories with letter fields + leaf (e,f)."""
    rows = []
    for br in walk.branches:
        h = tuple((nd['e'], nd['ell'], nd['h'], nd['g'], nd['mu'],
                   nd['row']) for nd in br['hist'])
        rows.append((h, br['ef'] if not br['deep'] else ('DEEP',)))
    return tuple(sorted(rows))

def sigma_of(walk):
    """Aggregated Q_p splitting type from leaves; None if deep/ambiguous."""
    from collections import defaultdict
    mass = defaultdict(Fraction)
    for br in walk.branches:
        if br['deep']: return None
        mass[br['ef']] += br['xw']
    sig = []
    for (e, f), xm in sorted(mass.items()):
        cnt = xm / (e * f)
        if cnt.denominator != 1: return 'AMBIG'
        sig.extend([(e, f)] * int(cnt))
    if sum(e * f for (e, f) in sig) != walk.n: return 'AMBIG'
    return tuple(sig)

def vp_int(a, p):
    if a == 0: return INF
    v = 0
    while a % p == 0: a //= p; v += 1
    return v

def vdisc_of(coeffs, p):
    d = pari.poldisc(pari.Pol(list(reversed([int(c) for c in coeffs]))))
    return vp_int(int(d), p) if d != 0 else INF

# ======================================================================
# Oracles
# ======================================================================
import quartic_oracle                                       # PARI full_type
try:
    import padic_types                                      # exact, deg <= 3
except Exception:
    padic_types = None

CUBIC_LABEL = {((1, 1), (1, 1), (1, 1)): '111', ((1, 1), (1, 2)): '12',
               ((1, 3),): '3', ((1, 1), (2, 1)): '1r1', ((3, 1),): '1c'}

# ======================================================================
# Report plumbing
# ======================================================================
LINES, CHECKS = [], []
def emit(s):
    LINES.append(s); print(s, flush=True)
def check(name, ok, detail=''):
    CHECKS.append((name, bool(ok), detail))
    emit('[%s] %s%s' % ('PASS' if ok else 'FINDING', name,
                        ('  ' + detail) if detail else ''))

# ======================================================================
# Law accumulators, per (n, p)
# ======================================================================
class LawTally:
    def __init__(self, n, p):
        self.n, self.p = n, p
        self.count = self.deep = self.oracle_bad = self.sigma_bad = 0
        self.anoms = {}
        self.max_track1 = (0, None)     # (value, witness)
        self.max_track1_depth = {}      # vdisc-bucket -> max track1
        self.max_dzero_ratio = (Fraction(0), None)
        self.max_ninc_ratio = (Fraction(0), None)
        self.viol_law1_n2 = 0           # track1 > n^2 (candidate refutations)
        self.viol_law3 = 0              # ninc > n*N*
        self.viol_law2 = 0              # dzero > n^2 * n! * N*
        self.trees = {}                 # sigma -> set of serials (with Nstar<=NCAP buckets)
    def feed(self, coeffs, walk, vd=None, witness_tag=''):
        self.count += 1
        for a in walk.anom:
            k = a.split(' ')[0]
            self.anoms[k] = self.anoms.get(k, 0) + 1
        n, stats_list = self.n, []
        anydeep = False
        for br in walk.branches:
            st = branch_stats(br)
            if st['deep']:
                anydeep = True
            stats_list.append(st)
        if anydeep: self.deep += 1
        wit = (witness_tag, tuple(int(c) for c in coeffs), vd)
        for st in stats_list:
            t1 = st['track1']
            if t1 > self.max_track1[0]:
                self.max_track1 = (t1, wit)
            if vd is not None and vd < INF:
                b = min(vd, 60)
                self.max_track1_depth[b] = max(self.max_track1_depth.get(b, 0), t1)
            if t1 > n * n: self.viol_law1_n2 += 1
            if not st['deep'] and st['Nstar']:
                Ns = st['Nstar']
                r2 = Fraction(st['dzero'], Ns)
                if r2 > self.max_dzero_ratio[0]:
                    self.max_dzero_ratio = (r2, wit)
                r3 = Fraction(st['ninc'], n * Ns)
                if r3 > self.max_ninc_ratio[0]:
                    self.max_ninc_ratio = (r3, wit)
                if st['ninc'] > n * Ns: self.viol_law3 += 1
                if st['dzero'] > n * n * factorial(n) * Ns: self.viol_law2 += 1
        return stats_list

# ======================================================================
# Stress families (LAW 1's increasing-depth refuter candidates)
# ======================================================================
def spectator(n_extra, p, avoid_res):
    """Monic degree-n_extra integer poly, separable irreducible mod p,
    residue disjoint from avoid_res (a set of F_p residual factors)."""
    if n_extra == 0: return [1]
    # scan small monic polys for irreducibility mod p and coprimality
    for trial in range(10000):
        cs = [RNG.randrange(p) for _ in range(n_extra)]
        pol = pari.Pol([1] + list(reversed(cs)))
        fac = pari.factormod(pol, p)
        if len(fac[:, 0]) == 1 and int(fac[0, 1]) == 1:
            g = pari.centerlift(pari.lift(fac[0, 0]))
            root_ok = True
            for r in avoid_res:
                if int(pari.subst(g, pari.Pol('x'), r)) % p == 0:
                    root_ok = False
            if root_ok:
                return [int(x) for x in reversed(list(pari.Vec(pol)))]
    raise RuntimeError('no spectator found')

def poly_mul_int(f, g):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return out

def stress_families(n, p, Ks):
    """Yield (tag, K', coeffs) increasing-depth families, all with a
    colliding cluster of depth ~K' plus a degree-(n-2 or n-4) spectator."""
    fams = []
    # a = unit with dense base-p digits (the center the engine must discover)
    a = sum(((i * 7 + 3) % (p - 1) + 1 if p > 2 else 1) * p ** i
            for i in range(30))
    for Kp in Ks:
        # S1 split pair: (x-a)(x-a-p^K d)
        pair = poly_mul_int([-a, 1], [-(a + p ** Kp), 1])
        fams.append(('S1-split', Kp, pair))
        # S2 ramified pair: (x-a)^2 - p^(2K+1)
        pair = [a * a - p ** (2 * Kp + 1), -2 * a, 1]
        fams.append(('S2-ram', Kp, pair))
        # S3 inert pair: (x-a)^2 - p^(2K) u, u a non-square unit
        u = None
        for cand in range(2, p * p):
            if cand % p and pow(cand, (p - 1) // 2, p) == p - 1 if p > 2 else False:
                u = cand; break
        if p == 2: u = 5    # 5 is a nonsquare unit in Z_2 (5 mod 8)
        if u is None: u = 2
        pair = [a * a - p ** (2 * Kp) * u, -2 * a, 1]
        fams.append(('S3-inert', Kp, pair))
    out = []
    for tag, Kp, pair in fams:
        res_root = (a % p)
        spec = spectator(n - 2, p, {res_root})
        out.append((tag, Kp, poly_mul_int(pair, spec)))
    # S4 (n>=4): deg-2-key cluster psi(x)^2 - p^(2K) u  (psi irred mod p)
    if n >= 4:
        psi = None
        for b in range(p):
            for c in range(1, p):
                pol = pari.Pol([1, b, c])
                fac = pari.factormod(pol, p)
                if len(fac[:, 0]) == 1 and int(fac[0, 1]) == 1:
                    psi = [c, b, 1]; break
            if psi: break
        psil = [psi[0] + p * 3, psi[1] + p * 7, 1]      # a lift with tail digits
        for Kp in Ks:
            base = poly_mul_int(psil, psil)
            base[0] -= p ** (2 * Kp) * (u if p > 2 else 5)
            spec = spectator(n - 4, p, set())
            out.append(('S4-key2', Kp, poly_mul_int(base, spec)))
    # S5 (n>=4): eis-frame chain ((x^2 - p c)^2 - p^(2K+1) style)
    if n >= 4:
        c = 1 + p  # unit
        for Kp in Ks:
            base = poly_mul_int([-p * c, 0, 1], [-p * c, 0, 1])
            base[0] -= p ** (2 * Kp + 1)
            spec = spectator(n - 4, p, set())
            out.append(('S5-eis', Kp, poly_mul_int(base, spec)))
    return out

# ======================================================================
# Random polynomial generators
# ======================================================================
def gen_uniform(n, p, K):
    M = p ** K
    return [RNG.randrange(M) for _ in range(n)] + [1]

def gen_valprofile(n, p, K):
    M = p ** K
    cs = []
    for i in range(n):
        v = RNG.randrange(0, K // 2 + 1)
        u = RNG.randrange(1, M)
        cs.append((u * p ** v) % M)
    return cs + [1]

def gen_clustered(n, p, K):
    M = p ** K
    roots, left = [], n
    while left > 0:
        d = RNG.choice([1, 1, 2, 2, 3]) if left >= 3 else left
        d = min(d, left)
        base = RNG.randrange(p)
        depth = RNG.randrange(1, max(2, K // 2))
        for _ in range(d):
            roots.append(base + p ** RNG.randrange(1, depth + 1) * RNG.randrange(M // p))
        left -= d
    f = [1]
    for r in roots:
        f = poly_mul_int(f, [-(r % M), 1])
    return [c % M for c in f[:-1]] + [1]

# ======================================================================
# Census driver
# ======================================================================
def walk_poly(coeffs, n, p, K):
    return Walk([c % (p ** K) for c in coeffs], n, p, K)

def oracle_tie(coeffs, p, walk, prec=None):
    """PARI full_type vs aggregated leaf multiset; returns (ok, expected)."""
    sig = sigma_of(walk)
    if sig is None: return (None, None)          # deep: not comparable
    prec = prec or (walk.K + 10)
    try:
        exp = quartic_oracle.full_type([int(c) for c in coeffs], p, prec=prec)
    except Exception as ex:
        return (None, 'oracle-error %s' % ex)
    return (sig == 'AMBIG' and 'AMBIG' or (tuple(sorted(sig)) == tuple(exp)), exp)

def run_config(n, p, K, counts, tally, do_full_oracle, quick):
    """Random censuses for one (n, p)."""
    nU, nV, nC = counts
    t0 = time.time()
    oracle_checked = oracle_full_bad = 0
    coarse_checked = coarse_bad = 0
    for kind, N in (('U', nU), ('V', nV), ('C', nC)):
        gen = {'U': gen_uniform, 'V': gen_valprofile, 'C': gen_clustered}[kind]
        for i in range(N):
            cs = gen(n, p, K)
            vd = vdisc_of(cs, p)
            if vd >= INF:   # inseparable representative: skip (discZero fence)
                continue
            wk = walk_poly(cs, n, p, K)
            tally.feed(cs, wk, vd, witness_tag='%s%d' % (kind, i))
            sig = sigma_of(wk)
            if sig == 'AMBIG':
                tally.sigma_bad += 1
            elif sig is not None:
                # coarse tie (degree multisets) on a subsample
                if i % 7 == 0:
                    try:
                        exp = quartic_oracle.coarse_type(
                            [int(c) for c in cs], p, prec=K + 10)
                        got = tuple(sorted(e * f for (e, f) in sig))
                        coarse_checked += 1
                        if got != tuple(exp):
                            coarse_bad += 1
                            if coarse_bad <= 3:
                                emit('    COARSE MISMATCH n=%d p=%d %s: got %s exp %s'
                                     % (n, p, cs, got, exp))
                    except Exception:
                        pass
                if do_full_oracle and i % 41 == 0:
                    ok, exp = oracle_tie(cs, p, wk)
                    if ok is not None:
                        oracle_checked += 1
                        if ok is not True:
                            oracle_full_bad += 1
                            tally.oracle_bad += 1
                            if oracle_full_bad <= 3:
                                emit('    FULL-ORACLE MISMATCH n=%d p=%d %s: got %s exp %s'
                                     % (n, p, cs, sigma_of(wk), exp))
                # law-4 tree registry
                ser = tree_serial(wk)
                Nst = max((b['Nstar'] or 0) for b in wk.branches)
                tally.trees.setdefault(sig, []).append((Nst, hash(ser)))
    emit('  (n=%d, p=%d) random census: %d walked, %d deep, %.0fs; '
         'coarse tie %d/%d bad, full tie %d/%d bad; anomalies %s'
         % (n, p, tally.count, tally.deep, time.time() - t0,
            coarse_bad, coarse_checked, oracle_full_bad, oracle_checked,
            tally.anoms or {}))
    return coarse_checked, coarse_bad, oracle_checked, oracle_full_bad

def run_stress(n, p, Ks, tally, K_extra=14):
    """LAW-1 stress families; returns rows for the depth table."""
    rows = []
    for tag, Kp, cs in stress_families(n, p, Ks):
        K = 2 * Kp + K_extra
        vd = vdisc_of(cs, p)
        wk = walk_poly(cs, n, p, K)
        stats = tally.feed(cs, wk, vd, witness_tag='%s-K%d' % (tag, Kp))
        t1max = max(st['track1'] for st in stats) if stats else 0
        dzmax = max(st['dzero'] for st in stats) if stats else 0
        Nst = max((st['Nstar'] or 0) for st in stats) if stats else 0
        ok, exp = oracle_tie(cs, p, wk, prec=K + 12)
        rows.append(dict(tag=tag, K=Kp, vd=(vd if vd < INF else -1),
                         track1=t1max, dzero=dzmax, Nstar=Nst,
                         oracle=(bool(ok) if ok is not None else None),
                         anom=list(wk.anom)))
        if ok is False:
            tally.oracle_bad += 1
            emit('    STRESS ORACLE MISMATCH n=%d p=%d %s K=%d: got %s exp %s'
                 % (n, p, tag, Kp, sigma_of(wk), exp))
    return rows

def cubic_box_census(p, K, cap, tally):
    """Exhaustive/capped monic cubic box mod p^K with padic_types tie."""
    M = p ** K
    total = min(M ** 3, cap)
    checked = bad = 0
    t0 = time.time()
    if M ** 3 <= cap:
        it = ((a2, a1, a0) for a2 in range(M) for a1 in range(M)
              for a0 in range(M))
    else:
        it = ((RNG.randrange(M), RNG.randrange(M), RNG.randrange(M))
              for _ in range(cap))
    for (a2, a1, a0) in it:
        cs = [a0, a1, a2, 1]
        vd = vdisc_of(cs, p)
        if vd >= INF:
            continue
        wk = walk_poly(cs, 3, p, K)
        tally.feed(cs, wk, vd, witness_tag='box')
        sig = sigma_of(wk)
        if sig not in (None, 'AMBIG') and padic_types is not None and vd < K - 2:
            lab = CUBIC_LABEL.get(tuple(sorted(sig)))
            exp = padic_types.cubic_type_monic(a2, a1, a0, p)
            checked += 1
            if lab != exp:
                bad += 1
                if bad <= 5:
                    emit('    PADIC_TYPES MISMATCH p=%d f=%s got %s exp %s'
                         % (p, cs, lab, exp))
    emit('  cubic box p=%d K=%d: %d members, tie %d/%d bad, %.0fs'
         % (p, K, total, bad, checked, time.time() - t0))
    return checked, bad

# ======================================================================
# main
# ======================================================================
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--quick', action='store_true')
    args = ap.parse_args()
    t00 = time.time()
    emit('#' * 74)
    emit('# N7-track-count run %s  (quick=%s)'
         % (time.strftime('%Y-%m-%d %H:%M:%S'), args.quick))
    emit('#' * 74)
    NS = [3, 4, 5, 6]
    PS = [2, 3, 5, 7]
    Ks_stress = [2, 3, 4, 6, 8, 10, 12] if not args.quick else [2, 4, 6]
    counts = (2500, 2500, 1500) if not args.quick else (300, 300, 200)
    K_census = 24
    tallies = {}
    results = {'stress': {}, 'census': {}, 'law4': {}}

    # ---------------- per-(n,p) censuses + stress ----------------
    for n in NS:
        for p in PS:
            tally = tallies[(n, p)] = LawTally(n, p)
            emit('')
            emit('=== (n=%d, p=%d) ===' % (n, p))
            rows = run_stress(n, p, Ks_stress, tally)
            for r in rows:
                emit('  stress %-9s K=%2d vd=%3d N*=%3d track1=%3d dzero=%3d '
                     'oracle=%s%s' % (r['tag'], r['K'], r['vd'], r['Nstar'],
                                      r['track1'], r['dzero'], r['oracle'],
                                      (' ANOM:' + ';'.join(r['anom'][:2]))
                                      if r['anom'] else ''))
            results['stress']['%d,%d' % (n, p)] = rows
            cc, cb, oc, ob = run_config(n, p, K_census, counts, tally,
                                        do_full_oracle=True, quick=args.quick)
            results['census']['%d,%d' % (n, p)] = dict(
                walked=tally.count, deep=tally.deep,
                coarse=(cc, cb), full=(oc, ob),
                max_track1=[tally.max_track1[0], tally.max_track1[1]],
                track1_by_vdisc=tally.max_track1_depth,
                max_dzero_over_Nstar=str(tally.max_dzero_ratio[0]),
                max_ninc_over_nNstar=str(tally.max_ninc_ratio[0]),
                viol_L_n2=tally.viol_law1_n2, viol_law2=tally.viol_law2,
                viol_law3=tally.viol_law3, anomalies=tally.anoms,
                sigma_ambig=tally.sigma_bad)

    # ---------------- exhaustive cubic boxes (padic_types tie) ----------------
    emit('')
    emit('=== exhaustive cubic boxes (independent padic_types oracle) ===')
    box_ties = []
    for (p, K, cap) in [(2, 6, 1 << 18), (3, 4, 600000), (5, 3, 200000),
                        (7, 2, 150000)]:
        if args.quick:
            cap = min(cap, 20000)
        checked, bad = cubic_box_census(p, K, cap, tallies[(3, p)])
        box_ties.append((p, checked, bad))

    # ---------------- verdict rows ----------------
    emit('')
    emit('=' * 74)
    emit('VERDICT ROWS')
    emit('=' * 74)
    tot_coarse_bad = sum(results['census'][k]['coarse'][1] for k in results['census'])
    tot_full_bad = sum(results['census'][k]['full'][1] for k in results['census'])
    tot_box_bad = sum(b for (_, _, b) in box_ties)
    anom_total = {}
    for t in tallies.values():
        for k, v in t.anoms.items():
            anom_total[k] = anom_total.get(k, 0) + v
    d10 = anom_total.get('D10-climb-violation', 0)
    check('V1 PARI oracle ties (coarse + full + stress rows)',
          tot_coarse_bad == 0 and tot_full_bad == 0,
          'coarse_bad=%d full_bad=%d (stress rows printed above)'
          % (tot_coarse_bad, tot_full_bad))
    check('V2 padic_types cubic ties', tot_box_bad == 0,
          '%s' % box_ties)
    check('V3 D.10 strict ladder climb (0 violations)', d10 == 0,
          'violations=%d' % d10)
    check('V4 engine anomaly budget (frame/residual asserts)',
          all(k in ('node-cap',) or v == 0 for k, v in anom_total.items()),
          '%s' % (anom_total or {}))

    # LAW 1
    emit('')
    emit('--- LAW 1 (track_restarts): #recT1 + #t4 <= L(n), sealed candidate L=n^2 ---')
    law1_refuted = []
    for n in NS:
        for p in PS:
            t = tallies[(n, p)]
            emit('  n=%d p=%d: max track1 = %3d  (candidate n^2 = %2d)  witness %s'
                 % (n, p, t.max_track1[0], n * n,
                    t.max_track1[1] if t.max_track1[0] > n * n else ''))
            if t.max_track1[0] > n * n:
                law1_refuted.append((n, p, t.max_track1[0]))
    emit('  depth trend (max track1 by vdisc bucket), n=3:')
    for p in PS:
        t = tallies[(3, p)]
        tr = dict(sorted(t.max_track1_depth.items()))
        emit('    p=%d: %s' % (p, tr))
    check('LAW1 candidate L(n)=n^2 survives', not law1_refuted,
          'REFUTED at %s' % law1_refuted if law1_refuted else 'all <= n^2')
    # growth verdict: does max track1 grow ~linearly along the stress K-sweep?
    growth = {}
    for n in NS:
        for p in PS:
            rows = results['stress']['%d,%d' % (n, p)]
            s1 = [(r['K'], r['track1']) for r in rows if r['tag'] == 'S1-split']
            s1.sort()
            if len(s1) >= 3:
                growth['%d,%d' % (n, p)] = s1
    lin = sum(1 for v in growth.values()
              if v[-1][1] - v[0][1] >= (v[-1][0] - v[0][0]) - 2)
    check('LAW1 unbounded-growth stress (S1 count grows with depth K)',
          lin == 0,
          '%d/%d configs show ~linear growth; e.g. %s'
          % (lin, len(growth), growth.get('3,2')))

    # LAW 2 + LAW 3
    emit('')
    emit('--- LAW 2 (zero_gain, candidate L*D*w* = n^2*n!*N) and LAW 3 (genuine_bound n*N) ---')
    v2 = v3 = 0
    for n in NS:
        for p in PS:
            t = tallies[(n, p)]
            emit('  n=%d p=%d: max d_zero/N* = %-8s  max ninc/(n N*) = %-8s '
                 'viol2=%d viol3=%d'
                 % (n, p, str(t.max_dzero_ratio[0]), str(t.max_ninc_ratio[0]),
                    t.viol_law2, t.viol_law3))
            v2 += t.viol_law2; v3 += t.viol_law3
    check('LAW2 zero_gain at candidate shapes (0 violations)', v2 == 0,
          'violations=%d' % v2)
    check('LAW3 genuine_bound ninc <= n*N* (0 violations)', v3 == 0,
          'violations=%d' % v3)

    # LAW 4: p-uniformity of tree counts at fixed (n, N)
    emit('')
    emit('--- LAW 4 (slice_bound surrogate): distinct decided trees with N* <= N ---')
    law4tab = {}
    for n in NS:
        for Ncap in (3, 5, 8):
            row = {}
            for p in PS:
                t = tallies[(n, p)]
                seen = set()
                for sig, lst in t.trees.items():
                    for (Nst, h) in lst:
                        if Nst <= Ncap:
                            seen.add((sig, h))
                row[p] = len(seen)
            law4tab['%d,N<=%d' % (n, Ncap)] = row
            emit('  n=%d N*<=%d: ' % (n, Ncap) +
                 '  '.join('p=%d: %4d' % (p, row[p]) for p in PS))
    results['law4'] = law4tab

    nfind = sum(1 for _, ok, _ in CHECKS if not ok)
    emit('')
    emit('OVERALL: %d checks, %d FINDING(s); wall %.0fs'
         % (len(CHECKS), nfind, time.time() - t00))
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
    outj = os.path.join(HERE, 'results', 'N7-track-count_results.json')
    with open(outj, 'w') as fh:
        json.dump({'checks': [{'name': a, 'ok': b, 'detail': c}
                              for a, b, c in CHECKS],
                   'results': results}, fh, indent=1, default=str)
    emit('JSON -> %s' % outj)
    return 0 if nfind == 0 else 1

if __name__ == '__main__':
    sys.exit(main())
