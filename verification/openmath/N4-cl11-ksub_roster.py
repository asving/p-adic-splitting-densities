#!/usr/bin/env python3
"""N4-cl11-ksub — numerical test of Conjecture M09 (BK.cl11_ksub at general n).

=============================================================================
THE LEAN STATEMENT BEING TESTED (fidelity anchor)
=============================================================================
DefsCarriers.lean:113 (MovesU), carried as the BridgeKernels/CapstoneLedger
ledger row `cl11_ksub : KsubM1C1T C.T` over the REAL pack `C : UCarriers n`:

  def KsubM1C1T {n : N} (T : MovesS.TableShape n) : Prop :=
    forall e in Icc 1 n, forall (tau : T.State e) (o : T.Out e tau),
      (forall mu in (T.odata e tau o).mem, mu.size = e) ->
      (T.odata e tau o).c != 0 ->
      (T.odata e tau o).m = 1 /\ (T.odata e tau o).c = 1

with (MovesS/Defs.lean:32-58)
  Member  = { size : N, delta : N+, status : VType + State size }
  Outcome = { mem : List Member, mem != [] }
  o.m = mem.length                       (row width)
  o.c = (mem.filter continuing).length   (continuing members; status = inr)
  routeOf o = if c = 0 then termFin else if m = 1 then kcol else split

Gloss (the row's own docstring): "equal-e CONTINUATION rides EXCLUSIVELY in
K_e's (c = 1, m = 1) rows" — an all-members-size-e outcome with a continuation
is a single-member single-continuation (kcol) row.  Same-size HALTS (c = 0)
stay exempt.  Instance-proved at n = 2 for the concrete table n2T
(SynK1_ksubN2.lean : ksubM1C1T_n2).  M09 = the same inclusion at the real
roster for general n; here tested at n = 3 and n = 4 (and n = 2 as a tie to
the proved instance).

=============================================================================
MAPPING Lean -> computation (what this script actually does)
=============================================================================
The real table at n >= 3 is NOT constructed in Lean.  Its intended semantics
(per the MOVESS blueprint sec 2.A and the validated density engine
verification/om_density_engine.py, whose beta_e recursion IS this table's
row content) is the depth-resummed Okutsu-Montes / root-cluster resolution
of monic degree-n polynomials over Z_p:

  * a STATE at block level e  = an undecided size-e root cluster (all e roots
    in one residue ball) at some depth, over its current frame;
  * an OUTCOME               = ONE resolution step: the Newton-polygon faces
    + residual factorizations of the recentered cluster polynomial;
  * a MEMBER                 = one (slope s = h/b, residual irreducible psi
    of degree D) group with total residual multiplicity mu:
      - mu = 1  : DECIDED  (status = verdict): frame verdict (e,f) = (b, D),
                  member size = b*D  (its root count in the current frame,
                  = its degree as a factor of the cluster polynomial; n2T
                  books decided members with size = frame degree, delta = 1);
      - mu >= 2 : CONTINUING (status = state): a child cluster of size mu
                  (root count over the base-changed frame), delta = D
                  (CONVENTION DELTA-ABS, Member docstring), ramified frame
                  factor b (b >= 2 only possible at n >= 4).
  * equal-e continuation = a continuing member of size mu = e, which forces
    b = D = 1 and the whole block descending one level (the K_e self-loop /
    kcol row: the o_K analogue of N2Shape.lean).

We reconstruct the ROSTER EMPIRICALLY: sample/enumerate actual monic integer
polynomials, obtain their true Q_p-irreducible factors from PARI factorpadic
(the repo's calibrated oracle, via the gp binary), and walk the cluster
resolution of each sample with EXACT integer arithmetic, recording every
outcome row (e, member list).  Then the Lean predicate, transcribed verbatim
below (outcome_m / outcome_c / route_of / ksub_check), is evaluated on every
observed row.

TRANSCRIBED LEAN DEFS (the roster check itself):
  outcome_m(mem)  = len(mem)
  outcome_c(mem)  = #continuing members
  route_of(mem)   = termFin / kcol / split by the (m,c) dispatch above
  KsubM1C1T check per observed row (e, mem):
      if all(size == e) and c != 0:  require m == 1 and c == 1.
We ALSO check the docstring's parenthetical equivalent reading (under
DEG-CONS): a row CONTAINING a size-e continuing member must be (m,c)=(1,1);
and DEG-CONS itself (C.hdc, Defs.lean:139): sizes >= 1, sum of sizes <= e.

=============================================================================
SIMPLIFICATIONS / DEVIATIONS (all flagged; see also FIDELITY VERDICT in log)
=============================================================================
S1. Observed roster is a SUBSET of the semantic roster: exhaustive small
    coefficient boxes + >=10^4 random/stratified samples per configuration;
    a numerical test can refute, or confirm-on-observed, never prove.
S2. States tau are not tracked beyond (frame, depth) context: KsubM1C1T
    quantifies over all (tau, o) and its premise/conclusion read only the
    member list, so collapsing tau loses nothing.
S3. The level-0 splitting of F mod p into residue points is booked as
    ENTRANCE data (EntShape side), not as an outcome row — matching the
    engine's FULLMONIC/cluster split and n2T (whose block layers have one
    state fed by the entrance side).  Cluster steps at every reached level
    e >= 2 ARE rows.  Size-1 pieces are decided at birth (verdict (1,1) in
    frame), so no e = 1 rows arise; the e = 1 layer of n2T is a terminal
    padding row with c = 0, KsubM1C1T-exempt either way.
S4. n = 4 EXOTIC children (continuing members with delta = D >= 2, i.e.
    cluster at a quadratic residue point, or ramified frame b = 2, i.e.
    mult->=2 residual on a fractional face): their BIRTH rows at the parent
    level ARE recorded and tested (that is where M09's novel content at
    n = 4 lives); their INTERNAL deeper rows (a size-2 cluster over an
    unramified-quadratic or ramified frame) are NOT reconstructed (would
    need extension-field arithmetic).  Those internal rows are n = 2-shape
    rows over a bigger frame; the n = 2 shape is instance-PROVED in Lean and
    empirically covered here over the rational frame.  Skips are counted.
S5. The engine consumes PARI's factorization (factor lifts mod p^PREC) as
    input, so factor DEGREES are not independent of the oracle; the (e,f)
    verdicts derived by the engine (products of face data (b, D) along each
    factor's path) ARE independent and are gated against PARI
    idealprimedec (Gate B, the repo's calibrated (e,f) method) on a large
    subsample.  All valuation reads guard against the p^PREC truncation
    (samples needing depth > PREC - MARGIN are discarded and counted).
S6. n2T itself is a CONSISTENCY DEVICE (N2Shape.lean R44), not the true
    arithmetic table: the true n = 2 roster observed here additionally
    contains the terminal ramified row [(V,(2,1))] (c = 0, exempt) which
    n2T folds elsewhere.  We report observed-n2-roster vs n2T for the tie.

ORACLE: PARI/GP 2.17.4 (`gp` binary), factorpadic at PREC digits + nfinit
[G,[p]] + idealprimedec — the identical method quartic_oracle.py calibrated
against 9 known cases (including Q_2(zeta_8) = (4,1)).  Calibration is
re-run here as Gate 0.

RUN:  PYTHONPATH=... python3 N4-cl11-ksub_roster.py [--smoke]
"""

import argparse
import ast
import os
import random
import subprocess
import sys
import tempfile
import time
from collections import defaultdict
from fractions import Fraction

GP = "/data/users/asvin/.local/bin/gp"
PREC = 80          # p-adic precision for factorpadic lifts
MARGIN = 8         # valuation reads must stay < PREC - MARGIN
MAX_STEPS = 400
INF = 10 ** 9

# =========================================================================
# Lean transcription (MovesS/Defs.lean:47-58 + DefsCarriers.lean:113).
# A member is a tuple:
#   ('V', size, b, D)      decided:   status = inl verdict, frame verdict (b,D)
#   ('C', size, delta, b)  continuing: status = inr (state at level `size`)
# =========================================================================

def is_continuing(mu):
    return mu[0] == 'C'


def outcome_m(mem):
    """Outcome.m = mem.length"""
    return len(mem)


def outcome_c(mem):
    """Outcome.c = (mem.filter continuing).length"""
    return sum(1 for mu in mem if is_continuing(mu))


def route_of(mem):
    """routeOf: if c = 0 then termFin else if m = 1 then kcol else split"""
    if outcome_c(mem) == 0:
        return 'termFin'
    if outcome_m(mem) == 1:
        return 'kcol'
    return 'split'


def ksub_violation(e, mem):
    """KsubM1C1T premise/conclusion at one row (the ALL-size-e Lean form).
    Returns True iff the row VIOLATES the conjecture."""
    if all(mu[1] == e for mu in mem) and outcome_c(mem) != 0:
        return not (outcome_m(mem) == 1 and outcome_c(mem) == 1)
    return False


def ksub_exists_violation(e, mem):
    """The docstring's DEG-CONS-equivalent exists-a-size-e reading."""
    if any(mu[1] == e and is_continuing(mu) for mu in mem):
        return not (outcome_m(mem) == 1 and outcome_c(mem) == 1)
    return False


def degcons_violation(e, mem):
    """DEG-CONS (Defs.lean:139): all sizes >= 1 and sum of sizes <= e."""
    return any(mu[1] < 1 for mu in mem) or sum(mu[1] for mu in mem) > e


# =========================================================================
# Exact integer / F_p polynomial helpers.  Polys are tuples low->high.
# =========================================================================

def vp(x, p):
    if x == 0:
        return INF
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def poly_shift(coeffs, c):
    """g(x) -> g(c + Y) exactly, coeffs low->high (synthetic Taylor shift)."""
    a = list(coeffs)
    n = len(a) - 1
    for i in range(n):            # repeated synthetic division by (Y - (-c))
        for j in range(n - 1, i - 1, -1):
            a[j] = a[j] + c * a[j + 1]
    return tuple(a)


def fp_normalize(coeffs, p):
    a = [c % p for c in coeffs]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a)


def fp_divmod(num, den, p):
    num = list(num)
    dn, dd = len(num) - 1, len(den) - 1
    inv = pow(den[-1], p - 2, p) if den[-1] != 1 else 1
    q = [0] * (dn - dd + 1)
    for k in range(dn - dd, -1, -1):
        coef = (num[dd + k] * inv) % p
        q[k] = coef
        if coef:
            for j in range(dd + 1):
                num[k + j] = (num[k + j] - coef * den[j]) % p
    r = fp_normalize(num[:dd] if dd > 0 else [0], p)
    return tuple(q), r


def fp_eval(coeffs, x, p):
    acc = 0
    for c in reversed(coeffs):
        acc = (acc * x + c) % p
    return acc


def fp_factor_monic(coeffs, p):
    """Factor a monic poly over F_p, deg <= 4 (p small): {irred_tuple: mult}."""
    f = fp_normalize(coeffs, p)
    assert f[-1] == 1, f
    out = defaultdict(int)
    # strip roots
    for r in range(p):
        while len(f) > 1 and fp_eval(f, r, p) == 0:
            f, rem = fp_divmod(f, ((-r) % p, 1), p)
            assert rem == (0,)
            out[((-r) % p, 1)] += 1
            if len(f) == 1:
                break
    d = len(f) - 1
    if d == 0:
        return dict(out)
    if d in (2, 3):               # no roots -> deg 2,3 irreducible
        out[f] += 1
        return dict(out)
    assert d == 4
    for b0 in range(p):           # rootless quartic: probe irreducible quadratics
        for b1 in range(p):
            qd = (b0, b1, 1)
            if any(fp_eval(qd, r, p) == 0 for r in range(p)):
                continue
            quo, rem = fp_divmod(f, qd, p)
            if rem == (0,):
                out[qd] += 1
                out[fp_normalize(quo, p)] += 1
                return dict(out)
    out[f] += 1
    return dict(out)


def fp_root_of_linear(psi, p):
    """psi = (c0, 1) = z + c0 -> root -c0."""
    return (-psi[0]) % p


# =========================================================================
# GP oracle plumbing
# =========================================================================

def run_gp(script, timeout=600):
    with tempfile.NamedTemporaryFile('w', suffix='.gp', delete=False) as f:
        f.write(script)
        path = f.name
    try:
        res = subprocess.run([GP, '-q', '-f'], stdin=open(path),
                             capture_output=True, text=True, timeout=timeout)
        if res.returncode != 0:
            raise RuntimeError(f"gp failed: {res.stderr[:500]}")
        return res.stdout
    finally:
        os.unlink(path)


def gp_factor_batch(polys, p, prec=PREC):
    """polys: list of coeff tuples low->high (monic).  Returns per poly a list
    of (factor_coeffs_low_to_high_ints, exponent)."""
    out = [None] * len(polys)
    B = 4000
    for lo in range(0, len(polys), B):
        chunk = polys[lo:lo + B]
        data = "[" + ",".join(
            "[" + ",".join(str(c) for c in reversed(cs)) + "]" for cs in chunk) + "]"
        script = (f"default(parisize, 268435456);\n"
                  f"p = {p}; prec = {prec};\nV = {data};\n"
                  "{for(i = 1, #V,\n"
                  "  my(F = Pol(V[i]));\n"
                  "  my(fa = factorpadic(F, p, prec));\n"
                  "  my(out = vector(matsize(fa)[1]));\n"
                  "  for(k = 1, matsize(fa)[1],\n"
                  "    out[k] = [Vec(liftall(fa[k,1])), fa[k,2]]);\n"
                  "  print(i, \"|\", out);\n"
                  ");}\nquit;\n")
        txt = run_gp(script)
        for line in txt.splitlines():
            line = line.strip()
            if '|' not in line or line.startswith('*'):
                continue
            idx, rest = line.split('|', 1)
            parsed = ast.literal_eval(rest.replace(' ', ''))
            fac = [(tuple(reversed(f[0])), f[1]) for f in parsed]
            out[lo + int(idx) - 1] = fac
    assert all(v is not None for v in out)
    return out


def gp_ef_batch(factors, p):
    """factors: list of coeff tuples (low->high, monic, deg>=2, Q_p-irreducible
    lifts).  Returns list of (e, f) via nfinit[G,[p]] + idealprimedec — the
    quartic_oracle.py method."""
    out = [None] * len(factors)
    B = 1500
    for lo in range(0, len(factors), B):
        chunk = factors[lo:lo + B]
        data = "[" + ",".join(
            "[" + ",".join(str(c) for c in reversed(cs)) + "]" for cs in chunk) + "]"
        script = (f"default(parisize, 268435456);\np = {p};\nD = {data};\n"
                  "{for(i = 1, #D,\n"
                  "  my(L = Pol(D[i]));\n"
                  "  my(d = poldegree(L));\n"
                  "  my(ef = [0,0]);\n"
                  "  my(nf = nfinit([L,[p]]));\n"
                  "  my(dec = idealprimedec(nf,p));\n"
                  "  for(k=1,#dec, if(dec[k].e*dec[k].f == d, ef=[dec[k].e,dec[k].f]));\n"
                  "  if(ef==[0,0], ef=[dec[1].e, dec[1].f]);\n"
                  "  print(i, \"|\", ef);\n"
                  ");}\nquit;\n")
        txt = run_gp(script)
        for line in txt.splitlines():
            line = line.strip()
            if '|' not in line or line.startswith('*'):
                continue
            idx, rest = line.split('|', 1)
            ef = ast.literal_eval(rest.replace(' ', ''))
            out[lo + int(idx) - 1] = (ef[0], ef[1])
    assert all(v is not None for v in out)
    return out


# =========================================================================
# The cluster-resolution engine (exact integer arithmetic on factor lifts)
# =========================================================================

class Deep(Exception):
    """valuation read too close to the p^PREC truncation -> discard sample"""


class EngineError(Exception):
    """internal Gate-A failure -> would be a FIDELITY bug, aborts the run"""


class Resolver:
    """Resolves one sample; factors = [(coeffs low->high, degree)]."""

    def __init__(self, p, factors, rows_sink, ctx):
        self.p = p
        self.factors = factors
        self.rows = rows_sink          # dict row_key -> [count, example]
        self.ctx = ctx                 # (n, p, coeffs) for examples
        self.derived_ef = {}           # factor index -> engine (e,f)
        self.skipped_exotic = []       # factor indices inside skipped children
        self.exotic_child_rows = 0
        self.exotic_entrance = 0
        self.steps = 0

    def emit(self, e, members, depth):
        key = (e, tuple(sorted(members)))
        slot = self.rows.get(key)
        if slot is None:
            self.rows[key] = [1, (self.ctx, depth)]
        else:
            slot[0] += 1

    # ---- one cluster step ------------------------------------------------
    def step(self, idxs, C, H, depth):
        """Cluster = factor indices idxs, center C (int), depth H (int, all
        roots x of the cluster's factors satisfy v(x - C) > H)."""
        p = self.p
        self.steps += 1
        if self.steps > MAX_STEPS:
            raise Deep("max steps")
        e_size = sum(self.factors[i][1] for i in idxs)
        groups = defaultdict(list)     # (s: Fraction, psi) -> [(i, mult mu_i)]
        for i in idxs:
            cs, d = self.factors[i]
            gC = 0
            for c in reversed(cs):
                gC = gC * C + c
            val = vp(gC, p)
            if val >= PREC - MARGIN:
                raise Deep("v(g(C)) too deep")
            s = Fraction(val, d)
            if s <= H:
                raise EngineError(f"cluster invariant broken: s={s} <= H={H}")
            b = s.denominator
            A = poly_shift(cs, C)      # g(C + Y), integer coeffs low->high
            # residual poly on the (single, slope-s) face of g(C+Y):
            # support j = d - k*b, coefficient A_j / p^{s*(d-j)} mod p
            rdeg = d // b
            R = [0] * (rdeg + 1)
            for j in range(d + 1):
                need = s * (d - j)
                if need.denominator == 1:
                    ex = int(need)
                    if ex >= PREC - MARGIN and A[j] != 0 and vp(A[j], p) < ex:
                        raise Deep("NP line read too deep")
                    if A[j] != 0:
                        v = vp(A[j], p)
                        if v < ex:
                            raise EngineError("point below NP line (not a face)")
                        if v == ex:
                            # b | (d-j) iff `need` integral; b | d, so b | j
                            R[j // b] = (A[j] // p ** ex) % p
                else:
                    if A[j] != 0 and vp(A[j], p) * 1 < need:
                        raise EngineError("fractional-line breach")
            # NB for b == 1 index j//1 == j; formula above collapses correctly.
            R = fp_normalize(tuple(R), p)
            if len(R) - 1 != rdeg or R[-1] != 1:
                raise EngineError(f"residual not monic of degree {rdeg}: {R}")
            if R[0] == 0:
                raise EngineError("residual has zero constant term")
            fac = fp_factor_monic(R, p)
            if len(fac) != 1:
                raise EngineError(f"residual of irreducible factor not a prime power: {fac}")
            (psi, mu_i), = fac.items()
            groups[(s, psi)].append((i, mu_i))
        # build members
        members = []
        recurse = []
        deg_total = 0
        for (s, psi), lst in sorted(groups.items()):
            b = s.denominator
            D = len(psi) - 1
            mu = sum(m for _, m in lst)
            deg_total += mu * b * D
            if mu == 1:
                (i, _), = lst
                members.append(('V', b * D, b, D))
                self.derived_ef[i] = (b, D)
            else:
                members.append(('C', mu, D, b))
                if D == 1 and b == 1:
                    r = fp_root_of_linear(psi, p)
                    ex = int(s)
                    C2 = C + r * p ** ex
                    recurse.append(([i for i, _ in lst], C2, ex))
                else:
                    self.skipped_exotic.extend(i for i, _ in lst)
                    self.exotic_child_rows += 1
        if deg_total != e_size:
            raise EngineError(f"degree bookkeeping broken: {deg_total} != {e_size}")
        self.emit(e_size, members, depth)
        for sub, C2, H2 in recurse:
            self.step(sub, C2, H2, depth + 1)

    # ---- entrance (level 0; booked as EntShape data, not a row: S3) ------
    def run(self):
        p = self.p
        groups = defaultdict(list)
        for i, (cs, d) in enumerate(self.factors):
            fac = fp_factor_monic(cs, p)
            if len(fac) != 1:
                raise EngineError("level-0 reduction of irreducible factor not a prime power")
            (psi, mu_i), = fac.items()
            groups[psi].append((i, mu_i))
        for psi, lst in groups.items():
            D = len(psi) - 1
            mu = sum(m for _, m in lst)
            if mu == 1:
                (i, _), = lst
                self.derived_ef[i] = (1, D)      # simple residue point: unramified
            elif D == 1:
                r = fp_root_of_linear(psi, p)
                self.step([i for i, _ in lst], r, 0, 1)
            else:
                self.skipped_exotic.extend(i for i, _ in lst)
                self.exotic_entrance += 1


# =========================================================================
# Samplers (all produce EXACT monic integer polynomials, coeffs low->high)
# =========================================================================

def sampler_exhaustive(n, p, m):
    box = p ** m
    if n == 2:
        return [(a0, a1, 1) for a1 in range(box) for a0 in range(box)]
    if n == 3:
        return [(a0, a1, a2, 1) for a2 in range(box)
                for a1 in range(box) for a0 in range(box)]
    raise ValueError


def sampler_random(n, p, count, rng, depth=12):
    box = p ** depth
    return [tuple(rng.randrange(box) for _ in range(n)) + (1,)
            for _ in range(count)]


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return tuple(out)


def sampler_stratified(n, p, count, rng):
    """Deep-cluster strata: forces long kcol chains, multi-face rows and (at
    n = 4) the exotic children.  All exact integer polys."""
    out = []
    box = p ** 4
    for _ in range(count):
        kind = rng.randrange(6)
        j = rng.randrange(1, 9)
        c = rng.randrange(p ** 2)
        noise = tuple(rng.randrange(box) for _ in range(n)) + (0,)
        if kind == 0:                                   # (x-c)^n + p^j * G
            base = (1,)
            for _ in range(n):
                base = poly_mul(base, (-c, 1))
        elif kind == 1 and n >= 3:                      # (x-c)^(n-1)(x-c') + p^j G
            c2 = rng.randrange(p ** 2)
            base = (-c2, 1)
            for _ in range(n - 1):
                base = poly_mul(base, (-c, 1))
        elif kind == 2 and n == 4:                      # (x-c)^2(x-c')^2 + p^j G
            c2 = rng.randrange(p ** 2)
            base = poly_mul(poly_mul((-c, 1), (-c, 1)),
                            poly_mul((-c2, 1), (-c2, 1)))
        elif kind == 3 and n == 4:                      # psi(x)^2 + p^j G, psi irred quad
            while True:
                b0, b1 = rng.randrange(p), rng.randrange(p)
                if all(fp_eval((b0, b1, 1), r, p) != 0 for r in range(p)):
                    break
            base = poly_mul((b0, b1, 1), (b0, b1, 1))   # -> delta=2 exotic child
        elif kind == 4 and n == 4:                      # (x^2 - c p^a)^2 + p^{2a+j} G
            a = rng.choice([1, 3])
            cc = rng.randrange(1, p)
            base = poly_mul((-cc * p ** a, 0, 1), (-cc * p ** a, 0, 1))
            j = 2 * a + rng.randrange(1, 4)             # -> b=2 ramified exotic child
        else:                                           # Eisenstein-ish deep
            base = tuple(0 for _ in range(n)) + (1,)
            noise = tuple(rng.randrange(1, box) if i == 0 else rng.randrange(box)
                          for i in range(n)) + (0,)
        F = tuple(bc + p ** j * nc for bc, nc in zip(base, noise))
        assert len(F) == n + 1 and F[-1] == 1
        out.append(F)
    return out


# =========================================================================
# Config runner
# =========================================================================

def run_config(n, p, polys, rows, stats, gate_b_budget, label):
    t0 = time.time()
    fax = gp_factor_batch(polys, p)
    stats['gp_factor_s'] += time.time() - t0
    gate_b_pool = []                 # (factor_coeffs, derived_ef, sample_idx)
    for si, (F, fac) in enumerate(zip(polys, fax)):
        if any(mult > 1 for _, mult in fac):
            stats['skip_nonsqfree'] += 1
            continue
        factors = [(cs, len(cs) - 1) for cs, _ in fac]
        if sum(d for _, d in factors) != n:
            raise EngineError("factor degrees don't sum to n")
        R = Resolver(p, factors, rows, (n, p, F))
        try:
            R.run()
        except Deep:
            stats['skip_deep'] += 1
            continue
        stats['samples'] += 1
        stats['exotic_child'] += R.exotic_child_rows
        stats['exotic_entrance'] += R.exotic_entrance
        # every factor must be accounted for: decided leaf XOR skipped exotic
        if len(R.derived_ef) + len(R.skipped_exotic) != len(factors):
            raise EngineError("factor accounting broken")
        # Gate A' : every decided factor got a verdict consistent with degree
        for i, ef in R.derived_ef.items():
            if ef[0] * ef[1] != factors[i][1]:
                raise EngineError(f"derived ef {ef} vs degree {factors[i][1]}")
            if factors[i][1] >= 2:
                gate_b_pool.append((factors[i][0], ef))
        for i in R.skipped_exotic:
            stats['skipped_factors'] += 1
    # Gate B on a subsample
    if gate_b_pool:
        rng = random.Random(1234)
        take = gate_b_pool if len(gate_b_pool) <= gate_b_budget else \
            rng.sample(gate_b_pool, gate_b_budget)
        t0 = time.time()
        efs = gp_ef_batch([t[0] for t in take], p)
        stats['gp_ef_s'] += time.time() - t0
        for (cs, ef_engine), ef_oracle in zip(take, efs):
            stats['gateB'] += 1
            if ef_engine != ef_oracle:
                stats['gateB_fail'] += 1
                print(f"    !! GATE B MISMATCH ({label}): factor {cs} "
                      f"engine {ef_engine} oracle {ef_oracle}")


def gate0_calibration():
    """quartic_oracle.py's 9 calibration cases through our gp plumbing."""
    cal = [(( 4, 0, 0, 0, 1), 2, ((4, 1),)),          # x^4+4 factors! see below
           ((-2, 0, 0, 0, 1), 2, ((4, 1),)),          # x^4-2 tot ram
           (( 1, 0, 0, 0, 1), 2, ((4, 1),)),          # x^4+1: Q_2(zeta_8) tot ram
           ((-2, 0, 1), 2, ((2, 1),)),                # x^2-2
           ((-5, 0, 1), 2, ((1, 2),)),                # x^2-5
           ((-2, 0, 0, 1), 3, ((3, 1),)),             # x^3-2 over Q_3
           ((-3, 0, 1), 3, ((2, 1),))]                # x^2-3
    ok = True
    for cs, p, expected in cal:
        fac = gp_factor_batch([cs], p)[0]
        types = []
        for f, mult in fac:
            assert mult == 1
            d = len(f) - 1
            if d == 1:
                types.append((1, 1))
            else:
                types.append(gp_ef_batch([f], p)[0])
        got = tuple(sorted(types))
        # x^4+4 = (x^2-2x+2)(x^2+2x+2): two ramified quadratics
        exp = expected if cs != (4, 0, 0, 0, 1) else ((2, 1), (2, 1))
        if got != exp:
            print(f"  GATE 0 FAIL: {cs} /Q_{p}: got {got} expected {exp}")
            ok = False
        else:
            print(f"  gate0 ok: {cs} /Q_{p} -> {got}")
    return ok


# =========================================================================
# main
# =========================================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--smoke', action='store_true')
    args = ap.parse_args()
    rng = random.Random(20260731)
    sm = 20 if args.smoke else 1

    print("=" * 78)
    print("N4-cl11-ksub: Conjecture M09 (BK.cl11_ksub at general n)")
    print("KsubM1C1T at the empirically reconstructed real roster, n = 2, 3, 4")
    print("=" * 78)

    print("\n[GATE 0] oracle calibration (quartic_oracle.py cases via gp):")
    if not gate0_calibration():
        print("ORACLE CALIBRATION FAILED — aborting")
        sys.exit(1)

    configs = []
    # n = 2 (tie to the Lean-proved instance)
    configs.append((2, 2, 'exh m=6', sampler_exhaustive(2, 2, 6)))
    configs.append((2, 3, 'exh m=4', sampler_exhaustive(2, 3, 4)))
    configs.append((2, 2, 'strat',   sampler_stratified(2, 2, 6000 // sm, rng)))
    configs.append((2, 5, 'rand',    sampler_random(2, 5, 5000 // sm, rng)))
    # n = 3 (the unit's target; wild p = 2, 3 preferential)
    configs.append((3, 2, 'exh m=4', sampler_exhaustive(3, 2, 4)))
    configs.append((3, 3, 'exh m=3', sampler_exhaustive(3, 3, 3)))
    configs.append((3, 5, 'exh m=2', sampler_exhaustive(3, 5, 2)))
    configs.append((3, 2, 'rand',    sampler_random(3, 2, 12000 // sm, rng)))
    configs.append((3, 3, 'rand',    sampler_random(3, 3, 12000 // sm, rng)))
    configs.append((3, 2, 'strat',   sampler_stratified(3, 2, 12000 // sm, rng)))
    configs.append((3, 3, 'strat',   sampler_stratified(3, 3, 12000 // sm, rng)))
    configs.append((3, 5, 'strat',   sampler_stratified(3, 5, 6000 // sm, rng)))
    configs.append((3, 7, 'rand',    sampler_random(3, 7, 6000 // sm, rng)))
    # n = 4 ("if cheap" — it is; wild p = 2, 3 preferential)
    configs.append((4, 2, 'rand',    sampler_random(4, 2, 12000 // sm, rng)))
    configs.append((4, 3, 'rand',    sampler_random(4, 3, 10000 // sm, rng)))
    configs.append((4, 2, 'strat',   sampler_stratified(4, 2, 14000 // sm, rng)))
    configs.append((4, 3, 'strat',   sampler_stratified(4, 3, 12000 // sm, rng)))
    configs.append((4, 5, 'rand',    sampler_random(4, 5, 5000 // sm, rng)))
    configs.append((4, 5, 'strat',   sampler_stratified(4, 5, 5000 // sm, rng)))

    rosters = {}                    # n -> rows dict
    per_config = []
    for n, p, tag, polys in configs:
        rows = rosters.setdefault(n, {})
        stats = defaultdict(float)
        label = f"n={n} p={p} {tag}"
        run_config(n, p, polys, rows, stats,
                   gate_b_budget=(2000 // sm + 10), label=label)
        per_config.append((label, len(polys), dict(stats)))
        print(f"[config] {label:22s} polys={len(polys):6d} "
              f"resolved={int(stats['samples']):6d} "
              f"skip(sqfree/deep)={int(stats['skip_nonsqfree'])}/{int(stats['skip_deep'])} "
              f"gateB={int(stats['gateB'])} fail={int(stats['gateB_fail'])} "
              f"exotic(child/entr)={int(stats['exotic_child'])}/{int(stats['exotic_entrance'])} "
              f"gp={stats['gp_factor_s']:.1f}+{stats['gp_ef_s']:.1f}s")
        if stats['gateB_fail']:
            print("ORACLE GATE B FAILED — engine unfaithful, aborting")
            sys.exit(1)

    # =====================================================================
    # THE TEST: Lean-transcribed checks over every observed roster row
    # =====================================================================
    print("\n" + "=" * 78)
    print("RECONSTRUCTED ROSTERS + KsubM1C1T / DEG-CONS row checks")
    print("=" * 78)
    total_viol = total_viol_ex = total_dc = 0
    kcol_summary = []
    for n in sorted(rosters):
        rows = rosters[n]
        print(f"\n--- n = {n}: {len(rows)} distinct observed rows, "
              f"{sum(v[0] for v in rows.values())} row instances ---")
        print(f"{'e':>2} {'route':8s} {'m':>2} {'c':>2} {'members':46s} "
              f"{'count':>8s}  ksub ksub-ex degc")
        for (e, mem), (count, example) in sorted(
                rows.items(), key=lambda kv: (kv[0][0], -kv[1][0])):
            v1 = ksub_violation(e, list(mem))
            v2 = ksub_exists_violation(e, list(mem))
            v3 = degcons_violation(e, list(mem))
            total_viol += v1
            total_viol_ex += v2
            total_dc += v3
            mark = lambda b: "VIOL" if b else "ok"
            memstr = " ".join(
                (f"C(sz{m[1]},dlt{m[2]},b{m[3]})" if m[0] == 'C'
                 else f"V(sz{m[1]},ef({m[2]},{m[3]}))") for m in mem)
            print(f"{e:>2} {route_of(list(mem)):8s} {outcome_m(list(mem)):>2} "
                  f"{outcome_c(list(mem)):>2} {memstr:46s} {count:>8d}  "
                  f"{mark(v1):4s} {mark(v2):7s} {mark(v3):4s}")
            if v1 or v2 or v3:
                print(f"      COUNTEREXAMPLE sample: {example}")
            if route_of(list(mem)) == 'kcol':
                kcol_summary.append((n, e, mem, count))

    # ---- K-matrix roster (the kcol rows) + the neighboring KmatHyp look
    print("\n--- K-matrix roster slice (all kcol-routed rows observed) ---")
    print("(KsubM1C1T governs the equal-e ones; member size < e rows are the")
    print(" delta>1 / ramified-frame legs — they concern the SEPARATE hK row")
    print(" (KmatHyp), reported here as neighboring observation only)")
    kmat_full_size = kmat_sub_size = 0
    for n, e, mem, count in sorted(kcol_summary):
        m0 = mem[0]
        eq = "EQUAL-e (K_e self-loop)" if m0[1] == e else \
             f"size {m0[1]} < e  [KmatHyp-relevant, delta={m0[2]}, b={m0[3]}]"
        if m0[1] == e:
            kmat_full_size += count
        else:
            kmat_sub_size += count
        print(f"  n={n} e={e}: {m0}  x{count}   {eq}")

    print("\n" + "=" * 78)
    n_rows = sum(len(r) for r in rosters.values())
    n_inst = sum(v[0] for r in rosters.values() for v in r.values())
    print(f"TOTALS: {n_rows} distinct rows / {n_inst} row instances")
    print(f"KsubM1C1T (all-size-e form)  violations: {total_viol}")
    print(f"KsubM1C1T (exists-size-e eq) violations: {total_viol_ex}")
    print(f"DEG-CONS                     violations: {total_dc}")
    print(f"kcol rows: equal-e {kmat_full_size} instances; "
          f"sub-size (KmatHyp-relevant, n=4 legs) {kmat_sub_size} instances")
    verdict = "CONFIRMED (no violation on observed roster)" \
        if total_viol == 0 and total_viol_ex == 0 and total_dc == 0 else "REFUTED"
    print(f"VERDICT over observed rosters: {verdict}")
    print("=" * 78)


if __name__ == '__main__':
    main()
