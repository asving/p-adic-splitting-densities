#!/usr/bin/env python3
"""l1_boundary_enum.py — PROBE-6: D4R.0-K part (a) BOUNDARY ENUMERATION for L1
(canonical-choice totality of the offset-P-lift).

KERNEL WARRANT (quoted). MOVES_2026-07-24.md, §D4-R.0 L1 (lines 4653-4671):
  "The offset-P-lift is DEFINED at every eligible recentering: whenever the
   classifier consumes a recentering side (e_read = 1) with value nu and
   prescribed residual class, nu lies strictly above the (S6b) threshold
   w(Phi-hat) (I-aug at the read), and the offset-P formula returns a realizer
   t with w(t) = nu and the prescribed class — for EVERY class (the offset
   choice of j0 removes (S6b)'s zero-class restriction), including the
   boundary cases: minimal eligible nu, g = 1 (single slot), a > 0 anchors.
   ... [OPEN — kernel D4R.0-K part (a); its fresh-context boundary enumeration
   is the kernel's part (a)]"
FORMULA SOURCE. §B2-DEF (S6b') (lines 2436-2455) + pass-11 finding 1 repair
(lines 2893-2900): j0 := h^{-1}·W mod e (the forced slot class); slots
j0, j0+e, ..., j0+(g-1)e <= eg-1; t := Sigma_{P_k != 0} t_k·Phi_prev^{j0+e k};
summand parent-scale weights (W - (j0+ek)h)/e, all zero-class by the choice of
j0, all clearing the lower threshold when W > ehg (clean threshold w_prev(Phi));
P in F_prev[z] the unique deg < g representative of the target class (the
forced offset z^m is a generator convention — see CONVENTION below); the
recursion bottoms at the base, "where digits are F_Q-unit lifts with no
threshold"; two-line mutual recursion: each summand weight
>= (W - (eg-1)h)/e > h/e > w_prevprev(Phi_prev) by (I-aug) h > e·w_prev(Phi).

MODEL (concrete, exact integer arithmetic — no truncation).
  Stage 2 (recursion bottoms immediately): base key Phi_1 = x over Q_p;
  stage-1 side data (e, h, g), gcd(e,h) = 1, psi monic irreducible of degree g
  over F_p with psi(0) != 0; current field F' = F_p[z]/(psi); coefficient
  space C = {t in Z[x] : deg t < eg}; parent-scale weight
  w(t) := min_j (e·v_p(t_j) + j·h); clean threshold w_prev(Phi_2) = ehg.
  Stage 3 (one genuine recursion step): stage-2 data (e2, h2, g2, psi_2) on
  top, psi_2 monic irreducible over F_2 := F', psi_2(0) != 0, h2 chosen
  > e2·(e1 h1 g1) per (I-aug); Phi_2 = the standard Ore lift
  x^{e1 g1} + Sigma_k lift(c_k)·p^{h1(g1-k)}·x^{e1 k}; stage-3 weight
  w2(t) := min_j (e2·w1(B_j) + j·h2) over the Phi_2-development t = Sigma B_j
  Phi_2^j; threshold e2 h2 g2; the summands t_k are realized by the STAGE-2
  offset-P formula (the recursion), guarded by u_k > e1 h1 g1.

CONVENTION (digit map) + INVARIANCE. dig(t) is read relative to the slot-j0
monomial generator: the k-th residual coefficient is
res(t_{j0+ek}/p^{(W-(j0+ek)h)/e}), the class is the resulting deg < g
polynomial mod psi (so the note's forced offset m is absorbed: m = 0 here).
The note's own digit may differ by slot-unit twists that are FUNCTIONS OF
NODE DATA only; any such twist is a data-determined bijection of nonzero
classes, so the checked statement — exact weight W, from-scratch reading =
the prescribed class, ALL classes covered at EVERY eligible W (bijectivity),
deterministic construction — implies L1's totality under the note's
convention as well. Convention risk is confined to WHICH class gets which
realizer, never to totality/weight/determinism.

WHAT A FINDING WOULD BE (refutes L1 totality): an enumerated boundary case
where the formula is PARTIAL (slot out of range / summand weight negative or
not zero-class / recursion guard u_k <= e1h1g1 trips at an eligible W3), or
where the independently recomputed realizer weight != W, or the minimizing
slots leave the forced class j0 mod e, or the recomputed residual class
misses the prescribed target, or some class in F'^x is NOT covered.

BOUNDARY CASES ENUMERATED (the L1 list, by name):
  (min-nu)  W = ehg + 1, ..., ehg + 2e — the minimal eligible weight and the
            minimal occurrence of EVERY forced slot class j0 in [0, e).
  (g = 1)   single-slot configs at both stages (incl. F'^x = {1} at p = 2).
  (a > 0)   anchored targets tau = zbar^a · u (a in {1,2}, u in F'^x) — the
            classes fed by recenterings inside anchored strata (Case-J /
            D.8 anchor bookkeeping); tallied explicitly.
  (j0 > 0)  the offset genuinely engaged (the pass-11 repair's new reach);
            tallied explicitly.
SCOPE FENCE (honesty). This is a FORMULA-LEVEL totality enumeration over the
displayed boundary grid; L1's quantifier "every eligible node of every
realizable prefix" is not exhausted by any finite enumeration — the gate
SUPPORTS the kernel part (a), it cannot prove it (L1 stays OPEN).

Exit 0 = PASS (all cases), 1 = FINDING.  Run: python3 l1_boundary_enum.py
"""
import sys
from itertools import product
from math import gcd

# ---------------------------------------------------------------- field towers
class Fp:
    """Prime field F_p. Elements: ints in [0, p)."""
    def __init__(self, p):
        self.p = p
        self.zero, self.one = 0, 1
    def add(self, a, b): return (a + b) % self.p
    def sub(self, a, b): return (a - b) % self.p
    def mul(self, a, b): return (a * b) % self.p
    def neg(self, a): return (-a) % self.p
    def elements(self): return list(range(self.p))
    def size(self): return self.p

class Ext:
    """Extension B[z]/(mod), mod monic of degree g over base field B.
    Elements: tuples of B-elements, length g (low -> high)."""
    def __init__(self, B, mod):
        self.B, self.mod = B, mod          # mod: list of B-elts, len g+1, monic
        self.g = len(mod) - 1
        self.zero = tuple([B.zero] * self.g)
        self.one = tuple([B.one] + [B.zero] * (self.g - 1)) if self.g >= 1 else ()
        if self.g >= 2:
            self.zbar = tuple([B.zero, B.one] + [B.zero] * (self.g - 2))
        else:                               # F'[z]/(z + c0): zbar = -c0
            self.zbar = (B.neg(mod[0]),)
    def add(self, a, b): return tuple(self.B.add(x, y) for x, y in zip(a, b))
    def sub(self, a, b): return tuple(self.B.sub(x, y) for x, y in zip(a, b))
    def neg(self, a): return tuple(self.B.neg(x) for x in a)
    def mul(self, a, b):
        B, g = self.B, self.g
        prod = [B.zero] * (2 * g - 1) if g >= 1 else []
        for i, x in enumerate(a):
            if x == B.zero: continue
            for j, y in enumerate(b):
                prod[i + j] = B.add(prod[i + j], B.mul(x, y))
        for d in range(len(prod) - 1, g - 1, -1):   # reduce (mod monic)
            c = prod[d]
            if c == B.zero: continue
            prod[d] = B.zero
            for k in range(self.g + 1 - 1):
                prod[d - self.g + k] = B.sub(prod[d - self.g + k],
                                             B.mul(c, self.mod[k]))
        return tuple(prod[:g])
    def pow(self, a, n):
        r = self.one
        while n:
            if n & 1: r = self.mul(r, a)
            a = self.mul(a, a); n >>= 1
        return r
    def elements(self):
        return [tuple(t) for t in product(self.B.elements(), repeat=self.g)]
    def units(self): return [x for x in self.elements() if x != self.zero]
    def size(self):
        s = self.B.size() ** self.g
        return s

def irreducibles(B, g, nonzero_const=True, cap=4):
    """Monic irreducible degree-g polys over field B (g <= 2 complete via
    root test; g = 3 via root test, valid over any field for deg 3)."""
    assert g <= 3
    out = []
    for tail in product(B.elements(), repeat=g):
        mod = list(tail) + [B.one]
        if nonzero_const and mod[0] == B.zero: continue
        if g == 1:
            out.append(mod)
            if len(out) >= cap: break
            continue
        has_root = False                   # cheap root test: eval at all elts
        for x in B.elements():
            acc, xp = B.zero, B.one
            for c in mod:
                acc = B.add(acc, B.mul(c, xp)); xp = B.mul(xp, x)
            if acc == B.zero: has_root = True; break
        if not has_root: out.append(mod)
        if len(out) >= cap: break
    return out

# ---------------------------------------------------------------- Z[x] helpers
def vp(n, p):
    assert n != 0
    v = 0
    while n % p == 0: n //= p; v += 1
    return v

def zx_trim(a):
    while a and a[-1] == 0: a.pop()
    return a

def zx_add(a, b):
    n = max(len(a), len(b))
    return zx_trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                    for i in range(n)])

def zx_mul(a, b):
    if not a or not b: return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0: continue
        for j, y in enumerate(b):
            out[i + j] += x * y
    return zx_trim(out)

def zx_divmod(a, m):
    """a = q*m + r over Z, m monic. Exact (integer) division."""
    a = list(a); q = [0] * max(1, len(a) - len(m) + 1)
    while len(a) >= len(m):
        c = a[-1]; d = len(a) - len(m)
        q[d] = c
        for i, mc in enumerate(m):
            a[d + i] -= c * mc
        zx_trim(a)
        if len(a) >= len(m) and a[-1] == 0: zx_trim(a)
    return zx_trim(q), zx_trim(a)

class Partial(Exception): pass            # the formula failed to return

# ------------------------------------------------- stage 2: formula + checker
def offsetP2(p, e, h, g, W, tau):
    """The offset-P-lift, stage-2 instance (recursion bottoms at the base).
    tau: element of F' = F_p[z]/psi (tuple len g), != 0. Returns Z[x] poly."""
    if W <= e * h * g: raise Partial('W <= clean threshold ehg')
    j0 = (pow(h, -1, e) * W) % e if e > 1 else 0
    t = [0] * (e * g)
    hit = False
    for k in range(g):
        Pk = tau[k]                        # P := the deg<g representative of tau
        if Pk == 0: continue
        j = j0 + e * k
        if j > e * g - 1: raise Partial('slot j0+ek out of coefficient space')
        num = W - j * h
        if num < 0: raise Partial('summand weight negative')
        if num % e: raise Partial('summand weight not zero-class')
        t[j] = Pk * p ** (num // e)        # base realizer: F_Q-unit lift, no threshold
        hit = True
    if not hit: raise Partial('empty sum (tau = 0)')
    return zx_trim(t)

def read2(p, e, h, g, psi, t):
    """INDEPENDENT from-scratch reading of a raw Z[x] poly: (W, j0, class in F').
    Returns (W, j0, tau_read) or a string describing a FINDING."""
    slots = {j: c for j, c in enumerate(t) if c != 0}
    if not slots: return 'zero polynomial'
    if max(slots) >= e * g: return 'degree >= eg'
    vals = {j: e * vp(c, p) + j * h for j, c in slots.items()}
    W = min(vals.values())
    mins = sorted(j for j in slots if vals[j] == W)
    j0 = mins[0] % e
    if any(j % e != j0 for j in mins): return 'minimizing slots in mixed classes mod e'
    if (j0 - pow(h, -1, e) * W if e > 1 else 0) % (e if e > 1 else 1) != 0:
        return 'minimizing class != h^{-1} W mod e'
    R = [0] * g
    for j in mins:
        k = (j - j0) // e
        if k >= g: return 'residual slot k >= g'
        R[k] = (slots[j] // p ** ((W - j * h) // e)) % p
    return (W, j0, tuple(R))               # deg < g: already reduced mod psi

# ------------------------------------------------- stage 3: formula + checker
def phi2_lift(p, e1, h1, g1, psi1):
    """Standard Ore lift of psi1: x^{e1 g1} + Sigma lift(c_k) p^{h1(g1-k)} x^{e1 k}."""
    poly = [0] * (e1 * g1) + [1]
    for k in range(g1):
        if psi1[k]: poly[e1 * k] += psi1[k] * p ** (h1 * (g1 - k))
    return poly

def offsetP3(p, S1, S2, W3, tau3):
    """Stage-3 offset-P-lift: one genuine recursion step. S1 = (e1,h1,g1,psi1);
    S2 = (e2,h2,g2,psi2) with psi2 over F2 = F_p[z]/psi1. tau3: tuple of
    F2-elements, len g2, != 0. Returns Z[x] poly of degree < e1g1e2g2."""
    (e1, h1, g1, psi1), (e2, h2, g2, _) = S1, S2
    if W3 <= e2 * h2 * g2: raise Partial('W3 <= clean threshold e2h2g2')
    j0 = (pow(h2, -1, e2) * W3) % e2 if e2 > 1 else 0
    Phi2 = phi2_lift(p, e1, h1, g1, psi1)
    t = []
    F2z = tuple([0] * g1)
    hit = False
    for k in range(g2):
        Pk = tau3[k]                       # element of F2
        if Pk == F2z: continue
        j = j0 + e2 * k
        if j > e2 * g2 - 1: raise Partial('slot j0+e2k out of coefficient space')
        num = W3 - j * h2
        if num < 0: raise Partial('summand weight negative')
        if num % e2: raise Partial('summand weight not zero-class')
        u = num // e2                      # required stage-2 parent-scale weight
        if u <= e1 * h1 * g1:              # the two-line recursion guard (I-aug)
            raise Partial('recursion guard: summand weight u <= e1h1g1')
        tk = offsetP2(p, e1, h1, g1, u, Pk)      # THE RECURSION (stage-2 S6b)
        t = zx_add(t, zx_mul(tk, zx_pow(Phi2, j)))
        hit = True
    if not hit: raise Partial('empty sum (tau3 = 0)')
    return t

def zx_pow(a, n):
    r = [1]
    for _ in range(n): r = zx_mul(r, a)
    return r

def read3(p, S1, S2, t):
    """INDEPENDENT from-scratch stage-3 reading: Phi2-develop t by exact
    division, read each B_j's stage-2 data via read2, form the stage-3
    residual over F2. Returns (W3, j0, tau3_read) or a FINDING string."""
    (e1, h1, g1, psi1), (e2, h2, g2, _) = S1, S2
    Phi2 = phi2_lift(p, e1, h1, g1, psi1)
    B, r = [], list(t)
    while r:
        r, rem = zx_divmod(r, Phi2)
        B.append(rem)
    if not B: return 'zero polynomial'
    if len(B) > e2 * g2: return 'Phi2-degree >= e2g2'
    data = {}
    for j, Bj in enumerate(B):
        if not Bj: continue
        got = read2(p, e1, h1, g1, psi1, Bj)
        if isinstance(got, str): return f'inner read of B_{j}: {got}'
        uj, _, digj = got
        data[j] = (e2 * uj + j * h2, digj)
    W3 = min(v for v, _ in data.values())
    mins = sorted(j for j in data if data[j][0] == W3)
    j0 = mins[0] % e2
    if any(j % e2 != j0 for j in mins): return 'minimizing slots in mixed classes mod e2'
    R = [tuple([0] * g1)] * g2
    for j in mins:
        k = (j - j0) // e2
        if k >= g2: return 'residual slot k >= g2'
        R[k] = data[j][1]
    return (W3, j0, tuple(R))              # deg < g2: already reduced mod psi2

# --------------------------------------------------------------------- driver
def banner(s):
    print('=' * 72); print(s); print('=' * 72)

def run():
    findings = []
    tally = {'cases': 0, 'min_nu': 0, 'g1_single_slot': 0, 'j0_pos': 0,
             'anchored_checked': 0, 'trivial_unit_group': 0}

    banner('1. STAGE-2 GRID (recursion bottoms at the base), p in {2,3,5}')
    grid2 = [(1, 1, 1), (2, 1, 1), (3, 1, 1), (2, 3, 1),
             (1, 1, 2), (2, 1, 2), (3, 2, 2), (2, 1, 3)]
    for p in (2, 3, 5):
        base = Fp(p)
        for (e, h, g) in grid2:
            assert gcd(e, h) == 1
            for psi in irreducibles(base, g, cap=4):
                F = Ext(base, psi)
                units = F.units()
                thr = e * h * g
                cov_fail, n_here = [], 0
                for W in range(thr + 1, thr + 2 * e + 1):
                    covered = set()
                    for tau in units:
                        tally['cases'] += 1; n_here += 1
                        if W == thr + 1: tally['min_nu'] += 1
                        if g == 1: tally['g1_single_slot'] += 1
                        if len(units) == 1: tally['trivial_unit_group'] += 1
                        try:
                            t = offsetP2(p, e, h, g, W, tau)
                        except Partial as ex:
                            findings.append((p, e, h, g, tuple(psi), W, tau,
                                             f'PARTIAL: {ex}')); continue
                        got = read2(p, e, h, g, psi, t)
                        if isinstance(got, str):
                            findings.append((p, e, h, g, tuple(psi), W, tau,
                                             f'READ: {got}')); continue
                        Wr, j0, taur = got
                        if j0 > 0: tally['j0_pos'] += 1
                        if Wr != W or taur != tau or taur == F.zero:
                            findings.append((p, e, h, g, tuple(psi), W, tau,
                                             f'MISMATCH: read (W={Wr}, tau={taur})'))
                        else:
                            covered.add(taur)
                    if len(covered) != len(units):
                        cov_fail.append(W)
                    # (a > 0) anchored-target tally: tau = zbar^a * u
                    for a in (1, 2):
                        za = F.pow(F.zbar, a)
                        anch = {F.mul(za, u) for u in units}
                        if not anch <= covered: cov_fail.append((W, 'anchor', a))
                        tally['anchored_checked'] += len(anch)
                status = 'PASS' if not cov_fail else 'FAIL'
                print(f'[{status}] p={p} (e,h,g)=({e},{h},{g}) psi={psi}: '
                      f'{n_here} cases, W in [{thr+1},{thr+2*e}], '
                      f'|F\'^x|={len(units)}'
                      + ('' if not cov_fail else f'  coverage fail at {cov_fail}'))
                if cov_fail:
                    findings.append((p, e, h, g, tuple(psi), None, None,
                                     f'COVERAGE: {cov_fail}'))

    banner('2. STAGE-3 GRID (one genuine recursion step), p in {2,3,5}')
    grid_s1 = [(2, 1, 1), (1, 1, 2), (2, 1, 2)]
    grid_s2 = [(2, 1), (1, 2), (2, 2)]
    for p in (2, 3, 5):
        base = Fp(p)
        for (e1, h1, g1) in grid_s1:
            for psi1 in irreducibles(base, g1, cap=2):
                F2 = Ext(base, psi1)
                for (e2, g2) in grid_s2:
                    h2 = e2 * e1 * h1 * g1 + 1        # (I-aug): h2 > e2*w1(Phi2)
                    assert gcd(e2, h2) == 1
                    S1 = (e1, h1, g1, psi1)
                    for psi2 in irreducibles(F2, g2, cap=2):
                        S2 = (e2, h2, g2, psi2)
                        F3 = Ext(F2, psi2)
                        units = F3.units()
                        thr = e2 * h2 * g2
                        cov_fail, n_here = [], 0
                        for W3 in range(thr + 1, thr + 2 * e2 + 1):
                            covered = set()
                            for tau in units:
                                tally['cases'] += 1; n_here += 1
                                if W3 == thr + 1: tally['min_nu'] += 1
                                if g2 == 1: tally['g1_single_slot'] += 1
                                try:
                                    t = offsetP3(p, S1, S2, W3, tau)
                                except Partial as ex:
                                    findings.append((p, S1[:3], (e2, h2, g2), W3,
                                                     tau, f'PARTIAL: {ex}'))
                                    continue
                                got = read3(p, S1, S2, t)
                                if isinstance(got, str):
                                    findings.append((p, S1[:3], (e2, h2, g2), W3,
                                                     tau, f'READ: {got}'))
                                    continue
                                Wr, j0, taur = got
                                if j0 > 0: tally['j0_pos'] += 1
                                if Wr != W3 or taur != tau:
                                    findings.append((p, S1[:3], (e2, h2, g2), W3,
                                                     tau, f'MISMATCH: (W={Wr}, tau={taur})'))
                                else:
                                    covered.add(taur)
                            if len(covered) != len(units): cov_fail.append(W3)
                            for a in (1, 2):
                                za = F3.pow(F3.zbar, a)
                                anch = {F3.mul(za, u) for u in units}
                                if not anch <= covered: cov_fail.append((W3, 'anchor', a))
                                tally['anchored_checked'] += len(anch)
                        status = 'PASS' if not cov_fail else 'FAIL'
                        print(f'[{status}] p={p} S1=({e1},{h1},{g1}) psi1={psi1} '
                              f'S2=({e2},{h2},{g2}) psi2={psi2}: {n_here} cases, '
                              f'W3 in [{thr+1},{thr+2*e2}], |F3^x|={len(units)}'
                              + ('' if not cov_fail else f'  coverage fail {cov_fail}'))
                        if cov_fail:
                            findings.append((p, S1[:3], (e2, h2, g2), None, None,
                                             f'COVERAGE: {cov_fail}'))

    banner('3. NEGATIVE CONTROLS (the gate has teeth)')
    ctrl_ok = True
    # NC1: corrupt the forced slot class (j0+1): summand weights must leave the
    # zero class, and the construction must be rejected.
    p, e, h, g = 3, 2, 1, 2
    psi = irreducibles(Fp(p), g, cap=1)[0]; F = Ext(Fp(p), psi)
    W = e * h * g + 1
    j0 = (pow(h, -1, e) * W) % e
    bad_ok = all((W - ((j0 + 1) % e + e * k) * h) % e != 0 for k in range(g))
    print(f'[{"PASS" if bad_ok else "FAIL"}] NC1: corrupted slot class j0+1 '
          f'leaves the zero class at every summand (p=3,(e,h,g)=(2,1,2),W={W})')
    ctrl_ok &= bad_ok
    # NC2: wrong-class detection: realizer for tau checked against tau' != tau.
    tau, tau2 = F.units()[0], F.units()[1]
    t = offsetP2(p, e, h, g, W, tau)
    got = read2(p, e, h, g, psi, t)
    nc2 = (not isinstance(got, str)) and got[2] == tau and got[2] != tau2
    print(f'[{"PASS" if nc2 else "FAIL"}] NC2: independent reader distinguishes '
          f'classes (read {got[2] if not isinstance(got, str) else got} = tau != tau\')')
    ctrl_ok &= nc2
    # NC3: violate (I-aug) at stage 3 (h2 = e2*e1h1g1 - 1): the two-line
    # recursion guard must trip at the minimal eligible W3.
    e1, h1, g1 = 2, 1, 1; psi1 = irreducibles(Fp(p), 1, cap=1)[0]
    e2, g2 = 2, 1; h2bad = e2 * e1 * h1 * g1 - 1
    F2 = Ext(Fp(p), psi1); psi2 = irreducibles(F2, 1, cap=1)[0]
    tripped = False
    try:
        offsetP3(p, (e1, h1, g1, psi1), (e2, h2bad, g2, psi2),
                 e2 * h2bad * g2 + 1, (F2.one,))
    except Partial as ex:
        tripped = 'recursion guard' in str(ex) or 'threshold' in str(ex)
    print(f'[{"PASS" if tripped else "FAIL"}] NC3: (I-aug) violation '
          f'(h2={h2bad} < e2*e1h1g1={e2*e1*h1*g1}) trips the recursion guard')
    ctrl_ok &= tripped

    banner('4. TALLIES (the named L1 boundary cases, all enumerated)')
    print(f"  total realizer cases:              {tally['cases']}")
    print(f"  (min-nu) minimal eligible W cases: {tally['min_nu']}")
    print(f"  (g=1) single-slot cases:           {tally['g1_single_slot']}")
    print(f"  (j0>0) offset genuinely engaged:   {tally['j0_pos']}")
    print(f"  (a>0) anchored targets checked:    {tally['anchored_checked']}"
          f"  (tau = zbar^a u, a in {{1,2}})")
    print(f"  trivial unit group (p=2, g=1):     {tally['trivial_unit_group']}")

    print()
    if findings:
        banner('FINDINGS (each would refute L1 totality as enumerated)')
        for f in findings[:40]: print('  FINDING:', f)
        print(f'\nVERDICT: L1 BOUNDARY ENUMERATION FINDS {len(findings)} FAILURES')
        return 1
    print('VERDICT: L1 BOUNDARY ENUMERATION PASSES — the offset-P realizer exists')
    print('with the prescribed weight and class at EVERY enumerated boundary case')
    print('(minimal eligible nu, every forced slot class incl. j0 > 0, g = 1')
    print('single slot at both stages, a > 0 anchored targets, one genuine')
    print('recursion step through stage-2 (S6b), all classes covered at every')
    print('eligible weight). SUPPORT for kernel D4R.0-K part (a); L1 stays OPEN')
    print('(finite enumeration cannot discharge the every-realizable-prefix')
    print('quantifier).')
    return 0

if __name__ == '__main__':
    sys.exit(run())
