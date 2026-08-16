#!/usr/bin/env python3
"""OM-9 certification battery — the two weld conjuncts at the CHAP-F carrier vocabulary.

Rows: HYP.74 (JD0-BOX-2), HYP.139 (W-1 transport), HYP.148 (GENHN-BOX-2, abstract side only
— the WELD-ZERO arc is FENCED and nothing here touches it).

Exact arithmetic over hand-built finite fields (the F-gate's table constructions: F4 with
theta^2 = theta+1 over Z/2, F9 with theta^2 = -1 over Z/3, plus prime fields F2/F3/F5).
Every leg runs at BOTH characteristics (GC-11), with the involution/non-involution separator
model of the F.29/F.30 gates carried to the new legs. Planted mutants are expected-RED: a
battery that cannot catch its own mutants certifies nothing.

Legs (mirroring the OM-9 outline, docs/openmath-campaign/OM-9_weld_2026-08-16.md):
  A — HYP.74: slotScale bijection/count-blindness + NONCHAR control; gaugeCobdry preserves
      the 2-cocycle class (the perimeter's consistency); resTwist conclusions; F2 vacuity.
  B — HYP.139: W1Transport iff equal vanishing loci (brute-force vs predicate; exact count
      ((q-1)^2+1)^|iota|); transport algebra; the DMULT-w coboundary omega (cocycle law;
      #{omega == 1} = #Hom(Z/6,K*) = gcd(6, q-1); the omega-vs-omega^{-1} separator).
  C — HYP.148 (abstract): associativity <=> cocycle identity at the singles level (both
      directions, every table); |Z^2| = |K*|^E count law; degenerate-row constancy
      c(0,b) = c(0,0) = c(a,0); first-row symmetry c(1,k) = c(k,1); FULL symmetry
      c(a,b) = c(b,a); the power basis v^E = (prod_k c(1,k)) . single 0 1, right AND left
      recursion; the {0,1} integer carry census.
"""

import itertools, json, sys, random
from math import gcd

random.seed(20260816)

# ---------------------------------------------------------------- finite fields
class Field:
    def __init__(self, name, elems, add, mul, zero, one):
        self.name, self.elems, self.add, self.mul = name, elems, add, mul
        self.zero, self.one = zero, one
        self.units = [x for x in elems if x != zero]
        self.inv = {}
        for x in self.units:
            for y in self.units:
                if mul(x, y) == one:
                    self.inv[x] = y
        assert len(self.inv) == len(self.units)
    def q(self):
        return len(self.elems)

def prime_field(p):
    return Field(f"F{p}", list(range(p)),
                 lambda a, b: (a + b) % p, lambda a, b: (a * b) % p, 0, 1)

def f4_mul(x, y):  # theta^2 = theta + 1 over Z/2 (the leanspec gate's table)
    a, b, c, d = x[0], x[1], y[0], y[1]
    return ((a * c + b * d) % 2, (a * d + b * c + b * d) % 2)

def f9_mul(x, y):  # theta^2 = -1 over Z/3 (the leanspec gate's table)
    a, b, c, d = x[0], x[1], y[0], y[1]
    return ((a * c - b * d) % 3, (a * d + b * c) % 3)

def ext_field(name, p, mulrule):
    elems = [(a, b) for a in range(p) for b in range(p)]
    return Field(name, elems,
                 lambda x, y: ((x[0] + y[0]) % p, (x[1] + y[1]) % p),
                 mulrule, (0, 0), (1, 0))

F2, F3, F5 = prime_field(2), prime_field(3), prime_field(5)
F4 = ext_field("F4", 2, f4_mul)
F9 = ext_field("F9", 3, f9_mul)

# ---------------------------------------------------------------- small helpers
def pow_field(K, x, n):
    acc = K.one
    for _ in range(n):
        acc = K.mul(acc, x)
    return acc

def pow_inv(K, x, n):
    return pow_field(K, K.inv[x], n)

def poly_eval(K, coeffs, x):
    acc = K.zero
    for c in reversed(coeffs):
        acc = K.add(K.mul(acc, x), c)
    return acc

CHECKS = []
def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(("GREEN " if ok else "RED   ") + name + ("  | " + detail if detail else ""))

def mutant(name, caught, detail=""):
    CHECKS.append({"name": name, "ok": bool(caught), "detail": detail, "mutant": True})
    print(("CAUGHT" if caught else "MISSED") + " [mutant] " + name
          + ("  | " + detail if detail else ""))

# ---------------------------------------------------------------- cocycle utilities
def all_tables(K, E):
    keys = [(a, b) for a in range(E) for b in range(E)]
    for vals in itertools.product(K.units, repeat=len(keys)):
        yield dict(zip(keys, vals))

def is_cocycle(K, E, c):
    for a in range(E):
        for b in range(E):
            for d in range(E):
                lhs = K.mul(c[(a, b)], c[((a + b) % E, d)])
                rhs = K.mul(c[(b, d)], c[(a, (b + d) % E)])
                if lhs != rhs:
                    return (a, b, d)
    return None

def cobdry(K, E, u):  # del(u)(a,b) = u_a u_b u_{a+b}^{-1}
    return {(a, b): K.mul(K.mul(u[a], u[b]), K.inv[u[(a + b) % E]])
            for a in range(E) for b in range(E)}

def wrap_cocycle(K, E, zeta):  # c(a,b) = zeta^{floor((a+b)/E)}, representatives 0..E-1
    return {(a, b): (zeta if a + b >= E else K.one) for a in range(E) for b in range(E)}

def gauge(K, E, u, c):  # gaugeCobdry u c = c * del(u)
    d = cobdry(K, E, u)
    return {k: K.mul(c[k], d[k]) for k in c}

def enum_cocycles(K, E, brute_limit=2_000_000):
    """Z^2: brute force when feasible; else the generated family del(u) * wrap(zeta)
    (complete by |Z^2| = |B^2| * |H^2| = |K*|^E for cyclic groups; brute-verified below at
    E = 2, 3 and at (F3, E=4))."""
    n_tables = len(K.units) ** (E * E)
    if n_tables <= brute_limit:
        return [c for c in all_tables(K, E) if is_cocycle(K, E, c) is None], "brute"
    seen, out = set(), []
    for u in itertools.product(K.units, repeat=E):
        for z in K.units:
            c = gauge(K, E, list(u), wrap_cocycle(K, E, z))
            key = tuple(sorted(c.items()))
            if key not in seen:
                assert is_cocycle(K, E, c) is None
                seen.add(key)
                out.append(c)
    return out, "generated"

def conv(K, E, c, f, g):  # (f * g) t = sum_a c(a, t-a) f(a) g(t-a)
    out = []
    for t in range(E):
        acc = K.zero
        for a in range(E):
            b = (t - a) % E
            acc = K.add(acc, K.mul(K.mul(c[(a, b)], f[a]), g[b]))
        out.append(acc)
    return tuple(out)

def single(K, E, a, x):
    return tuple(x if t == a else K.zero for t in range(E))

# ---------------------------------------------------------------- LEG A — HYP.74
print("\n=== LEG A — HYP.74 (JD0-BOX-2): the gauge-form mechanism ===")

# A1: slotScale bijection + count blindness (Gamma = 2 slots), + NONCHAR control.
for K in (F4, F3):
    q = K.q()
    fams = list(itertools.product(K.elems, repeat=2))
    stratum = [v for v in fams if v[0] == K.zero]  # S = {v | v 0 = 0}
    ok_bij, ok_cnt = True, True
    for u in itertools.product(K.units, repeat=2):
        img = [(K.mul(u[0], v[0]), K.mul(u[1], v[1])) for v in fams]
        if len(set(img)) != len(fams):
            ok_bij = False
        imgS = {(K.mul(u[0], v[0]), K.mul(u[1], v[1])) for v in stratum}
        if imgS != set(stratum) or len(imgS) != len(stratum):
            ok_cnt = False
    check(f"A1.bijection+count-blind slotScale [{K.name}, all u, all v]", ok_bij and ok_cnt,
          f"{len(K.units)**2} gauges x {q*q} families; |S| = {len(stratum)}")
for K in (F4, F3):
    fams = list(itertools.product(K.elems, repeat=2))
    stratum = {v for v in fams if v[0] == K.zero}
    s = (K.one, K.zero)
    imgS = {(K.add(v[0], s[0]), K.add(v[1], s[1])) for v in stratum}
    check(f"A1.NONCHAR-control: additive shift leaves the stratum [{K.name}]",
          imgS.isdisjoint(stratum) and len(imgS) == len(stratum),
          "a bijection OUTSIDE the four-line class; image disjoint from S")
K = F4
fams = list(itertools.product(K.elems, repeat=2))
img = [(K.mul(K.zero, v[0]), K.mul(K.one, v[1])) for v in fams]
mutant("A1m.zero-letter 'gauge' breaks bijectivity [F4]", len(set(img)) != len(fams))

# A2: |Z^2| = |K*|^E and gaugeCobdry preserves Z^2.
for K, E in ((F4, 2), (F3, 2), (F3, 3), (F4, 3), (F5, 2), (F5, 3)):
    cocs, mode = enum_cocycles(K, E)
    pred = len(K.units) ** E
    check(f"A2.count |Z2({K.name}, E={E})| = |K*|^E = {pred} [{mode}]",
          len(cocs) == pred, f"found {len(cocs)}")
    ok = True
    for c in cocs:
        for u in itertools.product(K.units, repeat=E):
            if is_cocycle(K, E, gauge(K, E, list(u), c)) is not None:
                ok = False
    check(f"A2.gaugeCobdry preserves cocycles [{K.name}, E={E}]", ok,
          f"{len(cocs)} cocycles x {len(K.units)**E} gauges")
K, E = F4, 2
c0 = wrap_cocycle(K, E, K.units[1])
cm = dict(c0)
cm[(0, 1)] = [z for z in K.units if z != cm[(0, 1)]][0]
mutant("A2m.single-entry flip breaks the cocycle identity [F4, E=2]",
       is_cocycle(K, E, cm) is not None, f"violating triple {is_cocycle(K, E, cm)}")

# A3: resTwist conclusions (degree / leading coeff / monicity / root census).
def res_twist(K, xi, R):
    """R(xi X) * xi^{-deg R}, coefficient form: coeff_i -> coeff_i * xi^{i - deg}."""
    deg = len(R) - 1
    return [K.mul(K.mul(R[i], pow_field(K, xi, i)), pow_inv(K, xi, deg))
            for i in range(len(R))]

for K in (F4, F9):
    ok_deg = ok_lc = ok_root = True
    for deg in (1, 2):
        for coeffs in itertools.product(K.elems, repeat=deg):
            for lc in K.units:
                R = list(coeffs) + [lc]
                for xi in K.units:
                    T = res_twist(K, xi, R)
                    if len(T) != len(R) or T[-1] == K.zero:
                        ok_deg = False
                    if T[-1] != R[-1]:
                        ok_lc = False
                    for r in K.elems:
                        if (poly_eval(K, T, r) == K.zero) != \
                           (poly_eval(K, R, K.mul(xi, r)) == K.zero):
                            ok_root = False
    check(f"A3.resTwist degree preserved [{K.name}, deg <= 2, all xi]", ok_deg)
    check(f"A3.resTwist leading coeff (hence monicity) preserved [{K.name}]", ok_lc)
    check(f"A3.resTwist root census r ~ xi*r [{K.name}]", ok_root)

def mutant_a3(K):  # wrong normalization xi^{+deg}: leading coeff moves
    for deg in (1, 2):
        for lc in K.units:
            R = [K.zero] * deg + [lc]
            for xi in K.units:
                T = [K.mul(K.mul(R[i], pow_field(K, xi, i)), pow_field(K, xi, deg))
                     for i in range(len(R))]
                if T[-1] != R[-1]:
                    return True
    return False

mutant("A3m.wrong normalization xi^{+deg} caught at F4 (non-involution)", mutant_a3(F4))
mutant("A3m.wrong normalization xi^{+deg} MISSED at F3 — expected miss, the involution "
       "separator", not mutant_a3(F3),
       "F3 units are involutions: xi^{2 deg} = 1 hides the defect (F-gate separator model)")

# A4: z-power strike gauges are unit-valued (the fold route's data shape).
K, E = F4, 3
okA4 = True
for z in K.units:
    for a in itertools.product(range(-2, 3), repeat=E):
        u = [pow_field(K, z, av % 3) if av >= 0 else pow_inv(K, z, (-av) % 3) for av in a]
        if any(x == K.zero for x in u):
            okA4 = False
check("A4.z-power strike gauges are unit-valued [F4, all z, exponents -2..2]", okA4)

# A5: F2 vacuity — the only unit acts trivially.
fams = list(itertools.product(F2.elems, repeat=2))
check("A5.F2 degeneracy: slotScale is the identity for every gauge (JD0-BOX-5)",
      all((F2.mul(1, v[0]), F2.mul(1, v[1])) == v for v in fams))

# ---------------------------------------------------------------- LEG B — HYP.139
print("\n=== LEG B — HYP.139 (W-1 transport at the carrier vocabulary) ===")

def w1_brute(K, Rh, RG):
    n = len(Rh)
    for c in itertools.product(K.units, repeat=n):
        if all(Rh[l] == K.mul(c[l], RG[l]) for l in range(n)):
            return True
    return False

for K in (F3, F4):
    q = K.q()
    fams = list(itertools.product(K.elems, repeat=3))
    n_ok, ok_iff = 0, True
    for Rh in fams:
        for RG in fams:
            loci = all((Rh[l] == K.zero) == (RG[l] == K.zero) for l in range(3))
            bf = w1_brute(K, Rh, RG)
            if bf != loci:
                ok_iff = False
            n_ok += bf
    pred = ((q - 1) ** 2 + 1) ** 3
    check(f"B1.W1Transport iff equal vanishing loci [{K.name}, all {len(fams)**2} pairs]",
          ok_iff)
    check(f"B1.count transportable pairs = ((q-1)^2+1)^3 = {pred} [{K.name}]",
          n_ok == pred, f"found {n_ok}")

K = F3
fams = list(itertools.product(K.elems, repeat=3))
rel = {(Rh, RG) for Rh in fams for RG in fams if w1_brute(K, Rh, RG)}
ok_sym = all((b, a) in rel for (a, b) in rel)
byl = {}
for (a, b) in rel:
    byl.setdefault(a, set()).add(b)
ok_trans = all(x in byl[a] for a in byl for b in byl[a] for x in byl.get(b, ()))
ok_refl = all((a, a) in rel for a in fams)
check("B2.transport relation reflexive + symmetric + transitive [F3, exhaustive]",
      ok_refl and ok_sym and ok_trans, f"|rel| = {len(rel)}")

# B3: the DMULT-w coboundary omega on iota = Z/6.
for K in (F3, F4, F5):
    E = 6
    n_hom_pred = gcd(E, len(K.units))
    total = len(K.units) ** E
    ok_coc, n_triv, n_invblind = True, 0, 0
    for c in itertools.product(K.units, repeat=E):
        om = {(l, m): K.mul(c[(l + m) % E], K.inv[K.mul(c[l], c[m])])
              for l in range(E) for m in range(E)}
        if is_cocycle(K, E, om) is not None:
            ok_coc = False
        if all(v == K.one for v in om.values()):
            n_triv += 1
        if all(K.inv[v] == v for v in om.values()):
            n_invblind += 1
    check(f"B3.omega = c(l+m)/(c_l c_m) is a 2-cocycle [Z/6, {K.name}, all {total} c]",
          ok_coc)
    check(f"B3.#{{omega == 1}} = #Hom(Z/6, K*) = gcd(6, q-1) = {n_hom_pred} [{K.name}]",
          n_triv == n_hom_pred,
          f"found {n_triv}; 'nothing gives omega == 1': {total - n_triv} systems refuse")
    all_inv = all(K.inv[z] == z for z in K.units)
    sep = ("COINCIDE (involution regime)" if n_invblind == total
           else f"separated: {n_invblind}/{total} omega-tables self-inverse")
    check(f"B3.separator omega vs omega^-1 [{K.name}]",
          (n_invblind == total) == all_inv, sep)

def b3_mutant(K, E=6):
    for c in itertools.product(K.units, repeat=E):
        om = {(l, m): K.mul(c[(l + m) % E], K.inv[K.mul(c[l], c[m])])
              for l in range(E) for m in range(E)}
        if any(K.inv[v] != v for v in om.values()):
            return True
    return False

mutant("B3m.omega vs omega^{-1} confusion caught at F4", b3_mutant(F4))
mutant("B3m.omega vs omega^{-1} confusion MISSED at F3 — expected miss (separator)",
       not b3_mutant(F3))

# B4: a concrete omega != 1 witness at F4.
K = F4
c6 = [K.units[0], K.units[1], K.units[0], K.units[0], K.units[0], K.units[0]]
om11 = K.mul(c6[2], K.inv[K.mul(c6[1], c6[1])])
check("B4.concrete omega != 1 witness at F4 (a non-homomorphic line system)",
      om11 != K.one, f"c = {c6}, omega(1,1) = {om11}")

# ---------------------------------------------------------------- LEG C — HYP.148 abstract
print("\n=== LEG C — HYP.148 (GENHN-BOX-2), abstract W-9 algebra only (arc FENCED) ===")

# C1: associativity <=> cocycle identity at the singles level, EVERY table.
for K, E in ((F4, 2), (F3, 2), (F3, 3), (F5, 2)):
    ok_bicond, n_assoc, n_coc = True, 0, 0
    for c in all_tables(K, E):
        coc = is_cocycle(K, E, c) is None
        assoc = True
        for a in range(E):
            for b in range(E):
                for d in range(E):
                    fg = conv(K, E, c, single(K, E, a, K.one), single(K, E, b, K.one))
                    lhs = conv(K, E, c, fg, single(K, E, d, K.one))
                    gh = conv(K, E, c, single(K, E, b, K.one), single(K, E, d, K.one))
                    rhs = conv(K, E, c, single(K, E, a, K.one), gh)
                    if lhs != rhs:
                        assoc = False
        n_assoc += assoc
        n_coc += coc
        if assoc != coc:
            ok_bicond = False
    check(f"C1.assoc(singles) <=> cocycle identity [{K.name}, E={E}, ALL tables]",
          ok_bicond, f"#assoc = {n_assoc} = #cocycles = {n_coc}")

K, E = F4, 3
cocs, mode = enum_cocycles(K, E)
fams = list(itertools.product(K.elems, repeat=E))
ok = True
for c in cocs:
    for _ in range(40):
        f, g, h = (random.choice(fams) for _ in range(3))
        if conv(K, E, c, conv(K, E, c, f, g), h) != conv(K, E, c, f, conv(K, E, c, g, h)):
            ok = False
check(f"C1.full-function associativity on all {len(cocs)} cocycles "
      f"[F4, E=3, 40 random triples each]", ok)

K, E = F4, 2
cm = wrap_cocycle(K, E, K.one)
cm[(0, 0)] = [z for z in K.units if z != K.one][0]  # c(0,0) != c(0,1): not a cocycle
viol = is_cocycle(K, E, cm)
fg = conv(K, E, cm, single(K, E, 0, K.one), single(K, E, 0, K.one))
lhs = conv(K, E, cm, fg, single(K, E, 1, K.one))
gh = conv(K, E, cm, single(K, E, 0, K.one), single(K, E, 1, K.one))
rhs = conv(K, E, cm, single(K, E, 0, K.one), gh)
mutant("C1m.non-cocycle table breaks associativity [F4, E=2]",
       viol is not None and lhs != rhs,
       f"cocycle violation at {viol}; assoc fails at singles (0, 0, 1)")

# C2: count form — |carrier| = q^E.
for K, E in ((F4, 2), (F3, 2), (F4, 3), (F9, 2)):
    check(f"C2.card K^(Z/E) = q^E = {K.q()**E} [{K.name}, E={E}]",
          len(list(itertools.product(K.elems, repeat=E))) == K.q() ** E)

# C3: structural lemmas + the power basis, over EVERY enumerated cocycle.
for K, E in ((F3, 2), (F4, 2), (F5, 2), (F3, 3), (F4, 3), (F5, 3),
             (F3, 4), (F4, 4), (F5, 4)):
    cocs, mode = enum_cocycles(K, E)
    pred = len(K.units) ** E
    ok_deg0 = ok_row1 = ok_sym = ok_pow = ok_left = True
    for c in cocs:
        if not all(c[(0, b)] == c[(0, 0)] and c[(a, 0)] == c[(0, 0)]
                   for a in range(E) for b in range(E)):
            ok_deg0 = False
        if not all(c[(1, k)] == c[(k, 1)] for k in range(E)):
            ok_row1 = False
        if not all(c[(a, b)] == c[(b, a)] for a in range(E) for b in range(E)):
            ok_sym = False
        one_el = single(K, E, 0, K.inv[c[(0, 0)]])
        v = single(K, E, 1, K.one)
        zeta = K.one
        for k in range(1, E):
            zeta = K.mul(zeta, c[(1, k)])
        target = single(K, E, 0, zeta)
        pw = one_el
        for _ in range(E):
            pw = conv(K, E, c, pw, v)   # right recursion (npowRec)
        if pw != target:
            ok_pow = False
        pl = one_el
        for _ in range(E):
            pl = conv(K, E, c, v, pl)   # left recursion (JC-F1's direction)
        if pl != target:
            ok_left = False
    check(f"C3.|Z2| = {pred} and degenerate rows constant [{K.name}, E={E}, {mode}]",
          len(cocs) == pred and ok_deg0, f"{len(cocs)} cocycles")
    check(f"C3.first-row symmetry c(1,k) = c(k,1) [{K.name}, E={E}]", ok_row1)
    check(f"C3.FULL symmetry c(a,b) = c(b,a) [{K.name}, E={E}]", ok_sym)
    check(f"C3.power basis v^E = (prod_k c(1,k)) . single 0 1, right recursion "
          f"[{K.name}, E={E}]", ok_pow)
    check(f"C3.left recursion agrees [{K.name}, E={E}]", ok_left)

K, E = F4, 3
cm = wrap_cocycle(K, E, K.one)
cm[(1, 2)] = [z for z in K.units if z != K.one][0]  # break symmetry against (2,1)
mutant("C3m.asymmetric table fails the cocycle identity [F4, E=3]",
       is_cocycle(K, E, cm) is not None)

# C4: the {0,1} integer carry census (W-9(ii) side).
for E in (2, 3):
    goods = []
    keys = [(a, b) for a in range(E) for b in range(E)]
    for vals in itertools.product((0, 1), repeat=len(keys)):
        d = dict(zip(keys, vals))
        if all(d[(a, b)] + d[((a + b) % E, e)] == d[(b, e)] + d[(a, (b + e) % E)]
               for a in range(E) for b in range(E) for e in range(E)):
            goods.append(d)
    wrap = {(a, b): (1 if a + b >= E else 0) for a in range(E) for b in range(E)}
    check(f"C4.integer carry census [E={E}]: standard wrap among {len(goods)} "
          f"{{0,1}}-solutions", any(g == wrap for g in goods))

# ---------------------------------------------------------------- summary
print("\n=== SUMMARY ===")
mutants = [c for c in CHECKS if c.get("mutant")]
greens = [c for c in CHECKS if not c.get("mutant") and c["ok"]]
reds = [c for c in CHECKS if not c.get("mutant") and not c["ok"]]
caught = [m for m in mutants if m["ok"]]
print(f"checks: {len(greens)} GREEN / {len(reds)} RED; "
      f"mutants: {len(caught)}/{len(mutants)} caught")
with open(__file__.replace(".py", "_results.json"), "w") as fh:
    json.dump(CHECKS, fh, indent=1)
sys.exit(0 if not reds and len(caught) == len(mutants) else 1)
