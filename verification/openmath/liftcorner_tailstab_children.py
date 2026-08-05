#!/usr/bin/env python3
"""liftcorner_tailstab_children.py — EXAMPLES-FIRST child-type table for the
(TAIL-STAB) lemma of lean/notes/openmath/LIFTCORNER_2026-08-08.md S4.1.

WHY THIS EXISTS.  passPE1 (LIFTCORNER_passPE1_report.md, F1 CRITICAL) refuted
the S4.1 strict-descent clause "every child has m' <= m-1": the mid-branch
q-digit child at k = e0-1 sits at m' = m.  Per the standing examples-first
directive (Asvin 2026-08-05, BRIDGE_ADJUDICATIONS "DIRECTIVE" section), the
repaired induction's case split must be DERIVED FROM an example battery that
tabulates, for every child of every instance, exactly the quantities the open
question turns on: (child genre, m', deg a', the lexicographic delta in
(m, deg a), the omega-gain).

This script is INDEPENDENT of the sealed runner verification/openmath/
liftcorner_checks.py (byte-untouched; not imported here).  Plain exact
integer/polynomial arithmetic, no external deps.

SETTING (S1/S4.1 of the note).  O = Z_p, pi = p, residue field F_p; Phi0 in
O[x] monic of degree d0, irreducible mod p; w0 = the Gauss valuation
w0(sum a_i x^i) = min_i v_p(a_i) (a valuation on O[x], w0(pi) = 1,
w0(Phi0) = 0).  A corner orbit member is
    Phi' = Phi0^{e0} + sum_{k<e0} b_k Phi0^k,   deg b_k < d0,
with e0 >= 2, gcd(e0,h0) = 1, w0(b0) = h0 exactly, c' := res(b0/pi^{h0}) != 0,
and w0(b_k) >= amin(k) := ceil((e0-k) h0 / e0) for k >= 1.  Write the wave-18
S1 split b0 = chat' * pi^{h0} + t0 with res(chat') = c' (so w0(chat') = 0) and
w0(t0) >= h0 + 1.
Level-1/2 ledger data: e1, h1 with gcd(e1,h1) = 1, gamma2 = e1 e0 h0 + h1, and
for X = a * Phi0^m * Phi'^j (deg a < d0):
    omega(X) := e1 (e0 w0(a) + m h0) + j gamma2.

ONE PASS (the step case, m >= e0), from Phi0^{e0} = Phi' - b0 - sum_{k>=1} b_k Phi0^k:
    X = a Phi0^{m-e0} Phi'^{j+1}
        - a b0 Phi0^{m-e0} Phi'^j
        - sum_{k>=1} a b_k Phi0^{m-e0+k} Phi'^j,
then each level-0 coefficient a*b (deg < 2 d0) is re-digited a*b = r + q*Phi0,
giving an r-child at Phi0-exponent M and a q-child at M+1.  The b0 branch is
further split main (chat' pi^{h0}) / tail (t0) because only the main-r child has
omega-gain 0.  CHILD GENRES therefore: key | b0-main-r | b0-main-q |
b0-tail-r | b0-tail-q | mid[k]-r | mid[k]-q.

WHAT THE TABLE MUST ANSWER (the directive's three questions):
  (1) which child genres exist;
  (2) which coordinate of (m, deg a) each genre drops;
  (3) whether ANY child drops NEITHER (a lex-order counterexample).

ASSERTIONS (script exits 1 if any fails):
  A1  every child is strictly lex-smaller in (m, deg a) than its parent;
  A2  every m' = m child is genre mid[e0-1]-q AND has deg a' <= deg a - 1;
  A3  no m' = m child occurs when deg a = 0 (the second-coordinate base);
  A4  no m' = m child occurs when d0 = 1 (no q-children at all there);
  A5  every child has omega-gain >= 0, and gain 0 occurs only at b0-main-r;
  A6  LEDGER holds on the honestly computed double development of X:
      every nonzero digit a_{ji} of X = sum_j (sum_i a_{ji} Phi0^i) Phi'^j
      obeys e1(e0 w0(a_{ji}) + i h0) + j gamma2 >= omega(X).

Ring genre: only O = Z_p is instantiated.  The child-type combinatorics depends
on the instance ONLY through degrees and w0-values (the pass identity and the
division algorithm by a monic key are ring-generic), and A6's arithmetic is
characteristic-free; F_p[[t]] would duplicate rows.  Disclosed, not assumed
away: p = 2 (char 2, wild) is in the battery, so no odd-characteristic
accident can hide.

Usage:  python3 liftcorner_tailstab_children.py [--table FILE]
Default table file: liftcorner_tailstab_children_table.txt (committed).
"""
import sys, json, math
from math import gcd

INF = float('inf')

# ---------------------------------------------------------------- polynomials
# poly = list of int coefficients, low degree first, no trailing zeros.

def ptrim(f):
    while f and f[-1] == 0:
        f = f[:-1]
    return f

def pdeg(f):
    f = ptrim(f)
    return -1 if not f else len(f) - 1

def padd(f, g):
    n = max(len(f), len(g))
    return ptrim([(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)
                  for i in range(n)])

def psub(f, g):
    n = max(len(f), len(g))
    return ptrim([(f[i] if i < len(f) else 0) - (g[i] if i < len(g) else 0)
                  for i in range(n)])

def pmul(f, g):
    f, g = ptrim(f), ptrim(g)
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                out[i + j] += a * b
    return ptrim(out)

def pscal(c, f):
    return ptrim([c * a for a in f])

def ppow(f, n):
    out = [1]
    for _ in range(n):
        out = pmul(out, f)
    return out

def vp(n, p):
    if n == 0:
        return INF
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

def w0(f, p):
    """Gauss valuation w0(sum a_i x^i) = min_i v_p(a_i); INF on 0."""
    f = ptrim(f)
    return INF if not f else min(vp(a, p) for a in f)

def divmod_monic(f, Phi):
    """f = q*Phi + r with deg r < deg Phi; Phi monic, so exact over O."""
    f, Phi = ptrim(f), ptrim(Phi)
    dP = pdeg(Phi)
    assert dP >= 0 and Phi[-1] == 1, "key must be monic"
    r = list(f)
    q = [0] * max(0, pdeg(f) - dP + 1)
    while pdeg(r) >= dP:
        d = pdeg(r) - dP
        c = r[-1]
        q[d] = c
        r = psub(r, pmul([0] * d + [c], Phi))
    return ptrim(q), ptrim(r)

def dev(f, Phi):
    """Phi-adic development: f = sum_j digits[j] Phi^j, deg digits[j] < deg Phi."""
    digits = []
    cur = ptrim(f)
    while ptrim(cur):
        q, r = divmod_monic(cur, Phi)
        digits.append(r)
        cur = q
    return digits

def fmt(f):
    f = ptrim(f)
    if not f:
        return "0"
    terms = []
    for i in range(len(f) - 1, -1, -1):
        c = f[i]
        if c == 0:
            continue
        if i == 0:
            terms.append(f"{c:+d}")
        elif i == 1:
            terms.append(f"{c:+d}x" if abs(c) != 1 else ("+x" if c > 0 else "-x"))
        else:
            terms.append(f"{c:+d}x^{i}" if abs(c) != 1 else
                         (f"+x^{i}" if c > 0 else f"-x^{i}"))
    s = "".join(terms)
    return s[1:] if s.startswith("+") else s

# ------------------------------------------------------------------ instances

def amin(k, e0, h0):
    return -((-(e0 - k) * h0) // e0)          # ceil((e0-k)h0/e0)

# irreducible monic Phi0 mod p of degree d0 (checked below)
PHI0 = {
    (2, 1): [0, 1],            # x
    (2, 2): [1, 1, 1],         # x^2+x+1
    (2, 3): [1, 1, 0, 1],      # x^3+x+1
    (3, 1): [1, 1],            # x+1
    (3, 2): [1, 0, 1],         # x^2+1
    (3, 3): [1, 2, 0, 1],      # x^3+2x+1
    (5, 1): [0, 1],            # x
    (5, 2): [2, 0, 1],         # x^2+2
    (5, 3): [1, 1, 0, 1],      # x^3+x+1
}

def irreducible_mod_p(Phi, p):
    d = pdeg(Phi)
    if d <= 0:
        return False
    if d == 1:
        return True
    for r in range(p):                       # no roots
        val = sum(c * pow(r, i, p) for i, c in enumerate(Phi)) % p
        if val == 0:
            return False
    if d <= 3:
        return True
    raise NotImplementedError("degree >= 4 irreducibility not checked")

def make_instance(name, p, d0, e0, h0, e1, h1, genre):
    """genre: 'pure'  = the standard lift Phi'' (t0 = 0, all mids 0);
              'dense' = tail t0 != 0 at w0 = h0+1 and every mid at w0 = amin(k),
                        each mid of FULL degree d0-1 with unit leading coeff
                        (the genre that makes q-children exist);
              'midonly' = mids dense, tail 0 (the recorded counter-instance's
                        genre);
              'tailonly' = tail dense, mids 0."""
    assert gcd(e0, h0) == 1 and e0 >= 2 and h0 >= 1
    assert gcd(e1, h1) == 1 and e1 >= 1 and h1 >= 1
    Phi0 = PHI0[(p, d0)]
    assert irreducible_mod_p(Phi0, p)
    chat = [1] if d0 == 1 else [1, 1]        # residue 1 or x+1, both nonzero
    b = []
    t0 = []
    if genre in ('dense', 'tailonly'):
        t0 = pscal(p ** (h0 + 1), [1] * d0)  # w0 = h0+1, full degree
    b0 = padd(pscal(p ** h0, chat), t0)
    b.append(b0)
    for k in range(1, e0):
        if genre in ('dense', 'midonly'):
            g = [0] * (d0 - 1) + [1]         # x^{d0-1}, unit leading coeff
            g = padd(g, [k % p if d0 > 1 else 1])
            b.append(pscal(p ** amin(k, e0, h0), g))
        else:
            b.append([])
    # lawfulness assertions (S1)
    assert w0(b0, p) == h0, (name, "w0(b0) must be exactly h0")
    for k in range(1, e0):
        if ptrim(b[k]):
            assert w0(b[k], p) >= amin(k, e0, h0), (name, k, "mid below amin")
    Phip = ppow(Phi0, e0)
    for k in range(e0):
        Phip = padd(Phip, pmul(b[k], ppow(Phi0, k)))
    return dict(name=name, p=p, d0=d0, e0=e0, h0=h0, e1=e1, h1=h1,
                genre=genre, Phi0=Phi0, b=b, chat=chat, t0=t0, Phip=Phip,
                gamma2=e1 * e0 * h0 + h1)


def instances():
    I = []
    add = lambda *a: I.append(make_instance(*a))
    # ---- the RECORDED COUNTER-INSTANCE (passPE1 F1), verbatim -------------
    # Z_2, d0=2, e0=2, h0=1, Phi0=x^2+x+1, b0 = 2 (c'=1), b1 = 2x
    ctr = make_instance('CTR', 2, 2, 2, 1, 1, 1, 'midonly')
    ctr['b'] = [[2], [0, 2]]                 # b0 = 2, b1 = 2x  (exactly as recorded)
    ctr['chat'], ctr['t0'] = [1], []
    Phip = ppow(ctr['Phi0'], 2)
    for k in range(2):
        Phip = padd(Phip, pmul(ctr['b'][k], ppow(ctr['Phi0'], k)))
    ctr['Phip'] = Phip
    I.append(ctr)
    # ---- e0 = 2, THE BOUNDARY (where mid[e0-1] = mid[1] = the top mid) ----
    add('A1', 2, 2, 2, 1, 2, 1, 'dense')
    add('A2', 2, 2, 2, 3, 1, 1, 'dense')
    add('A3', 2, 3, 2, 1, 3, 2, 'dense')
    add('A4', 2, 1, 2, 1, 1, 1, 'dense')     # d0 = 1: no q-children possible
    add('A5', 3, 2, 2, 1, 1, 1, 'dense')
    add('A6', 3, 2, 2, 3, 2, 1, 'midonly')
    add('A7', 3, 3, 2, 1, 1, 1, 'dense')
    add('A8', 3, 1, 2, 3, 1, 1, 'dense')
    add('A9', 5, 2, 2, 1, 2, 3, 'dense')
    add('A10', 5, 3, 2, 3, 1, 1, 'dense')
    add('A11', 5, 1, 2, 1, 1, 1, 'tailonly')
    add('A12', 2, 2, 2, 1, 1, 1, 'pure')     # the standard lift Phi''
    add('A13', 3, 3, 2, 5, 1, 2, 'tailonly')
    # ---- e0 >= 3 ---------------------------------------------------------
    add('B1', 2, 2, 3, 1, 1, 1, 'dense')
    add('B2', 2, 2, 3, 2, 2, 1, 'dense')
    add('B3', 2, 3, 3, 1, 1, 1, 'dense')
    add('B4', 3, 2, 3, 1, 1, 1, 'midonly')
    add('B5', 3, 3, 3, 2, 3, 1, 'dense')
    add('B6', 5, 2, 3, 2, 1, 1, 'dense')
    add('B7', 2, 2, 4, 1, 1, 1, 'dense')
    add('B8', 2, 3, 4, 3, 2, 1, 'dense')
    add('B9', 3, 2, 4, 3, 1, 1, 'dense')
    add('B10', 5, 3, 4, 1, 1, 3, 'dense')
    add('B11', 2, 3, 5, 2, 1, 1, 'dense')
    add('B12', 3, 2, 5, 3, 2, 1, 'dense')
    add('B13', 5, 2, 5, 4, 1, 1, 'dense')
    add('B14', 2, 2, 5, 1, 1, 1, 'pure')
    add('B15', 3, 3, 6, 5, 1, 1, 'dense')
    return I

# ------------------------------------------------------------- the ONE PASS

def omega(inst, wa, m, j):
    if wa == INF:
        return INF
    return inst['e1'] * (inst['e0'] * wa + m * inst['h0']) + j * inst['gamma2']

def children(inst, a, m, j):
    """One pass of the orbit identity on X = a Phi0^m Phi'^j (m >= e0).
    Returns the list of children as dicts (zero digits are RECORDED as
    genre-with-no-child, i.e. skipped, since a zero summand has no digits)."""
    p, d0, e0, Phi0 = inst['p'], inst['d0'], inst['e0'], inst['Phi0']
    assert m >= e0 and pdeg(a) < d0
    out = []
    # 1. key child (coefficient unchanged)
    out.append(dict(genre='key', k=None, digit='-', coef=a, m=m - e0, j=j + 1))
    # 2. b0 branch, split main / tail
    parts = [('b0-main', pmul(a, pscal(p ** inst['h0'], inst['chat'])), 0),
             ('b0-tail', pmul(a, inst['t0']), 0)]
    # 3. mid branches
    for k in range(1, e0):
        parts.append((f'mid[{k}]', pmul(a, inst['b'][k]), k))
    for label, P, k in parts:
        if not ptrim(P):
            continue
        q, r = divmod_monic(P, Phi0)
        if ptrim(r):
            out.append(dict(genre=f'{label}-r', k=k, digit='r',
                            coef=pscal(-1, r), m=m - e0 + k, j=j))
        if ptrim(q):
            out.append(dict(genre=f'{label}-q', k=k, digit='q',
                            coef=pscal(-1, q), m=m - e0 + k + 1, j=j))
    return out

def norm_genre(ch, e0):
    """Genre label collapsed across instances: the mid branches are split into
    the TOP mid (k = e0-1, the only place m' = m can happen) and the lower mids
    (k < e0-1).  This normalized list IS the proof's required case list."""
    if ch['k'] in (None, 0):
        return ch['genre']
    top = 'mid[TOP=e0-1]' if ch['k'] == e0 - 1 else 'mid[k<e0-1]'
    return f"{top}-{ch['digit']}"


def lex_delta(m, da, m2, da2):
    if m2 < m:
        return 'm-DROP'
    if m2 > m:
        return 'm-RISE(!)'
    if da2 < da:
        return 'degA-DROP'
    return 'NO-DESCENT(!)'

# ------------------------------------------------------------ LEDGER (A6)

def ledger_check(inst, a, m, j):
    """Honest double development of X = a Phi0^m Phi'^j: dev by Phi', then each
    Phi'-digit by Phi0.  Returns (ok, worst_slack, ndigits)."""
    p, Phi0, Phip = inst['p'], inst['Phi0'], inst['Phip']
    X = pmul(a, pmul(ppow(Phi0, m), ppow(Phip, j)))
    om = omega(inst, w0(a, p), m, j)
    worst, n = None, 0
    for jj, A in enumerate(dev(X, Phip)):
        for ii, aji in enumerate(dev(A, Phi0)):
            if not ptrim(aji):
                continue
            n += 1
            wt = inst['e1'] * (inst['e0'] * w0(aji, p) + ii * inst['h0']) \
                 + jj * inst['gamma2']
            slack = wt - om
            worst = slack if worst is None else min(worst, slack)
    return (worst is None or worst >= 0), worst, n

# ------------------------------------------------------------------ the table

def probe_coefs(inst):
    """One a per available degree 0..d0-1 (deg a < d0), with a unit leading
    coefficient (the worst case for q-child creation)."""
    d0, p = inst['d0'], inst['p']
    out = []
    for da in range(d0):
        a = [0] * da + [1]
        if da >= 1:
            a[0] = 1                          # x^da + 1, unit lc
        out.append(a)
    # one pi-scaled probe (w0(a) > 0): omega is w0-shift-covariant, but this
    # exercises the CONTENT sub-lemma's use inside the LEDGER check honestly.
    out.append(pscal(p, out[-1]))
    return out

def run(table_path):
    rows, fails, genre_stat, ledger_stat = [], [], {}, []
    nochild_m_eq = []           # every m' = m child, recorded
    insts = instances()
    for inst in insts:
        e0 = inst['e0']
        for a in probe_coefs(inst):
            da = pdeg(a)
            for m in [e0, e0 + 1, 2 * e0, 2 * e0 + 1]:
                for j in (0, 1):
                    ok, slack, nd = ledger_check(inst, a, m, j)
                    ledger_stat.append((inst['name'], da, m, j, ok, slack, nd))
                    if not ok:
                        fails.append(f"A6 LEDGER violated: {inst['name']} "
                                     f"a={fmt(a)} m={m} j={j} slack={slack}")
                    if j:                     # child table is j-independent
                        continue
                    om = omega(inst, w0(a, inst['p']), m, j)
                    for ch in children(inst, a, m, j):
                        da2 = pdeg(ch['coef'])
                        d = lex_delta(m, da, ch['m'], da2)
                        g = omega(inst, w0(ch['coef'], inst['p']),
                                  ch['m'], ch['j']) - om
                        rows.append(dict(inst=inst['name'], p=inst['p'],
                                         d0=inst['d0'], e0=e0, h0=inst['h0'],
                                         genre=inst['genre'], a=fmt(a), da=da,
                                         m=m, cg=ch['genre'], m2=ch['m'],
                                         da2=da2, delta=d, gain=g,
                                         coef=fmt(ch['coef'])))
                        gs = genre_stat.setdefault(norm_genre(ch, e0),
                                                   dict(n=0, deltas={},
                                                        gains=set()))
                        gs['n'] += 1
                        gs['deltas'][d] = gs['deltas'].get(d, 0) + 1
                        gs['gains'].add(g)
                        # --- the assertions -------------------------------
                        if d == 'NO-DESCENT(!)' or d == 'm-RISE(!)':
                            fails.append(f"A1 lex descent FAILS: {inst['name']}"
                                         f" a={fmt(a)} m={m} -> {ch['genre']}"
                                         f" (m'={ch['m']}, deg a'={da2})")
                        if ch['m'] == m:
                            nochild_m_eq.append((inst['name'], inst['d0'], e0,
                                                 fmt(a), da, m, ch['genre'],
                                                 da2, g))
                            if not (ch['genre'] == f'mid[{e0-1}]-q'):
                                fails.append(f"A2 m'=m child of UNEXPECTED "
                                             f"genre {ch['genre']} "
                                             f"({inst['name']})")
                            if da2 > da - 1:
                                fails.append(f"A2 m'=m child does NOT drop "
                                             f"deg a: {inst['name']} {da}->{da2}")
                            if da == 0:
                                fails.append(f"A3 m'=m child at deg a = 0: "
                                             f"{inst['name']}")
                            if inst['d0'] == 1:
                                fails.append(f"A4 m'=m child at d0 = 1: "
                                             f"{inst['name']}")
                        if g < 0:
                            fails.append(f"A5 negative omega-gain: "
                                         f"{inst['name']} {ch['genre']} {g}")
                        if g == 0 and ch['genre'] != 'b0-main-r':
                            fails.append(f"A5 gain-0 genre other than "
                                         f"b0-main-r: {ch['genre']} "
                                         f"({inst['name']})")
    return insts, rows, genre_stat, ledger_stat, nochild_m_eq, fails

# ------------------------------------------- the counter-instance descent tree

def descent_tree(inst, a, m, j, depth=0, lines=None, budget=[400]):
    if lines is None:
        lines = []
    p = inst['p']
    om = omega(inst, w0(a, p), m, j)
    tag = (f"{'  ' * depth}(m={m}, deg a={pdeg(a)}) a={fmt(a)} j={j} "
           f"w0(a)={w0(a,p)} omega={om}")
    if m < inst['e0']:
        lines.append(tag + "   [BASE: m < e0, single digit, ledger EQUALITY]")
        return lines
    lines.append(tag + "   [STEP]")
    for ch in children(inst, a, m, j):
        g = omega(inst, w0(ch['coef'], p), ch['m'], ch['j']) - om
        d = lex_delta(m, pdeg(a), ch['m'], pdeg(ch['coef']))
        lines.append(f"{'  ' * (depth+1)}--{ch['genre']}-> "
                     f"(m'={ch['m']}, deg a'={pdeg(ch['coef'])}) "
                     f"coef={fmt(ch['coef'])} j'={ch['j']} gain=+{g} [{d}]")
        budget[0] -= 1
        if budget[0] > 0:
            descent_tree(inst, ch['coef'], ch['m'], ch['j'], depth + 2, lines,
                         budget)
    return lines

# ------------------------------------------------------------------ reporting

def main():
    table_path = 'liftcorner_tailstab_children_table.txt'
    if '--table' in sys.argv:
        table_path = sys.argv[sys.argv.index('--table') + 1]
    insts, rows, genre_stat, ledger_stat, m_eq, fails = run(table_path)
    L = []
    W = L.append
    W("LIFT-CORNER (TAIL-STAB) CHILD-TYPE TABLE — examples-first artifact")
    W("generator: verification/openmath/liftcorner_tailstab_children.py")
    W("target lemma: LIFTCORNER_2026-08-08.md S4.1 (TAIL-STAB), repair round r1")
    W("")
    W("=== 1. INSTANCE ROSTER (towers) ===")
    W(f"{'inst':5} {'p':>2} {'d0':>3} {'e0':>3} {'h0':>3} {'e1':>3} {'h1':>3} "
      f"{'gam2':>5} {'genre':9} Phi0            Phi'")
    for I in insts:
        W(f"{I['name']:5} {I['p']:2d} {I['d0']:3d} {I['e0']:3d} {I['h0']:3d} "
          f"{I['e1']:3d} {I['h1']:3d} {I['gamma2']:5d} {I['genre']:9} "
          f"{fmt(I['Phi0']):15} {fmt(I['Phip'])}")
    W(f"total towers: {len(insts)}   "
      f"p in {sorted(set(I['p'] for I in insts))}   "
      f"d0 in {sorted(set(I['d0'] for I in insts))}   "
      f"e0 in {sorted(set(I['e0'] for I in insts))}   "
      f"genres {sorted(set(I['genre'] for I in insts))}")
    W("")
    W("=== 2. FULL CHILD TABLE (one row per child; j = 0 shown, j-independent) ===")
    W("inst   p d0 e0 a          dA   m | child genre    m2 dA2 lex delta    "
      " gain coef2      (m2 = m', dA2 = deg a', coef2 = the child's a')")
    for r in rows:
        W(f"{r['inst']:5} {r['p']:2d} {r['d0']:2d} {r['e0']:2d} {r['a']:10} "
          f"{r['da']:2d} {r['m']:3d} | {r['cg']:13} {r['m2']:3d} {r['da2']:3d} "
          f"{r['delta']:12} {r['gain']:5d} {r['coef']}")
    W(f"total child rows: {len(rows)}")
    W("")
    W("=== 3. GENRE SUMMARY (the case list the proof must match) ===")
    W(f"{'child genre':16} {'count':>6}  {'lex deltas observed':40} "
      f"omega-gains observed")
    for g in sorted(genre_stat):
        s = genre_stat[g]
        W(f"{g:16} {s['n']:6d}  "
          f"{str(sorted(s['deltas'].items())):40} "
          f"{sorted(s['gains'])[:6]}{'...' if len(s['gains'])>6 else ''}")
    W("")
    W("=== 4. THE m' = m CHILDREN (the F1 stratum) ===")
    W("inst  d0 e0 a          dA   m child genre   dA2  gain")
    for t in m_eq:
        W(f"{t[0]:5} {t[1]:2d} {t[2]:2d} {t[3]:10} {t[4]:2d} {t[5]:3d} "
          f"{t[6]:13} {t[7]:3d} {t[8]:5d}")
    W(f"total m'=m children: {len(m_eq)}; "
      f"genres: {sorted(set(t[6] for t in m_eq))}; "
      f"all with deg a' < deg a: {all(t[7] < t[4] for t in m_eq)}; "
      f"all with deg a >= 1: {all(t[4] >= 1 for t in m_eq)}; "
      f"all with d0 >= 2: {all(t[1] >= 2 for t in m_eq)}; "
      f"min gain: {min([t[8] for t in m_eq], default=None)}")
    W("")
    W("=== 5. LEDGER (A6) on the honest double development ===")
    okall = all(t[4] for t in ledger_stat)
    W(f"probes: {len(ledger_stat)}   all LEDGER-clean: {okall}   "
      f"digits inspected: {sum(t[6] for t in ledger_stat)}   "
      f"min slack over all digits: {min(t[5] for t in ledger_stat if t[5] is not None)}")
    W("(slack = digit weight - omega(X); 0 = the equality thread, > 0 = strictly above)")
    W("")
    W("=== 6. THE RECORDED COUNTER-INSTANCE, DESCENT CHAIN (passPE1 F1) ===")
    ctr = [I for I in insts if I['name'] == 'CTR'][0]
    W(f"CTR: O = Z_2, d0 = 2, e0 = 2, h0 = 1, Phi0 = {fmt(ctr['Phi0'])}, "
      f"b0 = {fmt(ctr['b'][0])} (c' = 1), b1 = {fmt(ctr['b'][1])}, "
      f"Phi' = {fmt(ctr['Phip'])}")
    W("X = a Phi0^m Phi'^j with a = x, m = 2, j = 0 "
      "(e1 = h1 = 1, gamma2 = e1 e0 h0 + h1 = 3):")
    for ln in descent_tree(ctr, [0, 1], 2, 0):
        W(ln)
    W("")
    W("=== 7. VERDICT ===")
    for f in fails:
        W("FAIL: " + f)
    W(f"assertion failures: {len(fails)}")
    W("A1 lex (m, deg a) strict descent on EVERY child: "
      f"{'PASS' if not any(x.startswith('A1') for x in fails) else 'FAIL'}")
    W("A2 every m'=m child is genre mid[e0-1]-q with deg a' <= deg a - 1: "
      f"{'PASS' if not any(x.startswith('A2') for x in fails) else 'FAIL'}")
    W("A3 no m'=m child at deg a = 0: "
      f"{'PASS' if not any(x.startswith('A3') for x in fails) else 'FAIL'}")
    W("A4 no m'=m child at d0 = 1: "
      f"{'PASS' if not any(x.startswith('A4') for x in fails) else 'FAIL'}")
    W("A5 omega-gain >= 0, gain 0 only at b0-main-r: "
      f"{'PASS' if not any(x.startswith('A5') for x in fails) else 'FAIL'}")
    W("A6 LEDGER on the honest double development: "
      f"{'PASS' if not any(x.startswith('A6') for x in fails) else 'FAIL'}")
    W("")
    W(f"ANY CHILD DROPPING NEITHER COORDINATE: "
      f"{'YES' if any('NO-DESCENT' in r['delta'] for r in rows) else 'NO'}")
    W(f"OVERALL: {'ALL GREEN' if not fails else 'VIOLATIONS PRESENT'}")
    out = "\n".join(L) + "\n"
    with open(table_path, 'w') as fh:
        fh.write(out)
    print(out)
    return 1 if fails else 0

if __name__ == '__main__':
    sys.exit(main())
