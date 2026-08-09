#!/usr/bin/env python3
"""GENHN passPE2 fresh instrument (hostile verifier, 2026-08-09).

FRESH ROUTE, disjoint from the sealed battery, PE1's legs, and
genhnr2_supp.py's sweeps (supp: outer-f1=1 genres (2,1,4)->(2,1,2)
u2=5,7 and (2,1,4)->(1,2,2), + 3-stage n=16; its TRUE-read decided
rows were tRAM/t2SIDED(3-stage) only).  This pass tests:

 PE2-K  composed-carrier legs for LEMMA GENHN-T(b)'(i): each composed
        key Phi2 is irreducible with (e,f) = (e1e2, f1f2) and
        v_L(Phi'(xi)) = u2 EXACTLY (nfeltval), at the BOUNDARY
        u2 = e2*D'h + 1 of the [r1] node floor.  5 keys, incl. the
        first outer-f1=2 tower keys (1,2,4)->(2,1,2).
 PE2-S  composed slot lemma GENHN-2'(ii) EXACTNESS, directly:
        random + tie-constructed A(x), formula slot-min vs
        PARI nfeltval, at genre A(u2=5) and the f1=2 genre F1b.
 PE2-D  T(b)'(iii) dictionary branches with ZERO prior 2-stage TRUE
        contact: composed-INERT and composed-2SIDED at genre A;
        RAM/INERT/SPLIT/2SIDED at the outer-f1=2 genres F1a
        (psi2 = T-1) and F1b (psi2 = T-eta, eta-letter key), incl.
        the eta2-cocycle division at odd w (T-COCYCLE tooth).
 PE2-P  [GENHN-TOW-1] item (4) honesty: a PARTIAL inner side member
        at n = 10 (genre (2,1,5), side length 4 < mu1 = 5): the
        corrected read must NOT apply (non-monic composed dev), and
        PARI exhibits the sibling x tower composite sigma.
 PE2-Q  first NON-PRIME-q tower contact: Q = 4 (base Q(w)/2 inert,
        residue F4), genre (2,1,4)->(2,1,2) with w-letters, absolute
        degree 16 via rnfequation; RAM/INERT/SPLIT/2SIDED.
 TEETH  T-DICT (swapped INERT prediction refused by PARI),
        T-SLOT (wrong-offset slot formula refused by nfeltval),
        T-COCYCLE (naive residual read without the eta2-division
        mispredicts the F1b odd-w instance),
        T-PARSE (a side-violating construction is rejected).
VERDICT: GREEN iff 0 violations on scored checks and all 4 teeth.
Independent: no imports from battery/supp; own readers.
"""
import random, subprocess, sys, time, json

random.seed(20260809)
VIOL = []; NCHK = {}; OUT = []
def say(s):
    print(s); sys.stdout.flush(); OUT.append(s)
def chk(fam, ok, msg):
    NCHK[fam] = NCHK.get(fam, 0) + 1
    if not ok:
        VIOL.append((fam, msg)); say('  !! VIOLATION [%s] %s' % (fam, msg))

def v2(n):
    n = abs(n); assert n != 0
    k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k

# ---- integer polys ----
def pstrip(f):
    while f and f[-1] == 0: f = f[:-1]
    return f
def padd(f, g):
    n = max(len(f), len(g))
    return pstrip([(f[i] if i < len(f) else 0)+(g[i] if i < len(g) else 0) for i in range(n)])
def pmul(f, g):
    if not f or not g: return []
    out = [0]*(len(f)+len(g)-1)
    for i, a in enumerate(f):
        for j, b in enumerate(g): out[i+j] += a*b
    return pstrip(out)
def pdiv(f, g):
    f = list(f); dg = len(g)-1; assert g[-1] == 1
    q = [0]*max(1, len(f)-dg)
    for i in range(len(f)-1, dg-1, -1):
        c = f[i]
        if c:
            q[i-dg] += c
            for j, gj in enumerate(g): f[i-dg+j] -= c*gj
    return pstrip(q), pstrip(f[:dg])

# ---- F4 = F2[eta], elements (s,t) ----
def f4_mul(a, b):
    s = (a[0]&b[0]) ^ (a[1]&b[1])
    t = (a[0]&b[1]) ^ (a[1]&b[0]) ^ (a[1]&b[1])
    return (s, t)
def f4_add(a, b): return (a[0]^b[0], a[1]^b[1])
F4 = [(0,0),(1,0),(0,1),(1,1)]
def f4_inv(a):
    for z in F4[1:]:
        if f4_mul(a, z) == (1,0): return z
    raise ValueError
def quad_roots_f4(r1, r0):
    return [z for z in F4 if f4_add(f4_add(f4_mul(z,z), f4_mul(r1,z)), r0) == (0,0)]

# ---- genre A: outer (2,1,4) Phi' = x^2-2, inner (2,1,2) u2=5 ----
PHIA = [-2, 0, 1]
PHI2A = padd(pmul(PHIA, PHIA), [0, -4])          # (x^2-2)^2 - 4x
def phidev(f, key, mu):
    A = []
    for _ in range(mu):
        f, r = pdiv(f, key); A.append(r)
    A.append(f); return A
def compA(C):
    C = list(C)+[0]*(4-len(C))
    return {'1': C[0]+2*C[2], 'x': C[1]+2*C[3], 'p': C[2], 'xp': C[3]}
OFFA = {'1': 0, 'x': 2, 'p': 5, 'xp': 7}
def dv2A(C):
    b = compA(C)
    c = [4*v2(v)+OFFA[k] for k, v in b.items() if v]
    return min(c) if c else None
def resA(C, m):
    """K2 = F2 residue-existence at height m (digits are 0/1)."""
    b = compA(C)
    return sum(1 for k, v in b.items() if v and 4*v2(v)+OFFA[k] == m) % 2
def read_A(f):
    q1, C0 = pdiv(f, PHI2A); q2, C1 = pdiv(q1, PHI2A)
    if q2 != [1]: return None
    u, w = dv2A(C0), dv2A(C1)
    if u is None: return (u, w, 'DRAIN', None)
    if w is None or u < 2*w:
        return (u, w, 'tRAM', [(8,1)]) if u % 2 else (u, w, 'tEVEN', None)
    if u == 2*w:
        return (u, w, 'tINERT', [(4,2)])   # F2: residues 1,1 -> T^2+T+1
    return (u, w, 't2SIDED', [(4,1),(4,1)])
def parse_A(f, mu, wantdv0, side_num, side_den, lat_zero):
    """level-1 gate: A_mu=1, dv(A0) exact, mids strictly above side,
    lattice residues at lat_zero must vanish (residual (T-1)^mu2)."""
    A = phidev(f, PHIA, mu)
    if A[mu] != [1]: return None, 'not monic'
    dvs = []
    for a in A[:mu]:
        c = [2*v2(cc)+i for i, cc in enumerate(a) if cc]
        dvs.append(min(c) if c else None)
    if dvs[0] != wantdv0: return None, 'dv(A0)=%s want %s' % (dvs[0], wantdv0)
    for J in range(1, mu):
        if dvs[J] is not None and dvs[J]*side_den <= side_num*(mu-J) and J in lat_zero:
            return None, 'pin J=%d below/on side' % J
    return dvs, None

# ---- genres F1a/F1b: outer (1,2,4) Phi' = x^2+2x+4 (K = F4), ----
# ---- inner (2,1,2) at u2 = 5; psi2 = T-1 (F1a) / T-eta (F1b) ----
PHIF = [4, 2, 1]
PHI2F = {'a': padd(pmul(PHIF, PHIF), [-32]),      # Phi'^2 - 32
         'b': padd(pmul(PHIF, PHIF), [0, -16])}   # Phi'^2 - 16x
ETA2 = {'a': (1, 0), 'b': (0, 1)}
def compF(C):
    """x^2 = Phi' - 2x - 4;  x^3 = x*Phi' - 2*Phi' + 8."""
    C = list(C)+[0]*(4-len(C))
    return {'1': C[0]-4*C[2]+8*C[3], 'x': C[1]-2*C[2],
            'p': C[2]-2*C[3], 'xp': C[3]}
OFFF = {'1': 0, 'x': 2, 'p': 5, 'xp': 7}
FLAVF = {'1': (1,0), 'x': (0,1), 'p': (1,0), 'xp': (0,1)}
def slotF(C):
    """(min height, F4 residue on the in-parity basis)."""
    b = compF(C)
    hs = [(2*v2(v)+OFFF[k], k) for k, v in b.items() if v]
    if not hs: return None, None
    m = min(h for h, _ in hs)
    r = (0, 0)
    for h, k in hs:
        if h == m: r = f4_add(r, FLAVF[k])
    return m, r
def read_F(f, var, cocycle=True):
    key = PHI2F[var]
    q1, C0 = pdiv(f, key); q2, C1 = pdiv(q1, key)
    if q2 != [1]: return None
    u, r0 = slotF(C0); w, r1 = slotF(C1)
    if u is None: return (u, w, 'DRAIN', None)
    if w is None or u < 2*w:
        return (u, w, 'tRAM', [(4,2)]) if u % 2 else (u, w, 'tEVEN', None)
    if u == 2*w:
        if w % 2 and cocycle:                     # n(w)^2 = 2^w * eta2
            r0 = f4_mul(r0, f4_inv(ETA2[var]))
        if r1 == (0,0): return (u, w, 'tDBL', None)
        rt = quad_roots_f4(r1, r0)
        if rt: return (u, w, 'tSPLIT', [(2,2),(2,2)])
        return (u, w, 'tINERT', [(2,4)])
    return (u, w, 't2SIDED', [(2,2),(2,2)])
def parse_F(f, var):
    """level-1 gate at (1,2,4): dv = v, A_4 = 1, dv(A0) = 10 with
    residue = c0^2 ((T-c0)^2 residual), dv(A1)>=8, dv(A2)>=6, A3>=3."""
    A = phidev(f, PHIF, 4)
    if A[4] != [1]: return None, 'not monic'
    dvs, ress = [], []
    for a in A[:4]:
        a = list(a)+[0]*(2-len(a))
        hs = [(v2(a[0]), (1,0)) if a[0] else None,
              (v2(a[1])+1, (0,1)) if a[1] else None]
        hs = [h for h in hs if h]
        if not hs: dvs.append(None); ress.append(None); continue
        m = min(h for h, _ in hs)
        r = (0,0)
        for h, fl in hs:
            if h == m: r = f4_add(r, fl)
        dvs.append(m); ress.append(r)
    c0sq = f4_mul(ETA2[var], ETA2[var])
    if dvs[0] != 10 or ress[0] != c0sq:
        return None, 'A0 (dv,res)=(%s,%s) want (10,%s)' % (dvs[0], ress[0], c0sq)
    for J, fl in [(1, 8), (2, 6), (3, 3)]:
        if dvs[J] is not None and dvs[J] < fl:
            return None, 'dv(A%d)=%s < %d' % (J, dvs[J], fl)
    return dvs, None

# ---- Z[w] layer (w^2 = -1-w), residue F4, 2 inert ----
def wadd(a, b): return (a[0]+b[0], a[1]+b[1])
def wmul(a, b):
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def wint(n): return (n, 0)
def wiszero(a): return a == (0, 0)
def v2w(a):
    vs = [v2(c) for c in a if c]
    return min(vs) if vs else None
def resw(a):
    v = v2w(a)
    return ((abs(a[0]) >> v) & 1 if a[0] else 0,
            (abs(a[1]) >> v) & 1 if a[1] else 0)
def wpstrip(f):
    while f and wiszero(f[-1]): f = f[:-1]
    return f
def wpadd(f, g):
    n = max(len(f), len(g))
    z = (0, 0)
    return wpstrip([wadd(f[i] if i < len(f) else z, g[i] if i < len(g) else z) for i in range(n)])
def wpmul(f, g):
    if not f or not g: return []
    out = [(0,0)]*(len(f)+len(g)-1)
    for i, a in enumerate(f):
        for j, b in enumerate(g): out[i+j] = wadd(out[i+j], wmul(a, b))
    return wpstrip(out)
def wpdiv(f, g):
    f = list(f); dg = len(g)-1; assert g[-1] == (1, 0)
    q = [(0,0)]*max(1, len(f)-dg)
    for i in range(len(f)-1, dg-1, -1):
        c = f[i]
        if not wiszero(c):
            q[i-dg] = wadd(q[i-dg], c)
            for j, gj in enumerate(g):
                f[i-dg+j] = wadd(f[i-dg+j], wmul((-c[0], -c[1]), gj))
    return wpstrip(q), wpstrip(f[:dg])
PHIA_W = [(-2,0), (0,0), (1,0)]
PHI2A_W = wpadd(wpmul(PHIA_W, PHIA_W), [(0,0), (-4,0)])
def compA_W(C):
    C = list(C)+[(0,0)]*(4-len(C))
    return {'1': wadd(C[0], wmul(wint(2), C[2])),
            'x': wadd(C[1], wmul(wint(2), C[3])), 'p': C[2], 'xp': C[3]}
def slotQ(C):
    b = compA_W(C)
    hs = [(4*v2w(v)+OFFA[k], k) for k, v in b.items() if not wiszero(v)]
    if not hs: return None, None
    m = min(h for h, _ in hs)
    r = (0, 0)
    for h, k in hs:
        if h == m: r = f4_add(r, resw(b[k]))
    return m, r
def read_Q(f):
    """genre A over Z[w] (Q = 4, K2 = F4, eta2 = 1); returns ABS sigma
    over Q (compose with the inert base: f_abs = 2*f_rel)."""
    q1, C0 = wpdiv(f, PHI2A_W); q2, C1 = wpdiv(q1, PHI2A_W)
    if q2 != [(1, 0)]: return None
    u, r0 = slotQ(C0); w, r1 = slotQ(C1)
    if u is None: return (u, w, 'DRAIN', None)
    if w is None or u < 2*w:
        return (u, w, 'tRAM', [(8,2)]) if u % 2 else (u, w, 'tEVEN', None)
    if u == 2*w:
        if r1 == (0,0): return (u, w, 'tDBL', None)
        rt = quad_roots_f4(r1, r0)                # eta2 = 1: no division
        if rt: return (u, w, 'tSPLIT', [(4,2),(4,2)])
        return (u, w, 'tINERT', [(4,4)])
    return (u, w, 't2SIDED', [(4,2),(4,2)])
def parse_Q(f):
    A = phidev_w(f)
    if A[4] != [(1,0)]: return None, 'not monic'
    dvs = []
    for a in A[:4]:
        c = [2*v2w(cc)+i for i, cc in enumerate(a) if not wiszero(cc)]
        dvs.append(min(c) if c else None)
    if dvs[0] != 10: return None, 'dv(A0)=%s want 10' % dvs[0]
    for J in range(1, 4):
        if dvs[J] is not None and 2*dvs[J] <= 5*(4-J):
            return None, 'pin J=%d below/on side' % J
    return dvs, None
def phidev_w(f):
    A = []
    for _ in range(4):
        f, r = wpdiv(f, PHIA_W); A.append(r)
    A.append(f); return A

# ---- PARI ----
GP_HDR = r"""
sig1(f) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) == 1,
        listput(out, [1, 1]),
        my(nf = nfinit([g, [2]]), dec = idealprimedec(nf, 2));
        for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out))
}
ef2(g) = {
  my(nf = nfinit([g, [2]]), dec = idealprimedec(nf, 2));
  [dec[1].e, dec[1].f]
}
sig2(f) = {
  my(F = factorpadic(f, 2, 400));
  vecsort(vector(matsize(F)[1], i, ef2(liftall(F[i, 1]))))
}
KW = nfinit(w^2+w+1);
"""
def pstr(f):
    return '+'.join('(%d)*x^%d' % (c, i) for i, c in enumerate(f) if c) or '0'
def wpstr(f):
    ts = []
    for i, c in enumerate(f):
        if not wiszero(c):
            ts.append('(%d+(%d)*Mod(w,w^2+w+1))*x^%d' % (c[0], c[1], i))
    return '+'.join(ts) or '0'
def run_gp(lines):
    src = GP_HDR + '\n' + '\n'.join(lines) + '\nquit\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=900)
    if out.stderr.strip():
        say('  gp stderr tail: %s' % out.stderr[-300:])
    res = {}
    for line in out.stdout.splitlines():
        p = line.split(' ', 1)
        if len(p) == 2 and p[0]: res.setdefault(p[0], []).append(p[1])
    return res

def sig_parse(s):
    return sorted(tuple(t) for t in json.loads(s))

def main():
    t0 = time.time()
    say('=== GENHN passPE2 fresh: T(b)\' carrier/slot/dictionary at fresh genres ===')
    L = []   # gp lines

    # ---------- PE2-K: composed carrier keys ----------
    keys = [('A5', PHI2A, 4, 1, 5), ('A7', padd(pmul(PHIA, PHIA), [0, -8]), 4, 1, 7),
            ('B',  padd(padd(pmul(PHIA, PHIA), pmul([0, -2], PHIA)), [-8]), 2, 2, 3),
            ('F1a', PHI2F['a'], 2, 2, 5), ('F1b', PHI2F['b'], 2, 2, 5)]
    for i, (tag, P, e, fr, u2) in enumerate(keys):
        L.append('my(nf=nfinit([Pol(%s),[2]]),dec=idealprimedec(nf,2));'
                 'print("K%d ", #dec, " ", dec[1].e, " ", dec[1].f, " ", '
                 'nfeltval(nf, Pol(%s), dec[1]), " ", poldegree(nf.pol))'
                 % (pstr(P), i, pstr(PHIA if tag in ('A5','A7','B') else PHIF)))
    # ---------- PE2-S: slot exactness (genre A5 + F1b) ----------
    sjobs = []
    for g in range(30):
        C = [random.choice([0,1]) and (2**random.randint(0,6))*random.choice([1,3,5,7,-1,-3]) or 0
             for _ in range(4)]
        if not any(C): C[0] = 3
        sjobs.append(('A', C, dv2A(C)))
    for g in range(6):   # constructed within/cross-class ties at A
        v = random.randint(0, 5); od1, od2 = random.choice([1,3,5]), random.choice([1,3,-1])
        C = pstrip(padd([od1*2**(v+1), od2*2**v * random.choice([1,0])], [0,0,2**v*random.choice([1,3])]))
        sjobs.append(('A', C, dv2A(C)))
    for g in range(30):
        C = [random.choice([0,1]) and (2**random.randint(0,6))*random.choice([1,3,5,-1,-5]) or 0
             for _ in range(4)]
        if not any(C): C[1] = 5
        sjobs.append(('F', C, slotF(C)[0]))
    for g in range(6):   # eta-tie constructions at F1b: v(a0) = v(a1)+1
        v = random.randint(0, 5)
        C = [2**(v+1)*random.choice([1,3,5]), 2**v*random.choice([1,3,7]), 0, 0]
        sjobs.append(('F', C, slotF(C)[0]))
    for i, (gg, C, pred) in enumerate(sjobs):
        P = PHI2A if gg == 'A' else PHI2F['b']
        L.append('my(nf=nfinit([Pol(%s),[2]]),dec=idealprimedec(nf,2));'
                 'print("S%d ", nfeltval(nf, Pol(%s), dec[1]))'
                 % (pstr(P), i, pstr(C)))
    # ---------- PE2-D: dictionary instances ----------
    xp = lambda sc: [sc*random.randint(0, 15) for _ in range(8)]
    djobs = []   # (tag, genre, f, want_pins, want_lab, want_sig)
    def dA(tag, C1, C0, u, w, lab, sig):
        f = padd(padd(pmul(PHI2A, PHI2A), pmul(C1, PHI2A)), C0)
        djobs.append((tag, 'A', f, (u, w), lab, sig))
        fp = padd(f, xp(2**11))
        djobs.append((tag+'-pert', 'A', fp, (u, w), lab, sig))
    dA('A-INERT',  pmul([4], PHIA), [0, 192], 26, 13, 'tINERT', [(4,2)])
    dA('A-INERT2', pmul([4], PHIA), [0, 64],  26, 13, 'tINERT', [(4,2)])
    dA('A-2SIDED', [0, 8], [0, 128], 30, 14, 't2SIDED', [(4,1),(4,1)])
    dA('A-2SIDED2', [0, 8], [256],   32, 14, 't2SIDED', [(4,1),(4,1)])
    def dF(tag, var, C1, C0, u, w, lab, sig, pert=True):
        key = PHI2F[var]
        f = padd(padd(pmul(key, key), pmul(C1, key)), C0)
        djobs.append((tag, 'F'+var, f, (u, w), lab, sig))
        if pert:
            fp = padd(f, xp(2**14))
            djobs.append((tag+'-pert', 'F'+var, fp, (u, w), lab, sig))
    dF('F1a-RAM',    'a', [64], pmul([256], PHIF), 21, 12, 'tRAM', [(4,2)])
    dF('F1a-RAMxp',  'a', [64], pmul([0, 256], PHIF), 23, 12, 'tRAM', [(4,2)], False)
    dF('F1a-INERT',  'a', [64], [0, 2048], 24, 12, 'tINERT', [(2,4)])
    dF('F1a-SPLIT',  'a', [64], [4096], 24, 12, 'tSPLIT', [(2,2),(2,2)])
    dF('F1a-2SIDED', 'a', [64], [8192], 26, 12, 't2SIDED', [(2,2),(2,2)])
    dF('F1a-woddSPL', 'a', pmul([8], PHIF), [2048, 0], 22, 11, 'tSPLIT', [(2,2),(2,2)], False)
    dF('F1b-RAM',    'b', [64], pmul([256], PHIF), 21, 12, 'tRAM', [(4,2)])
    dF('F1b-INERT',  'b', [64], [0, 2048], 24, 12, 'tINERT', [(2,4)])
    dF('F1b-COCY',   'b', pmul([8], PHIF), [2048], 22, 11, 'tINERT', [(2,4)])
    dF('F1b-SPLIT',  'b', [64], [4096], 24, 12, 'tSPLIT', [(2,2),(2,2)], False)
    dF('F1b-2SIDED', 'b', [64], [8192], 26, 12, 't2SIDED', [(2,2),(2,2)], False)
    for i, (tag, gg, f, pins, lab, sig) in enumerate(djobs):
        if gg == 'A':
            dvs, err = parse_A(f, 4, 10, 5, 2, {1, 2, 3})
            rd = read_A(f)
        else:
            dvs, err = parse_F(f, gg[1])
            rd = read_F(f, gg[1])
        chk('PE2-D', err is None, '%s parse: %s' % (tag, err))
        ok = rd is not None and (rd[0], rd[1]) == pins and rd[2] == lab
        chk('PE2-D', ok, '%s read %s want %s %s' % (tag, rd, pins, lab))
        say('  PE2-D %s: pins %s %s -> %s' % (tag, pins, lab, sig))
        L.append('print("D%d ", poldisc(Pol(%s)) != 0, " ", sig1(Pol(%s)))'
                 % (i, pstr(f), pstr(f)))
        if not tag.endswith('pert'):
            L.append('print("E%d ", sig2(Pol(%s)))' % (i, pstr(f)))
    return t0, L, djobs, sjobs, keys

def main2(t0, L, djobs, sjobs, keys):
    # ---------- PE2-P: partial inner side at n = 10 ----------
    fP = [0]*11
    for J, A in [(5, [1]), (4, [4]), (1, [32]), (0, [0, 64])]:
        fP = padd(fP, pmul(A, [PHIA, pmul(PHIA, PHIA), None][0]*0 or ppow(PHIA, J)))
    rdP = read_A(fP)   # composed dev of a deg-10 poly: must be None
    chk('PE2-P', rdP is None, 'partial-side member NOT refused by the T(b)\' read: %s' % (rdP,))
    dvsP, errP = parse_A(fP, 5, 13, 5, 2, {3})   # dv(A0)=13 steep pin
    chk('PE2-P', errP is None and dvsP[1] == 10,
        'partial-side level-1 shape: %s %s' % (dvsP, errP))
    say('  PE2-P partial-side n=10 level-1 dvs: %s (two sides: slope 3 then 5/2)' % (dvsP,))
    L.append('print("P0 ", poldisc(Pol(%s)) != 0, " ", sig1(Pol(%s)))' % (pstr(fP), pstr(fP)))
    # ---------- PE2-Q: non-prime q (Q = 4) ----------
    qjobs = []
    def dQ(tag, C1, C0, u, w, lab, sig):
        f = wpadd(wpadd(wpmul(PHI2A_W, PHI2A_W), wpmul(C1, PHI2A_W)), C0)
        qjobs.append((tag, f, (u, w), lab, sig))
    dQ('Q-RAM',    [(64,0)], wpmul([(0,32)], PHIA_W), 25, 24, 'tRAM', [(8,2)])
    dQ('Q-INERT',  wpmul([(4,0)], PHIA_W), [(0,0), (0,64)], 26, 13, 'tINERT', [(4,4)])
    dQ('Q-SPLIT',  wpmul([(4,0)], PHIA_W), [(0,0), (64,0)], 26, 13, 'tSPLIT', [(4,2),(4,2)])
    dQ('Q-2SIDED', [(0,0), (8,0)], [(0,0), (0,128)], 30, 14, 't2SIDED', [(4,2),(4,2)])
    for i, (tag, f, pins, lab, sig) in enumerate(qjobs):
        dvs, err = parse_Q(f)
        chk('PE2-Q', err is None, '%s parse: %s' % (tag, err))
        rd = read_Q(f)
        ok = rd is not None and (rd[0], rd[1]) == pins and rd[2] == lab
        chk('PE2-Q', ok, '%s read %s want %s %s' % (tag, rd, pins, lab))
        say('  PE2-Q %s: pins %s %s -> abs %s' % (tag, pins, lab, sig))
        L.append('my(P=rnfequation(KW, Pol(%s)));'
                 'my(nf=nfinit([P,[2]]),dec=idealprimedec(nf,2));'
                 'print("Q%d ", poldisc(P) != 0, " ", poldegree(P), " ", '
                 'vecsort(vector(#dec, j, [dec[j].e, dec[j].f])))'
                 % (wpstr(f), i))
    # ---------- run gp ----------
    say('  launching gp: %d lines' % len(L))
    R = run_gp(L)
    # K-family
    for i, (tag, P, e, fr, u2) in enumerate(keys):
        got = R.get('K%d' % i, ['?'])[0].split()
        ok = got[:4] == ['1', str(e), str(fr), str(u2)]
        chk('PE2-K', ok, 'key %s: got %s want [1,%d,%d,%d]' % (tag, got, e, fr, u2))
        say('  PE2-K %s: #dec/e/f/v_L(Phi\')/deg = %s' % (tag, got))
    # S-family + T-SLOT tooth
    nslot_bad = 0
    for i, (gg, C, pred) in enumerate(sjobs):
        got = int(R.get('S%d' % i, ['-1'])[0])
        chk('PE2-S', got == pred, 'slot %s #%d %s: formula %s vs nfeltval %s' % (gg, i, C, pred, got))
        if gg == 'A':
            b = compA(C); OFFBAD = {'1': 0, 'x': 2, 'p': 7, 'xp': 5}
            cands = [4*v2(v)+OFFBAD[k] for k, v in b.items() if v]
            if cands and min(cands) != got: nslot_bad += 1
    say('  PE2-S: %d slot-exactness legs; wrong-offset control mismatches %d' % (len(sjobs), nslot_bad))
    chk('TEETH', nslot_bad >= 3, 'T-SLOT fired only %d' % nslot_bad)
    # D-family + T-DICT + T-COCYCLE teeth
    ndict = 0; ncocy = 0
    for i, (tag, gg, f, pins, lab, sig) in enumerate(djobs):
        row = R.get('D%d' % i)
        if not row: chk('PE2-D', False, '%s: no gp answer' % tag); continue
        disc, s = row[0].split(' ', 1)
        chk('PE2-D', disc == '1', '%s disc' % tag)
        got = sig_parse(s)
        chk('PE2-D', got == sorted(sig), '%s PARI r1 %s want %s' % (tag, got, sorted(sig)))
        row2 = R.get('E%d' % i)
        if row2:
            chk('PE2-D', sig_parse(row2[0]) == sorted(sig),
                '%s PARI r2 %s want %s' % (sig_parse(row2[0]), tag, sorted(sig)))
        if 'INERT' in tag and got != sorted([(2,2),(2,2)]) and got != sorted([(4,1),(4,1)]):
            ndict += 1
        if tag == 'F1b-COCY':
            naive = read_F(f, 'b', cocycle=False)
            if naive[2] != lab and got == sorted(sig): ncocy += 1
            say('  T-COCYCLE control: naive (no eta2 division) reads %s vs true %s, PARI %s'
                % (naive[2], lab, got))
    chk('TEETH', ndict >= 2, 'T-DICT fired only %d' % ndict)
    chk('TEETH', ncocy >= 1, 'T-COCYCLE did not fire')
    # P-family
    rowP = R.get('P0')
    if rowP:
        disc, s = rowP[0].split(' ', 1)
        got = sig_parse(s)
        chk('PE2-P', disc == '1' and ('2', '1') in [tuple(map(str, t)) for t in got] or (2,1) in got,
            'partial-side sigma %s lacks the (2,1) sibling' % (got,))
        say('  PE2-P PARI sigma = %s (sibling (2,1) + tower part; NO r2 display prices this)' % (got,))
    else:
        chk('PE2-P', False, 'no gp answer for partial-side member')
    # Q-family
    for i, (tag, f, pins, lab, sig) in enumerate(qjobs):
        row = R.get('Q%d' % i)
        if not row: chk('PE2-Q', False, '%s: no gp answer' % tag); continue
        parts = row[0].split(' ', 2)
        chk('PE2-Q', parts[0] == '1' and parts[1] == '16', '%s disc/deg: %s' % (tag, parts[:2]))
        got = sig_parse(parts[2])
        chk('PE2-Q', got == sorted(sig), '%s PARI abs %s want %s' % (tag, got, sorted(sig)))
        say('  PE2-Q %s: PARI abs sigma %s' % (tag, got))
    # T-PARSE tooth
    fbad = padd(padd(pmul(PHI2A, PHI2A), pmul([0, 1], PHI2A)), [0, 128])
    _, errbad = parse_A(fbad, 4, 10, 5, 2, {1, 2, 3})
    chk('TEETH', errbad is not None, 'T-PARSE: side-violating member accepted')
    say('  tooth T-PARSE fired (%s)' % errbad)
    nv = len(VIOL)
    say('=== VERDICT: %s -- checks %s, %d violations (%.1fs) ==='
        % ('GREEN' if nv == 0 else 'RED', NCHK, nv, time.time()-t0))
    return 0 if nv == 0 else 1

def ppow(p, k):
    out = [1]
    for _ in range(k): out = pmul(out, p)
    return out

if __name__ == '__main__':
    rc = main2(*main())
    with open(__file__.replace('.py', '_output.txt'), 'w') as fh:
        fh.write('\n'.join(OUT) + '\n')
    sys.exit(rc)
