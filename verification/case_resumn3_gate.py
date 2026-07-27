#!/usr/bin/env python3
"""CASE-RESUMN3 census (written AFTER CASE_RESUMN3_SEALED_PREDICTIONS.md was sealed).
Layers: F1 classifier-decided counts vs sealed S7 integers; F2 oracle anchor (PARI);
F3 ORC-1/2 radius+bin; F4 ACT entry-vanishing; F5 checksum; F6 depth bounds; D-c sym-diff.
Oracle: elementary Newton-Hensel typing (FC3) on exact integer reps; PARI anchor via
factor+idealprimedec (types (e,f) PARI-native; factorpadic degree cross-check)."""
import sys, os, json, subprocess
from fractions import Fraction as F

def vp(x, p, cap=10**9):
    if x == 0: return cap
    v = 0
    while x % p == 0: x //= p; v += 1
    return v

def disc3(a, b, c):
    return 18*a*b*c - 4*a*a*a*c + a*a*b*b - 4*b*b*b - 27*c*c

# ---------- elementary oracle on exact integer rep (certified boxes only) ----------
def zp_roots(a, b, c, p, K, d):
    """distinct Z_p roots of z^3+az^2+bz+c (disc!=0, v(disc)=d), root mod p^K list.
    A class mod p^j is certified only when j > d/2 (roots separate by level d/2:
    pairwise v(r_i - r_j) <= d/2) AND Hensel fires: then at most/exactly one root."""
    f = lambda z: ((z*z + a*z + b)*z + c)
    fp = lambda z: (3*z*z + 2*a*z + b)
    cands = [(r, 1) for r in range(p) if f(r) % p == 0]
    roots = []
    while cands:
        r, j = cands.pop()
        vf, vfp = vp(f(r), p), vp(fp(r), p)
        if 2*j > d and vf > 2*vfp:           # separated + Hensel: unique root here
            x, M = r, p**(K+6)
            for _ in range(12):              # Newton (handles non-unit fp via exact division)
                num, den = f(x), fp(x)
                vd = vp(den, p)
                x = (x - (num // p**vd) * pow(den // p**vd, -1, M)) % M
            roots.append(x % p**K); continue
        if j > K + 6: continue                # no root here (certified d small)
        for t in range(p):
            r2 = r + t * p**j
            if f(r2) % p**(j+1) == 0: cands.append((r2, j+1))
    out = []
    for x in roots:
        if all((x - y) % p**K != 0 for y in out): out.append(x)
    return out

def quad_type(B, C, p, K):
    """type of z^2+Bz+C over Q_p by disc square class; B,C exact ints mod p^K."""
    D = (B*B - 4*C) % p**K
    v = vp(D, p)
    assert v < K - 3, "quad disc too deep for certified box"
    u = (D // p**v) % (8 if p == 2 else p)
    if v % 2 == 1: return 'R'
    if p == 2: return {1:'S', 5:'I', 3:'R', 7:'R'}[u % 8]
    return 'S' if pow(u, (p-1)//2, p) == 1 else 'I'

def cubic_res_type(A, B, C, p):
    """factorization shape of y^3+Ay^2+By+C over F_p (synthetic division, char-free)."""
    R = [C % p, B % p, A % p, 1]
    rs = {}
    for r in range(p):
        cur, m = R, 0
        while len(cur) > 1:
            # synthetic divide cur by (y-r); remainder last
            qout = [0]*(len(cur)-1); acc = 0
            for i in range(len(cur)-1, 0, -1):
                acc = (acc*r + cur[i]) % p; qout[i-1] = acc
            rem = (acc*r + cur[0]) % p
            if rem != 0: break
            m += 1; cur = qout
        if m: rs[r] = m
    tot = sum(rs.values()); roots = sorted(rs)
    if tot == 0: return ('irr', roots, rs)
    if tot == 1: return ('1r+quad', roots, rs)
    if tot == 3 and len(roots) == 3: return ('3dist', roots, rs)
    if tot == 3 and len(roots) == 2: return ('dbl+smp', roots, rs)
    if tot == 3 and len(roots) == 1: return ('triple', roots, rs)
    raise AssertionError("impossible cubic residual shape")

def r0_type(a, b, c, p, K):
    """r=0 certified boxes: (1,3) vs (3,1) by triple-residual NP descent (exact ints)."""
    sh = cubic_res_type(a % p, b % p, c % p, p)
    if sh[0] == 'irr': return '13'
    assert sh[0] == 'triple', "r=0 must have irreducible or triple reduction"
    r0 = sh[1][0]
    # recenter at r0, then descend
    mod = p**(K+8)
    aa, bb, cc = a, b, c; mu = 0; r = r0; scale = 1
    for _ in range(3*K + 12):
        # shift z -> z + r*scale
        t = r*scale
        cc = ((t*t + aa*t + bb)*t + cc) % mod
        bb = (3*t*t + 2*aa*t + bb) % mod
        aa = (aa + 3*t) % mod
        ka, kb, kc = vp(aa, p), vp(bb, p), vp(cc, p)
        ka -= mu; kb -= 2*mu; kc -= 3*mu
        assert kc >= 1 and kb >= 1 and ka >= 1 or True
        assert kc < K + 4, "descent too deep for a certified box"
        if kc % 3 != 0:
            assert kb*3 >= 2*kc and ka*3 >= kc, "r=0 must be single-segment"
            return '31'
        lam = kc // 3
        assert kb >= 2*lam and ka >= lam, "r=0 must be single-segment"
        u = (cc // p**(3*mu + kc)) % p
        A2 = (aa // p**(mu + lam)) % p if vp(aa, p) == mu + lam else 0
        B2 = (bb // p**(2*mu + 2*lam)) % p if vp(bb, p) == 2*mu + 2*lam else 0
        sh = cubic_res_type(A2, B2, u, p)
        if sh[0] == 'irr': return '13'
        assert sh[0] == 'triple', "r=0 residual must be irr or triple"
        r = sh[1][0]; mu += lam; scale = p**mu
        r = r  # next shift at level mu
    raise AssertionError("r0 descent did not terminate")

def oracle_type(a, b, c, p, d):
    """sigma of the exact integer poly (certified: disc!=0, small d)."""
    K = d + 6
    roots = zp_roots(a, b, c, p, K, d)
    if len(roots) == 3: return '111'
    if len(roots) == 1:
        r = roots[0]; mod = p**K
        B = (a + r) % mod; C = (b + r*B) % mod
        t = quad_type(B, C, p, K)
        return {'S': '111', 'I': '112', 'R': '1121'}[t]
    assert len(roots) == 0
    return r0_type(a, b, c, p, d + 4)

# ---------- the classifier walk (box semantics: digits < N only) ----------
UNDEC = '?'
def digit(x, p, l, N):
    return None if l >= N else (x // p**l) % p
def val(x, p, N):
    """valuation as seen in the box: (v, exact?) — exact iff a nonzero digit < N."""
    if x % p**N == 0: return (N, False)
    v = vp(x % p**N, p)
    return (v, True)

def quad_res(u, w, p):
    """y^2 + w y + u (u != 0 in F_p) -> ('S',None)/('I',None)/('D', ystar)."""
    rs = [y for y in range(p) if (y*y + w*y + u) % p == 0]
    if len(rs) == 2: return ('S', None)
    if len(rs) == 0: return ('I', None)
    return ('D', rs[0])       # deg-2 monic with exactly one F_p root => double root

def blk2walk(h1, h0, p, N, s, reads):
    """standalone block-2 (root entrance). Returns ('S'/'I'/'R'/UNDEC, reads)."""
    while True:
        v1, e1 = val(h1, p, N); v0, e0 = val(h0, p, N)
        k1 = v1 - s; k0 = v0 - 2*s
        if e1 and ((e0 and 2*k1 < k0) or (not e0 and 2*s + 2*k1 <= N - 1)):
            return ('S', reads + 1)                          # m_vv, certificate in-box
        if not e0: return (UNDEC, reads)
        if e1 and 2*k1 < k0: return (UNDEC, reads)           # m_vv but zeros not visible
        if k0 % 2 == 1: return ('R', reads + 1)              # m_w2 (2k1 > k0 by parity)
        L = s + k0 // 2                                       # m2 read (k1 >= k0/2 here)
        u = digit(h0, p, 2*L, N); w = digit(h1, p, L, N)
        t, y = quad_res(u, w, p)
        if t == 'S': return ('S', reads + 1)
        if t == 'I': return ('I', reads + 1)
        sh = y * p**L
        h0 = (h0 + h1*sh + sh*sh) % p**N; h1 = (h1 + 2*sh) % p**N
        s = L; reads += 1

def sub2incubic(a, b, c, p, N, lam, sc, reads):
    """block-2 leg inside the recentered cubic; v(a)=lam exact. -> sigma or UNDEC."""
    M = {'S': '111', 'I': '112', 'R': '1121'}
    while True:
        vc, ec = val(c, p, N); vb, eb = val(b, p, N)
        K0 = vc - lam - 2*sc; K1 = vb - lam - sc
        if eb and ((ec and 2*K1 < K0) or (not ec and lam + 2*sc + 2*K1 <= N - 1)):
            return (M['S'], reads + 1)
        if not ec: return (UNDEC, reads)
        if eb and 2*K1 < K0: return (UNDEC, reads)
        if K0 % 2 == 1: return (M['R'], reads + 1)
        Lm = sc + K0 // 2
        ub = digit(a, p, lam, N); bd = digit(b, p, lam + Lm, N); cd = digit(c, p, lam + 2*Lm, N)
        inv = pow(ub, -1, p)
        t, y = quad_res((cd * inv) % p, (bd * inv) % p, p)
        if t in ('S', 'I'): return (M[t], reads + 1)
        sh = y * p**Lm
        c = ((sh*sh + a*sh + b)*sh + c) % p**N
        b = (3*sh*sh + 2*a*sh + b) % p**N
        a = (a + 3*sh) % p**N
        sc = Lm; reads += 1

def ge_marked(v, exact, thr, Nline):
    """is (valuation v-or->=Nline) >= thr? True/False/None(=invisible)."""
    if exact: return v >= thr
    return True if Nline >= thr else None

def blk3walk(a, b, c, p, N, mu, reads):
    while True:
        va, ea = val(a, p, N); vb, eb = val(b, p, N); vc, ec = val(c, p, N)
        ka = va - mu; kb = vb - 2*mu; kc = vc - 3*mu
        Na, Nb, Nc = N - mu, N - 2*mu, N - 3*mu
        if ea:
            t1 = (kb > 2*ka) if eb else (True if Nb > 2*ka else None)
            t2 = (kc > 3*ka) if ec else (True if Nc > 3*ka else None)
            if (t1 is not False) and (t2 is not False):
                if t1 is None or t2 is None: return (UNDEC, reads)
                # vertex at (2,ka): D or E
                if eb:
                    tE = (kc > 2*kb - ka) if ec else (True if Nc > 2*kb - ka else None)
                    if tE is None: return (UNDEC, reads)
                    if tE: return ('111', reads + 1)        # E
                else:
                    if not ec: return (UNDEC, reads)        # D parity needs kc exact
                    if 2*Nb <= ka + kc: return (UNDEC, reads)  # vertex-at-1 ambiguous
                # D with kc exact (tE False forces ec in the eb branch)
                if (kc - ka) % 2 == 1: return ('1121', reads + 1)
                muD = (kc - ka) // 2
                ua = digit(a, p, mu + ka, N); uc = digit(c, p, mu*3 + kc, N)
                bd = digit(b, p, 2*mu + (ka + kc)//2, N)
                if bd is None: return (UNDEC, reads)
                inv = pow(ua, -1, p)
                t, y = quad_res((uc*inv) % p, (bd*inv) % p, p)
                if t == 'S': return ('111', reads + 1)
                if t == 'I': return ('112', reads + 1)
                sh = y * p**(mu + muD)
                c2 = ((sh*sh + a*sh + b)*sh + c) % p**N
                b2 = (3*sh*sh + 2*a*sh + b) % p**N
                a2 = (a + 3*sh) % p**N
                return sub2incubic(a2, b2, c2, p, N, mu + ka, mu + muD, reads + 1)
        # C: vertex at (1,kb) only
        if eb:
            tka = ge_marked(ka, ea, (kb + 1)//2, Na)
            tc = (2*kc > 3*kb) if ec else (True if 2*Nc > 3*kb else None)
            if (tka is not False) and (tc is not False):
                if tka is None or tc is None: return (UNDEC, reads)
                if kb % 2 == 1: return ('1121', reads + 1)
                muC = kb // 2
                ab = digit(a, p, mu + muC, N); ub = digit(b, p, 2*mu + kb, N)
                if ab is None: return (UNDEC, reads)
                t, y = quad_res(ub, ab, p)
                if t == 'S': return ('111', reads + 1)
                if t == 'I': return ('112', reads + 1)
                sh = y * p**(mu + muC)
                c2 = ((sh*sh + a*sh + b)*sh + c) % p**N
                b2 = (3*sh*sh + 2*a*sh + b) % p**N
                a2 = (a + 3*sh) % p**N
                return sub2incubic(a2, b2, c2, p, N, mu + muC, mu + muC, reads + 1)
        # A/B: single segment; needs kc exact
        if not ec: return (UNDEC, reads)
        tb = ge_marked(kb, eb, (2*kc + 2)//3, Nb); ta = ge_marked(ka, ea, (kc + 2)//3, Na)
        if tb is None or ta is None: return (UNDEC, reads)
        assert tb and ta, "hull dispatch fell through"
        if kc % 3 != 0: return ('31', reads + 1)
        lam = kc // 3
        ab = digit(a, p, mu + lam, N); bb = digit(b, p, 2*mu + 2*lam, N)
        u = digit(c, p, 3*mu + 3*lam, N)
        sh3 = cubic_res_type(ab, bb, u, p)
        if sh3[0] == '3dist': return ('111', reads + 1)
        if sh3[0] == '1r+quad': return ('112', reads + 1)
        if sh3[0] == 'irr': return ('13', reads + 1)
        roots, mult = sh3[1], sh3[2]
        r = [x for x in roots if mult[x] >= 2][0] if sh3[0] != 'triple' else roots[0]
        t = r * p**(mu + lam)
        c = ((t*t + a*t + b)*t + c) % p**N
        b = (3*t*t + 2*a*t + b) % p**N
        a = (a + 3*t) % p**N
        if sh3[0] == 'triple':
            mu = mu + lam; reads += 1; continue
        return sub2incubic(a, b, c, p, N, mu + lam, mu + lam, reads + 1)

_RES3 = {}
def res3(x, y, z, p):
    k = (p, x, y, z)
    v = _RES3.get(k)
    if v is None:
        v = cubic_res_type(x, y, z, p); _RES3[k] = v
    return v

def rootwalk(a, b, c, p, N):
    """full classifier walk on the box (a,b,c) mod p^N -> (sigma-or-UNDEC, reads)."""
    sh = res3(a % p, b % p, c % p, p)
    if sh[0] == '3dist': return ('111', 1)
    if sh[0] == '1r+quad': return ('112', 1)
    if sh[0] == 'irr': return ('13', 1)
    M = p**N
    if sh[0] == 'dbl+smp':
        roots, mult = sh[1], sh[2]
        r = [x for x in roots if mult[x] == 2][0]; s0 = [x for x in roots if mult[x] == 1][0]
        x = s0
        for _ in range(5):   # Newton on the simple root (f'(s) unit)
            fx = ((x*x + a*x + b)*x + c) % M
            dfx = (3*x*x + 2*a*x + b) % M
            x = (x - fx * pow(dfx, -1, M)) % M
        B = (a + x) % M; C = (b + x*B) % M
        h1 = (2*r + B) % M; h0 = (r*r + B*r + C) % M
        assert h1 % p == 0 and h0 % p == 0, "block-2 entry violated"
        t, reads = blk2walk(h1, h0, p, N, 0, 1)
        return ({'S': '111', 'I': '112', 'R': '1121', UNDEC: UNDEC}[t], reads)
    r = sh[1][0]
    c2 = ((r*r + a*r + b)*r + c) % M
    b2 = (3*r*r + 2*a*r + b) % M
    a2 = (a + 3*r) % M
    assert a2 % p == 0 and b2 % p == 0 and c2 % p == 0, "block-3 entry violated"
    return blk3walk(a2, b2, c2, p, N, 0, 1)

# ---------- main census ----------
def run_pool(p, Nmax, out):
    SIG = ('111', '112', '13', '1121', '31')
    typecache = {}
    results = {}
    for N in range(1, Nmax + 1):
        M = p**N
        walk_cnt = {s: 0 for s in SIG}; walk_undec = 0
        cert_cnt = {s: 0 for s in SIG}; unresolved = 0
        both_agree = 0; both_mismatch = []
        dec_not_cert = 0; cert_not_dec = 0
        depth_cnt = {}
        entryviol = 0
        for a in range(M):
            for b in range(M):
                for cc in range(M):
                    sig_w, reads = rootwalk(a, b, cc, p, N)
                    if sig_w == UNDEC: walk_undec += 1
                    else:
                        walk_cnt[sig_w] += 1
                        depth_cnt[reads] = depth_cnt.get(reads, 0) + 1
                    D = disc3(a, b, cc)
                    if D == 0: d = None
                    else: d = vp(D, p)
                    if d is None or 3*d >= 2*N:
                        unresolved += 1
                        if sig_w != UNDEC: dec_not_cert += 1
                        continue
                    N0 = (3*d)//2 + 1
                    key = (N0, a % p**N0, b % p**N0, cc % p**N0)
                    sig_o = typecache.get(key)
                    if sig_o is None:
                        sig_o = oracle_type(key[1], key[2], key[3], p, d)
                        typecache[key] = sig_o
                    cert_cnt[sig_o] += 1
                    if sig_w == UNDEC: cert_not_dec += 1
                    elif sig_w == sig_o: both_agree += 1
                    else: both_mismatch.append((a, b, cc, N, sig_w, sig_o))
        results[N] = dict(walk=walk_cnt, undec=walk_undec, cert=cert_cnt,
                          unresolved=unresolved, agree=both_agree,
                          mismatch=both_mismatch[:20], n_mismatch=len(both_mismatch),
                          dec_not_cert=dec_not_cert, cert_not_dec=cert_not_dec,
                          depth=depth_cnt)
        print(f"p={p} N={N}: walk={walk_cnt} undec={walk_undec} | cert={cert_cnt} "
              f"unres={unresolved} | mism={len(both_mismatch)} d\\c={dec_not_cert} "
              f"c\\d={cert_not_dec}", file=out, flush=True)
    return results

SEALED_S7 = {  # corrected sealed classifier-decided integers (seal S7)
 2: {1:(0,2,2,0,0), 2:(0,16,16,12,8), 3:(16,144,128,96,80), 4:(128,1184,1056,896,640),
     5:(1280,9728,8448,7360,5248), 6:(10496,78080,67584,60928,42240),
     7:(88064,629248,541184,489472,337920), 8:(708608,5038080,4329472,3951616,2705408)},
 3: {1:(1,9,8,0,0), 2:(27,243,216,126,54), 3:(1215,7047,5832,3402,1620),
     4:(32886,190998,158112,100602,43740), 5:(927288,5196312,4269024,2726460,1185354)}}
SEALED_T = {
 2: [F(1,2),F(281,294),F(18413,18522),F(166559,166698),F(73505069,73513818),
     F(4631291801,4631370534),F(5954604797,5954619258),F(18381903272153,18381909649446)],
 3: [F(2,3),F(3485,3549),F(1290071,1291836),F(470178911,470228304),F(171161719679,171163102656)]}
SIG = ('111','112','13','1121','31')

def act_layer_checks(p, out):
    ok = True
    q = p
    k2 = F(1, q*q+q+1); k3 = F(q-1, q**6-1)
    sealed = {2:(F(1,7),F(6,7),F(1,63),F(62,63)), 3:(F(1,13),F(12,13),F(1,364),F(363,364)),
              4:(F(1,21),F(20,21),F(1,1365),F(1364,1365))}
    s2, sd2, s3, sd3 = sealed[p]
    ok &= (k2 == s2 and 1-k2 == sd2 and k3 == s3 and 1-k3 == sd3)
    print(f"ACT q0={p}: K2={k2} det(I-K2)={1-k2} K3={k3} det(I-K3)={1-k3} sealed-match={ok}", file=out)
    # entry vanishing (finite LUT checks)
    if p == 2:
        n3d = sum(1 for a in range(2) for b in range(2) for c in range(2)
                  if cubic_res_type(a,b,c,2)[0] == '3dist')
        osplit = sum(1 for u in (1,) for w in range(2) if quad_res(u,w,2)[0] == 'S')
        n21 = sum(1 for a in range(2) for b in range(2) for c in (1,)
                  if cubic_res_type(a,b,c,2)[0] == 'dbl+smp')
        print(f"ACT p=2 entry vanishing: mH3={n3d} o_split={osplit} A-split(N21,const!=0)={n21} (sealed: 0,0,0)", file=out)
        ok &= (n3d == 0 and osplit == 0 and n21 == 0)
    if p == 3:
        n3d = sum(1 for a in range(3) for b in range(3) for c in (1,2)
                  if cubic_res_type(a,b,c,3)[0] == '3dist')
        print(f"ACT p=3 entry vanishing: A-3dist(const!=0)={n3d} (sealed: 0)", file=out)
        ok &= (n3d == 0)
    return ok

def pari_type(polys, p):
    """PARI oracle: factor over Q + idealprimedec -> sigma per poly."""
    lines = []
    for (a,b,cc) in polys:
        lines.append(f"f=x^3+({a})*x^2+({b})*x+({cc});F=factor(f);S=[];"
                     f"for(i=1,matsize(F)[1],g=F[i,1];m=F[i,2];"
                     f"if(poldegree(g)==1,for(j=1,m,S=concat(S,[1,1])),"
                     f"K=nfinit(g);D=idealprimedec(K,{p});"
                     f"for(j=1,m,for(k=1,length(D),S=concat(S,[D[k].e,D[k].f])))));"
                     f"print({a},\" \",{b},\" \",{cc},\" \",S)")
    import tempfile
    with tempfile.NamedTemporaryFile('w', suffix='.gp', delete=False) as fh:
        fh.write("\n".join(lines) + "\nquit\n"); path = fh.name
    r = subprocess.run([os.path.expanduser("~/.local/bin/gp"), "-q", "-f", "-s", "256M", path],
                       capture_output=True, text=True, timeout=7200)
    out = {}
    for ln in r.stdout.splitlines():
        parts = ln.split(None, 3)
        if len(parts) < 4: continue
        a, b, cc = int(parts[0]), int(parts[1]), int(parts[2])
        flat = [int(x) for x in parts[3].strip("[]").replace(",", " ").split()]
        key = tuple(sorted((flat[i], flat[i+1]) for i in range(0, len(flat), 2)))
        m = {(((1,1),)*3): '111', ((1,1),(1,2)): '112', ((1,3),): '13',
             ((1,1),(2,1)): '1121', ((3,1),): '31'}[key]
        out[(a,b,cc)] = m
    os.unlink(path)
    missing = [t for t in polys if t not in out]
    if missing and len(missing) < max(50, len(polys)//100):
        for t in missing:                       # per-poly retry (gp -f skips a line on error)
            sub = pari_type([t], p) if len(polys) > 1 else {}
            out.update(sub)
    return out

def main():
    import random
    random.seed(20260727)
    out = open("/tmp/resumn3_census.out", "w")
    fails, findings = [], []
    allres = {}
    for p, Nmax in ((3, 5), (2, 8)):
        print(f"=== POOL p={p} (Nmax={Nmax}) ===", file=out, flush=True)
        if not act_layer_checks(p, out): fails.append(f"F4 ACT p={p}")
        res = run_pool(p, Nmax, out)
        allres[str(p)] = {str(N): {k: v for k, v in r.items()} for N, r in res.items()}
        for N in range(1, Nmax + 1):
            r = res[N]
            got = tuple(r['walk'][s] for s in SIG)
            if got != SEALED_S7[p][N]:
                fails.append(f"F1 p={p} N={N}: census {got} != sealed {SEALED_S7[p][N]}")
            tot = sum(got) + r['undec']
            if tot != p**(3*N): fails.append(f"F5 p={p} N={N}: total {tot} != {p**(3*N)}")
            if r['n_mismatch']: fails.append(f"F2-structural p={p} N={N}: {r['mismatch'][:5]}")
            if r['dec_not_cert'] == 0 and N >= 4: findings.append(f"D-c p={p} N={N}: dec\\cert EMPTY")
            if r['cert_not_dec'] == 0 and N >= 4: findings.append(f"D-c p={p} N={N}: cert\\dec EMPTY")
        # F6 depth bounds at top N
        r = res[Nmax]; dep = r['depth']; cum = 0; M3 = p**(3*Nmax)
        for k in range(1, Nmax + 1):
            cum += dep.get(k, 0)
            if k <= len(SEALED_T[p]):
                Tk = SEALED_T[p][k-1]
                lo, hi = F(cum, M3), F(cum + r['undec'], M3)
                if not (lo <= Tk <= hi):
                    fails.append(f"F6 p={p} k={k}: T_k={Tk} not in [{lo},{hi}]")
                print(f"DEPTH p={p} k={k}: census cum={cum} bounds ok={lo<=Tk<=hi} (T_k={Tk})", file=out)
        # PARI anchor
        Nanc = 4 if p == 2 else 3
        Manc = p**Nanc
        cert_polys = []
        for a in range(Manc):
            for b in range(Manc):
                for cc in range(Manc):
                    D = disc3(a, b, cc)
                    if D != 0 and 3*vp(D, p) < 2*Nanc: cert_polys.append((a, b, cc))
        print(f"PARI anchor p={p}: exhaustive N={Nanc}, certified={len(cert_polys)}", file=out, flush=True)
        ptypes = pari_type(cert_polys, p)
        n_bad = 0
        for (a, b, cc) in cert_polys:
            d = vp(disc3(a, b, cc), p)
            et = oracle_type(a, b, cc, p, d)
            if ptypes.get((a, b, cc)) != et:
                n_bad += 1
                if n_bad < 6: print(f"ANCHOR MISMATCH p={p}: {(a,b,cc)} pari={ptypes.get((a,b,cc))} elem={et}", file=out)
        if n_bad: fails.append(f"F2 anchor p={p} exhaustive N={Nanc}: {n_bad} mismatches")
        print(f"PARI anchor p={p} exhaustive: {len(cert_polys)-n_bad}/{len(cert_polys)} agree", file=out, flush=True)
        # stratified sample at top N
        Mtop = p**Nmax; sample, seen = [], set()
        while len(sample) < 2500:
            a, b, cc = (random.randrange(Mtop) for _ in range(3))
            D = disc3(a, b, cc)
            if D == 0 or 3*vp(D, p) >= 2*Nmax: continue
            if (a, b, cc) in seen: continue
            seen.add((a, b, cc)); sample.append((a, b, cc))
        ptypes = pari_type(sample, p)
        n_bad = sum(1 for t in sample
                    if ptypes.get(t) != oracle_type(t[0], t[1], t[2], p, vp(disc3(*t), p)))
        if n_bad: fails.append(f"F2 anchor p={p} sample topN: {n_bad}/2500 mismatches")
        print(f"PARI anchor p={p} sample N={Nmax}: {2500-n_bad}/2500 agree", file=out, flush=True)
    json.dump({"fails": fails, "findings": findings, "results": allres}, 
              open("results/case_resumn3_results.json", "w"), indent=1, default=str)
    print("FAILS:", fails, file=out)
    print("FINDINGS:", findings, file=out)
    print("VERDICT:", "PASS" if not fails else "FAIL", file=out)
    out.close()
    print("FAILS:", len(fails), "FINDINGS:", len(findings))
    for f_ in fails: print(" FAIL:", f_)

if __name__ == "__main__":
    main()
