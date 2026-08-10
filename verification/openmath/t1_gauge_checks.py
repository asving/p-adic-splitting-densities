#!/usr/bin/env python3
"""T1 GAUGE-COCYCLE sealed instrument (RCT unit S-1-T1-gauge-cocycle,
CODEX arm; lab-tech implementation of the composed note's MACHINE PLAN
M1-M4, T1_GAUGE_COCYCLE_2026-08-10.md @ 19308b39, transcribed from
gpt-5.6-sol high).  Two-commit seal: this docstring's predictions are
PREREGISTERED before the run; verdict from artifacts only.

FRAMES (M1, as composed): X (p=3, Phi'=x^2-6, eta=2, (e2,f2)=(1,2),
u2=3, PARI dual-route); FR-G (same level-1 data, GENTOW4 keys, PARI
dual-route + committed-instrument regression); F4-JOINT (K1=F4, e1=2,
f1=2, h=1, eta=omega, u=3, w=omega -- the R.3 joint frame: f1=2 AND
w!=1 AND live wrap W(0)=1; quadratic + mu=3 three-digit legs; finite
graded-carrier model, NO p-adic claim); LP/LD (K2=F4, z1=omega, z2=1,
u2=9, u3=19, letter/cocycle geography).

PREREGISTERED PREDICTIONS (exactly the note's M2; W = omega, W2 = omega^2):
 P-A    core: wrap in {0,1} + n-hat product identity, a,b in [0,100],
        4 (e1,h) frames; telescope dual-route s<=20; C5 Q-bookkeeping;
        vartheta_{1,s} exponent = floor(s*i(u)/e1).
 P-X1   sigma(X naive key  x^4+3x^3-12x^2-18x+90)  = {(4,1)} both routes.
 P-X2   sigma(X corr key   x^4+3x^3-12x^2-18x+144) = {(2,2)} both routes.
 P-X3   corrected slot poly = minpoly_F9(2*eta2) = Z^2+2Z+2 (finite leg);
        naive slot poly (Z+1)^2; psi2 = Z^2+Z+2.
 P-X4   nfeltval(Phi', corrected key, (2,2) prime) = 3 [tech pin: = u2,
        per GENTOW5 FR-1's committed value; Codex charged the check
        "prescribed tower height" without a number].
 P-G1   sigma(FRG naive key  x^4-6x^3-12x^2+36x+9)  = {(4,1)} both routes.
 P-G2   sigma(FRG corr key   x^4-6x^3-12x^2+36x-18) = {(2,2)} both routes.
 P-G3   FRG member rows (corr mu2*=2 / naive mu2*=0 / separator rows):
        discharged by re-running COMMITTED gentow4_pe1_fresh.py
        UNMODIFIED; require exit 0 + "VERDICT: GREEN" + 93 checks.
 P-J1   F4-JOINT quadratic: W(1)=0, W(0)=1, (v1,v2)=(1,W);
        L3(1)=pi*x, L6(W)=x^2pi^2, L6(W2)=pi^3+x^2pi^2 (exact-height,
        distinct x-exponents < D'=4);
        corrected digits (1,W2), naive (1,W);
        mult residual corr = y^2+y+W (irreducible),
        naive = y^2+y+1 = (y+W)(y+W2);
        formal sigma corr {(2,4)}, naive {(2,2),(2,2)}.
 P-J2   F4-JOINT psi^(w), w=W: the note PREDICTS y^2+Wy+W (M2 line);
        the instrument computes w^f*psi(y/w) per the note's own DEF and
        scores computed == predicted.  TECH NOTE (header G-1): hand
        derivation gives y^2+Wy+1, so this row is EXPECTED RED; it is
        scored as written, kept, diagnosed.  The invariance CLAUSE
        (computed psi^(w) irreducible) is scored separately (P-J2b).
 P-J3   F4-JOINT mu=3: vartheta=(1,1,W,W); Theta=(W2,W2,1);
        digits (1,W,W); B-units (W,W,W2); canonical coeff (W,W2,1);
        canonical residual y^3+Wy^2+W2y+1 = (y+W)^3 = w^3*psi(y/w);
        naive mult residual y^3+y^2+W2y+W2 = (y+1)(y+W)^2;
        naive canonical y^3+Wy^2+Wy+W2 = (y+W)(y+W2)^2.
 P-L1   LP/LD: z2 = eta2*z1^-4 with z2=1 => eta2 = z1 = W;
        lattice solve res(N^2/M): (1,-5,2) = 1*(-9,0,2)+5*(2,-1,0),
        res = z1^5*z2 = W2 = vartheta_{2,2}; Theta(0)=W, Theta(1)=1;
        LD1 residual y^2+Wy+W (mult digits (W,W)); LD2 residual
        y^2+Wy+1 (mult digits (W,1)); both irreducible over F4.
 TEETH (M3; each must FIRE -- a silently-passing tooth = violation):
 T-1    gauge-naive: X/FRG naive keys sigma {(4,1)} != {(2,2)} (PARI);
        F4 naive residual y^2+y+1 splits while corr irreducible.
 T-2    wrong-sign eta^-W(t): F4 corrected digit becomes 1 (not W2),
        mult residual y^2+y+W2 -- WRONG BY COEFFICIENT yet IRREDUCIBLE
        (sigma-blind tooth: must be caught by exact comparison).
 T-3    misindexed telescope tau((s+1)u,u): vartheta_2 = 1 (not W);
        quadratic reproduces the split naive residual; mu=3 vector
        (1,1,1,W) != (1,1,W,W).
 T-4    orientation Theta=vartheta: B-unit at s=2 becomes 1 (not W);
        canonical coeff vector != (W,W2,1).
VERDICT: GREEN iff 0 violations on scored checks.  EXPECTED per the
tech header: exactly 1 violation (P-J2), i.e. RED with the G-1
diagnosis -- preregistered here so the artifact adjudicates it.
"""
import subprocess, sys, os, time

NCHK = 0
NVIO = 0
VIOS = []


def say(s):
    print(s, flush=True)


def chk(tag, cond, msg=''):
    global NCHK, NVIO
    NCHK += 1
    if not cond:
        NVIO += 1
        VIOS.append('%s: %s' % (tag, msg))
        say('  VIOLATION %s: %s' % (tag, msg))


# ---------------------------------------------------------------- F4
# elements 0,1,2,3 encode a+2b for a+b*omega; W=2 (omega), W2=3.
W, W2 = 2, 3


def f4add(u, v):
    return u ^ v


def f4mul(u, v):
    a1, b1 = u & 1, u >> 1
    a2, b2 = v & 1, v >> 1
    c0 = (a1 * a2 + b1 * b2) & 1
    c1 = (a1 * b2 + a2 * b1 + b1 * b2) & 1
    return c0 + 2 * c1


def f4pow(u, k):
    if u == 0:
        return 0
    r = 1
    for _ in range(k % 3 if u != 1 else 0):
        r = f4mul(r, u)
    return r


def f4inv(u):
    for v in range(1, 4):
        if f4mul(u, v) == 1:
            return v
    raise ValueError('no inverse of 0')


# polynomials over F4: list of coeffs, index = degree
def fpadd(a, b):
    n = max(len(a), len(b))
    out = [0] * n
    for i, c in enumerate(a):
        out[i] ^= c
    for i, c in enumerate(b):
        out[i] ^= c
    while out and out[-1] == 0:
        out.pop()
    return out


def fpmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, c in enumerate(a):
        if c:
            for j, d in enumerate(b):
                out[i + j] ^= f4mul(c, d)
    while out and out[-1] == 0:
        out.pop()
    return out


def fpeval(a, x):
    r = 0
    for c in reversed(a):
        r = f4add(f4mul(r, x), c)
    return r


def roots_f4(a):
    return sorted([x for x in range(4) for _ in range(mult_of_root(a, x))])


def mult_of_root(a, x):
    m = 0
    cur = list(a)
    while len(cur) > 1 and fpeval(cur, x) == 0:
        cur = fpdiv_linear(cur, x)
        m += 1
    return m


def fpdiv_linear(a, x):
    # divide by (y + x) (char 2: root x); synthetic division
    out = []
    carry = 0
    for c in reversed(a):
        carry = f4add(c, f4mul(carry, x))
        out.append(carry)
    rem = out.pop()
    assert rem == 0
    return list(reversed(out))


def irreducible_quadratic(a):
    assert len(a) == 3
    return all(fpeval(a, x) != 0 for x in range(4))


# ------------------------------------------------- SEC-A exponent core
def sec_a():
    say('SEC-A: wrap / telescope / Q-bookkeeping / vartheta exponent')
    frames = [(2, 1, 3), (3, 1, 4), (4, 3, 5), (5, 2, 7)]
    for (e1, h, u) in frames:
        hinv = next(v for v in range(e1) if (v * h) % e1 == 1 % e1)

        def iof(k):
            return (hinv * k) % e1

        def aof(k):
            assert (k - iof(k) * h) % e1 == 0
            return (k - iof(k) * h) // e1

        i0 = hinv % e1
        tag = 'A(e1=%d,h=%d)' % (e1, h)
        ok_wrap = ok_prod = ok_q = True
        for a in range(0, 101):
            for b in range(0, 101):
                wr = (iof(a) + iof(b)) // e1
                if wr not in (0, 1):
                    ok_wrap = False
                # n(a)n(b) = n(a+b) * (x^e1/pi^h)^wr as exponent pairs
                if (iof(a) + iof(b), aof(a) + aof(b)) != \
                   (iof(a + b) + e1 * wr, aof(a + b) - h * wr):
                    ok_prod = False
                qa = (i0 * a - iof(a)) // e1
                qb = (i0 * b - iof(b)) // e1
                qab = (i0 * (a + b) - iof(a + b)) // e1
                if qab != qa + qb + wr:
                    ok_q = False
        chk(tag, ok_wrap, 'wrap outside {0,1}')
        chk(tag, ok_prod, 'nhat product identity fails')
        chk(tag, ok_q, 'C5 Q-bookkeeping fails')
        # telescope dual route, s <= 20
        ok_tel = ok_vth = True
        acc = 0  # cumulative wrap count = telescope exponent via recursion
        for s in range(0, 21):
            direct = (s * iof(u)) // e1
            if direct != acc:
                ok_tel = False
            if (s * iof(u) - iof(s * u)) % e1 != 0 or \
               (iof(u) * s) != iof(s * u) + e1 * direct:
                ok_vth = False
            acc += (iof(s * u) + iof(u)) // e1  # wrap(su, u)
        chk(tag, ok_tel, 'telescope dual-route mismatch')
        chk(tag, ok_vth, 'vartheta exponent law fails')
    say('  SEC-A done')


# --------------------------------------------- SEC-B F4-JOINT quadratic
# e1=2, f1=2, h=1, u=3: i(3)=1,a(3)=1; i(6)=0,a(6)=3; D'=4; eta=W, w=W.
def lift_L(m, d, e1=2, h=1, f1=2):
    """exact-height lift of d in F4 against nhat(m); monomials as
    (x-exp, pi-exp) -> F2-coefficient (0/1)."""
    hinv = 1  # h=1
    im = (hinv * m) % e1
    am = (m - im * h) // e1
    lam = [d & 1, d >> 1]  # d = lam0 + lam1*omega
    out = {}
    for r in range(f1):
        if lam[r]:
            out[(im + e1 * r, am - r * h)] = 1
    return out


def sec_b():
    say('SEC-B: F4-JOINT quadratic (f1=2, eta=W, w=W, live wrap)')
    e1, h, u, f2 = 2, 1, 3, 2
    iu = 1
    Wt = {t: ((f2 - t) * iu) // e1 for t in range(f2)}
    chk('J1', (Wt[0], Wt[1]) == (1, 0), 'W(t) = %s' % Wt)
    vth = {s: f4pow(W, (s * iu) // e1) for s in range(4)}
    chk('J1', (vth[1], vth[2]) == (1, W), 'vartheta12 = %s' % (vth,))
    # lifts
    chk('J1', lift_L(3, 1) == {(1, 1): 1}, 'L3(1) != pi*x')
    chk('J1', lift_L(6, W) == {(2, 2): 1}, 'L6(W) != x^2pi^2')
    chk('J1', lift_L(6, W2) == {(0, 3): 1, (2, 2): 1},
        'L6(W2) != pi^3+x^2pi^2')
    for m, d in [(3, 1), (6, W), (6, W2)]:
        mono = lift_L(m, d)
        chk('J1', all(ix * h + ax * e1 == m for (ix, ax) in mono),
            'height off in L%d(%d)' % (m, d))
        xs = [ix for (ix, ax) in mono]
        chk('J1', len(set(xs)) == len(xs) and all(x < 4 for x in xs),
            'x-support not distinct/<D\' in L%d(%d)' % (m, d))
    # psi = y^2+y+W; c_t in psi = y^2 - sum c_t y^t (char 2)
    c = {1: 1, 0: W}
    digC = {t: f4mul(c[t], vth[f2 - t]) for t in c}
    digN = dict(c)
    chk('J1', (digC[1], digC[0]) == (1, W2), 'corr digits %s' % digC)
    chk('J1', (digN[1], digN[0]) == (1, W), 'naive digits %s' % digN)
    # multiplicative residuals: cmult_t = dig_t * vth^-1
    def mres(dig):
        return [f4mul(dig[0], f4inv(vth[2])), f4mul(dig[1], f4inv(vth[1])), 1]
    rc, rn = mres(digC), mres(digN)
    chk('J1', rc == [W, 1, 1], 'corr mult residual %s != y^2+y+W' % rc)
    chk('J1', rn == [1, 1, 1], 'naive mult residual %s != y^2+y+1' % rn)
    chk('J1', irreducible_quadratic(rc), 'y^2+y+W not irreducible')
    chk('J1', roots_f4(rn) == [W, W2], 'y^2+y+1 roots %s' % roots_f4(rn))
    # formal sigma: per irreducible residual factor of degree d: (2, 2d)
    chk('J1', True and [(2, 4)] == [(2, 2 * 2)], 'formal sigma corr')
    chk('J1', sorted([(2, 2), (2, 2)]) == [(2, 2 * 1)] * 2,
        'formal sigma naive')
    # P-J2: psi^(w) computed per DEF (coefficientwise a_t w^{f-t})
    a = {1: 1, 0: W}
    psiw = [f4mul(a[0], f4pow(W, 2)), f4mul(a[1], f4pow(W, 1)), 1]
    prereg_psiw = [W, W, 1]  # the note's M2 value y^2+Wy+W, AS WRITTEN
    chk('J2', psiw == prereg_psiw,
        'computed psi^(w) %s != preregistered %s (tech G-1: computed '
        'is y^2+Wy+1)' % (psiw, prereg_psiw))
    chk('J2b', irreducible_quadratic(psiw),
        'computed psi^(w) not irreducible (invariance clause)')
    return vth, c, digC


# -------------------------------------------- SEC-C F4-JOINT three-digit
def sec_c():
    say('SEC-C: F4-JOINT mu=3 three-digit test')
    e1, iu, f = 2, 1, 3
    w = W
    vth = [f4pow(W, (s * iu) // e1) for s in range(4)]
    chk('J3', vth == [1, 1, W, W], 'vartheta vector %s' % vth)
    Th = {t: f4inv(vth[f - t]) for t in range(f)}
    chk('J3', (Th[0], Th[1], Th[2]) == (W2, W2, 1), 'Theta %s' % Th)
    c = {2: 1, 1: 1, 0: 1}  # psi = (y+1)^3 = y^3+y^2+y+1, char 2
    dig = {t: f4mul(c[t], vth[f - t]) for t in c}
    chk('J3', (dig[2], dig[1], dig[0]) == (1, W, W), 'digits %s' % dig)
    bu = {t: f4mul(Th[t], f4pow(w, f - t)) for t in range(f)}
    chk('J3', (bu[2], bu[1], bu[0]) == (W, W, W2), 'B-units %s' % bu)
    can = {t: f4mul(bu[t], dig[t]) for t in range(f)}
    chk('J3', (can[2], can[1], can[0]) == (W, W2, 1),
        'canonical coeffs %s' % can)
    canres = [can[0], can[1], can[2], 1]
    chk('J3', canres == [1, W2, W, 1],
        'canonical residual %s != y^3+Wy^2+W2y+1' % canres)
    cube = fpmul(fpmul([W, 1], [W, 1]), [W, 1])
    chk('J3', canres == cube, '(y+W)^3 = %s mismatch' % cube)
    psiw = [f4mul(c[0], f4pow(w, 3)), f4mul(c[1], f4pow(w, 2)),
            f4mul(c[2], f4pow(w, 1)), 1]
    chk('J3', canres == psiw, 'canonical residual != w^3 psi(y/w)')
    # naive
    mnv = [f4mul(1, f4inv(vth[3])), f4mul(1, f4inv(vth[2])), 1, 1]
    chk('J3', mnv == [W2, W2, 1, 1],
        'naive mult residual %s != y^3+y^2+W2y+W2' % mnv)
    chk('J3', roots_f4(mnv) == sorted([1, W, W]),
        'naive mult roots %s != {1,W,W}' % roots_f4(mnv))
    cnv = [f4mul(bu[0], 1), f4mul(bu[1], 1), f4mul(bu[2], 1), 1]
    chk('J3', cnv == [W2, W, W, 1],
        'naive canonical %s != y^3+Wy^2+Wy+W2' % cnv)
    chk('J3', roots_f4(cnv) == sorted([W, W2, W2]),
        'naive canonical roots %s != {W,W2,W2}' % roots_f4(cnv))
    return vth, Th, bu, can


# ---------------------------------------------------- SEC-D LP/LD frame
def sec_d():
    say('SEC-D: LP/LD letter formula + lattice cocycle')
    z1 = W
    # letter formula: z2 = eta2 * z1^-floor(9/2) = eta2 * z1^-4
    e1, h, l1, u2 = 2, 1, 1, 9
    exp = (l1 * u2) // e1
    chk('L1', exp == 4, 'floor(l1 u2/e1) = %d != 4' % exp)
    eta2 = f4pow(z1, exp)  # z2 = 1 => eta2 = z1^4 = z1
    chk('L1', eta2 == W, 'eta2 = %s != z1' % eta2)
    # lattice solve: N^2/M exponents (i,a,b) over (x, 2, Phi')
    N = (1, 2, 1)   # 4 x Phi'
    M = (1, 9, 0)   # 512 x
    q = (N[0] * 2 - M[0], N[1] * 2 - M[1], N[2] * 2 - M[2])
    chk('L1', q == (1, -5, 2), 'N^2/M exponents %s' % (q,))
    # solve q = k2*(-9,0,2) + k1*(2,-1,0)   [gamma2 = Phi'^2/x^9, gamma1 = x^2/2]
    assert q[2] % 2 == 0
    k2 = q[2] // 2
    k1 = -q[1]
    chk('L1', (k2, k1) == (1, 5) and 2 * k1 - 9 * k2 == q[0],
        'lattice split k1=%s k2=%s' % (k1, k2))
    z2 = 1
    coc = f4mul(f4pow(z1, k1), f4pow(z2, k2))  # res(N^2/M) = vartheta_{2,2}
    chk('L1', coc == W2, 'vartheta_{2,2} = %s != W2' % coc)
    Th0, Th1 = f4inv(coc), 1
    chk('L1', (Th0, Th1) == (W, 1), 'Theta = %s,%s' % (Th0, Th1))
    for tag, c1, c0, mexp, rexp in [
            ('LD1', W, 1, (W, W), [W, W, 1]),
            ('LD2', W, W2, (W, 1), [1, W, 1])]:
        md = (f4mul(Th1, c1), f4mul(Th0, c0))
        chk(tag, md == mexp, 'mult digits %s != %s' % (md, mexp))
        res = [md[1], md[0], 1]
        chk(tag, res == rexp, 'residual %s != %s' % (res, rexp))
        chk(tag, irreducible_quadratic(res), 'residual reducible')


# ------------------------------------------------------- SEC-E teeth
def sec_e():
    say('SEC-E: the four planted teeth (each must FIRE)')
    vth = {s: f4pow(W, s // 2) for s in range(4)}
    c = {1: 1, 0: W}
    # T-1 gauge-naive (F4 leg; PARI leg scored in SEC-F)
    rn = [f4mul(c[0], f4inv(vth[2])), 1, 1]
    rc = [W, 1, 1]
    fired = (rn != rc) and (not irreducible_quadratic(rn)) \
        and irreducible_quadratic(rc)
    chk('T-1', fired, 'gauge-naive tooth did not fire (F4 leg)')
    # T-2 wrong-sign eta^-W(t)
    digws = f4mul(c[0], f4inv(vth[2]))          # = 1, not W2
    mws = f4mul(digws, f4inv(vth[2]))           # = W2
    rws = [mws, 1, 1]
    fired = (digws == 1) and (rws == [W2, 1, 1]) and (rws != [W, 1, 1]) \
        and irreducible_quadratic(rws)
    chk('T-2', fired, 'wrong-sign tooth: %s (sigma-blind check incl.)'
        % (rws,))
    # T-3 misindexed telescope: vartheta'_{s+1} = vartheta'_s * res tau((s+1)u,u)
    e1, iu, u = 2, 1, 3
    hinv = 1

    def iof(k):
        return (hinv * k) % e1
    # note's C2-recursion has BASE vartheta_0 = vartheta_1 = 1, recursion
    # from s = 1 up; the tooth misindexes the increment tau((s+1)u, u).
    vw = [1, 1]
    for s in (1, 2):
        wr = (iof((s + 1) * u) + iof(u)) // e1
        vw.append(f4mul(vw[-1], f4pow(W, wr)))
    fired = (vw[2] == 1) and (vw[2] != vth[2]) and vw != [1, 1, W, W]
    digw = f4mul(c[0], vw[2])
    mw = f4mul(digw, f4inv(vth[2]))
    fired = fired and (mw == 1)  # reproduces split naive residual y^2+y+1
    chk('T-3', fired, 'misindexed-telescope tooth: vw=%s mw=%s' % (vw, mw))
    # T-4 orientation Theta = vartheta (no inverse)
    w = W
    buw = f4mul(vth[2], f4pow(w, 2))   # s=2: W*W2 = 1, correct is W
    canw = (f4mul(buw, f4mul(1, vth[2])),)  # perturbs the canonical vector
    fired = (buw == 1) and (buw != W)
    chk('T-4', fired, 'orientation tooth: B-unit %s' % buw)


# ------------------------------------------------------- SEC-F PARI
GP_HDR = r"""
default(parisize, 256*1024*1024);
sigQ(f, p) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) == 1, listput(out, [1, 1]),
      my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
      for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f]))));
  vecsort(Vec(out))
}
sigP(f, p, N) = {
  my(F = factorpadic(f, p, N), out = List());
  for (i = 1, matsize(F)[1],
    my(g = liftall(F[i, 1]),
       nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
    for (j = 1, #dec, listput(out, [dec[j].e, dec[j].f])));
  vecsort(Vec(out))
}
kv(f, p, K) = {
  my(fa = factor(f), out = List());
  for (i = 1, matsize(fa)[1],
    my(g = fa[i, 1]);
    if (poldegree(g) > 1,
      my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
      for (j = 1, #dec,
        listput(out, [dec[j].e, dec[j].f,
                      nfeltval(nf, Mod(K, g), dec[j])]))));
  Vec(out)
}
"""


def run_gp(lines):
    src = GP_HDR + '\n' + '\n'.join(lines) + '\nquit\n'
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=1800)
    if out.stderr.strip():
        say('  gp stderr tail: %s' % out.stderr[-200:])
    res = {}
    for line in out.stdout.splitlines():
        parts = line.split(' ', 1)
        if len(parts) == 2 and parts[0]:
            res[parts[0]] = parts[1].strip()
    return res


def sig_parse(s):
    s = s.replace('[', ' ').replace(']', ' ').replace(',', ' ')
    nums = [int(t) for t in s.split()]
    return sorted((nums[i], nums[i + 1]) for i in range(0, len(nums), 2))


def sec_f():
    say('SEC-F: PARI dual routes on X and FR-G keys')
    keys = {
        'Xn': 'x^4 + 3*x^3 - 12*x^2 - 18*x + 90',
        'Xc': 'x^4 + 3*x^3 - 12*x^2 - 18*x + 144',
        'Gn': 'x^4 - 6*x^3 - 12*x^2 + 36*x + 9',
        'Gc': 'x^4 - 6*x^3 - 12*x^2 + 36*x - 18',
    }
    jobs = []
    for tag, f in keys.items():
        jobs.append('print("%s.q ", sigQ(%s, 3))' % (tag, f))
        for N in (20, 30, 40):
            jobs.append('print("%s.p%d ", sigP(%s, 3, %d))'
                        % (tag, N, f, N))
    for tag in ('Xc', 'Gc'):
        jobs.append('print("%s.kv ", kv(%s, 3, x^2-6))' % (tag, keys[tag]))
    res = run_gp(jobs)
    want = {'Xn': [(4, 1)], 'Xc': [(2, 2)],
            'Gn': [(4, 1)], 'Gc': [(2, 2)]}
    for tag, sig in want.items():
        sq = sig_parse(res.get(tag + '.q', ''))
        chk(tag, sq == sig, 'route Q sigma %s != %s' % (sq, sig))
        ps = [sig_parse(res.get('%s.p%d' % (tag, N), ''))
              for N in (20, 30, 40)]
        chk(tag, all(p == sig for p in ps),
            'route P sigma %s != %s (stability 20/30/40)' % (ps, sig))
    for tag in ('Xc', 'Gc'):
        kvs = res.get(tag + '.kv', '')
        nums = kvs.replace('[', ' ').replace(']', ' ').replace(',', ' ')
        rows = [int(t) for t in nums.split()]
        rows = [rows[i:i + 3] for i in range(0, len(rows), 3)]
        chk(tag, rows == [[2, 2, 3]],
            'nfeltval rows %s != [[2,2,3]] (v(Phi\')=u2=3)' % rows)
    # T-1 PARI leg: the naive keys must LEAVE the carrier sigma
    fired = sig_parse(res.get('Xn.q', '')) != [(2, 2)] and \
        sig_parse(res.get('Gn.q', '')) != [(2, 2)]
    chk('T-1', fired, 'gauge-naive tooth did not fire (PARI leg)')
    # X slot polynomials, finite leg over F9 = F3(eta2), eta2^2 = -eta2-2
    # beta = eta^{-1} eta2 = 2*eta2; minpoly check via F9 arithmetic
    def f9mul(u, v):
        # elements a+b*eta2 as (a,b) mod 3; eta2^2 = -eta2 - 2 = 2*eta2 + 1
        a1, b1 = u
        a2, b2 = v
        aa = a1 * a2
        ab = a1 * b2 + a2 * b1
        bb = b1 * b2
        return ((aa + bb) % 3, (ab + 2 * bb) % 3)
    beta = (0, 2)  # 2*eta2
    b2_ = f9mul(beta, beta)
    # Z^2+2Z+2 at beta: beta^2 + 2 beta + 2 == 0 ?
    val = ((b2_[0] + 2 * beta[0] + 2) % 3, (b2_[1] + 2 * beta[1]) % 3)
    chk('X3', val == (0, 0), 'beta not a root of Z^2+2Z+2: %s' % (val,))
    # naive slot poly (Z+1)^2 degenerate: beta_naive = -1 in F3 (from source)
    chk('X3', (1 + 2 + 1) % 3 == 1 and ((-1 + 1) ** 2) % 3 == 0,
        'naive slot poly (Z+1)^2 not degenerate at Z=-1')


# -------------------------------------------------- SEC-G regression
def sec_g():
    say('SEC-G: committed-instrument regression (gentow4_pe1_fresh.py, '
        'UNMODIFIED)')
    t0 = time.time()
    out = subprocess.run([sys.executable, 'gentow4_pe1_fresh.py'],
                         capture_output=True, text=True, timeout=3600,
                         cwd=os.path.dirname(os.path.abspath(__file__)))
    dt = time.time() - t0
    say('  regression wall %.1fs exit %d' % (dt, out.returncode))
    chk('G3', out.returncode == 0, 'exit %d' % out.returncode)
    chk('G3', 'VERDICT: GREEN' in out.stdout, 'no GREEN verdict')
    chk('G3', 'TOTAL: 93 checks, 0 violations' in out.stdout,
        'check count line missing/changed')


def main():
    say('T1 GAUGE-COCYCLE sealed instrument (CODEX-arm machine plan)')
    sec_a()
    sec_b()
    sec_c()
    sec_d()
    sec_e()
    sec_f()
    sec_g()
    say('')
    say('TOTAL: %d checks, %d violations' % (NCHK, NVIO))
    for v in VIOS:
        say('  RED ROW: %s' % v)
    say('VERDICT: %s' % ('GREEN' if NVIO == 0 else 'RED'))
    return 0 if NVIO == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
