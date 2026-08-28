#!/usr/bin/env python3
"""dv_hensel_cert.py — numeric certificate for the dv-graded one-slope Hensel engine
(unit MHENS, 2026-08-26; companion to docs/in-progress/HENSEL_ENGINE_2026-08-26.md §10).

Exact integer arithmetic throughout (2-adic valuations on exact ints; the Newton
iteration works mod 2^PREC and monitors that no consulted valuation approaches PREC).

THE AUDITED FRAME (doc §7.1): O = Z_2, pi = 2, e1 = 1, f1 = 2, h = 1, D' = 2,
  Phi' = x^2 + 2x + 12,  K = F_4 = F_2(theta), theta^2 = theta + 1,
  direction (u, l) = (3, 1)  [floor 1*2*1 = 2 < 3],  label r = Z + theta.

MODEL CAVEAT: slot reads are computed in the RAW normalization (no twist).  Certified
claims are twist-invariant (weights, side sets, degrees) or normalization-robust in the
doc's Sec 7.2 sense (identical slot-height patterns).

Sections (doc Sec 10): 1 frame audit / 2 M support+side laws / 3 M residual law (raw)
/ 3b MH9M above-line mixed reads (twist-normalized, both carry branches) / 4 Newton engine
end-to-end + contraction + negative controls / 5 the defective-stratum refutation /
6 uniqueness brute search on a D'-divisible ambient.
"""

import random, sys

random.seed(20260826)
PREC = 200            # working 2-adic precision for the Newton section
INF = 10**9

FAILS = []
TESTS = [0]

def check(cond, msg):
    TESTS[0] += 1
    if not cond:
        FAILS.append(msg)
        print("FAIL:", msg)

# ---------------------------------------------------------------- 2-adic + Z[x]
def v2(n):
    if n == 0:
        return INF
    n = abs(n)
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v

def trim(p):
    while p and p[-1] == 0:
        p.pop()
    return p

def padd(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])

def pneg(p): return [-c for c in p]
def psub(p, q): return padd(p, pneg(q))

def pmul(p, q):
    if not p or not q:
        return []
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return trim(out)

def pdivmod_monic(p, q):
    """divide by monic q over Z, exactly."""
    assert q and q[-1] == 1
    p = list(p)
    dq = len(q) - 1
    quo = [0] * max(0, len(p) - dq)
    while len(p) - 1 >= dq and p:
        c = p[-1]
        k = len(p) - 1 - dq
        quo[k] = c
        for i in range(len(q)):
            p[i + k] -= c * q[i]
        trim(p)
    return trim(quo), trim(p)

def pmod2n(p, n):
    m = 1 << n
    return trim([((c % m) + m) % m if False else c % m for c in p])  # symmetric not needed; use nonneg

def preduce(p, n):
    m = 1 << n
    return trim([c % m for c in p])

# ---------------------------------------------------------------- F4 arithmetic
# element = (a, b) meaning a + b*theta, a,b in {0,1}; theta^2 = theta + 1
F4_ZERO, F4_ONE, F4_TH, F4_TH1 = (0, 0), (1, 0), (0, 1), (1, 1)

def f4_add(x, y): return ((x[0] ^ y[0]), (x[1] ^ y[1]))
def f4_mul(x, y):
    a, b = x; c, d = y
    # (a+bT)(c+dT) = ac + (ad+bc)T + bd T^2 = (ac+bd) + (ad+bc+bd)T
    return ((a & c) ^ (b & d), (a & d) ^ (b & c) ^ (b & d))
def f4_inv(x):
    for y in (F4_ONE, F4_TH, F4_TH1):
        if f4_mul(x, y) == F4_ONE:
            return y
    raise ZeroDivisionError

# F4[Z] polynomials: list of F4 elements, low degree first
def z_trim(P):
    while P and P[-1] == F4_ZERO:
        P.pop()
    return P
def z_add(P, Q):
    n = max(len(P), len(Q))
    return z_trim([f4_add(P[i] if i < len(P) else F4_ZERO, Q[i] if i < len(Q) else F4_ZERO) for i in range(n)])
def z_mul(P, Q):
    if not P or not Q:
        return []
    out = [F4_ZERO] * (len(P) + len(Q) - 1)
    for i, a in enumerate(P):
        for j, b in enumerate(Q):
            out[i + j] = f4_add(out[i + j], f4_mul(a, b))
    return z_trim(out)
def z_divmod(P, Q):
    P = list(P); Q = z_trim(list(Q))
    assert Q
    inv = f4_inv(Q[-1])
    quo = [F4_ZERO] * max(0, len(P) - len(Q) + 1)
    while len(P) >= len(Q) and z_trim(P):
        if len(P) < len(Q):
            break
        c = f4_mul(P[-1], inv)
        k = len(P) - len(Q)
        quo[k] = c
        for i in range(len(Q)):
            P[i + k] = f4_add(P[i + k], f4_mul(c, Q[i]))
        z_trim(P)
    return z_trim(quo), z_trim(P)
def z_gcd_bezout(P, Q):
    """returns (g, s, t) with sP + tQ = g."""
    r0, r1 = z_trim(list(P)), z_trim(list(Q))
    s0, s1 = [F4_ONE], []
    t0, t1 = [], [F4_ONE]
    while r1:
        q, r = z_divmod(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, z_add(s0, z_mul(q, s1))
        t0, t1 = t1, z_add(t0, z_mul(q, t1))
    return r0, s0, t0

# ---------------------------------------------------------------- the frame
H, E1, F1D, U, ELL = 1, 1, 2, 3, 1
DPRIME = E1 * F1D
KEY = [12, 2, 1]  # x^2 + 2x + 12

def stage_height(A):
    """dv(A) = min_i (e1*v2(a_i) + h*i); A a digit (any Z[x] poly here)."""
    if not A:
        return INF
    return min(v2(c) + i for i, c in enumerate(A) if c != 0)

def raw_read(A, k):
    """raw slot read of digit A (deg < D') at height k: sum over slots with
    v2(a_i) + i = k of res(a_i / 2^(k-i)) * theta^i in F4."""
    out = F4_ZERO
    thpow = [F4_ONE, F4_TH]
    for i, c in enumerate(A):
        if c != 0 and v2(c) + i == k and k - i >= 0:
            bit = (c >> (k - i)) & 1
            if bit:
                out = f4_add(out, thpow[i])
    return out

def dev_digits(f, nmax=None):
    """Phi'-adic digits of f, low first."""
    digs = []
    p = list(f)
    if nmax is None:
        nmax = len(f) // DPRIME + 2
    for _ in range(nmax):
        q, r = pdivmod_monic(p, KEY)
        digs.append(r)
        p = q
        if not p:
            break
    return digs

def dv_hgt(f, j):
    d = dev_digits(f)
    return stage_height(d[j]) if j < len(d) else INF

def W(f):
    if not f:
        return INF
    d = dev_digits(f)
    return min(ELL * stage_height(d[j]) + U * j for j in range(len(d))) if d else INF

def side_set(f):
    if not f:
        return []
    w = W(f)
    d = dev_digits(f)
    return [j for j in range(len(d))
            if stage_height(d[j]) < INF and ELL * stage_height(d[j]) + U * j == w]

def res_poly(f):
    """raw dvResPoly: reads along the side line, Z-slot = (j - jmin)/ell."""
    s = side_set(f)
    if not s:
        return None
    jmin, jmax = min(s), max(s)
    d = dev_digits(f)
    w = W(f)
    out = []
    t = 0
    j = jmin
    while j <= jmax:
        k = (w - U * j) // ELL if (w - U * j) % ELL == 0 and w - U * j >= 0 else None
        if k is None or j >= len(d):
            out.append(F4_ZERO)
        else:
            out.append(raw_read(d[j], k))
        j += ELL
        t += 1
    return z_trim(out)

def line_read(f, c, jcap):
    """read-poly of f on the weight line c, Z-power = abscissa j (ell = 1 frame),
    for abscissae 0..jcap-1; coefficient 0 unless the digit sits exactly on the line."""
    d = dev_digits(f)
    out = []
    for j in range(jcap):
        k = c - U * j
        if k < 0 or j >= len(d):
            out.append(F4_ZERO)
            continue
        hj = stage_height(d[j]) if j < len(d) else INF
        if hj < k:
            raise AssertionError("line_read consulted below-line content (W(f) < c?)")
        out.append(raw_read(d[j], k) if hj == k else F4_ZERO)
    return z_trim(out)

def digit_lift(val, k):
    """a digit (deg < D') with stage height exactly k (if val != 0) and raw read val."""
    a, b = val
    L = []
    if a:
        L = padd(L, [1 << k])
    if b:
        assert k >= 1
        L = padd(L, [0, 1 << (k - 1)])
    return L

def side_lift(P, monic_top=True):
    """Lambda(P): sum_t digit_lift(P_t, u*(d-t)) * KEY^t (+ KEY^d if monic_top)."""
    d = len(P) - 1
    out = []
    keypow = [ [1] ]
    for _ in range(d + 1):
        keypow.append(pmul(keypow[-1], KEY))
    for t in range(d):
        if P[t] != F4_ZERO:
            out = padd(out, pmul(digit_lift(P[t], U * (d - t)), keypow[t]))
    if monic_top:
        out = padd(out, keypow[d])
    else:
        if P and P[-1] != F4_ZERO:
            out = padd(out, pmul(digit_lift(P[-1], 0 * U), keypow[d]))
    return out

def window_lift(Ubar, cline):
    """lift of Ubar on the weight line cline: digits at abscissa j with height cline-U*j."""
    out = []
    keypow = [[1]]
    for _ in range(len(Ubar) + 1):
        keypow.append(pmul(keypow[-1], KEY))
    for j, val in enumerate(Ubar):
        if val != F4_ZERO:
            k = cline - U * j
            assert k >= 1, "window lift height too small for theta component"
            out = padd(out, pmul(digit_lift(val, k), keypow[j]))
    return out

def is_pure(f):
    s = side_set(f)
    if not s:
        return False
    return 0 in s and (len(f) - 1) // DPRIME in s

def rand_poly(deg, coefbits=8, monic=False):
    p = [random.randrange(-(1 << coefbits), 1 << coefbits) for _ in range(deg + 1)]
    if monic:
        p[-1] = 1
    return trim(p) or [0]

R_LAB = [F4_TH, F4_ONE]     # r = Z + theta
S_LAB = [F4_TH1, F4_ONE]    # s = Z + theta^2 = Z + (theta+1)

def zpoly_str(P):
    names = {F4_ZERO: "0", F4_ONE: "1", F4_TH: "th", F4_TH1: "th+1"}
    return " + ".join(f"({names[c]})Z^{i}" for i, c in enumerate(P)) if P else "0"

# ================================================================ Section 1
print("== Sec 1: frame audit (Phi' = x^2+2x+12 over Z_2) ==")
check(v2(2) == 1 and v2(12) == 2, "coefficient valuations")
h0, h1, h2v = v2(12) + 0, v2(2) + 1, 0 + 2
check(h0 == h1 == h2v == 2, "X-polygon one-sided slope 1, all three abscissae attain")
# psi = 1 + T + T^2 irreducible over F2: no root in F2
check(all((1 + t + t * t) % 2 == 1 for t in (0, 1)), "psi=T^2+T+1 irreducible over F2")
# disc = 4 - 48 = -44 = 4 * (-11); -11 = 5 mod 8 -> nonsquare unit -> Phi' irreducible
check((-11) % 8 == 5, "disc/4 = -11 is a 2-adic nonsquare (5 mod 8): Phi' irreducible")

# ================================================================ Section 2+3
print("== Sec 2/3: mixed product law M (support, side endpoints, raw residual) ==")
n_eq = 0
for trial in range(600):
    g = rand_poly(random.randrange(0, 9), monic=random.random() < 0.5)
    z = rand_poly(random.randrange(0, 9), monic=random.random() < 0.5)
    if not g or not z or g == [0] or z == [0]:
        continue
    gz = pmul(g, z)
    check(W(gz) == W(g) + W(z), f"W additivity trial {trial}")
    sg, sz, sgz = side_set(g), side_set(z), side_set(gz)
    check(min(sgz) == min(sg) + min(sz), f"sideMin additivity trial {trial}")
    check(max(sgz) == max(sg) + max(sz), f"sideMax additivity trial {trial}")
    Rg, Rz, Rgz = res_poly(g), res_poly(z), res_poly(gz)
    check(Rgz == z_mul(Rg, Rz), f"raw residual multiplicativity trial {trial}")
    n_eq += 1
print(f"   {n_eq} random pairs checked (mixed strata incl. non-monic, far, defective)")

# ================================================================ Section 3b (MH9M)
# This is a second, parameterized mirror because the historical frame above has e1=1 and
# therefore cannot exercise the nontrivial twist carry.  The two audited frames are the
# document's Z_2/F_4 frame (e1=1) and the live-carry Z_2/F_4 frame
#   key=x^4+2x^2+4, (e1,f1,h)=(2,2,1), (u,l)=(5,1).

def mh9_slot_idx(e1, h, k):
    for i in range(e1):
        if (i * h) % e1 == k % e1:
            return i
    raise AssertionError("non-coprime slot parameters")

def mh9_twist_exp(e1, h, k):
    return (mh9_slot_idx(e1, h, 1) * k - mh9_slot_idx(e1, h, k)) // e1

def mh9_stage_height(A, e1, h):
    if not A:
        return INF
    return min(e1 * v2(c) + h * i for i, c in enumerate(A) if c != 0)

def mh9_slot_res(A, k, e1, f1, h):
    i = mh9_slot_idx(e1, h, k)
    out = F4_ZERO
    for t in range(f1):
        n = i + e1 * t
        if n * h > k:
            continue
        m = (k - n * h) // e1
        bit = ((A[n] if n < len(A) else 0) // (1 << m)) & 1
        if bit:
            out = f4_add(out, F4_ONE if t == 0 else F4_TH)
    return out

def mh9_twist_read(A, k, e1, f1, h):
    eta_inv = f4_inv(F4_TH)
    q = mh9_twist_exp(e1, h, k)
    eta_inv_q = F4_ONE
    for _ in range(q):
        eta_inv_q = f4_mul(eta_inv_q, eta_inv)
    return f4_mul(eta_inv_q, mh9_slot_res(A, k, e1, f1, h))

def mh9_digit_lift(val, k, e1, f1, h):
    """Inverse-twisted digit lift: twistRead(k,A)=val, in the full slot window."""
    q = mh9_twist_exp(e1, h, k)
    raw = val
    for _ in range(q):
        raw = f4_mul(raw, F4_TH)
    A = [0] * (e1 * f1)
    i = mh9_slot_idx(e1, h, k)
    for t, bit in enumerate(raw):
        n = i + e1 * t
        if bit:
            assert n * h <= k
            A[n] = 1 << ((k - n * h) // e1)
    return trim(A)

def mh9_dev_digits(f, key):
    digs, q = [], list(f)
    while q:
        q, r = pdivmod_monic(q, key)
        digs.append(r)
    return digs

def mh9_W(f, key, e1, h, u):
    if not f:
        return INF
    return min(mh9_stage_height(A, e1, h) + u * j
               for j, A in enumerate(mh9_dev_digits(f, key)) if A)

def mh9_line_read(f, c, key, e1, f1, h, u, jcap):
    digs = mh9_dev_digits(f, key)
    out = []
    for j in range(jcap):
        k = c - u * j
        A = digs[j] if j < len(digs) else []
        out.append(F4_ZERO if k < 0 else mh9_twist_read(A, k, e1, f1, h))
    return z_trim(out)

def mh9_key_powers(key, n):
    powers = [[1]]
    for _ in range(n):
        powers.append(pmul(powers[-1], key))
    return powers

def mh9_side_lift(P, key, e1, f1, h, u):
    d = len(P) - 1
    powers = mh9_key_powers(key, d)
    out = list(powers[d])
    for t in range(d):
        out = padd(out, pmul(mh9_digit_lift(P[t], u * (d - t), e1, f1, h), powers[t]))
    return out

def mh9_window_lift(P, grade, key, e1, f1, h, u):
    powers = mh9_key_powers(key, len(P))
    out = []
    for j, val in enumerate(P):
        k = grade - u * j
        assert k >= (e1 * f1) * h
        out = padd(out, pmul(mh9_digit_lift(val, k, e1, f1, h), powers[j]))
    return out

print("== Sec 3b [MH9M]: above-line mixed reads, twist carry delta=0/1 ==")
mh9_checks_start = TESTS[0]
mh9_frames = [
    ("doc-e1=1", [12, 2, 1], 1, 2, 1, 3),
    ("live-e1=2", [4, 0, 2, 0, 1], 2, 2, 1, 5),
]
mh9_grades = 0
mh9_zero_terms = 0
mh9_one_terms = 0
for fname, fkey, fe1, ff1, fh, fu in mh9_frames:
    P = [F4_TH, F4_TH1, F4_ONE]
    Q = [F4_TH1, F4_TH]
    pure = mh9_side_lift(P, fkey, fe1, ff1, fh, fu)
    wpure = mh9_W(pure, fkey, fe1, fh, fu)
    check(wpure == fu * (len(P) - 1), f"MH9M {fname}: pure support weight")
    check(mh9_line_read(pure, wpure, fkey, fe1, ff1, fh, fu, len(P)) == P,
          f"MH9M {fname}: support-line residual")
    for rise in range(1, 9):
        d = fu * (len(Q) + 1) + rise
        Uline = mh9_window_lift(Q, d, fkey, fe1, ff1, fh, fu)
        check(mh9_W(Uline, fkey, fe1, fh, fu) == d,
              f"MH9M {fname}: correction grade +{rise}")
        c = wpure + d
        lhs = mh9_line_read(pmul(pure, Uline), c, fkey, fe1, ff1, fh, fu,
                             len(P) + len(Q) - 1)
        rhs = z_mul(P, Q)
        check(lhs == rhs, f"MH9M {fname}: above-line product read +{rise}")
        # The same requested line is zero if the correction is moved one grade higher.
        Uhigh = mh9_window_lift(Q, d + 1, fkey, fe1, ff1, fh, fu)
        check(mh9_W(Uhigh, fkey, fe1, fh, fu) >= d,
              f"MH9M {fname}: strict correction floor +{rise}")
        check(mh9_line_read(pmul(pure, Uhigh), c, fkey, fe1, ff1, fh, fu,
                             len(P) + len(Q) - 1) == [],
              f"MH9M {fname}: strict-above product read vanishes +{rise}")
        # Audit TW-delta termwise on the surviving convolution, including its raw carry.
        for t, pv in enumerate(P):
            for j, qv in enumerate(Q):
                if pv == F4_ZERO or qv == F4_ZERO:
                    continue
                kp, kq = wpure - fu * t, d - fu * j
                delta = (mh9_twist_exp(fe1, fh, kp + kq)
                         - mh9_twist_exp(fe1, fh, kp) - mh9_twist_exp(fe1, fh, kq))
                check(delta in (0, 1), f"MH9M {fname}: delta bit")
                a = mh9_digit_lift(pv, kp, fe1, ff1, fh)
                b = mh9_digit_lift(qv, kq, fe1, ff1, fh)
                _, rem = pdivmod_monic(pmul(a, b), fkey)
                eta_delta = F4_ONE if delta == 0 else F4_TH
                check(mh9_slot_res(rem, kp + kq, fe1, ff1, fh)
                      == f4_mul(eta_delta,
                                f4_mul(mh9_slot_res(a, kp, fe1, ff1, fh),
                                       mh9_slot_res(b, kq, fe1, ff1, fh))),
                      f"MH9M {fname}: raw carry branch delta={delta}")
                check(mh9_twist_read(rem, kp + kq, fe1, ff1, fh) == f4_mul(pv, qv),
                      f"MH9M {fname}: tau=1 after twist delta={delta}")
                if delta == 0:
                    mh9_zero_terms += 1
                else:
                    mh9_one_terms += 1
        mh9_grades += 1
print(f"   {TESTS[0] - mh9_checks_start} checks on {mh9_grades} above-line grades; "
      f"term branches delta=0: {mh9_zero_terms}, delta=1: {mh9_one_terms}")

# ================================================================ Section 4
print("== Sec 4: the Newton engine end-to-end (G=r, H=s), contraction audit ==")
G, Hres = R_LAB, S_LAB
a, b = len(G) - 1, len(Hres) - 1
w1, w2 = U * ELL * a, U * ELL * b
w = w1 + w2

g1 = side_lift(G)
g2 = side_lift(Hres)
check(is_pure(g1) and res_poly(g1) == G, "Lambda(r): pure, residual exactly r")
check(is_pure(g2) and res_poly(g2) == Hres, "Lambda(s): pure, residual exactly s")
check(W(g1) == w1 and W(g2) == w2, "lift weights")

# ambient: product + admissible perturbation of weight >= w+1
pert = pmul([1 << (w + 1)], rand_poly(2))
if W(pert) < w + 1:
    pert = [1 << (w + 1)]
g_amb = padd(pmul(g1, g2), pert)
check(g_amb[-1] == 1 and len(g_amb) - 1 == ELL * (a + b) * DPRIME, "ambient monic, degree l(a+b)D'")
check(is_pure(g_amb), "ambient pure")
check(res_poly(g_amb) == z_mul(G, Hres), "R(ambient) = r*s")

# Newton loop
p1, p2 = list(g1), list(g2)
prev_weight = None
CMAX = 60
step = 0
weights = []
while True:
    e = psub(g_amb, pmul(p1, p2))
    we = W(e)
    weights.append(we)
    if prev_weight is not None:
        check(we >= prev_weight + 1, f"contraction step {step}: {prev_weight} -> {we}")
    if we >= CMAX or not e:
        break
    c = we
    jcap = ELL * (a + b)  # error digit window
    Ebar = line_read(e, c, jcap)
    # Bezout: Ebar = H*Ubar + G*Vbar, deg Ubar < a, deg Vbar < b
    gcd, sc, tc = z_gcd_bezout(Hres, G)   # sc*H + tc*G = gcd (a unit)
    check(len(gcd) == 1, "gcd(H,G) is a unit")
    ginv = f4_inv(gcd[0])
    sc = z_mul(sc, [ginv]); tc = z_mul(tc, [ginv])
    Ubar_full = z_mul(sc, Ebar)
    q, Ubar = z_divmod(Ubar_full, G)        # Ubar = sc*Ebar mod G, deg < a
    Vbar_num = z_add(Ebar, z_mul(Hres, Ubar))  # char 2: subtraction = addition
    Vbar, rem = z_divmod(Vbar_num, G)
    check(not rem, "exact division in Bezout solve")
    check(len(Ubar) <= a and len(Vbar) <= b, "Bezout degree windows")
    Ucor = window_lift(Ubar, c - w2)
    Vcor = window_lift(Vbar, c - w1)
    p1 = preduce(padd(p1, Ucor), PREC)
    p2 = preduce(padd(p2, Vcor), PREC)
    check(p1[-1] == 1 and len(p1) - 1 == ELL * a * DPRIME, f"p1 window step {step}")
    check(p2[-1] == 1 and len(p2) - 1 == ELL * b * DPRIME, f"p2 window step {step}")
    check(is_pure(p1) and res_poly(p1) == G, f"p1 invariants step {step}")
    check(is_pure(p2) and res_poly(p2) == Hres, f"p2 invariants step {step}")
    prev_weight = we
    step += 1
    if step > 200:
        check(False, "no convergence in 200 steps")
        break
print(f"   converged in {step} steps; error-weight trajectory: {weights}")
exact_gain = sum(1 for i in range(1, len(weights)) if weights[i] == weights[i-1] + 1)
print(f"   contraction: gains of exactly +1 in {exact_gain}/{max(1,len(weights)-1)} steps (>= +1 in all)")
final_err = psub(g_amb, pmul(p1, p2))
check(W(final_err) >= CMAX, "final factorization error weight >= CMAX")

# negative control 1: r = s (not coprime) -> Bezout gcd is not a unit
gcd_bad, _, _ = z_gcd_bezout(R_LAB, R_LAB)
check(len(gcd_bad) != 1, "negative control: gcd(r,r) not a unit (solve impossible)")
# negative control 2: point-sided ambient rejected by the hypothesis check
g_far = padd(pmul(KEY, KEY), [2])   # Phi'^2 + 2: point side at 0
check(not is_pure(g_far) or len(side_set(g_far)) == 1, "negative control: Phi'^2+2 has point side")
Rfar = res_poly(g_far)
check(Rfar is not None and len(Rfar) == 1, "negative control: constant residual (r does not divide)")

# ================================================================ Section 5
print("== Sec 5: the defective-stratum refutation (doc Sec 7) ==")
fS = padd(KEY, [0, 4])                    # x^2 + 6x + 12
check(fS == [12, 6, 1], "fS = x^2+6x+12")
check(is_pure(fS) and W(fS) == 3 and side_set(fS) == [0, 1], "fS pure, W=3, side {0,1}")
check(res_poly(fS) == R_LAB, "R_raw(fS) = Z + theta = r EXACTLY (m=1)")
q_far = [1, 1]                            # x + 1
check(W(q_far) == 0 and side_set(q_far) == [0], "q = x+1: far, weight 0")
check(res_poly(q_far) == [F4_ONE], "R_raw(q) = 1 (the graded identity)")
g_def = pmul(fS, q_far)
check(len(g_def) - 1 == 3, "ambient degree 3 (defective: D'=2 does not divide 3)")
check(is_pure(g_def), "DEFECTIVE ambient IS pure (IsDvPure holds)")
d0, d1 = dev_digits(g_def)[0], dev_digits(g_def)[1]
print(f"   dev0 = {d0}, dev1 = {d1}; dvHgt = ({stage_height(d0)}, {stage_height(d1)})")
check(res_poly(g_def) == R_LAB, "R_raw(fS*q) = Z + theta = r EXACTLY -> HasLabel(fS*q)")
# slot-height pattern identical for fS and fS*q  (normalization robustness)
sh_fS = [ (j, W(fS) - U*j) for j in side_set(fS) ]
sh_g  = [ (j, W(g_def) - U*j) for j in side_set(g_def) ]
check(sh_fS == sh_g, "identical slot-height patterns (3,0): twist-normalization-robust")
# BlockContext for the ambient: monic, squarefree, key-free, genuine side, r | R
check(g_def[-1] == 1, "ambient monic")
disc_fS = 6 * 6 - 4 * 12
check(disc_fS != 0, "fS squarefree (disc = -12 != 0)")
check(sum(c * (-1) ** i for i, c in enumerate(fS)) != 0, "fS(-1) != 0: q coprime to fS -> f squarefree")
check(dev_digits(g_def)[0] != [], "Phi' does not divide the ambient")
check((max(side_set(g_def)) - min(side_set(g_def))) // ELL == 1 > 0, "genuine side (sideDeg = 1)")
# and the two labelled splits differ: (fS, q) vs (g_def, 1); deg 2 != 3.
print("   REFUTATION CONFIRMED: two labelled splits (fS, x+1) and (fS*(x+1), 1);")
print("   the D'-divisible labelled divisor fS does NOT absorb fS*(x+1):")
quo, rem = z_divmod(res_poly(g_def), res_poly(fS))
check(len(g_def) - 1 == 3 and len(fS) - 1 == 2, "degrees 3 vs 2: fS*(x+1) cannot divide fS")

# ================================================================ Section 6
print("== Sec 6: uniqueness brute search on a D'-divisible pure ambient ==")
amb = pmul(g1, g2)  # Lambda(r)*Lambda(s), degree 4, D' | 4
check(is_pure(amb) and (len(amb) - 1) % DPRIME == 0, "ambient pure with D' | deg")
# search monic quadratics x^2 + beta x + gamma (coefficients in [0, 2^7)) that divide amb
# mod 2^12 and carry the exact label r (residual = r, pure, side reach)
found = []
for beta in range(0, 128):
    for gamma in range(0, 128):
        cand = [gamma, beta, 1]
        quo_c, rem_c = pdivmod_monic(list(amb), cand)
        if any(c % (1 << 12) != 0 for c in rem_c):
            continue
        if not is_pure(cand):
            continue
        if res_poly(cand) == R_LAB:
            found.append((beta, gamma))
g1red = [c % (1 << 7) for c in g1]
check(len(found) <= 1, f"at most one labelled quadratic divisor mod 2^12 (found {found})")
if found:
    check(found[0] == (g1red[1], g1red[0]), f"the found divisor IS the engine's g1 mod 2^7: {found[0]} vs {(g1red[1], g1red[0])}")

# ================================================================ summary
print("=" * 60)
print(f"TOTAL {TESTS[0]} checks, {len(FAILS)} FAILS")
if FAILS:
    for m in FAILS:
        print("  -", m)
    sys.exit(1)
print("ALL PASS")
