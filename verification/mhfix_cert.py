#!/usr/bin/env python3
"""mhfix_cert.py — unit MHFIX (2026-08-27): numeric certificate for the CORRECTED
Theorem M root (the slot-carry / twistRead product law), replacing the refuted M1(2).

Claimed generic laws (frame F = (e1, f1, h, key), gcd(h,e1)=1, 0<h, K = F_p[T]/psi,
eta = class of T, notation q = twistExp, i = slotIdx, D' = e1*f1):

  (TW-d)  q(k) + q(k') + d(k,k') = q(k+k'),  where e1*d(k,k') = i(k)+i(k')-i(k+k'),
          and d(k,k') in {0,1}.
  (M1'-carry)  for digits a, b (deg < D') with stageHeight a >= ka, stageHeight b >= kb:
          slotRes(ka+kb, (a*b) mod key) = eta^d(ka,kb) * slotRes(ka,a) * slotRes(kb,b).
  (M1'-twist)  twistRead(ka+kb, (a*b) mod key) = twistRead(ka,a) * twistRead(kb,b),
          twistRead(k,A) := eta^{-q(k)} * slotRes(k,A).
  (M1'-faith)  if the heights are EXACT (= ka, = kb, finite), both right-hand reads are
          nonzero, hence stageHeight((a*b) mod key) = ka+kb exactly.
  (M-tau1)  dvResPoly(g*z) = dvResPoly(g) * dvResPoly(z) in K[Z]  (tau = 1), under the
          strict floor l*(D'*h) < u — checked at a frame with e1 = 2 (live carry), which
          the 2026-08-26 dv_hensel_cert (e1 = 1, twist-trivial) never exercised.

All mirrors are faithful to the Lean sources: slotIdx/twistExp (C15), slotWindow (C17),
slotRes (C21: digAt-read times eta^t), twistRead (C22), stageHeight (C02: min e1*v+h*n),
dev (B: key-adic digits), dvResPoly (C25: coeff t = twistRead(M0-t*u, dev(jmin+t*l))),
resPoly convention (B29: T^j-coeff read at abscissa sideMin+l*j, line height H0-u*j).
Exact integer arithmetic throughout (no truncation).
"""

import random
import sys

random.seed(20260827)

FAILS = []
CHECKS = [0]


def check(cond, msg):
    CHECKS[0] += 1
    if not cond:
        FAILS.append(msg)
        print("FAIL:", msg)


# ---------- C15/C16/C17 mirrors (pure integer) ----------

def slot_idx(e1, h, k):
    for i in range(e1):
        if (i * h) % e1 == k % e1:
            return i
    return 0  # junk default, unreachable when gcd(h,e1)=1


def twist_exp(e1, h, k):
    return (slot_idx(e1, h, 1) * k - slot_idx(e1, h, k)) // e1


def slot_window(e1, f1, h, k):
    i = slot_idx(e1, h, k)
    return [t for t in range(f1) if (i + e1 * t) * h <= k]


# ---------- Part A: the delta-arithmetic grid ----------

def part_A():
    for e1 in range(1, 9):
        for h in range(1, 13):
            if __import__("math").gcd(h, e1) != 1:
                continue
            for k in range(0, 61):
                for kp in range(0, 61):
                    ik, ikp, iks = slot_idx(e1, h, k), slot_idx(e1, h, kp), slot_idx(e1, h, k + kp)
                    diff = ik + ikp - iks
                    ok = diff % e1 == 0 and diff // e1 in (0, 1)
                    check(ok, f"A: carry not a bit e1={e1} h={h} k={k} k'={kp}")
                    d = diff // e1
                    check(twist_exp(e1, h, k) + twist_exp(e1, h, kp) + d
                          == twist_exp(e1, h, k + kp),
                          f"A: TW-d fails e1={e1} h={h} k={k} k'={kp}")
    print(f"Part A done ({CHECKS[0]} checks so far)")


# ---------- exact polynomial arithmetic over ZZ ----------

def pnorm(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    n = max(len(a), len(b))
    return pnorm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return pnorm(out)


def pdivmod_monic(f, g):
    """f = q*g + r with g monic, deg r < deg g; exact over ZZ."""
    f = f[:]
    dg = len(g) - 1
    q = [0] * max(len(f) - dg, 0)
    while len(f) - 1 >= dg and f:
        c = f[-1]
        s = len(f) - 1 - dg
        q[s] = c
        for i in range(len(g)):
            f[s + i] -= c * g[i]
        f = pnorm(f)
    return pnorm(q), f


def vp(x, p):
    if x == 0:
        return None
    x = abs(x)
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def stage_height(A, p, e1, h):
    """C02: min over n of e1*vp(A_n) + h*n; None for the zero polynomial."""
    best = None
    for n, c in enumerate(A):
        if c == 0:
            continue
        val = e1 * vp(c, p) + h * n
        if best is None or val < best:
            best = val
    return best


def dev(f, key, j):
    """the j-th key-adic digit of f."""
    for _ in range(j):
        f, _ = pdivmod_monic(f, key)
    _, r = pdivmod_monic(f, key)
    return r


# ---------- K = F_p[T]/psi arithmetic ----------

class K:
    def __init__(self, p, psi):
        self.p, self.psi, self.f1 = p, psi, len(psi) - 1

    def red(self, a):
        a = [c % self.p for c in a]
        while len(a) > self.f1:
            c = a.pop()
            s = len(a) - self.f1
            for i in range(self.f1):
                a[s + i] = (a[s + i] - c * self.psi[i]) % self.p
        while len(a) < self.f1:
            a.append(0)
        return tuple(a)

    def add(self, x, y):
        return tuple((a + b) % self.p for a, b in zip(x, y))

    def mul(self, x, y):
        out = [0] * (2 * self.f1 - 1 if self.f1 > 0 else 1)
        for i, a in enumerate(x):
            for j, b in enumerate(y):
                out[i + j] += a * b
        return self.red(out)

    def zero(self):
        return tuple([0] * self.f1)

    def one(self):
        return self.red([1])

    def eta(self):
        return self.red([0, 1]) if self.f1 > 1 else self.red([self.p - self.psi[0] % self.p])

    def pow(self, x, n):
        r = self.one()
        for _ in range(n):
            r = self.mul(r, x)
        return r

    def inv(self, x):
        # q-2 power in F_q
        q = self.p ** self.f1
        r, b, n = self.one(), x, q - 2
        while n:
            if n & 1:
                r = self.mul(r, b)
            b = self.mul(b, b)
            n >>= 1
        return r


def digat(c, p, m):
    """B.21 digAt mirror: the m-th p-adic digit of the integer c (floor semantics)."""
    return (c // p ** m) % p


class Frame:
    """key = sum_j lift(psi_j) p^{h(f1-j)} x^{e1 j} + strictly-above noise; pure of slope
    h/e1 at X, stageHeight key = D'*h, frame residual psi (B29 convention audited)."""

    def __init__(self, p, e1, f1, h, psi, noise=True):
        self.p, self.e1, self.f1, self.h = p, e1, f1, h
        self.D = e1 * f1
        self.K = K(p, psi)
        key = [0] * (self.D + 1)
        for j in range(f1 + 1):
            key[e1 * j] = (psi[j] if j < f1 else 1) * p ** (h * (f1 - j))
        if noise:
            for _ in range(3):
                n = random.randrange(self.D)
                # strictly above the side line: e1*m + h*n > D'*h
                m0 = (self.D * h - h * n) // e1 + 1
                key[n] += random.randrange(p) * p ** (m0 + random.randrange(3))
        self.key = key
        # frame audit: stage height and B29-convention residual
        assert stage_height(key, p, e1, h) == self.D * h
        got = [digat(key[e1 * j], p, h * (f1 - j)) for j in range(f1)]
        assert got == [c % p for c in psi[:f1]], "frameRes != psi (B29 convention)"

    def slot_res(self, A, k):
        """C21 mirror: sum over the window of digAt-reads times eta^t."""
        i = slot_idx(self.e1, self.h, k)
        acc = self.K.zero()
        for t in slot_window(self.e1, self.f1, self.h, k):
            n = i + self.e1 * t
            m = (k - n * self.h) // self.e1
            c = digat(A[n], self.p, m) if n < len(A) else 0
            acc = self.K.add(acc, self.K.mul(self.K.red([c]),
                                             self.K.pow(self.K.eta(), t)))
        return acc

    def twist_read(self, A, k):
        q = twist_exp(self.e1, self.h, k)
        return self.K.mul(self.K.pow(self.K.inv(self.K.eta()), q), self.slot_res(A, k))

    def rand_digit(self, k, exact=True):
        """random digit (deg < D') with stageHeight >= k, and = k when exact."""
        i = slot_idx(self.e1, self.h, k)
        A = [0] * self.D
        slots = slot_window(self.e1, self.f1, self.h, k)
        live = [t for t in slots if random.random() < 0.7] if slots else []
        if exact and slots and not live:
            live = [random.choice(slots)]
        for t in slots:
            n = i + self.e1 * t
            m = (k - n * self.h) // self.e1
            c = random.randrange(1, self.p) if t in live else 0
            A[n] = c * self.p ** m + random.randrange(self.p) * self.p ** (m + 1 + random.randrange(2))
        # above-line noise at arbitrary degrees
        for _ in range(2):
            n = random.randrange(self.D)
            m0 = (k - n * self.h) // self.e1 + 1 if n * self.h <= k else 0
            A[n] += random.randrange(self.p) * self.p ** (m0 + random.randrange(2))
        if exact and not slots:
            return None  # height k has an empty window: no digit attains it
        return A


def part_B():
    frames = [(3, 2, 2, 3), (5, 3, 2, 2), (3, 2, 3, 5), (2, 1, 2, 1),
              (7, 4, 1, 3), (5, 3, 1, 4), (3, 5, 2, 2)]
    for (p, e1, f1, h) in frames:
        # psi monic irreducible, psi(0) != 0 (deg <= 3: no roots <=> irreducible; deg 1 free)
        while True:
            psi = [random.randrange(1, p)] + [random.randrange(p) for _ in range(f1 - 1)] + [1]
            if f1 == 1 or all(sum(c * x ** j for j, c in enumerate(psi)) % p for x in range(p)):
                break
        F = Frame(p, e1, f1, h, psi)
        delta_hits = {0: 0, 1: 0}
        trials = 0
        while trials < 120:
            ka, kb = random.randrange(0, 5 * F.D * h + 1), random.randrange(0, 5 * F.D * h + 1)
            exact_a, exact_b = random.random() < 0.85, random.random() < 0.85
            a, b = F.rand_digit(ka, exact_a), F.rand_digit(kb, exact_b)
            if a is None or b is None or not pnorm(a[:]) or not pnorm(b[:]):
                continue
            trials += 1
            ha, hb = stage_height(a, p, e1, h), stage_height(b, p, e1, h)
            check(ha >= ka and hb >= kb, f"B{p},{e1},{f1},{h}: bad digit heights")
            if exact_a:
                check(ha == ka, f"B{p},{e1},{f1},{h}: exact height missed a")
            _, E = pdivmod_monic(pmul(a, b), F.key)
            k = ka + kb
            d = twist_exp(e1, h, k) - twist_exp(e1, h, ka) - twist_exp(e1, h, kb)
            delta_hits[d] += 1
            lhs = F.slot_res(E, k)
            rhs = F.K.mul(F.K.pow(F.K.eta(), d),
                          F.K.mul(F.slot_res(a, ka), F.slot_res(b, kb)))
            check(lhs == rhs, f"B{p},{e1},{f1},{h}: carry law ka={ka} kb={kb}")
            check(F.twist_read(E, k) ==
                  F.K.mul(F.twist_read(a, ka), F.twist_read(b, kb)),
                  f"B{p},{e1},{f1},{h}: twistRead law ka={ka} kb={kb}")
            if exact_a and exact_b and ha == ka and hb == kb:
                check(F.slot_res(a, ka) != F.K.zero() and F.slot_res(b, kb) != F.K.zero(),
                      f"B{p},{e1},{f1},{h}: faithfulness (nonzero read) ka={ka} kb={kb}")
                check(stage_height(E, p, e1, h) == k,
                      f"B{p},{e1},{f1},{h}: M1(1) exact height ka={ka} kb={kb}")
        print(f"Part B frame (p,e1,f1,h)=({p},{e1},{f1},{h}): 120 pairs, "
              f"delta=0 on {delta_hits[0]}, delta=1 on {delta_hits[1]}")
        if e1 > 1:
            check(delta_hits[1] > 0, f"B{p},{e1},{f1},{h}: carry never live (weak test)")


# ---------- Part C: the mixed residual product law, tau = 1 ----------

def dv_data(F, f, u, l):
    """(W, jmin, jmax, R) for the direction (u,l); R per the C25 mirror."""
    p, e1, h = F.p, F.e1, F.h
    nd = len(f) - 1
    heights = {}
    g = f[:]
    j = 0
    while pnorm(g[:]):
        _, r = pdivmod_monic(g, F.key)
        hh = stage_height(r, p, e1, h)
        if hh is not None:
            heights[j] = hh
        g, _ = pdivmod_monic(g, F.key)
        j += 1
    W = min(l * hh + u * jj for jj, hh in heights.items())
    side = [jj for jj, hh in heights.items() if l * hh + u * jj == W]
    jmin, jmax = min(side), max(side)
    assert (jmax - jmin) % l == 0
    sdeg = (jmax - jmin) // l
    M0 = heights[jmin]
    R = []
    for t in range(sdeg + 1):
        R.append(F.twist_read(dev(f, F.key, jmin + t * l), M0 - t * u))
    while R and R[-1] == F.K.zero():
        R.pop()
    return W, jmin, jmax, R


def kpoly_mul(Kf, A, B):
    if not A or not B:
        return []
    out = [Kf.zero()] * (len(A) + len(B) - 1)
    for i, x in enumerate(A):
        for j, y in enumerate(B):
            out[i + j] = Kf.add(out[i + j], Kf.mul(x, y))
    while out and out[-1] == Kf.zero():
        out.pop()
    return out


def rand_poly(F, maxdeg):
    while True:
        f = [random.randrange(F.p) * F.p ** random.randrange(0, 4)
             for _ in range(random.randrange(1, maxdeg + 2))]
        f = pnorm(f)
        if f:
            return f


def part_C():
    p, e1, f1, h = 3, 2, 2, 3
    psi = [1, 0, 1]  # T^2 + 1, irreducible over F_3, psi(0) = 1 != 0 (the F9 gate model)
    F = Frame(p, e1, f1, h, psi, noise=True)
    u, l = 25, 2  # strict floor: l*(D'*h) = 2*12 = 24 < 25, gcd(25,2)=1
    for trial in range(250):
        g, z = rand_poly(F, 7), rand_poly(F, 7)
        Wg, jg, jGmax, Rg = dv_data(F, g, u, l)
        Wz, jz, jZmax, Rz = dv_data(F, z, u, l)
        Wp, jp, jPmax, Rp = dv_data(F, pmul(g, z), u, l)
        check(Wp == Wg + Wz, f"C: W additivity trial {trial}")
        check(jp == jg + jz and jPmax == jGmax + jZmax, f"C: side additivity trial {trial}")
        check(Rp == kpoly_mul(F.K, Rg, Rz), f"C: R(gz) != R(g)R(z) (tau!=1?) trial {trial}")
    print("Part C done: 250 mixed pairs at the (2,2,3)/F9 frame, u/l = 25/2")


part_A()
part_B()
part_C()
print(f"\nTOTAL: {CHECKS[0]} checks, {len(FAILS)} FAILS")
sys.exit(1 if FAILS else 0)
