#!/usr/bin/env python3
"""
WELD-ZERO battery (WELDZERO_2026-08-14.md, S5).

Purpose.  Test, by ACTUAL polynomial re-division over Z_p (exact integer
arithmetic, no formula shortcut), the level-1 substitution theorem
LEMMA WZ-A of `lean/notes/openmath/WELDZERO_2026-08-14.md`:

    at a stage-alpha event of multiplicity mu and integer dv-slope kappa,
    recentering Phi' |-> Phi' + w with w := -lift(s; kappa) kills all mu
    pins IFF the MULTIPLICATIVE-convention side residual R_N satisfies
    R_N(T) = (T - s)^mu,

and, sharply, that for a general side residual the surviving pins and their
coherent digits are exactly

    dv(A_k^new) = (mu-k)kappa   and   gamma_k^new = vartheta_{mu-k} * rho_k
    (rho_k := [T^k] R_N(T + s))   whenever rho_k != 0,
    dv(A_k^new) > (mu-k)kappa                                 whenever rho_k = 0.

The battery therefore also decides the CONVENTION question: the
digit-convention ("twisted residual", read against the coherent normalizers
n(t*kappa)) and the multiplicative-convention (read against n(kappa)^t)
residuals differ by the diagonal unit rescaling

    Gamma_t = c_t^mult * vartheta_t,   vartheta_t = eta^{floor(t*i(kappa)/e1)}
                                                    [T1 (C2-level-1)],

and a digit-convention perfect power is NOT a multiplicative-convention
perfect power when vartheta is live.  Frames with eta != 1 exhibit the
separation; eta = 1 / i(kappa) = 0 frames are the controls.

Coverage (honest): f1 = 1 genres only (as GENHN's own sealed battery,
GENHN-BOX-3), e1 in {2,3}, h in {1,3}, mu in {3,4}, p in {2,3,5,7}.
A live level-1 wrap needs eta != 1, hence |K| > 2, hence q > 2 at f1 = 1 --
which is exactly why GENHN's q = 2 tower rows never saw it (GENHN dated
erratum 2026-08-09, HETOW PE1 F-1: "where eta = 1 forcibly").

Exit 0 iff every check passes.  No external dependencies.
"""

from fractions import Fraction
import itertools
import sys

# ----------------------------------------------------------------- polynomials
# A polynomial is a list of Fraction coefficients, index = degree, no trailing 0s.


def trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else Fraction(0)) + (b[i] if i < len(b) else Fraction(0))
                 for i in range(n)])


def psub(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else Fraction(0)) - (b[i] if i < len(b) else Fraction(0))
                 for i in range(n)])


def pmul(a, b):
    if not a or not b:
        return []
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def pscal(c, a):
    return trim([Fraction(c) * x for x in a])


def pdivmod_monic(f, g):
    """Divide f by MONIC g; return (q, r)."""
    assert g and g[-1] == 1
    f = list(f)
    dg = len(g) - 1
    q = [Fraction(0)] * max(0, len(f) - dg)
    for k in range(len(f) - 1, dg - 1, -1):
        c = f[k]
        if c == 0:
            continue
        q[k - dg] = c
        for j in range(dg + 1):
            f[k - dg + j] -= c * g[j]
    return trim(q), trim(f[:dg])


def development(f, Phi):
    """Phi-adic development: f = sum_j C_j Phi^j, deg C_j < deg Phi."""
    out = []
    cur = list(f)
    while cur:
        q, r = pdivmod_monic(cur, Phi)
        out.append(r)
        cur = q
    return out


def det(mat):
    """Exact determinant, fraction arithmetic, small matrices."""
    n = len(mat)
    m = [[Fraction(x) for x in row] for row in mat]
    sign = Fraction(1)
    for c in range(n):
        piv = None
        for r in range(c, n):
            if m[r][c] != 0:
                piv = r
                break
        if piv is None:
            return Fraction(0)
        if piv != c:
            m[c], m[piv] = m[piv], m[c]
            sign = -sign
        for r in range(c + 1, n):
            if m[r][c] != 0:
                fac = m[r][c] / m[c][c]
                for k in range(c, n):
                    m[r][k] -= fac * m[c][k]
    out = sign
    for i in range(n):
        out *= m[i][i]
    return out


def resultant(a, b):
    """Sylvester resultant of two polynomials (lists, index = degree)."""
    da, db = len(a) - 1, len(b) - 1
    n = da + db
    if n == 0:
        return Fraction(1)
    M = [[Fraction(0)] * n for _ in range(n)]
    for r in range(db):
        for i, c in enumerate(a):
            M[r][r + (da - i)] = c
    for r in range(da):
        for i, c in enumerate(b):
            M[db + r][r + (db - i)] = c
    return det(M)


# ----------------------------------------------------------------- p-adic tools

def vp(x, p):
    """p-adic valuation of a nonzero Fraction; None for 0."""
    if x == 0:
        return None
    num, den = x.numerator, x.denominator
    v = 0
    while num % p == 0:
        num //= p
        v += 1
    while den % p == 0:
        den //= p
        v -= 1
    return v


def unit_res(x, p):
    """residue of x / p^{v_p(x)} in F_p, as an int in [0, p)."""
    v = vp(x, p)
    y = x / Fraction(p) ** v
    num, den = y.numerator % p, y.denominator % p
    return (num * pow(den, p - 2, p)) % p if p > 2 else (num * pow(den, p - 2, p)) % p


def dv_of(A, e1, h, p):
    """GENHN-2 slot minimum: dv(A(theta)) = min_i (e1*v_p(a_i) + i*h).  inf if A = 0."""
    best = None
    for i, c in enumerate(A):
        if c == 0:
            continue
        m = e1 * vp(c, p) + i * h
        if best is None or m < best:
            best = m
    return best  # None means +infinity


def dv_argmin(A, e1, h, p):
    best, arg = None, None
    for i, c in enumerate(A):
        if c == 0:
            continue
        m = e1 * vp(c, p) + i * h
        if best is None or m < best:
            best, arg = m, i
    return best, arg


def coherent_digit(A, e1, h, p):
    """At f1 = 1 the slot minimum is attained at a UNIQUE monomial index i0
    (distinct i < e1 sit in distinct classes mod e1 since gcd(h,e1)=1), so the
    coherent digit against n(m) = x^{i0} pi^{a} is the unit residue of a_{i0}."""
    m, i0 = dv_argmin(A, e1, h, p)
    if m is None:
        return None
    return unit_res(A[i0], p)


def norm_dv(A, Phi, e1, h, p, D):
    """Decorrelated valuation leg: dv(A(theta)) = e1 * v_p(Res(Phi, A)) / D."""
    R = resultant(Phi, A) if A else Fraction(0)
    if R == 0:
        return None
    num = e1 * vp(R, p)
    assert num % D == 0, (num, D)
    return num // D


def iofm(m, e1, h):
    """i(m): the unique 0 <= i < e1 with i*h == m (mod e1)."""
    for i in range(e1):
        if (i * h - m) % e1 == 0:
            return i
    raise AssertionError


def nhat(m, e1, h, p):
    """Normalizer monomial n(m) = x^{i(m)} pi^{a(m)} as a polynomial."""
    i = iofm(m, e1, h)
    a = (m - i * h) // e1
    poly = [Fraction(0)] * i + [Fraction(p) ** a]
    return trim(poly)


# ----------------------------------------------------------------- F_p[T] tools

def shift_poly(coeffs, s, p):
    """coefficients of R(T + s) mod p, coeffs indexed by degree."""
    n = len(coeffs)
    out = [0] * n
    for j, cj in enumerate(coeffs):
        if cj % p == 0:
            continue
        # (T + s)^j
        for k in range(j + 1):
            out[k] = (out[k] + cj * binom(j, k) * pow(s, j - k, p)) % p
    return out


def binom(n, k):
    if k < 0 or k > n:
        return 0
    num = 1
    for i in range(k):
        num = num * (n - i) // (i + 1)
    return num


def power_linear(mu, s, p):
    """coefficients of (T - s)^mu mod p, indexed by degree."""
    return [(binom(mu, j) * pow(-s % p, mu - j, p)) % p for j in range(mu + 1)]


# ----------------------------------------------------------------- one frame

class Frame:
    def __init__(self, name, p, e1, h, z, mu, kappa, s, residual=None, expect_all_kill=None):
        self.name = name
        self.p, self.e1, self.h, self.z = p, e1, h, z
        self.mu, self.kappa, self.s = mu, kappa, s
        self.D = e1                      # f1 = 1, so D' = e1*f1 = e1
        self.eta = z % p
        # Phi' = x^{e1} - z*pi^h  (f1 = 1); theta^{e1} = z pi^h, eta = res(z)
        self.Phi = trim([Fraction(-z) * Fraction(p) ** h] + [Fraction(0)] * (e1 - 1) + [Fraction(1)])
        # residual: list of length mu+1 of MULTIPLICATIVE coefficients c_j (c_mu = 1)
        self.residual = residual if residual is not None else power_linear(mu, s, p)
        self.expect_all_kill = expect_all_kill

    def vartheta(self, t):
        """vartheta_t = res( n(kappa)^t / n(t*kappa) ) -- computed from the MONOMIALS,
        not from the closed form, so the closed form can be checked against it."""
        p, e1, h, kappa = self.p, self.e1, self.h, self.kappa
        ik, ak = iofm(kappa, e1, h), (kappa - iofm(kappa, e1, h) * h) // e1
        it, at = iofm(t * kappa, e1, h), (t * kappa - iofm(t * kappa, e1, h) * h) // e1
        # n(kappa)^t / n(t kappa) = x^{t*ik - it} pi^{t*ak - at} = (x^{e1}/pi^h)^W
        dx, dpi = t * ik - it, t * ak - at
        assert dx % e1 == 0
        W = dx // e1
        assert dpi == -h * W, (dpi, W)
        return pow(self.eta, W, p), W

    def vartheta_closed(self, t):
        """T1 (C2-level-1): vartheta_{1,t} = eta^{floor(t*i(kappa)/e1)}."""
        W = (t * iofm(self.kappa, self.e1, self.h)) // self.e1
        return pow(self.eta, W, self.p), W


def run_frame(fr, convention, log):
    """convention = 'mult' : the side is built so that its MULTIPLICATIVE residual
                             is fr.residual;
       convention = 'digit': the side is built so that its COHERENT-DIGIT residual
                             ("twisted residual") is fr.residual."""
    p, e1, h, mu, kappa, s = fr.p, fr.e1, fr.h, fr.mu, fr.kappa, fr.s
    D, eta = fr.D, fr.eta
    checks = []

    # ---- vartheta: monomial computation vs T1 (C2-level-1) closed form
    thetas = []
    for t in range(mu + 1):
        vm, Wm = fr.vartheta(t)
        vc, Wc = fr.vartheta_closed(t)
        checks.append(("vartheta_%d monomial == T1 closed form" % t, (vm, Wm) == (vc, Wc)))
        thetas.append(vm)
    checks.append(("vartheta_0 = vartheta_1 = 1", thetas[0] == 1 % p and thetas[1] == 1 % p))

    # ---- build the coherent digits Gamma_j from the requested convention
    c = fr.residual                                   # length mu+1
    if convention == "mult":
        Gamma = [(c[j] * thetas[mu - j]) % p for j in range(mu + 1)]
        c_mult = [x % p for x in c]
    else:
        Gamma = [x % p for x in c]
        c_mult = [(c[j] * pow(thetas[mu - j], p - 2, p)) % p for j in range(mu + 1)]
    checks.append(("top coefficient normalised to 1", Gamma[mu] % p == 1 % p and c_mult[mu] % p == 1 % p))
    # dictionary consistency, both directions (T1 (C3-dictionary))
    checks.append(("C3-dictionary Gamma_j = c_j^mult * vartheta_{mu-j}",
                   all(Gamma[j] % p == (c_mult[j] * thetas[mu - j]) % p for j in range(mu + 1))))

    # ---- realise the side: A_j with dv(A_j(theta)) = (mu-j)kappa and digit Gamma_j
    A = []
    for j in range(mu):
        g = Gamma[j] % p
        if g == 0:
            A.append([])                              # pin strictly above the side
        else:
            A.append(pscal(Fraction(g), nhat((mu - j) * kappa, e1, h, p)))
    # f = Phi'^mu + sum_{j<mu} A_j Phi'^j   (C = 1: full-side genre, GENHN-1's convention)
    f = [Fraction(1)]
    for _ in range(mu):
        f = pmul(f, fr.Phi)
    for j in range(mu):
        if A[j]:
            term = A[j]
            for _ in range(j):
                term = pmul(term, fr.Phi)
            f = padd(f, term)

    # ---- sanity: the pins are where we put them, by BOTH the slot formula and the
    #      decorrelated resultant/norm leg; and the coherent digits read back
    for j in range(mu):
        if not A[j]:
            continue
        d1 = dv_of(A[j], e1, h, p)
        d2 = norm_dv(A[j], fr.Phi, e1, h, p, D)
        checks.append(("pin_%d slot-min = (mu-j)kappa" % j, d1 == (mu - j) * kappa))
        checks.append(("pin_%d GENHN-2 slot-min == e1*v(Res)/D'" % j, d1 == d2))
        checks.append(("pin_%d coherent digit reads back" % j,
                       coherent_digit(A[j], e1, h, p) == Gamma[j] % p))

    # ---- the recentering, done by ACTUAL re-division
    #      w := -lift(s; kappa) = -s_hat * n(kappa);  Phi'_new := Phi' + w
    w = pscal(Fraction(-(s % p)), nhat(kappa, e1, h, p))
    checks.append(("lift height dv(w) = kappa", dv_of(w, e1, h, p) == kappa))
    checks.append(("lift digit res(w/n(kappa)) = -s",
                   coherent_digit(w, e1, h, p) == (-s) % p))
    Phi_new = padd(fr.Phi, w)
    checks.append(("recentred key is monic of degree D'", len(Phi_new) - 1 == D and Phi_new[-1] == 1))
    Anew = development(f, Phi_new)
    # top coefficient must still be 1 at index mu
    checks.append(("development top index = mu", len(Anew) == mu + 1 and Anew[mu] == [Fraction(1)]))

    # ---- the PREDICTION (LEMMA WZ-A / COROLLARY WZ-A'): rho_k = [T^k] R_N(T + s)
    rho = shift_poly(c_mult, s % p, p)
    pred = []
    for k in range(mu):
        if rho[k] % p == 0:
            pred.append(("kill", None))
        else:
            pred.append(("survive", (rho[k] * thetas[mu - k]) % p))

    for k in range(mu):
        Ak = Anew[k] if k < len(Anew) else []
        d = dv_of(Ak, e1, h, p)
        dn = norm_dv(Ak, Phi_new, e1, h, p, D) if Ak else None
        checks.append(("new pin_%d slot-min == e1*v(Res)/D' (decorrelated)" % k, d == dn))
        kind, dig = pred[k]
        if kind == "kill":
            ok = (d is None) or (d > (mu - k) * kappa)
            checks.append(("pin_%d DIES  (rho_%d = 0)" % (k, k), ok))
        else:
            ok = (d == (mu - k) * kappa) and (coherent_digit(Ak, e1, h, p) == dig)
            checks.append(("pin_%d SURVIVES at height (mu-k)kappa with digit %s" % (k, dig), ok))

    all_killed = all(pred[k][0] == "kill" for k in range(mu))
    if fr.expect_all_kill is not None and convention == "mult":
        checks.append(("preregistered: multiplicative convention kills all pins",
                       all_killed == fr.expect_all_kill))

    n_bad = sum(1 for _, ok in checks if not ok)
    log.append("  [%s / %-5s] eta=%d  vartheta=%s  rho=%s  -> %d checks, %d violations%s"
               % (fr.name, convention, eta, thetas[:mu + 1], rho[:mu],
                  len(checks), n_bad, "   ALL PINS DIE" if all_killed else "   PINS SURVIVE"))
    for label, ok in checks:
        if not ok:
            log.append("      VIOLATION: " + label)
    return len(checks), n_bad, all_killed


def main():
    log = []
    frames = [
        # name, p, e1, h, z(eta), mu, kappa, s
        Frame("F1 live-wrap   ", 5, 2, 1, 2, 3, 3, 1, expect_all_kill=True),
        Frame("F2 eta=1 ctrl  ", 5, 2, 1, 1, 3, 3, 1, expect_all_kill=True),
        Frame("F3 i(kappa)=0  ", 5, 2, 1, 2, 3, 4, 1, expect_all_kill=True),
        Frame("F4 char|binom  ", 3, 2, 1, 2, 3, 3, 1, expect_all_kill=True),
        Frame("F5 e1=3        ", 7, 3, 1, 3, 3, 4, 2, expect_all_kill=True),
        Frame("F6 mu=4        ", 5, 2, 1, 2, 4, 3, 1, expect_all_kill=True),
        Frame("F7 h=3         ", 5, 2, 3, 2, 3, 7, 3, expect_all_kill=True),
        Frame("F8 wild p=2    ", 2, 2, 1, 1, 4, 3, 1, expect_all_kill=True),
        Frame("F9 e1=2 p=7    ", 7, 2, 1, 3, 3, 5, 4, expect_all_kill=True),
        # mu = 2 frames: the convention is ALREADY live at mu = 2 in odd
        # characteristic (F10) and provably dead at mu = 2 in char 2 (F11,
        # where every K-element is a square and the root re-parameterises) --
        # GENTOW5 S1.2's convention-consequence remark, tested one level down.
        Frame("F10 mu=2 odd   ", 5, 2, 1, 2, 2, 3, 1, expect_all_kill=True),
        Frame("F11 mu=2 char2 ", 2, 2, 1, 1, 2, 3, 1, expect_all_kill=True),
    ]

    total, bad = 0, 0
    sep_frames, nonsep_frames = [], []
    log.append("=== A. the substitution theorem, both conventions, by actual re-division ===")
    for fr in frames:
        t1, b1, kill_mult = run_frame(fr, "mult", log)
        t2, b2, kill_digit = run_frame(fr, "digit", log)
        total += t1 + t2
        bad += b1 + b2
        live = any(fr.vartheta(t)[0] != 1 % fr.p for t in range(fr.mu + 1))
        # the CONVENTION SEPARATION tooth: a digit-convention perfect power is a
        # multiplicative-convention perfect power iff the vartheta's in play are trivial
        sep = (kill_mult and not kill_digit)
        ok = (sep == live)
        total += 1
        if not ok:
            bad += 1
            log.append("      VIOLATION: convention separation != liveness of vartheta (%s)" % fr.name)
        (sep_frames if sep else nonsep_frames).append(fr.name.strip())

    log.append("")
    log.append("  conventions SEPARATE at: " + (", ".join(sep_frames) or "(none)"))
    log.append("  conventions AGREE at:    " + (", ".join(nonsep_frames) or "(none)"))

    # === B. negative control: a non-perfect-power residual is not an alpha event ===
    log.append("")
    log.append("=== B. negative control: residual (T-1)^2 (T-2), mu = 3, must NOT kill ===")
    fr = Frame("N1 not-a-power ", 5, 2, 1, 2, 3, 3, 1,
               residual=None)
    # build (T-1)^2 (T-2) mod 5
    a = power_linear(2, 1, 5) + [0]
    a = a[:3]
    prod = [0, 0, 0, 0]
    q = [(-2) % 5, 1]
    for i, x in enumerate(a):
        for j, y in enumerate(q):
            prod[i + j] = (prod[i + j] + x * y) % 5
    fr.residual = prod
    t, b, kill = run_frame(fr, "mult", log)
    total += t + 1
    bad += b
    if kill:
        bad += 1
        log.append("      VIOLATION: non-perfect-power residual killed all pins")

    # === C. the closed form for vartheta over a sweep ===
    log.append("")
    log.append("=== C. vartheta_t = eta^{floor(t*i(kappa)/e1)} over a sweep ===")
    n_c = 0
    for p, e1, h in itertools.product([2, 3, 5, 7], [1, 2, 3, 4], [1, 2, 3, 5]):
        from math import gcd
        if gcd(h, e1) != 1:
            continue
        for z in range(1, p):
            fr = Frame("sweep", p, e1, h, z, 4, 0, 1)
            for kappa in range(e1 * h + 1, e1 * h + 12):
                fr.kappa = kappa
                for t in range(5):
                    vm, Wm = fr.vartheta(t)
                    vc, Wc = fr.vartheta_closed(t)
                    n_c += 1
                    if (vm, Wm) != (vc, Wc):
                        bad += 1
                        log.append("      VIOLATION: sweep p=%d e1=%d h=%d z=%d kappa=%d t=%d"
                                   % (p, e1, h, z, kappa, t))
    total += n_c
    log.append("  %d sweep checks" % n_c)

    log.append("")
    log.append("TOTAL: %d checks, %d violations" % (total, bad))
    print("\n".join(log))
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
