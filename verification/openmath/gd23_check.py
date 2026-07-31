#!/usr/bin/env python3
"""GD23 falsifier harness — the GD-2/GD-3 dictionary unit over an arbitrary
complete DVR, tested at the NEW perimeter beyond T-E/T-F:

  * root keys of degree d0 = 2 (T-E/T-F only ever ran d0 = 1), and
  * an EQUAL-CHARACTERISTIC base ring O = F_p[[t]] alongside Z_p
    (the arbitrary-DVR claim of the unit; D-3 kill).

Checks, per sampled monic f realizing a root read at a degree-2 root key:
  (GAUSS-g) w0 computed from the Phi0-development == plain Gauss valuation;
  (VAL-g)   w1(AB) = w1(A) + w1(B) on random pairs (order-1
            multiplicativity of the augmented valuation, d0 = 2);
  (KEY-g)   the standard lift Phi1 = sum_k psihat_k pi^{(g-k)h} Phi0^{ek}
            is monic of degree e*g*d0, every nonzero monomial of w1-weight
            exactly e*g*h, and w1(Phi1) = e*g*h;
  (A-law)   w1(f) = e*u0 + s0*h (WGEO(a): the parent read displays w(f));
  (DEVID)   min_k ( w1(C_k) + k*e*g*h ) over the Phi1-development of f
            equals w1(f)  (the development identity (V2b) at the child);
  (MINCORE) the FIRST attainment of that min is at k = mu = ord_psi(R_lambda(f))
            (the residual dictionary (V2c) = GD-3 min core, via WGEO(b)'s
            displayed consequence).

Residuals are computed over F1 = F_p[X]/(phibar) = F_{p^2} with GMN's (L3)
order-1 coefficients (class of b_{s+ke}/pi^{u0-kh} on-line, 0 above), and
factored completely over F_{p^2} (degree-1/2 trial division; a remainder with
no factor of degree <= 2 is irreducible).

Exact arithmetic throughout. Any single violation is a refutation of the
corresponding GD23 claim at this perimeter.
"""
import random, json, sys, math

random.seed(20260731)

# ---------------- coefficient rings: O = Z_p ("Zp") or F_p[[t]] ("Fpt") ----
INF = 10**9

def mk_ring(kind, p):
    if kind == "Zp":
        return dict(kind=kind, p=p,
            zero=0, one=1,
            add=lambda a,b: a+b, neg=lambda a: -a, mul=lambda a,b: a*b,
            isz=lambda a: a == 0,
            val=lambda a: INF if a == 0 else _vp(a, p),
            divpi=lambda a,k: a // (p**k),          # exact when val>=k
            pi_pow=lambda k: p**k,
            res=lambda a: a % p)                    # residue in F_p
    else:  # Fpt: elements are tuples of F_p digits (coeff of t^i)
        def norm(t):
            t = list(t)
            while t and t[-1] % p == 0 and all(x % p == 0 for x in t[len(t)-1:]):
                if t[-1] % p == 0: t.pop()
                else: break
            return tuple(x % p for x in t)
        def add(a,b):
            n = max(len(a), len(b))
            return norm([ (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n) ])
        def mul(a,b):
            if not a or not b: return ()
            out = [0]*(len(a)+len(b)-1)
            for i,x in enumerate(a):
                if x % p == 0: continue
                for j,y in enumerate(b):
                    out[i+j] += x*y
            return norm(out)
        return dict(kind=kind, p=p,
            zero=(), one=(1,),
            add=add, neg=lambda a: tuple((-x) % p for x in a), mul=mul,
            isz=lambda a: len(norm(a)) == 0,
            val=lambda a: INF if not norm(a) else min(i for i,x in enumerate(a) if x % p != 0),
            divpi=lambda a,k: tuple(a[k:]),
            pi_pow=lambda k: tuple([0]*k + [1]),
            res=lambda a: (a[0] % p) if a else 0)

def _vp(n, p):
    v = 0; n = abs(n)
    while n % p == 0: n //= p; v += 1
    return v

# ---------------- O[x] polynomials: lists of ring elements ----------------
def pnorm(R, A):
    A = list(A)
    while A and R["isz"](A[-1]): A.pop()
    return A
def padd(R, A, B):
    n = max(len(A), len(B))
    return pnorm(R, [ R["add"](A[i] if i < len(A) else R["zero"],
                               B[i] if i < len(B) else R["zero"]) for i in range(n) ])
def pneg(R, A): return [R["neg"](a) for a in A]
def pmul(R, A, B):
    if not A or not B: return []
    out = [R["zero"]]*(len(A)+len(B)-1)
    for i,a in enumerate(A):
        if R["isz"](a): continue
        for j,b in enumerate(B):
            out[i+j] = R["add"](out[i+j], R["mul"](a,b))
    return pnorm(R, out)
def pscal(R, c, A): return pnorm(R, [R["mul"](c,a) for a in A])
def pdivmod(R, A, B):
    # B monic (leading coeff == one). Returns (Q, Rm).
    A = list(A); Q = []
    dB = len(B)-1
    Qc = {}
    while len(A)-1 >= dB and A:
        d = len(A)-1
        c = A[-1]
        Qc[d-dB] = c
        # A -= c * x^(d-dB) * B
        for j,b in enumerate(B):
            idx = d-dB+j
            A[idx] = R["add"](A[idx], R["neg"](R["mul"](c,b)))
        A = pnorm(R, A)
        if len(A)-1 < dB: break
    Qd = max(Qc) if Qc else -1
    Q = [ Qc.get(i, R["zero"]) for i in range(Qd+1) ]
    return pnorm(R,Q), pnorm(R,A)
def dev(R, A, Phi):
    """Phi-adic development: list of coefficient polys (deg < deg Phi)."""
    out = []
    while A:
        Q, rem = pdivmod(R, A, Phi)
        out.append(rem)
        A = Q
    return out
def w0(R, A):
    """Gauss valuation = min coefficient valuation."""
    if not A: return INF
    return min(R["val"](a) for a in A)
def w0_via_dev(R, A, Phi):
    if not A: return INF
    return min((w0(R, b) for b in dev(R, A, Phi)), default=INF)
def w1(R, A, Phi0, e, h):
    if not A: return INF
    return min(e*w0(R,b) + t*h for t,b in enumerate(dev(R, A, Phi0)) if b)

# ---------------- F1 = F_p[X]/(phibar), phibar monic deg 2 ----------------
def f1_make(p, phibar):  # phibar: list of 3 ints, monic
    a0, a1 = phibar[0] % p, phibar[1] % p
    def mul(u, v):
        c0 = u[0]*v[0]; c1 = u[0]*v[1] + u[1]*v[0]; c2 = u[1]*v[1]
        # reduce X^2 = -a1 X - a0
        return ((c0 - c2*a0) % p, (c1 - c2*a1) % p)
    return dict(p=p, zero=(0,0), one=(1,0), mul=mul,
                add=lambda u,v: ((u[0]+v[0]) % p, (u[1]+v[1]) % p),
                neg=lambda u: ((-u[0]) % p, (-u[1]) % p),
                isz=lambda u: u[0] % p == 0 and u[1] % p == 0,
                elts=[(i,j) for i in range(p) for j in range(p)])
def f1_class(R, F1, b):
    """class of b in F1, b an O[x]-poly of degree < 2 (residues of coeffs)."""
    c0 = R["res"](b[0]) if len(b) > 0 else 0
    c1 = R["res"](b[1]) if len(b) > 1 else 0
    return (c0 % F1["p"], c1 % F1["p"])
# F1[z] polynomials: lists of F1 elements
def f1p_norm(F1, A):
    A = list(A)
    while A and F1["isz"](A[-1]): A.pop()
    return A
def f1p_divmod(F1, A, B):  # B monic
    A = list(A); dB = len(B)-1; Qc = {}
    while len(A)-1 >= dB and A:
        d = len(A)-1; c = A[-1]; Qc[d-dB] = c
        for j,b in enumerate(B):
            A[d-dB+j] = F1["add"](A[d-dB+j], F1["neg"](F1["mul"](c,b)))
        A = f1p_norm(F1, A)
    Qd = max(Qc) if Qc else -1
    return [Qc.get(i, F1["zero"]) for i in range(Qd+1)], f1p_norm(F1, A)
def f1p_ord(F1, A, psi):
    mu = 0
    while A:
        Q, rem = f1p_divmod(F1, A, psi)
        if rem: break
        mu += 1; A = f1p_norm(F1, Q)
    return mu
def f1_irreducibles(F1, maxdeg):
    """monic irreducibles over F1 of degree <= maxdeg (maxdeg <= 2)."""
    out = []
    for c in F1["elts"]:
        out.append([F1["neg"](c), F1["one"]])           # z - c... (z + (-c))
    if maxdeg >= 2:
        for a in F1["elts"]:
            for b in F1["elts"]:
                q = [b, a, F1["one"]]
                # irreducible iff no root in F1
                if all(not F1["isz"](F1["add"](F1["add"](F1["mul"](F1["mul"](r,r),F1["one"]),
                        F1["mul"](a,r)), b)) for r in F1["elts"]):
                    out.append(q)
    return out
def f1p_factor(F1, A, irrs):
    """complete factorization using irreducibles of deg <= 2; a remainder of
    degree >= 3 with no small factor is itself irreducible."""
    A = f1p_norm(F1, A); fac = []
    for psi in irrs:
        mu = f1p_ord(F1, A, psi)
        if mu > 0:
            fac.append((psi, mu))
            for _ in range(mu):
                A, _r = f1p_divmod(F1, A, psi)
    if len(A)-1 >= 1:
        # normalize monic
        lead = A[-1]
        # find inverse of lead by scan
        inv = next(u for u in F1["elts"] if F1["mul"](u, lead) == F1["one"])
        fac.append(([F1["mul"](inv, c) for c in A], 1))
    return fac

# ---------------- lower hull of window points ------------------------------
def lower_hull(pts):
    pts = sorted(pts)
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1,y1),(x2,y2) = hull[-2], hull[-1]
            if (y2-y1)*(pt[0]-x1) >= (pt[1]-y1)*(x2-x1): hull.pop()
            else: break
        hull.append(pt)
    return hull

# ---------------- sample builders ------------------------------------------
def rand_coeffpoly(R, unit=True):
    """random O[x]-poly of degree <= 1 with nonzero class mod (pi, Phi0)."""
    p = R["p"]
    while True:
        if R["kind"] == "Zp":
            c0 = random.randrange(-3*p, 3*p+1); c1 = random.randrange(-3*p, 3*p+1)
            b = pnorm(R, [c0, c1])
        else:
            c0 = tuple(random.randrange(p) for _ in range(random.randrange(1,3)))
            c1 = tuple(random.randrange(p) for _ in range(random.randrange(1,3)))
            b = pnorm(R, [c0, c1])
        if not unit: return b
        if b and (R["res"](b[0]) % p != 0 or (len(b) > 1 and R["res"](b[1]) % p != 0)):
            return b

def rand_opoly(R, maxdeg):
    """random O[x]-poly, coefficients with random pi-powers."""
    out = []
    for i in range(maxdeg+1):
        if random.random() < 0.25: out.append(R["zero"]); continue
        a = random.randrange(0, 4)
        u = rand_coeffpoly(R, unit=True)[0]
        out.append(R["mul"](R["pi_pow"](a), u))
    return pnorm(R, out)

def build_f(R, Phi0, m):
    """f = sum b_j Phi0^j in developed form; b_m unit-class; b_j (j<m)
    pi-divisible with exact valuation; a couple of beyond-window slots."""
    slots = {}
    slots[m] = rand_coeffpoly(R, unit=True)
    a0 = random.randrange(1, 6)
    slots[0] = pscal(R, R["pi_pow"](a0), rand_coeffpoly(R, unit=True))
    for j in range(1, m):
        r = random.random()
        if r < 0.35: continue
        aj = random.randrange(1, 6)
        slots[j] = pscal(R, R["pi_pow"](aj), rand_coeffpoly(R, unit=True))
    for j in range(m+1, m+3):
        if random.random() < 0.5:
            aj = random.randrange(0, 3)
            slots[j] = pscal(R, R["pi_pow"](aj), rand_coeffpoly(R, unit=True))
    f = []
    for j, b in slots.items():
        f = padd(R, f, pmul(R, b, ppow(R, Phi0, j)))
    return f, slots

def ppow(R, A, k):
    out = [R["one"]]
    for _ in range(k): out = pmul(R, out, A)
    return out

def std_lift(R, F1, psi, e, h, Phi0):
    """standard key lift Phi1 = sum_k psihat_k pi^{(g-k)h} Phi0^{ek}."""
    g = len(psi)-1
    Phi1 = []
    terms = []
    for k, c in enumerate(psi):
        if F1["isz"](c): continue
        lift = pnorm(R, [_lift_scalar(R, c[0]), _lift_scalar(R, c[1])])
        term = pscal(R, R["pi_pow"]((g-k)*h), pmul(R, lift, ppow(R, Phi0, e*k)))
        terms.append(term)
        Phi1 = padd(R, Phi1, term)
    return Phi1, terms, g

def _lift_scalar(R, c):
    if R["kind"] == "Zp": return c
    return (c % R["p"],) if c % R["p"] else ()

# ---------------- the test battery -----------------------------------------
def run_config(kind, p, phibar, n_f, n_mult, stats):
    R = mk_ring(kind, p)
    F1 = f1_make(p, phibar)
    irrs = f1_irreducibles(F1, 2)
    if kind == "Zp":
        Phi0 = pnorm(R, [phibar[0], phibar[1], 1])
    else:
        # a lift with genuine t-noise: Phi0 = X^2 + (phibar1 + t)X + phibar0
        Phi0 = pnorm(R, [ (phibar[0] % p,), (phibar[1] % p, 1), (1,) ])
    sides_pool = [(1,1),(1,2),(2,1),(3,2),(2,3)]
    # --- Test 1: VAL-g multiplicativity + GAUSS-g agreement ---
    for _ in range(n_mult):
        e, h = random.choice(sides_pool)
        A = rand_opoly(R, random.randrange(1, 7))
        B = rand_opoly(R, random.randrange(1, 7))
        if not A or not B: continue
        assert w0_via_dev(R, A, Phi0) == w0(R, A), ("GAUSS-g", kind, p, A)
        wa, wb = w1(R, A, Phi0, e, h), w1(R, B, Phi0, e, h)
        wab = w1(R, pmul(R, A, B), Phi0, e, h)
        if wab != wa + wb:
            stats["violations"].append(("VAL-g", kind, p, e, h, A, B, wa, wb, wab))
        stats["n_val"] += 1
    # --- Tests 2-6: per sampled root read ---
    for _ in range(n_f):
        m = random.randrange(2, 5)
        f, slots = build_f(R, Phi0, m)
        devf = dev(R, f, Phi0)
        pts = [(j, w0(R, b)) for j, b in enumerate(devf) if b and j <= m]
        if len(pts) < 2: continue
        hull = lower_hull(pts)
        faces = [(hull[i], hull[i+1]) for i in range(len(hull)-1)
                 if hull[i+1][1] < hull[i][1]]
        for (j1,v1),(j2,v2) in faces:
            gcdv = math.gcd(j2-j1, v1-v2)
            e, h = (j2-j1)//gcdv, (v1-v2)//gcdv
            d = (j2-j1)//e
            s0, u0 = j1, v1
            # residual R(z) over F1: on-line classes at strides
            Rz = []
            for kk in range(d+1):
                j = s0 + kk*e
                ell = u0 - kk*h
                b = devf[j] if j < len(devf) else []
                if b and w0(R, b) == ell:
                    bb = pnorm(R, [R["divpi"](c, ell) for c in b])
                    Rz.append(f1_class(R, F1, bb))
                else:
                    if b and w0(R, b) < ell:
                        stats["violations"].append(("HULL", kind, p, f)); continue
                    Rz.append(F1["zero"])
            if F1["isz"](Rz[0]) or F1["isz"](Rz[-1]):
                stats["violations"].append(("R-ENDS", kind, p, f, (e,h,d,s0,u0)))
                continue
            wf = w1(R, f, Phi0, e, h)
            if wf != e*u0 + s0*h:
                stats["violations"].append(("A-LAW", kind, p, f, (e,h,s0,u0), wf))
            stats["n_alaw"] += 1
            for psi, mu in f1p_factor(F1, Rz, irrs):
                g = len(psi)-1
                if g > 2:  # standard lift built only for deg<=2 psi coeffs: fine, psi coeffs are F1-elts any g
                    pass
                Phi1, terms, g = std_lift(R, F1, psi, e, h, Phi0)
                # KEY-g: monic of degree e*g*2; each monomial weight e*g*h
                if len(Phi1)-1 != e*g*2 or not _is_one(R, Phi1[-1]):
                    stats["violations"].append(("KEY-deg", kind, p, psi, (e,h)))
                for term in terms:
                    if w1(R, term, Phi0, e, h) != e*g*h:
                        stats["violations"].append(("KEY-hom", kind, p, psi, (e,h), term))
                if w1(R, Phi1, Phi0, e, h) != e*g*h:
                    stats["violations"].append(("KEY-w", kind, p, psi, (e,h)))
                stats["n_key"] += 1
                # DEVID + MINCORE at the child
                gamma_hat = e*g*h
                C = dev(R, f, Phi1)
                us = [ (w1(R, ck, Phi0, e, h) + k*gamma_hat) for k, ck in enumerate(C) ]
                finite = [(u,k) for k,u in enumerate(us) if u < INF]
                umin = min(u for u,_ in finite)
                kfirst = min(k for u,k in finite if u == umin)
                if umin != wf:
                    stats["violations"].append(("DEVID", kind, p, f, (e,h), psi, umin, wf))
                if kfirst != mu:
                    stats["violations"].append(("MINCORE", kind, p, f, (e,h), psi, mu, kfirst))
                stats["n_dev"] += 1

def _is_one(R, c):
    return (not R["isz"](c)) and R["isz"](R["add"](c, R["neg"](R["one"])))

def main():
    stats = dict(n_val=0, n_alaw=0, n_key=0, n_dev=0, violations=[])
    configs = [
        ("Zp", 2, [1,1,1]),   # phibar = X^2+X+1 irred over F_2
        ("Zp", 3, [1,0,1]),   # X^2+1 irred over F_3
        ("Fpt", 2, [1,1,1]),  # O = F_2[[t]]
        ("Fpt", 3, [1,0,1]),  # O = F_3[[t]]
    ]
    for kind, p, phibar in configs:
        run_config(kind, p, phibar, n_f=400, n_mult=700, stats=stats)
        print(f"config ({kind}, p={p}): cumulative "
              f"val={stats['n_val']} alaw={stats['n_alaw']} key={stats['n_key']} "
              f"dev={stats['n_dev']} violations={len(stats['violations'])}")
    print()
    if stats["violations"]:
        print("VIOLATIONS FOUND:")
        for v in stats["violations"][:20]:
            print("  ", v)
        sys.exit(1)
    print(f"ALL PASS: VAL-g {stats['n_val']} | A-law {stats['n_alaw']} | "
          f"KEY-g {stats['n_key']} | DEVID+MINCORE {stats['n_dev']} | 0 violations")

if __name__ == "__main__":
    main()
