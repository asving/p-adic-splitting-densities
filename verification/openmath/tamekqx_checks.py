#!/usr/bin/env python3
"""TAMEKQX battery (sealed at commit 1; scoring run -> tamekqx_results.json at commit 2).

Unit TAMEK-QX (Asvin 2026-08-09): retire archimedean/MC evidence for the unramified-K
moments in favor of EXACT rational identities. Everything symbolic (sympy), NO Monte
Carlo in this battery.

TIER 1 (P1-P3): for K unramified of degree f in {2,3} over F (residue size q),
E[X_K^k](n) for k=1..4, n=2..5, computed two independent ways:
  (a) MENU route: certified factorization-type menus (TK-Q n=2; HMENU3 HM3.D n=3;
      GENH4 Rtau n=4; BCFGTIE quintic_densities n=5) weighted by X_K(tau)^k,
      X_K(tau) = sum of f' over parts (1,f') with f' | f  [LEMMA TKQX-0];
  (b) RECURSION route: the MOMENTS PGF master identity generalized over the divisor
      lattice (TAMEK S5, unramified case), consuming ONLY the deep-count law P_m(j)
      + level-0 independence -- no menu, no engine.
TIER 2 (P4-P5): the Kac-Rice configuration-count legs (independent of BOTH routes):
  E[X_K](n) for f=2 at n=2, n=3, n>=4 by the collision-codimension-graded integral,
  tied to TK-Q, the S3 dip anchor, and the S4.R closed form; plus the 1/q-expansion
  protocol demonstration (truncated strata to determining depth).
TEETH (P6): T1 wrong-weight (drop f'|f), T2 wrong-menu-row (swap two n=3 rows),
  T3 block-drop (recursion without its delta=f block). All must bite.

Disclosure [proto]: the Tier-2 closed forms were scratch-derived pre-seal; the first
derivation had an Abel-summation bug (J(w) formula), caught by an independent exact
root-counter diagnostic (MC, development scaffolding only, NOT part of this battery)
and fixed before sealing. Tier-1 cells were never evaluated before the scoring run.
SMOKE RECORD (pre-seal, disclosed): the recursion code was smoke-tested at k=1 ONLY,
numeric q=3 ONLY, against the COMMITTED mean recursion tamek_unram_exact.E_mean
(f=2 n=2..5 and f=3 n=2..4 all equal, incl. 852/605), plus the f=1 symbolic F_2
sanity (surfaced the binomial(q,2) expand_func fix, pre-seal repair, non-predicate).
No k>=2 value, no symbolic f>=2 value, and no menu-vs-recursion comparison was
computed before sealing.
ARC INTEGRITY (run 1 aborted, disclosed): the first scoring run FAILed P2 at n>=4
with byte-identical menu/recursion displays -- an INSTRUMENT defect, not a math
mismatch: sympify of the JSON menus created a plain Symbol('q') distinct from the
module's positive Symbol('q'), so the difference could not cancel. Repair = bind
sympify locals to the module symbol (one line, manifestly non-predicate; no
predicate, weight, menu row, or recursion coefficient touched). Run 2 is the
scoring run; run-1 log kept as tamekqx_run1_aborted.log.
ARC INTEGRITY (run 2 completed exit 1, log tamekqx_run2.log, disclosed): 37/47
PASS. ALL 24 n<=4 identity cells EQUAL (both f, all k) + P3 both rows + all 3
teeth. The 10 FAILs decompose into three INSTRUMENT errors, repaired as r2a/r2b/
r2c (tagged at their sites): r2a -- the 8 n=5 cells compared the committed
QUINTIC menu (PROJECTIVE model; its K=F mean is exactly 1, machine-verified)
against the MONIC recursion: model-key error in menu consumption; n=5 now runs
projective-vs-projective via proj_pgf (+ new sanity gate R-sanity-proj). r2b --
P4's sealed closed form had piece2 exponent q^{-4} for q^{-2} (transcription slip
vs the [proto] scratch record). r2c -- P5-KR-n3's sealed TARGET was the
ramified-quad dip anchor 1-Phi6/Phi5 pasted in error for the unramified-quad n=3
anchor. No menu row, recursion coefficient, P_mj, or tooth was touched. Run 3 =
the scoring run for the repaired rows; the 24 clean n<=4 cells stand from run 2
and must reproduce.
"""
import json, os, sys, time, ast
sys.setrecursionlimit(10000)
import sympy as sp

q = sp.symbols('q', positive=True)
t = sp.symbols('t')
HERE = os.path.dirname(os.path.abspath(__file__))
T0 = time.time()
RESULTS = {"unit": "TAMEKQX", "checks": [], "fails": 0, "teeth": []}
LOG = []

def log(msg):
    line = "[%7.1fs] %s" % (time.time() - T0, msg)
    print(line, flush=True)
    LOG.append(line)

def check(name, ok, detail=""):
    RESULTS["checks"].append({"name": name, "ok": bool(ok), "detail": str(detail)[:400]})
    if not ok:
        RESULTS["fails"] += 1
    log("%s  %s  %s" % ("PASS" if ok else "FAIL", name, detail))

def is_zero(expr):
    return sp.simplify(sp.together(sp.cancel(sp.expand_func(expr)))) == 0

# ---------------------------------------------------------------------------
# Shared primitive: the deep-count law P_m(j) (BCFGTIE Lemma C closed form,
# independently re-derived in MOMENTS C1). Q is a sympy expression (q, q^2, ...).
# ---------------------------------------------------------------------------
def P_mj(Q, m, j):
    if m == 0: return sp.Integer(1) if j == 0 else sp.Integer(0)
    if m == 1: return sp.Integer(1) if j == 1 else sp.Integer(0)
    if j == m: return Q**sp.Integer(-(m*(m-1)//2))
    if j > m or j < 0 or j == m - 1: return sp.Integer(0)
    tot = sp.Integer(0)
    for mu in range(j+1, m):
        E = (mu-j-1) + j*(mu-1) - j*(j-1)//2 + (mu-1-j)*(mu-j)//2
        tot += (1 - 1/Q) * Q**(-E)
    return sp.together(tot)

def n_points(Q, d):
    """# closed points of degree d on A^1 over F_Q (symbolic)."""
    from sympy import divisors, mobius
    return sp.together(sum(sp.mobius(d//e) * Q**e for e in sp.divisors(d)) / d)

# ---------------------------------------------------------------------------
# t-polynomial helpers: represent F_n(t) as list of q-rational coeffs, index = t-power
# ---------------------------------------------------------------------------
def padd(a, b):
    n = max(len(a), len(b))
    return [ (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n) ]

def pscal(s, a):
    return [sp.cancel(s * c) for c in a]

def pmul(a, b):
    out = [sp.Integer(0)] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca == 0: continue
        for j, cb in enumerate(b):
            if cb == 0: continue
            out[i+j] += ca * cb
    return [sp.cancel(c) for c in out]

def pspread(a, d):
    """t -> t^d on a t-poly."""
    out = [sp.Integer(0)] * ((len(a)-1)*d + 1)
    for i, c in enumerate(a):
        out[i*d] = c
    return out

ZERO_P = [sp.Integer(0)]
ONE_P = [sp.Integer(1)]

# u-series with t-poly coefficients: list (index = u-power) of t-polys
def smul(A, B, N):
    out = [[sp.Integer(0)] for _ in range(N+1)]
    for i, pa in enumerate(A):
        if i > N: break
        for j, pb in enumerate(B):
            if i + j > N: break
            out[i+j] = padd(out[i+j], pmul(pa, pb))
    return [[sp.cancel(c) for c in p] for p in out]

# ---------------------------------------------------------------------------
# RECURSION ROUTE: F^{(f)}_n(t; Q) via the divisor-lattice master identity
#   sum_n F_n u^n = (1/(1-u)) prod_{d|f} [ (1-(u/Q)^d) W_d((u/Q)^d, t) ]^{N_d(Q)}
#   W_d(v,t) = sum_m phi^{(f/d)}_m(t^d; Q^d) v^m,  phi = sum_j P_m(j) F_j
# Self-loop (delta=1, m=n) solved linearly by the two-run trick.
# ---------------------------------------------------------------------------
_FVEC_MEMO = {}

def Fvec(f, Q, N, drop_top_block=False):
    key = (f, sp.srepr(Q), N, drop_top_block)
    if key in _FVEC_MEMO:
        return _FVEC_MEMO[key]
    F = [ONE_P[:], [sp.Integer(0), sp.Integer(1)]]  # F_0 = 1, F_1 = t
    for n in range(2, N+1):
        A0 = _master_coeff(f, Q, F + [ZERO_P[:]], n, drop_top_block)
        A1 = _master_coeff(f, Q, F + [ONE_P[:]], n, drop_top_block)
        diff = padd(A1, pscal(-1, A0))
        csel = sp.cancel(diff[0])
        assert all(sp.cancel(c) == 0 for c in diff[1:]), "self-coefficient not scalar"
        Fn = pscal(sp.cancel(1/(1 - csel)), A0)
        F.append(Fn)
    _FVEC_MEMO[key] = F
    return F

def _master_coeff(f, Q, Flist, n, drop_top_block):
    """[u^n] of the master RHS given Flist (length n+1, unknown slot filled)."""
    prod = [ONE_P[:]] + [[sp.Integer(0)] for _ in range(n)]
    divs = [d for d in range(1, f+1) if f % d == 0]
    if drop_top_block and f > 1:
        divs = [d for d in divs if d != f]
    for d in divs:
        sub_f, Qd = f // d, sp.together(Q**d)
        if d == 1:
            subF = Flist
        else:
            subF = Fvec(sub_f, Qd, n // d)
        # phi_m(t^d; Q^d) for m = 0..n//d
        phis = []
        for m in range(0, n//d + 1):
            ph = [sp.Integer(0)]
            for j in range(0, m+1):
                pm = P_mj(Qd, m, j)
                if pm != 0:
                    ph = padd(ph, pscal(pm, subF[j]))
            phis.append(pspread(ph, d))
        # Z(u) = (1 - (u/Q)^d) * W_d((u/Q)^d) - 1, as u-series to order n
        W = [[sp.Integer(0)] for _ in range(n+1)]
        for m, ph in enumerate(phis):
            if m*d <= n:
                W[m*d] = pscal(Q**(-m*d), ph)
        onemv = [[sp.Integer(1)]] + [[sp.Integer(0)] for _ in range(n)]
        if d <= n:
            onemv[d] = [-Q**(-d)]
        Z = smul(onemv, W, n)
        Z[0] = padd(Z[0], [sp.Integer(-1)])
        # B_d = sum_j binom(N_d, j) Z^j
        Nd = n_points(Q, d)
        B = [ONE_P[:]] + [[sp.Integer(0)] for _ in range(n)]
        Zp = [ONE_P[:]] + [[sp.Integer(0)] for _ in range(n)]
        for jj in range(1, n//d + 1):
            Zp = smul(Zp, Z, n)
            coef = sp.cancel(sp.expand_func(sp.binomial(Nd, jj)))
            B = [padd(B[i], pscal(coef, Zp[i])) for i in range(n+1)]
        prod = smul(prod, B, n)
    # multiply by 1/(1-u): cumulative sum, take [u^n]
    acc = [sp.Integer(0)]
    for i in range(n+1):
        acc = padd(acc, prod[i])
    return [sp.cancel(c) for c in acc]

def moments_from_pgf(Fn, kmax):
    """E[X^k] for k=1..kmax from a t-poly law."""
    return [sp.cancel(sum((sp.Integer(r)**k) * c for r, c in enumerate(Fn))) for k in range(1, kmax+1)]

def proj_pgf(f, n):
    """PROJECTIVE-model law F^p_n(t) for X_K over P^1 (uniform degree-n divisor):
    b_n F^p_n = sum_j q^{n-j} F_{n-j} phi_j  (MOMENTS Cor 2.2 generalized: the
    infinity point of P^1 is one more RATIONAL residue point, its cluster the
    delta=1 species phi^{(f)}_j at the same (f, q) context).
    [run-2 repair r2a: the committed quintic menu is the PROJECTIVE model (its
    K=F mean is exactly 1, verified); the sealed P2 n=5 cells compared it against
    the MONIC recursion -- a model-key transcription error in menu CONSUMPTION,
    not a defect of either source. n=5 comparisons now run projective-vs-projective.]"""
    F = Fvec(f, q, n)
    acc = [sp.Integer(0)]
    for j in range(0, n+1):
        phi_j = [sp.Integer(0)]
        for i in range(0, j+1):
            pm = P_mj(q, j, i)
            if pm != 0:
                phi_j = padd(phi_j, pscal(pm, F[i]))
        acc = padd(acc, pscal(q**(n-j), pmul(F[n-j], phi_j)))
    bn = sp.cancel((q**(n+1) - 1)/(q - 1))
    return pscal(sp.cancel(1/bn), acc)

# ---------------------------------------------------------------------------
# MENU ROUTE: certified factorization-type menus, grades disclosed in the note
# ---------------------------------------------------------------------------
def menu_n2():
    # THEOREM TK-Q (TAMEK S3): three quadratic types, monic model.
    return {((1,1),(1,1)): q/(2*(q+1)), ((1,2),): q/(2*(q+1)), ((2,1),): 1/(q+1)}

def menu_n3():
    # COROLLARY HM3.D (HMENU3, ACCEPTED 2/2), Phi := Phi_5.
    Phi = q**4+q**3+q**2+q+1
    return {((1,1),(1,1),(1,1)): q**3*(q**2-q+1)/(6*(q+1)*Phi),
            ((1,1),(1,2)):       q**3*(q**2+q+1)/(2*(q+1)*Phi),
            ((1,3),):            q**3*(q+1)/(3*Phi),
            ((1,1),(2,1)):       q*(q**3+q+1)/((q+1)*Phi),
            ((3,1),):            (q**2+1)/Phi}

def _load_json_menu(fname, key):
    with open(os.path.join(HERE, fname)) as fh:
        raw = json.load(fh)[key]
    out = {}
    for kk, vv in raw.items():
        tau = tuple(tuple(x) for x in ast.literal_eval(kk))
        out[tau] = sp.sympify(vv, locals={"q": q})  # bind to THIS module's q symbol
    return out

def X_K(tau, f):
    return sum(fp for (e, fp) in tau if e == 1 and f % fp == 0)

def X_K_bad(tau, f):   # tooth T1: divisibility dropped
    return sum(fp for (e, fp) in tau if e == 1)

def menu_moment(menu, f, k, Xfun=X_K):
    return sp.cancel(sum(R * sp.Integer(Xfun(tau, f))**k for tau, R in menu.items()))

# ---------------------------------------------------------------------------
# TIER 2: Kac-Rice configuration-count legs (f = 2), independent of both routes.
# E[X_F](n>=2) = q/(q+1)  [one-line KR over O: density 1 x E|h(z)|, h(z) Haar]
# E_quad(n) = (1-1/q) sum_w q^{-2w} J_n(w), w = v(y) the conjugate-collision depth:
#   delta-density q^w ([O_K:O[z]]) x |z-zbar|_K = q^{-2w} x J_n(w) = E|h(z)|_K,
#   h = f/m_z Haar monic deg n-2, h(z) uniform on O[z] for n >= 4.
#   J_n(w) = E[q^{-2 min(A, w+B)}] (n>=4, A,B iid geometric-valuation);
#   J_3(w) = E[q^{-2 min(A, w)}]; J_2(w) = 1.
# Abel: E[t^M] = 1 - (1-t) sum_{m>=1} t^{m-1} P(M >= m).
# ---------------------------------------------------------------------------
def geo(r, start=0):
    return r**start / (1 - r)

def J4_closed(w):
    tt = q**-2
    piece1 = (q**-1) * (1 - (tt/q)**w) / (1 - tt/q)          # sum_{m=1..w} t^{m-1} q^{-m}
    piece2 = q**w * tt**w * q**(-2*(w+1)) / (1 - tt*q**-2)   # sum_{m>w} t^{m-1} q^{w-2m}
    return 1 - (1 - tt)*(piece1 + piece2)

def E_quad_n4_closed():
    # sum_w q^{-2w} J4(w) assembled from geometric pieces (t := q^-2):
    #   J4(w) = 1 - (1-t)[ q^{-1}(1-q^{-3w})/(1-q^{-3}) + q^{-3w} q^{-2}/(1-q^{-4}) ]
    # [run-2 repair r2b: piece2 = q^w t^w q^{-2(w+1)}/(1-t q^{-2}) = q^{-3w} q^{-2}/(1-q^{-4});
    #  the sealed form had q^{-4}, a transcription slip vs the [proto] scratch record
    #  (J(0)=q^2/(q^2+1), J(1)=0.6999 at q=3, assembly 1.408256 = 852/605).]
    tt = q**-2
    c1 = (1-tt)*q**-1/(1-q**-3)
    c2 = (1-tt)*q**-2/(1-q**-4)
    S = geo(q**-2)*(1 - c1) + c1*geo(q**-5) - c2*geo(q**-5)
    return sp.cancel((1 - 1/q) * S)

def E_quad_n3_closed():
    # J3(w) = E[q^{-2 min(A,w)}] = 1 - (1-t)[ q^{-1}(1-q^{-3w})/(1-q^{-3}) ]  truncated at m<=w
    #       = sum_{a<w} (1-1/q) q^{-3a} + q^{-3w}   (direct)
    S = geo(q**-2)*(1-1/q)/(1-q**-3) - (1-1/q)/(1-q**-3)*geo(q**-5) + geo(q**-5)
    return sp.cancel((1 - 1/q) * S)

def E_quad_n2_closed():
    return sp.cancel((1 - 1/q) * geo(q**-2))

def J4_trunc_terms(w, MB):
    """J4(w) from finite strata only: sum over (a,b) with a,b <= MB, + remainder bound."""
    tot = sp.Integer(0)
    for a in range(MB+1):
        for b in range(MB+1):
            m = min(a, w + b)
            tot += (1-1/q)*q**-a * (1-1/q)*q**-b * q**(-2*m)
    return tot

# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------
def main():
    Phi5 = q**4+q**3+q**2+q+1
    S4R = q*(2*q**6+2*q**5+3*q**4+2*q**3+3*q**2+q+1)/((q+1)*(q**2+1)*Phi5)
    menus = {2: menu_n2(), 3: menu_n3(),
             4: _load_json_menu('genh4_checks_results.json', 'Rtau'),
             5: _load_json_menu('bcfgtie_results.json', 'quintic_densities')}
    log("menus loaded: " + ", ".join("n=%d:%d rows" % (n, len(m)) for n, m in sorted(menus.items())))

    # P1: menu cross-foot
    for n, m in sorted(menus.items()):
        check("P1-foot-n%d" % n, is_zero(sum(m.values()) - 1), "sum R_tau = 1")

    # sanity gates (non-prereg): f=1 recursion reproduces MOMENTS anchors
    F1 = Fvec(1, q, 4)
    check("R-sanity-F2", is_zero(F1[2][0] - (q+2)/(2*(q+1))) and is_zero(F1[2][2] - q/(2*(q+1))),
          "F_2 = (qt^2+q+2)/(2(q+1))")
    check("R-sanity-mean", all(is_zero(moments_from_pgf(F1[n], 1)[0] - q/(q+1)) for n in (2,3,4)),
          "E_n = q/(q+1)")

    # P2: the 32 cells, and P3 rows. Models: menus n=2,3,4 MONIC; n=5 PROJECTIVE (r2a).
    NMAX = 5
    # r2a sanity gate: projective conversion reproduces E^p = 1 at K = F
    Fp1 = proj_pgf(1, 5)
    check("R-sanity-proj", is_zero(moments_from_pgf(Fp1, 1)[0] - 1), "K=F projective mean = 1 at n=5")
    verdict_table = {}
    for f in (2, 3):
        FK = Fvec(f, q, NMAX)
        for n in range(2, NMAX+1):
            model = "proj" if n == 5 else "monic"
            law = proj_pgf(f, n) if n == 5 else FK[n]
            rec = moments_from_pgf(law, 4)
            for k in (1, 2, 3, 4):
                men = menu_moment(menus[n], f, k)
                ok = is_zero(men - rec[k-1])
                verdict_table["f%d_k%d_n%d" % (f, k, n)] = "EQUAL" if ok else "MISMATCH"
                check("P2-f%d-k%d-n%d" % (f, k, n), ok,
                      model if ok else "%s menu=%s recur=%s" % (model, sp.cancel(men), sp.cancel(rec[k-1])))
        if f == 2:
            m4 = moments_from_pgf(FK[4], 1)[0]
            m5 = moments_from_pgf(FK[5], 1)[0]
            check("P3-S4R-n4", is_zero(m4 - S4R), "E(4) = S4.R closed form")
            check("P3-S4R-n5", is_zero(m5 - S4R), "E(5) = S4.R closed form")
            RESULTS["S4R_mean_f2"] = str(sp.cancel(m4))

    # P4: Tier-2 Kac-Rice legs (f=2)
    KR4 = sp.cancel(q/(q+1) + E_quad_n4_closed())
    check("P4-KR-S4R", is_zero(KR4 - S4R), "Kac-Rice E[X_K](n>=4) == S4.R")
    # depth-bounded expansion protocol: truncated strata vs closed form, depth 15
    x = sp.symbols('x', positive=True)
    D = 15; WB = 8; MB = 16
    trunc = (1-1/q)*sum(q**(-2*w) * J4_trunc_terms(w, MB) for w in range(WB+1)) + q/(q+1)
    serA = sp.series(KR4.subs(q, 1/x), x, 0, D+1).removeO()
    serB = sp.series(sp.cancel(trunc).subs(q, 1/x), x, 0, D+1).removeO()
    check("P4-KR-depth15", sp.expand(serA - serB) == 0,
          "1/q-expansion agrees to depth %d (num+den+1 = 15; strata w<=%d, vals<=%d)" % (D, WB, MB))
    RESULTS["KR_depth_series"] = str(sp.expand(serA))

    # P5: small-n KR legs
    check("P5-KR-n2", is_zero(q/(q+1) + E_quad_n2_closed() - 2*q/(q+1)), "TK-Q reproduced")
    # [run-2 repair r2c: the sealed target was 1 - Phi6/Phi5 -- that is TAMEK S3's
    #  RAMIFIED-quad dip anchor, pasted in error; the unramified-quad n=3 anchor is
    #  q/(q+1) + 2 R_{(1,2)(1,1)} = q/(q+1) + q^3(q^2+q+1)/((q+1)Phi5) (= 357/242 at q=3).]
    anchor3 = q/(q+1) + q**3*(q**2+q+1)/((q+1)*Phi5)
    check("P5-KR-n3", is_zero(q/(q+1) + E_quad_n3_closed() - anchor3), "unram n=3 anchor reproduced")

    # P6: teeth
    bites = 0
    for f in (2, 3):
        FK = Fvec(f, q, 3)
        for n in (2, 3):
            for k in (1, 2):
                if not is_zero(menu_moment(menus[n], f, k, X_K_bad) - moments_from_pgf(FK[n], k)[k-1]):
                    bites += 1
    RESULTS["teeth"].append({"name": "T1-wrong-weight", "bites": bites})
    check("P6-T1", bites >= 1, "wrong-weight mutant breaks %d cells" % bites)

    m3s = dict(menu_n3())
    a, b = ((1,1),(1,2)), ((1,1),(2,1))
    m3s[a], m3s[b] = m3s[b], m3s[a]
    F2v = Fvec(2, q, 3)
    t2 = not is_zero(menu_moment(m3s, 2, 1) - moments_from_pgf(F2v[3], 1)[0])
    RESULTS["teeth"].append({"name": "T2-swapped-rows", "bites": int(t2)})
    check("P6-T2", t2, "swapped n=3 menu rows break f=2 k=1 n=3")

    Fdrop = Fvec(2, q, 2, drop_top_block=True)
    t3 = not is_zero(menu_moment(menus[2], 2, 1) - moments_from_pgf(Fdrop[2], 1)[0])
    RESULTS["teeth"].append({"name": "T3-block-drop", "bites": int(t3)})
    check("P6-T3", t3, "delta=f block dropped breaks f=2 k=1 n=2")

    RESULTS["verdict_table"] = verdict_table
    RESULTS["elapsed_s"] = round(time.time() - T0, 1)
    RESULTS["verdict"] = "GREEN" if RESULTS["fails"] == 0 else "RED"
    with open(os.path.join(HERE, "tamekqx_results.json"), "w") as fh:
        json.dump(RESULTS, fh, indent=1, default=str)
    with open(os.path.join(HERE, "tamekqx_output.txt"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")
    log("VERDICT: %s (%d checks, %d fails)" % (RESULTS["verdict"], len(RESULTS["checks"]), RESULTS["fails"]))
    sys.exit(0 if RESULTS["fails"] == 0 else 1)

if __name__ == "__main__":
    main()
