#!/usr/bin/env python3
"""l3cohom_m2.py -- M2 COHOMOLOGICAL COBOUNDARY TEST (POST-SEAL DIAGNOSTIC;
NOT PREREGISTERED; the sealed prereg ITERLAWR_PROBE_2026-08-08.md + runner
iterlawr_probe.py are consumed READ-ONLY as the measurement apparatus).

METHOD.  The measured level-3 values c3(g,g') = val3(phi_g phi_g')/val3(phi_{g+g'})
form a 2-cocycle on the window (associativity of the graded product).  On tiny
towers (E3 in {4,6,8}, p in {2,3}, all four rings) we:
  (1) verify the cocycle identity on the MEASURED data, window level (raw sums,
      no reduction) AND quotient level (the Z/E3-descended table; G7 descent
      re-verified first, including the fresh rows);
  (2) for each template t in {composed sealed candidate, naive per-level}:
      form the discrepancy d = c_meas / t and test COBOUNDARY exactly --
      is d = f(g) f(g') / f(g+g') for some 1-cochain f: Z/E3 -> M, with
      M = <zbar, z2, z1> the letter subgroup of K3^x (cyclic; exact dlog);
      cyclic-group solver: x(0) forced by L(0,0), x(1) = t scanned over Z/m,
      the rest forced by the (k,1) equations, then ALL n^2 equations verified;
      obstruction kappa = sum_k L(k,1) mod m cross-checked (H^2(Z/n, Z/m));
  (3) integer layer: the exponent cochains d3, D2, D1 (composed), numN (naive
      z1-numerator), dint = l0*(Sig - gamma2*d2) tested as Z-valued 2-cocycles
      (defect counts over all n^3 quotient triples), Z-coboundary + class in
      H^2(Z/n, Z) = Z/n where they ARE cocycles;
  (4) the GAUGE DECOMPOSITION (the strategy reading): verify exhaustively at
      window level  c3 = zbar^{d3} * dF,  dF(g,g') = F(g)F(g')/F(g+g'),
      F(g) = eps2(b2(g))*eps1(b1(g)) = the eps-chain (= val3(phi_g), L6-3),
      with closed form F = z2^{(s2-l1*b2)/e1} * z1^{(s1-l0*b1)/e0}, and the
      monodromy rho = F(g+E3)/F(g) = z2^{-l1*e0} * z1^{-l0} (constant).

STATED EXPECTATIONS (checked in-run; NOT a seal -- post-seal diagnostics):
  P1 measured cocycle identity: 0 violations (window + quotient).
  P2 composed template: d_comp == 1 identically (fresh E3=6 shapes included).
  P3 c3/zbar^d3 == dF at window level, F == its closed form: 0 violations.
  P4 classes on the quotient (closed-form predictions, derived by telescoping):
     kappa_Z(d3-table) = (E3/e2)*l2  exactly over Z;
     sigma(tail) == z2^{l1*e0} * z1^{l0}   mod M^E3;
     sigma(c3)   == zbar^{(E3/e2)*l2} * z2^{l1*e0} * z1^{l0}  mod M^E3.
  P5 naive template: on towers with e1 >= 2, l0 != 0, e2 >= 2 the naive
     numerator numN FAILS the Z-cocycle identity (defect = l0*gamma2*defect(d2)
     with defect(d2) != 0) -- no gauge can repair it; on e1 = 1 towers numN IS
     a cocycle and the discrepancy is the class l0*gamma3*[d3].
  P6 composed integer layer: d3, D2, D1 all Z-valued 2-cocycles (0 defects).
  P7 M5 cross-check (transplanted Phi-chain, LEG-T pattern): 20/20 exact.

Author: M2 (level-3 pattern hunt fleet), campaign date 2026-08-08
(wallclock 2026-08-03).  Deterministic, exact arithmetic, no sampling.
"""
import sys, os, json, math, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawr_probe as ILP
from iterlawr_probe import Composite3, k3_repr
from strata3_probe import Tower3
from grb_order2_check import eq12, bezout, pmul

# roster: sealed shapes re-measured (A,C,E,G,CV,CW,CX) + FRESH E3=6 shapes S1-S4
ROWS = [
    ("A",  1, (2,1,1), (2,1,1), (2,1,1), "sealed shape; E3=8 fully stacked"),
    ("C",  1, (2,1,2), (2,1,1), (2,1,1), "sealed shape; E3=8 z1 genuine"),
    ("E",  1, (2,1,1), (2,1,2), (2,1,1), "sealed shape; E3=8 z2 genuine"),
    ("G",  1, (2,1,1), (2,1,1), (2,1,2), "sealed shape; E3=8 zbar genuine"),
    ("CV", 1, (1,1,2), (2,1,1), (2,1,1), "sealed shape; E3=4 e0=1 control"),
    ("CW", 1, (2,1,1), (1,1,2), (2,1,1), "sealed shape; E3=4 e1=1 control"),
    ("CX", 1, (2,1,1), (2,1,1), (1,1,2), "sealed shape; E3=4 e2=1 control"),
    ("S1", 1, (1,1,2), (2,1,1), (3,1,1), "FRESH; E3=6 e=(1,2,3) z1-field live"),
    ("S2", 1, (2,1,2), (1,1,2), (3,2,1), "FRESH; E3=6 e=(2,1,3) z1,z2 live"),
    ("S3", 1, (3,2,1), (1,1,2), (2,1,2), "FRESH; E3=6 e=(3,1,2) l0=2, z2,zbar live"),
    ("S4", 1, (1,1,2), (3,1,1), (2,1,2), "FRESH; E3=6 e=(1,3,2) l1=1, zbar live"),
]
CONFIGS = [("Zp", 2), ("Zp", 3), ("Fpt", 2), ("Fpt", 3)]
TABLE_TOWERS = [("Zp",3,"CW"), ("Zp",3,"C"), ("Zp",3,"S2"), ("Zp",3,"S3")]

LINES = []
def log(s=""):
    print(s); LINES.append(s)

# ---------------- independent transcription of the S1 constants ----------------
def msplit(T3, g):
    T = T3.T
    s3, u3 = eq12(g, T3.e2, T3.h2); b2 = u3 - s3*T.w2Phi2
    s2, u2 = eq12(b2, T.e1, T.h1);  b1 = u2 - s2*T.w1Phi1
    s1, u1 = eq12(b1, T.e0, T.h0)
    return s3, s2, s1, b2, b1, u1

def consts(T3, ga, gb):
    T = T3.T
    s3a,s2a,s1a,b2a,b1a,_ = msplit(T3, ga)
    s3b,s2b,s1b,b2b,b1b,_ = msplit(T3, gb)
    s3c,s2c,s1c,b2c,b1c,_ = msplit(T3, ga+gb)
    d3 = (s3a+s3b)//T3.e2; d2 = (s2a+s2b)//T.e1; d1 = (s1a+s1b)//T.e0
    numD2 = s2a+s2b-s2c + T.l1*T3.gamma3*d3
    D2 = numD2//T.e1 if numD2 % T.e1 == 0 else None
    Sig = None if D2 is None else D2*T.gamma2 + d3*T3.gamma3*(T.l1p - T.l1*T.w1Phi1)
    numD1 = None if Sig is None else s1a+s1b-s1c + T.l0*Sig
    D1 = (numD1//T.e0 if numD1 is not None and numD1 % T.e0 == 0 else None)
    numN = s1a+s1b-s1c + T.l0*T.gamma2*d2
    D1n = numN//T.e0 if numN % T.e0 == 0 else None
    dint = None if Sig is None else T.l0*(Sig - T.gamma2*d2)
    return dict(d3=d3, d2=d2, D2=D2, Sig=Sig, D1=D1, D1n=D1n,
                numN=numN, dint=dint)

# ---------------- letter subgroup M, dlog, cyclic solvers ----------------
def ordv(K3, x):
    o = 1; y = x
    while y != K3["one"]:
        y = K3["mul"](y, x); o += 1
        assert o < 10000
    return o

def letter_group(C):
    K3 = C.K3
    gens = [C.zbar, C.z2_3, C.z1_3]
    elems = {K3["one"]}; frontier = [K3["one"]]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = K3["mul"](x, g)
                if y not in elems:
                    elems.add(y); new.append(y)
        frontier = new
    m = len(elems)
    gen = None
    for x in elems:
        if ordv(K3, x) == m:
            gen = x; break
    assert gen is not None, "letter subgroup not cyclic?!"
    dlog = {}; y = K3["one"]
    for k in range(m):
        dlog[y] = k; y = K3["mul"](y, gen)
    Mn = {K3["pow"](x, C.T3.E3) for x in elems}   # E3-th powers in M
    return elems, m, gen, dlog, Mn

def cob_solve_modm(L, n, m):
    """x: Z/n -> Z/m with x(r)+x(s)-x((r+s)%n) == L[r][s] mod m, or None."""
    x0 = L[0][0] % m
    for t in range(m):
        x = [x0, t % m]
        for k in range(1, n-1):
            x.append((x[k] + x[1] - L[k][1]) % m)
        if all((x[r]+x[s]-x[(r+s)%n]-L[r][s]) % m == 0
               for r in range(n) for s in range(n)):
            return x
    return None

def cob_solve_Z(L, n):
    """x: Z/n -> Z with x(r)+x(s)-x((r+s)%n) == L[r][s] in Z, or None."""
    kap = sum(L[k][1] for k in range(n))
    if kap % n != 0:
        return None, kap
    t = kap//n
    x = [L[0][0], t]
    for k in range(1, n-1):
        x.append(x[k] + x[1] - L[k][1])
    ok = all(x[r]+x[s]-x[(r+s)%n] == L[r][s] for r in range(n) for s in range(n))
    return (x if ok else None), kap

def int_defect(X, n):
    """count + first witness of 2-cocycle defects of integer table X on Z/n."""
    bad = 0; wit = None
    for a in range(n):
        for b in range(n):
            for t in range(n):
                d = (X[b][t] + X[a][(b+t)%n]) - (X[a][b] + X[(a+b)%n][t])
                if d != 0:
                    bad += 1
                    if wit is None: wit = (a, b, t, d)
    return bad, wit

# ---------------- per-tower analysis ----------------
def analyze(kind, p, tag, d0, r0, r1, r2):
    T3 = Tower3(kind, p, d0, r0, r1, r2, f"{kind},p={p},{tag}")
    C = Composite3(T3); T = T3.T; K3 = C.K3
    n = T3.E3; G0 = C.Gamma0
    assert G0 % n == 0, "Gamma0 not == 0 mod E3 -- quotient labels shift"
    rec = dict(tower=f"{kind},p={p},{tag}", E3=n, Gamma0=G0,
               e=(T.e0, T.e1, T3.e2), h=(T.h0, T.h1, T3.h2),
               l0=T.l0, l1=T.l1, l2=T3.l2, gamma2=T.gamma2, gamma3=T3.gamma3)
    reps = [G0 + r for r in range(n)]
    cmeas = [[C.cocycle(ga, gb)[0] for gb in reps] for ga in reps]
    K = [[consts(T3, ga, gb) for gb in reps] for ga in reps]

    # XCONST: my transcription vs the sealed runner's constants
    xbad = 0
    for i, ga in enumerate(reps):
        for j, gb in enumerate(reps):
            rc = C.constants(ga, gb)
            if any(K[i][j][k] != rc[k] for k in
                   ("d3", "d2", "D2", "Sig", "D1")) or K[i][j]["D1n"] != rc["D1n"]:
                xbad += 1
    rec["XCONST_viol"] = xbad

    # DESC: field + integer descent under either-representative translation
    dbad = 0
    for i, ga in enumerate(reps):
        for j, gb in enumerate(reps):
            if C.cocycle(ga+n, gb)[0] != cmeas[i][j]: dbad += 1
            if C.cocycle(ga, gb+n)[0] != cmeas[i][j]: dbad += 1
            k2 = consts(T3, ga+n, gb)
            if any(k2[k] != K[i][j][k] for k in
                   ("d3","d2","D2","Sig","D1","D1n","numN","dint")): dbad += 1
    rec["DESC_viol"] = dbad

    # COC window (raw sums) + quotient (descended table)
    wbad = 0
    for ga in reps:
        for gb in reps:
            for gt in reps:
                lhs = K3["mul"](C.cocycle(gb, gt)[0], C.cocycle(ga, gb+gt)[0])
                rhs = K3["mul"](C.cocycle(ga, gb)[0], C.cocycle(ga+gb, gt)[0])
                if lhs != rhs: wbad += 1
    qbad = 0
    for a in range(n):
        for b in range(n):
            for t in range(n):
                lhs = K3["mul"](cmeas[b][t], cmeas[a][(b+t)%n])
                rhs = K3["mul"](cmeas[a][b], cmeas[(a+b)%n][t])
                if lhs != rhs: qbad += 1
    rec["COC_window_viol"] = wbad; rec["COC_quotient_viol"] = qbad

    # P2: composed template == measured (incl. FRESH shapes)
    g3bad = 0
    for i in range(n):
        for j in range(n):
            c = K[i][j]
            assert c["D2"] is not None and c["D1"] is not None, "composed nonintegral"
            tv = K3["mul"](K3["pow"](C.zbar, c["d3"]),
                 K3["mul"](K3["pow"](C.z2_3, c["D2"]), K3["pow"](C.z1_3, c["D1"])))
            if tv != cmeas[i][j]: g3bad += 1
    rec["COMPOSED_viol"] = g3bad

    # naive census
    nonint = fdiff = eqc = 0; sep_not_d3 = 0; first_nonint = None
    for i in range(n):
        for j in range(n):
            c = K[i][j]
            if c["D1n"] is None:
                nonint += 1
                if first_nonint is None:
                    first_nonint = (reps[i], reps[j], c["d3"], c["numN"])
                if c["d3"] != 1: sep_not_d3 += 1
                continue
            tv = K3["mul"](K3["pow"](C.zbar, c["d3"]),
                 K3["mul"](K3["pow"](C.z2_3, c["D2"]), K3["pow"](C.z1_3, c["D1n"])))
            if tv != cmeas[i][j]:
                fdiff += 1
                if c["d3"] != 1: sep_not_d3 += 1
            else:
                eqc += 1
    rec["NAIVE"] = dict(nonint=nonint, fielddiff=fdiff, eq=eqc,
                        sep_not_at_d3eq1=sep_not_d3, first_nonint=first_nonint)

    # P3: gauge decomposition at window level; F closed form; monodromy rho
    F = {g: C.eps_chain(g) for g in range(G0, 2*G0 + 2*n)}
    wm = fc = 0
    for i, ga in enumerate(reps):
        for j, gb in enumerate(reps):
            dF = K3["mul"](K3["mul"](F[ga], F[gb]), K3["inv"](F[ga+gb]))
            if K3["mul"](K3["pow"](C.zbar, K[i][j]["d3"]), dF) != cmeas[i][j]:
                wm += 1
    for g in reps + [ga+gb for ga in reps for gb in reps][:n]:
        s3, s2, s1, b2, b1, _ = msplit(T3, g)
        a2 = s2 - T.l1*b2; a1 = s1 - T.l0*b1
        assert a2 % T.e1 == 0 and a1 % T.e0 == 0
        if K3["mul"](K3["pow"](C.z2_3, a2//T.e1),
                     K3["pow"](C.z1_3, a1//T.e0)) != F.get(g, C.eps_chain(g)):
            fc += 1
    rho_pred = K3["mul"](K3["pow"](C.z2_3, -T.l1*T.e0), K3["pow"](C.z1_3, -T.l0))
    rho_bad = sum(1 for g in reps[:4]
                  if K3["mul"](C.eps_chain(g+n), K3["inv"](C.eps_chain(g))) != rho_pred)
    rec["WMULT3_window_viol"] = wm; rec["EPSCLOSED_viol"] = fc
    rec["RHO_viol"] = rho_bad

    # integer layer on the quotient
    IL = {}
    for name, key in (("d3","d3"), ("D2","D2"), ("D1","D1"),
                      ("numN","numN"), ("dint","dint")):
        X = [[K[i][j][key] for j in range(n)] for i in range(n)]
        bad, wit = int_defect(X, n)
        IL[name] = dict(defect=bad, witness=wit)
        if bad == 0:
            x, kap = cob_solve_Z(X, n)
            IL[name].update(kappaZ=kap, classZ=kap % n,
                            cobZ=(x is not None), fZ=x)
    IL["d3"]["kappaZ_pred"] = (n//T3.e2)*T3.l2
    rec["INT"] = IL

    # field-level cohomology over M
    elems, m, gen, dlog, Mn = letter_group(C)
    rec["letters"] = dict(m=m, ord_zbar=ordv(K3, C.zbar),
                          ord_z2=ordv(K3, C.z2_3), ord_z1=ordv(K3, C.z1_3))
    fam = {}
    if m == 1:
        rec["COB"] = "FIELD-INVISIBLE (all letters = 1; integer layer governs)"
    else:
        def cob_family(name, tab, pred_sigma=None):
            assert all(v in elems for row in tab for v in row), f"{name}: value outside M"
            L = [[dlog[v] for v in row] for row in tab]
            x = cob_solve_modm(L, n, m)
            kap = sum(L[k][1] for k in range(n)) % m
            sigma = K3["pow"](gen, kap)
            out = dict(coboundary=(x is not None), kappa=kap,
                       sigma=k3_repr(C, sigma),
                       kappa_says_cob=(sigma in Mn),
                       f=( [k3_repr(C, K3["pow"](gen, xi)) for xi in x] if x else None))
            assert out["coboundary"] == out["kappa_says_cob"], f"{name}: solver/kappa clash"
            # full unit-group gauge: sigma an E3-th power in K3^x ?
            Q = K3["q"]; gfull = math.gcd(n, Q-1)
            out["coboundary_fullK3x"] = (K3["pow"](sigma, (Q-1)//gfull) == K3["one"])
            if pred_sigma is not None:
                dev = K3["mul"](sigma, K3["inv"](pred_sigma))
                out["sigma_matches_pred_mod_Mn"] = (dev in Mn)
            fam[name] = out
        top = [[K3["pow"](C.zbar, K[i][j]["d3"]) for j in range(n)] for i in range(n)]
        tail = [[K3["mul"](cmeas[i][j], K3["inv"](top[i][j])) for j in range(n)]
                for i in range(n)]
        pred_tail = K3["mul"](K3["pow"](C.z2_3, T.l1*T.e0), K3["pow"](C.z1_3, T.l0))
        pred_full = K3["mul"](K3["pow"](C.zbar, (n//T3.e2)*T3.l2), pred_tail)
        cob_family("c_meas", cmeas, pred_full)
        cob_family("topcarry", top)
        cob_family("tail", tail, pred_tail)
        dcomp = [[K3["one"] for _ in range(n)] for _ in range(n)]
        cob_family("d_composed", dcomp)
        if nonint == 0:
            dn = [[K3["mul"](cmeas[i][j], K3["inv"](
                    K3["mul"](K3["pow"](C.zbar, K[i][j]["d3"]),
                    K3["mul"](K3["pow"](C.z2_3, K[i][j]["D2"]),
                              K3["pow"](C.z1_3, K[i][j]["D1n"])))))
                   for j in range(n)] for i in range(n)]
            cob_family("d_naive", dn)
        else:
            fam["d_naive"] = f"ILL-POSED at field level ({nonint} pairs nonintegral)"
        rec["COB"] = fam
    return T3, C, rec, cmeas, K

# ---------------- eyeball tables ----------------
def print_table(C, rec, cmeas, K):
    n = rec["E3"]; G0 = rec["Gamma0"]
    log(f"\n---- FULL PAIR TABLE {rec['tower']}  E3={n}  Gamma0={G0}  "
        f"(e)={rec['e']} (h)={rec['h']}  l0={rec['l0']} l1={rec['l1']} l2={rec['l2']}  "
        f"letters m={rec['letters']['m']} "
        f"(ord zbar,z2,z1)=({rec['letters']['ord_zbar']},"
        f"{rec['letters']['ord_z2']},{rec['letters']['ord_z1']}) ----")
    log(f"{'r':>2} {'s':>2} {'gam':>5} {'gam2':>5} | {'measured c3':22} | "
        f"{'d3':>2} {'D2':>3} {'D1':>3} | {'D1naive':>7} | discrepancy c3/naive")
    for i in range(n):
        for j in range(n):
            c = K[i][j]; K3 = C.K3
            meas = k3_repr(C, cmeas[i][j])
            if c["D1n"] is None:
                nv, dis = "NONINT", "(undefined)"
            else:
                nval = K3["mul"](K3["pow"](C.zbar, c["d3"]),
                       K3["mul"](K3["pow"](C.z2_3, c["D2"]),
                                 K3["pow"](C.z1_3, c["D1n"])))
                nv = str(c["D1n"])
                dis = k3_repr(C, K3["mul"](cmeas[i][j], K3["inv"](nval)))
            log(f"{i:>2} {j:>2} {G0+i:>5} {G0+j:>5} | {meas:22} | "
                f"{c['d3']:>2} {c['D2']:>3} {c['D1']:>3} | {nv:>7} | {dis}")

# ---------------- M5 cross-check (LEG-T transplant pattern) ----------------
def m5_crosscheck():
    import level3_xcheck as MX
    def convM2T(level, x):
        if level == 0: return (x,)
        return tuple(convM2T(level-1, c) for c in x)
    def conv_psi(level, psi):
        def cT2M(lv, y):
            if lv == 0: return y[0]
            return tuple(cT2M(lv-1, c) for c in y)
        return [cT2M(level, c) for c in psi[:-1]]
    total = bad = 0; lines = []
    for kind, p, tag in [("Zp",3,"S2"), ("Fpt",3,"G")]:
        row = next(r for r in ROWS if r[0] == tag)
        _, d0, r0, r1, r2, _ = row
        T3 = Tower3(kind, p, d0, r0, r1, r2, f"{kind},p={p},{tag}")
        C = Composite3(T3); n = T3.E3; G0 = C.Gamma0
        R = MX.ZRing(p) if kind == "Zp" else MX.TRing(p)
        reads = [(r0[0], r0[1], conv_psi(0, T3.T.psi0)),
                 (r1[0], r1[1], conv_psi(1, T3.T.psi1)),
                 (r2[0], r2[1], conv_psi(2, T3.psi2))]
        Tt = MX.Tower(R, reads)
        Tt.Phi[0] = list(T3.T.Phi0); Tt.Phi[1] = list(T3.T.Phi1)
        Tt.Phi[2] = list(T3.T.Phi2); Tt._phipowcache = {}
        pairs = [(G0 + k % n, G0 + (3*k+1) % n) for k in range(10)]
        for ga, gb in pairs:
            cs = C.cocycle(ga, gb)[0]
            cm, _ = Tt.cocycle(ga, gb)
            total += 1
            if cm is None or convM2T(3, cm) != cs:
                bad += 1
                lines.append(f"  M5 DIVERGENCE {kind},p={p},{tag} ({ga},{gb}): "
                             f"m5={cm} sealed={cs}")
        lines.append(f"  M5 xcheck {kind},p={p},{tag}: 10 tuples, "
                     f"{sum(1 for _ in pairs)} compared")
    return total, bad, lines

# ---------------- main ----------------
def main():
    t0 = time.time()
    log("l3cohom_m2.py -- M2 cohomological coboundary test "
        "(POST-SEAL DIAGNOSTIC, NON-PREREG)")
    log(f"roster: {len(ROWS)} shapes x {len(CONFIGS)} rings; exhaustive "
        "W1xW1 pairs, n^3 triples, exact cohomology on Z/E3")
    log("")
    recs = []; tables = []
    for kind, p in CONFIGS:
        for tag, d0, r0, r1, r2, note in ROWS:
            T3, C, rec, cmeas, K = analyze(kind, p, tag, d0, r0, r1, r2)
            rec["note"] = note
            recs.append(rec)
            if (kind, p, tag) in TABLE_TOWERS:
                tables.append((C, rec, cmeas, K))
        log(f"[{time.time()-t0:6.1f}s] ring ({kind},p={p}) analyzed")
    for C, rec, cmeas, K in tables:
        print_table(C, rec, cmeas, K)

    # aggregates
    log("\n" + "="*78)
    log("AGGREGATES (all towers)")
    log("="*78)
    agg = lambda k: sum(r[k] for r in recs)
    for k in ("XCONST_viol", "DESC_viol", "COC_window_viol", "COC_quotient_viol",
              "COMPOSED_viol", "WMULT3_window_viol", "EPSCLOSED_viol", "RHO_viol"):
        log(f"  {k:22} total = {agg(k)}   (expected 0)")
    ni = sum(r["NAIVE"]["nonint"] for r in recs)
    fd = sum(r["NAIVE"]["fielddiff"] for r in recs)
    sn = sum(r["NAIVE"]["sep_not_at_d3eq1"] for r in recs)
    log(f"  NAIVE: nonintegral pairs = {ni}, field-diff pairs = {fd}, "
        f"separation pairs NOT at d3=1 = {sn} (expected 0)")
    log("\nINTEGER-LAYER COCYCLE DEFECTS + CLASSES (per tower)")
    log(f"{'tower':16} {'d3 def':>6} {'D2 def':>6} {'D1 def':>6} {'numN def':>8} "
        f"{'dint def':>8} | {'kZ(d3)':>6} {'pred':>5} {'clsZ(d3)':>8} "
        f"{'kZ(dint)':>8} {'clsZ':>5}")
    for r in recs:
        I = r["INT"]
        kz = I["d3"].get("kappaZ"); pz = I["d3"]["kappaZ_pred"]
        cz = I["d3"].get("classZ")
        kd = I["dint"].get("kappaZ", "-"); cd = I["dint"].get("classZ", "-")
        log(f"{r['tower']:16} {I['d3']['defect']:>6} {I['D2']['defect']:>6} "
            f"{I['D1']['defect']:>6} {I['numN']['defect']:>8} "
            f"{I['dint']['defect']:>8} | {str(kz):>6} {pz:>5} {str(cz):>8} "
            f"{str(kd):>8} {str(cd):>5}")
    log("\nFIELD-LEVEL COHOMOLOGY OVER M = <zbar,z2,z1> (per tower)")
    log(f"{'tower':16} {'m':>3} | {'c3 cob?':>8} {'sigma(c3)':>18} {'predOK':>6} "
        f"{'full':>5} | {'top cob?':>8} | {'tail cob?':>9} {'predOK':>6} | naive")
    for r in recs:
        if isinstance(r["COB"], str):
            log(f"{r['tower']:16} {r['letters']['m']:>3} | {r['COB']}")
            continue
        F = r["COB"]
        nv = F["d_naive"] if isinstance(F["d_naive"], str) else \
             ("cob" if F["d_naive"]["coboundary"] else "NOT-cob")
        log(f"{r['tower']:16} {r['letters']['m']:>3} | "
            f"{str(F['c_meas']['coboundary']):>8} {F['c_meas']['sigma']:>18} "
            f"{str(F['c_meas'].get('sigma_matches_pred_mod_Mn')):>6} "
            f"{str(F['c_meas']['coboundary_fullK3x']):>5} | "
            f"{str(F['topcarry']['coboundary']):>8} | "
            f"{str(F['tail']['coboundary']):>9} "
            f"{str(F['tail'].get('sigma_matches_pred_mod_Mn')):>6} | {nv}")

    log("\nM5 CROSS-CHECK (transplanted Phi-chain, 20 tuples)")
    tot, bad, lines = m5_crosscheck()
    for l in lines: log(l)
    log(f"  M5 xcheck TOTAL: {tot} tuples, {bad} divergent "
        f"({'GREEN' if bad == 0 else 'RED'})")

    with open("l3cohom_m2_results.json", "w") as f:
        json.dump(recs, f, indent=1, default=str)
    with open("l3cohom_m2_output.txt", "w") as f:
        f.write("\n".join(LINES) + "\n")
    log(f"\nwrote l3cohom_m2_results.json + l3cohom_m2_output.txt   "
        f"elapsed {time.time()-t0:.1f}s")
    return 0

if __name__ == "__main__":
    sys.exit(main())
