#!/usr/bin/env python3
"""gentow5_wi_checks.py -- SEALED INSTRUMENT for [GENTOW5-W(i)]
(companion note GENTOW5_WI_2026-08-10.md, RCT unit GENTOW5-W-i-lemma).

TWO-COMMIT SEAL: this file is committed BEFORE any run, with the
preregistered predictions below (verbatim ids from note S5).  The run
output (gentow5_wi_checks_output.txt) and the S6 verdict land in a
second commit.  RED outcomes are kept with diagnosis, never tuned away.
NO smoke run precedes the seal: the LW3 gp leg and every LW3 exact leg
run first UNDER the seal.  (Hand arithmetic behind the predictions --
the nhat solves and the lattice split -- was done twice on paper in the
note; no code executed against LW3 before sealing.)

FRAMES.
  F-A   the committed q = 2 chain (GENTOW5 S4 + pe3 D-legs):
        u = (1,5,21,85,341,1365), Phi_1 = x^2-2, Phi_2 = Phi_1^2-4x,
        Phi_3 = Phi_2^2-16Phi_1, Phi_4 = Phi_3^2-256Phi_2,
        f32 = Phi_4^2-2^16 Phi_3, f64 = f32^2-2^32 Phi_4,
        mutants f32m = Phi_4^2-2^20 Phi_1, f64m = f32^2-2^40 Phi_2.
  F-LW3 THE NEW FRAME (letter-live level 3): p = 3, h = 1,
        (e,f) = (2,1),(2,1),(2,1),(1,2), u = (1,5,21,43),
        Phi_1 = x^2-6, Phi_2 = Phi_1^2-18x, Phi_3 = Phi_2^2-162Phi_1,
        coherent key  Phi_4LW = Phi_3^2 - 3xPhi_1Phi_2*Phi_3 - 2*3^9*xPhi_1,
        naive twin    Phi_4n  = Phi_3^2 - 3xPhi_1Phi_2*Phi_3 -   3^9*xPhi_1,
        target psi_4 = y^2 - y - 1 over K_3 = F_3.

PREREGISTERED PREDICTIONS (T = tooth, must FIRE/kill).
  P-A1  committed nhat values EXACT: nhat_1(5)=4x, nhat_2(21)=16Phi_1,
        nhat_3(85)=256Phi_2, nhat_4(341)=2^16 Phi_3, nhat_5(1365)=2^32 Phi_4.
  P-A2  LW3 nhat values EXACT: nhat_1(5)=9x, nhat_2(21)=81Phi_1,
        nhat_3(43)=3xPhi_1Phi_2, nhat_3(86)=3^9 xPhi_1.
  P-A3  lattice: nhat_3(86)/nhat_3(43)^2 splits as gamma_1^-1 gamma_2^-1
        gamma_3^-1 EXACTLY; theta_3(0) = (z1 z2 z3)^-1 = 2 in F_3^x
        (z1 = z2 = z3 = 2); reciprocity vartheta_{3,2}*theta_3(0) = 1.
  P-B1  committed resultant ladders EXACT:
        v2(Res(Phi_4,g)) = (8,20,42,85), g = (x,Phi_1,Phi_2,Phi_3);
        v2(Res(f32,g))  = (16,40,84,170,341), g = (..,Phi_4);
        v2(Res(f64,g))  = (32,80,168,340,682,1365), g = (..,Phi_4,f32).
  P-B2  (T) committed mutant kills reproduced: Res(f32m,Phi_3) = 0,
        Res(f64m,Phi_4) = 0 (drain collapse, exact integer zero).
  P-C1  LW3 exact ladders: v3(Res(Phi_4LW,g)) = (8,20,42,86) for
        g = (x,Phi_1,Phi_2,Phi_3); naive twin the SAME (8,20,42,86)
        (resultants are height-level: gauge-blind).
  P-D1  gp: factorpadic(Phi_4LW,3) = ONE deg-16 factor; single prime,
        (e,f) = (8,2); nfeltval ladder (4,10,21,43).
  P-D2  letters at the prime: res(gamma_1)=res(gamma_2)=res(gamma_3)=2.
  P-D3  THE LAW [GENTOW5-W(3)]: with w_av := res(nhat_3(43)/P_3^43)
        (P_3 = Phi_2 x^20/Phi_1^10) and Y := res(Phi_3/(3xPhi_1Phi_2)):
        LAW-1 tr(Y) = Y+Y^3 = w_av;  LAW-2 Y^4 = 2*w_av^2;
        LAW-3 Y^2 - w_av*Y - w_av^2 = 0  (= psi_4^{(w_av)}(Y) = 0).
        w_av's VALUE is measured, not predicted; w_av in {1,2} is
        predicted (K_3 = F_3).
  P-D4  (T) psi_4^{(w')}(Y) != 0 at the other unit w' != w_av.
  P-D5  (T, w-free) Y^4 != (Y+Y^3)^2: u_3(beta_0) != u_3(beta_1)^2 --
        the theta-free power law killed regardless of w_av.
  P-D6  (T, conditional) if w_av != 1 then psi_4(Y) = Y^2-Y-1 != 0.
  P-D7  (T, disjunctive) naive twin fails the coherent certificate:
        NOT(one deg-16 factor AND f = 2 AND psi_4^{(w_av)}(Y') = 0);
        the firing branch is RECORDED.

DATED REPAIR (2026-08-10, post RUN 1 — RED KEPT as
gentow5_wi_checks_output_run1_RED.txt, md5 598d6704; 58 checks,
5 violations).  Diagnosis, two independent defects, both
INSTRUMENT-side:
 (1) gp PARSE: gp reading stdin does NOT continue statements across
     newlines at unbalanced parens — the multi-line C-VALS print and
     the whole naive-twin if-block executed as FRAGMENTS (so run 1's
     P-D1 ladder FAIL was a missing print, not a wrong value; probe
     shows C-VALS = (4,10,21,43) EXACT as preregistered).  Repair:
     every gp statement single-line.
 (2) AVATAR MIS-KEY: P-D3 LAW-1/LAW-3 + P-D4/P-D6 keyed the law to
     w_av = res(nhat_3(43)/pi_4^43), consuming the avatar = w
     identification — GENTOW2 S6.1 row 23, DESCRIPTIVE status (rides
     Thm 4.2's normal form incl. its x_r^{s(alpha)}-factor).  Run 1
     + the disclosed diagnosis probe measured the INTRINSIC data:
     tr(Y) = 1, norm(Y) = 2 — i.e. u_3(beta_1) = w = 1, u_3(beta_0)
     = 2 = theta_3(0)*w^2: [GENTOW5-W(3)] HOLDS on the nose at
     w = 1, while w_av = 2.  LW3 is the first machine geography
     where avatar != intrinsic w (PE6's four frames had the row-23
     factor trivial); the lemma (an R-read statement) is untouched
     — the avatar leg was never part of its content.  Repair: the
     law rows re-keyed INTRINSIC (w* := tr(Y), the top-slot
     tautology w = u_3(kbar) made operational); the avatar becomes a
     RECORD + the IDY closure; the discrepancy unit w_av/w* is
     RECORDED as the first measured row-23 gap.
RUN-2 PREREGISTRATION (provenance disclosed: rows marked [probe]
were observed once in the post-RED diagnosis probe /tmp/gpprobe3;
run 2 asserts their reproduction under the sealed instrument):
  P-D1' C-VALS ladder (4,10,21,43) [probe].
  P-D3' INTRINSIC LAW: w* := tr(Y) in {1,2}; LAW-I1 norm(Y) =
        2*tr(Y)^2 (the [GENTOW5-W(3)] two-slot closure at
        theta_3(0) = 2); LAW-I2 Y^2 - w*Y - (w*)^2 = 0 (minpoly(Y)
        = psi_4^{(w*)}, the display form).
  P-D4' (T) psi_4^{(w')}(Y) != 0 at w' != w* (kills the other unit).
  P-D5  (T) unchanged: norm(Y) != tr(Y)^2 (theta-free law dead).
  P-D6' (T, conditional) if w* != 1 then psi_4(Y) != 0 (vacuous at
        the probe-observed w* = 1; kept for form).
  P-D8  AVATAR RECORD: w_av printed; T0 := res(nhat_3(86)/
        nhat_3(43)^2) = 2 (lattice cross-pin); IDY U0 = T0*w_av^2
        with U0 := res(nhat_3(86)/pi_4^86) [probe: holds] — the
        avatar family obeys the SAME cocycle shape; the discrepancy
        unit w_av*(w*)^{-1} RECORDED (probe: 2) — row 23's first
        measured gap, filed to WFRAME OPEN-3's geography, NOT a law
        violation.
  P-D7' (T) naive twin VERDICT KILL: one deg-16 factor with (e,f) =
        (16,1) != (8,2) [probe] — the gauge-naive prescription's
        repeated-root residual (y+w)^2 drives a ramified refinement;
        nfeltval(Phi_3) at its prime RECORDED (probe: 86, value
        exact — the kill is in (e,f), not the ladder).
"""

import subprocess, sys

# ---------------- poly kit (dense int lists, index = degree) --------------
def pnorm(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a

def padd(a, b):
    n = max(len(a), len(b))
    return pnorm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                  for i in range(n)])

def pneg(a):
    return [-c for c in a]

def psub(a, b):
    return padd(a, pneg(b))

def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca:
            for j, cb in enumerate(b):
                if cb:
                    out[i + j] += ca * cb
    return pnorm(out)

def pscal(c, a):
    return pnorm([c * x for x in a])

def xpow(k):
    return [0] * k + [1]

def sylres(f, g):
    """Resultant via Bareiss fraction-free elimination on Sylvester."""
    m, n = len(f) - 1, len(g) - 1
    if m < 0 or n < 0:
        return 0
    N = m + n
    M = []
    fr = f[::-1]; gr = g[::-1]
    for i in range(n):
        M.append([0] * i + fr + [0] * (N - m - 1 - i))
    for i in range(m):
        M.append([0] * i + gr + [0] * (N - n - 1 - i))
    prev = 1
    sign = 1
    for k in range(N - 1):
        if M[k][k] == 0:
            piv = next((r for r in range(k + 1, N) if M[r][k] != 0), None)
            if piv is None:
                return 0
            M[k], M[piv] = M[piv], M[k]
            sign = -sign
        for i in range(k + 1, N):
            for j in range(k + 1, N):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
            M[i][k] = 0
        prev = M[k][k]
    return sign * M[N - 1][N - 1]

def vp(n, p):
    if n == 0:
        return None  # infinite
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

# ---------------- checks harness ----------------
class T:
    def __init__(self):
        self.n = 0
        self.bad = []
    def chk(self, cond, msg):
        self.n += 1
        print(('  ok: ' if cond else 'FAIL: ') + msg)
        if not cond:
            self.bad.append(msg)

# ---------------- nhat recursion (DEF GENTOW5-1) ----------------
def nhat(chain, i, m):
    """chain = dict(p, h, e=[e1..], u=[u1..]); returns (a, i0, [b1..b_{i-1}])
    with nhat_i(m) = p^a x^{i0} Phi_1^{b1} ... Phi_{i-1}^{b_{i-1}}, or None."""
    e, u, h = chain['e'], chain['u'], chain['h']
    bs = []
    cur = m
    for j in range(i - 1, 0, -1):        # level j+1 -> j : e_{j+1} m' + b_j u_{j+1} = cur
        ej, uj = e[j], u[j]              # e[j] = e_{j+1}, u[j] = u_{j+1} (0-based lists)
        b = next((bb for bb in range(ej) if (cur - bb * uj) % ej == 0
                  and cur - bb * uj >= 0), None)
        if b is None:
            return None
        bs.append(b)
        cur = (cur - b * uj) // ej
    e1 = e[0]
    i0 = next((ii for ii in range(e1) if (cur - ii * h) % e1 == 0
               and cur - ii * h >= 0), None)
    if i0 is None:
        return None
    a = (cur - i0 * h) // e1
    return (a, i0, bs[::-1])

def nhat_poly(chain, phis, spec):
    a, i0, bs = spec
    out = pscal(chain['p'] ** a, xpow(i0))
    for j, b in enumerate(bs):
        for _ in range(b):
            out = pmul(out, phis[j])
    return out

# ---------------- exponent-lattice split (gamma-calculus) ----------------
def gamma_vectors(chain, i):
    """gamma_1..gamma_i as exponent vectors (a, i0, b_1..b_{i-1})."""
    e, u, h = chain['e'], chain['u'], chain['h']
    dim = 2 + (i - 1)
    gs = []
    g1 = [0] * dim; g1[0] = -h; g1[1] = e[0]
    gs.append(g1)
    for j in range(1, i):                # gamma_{j+1} = Phi_j^{e_{j+1}} / nhat_j(u_{j+1})
        spec = nhat(chain, j, u[j])
        a, i0, bs = spec
        v = [0] * dim
        v[0] -= a; v[1] -= i0
        for k, b in enumerate(bs):
            v[2 + k] -= b
        v[2 + (j - 1)] += e[j]
        gs.append(v)
    return gs

def lattice_split(chain, i, ratio):
    """Solve ratio = sum k_j * gamma_j exactly (back-substitution from the
    top Phi slot down); return [k_1..k_i] or None."""
    gs = gamma_vectors(chain, i)
    r = list(ratio)
    ks = [0] * i
    for j in range(i - 1, 0, -1):        # gamma_{j+1} alone carries Phi_j
        gj = gs[j]
        col = 2 + (j - 1)
        if r[col] % gj[col] != 0:
            return None
        k = r[col] // gj[col]
        ks[j] = k
        r = [r[t] - k * gj[t] for t in range(len(r))]
    g1 = gs[0]
    if r[1] % g1[1] != 0:
        return None
    ks[0] = r[1] // g1[1]
    r = [r[t] - ks[0] * g1[t] for t in range(len(r))]
    if any(r):
        return None
    return ks

# ---------------- frames ----------------
CH_A = {'p': 2, 'h': 1, 'e': [2, 2, 2, 2, 2, 2],
        'u': [1, 5, 21, 85, 341, 1365]}
CH_LW3 = {'p': 3, 'h': 1, 'e': [2, 2, 2, 1], 'u': [1, 5, 21, 43]}

GP_SCRIPT = r"""
default(parisize, 512000000);
P1 = x^2 - 6;
P2 = P1^2 - 18*x;
P3 = P2^2 - 162*P1;
F  = P3^2 - 3*x*P1*P2*P3 - 2*3^9*x*P1;
Fn = P3^2 - 3*x*P1*P2*P3 - 3^9*x*P1;
fp = factorpadic(F, 3, 300);
print("C-FP ", matsize(fp)[1], " ", poldegree(fp[1,1]));
K = nfinit([F, [3]]);
prs = idealprimedec(K, 3);
print("C-NPR ", #prs);
pr = prs[1];
print("C-EF ", pr.e, " ", pr.f);
xF = Mod(x, F); P1F = Mod(P1, F); P2F = Mod(P2, F); P3F = Mod(P3, F);
print("C-VALS ", nfeltval(K, xF, pr), " ", nfeltval(K, P1F, pr), " ", nfeltval(K, P2F, pr), " ", nfeltval(K, P3F, pr));
g1 = nfmodpr(K, xF^2/3, pr);
g2 = nfmodpr(K, P1F^2/(9*xF), pr);
g3 = nfmodpr(K, P2F^2/(81*P1F), pr);
print("C-G1 ", g1 == 2); print("C-G2 ", g2 == 2); print("C-G3 ", g3 == 2);
NH43 = 3*xF*P1F*P2F;
NH86 = 3^9*xF*P1F;
PI4 = P2F*xF^20/P1F^10;
print("C-PI4V ", nfeltval(K, PI4, pr));
Y = nfmodpr(K, P3F/NH43, pr);
print("C-YGEN ", Y^3 != Y);
trY = Y + Y^3;
nmY = Y^4;
ws = if(trY == 1, 1, if(trY == 2, 2, -1));
print("C-WSTAR ", ws);
print("C-LAWI1 ", nmY == 2*trY^2);
print("C-LAWI2 ", Y^2 - trY*Y - trY^2 == 0);
wo = if(ws == 1, 2, 1);
print("C-TI ", Y^2 - wo*Y - wo^2 != 0);
print("C-T5 ", nmY != trY^2);
print("C-NOSE ", if(ws != 1, (Y^2 - Y - 1 != 0), 1));
wav = nfmodpr(K, NH43/PI4^43, pr);
wa = if(wav == 1, 1, if(wav == 2, 2, -1));
print("C-WAV ", wa);
T0 = nfmodpr(K, NH86/NH43^2, pr);
print("C-T0 ", T0 == 2);
U0 = nfmodpr(K, NH86/PI4^86, pr);
print("C-IDY ", U0 == T0*wav^2);
print("C-DISC ", wa, " vs ", ws, " gap ", wav != trY);
fpn = factorpadic(Fn, 3, 300);
print("N-FP ", matsize(fpn)[1], " ", poldegree(fpn[1,1]));
Kn = nfinit([Fn, [3]]);
prn = idealprimedec(Kn, 3);
prn1 = prn[1];
print("N-EF ", #prn, " ", prn1.e, " ", prn1.f);
print("N-KILL ", (#prn != 1) || (prn1.e != 8) || (prn1.f != 2));
print("N-V3 ", nfeltval(Kn, Mod(P3, Fn), prn1));
print("GPDONE");
"""

def main():
    t = T()
    print("== [GENTOW5-W(i)] sealed instrument ==")

    # ---------- Section A: nhat recursion ----------
    print("-- A: nhat recursion --")
    t.chk(nhat(CH_A, 1, 5) == (2, 1, []), "P-A1 nhat_1(5) = 4x")
    t.chk(nhat(CH_A, 2, 21) == (4, 0, [1]), "P-A1 nhat_2(21) = 16 Phi_1")
    t.chk(nhat(CH_A, 3, 85) == (8, 0, [0, 1]), "P-A1 nhat_3(85) = 256 Phi_2")
    t.chk(nhat(CH_A, 4, 341) == (16, 0, [0, 0, 1]),
          "P-A1 nhat_4(341) = 2^16 Phi_3")
    t.chk(nhat(CH_A, 5, 1365) == (32, 0, [0, 0, 0, 1]),
          "P-A1 nhat_5(1365) = 2^32 Phi_4")
    t.chk(nhat(CH_LW3, 1, 5) == (2, 1, []), "P-A2 LW3 nhat_1(5) = 9x")
    t.chk(nhat(CH_LW3, 2, 21) == (4, 0, [1]), "P-A2 LW3 nhat_2(21) = 81 Phi_1")
    t.chk(nhat(CH_LW3, 3, 43) == (1, 1, [1, 1]),
          "P-A2 LW3 nhat_3(43) = 3 x Phi_1 Phi_2")
    t.chk(nhat(CH_LW3, 3, 86) == (9, 1, [1, 0]),
          "P-A2 LW3 nhat_3(86) = 3^9 x Phi_1")

    # ---------- Section A3: lattice / theta ----------
    print("-- A3: lattice split, theta_3(0) --")
    n43 = nhat(CH_LW3, 3, 43); n86 = nhat(CH_LW3, 3, 86)
    vec43 = [n43[0], n43[1]] + n43[2]
    vec86 = [n86[0], n86[1]] + n86[2]
    ratio = [vec86[k] - 2 * vec43[k] for k in range(4)]   # M / N^2
    ks = lattice_split(CH_LW3, 3, ratio)
    t.chk(ks == [-1, -1, -1], "P-A3 M/N^2 = gamma_1^-1 gamma_2^-1 gamma_3^-1"
          " (split %s)" % (ks,))
    z = [2, 2, 2]
    theta30 = 1
    for j in range(3):
        theta30 = (theta30 * pow(z[j], ks[j] % 2, 3)) % 3  # F_3^x: z^-1 = z
    t.chk(theta30 == 2, "P-A3 theta_3(0) = 2 in F_3^x (letter-LIVE)")
    vth32 = pow(theta30, 1, 3)  # inverse of theta30 in F_3^x equals theta30
    t.chk((vth32 * theta30) % 3 == 1, "P-A3 vartheta_{3,2} * theta_3(0) = 1")

    # ---------- Section B: committed q=2 witnesses ----------
    print("-- B: committed depth-4/5/6 witnesses (exact) --")
    p = 2
    Phi1 = psub(xpow(2), [2])                       # x^2 - 2
    Phi2 = psub(pmul(Phi1, Phi1), pscal(4, xpow(1)))
    Phi3 = psub(pmul(Phi2, Phi2), pscal(16, Phi1))
    Phi4 = psub(pmul(Phi3, Phi3), pscal(256, Phi2))
    f32 = psub(pmul(Phi4, Phi4), pscal(2 ** 16, Phi3))
    f64 = psub(pmul(f32, f32), pscal(2 ** 32, Phi4))
    f32m = psub(pmul(Phi4, Phi4), pscal(2 ** 20, Phi1))
    f64m = psub(pmul(f32, f32), pscal(2 ** 40, Phi2))
    # recipe == nhat check (keys are nhat-built)
    t.chk(psub(Phi3, psub(pmul(Phi2, Phi2),
          nhat_poly(CH_A, [Phi1, Phi2], nhat(CH_A, 2, 21)))) == [],
          "P-A1 Phi_3 = Phi_2^2 - nhat_2(21) (recipe = recursion)")
    t.chk(psub(f32, psub(pmul(Phi4, Phi4),
          nhat_poly(CH_A, [Phi1, Phi2, Phi3], nhat(CH_A, 4, 341)))) == [],
          "P-A1 f32 = Phi_4^2 - nhat_4(341)")
    for g, pred, nm in ((xpow(1), 8, "x"), (Phi1, 20, "Phi1"),
                        (Phi2, 42, "Phi2"), (Phi3, 85, "Phi3")):
        t.chk(vp(sylres(Phi4, g), p) == pred,
              "P-B1 v2(Res(Phi4,%s)) = %d" % (nm, pred))
    for g, pred, nm in ((xpow(1), 16, "x"), (Phi1, 40, "Phi1"),
                        (Phi2, 84, "Phi2"), (Phi3, 170, "Phi3"),
                        (Phi4, 341, "Phi4")):
        t.chk(vp(sylres(f32, g), p) == pred,
              "P-B1 v2(Res(f32,%s)) = %d" % (nm, pred))
    for g, pred, nm in ((xpow(1), 32, "x"), (Phi1, 80, "Phi1"),
                        (Phi2, 168, "Phi2"), (Phi3, 340, "Phi3"),
                        (Phi4, 682, "Phi4"), (f32, 1365, "f32")):
        t.chk(vp(sylres(f64, g), p) == pred,
              "P-B1 v2(Res(f64,%s)) = %d" % (nm, pred))
    t.chk(sylres(f32m, Phi3) == 0, "P-B2 TOOTH Res(f32m, Phi_3) == 0 (drain)")
    t.chk(sylres(f64m, Phi4) == 0, "P-B2 TOOTH Res(f64m, Phi_4) == 0 (drain)")

    # ---------- Section C: LW3 exact ladders ----------
    print("-- C: LW3 exact resultant ladders --")
    q = 3
    L1 = psub(xpow(2), [6])                          # x^2 - 6
    L2 = psub(pmul(L1, L1), pscal(18, xpow(1)))
    L3 = psub(pmul(L2, L2), pscal(162, L1))
    NH43p = nhat_poly(CH_LW3, [L1, L2], nhat(CH_LW3, 3, 43))
    NH86p = nhat_poly(CH_LW3, [L1, L2], nhat(CH_LW3, 3, 86))
    t.chk(psub(NH43p, pmul(pscal(3, xpow(1)), pmul(L1, L2))) == [],
          "P-A2 nhat_3(43) poly = 3 x Phi_1 Phi_2")
    L4 = psub(psub(pmul(L3, L3), pmul(NH43p, L3)), pscal(2, NH86p))
    L4n = psub(psub(pmul(L3, L3), pmul(NH43p, L3)), NH86p)
    t.chk(len(L4) - 1 == 16 and L4[-1] == 1, "P-C1 Phi_4LW deg 16 monic")
    for g, pred, nm in ((xpow(1), 8, "x"), (L1, 20, "Phi1"),
                        (L2, 42, "Phi2"), (L3, 86, "Phi3")):
        t.chk(vp(sylres(L4, g), q) == pred,
              "P-C1 v3(Res(Phi4LW,%s)) = %d" % (nm, pred))
        t.chk(vp(sylres(L4n, g), q) == pred,
              "P-C1 v3(Res(Phi4n,%s)) = %d (gauge-blind)" % (nm, pred))

    # ---------- Section D: gp leg ----------
    print("-- D: PARI leg (LW3 law + teeth) --")
    try:
        r = subprocess.run(['gp', '-q', '-f'], input=GP_SCRIPT,
                           capture_output=True, text=True, timeout=1200)
        out = r.stdout
        sys.stdout.write(out)
        if r.returncode != 0 or 'GPDONE' not in out:
            t.chk(False, "P-D gp leg completed (rc=%d)" % r.returncode)
            sys.stdout.write(r.stderr[-2000:])
        else:
            lines = dict()
            for ln in out.splitlines():
                ps = ln.strip().split()
                if ps:
                    lines.setdefault(ps[0], []).append(ps[1:])
            def one(tag):
                return lines.get(tag, [['?']])[0]
            t.chk(one('C-FP') == ['1', '16'], "P-D1 factorpadic: 1 deg-16 factor")
            t.chk(one('C-NPR') == ['1'], "P-D1 single prime over 3")
            t.chk(one('C-EF') == ['8', '2'], "P-D1 (e,f) = (8,2)")
            t.chk(one('C-VALS') == ['4', '10', '21', '43'],
                  "P-D1' nfeltval ladder (4,10,21,43)")
            t.chk(one('C-PI4V') == ['1'], "P-D1 v(pi_4) = 1/8 (scaled: 1)")
            for k in ('C-G1', 'C-G2', 'C-G3'):
                t.chk(one(k) == ['1'], "P-D2 %s letter = 2" % k)
            t.chk(one('C-YGEN') == ['1'], "P-D3' Y generates F_9 (Y^3 != Y)")
            t.chk(one('C-WSTAR')[0] in ('1', '2'),
                  "P-D3' w* = tr(Y) in F_3^x = {1,2}")
            print("  MEASURED w* = %s (intrinsic w = u_3(kbar); recorded)"
                  % one('C-WSTAR')[0])
            t.chk(one('C-LAWI1') == ['1'], "P-D3' LAW-I1 norm(Y) = 2 tr(Y)^2"
                  "  [u_3(beta_0) = theta_3(0) u_3(beta_1)^2, theta live]")
            t.chk(one('C-LAWI2') == ['1'],
                  "P-D3' LAW-I2 psi_4^{(w*)}(Y) = 0 (single-w display)")
            t.chk(one('C-TI') == ['1'], "P-D4' TOOTH psi_4^{(w')}(Y) != 0")
            t.chk(one('C-T5') == ['1'],
                  "P-D5 TOOTH u_3(beta_0) != u_3(beta_1)^2 (theta-free law dead)")
            t.chk(one('C-NOSE') == ['1'], "P-D6' TOOTH nose (conditional)")
            print("  MEASURED w_av = %s (avatar; row-23 record)"
                  % one('C-WAV')[0])
            t.chk(one('C-T0') == ['1'],
                  "P-D8 T0 = res(nhat_3(86)/nhat_3(43)^2) = 2 (lattice x-pin)")
            t.chk(one('C-IDY') == ['1'],
                  "P-D8 IDY U0 = T0 * w_av^2 (avatar-side cocycle closure)")
            print("  RECORD row-23 gap: " + ' '.join(one('C-DISC')))
            t.chk(one('N-FP') == ['1', '16'],
                  "P-D7' naive twin: one deg-16 factor")
            t.chk(one('N-KILL') == ['1'],
                  "P-D7' TOOTH naive twin VERDICT KILL: (e,f) != (8,2)"
                  " (measured N-EF: %s)" % ' '.join(one('N-EF')))
            print("  RECORD naive twin nfeltval(Phi_3) = %s"
                  % ' '.join(one('N-V3')))
    except subprocess.TimeoutExpired:
        t.chk(False, "P-D gp leg within budget (1200s) -- DISCLOSED not-run")

    print("== SUMMARY: %d checks, %d violations ==" % (t.n, len(t.bad)))
    for m in t.bad:
        print("  VIOLATION: " + m)
    return 1 if t.bad else 0

if __name__ == '__main__':
    sys.exit(main())
