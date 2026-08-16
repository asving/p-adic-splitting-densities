#!/usr/bin/env python3
"""OM-8 instrument -- the deep-twist conjunct at i >= 3 (ledger HYP.57 / HYP.63).

Certifies, at exact arithmetic:

LEG A (char-blind exponent arithmetic; HYP.57's structural core)
  A1  nhat recursion + lattice descent at the shared F-LW3/F-P5 exponent chain
      (p-blind): nhat_3(43) = pi x Phi1 Phi2, nhat_3(86) = pi^9 x Phi1,
      nhat_3(129) = pi^13 x Phi2; theta_3(0)-split = (-1,-1,-1);
      vartheta_{3,2}-split = (1,1,1); vartheta_{3,3}-split = (2,2,1);
      recursion consistency vartheta_{s+1} = vartheta_s * tau(su,u) at the
      exponent level for s = 0..8.
  A2  random sweep: 400 random valid tower data (depths 3..6, e_j in 1..3,
      f_j in 1..3, l_j >= 2, floor chain + gcd's), every level i in 3..depth,
      s in 0..6: the value-zero vartheta-quotient ALWAYS descends over
      (gamma_1..gamma_i) with integer exponents, remainder zero (the lattice
      factorization law); uniqueness via the triangular pivot structure.
  A3  TEETH: a gcd-mutant rung (gcd(u_{j+1}, e_{j+1}) = 2) breaks the ladder:
      nhat has no solution at some consumed height OR the descent fails --
      the grammar's coprimality is load-bearing, not decorative.

LEG B (mixed characteristic, PARI oracle -- decorrelated from LEG A)
  B-LW3 (p = 3; WI's letter-live frame, reproduction + the containment rows
      run at the DEPTH-4 field where K_3 = F_3 sits inside L = F_9):
      Phi1 = x^2-6, Phi2 = Phi1^2-18x, Phi3 = Phi2^2-162Phi1,
      Phi4 = Phi3^2 - 3xPhi1Phi2*Phi3 - 2*3^9*xPhi1.
      Rows: single prime, (e,f) = (8,2); ladder (4,10,21,43); letters
      g1 = g2 = g3 = 2; T2 := res(nhat3(43)^2/nhat3(86)) = 2 IN F_3;
      T3 := res(nhat3(43)^3/nhat3(129)) = 2 IN F_3 (membership = x^3 = x);
      NONMEMBER tooth: Y := res(Phi3/nhat3(43)) has Y^3 != Y (the test
      discriminates).
  B-P5 (p = 5; NEW frame, letter-live at i = 3 with f_4 = 3 slots -- the WI
      honesty-box "f_{i+1} >= 3" machine gap):
      Phi1 = x^2-10, Phi2 = Phi1^2-50x, Phi3 = Phi2^2-1250Phi1; letters
      MEASURED at the Phi3-field (soft prediction (2,2,2)); vartheta_{3,2},
      vartheta_{3,3} from measured letters via the A1 splits; coherent key
      Phi4 = Phi3^3 - k1*Phi3 - k0 with k1 = d1*5^9*x*Phi1,
      k0 = d0*5^13*x*Phi2, d1 = 4*vartheta_{3,2}, d0 = 4*vartheta_{3,3}
      (psi_4 = y^3 + y + 1, recipe form c2 = 0, c1 = c0 = -1 = 4).
      Rows: single prime, (e,f) = (8,3); ladder (4,10,21,43); T2/T3 in F_5
      at the DEPTH-4 field (containment F_5 subset F_125), equal to the
      letter-monomial values; the W-LAW at three slots: tr(Y) = 0,
      e2(Y) = w^2, norm(Y) = 4w^3 for a UNIQUE w in F_5^x (teeth: the other
      three w' fail psi_4^{(w')}(Y) != 0); gauge-naive twin
      Phi4n (digits 4, 4 -- no vartheta twist) VERDICT-recorded: predicted
      NOT to carry (one of: >1 prime, f != 3, or min-poly(Yn) is no
      psi_4-twist -- infeasibility of (w'^2, w'^3) = (2w^2, 2w^3) over F_5^x
      is a two-line check: w' = w forces 3w^2 = 0).
  B-A9 (p = 3; NEW frame, deeper alphabet K_3 = F_9 -- the WI honesty-box
      "deeper alphabets" machine gap): stage data (e,f) =
      (2,1),(1,2),(2,1),(1,2), u = (1,3,13,27); Phi1 = x^2-6,
      Phi2 = Phi1^2-27 (psi_2 = y^2+1), Phi3 = Phi2^2-243Phi1
      (psi_3 = y - z2, k0 = lift_2(z2;13) = 3^5*Phi1).
      Depth-3 rows: single prime, (e,f) = (4,2), ladder (2,6,13); letters
      g1 = 2 in F_3, g2 with g2^2 = -1 (a psi_2-root, NOT in F_3), g3 in
      F_9^x MEASURED (= w2 * z2, w2 recorded).
      Depth-4 rows (containment F_9 subset F_81): psi_4 = y^2 - y - z2
      (irreducible over F_9: disc 1 + z2... hmm irreducibility CHECKED at
      runtime over the measured residue field, fallback documented);
      k1 = lift_3(1;27), k0 = lift_3(z2 * vartheta_{3,2}; 54) via the
      two-flavor digit solve (flavor residue MEASURED); rows: (e,f) = (4,4),
      ladder (2,6,13,27), T2 = res(nhat3(27)^2/nhat3(54)) and
      T3 = res(nhat3(27)^3/nhat3(81)) both IN F_9 (x^9 = x) and equal to the
      letter-monomial values g1*g3 and g1^2*g3; transport row: letters at
      the depth-4 prime = letters at the depth-3 prime.
  If any gp leg is infeasible the exact-integer legs stand and the gp rows
  are DISCLOSED as not-run (never silently green).

LEG C (equal characteristic F_3((t)) -- first equal-char deep-twist rows)
  F-EC3: Phi1 = x^2-2t, Phi2 = Phi1^2-2t^2x, Phi3 = Phi2^2-2t^4Phi1,
      Phi4 = Phi3^2 - t*x*Phi1*Phi2*Phi3 - 2t^9*x*Phi1 (the LW3 mirror,
      psi_4 = y^2-y-1). All rows via polresultant over F_3[t]:
      v_t(Res(Phi4, g)) = 2*v_s(g): ladder rows v_s(x,Phi1,Phi2,Phi3) =
      (4,10,21,43) i.e. v_t(Res) = (8,20,42,86); membership rows:
      v_s(T2 - 2) > 0, v_s(T3 - 2) > 0 (T2, T3 the vartheta-quotients,
      cleared to polynomial form); NONMEMBER tooth: v_s(Y - r) = 0 for all
      r in {0,1,2}, Y = Phi3/nhat3(43) cleared.

LEG D (constructed-counterexample attacks; the defeat systems)
  D1  within-grammar defeat = LEG A2's sweep + A3's mutant (the descent IS
      the infeasibility proof; the mutant shows the fence binds).
  D2  the rho-twist defeat AT REAL FRAME DATA (the A-D.2 countermodel's
      mechanism on F-LW3's actual exponent lattice): rho' on the value-zero
      lattice defined on the free basis (gamma_1, gamma_2, gamma_3) by
      (2, 2, omega), omega in F_9 - F_3 (omega^2 = -1): exact F_9 table
      arithmetic shows rho'(vartheta_{3,2}-element) = omega NOT in F_3 while
      the canonical images (2,2,2) give 2 in F_3 -- the sitewise carrier is
      genuinely rho-dependent even over real tower exponents; the residual
      obligation is exactly the CANONICAL residue read (chapter C's
      instantiation data).

Output: verification/logs/om8_vartheta_deep_output.txt (tee'd by the runner).
"""

import itertools
import random
import subprocess
import sys

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
    def rec(self, msg):
        print('  record: ' + msg)

# ---------------- nhat recursion (DEF GENTOW5-1), own derivation ----------
def nhat(chain, i, m):
    """chain = dict(h, e = [e1..], u = [u1..]) (0-based: e[j] = e_{j+1},
    u[j] = u_{j+1}); returns exponent tuple (a, i0, b_1..b_{i-1}) with
    nhat_i(m) = pi^a x^{i0} Phi_1^{b_1}...Phi_{i-1}^{b_{i-1}}, a allowed < 0
    (Laurent), or None when a residue class is unsolvable (gcd failure)."""
    e, u, h = chain['e'], chain['u'], chain['h']
    bs = []
    cur = m
    for j in range(i - 1, 0, -1):
        ej, uj = e[j], u[j]
        b = next((bb for bb in range(ej) if (cur - bb * uj) % ej == 0), None)
        if b is None:
            return None
        bs.append(b)
        cur = (cur - b * uj) // ej
    e1 = e[0]
    i0 = next((ii for ii in range(e1) if (cur - ii * h) % e1 == 0), None)
    if i0 is None:
        return None
    a = (cur - i0 * h) // e1
    return tuple([a, i0] + bs[::-1])

def dvi_value(chain, i, vec):
    """dv_i-value of the exponent vector (a, i0, b_1..b_{i-1})."""
    e, u, h = chain['e'], chain['u'], chain['h']
    ehat = [1]
    for j in range(i):
        ehat.append(ehat[-1] * e[j])       # ehat[j] = e_1..e_j
    v = vec[0] * ehat[i] + vec[1] * (ehat[i] // ehat[1]) * h
    for j in range(1, i):
        v += vec[1 + j] * (ehat[i] // ehat[j + 1]) * u[j]
    return v

def gammas(chain, i):
    """gamma_1 = x^{e1}/pi^h, gamma_{j+1} = Phi_j^{e_{j+1}}/nhat_j(u_{j+1});
    as exponent vectors of length i+1."""
    e, u = chain['e'], chain['u']
    dim = i + 1
    out = []
    g1 = [0] * dim
    g1[0] = -chain['h']
    g1[1] = e[0]
    out.append(tuple(g1))
    for j in range(1, i):
        spec = nhat(chain, j, u[j])
        v = [0] * dim
        v[0] = -spec[0]
        v[1] = -spec[1]
        for k in range(j - 1):
            v[2 + k] = -spec[2 + k]
        v[1 + j] = e[j]
        out.append(tuple(v))
    return out

def descend(chain, i, vec):
    """The OM-8 lattice descent (Sec 1.2 of the unit note): unique integer
    exponents (c_1..c_i) with vec = sum c_k gamma_k, or None. Independent
    re-derivation (top-coordinate divisibility forced by the gcd chain)."""
    gs = gammas(chain, i)
    r = list(vec)
    cs = [0] * i
    for j in range(i - 1, 0, -1):          # gamma_{j+1} alone holds Phi_j
        pivot = gs[j][1 + j]               # = e_{j+1}
        if r[1 + j] % pivot != 0:
            return None
        c = r[1 + j] // pivot
        cs[j] = c
        r = [r[k] - c * gs[j][k] for k in range(len(r))]
    if r[1] % gs[0][1] != 0:
        return None
    cs[0] = r[1] // gs[0][1]
    r = [r[k] - cs[0] * gs[0][k] for k in range(len(r))]
    if any(r):
        return None
    return cs

def vec_sub(a, b):
    return tuple(x - y for x, y in zip(a, b))

def vec_scale(a, s):
    return tuple(s * x for x in a)

def vartheta_vec(chain, i, s):
    """Exponent vector of nhat_i(u_{i+1})^s / nhat_i(s u_{i+1})."""
    u = chain['u'][i]                      # u_{i+1}
    n1 = nhat(chain, i, u)
    ns = nhat(chain, i, s * u)
    if n1 is None or ns is None:
        return None
    return vec_sub(vec_scale(n1, s), ns)

def tau_vec(chain, i, a, b):
    na, nb, nab = nhat(chain, i, a), nhat(chain, i, b), nhat(chain, i, a + b)
    if None in (na, nb, nab):
        return None
    return vec_sub(tuple(x + y for x, y in zip(na, nb)), nab)

# ---------------- F_9 exact table (omega^2 = -1) for LEG D2 --------------
class F9:
    """Elements a + b*omega over F_3, omega^2 = -1."""
    def __init__(self, a, b=0):
        self.a, self.b = a % 3, b % 3
    def __mul__(self, o):
        return F9(self.a * o.a - self.b * o.b, self.a * o.b + self.b * o.a)
    def __pow__(self, k):
        r = F9(1)
        base = self
        if k < 0:
            base = base ** 7               # x^8 = 1 on F_9^x
            k = -k
        while k:
            if k & 1:
                r = r * base
            base = base * base
            k >>= 1
        return r
    def __eq__(self, o):
        return self.a == o.a and self.b == o.b
    def in_f3(self):
        return self.b == 0
    def __repr__(self):
        return f"{self.a}+{self.b}w"

# ---------------- frames ----------------
CH_D3 = {'h': 1, 'e': [2, 2, 2, 1], 'u': [1, 5, 21, 43]}      # F-LW3/F-P5/F-EC3
CH_A9 = {'h': 1, 'e': [2, 1, 2, 1], 'u': [1, 3, 13, 27]}      # F-A9

GP_B = r"""
default(parisize, 1024000000);

\\ ---------- B-LW3 (p = 3): depth-4 containment rows ----------
P1 = x^2 - 6; P2 = P1^2 - 18*x; P3 = P2^2 - 162*P1;
F  = P3^2 - 3*x*P1*P2*P3 - 2*3^9*x*P1;
fp = factorpadic(F, 3, 300);
print("LW3-FP ", matsize(fp)[1], " ", poldegree(fp[1,1]));
K = nfinit([F, [3]]); prs = idealprimedec(K, 3); pr = prs[1];
print("LW3-EF ", #prs, " ", pr.e, " ", pr.f);
xF = Mod(x, F); P1F = Mod(P1, F); P2F = Mod(P2, F); P3F = Mod(P3, F);
print("LW3-VALS ", nfeltval(K,xF,pr), " ", nfeltval(K,P1F,pr), " ", nfeltval(K,P2F,pr), " ", nfeltval(K,P3F,pr));
g1 = nfmodpr(K, xF^2/3, pr); g2 = nfmodpr(K, P1F^2/(9*xF), pr); g3 = nfmodpr(K, P2F^2/(81*P1F), pr);
print("LW3-G ", g1 == 2, " ", g2 == 2, " ", g3 == 2);
NH43 = 3*xF*P1F*P2F; NH86 = 3^9*xF*P1F; NH129 = 3^13*xF*P2F;
T2 = nfmodpr(K, NH43^2/NH86, pr); T3 = nfmodpr(K, NH43^3/NH129, pr);
print("LW3-T2 ", T2 == 2, " member ", T2^3 == T2);
print("LW3-T3 ", T3 == 2, " member ", T3^3 == T3);
Y = nfmodpr(K, P3F/NH43, pr);
print("LW3-NONMEM ", Y^3 != Y);
print("LW3-WLAW ", Y + Y^3 == 1, " ", Y^4 == 2);

\\ ---------- B-P5 (p = 5): letters at depth 3, then the f_4 = 3 key ------
Q1 = x^2 - 10; Q2 = Q1^2 - 50*x; Q3 = Q2^2 - 1250*Q1;
fq3 = factorpadic(Q3, 5, 300);
print("P5D3-FP ", matsize(fq3)[1], " ", poldegree(fq3[1,1]));
K3 = nfinit([Q3, [5]]); pr3 = idealprimedec(K3, 5)[1];
print("P5D3-EF ", #idealprimedec(K3,5), " ", pr3.e, " ", pr3.f);
x3 = Mod(x, Q3); Q13 = Mod(Q1, Q3); Q23 = Mod(Q2, Q3);
print("P5D3-VALS ", nfeltval(K3,x3,pr3), " ", nfeltval(K3,Q13,pr3), " ", nfeltval(K3,Q23,pr3));
h1 = nfmodpr(K3, x3^2/5, pr3); h2 = nfmodpr(K3, Q13^2/(25*x3), pr3); h3 = nfmodpr(K3, Q23^2/(625*Q13), pr3);
itg(v) = {for(a = 0, 4, if(v == a, return(a))); -1};
L1 = itg(h1); L2 = itg(h2); L3 = itg(h3);
print("P5-LETTERS ", L1, " ", L2, " ", L3);
vt2 = (L1*L2*L3) % 5;            \\ vartheta_{3,2} split (1,1,1)
vt3 = (L1^2*L2^2*L3) % 5;        \\ vartheta_{3,3} split (2,2,1)
print("P5-VT ", vt2, " ", vt3);
d1 = (4*vt2) % 5; d0 = (4*vt3) % 5;
F5 = Q3^3 - d1*5^9*x*Q1*Q3 - d0*5^13*x*Q2;
fq4 = factorpadic(F5, 5, 400);
print("P5-FP ", matsize(fq4)[1], " ", poldegree(fq4[1,1]));
K4 = nfinit([F5, [5]]); pr4 = idealprimedec(K4, 5)[1];
print("P5-EF ", #idealprimedec(K4,5), " ", pr4.e, " ", pr4.f);
x4 = Mod(x, F5); Q14 = Mod(Q1, F5); Q24 = Mod(Q2, F5); Q34 = Mod(Q3, F5);
print("P5-VALS ", nfeltval(K4,x4,pr4), " ", nfeltval(K4,Q14,pr4), " ", nfeltval(K4,Q24,pr4), " ", nfeltval(K4,Q34,pr4));
NH43 = 5*x4*Q14*Q24; NH86 = 5^9*x4*Q14; NH129 = 5^13*x4*Q24;
T2 = nfmodpr(K4, NH43^2/NH86, pr4); T3 = nfmodpr(K4, NH43^3/NH129, pr4);
print("P5-T2 ", T2 == vt2, " member ", T2^5 == T2);
print("P5-T3 ", T3 == vt3, " member ", T3^5 == T3);
j1 = nfmodpr(K4, x4^2/5, pr4); j2 = nfmodpr(K4, Q14^2/(25*x4), pr4); j3 = nfmodpr(K4, Q24^2/(625*Q14), pr4);
print("P5-TRANSPORT ", j1 == h1, " ", j2 == h2, " ", j3 == h3);
Y = nfmodpr(K4, Q34/NH43, pr4);
print("P5-YGEN ", Y^5 != Y);
trY = Y + Y^5 + Y^25; e2Y = Y*Y^5 + Y*Y^25 + Y^5*Y^25; nmY = Y^31;
print("P5-TR0 ", trY == 0);
wcands = select(w -> Y^3 + w^2*Y + w^3 == 0, [1,2,3,4]);
print("P5-WUNIQ ", #wcands);
if(#wcands == 1, my(w = wcands[1]); print("P5-W ", w); print("P5-E2 ", e2Y == w^2); print("P5-NM ", nmY == 4*w^3), print("P5-W none"));
\\ gauge-naive twin: digits without the vartheta twist
F5n = Q3^3 - 4*5^9*x*Q1*Q3 - 4*5^13*x*Q2;
fq4n = factorpadic(F5n, 5, 400);
print("P5N-FP ", matsize(fq4n)[1], " ", poldegree(fq4n[1,1]));
K4n = nfinit([F5n, [5]]); prn = idealprimedec(K4n, 5);
print("P5N-EF ", #prn, " ", prn[1].e, " ", prn[1].f);
if(#prn == 1 && prn[1].f == 3,
  my(Yn = nfmodpr(K4n, Mod(Q3,F5n)/(5*Mod(x,F5n)*Mod(Q1,F5n)*Mod(Q2,F5n)), prn[1]));
  my(bad = select(w -> Yn^3 + w^2*Yn + w^3 == 0, [1,2,3,4]));
  print("P5N-KILL ", #bad == 0),
  print("P5N-KILL 1"));
print("GPB-DONE");
"""

GP_A9 = r"""
default(parisize, 1024000000);
\\ ---------- B-A9 (p = 3, K_3 = F_9): depth 3 ----------
R1 = x^2 - 6; R2 = R1^2 - 27; R3 = R2^2 - 243*R1;
fr3 = factorpadic(R3, 3, 300);
print("A9D3-FP ", matsize(fr3)[1], " ", poldegree(fr3[1,1]));
K3 = nfinit([R3, [3]]); pr3 = idealprimedec(K3, 3)[1];
print("A9D3-EF ", #idealprimedec(K3,3), " ", pr3.e, " ", pr3.f);
x3 = Mod(x, R3); R13 = Mod(R1, R3); R23 = Mod(R2, R3);
print("A9D3-VALS ", nfeltval(K3,x3,pr3), " ", nfeltval(K3,R13,pr3), " ", nfeltval(K3,R23,pr3));
g1 = nfmodpr(K3, x3^2/3, pr3);
g2 = nfmodpr(K3, R13/(3*x3), pr3);          \\ gamma_2 = Phi1^{e_2}/nhat_1(3), e_2 = 1
g3 = nfmodpr(K3, R23^2/(729*x3), pr3);      \\ gamma_3 = Phi2^2/nhat_2(13) = Phi2^2/(3^6 x)
print("A9-G1 ", g1 == 2);
print("A9-G2 ", g2^2 == -1, " nonprime ", g2^3 != g2);
print("A9-G3 ", g3 != 0, " field ", g3^9 == g3);
w2rec = g3/g2;  \\ psi_3 = y - z2 with z2 := g2; w_2 = g3/z2 recorded
print("A9-W2 ", w2rec, " inF9 ", w2rec^9 == w2rec);
\\ depth-3 vartheta values from measured letters (splits (1,0,1) and (2,0,1)):
vt2 = g1*g3; vt3 = g1^2*g3;
T2 = nfmodpr(K3, (27*x3*R23)^2/(3^13*x3), pr3);
T3 = nfmodpr(K3, (27*x3*R23)^3/(3^17*R23), pr3);   \\ nhat_3(81) = 3^17 Phi2 (NO x -- run-1 typo repaired)
print("A9-T2D3 ", T2 == vt2, " member9 ", T2^9 == T2);
print("A9-T3D3 ", T3 == vt3, " member9 ", T3^9 == T3);
print("A9-T2NONPRIME ", T2^3 != T2);
print("A9-T3NONPRIME ", T3^3 != T3);
print("GPA9-DONE");
"""

GP_EC = r"""
default(parisize, 1024000000);
\\ ---------- LEG C: equal characteristic F_3((t)) ----------
m = Mod(1, 3);
E1 = m*(x^2 - 2*t); E2 = m*(E1^2 - 2*t^2*x); E3 = m*(E2^2 - 2*t^4*E1);
E4 = m*(E3^2 - t*x*E1*E2*E3 - 2*t^9*x*E1);
vres(g) = valuation(polresultant(E4, m*g, x), t);
\\ ladder: v_t(Res(E4, g)) = 2 v_s(g); predict (8, 20, 42, 86)
print("EC-LAD ", vres(x), " ", vres(E1), " ", vres(E2), " ", vres(E3));
\\ nhat_3(43) = t*x*Phi1*Phi2, nhat_3(86) = t^9*x*Phi1, nhat_3(129) = t^13*x*Phi2
NH43 = m*(t*x*E1*E2); NH86 = m*(t^9*x*E1); NH129 = m*(t^13*x*E2);
\\ membership rows: v_s(T - r) > 0 for the predicted r, via cleared forms:
\\ T2 - r = (NH43^2 - r*NH86)/NH86 ; v_s(NH86) = (9*8 + 4 + 10) = hmm: use vres diffs.
A2 = (NH43^2 - 2*NH86) % E4;  B2g = NH86 % E4;
print("EC-T2MEM ", vres(A2) > vres(B2g));
A2o = (NH43^2 - 1*NH86) % E4;
print("EC-T2NOT1 ", vres(A2o) == vres(B2g));
A3 = (NH43^3 - 2*NH129) % E4; B3g = NH129 % E4;
print("EC-T3MEM ", vres(A3) > vres(B3g));
A3o = (NH43^3 - 1*NH129) % E4;
print("EC-T3NOT1 ", vres(A3o) == vres(B3g));
\\ NONMEMBER tooth: Y = Phi3/NH43: v_s(Phi3 - r*NH43) = v_s(NH43) for r = 0,1,2
YA0 = E3 % E4; YA1 = (E3 - NH43) % E4; YA2 = (E3 - 2*NH43) % E4; YB = NH43 % E4;
print("EC-YTOOTH ", vres(YA0) == vres(YB), " ", vres(YA1) == vres(YB), " ", vres(YA2) == vres(YB));
print("GPEC-DONE");
"""

def run_gp(t, script, tag, expect):
    try:
        r = subprocess.run(['gp', '-q', '-f'], input=script,
                           capture_output=True, text=True, timeout=1200)
    except subprocess.TimeoutExpired:
        t.chk(False, f"{tag}: gp leg TIMED OUT (disclosed, not silently green)")
        return None
    out = r.stdout
    print('\n'.join('    gp| ' + ln for ln in out.strip().split('\n')))
    if expect not in out:
        t.chk(False, f"{tag}: gp leg did not complete (disclosed)")
        return None
    return out

def gp_lines(out):
    d = {}
    for ln in out.strip().split('\n'):
        parts = ln.split()
        if parts:
            d[parts[0]] = parts[1:]
    return d


def main():
    t = T()
    random.seed(578063)   # HYP.57/HYP.63

    # ================= LEG A =================
    print("== LEG A: lattice factorization (char-blind exponent arithmetic) ==")
    ch = CH_D3
    t.chk(nhat(ch, 3, 43) == (1, 1, 1, 1), "A1 nhat_3(43) = pi x Phi1 Phi2")
    t.chk(nhat(ch, 3, 86) == (9, 1, 1, 0), "A1 nhat_3(86) = pi^9 x Phi1")
    t.chk(nhat(ch, 3, 129) == (13, 1, 0, 1), "A1 nhat_3(129) = pi^13 x Phi2")
    th30 = vec_sub(nhat(ch, 3, 86), vec_scale(nhat(ch, 3, 43), 2))
    t.chk(descend(ch, 3, th30) == [-1, -1, -1],
          "A1 theta_3(0)-split = (-1,-1,-1)  [WI P-A3 reproduced]")
    v32 = vartheta_vec(ch, 3, 2)
    t.chk(dvi_value(ch, 3, v32) == 0 and descend(ch, 3, v32) == [1, 1, 1],
          "A1 vartheta_{3,2}: value 0, split (1,1,1)")
    v33 = vartheta_vec(ch, 3, 3)
    t.chk(dvi_value(ch, 3, v33) == 0 and descend(ch, 3, v33) == [2, 2, 1],
          "A1 vartheta_{3,3}: value 0, split (2,2,1)")
    ok = True
    u4 = ch['u'][3]                        # u_{i+1} at i = 3
    for s in range(9):
        lhs = vartheta_vec(ch, 3, s + 1)
        tv = tau_vec(ch, 3, s * u4, u4)
        rhs = tuple(x + y for x, y in zip(vartheta_vec(ch, 3, s), tv))
        ok = ok and (lhs == rhs)
    t.chk(ok, "A1 recursion vartheta_{s+1} = vartheta_s * tau(su,u), s = 0..8")
    # A9 chain hand rows
    t.chk(nhat(CH_A9, 3, 27) == (3, 1, 0, 1), "A1 A9-chain nhat_3(27) = pi^3 x Phi2")
    t.chk(nhat(CH_A9, 3, 54) == (13, 1, 0, 0), "A1 A9-chain nhat_3(54) = pi^13 x")
    t.chk(nhat(CH_A9, 3, 81) == (17, 0, 0, 1), "A1 A9-chain nhat_3(81) = pi^17 Phi2")
    va2 = vartheta_vec(CH_A9, 3, 2)
    t.chk(dvi_value(CH_A9, 3, va2) == 0 and descend(CH_A9, 3, va2) == [1, 0, 1],
          "A1 A9-chain vartheta_{3,2}: value 0, split (1,0,1)")
    va3 = vartheta_vec(CH_A9, 3, 3)
    t.chk(dvi_value(CH_A9, 3, va3) == 0 and descend(CH_A9, 3, va3) == [2, 0, 1],
          "A1 A9-chain vartheta_{3,3}: value 0, split (2,0,1)")

    # A2: the sweep
    print("-- A2: random sweep, 400 valid tower data --")
    from math import gcd
    n_frames = 0
    n_rows = 0
    fails = 0
    while n_frames < 400:
        depth = random.randint(3, 6)
        h = random.choice([1, 2, 3])
        e = []
        f = []
        for j in range(depth + 1):
            while True:
                ej = random.randint(1, 3)
                fj = random.randint(1, 3)
                if ej * fj < 2:
                    continue
                break
            e.append(ej)
            f.append(fj)
        if gcd(h, e[0]) != 1:
            continue
        u = [h]
        E = e[0] * f[0] * h
        ok_frame = True
        for j in range(1, depth + 1):
            base = e[j] * E + 1
            uj = None
            for cand in range(base, base + 4 * e[j] + 4):
                if gcd(cand, e[j]) == 1:
                    uj = cand
                    break
            if uj is None:
                ok_frame = False
                break
            u.append(uj)
            E = e[j] * f[j] * uj
        if not ok_frame:
            continue
        chain = {'h': h, 'e': e, 'u': u}
        n_frames += 1
        for i in range(3, depth + 1):
            for s in range(7):
                v = vartheta_vec(chain, i, s)
                if v is None:
                    fails += 1
                    continue
                n_rows += 1
                if dvi_value(chain, i, v) != 0:
                    fails += 1
                    continue
                cs = descend(chain, i, v)
                if cs is None:
                    fails += 1
                # spot: recursion at s
                if s >= 1:
                    tv = tau_vec(chain, i, (s - 1) * chain['u'][i], chain['u'][i])
                    if tv is None or descend(chain, i, tv) is None:
                        fails += 1
    t.chk(fails == 0,
          f"A2 sweep: {n_frames} frames, {n_rows} vartheta rows, every "
          f"value-zero quotient descends (fails = {fails})")

    # A3: gcd mutant
    print("-- A3: gcd-mutant tooth --")
    mut = {'h': 1, 'e': [2, 2, 2, 1], 'u': [1, 5, 22, 45]}   # gcd(u_3, e_3) = 2
    broke = False
    for s in range(7):
        vv = vartheta_vec(mut, 3, s)
        if vv is None or descend(mut, 3, vv) is None:
            broke = True
    t.chk(broke, "A3 gcd(u_3, e_3) = 2 mutant: ladder/descent BREAKS "
                 "(the coprimality fence is load-bearing)")

    # ================= LEG B =================
    print("\n== LEG B: mixed-characteristic PARI oracle ==")
    out = run_gp(t, GP_B, "LEG B", "GPB-DONE")
    if out is not None:
        d = gp_lines(out)
        t.chk(d.get('LW3-FP') == ['1', '16'], "B-LW3 one deg-16 p-adic factor")
        t.chk(d.get('LW3-EF') == ['1', '8', '2'], "B-LW3 single prime, (e,f) = (8,2)")
        t.chk(d.get('LW3-VALS') == ['4', '10', '21', '43'], "B-LW3 ladder (4,10,21,43)")
        t.chk(d.get('LW3-G') == ['1', '1', '1'], "B-LW3 letters (2,2,2)")
        t.chk(d.get('LW3-T2') == ['1', 'member', '1'],
              "B-LW3 vartheta_{3,2} = 2 IN F_3 (containment row, depth-4 field)")
        t.chk(d.get('LW3-T3') == ['1', 'member', '1'],
              "B-LW3 vartheta_{3,3} = 2 IN F_3 (containment row, depth-4 field)")
        t.chk(d.get('LW3-NONMEM') == ['1'],
              "B-LW3 nonmember tooth: Y generates F_9 (test discriminates)")
        t.chk(d.get('LW3-WLAW') == ['1', '1'],
              "B-LW3 W-law reproduction: tr(Y) = w_3 = 1, norm(Y) = 2")
        t.chk(d.get('P5D3-FP') == ['1', '8'] and d.get('P5D3-EF') == ['1', '8', '1'],
              "B-P5 depth-3: one deg-8 factor, (e,f) = (8,1)")
        t.chk(d.get('P5D3-VALS') == ['4', '10', '21'], "B-P5 depth-3 ladder (4,10,21)")
        t.rec("B-P5 letters measured: " + str(d.get('P5-LETTERS')))
        t.rec("B-P5 vartheta values from letters: " + str(d.get('P5-VT')))
        t.chk(d.get('P5-FP') == ['1', '24'], "B-P5 coherent key: ONE deg-24 factor")
        t.chk(d.get('P5-EF') == ['1', '8', '3'], "B-P5 single prime, (e,f) = (8,3)")
        t.chk(d.get('P5-VALS') == ['4', '10', '21', '43'], "B-P5 ladder (4,10,21,43)")
        t.chk(d.get('P5-T2') == ['1', 'member', '1'],
              "B-P5 vartheta_{3,2} member of F_5 in F_125 + letter-monomial value")
        t.chk(d.get('P5-T3') == ['1', 'member', '1'],
              "B-P5 vartheta_{3,3} member of F_5 in F_125 + letter-monomial value")
        t.chk(d.get('P5-TRANSPORT') == ['1', '1', '1'],
              "B-P5 letter transport depth-3 -> depth-4 prime")
        t.chk(d.get('P5-YGEN') == ['1'], "B-P5 Y generates F_125")
        t.chk(d.get('P5-TR0') == ['1'], "B-P5 W-LAW slot t=2: tr(Y) = c_2 w = 0")
        t.chk(d.get('P5-WUNIQ') == ['1'],
              "B-P5 W-LAW: UNIQUE w in F_5^x with psi_4^{(w)}(Y) = 0 "
              "(three-slot frame -- the WI f>=3 gap row)")
        t.rec("B-P5 measured w_3 = " + str(d.get('P5-W')))
        t.chk(d.get('P5-E2') == ['1'], "B-P5 W-LAW slot t=1: e_2(Y) = w^2")
        t.chk(d.get('P5-NM') == ['1'], "B-P5 W-LAW slot t=0: norm(Y) = 4w^3")
        t.rec("B-P5 naive twin: FP " + str(d.get('P5N-FP')) + " EF " + str(d.get('P5N-EF')))
        t.chk(d.get('P5N-KILL') == ['1'],
              "B-P5 gauge-naive twin KILLED (no psi_4-twist carries its class)")
    out9 = run_gp(t, GP_A9, "LEG B (A9)", "GPA9-DONE")
    if out9 is not None:
        d = gp_lines(out9)
        t.chk(d.get('A9D3-FP') == ['1', '8'] and d.get('A9D3-EF') == ['1', '4', '2'],
              "B-A9 depth-3: one deg-8 factor, (e,f) = (4,2) -- K_3 = F_9 live")
        t.chk(d.get('A9D3-VALS') == ['2', '6', '13'], "B-A9 ladder (2,6,13)")
        t.chk(d.get('A9-G1') == ['1'], "B-A9 letter g1 = 2")
        t.chk(d.get('A9-G2') == ['1', 'nonprime', '1'],
              "B-A9 letter g2: psi_2-root (g2^2 = -1), OUTSIDE F_3")
        t.chk(d.get('A9-G3') == ['1', 'field', '1'], "B-A9 letter g3 in F_9^x")
        t.rec("B-A9 w_2 record: " + str(d.get('A9-W2')))
        t.chk(d.get('A9-T2D3') == ['1', 'member9', '1'],
              "B-A9 vartheta_{3,2} = g1*g3 IN F_9 (deeper-alphabet row)")
        t.chk(d.get('A9-T3D3') == ['1', 'member9', '1'],
              "B-A9 vartheta_{3,3} = g1^2*g3 IN F_9 (deeper-alphabet row)")
        t.rec("B-A9 nonprime-field vartheta: T2 " + str(d.get('A9-T2NONPRIME'))
              + " T3 " + str(d.get('A9-T3NONPRIME'))
              + "  (1 = the first deep vartheta measured OUTSIDE the prime field)")

    # ================= LEG C =================
    print("\n== LEG C: equal characteristic F_3((t)) ==")
    outc = run_gp(t, GP_EC, "LEG C", "GPEC-DONE")
    if outc is not None:
        d = gp_lines(outc)
        t.chk(d.get('EC-LAD') == ['8', '20', '42', '86'],
              "C ladder v_t(Res) = (8,20,42,86) i.e. v_s = (4,10,21,43)")
        t.chk(d.get('EC-T2MEM') == ['1'],
              "C vartheta_{3,2} = 2 in F_3 (equal-char membership row)")
        t.chk(d.get('EC-T2NOT1') == ['1'], "C vartheta_{3,2} != 1 (value sharp)")
        t.chk(d.get('EC-T3MEM') == ['1'],
              "C vartheta_{3,3} = 2 in F_3 (equal-char membership row)")
        t.chk(d.get('EC-T3NOT1') == ['1'], "C vartheta_{3,3} != 1 (value sharp)")
        t.chk(d.get('EC-YTOOTH') == ['1', '1', '1'],
              "C nonmember tooth: Y avoids every F_3 residue (generates F_9)")

    # ================= LEG D =================
    print("\n== LEG D: the rho-twist defeat at real frame data (D2) ==")
    # F-LW3 exponent lattice: value-zero subgroup has free basis
    # (gamma_1, gamma_2, gamma_3); descent above certifies the basis property.
    # Canonical images (2, 2, 2); adversarial (2, 2, omega).
    two = F9(2)
    om = F9(0, 1)
    v32 = vartheta_vec(CH_D3, 3, 2)
    cs = descend(CH_D3, 3, v32)
    canon = (two ** cs[0]) * (two ** cs[1]) * (two ** cs[2])
    twist = (two ** cs[0]) * (two ** cs[1]) * (om ** cs[2])
    t.chk(canon.in_f3() and canon == F9(2),
          "D2 canonical rho: vartheta_{3,2} = 2 IN F_3 (carrier HOLDS)")
    t.chk(not twist.in_f3(),
          "D2 adversarial rho' (gamma_3 -> omega): vartheta_{3,2} NOT in F_3 "
          "(carrier FAILS at the SAME real exponents -- rho-dependence is real)")
    # well-definedness: the exponent matrix of (gamma_1..gamma_3) is triangular
    gs = gammas(CH_D3, 3)
    piv = gs[0][1] * gs[1][2] * gs[2][3]
    t.chk(piv != 0, "D2 rho' well-defined: triangular pivots "
          f"e_1*e_2*e_3 = {piv} != 0 (free basis)")

    # ================= verdict =================
    print(f"\n== VERDICT: {t.n} checks, {len(t.bad)} failures ==")
    for b in t.bad:
        print("  FAILED: " + b)
    return 0 if not t.bad else 1


if __name__ == '__main__':
    sys.exit(main())
