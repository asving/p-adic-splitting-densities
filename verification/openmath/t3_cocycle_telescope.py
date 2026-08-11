#!/usr/bin/env python3
"""t3_cocycle_telescope.py -- SEALED INSTRUMENT for LEMMA COCYCLE-TELESCOPE
(RCT unit T3-cocycle-telescope, CODEX arm; companion note
T3_COCYCLE_TELESCOPE_2026-08-10.md S7 = the composing model's machine plan,
implemented by the lab tech EXACTLY as specified -- protocol
docs/PROVER_RCT_PROTOCOL_2026-08-10.md S3: the tech may not alter
mathematical content; any spec gap hit during implementation is recorded
in the note, not fixed here).

TWO-COMMIT SEAL: this file is committed BEFORE any run with the
preregistered predictions below (verbatim values from note S7).  The run
output (t3_cocycle_telescope_output.txt) and the verdict land in a second
commit.  RED outcomes are kept with diagnosis, never tuned away.  NO smoke
run precedes the seal.  Self-contained: no import from any committed
verification runner (note S7.1 requirement); gp subprocess only for the
stated PARI legs.

SPEC SOURCE (note S7.1-S7.5, CODEX-composed):
  M1 FRAME-C   direct common-carrier frame: p=5, pi=5, e1=2, f1=1, h=1,
               Phi_1=x^2-10, eta=res(x^2/5)=2 in F_5^x; doubled height
               ht(x)=1, ht(5)=2; section N(k)=x^i 5^a, i=k mod 2,
               a=(k-i)/2; formal reference T of height 1 with
               res(x/T)=3, res(x^2/5)=2 (forcing res(5/T^2)=2);
               U(k):=res(N(k)/T^k); q=1, d=0..4.
  M1 FRAME-LW3 direct tower boundary-read port at SOURCE 4's letter-live
               frame: p=3, (e,f)=(2,1),(2,1),(2,1),(1,2), u=(1,5,21,43),
               Phi_1=x^2-6, Phi_2=Phi_1^2-18x, Phi_3=Phi_2^2-162Phi_1,
               Phi_4=Phi_3^2-3xPhi_1Phi_2*Phi_3-2*3^9*xPhi_1.
  M2 LEG-I1    GENTOW2-B'' at LP1 (p=2): nhat_2(19)=4xPhi', nhat_2(38)
               =512x; symbolic mod z_1^3-1 (z_2=1).
  M2 LEG-I2    HETOW-4 fixtures: tau(H_0)=2, delta=2; raw strings
               (2,2,1) and (1,2,2,1); symbolic coefficient identity.
  M2 LEG-I3    GENTOW-6.4 FRAME-P (p=3) NON_INSTANCE_REGRESSION --
               success MUST NOT increment the instantiation count.
  M2 LEG-I4    [GENTOW5-W(i)] at FRAME-LW3, cited ATTEMPT GRADE arc 1/2.
  M3 teeth     T-1..T-4 (all must kill).
  M5           joint-coverage label: the realized-tower cell
               (theta != 1 AND intrinsic w != 1 in one B'' instance) is
               MACHINE-UNEXPLORED and must be printed as such.

PREREGISTERED PREDICTIONS (verbatim from note S7; any miss = RED).
  P-A  FRAME-C section/cocycle: U(0..4)=(1,3,2,1,4); cocycle residues
       res(c_N(k,1)) for k=0..3 = (1,2,1,2); vartheta_d (d=0..4)
       = (1,1,2,2,4) by BOTH recurrence and product formula;
       theta_d = (1,1,3,3,4).
  P-B  FRAME-C boundary: w=U(1)=3; theta_d*w^d = independently computed
       U(d) = (3,2,1,4) at d=1..4; pre-cancellation w^d = U(d)*vartheta_d
       with w^d = (3,4,2,1).
  P-C  FRAME-C comparison: Nhat(k)=x^k; tau(0..6)=(1,1,2,2,4,4,3);
       tau(1)^2=1 != 2=tau(2) (non-character); q=2, H_0=6, A_t=T^(6-2t):
       tau(H_0)=3, delta=2; rho=(2,4,3,1), rhohat=(4,1,4,1);
       R(Z)=2+4Z+3Z^2+Z^3 = 3*Rhat(Z/2) in F_5[Z] coefficientwise;
       bracket telescope Prod_{s<t} c_N(H_{s+1},2) = N(H_t)N(2)^t/N(6)
       as exponent vectors, t=1,2,3.
  P-D  FRAME-LW3: fresh reconstruction nhat_3(43)=3xPhi_1Phi_2,
       nhat_3(86)=3^9xPhi_1 (brute-force UNIQUE in the digit box);
       quotient nhat_3(86)/nhat_3(43)^2 = 3^7/(xPhi_1Phi_2^2)
       = gamma_1^-1 gamma_2^-1 gamma_3^-1 (lattice split (-1,-1,-1));
       gp leg: one deg-16 factor, (e,f)=(8,2), nfeltval ladder
       (4,10,21,43), res(gamma_i)=2 (i=1,2,3), tr(Y)=1, norm(Y)=2;
       boundary conclusion at both slots: theta_3(0)=2, theta_3(1)=1,
       w_3=tr(Y)=1, u_3(beta_1)=1=theta_3(1)*w_3,
       u_3(beta_0)=2=theta_3(0)*w_3^2.
  P-E  per-instance legs:
       I1: res(nhat_2(19)^2/nhat_2(38))=z_1^2 via lattice split (5,1)
           against gamma_1=x^2/2, gamma_2=Phi'^2/x^9; theta(0)=z_1,
           theta(1)=1; LD1: P=y^2+z_1y+z_1 (c_0=1); LD2: P=y^2+z_1y+1
           (c_0=z_1^2); exact symbolic arithmetic mod z_1^3-1, z_2=1.
       I2: raw strings (2,2,1),(1,2,2,1) non-geometric over F_3 AND F_5;
           character-law reconstruction from the first entry fails at a
           later entry; symbolic identity rhohat_t -> rhohat_t*tau(H_0)
           *delta^(-t) == coefficients of tau(H_0)*Rhat(Z/delta), at
           lengths 3 and 4, (tau(H_0),delta)=(2,2).
       I3: FRAME-P pins (26,16,5), c_g=5; digit congruence mod 3^N and
           below-cap pin stability across ambient lifts (N=6, cap
           e1e2*N=24, block cap 24-c_g=19); NON_INSTANCE_REGRESSION.
       I4: FRAME-LW3 values as P-D; recorded at ATTEMPT GRADE arc 1/2.
  T-1  character-law mutant tau(2):=tau(1)^2=1 must fail the exact
       quotient (res(x^2/5)=2) AND the P-C coefficient comparison.
  T-2  theta-free mutant U(d):=w^d: at FRAME-C d=2 predicts 4 vs
       independent U(2)=2; at FRAME-LW3 predicts u_3(beta_0)=1 vs 2.
       BOTH kills must fire.
  T-3  endpoint-as-input probe: feed U_mut(2)=4; pre-cancellation
       w^2=4 vs U_mut(2)*vartheta_2=4*2=3 mod 5; mismatch 4 != 3 must
       be DETECTED as a contradiction (no overwrite from the theorem).
  T-4  inverse-orientation mutant theta_d -> vartheta_d: at d=2
       predicts vartheta_2*w^2=2*4=3 vs U(2)=2; must kill.

REGRESSION LEGS (M4; run OUTSIDE this file, committed runners
unmodified, stdout captured): hetow_r2_hetow4.py (GREEN 203 checks /
37 gp jobs), gentow2_pe6_fresh.py (GREEN 68), gentow6_r1_caplemma.py
(GREEN 303), gentow5_wi_checks.py (GREEN 60).  A regression mismatch is
a T3 verification failure even if this runner is green.
VERDICT: GREEN iff 0 violations here AND all four regressions green.
"""

import subprocess, sys
from fractions import Fraction

# ---------------- checks harness ----------------
NCHK = 0
VIOL = []
def chk(cond, msg):
    global NCHK
    NCHK += 1
    print(('  ok: ' if cond else 'FAIL: ') + msg)
    if not cond:
        VIOL.append(msg)

# ---------------- generic exponent-vector monoid ----------------
def vadd(u, v):
    return tuple(a + b for a, b in zip(u, v))

def vsub(u, v):
    return tuple(a - b for a, b in zip(u, v))

def vscal(c, u):
    return tuple(c * a for a in u)

def vzero(n):
    return tuple([0] * n)

# ---------------- dense integer polynomial kit (fresh) ----------------
def ptrim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a

def pl_add(a, b):
    n = max(len(a), len(b))
    return ptrim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                  for i in range(n)])

def pl_sub(a, b):
    return pl_add(a, [-c for c in b])

def pl_mul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca:
            for j, cb in enumerate(b):
                out[i + j] += ca * cb
    return ptrim(out)

def pl_scal(c, a):
    return ptrim([c * x for x in a])

def pl_x(k):
    return [0] * k + [1]

def pl_divmod_monic(a, b):
    """a = q*b + r with b monic; exact over Z."""
    a = list(a)
    q = []
    while len(a) >= len(b) and a:
        c = a[-1]
        d = len(a) - len(b)
        q = pl_add(q, [0] * d + [c])
        a = pl_sub(a, pl_mul([0] * d + [c], b))
    return q, ptrim(a)

def v_p(n, p):
    """p-adic valuation; None for 0 (= +infinity)."""
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

# =====================================================================
# SECTION 1: FRAME-C (direct common-carrier frame; note S7.1)
# Generators (x, 5, T); vector = (i, a, b) exponents.  ht = i + 2a + b.
# A_0 solve: v = alpha*(x/T) + beta*(x^2/5); (x/T)=(1,0,-1),
# (x^2/5)=(2,-1,0)  =>  beta = -a, alpha = i + 2a, consistency b = -alpha.
# res(v) = 3^alpha * 2^beta in F_5^x.
# =====================================================================
P5 = 5

def C_ht(v):
    return v[0] + 2 * v[1] + v[2]

def C_res(v):
    assert C_ht(v) == 0, "res on nonzero height"
    i, a, b = v
    beta = -a
    alpha = i + 2 * a
    assert b == -alpha, "A_0 solve inconsistent"
    # F_5^x has order 4
    return (pow(3, alpha % 4, P5) * pow(2, beta % 4, P5)) % P5

def C_N(k):
    i = k % 2
    a = (k - i) // 2
    return (i, a, 0)

def C_Nhat(k):
    return (k, 0, 0)

def C_T(k):
    return (0, 0, k)

def frame_C():
    print("== FRAME-C: common-carrier joint frame (p=5) ==")
    # ---- P-A: section table, U(k), cocycles, telescope ----
    predN = {0: (0, 0, 0), 1: (1, 0, 0), 2: (0, 1, 0), 3: (1, 1, 0),
             4: (0, 2, 0)}
    predU = {0: 1, 1: 3, 2: 2, 3: 1, 4: 4}
    for k in range(5):
        chk(C_N(k) == predN[k], "P-A N(%d) exponent vector" % k)
        chk(C_ht(C_N(k)) == k, "P-A ht(N(%d)) = %d" % (k, k))
        u = C_res(vsub(C_N(k), C_T(k)))
        chk(u == predU[k], "P-A U(%d) = %d (got %d)" % (k, predU[k], u))
    chk(C_res((2, -1, 0)) == 2, "P-A res(x^2/5) = 2 (eta)")
    chk(C_res((0, 1, -2)) == 2, "P-A res(5/T^2) = 2 (forced)")
    # cocycles c_N(k,1) = N(k)N(1)/N(k+1), k=0..3
    predc = {0: (0, 0, 0), 1: (2, -1, 0), 2: (0, 0, 0), 3: (2, -1, 0)}
    predcr = {0: 1, 1: 2, 2: 1, 3: 2}
    for k in range(4):
        c = vsub(vadd(C_N(k), C_N(1)), C_N(k + 1))
        chk(c == predc[k], "P-A c_N(%d,1) vector" % k)
        chk(C_res(c) == predcr[k], "P-A res(c_N(%d,1)) = %d" % (k, predcr[k]))
    # vartheta_d = res(N(1)^d / N(d)): recurrence AND product formula
    predvt = {0: 1, 1: 1, 2: 2, 3: 2, 4: 4}
    predth = {0: 1, 1: 1, 2: 3, 3: 3, 4: 4}
    vt_dir = {}
    for d in range(5):
        vt_dir[d] = C_res(vsub(vscal(d, C_N(1)), C_N(d)))
        chk(vt_dir[d] == predvt[d],
            "P-A vartheta_%d = %d (direct)" % (d, predvt[d]))
    vt_rec = 1
    for d in range(4):
        vt_rec = (vt_rec * C_res(vsub(vadd(C_N(d), C_N(1)), C_N(d + 1)))) % P5
        chk(vt_rec == vt_dir[d + 1],
            "P-A recurrence vartheta_%d = vartheta_%d*res(c_N(%d,1))"
            % (d + 1, d, d))
    for d in range(5):
        prod = 1
        for s in range(d):
            prod = (prod * C_res(vsub(vadd(C_N(s), C_N(1)), C_N(s + 1)))) % P5
        chk(prod == vt_dir[d], "P-A product formula at d=%d" % d)
        th = pow(vt_dir[d], 3, P5)  # inverse in F_5^x: t^-1 = t^3
        chk(th == predth[d], "P-A theta_%d = %d" % (d, predth[d]))
    # ---- P-B: boundary-times-monomial ----
    w = C_res(vsub(C_N(1), C_T(1)))
    chk(w == 3, "P-B w = U(1) = 3")
    predUd = {1: 3, 2: 2, 3: 1, 4: 4}
    predwd = {1: 3, 2: 4, 3: 2, 4: 1}
    for d in range(1, 5):
        Ud = C_res(vsub(C_N(d), C_T(d)))     # independent boundary read
        th = pow(vt_dir[d], 3, P5)
        chk((th * pow(w, d, P5)) % P5 == Ud,
            "P-B theta_%d*w^%d = U(%d) = %d" % (d, d, d, predUd[d]))
        chk(Ud == predUd[d], "P-B independent U(%d) = %d" % (d, predUd[d]))
        chk(pow(w, d, P5) == predwd[d], "P-B w^%d = %d" % (d, predwd[d]))
        chk(pow(w, d, P5) == (Ud * vt_dir[d]) % P5,
            "P-B pre-cancellation w^%d = U(%d)*vartheta_%d" % (d, d, d))
    # ---- P-C: assembled-comparison port ----
    predtau = [1, 1, 2, 2, 4, 4, 3]
    tau = {}
    for k in range(7):
        tau[k] = C_res(vsub(C_Nhat(k), C_N(k)))
        chk(tau[k] == predtau[k], "P-C tau(%d) = %d" % (k, predtau[k]))
    chk((tau[1] * tau[1]) % P5 == 1 and tau[2] == 2,
        "P-C non-character: tau(1)^2 = 1 != 2 = tau(2)")
    q, H0, D = 2, 6, 3
    predrho = [2, 4, 3, 1]
    predrhohat = [4, 1, 4, 1]
    rho, rhohat = [], []
    for t in range(D + 1):
        At = C_T(H0 - q * t)
        rv = C_res(vsub(vadd(At, vscal(t, C_N(q))), C_N(H0)))
        rhv = C_res(vsub(vadd(At, vscal(t, C_Nhat(q))), C_Nhat(H0)))
        rho.append(rv)
        rhohat.append(rhv)
        chk(rv == predrho[t], "P-C rho_%d = %d" % (t, predrho[t]))
        chk(rhv == predrhohat[t], "P-C rhohat_%d = %d" % (t, predrhohat[t]))
    tauH0, delta = tau[6], tau[2]
    chk(tauH0 == 3, "P-C tau(H_0) = 3")
    chk(delta == 2, "P-C delta = 2")
    # actual polynomial substitution R(Z) ?= tauH0 * Rhat(Z/delta) in F_5[Z]
    dinv = pow(delta, 3, P5)
    subst = [(tauH0 * rhohat[t] * pow(dinv, t, P5)) % P5 for t in range(D + 1)]
    chk(subst == rho, "P-C R(Z) = 3*Rhat(Z/2) coefficientwise (%s vs %s)"
        % (subst, rho))
    chk(rho == [2, 4, 3, 1], "P-C R(Z) = 2+4Z+3Z^2+Z^3")
    chk(rhohat == [4, 1, 4, 1], "P-C Rhat(Z) = 4+Z+4Z^2+Z^3")
    # bracket telescope as exponent vectors (before residues)
    for t in range(1, D + 1):
        prod = vzero(3)
        for s in range(t):
            Hs1 = H0 - (s + 1) * q
            prod = vadd(prod, vsub(vadd(C_N(Hs1), C_N(q)), C_N(Hs1 + q)))
        rhs = vsub(vadd(C_N(H0 - t * q), vscal(t, C_N(q))), C_N(H0))
        chk(prod == rhs, "P-C bracket telescope t=%d (exponent vectors)" % t)
    return w, vt_dir, tau, rho, rhohat, tauH0, delta

# =====================================================================
# SECTION 2: FRAME-C teeth T-1, T-2(part), T-3, T-4  (note S7.3)
# =====================================================================
def teeth_frame_C(w, vt_dir, tau, rho, rhohat, tauH0, delta):
    print("== TEETH (FRAME-C side) ==")
    # T-1 character-law mutant: tau(2) := tau(1)^2 = 1
    tau2_mut = (tau[1] * tau[1]) % P5
    kill_quot = (tau2_mut != C_res((2, -1, 0)))
    dinv_mut = pow(tau2_mut, 3, P5)
    subst_mut = [(tauH0 * rhohat[t] * pow(dinv_mut, t, P5)) % P5
                 for t in range(4)]
    kill_coeff = (subst_mut != rho)
    chk(kill_quot, "T-1 KILL(a): mutant tau(2)=1 fails exact quotient"
        " res(x^2/5)=2")
    chk(kill_coeff, "T-1 KILL(b): mutant delta=1 fails P-C comparison"
        " (%s vs %s)" % (subst_mut, rho))
    # T-2 theta-free mutant at d=2 (FRAME-C half)
    U2 = C_res(vsub(C_N(2), C_T(2)))
    mut = pow(w, 2, P5)  # theta-free prediction = w^2 = 4
    chk(mut == 4 and U2 == 2 and mut != U2,
        "T-2 KILL (FRAME-C): theta-free predicts 4, independent U(2)=2")
    # T-3 endpoint-as-input vacuity probe: U_mut(2) = 4 fed as input
    U_mut = 4
    lhs = pow(w, 2, P5)                      # peel path: w^2 = 4
    rhs = (U_mut * vt_dir[2]) % P5           # digit path: 4*2 = 3
    chk(lhs == 4 and rhs == 3 and lhs != rhs,
        "T-3 DETECTED: pre-cancellation contradiction 4 != 3 for fed"
        " endpoint U_mut(2)=4 (no overwrite performed)")
    # T-4 inverse-orientation mutant: vartheta_2*w^2 vs U(2)
    pred_mut = (vt_dir[2] * pow(w, 2, P5)) % P5
    chk(pred_mut == 3 and U2 == 2 and pred_mut != U2,
        "T-4 KILL: vartheta-oriented predicts 3, independent U(2)=2")

# =====================================================================
# SECTION 3: FRAME-LW3 (fresh tower boundary-read port; note S7.1)
# Level-3 monomials 3^a x^i0 Phi_1^b1 Phi_2^b2 as vectors (a,i0,b1,b2);
# dv_3 weights (nfeltval scaling of the committed frame): wt(3)=8,
# wt(x)=4, wt(Phi_1)=10, wt(Phi_2)=21.  FRESH ROUTE: brute-force the
# digit box (i0<2, b1<2, b2<2, a>=0) for the UNIQUE normalizer at each
# height -- independent of the committed sequential-solve code.
# =====================================================================
LW3_WT = (8, 4, 10, 21)

def lw3_ht(v):
    return sum(a * b for a, b in zip(v, LW3_WT))

def lw3_solve(m):
    sols = []
    for i0 in range(2):
        for b1 in range(2):
            for b2 in range(2):
                rem = m - 4 * i0 - 10 * b1 - 21 * b2
                if rem >= 0 and rem % 8 == 0:
                    sols.append((rem // 8, i0, b1, b2))
    return sols

# gamma letters at level 3 (value-0 generators), vectors (a,i0,b1,b2):
LW3_G1 = (-1, 2, 0, 0)    # x^2/3
LW3_G2 = (-2, -1, 2, 0)   # Phi_1^2/(9x)
LW3_G3 = (-4, 0, -1, 2)   # Phi_2^2/(81 Phi_1)

def lw3_split(v):
    """v = k1*G1 + k2*G2 + k3*G3, solved top slot down; None if not."""
    k3, r = None, list(v)
    if r[3] % 2:
        return None
    k3 = r[3] // 2
    r = [r[i] - k3 * LW3_G3[i] for i in range(4)]
    if r[2] % 2:
        return None
    k2 = r[2] // 2
    r = [r[i] - k2 * LW3_G2[i] for i in range(4)]
    if r[1] % 2:
        return None
    k1 = r[1] // 2
    r = [r[i] - k1 * LW3_G1[i] for i in range(4)]
    if any(r):
        return None
    return (k1, k2, k3)

LW3_GP = "\n".join([
    "default(parisize, 512000000);",
    "P1 = x^2 - 6;",
    "P2 = P1^2 - 18*x;",
    "P3 = P2^2 - 162*P1;",
    "F = P3^2 - 3*x*P1*P2*P3 - 2*3^9*x*P1;",
    "fp = factorpadic(F, 3, 300);",
    'print("T3FP ", matsize(fp)[1], " ", poldegree(fp[1,1]));',
    "K = nfinit([F, [3]]);",
    "prs = idealprimedec(K, 3);",
    'print("T3NPR ", #prs);',
    "pr = prs[1];",
    'print("T3EF ", pr.e, " ", pr.f);',
    "xF = Mod(x, F); P1F = Mod(P1, F); P2F = Mod(P2, F); P3F = Mod(P3, F);",
    'print("T3VALS ", nfeltval(K, xF, pr), " ", nfeltval(K, P1F, pr),'
    ' " ", nfeltval(K, P2F, pr), " ", nfeltval(K, P3F, pr));',
    "g1 = nfmodpr(K, xF^2/3, pr);",
    "g2 = nfmodpr(K, P1F^2/(9*xF), pr);",
    "g3 = nfmodpr(K, P2F^2/(81*P1F), pr);",
    'print("T3G ", g1 == 2, " ", g2 == 2, " ", g3 == 2);',
    "NH43 = 3*xF*P1F*P2F;",
    "Y = nfmodpr(K, P3F/NH43, pr);",
    'print("T3YGEN ", Y^3 != Y);',
    "trY = Y + Y^3;",
    "nmY = Y^4;",
    'print("T3TR ", trY == 1);',
    'print("T3NM ", nmY == 2);',
    'print("T3LAW0 ", nmY == 2*trY^2);',
    'print("T3T2LW ", nmY != trY^2);',
    'print("T3DONE");'])

def frame_LW3():
    print("== FRAME-LW3: tower boundary-read port (p=3, letter-live) ==")
    s43 = lw3_solve(43)
    s86 = lw3_solve(86)
    chk(s43 == [(1, 1, 1, 1)],
        "P-D nhat_3(43) = 3 x Phi_1 Phi_2, UNIQUE in digit box (%s)" % s43)
    chk(s86 == [(9, 1, 1, 0)],
        "P-D nhat_3(86) = 3^9 x Phi_1, UNIQUE in digit box (%s)" % s86)
    n43, n86 = s43[0], s86[0]
    quot = vsub(n86, vscal(2, n43))
    chk(quot == (7, -1, -1, -2),
        "P-D nhat_3(86)/nhat_3(43)^2 = 3^7/(x Phi_1 Phi_2^2) (%s)" % (quot,))
    for g, nm in ((LW3_G1, "gamma_1"), (LW3_G2, "gamma_2"),
                  (LW3_G3, "gamma_3")):
        chk(lw3_ht(g) == 0, "P-D %s has height 0" % nm)
    ks = lw3_split(quot)
    chk(ks == (-1, -1, -1),
        "P-D lattice split = gamma_1^-1 gamma_2^-1 gamma_3^-1 (%s)" % (ks,))
    # letters res(gamma_i) = 2 in F_3^x (verified below in gp); telescope:
    zres = 2
    vth32 = (zres ** 3) % 3         # res(N(q)^2/N(2q)) = res(g1 g2 g3) = 2
    chk(vth32 == 2, "P-D vartheta_{3,2} = 2 (product of three letters)")
    th30 = vth32                     # inverse of 2 in F_3^x is 2
    chk((th30 * vth32) % 3 == 1, "P-D theta_3(0)*vartheta_{3,2} = 1")
    chk(th30 == 2, "P-D theta_3(0) = 2 (letter-live)")
    th31 = 1
    chk(th31 == 1, "P-D theta_3(1) = 1 (top slot)")
    # gp leg
    got = {}
    try:
        r = subprocess.run(['gp', '-q', '-f'], input=LW3_GP,
                           capture_output=True, text=True, timeout=1200)
        sys.stdout.write(r.stdout)
        if r.returncode != 0 or 'T3DONE' not in r.stdout:
            chk(False, "P-D gp leg completed")
            sys.stdout.write(r.stderr[-2000:])
            return None
        for ln in r.stdout.splitlines():
            ps = ln.strip().split()
            if ps and ps[0].startswith('T3'):
                got[ps[0]] = ps[1:]
    except subprocess.TimeoutExpired:
        chk(False, "P-D gp leg within budget (1200s)")
        return None
    chk(got.get('T3FP') == ['1', '16'], "P-D factorpadic: ONE deg-16 factor")
    chk(got.get('T3NPR') == ['1'], "P-D single prime over 3")
    chk(got.get('T3EF') == ['8', '2'], "P-D (e,f) = (8,2)")
    chk(got.get('T3VALS') == ['4', '10', '21', '43'],
        "P-D nfeltval ladder (4,10,21,43)")
    chk(got.get('T3G') == ['1', '1', '1'],
        "P-D res(gamma_1)=res(gamma_2)=res(gamma_3)=2")
    chk(got.get('T3YGEN') == ['1'], "P-D Y generates F_9")
    chk(got.get('T3TR') == ['1'], "P-D w_3 = tr(Y) = 1")
    chk(got.get('T3NM') == ['1'], "P-D u_3(beta_0) = norm(Y) = 2")
    # boundary conclusion at both slots (integer arithmetic in F_3):
    w3, u3b0, u3b1 = 1, 2, 1
    chk(u3b1 == (th31 * w3) % 3,
        "P-D slot t=1: u_3(beta_1) = 1 = theta_3(1)*w_3")
    chk(u3b0 == (th30 * w3 * w3) % 3,
        "P-D slot t=0: u_3(beta_0) = 2 = theta_3(0)*w_3^2")
    chk(got.get('T3LAW0') == ['1'],
        "P-D gp-side law norm(Y) = 2*tr(Y)^2 (field-internal)")
    # T-2 LW3 half: theta-free mutant predicts u_3(beta_0) = w_3^2 = 1 vs 2
    chk(got.get('T3T2LW') == ['1'],
        "T-2 KILL (FRAME-LW3): norm(Y) != tr(Y)^2 -- theta-free law dead")
    return got

# =====================================================================
# SECTION 4: LEG-I1 -- GENTOW2-B'' at LP1 (p=2); note S7.2.
# Vectors (i, a, b) = exponents of (x, 2, Phi').  Residue group
# <z_1> x <z_2> with z_2 = 1, z_1^3 = 1: represent residues as
# z_1-exponent mod 3.  LD polys in F_2[z]/(z^3+1): elements = 3-bit
# vectors over GF(2) in basis (1, z, z^2).
# =====================================================================
LP1_G1 = (2, -1, 0)     # gamma_1 = x^2/2
LP1_G2 = (-9, 0, 2)     # gamma_2 = Phi'^2/x^9  (u_2 = 9)

def lp1_split(v):
    if v[2] % 2:
        return None
    k2 = v[2] // 2
    r = vsub(v, vscal(k2, LP1_G2))
    if r[0] % 2:
        return None
    k1 = r[0] // 2
    r = vsub(r, vscal(k1, LP1_G1))
    if any(r):
        return None
    return (k1, k2)

def z3mul(u, v):
    """Multiply in F_2[z]/(z^3+1); u,v = 3-tuples over GF(2)."""
    out = [0, 0, 0]
    for i in range(3):
        if u[i]:
            for j in range(3):
                if v[j]:
                    out[(i + j) % 3] ^= 1
    return tuple(out)

def zpow_vec(e):
    """z_1^e as a 3-bit vector."""
    return tuple(1 if k == e % 3 else 0 for k in range(3))

def leg_I1():
    print("== LEG-I1: GENTOW2-B'' instantiation (LP1, p=2) ==")
    N = (1, 2, 1)        # nhat_2(19) = 4 x Phi'
    M = (1, 9, 0)        # nhat_2(38) = 512 x
    quot = vsub(vscal(2, N), M)
    chk(quot == (1, -5, 2), "I1 N^2/M = x Phi'^2 / 32 (%s)" % (quot,))
    ks = lp1_split(quot)
    chk(ks == (5, 1), "I1 lattice split (k1,k2) = (5,1) (%s)" % (ks,))
    # res = z_2^k2 * z_1^k1 = z_1^5 = z_1^2  (z_2 = 1, z_1^3 = 1)
    coc = ks[0] % 3
    chk(coc == 2, "I1 COC = res(nhat_2(19)^2/nhat_2(38)) = z_1^2")
    th0 = (-coc) % 3
    chk(th0 == 1, "I1 theta(0) = z_1 (exponent %d)" % th0)
    th1 = 0
    chk(th1 == 0, "I1 theta(1) = 1 (top slot)")
    one = (1, 0, 0)
    z1 = zpow_vec(1)
    # P = y^2 + theta(1)c_1 y + theta(0)c_0, c_1 = z_1
    coeff_y = z3mul(zpow_vec(th1), z1)
    chk(coeff_y == z1, "I1 y-coefficient = z_1 (both LD1 and LD2)")
    ld1_c0 = z3mul(zpow_vec(th0), one)          # c_0 = 1
    chk(ld1_c0 == z1, "I1 LD1: P = y^2 + z_1 y + z_1 (constant = z_1)")
    ld2_c0 = z3mul(zpow_vec(th0), zpow_vec(2))  # c_0 = z_1^2
    chk(ld2_c0 == one, "I1 LD2: P = y^2 + z_1 y + 1 (constant = z_1^3 = 1)")

# =====================================================================
# SECTION 5: LEG-I2 -- HETOW-4 fixtures (note S7.2)
# =====================================================================
def leg_I2():
    print("== LEG-I2: HETOW-4 instantiation algebra ==")
    strings = {"INT7 (2,2,1)": [2, 2, 1], "MU3 (1,2,2,1)": [1, 2, 2, 1]}
    for p in (3, 5):   # committed residue fields: X (p=3), Z (p=5)
        for nm, s in strings.items():
            # non-geometric: consecutive ratios not all equal in F_p^x
            ratios = [(s[i + 1] * pow(s[i], p - 2, p)) % p
                      for i in range(len(s) - 1)]
            chk(len(set(ratios)) > 1,
                "I2 raw string %s non-geometric over F_%d (ratios %s)"
                % (nm, p, ratios))
            # character-law reconstruction from the first entries fails
            r = ratios[0]
            recon = [(s[0] * pow(r, t, p)) % p for t in range(len(s))]
            fail_at = next((t for t in range(len(s))
                            if recon[t] != s[t] % p), None)
            chk(fail_at is not None,
                "I2 character reconstruction of %s fails over F_%d"
                " (at index %s)" % (nm, p, fail_at))
    # symbolic identity: coefficients as dict {sym: Fraction}
    tauH0, delta = Fraction(2), Fraction(2)
    for D in (2, 3):   # lengths 3 and 4
        # Rhat(Z) = sum a_t Z^t; sym t <-> a_t
        # LHS map: rho_t = a_t * tauH0 * delta^-t
        lhs = [{t: tauH0 * delta ** (-t)} for t in range(D + 1)]
        # RHS: expand tauH0 * Rhat(Z/delta) by substitution
        rhs = [dict() for _ in range(D + 1)]
        for t in range(D + 1):
            # a_t * (Z/delta)^t contributes to degree t only
            coef = tauH0 * delta ** (-t)
            rhs[t][t] = rhs[t].get(t, Fraction(0)) + coef
        # do the substitution genuinely: build (Z/delta)^t by repeated mul
        rhs2 = [dict() for _ in range(D + 1)]
        zod = [Fraction(1)]                     # poly (Z/delta)^0 = 1
        for t in range(D + 1):
            for deg, c in enumerate(zod):
                if c:
                    rhs2[deg][t] = rhs2[deg].get(t, Fraction(0)) + tauH0 * c
            zod = [Fraction(0)] + [c / delta for c in zod]
        ok = all({k: v for k, v in lhs[t].items() if v} ==
                 {k: v for k, v in rhs2[t].items() if v}
                 for t in range(D + 1))
        chk(ok, "I2 symbolic: coefficient map == substitution, length %d"
            % (D + 1))
        chk(rhs == rhs2, "I2 symbolic: expansion routes agree, length %d"
            % (D + 1))

# =====================================================================
# SECTION 6: LEG-I3 -- GENTOW-6.4 FRAME-P (NON_INSTANCE_REGRESSION)
# p=3, Phi'=x^2-3, Phi2=Phi'^2-9x, f=(Phi2^2+81Phi')(Phi'-27), deg 10.
# Composed digits c_{j,a,b}: Phi2-adic, then Phi'-adic, then x-digits;
# slot height = e1e2*v3(c) + w(a,b), e1e2 = 4, w(a,b) = 2a + 5b.
# Pins p_j = slot-min over (a,b).  Predicted (26,16,5), c_g = 5.
# =====================================================================
def composed_digits_P(f):
    """Return dict (j,a,b) -> integer digit for FRAME-P conventions."""
    PhiP = pl_sub(pl_x(2), [3])                  # x^2 - 3
    Phi2 = pl_sub(pl_mul(PhiP, PhiP), pl_scal(9, pl_x(1)))
    # Phi2-adic
    Cs = []
    rem = list(f)
    while True:
        q, r = pl_divmod_monic(rem, Phi2)
        Cs.append(r)
        rem = q
        if not q:
            break
        if len(Cs) > 8:
            raise RuntimeError("runaway division")
    digits = {}
    for j, Cj in enumerate(Cs):
        # Phi'-adic within C_j (deg C_j < 4)
        q, r = pl_divmod_monic(Cj, PhiP) if Cj else ([], [])
        for b, part in enumerate((r, q)):
            for a in range(2):
                digits[(j, a, b)] = part[a] if a < len(part) else 0
    return digits

def pins_P(digits, jmax=2):
    pins = {}
    for j in range(jmax + 1):
        hs = []
        for (jj, a, b), c in digits.items():
            if jj == j and c != 0:
                hs.append(4 * v_p(c, 3) + 2 * a + 5 * b)
        pins[j] = min(hs) if hs else None
    return pins

def leg_I3():
    print("== LEG-I3: GENTOW-6.4 FRAME-P [NON_INSTANCE_REGRESSION] ==")
    PhiP = pl_sub(pl_x(2), [3])
    Phi2 = pl_sub(pl_mul(PhiP, PhiP), pl_scal(9, pl_x(1)))
    f = pl_mul(pl_add(pl_mul(Phi2, Phi2), pl_scal(81, PhiP)),
               pl_sub(PhiP, [27]))
    chk(len(f) - 1 == 10 and f[-1] == 1, "I3 f monic of degree 10")
    digits = composed_digits_P(f)
    # reconstruction: sum c_{j,a,b} x^a Phi'^b Phi2^j == f
    rec = []
    for (j, a, b), c in digits.items():
        term = pl_scal(c, pl_x(a))
        for _ in range(b):
            term = pl_mul(term, PhiP)
        for _ in range(j):
            term = pl_mul(term, Phi2)
        rec = pl_add(rec, term)
    chk(pl_sub(rec, f) == [], "I3 digit reconstruction exact")
    pins = pins_P(digits)
    chk((pins[0], pins[1], pins[2]) == (26, 16, 5),
        "I3 pin tuple (p_0,p_1,p_2) = (26,16,5) (got %s)"
        % ((pins[0], pins[1], pins[2]),))
    c_g = 5
    chk(pins[2] == c_g, "I3 c_g = p_2 = 5")
    # ambient lifts modulo 3^N, N = 6; cap e1e2*N = 24; block cap 19
    N = 6
    mod = 3 ** N
    lifts = [pl_add(f, pl_scal(mod, g)) for g in
             ([1], pl_x(3), pl_add(pl_x(9), [2]),
              pl_add(pl_scal(2, pl_x(5)), pl_x(1)))]
    for li, fl in enumerate(lifts):
        dl = composed_digits_P(fl)
        cong = all((dl.get(k, 0) - digits.get(k, 0)) % mod == 0
                   for k in set(dl) | set(digits))
        chk(cong, "I3 lift %d: all digits congruent mod 3^%d" % (li, N))
        inwin = all(v_p(digits[k], 3) == v_p(dl[k], 3)
                    for k in digits
                    if digits[k] != 0 and v_p(digits[k], 3) < N)
        chk(inwin, "I3 lift %d: in-window valuations stable" % li)
        pl_ = pins_P(dl)
        chk(pl_[1] == pins[1] and pl_[2] == pins[2],
            "I3 lift %d: below-cap pins p_1=16, p_2=5 stable" % li)
        chk((pl_[1] - c_g == 11) and (pl_[2] - c_g == 0),
            "I3 lift %d: block pins p_1-c_g=11, p_2-c_g=0 stable"
            " (below block cap 19)" % li)
    print("  NON_INSTANCE_REGRESSION: this leg's success does NOT count"
          " as a common-lemma instantiation (note S5).")

# =====================================================================
# SECTION 7: main
# =====================================================================
def main():
    print("== T3 LEMMA COCYCLE-TELESCOPE sealed instrument (CODEX arm) ==")
    w, vt, tau, rho, rhohat, tauH0, delta = frame_C()
    teeth_frame_C(w, vt, tau, rho, rhohat, tauH0, delta)
    frame_LW3()
    leg_I1()
    leg_I2()
    leg_I3()
    print("== M5 JOINT-COVERAGE STATUS ==")
    print("  FRAME-C is a direct common-carrier JOINT frame:"
          " theta_2=3 != 1, tau non-character, delta=2 != 1, w=3 != 1.")
    print("  FRAME-C's reference T is FORMAL -- not a realized FGMN tower"
          " normalizer; no realized-tower claim is made.")
    print("  COVERAGE CELL (realized p-adic tower, theta_d != 1 AND"
          " intrinsic w != 1 in one B'' instance): MACHINE-UNEXPLORED"
          " (note S8.3 OPEN COVERAGE T3-JOINT).")
    print("  INSTANTIATION COUNT: 3 (GENTOW2-B'', HETOW-4, [GENTOW5-W(i)]"
          " at ATTEMPT GRADE arc 1/2); GENTOW-6.4 = displayed"
          " NON-INSTANCE (regression leg only).")
    print("== SUMMARY: %d checks, %d violations ==" % (NCHK, len(VIOL)))
    for m in VIOL:
        print("  VIOLATION: " + m)
    return 1 if VIOL else 0

if __name__ == '__main__':
    sys.exit(main())
