#!/usr/bin/env python3
"""grb_order2_gate.py — leaf-local falsifier gates for GRB_ORDER2_2026-08-05.md (unit A-M2).

NOT the blueprint's full N-1 (grb_order2_check.py, exact order-2 towers over
Z2/Z3/F2[[t]]/F3[[t]]); these are the leaf's own two gates, run BEFORE S3/S5/S6
were written (falsifier-first at leaf scope; N-1 proper remains the wave-0 debt).

G1 (CARRY-1): the integral anchor arithmetic at a state with read data (e,h):
    eq (12)-integral:  u(g)*e + s(g)*h = g,  0 <= s(g) < e   (g in Z, our weights)
    wrap law:          s(g)+s(g') = s(g+g') + d*e,  u(g)+u(g') = u(g+g') - d*h,
                       d = floor((s(g)+s(g'))/e) in {0,1}
    e-fold wrap:       e*(s(1),u(1)) = (s(e),u(e)) + l*(e,-h),  l = Bezout inverse
                       of h mod e  (phi_1^e = p * ybar^l as exponent identity).

G2 (TR-3 ratio): depth-2 instance, d0=1, K=Q, p=5, level-1 read (e,h)=(1,1)
    (phi_1 = x, mu_1 = min(v(c_k)+k)), level-2 key phi_2 = x^2+5x+2*25
    (R_1(phi_2) = psi_1 = y^2+y+2, irreducible over F_5), second read
    (e_2,h_2) = (2,1).  For developments f = sum a_s phi_2^s with monomial
    coefficients a_s = c*x^k*5^m, compute the depth-2 residual coefficients from
    the RAW printed definitions:
      FGMN Def 3.16:  C^F_j = eps_1(alpha_j) * R_{1,alpha_j}(a_{s_j})(z_1),
                      eps_1(beta) = z_1^(l_1*s(beta) - l'_1*u(beta))  [Def 3.15]
      GMN  Def 2.20:  c_{s_j} = z_1^(t_1(s_j)) * R_1(a_{s_j})(z_1),
                      t_1(i) = (s_1(a_i) - l_1*u_i)/e_1, u_i = v_2(a_i phi_2^i)
    in F_25 = F_5[z]/(psi_1), and test:
      (i)  is the coefficientwise ratio C^F_j / c^G_j CONSTANT across attained
           slots?  (the naive one-scalar reading of (GR-B)(2')'s "~ R_lambda")
      (ii) the displayed dictionary law: ratio(j+1)/ratio(j) = z_1^(gamma_2),
           gamma_2 = e_2*V_2 + h_2 = 5.
Preregistered predictions: G1 zero violations; G2(i) FAILS (non-constant ratio,
refuting the naive collapse), G2(ii) holds exactly.
"""
import itertools, random

random.seed(20260805)
fails = []

# ---------- G1 ----------
def su(gamma, e, h):
    # integral eq (12): unique (s,u), u*e + s*h = gamma, 0 <= s < e
    l = pow(h, -1, e) if e > 1 else 0
    s = (l * gamma) % e if e > 1 else 0
    u = (gamma - s * h) // e
    assert u * e + s * h == gamma
    return s, u

g1_n = 0
for _ in range(20000):
    e = random.randint(1, 12)
    h = random.choice([x for x in range(1, 40) if __import__('math').gcd(x, e) == 1])
    g, gp = random.randint(-300, 300), random.randint(-300, 300)
    s1, u1 = su(g, e, h); s2, u2 = su(gp, e, h); s3, u3 = su(g + gp, e, h)
    d = (s1 + s2) // e
    ok = (d in (0, 1)) and (s1 + s2 == s3 + d * e) and (u1 + u2 == u3 - d * h)
    if not ok:
        fails.append(("G1-wrap", e, h, g, gp)); break
    g1_n += 1
# e-fold wrap: e*(s(1),u(1)) = (s(e),u(e)) + l*(e,-h)
for e in range(2, 13):
    for h in range(1, 40):
        if __import__('math').gcd(h, e) != 1:
            continue
        l = pow(h, -1, e)
        s1, u1 = su(1, e, h); se, ue = su(e, e, h)
        if not (e * s1 == se + l * e and e * u1 == ue - l * h and (se, ue) == (0, 1)):
            fails.append(("G1-efold", e, h))
print(f"G1: {g1_n} wrap-law samples + e-fold wraps: "
      f"{'OK (0 violations)' if not any(f[0].startswith('G1') for f in fails) else 'FAIL'}")

# ---------- G2 ----------
P = 5
PSI = (2, 1)  # psi_1 = y^2 + 1*y + 2 over F_5 (irreducible: disc = 1-8 = 3, non-QR)

def gf_mul(a, b):  # F_25 = F_5[z]/(z^2 + z + 2); elements (c0, c1) = c0 + c1 z
    c0 = a[0] * b[0]; c1 = a[0] * b[1] + a[1] * b[0]; c2 = a[1] * b[1]
    # z^2 = -z - 2 = 4z + 3
    return ((c0 + 3 * c2) % P, (c1 + 4 * c2) % P)

def gf_pow(a, n):
    if n < 0:
        # invert via a^(24) = 1 in F_25^*
        return gf_pow(gf_pow(a, 24 - ((-n) % 24)), 1) if (-n) % 24 else (1, 0)
    r = (1, 0)
    for _ in range(n % 24 if a != (0, 0) else n):
        r = gf_mul(r, a)
    return r

Z1 = (0, 1)  # z_1 = the class of z: psi_1(z_1) = 0

# level-1 data (FGMN indexing r=1): (e_1,h_1) = (1,1) -> l_1 = 0, l'_1 = 1
E1, H1 = 1, 1
L1, L1p = 0, 1  # l*h + l'*e = 1, 0 <= l < e
# level-2: V_2 = e(mu_1)*mu_1(phi_2) = 1*2 = 2; read (e_2,h_2) = (2,1)
V2, E2, H2 = 2, 2, 1
GAMMA2 = E2 * V2 + H2  # = 5

def mu1(k, m):  # mu_1(c x^k 5^m) = m + k   (v(5)=1, mu_1(x)=1 via lambda_1=1)
    return m + k

def fgmn_coeff(c, k, m, alpha_j):
    """FGMN Def 3.16 coefficient at slot j with weight alpha_j = mu_1(a):
       eps_1(alpha_j) * R_{1,alpha_j}(a)(z_1); R_{1,beta}(c x^k 5^m) = cbar y^k."""
    assert mu1(k, m) == alpha_j
    # eq (12) at level 1: u*e_1 + s*h_1 = e(mu_1)*alpha_j = alpha_j, 0<=s<1 -> s=0
    s_b, u_b = 0, alpha_j
    eps_exp = L1 * s_b - L1p * u_b          # = -alpha_j
    inner = gf_mul((c % P, 0), gf_pow(Z1, k))  # cbar * z_1^k
    return gf_mul(gf_pow(Z1, eps_exp % 24), inner)

def gmn_coeff(c, k, m, slot):
    """GMN Def 2.19/2.20: c_i = z_1^{t_1(i)} R_1(a_i)(z_1), t_1(i) =
       (s_1(a_i) - l_1 * u_i)/e_1, u_i = v_2(a_i phi_2^i) = mu_1(a_i) + i*V_2;
       R_1 (side-read, Def 2.21 order-1) of a monomial = cbar."""
    u_i = mu1(k, m) + slot * V2
    t = (k - L1 * u_i) // E1                # = k here (l_1 = 0)
    return gf_mul(gf_pow(Z1, t % 24), (c % P, 0))

# family of test developments: slots s_j = 0,2,4 attained (s(alpha)=0, e_2=2),
# alpha = 10: mu_1(a_{2j}) = alpha_j = 10 - 5j  (alpha_j = alpha - s_j*(V_2+h_2/e_2),
# doubled: A_j = 2*alpha_j = 20 - 10j, integral)
g2_viol_const, g2_law_ok, g2_n = 0, 0, 0
for trial in range(500):
    coeffs = []
    for j, aj in enumerate([10, 5, 0]):
        c = random.randint(1, 4)
        k = random.choice([0, 1])
        m = aj - k
        coeffs.append((c, k, m, aj, 2 * j))
    CF = [fgmn_coeff(c, k, m, aj) for (c, k, m, aj, s) in coeffs]
    CG = [gmn_coeff(c, k, m, s) for (c, k, m, aj, s) in coeffs]
    # slot argument = development abscissa s_j = 2j
    ratios = [gf_mul(f, gf_pow(g, -1)) for f, g in
              [(CF[i], CG[i]) for i in range(3)]]
    g2_n += 1
    if not (ratios[0] == ratios[1] == ratios[2]):
        g2_viol_const += 1
    step = gf_pow(Z1, GAMMA2)
    if (gf_mul(ratios[0], step) == ratios[1] and gf_mul(ratios[1], step) == ratios[2]):
        g2_law_ok += 1

def gf_inv(a):
    return gf_pow(a, 23)

print(f"G2: {g2_n} depth-2 samples; naive one-scalar collapse violated in "
      f"{g2_viol_const}/{g2_n}; dictionary law ratio(j+1)=ratio(j)*z1^{GAMMA2} "
      f"held in {g2_law_ok}/{g2_n}")
print(f"G2 check z1^5 != 1: {gf_pow(Z1, 5) != (1, 0)} (z1^5 = {gf_pow(Z1, 5)})")

if fails:
    print("FAILS:", fails[:5])
print("VERDICT: G1", "PASS" if not fails else "FAIL",
      "| G2 naive-collapse", "REFUTED" if g2_viol_const == g2_n else "NOT refuted",
      "| G2 dictionary-law", "PASS" if g2_law_ok == g2_n else "FAIL")
