#!/usr/bin/env python3
"""RESUM-n3 seal re-verification + the statable SQUEEZE-n3 gate arithmetic.

Re-verifies, exactly (sympy symbolic + Fractions), the SEALED numbers:
 R1 the MOVESS n = 2 gate instance (MOVESS_LEAN_BLUEPRINT_2026-07-28.md ~L281/L1683,
    dual-audited): one state, three outcomes (kcol q^-3; termFin (1,1)^2 at 1 - q^-1;
    termFin (1,2) at q^-1 - q^-3); part1 sums to 1; E0 entry < 1;
    det(1-K) = (q^3-1)/q^3 = (q-1)(q^2+q+1)/q^3; the reduced solve
    beta_(1,2) = (q+1)/(q^2+q+1), beta_(1,1)^2 = q^2/(q^2+q+1); sum 1 --
    symbolically and at q in {2, 3, 4, 5}.
 R2 the RESUM-n3 kernel/det/J pool table (CASE_RESUMN3_SEALED_PREDICTIONS.md S1/S3).
 R3 the five sealed R_sigma: re-derived bottom-up from the S1 stratum table
    (beta_2 -> beta_3 -> root assembly), checked against the sealed closed forms,
    the sealed four-prime table (q = 2, 3, 5, 7), the checksum Sum R_sigma = 1,
    the Kac-Rice moment cross-check, and the q -> oo limits (1/6, 1/2, 1/3, 0, 0).
 R4 gate SQUEEZE-n3 (MOVES_2026-07-24.md SQ.5, ~L13498): SPECIFIED, not sealed; its
    seal artifact does not exist yet and this script is NOT it. What is statable NOW:
    the 25 upper-leg bracket pairs decided_sigma(N) <= floor(R_sigma(p) p^{3N}) at
    (p,N) in {(2,4),(2,6),(2,8),(3,4),(3,5)}, the checksum rows, and the (L-meas)
    aggregate legs Sum_{tau != sigma} d_tau <= Sum_{tau != sigma} R_tau(p) -- computed
    against RESUM-n3's S7 CORRECTED sealed integers (census-verified 65/65 in S8).
    HONESTY: the gate's own census must be EXHAUSTIVE under the PARI oracle, never
    stratum formulas; this layer only re-verifies the bracket ARITHMETIC. The (L-thy)
    theory-env leg is TOOTHLESS at census range (env*(N) > 1, SX.5(iii)) -- displayed,
    not checked, never sold as falsifiable there.
"""
import sys
from fractions import Fraction as F
import sympy as sp

q = sp.symbols('q')
FINDINGS = []
def chk(name, cond, detail=""):
    tag = "PASS" if cond else "FINDING"
    if not cond: FINDINGS.append(name)
    print(f"[{tag}] {name}  {detail}")

def ev(expr, p):
    r = sp.Rational(sp.nsimplify(sp.simplify(expr.subs(q, p))))
    return F(int(r.p), int(r.q))

print("=" * 72)
print("R1. The MOVESS n = 2 gate instance (kcol q^-3)")
print("=" * 72)
kcol, t11, t12 = q**-3, 1 - 1/q, 1/q - q**-3
chk("part1: kcol + term(1,1)^2 + term(1,2) = 1", sp.simplify(kcol + t11 + t12 - 1) == 0)
det = 1 - kcol
chk("det(1-K) = (q-1)(q^2+q+1)/q^3", sp.simplify(det - (q-1)*(q**2+q+1)/q**3) == 0)
b12, b11 = sp.simplify(t12/det), sp.simplify(t11/det)
chk("beta_(1,2) = (q+1)/(q^2+q+1)", sp.simplify(b12 - (q+1)/(q**2+q+1)) == 0)
chk("beta_(1,1)^2 = q^2/(q^2+q+1)", sp.simplify(b11 - q**2/(q**2+q+1)) == 0)
chk("beta sum = 1", sp.simplify(b12 + b11 - 1) == 0)
SEALED_N2 = {2: (F(1,8), F(3,7), F(4,7)),
             3: (F(1,27), F(4,13), F(9,13)),
             4: (F(1,64), F(5,21), F(16,21)),
             5: (F(1,125), F(6,31), F(25,31))}
for p in (2, 3, 4, 5):
    got = (ev(kcol,p), ev(b12,p), ev(b11,p))
    chk(f"q={p}: (kcol, beta_(1,2), beta_(1,1)^2) = {tuple(map(str,SEALED_N2[p]))}",
        got == SEALED_N2[p], f"got {tuple(map(str,got))}; E0 entry {got[0]} < 1: {got[0] < 1}")

print("=" * 72)
print("R2. RESUM-n3 kernel/det/J pool table (S1/S3)")
print("=" * 72)
D3s, D6s = q**3 - 1, q**6 - 1
k2, k3 = (q-1)/D3s, (q-1)/D6s
Jx = ((q-1)*(q-2) + (q-1))/D6s + (q-1)**2/(D3s*D6s)
chk("K_2 = 1/(q^2+q+1); det(I-K_2) = (q^2+q)/(q^2+q+1)",
    sp.simplify(k2 - 1/(q**2+q+1)) == 0 and
    sp.simplify(1 - k2 - (q**2+q)/(q**2+q+1)) == 0)
chk("det(I-K_3) = (q^6-q)/(q^6-1)", sp.simplify(1 - k3 - (q**6-q)/D6s) == 0)
SEAL_POOL = {2: (F(1,7), F(6,7), F(1,63), F(62,63), F(8,441)),
             3: (F(1,13), F(12,13), F(1,364), F(363,364), F(27,4732)),
             4: (F(1,21), F(20,21), F(1,1365), F(1364,1365), F(64,28665))}
for p in (2, 3, 4):
    got = (ev(k2,p), ev(1-k2,p), ev(k3,p), ev(1-k3,p), ev(Jx,p))
    chk(f"q0={p}: (K_2, det, K_3, det, J) sealed", got == SEAL_POOL[p])

print("=" * 72)
print("R3. The five R_sigma re-derived bottom-up from the S1 strata")
print("=" * 72)
# blk2 solve (resummed strata / (1 - kappa_2)); sigma_1 in {(1,1)^2, (1,2), (2,1)}
m2s, m2i, mw2, mvv = ((q-1)*(q-2)/2)/D3s, (q*(q-1)/2)/D3s, ((q-1)*q**2)/D3s, (q-1)/D3s
beta2 = {'11': sp.simplify((m2s + mvv)/(1-k2)),   # (1,1)^2: o_split + m_vv
         '12': sp.simplify(m2i/(1-k2)),           # (1,2)
         '21': sp.simplify(mw2/(1-k2))}           # (2,1)
chk("beta_2 = (1/(2(q+1)), 1/(2(q+1)), q/(q+1)); sum 1",
    sp.simplify(beta2['11'] - 1/(2*(q+1))) == 0 and
    sp.simplify(beta2['12'] - 1/(2*(q+1))) == 0 and
    sp.simplify(beta2['21'] - q/(q+1)) == 0 and
    sp.simplify(sum(beta2.values()) - 1) == 0)
chk("odd-p complete-the-square law: beta_2(ram) = P(v(delta) odd) = q/(q+1)",
    sp.simplify(beta2['21'] - q/(q+1)) == 0)
# blk3 terminal totals per sigma (S1 strata; split legs excluded -> via J * beta_2)
t3 = {'111': ((q-1)*(q-2)*(q-3)/6)/D6s + ((q-1)*(q-2)/2)/D6s
             + ((q-1)**2*(q-2)/2)/(D3s*D6s) + (q-1)**2/(D3s*D6s),
      '112': (q*(q-1)**2/2)/D6s + (q*(q-1)/2)/D6s + (q*(q-1)**2/2)/(D3s*D6s),
      '13':  ((q**3-q)/3)/D6s,
      '1121': ((q-1)*q**4)/D6s + ((q-1)**2*q**2)/(D3s*D6s),
      '31':  ((q-1)*(q**5+q**3))/D6s}
chk("blk3 mass checksum: sum t3 + J + kappa_3 = 1",
    sp.simplify(sum(t3.values()) + Jx + k3 - 1) == 0)
b2map = {'111': beta2['11'], '112': beta2['12'], '1121': beta2['21'], '13': 0, '31': 0}
beta3 = {s: sp.simplify((t3[s] + Jx*b2map[s])/(1-k3)) for s in t3}
chk("beta_3 checksum: sum = 1", sp.simplify(sum(beta3.values()) - 1) == 0)
# root assembly (S1 ROOT row)
root_t = {'111': (q-1)*(q-2)/(6*q**2), '112': (q-1)/(2*q), '13': (q**2-1)/(3*q**2),
          '1121': 0, '31': 0}
R = {s: sp.simplify(root_t[s] + (q-1)/q**2 * b2map[s] + beta3[s]/q**2) for s in t3}
P4 = q**4 + q**3 + q**2 + q + 1
P5 = (q + 1) * P4
chk("P5 = q^5+2q^4+2q^3+2q^2+2q+1 = (q+1) P4",
    sp.simplify(P5 - (q**5+2*q**4+2*q**3+2*q**2+2*q+1)) == 0)
SEALED_R = {'111': (q**5-q**4+q**3)/(6*P5), '112': (q**5+q**4+q**3)/(2*P5),
            '13': (q**4+q**3)/(3*P4), '1121': (q**4+q**2+q)/P5, '31': (q**2+1)/P4}
for s in ('111', '112', '13', '1121', '31'):
    chk(f"R_{s} == sealed closed form", sp.simplify(R[s] - SEALED_R[s]) == 0,
        f"{sp.factor(R[s])}")
chk("checksum: Sum R_sigma = 1 identically", sp.simplify(sum(R.values()) - 1) == 0)
chk("moment cross-check (Kac-Rice): 3 R_111 + R_112 + R_1121 = q/(q+1)",
    sp.simplify(3*R['111'] + R['112'] + R['1121'] - q/(q+1)) == 0)
lims = tuple(sp.limit(R[s], q, sp.oo) for s in ('111', '112', '13', '1121', '31'))
chk("q -> oo limits = (1/6, 1/2, 1/3, 0, 0)",
    lims == (sp.Rational(1,6), sp.Rational(1,2), sp.Rational(1,3), 0, 0))
SEALED_TABLE = {2: [F(4,93), F(28,93), F(8,31), F(22,93), F(5,31)],
                3: [F(63,968), F(351,968), F(36,121), F(93,484), F(10,121)],
                5: [F(875,9372), F(3875,9372), F(250,781), F(655,4686), F(26,781)],
                7: [F(14749,134448), F(19551,44816), F(2744,8403), F(2457,22408),
                    F(50,2801)]}
for p, row in SEALED_TABLE.items():
    got = [ev(R[s], p) for s in ('111', '112', '13', '1121', '31')]
    chk(f"q={p}: four-prime row sealed; sum = 1", got == row and sum(got) == 1)

print("=" * 72)
print("R4. Gate SQUEEZE-n3 -- the statable arithmetic (S7 corrected integers)")
print("    [NOT the gate seal; the gate's own census must be PARI-exhaustive]")
print("=" * 72)
SIGS = ('111', '112', '13', '1121', '31')
S7 = {2: {1: [0,2,2,0,0], 2: [0,16,16,12,8], 3: [16,144,128,96,80],
          4: [128,1184,1056,896,640], 5: [1280,9728,8448,7360,5248],
          6: [10496,78080,67584,60928,42240], 7: [88064,629248,541184,489472,337920],
          8: [708608,5038080,4329472,3951616,2705408]},
      3: {1: [1,9,8,0,0], 2: [27,243,216,126,54], 3: [1215,7047,5832,3402,1620],
          4: [32886,190998,158112,100602,43740],
          5: [927288,5196312,4269024,2726460,1185354]}}
S7TOT = {2: {1: F(1,2), 2: F(13,16), 3: F(29,32), 4: F(61,64), 5: F(501,512),
             6: F(1013,1024), 7: F(2037,2048), 8: F(16341,16384)},
         3: {1: F(2,3), 2: F(74,81), 3: F(236,243), 4: F(722,729), 5: F(19622,19683)}}
Rp = {p: {s: ev(R[s], p) for s in SIGS} for p in (2, 3)}
for p in (2, 3):
    for N, row in S7[p].items():
        chk(f"p={p} N={N}: checksum row Sum decided + undecided = p^3N; total sealed",
            sum(row) == S7TOT[p][N] * p**(3*N),
            f"undecided = {p**(3*N) - sum(row)}")
        ok = all(row[i] <= Rp[p][s] * p**(3*N) for i, s in enumerate(SIGS))
        chk(f"p={p} N={N}: monotone-from-below decided_sigma <= R_sigma p^3N (all 5)", ok)
GATE = [(2, 4), (2, 6), (2, 8), (3, 4), (3, 5)]
print("   -- the 25 gate bracket pairs (upper leg EXACT; any overshoot falsifies SQ.2):")
for (p, N) in GATE:
    for i, s in enumerate(SIGS):
        dec, ub = S7[p][N][i], (Rp[p][s] * p**(3*N)).__floor__()
        chk(f"gate ({p},{N}) sigma={s}: decided {dec} <= floor(R p^3N) = {ub}", dec <= ub)
    # (L-meas) aggregate leg, retyped form (rev 2): per sigma, the sum over tau != sigma
    d = {s: F(S7[p][N][i], p**(3*N)) for i, s in enumerate(SIGS)}
    okm = all(sum(d[t] for t in SIGS if t != s0) <= sum(Rp[p][t] for t in SIGS if t != s0)
              for s0 in SIGS)
    chk(f"gate ({p},{N}): (L-meas) aggregate legs (all 5 sigma)", okm)
print("   -- (L-thy) leg: env*(N) > 1 at every census N (SX.5(iii)) -- TOOTHLESS at")
print("      census range; displayed for shape only, NO check run, nothing claimed.")

print("=" * 72)
if not FINDINGS:
    print("RESUM-N3-SEAL VERDICT: ALL PASS -- every sealed number re-verified; the")
    print("SQUEEZE-n3 statable arithmetic holds on the S7 integers. (Conditionality")
    print("unchanged: E0/X.3/the nine CL-5 inputs remain OPEN; brackets SUPPORT,")
    print("never prove -- plan SS7 gate-epistemics.)")
else:
    print(f"RESUM-N3-SEAL VERDICT: {len(FINDINGS)} FINDING(S): {FINDINGS}")
sys.exit(0 if not FINDINGS else 1)
