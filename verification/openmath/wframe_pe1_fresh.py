#!/usr/bin/env python3
"""WFRAME passPE1 FRESH LEG (hostile verifier's own route, 2026-08-10).

Frame GF29 — NOT in any committed record: the GB tower (PHIP = x^2-2,
PHI2 = PHIP^4 - 4x*PHIP^2 - 32; e1=2,f1=1,z1=1; e2=2,f2=2,z2 live,
z2^2+z2+1=0; u2=5, V2=2, e(mu2)=4, pi3 = PHIP/x^2) with a NEW stage-3
key at u3 = 29 (e3=1, f3=2; no committed key uses u3 = 29), target
psi3 = y^2 + y + z2.

PREREGISTERED (sealed in WFRAME_passPE1_report.md @ 63890e5e, BEFORE
this run): nhat2(29) = 64*PHIP, nhat2(58) = 2^14*x; w-avatar ratio
exponents (58,6,-28) -> z2 != 1; theta(0) ratio (1,2,-2) -> z2^2;
u(beta0) ratio (117,14,-58) -> z2; LAW key PHI3L = PHI2^2 -
64*PHIP*PHI2 - (2^14*x + 2^12*PHIP^2) [c0 = theta(0)^{-1}a0 = z2^2,
lift 1+z2] realizes psi3^{(z2)} = y^2 + z2*y + 1 irreducible /F4 ->
ONE prime (4,4); naive twin PHI3N = PHI2^2 - 64*PHIP*PHI2 -
2^12*PHIP^2 realizes y^2 + z2*y + z2^2 = (y+1)(y+z2^2) -> TWO primes
(4,2) each.  Laws exercised LIVE: W-B (IDY closure with all three
residues measured at an actual prime), W-C (multiplicative
prescription -> psi^{(w)}, PSIW on the nose, verdict discrimination
vs the twin), W-A (pattern transport), W-E (theta(0) letter value).
Dual routes: gp factorpadic (A) + nfinit/idealprimedec/nfmodpr (B);
lattice splits + F4 algebra re-done in own python (no committed
runner code reused).
"""
import subprocess, sys

# ---------- own poly arithmetic over Z (fresh code) ----------
def pmul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            r[i+j] += ai*bj
    return r
def padd(a, b):
    n = max(len(a), len(b)); r = [0]*n
    for i, ai in enumerate(a): r[i] += ai
    for i, bi in enumerate(b): r[i] += bi
    return r
def pscal(c, a): return [c*x for x in a]
def psub(a, b): return padd(a, pscal(-1, b))
def pstr(a):
    return "+".join(f"({c})*x^{i}" for i, c in enumerate(a) if c) or "0"

PHIP = [-2, 0, 1]                                  # x^2 - 2
PHIP2 = pmul(PHIP, PHIP)
PHI2 = psub(psub(pmul(PHIP2, PHIP2), pscal(4, pmul([0,1], PHIP2))), [32])
NH29 = pscal(64, PHIP)                              # nhat2(29)
NH58 = pscal(2**14, [0,1])                          # nhat2(58)
K0L  = padd(NH58, pscal(2**12, PHIP2))              # lift of c0 = z2^2 = 1+z2
K0N  = pscal(2**12, PHIP2)                          # lift of c0 = z2
PHI3L = psub(psub(pmul(PHI2, PHI2), pmul(NH29, PHI2)), K0L)
PHI3N = psub(psub(pmul(PHI2, PHI2), pmul(NH29, PHI2)), K0N)

FAIL = 0; NCHK = 0
def chk(ok, msg):
    global FAIL, NCHK
    NCHK += 1
    print(("PASS " if ok else "FAIL ") + msg)
    if not ok: FAIL += 1

# ---------- leg 1: heights + exponent-lattice splits (own route) ----
dv = {'x': 2, '2': 4, 'P': 5}                       # dv2 heights (GB)
chk(6*dv['2'] + dv['P'] == 29, "L1 nhat2(29) = 2^6*PHIP has dv2-height 29")
chk(14*dv['2'] + dv['x'] == 58, "L1 nhat2(58) = 2^14*x has dv2-height 58")

def split(i, a, b):
    """(i,a,b) = j*gamma1 + k*gamma2, gamma1=(2,-1,0), gamma2=(-5,0,2);
    return (j, k) or None. Letter = z1^j z2^k."""
    if b % 2: return None
    k = b // 2; j = -a
    return (j, k) if 2*j - 5*k == i else None

# [run-1 RED diagnosis, kept: run 1 asserted on -k; the letter is
#  z1^j z2^k with exponent k ITSELF (PE6 convention, e.g. LD1
#  (77,2,-18) = -2*g1 - 9*g2 -> z1^{-2}z2^{-9}).  gp legs were GREEN
#  on all preregistered values in run 1; own-route assertion fixed.]
# W-ratio nhat2(29)/pi3^29 = 2^6*PHIP * x^58 / PHIP^29 = (58, 6, -28)
sW = split(58, 6, -28)
chk(sW is not None and sW[1] % 3 == 1,
    f"L1 W-avatar split (58,6,-28) = {sW} -> z2^{{{sW[1] if sW else '?'}}} = z2 (letter z2, != 1)")
# theta(0)-ratio nhat2(58)/nhat2(29)^2 = 4x/PHIP^2 = (1, 2, -2)
sT = split(1, 2, -2)
chk(sT is not None and sT[1] % 3 == 2,
    f"L1 theta(0) split (1,2,-2) = {sT} -> z2^2 (LAW W-E letter value)")
# U0-ratio nhat2(58)/pi3^58 = 2^14 x^117 / PHIP^58 = (117, 14, -58)
sU = split(117, 14, -58)
chk(sU is not None and sU[1] % 3 == 1,
    f"L1 u(beta0) split (117,14,-58) = {sU} -> z2")
# IDY closure in letters: z2 == z2^2 * z2^2  (LAW W-B(6) at t=0)
chk((2 + 2) % 3 == 1, "L1 IDY letters: z2 = z2^2 * (z2)^2 (LAW W-B(6), t=0)")

# ---------- leg 2: F4 algebra (own tables) ----------
# F4 = {0,1,2,3} with 2 = z2, 3 = z2+1 = z2^2; char 2.
def f4mul(a, b):
    if a == 0 or b == 0: return 0
    la = {1:0, 2:1, 3:2}[a]; lb = {1:0, 2:1, 3:2}[b]
    return {0:1, 1:2, 2:3}[(la+lb) % 3]
def f4add(a, b): return a ^ b
def ev2(c0, c1, y): return f4add(f4add(f4mul(y, y), f4mul(c1, y)), c0)  # y^2+c1*y+c0
Z, Z2 = 2, 3
psi   = (Z, 1)     # y^2 + y + z2      (c0, c1)
psiw  = (1, Z)     # y^2 + z2 y + 1    = psi^{(z2)}
twinr = (Z2, Z)    # y^2 + z2 y + z2^2
# twist algebra: psi^{(w)} = y^2 - a1 w y - a0 w^2, a1=1, a0=z2, w=z2
chk((f4mul(Z, f4mul(Z, Z)), f4mul(1, Z)) == (psiw[0], psiw[1]),
    "L2 DEF W-2 coefficientwise: psi^{(z2)} = y^2 + z2 y + 1")
roots = lambda p: [y for y in range(4) if ev2(p[0], p[1], y) == 0]
chk(roots(psi) == [], "L2 target psi = y^2+y+z2 irreducible /F4 (admissible)")
chk(roots(psiw) == [], "L2 LAW W-A: psi^{(z2)} irreducible /F4 (pattern preserved)")
chk(sorted(roots(twinr)) == [1, Z2],
    "L2 twin residual y^2+z2 y+z2^2 SPLITS: roots {1, z2^2}")
chk(psiw != psi, "L2 psi^{(w)} != psi at w = z2 (NOSE contrast live)")
# multiplicative prescription: c1 = a1 = 1; c0 = theta(0)^{-1} a0 = z2^{-2} z2 = z2^2
chk(f4mul(Z2, Z2) == Z, "L2 c0 check: theta(0)*c0 = z2^2*z2^2 = z2 = a0")

# ---------- leg 3: gp dual routes ----------
GP = f"""
default(parisize, 512000000);
FL = {pstr(PHI3L)};
FN = {pstr(PHI3N)};
PHIP = x^2 - 2; PHI2 = {pstr(PHI2)};
faL = factorpadic(FL, 2, 100); faN = factorpadic(FN, 2, 100);
print("FPADL ", apply(poldegree, faL[,1]~));
print("FPADN ", apply(poldegree, faN[,1]~));
probe(tag, F) = {{
  my(K, prs, xF, PP, P2F, NH, NH2, pi3);
  K = nfinit([F, [2]]);
  prs = idealprimedec(K, 2);
  print(tag, " NPR ", #prs);
  xF = Mod(x, F); PP = Mod(PHIP, F); P2F = Mod(PHI2, F);
  NH = 64*PP; NH2 = 2^14*xF; pi3 = PP/xF^2;
  for(ii = 1, #prs,
    my(pr = prs[ii], r1, r2, w, t0, u0, Y);
    print(tag, " EF ", pr.e, " ", pr.f);
    print(tag, " VALS ", nfeltval(K, xF, pr), " ", nfeltval(K, PP, pr),
          " ", nfeltval(K, Mod(2, F), pr), " ", nfeltval(K, pi3, pr));
    r1 = nfmodpr(K, xF^2/2, pr);
    r2 = nfmodpr(K, PP^2/xF^5, pr);
    print(tag, " R1 ", r1 == 1);
    print(tag, " R2 ", r2 != 1, " ", r2^2 + r2 + 1 == 0);
    w  = nfmodpr(K, NH/pi3^29, pr);
    t0 = nfmodpr(K, NH2/NH^2, pr);
    u0 = nfmodpr(K, NH2/pi3^58, pr);
    print(tag, " WAVA ", w == r2, " ", w != 1, " ", w != r2^2);
    print(tag, " TH0 ", t0 == r2^2);
    print(tag, " U0 ", u0 == r2);
    print(tag, " IDY ", u0 == t0*w^2, " ", u0 != t0);
    Y = nfmodpr(K, P2F/pi3^29, pr);
    if(tag == "GFL",
      print(tag, " PSIW ", Y^2 + w*Y + r2*w^2 == 0);
      print(tag, " NOSE ", Y^2 + Y + r2 != 0),
      print(tag, " YRT ", Y == 1 || Y == r2^2));
  );
}}
probe("GFL", FL);
if(polisirreducible(FN), probe("GFN", FN), print("GFN RATRED"));
print("GPDONE");
"""
out = subprocess.run(['gp', '-q'], input=GP, capture_output=True, text=True)
o = out.stdout
sys.stdout.write(o)
if out.returncode != 0 or 'GPDONE' not in o:
    print('gp stderr:', out.stderr.strip().splitlines()[-1] if out.stderr.strip() else '?')
has = lambda s: s in o
chk(has('GPDONE'), "L3 gp completed")
chk(has('FPADL [16]'), "L3A LAW key: factorpadic ONE factor deg 16 (single prime)")
chk(has('FPADN [8, 8]'), "L3A twin: factorpadic TWO factors deg 8 (verdict differs)")
chk(has('GFL NPR 1'), "L3B LAW key: ONE prime above 2")
chk(o.count('GFL EF 4 4') == 1, "L3B LAW key prime (e,f) = (4,4) [preregistered]")
chk(has('GFL VALS 2 5 4 1'), "L3B v(x),v(PHIP),v(2),v(pi3) = 2,5,4,1 (Lemma 3.13(1): v(pi3)=e/4)")
chk(has('GFL R1 1'), "L3B z1 = 1 on GB (letter-dead level 1)")
chk(has('GFL R2 1 1'), "L3B z2 letter LIVE: r2 != 1, r2^2+r2+1 = 0")
chk(has('GFL WAVA 1 1 1'), "L3B W-AVATAR MEASURED = z2, != 1, != z2^2 (8th prime; != committed GA1 value: u3-discrimination at a NEW pair)")
chk(has('GFL TH0 1'), "L3B theta(0) measured = z2^2 (LAW W-E letter value live)")
chk(has('GFL U0 1'), "L3B u(beta0) measured = z2 (canonical unit letter-valued)")
chk(has('GFL IDY 1 1'), "L3B LAW W-B(6): u0 = theta0*w^2 with three residues measured at an ACTUAL prime (and u0 != theta0, so w = 1 refuted in-frame)")
chk(has('GFL PSIW 1'), "L3B LAW W-C: psi3^{(w)}(Y) = 0 ON THE NOSE at measured w")
chk(has('GFL NOSE 1'), "L3B NOSE tooth: psi3(Y) != 0 (untwisted read refuted)")
chk(has('GFN NPR 2'), "L3B twin: TWO primes above 2")
chk(o.count('GFN EF 4 2') == 2, "L3B twin primes (e,f) = (4,2) each [preregistered]")
chk(o.count('GFN WAVA 1 1 1') == 2, "L3B twin primes: SAME w-avatar z2 (w is frame data, key-independent — DEF W-1 slot/key-independence live)")
chk(o.count('GFN IDY 1 1') == 2, "L3B twin primes: IDY closure live there too")
chk(o.count('GFN YRT 1') == 2, "L3B twin: Y a root of the split residual at each prime (LAW W-C split pattern)")

print(f"checks: {NCHK}, violations: {FAIL}")
print("VERDICT: " + ("GREEN" if FAIL == 0 else "RED"))
sys.exit(0 if FAIL == 0 else 1)
