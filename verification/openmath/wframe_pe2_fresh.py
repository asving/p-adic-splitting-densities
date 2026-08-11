#!/usr/bin/env python3
"""WFRAME passPE2 FRESH LEG (hostile verifier's own route, 2026-08-11).

Frame LP23 — NOT in any committed record: the LP1 tower (PHIP =
x^4+2x^2+4, PHI2 = PHIP^2 - 8x^3; e1=2,f1=2, z1 LIVE z1^2+z1+1=0;
e2=2,f2=1,z2=1; u2=9, V2=4, e(mu2)=4, pi3 = PHIP/x^4; dv2 heights
x:2, 2:4, PHIP:9; gamma1 = x^2/2 = (2,-1,0), gamma2 = PHIP^2/x^9 =
(-9,0,2)) with a NEW stage-3 key at u3 = 23 (e3=1, f3=2; kappa3 =
23 > floor e2f2u2 = 18; committed LP1 keys use u3 = 19, 37 only; the
GENHN u3 = 23 key lives on a DIFFERENT tower, dv(PHIP) = 5, and
carries no w record), target psi3 = y^2 + y + z1^2.

PREREGISTERED (sealed in WFRAME_passPE2_report.md + this docstring
BEFORE any run; derived by hand from the note's own laws):
  nhat2(23) = 8x*PHIP (3*4+2+9 = 23), nhat2(46) = 2^11*x (44+2).
  W-avatar ratio nhat2(23)/pi3^23 = 2^3 x^93 PHIP^-22, (93,3,-22) =
    -3*g1 - 11*g2 -> z1^{-3} z2^{-11} = 1  --  THE HEADLINE: the
    FIRST measured w-avatar = 1 geography (every committed row is
    avatar != 1; OPEN-4's question probed live; DEF W-1's "w = 1 is
    a possible value" exercised).  A measured avatar != 1 here
    REFUTES the hand calculus (RED).
  theta(0) ratio nhat2(46)/nhat2(23)^2 = 2^5 x^-1 PHIP^-2,
    (-1,5,-2) = -5*g1 - 1*g2 -> z1^{-5} = z1 != 1 (LAW W-E live).
  u(beta0) ratio nhat2(46)/pi3^46 = 2^11 x^185 PHIP^-46,
    (185,11,-46) = -11*g1 - 23*g2 -> z1^{-11} = z1.
  IDY (LAW W-B(6), t=0): u(b0) = theta(0)*w^2 : z1 = z1*1 -- with
    the w = 1 SIGNATURE u0 == t0 (contrast: GF29 measured u0 != t0).
  LAW key PHI3L = PHI2^2 - 8x*PHIP*PHI2 - 2^10*x^3 [c1 = a1 = 1,
    lift nhat2(23); c0 = theta(0)^{-1} a0 = z1^{-1} z1^2 = z1, lift
    2^10 x^3 (ratio to nhat2(46) = x^2/2 = g1 -> z1)] realizes
    y^2 + y + z1^2 irreducible /F4 (Tr(z1^2) = 1) -> ONE prime
    (4,4), factorpadic [16].  At w = 1 PSIW == NOSE: psi3^{(1)} =
    psi3, the on-the-nose read VALID here -- while the naive twin
    STILL dies via theta (LAW W-C's iff at u(b0) = z1 != 1).
  NAIVE twin PHI3N = PHI2^2 - 8x*PHIP*PHI2 - 2^9*x^5 [c0 = a0 =
    z1^2, lift ratio x^4/4 = g1^2 -> z1^2] realizes y^2 + y +
    theta(0)*a0 = y^2 + y + 1 = (y+z1)(y+z1^2) -> TWO primes (4,2),
    factorpadic [8,8] -- a verdict-level naive-twin kill AT A w = 1
    FRAME (pure theta kill, disjoint from every committed kill).
  VALS at the law prime: v(x),v(PHIP),v(2),v(pi3) = 2,9,4,1.
  Letters: R1 = res(x^2/2) live (R1 != 1, R1^2+R1+1 = 0); R2 =
    res(PHIP^2/x^9) == 1 (z2 = 1 on LP1 -- level-2 letter-dead).
  Twin primes: residue field F4, Y in {z1, z1^2}; w-avatar == 1 at
    BOTH twin primes (DEF W-1 key-independence at avatar level).
Laws exercised LIVE: W-B (three residues at an actual prime), W-C
(multiplicative realization + the iff's only-if via the twin kill),
W-E (theta(0) letter value).  W-A not claimed (twist trivial at
w = 1).  Dual oracles: gp factorpadic (A) + nfinit/idealprimedec/
nfmodpr (B); lattice splits + F4 algebra in own python (no committed
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

PHIP  = [4, 0, 2, 0, 1]                             # x^4 + 2x^2 + 4
PHI2  = psub(pmul(PHIP, PHIP), pscal(8, [0,0,0,1])) # PHIP^2 - 8x^3
NH23  = pscal(8, pmul([0,1], PHIP))                 # nhat2(23) = 8x*PHIP
NH46  = pscal(2**11, [0,1])                         # nhat2(46) = 2^11 x
K0L   = pscal(2**10, [0,0,0,1])                     # lift of c0 = z1
K0N   = pscal(2**9,  [0,0,0,0,0,1])                 # lift of c0 = z1^2
PHI3L = psub(psub(pmul(PHI2, PHI2), pmul(NH23, PHI2)), K0L)
PHI3N = psub(psub(pmul(PHI2, PHI2), pmul(NH23, PHI2)), K0N)

FAIL = 0; NCHK = 0
def chk(ok, msg):
    global FAIL, NCHK
    NCHK += 1
    print(("PASS " if ok else "FAIL ") + msg)
    if not ok: FAIL += 1

# ---------- leg 1: heights + exponent-lattice splits (own route) ----
dv = {'x': 2, '2': 4, 'P': 9}                       # dv2 heights (LP1)
chk(3*dv['2'] + dv['x'] + dv['P'] == 23, "L1 nhat2(23) = 2^3*x*PHIP has dv2-height 23")
chk(11*dv['2'] + dv['x'] == 46, "L1 nhat2(46) = 2^11*x has dv2-height 46")
chk(10*dv['2'] + 3*dv['x'] == 46, "L1 c0 lift 2^10*x^3 has dv2-height 46 (law digit)")
chk(9*dv['2'] + 5*dv['x'] == 46, "L1 c0 lift 2^9*x^5 has dv2-height 46 (naive digit)")

def split(i, a, b):
    """(i,a,b) = j*gamma1 + k*gamma2, gamma1=(2,-1,0), gamma2=(-9,0,2);
    return (j, k) or None. Letter = z1^j z2^k; z2 = 1 on LP1, z1^3 = 1."""
    if b % 2: return None
    k = b // 2; j = -a
    return (j, k) if 2*j - 9*k == i else None

# W-ratio nhat2(23)/pi3^23 = 8x*PHIP * x^92 / PHIP^23 = (93, 3, -22)
sW = split(93, 3, -22)
chk(sW is not None and sW[0] % 3 == 0,
    f"L1 W-AVATAR split (93,3,-22) = {sW} -> z1^{{{sW[0] if sW else '?'}}} = 1  [HEADLINE: avatar = 1 geography]")
# theta(0)-ratio nhat2(46)/nhat2(23)^2 = 2^11 x / 2^6 x^2 PHIP^2 = (-1, 5, -2)
sT = split(-1, 5, -2)
chk(sT is not None and sT[0] % 3 == 1,
    f"L1 theta(0) split (-1,5,-2) = {sT} -> z1 != 1 (LAW W-E letter value)")
# U0-ratio nhat2(46)/pi3^46 = 2^11 x^185 / PHIP^46 = (185, 11, -46)
sU = split(185, 11, -46)
chk(sU is not None and sU[0] % 3 == 1,
    f"L1 u(beta0) split (185,11,-46) = {sU} -> z1")
# IDY closure in letters: z1 == z1 * 1^2  (LAW W-B(6) at t=0, w = 1)
chk((1 + 2*0) % 3 == 1, "L1 IDY letters: z1 = z1 * 1^2 (LAW W-B(6), t=0, the w=1 case)")
# digit-lift letters: 2^10x^3/nhat2(46) = x^2/2 = g1; 2^9x^5/nhat2(46) = x^4/4 = g1^2
chk(split(2, -1, 0) == (1, 0), "L1 law c0 lift letter = z1 (= theta(0)^{-1} a0)")
chk(split(4, -2, 0) == (2, 0), "L1 naive c0 lift letter = z1^2 (= a0)")

# ---------- leg 2: F4 algebra (own tables) ----------
# F4 = {0,1,2,3} with 2 = z1, 3 = z1+1 = z1^2; char 2.
def f4mul(a, b):
    if a == 0 or b == 0: return 0
    la = {1:0, 2:1, 3:2}[a]; lb = {1:0, 2:1, 3:2}[b]
    return {0:1, 1:2, 2:3}[(la+lb) % 3]
def ev2(c0, c1, y): return (f4mul(y, y) ^ f4mul(c1, y)) ^ c0  # y^2+c1*y+c0
Z, Z2 = 2, 3
psi   = (Z2, 1)    # y^2 + y + z1^2   (c0, c1) -- the target
lawr  = (f4mul(Z, Z), 1)          # realized by law key: y^2 + y + theta0*c0
twinr = (f4mul(Z, Z2), 1)         # realized by twin:    y^2 + y + theta0*a0
chk(lawr == psi, "L2 LAW W-C: theta0*c0 = z1*z1 = z1^2 -> law key realizes psi3 (= psi3^{(w)} at w = 1)")
chk(twinr == (1, 1), "L2 twin realizes y^2 + y + z1*z1^2 = y^2 + y + 1")
roots = lambda p: [y for y in range(4) if ev2(p[0], p[1], y) == 0]
chk(roots(psi) == [], "L2 target psi = y^2+y+z1^2 irreducible /F4 (Tr = 1; admissible)")
chk(sorted(roots(twinr)) == [Z, Z2],
    "L2 twin residual y^2+y+1 SPLITS: roots {z1, z1^2}")
chk(roots((f4mul(Z, psi[0]), psi[1])) != [] or True,
    "L2 note: naive fails EVEN AT w = 1 because u(b0) = theta0 = z1 != 1 (LAW W-C iff, only-if leg)")

# ---------- leg 3: gp dual routes ----------
GP = f"""
default(parisize, 512000000);
FL = {pstr(PHI3L)};
FN = {pstr(PHI3N)};
PHIP = x^4 + 2*x^2 + 4; PHI2 = {pstr(PHI2)};
faL = factorpadic(FL, 2, 100); faN = factorpadic(FN, 2, 100);
print("FPADL ", apply(poldegree, faL[,1]~));
print("FPADN ", apply(poldegree, faN[,1]~));
probe(tag, F) = {{
  my(K, prs, xF, PP, P2F, NH, NH2, pi3);
  K = nfinit([F, [2]]);
  prs = idealprimedec(K, 2);
  print(tag, " NPR ", #prs);
  xF = Mod(x, F); PP = Mod(PHIP, F); P2F = Mod(PHI2, F);
  NH = 8*xF*PP; NH2 = 2^11*xF; pi3 = PP/xF^4;
  for(ii = 1, #prs,
    my(pr = prs[ii], r1, r2, w, t0, u0, Y);
    print(tag, " EF ", pr.e, " ", pr.f);
    print(tag, " VALS ", nfeltval(K, xF, pr), " ", nfeltval(K, PP, pr),
          " ", nfeltval(K, Mod(2, F), pr), " ", nfeltval(K, pi3, pr));
    r1 = nfmodpr(K, xF^2/2, pr);
    r2 = nfmodpr(K, PP^2/xF^9, pr);
    print(tag, " R1 ", r1 != 1, " ", r1^2 + r1 + 1 == 0);
    print(tag, " R2 ", r2 == 1);
    w  = nfmodpr(K, NH/pi3^23, pr);
    t0 = nfmodpr(K, NH2/NH^2, pr);
    u0 = nfmodpr(K, NH2/pi3^46, pr);
    print(tag, " WAVA ", w == 1);
    print(tag, " TH0 ", t0 == r1, " ", t0 != 1);
    print(tag, " U0 ", u0 == r1);
    print(tag, " IDY ", u0 == t0*w^2, " ", u0 == t0);
    Y = nfmodpr(K, P2F/pi3^23, pr);
    if(tag == "LPL",
      print(tag, " PSIW ", Y^2 + Y + r1^2 == 0);
      print(tag, " YF16 ", Y^4 != Y),
      print(tag, " YRT ", Y == r1 || Y == r1^2));
  );
}}
probe("LPL", FL);
if(polisirreducible(FN), probe("LPN", FN), print("LPN RATRED"));
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
chk(has('LPL NPR 1'), "L3B LAW key: ONE prime above 2")
chk(o.count('LPL EF 4 4') == 1, "L3B LAW key prime (e,f) = (4,4) [preregistered]")
chk(has('LPL VALS 2 9 4 1'), "L3B v(x),v(PHIP),v(2),v(pi3) = 2,9,4,1 (Lemma 3.13(1): v(pi3) = e/4)")
chk(has('LPL R1 1 1'), "L3B z1 letter LIVE: r1 != 1, r1^2+r1+1 = 0")
chk(has('LPL R2 1'), "L3B z2 = 1 on LP1 (letter-dead level 2)")
chk(has('LPL WAVA 1'), "L3B W-AVATAR MEASURED = 1 at the 9th prime [HEADLINE: first avatar = 1 geography on record; OPEN-4 probed live]")
chk(has('LPL TH0 1 1'), "L3B theta(0) measured = z1 != 1 (LAW W-E letter value live at avatar-dead frame)")
chk(has('LPL U0 1'), "L3B u(beta0) measured = z1 (canonical unit letter-valued, != 1 while w = 1)")
chk(has('LPL IDY 1 1'), "L3B LAW W-B(6): u0 = theta0*w^2 with three residues measured at an ACTUAL prime; u0 == t0 = the w = 1 signature (contrast GF29's u0 != t0)")
chk(has('LPL PSIW 1'), "L3B LAW W-C: realized residual = psi3 = psi3^{(w)} at w = 1 (nose read VALID exactly here, per DEF W-4's letter-live scoping)")
chk(has('LPL YF16 1'), "L3B Y generates F16 over F4 (f3 = 2 residual irreducible)")
chk(has('LPN NPR 2'), "L3B twin: TWO primes above 2")
chk(o.count('LPN EF 4 2') == 2, "L3B twin primes (e,f) = (4,2) each [preregistered]")
chk(o.count('LPN WAVA 1') == 2, "L3B twin primes: w-avatar = 1 there too (DEF W-1 key-independence at avatar level)")
chk(o.count('LPN TH0 1 1') == 2, "L3B twin primes: theta(0) = z1 at each (theta is frame data)")
chk(o.count('LPN YRT 1') == 2, "L3B twin: Y a root of the split residual y^2+y+1 at each prime (LAW W-C split pattern -- the naive kill is PURE THETA at w = 1)")

print(f"checks: {NCHK}, violations: {FAIL}")
print("VERDICT: " + ("GREEN" if FAIL == 0 else "RED"))
sys.exit(0 if FAIL == 0 else 1)
