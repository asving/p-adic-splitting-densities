#!/usr/bin/env python3
"""wframe_note_checks.py — SEALED instrument for WFRAME_NOTE_2026-08-10.md (§7).

RE-VERIFIES the note's displayed laws at the committed frames LD1, LD3,
GA1, GA3 (+ the GA3* record polynomial), on FRESH code: exact Fraction
value checks, integer exponent-lattice splits, and F4 polynomial algebra.
No PARI, no reuse of any committed runner's code. Route: A-route only
(the avatar<->w interpretation leg's status is carried in the note S4
preamble; this instrument checks the LAWS' algebra + the committed pins).

JOINT FRAME (R.3): LD1 = LP1 tower with f1 = 2 (z1 in F4\\F2) AND
measured w != 1 AND letter-live slot (theta(0) != 1) — the joint
geography (f1 = 2 ∧ w != 1) the T5 charge requires.

FRAME DATA (committed; GENTOW2_passPE6 runner header + note S4):
  LP1: lam1 = 1/2, u2 = 9, w2+lam2 = 9/4, V2 = 4, pi3 = PHIP/x^4;
       letters: z1 live (order 3), z2 = 1.
  GB : lam1 = 1/2, u2 = 5, w2+lam2 = 5/4, V2 = 2, pi3 = PHIP/x^2;
       letters: z1 = 1, z2 live (order 3).
  Monomial vectors (x-exp, 2-exp, PHIP-exp):
  LD1 (e3,f3,u3 = 1,2,19): nhat2(19) = 4x*PHIP = (1,2,1);
       nhat2(38) = 512x = (1,9,0).
  LD3 (2,1,37): nhat2(37) = 128*PHIP = (0,7,1).
  GA1 (1,2,21): nhat2(21) = 16*PHIP = (0,4,1); nhat2(42) = 1024x = (1,10,0).
  GA3 (2,2,41): nhat2(41) = 512*PHIP = (0,9,1); nhat2(82) = 2^20*x = (1,20,0).
  gamma1 = x^2/2 = (2,-1,0); gamma2 = PHIP^2/x^{u2} = (-u2,0,2);
  split r = j*gamma1 + k*gamma2, avatar = z1^j z2^k (letter exps mod 3).

PREREGISTERED PREDICTIONS (hand-derived from the note's laws BEFORE the
first run; teeth below must BITE):
  W-avatar splits (j,k) and letter values:
    LD1 (77,2,-18) -> (-2,-9)  -> z1^1  != 1
    LD3 (148,7,-36)-> (-7,-18) -> z1^2  != 1
    GA1 (42,4,-20) -> (-4,-10) -> z2^2  != 1
    GA3 (82,9,-40) -> (-9,-20) -> z2^1  != 1
  theta(0) splits: LD1 (-1,5,-2) -> (-5,-1) -> z1; GA1 (1,2,-2) ->
    (-2,-1) -> z2^2; GA3 (1,2,-2) -> (-2,-1) -> z2^2; LD3 trivial (f3=1);
    theta(top) = 1 at LD1/GA1/GA3.
  IDY (LAW W-B at slot 0): theta(0)*w^2 = 1 (LD1), 1 (GA1), z2 (GA3)
    == the PE6-measured u(beta0) pins; direct u(beta0)-avatar splits:
    LD1 (153,9,-38) -> (-9,-19) -> 1; GA1 (85,10,-42) -> (-10,-21) -> 1;
    GA3 (165,20,-82) -> (-20,-41) -> z2.
  SUBST (LAW W-A/W-C in F4, char 2):
    LD1: P = y^2+z*y+z, w = z    -> w^2 P(y/w) = y^2+z^2*y+1 (PE6 pin);
         both irreducible /F4 (0 roots).
    LD2: per-height digits (z,z^2) -> realized y^2+z*y+1 (PE4 decode MP2),
         irreducible (PE4 measured ONE (4,4) prime); nose target
         y^2+z*y+z^2 = (y+1)(y+z^2) SPLIT — the nose FAILS here.
    GA1: P = y^2+y+1 (split: roots z,z^2), w = z^2 -> y^2+z^2*y+z
         (PE6 pin, = (y+1)(y+z)); pattern preserved (2 roots each).
    GA3*: psi3 = y^2+y+z2, w = z2 -> psi3^{(w)} = y^2+z2*y+1; both
         irreducible /F4 (PE3 pin: ONE (8,4) prime; NOSE tooth fired).
TEETH (each must BITE, i.e. the perturbed claim must FAIL):
  T-W1    w := 1 in IDY at GA3: z2^2 != z2.
  T-CONST LD1 vs LD3 and GA1 vs GA3 avatar equality both FALSE.
  T-NOSE  LD2 nose prediction (split) != measured pattern (irreducible).
  T-GAMMA gamma2 -> (-u2-1,0,2) breaks the LD1 W-split consistency.
Exit 0 iff violations == 0 AND all 4 teeth bite. RED runs are kept.
"""
from fractions import Fraction as Fr

CHECKS = []
def chk(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print(f"CHECK {name:34s} {'PASS' if ok else 'FAIL'} {detail}")

# ---------- towers & frames ----------
TOWERS = {
    'LP1': dict(lam1=Fr(1,2), u2=9, wl=Fr(9,4), pi3=(-4,0,1), live='z1'),
    'GB':  dict(lam1=Fr(1,2), u2=5, wl=Fr(5,4), pi3=(-2,0,1), live='z2'),
}
FRAMES = {
    'LD1': dict(tw='LP1', e3=1, f3=2, u3=19, n1=(1,2,1),  n2=(1,9,0)),
    'LD3': dict(tw='LP1', e3=2, f3=1, u3=37, n1=(0,7,1),  n2=None),
    'GA1': dict(tw='GB',  e3=1, f3=2, u3=21, n1=(0,4,1),  n2=(1,10,0)),
    'GA3': dict(tw='GB',  e3=2, f3=2, u3=41, n1=(0,9,1),  n2=(1,20,0)),
}
PRED_W   = {'LD1': ('z1',1), 'LD3': ('z1',2), 'GA1': ('z2',2), 'GA3': ('z2',1)}
PRED_TH0 = {'LD1': ('z1',1), 'GA1': ('z2',2), 'GA3': ('z2',2)}
PRED_U0  = {'LD1': ('z1',0), 'GA1': ('z2',0), 'GA3': ('z2',1)}  # exp mod 3

def vsub(a, b, m=1):  # a - m*b componentwise
    return tuple(x - m*y for x, y in zip(a, b))
def val(tw, v):       # exact value of the monomial vector
    t = TOWERS[tw]
    return v[0]*t['lam1'] + v[1] + v[2]*t['wl']
def split(tw, v, g2=None):
    u2 = TOWERS[tw]['u2']; g2 = g2 or (-u2, 0, 2)
    j = -v[1]
    if v[2] % g2[2]: return None
    k = v[2]//g2[2]
    if j*2 + k*g2[0] != v[0]: return None
    return (j, k)
def avatar(tw, jk):   # letter value: exponent mod 3 on the live letter
    j, k = jk
    return (TOWERS[tw]['live'], (j if TOWERS[tw]['live']=='z1' else k) % 3)

# ---------- F4 = {0,1,2,3} with 2 = z, 3 = z+1 = z^2; char 2 ----------
MUL = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
def fm(a,b): return MUL[a][b]
def fa(a,b): return a ^ b
def zpow(e): return [1,2,3][e % 3]
def peval(p, x):      # p = [c0, c1, c2] low-to-high
    acc, xp = 0, 1
    for c in p:
        acc = fa(acc, fm(c, xp)); xp = fm(xp, x)
    return acc
def roots(p): return [x for x in range(4) if peval(p, x) == 0]
def twist(p, w):      # w^deg * p(y/w) for monic deg-2 p = [c0,c1,1]
    return [fm(p[0], fm(w, w)), fm(p[1], w), 1]

# ---------- 1. W-avatar: value-0, split, letter value, != 1 ----------
for f, d in FRAMES.items():
    tw = d['tw']
    r = vsub(d['n1'], TOWERS[tw]['pi3'], d['u3'])
    chk(f'{f}.WVAL', val(tw, r) == 0, f'ratio={r} val={val(tw,r)}')
    jk = split(tw, r)
    chk(f'{f}.WSPLIT', jk is not None, f'(j,k)={jk}')
    av = avatar(tw, jk)
    chk(f'{f}.WAVA', av == PRED_W[f], f'avatar={av[0]}^{av[1]}')
    chk(f'{f}.WNE1', av[1] % 3 != 0, 'w-avatar != 1')

# ---------- 2. theta(0) and theta(top) (f3 = 2 frames) ----------
TH0 = {}
for f in ('LD1', 'GA1', 'GA3'):
    d = FRAMES[f]; tw = d['tw']
    r = vsub(d['n2'], d['n1'], 2)          # nhat2(2u3)/nhat2(u3)^2
    chk(f'{f}.THVAL', val(tw, r) == 0, f'ratio={r}')
    jk = split(tw, r); av = avatar(tw, jk)
    chk(f'{f}.TH0', av == PRED_TH0[f], f'theta(0)={av[0]}^{av[1]} (j,k)={jk}')
    TH0[f] = av
    rt = vsub(d['n1'], d['n1'], 1)         # top slot: trivial ratio
    chk(f'{f}.THTOP', split(tw, rt) == (0, 0), 'theta(top)=1')
chk('LD3.THTRIV', FRAMES['LD3']['f3'] == 1, 'single slot = top: no cocycle live')

# ---------- 3. IDY — LAW W-B (6) at slot 0: u(b0) = theta(0)*w^f3 ----------
for f in ('LD1', 'GA1', 'GA3'):
    d = FRAMES[f]; tw = d['tw']
    # direct recompute of the u(beta0)-avatar: nhat2(2u3)/pi3^(2u3)
    r = vsub(d['n2'], TOWERS[tw]['pi3'], 2*d['u3'])
    chk(f'{f}.U0VAL', val(tw, r) == 0, f'ratio={r}')
    jk = split(tw, r); av = avatar(tw, jk)
    chk(f'{f}.U0', av[1] == PRED_U0[f][1], f'u(b0)={av[0]}^{av[1]}')
    lhs = av[1] % 3                        # measured-object exponent
    rhs = (TH0[f][1] + 2*PRED_W[f][1]) % 3 # theta(0)*w^2 exponent
    chk(f'{f}.IDY', lhs == rhs, f'u(b0)==theta0*w^2: {lhs}=={rhs} mod 3')

# ---------- 4. SUBST — LAW W-A / W-C in F4 (z = 2, z^2 = 3) ----------
# LD1: P = y^2+z*y+z, w = z -> y^2+z^2*y+1 (PE6 pin); both irreducible.
P = [2, 2, 1]; T = twist(P, 2)
chk('LD1.SUB', T == [1, 3, 1], f'w^2P(y/w)={T} pin=[1,3,1]')
chk('LD1.MONIC', T[2] == 1 and T[0] != 0, 'monic, const != 0')
chk('LD1.IRRPAT', len(roots(P)) == 0 and len(roots(T)) == 0, 'pattern preserved (irr)')
# LD2: per-height digits (z, z^2): realized = y^2 + th1*c1*y + th0*c0
LD2R = [fm(2, 3), fm(1, 2), 1]             # theta0=z * c0=z^2 ; theta1=1 * c1=z
chk('LD2.REAL', LD2R == [1, 2, 1], f'realized={LD2R} pin=[1,2,1] (decode MP2)')
chk('LD2.MEASIRR', len(roots(LD2R)) == 0, 'measured pattern: ONE (4,4) prime = irr')
NOSE = [3, 2, 1]                           # target psi3 = y^2+z*y+z^2
chk('LD2.NOSESPLIT', len(roots(NOSE)) == 2, 'nose target splits (y+1)(y+z^2)')
# GA1: P = y^2+y+1 (split), w = z^2 -> y^2+z^2*y+z (PE6 pin); split kept.
P = [1, 1, 1]; T = twist(P, 3)
chk('GA1.SUB', T == [2, 3, 1], f'w^2P(y/w)={T} pin=[2,3,1]')
chk('GA1.SPLITPAT', len(roots(P)) == 2 and len(roots(T)) == 2, 'pattern preserved (split)')
chk('GA1.ROOTMAP', sorted(fm(3, r) for r in roots(P)) == sorted(roots(T)), 'roots scale by w')
# GA3*: psi3 = y^2+y+z2, w = z2 -> y^2+z2*y+1; both irreducible (PE3 pin).
P = [2, 1, 1]; T = twist(P, 2)
chk('GA3s.SUB', T == [1, 2, 1], f'psi^{{(w)}}={T} pin=[1,2,1]')
chk('GA3s.IRRPAT', len(roots(P)) == 0 and len(roots(T)) == 0, 'ONE (8,4) prime = irr, both')
chk('GA3s.CONST', T[0] == fm(fm(2, 2), 2) and T[0] != 0, 'const = w^2*psi(0) != 0')

# ---------- teeth ----------
teeth = []
def tooth(name, bites, detail=""):
    teeth.append((name, bool(bites)))
    print(f"TOOTH {name:12s} {'BITES' if bites else 'DUD'} {detail}")
tooth('T-W1', (TH0['GA3'][1] + 0) % 3 != PRED_U0['GA3'][1],
      'w:=1 at GA3: theta0*1 = z2^2 != z2 = u(b0)')
avs = {f: avatar(FRAMES[f]['tw'], split(FRAMES[f]['tw'],
       vsub(FRAMES[f]['n1'], TOWERS[FRAMES[f]['tw']]['pi3'], FRAMES[f]['u3'])))
       for f in FRAMES}
tooth('T-CONST', avs['LD1'] != avs['LD3'] and avs['GA1'] != avs['GA3'],
      'w constant-per-tower FALSE twice')
tooth('T-NOSE', len(roots(NOSE)) != len(roots(LD2R)),
      'nose split-prediction != measured irreducible at LD2')
r = vsub(FRAMES['LD1']['n1'], TOWERS['LP1']['pi3'], 19)
tooth('T-GAMMA', split('LP1', r, g2=(-10, 0, 2)) is None,
      'perturbed gamma2 breaks the LD1 split')

nv = sum(1 for _, ok in CHECKS if not ok)
nb = sum(1 for _, b in teeth if not b)
print(f"checks: {len(CHECKS)}, violations: {nv}; teeth: {len(teeth)}, duds: {nb}")
print("VERDICT:", "GREEN" if nv == 0 and nb == 0 else "RED")
raise SystemExit(0 if nv == 0 and nb == 0 else 1)
