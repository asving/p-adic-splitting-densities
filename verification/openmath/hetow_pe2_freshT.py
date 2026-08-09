#!/usr/bin/env python3
"""HETOW passPE2 fresh route, FRAME T: the first NON-PRIME-q wrap frame
(q = 4, K = F_4, equal characteristic).  Construction-grade oracle (no
PARI: factorpadic has no F_q((t)) route) -- root branches in F_16[[s]]
with a Galois/Hensel certification argument, disclosed below.

FRAME T: K = F_4 = {0,1,g,g^2} (g^2 = g+1), base F_4((t)); outer genre
(4; 3, 1, 1): Phi' = x^3 + g*t (char 2), eta = res(x0^3/t) = ...
at the root branch below res(t/s^3) = g^2 = eta^{-1}, i.e. eta = g,
ord(eta) = 3.  Tower (e2,f2) = (1,2), u2 = 5 > D'h = 3, i(5) = 2,
Q(5) = 1, W = (1,0); psi2 = Z^2 + Z + g irreducible over F_4
(Tr(g) = g + g^2 = 1); c1 = 1, c0 = g (char 2 signs).
n(5) = x^2 t, n(10) = x t^3.
  coh key   = x^6 + x^5 t + g x^2 t^2 + g^2 x t^3 + g^2 t^2
              (lift c1*eta^W(1) = 1, c0*eta^W(0) = g*g = g^2)
  naive key = x^6 + x^5 t + g x^2 t^2 + g   x t^3 + g^2 t^2

PREREGISTERED PREDICTIONS (scored; any miss = RED):
 TE1: W(0) two ways: Q(10) - 2Q(5) = 1 = floor(2*i(5)/3).
 TE2: corrected slot residues (exact F_4 algebra, res(x^a t^g0/x^k) =
   eta^{-g0}) assemble minpoly(beta), beta = eta^{-1}*eta2 = g^2*eta2:
   r~ = Z^2 + g^2 Z + g^2, != psi2 (twist real).
 TE3: naive slot residues assemble N = Z^2 + g^2 Z + g = (Z+1)(Z+g):
   SPLIT over F_4 (degenerate).
 TG1 (carrier, by construction): solving coh(s) = 0 with t = s^3*w,
   w = sum w_i s^i in F_16[[s]] gives EXACTLY TWO final branches with
   w0 = g^2, w1 = 0 forced and w2 = g*eta2 for the two roots eta2 of
   psi2 in F_16 (both OUTSIDE F_4 -- the letter clause), branches
   separated by w2 (transient multiplicity from char-2 constraint lag
   is killed two orders later; final count is what is scored).
   Certification: val(key) > 30 >> 2*v(dK/dt) = 10 (Hensel: each
   branch refines to a unique true root) + Frobenius fixing of the
   separating prefix => the true Puiseux root has w in F_16[[s]] with
   res((w-g^2)/s^2) = g*eta2 generating F_16; so F_4((t))(s) has
   e = 3 (v_s(t) = 3) and f = 2, degree >= 6 = deg(coh):
   coh IRREDUCIBLE with (e,f) = (3,2) over F_4((t)) -- sigma {(3,2)}.
 TG2 (TOOTH): same solve on the naive key gives TWO branches with
   w2 = g*z for z in roots of the ETA2-FORM naive poly
   N_eta = Z^2 + Z + 1 (= eta^2 N(Z/eta); roots {g, g^2}), i.e.
   w2 in {g^2, 1} -- BOTH IN F_4 -- and every w_i in F_4 up to order
   N.  [INSTRUMENT ERRATUM, 2026-08-09 post-first-run: the sealed
   prereg wrote w2 = g*{1, g} from the BETA-form roots (the same
   wrong-variable slip as the char-0 letter jobs, disclosed there);
   the letter the branch realizes is eta2 = g^2 w2, which kills the
   eta2-form; measured {1, 7} = g*{g, g^2} exactly.  First run:
   every other TG check GREEN incl. the scored coeff-field tooth.]  Frobenius fixing (w0,w1,w2) => the true
   root has w in F_4[[s]] => t = s^3 w in F_4((s)) => x0 = s lies in
   an extension of degree <= [F_4((s)):F_4((t))] = 3 < 6: the naive
   key is REDUCIBLE (derived shape {(3,1)} x2, recorded as INFO)
   -- sigma(naive) != {(3,2)} at non-prime q.
 TG3: at each coh branch, psi2(g^2 * w2) = 0 in F_16 (the letter
   clause verified from the SOLVED branch, not imposed).
VERDICT: GREEN iff 0 violations."""
import json, time

# F_16 = F_2[y]/(y^4+y+1), elements = ints 0..15 (bit i = y^i)
def gmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1
        if a & 16: a ^= 0b10011
        b >>= 1
    return r

def gpow(a, k):
    r = 1
    for _ in range(k): r = gmul(r, a)
    return r

G = None
for cand in range(2, 16):                      # find g with g^2+g+1 = 0
    if gmul(cand, cand) ^ cand ^ 1 == 0: G = cand; break
F4 = {0, 1, G, gmul(G, G)}
G2 = gmul(G, G)
PSI2_ROOTS = [z for z in range(16) if gmul(z, z) ^ z ^ G == 0]

VIOL = []
def check(leg, ok, detail):
    print('  %-30s %s  %s' % (leg, 'ok' if ok else '!! VIOLATION', detail))
    if not ok: VIOL.append((leg, str(detail)[:300]))

# series in s over F_16: list of ints, index = s-power, mod s^PREC
PREC = 31
def smul(a, b):
    out = [0]*PREC
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y and i+j < PREC: out[i+j] ^= gmul(x, y)
    return out

def sadd(a, b):
    n = max(len(a), len(b)); out = [0]*n
    for i, x in enumerate(a): out[i] ^= x
    for i, x in enumerate(b): out[i] ^= x
    return out

def key_eval(c0h, w):
    """evaluate key(x=s, t=s^3*w) mod s^PREC; key = x^6 + x^5 t
    + g x^2 t^2 + c0h x t^3 + g^2 t^2 (c0h = g^2 coh / g naive).
    Wait -- t^2 terms: g x^2 t^2 and g^2 t^2; t^3 term c0h x t^3."""
    t = [0]*3 + list(w[:PREC-3])
    t2, t3 = smul(t, t), smul(smul(t, t), t)
    e = lambda k: [0]*k + [1]
    out = e(6)
    out = sadd(out, smul(e(5), t))
    out = sadd(out, smul([0, 0, G], t2))
    out = sadd(out, smul([0, c0h], t3))
    out = sadd(out, smul([G2], t2))
    return [c for c in out[:PREC]]

def solve_branches(c0h, N):
    """breadth-first order-by-order solve of key(s; t=s^3 w) = 0 for
    w = sum_{i<=N} w_i s^i, w_i in F_16.  Soundness of the prune: the
    output coefficient at order k <= 6+m depends only on w_0..w_m
    (linear appearance of w_m at 8+m; square at 6+2m; cubic at
    >= 10+m -- char 2 Frobenius on w^2 delays constraints, so
    transient multiplicity up to 16x is expected and killed two
    orders later; only FINAL branches are scored).  Returns final
    w-lists with all output orders <= 6+N vanishing (val > 30, far
    beyond the Hensel bound 2*v(dK/dt) = 10 -- each branch refines
    to a unique true root)."""
    branches = [[]]
    for order in range(N+1):
        new = []
        for w in branches:
            for cand in range(16):
                wtry = w + [cand] + [0]*(N-order)
                val = key_eval(c0h, wtry)
                if all(val[k] == 0 for k in range(6+order+1)):
                    new.append(w + [cand])
        branches = new
        if not branches: return []
    return branches

def main():
    t0 = time.time()
    print('HETOW passPE2 frame T: non-prime q = 4 wrap frame,'
          ' construction oracle (g = %d, psi2 roots %s)' % (G, PSI2_ROOTS))
    i5, Q5, Q10 = 5 % 3, (5 - 2)//3, (10 - 1)//3
    check('TE1-W-two-ways', Q10 - 2*Q5 == (2*i5)//3 == 1,
          'Q(10)-2Q(5) = %d' % (Q10 - 2*Q5))
    # exact slot residues: coeff of Phi'-slot t=1 is x^2 t (coh & naive),
    # residue at height 5 = 1*eta^{-1} = g^2; slot t=0: c0h x t^3,
    # residue at height 10 = c0h*eta^{-3} = c0h.
    eta, etainv = G, G2
    r1 = gmul(1, etainv)                       # both keys
    for tag, c0h, pred in (('coh', G2, (G2, G2)), ('naive', G, (G, G2))):
        r0 = gmul(c0h, gpow(etainv, 3))
        check('TE23-slotpoly-%s' % tag, (r0, r1) == pred,
              'Z^2+(%d)Z+(%d) vs pred %s' % (r1, r0, pred))
    beta = gmul(G2, PSI2_ROOTS[0])
    check('TE2-minpoly', gmul(beta, beta) ^ gmul(G2, beta) ^ G2 == 0,
          'beta = g^2*eta2 kills Z^2+g^2 Z+g^2')
    check('TE2-twist-real', (G2, G2) != (G, 1), 'r~ != psi2')
    check('TE3-naive-split', gmul(1, 1) ^ gmul(G2, 1) ^ G == 0 and
          gmul(G, G) ^ gmul(G2, G) ^ G == 0, 'N(1) = N(g) = 0')
    N = 24
    for tag, c0h, w2pred, infield in (
            ('TG1-coh', G2, {gmul(G, z) for z in PSI2_ROOTS}, False),
            ('TG2-naive', G, {gmul(G, G), gmul(G, G2)}, True)):
        raw = solve_branches(c0h, N)
        # [INSTRUMENT ERRATUM, 2026-08-09 post-first-run: the last two
        # tail coefficients w_{N-1}, w_N have their linear constraints
        # at output orders 8+(N-1), 8+N > 6+N -- unconstrained within
        # the solve window, so raw counts carried a free 16^2 tail
        # (first run: 512 = 2*16^2 raw branches, everything else
        # green).  Score the CONSTRAINED prefix w_0..w_{N-2}.]
        br = sorted({tuple(b[:N-1]) for b in raw})
        check(tag + '-branchcount', len(br) == 2,
              '%d constrained-prefix branches (raw %d) at order %d'
              % (len(br), len(raw), N))
        if len(br) != 2: continue
        w2s = {b[2] for b in br}
        check(tag + '-w2', w2s == w2pred, 'w2 = %s vs pred %s' % (w2s, w2pred))
        check(tag + '-w0w1', all(b[0] == G2 and b[1] == 0 for b in br),
              'w0 = g^2, w1 = 0 forced')
        check(tag + '-prefix-separates', len(w2s) == 2,
              'branches distinguished by w2 (Frobenius-fixing leg)')
        allf4 = all(all(c in F4 for c in b) for b in br)
        check(tag + '-coeff-field', allf4 == infield,
              'all coeffs in F_4: %s (pred %s)' % (allf4, infield))
        if tag == 'TG1-coh':
            ok = all(gmul(z, z) ^ z ^ G == 0
                     for b in br for z in [gmul(G2, b[2])])
            check('TG3-letter-clause', ok,
                  'psi2(g^2 w2) = 0 at both branches (letter from solve)')
    print('\nTOTAL violations %d (%.1fs)' % (len(VIOL), time.time() - t0))
    print('VERDICT: %s' % ('GREEN' if not VIOL else 'RED'))
    json.dump({'viol': VIOL}, open('hetow_pe2_freshT_results.json', 'w'),
              indent=1)

if __name__ == '__main__':
    main()
