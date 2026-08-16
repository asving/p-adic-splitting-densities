#!/usr/bin/env python3
"""OM-10 LEG F — HYP.142 (GENHN-ERR-1): the corrected-node mu = 2 count
law at K = F_9 — the FIRST odd-characteristic f_1 = 2 contact.

Decorrelated from verification/openmath/genhn_f2_count_check.py (F_4):
fresh field (F_9 = F_3[y]/(y^2 - 2)), fresh implementation, and the
predictor's residual censuses are ENUMERATED over K x K rather than
taken from closed forms (non-textual leg per the extraction-corruption
rule).

The law under test (LEMMA GENHN-COUNT-RERUN, GENHN_PROOF_2026-08-08.md
dated proof completion 2026-08-12; the consumer sweep L2593: "the
ordinary mu = 2 stage law is the (2,K)-law at B = D'h, not at the old
numeric node S = e1 h"): the raw finite-node census of complete-K-slot
windows {dv(A_1) >= B + 1, dv(A_0) >= 2B + 1, heights <= cap} splits by
polygon + residual keys with
  - UND / SPLTAIL / RAM / 2SIDED counts = leading-digit censuses times
    free tails,
  - SPLITEQ / INERT counts = the residual-pair censuses of
    T^2 + a T + b over K times free tails,
  - each ALPHA (repeated-root) letter slice carrying the FULL child
    node census at kappa by refine transfer (the clause whose sealed
    S-node version was REFUTED by the F_4 certificate: sealed RAM 0 /
    UND-full vs actual child split).

Runs:
  smoke   genre (1,2,2): B = D' h = 2, cap = 6 (9^6 = 531,441 members)
  full    genre (1,2,2): B = 2, cap = 7 (9^8 = 43,046,721 members) —
          the ALPHA child window contains RAM content at cap 7, so the
          sealed-error mutant (alpha -> all-UND) is KILLED here
  mixed   genre (2,2,2): B = D' h = 4, cap = 9 (9^6) — the corrected
          floors at the mixed genre, odd characteristic (RAM/UND band)
Teeth:
  T-F9-SEAL  the sealed-error pattern (alpha slices lumped to UND)
             must mismatch the measured census (full run)
  T-F9-Q     the law with |K| -> Q = 3 must mismatch (smoke run)
  T-F9-SNODE the S-node window (node = e1 h) is a DIFFERENT window;
             at the mixed genre S = 2 != B = 4: the S-node law's
             volume disagrees with the measured B-window volume

Usage: python3 om10_f9_count.py [smoke|full|mixed|all]
"""
import sys
from collections import Counter

# ---------------------------------------------------------------------
# F_9 = F_3[y]/(y^2 - 2); elements 0..8 as a + 3b  <->  a + b*y
# ---------------------------------------------------------------------
K = 9
def _mk_tables():
    add = [[0] * K for _ in range(K)]
    mul = [[0] * K for _ in range(K)]
    for x in range(K):
        a, b = x % 3, x // 3
        for z in range(K):
            c, d = z % 3, z // 3
            add[x][z] = (a + c) % 3 + 3 * ((b + d) % 3)
            # (a+by)(c+dy) = ac + 2bd + (ad+bc) y
            mul[x][z] = (a * c + 2 * b * d) % 3 + 3 * ((a * d + b * c) % 3)
    return add, mul
ADD, MUL = _mk_tables()
NEG = [ADD[x].index(0) for x in range(K)]

def quad_roots(a, b):
    """roots of T^2 + a T + b over F_9 (b != 0)."""
    return [t for t in range(1, K)
            if ADD[ADD[MUL[t][t]][MUL[a][t]]][b] == 0]

# ---------------------------------------------------------------------
# the reader (node-agnostic polygon + residual + refine recursion)
# ---------------------------------------------------------------------

def read_member(A1, A0, cap, path=()):
    """A1, A0: tuples of F_9 digits indexed by height 0..cap."""
    w = next((i for i, d in enumerate(A1) if d), None)
    u = next((i for i, d in enumerate(A0) if d), None)
    if u is None:
        if w is None or 2 * w >= cap + 1:
            return path + ('UND',)
        return path + ('SPLTAIL(w=%d)' % w,)
    if w is not None and 2 * w < u:
        return path + ('2SIDED(w=%d,u=%d)' % (w, u),)
    if u % 2 == 1:
        return path + ('RAM(u=%d)' % u,)
    k = u // 2
    a_res = A1[k] if (w is not None and w == k) else 0
    b_res = A0[u]
    roots = quad_roots(a_res, b_res)
    if len(roots) == 2:
        return path + ('SPLITEQ(k=%d)' % k,)
    if len(roots) == 0:
        return path + ('INERT(k=%d)' % k,)
    s = roots[0]
    # translate Y -> Y' + T, T = s at height k:
    # A1' = A1 + 2T ; A0' = A0 + A1*T + T^2
    A1n = list(A1)
    A1n[k] = ADD[A1n[k]][MUL[2 % 3][s]]  # 2 in F_9 is 2
    A1n[k] = A1n[k] if True else A1n[k]
    A0n = list(A0)
    for i, d in enumerate(A1):
        if d and i + k <= cap:
            A0n[i + k] = ADD[A0n[i + k]][MUL[d][s]]
    if 2 * k <= cap:
        A0n[2 * k] = ADD[A0n[2 * k]][MUL[s][s]]
    return read_member(tuple(A1n), tuple(A0n), cap,
                       path + ('ALPHA(k=%d,s=%d)' % (k, s),))

# ---------------------------------------------------------------------
# the predictor (the lemma's clauses; residual censuses ENUMERATED)
# ---------------------------------------------------------------------

def node_volume(b, cap, ksize=K):
    return ksize ** (max(0, cap - b) + max(0, cap - 2 * b))

def residual_censuses():
    spl = ine = 0
    alpha = {}
    for a in range(K):
        for bb in range(1, K):
            r = quad_roots(a, bb)
            if len(r) == 2:
                spl += 1
            elif len(r) == 0:
                ine += 1
            else:
                alpha[(a, bb)] = r[0]
    return spl, ine, alpha

SPL_CENSUS, INE_CENSUS, ALPHA_PAIRS = residual_censuses()

def predict(b, cap, ksize=K):
    out = Counter()
    fuw = max(b + 1, (cap + 2) // 2)
    out[('UND',)] += ksize ** (cap - fuw + 1) if fuw <= cap else 1
    for w in range(b + 1, cap + 1):
        if 2 * w < cap + 1:
            out[('SPLTAIL(w=%d)' % w,)] += \
                (ksize - 1) * ksize ** (cap - w)
    for u in range(2 * b + 1, cap + 1):
        c0 = (ksize - 1) * ksize ** (cap - u)
        for w in range(b + 1, (u - 1) // 2 + 1):
            out[('2SIDED(w=%d,u=%d)' % (w, u),)] += \
                c0 * (ksize - 1) * ksize ** (cap - w)
        if u % 2 == 1:
            lo = max(b + 1, (u + 1) // 2)
            out[('RAM(u=%d)' % u,)] += \
                c0 * (ksize ** (cap - lo + 1) if lo <= cap else 1)
            continue
        k = u // 2
        tail = ksize ** ((cap - 2 * k) + (cap - k))
        # the residual censuses (enumerated over K x K for ksize = K;
        # closed forms for the mutant field size)
        if ksize == K:
            spl, ine = SPL_CENSUS, INE_CENSUS
            apairs = ALPHA_PAIRS
        else:
            spl = ine = 0
            apairs = {}
            for a in range(ksize):
                for bb in range(1, ksize):
                    rr = [t for t in range(1, ksize)
                          if (t * t + a * t + bb) % ksize == 0]
                    if len(rr) == 2:
                        spl += 1
                    elif len(rr) == 0:
                        ine += 1
                    else:
                        apairs[(a, bb)] = rr[0]
        out[('SPLITEQ(k=%d)' % k,)] += spl * tail
        out[('INERT(k=%d)' % k,)] += ine * tail
        child = predict(k, cap, ksize)
        for (a, bb), s in apairs.items():
            key0 = 'ALPHA(k=%d,s=%d)' % (k, s)
            for ck, cn in child.items():
                out[(key0,) + ck] += cn
    assert sum(out.values()) == node_volume(b, cap, ksize), \
        (b, cap, sum(out.values()), node_volume(b, cap, ksize))
    return out

# ---------------------------------------------------------------------
# measurement
# ---------------------------------------------------------------------

def measure(b, cap, progress=None):
    a1_pos = list(range(b + 1, cap + 1))
    a0_pos = list(range(2 * b + 1, cap + 1))
    got = Counter()
    n1, n0 = len(a1_pos), len(a0_pos)
    total = K ** (n1 + n0)
    zero1 = [0] * (cap + 1)
    step = 0
    for i1 in range(K ** n1):
        A1 = list(zero1)
        x = i1
        for p in a1_pos:
            A1[p] = x % K
            x //= K
        tA1 = tuple(A1)
        for i0 in range(K ** n0):
            A0 = list(zero1)
            x = i0
            for p in a0_pos:
                A0[p] = x % K
                x //= K
            got[read_member(tA1, tuple(A0), cap)] += 1
            step += 1
        if progress and i1 % progress == 0:
            print('  ... %d / %d outer' % (i1, K ** n1), flush=True)
    assert step == total
    return got

def compare(tag, got, want):
    keys = set(got) | set(want)
    bad = 0
    for k in sorted(keys):
        if got.get(k, 0) != want.get(k, 0):
            bad += 1
            print('MISMATCH [%s] %s: measured %d predicted %d'
                  % (tag, ' -> '.join(k), got.get(k, 0), want.get(k, 0)))
    print('%s: %d keys, %d mismatches — %s'
          % (tag, len(keys), bad, 'GREEN' if bad == 0 else 'RED'))
    return bad

def mutant_seal(pred):
    """the sealed-error pattern: every ALPHA slice lumped to UND-after-
    alpha (i.e. child keys erased)."""
    out = Counter()
    for k, n in pred.items():
        if any(x.startswith('ALPHA') for x in k):
            head = k[:max(i for i, x in enumerate(k)
                          if x.startswith('ALPHA')) + 1]
            out[head + ('UND',)] += n
        else:
            out[k] += n
    return out

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'smoke'
    nbad = 0
    if which in ('smoke', 'all'):
        print('== F9 smoke: genre (1,2,2), B = 2, cap = 6 ==', flush=True)
        got = measure(2, 6)
        want = predict(2, 6)
        nbad += compare('F9-SMOKE', got, want)
        # T-F9-Q tooth: the law at |K| -> 3 must mismatch
        want_q = predict(2, 6, ksize=3)
        tooth_fired = any(got.get(k, 0) != want_q.get(k, 0)
                          for k in set(got) | set(want_q))
        print('T-F9-Q: %s' % ('KILLED' if tooth_fired else
                              'NOT KILLED (VIOLATION)'))
        if not tooth_fired:
            nbad += 1
    if which in ('mixed', 'all'):
        print('== F9 mixed: genre (2,2,2), B = 4, cap = 9 ==', flush=True)
        got = measure(4, 9)
        want = predict(4, 9)
        nbad += compare('F9-MIXED', got, want)
        # T-F9-SNODE: the S-node (S = e1 h = 2) window volume differs
        sn_vol = node_volume(2, 9)
        b_vol = node_volume(4, 9)
        ok = (sum(got.values()) == b_vol and sn_vol != b_vol)
        print('T-F9-SNODE: %s (B-window %d, S-window %d)'
              % ('KILLED' if ok else 'NOT KILLED (VIOLATION)',
                 b_vol, sn_vol))
        if not ok:
            nbad += 1
    if which in ('full', 'all'):
        print('== F9 full: genre (1,2,2), B = 2, cap = 7 '
              '(43,046,721 members) ==', flush=True)
        got = measure(2, 7, progress=729)
        want = predict(2, 7)
        nbad += compare('F9-FULL', got, want)
        # T-F9-SEAL: the sealed-error mutant must mismatch at cap 7
        # (the ALPHA(k=3) child window carries RAM(u=7) content)
        wm = mutant_seal(want)
        fired = any(got.get(k, 0) != wm.get(k, 0)
                    for k in set(got) | set(wm))
        print('T-F9-SEAL: %s' % ('KILLED' if fired else
                                 'NOT KILLED (VIOLATION)'))
        if not fired:
            nbad += 1
        for k in sorted(set(got) | set(want)):
            print('  %-60s %12d' % (' -> '.join(k), got.get(k, 0)))
    print('VERDICT: %s' % ('GREEN' if nbad == 0 else 'RED (%d)' % nbad))

if __name__ == '__main__':
    main()
