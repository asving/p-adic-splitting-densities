#!/usr/bin/env python3
"""POST-SEAL DIAGNOSTIC (pass ITERLAW3-PE2; labeled per the note's S8 rule:
NOT a prereg, NOT a proof step, NOT part of any seal).

Targeted mini-check of the ERRATA ROUND 1 (f9daca0) S6.3-erratum witnesses in
lean/notes/openmath/ITERLAW3_PROOF_2026-08-08.md ["errata round 1, 2026-08-03;
convergent findings PC-F2 [CRITICAL] = PE-F1 [CRITICAL]"]:

  (i)  the e2 = 1 tower (3,2,1)(2,1,1)(1,1,1)/Z5 "realizes 4 DCX pairs per
       W1xW1-equivalent block";
  (ii) the e1 = 1 battery tower TW2 = (4,1,1)(1,3,1)(2,1,1)/F3[[t]]
       "realizes 48";
  and on those DCX pairs the THEOREM DISPLAY still holds (instance data for
  the open lemma (W-MULT-3-DCX) at the degeneration corners -- NOT proof
  coverage), together with the erratum's "genuinely unconditional NOW"
  integer-level reductions (CX: d3=0, b2=gamma, D2=delta2, Sig=gamma2*delta2,
  D1=accepted exponent; CW: D2=0, Sig=delta3*gamma3) on EVERY pair of both
  blocks, and c3 == embed(c2) on the CX DCX pairs (instance-true, displayed
  as conditional by the erratum).

ANALYTIC EXPECTATIONS derived from the note's S0.4/S4.7 DCX predicate before
running (asserted below):
  CXW  (e,h,g) = (3,2,1)(2,1,1)(1,1,1), E3 = 6: gamma2 = 2*(3*1*2)+1 = 13,
       l0 = 2 (2*2 = 4 == 1 mod 3), s(gamma2) = 2*13 mod 3 = 2. DCX needs
       delta1 = 1 and S1 + 2 >= 6, i.e. S1 = 4 = 2*(e0-1): (s1,s1') = (2,2);
       s2 = s2' = e1-1 = 1; s3 = s3' = 0 forced (e2 = 1). One split-class
       pair per E3xE3 sub-block; the 2-window battery has 4 sub-blocks
       => 4 DCX pairs per battery block.
  TW2  (e,h,g) = (4,1,1)(1,3,1)(2,1,1), E3 = 8: gamma2 = 1*(4*1*1)+3 = 7,
       l0 = 1, s(gamma2) = 7 mod 4 = 3. DCX needs S1 + 3 >= 8, i.e.
       S1 >= 5: (s1,s1') in {(2,3),(3,2),(3,3)} (3 combos); s2 = s2' = 0
       AUTOMATIC (e1 = 1 -- the locus-ENLARGING clause of the erratum);
       (s3,s3') free in {0,1}^2 (4 combos). 12 per sub-block => 48 per
       battery block.

Harness: imports the PE reimplementation (iterlaw3_pe_reimpl.py), whose
byte-exact reproduction (3,344 pairs / 55,186 checks / 0 violations) was
re-established by this pass immediately before this file was written.
Deterministic: fixed window shift M = 5, no randomness.

Verifier: Fable, pass ITERLAW3-PE2 (errata-round-1 verification arc, round 2).
Wallclock 2026-08-03 (campaign 2026-08-08).
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from iterlaw3_pe_reimpl import (Tower3, OZp, OFpt, Ctr, eq12, case_of,
                                dcx_record, x_mul, x_pow, x_scal, x_deg,
                                ic)

M_SHIFT = 5  # fixed two-window shift (deterministic)

def build_window_fixed(T):
    G0 = 0
    while not all(T.split(g)['u1'] >= 0 for g in range(G0, G0 + T.E3)):
        G0 += T.E3
        assert G0 < 10000 * T.E3
    W = (list(range(G0, G0 + T.E3)) +
         list(range(G0 + M_SHIFT * T.E3, G0 + (M_SHIFT + 1) * T.E3)))
    return W, G0

def subblock(T, G0, g):
    return 0 if g < G0 + T.E3 else 1

def run_tower(T, expect):
    """expect = dict(s_gamma2, dcx_per_block, dcx_per_subblock, classes)
    classes = set of ((s1,s2,s3),(s1',s2',s3')) admissible split-class pairs."""
    O = T.O
    C = Ctr()
    W, G0 = build_window_fixed(T)
    okA = (T.s_gamma2 == expect['s_gamma2'])
    print('%s: E3=%d gamma2=%d s(gamma2)=%d (expected %d) %s'
          % (T.name, T.E3, T.gamma2, T.s_gamma2, expect['s_gamma2'],
             'OK' if okA else '** MISMATCH **'))
    cache = {}
    def getv(g):
        if g not in cache:
            d = T.split(g)
            assert d['u1'] >= 0
            poly = T.anchor_poly(d)
            v, w3g, reads, _ = T.val3(poly)
            assert v == T.K3val(0, T.eps2(d['b2']), T.eps1(d['b1'])) \
                and w3g == g and len(reads) == 1 and reads[0][0] == 0
            cache[g] = (v, poly)
        return cache[g]
    dcx = []            # (g, gp, subblock-pair, class-pair)
    sub_counts = {}     # (ia, ib) -> count of DCX pairs
    nbad_int = 0
    dcx_thm = dcx_wm = dcx_prod = dcx_shape = dcx_q1 = dcx_ovf = 0
    dcx_cx_c2 = 0       # CX only: c3 == embed(c2) on DCX pairs
    rec = []
    npairs = 0
    for g in W:
        for gp in W:
            npairs += 1
            d, dP, dS = T.split(g), T.split(gp), T.split(g + gp)
            S3 = d['s3'] + dP['s3']; S2 = d['s2'] + dP['s2']
            S1 = d['s1'] + dP['s1']; U = d['u1'] + dP['u1']
            d3 = S3 // T.e2; d2 = S2 // T.e1
            B2 = d['b2'] + dP['b2']; B1 = d['b1'] + dP['b1']
            num2 = S2 - dS['s2'] + T.l1 * T.gamma3 * d3
            assert num2 % T.e1 == 0
            D2 = num2 // T.e1
            Sig = D2 * T.gamma2 + d3 * T.gamma3 * (T.l1p - T.l1 * T.w1Phi1)
            num1 = S1 - dS['s1'] + T.l0 * Sig
            assert num1 % T.e0 == 0
            D1 = num1 // T.e0
            # --- erratum's "genuinely unconditional NOW" integer reductions ---
            if T.e2 == 1:  # CX integer-level
                naccp = S1 - dS['s1'] + T.l0 * T.gamma2 * d2
                if not (d3 == 0 and d['b2'] == g and dP['b2'] == gp
                        and D2 == d2 and Sig == T.gamma2 * d2
                        and naccp % T.e0 == 0 and D1 == naccp // T.e0):
                    nbad_int += 1
            if T.e1 == 1:  # CW integer-level
                if not (D2 == 0 and Sig == d3 * T.gamma3):
                    nbad_int += 1
            # --- classification (reimpl's independent predicates) ---
            case, isdcx = case_of(T, d, dP, C, (T.name, g, gp))
            if not isdcx:
                continue
            clsa = (d['s1'], d['s2'], d['s3'])
            clsb = (dP['s1'], dP['s2'], dP['s3'])
            key = (subblock(T, G0, g), subblock(T, G0, gp))
            sub_counts[key] = sub_counts.get(key, 0) + 1
            dcx.append((g, gp, key, (clsa, clsb)))
            if (clsa, clsb) not in expect['classes']:
                print('  ** DCX pair OUTSIDE the erratum classes: %s' %
                      str((g, gp, clsa, clsb)))
                nbad_int += 1
            # --- instance data on the DCX pair (open lemma; NOT proof) ---
            vg, pg = getv(g); vgp, pgp = getv(gp); vS, pS = getv(g + gp)
            P = x_mul(O, pg, pgp)
            vP, w3P, readsP, devP = T.val3(P)
            inner = T.K1.mul(T.K1.pow(T.z1, S1 // T.e0), T.eps1(B1))
            mid = T.K2.mul(T.K2.pow(T.z2, d2), T.eps2(B2))
            wm_ok = (vP == T.K3val(d3, mid, inner))
            prod_ok = (vP == T.K3.mul(T.K3.pow(T.zbar, d3),
                                      T.K3.mul(vg, vgp)))
            shape_ok = (w3P == g + gp and len(readsP) == 1
                        and readsP[0][0] == d3)
            c3 = T.K3.mul(vP, T.K3.inv(vS))
            pred = T.K3val(d3, T.K2.pow(T.z2, D2), T.K1.pow(T.z1, D1))
            thm_ok = (c3 == pred)
            dcx_thm += thm_ok; dcx_wm += wm_ok
            dcx_prod += prod_ok; dcx_shape += shape_ok
            dcx_record(T, case, S1, S2, S3, U, thm_ok, wm_ok, prod_ok,
                       shape_ok, devP, rec, (T.name, g, gp))
            dcx_q1 += rec[-1]['q1_nonzero']
            dcx_ovf += rec[-1]['naive_E0_overflows']
            if T.e2 == 1:
                v2P = T.R2v(P)[0]
                c2 = T.K2.mul(v2P, T.K2.inv(T.R2v(pS)[0]))
                acc2 = T.K2.mul(T.K2.pow(T.z2, d2),
                                T.K2.embed(T.K1.pow(T.z1, D1)))
                dcx_cx_c2 += (c3 == T.e23(c2) and c2 == acc2)
    n = len(dcx)
    okB = (n == expect['dcx_per_block'])
    okC = all(sub_counts.get((a, b), 0) == expect['dcx_per_subblock']
              for a in (0, 1) for b in (0, 1))
    okD = (dcx_thm == dcx_wm == dcx_prod == dcx_shape == dcx_q1
           == dcx_ovf == n)
    okE = (nbad_int == 0)
    okF = (T.e2 != 1 or dcx_cx_c2 == n)
    print('  battery block %d pairs (2 windows, M=%d): DCX = %d '
          '(expected %d) %s' % (npairs, M_SHIFT, n, expect['dcx_per_block'],
                                'OK' if okB else '** MISMATCH **'))
    print('  per E3xE3 sub-block: %s (expected %d each) %s'
          % (sorted(sub_counts.items()), expect['dcx_per_subblock'],
             'OK' if okC else '** MISMATCH **'))
    print('  DCX split-classes: %s'
          % sorted(set(cp for _, _, _, cp in dcx)))
    print('  ON the DCX pairs (instance data for (W-MULT-3-DCX), open): '
          'thm %d/%d wmult %d/%d prod %d/%d shape %d/%d Q1!=0 %d/%d '
          'naive-E0-overflow %d/%d %s'
          % (dcx_thm, n, dcx_wm, n, dcx_prod, n, dcx_shape, n, dcx_q1, n,
             dcx_ovf, n, 'OK' if okD else '** FAIL **'))
    if T.e2 == 1:
        print('  CX c3 == embed(c2) == accepted display on DCX pairs: %d/%d %s'
              % (dcx_cx_c2, n, 'OK' if okF else '** FAIL **'))
    print('  integer-level reductions (erratum "unconditional NOW") bad: %d %s'
          % (nbad_int, 'OK' if okE else '** FAIL **'))
    tot, bad = C.total()
    ok = okA and okB and okC and okD and okE and okF and bad == 0
    return ok, dict(tower=T.name, pairs=npairs, dcx=n,
                    expected=expect['dcx_per_block'],
                    sub_counts={str(k): v for k, v in sorted(sub_counts.items())},
                    thm=dcx_thm, wmult=dcx_wm, prod=dcx_prod, shape=dcx_shape,
                    q1=dcx_q1, overflow=dcx_ovf,
                    cx_c2=(dcx_cx_c2 if T.e2 == 1 else None),
                    int_bad=nbad_int, records=rec)

def main():
    print('=' * 78)
    print('ITERLAW3-PE2 mini-check: the S6.3-erratum (E1) DCX witnesses '
          '(post-seal diagnostic)')
    print('=' * 78)
    # (i) the erratum's CX witness: (3,2,1)(2,1,1)(1,1,1)/Z5 (e2 = 1)
    CXW = Tower3('CXW-Z5-e2is1', OZp(5), [1, 1],
                 (3, 2, lambda K: [ic(K, 2), K.one()]),
                 (2, 1, lambda K: [ic(K, 2), K.one()]),
                 (1, 1, lambda K: [ic(K, 3), K.one()]))
    assert not CXW.welldef_bad
    # DCX classes: ((2,1,0),(2,1,0)) only
    exp_cx = dict(s_gamma2=2, dcx_per_block=4, dcx_per_subblock=1,
                  classes={((2, 1, 0), (2, 1, 0))})
    # (ii) the erratum's CW witness: TW2 = (4,1,1)(1,3,1)(2,1,1)/F3[[t]],
    # spec VERBATIM from the PE battery roster (iterlaw3_pe_reimpl.SPECS)
    TW2 = Tower3('TW2-F3t-DCX-e1is1', OFpt(3), [2, 1],
                 (4, 1, lambda K: [ic(K, 1), K.one()]),
                 (1, 3, lambda K: [ic(K, 1), K.one()]),
                 (2, 1, lambda K: [ic(K, 1), K.one()]))
    assert not TW2.welldef_bad
    cls_tw2 = set()
    for s1a, s1b in ((2, 3), (3, 2), (3, 3)):
        for s3a in (0, 1):
            for s3b in (0, 1):
                cls_tw2.add(((s1a, 0, s3a), (s1b, 0, s3b)))
    exp_tw2 = dict(s_gamma2=3, dcx_per_block=48, dcx_per_subblock=12,
                   classes=cls_tw2)
    ok1, r1 = run_tower(CXW, exp_cx)
    ok2, r2 = run_tower(TW2, exp_tw2)
    green = ok1 and ok2
    print('=' * 78)
    print('PE2 E1-WITNESS VERDICT: %s' % ('GREEN' if green else 'RED'))
    json.dump(dict(pass_='ITERLAW3-PE2', label='post-seal diagnostic',
                   m_shift=M_SHIFT, towers=[r1, r2],
                   verdict='GREEN' if green else 'RED'),
              open(__file__.replace('.py', '_results.json'), 'w'),
              indent=1, default=str)
    sys.exit(0 if green else 1)

if __name__ == '__main__':
    main()
