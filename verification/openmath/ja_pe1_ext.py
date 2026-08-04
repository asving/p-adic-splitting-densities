#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ja_pe1_ext.py -- JA-PE1 hostile-pass extension (NEW file; read-only w.r.t.
all committed artifacts).  Purpose: extract ONE fully-traced JA-RES
per-slot-law instance PER RING (Zp and Fpt) at level m = 2, printing every
intermediate integer (beta, attained set, u_i, s_sub(a_i), t(i), tau(a_i),
beta_i, A_1, z1-order) plus both field-element sides, so the equality
c_i = z_{m-1}^{-i*A_{m-1}} * C_i and the integer identity
t(i) - tau_{m-1}(a_i) = -i*A_{m-1} can be re-derived BY HAND in the
JA-PE1 report.  All exponent integers here are recomputed with fresh
arithmetic (independent modular inverse), not copied from either engine.
Also: one JA-EPS hand instance per ring (integers only).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL
import grt_weld_probe as GWP

def fresh_ell(h, e):
    return 0 if e == 1 else pow(h % e, -1, e)

def trace_res_instance(spec):
    tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
    T = ITL.build_tower(spec)
    G = GWP.gmn_from_tower(T)
    m = 2
    e, h = T.e[m-1], T.h[m-1]
    # fresh A_{m-1} = ell_{m-2} * g_{m-2} * gamma_{m-1}
    lf0 = fresh_ell(T.h[m-2], T.e[m-2])
    A1 = lf0 * T.g[m-2] * T.gam[m-1]
    K1 = T.K[m-1]
    # find z1 multiplicative order (small fields)
    zo, acc = 1, T.z[m-1]
    while acc != K1.one():
        acc = K1.mul(acc, T.z[m-1]); zo += 1
        assert zo < 200
    # walk the pool for the first scored multi-slot sample
    import grt_ja_checks as JA   # only for sample_pool + vd_eval (no main run)
    pool = JA.sample_pool(T, small=True)
    for A in pool:
        At = tuple(A)
        try:
            beta = T.wlev(m, At)
            Cs = T.read_coeffs(m, beta, At)
            dv, pts, att, s0, s1, _ = G._support(m, list(At))
            Rl = G.rres(m, list(At))
        except AssertionError:
            continue
        if len(att) < 2:
            continue
        if not all(JA.vd_eval(T, G, m-1, dv[i]) is True for i in att):
            continue
        s_eq, _ = ITL.eq12(beta, e, h)
        print('== RING INSTANCE %s  (level m = 2) ==' % tag)
        print('  reads: (e0,h0,g0)=(%d,%d,%d) (e1,h1,g1)=(%d,%d,%d)'
              % (T.e[0], T.h[0], T.g[0], T.e[1], T.h[1], T.g[1]))
        print('  gam1=%d gam2=%d W1=e0*g0*gam1=%d  ell0(fresh)=%d  A_1=%d'
              % (T.gam[1], T.gam[2], T.e[0]*T.g[0]*T.gam[1], lf0, A1))
        print('  ord(z1) = %d   z1 = %r' % (zo, T.z[m-1]))
        print('  A = %r' % (At,))
        print('  beta = w_2(A) = %d ; eq12 offset s(beta) = %d ; att = %s ; s0 = %d'
              % (beta, s_eq, att, s0))
        for i in att:
            ai = dv[i]
            u_i = pts[i]
            _, _, _, ssub, _, _ = G._support(m-1, ai)
            beta_i = (beta - i*T.gam[m]) // T.e[m-1]
            t_i_num = ssub - fresh_ell(T.h[m-2], T.e[m-2])*u_i
            tau_num = ssub - fresh_ell(T.h[m-2], T.e[m-2])*beta_i
            assert t_i_num % T.e[m-2] == 0 and tau_num % T.e[m-2] == 0
            t_i, tau_i = t_i_num//T.e[m-2], tau_num//T.e[m-2]
            c_prn = Rl[(i - s0)//e]
            C_har = Cs.get((i - s_eq)//e)
            want = K1.mul(ITL.fpow(K1, T.z[m-1], -i*A1), C_har)
            print('  slot i=%d: u_i=%d s_sub(a_i)=%d beta_i=%d | t(i)=%d tau=%d '
                  't-tau=%d -i*A1=%d %s | c_i=%r C_i=%r z1^{-iA1}*C_i=%r LAW %s'
                  % (i, u_i, ssub, beta_i, t_i, tau_i, t_i - tau_i, -i*A1,
                     'OK' if t_i - tau_i == -i*A1 else 'MISMATCH',
                     c_prn, C_har, want,
                     'HOLDS' if c_prn == want else 'FAILS'))
        print()
        return
    print('== %s: no multi-slot scored sample found at m=2 ==' % tag)

def trace_eps_instance(spec, V):
    tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
    T = ITL.build_tower(spec)
    m = 1
    e, h = T.e[0], T.h[0]
    lf = fresh_ell(h, e)
    lpf = (1 - lf*h)//e
    s = (lf*V) % e
    u = (V - s*h)//e
    t = (lf*V - s)//e
    K = T.K[1]
    epsv = T.eps(1, V)
    print('== JA-EPS instance %s: m=1 (e,h)=(%d,%d) V=%d ==' % (tag, e, h, V))
    print('  ell=%d ellp=%d ; s=ellV mod e=%d u=(V-sh)/e=%d ; t_1(V)=(ellV-s)/e=%d'
          % (lf, lpf, s, u, t))
    print('  eps-exponent ellp*s - ell*u = %d ; -t = %d ; equal: %s'
          % (lpf*s - lf*u, -t, lpf*s - lf*u == -t))
    print('  eps_1(V) = %r ; z1^{-t} = %r ; field equality: %s'
          % (epsv, ITL.fpow(K, T.z[1], -t), epsv == ITL.fpow(K, T.z[1], -t)))
    print()

if __name__ == '__main__':
    zp = next(s for s in GWP.TOWERS if s['id'] == 'T2A')    # Zp, p=2
    fpt = next(s for s in GWP.TOWERS if s['id'] == 'T2D')   # Fpt, p=2
    trace_res_instance(zp)
    trace_res_instance(fpt)
    trace_eps_instance(zp, 7)
    trace_eps_instance(fpt, 5)
