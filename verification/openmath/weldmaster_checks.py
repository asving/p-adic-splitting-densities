#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
weldmaster_checks.py -- SEALED BATTERY for WELDMASTER_2026-08-08.md
(the WELD MASTER-TRANSPORT consolidation note).

TWO-COMMIT SEAL.  Commit 1 = this runner + the note with its S5 predictions,
battery UNRUN on the full roster; commit 2 = the verdict appended to the note
FROM the committed artifacts (weldmaster_checks_output.txt /
weldmaster_checks_results.json).  PRE-SEAL SMOKE DISCLOSED: the runner was
developed and debugged against the 4-row smoke subset {C2A, C2I, C3A, I4B}
(`--smoke`); observed on the smoke rows: all violation families 0, all four
teeth firing.  No full-roster run happened before the seal.

WHAT IS KEYED (note section in brackets):

  WM-EPS    [S0/S2]  the committed engine's eps == z^(-t) with t computed
            FRESH (t(beta) = (l*beta - s)/e, s = l*beta mod e) -- JA-EPS's
            identification re-keyed against a fresh cochain implementation.
  WM-COB-I  [S2 THM WM-COB, integer form]  D_j == t_j(beta_j'') -
            t_j(beta_j) - t_j(beta_j') at EVERY level j = 1..n of every
            sampled window pair; D_j/S_j from the committed Tower.constants
            (the [ILN] S0.3 recursion), t FRESH.
  WM-COB-OFFW [S2]  the same integer identity on OFF-WINDOW pairs
            (gamma - E vs gamma'), mirroring [ILN] S2's "gamma, gamma' in Z
            arbitrary" scope.
  WM-COB-F  [S2, field form]  z_j^{D_j} == eps_j(beta_j) eps_j(beta_j')
            eps_j(beta_j'')^{-1} in K_j.
  WM-COB-C  [S2, composite display]  embedded in the TOP field:
            prod_j z_j^{D_j} == E(g)E(g')/E(g+g') (dE), and the full display
            zbar^delta * prod == zbar^delta * dE.
  WM-RHO    [S2 LEMMA WM-RHO]  E(gamma+E)/E(gamma) == the CONSTANT
            prod_j z_j^{-l_{j-1}*E_{j-1}} (E_j = e_0...e_{j-1}), sampled
            gamma; plus the section-carry census k(nu,nu') for the descent
            corollary (census, not violation-keyed).
  WM-FENCE-XI [S3]  the fence characters are cochain data: t_mu(k*W_mu) ==
            k*A_mu (integers, k = 0..e_mu+1), eps_mu(W_mu) == z_mu^{-A_mu}
            (the c1 tie), eps_mu(e_mu*W_mu) == z_mu^{-e_mu*A_mu} (= the
            slot character theta).
  WM-FENCE-EQ [S3]  the specialization equivalences, sampled: brute
            triviality of {z_mu^{i*A_mu}} vs ord-divisibility (the (R-coll)
            absolute form); brute theta == 1 vs ord | e_mu*A_mu (the
            (C-coll) slot form at trivial lower chain); the implication
            full => slot asserted; the census of strict slot-only rows
            (the honest gap between (C-coll) and (R-coll)) reported.
  WM-SHEAR  [S1 face M1, re-keyed independently]  a FRESH lower-hull
            (monotone chain, exact Fraction slopes) + the FRESH affine
            shear Sigma_q(i,u) = (i, e_q*u + h_q*i): hull(Sigma_q(U-points))
            == hull(H-points) vertex-for-vertex, per-side slope law
            s -> e_q*s + h_q, and min H-ordinate == T.wlev(q+1, f).
            DISCLOSED: the min tie recomputes the engine's own weight
            recursion (sanity leg, not IND); the IND content is the
            hull/vertex/slope covariance under the fresh shear.

  TEETH (each must fire >= 1 GLOBALLY or the battery is RED):
  WM-T-SIGN   t with the OPPOSITE (Def-t(i)) sign convention must break
              WM-COB-I (fires whenever some D_j != 0).
  WM-T-DELTA  zbar^{delta+1} must break the composite display (fires
              whenever zbar != 1).
  WM-T-SHEAR  the garbled shear (h_q -> h_q + 1) must break the vertex law
              (fires on any hull with a vertex at abscissa != 0).
  WM-T-XI     A_mu -> A_mu + 1 must break the c1 tie (fires whenever
              z_mu != 1).

ROSTER: grt_jc_probe.ROSTER imported FROZEN (29 rows: m <= 3, p in {2,3,5},
d0 <= 3, wild e_j = p legs, g_j = 2 branching, eq-char rows, I4A/I4B/I4C) --
md5-pinned below together with the engine.  Tower construction is
ITL.build_tower, the same code path the sealed J-C instrument used.

FROZEN-IMPORT PINS (WM-PIN; violation if a pinned file's md5 moved):
  iterlawn_pe_reimpl.py  cae45db2318b89520dd5484466ef3604
  grt_jc_probe.py        03811b695cf7aa1bd5b52d5b0cd8bcd6

Exact arithmetic throughout (integers, Fractions, finite-field tuples);
no randomness; deterministic.
"""

import sys, os, json, time, hashlib
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import iterlawn_pe_reimpl as ITL
import grt_jc_probe as JCP

PINS = {
    'iterlawn_pe_reimpl.py': 'cae45db2318b89520dd5484466ef3604',
    'grt_jc_probe.py':       '03811b695cf7aa1bd5b52d5b0cd8bcd6',
}

SMOKE_IDS = ('C2A', 'C2I', 'C3A', 'I4B')

FAMILIES = ['WM-PIN', 'WM-EPS', 'WM-COB-I', 'WM-COB-OFFW', 'WM-COB-F',
            'WM-COB-C', 'WM-RHO', 'WM-FENCE-XI', 'WM-FENCE-EQ', 'WM-SHEAR']
TEETH = ['WM-T-SIGN', 'WM-T-DELTA', 'WM-T-SHEAR', 'WM-T-XI']


# ---------------------------------------------------------------- fresh kit
def t_fresh(T, j, beta):
    """The weld cochain at level j (read (e_{j-1}, h_{j-1})), FRESH:
    t_j(beta) = (l*beta - s)/e with s = l*beta mod e."""
    e, l = T.e[j - 1], T.l[j - 1]
    s = (l * beta) % e
    return (l * beta - s) // e


def zpow(K, z, o, k):
    """z^k with z of multiplicative order o (exponent reduced mod o)."""
    return ITL.fpow(K, z, k % o)


def mul_order(K, z):
    o, acc = 1, z
    one = K.one()
    while acc != one:
        acc = K.mul(acc, z)
        o += 1
        assert o <= 4096, 'order runaway'
    return o


def lower_hull(pts):
    """Fresh monotone-chain LOWER hull; returns the strict vertex list
    sorted by abscissa (collinear interior points removed)."""
    pts = sorted(set(pts))
    if len(pts) <= 1:
        return list(pts)
    hull = []
    for p in pts:
        while len(hull) >= 2:
            (ox, oy), (ax, ay) = hull[-2], hull[-1]
            cross = (ax - ox) * (p[1] - oy) - (ay - oy) * (p[0] - ox)
            if cross <= 0:
                hull.pop()
            else:
                break
        hull.append(p)
    return hull


def sides(hull):
    """Fraction slopes of consecutive hull vertices."""
    return [Fraction(hull[i + 1][1] - hull[i][1], hull[i + 1][0] - hull[i][0])
            for i in range(len(hull) - 1)]


# ---------------------------------------------------------------- per tower
class Ctx:
    def __init__(self, spec):
        self.spec = spec
        self.T = ITL.build_tower(spec)
        T = self.T
        self.NR = T.NR
        self.n = T.NR - 1                     # inner levels j = 1..n
        self.Ktop = T.K[T.NR]
        self.zbar = T.z[T.NR]
        E = 1
        for e in T.e:
            E *= e
        self.E = E
        # multiplicative orders of the letters (z_j in K_j) and zbar
        self.oz = {j: mul_order(T.K[j], T.z[j]) for j in range(1, T.NR + 1)}
        # embed z_j into the top field once
        self.ztop = {j: T.embed(T.z[j], j, T.NR) for j in range(1, T.NR)}
        self.oz_top = {j: mul_order(self.Ktop, self.ztop[j])
                       for j in range(1, T.NR)}
        self.obar = self.oz[T.NR]
        # E_j = e_0...e_{j-1}
        self.El = [1] * (T.NR + 1)
        for j in range(1, T.NR + 1):
            self.El[j] = self.El[j - 1] * T.e[j - 1]

    def Ecoch(self, gama):
        """E(gamma) = prod_{j=1}^{n} eps_j(beta_j(gamma)), embedded top,
        with the FRESH cochain exponent."""
        sp = self.T.split(gama)
        acc = self.Ktop.one()
        for j in range(1, self.NR):
            tj = t_fresh(self.T, j, sp['beta'][j])
            acc = self.Ktop.mul(acc,
                                zpow(self.Ktop, self.ztop[j],
                                     self.oz_top[j], -tj))
        return acc


# ---------------------------------------------------------------- battery
def main(smoke=False):
    t0 = time.time()
    C = {f: [0, 0] for f in FAMILIES}          # family -> [violations, samples]
    fires = {t: 0 for t in TEETH}
    viol = []

    def V(fam, msg):
        C[fam][0] += 1
        viol.append('%s: %s' % (fam, msg))

    def S(fam):
        C[fam][1] += 1

    # ---- WM-PIN
    for fn, want in PINS.items():
        S('WM-PIN')
        got = hashlib.md5(open(os.path.join(HERE, fn), 'rb').read()).hexdigest()
        if got != want:
            V('WM-PIN', '%s md5 %s != pinned %s' % (fn, got, want))

    roster = [s for s in JCP.ROSTER if (not smoke) or s['id'] in SMOKE_IDS]
    census = {'towers': 0, 'pairs_scored': 0, 'kappa_hist': {},
              'fence_rows': {'full': 0, 'slot_only': 0, 'neither': 0},
              'shear_hulls': 0, 'shear_multivertex': 0}

    for spec in roster:
        cx = Ctx(spec)
        T = cx.T
        tag = spec['id']
        census['towers'] += 1
        reps = ITL.window_reps(T, min(cx.E, 6))

        # ------------------------------------------------ WM-EPS
        for j in range(1, cx.NR):
            for beta in range(0, 3 * T.e[j - 1] * T.h[j - 1] + 4):
                S('WM-EPS')
                if T.eps(j, beta) != zpow(T.K[j], T.z[j], cx.oz[j],
                                          -t_fresh(T, j, beta)):
                    V('WM-EPS', '%s j=%d beta=%d' % (tag, j, beta))

        # ------------------------------------------------ WM-COB families
        pairs = [(ga, gb) for ga in reps for gb in reps]
        for (ga, gb) in pairs:
            cst = T.constants(ga, gb)
            if not cst['dint_ok']:
                continue                       # census only; scored stratum
            in_window = T.inW(ga + gb)
            if in_window:
                census['pairs_scored'] += 1
            sa, sb, sc = T.split(ga), T.split(gb), T.split(ga + gb)
            sign_fired_here = False
            for j in range(1, cx.NR):
                ba, bb, bc = sa['beta'][j], sb['beta'][j], sc['beta'][j]
                pred = (t_fresh(T, j, bc) - t_fresh(T, j, ba)
                        - t_fresh(T, j, bb))
                S('WM-COB-I')
                if cst['D'][j] != pred:
                    V('WM-COB-I', '%s (%d,%d) j=%d D=%s pred=%d'
                      % (tag, ga, gb, j, cst['D'][j], pred))
                # tooth: opposite sign convention
                tflip = lambda b: -t_fresh(T, j, b)
                predflip = tflip(bc) - tflip(ba) - tflip(bb)
                if cst['D'][j] != predflip:
                    sign_fired_here = True
                if in_window:
                    Kj = T.K[j]
                    S('WM-COB-F')
                    lhs = zpow(Kj, T.z[j], cx.oz[j], cst['D'][j])
                    rhs = Kj.mul(Kj.mul(T.eps(j, ba), T.eps(j, bb)),
                                 Kj.inv(T.eps(j, bc)))
                    if lhs != rhs:
                        V('WM-COB-F', '%s (%d,%d) j=%d' % (tag, ga, gb, j))
            if sign_fired_here:
                fires['WM-T-SIGN'] += 1
            if in_window:
                # composite display in the top field
                S('WM-COB-C')
                inner = cx.Ktop.one()
                for j in range(1, cx.NR):
                    inner = cx.Ktop.mul(inner,
                                        zpow(cx.Ktop, cx.ztop[j],
                                             cx.oz_top[j], cst['D'][j]))
                dE = cx.Ktop.mul(cx.Ktop.mul(cx.Ecoch(ga), cx.Ecoch(gb)),
                                 cx.Ktop.inv(cx.Ecoch(ga + gb)))
                ok_inner = (inner == dE)
                lhs_full = cx.Ktop.mul(zpow(cx.Ktop, cx.zbar, cx.obar,
                                            cst['delta']), inner)
                rhs_full = cx.Ktop.mul(zpow(cx.Ktop, cx.zbar, cx.obar,
                                            cst['delta']), dE)
                if not (ok_inner and lhs_full == rhs_full):
                    V('WM-COB-C', '%s (%d,%d)' % (tag, ga, gb))
                # tooth: delta + 1
                bad = cx.Ktop.mul(zpow(cx.Ktop, cx.zbar, cx.obar,
                                       cst['delta'] + 1), inner)
                if bad != rhs_full:
                    fires['WM-T-DELTA'] += 1

        # off-window integer leg: gamma - E against each rep
        for ga in reps[:3]:
            for gb in reps[:3]:
                gao = ga - cx.E
                cst = T.constants(gao, gb)
                if not cst['dint_ok']:
                    continue
                sa, sb, sc = T.split(gao), T.split(gb), T.split(gao + gb)
                for j in range(1, cx.NR):
                    S('WM-COB-OFFW')
                    pred = (t_fresh(T, j, sc['beta'][j])
                            - t_fresh(T, j, sa['beta'][j])
                            - t_fresh(T, j, sb['beta'][j]))
                    if cst['D'][j] != pred:
                        V('WM-COB-OFFW', '%s (%d,%d) j=%d'
                          % (tag, gao, gb, j))

        # ------------------------------------------------ WM-RHO
        rho = cx.Ktop.one()
        for j in range(1, cx.NR):
            rho = cx.Ktop.mul(rho, zpow(cx.Ktop, cx.ztop[j], cx.oz_top[j],
                                        -T.l[j - 1] * cx.El[j - 1]))
        for ga in reps[:3]:
            S('WM-RHO')
            got = cx.Ktop.mul(cx.Ecoch(ga + cx.E),
                              cx.Ktop.inv(cx.Ecoch(ga)))
            if got != rho:
                V('WM-RHO', '%s gamma=%d' % (tag, ga))
        # descent-carry census kappa(nu,nu') (not violation-keyed)
        full_reps = ITL.window_reps(T)
        for ga in reps[:4]:
            for gb in reps[:4]:
                nu = (ga + gb) % cx.E
                sig = full_reps[0]
                for r in full_reps:
                    if r % cx.E == nu:
                        sig = r
                        break
                kap = (ga + gb - sig) // cx.E
                census['kappa_hist'][kap] = census['kappa_hist'].get(kap, 0) + 1

        # ------------------------------------------------ WM-FENCE-XI / EQ
        for mu in range(1, cx.NR):
            A = T.l[mu - 1] * T.g[mu - 1] * T.gam[mu]
            Wm = T.wPhi[mu]
            z, K, o = T.z[mu], T.K[mu], cx.oz[mu]
            e_mu = T.e[mu]
            # integer leg: t(k W) = k A
            for k in range(0, e_mu + 2):
                S('WM-FENCE-XI')
                if t_fresh(T, mu, k * Wm) != k * A:
                    V('WM-FENCE-XI', '%s mu=%d k=%d int' % (tag, mu, k))
            # c1 tie + slot character
            S('WM-FENCE-XI')
            if T.eps(mu, Wm) != zpow(K, z, o, -A):
                V('WM-FENCE-XI', '%s mu=%d c1' % (tag, mu))
            S('WM-FENCE-XI')
            if T.eps(mu, e_mu * Wm) != zpow(K, z, o, -e_mu * A):
                V('WM-FENCE-XI', '%s mu=%d slot' % (tag, mu))
            # tooth: A -> A + 1 on the c1 tie
            if T.eps(mu, Wm) != zpow(K, z, o, -(A + 1)):
                fires['WM-T-XI'] += 1
            # equivalences: brute vs criterion
            S('WM-FENCE-EQ')
            brute_full = all(zpow(K, z, o, i * A) == K.one()
                             for i in range(1, o + 1))
            crit_full = (A % o == 0)
            if brute_full != crit_full:
                V('WM-FENCE-EQ', '%s mu=%d full' % (tag, mu))
            S('WM-FENCE-EQ')
            brute_slot = (zpow(K, z, o, e_mu * A) == K.one())
            crit_slot = ((e_mu * A) % o == 0)
            if brute_slot != crit_slot:
                V('WM-FENCE-EQ', '%s mu=%d slot' % (tag, mu))
            S('WM-FENCE-EQ')
            if crit_full and not crit_slot:
                V('WM-FENCE-EQ', '%s mu=%d full-not-slot' % (tag, mu))
            key = ('full' if crit_full else
                   ('slot_only' if crit_slot else 'neither'))
            census['fence_rows'][key] += 1

        # ------------------------------------------------ WM-SHEAR
        P = T.P
        fs = []
        for ga in reps[:3]:
            for gb in reps[:3]:
                fs.append(P.mul(T.tanch(ga, T.n), T.tanch(gb, T.n)))
        for mm in range(1, T.n + 1):
            fs.append(T.Phi[mm])
            fs.append(P.add(T.Phi[mm], T.tanch(reps[0], T.n)))
        seen = set()
        for f in fs:
            if not f or f in seen:
                continue
            seen.add(f)
            for q in range(0, cx.NR):
                dv = P.dev(f, T.Phi[q])
                Upts, Hpts = [], []
                for i, Ai in enumerate(dv):
                    if not Ai:
                        continue
                    wq = T.wlev(q, Ai)
                    Upts.append((i, wq + i * T.wPhi[q]))
                    Hpts.append((i, T.e[q] * wq + i * T.gam[q + 1]))
                if not Upts:
                    continue
                S('WM-SHEAR')
                census['shear_hulls'] += 1
                eq_, hq = T.e[q], T.h[q]
                shearU = [(i, eq_ * u + hq * i) for (i, u) in Upts]
                hullSU = lower_hull(shearU)
                hullH = lower_hull(Hpts)
                hullU = lower_hull(Upts)
                ok = (hullSU == hullH)
                # vertex-for-vertex: shear of U-hull vertices == H-hull
                ok = ok and ([(i, eq_ * u + hq * i) for (i, u) in hullU]
                             == hullH)
                # slope law per side
                sU, sH = sides(hullU), sides(hullH)
                ok = ok and (len(sU) == len(sH)) and \
                    all(eq_ * su + hq == sh for su, sh in zip(sU, sH))
                # min tie (sanity leg -- engine's own recursion recomputed)
                ok = ok and (min(y for (_, y) in Hpts) == T.wlev(q + 1, f))
                if not ok:
                    V('WM-SHEAR', '%s q=%d deg=%d' % (tag, q, len(dv) - 1))
                if len(hullH) >= 2:
                    census['shear_multivertex'] += 1
                # tooth: garbled shear h_q + 1
                badSU = lower_hull([(i, eq_ * u + (hq + 1) * i)
                                    for (i, u) in Upts])
                if badSU != hullH:
                    fires['WM-T-SHEAR'] += 1

        print('%-4s done  (NR=%d, E=%d, reps=%d)'
              % (tag, cx.NR, cx.E, len(reps)))

    # -------------------------------------------------------------- verdict
    lines = []
    lines.append('')
    lines.append('family        violations   samples')
    all_green = True
    for f in FAMILIES:
        lines.append('%-13s %10d %9d' % (f, C[f][0], C[f][1]))
        if C[f][0] != 0:
            all_green = False
    lines.append('')
    lines.append('teeth (must fire >= 1 globally):')
    for t in TEETH:
        lines.append('%-13s fires=%d' % (t, fires[t]))
        if fires[t] < 1:
            all_green = False
    lines.append('')
    lines.append('census: %s' % json.dumps(census, sort_keys=True))
    lines.append('')
    lines.append('VERDICT: %s' % ('ALL GREEN' if all_green else 'RED'))
    lines.append('elapsed %.1fs' % (time.time() - t0))
    out = '\n'.join(lines)
    print(out)
    if viol:
        print('\nviolations (first 50):')
        for v in viol[:50]:
            print('  ' + v)

    suffix = '_smoke' if smoke else ''
    with open(os.path.join(HERE, 'weldmaster_checks_output%s.txt' % suffix),
              'w') as fh:
        fh.write(out + '\n')
        if viol:
            fh.write('\nviolations:\n')
            for v in viol:
                fh.write('  ' + v + '\n')
    with open(os.path.join(HERE, 'weldmaster_checks_results%s.json' % suffix),
              'w') as fh:
        json.dump({'families': {f: {'violations': C[f][0],
                                    'samples': C[f][1]} for f in FAMILIES},
                   'teeth': fires, 'census': census,
                   'violations': viol, 'all_green': all_green,
                   'smoke': smoke,
                   'elapsed_s': round(time.time() - t0, 1)},
                  fh, indent=1, sort_keys=True)
    return 0 if all_green else 1


if __name__ == '__main__':
    sys.exit(main(smoke=('--smoke' in sys.argv)))
