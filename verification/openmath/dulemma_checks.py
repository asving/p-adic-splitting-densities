#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
dulemma_checks.py -- THE MACHINE LEG for lean/notes/openmath/
DULEMMA_PROOF_2026-08-08.md (the DU-LEMMA unit: the (DMULT-s) upgrade,
PROVING the coboundary identity du == 1 for the JC-SCAL unit cochain).

TWO-COMMIT SEAL (the standing r1 protocol): commit 1 = the note (SS8.1
predictions sealed, verdict PENDING) + this runner, UNRUN; this docstring is
the authoritative preregistration.  Commit 2 = the verdict written FROM the
committed artifacts (dulemma_checks_output.txt, dulemma_checks_results.json).

WHAT IS TESTED (the note's chain, link by link, plus the conclusion):

  THEOREM DU   (note SS4): omega(lam,mu) == 1 -- the (DMULT-s) multiplier is
               exactly 1 -- via the four-line compose
                 omega = u_span/(a_lam a_mu)              [DU-B(i)]
                       = a_{lam+mu} prod_j z_j^{D_j} / (a_lam a_mu)  [JC-INNER]
                       = a_{lam+mu} (dE)(lam,mu) / (a_lam a_mu)      [WM-COB(ii)]
                       = 1                                [DU-A: a == E].
  LEMMA DU-A   (note SS3): a_gam = E(gam) = prod_{j=1..m} eps_j(beta_j(gam)),
               the harness anchor constant IS the composite eps-kit cochain.
  DU-A rider:  a_{gam+E}/a_gam == rho_T = prod_j z_j^{-l_{j-1} E_{j-1}}
               (JC-PIINV's c_pi and WM-RHO's rho_T are ONE constant).

ROSTER: grt_jc_probe.ROSTER imported FROZEN (the same 29 rows every J-C
battery used), md5-pinned below with the engine and the frozen r1 helper
module (Rpoly / pmul / pshift / delta_of / surj_build are IMPORTED, not
re-typed, so the (DMULT) predicate is byte-identical to the audited one).

============================= PREREGISTERED LEGS ==============================
(violation counts; a family whose observed count differs from its sealed
prediction is RED.  Deterministic, exact arithmetic, no randomness.)

DU-PIN     md5 pins of the four frozen imports (engine, probe/roster, r1
           helpers, engine_ext).  Violation if a pin moved.   PREDICTED 0.

EXT-GATE   engine_ext install() + check_pins() + agreement_gate(full=False)
           re-run (standing in-unit rule).                    PREDICTED 0.

DU-EPS     LEMMA DU-A on the nose: for every gam in [G0, G0+2E) (all window
           lines, 2 periods per row): slot set of R_gam(phi_gam) == {0} and
           a_gam == E(gam), with E(gam) computed FRESH from the split +
           t_fresh cochain (weldmaster's independent kit re-implementation),
           embedded in K_m.                                   PREDICTED 0.

DU-RHO     the period rider: a_{gam+E} == rho_T * a_gam with rho_T the
           CLOSED FORM prod_{j=1..m} z_j^{-l_{j-1}*El[j-1]} (El[j] =
           e_0...e_{j-1}), gam in [G0, G0+E).  This simultaneously re-reads
           JC-PIINV's c_pi and WM-RHO's rho_T as one constant. PREDICTED 0.

DU-COBW    THE CONCLUSION du == 1, decided on the full per-row grid (the
           anchor-witness form, = R1-COB's predicate): for every ordered
           pair (lam, mu) in {G0+r : r in [0,E)}^2 with lam+mu in W and
           dint_ok (skips CENSUSED, see below):
              R_{lam+mu}(phi_lam phi_mu) == {delta: a_lam*a_mu}  (exact dict).
           By COROLLARY DU-FIN this grid DECIDES du == 1 for every attained
           line pair of the row.  Runs on ALL rows including the one
           e_m = 1 row (C4H), where the verdict is MEASURED tier (the
           theorem's fence is e_m >= 2); the e_m = 1 rows are censused.
                                                              PREDICTED 0.

DU-CHAIN   the compose, link by link, on every DU-COBW-scored pair:
           (i)  prod_j z_j^{D_j} == (dE)(lam,mu) = E(lam)E(mu)/E(lam+mu)
                in K_m                            [WM-COB(ii) product form];
           (ii) [e_m >= 2 rows] slot set of R_{lam+mu}(phi_lam phi_mu)
                == {delta} and u_span == a_{lam+mu} * prod_j z_j^{D_j}
                                                  [JC-SPAN + JC-INNER];
                at the e_m = 1 row the slot-set predicate weakens to
                subset of {0,1} (JC-SPAN's own fence) and the u_span leg
                is scored only when the slot set is {delta} (census).
                                                              PREDICTED 0.

DU-DENSE   the r2 lesson (dense NON-MONOMIAL x NON-MONOMIAL pairs): the
           dense set D = {ones2, mix2 [, ones3 where realized]} is built by
           the frozen JC-BSURJ builder (surj_build, cap 80; degree-2 targets
           are SCORED -- they realize on every row per the r2 battery -- and
           each element is verified w == lam, R == target before use), plus
           Phi_{m+1} (the once-skipped pair; its R is psi_m, always
           multi-slot).  Every ordered pair from D u {PhiTop} x D u {PhiTop}
           AND the mixed pairs (f, phi_r) / (phi_r, f), r in {0, 1 mod E},
           is scored with the exact (DMULT-s) predicate
              R_{w(f)+w(g)}(fg) == y^delta * R(f) * R(g)   (frozen pmul/pshift).
           Census: #pairs with BOTH factors multi-slot (>= 4 per row
           expected: {ones2,mix2,PhiTop}^2 minus none).       PREDICTED 0.

SKIPPED-PAIR CENSUS (printed per row and totalled; skips are DISCLOSED, not
silent): (a) grid pairs with lam+mu not in W -- predicted census 0 (WINDOW-(n));
(b) grid pairs with dint_ok false (off the scored stratum -- there the value
law and hence JC-INNER do not apply; DU-COBW/DU-CHAIN skip them);
(c) dense targets not realized within cap (only ones3 may be absent; census);
(d) e_m = 1 rows (C4H): scored but MEASURED-tier (theorem fence).

TEETH (a silent tooth is RED):
  DU-T1-FAKEU   the charge's required tooth: a FAKE UNIT COCHAIN whose
      coboundary is NOT 1.  Regauge the read by u~_gam := c^{ind(gam)} with
      ind(gam) := [gam == 0 mod E] and c := the first element of
      K_m^* \ {1}: the mutated (DMULT-s) predicate
         c^{ind(lam+mu)} * R_{lam+mu}(phi_lam phi_mu)
             == y^delta * c^{ind(lam)} R(phi_lam) * c^{ind(mu)} R(phi_mu)
      must FAIL wherever d(ind) != 0 and the true predicate passed -- at
      (G0, G0) the defect is 1, so it fires there on every ELIGIBLE row.
      Eligibility := |K_m| > 2 (on a row with K_m = F_2 no nontrivial unit
      cochain EXISTS -- du == 1 is trivially true there; censused).
      PREDICTED: fires >= 1 on every eligible row; ineligible rows censused;
      total >= 1.
  DU-T2-FAKEKIT the fake eps-kit (kills DU-A): flip the sign of the level-j*
      cochain exponent (t~_{j*} := -t_{j*}), one level at a time; the
      mutated DU-EPS predicate a_gam == E~(gam) must FAIL for some
      (j*, gam in [G0, G0+2E)) on every ELIGIBLE row (eligibility :=
      exists (j, gam) with z_j^{2 t_j(beta_j(gam))} != 1 in K_m, computed
      and censused at runtime).  PREDICTED: fires on every eligible row;
      total >= 1.
  DU-T3-SHIFT   r1's T3 re-armed on the grid: the y^{delta+1} mutation
      {delta+1: a_lam*a_mu} must differ from R_{lam+mu}(phi_lam phi_mu) on
      every DU-COBW-scored pair.  PREDICTED: fires >= 1 per row.

Exit code = (violations + silent teeth).

FROZEN-IMPORT PINS (DU-PIN; violation if a pinned file's md5 moved):
  iterlawn_pe_reimpl.py  cae45db2318b89520dd5484466ef3604
  grt_jc_probe.py        03811b695cf7aa1bd5b52d5b0cd8bcd6
  grt_jc_r1_checks.py    7f896bfa27d06158f95c5987c7299770
  engine_ext.py          d7eba6ac75d8d894f41ac8d0cf16de9c

FENCE HYGIENE (GRTJC SS3.5 [r1, G8]): Tower.constants is called ONLY for the
integer S0.3 data (delta, D_j) that DU-CHAIN's statements are ABOUT (the
closed-form c_T field is never read; delta for the read-side predicate comes
from the frozen delta_of, i.e. from split data); the read side is
Tower.read_coeffs via the frozen Rpoly.  No family compares against the
[ILN] closed form.

PRE-SEAL SMOKE DISCLOSURE (honest, part of this seal).  One --smoke run on
rows C2A/C2I/C3A/C4H executed BEFORE sealing and found: 0 violations across
all seven families (DU-EPS a == E EXACT on all 52 sampled lines incl. the
on-demand lam+mu lines; 196 grid pairs, 0 skips of either kind); DU-T1
fired on C2A/C3A/C4H (60 total) and was structurally SILENT on C2I, which
the runtime census marks INELIGIBLE (|K_m| = 2: no nontrivial unit cochain
exists -- there du == 1 is trivially true); DU-T2 fired on C2A/C3A (28) and
was SILENT on the censused-ineligible C2I and C4H (all z_j^{2 t_j} == 1
there); DU-T3 fired on all 196 scored pairs.  No scored predicate was
weakened after the smoke; the only post-smoke edit was this disclosure
paragraph itself (updated from its pre-run draft to the observed facts:
the ineligible-row lists and fire counts).

Outputs: dulemma_checks_output.txt (stdout, tee'd by the caller) and
dulemma_checks_results.json.
"""
import sys, os, json, time, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import iterlawn_pe_reimpl as ITL
import grt_jc_probe as PR
import engine_ext as EE
from grt_jc_r1_checks import Rpoly, pmul, pshift, delta_of, surj_build

PINS = {
    'iterlawn_pe_reimpl.py': 'cae45db2318b89520dd5484466ef3604',
    'grt_jc_probe.py':       '03811b695cf7aa1bd5b52d5b0cd8bcd6',
    'grt_jc_r1_checks.py':   '7f896bfa27d06158f95c5987c7299770',
    'engine_ext.py':         'd7eba6ac75d8d894f41ac8d0cf16de9c',
}

SMOKE_IDS = ('C2A', 'C2I', 'C3A', 'C4H')

FAMILIES = ['DU-PIN', 'EXT-GATE', 'DU-EPS', 'DU-RHO', 'DU-COBW', 'DU-CHAIN',
            'DU-DENSE']
TEETH = ['DU-T1-FAKEU', 'DU-T2-FAKEKIT', 'DU-T3-SHIFT']

VIOL = []
COUNTS = {f: 0 for f in FAMILIES}
FIRES = {t: 0 for t in TEETH}
RESULTS = {'rows': {}, 'families': {}, 'teeth': {}, 'census': {}}


def note(fam, n=1):
    COUNTS[fam] += n


def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)))


def fire(t, n=1):
    FIRES[t] += n


# ------------------------------------------------------------------ helpers
def t_fresh(T, j, beta):
    """the weld cochain at level j (read (e_{j-1}, h_{j-1})), FRESH:
    t_j(beta) = (l*beta - s)/e with s = l*beta mod e (weldmaster S0)."""
    e, l = T.e[j - 1], T.l[j - 1]
    s = (l * beta) % e
    return (l * beta - s) // e


def mul_order(K, z):
    o, acc, one = 1, z, K.one()
    while acc != one:
        acc = K.mul(acc, z)
        o += 1
        assert o <= 4096, 'order runaway'
    return o


def zpow(K, z, o, k):
    return ITL.fpow(K, z, k % o)


class Kit:
    """fresh eps-kit data for one row, valued in K_m."""

    def __init__(self, S):
        T = S.T
        self.S, self.T = S, T
        self.m = S.NR - 1
        self.Km = T.K[S.NR - 1]
        # letters z_1..z_m embedded into K_m, with multiplicative orders
        self.zm = {j: T.embed(T.z[j], j, S.NR - 1) for j in range(1, S.NR)}
        self.oz = {j: mul_order(self.Km, self.zm[j]) for j in range(1, S.NR)}
        # El[j] = e_0...e_{j-1}
        self.El = [1] * (S.NR + 1)
        for j in range(1, S.NR + 1):
            self.El[j] = self.El[j - 1] * T.e[j - 1]

    def Ecoch(self, gama, flip=None):
        """E(gama) = prod_{j=1..m} eps_j(beta_j(gama)) in K_m; flip = j*
        negates the level-j* cochain exponent (tooth DU-T2)."""
        sp = self.T.split(gama)
        acc = self.Km.one()
        for j in range(1, self.S.NR):
            tj = t_fresh(self.T, j, sp['beta'][j])
            if flip == j:
                tj = -tj
            acc = self.Km.mul(acc, zpow(self.Km, self.zm[j], self.oz[j], -tj))
        return acc

    def rho(self):
        acc = self.Km.one()
        for j in range(1, self.S.NR):
            acc = self.Km.mul(acc, zpow(self.Km, self.zm[j], self.oz[j],
                                        -self.T.l[j - 1] * self.El[j - 1]))
        return acc

    def inner(self, D):
        """prod_{j=1..m} z_j^{D_j} in K_m (requires D_j integral)."""
        acc = self.Km.one()
        for j in range(1, self.S.NR):
            acc = self.Km.mul(acc, zpow(self.Km, self.zm[j], self.oz[j], D[j]))
        return acc


def anchor_const(S, gama):
    """(slot-dict, a_gama or None): R_gama(phi_gama), expected slot set {0}."""
    R = Rpoly(S, gama, S.T.tanch(gama, S.NR - 1))
    return R, (R.get(0) if set(R) == {0} else None)


def build_dense(S):
    """the row's dense multi-slot set, via the frozen JC-BSURJ builder
    (r2's targets: ones2/mix2 scored, ones3 attempted)."""
    T = S.T
    Km = T.K[S.NR - 1]
    elems = [c for c in Km.elems() if not Km.is_zero(c)]
    alt = elems[1] if len(elems) > 1 else elems[0]
    targets = [('ones2', 2, {j: Km.one() for j in range(3)}),
               ('mix2', 2, {0: Km.one(), 1: alt, 2: Km.one()}),
               ('ones3', 3, {j: Km.one() for j in range(4)})]
    D, ks = [], {}
    for (name, d, tg) in targets:
        got = surj_build(S, tg, d)
        if got is None:
            ks[name] = None
            if d == 2:
                note('DU-DENSE')
                viol('DU-DENSE', S.spec['id'],
                     'dense degree-2 target %s not realizable within cap' % name)
            continue
        k, lam, f, recs = got
        ks[name] = k
        tgt = {j: c for j, c in tg.items() if not Km.is_zero(c)}
        note('DU-DENSE')
        if T.wlev(S.NR, f) != lam or Rpoly(S, lam, f) != tgt:
            viol('DU-DENSE', S.spec['id'], 'dense %s failed verification' % name)
            continue
        D.append((name, f, lam))
    return D, ks


# ------------------------------------------------------------------ per row
def run_row(S, census):
    T, P = S.T, S.P
    NR, E, rid = S.NR, S.E, S.spec['id']
    Km = T.K[NR - 1]
    em, gm = T.e[NR - 1], T.g[NR - 1]
    kit = Kit(S)
    rec = {'id': rid, 'm': S.m, 'E': E, 'e_m': em, 'g_m': gm,
           'nKm': len([c for c in Km.elems()])}
    rowfire = {t: 0 for t in TEETH}

    # ---------------- DU-EPS + DU-T2 ----------------------------------
    A = {}                                   # gama -> a_gama
    for gama in range(S.G0, S.G0 + 2 * E):
        Rg, a = anchor_const(S, gama)
        note('DU-EPS')
        if a is None:
            viol('DU-EPS', rid, 'gam=%d slot set %s != {0}' % (gama, set(Rg)))
            continue
        A[gama] = a
        if a != kit.Ecoch(gama):
            note('DU-EPS')
            viol('DU-EPS', rid, 'gam=%d a != E' % gama)
    t2_eligible = False
    for jstar in range(1, NR):
        for gama in range(S.G0, S.G0 + 2 * E):
            sp = T.split(gama)
            tj = t_fresh(T, jstar, sp['beta'][jstar])
            if zpow(Km, kit.zm[jstar], kit.oz[jstar], 2 * tj) != Km.one():
                t2_eligible = True
            if gama in A and A[gama] != kit.Ecoch(gama, flip=jstar):
                rowfire['DU-T2-FAKEKIT'] += 1
    rec['t2_eligible'] = t2_eligible

    # ---------------- DU-RHO ------------------------------------------
    rho = kit.rho()
    for gama in range(S.G0, S.G0 + E):
        if gama not in A or gama + E not in A:
            continue
        note('DU-RHO')
        if A[gama + E] != Km.mul(rho, A[gama]):
            viol('DU-RHO', rid, 'gam=%d a(g+E) != rho*a(g)' % gama)

    # ---------------- DU-COBW / DU-CHAIN / DU-T1 / DU-T3 --------------
    cunit = None
    for c in Km.elems():
        if not Km.is_zero(c) and c != Km.one():
            cunit = c
            break
    rec['t1_eligible'] = cunit is not None
    skips = {'offW': 0, 'dint': 0}
    scored = 0
    for r1 in range(E):
        for r2 in range(E):
            lam, mu = S.G0 + r1, S.G0 + r2
            if not T.inW(lam + mu):
                skips['offW'] += 1
                continue
            cst = T.constants(lam, mu)
            if not cst['dint_ok']:
                skips['dint'] += 1
                continue
            if (lam + mu) not in A:      # extend the anchor table on demand
                _, a_sum = anchor_const(S, lam + mu)
                A[lam + mu] = a_sum      # None iff slot set != {0}
            if A.get(lam) is None or A.get(mu) is None:
                continue                 # already a DU-EPS violation
            d = delta_of(S, lam, mu)
            Rprod = Rpoly(S, lam + mu, P.mul(S.ph[r1], S.ph[r2]))
            aa = Km.mul(A[lam], A[mu])
            want = {d: aa}
            scored += 1
            note('DU-COBW')
            if Rprod != want:
                viol('DU-COBW', rid, '(%d,%d) R(prod) != {delta: a*a}'
                     % (lam, mu))
            # DU-T3: the y^{delta+1} mutation must differ
            if Rprod != {d + 1: aa}:
                rowfire['DU-T3-SHIFT'] += 1
            # DU-T1: the fake unit cochain c^{ind} must be caught
            if cunit is not None:
                ind = lambda g: 1 if (g % E) == 0 else 0
                lhs = {k: Km.mul(v, zpow(Km, cunit, mul_order(Km, cunit),
                                         ind(lam + mu)))
                       for k, v in Rprod.items()}
                rhs = {d: Km.mul(aa, zpow(Km, cunit, mul_order(Km, cunit),
                                          ind(lam) + ind(mu)))}
                if Rprod == want and lhs != rhs:
                    rowfire['DU-T1-FAKEU'] += 1
            # DU-CHAIN (i): inner word == coboundary of E
            note('DU-CHAIN')
            innerD = kit.inner(cst['D'])
            dE = Km.mul(Km.mul(kit.Ecoch(lam), kit.Ecoch(mu)),
                        Km.inv(kit.Ecoch(lam + mu)))
            if innerD != dE:
                viol('DU-CHAIN', rid, '(%d,%d) prod z^D != dE' % (lam, mu))
            # DU-CHAIN (ii): JC-SPAN slot set + JC-INNER value
            am = A.get(lam + mu)
            if am is None:
                viol('DU-CHAIN', rid, '(%d,%d) missing a_{lam+mu}' % (lam, mu))
                continue
            if em >= 2:
                note('DU-CHAIN')
                if set(Rprod) != {d}:
                    viol('DU-CHAIN', rid, '(%d,%d) slot set %s != {%d}'
                         % (lam, mu, set(Rprod), d))
                elif Rprod[d] != Km.mul(am, innerD):
                    viol('DU-CHAIN', rid, '(%d,%d) u_span != a*innerD'
                         % (lam, mu))
            else:
                census['em1_rows'].add(rid)
                if not set(Rprod) <= {0, 1}:
                    note('DU-CHAIN')
                    viol('DU-CHAIN', rid, '(%d,%d) e_m=1 slot set %s !<= {0,1}'
                         % (lam, mu, set(Rprod)))
                elif set(Rprod) == {d}:
                    note('DU-CHAIN')
                    if Rprod[d] != Km.mul(am, innerD):
                        viol('DU-CHAIN', rid, '(%d,%d) e_m=1 u_span != a*innerD'
                             % (lam, mu))
    rec['grid_scored'] = scored
    rec['grid_skips'] = skips
    census['offW'] += skips['offW']
    census['dint'] += skips['dint']
    census['scored'] += scored

    # ---------------- DU-DENSE ----------------------------------------
    D, ks = build_dense(S)
    rec['dense_k'] = ks
    pool = list(D) + [('PhiTop', S.PhiTop, S.wPhiTop)]
    both_dense = 0
    for (n1, f, lf) in pool:
        for (n2, g, lg) in pool:
            Rf, Rg = Rpoly(S, lf, f), Rpoly(S, lg, g)
            if len(Rf) > 1 and len(Rg) > 1:
                both_dense += 1
            fg = P.mul(f, g)
            note('DU-DENSE')
            if T.wlev(NR, fg) != lf + lg:
                viol('DU-DENSE', rid, 'w(fg) != w(f)+w(g) on (%s,%s)'
                     % (n1, n2))
                continue
            d = delta_of(S, lf, lg)
            note('DU-DENSE')
            if Rpoly(S, lf + lg, fg) != pshift(pmul(Km, Rf, Rg), d):
                viol('DU-DENSE', rid, '(DMULT-s) fails on (%s,%s)' % (n1, n2))
    # mixed dense x anchor pairs
    for (n1, f, lf) in pool:
        for r in (0, 1 % E):
            for (a, b, la, lb, nm) in (((f, S.ph[r], lf, S.G0 + r,
                                         '(%s,phi%d)' % (n1, r))),
                                       ((S.ph[r], f, S.G0 + r, lf,
                                         '(phi%d,%s)' % (r, n1)))):
                Ra, Rb = Rpoly(S, la, a), Rpoly(S, lb, b)
                ab = P.mul(a, b)
                note('DU-DENSE')
                if T.wlev(NR, ab) != la + lb:
                    viol('DU-DENSE', rid, 'w mixed %s' % nm)
                    continue
                d = delta_of(S, la, lb)
                note('DU-DENSE')
                if Rpoly(S, la + lb, ab) != pshift(pmul(Km, Ra, Rb), d):
                    viol('DU-DENSE', rid, '(DMULT-s) fails on mixed %s' % nm)
    rec['both_dense_pairs'] = both_dense
    census['both_dense'] += both_dense

    # ---------------- tooth scoring ------------------------------------
    for t in TEETH:
        fire(t, rowfire[t])
    rec['teeth'] = rowfire
    # per-row obligations
    if rowfire['DU-T3-SHIFT'] < 1 and scored > 0:
        viol('DU-COBW', rid, 'SILENT TOOTH DU-T3 on a row with scored pairs')
    if rec['t1_eligible'] and rowfire['DU-T1-FAKEU'] < 1:
        viol('DU-COBW', rid, 'SILENT TOOTH DU-T1 on an ELIGIBLE row')
    if rec['t2_eligible'] and rowfire['DU-T2-FAKEKIT'] < 1:
        viol('DU-EPS', rid, 'SILENT TOOTH DU-T2 on an ELIGIBLE row')
    if not rec['t1_eligible']:
        census['t1_ineligible'].append(rid)
    if not rec['t2_eligible']:
        census['t2_ineligible'].append(rid)
    return rec


def main(smoke=False):
    t0 = time.time()
    # ---- DU-PIN
    for fn, want in PINS.items():
        note('DU-PIN')
        got = hashlib.md5(open(os.path.join(HERE, fn), 'rb').read()).hexdigest()
        if got != want:
            viol('DU-PIN', fn, 'md5 %s != pinned %s' % (got, want))
    # ---- EXT-GATE (standing rule)
    v0 = len(EE.VIOL)
    EE.install()
    EE.check_pins()
    gate_new = EE.agreement_gate(full=False)
    note('EXT-GATE')
    if gate_new or len(EE.VIOL) > v0:
        viol('EXT-GATE', 'engine_ext', '%d new violations' % (len(EE.VIOL) - v0))
    print('[gate] engine_ext OK (%.1fs)' % (time.time() - t0))

    census = {'offW': 0, 'dint': 0, 'scored': 0, 'both_dense': 0,
              'em1_rows': set(), 't1_ineligible': [], 't2_ineligible': []}
    roster = [s for s in PR.ROSTER if (not smoke) or s['id'] in SMOKE_IDS]
    for spec in roster:
        S = PR.Stage(spec)
        rec = run_row(S, census)
        RESULTS['rows'][spec['id']] = rec
        print('  [%6.1fs] %-5s m=%d E=%-3d e_m=%d g_m=%d |Km|=%-3d '
              'grid=%d skips=%s dense_both=%d teeth=%s'
              % (time.time() - t0, spec['id'], rec['m'], rec['E'],
                 rec['e_m'], rec['g_m'], rec['nKm'], rec['grid_scored'],
                 rec['grid_skips'], rec['both_dense_pairs'],
                 [rec['teeth'][t] for t in TEETH]))

    census['em1_rows'] = sorted(census['em1_rows'])
    print('\n================ SKIPPED-PAIR CENSUS ================')
    print('grid pairs scored: %d' % census['scored'])
    print('skipped off-window sums: %d (predicted 0)' % census['offW'])
    print('skipped dint_ok=False (off scored stratum): %d (census only)'
          % census['dint'])
    print('e_m = 1 rows (MEASURED tier, theorem fence): %s'
          % census['em1_rows'])
    print('both-dense pairs scored: %d' % census['both_dense'])
    print('T1-ineligible rows (|Km^*| = 1, du==1 trivially): %s'
          % census['t1_ineligible'])
    print('T2-ineligible rows (all z_j^{2t_j} == 1): %s'
          % census['t2_ineligible'])

    print('\n================ FAMILIES ================')
    for f in FAMILIES:
        vs = [v for v in VIOL if v[0] == f]
        RESULTS['families'][f] = {'samples': COUNTS[f], 'violations': len(vs)}
        print('%-9s samples=%-7d violations=%d' % (f, COUNTS[f], len(vs)))
    print('\n================ TEETH ================')
    silent = []
    for t in TEETH:
        RESULTS['teeth'][t] = FIRES[t]
        ok = FIRES[t] >= 1
        if not ok:
            silent.append(t)
        print('%-14s fires=%-6d %s' % (t, FIRES[t],
                                       'OK' if ok else 'SILENT (RED)'))
    RESULTS['census'] = census
    RESULTS['violations'] = ['%s %s %s' % v for v in VIOL]
    RESULTS['elapsed_s'] = round(time.time() - t0, 1)
    for v in VIOL:
        print('VIOLATION: %s %s %s' % v)
    print('\nTOTAL: %d violations, %d silent teeth, %.1fs'
          % (len(VIOL), len(silent), time.time() - t0))
    out = os.path.join(HERE, 'dulemma_checks_results.json')
    if not smoke:
        with open(out, 'w') as fh:
            json.dump(RESULTS, fh, indent=1, sort_keys=True, default=str)
        print('results -> %s' % out)
    return len(VIOL) + len(silent)


if __name__ == '__main__':
    sys.exit(0 if main(smoke=('--smoke' in sys.argv)) == 0 else 1)
