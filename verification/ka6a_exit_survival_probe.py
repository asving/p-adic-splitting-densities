#!/usr/bin/env python3
"""ka6a_exit_survival_probe.py — UNIT KA6a (bridge campaign, area BP4, cluster
BP4-c1, GATE unit) — the exit-cell survival probe.

[CM-first for KA6b2 — this probe is an explicit dependency of the KA6b2 prover
and MUST run (and its record land) BEFORE that prover is assigned.]

STATEMENT (blueprint BRIDGE_BP4_KERNELS_2026-07-30.md §4 KA6a + §3.A (1d) +
risk R1): for synthetic (K-SUB)-shaped tables at pools q0 in {2, 3, 4, 8, 9}
and states with anchored windows, SEARCH for a (state, pool) whose EVERY exit
cell dies (cell count 0 at q0).  SEARCH ORDER (REV 2, F2): anchored states
with pin a >= 2 FIRST — there the squarefree-residual mechanism is provably
ABSENT (z^2 divides every residual regardless of the free window digits), so
any survival must come from a DIFFERENT exit (the cofactor criterion); that
zone is likeliest to refute the per-state form.  A finding REFUTES the
per-state form of E0's escape (row sum < 1 at every realized active state)
and REROUTES KA6b2 to the class-level statement (KA2c reachability from
anchored states).  A finding does NOT refute E0 itself.

DEPS: none (gate unit; verification/ infra only).  Carriers: the M-SPECIES
menu (lean/LeanUrat/MovesSp) transcribed, or a self-contained window model —
the Q1-ratified Kernels/ placement does not bind this python side; the
transcription choice is recorded at run time in the results block.

SKETCH (blueprint §3.A route 1 (1d)): per (state, pool) enumerate the exit
cells of the (K-SUB) classification (terminal/hen + split columns); a cell
"dies" at q0 when its cell-count polynomial vanishes at q = q0 (the probes
already show p = 2 kills six cells — escape_probe_a §2 sealed list); the
per-state form needs only that SOME exit cell survives at every (state, q0).
Case split on the anchor pin a of the state's window:
  a = 0: some free-digit choice makes the residual squarefree
         (count q^e - q^{e-1} > 0 for e >= 2, q >= 2; degree-1 separable);
  a = 1: target z * (squarefree cofactor coprime to z) — same count one
         degree down;
  a >= 2: NO residual is squarefree (KA6b1's compiled impossibility);
         search the anchored read's cofactor-criterion exit instead.

SEALED PREDICTIONS (Q6 discipline — sealed 2026-07-30, BEFORE any run;
recorded here at E-phase spec time; a run that contradicts a seal is a
FINDING, adjudicated, never patched):
  P1 (consistency, must hold — compiled arithmetic): at every a >= 2
      anchored state, the squarefree-residual exit count is 0 at EVERY pool
      (z^2 | every residual).  This leg checks the model transcription, not
      a conjecture; failure = transcription bug, stop and adjudicate.
  P2 (the load-bearing seal): at every a <= 1 state and every
      q0 in {2, 3, 4, 8, 9}, some free window-digit choice yields a
      squarefree residual — i.e. a surviving terminal/hen exit cell;
      per-state row sum < 1 follows (KA5 shape).
  P3 (OPEN — deliberately NOT sealed): whether every a >= 2 (state, pool)
      retains SOME exit cell (the cofactor-criterion exit).  Either outcome
      is a deliverable: all survive => KA6b2 keeps the per-state target at
      a >= 2 via the cofactor mechanism; a (state, pool) with ALL exit
      cells dead => FINDING, KA6b2 rerouted to the class-level escape, the
      obstruction record pins the window-to-residual coefficient map and
      the resisting (state, pool).
  P4 (context re-check): at q0 = 2 the six known dead cells of the sealed
      escape_probe_a §2 list reappear ('A.3dist', 'A.dblsimple',
      'C_even.dist', 'D_even.dist', 'm2.o_split', 'root.m_H3');
      INDIVIDUAL cell death is expected and is NOT a finding — only
      all-exit death at a single state is.

OUTPUT (run phase): PASS/FINDING rows appended to
probe_results_2026-07-30.txt; JSON to results/ka6a_exit_survival.json;
exit code 0 = all sealed legs PASS (P3 recorded either way), 1 = FINDING.

STATUS: RUN PHASE (implemented 2026-07-30 by the KA6a gate prover; the
SEALED PREDICTIONS block above is VERBATIM from the E-phase spec — no seal
was touched).  TRANSCRIPTION CHOICE (recorded per the DEPS clause): the
SELF-CONTAINED WINDOW MODEL, the exact python twin of KA6b2's Lean carrier
`WindowModel` (lean/LeanUrat/Kernels/KA6b2.lean): a state is (anchor pin a,
normalized window length l = deg R_anch >= 1, e_read); the free window
digits are the l coefficients of a monic cofactor c; the residual is
z^a * c; the (K-SUB) (m, c)-classification (MOVES_2026-07-24.md 11792-11821)
of the residual's degree-multiplicity partition routes each digit cell:
c = 0 -> TERM (terminal/hen exit), m = 1 & c = 1 -> KCOL (still-in-block),
m >= 2 & c >= 1 -> SPLIT (exit).  Counts are computed by EXACT ENUMERATION
of all digit choices over F_{q0} (= evaluating the cell-count polynomial at
q = q0; F_4/F_8/F_9 arithmetic implemented via explicit modulus tables).
Swept VARIANTS, recorded so the adjudication is reading-proof:
 · digit-set models: `free_surj` (KA6b2's contested seam premise — the
   digits reach EVERY monic cofactor) AND `vertex_pinned` (the §M-SPECIES
   SP.1 geometric constraint: the side's left endpoint is a vertex, its
   digit nonzero => z does not divide c);
 · classification readings: A (FULL residual z^a * c — the blueprint
   §3.A (1d)/KA6b2 reading; PRIMARY, the sealed P1/P2 quantities) AND
   B (R_anch only — the anchor rides outside the branching data, the
   §M-SPECIES lambda; recorded as context).
The l = 0 (a = full degree) corner is EXCLUDED from the state menu with
reason: a read consumes a polygon side of raw width w' = e*l >= 1
(§M-SPECIES SP.1 (side)), so deg R_anch = l >= 1 at every realized read;
the corner is recorded, not searched.  GRID: a in {0..4}, l in {1..4},
pools {2,3,4,8,9}; plus the REAL n <= 3 menu (escape_probe_a rosters =
MovesV/DefsGate closed forms) for the P4 leg and the real-menu search.
"""

import itertools
import json
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS_TXT = os.path.join(HERE, 'probe_results_2026-07-30.txt')
OUTJSON = os.path.join(HERE, 'results', 'ka6a_exit_survival.json')

POOLS = [2, 3, 4, 8, 9]          # q0 sweep (blueprint-specified)
DEAD_CELLS_Q2 = ['A.3dist', 'A.dblsimple', 'C_even.dist', 'D_even.dist',
                 'm2.o_split', 'root.m_H3']   # escape_probe_a §2 sealed list

E_PHASE = False                  # run phase: body implemented below

A_MAX = 4                        # anchor pins 0..A_MAX
L_MAX = 4                        # normalized window lengths 1..L_MAX
MODELS = ('free_surj', 'vertex_pinned')

FINDINGS = []                    # (tag, detail) rows
PASSROWS = []                    # printed [PASS] rows for the results block


def chk(name, cond, detail=""):
    tag = "PASS" if cond else "FINDING"
    row = f"[{tag}] {name}  {detail}"
    print(row)
    (PASSROWS if cond else FINDINGS).append(row)
    return cond


# --------------------------------------------------------------------------
# Finite fields F_q, q in {2,3,4,8,9}: elements 0..q-1 encoded base p.
# --------------------------------------------------------------------------
_MODULI = {4: (1, 1, 1),          # x^2 + x + 1 over F_2
           8: (1, 1, 0, 1),       # x^3 + x + 1 over F_2
           9: (1, 0, 1)}          # x^2 + 1     over F_3 (irreducible: -1 not a QR)


class GF:
    """F_q arithmetic with precomputed add/mul/neg tables."""

    def __init__(self, q):
        self.q = q
        p = 2 if q in (2, 4, 8) else 3 if q in (3, 9) else q
        self.p = p
        if q == p:
            self.add = [[(x + y) % p for y in range(q)] for x in range(q)]
            self.mul = [[(x * y) % p for y in range(q)] for x in range(q)]
            self.neg = [(-x) % p for x in range(q)]
        else:
            mod = _MODULI[q]
            k = len(mod) - 1
            dig = lambda x: [(x // p**i) % p for i in range(k)]
            enc = lambda d: sum(c * p**i for i, c in enumerate(d))

            def fmul(x, y):
                a, b = dig(x), dig(y)
                prod = [0] * (2 * k - 1)
                for i, ai in enumerate(a):
                    if ai:
                        for j, bj in enumerate(b):
                            prod[i + j] = (prod[i + j] + ai * bj) % p
                for i in range(len(prod) - 1, k - 1, -1):
                    c = prod[i]
                    if c:
                        for j in range(k + 1):
                            prod[i - k + j] = (prod[i - k + j] - c * mod[j]) % p
                return enc(prod[:k])

            self.add = [[enc([(ai + bi) % p for ai, bi in zip(dig(x), dig(y))])
                         for y in range(q)] for x in range(q)]
            self.mul = [[fmul(x, y) for y in range(q)] for x in range(q)]
            self.neg = [enc([(-c) % p for c in dig(x)]) for x in range(q)]


# --------------------------------------------------------------------------
# Monic polynomial layer over a GF instance: tuples of coeffs, low -> high.
# --------------------------------------------------------------------------
ZPOLY = (0, 1)                    # the polynomial z


def _pnorm(t):
    i = len(t)
    while i > 0 and t[i - 1] == 0:
        i -= 1
    return tuple(t[:i])


def _pmod(F, f, g):
    """f mod g, g monic."""
    f = list(f)
    dg = len(g) - 1
    while len(f) - 1 >= dg and f:
        c = f[-1]
        if c:
            off = len(f) - 1 - dg
            for j in range(dg + 1):
                f[off + j] = F.add[f[off + j]][F.neg[F.mul[c][g[j]]]]
        f.pop()
    return _pnorm(f)


def _pdiv(F, f, g):
    """f / g exactly (g monic, g | f)."""
    f = list(f)
    dg = len(g) - 1
    qout = [0] * (len(f) - dg)
    while len(f) - 1 >= dg and f:
        c = f[-1]
        if c:
            off = len(f) - 1 - dg
            qout[off] = c
            for j in range(dg + 1):
                f[off + j] = F.add[f[off + j]][F.neg[F.mul[c][g[j]]]]
        f.pop()
    return tuple(qout)


def _monics(q, d):
    for lower in itertools.product(range(q), repeat=d):
        yield lower + (1,)


class PoolField:
    """F_{q0} with an irreducible sieve (deg <= L_MAX) and a factor memo."""

    def __init__(self, q0):
        self.q0 = q0
        self.F = GF(q0)
        self.irr = {1: list(_monics(q0, 1))}
        for d in range(2, L_MAX + 1):
            self.irr[d] = [f for f in _monics(q0, d)
                           if not self._has_small_factor(f, d // 2)]
        self._memo = {}

    def _has_small_factor(self, f, dmax):
        for e in range(1, dmax + 1):
            for g in self.irr[e]:
                if not _pmod(self.F, f, g):
                    return True
        return False

    def factor(self, f):
        """Complete monic factorization as a dict {irreducible: multiplicity}."""
        if f in self._memo:
            return self._memo[f]
        d = len(f) - 1
        if d == 0:
            res = {}
        else:
            res = None
            for e in range(1, d // 2 + 1):
                for g in self.irr[e]:
                    if not _pmod(self.F, f, g):
                        sub = dict(self.factor(_pdiv(self.F, f, g)))
                        sub[g] = sub.get(g, 0) + 1
                        res = sub
                        break
                if res is not None:
                    break
            if res is None:
                res = {f: 1}          # no factor of deg <= d/2 => irreducible
        self._memo[f] = res
        return res


# --------------------------------------------------------------------------
# The synthetic (K-SUB) table builder (the self-contained window model).
# --------------------------------------------------------------------------
def _classify(partition_items):
    """(K-SUB) (m, c)-classification of a factorization's (deg, mult) items:
    c = 0 -> TERM; m = 1 & c = 1 -> KCOL; m >= 2 & c >= 1 -> SPLIT."""
    m = len(partition_items)
    cc = sum(1 for _, mu in partition_items if mu >= 2)
    if cc == 0:
        return 'TERM'
    if m == 1:
        return 'KCOL'
    return 'SPLIT'


def build_ksub_tables(q0):
    """Synthetic (K-SUB)-shaped tables at pool q0: states = realized active
    window states (anchor pin a, window shape, e_read), columns = exit cells
    (terminal/hen + split) and still-in-block cells, entries = cell-count
    polynomials evaluated at q = q0 (exact enumeration over F_q0)."""
    P = PoolField(q0)
    # factor every monic cofactor once per length; shared across anchor pins
    cof = {}
    for l in range(1, L_MAX + 1):
        cof[l] = [(c, P.factor(c)) for c in _monics(q0, l)]

    # KA6b1 numeric cross-check: #squarefree monics deg l = q^l - q^{l-1} (l>=2)
    sqfree_counts = {}
    for l in range(1, L_MAX + 1):
        n_sf = sum(1 for _, fac in cof[l] if all(mu == 1 for mu in fac.values()))
        sqfree_counts[l] = n_sf

    states = []
    for a in range(0, A_MAX + 1):
        for l in range(1, L_MAX + 1):
            st = {'a': a, 'l': l, 'D': a + l,
                  'e_read': 1,   # anchors fire only at e_read = 1 (Species lemma);
                                 # a = 0 rows are stated in the same normalized frame
                  'models': {}}
            for model in MODELS:
                cells = {}
                sqfree_A = 0          # reading A: full residual squarefree
                cofexit = 0           # cofactor squarefree AND z does not divide it
                rB = {'TERM': 0, 'KCOL': 0, 'SPLIT': 0}   # reading B on R_anch
                n_digits = 0
                for c, fac in cof[l]:
                    vz = fac.get(ZPOLY, 0)
                    if model == 'vertex_pinned' and vz > 0:
                        continue      # left-endpoint vertex digit nonzero: z !| c
                    n_digits += 1
                    # reading A: full residual z^a * c
                    full = dict(fac)
                    if a + vz > 0:
                        full[ZPOLY] = a + vz
                    items = tuple(sorted((len(g) - 1, mu) for g, mu in full.items()))
                    ty = _classify(items)
                    key = str(items)
                    if key not in cells:
                        cells[key] = {'count': 0, 'type': ty}
                    cells[key]['count'] += 1
                    if ty == 'TERM':
                        sqfree_A += 1
                    cof_sqfree = all(mu == 1 for mu in fac.values())
                    if cof_sqfree and vz == 0:
                        cofexit += 1
                    # reading B: classify R_anch = c / z^vz (anchor rides outside)
                    ranch = {g: mu for g, mu in fac.items() if g != ZPOLY}
                    if not ranch:
                        rB['KCOL'] += 1        # pure-anchor digit choice
                    else:
                        rB[_classify(tuple((len(g) - 1, mu)
                                           for g, mu in ranch.items()))] += 1
                exit_A = sum(c['count'] for c in cells.values()
                             if c['type'] in ('TERM', 'SPLIT'))
                kcol_A = sum(c['count'] for c in cells.values()
                             if c['type'] == 'KCOL')
                st['models'][model] = {
                    'n_digit_choices': n_digits,
                    'cells': cells,
                    'sqfree_residual_count': sqfree_A,
                    'exit_count_A': exit_A,
                    'kcol_count_A': kcol_A,
                    'cofactor_exit_count': cofexit,
                    'readingB': {'term': rB['TERM'], 'kcol': rB['KCOL'],
                                 'split': rB['SPLIT'],
                                 'exit_count': rB['TERM'] + rB['SPLIT']},
                }
            states.append(st)

    return {
        'q0': q0,
        'transcription': ('self-contained window model (python twin of '
                          'Kernels/KA6b2.lean WindowModel); residual = z^a * '
                          'monic cofactor of degree l; exact enumeration over '
                          'F_q0; NO MovesSp import (spec DEPS clause)'),
        'grid': {'a': [0, A_MAX], 'l': [1, L_MAX]},
        'sqfree_monic_counts': sqfree_counts,
        'states': states,
    }


def anchored_states(tables, a_min=0, a_max=None):
    """Enumerate states with anchor pin a in [a_min, a_max], SORTED so that
    a >= 2 states come FIRST (the F2-mandated search order)."""
    sts = [s for s in tables['states']
           if s['a'] >= a_min and (a_max is None or s['a'] <= a_max)]
    return sorted(sts, key=lambda s: (0 if s['a'] >= 2 else 1, -s['a'], s['l']))


def exit_cells(state, model='free_surj'):
    """The exit cells (terminal/hen + split columns) of a state under the
    (K-SUB) classification."""
    return {k: v for k, v in state['models'][model]['cells'].items()
            if v['type'] in ('TERM', 'SPLIT')}


def squarefree_residual_count(state, q0=None):
    """Number of free window-digit choices whose residual is squarefree
    (the P1/P2 legs; must be 0 at a >= 2 by compiled arithmetic).
    Reading A / free_surj model — the sealed quantity."""
    return state['models']['free_surj']['sqfree_residual_count']


# --------------------------------------------------------------------------
# The REAL n <= 3 menu (escape_probe_a rosters = MovesV/DefsGate closed
# forms), transcribed as exact-Fraction closed forms for the P4 leg.
# --------------------------------------------------------------------------
def _fr(num, den):
    return Fraction(num, den)


REAL_MENU = {
    'blk2': [
        ('m2.o_split',  lambda q: _fr((q-1)*(q-2), 2*(q**3-1)), 'TERM'),
        ('m2.o_inert',  lambda q: _fr(q*(q-1), 2*(q**3-1)),     'TERM'),
        ('m2.o_double', lambda q: _fr(q-1, q**3-1),             'KCOL'),
        ('m_w2',        lambda q: _fr((q-1)*q**2, q**3-1),      'TERM'),
        ('m_vv',        lambda q: _fr(q-1, q**3-1),             'TERM'),
    ],
    'blk3': [
        ('A.3dist',     lambda q: _fr((q-1)*(q-2)*(q-3), 6*(q**6-1)), 'TERM'),
        ('A.linquad',   lambda q: _fr(q*(q-1)**2, 2*(q**6-1)),        'TERM'),
        ('A.irr',       lambda q: _fr(q**3-q, 3*(q**6-1)),            'TERM'),
        ('A.dblsimple', lambda q: _fr((q-1)*(q-2), q**6-1),           'SPLIT'),
        ('A.triple',    lambda q: _fr(q-1, q**6-1),                   'KCOL'),
        ('B',           lambda q: _fr((q-1)*(q**5+q**3), q**6-1),     'TERM'),
        ('C_odd',       lambda q: _fr((q-1)*q**4, q**6-1),            'TERM'),
        ('C_even.dist', lambda q: _fr((q-1)*(q-2), 2*(q**6-1)),       'TERM'),
        ('C_even.irr',  lambda q: _fr(q*(q-1), 2*(q**6-1)),           'TERM'),
        ('C_even.dbl',  lambda q: _fr(q-1, q**6-1),                   'SPLIT'),
        ('D_odd',       lambda q: _fr((q-1)**2*q**2, (q**3-1)*(q**6-1)),   'TERM'),
        ('D_even.dist', lambda q: _fr((q-1)**2*(q-2), 2*(q**3-1)*(q**6-1)), 'TERM'),
        ('D_even.irr',  lambda q: _fr(q*(q-1)**2, 2*(q**3-1)*(q**6-1)),    'TERM'),
        ('D_even.dbl',  lambda q: _fr((q-1)**2, (q**3-1)*(q**6-1)),        'SPLIT'),
        ('E',           lambda q: _fr((q-1)**2, (q**3-1)*(q**6-1)),        'TERM'),
    ],
    'root': [
        ('root.m_H3',   lambda q: _fr(q*(q-1)*(q-2), 6*q**3), 'TERM'),
        ('root.m_H12',  lambda q: _fr(q**2*(q-1), 2*q**3),    'TERM'),
        ('root.m_H<3>', lambda q: _fr(q**3-q, 3*q**3),        'TERM'),
        ('root.m_2+1',  lambda q: _fr(q*(q-1), q**3),         'ENTRY'),
        ('root.m_3',    lambda q: _fr(q, q**3),               'ENTRY'),
    ],
}


def cell_count_at_pool(cell, q0):
    """Evaluate the cell-count polynomial at q = q0 (exact Fraction) —
    real-menu leg; cell = (name, closed_form, type)."""
    return cell[1](q0)


# --------------------------------------------------------------------------
# The sweep.
# --------------------------------------------------------------------------
def sweep():
    """Main sweep: for each pool q0 and each state (a >= 2 first), record
    surviving exit cells; FINDING iff some (state, pool) has all exit cells
    dead.  Emit P1-P4 verdicts."""
    results = {'unit': 'KA6a', 'date': '2026-07-30', 'pools': POOLS,
               'grid': {'a': [0, A_MAX], 'l': [1, L_MAX]},
               'models': list(MODELS), 'primary': 'free_surj / reading A',
               'transcription': None, 'per_pool': {}, 'real_menu': {},
               'verdicts': {}, 'excluded_corner': (
                   'l = 0 (a = D) excluded: a read consumes a polygon side of '
                   'raw width w\' = e*l >= 1 (M-SPECIES SP.1 (side)), so '
                   'deg R_anch >= 1 at every realized read; under the window '
                   'model that corner would be the forced z^D still-in-block '
                   'cell with NO exit — it is a non-read, not a countermodel')}

    p1_ok, p2_ok, p3_all_survive, p4_ok = True, True, True, True
    all_exit_dead_rows = []

    print("=" * 72)
    print("1. SYNTHETIC WINDOW-MODEL SWEEP (anchored a >= 2 states FIRST)")
    print("=" * 72)
    for q0 in POOLS:
        tab = build_ksub_tables(q0)
        results['transcription'] = tab['transcription']
        pool_rows = []
        # KA6b1 count-law cross-check (context, not sealed)
        for l in range(2, L_MAX + 1):
            expect = q0**l - q0**(l - 1)
            got = tab['sqfree_monic_counts'][l]
            if got != expect:
                chk(f"q0={q0} l={l}: KA6b1 count law q^l - q^(l-1)", False,
                    f"enum={got} expected={expect}")
        for st in anchored_states(tab):
            a, l = st['a'], st['l']
            row = {'a': a, 'l': l, 'e_read': st['e_read'], 'models': {}}
            for model in MODELS:
                md = st['models'][model]
                ex = exit_cells(st, model)
                n_exit_cells_alive = sum(1 for v in ex.values() if v['count'] > 0)
                surv_A = md['exit_count_A'] > 0
                surv_B = md['readingB']['exit_count'] > 0
                row['models'][model] = {
                    'digit_choices': md['n_digit_choices'],
                    'exit_count_A': md['exit_count_A'],
                    'exit_cells_alive_A': n_exit_cells_alive,
                    'kcol_count_A': md['kcol_count_A'],
                    'sqfree_residual_count': md['sqfree_residual_count'],
                    'cofactor_exit_count': md['cofactor_exit_count'],
                    'readingB': md['readingB'],
                    'survives_A': surv_A, 'survives_B': surv_B,
                    'cells': md['cells'],
                }
                if not (surv_A and surv_B):
                    all_exit_dead_rows.append(
                        (q0, a, l, model,
                         'A' if not surv_A else 'B'))
                # internal consistency: cofactor-exit choices are exits
                if a >= 2 and md['cofactor_exit_count'] > md['exit_count_A']:
                    chk(f"q0={q0} (a={a},l={l},{model}): cofexit <= exit_A",
                        False, "consistency violated")
                # P1 / P2 on the sealed (primary) quantities
                if model == 'free_surj':
                    if a >= 2 and md['sqfree_residual_count'] != 0:
                        p1_ok = False
                        chk(f"P1 q0={q0} (a={a},l={l}): sqfree count == 0",
                            False, f"count={md['sqfree_residual_count']}")
                    if a <= 1 and md['sqfree_residual_count'] <= 0:
                        p2_ok = False
                        chk(f"P2 q0={q0} (a={a},l={l}): sqfree count > 0",
                            False, f"count={md['sqfree_residual_count']}")
                    if a >= 2 and not surv_A:
                        p3_all_survive = False
            pool_rows.append(row)
        results['per_pool'][str(q0)] = {'states': pool_rows,
                                        'sqfree_monic_counts':
                                            tab['sqfree_monic_counts']}
        # compact per-pool print: the a >= 2 zone first
        deep = [r for r in pool_rows if r['a'] >= 2]
        n_surv = sum(1 for r in deep
                     if all(r['models'][m]['survives_A'] and
                            r['models'][m]['survives_B'] for m in MODELS))
        fs = [f"(a={r['a']},l={r['l']}):exitA={r['models']['free_surj']['exit_count_A']}"
              f"/{r['models']['free_surj']['digit_choices']}"
              f",cof={r['models']['free_surj']['cofactor_exit_count']}"
              for r in deep[:4]]
        print(f"  q0={q0}: a>=2 states {n_surv}/{len(deep)} survive in ALL "
              f"model x reading variants; first rows {fs}")

    chk("P1: sqfree-residual count == 0 at EVERY a >= 2 (state, pool) "
        "[transcription leg]", p1_ok)
    chk("P2: sqfree-residual count > 0 at EVERY a <= 1 (state, pool) "
        "[the load-bearing seal]", p2_ok)

    print("=" * 72)
    print("2. P3 RECORD (open leg, either outcome a deliverable)")
    print("=" * 72)
    if not all_exit_dead_rows:
        print("  EVERY (state, pool) in the grid retains a surviving exit cell,")
        print("  in BOTH digit-set models AND both classification readings.")
        print("  At a >= 2 the survivor is the COFACTOR-CRITERION exit:")
        print("  free_surj: exit_count_A = q^l - 1 (all but the pure-anchor")
        print("  digit cell c = z^l); vertex_pinned: ALL (q-1)q^(l-1) realizable")
        print("  digit cells are exits (the still-in-block KCOL cell needs the")
        print("  vertex digit to vanish — pinned away); cofactor-criterion")
        print("  choices (c squarefree, z !| c) are positive at every (state,")
        print("  pool) — reading A types them SPLIT (anchor member continues")
        print("  into a strictly smaller block), reading B types them TERM;")
        print("  they are EXITS under both readings.")
    else:
        for q0, a, l, model, reading in all_exit_dead_rows:
            print(f"  ALL-EXIT-DEATH: q0={q0} (a={a},l={l}) model={model} "
                  f"reading={reading}")
    results['verdicts']['P3'] = {
        'all_a_ge_2_survive': p3_all_survive,
        'all_variants_survive': not all_exit_dead_rows,
        'dead_rows': all_exit_dead_rows,
        'consequence': ('KA6b2 keeps the per-state target at a >= 2 via the '
                        'cofactor mechanism (ka6b2_cofactor_exit is the '
                        'supported leg); NO reroute to class-level KA2c needed'
                        if not all_exit_dead_rows else
                        'REROUTE KA6b2 to the class-level escape (KA2c)'),
        'caveat_l0': ('the cofactor criterion equals an exit only at l >= 1; '
                      'l = 0 is not a read (side width w\' = e*l >= 1)'),
        'free_surj_note': ('exit survival is INSENSITIVE to the contested '
                           'free_surj premise: the vertex-pinned digit set '
                           '(z !| c) only removes still-in-block cells at '
                           'a >= 1, never the exits')}
    chk("P3 (recorded, not sealed): every a >= 2 (state, pool) retains an "
        "exit cell", p3_all_survive,
        "cofactor-criterion exit survives everywhere" if p3_all_survive else
        f"dead rows: {all_exit_dead_rows}")

    print("=" * 72)
    print("3. REAL n <= 3 MENU (P4 context re-check + real-menu search)")
    print("=" * 72)
    real = {}
    for q0 in POOLS:
        dead = [name for rows in REAL_MENU.values() for (name, fn, ty) in rows
                if fn(q0) == 0]
        per_state = {}
        for stname, rows in REAL_MENU.items():
            exit_alive = [name for (name, fn, ty) in rows
                          if ty in ('TERM', 'SPLIT') and fn(q0) > 0]
            per_state[stname] = {'exit_cells_alive': exit_alive,
                                 'survives': bool(exit_alive)}
            if not exit_alive:
                chk(f"real-menu q0={q0} state {stname}: some exit survives",
                    False, "ALL EXIT CELLS DEAD")
        real[str(q0)] = {'dead_cells': sorted(dead), 'per_state': per_state}
        print(f"  q0={q0}: dead cells {sorted(dead)}; all real states survive: "
              f"{all(v['survives'] for v in per_state.values())}")
    results['real_menu'] = real
    p4_ok = sorted(real['2']['dead_cells']) == sorted(DEAD_CELLS_Q2)
    chk("P4: q0=2 dead-cell list == escape_probe_a §2 sealed six", p4_ok,
        f"got {real['2']['dead_cells']}")
    real_menu_ok = all(v['survives'] for q0 in POOLS
                       for v in real[str(q0)]['per_state'].values())
    chk("real-menu search: every (state, pool) retains a surviving exit cell",
        real_menu_ok)

    results['verdicts'].update({
        'P1': p1_ok, 'P2': p2_ok, 'P4': p4_ok,
        'real_menu_all_survive': real_menu_ok,
        'FINDING': bool(FINDINGS)})
    return results


def main():
    print(f"KA6a exit-cell survival probe — RUN PHASE (grid a<= {A_MAX}, "
          f"l <= {L_MAX}, pools {POOLS})")
    print("Transcription: self-contained window model (KA6b2 WindowModel twin)"
          " + real n<=3 menu; seals P1-P4 verbatim from the E-phase header.")
    results = sweep()

    os.makedirs(os.path.dirname(OUTJSON), exist_ok=True)
    with open(OUTJSON, 'w') as fh:
        json.dump(results, fh, indent=1, default=str)
    print(f"JSON -> {OUTJSON}")

    verdict = "FINDING" if FINDINGS else "ALL SEALED LEGS PASS"
    block = ["", "##### ka6a_exit_survival_probe.py (UNIT KA6a run, "
                 "2026-07-30) #####",
             "transcription: self-contained window model (python twin of "
             "Kernels/KA6b2.lean WindowModel) + real n<=3 menu;",
             f"grid a in 0..{A_MAX}, l in 1..{L_MAX}, pools {POOLS}; "
             "models free_surj + vertex_pinned; readings A (full residual) + "
             "B (R_anch);",
             "l = 0 corner EXCLUDED (not a read: side width w' = e*l >= 1, "
             "M-SPECIES SP.1)."]
    block += PASSROWS[-6:] if not FINDINGS else FINDINGS
    block += [f"P3 record: every a >= 2 (state, pool) retains an exit cell — "
              f"{results['verdicts']['P3']['all_a_ge_2_survive']}; "
              "survivor = the cofactor-criterion exit (SPLIT under reading A, "
              "TERM under reading B); insensitive to the contested free_surj "
              "premise.",
              f"VERDICT: {verdict}; exit code {1 if FINDINGS else 0}."]
    with open(RESULTS_TXT, 'a') as fh:
        fh.write("\n".join(block) + "\n")
    print(f"results block appended -> {RESULTS_TXT}")

    print("=" * 72)
    if FINDINGS:
        print(f"KA6A VERDICT: {len(FINDINGS)} FINDING(S)")
        for row in FINDINGS:
            print("  " + row)
        return 1
    print("KA6A VERDICT: ALL SEALED LEGS PASS (P1, P2, P4; P3 recorded: "
          "all a >= 2 states retain the cofactor-criterion exit)")
    return 0


if __name__ == '__main__':
    sys.exit(main())
