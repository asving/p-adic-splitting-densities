#!/usr/bin/env python3
"""
HK-29 countermodel search probe (bridge campaign, BP2 Block Z, 2026-07-30).

TARGET: HC2/U4_freshCover.levelSet_no_straddle — search for a coherent+realizable
history H (i >= 1) with a fine slot j whose exact-valuation level set STRADDLES the
floor: one member in-band, another not.

WAVE-INVARIANCE (why this probe is valid despite HK-06 pending): the HK-06 wave
rewrites ONLY HistoryCoherent's non-recentering transition-core keying
(IsNodeLift/TransitionCoreL/s-t ties) and StageTransHyp.  The straddle geometry is
governed by the clauses this probe samples, ALL of which are wave-invariant:
  (C1) root degree 1 (=> Dwidth_0 = 1)          [coherence conj. 1 + Node.hDwidth]
  (C2) slope law: slope_m * (e_m*STR_m*D_m) = h_m [coherence conj. 2]
  (C5) window containment: s0_{m+1}+w_{m+1} <= mu_m [coherence, in conj. 4 tail]
  (C6) width chain: D_{m+1} = e_m*g_m*D_m        [coherence, in conj. 4 tail]
  (C7) strict slope steepening: slope_m < slope_{m+1} [coherence, in conj. 4 tail]
  (NL) node laws: e,h,g,mu >= 1; gcd(e,h)=1; e | wSide; mu*e*g <= wSide
       (the last from hOrd+hRanch+hpatTop+hpsi_deg: psi^mu | Ranch, deg Ranch=wSide/e)
  (SAE/NA) TransitionAdmissible clauses 1,3,4 via Realizable (clause 2 (HV) is
       residue data with no line content).
The probed class is a SUPERSET of the line data of every OLD-coherent AND every
candidate post-repair-coherent realizable history (the wave's clauses only ADD
constraints on stages/weights).  An empty search over the superset therefore settles
the gate for BOTH semantics; a hit would be a finding to re-check post-wave.

MODEL: nodes m = 0..len-1 carry (e,h,g,mu,s0,w,D,line=(intercept,slope)) exactly per
MovesC/Defs.lean: staircase_m(b) = line_m.at((b/cw_m)*cw_m) if b < mu_m*cw_m else BOT,
cw_m = e_m*g_m*D_m, floorH_i(b) = max_{r<i} staircase_r(b), slotVal_i(j) =
line_i.at(j*D_i), fineSlot window W_j = [j*D_i,(j+1)*D_i), prevRim(i) =
mu_{i-1}*cw_{i-1}, Line.at(b) = intercept - slope*b.  Exact rationals throughout.

STRADDLE (per the lemma, both legs checked): exists j and bases b, b' in W_j with
  c-side  : b  < prevRim  and  floorH_i(b)  < slotVal_i(j)   [c in-band]
  c'-side : (floorH_i(b') >= slotVal_i(j))  or  (b' >= prevRim)  [c' NOT in-band]
(heights: levelSet forces htH = slotVal_i(j) at both members, so the third band
clause is equality and the floor clause reads floorH < slotVal; the level-integrality
side condition only SHRINKS the countermodel class - superset direction, ignorable.)

RUNS: FULL (all constraints) + three ablations, each dropping ONE named clause:
  AB-SAE : drop TransitionAdmissible (realizability) entirely
  AB-C5  : drop window containment (s0 sampled freely; rim chain breaks)
  AB-C6  : drop the width chain (D_{m+1} sampled freely; grids misalign)

=== SEALED PREDICTIONS (written before first run; the a-priori analysis says the
=== floor is CONSTANT on every reachable fine-slot window under the full clause set):
  (P1) FULL run: ZERO straddles (floor leg AND rim leg), across all lengths 2..4
       and all target indices i >= 1.
  (P2) FULL run: the stronger invariant holds on every sampled config: floorH_i is
       constant on every window W_j with j < mu_{i-1}, and W_j lies entirely below
       prevRim (aligned windows).
  (P3) each ablation run finds >= 1 floor-leg straddle (AB-C6 may find rim-leg
       violations too) within the sample budget.
EXIT CODE: 0 iff P1..P3 all hold (probe PASS = the countermodel attempt STALLS and
the named clauses are exactly the blockers); 1 otherwise (PROBE-FINDING).
"""

import random
import sys
from fractions import Fraction
from math import gcd

random.seed(2026_07_30)

BOT = None  # WithBot bottom


class Node:
    __slots__ = ("e", "h", "g", "mu", "s0", "w", "D", "intercept", "slope")

    def __init__(self, **kw):
        for k, v in kw.items():
            setattr(self, k, v)

    @property
    def cw(self):  # childWidth
        return self.e * self.g * self.D

    def line_at(self, b):
        return self.intercept - self.slope * b

    def staircase(self, b):
        if b < self.mu * self.cw:
            return self.line_at((b // self.cw) * self.cw)
        return BOT


def floor_h(nodes, i, b):
    """History.floorH: max over r < i of staircase_r(b); BOT if all BOT."""
    best = BOT
    for r in range(i):
        v = nodes[r].staircase(b)
        if v is not None and (best is None or v > best):
            best = v
    return best


def lt_withbot(x, y):
    """x < y in WithBot Q (x may be BOT; y is a rational)."""
    return True if x is None else x < y


def rand_frac(lo=-30, hi=120, dens=(1, 2, 3, 4, 6, 12)):
    d = random.choice(dens)
    return Fraction(random.randint(lo * d, hi * d), d)


def sample_history(length, drop_sae=False, drop_c5=False, drop_c6=False,
                   max_D=64, max_rim=512):
    """Constructively sample node data satisfying the (non-dropped) clause set.
    Returns list[Node] or None (size cap / arithmetic dead end)."""
    nodes = []
    STR = 1
    for m in range(length):
        parent = nodes[-1] if nodes else None
        # --- widths ---
        if m == 0:
            D = 1  # (C1)
        elif drop_c6:
            D = random.choice([1, 2, 3, 4, 6])
        else:
            D = parent.cw  # (C6)
        if D > max_D:
            return None
        # --- e, g (recenterings = the (1,1) draws, naturally interleaved) ---
        e = random.choice([1, 1, 2, 3])
        g = random.choice([1, 1, 2, 3])
        # --- mu, w with (NL) mu*e*g <= w and e | w ---
        # deep nodes need room: bias mu large early, small late
        mu_hi = max(1, 12 // (m + 1))
        mu = random.randint(1, mu_hi)
        w = e * (mu * g + random.randint(0, 3))  # e | w and mu*e*g <= w
        # --- s0 with (C5) s0 + w <= mu_parent ---
        if parent is None or drop_c5:
            s0 = random.randint(0, 4)
        else:
            if parent.mu < w:
                return None  # containment unsatisfiable; resample
            s0 = random.randint(0, parent.mu - w)
        # --- h with gcd(e,h)=1 and (C7) slope increasing ---
        # slope = h/(e*STR*D); need slope > parent.slope
        den = e * STR * D
        if parent is None:
            h = random.randint(1, 6)
        else:
            hmin = int(parent.slope * den) + 1
            h = hmin + random.randint(0, 5)
        for _ in range(50):
            if gcd(e, h) == 1:
                break
            h += 1
        if gcd(e, h) != 1:
            return None
        slope = Fraction(h, den)
        if parent is not None and not slope > parent.slope:
            return None  # (C7) — should not happen by construction
        # --- intercept: free at root; (SAE)/(NA) window between consecutive pairs ---
        if parent is None:
            intercept = rand_frac()
        else:
            sd = slope - parent.slope  # > 0
            x_vtx = parent.mu * parent.cw
            # top span-grid point strictly below the old vertex:
            jtop = min(s0 + w, parent.mu - 1) if not drop_c5 else \
                   min(s0 + w, parent.mu - 1)
            x_top = jtop * parent.cw
            adjacent = (s0 + w == parent.mu)
            if drop_sae:
                intercept = parent.intercept + rand_frac(-40, 40)
            elif adjacent:
                # (SAE cl.4): equality at the vertex pins the intercept;
                # cl.3 strict below follows since the line gap decreases in x.
                intercept = parent.intercept + sd * x_vtx
            else:
                # (SAE cl.3) at all span slots j'' <= jtop  <=>  gap > 0 at x_top
                # (NA cl.1): gap < 0 at x_vtx.  Window (sd*x_top, sd*x_vtx).
                lo, hi = sd * x_top, sd * x_vtx
                if not lo < hi:
                    return None
                t = Fraction(random.randint(1, 15), 16)
                intercept = parent.intercept + lo + (hi - lo) * t
        nodes.append(Node(e=e, h=h, g=g, mu=mu, s0=s0, w=w, D=D,
                          intercept=intercept, slope=slope))
        STR *= e
        if nodes and m >= 1 and nodes[m - 1].mu * nodes[m - 1].cw > max_rim:
            return None
    return nodes


def check_config(nodes, i, record, full_run):
    """Search all reachable windows of target node i for straddles.
    Returns list of straddle dicts; if full_run, also verifies (P2) invariants."""
    straddles = []
    nu = nodes[i]
    prev = nodes[i - 1]
    prev_rim = prev.mu * prev.cw
    Di = nu.D
    if Di == 0:
        return straddles
    j_max = prev_rim // Di + 2  # windows possibly meeting [0, prev_rim)
    for j in range(0, j_max):
        W = range(j * Di, (j + 1) * Di)
        S = nu.line_at(j * Di)  # slotVal_i(j)
        floors = [floor_h(nodes, i, b) for b in W]
        c_bases = [b for b in W
                   if b < prev_rim and lt_withbot(floor_h(nodes, i, b), S)]
        if not c_bases:
            continue  # no in-band member; lemma hypotheses unsatisfiable here
        cp_bad = [b for b in W
                  if (b >= prev_rim) or (not lt_withbot(floor_h(nodes, i, b), S))]
        if cp_bad:
            straddles.append(dict(j=j, S=S, c=c_bases[0], cprime=cp_bad[0],
                                  floors=[str(f) for f in floors],
                                  rim=prev_rim))
        if full_run:
            # (P2a) aligned windows: some base < prevRim => whole window < prevRim
            if any(b >= prev_rim for b in W):
                record["p2_rim_misaligned"] += 1
            # (P2b) floor constant on the window
            if len(set(floors)) != 1:
                record["p2_floor_varies"] += 1
    return straddles


def run(tag, n_samples, **drops):
    full_run = not any(drops.values())
    record = dict(p2_rim_misaligned=0, p2_floor_varies=0)
    found = []
    tried = 0
    for _ in range(n_samples):
        length = random.choice([2, 3, 3, 4])
        nodes = sample_history(length, **drops)
        if nodes is None:
            continue
        tried += 1
        for i in range(1, length):
            hits = check_config(nodes, i, record, full_run)
            for hcm in hits:
                hcm["i"] = i
                hcm["nodes"] = [(nd.e, nd.h, nd.g, nd.mu, nd.s0, nd.w, nd.D,
                                 str(nd.intercept), str(nd.slope)) for nd in nodes]
                found.append(hcm)
    print(f"[{tag}] configs accepted: {tried}/{n_samples}; straddles: {len(found)}; "
          f"P2 rim-misaligned: {record['p2_rim_misaligned']}; "
          f"P2 floor-varies: {record['p2_floor_varies']}")
    if found:
        ex = found[0]
        print(f"  example: i={ex['i']} j={ex['j']} slotVal={ex['S']} "
              f"c-base={ex['c']} c'-base={ex['cprime']} rim={ex['rim']}")
        print(f"    floors on window: {ex['floors']}")
        print(f"    nodes (e,h,g,mu,s0,w,D,int,slope): {ex['nodes']}")
    return found, record


def main():
    N = 40000
    ok = True

    full_found, full_rec = run("FULL", N)
    p1 = len(full_found) == 0
    p2 = full_rec["p2_rim_misaligned"] == 0 and full_rec["p2_floor_varies"] == 0
    print(f"P1 (FULL: zero straddles): {'HOLDS' if p1 else 'FAILS'}")
    print(f"P2 (FULL: aligned windows + constant floor): {'HOLDS' if p2 else 'FAILS'}")
    ok &= p1 and p2

    ab_results = {}
    for tag, drops in [("AB-SAE", dict(drop_sae=True)),
                       ("AB-C5", dict(drop_c5=True)),
                       ("AB-C6", dict(drop_c6=True))]:
        f, _ = run(tag, N, **drops)
        ab_results[tag] = len(f)
    p3 = all(v >= 1 for v in ab_results.values())
    print(f"P3 (each ablation finds a straddle): "
          f"{'HOLDS' if p3 else 'FAILS'} {ab_results}")
    ok &= p3

    print("PROBE RESULT:", "PASS (P1-P3 sealed predictions all hold)" if ok
          else "FINDING (a sealed prediction failed)")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
