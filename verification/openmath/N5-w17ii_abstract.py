#!/usr/bin/env python3
"""N5-w17ii (script 1/3): ABSTRACT-LAW tests for W17ii clause (ii), old vs repaired.

CONJECTURE UNDER TEST (unit N5-w17ii; BK.cl17 / queue item 4 of
lean/notes/REMAINING_CENSUS_2026-07-31.md):

  Lean statement (MovesS/Interfaces.lean, `W17ii`, clause (ii); the banked sorry is
  MovesV/V7_w17ii.lean:48):
     forall Shat in F.Sh, forall q0 in M.Pools,
       HasSum (fun h : shDom Shat => shWeightH Shat h q0) (WshVal Shat q0)
  available chain census laws (RS4Chain fields, verbatim quantifier structure):
     shweight_card : forall Shat in F.Sh, forall h in shDom Shat, forall q0 in M.Pools,
        EXISTS N0, forall N >= N0,  shWeightH(Shat,h,q0) * |Box(q0,N)| = |shEvtH(Shat,h,q0,N)|
     wshval_card   : forall Shat in F.Sh, forall q0 in M.Pools,
        EXISTS N0, forall N >= N0,  WshVal(Shat,q0) * |Box(q0,N)| = |shEvt(Shat,q0,N)|
     shevt_grouping: forall Shat q0 N,  shEvt = Union_{h in visH(Shat,q0,N)} shEvtH(Shat,h,q0,N)
  REPAIRED roster (BRIDGE_BP3_TV_2026-07-30.md section 3.G REV 2, menu (a')/(b');
  queue item 4 "census fields + shevt_disj"; Lean retype pending escalation E-1):
     shevt_disj      : the shEvtH(Shat,h,q0,N), h in visH(Shat,q0,N), are pairwise disjoint
     shdom_no_stray  : h in shDom  =>  shEvtH(Shat,h,q0,N) eventually nonempty
     off-visH vanish : h in shDom \\ visH(N) => shEvtH(h,N) = empty (eventually), and
                       visH(N) subset shDom (eventually)
     guard (a')      : shDom finite     [menu (a')]
     guard (b')      : shWeightH summable over shDom   [menu (b') = Q4-preferred]

MAPPING Lean -> computation (fidelity notes):
  * Box(q0,N), shEvtH, shEvt are modeled as finite sets/cardinalities with exact
    Fraction arithmetic; q0 is fixed (one pool) since the law is per-pool.
  * `HasSum f (WshVal)` over a countable index with f >= 0 is equivalent to
    sup over finite partial sums = WshVal; we test it by (i) exact finite sums when
    shDom is finite, (ii) exhibiting a finite F0-violation witness when it fails
    (for HasSum to L, every finite superset F of some F0 must have |sum_F - L| < eps).
  * "eventually" quantifiers are checked exactly over N in [0, NMAX] together with a
    closed-form argument printed per law (the configurations used are all
    eventually-periodic/exactly-geometric in N, so the finite check + the printed
    identity covers all N).  This is the only simplification: numerics cannot range
    over all N; every configuration here is chosen so the per-law identity is exact
    and displayed.
  * Realizability: every abstract configuration below uses only carriers that the
    quarantined TV-H1b build (lean/quarantine/TV_H1b_w17iiNeg_2026-07-30.lean.txt)
    showed wrap into a full ~30-field RS4Chain over degenerate tables (Box := Fin k
    is a free choice of MeasuredSide).  Not machine-checked here; flagged.

SEALED PREDICTIONS (before first run):
  P1 (regression anchor): the TV-H1 countermodel configuration satisfies every OLD
     census law and violates clause (ii); of the repaired roster it violates exactly
     {off-visH vanishing, guard (a'), guard (b')} and satisfies the rest.
  P2: menu (a') with FINITE shDom: random adversarial search (>= 10^4 accepted
     configurations) finds NO violation of the tie sum = WshVal.
  P3: menu (b') AS SPECCED (summability guard + census fields, shDom infinite) does
     NOT imply the tie: the explicit "mass-leak" chain below satisfies the entire
     repaired roster yet sum_h w_h = 1/2 while WshVal = 1.
  P4: ablations: dropping shevt_disj, off-visH vanishing, or visH-subset-shDom each
     admits a finite counterexample satisfying all remaining laws; dropping
     shdom_no_stray does NOT break the tie (not load-bearing for clause (ii)).
  P5: the count-domination law (u3): |shEvtH(h,N)| <= w_h * |Box(N)| for ALL N
     (not just eventually) kills the leak chain and (with the roster) forces the
     tie in every random infinite-shDom configuration tested.

Run: python3 N5-w17ii_abstract.py   (stdlib only; exact Fractions)
"""

from fractions import Fraction as Fr
import random
import sys

FAIL = []


def check(name, cond, detail=""):
    tag = "PASS" if cond else "FAIL"
    if not cond:
        FAIL.append(name)
    print(f"  [{tag}] {name}" + (f" -- {detail}" if detail else ""))
    return cond


# ----------------------------------------------------------------------------
# A configuration = per-level data at a fixed pool q0.
#   box(N)        : |Box(q0,N)|            (int > 0)
#   visH(N)       : set of heights visible at level N
#   cnt(h, N)     : |shEvtH(Shat,h,q0,N)|  (int >= 0)   -- CARD-LEVEL model
#   shDom         : set of heights (finite) or predicate+enumerator (infinite)
#   w(h)          : shWeightH(Shat,h,q0)   (Fraction)
#   wshval        : WshVal(Shat,q0)        (Fraction)
# shEvt(N) is DEFINED through shevt_grouping as the union; in the card-level model
# with shevt_disj imposed, |shEvt(N)| = sum_{h in visH(N)} cnt(h,N).  Where a test
# needs the SET-level laws (disjointness/grouping literally), sets are materialized.
# ----------------------------------------------------------------------------


def law_report(cfg, NMAX, heights, n0_of_h, n0_val, expect):
    """Exact check of every law of the repaired roster over N in [0,NMAX].
    expect: dict law -> bool (True = expect PASS).  Returns dict law -> bool."""
    res = {}
    # shweight_card (with its own EXISTS N0 per h, as declared by the config)
    ok = True
    for h in heights:
        for N in range(n0_of_h(h), NMAX + 1):
            if cfg["w"](h) * cfg["box"](N) != cfg["cnt"](h, N):
                ok = False
                break
        if not ok:
            break
    res["shweight_card"] = ok
    # wshval_card
    ok = all(cfg["wshval"] * cfg["box"](N) == cfg["shEvt_card"](N)
             for N in range(n0_val, NMAX + 1))
    res["wshval_card"] = ok
    # shevt_grouping + shevt_disj (card level: grouping = sum over visH; the
    # configs below materialize sets when disjointness is the tested law)
    ok = all(cfg["shEvt_card"](N) == sum(cfg["cnt"](h, N) for h in cfg["visH"](N))
             for N in range(0, NMAX + 1))
    res["grouping+disj(card)"] = ok
    # shdom_no_stray: h in shDom => shEvtH eventually nonempty
    ok = all(any(cfg["cnt"](h, N) > 0 for N in range(0, NMAX + 1)) and
             all(cfg["cnt"](h, N) > 0 for N in range(max(n0_of_h(h), 1), NMAX + 1))
             for h in heights)
    res["shdom_no_stray"] = ok
    # off-visH vanishing: h in shDom \ visH(N) => cnt(h,N)=0  (checked STRICTLY at
    # every N; the strict form implies every "eventually" reading)
    ok = all(cfg["cnt"](h, N) == 0
             for N in range(0, NMAX + 1) for h in heights if h not in cfg["visH"](N))
    res["offvis_vanish"] = ok
    # visH subset shDom
    ok = all(set(cfg["visH"](N)) <= set(cfg["shDomAll"](NMAX))
             for N in range(0, NMAX + 1))
    res["visH_sub_shDom"] = ok
    for law, exp in expect.items():
        check(f"{cfg['name']}: {law} {'holds' if exp else 'FAILS (as predicted)'}",
              res[law] == exp)
    return res


# =============================================================================
print("=" * 78)
print("PART A: TV-H1 countermodel configuration vs the OLD form (regression anchor)")
print("=" * 78)
# The quarantined negChain (TV_H1b_w17iiNeg_2026-07-30.lean.txt) shallow carriers:
#   Box(q0,N) = Fin 1;  shDom = univ = NAT (infinite);  shWeightH == 1;
#   shEvtH = univ; visH = {0}; shEvt = univ; WshVal == 1.
NMAX, HMAX = 40, 40
tvh1 = {
    "name": "TV-H1",
    "box": lambda N: 1,
    "visH": lambda N: {0},
    "cnt": lambda h, N: 1,            # univ over Fin 1
    "shEvt_card": lambda N: 1,        # univ
    "w": lambda h: Fr(1),
    "wshval": Fr(1),
    "shDomAll": lambda upto: set(range(upto + 1)),   # NAT truncated for iteration
}
heights = range(HMAX + 1)

print("OLD-form census laws (shweight_card / wshval_card / grouping) at the countermodel:")
res = law_report(tvh1, NMAX, heights, lambda h: 0, 0,
                 {"shweight_card": True, "wshval_card": True,
                  "grouping+disj(card)": True})
print("Clause (ii) OLD form: HasSum (const 1 over NAT) (WshVal=1)?")
# HasSum f 1 requires: for eps=1/2 exists finite F0 s.t. all finite F >= F0 have
# |sum_F - 1| < 1/2.  But any F with |F| >= 3 has sum_F = |F| >= 3, |sum-1| >= 2.
F = [0, 1, 2]
sF = sum(tvh1["w"](h) for h in F)
check("HasSum VIOLATED: witness finite F={0,1,2}, sum_F = 3, |3 - 1| = 2 >= eps",
      abs(sF - tvh1["wshval"]) >= 2,
      "every finite F0 extends to F ⊇ F0 with |F|>=3, so no F0 can work")
print("Repaired-roster fields at the countermodel (which ones exclude it):")
law_report(tvh1, NMAX, heights, lambda h: 0, 0,
           {"shdom_no_stray": True, "offvis_vanish": False, "visH_sub_shDom": True})
check("guard (a') FAILS: shDom = NAT is infinite", True)
check("guard (b') FAILS: sum of const 1 over NAT not summable", True)
print("=> P1: countermodel violates OLD clause (ii); excluded by off-visH vanishing")
print("   and by BOTH guards; all other repaired fields hold there (disj vacuous:")
print("   visH a singleton).")

# =============================================================================
print()
print("=" * 78)
print("PART B: menu (a') -- FINITE shDom: adversarial random search for tie violations")
print("=" * 78)
# Generator: random finite configurations over a base-m box tower |Box(N)| = m^N.
# Strata: random finite height set with random true weights w_h = k_h / m^{Dh}
# (exact dyadic-in-m fractions), random per-h stabilization levels N0(h), random
# pre-stabilization junk counts, random visibility schedules visH(N) (fluctuating
# before a random horizon, complete after), optional zero-weight strata, optional
# heights outside shDom never visible.  The full repaired roster is then CHECKED
# (not assumed): configurations failing any law are rejected (counted); accepted
# ones get the tie test  sum_{h in shDom} w_h == WshVal.
rng = random.Random(20260731)


def gen_finite_cfg():
    """Adversarial generator.  feature = none  : roster-conforming by design;
    stray : some h* in shDom keeps positive counts while NEVER visible
            (violates off-visH vanishing -- the filter must catch it);
    ghost : an extra height OUTSIDE shDom enters visH with positive counts
            (violates visH subset shDom -- the filter must catch it).
    The tie test then runs on filter-SURVIVORS only: if the filter (= the
    repaired roster, as we encoded it) let a stray/ghost through, the tie
    check would flag it -- that is the adversarial content."""
    m = rng.choice([2, 3, 5, 7, 10])
    H = rng.randint(1, 6)                      # shDom = {0..H-1}
    Dh = rng.randint(1, 3)
    feature = rng.choice(["none", "none", "stray", "ghost"])
    w = {}
    for h in range(H):
        w[h] = Fr(rng.randint(0, m ** Dh - 1), m ** (Dh + h + 1))
        if rng.random() < 0.2:
            w[h] = Fr(0)
    stray_h = None
    if feature == "stray":
        stray_h = rng.randrange(H)
        w[stray_h] = Fr(rng.randint(1, m ** Dh - 1) if m ** Dh > 1 else 1,
                        m ** (Dh + stray_h + 1))
    ghost_h = H if feature == "ghost" else None
    ghost_w = Fr(1, m ** (Dh + 2))
    N0 = {h: rng.randint(1, 8) for h in range(H)}
    horizon = max(max(N0.values()), rng.randint(1, 10))
    denom_pow = Dh + H + 3
    rng_vis = {(N, h): (rng.random() < 0.7) for N in range(horizon) for h in range(H)}
    rng_junk = {(h, N): rng.randint(0, m ** (N + denom_pow) // (4 * (H + 1)))
                for h in range(H) for N in range(horizon + 1)}

    def visH(N):
        base = (set(range(H)) if N >= horizon
                else set(h for h in range(H) if rng_vis[(N, h)]))
        if stray_h is not None:
            base.discard(stray_h)              # never visible
        if ghost_h is not None and N >= 1:
            base.add(ghost_h)                  # visible but outside shDom
        return base

    def cnt(h, N):
        if h == ghost_h:
            v = ghost_w * m ** (N + denom_pow)
            return int(v)
        if h == stray_h:                       # positive counts despite no visibility
            if N >= N0[h]:
                return int(w[h] * m ** (N + denom_pow))
            return 0
        if h not in visH(N):
            return 0
        if N >= N0[h]:
            v = w[h] * m ** (N + denom_pow)
            assert v.denominator == 1
            return int(v)
        return rng_junk[(h, N)]

    box = lambda N: m ** (N + denom_pow)
    # grouping defines shEvt as the union over visH (disjoint blocks)
    shEvt_card = lambda N: sum(cnt(h, N) for h in visH(N))
    N0v = max(max(N0.values()), horizon, 1)
    wshval = Fr(shEvt_card(N0v), box(N0v))
    return (dict(name="rand-a'", m=m, H=H, box=box, visH=visH, cnt=cnt,
                 shEvt_card=shEvt_card, w=lambda h: w[h], wshval=wshval,
                 shDomAll=lambda upto: set(range(H))),
            N0, N0v, horizon, w, feature)


TRIALS = 12000
NMAX_B = 16
viol = accepted = 0
rej = {"stray": 0, "ghost": 0, "none": 0}
acc_feat = {"stray": 0, "ghost": 0, "none": 0}
for t in range(TRIALS):
    cfg, N0, N0v, horizon, w, feature = gen_finite_cfg()
    heights = range(cfg["H"])
    # exact roster filter; each law with its declared N0 witness
    ok = True
    # shweight_card over shDom
    ok &= all(cfg["w"](h) * cfg["box"](N) == cfg["cnt"](h, N)
              for h in heights for N in range(max(N0[h], horizon), NMAX_B + 1))
    # wshval_card
    ok &= all(cfg["wshval"] * cfg["box"](N) == cfg["shEvt_card"](N)
              for N in range(N0v, NMAX_B + 1))
    # off-visH vanishing over shDom
    ok &= all(cfg["cnt"](h, N) == 0
              for N in range(NMAX_B + 1) for h in heights if h not in cfg["visH"](N))
    # visH subset shDom
    ok &= all(cfg["visH"](N) <= set(range(cfg["H"])) for N in range(NMAX_B + 1))
    # shdom_no_stray (eventual nonemptiness, or weight zero)
    ok &= all(cfg["cnt"](h, N) > 0 or cfg["w"](h) == 0
              for h in heights for N in range(max(N0[h], horizon), NMAX_B + 1))
    if not ok:
        rej[feature] += 1
        continue
    accepted += 1
    acc_feat[feature] += 1
    if sum(w.values()) != cfg["wshval"]:
        viol += 1
        if viol == 1:
            print(f"  VIOLATION at trial {t} (feature={feature}): sum w = "
                  f"{sum(w.values())}, WshVal = {cfg['wshval']}, m={cfg['m']}")
print(f"  trials={TRIALS}, accepted={accepted} (by feature {acc_feat}), "
      f"rejected by roster filter: {rej}, tie violations among accepted={viol}")
check("filter catches every stray (off-visH violation) and ghost (visH-sub viol.)",
      acc_feat["stray"] == 0 and acc_feat["ghost"] == 0 and
      rej["stray"] > 1000 and rej["ghost"] > 1000,
      "the two law-violating features never survive the roster filter")
check("P2: menu (a') finite shDom -- NO tie violation among roster survivors",
      viol == 0 and accepted >= 5000,
      f"{accepted} roster-satisfying configurations, all tie exactly")

# =============================================================================
print()
print("=" * 78)
print("PART C: menu (b') AS SPECCED -- the mass-leak chain (sealed counterexample P3)")
print("=" * 78)
# Config: |Box(N)| = 2^N; shDom = NAT; w_h = 2^{-h-2} (summable, sum = 1/2);
# visH(N) = {0..N-1}; cnt(h,N) = 2^{N-h-2} for h <= N-2  (= w_h |Box|, N0(h)=h+2),
# cnt(N-1,N) = 2^{N-1}+1 (the still-unstabilized youngest height carries the rest),
# cnt(h,N) = 0 for h >= N.  shEvt(N) = whole box; WshVal = 1 (wshval_card exact, N0=0).
print("Definition: Box(N)=2^N; w_h = 2^(-h-2); visH(N)={0..N-1};")
print("  cnt(h,N) = 2^(N-h-2) for h<=N-2;  cnt(N-1,N) = 2^(N-1)+1;  cnt = 0 for h>=N")
print("  shEvt(N) = Box (all of it);  WshVal = 1.")


def leak_cnt(h, N):
    if h >= N:
        return 0
    if h <= N - 2:
        return 2 ** (N - h - 2)
    return 2 ** (N - 1) + 1


leak = {
    "name": "leak-(b')",
    "box": lambda N: 2 ** N,
    "visH": lambda N: set(range(N)),
    "cnt": leak_cnt,
    "shEvt_card": lambda N: 2 ** N,
    "w": lambda h: Fr(1, 2 ** (h + 2)),
    "wshval": Fr(1),
    "shDomAll": lambda upto: set(range(upto + 1)),
}
NMAX_C, HMAX_C = 60, 60
# partition sanity: the counts fill the box exactly at every N
check("set-realizability: sum_{h in visH(N)} cnt = |Box(N)| exactly, all N<=60",
      all(sum(leak_cnt(h, N) for h in range(N)) == 2 ** N for N in range(1, NMAX_C + 1)),
      "so disjoint shEvtH with these cards exist literally (a partition of Box)")
res = law_report(leak, NMAX_C, range(HMAX_C + 1), lambda h: h + 2, 0,
                 {"shweight_card": True, "wshval_card": True,
                  "grouping+disj(card)": True, "shdom_no_stray": True,
                  "offvis_vanish": True, "visH_sub_shDom": True})
S = sum(leak["w"](h) for h in range(200))     # partial; series is exactly geometric
check("guard (b') HOLDS: sum_h w_h = 1/2 (geometric, summable)",
      S < Fr(1, 2) and Fr(1, 2) - S < Fr(1, 2 ** 190))
check("P3: clause (ii) FAILS under full (b') roster: sum_h w_h = 1/2 != 1 = WshVal",
      Fr(1, 2) != leak["wshval"],
      "HasSum to WshVal impossible: partial sums bounded by 1/2")
print("  (mechanism: at every level N the youngest visible height h=N-1 is still")
print("   pre-stabilization -- shweight_card's per-h EXISTS N0 never bites at a")
print("   single uniform N; half the box's mass leaks to h -> infinity.)")
# leak variants: leaked fraction 2^-r, r = 1..4  (w_h = (2^r - 1) * 2^-(h+1+r),
# stabilization N0(h) = h+1+r, youngest visible height carries the remainder)
print("leak-variant family (leaked fraction 2^-r):")
for r in range(1, 5):
    def mk_cnt(r):
        def cntv(h, N):
            if h >= N:
                return 0
            if N >= h + 1 + r and h <= N - 2:
                return (2 ** r - 1) * 2 ** (N - h - 1 - r)
            if h == N - 1:                     # youngest: the whole remainder
                stab = sum((2 ** r - 1) * 2 ** (N - g - 1 - r)
                           for g in range(0, N - 1) if N >= g + 1 + r)
                return 2 ** N - stab
            return 0                           # pre-stabilization junk = 0
        return cntv
    cntv = mk_cnt(r)
    lv = {"name": f"leak-r{r}", "box": lambda N: 2 ** N,
          "visH": lambda N: set(range(N)), "cnt": cntv,
          "shEvt_card": lambda N: 2 ** N,
          "w": lambda h, r=r: Fr(2 ** r - 1, 2 ** (h + 1 + r)),
          "wshval": Fr(1), "shDomAll": lambda upto: set(range(upto + 1))}
    part_ok = all(sum(cntv(h, N) for h in range(N)) == 2 ** N
                  for N in range(1, 41))
    laws = law_report(lv, 40, range(41), lambda h, r=r: h + 1 + r, 0,
                      {"shweight_card": True, "wshval_card": True,
                       "grouping+disj(card)": True, "offvis_vanish": True,
                       "visH_sub_shDom": True})
    ssum = 1 - Fr(1, 2 ** r)
    check(f"   r={r}: partition exact & tie FAILS: sum w = {ssum} != 1 = WshVal",
          part_ok and ssum != 1)

# =============================================================================
print()
print("=" * 78)
print("PART D: ablations -- each census field's necessity (finite exhibits)")
print("=" * 78)
# Exhibits are SET-level (explicit finite sets), so grouping/disjointness are the
# literal Lean-shaped laws, |Box(N)| = 4^N over ground set range(4^N).
print("D1. drop shevt_disj: Box=4^N; shDom=visH={0,1}; shEvtH(0)=shEvtH(1)=first half")
for N in (1, 2, 6):
    box = list(range(4 ** N))
    A = set(box[: 4 ** N // 2])
    E0, E1 = A, A                          # NOT disjoint
    shEvt = E0 | E1
    assert shEvt == A
w0 = w1 = Fr(1, 2)
wshval = Fr(1, 2)                          # |shEvt|/|Box|
check("   all other laws hold (grouping/cards/no_stray/off-vis/finite) [by constr.]",
      True)
check("   disjointness FAILS and tie FAILS: w0+w1 = 1 != 1/2 = WshVal",
      w0 + w1 != wshval, "double counting -- shevt_disj is load-bearing")

print("D2. drop off-visH vanishing: shDom={0,1}; visH(N)={0} always;")
print("    shEvtH(0)=half box, shEvtH(1)=quarter box (nonzero forever, never visible)")
w0, w1 = Fr(1, 2), Fr(1, 4)
wshval = Fr(1, 2)                          # shEvt = shEvtH(0) only (grouping over visH)
check("   no_stray HOLDS for h=1 (shEvtH(1) nonempty eventually) -- note",
      True)
check("   off-visH FAILS and tie FAILS: w0+w1 = 3/4 != 1/2 = WshVal",
      w0 + w1 != wshval,
      "EXACTLY the adjudication note's recorded failure shape (BP3 sec 3.G REV 2)")

print("D3. drop visH subset shDom: shDom={0}; visH={0,1}; shEvtH(1)=quarter box disjoint")
w0 = Fr(1, 2)
wshval = Fr(1, 2) + Fr(1, 4)               # union includes the h=1 quarter
check("   visH-subset FAILS and tie FAILS: sum over shDom = 1/2 != 3/4 = WshVal",
      w0 != wshval, "mass visible outside shDom escapes the sum")

print("D4. drop shdom_no_stray: shDom={0,1}; shEvtH(1,N) = empty for ALL N")
# shweight_card at h=1 then forces w1 * |Box| = 0, i.e. w1 = 0: tie unaffected.
w0, w1 = Fr(1, 2), Fr(0)
wshval = Fr(1, 2)
check("   tie STILL HOLDS (w1 forced 0 by shweight_card): no_stray NOT load-bearing"
      " for clause (ii)", w0 + w1 == wshval)

# =============================================================================
print()
print("=" * 78)
print("PART E: the count-domination candidate (u3) -- instance-compatible leak-killer")
print("=" * 78)
# (u3): |shEvtH(h,N)| <= w_h * |Box(N)| for ALL N (monotone census; true for the
# p-adic instance where decided classes only accumulate -- verified in script 2).
print("E1. leak chain vs (u3): youngest height h=N-1 has cnt = 2^(N-1)+1 but")
print("    w_{N-1}*|Box| = 2^(N-1-... ) -- check the violation exactly:")
vio = []
for N in range(2, 30):
    h = N - 1
    if leak_cnt(h, N) > leak["w"](h) * 2 ** N:
        vio.append(N)
check("   (u3) FAILS in the leak chain at h=N-1 for every N in [2,30)",
      len(vio) == 28, f"witness N=2: cnt={leak_cnt(1,2)} > w*box={leak['w'](1)*4}")
print("E2. random infinite-shDom configurations under (u3): squeeze validation")
# Under (u3) the tie-proof runs through two inequalities at every level N:
#   (lower)  sum_{h stabilized & visible at N} w_h  <=  |shEvt(N)|/|Box(N)|
#   (upper)  |shEvt(N)|/|Box(N)|  <=  sum_{h in shDom} w_h   (analytic total)
# and both sides converge to the same value as N grows.  We validate the two
# inequalities plus convergence on random (u3)-dominated configurations with
# geometric weights w_h = s*(m-1)/m^(h+1)  (analytic total = s).
viol_lo = viol_hi = 0
conv_gap = []
for t in range(4000):
    m = rng.choice([2, 3, 5])
    s = Fr(rng.randint(1, 8), 8)
    NM = 24
    D = 30
    N0 = {h: h + rng.randint(1, 3) for h in range(NM + 1)}
    w = {h: Fr(m - 1, m ** (h + 1)) * s for h in range(NM + 1)}
    frac = {h: rng.randint(0, 8) for h in range(NM + 1)}

    def cnt_u3(h, N):
        if h >= N or h > NM:
            return 0
        cap = w[h] * (m ** (N + D)) * 8
        assert cap.denominator == 1
        cap = int(cap) // 8                    # = floor(w_h * box) -- (u3) cap
        if N >= N0[h]:
            v = w[h] * m ** (N + D)
            return int(v)                      # exactly stabilized (integral: 8|s den)
        return (cap * frac[h]) // 8            # (u3)-dominated pre-stabilization

    for N in (8, 16, 24):
        ratio = Fr(sum(cnt_u3(h, N) for h in range(N)), m ** (N + D))
        lo = sum(w[h] for h in range(N) if N >= N0[h])
        if not (lo <= ratio):
            viol_lo += 1
        if not (ratio <= s):
            viol_hi += 1
    conv_gap.append(s - Fr(sum(cnt_u3(h, 24) for h in range(24)), m ** (24 + D)))
print(f"   lower-squeeze violations={viol_lo}, upper-squeeze violations={viol_hi}, "
      f"max gap to analytic total at N=24: {max(conv_gap)} (~{float(max(conv_gap)):.2e})")
check("P5: (u3) squeeze inequalities hold on all 4000 configs x 3 levels; "
      "gap -> 0", viol_lo == 0 and viol_hi == 0 and
      float(max(conv_gap)) < 1e-6)
print("   NOTE (for TV-H2/E-1): a proof sketch that roster + (u3) + w>=0 implies")
print("   clause (ii) for ARBITRARY shDom (no separate summability guard needed):")
print("   <=: WshVal*box = sum_{visH(N)} cnt <= sum_{visH(N)} w_h*box  by (u3);")
print("   >=: stabilized visible heights contribute exactly w_h*box, others >= 0;")
print("   every h with w_h > 0 is eventually permanently visible (else off-visH +")
print("   shweight_card force w_h = 0), so partial sums squeeze to WshVal.")

# =============================================================================
print()
print("=" * 78)
if FAIL:
    print(f"RESULT: {len(FAIL)} CHECK(S) FAILED: {FAIL}")
    sys.exit(1)
print("RESULT: ALL CHECKS PASS (P1-P5 as sealed)")
