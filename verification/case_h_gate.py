#!/usr/bin/env python3
"""case_h_gate.py — Case H census: deg-1-key descends at sides that do NOT span the
whole window (the D5 "mid-polygon" probe + the D3 "partial-side" probe), n = 3.

Ambient: monic cubics f = x^3 + a2 x^2 + a1 x + a0 over Z_p mod p^N; root read
f-bar = x^3 (all a_i == 0 mod p): width-3 window at key phi = x.  Enumeration is
DIRECT stratum parametrization (imposed digits fixed, free digits explicit), with a
per-member Taylor shift x = y + chat*p, chat in {1..p-1} the integer lift of ct.
Child coefficients (exact Taylor expansion, t = chat*p):
    a2' = a2 + 3t
    a1' = a1 + 2t*a2 + 3t^2
    a0' = a0 + t*a1 + t^2*a2 + t^3

CONFIGURATION 1 — ORIGINAL SPEC, **INVALID-AS-D5-PROBE** (kept for the record; its
  runs stay in the output, so labeled).  Reason (coordinator-confirmed 2026-07-23):
  the spec's named vertices (0,4),(2,2),(3,0) are NOT a lower convex hull — the chord
  (0,4)-(3,0) has value 4/3 < 2 at abscissa 2, so (2,2) lies 2/3 ABOVE it and the true
  polygon of the imposed digit conditions is the single side (0,4)-(3,0) of slope -4/3
  (the script's hull computation prints this per stratum).  Stratum per (ct,u):
    digits 0,1 of a2 = 0,  digit_2(a2) = u                (v(a2) = 2 exact)
    digits 0..2 of a1 = 0, digit_3(a1) = -2*ct*u mod p    (v(a1) >= 3)
    digits 0..3 of a0 = 0, digit_4(a0) = ct^2*u mod p     (v(a0) = 4 exact)
  Side-A residual (per spec) R(y) = u y^2 + d3(a1) y + d4(a0) = u(y-ct)^2 — verified
  per stratum.  Spec's side labels: vertices (0,4),(2,2),(3,0); side A = (0,4)-(2,2)
  slope -1 width 2 (descend side); side B = (2,2)-(3,0) slope -2 width 1 (flank).
  GEOMETRY NOTE (printed as data, not interpretation): the script also computes the
  lower convex hull of the coefficient-wise minimal valuation points of the stratum
  under the standard lower-hull convention, and reports where the imposed points sit
  relative to it.
  GATE H0: per-(ct,u) stratum mass vs nominal p^-12 (12 imposed digits: 3+4+5);
    membership independently re-verified per member (sampled on the heaviest runs).
  GATE H1: joint (v(a2'), v(a1'), v(a0')) distribution on the stratum, valuations
    capped at N-1; reports which components are forced (constant) vs bounded.
  GATE H2 (the D5 question): bucket members by digit windows, K = 2 digits per
    coordinate: a0' anchored at its empirical forced minimum, a1' likewise, a2'
    anchored at height 2 (per spec).  All buckets exactly equal <=> joint ledger
    product-exact on the stratum.  Verdict per (ct,u).
  GATE H3 (flank invariance): count violations of digit_2(a2') = digit_2(a2).

CONFIGURATION 1-CORRECTED (coordinator fix 2026-07-23: the genuine mid-polygon D5
  probe).  Vertices (0,5),(2,1),(3,0): side A = (0,5)-(2,1) slope -2 width 2 (the
  descendable side, d_S = 2); side B = (2,1)-(3,0) slope -1 width 1 (the flank).
  Slopes genuinely distinct; (2,1) is a TRUE vertex: the chord (0,5)-(3,0) has value
  5/3 > 1 at abscissa 2, and the side-A line has value 3 at abscissa 1 (both verified
  and printed by the script's hull code).  Stratum per (ct,u), both in F_p^x:
    digit_0(a2) = 0,       digit_1(a2) = u                 (v(a2) = 1 exact)
    digits 0..2 of a1 = 0, digit_3(a1) = -2*ct*u mod p     (v(a1) >= 3)
    digits 0..4 of a0 = 0, digit_5(a0) = ct^2*u mod p      (v(a0) = 5 exact)
  Side-A residual (digits read at (0,5),(1,3),(2,1) along the slope -2 side):
  R(y) = u y^2 + d3(a1) y + d5(a0) = u(y-ct)^2 — verified per stratum.
  Descend: slope -2 => residual root at valuation 2: Taylor shift x = y + chat*p^2.
  Gates: H0 (mass vs nominal p^-12: 12 imposed digits = 2+4+6); H1 as before;
  H2 windows anchored at each coordinate's EMPIRICAL forced minimum (a2' included,
  anchored at its own minimum, not at a fixed height); H3 = deterministic-transport
  check: the full distribution of digit_1(a2') per stratum with CONSTANT /
  NON-CONSTANT verdict (not a violation count).
  Runs: p=2 N=9; p=3 N=7 (spec N — the a0' K=2 window @[6..7] does NOT fit below N:
  truncated to K=1, and the cap N-1=6 pins v(a0') at 6) and N=8 (beyond-spec, full
  window); p=5 N=7 (a0' window truncated likewise; N=8 would need 16 x 5^12 members —
  unaffordable in pure Python, stated rather than silently absorbed).

CONFIGURATION 2 (spec: the D3 "partial-side" probe).  The full side is the
  degenerate-colinear line (0,3)-(1,2)-(2,1)-(3,0) of slope -1; the descend side is
  the PROPER SUBSEGMENT (0,3)-(2,1) (mu = 2 at ct) with the width-1 tail
  (2,1)-(3,0) touching the window edge.  Full-side residual
      R3(y) = y^3 + d1(a2) y^2 + d2(a1) y + d3(a0)
  is required to factor as (y-ct)^2 (y-r) with r not in {0, ct}.  Stratum per (ct,r):
    digit_0(a2) = 0,       digit_1(a2) = A = -(2ct+r)    mod p
    digits 0,1 of a1 = 0,  digit_2(a1) = B = ct^2+2ct*r  mod p
    digits 0..2 of a0 = 0, digit_3(a0) = C = -ct^2*r     mod p   (C != 0: v(a0)=3 exact)
  (A or B may vanish for special (ct,r) at p = 5 — flagged in the output as data.)
  Gates H0'-H3' identical in form; nominal mass p^-9 (9 imposed digits: 2+3+4).
  H3' reports BOTH the spec-literal height-2 comparison and the height-1 comparison
  (the flank vertex (2,1) sits at a2-height 1).
  r = 0 boundary (R3 = (y-ct)^2 * y, C = 0 so v(a0) >= 4: the polygon vertex moves):
  recorded separately — count/mass + child valuation distribution only.
  p = 2: the (ct,r) index set is EMPTY (F_2 has no r outside {0, ct=1}) — recorded
  honestly; config 2 runs at p = 3 and p = 5 instead (per spec).  p = 5 runs both at
  N = 5 (spec N; the a0' K=2 window does NOT fit below N — truncated to K=1, noted)
  and at N = 6 (full K=2 window; the deviation is only to give H2' its full window).

Run: python3 case_h_gate.py [--skip-heavy]
     (--skip-heavy drops config-2 p=5 N=6, the only slow run: 12 strata x 5^9
      members x 2 passes, a few minutes of pure Python)
"""
import sys
import time
from fractions import Fraction as F
from collections import Counter


# ---------------------------------------------------------------- small helpers
def vp_cap(x, p, cap):
    """p-adic valuation of x (held mod p^N), capped at cap = N-1 per spec (0 -> cap)."""
    if x == 0:
        return cap
    v = 0
    while v < cap and x % p == 0:
        x //= p
        v += 1
    return v


def lower_hull(pts):
    """Vertices of the lower convex hull (standard convention), colinear points removed."""
    pts = sorted(set(pts))
    h = []
    for q in pts:
        while len(h) >= 2:
            (x1, y1), (x2, y2) = h[-2], h[-1]
            if (x2 - x1) * (q[1] - y1) - (y2 - y1) * (q[0] - x1) <= 0:
                h.pop()
            else:
                break
        h.append(q)
    return h


def hull_note(pts):
    """Data string: hull sides of the given valuation points + position of the rest."""
    h = lower_hull(pts)
    segs = ", ".join(
        f"({x1},{y1})-({x2},{y2}) slope {F(y2 - y1, x2 - x1)} width {x2 - x1}"
        for (x1, y1), (x2, y2) in zip(h, h[1:]))
    marg = []
    for (x, y) in sorted(set(pts)):
        if (x, y) in h:
            continue
        for (x1, y1), (x2, y2) in zip(h, h[1:]):
            if x1 <= x <= x2:
                m = F(y) - (F(y1) + F(y2 - y1, x2 - x1) * (x - x1))
                marg.append(f"({x},{y}) " + ("ON hull" if m == 0 else f"+{m} ABOVE hull"))
                break
    return f"hull: {segs}" + ("; non-vertex pts: " + "; ".join(marg) if marg else "")


def child_consts(p, N, t):
    """Constants of the Taylor shift x = y + t (t already includes its p-power),
    all reduced mod p^N."""
    M = p ** N
    return M, (3 * t) % M, (2 * t) % M, (3 * t * t) % M, (t * t) % M, t % M, (t ** 3) % M


def fmt_vdist(vd):
    it = ", ".join(f"({k >> 8},{(k >> 4) & 15},{k & 15}):{vd[k]}" for k in sorted(vd))
    return "{" + it + "}"


def forced_summary(vd, cap):
    s2 = sorted({k >> 8 for k in vd})
    s1 = sorted({(k >> 4) & 15 for k in vd})
    s0 = sorted({k & 15 for k in vd})

    def one(name, s):
        return (f"{name} FORCED = {s[0]}" if len(s) == 1
                else f"{name} bounded: min {s[0]}, values {s}")
    return ("; ".join([one("v(a2')", s2), one("v(a1')", s1), one("v(a0')", s0)])
            + f"  [cap {cap}]")


# ---------------------------------------------------------------- census passes
def pass1(p, N, spec, t, h3_heights, recheck_inner, h3_dist_height=None):
    """Pass 1 over the stratum: H0 count + membership recheck, H1 joint child
    valuation distribution (keys (v2'<<8)|(v1'<<4)|v0', capped N-1), H3 counts
    (digit-invariance violations per height in h3_heights, and/or the full
    distribution of digit_{h3_dist_height}(a2') for the deterministic-transport
    check)."""
    (base2, h2), (base1, h1), (base0, h0) = spec
    M, add2, mul1, add1, mul0a, mul0b, add0 = child_consts(p, N, t)
    cap = N - 1
    n2, n1, n0 = p ** (N - h2), p ** (N - h1), p ** (N - h0)
    P2, P1, P0 = p ** h2, p ** h1, p ** h0
    ph = [p ** h for h in h3_heights]
    hq = p ** h3_dist_height if h3_dist_height is not None else None
    vdist = {}
    h3v = [0] * len(h3_heights)
    h3dist = {}
    rechecked = rfail = 0
    tick = 0
    w10 = n1 * n0
    for k2 in range(n2):
        a2 = base2 + k2 * P2
        a2p = (a2 + add2) % M
        v2 = vp_cap(a2p, p, cap)
        for i, q in enumerate(ph):
            if (a2p // q) % p != (a2 // q) % p:
                h3v[i] += w10
        if hq is not None:
            d = (a2p // hq) % p
            h3dist[d] = h3dist.get(d, 0) + w10
        if a2 % P2 != base2:
            rfail += 1
        key2 = v2 << 8
        lin1 = (mul1 * a2 + add1) % M
        lin0 = (mul0a * a2 + add0) % M
        for k1 in range(n1):
            a1 = base1 + k1 * P1
            a1p = (a1 + lin1) % M
            v1 = vp_cap(a1p, p, cap)
            if a1 % P1 != base1:
                rfail += 1
            key21 = key2 | (v1 << 4)
            T = (mul0b * a1 + lin0) % M
            for k0 in range(n0):
                a0p = (base0 + k0 * P0 + T) % M
                x = a0p
                if x == 0:
                    v0 = cap
                else:
                    v0 = 0
                    while v0 < cap and x % p == 0:
                        x //= p
                        v0 += 1
                k = key21 | v0
                vdist[k] = vdist.get(k, 0) + 1
                tick += 1
                if tick >= recheck_inner:
                    tick = 0
                    rechecked += 1
                    a0 = base0 + k0 * P0
                    if (a0 % P0 != base0
                            or a0p != (a0 + t * a1 + t * t * a2 + t ** 3) % M):
                        rfail += 1
    return sum(vdist.values()), vdist, h3v, h3dist, rechecked, rfail


def pass2(p, N, spec, t, anchor2, vmin1, vmin0, K):
    """Pass 2: H2 buckets by child digit windows — a2' anchored at height anchor2,
    a1'/a0' at their empirical forced minima; K digits per coordinate (truncated
    at N)."""
    (base2, h2), (base1, h1), (base0, h0) = spec
    M, add2, mul1, add1, mul0a, mul0b, add0 = child_consts(p, N, t)
    n2, n1, n0 = p ** (N - h2), p ** (N - h1), p ** (N - h0)
    P2, P1, P0 = p ** h2, p ** h1, p ** h0
    K2w = max(1, min(K, N - anchor2))
    K1w = max(1, min(K, N - vmin1))
    K0w = max(1, min(K, N - vmin0))
    Q2, B2 = p ** anchor2, p ** K2w
    Q1, B1 = p ** vmin1, p ** K1w
    Q0, B0 = p ** vmin0, p ** K0w
    buckets = {}
    for k2 in range(n2):
        a2 = base2 + k2 * P2
        a2p = (a2 + add2) % M
        w2 = (a2p // Q2) % B2
        lin1 = (mul1 * a2 + add1) % M
        lin0 = (mul0a * a2 + add0) % M
        for k1 in range(n1):
            a1 = base1 + k1 * P1
            a1p = (a1 + lin1) % M
            keyA = (w2 * B1 + (a1p // Q1) % B1) * B0
            T = (mul0b * a1 + lin0) % M
            for k0 in range(n0):
                a0p = (base0 + k0 * P0 + T) % M
                k = keyA + (a0p // Q0) % B0
                buckets[k] = buckets.get(k, 0) + 1
    return buckets, (K2w, K1w, K0w)


# ---------------------------------------------------------------- stratum report
def report_stratum(p, N, spec, t, h3_heights, K, do_h2=True, anchor2=2,
                   h3_dist_height=None):
    """t = the full Taylor-shift amount (chat*p for slope -1, chat*p^2 for slope -2).
    anchor2 = fixed a2'-window anchor height, or None = empirical min of v(a2')."""
    nfixed = spec[0][1] + spec[1][1] + spec[2][1]
    expected = p ** (3 * N - nfixed)
    recheck_inner = 1 if expected <= 200_000 else 97
    count, vdist, h3v, h3dist, rechecked, rfail = pass1(
        p, N, spec, t, h3_heights, recheck_inner, h3_dist_height)
    mass = F(count, p ** (3 * N))
    nominal = F(1, p ** nfixed)
    h0ok = (count == expected and mass == nominal and rfail == 0)
    print(f"    H0: count {count} (nominal-predicted {expected}); mass {mass} vs "
          f"nominal p^-{nfixed} = {nominal} [{'EXACT' if h0ok else 'MISMATCH'}]"
          f" (membership rechecked {rechecked}, failures {rfail})")
    cap = N - 1
    print(f"    H1: joint (v(a2'),v(a1'),v(a0')) dist: {fmt_vdist(vdist)}")
    print(f"        forced: {forced_summary(vdist, cap)}")
    res = {"h0ok": h0ok, "count": count, "h3": h3v, "h2uniform": None,
           "vdist": vdist}
    if do_h2:
        vmin1 = min((k >> 4) & 15 for k in vdist)
        vmin0 = min(k & 15 for k in vdist)
        a2anchor = anchor2 if anchor2 is not None else min(k >> 8 for k in vdist)
        buckets, Ks = pass2(p, N, spec, t, a2anchor, vmin1, vmin0, K)
        sizes = Counter(buckets.values())
        uniform = len(sizes) == 1
        trunc = "" if Ks == (K, K, K) else "  ** WINDOW TRUNCATED (N too small) **"
        poss = (p ** Ks[0]) * (p ** Ks[1]) * (p ** Ks[2])
        hist = dict(sorted(sizes.items()))
        if len(sizes) > 20:
            hist = dict(list(sorted(sizes.items()))[:20])
            hist["..."] = f"{len(sizes) - 20} more sizes"
        print(f"    H2: windows a2'@h[{a2anchor}..{a2anchor + Ks[0] - 1}], "
              f"a1'@h[{vmin1}.."
              f"{vmin1 + Ks[1] - 1}], a0'@h[{vmin0}..{vmin0 + Ks[2] - 1}] "
              f"(K={Ks}){trunc}")
        print(f"        buckets present {len(buckets)} of {poss} possible; size "
              f"histogram {{size: #buckets}} = {hist} "
              f"[{'UNIFORM' if uniform else 'NON-UNIFORM'}]")
        res["h2uniform"] = uniform
        res["nbuckets"] = len(buckets)
    for h, v in zip(h3_heights, h3v):
        print(f"    H3 (d{h}): digit_{h}(a2') != digit_{h}(a2) violations: "
              f"{v} / {count}")
    if h3_dist_height is not None:
        const = len(h3dist) == 1
        verdict = (f"CONSTANT = {sorted(h3dist)[0]}" if const else "NON-CONSTANT")
        print(f"    H3 (deterministic transport): digit_{h3_dist_height}(a2') "
              f"distribution {dict(sorted(h3dist.items()))} [{verdict}]")
        res["h3dist"] = h3dist
        res["h3const"] = const
    return res


def finalize(name, summ, h3_heights):
    h0 = all(r["h0ok"] for _, r in summ)
    h2s = [r["h2uniform"] for _, r in summ if r["h2uniform"] is not None]
    h2 = all(h2s) if h2s else None
    tot = sum(r["count"] for _, r in summ)
    h3tot = [sum(r["h3"][i] for _, r in summ) for i in range(len(h3_heights))]
    h3s = ", ".join(f"d{h}: {v}/{tot}" for h, v in zip(h3_heights, h3tot))
    print(f"\n  {name} SUMMARY: H0 all exact: {'YES' if h0 else 'NO'}; "
          f"H2 all uniform: {'YES' if h2 else ('n/a' if h2 is None else 'NO')}; "
          f"H3 violation totals: {h3s}")
    return {"name": name, "h0": h0, "h2": h2, "h3": h3s}


# ---------------------------------------------------------------- configurations
def run_config1(p, N, K=2, tag=""):
    t0 = time.time()
    name = f"CONFIG 1 (ORIGINAL — INVALID-AS-D5-PROBE, kept for record) p={p} N={N}{tag}"
    print(f"\n{'=' * 78}\n{name}")
    print("  spec side labels: A=(0,4)-(2,2) slope -1 width 2 (descend); "
          "B=(2,2)-(3,0) slope -2 width 1 (flank)")
    print("  ** INVALID-AS-D5-PROBE: (0,4),(2,2),(3,0) is not a lower hull — the "
          "chord (0,4)-(3,0) has value 4/3 < 2 at abscissa 2; see per-stratum hull "
          "lines.  Superseded by CONFIG 1-CORRECTED below. **")
    summ = []
    for ct in range(1, p):
        for u in range(1, p):
            B1d = (-2 * ct * u) % p
            C1d = (ct * ct * u) % p
            spec = ((u * p ** 2, 3), (B1d * p ** 3, 4), (C1d * p ** 4, 5))
            res_ok = ((u * ct * ct + B1d * ct + C1d) % p == 0
                      and (2 * u * ct + B1d) % p == 0)
            pts = [(0, 4), (1, 3 if B1d else 4), (2, 2), (3, 0)]
            print(f"\n  (ct,u)=({ct},{u}): imposed d2(a2)={u} d3(a1)={B1d} "
                  f"d4(a0)={C1d} | side-A residual u(y-ct)^2 "
                  f"{'check OK' if res_ok else 'CHECK FAILED'}")
            print(f"    parent min-val points {pts}; computed {hull_note(pts)}")
            summ.append(((ct, u), report_stratum(p, N, spec, ct * p, [2], K)))
    out = finalize(name, summ, [2])
    print(f"  [{time.time() - t0:.1f}s]")
    return out


def run_config1_corrected(p, N, K=2, tag=""):
    """The genuine mid-polygon D5 probe: vertices (0,5),(2,1),(3,0); descend side
    A = (0,5)-(2,1) slope -2 width 2; flank B = (2,1)-(3,0) slope -1 width 1;
    Taylor shift x = y + chat*p^2 (residual root at valuation 2)."""
    t0 = time.time()
    name = f"CONFIG 1-CORRECTED (mid-polygon / D5) p={p} N={N}{tag}"
    print(f"\n{'=' * 78}\n{name}")
    print("  vertices (0,5),(2,1),(3,0): side A=(0,5)-(2,1) slope -2 width 2 "
          "(descend, d_S=2); side B=(2,1)-(3,0) slope -1 width 1 (flank); "
          "shift x = y + chat*p^2")
    chord2 = F(5) + F(0 - 5, 3 - 0) * 2      # chord (0,5)-(3,0) at abscissa 2
    lineA1 = F(5) + F(1 - 5, 2 - 0) * 1      # side-A line (0,5)-(2,1) at abscissa 1
    print(f"  vertex check: chord (0,5)-(3,0) at abscissa 2 = {chord2} "
          f"{'>' if chord2 > 1 else '<='} 1 = v(a2)  [(2,1) "
          f"{'strictly BELOW chord: TRUE VERTEX' if chord2 > 1 else 'NOT below chord'}]"
          f"; side-A line at abscissa 1 = {lineA1} (imposed v(a1) >= 3 consistent)")
    summ = []
    for ct in range(1, p):
        for u in range(1, p):
            B1d = (-2 * ct * u) % p
            C1d = (ct * ct * u) % p
            spec = ((u * p, 2), (B1d * p ** 3, 4), (C1d * p ** 5, 6))
            res_ok = ((u * ct * ct + B1d * ct + C1d) % p == 0
                      and (2 * u * ct + B1d) % p == 0)
            pts = [(0, 5), (1, 3 if B1d else 4), (2, 1), (3, 0)]
            print(f"\n  (ct,u)=({ct},{u}): imposed d1(a2)={u} d3(a1)={B1d} "
                  f"d5(a0)={C1d} | side-A residual u(y-ct)^2 "
                  f"{'check OK' if res_ok else 'CHECK FAILED'}")
            print(f"    parent min-val points {pts}; computed {hull_note(pts)}")
            summ.append(((ct, u),
                         report_stratum(p, N, spec, ct * p * p, [], K,
                                        anchor2=None, h3_dist_height=1)))
    h0 = all(r["h0ok"] for _, r in summ)
    h2 = all(r["h2uniform"] for _, r in summ)
    h3c = all(r["h3const"] for _, r in summ)
    h3u = all(sorted(r["h3dist"]) == [su[1]] for su, r in summ)
    tot = sum(r["count"] for _, r in summ)
    h3msg = (f"digit1(a2') {'CONSTANT per stratum' if h3c else 'NON-CONSTANT somewhere'}"
             f"{' and = parent digit u in every stratum' if h3c and h3u else ''}"
             f" ({tot} members)")
    print(f"\n  {name} SUMMARY: H0 all exact: {'YES' if h0 else 'NO'}; "
          f"H2 all uniform: {'YES' if h2 else 'NO'}; H3 {h3msg}")
    print(f"  [{time.time() - t0:.1f}s]")
    return {"name": name, "h0": h0, "h2": h2, "h3": h3msg}


def run_config2(p, N, K=2, tag=""):
    t0 = time.time()
    name = f"CONFIG 2 (partial-side / D3) p={p} N={N}{tag}"
    print(f"\n{'=' * 78}\n{name}")
    print("  full side (0,3)-(1,2)-(2,1)-(3,0) slope -1 (colinear); descend "
          "subsegment (0,3)-(2,1) mu=2 at ct; width-1 tail (2,1)-(3,0)")
    summs = []
    if p == 2:
        print("\n  (ct,r) INDEX SET EMPTY at p=2: F_2^x = {1}, r must avoid "
              "{0, ct} = {0,1} = all of F_2.  Recorded honestly; config 2 runs at "
              "p=3 and p=5 instead (per spec).")
    else:
        for ct in range(1, p):
            for r in range(1, p):
                if r == ct:
                    continue
                A = (-(2 * ct + r)) % p
                B = (ct * ct + 2 * ct * r) % p
                C = (-ct * ct * r) % p
                ok_ct = (ct ** 3 + A * ct ** 2 + B * ct + C) % p == 0
                ok_dct = (3 * ct ** 2 + 2 * A * ct + B) % p == 0
                ok_r = (r ** 3 + A * r ** 2 + B * r + C) % p == 0
                flags = []
                if A == 0:
                    flags.append("A=0: d1(a2)=0, v(a2)>=2 (point (2,1) moves)")
                if B == 0:
                    flags.append("B=0: d2(a1)=0, v(a1)>=3 (point (1,2) moves)")
                fl = ("  ** " + "; ".join(flags) + " **") if flags else ""
                spec = ((A * p, 2), (B * p ** 2, 3), (C * p ** 3, 4))
                pts = [(0, 3), (1, 2 if B else 3), (2, 1 if A else 2), (3, 0)]
                print(f"\n  (ct,r)=({ct},{r}): R3(y) = y^3 + {A} y^2 + {B} y + {C} "
                      f"= (y-{ct})^2 (y-{r}) over F_{p}; checks R3(ct)="
                      f"{'0 OK' if ok_ct else 'NONZERO FAIL'}, R3'(ct)="
                      f"{'0 OK' if ok_dct else 'NONZERO FAIL'}, R3(r)="
                      f"{'0 OK' if ok_r else 'NONZERO FAIL'}{fl}")
                print(f"    parent min-val points {pts}; computed {hull_note(pts)}")
                summs.append(((ct, r),
                              report_stratum(p, N, spec, ct * p, [1, 2], K)))
    # r = 0 boundary strata, recorded separately (counts + child v-dist only)
    print(f"\n  --- r = 0 BOUNDARY (R3 = (y-ct)^2 * y; C = 0 so v(a0) >= 4: "
          f"vertex moves) — recorded separately ---")
    for ct in range(1, p):
        A = (-2 * ct) % p
        B = (ct * ct) % p
        spec = ((A * p, 2), (B * p ** 2, 3), (0, 4))
        print(f"\n  r=0 boundary, ct={ct}: d1(a2)={A} d2(a1)={B} d3(a0)=0")
        report_stratum(p, N, spec, ct * p, [], K, do_h2=False)
    if summs:
        out = finalize(name, summs, [1, 2])
    else:
        out = {"name": name, "h0": True, "h2": None,
               "h3": "n/a (empty index set at p=2)"}
    print(f"  [{time.time() - t0:.1f}s]")
    return out


def main(argv):
    t0 = time.time()
    skip_heavy = "--skip-heavy" in argv
    outs = []
    # -------- configuration 1: p = 2 (N=8), p = 3 (N=6), p = 5 (N=5 per spec,
    #          N=6 as a beyond-spec robustness rerun — cheap)
    outs.append(run_config1(2, 8))
    outs.append(run_config1(3, 6))
    outs.append(run_config1(5, 5))
    outs.append(run_config1(5, 6, tag="  [beyond-spec robustness rerun]"))
    # -------- configuration 1-CORRECTED (the genuine D5 mid-polygon probe):
    #          p = 2 (N=9), p = 3 (N=7 spec + N=8 full-window), p = 5 (N=7;
    #          N=8 for a full a0' window would be 16 x 5^12 members — unaffordable)
    outs.append(run_config1_corrected(2, 9))
    outs.append(run_config1_corrected(3, 7,
                tag="  [spec N; a0' K=2 window does not fit, cap pins v(a0')]"))
    outs.append(run_config1_corrected(3, 8, tag="  [beyond-spec; full a0' window]"))
    outs.append(run_config1_corrected(5, 7,
                tag="  [a0' K=2 window does not fit; N=8 unaffordable]"))
    # -------- configuration 2: p = 2 empty (recorded), p = 3 (N=6),
    #          p = 5 at N=5 (spec N; a0' window truncated) and N=6 (full window)
    outs.append(run_config2(2, 8))
    outs.append(run_config2(3, 6))
    outs.append(run_config2(5, 5, tag="  [spec N; a0' K=2 window does not fit]"))
    if skip_heavy:
        print("\n[--skip-heavy: config-2 p=5 N=6 (full a0' window) SKIPPED]")
    else:
        outs.append(run_config2(5, 6, tag="  [full a0' K=2 window]"))
    # -------- summary
    print(f"\n{'=' * 78}\nCASE H SUMMARY ({time.time() - t0:.1f}s total)")
    all_h0 = all(o["h0"] for o in outs)
    h2list = [o["h2"] for o in outs if o["h2"] is not None]
    all_h2 = all(h2list)
    for o in outs:
        h2 = "n/a" if o["h2"] is None else ("UNIFORM" if o["h2"] else "NON-UNIFORM")
        print(f"  {o['name']}: H0 {'EXACT' if o['h0'] else 'MISMATCH'}; H2 {h2}; "
              f"H3 {o['h3']}")
    print(f"\nVERDICT: H0 masses {'ALL EXACT' if all_h0 else 'MISMATCH SOMEWHERE'}; "
          f"H2 joint-ledger buckets {'ALL UNIFORM' if all_h2 else 'NON-UNIFORM SOMEWHERE'}"
          f" (H1/H3 are reported data, not pass/fail)")
    return 0 if (all_h0 and all_h2) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
