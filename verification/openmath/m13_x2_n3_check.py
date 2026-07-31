#!/usr/bin/env python3
"""M13-x2-progress numeric check, n=3 leg: per-read wf <= n*h (positive-h reads),
   ladder along chains, and thr + cap <= 2 + 2*n*max(1, maxH) per leaf branch."""
import sys, time
sys.path.insert(0, '/data/users/asvin/math-and-lean/p-adic-splitting-densities/verification')
import ke11_affine_envelope_probe as KP

for p in (2, 3):
    t0 = time.time()
    data = KP.census_branches(p)
    n = 3
    viol_price = 0; viol_ladder = 0; viol_wf = 0; viol_depth = 0
    worst = 0.0; worst_dat = None
    for (pk, rowkey), (d, sumh, thr, cap) in data['leaf'].items():
        chain_h = [hn for (mu, ell, hn, r) in pk]
        pos = [h for h in chain_h if h >= 1]
        if any(b <= a for a, b in zip(pos, pos[1:])):
            viol_ladder += 1
        (e, ell, a, flk, frk, f, s0, hn_row, u1) = rowkey
        wf_row = u1 + s0 * hn_row
        if hn_row >= 1 and wf_row > n * hn_row:
            viol_wf += 1
        maxh = max(pos + ([hn_row] if hn_row >= 1 else []) + [0])
        if d > maxh + 1:
            viol_depth += 1
        lhs = thr + cap; rhs = 2 + 2 * n * max(1, maxh)
        if lhs > rhs:
            viol_price += 1
            if viol_price <= 3: print("  PRICE VIOL:", pk, rowkey, (d, sumh, thr, cap), maxh)
        r = lhs / (1 + maxh)
        if r > worst: worst, worst_dat = r, (pk, rowkey[:5], d, maxh, thr, cap)
    # chain moves: wf_cont <= n*hn is implicit in thr via maxwf; check move ledger deltas
    viol_move = sum(c for (h, delta), c in data['moves'].items() if h >= 1 and delta > n * h)
    print(f"n=3 p={p} N={data['N']}: leaves={len(data['leaf'])} internal={len(data['internal'])} "
          f"margin={data['margin_events']} viol_price={viol_price} viol_ladder={viol_ladder} "
          f"viol_wf={viol_wf} viol_depth={viol_depth} viol_move_delta={viol_move} "
          f"max (thr+cap)/(1+maxH) = {worst:.3f}")
    print(f"   worst: {worst_dat}   [{time.time()-t0:.1f}s]")
