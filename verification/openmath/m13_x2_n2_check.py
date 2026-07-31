#!/usr/bin/env python3
"""M13-x2-progress numeric check, n=2 leg: max-currency pricing
   thr + cap <= 2 + 2*n*maxH  per leaf branch, and the height ladder
   (chain heights strictly increase; d <= maxH + 1)."""
import sys, time
sys.path.insert(0, '/data/users/asvin/math-and-lean/p-adic-splitting-densities/verification')
from ke11_affine_envelope_probe import walk_n2_one

def check(p, N):
    M = p ** N
    viol_price = 0; viol_ladder = 0; viol_depth = 0
    worst = 0.0; worst_dat = None
    n_leaf = 0; censored_ct = 0
    t0 = time.time()
    for a1 in range(M):
        for a0 in range(M):
            dtype, rows, cens, mvs, chain = walk_n2_one(p, N, a1, a0)
            if cens: censored_ct += 1
            # chain: list of (h, digit); heights of chain moves (h=0 = T0 opening)
            hs = [h for h, _ in chain]
            pos = [h for h in hs if h >= 1]
            # ladder: positive chain heights strictly increase
            if any(b <= a for a, b in zip(pos, pos[1:])):
                viol_ladder += 1
            for row in rows:
                if row[0] != 'leaf' or len(row) < 5: continue
                n_leaf += 1
                kind, d, sumh, thr, cap = row
                # leaf height = sumh - (chain sum up to depth d)
                chain_sum = sum(hs[:d])
                hleaf = sumh - chain_sum
                maxh = max(pos[:sum(1 for h in hs[:d])] + [hleaf] or [0]) if True else 0
                maxh = max(pos[:d] + [hleaf]) if (pos[:d] or hleaf) else 0
                # d_total <= maxH + 1 (+1 absorbs the depth-0 T0 opening)
                if d > maxh + 1: viol_depth += 1
                lhs = thr + cap; rhs = 2 + 2 * 2 * maxh
                if lhs > rhs: viol_price += 1
                r = lhs / (1 + maxh)
                if r > worst: worst, worst_dat = r, (a1, a0, d, maxh, thr, cap)
    print(f"p={p} N={N}: leaves={n_leaf} censored_f={censored_ct} "
          f"viol_price={viol_price} viol_ladder={viol_ladder} viol_depth={viol_depth} "
          f"max (thr+cap)/(1+maxH) = {worst:.3f} at {worst_dat}  [{time.time()-t0:.1f}s]")

check(2, 8)
check(3, 5)
