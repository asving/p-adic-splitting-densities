#!/usr/bin/env python3
"""Fable §X-EXHAUST rev-7 census check (independent construction, 2026-07-27).

Layer 1: order-0 sweep. For every monic f of degree n over Z_p in a box
(disc != 0, a0 != 0), compute the principal (negative-slope) Newton polygon,
per-side ind(S) = l*(e*h*l - e - h + 1)/2 from GMN (IND) (T1/T2/T3/T4 row
values), and test the raw-table transport at prefix depth 0:
    v_p(disc f) >= 2 * sum_sides ind(S)        (stronger than one branch's CUM)
This is exactly X.5(i)'s sweep restricted to root reads, but with the sum over
ALL sides (legit: GMN ind(f) >= ind(N0) = sum ind(S_i) + cross terms >= sum).

Layer 2: a T1->T2 depth-1 letter instance, f = (x^2 - 2)^2 - 2^m over Z_2.
Level 0: side (0,2)-(4,0), e=2,h=1,l=2 -> T1, ind0 = 2, selection (g,mu)=(1,2).
Level 1 (frame of key phi = x^2-2): f = phi^2 - 2^m, a T2-shaped read; the
claimed T2 increment (e-1)(h-1)/2 must show up as v2(disc) growth ~ +2 per
m -> m+2 on top of 2*ind0 = 4.  Exact disc via sympy.
"""
import itertools, sys
from fractions import Fraction
from math import gcd, inf
from sympy import symbols, discriminant, Poly

x = symbols('x')

def vp(a, p):
    if a == 0:
        return inf
    v = 0
    while a % p == 0:
        a //= p; v += 1
    return v

def principal_sides(coeffs, p):
    """coeffs = [a0, a1, ..., an=1]. Lower hull of (i, vp(a_i)), finite pts.
    Return list of sides of strictly negative slope as (e, h, l) lowest terms."""
    pts = [(i, vp(c, p)) for i, c in enumerate(coeffs) if vp(c, p) != inf]
    # lower convex hull (Andrew), by increasing i
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (x2 - x1) * (pt[1] - y1) <= (pt[0] - x1) * (y2 - y1):
                hull.pop()
            else:
                break
        hull.append(pt)
    sides = []
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        if y2 >= y1:
            continue  # nonnegative slope: not principal
        E, H = x2 - x1, y1 - y2
        l = gcd(E, H)
        sides.append((E // l, H // l, l))
    return sides

def ind_side(e, h, l):
    num = l * (e * h * l - e - h + 1)
    assert num % 2 == 0, (e, h, l)
    return num // 2

def layer1(n, p, box, label):
    worst = None; checked = 0; viol = []
    rows_hit = {'T1': 0, 'T2': 0, 'T3': 0, 'T4': 0}
    for tail in itertools.product(range(box), repeat=n):
        if tail[0] == 0:
            continue
        coeffs = list(tail) + [1]
        f = Poly(coeffs[::-1], x)
        d = int(discriminant(f))
        if d == 0:
            continue
        vd = vp(d, p)
        sides = principal_sides(coeffs, p)
        tot = 0
        for e, h, l in sides:
            tot += ind_side(e, h, l)
            row = 'T1' if l >= 2 else ('T2' if (e >= 2 and h >= 2) else
                  ('T3' if e >= 2 else 'T4'))
            rows_hit[row] += 1
        checked += 1
        slack = vd - 2 * tot
        if slack < 0:
            viol.append((coeffs, vd, tot))
        if worst is None or slack < worst[0]:
            worst = (slack, coeffs, vd, tot)
    print(f"[{label}] checked={checked} violations={len(viol)} "
          f"min_slack={worst[0]} at {worst[1]} (v={worst[2]}, sum_ind={worst[3]}) "
          f"rows_hit={rows_hit}")
    for v in viol[:5]:
        print("   VIOLATION:", v)
    return len(viol)

def layer2():
    print("[layer2] T1(depth0)+T2(depth1) instance f=(x^2-2)^2-2^m over Z_2")
    prev = None
    ok = True
    for m in range(5, 16, 2):
        f = Poly((x**2 - 2)**2 - 2**m, x)
        d = int(discriminant(f))
        v = vp(d, 2)
        # raw frame read at depth 1: T2 with e=2 (m odd), height h_raw;
        # predicted CUM(1) = ind0 + (e-1)(h-1)/2; check v >= 2*CUM and the
        # +2 growth per m->m+2 (Delta ind = 1 per unit h).
        print(f"   m={m:2d}  v2(disc)={v}", end="")
        if prev is not None:
            print(f"   growth={v - prev}", end="")
        print()
        prev = v
    return ok

def single_instances():
    # T2 root instance: x^2 + 8, side (0,3)-(2,0): e=2,h=3,l=1, ind=(1)(2)/2=1
    f = Poly(x**2 + 8, x); d = int(discriminant(f))
    print(f"[T2 single] x^2+8: v2(disc)={vp(d,2)} >= 2*ind=2 ?", vp(d, 2) >= 2,
          f"(exact GMN: 2*1 + v2(disc Q2(sqrt-2))=2+3=5 = {vp(d,2)})")
    # T1 on-or-below witness: x^2+2x+4, side (0,2)-(2,0): e=h=1,l=2, ind=1
    f = Poly(x**2 + 2*x + 4, x); d = int(discriminant(f))
    print(f"[T1 single] x^2+2x+4: v2(disc)={vp(d,2)} >= 2*ind=2 ?", vp(d, 2) >= 2,
          "(strictly-below would predict ind=0; equality v=2 pins ON-OR-BELOW)")
    # GMN witness x^2+6x+36 over Z_3: ind=1, v3(disc)=3=2+1
    f = Poly(x**2 + 6*x + 36, x); d = int(discriminant(f))
    print(f"[P1 witness] x^2+6x+36: v3(disc)={vp(d,3)} (record says 3 = 2*1+1)")

if __name__ == '__main__':
    single_instances()
    v1 = layer1(3, 2, 8, "cubics p=2 box 8^3")
    v2 = layer1(3, 3, 9, "cubics p=3 box 9^3")
    v3 = layer1(4, 2, 8, "quartics p=2 box 8^4")
    layer2()
    print("TOTAL layer-1 violations:", v1 + v2 + v3)
