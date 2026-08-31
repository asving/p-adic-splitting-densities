#!/usr/bin/env python3
"""UNIT IGV battery: exact depth-stratum box counts vs the derived master law.

Claim under test (derived 2026-08-31, unit IGV):
  For random monic f (deg n1), g (deg n2) over a DVR O with residue card q,
  the exact-depth densities P[v(Res(f,g)) = v] have generating function
      Z_m(t) = prod_{j=1..m} (1 - s^j t^(j-1)) / (1 - s^j t^j),   s = 1/q,
  depending only on m = min(n1, n2).  Box form: for v < L,
      #depthPairSet(n1,n2,L,v) = [t^v] Z_m * q^((n1+n2) L)   (exact integer).

The battery counts the boxes exhaustively over Z/p^L and compares EXACTLY.
"""
import sys, itertools
from fractions import Fraction

def sylvester_det(fc, gc, m, n, ppow):
    """Pinned-size Sylvester determinant. fc: coeffs f0..fm (len m+1), gc: g0..gn.
    Integer Bareiss, reduced mod nothing (exact)."""
    N = m + n
    M = [[0]*N for _ in range(N)]
    frow = list(reversed(fc))  # fm ... f0
    grow = list(reversed(gc))  # gn ... g0
    for i in range(n):
        for j, c in enumerate(frow):
            M[i][i+j] = c
    for i in range(m):
        for j, c in enumerate(grow):
            M[n+i][i+j] = c
    # Bareiss
    sign = 1
    prev = 1
    for k in range(N-1):
        if M[k][k] == 0:
            for r in range(k+1, N):
                if M[r][k] != 0:
                    M[k], M[r] = M[r], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k+1, N):
            Mik = M[i][k]; Mkk = M[k][k]
            rowi = M[i]; rowk = M[k]
            for j in range(k+1, N):
                rowi[j] = (rowi[j]*Mkk - Mik*rowk[j]) // prev
            rowi[k] = 0
        prev = M[k][k]
    return sign * M[N-1][N-1]

def valuation(x, p, cap):
    if x == 0:
        return cap
    v = 0
    while x % p == 0 and v < cap:
        x //= p
        v += 1
    return v

def predicted_Pv(m, p, vmax):
    """Coefficients of Z_m(t) up to t^vmax, exact Fractions, s = 1/p."""
    s = Fraction(1, p)
    # series in t as list of Fractions, index 0..vmax
    ser = [Fraction(1)] + [Fraction(0)]*vmax
    for j in range(1, m+1):
        # multiply by (1 - s^j t^(j-1))
        num = [Fraction(0)]*(vmax+1)
        for i in range(vmax+1):
            num[i] += ser[i]
            if i + (j-1) <= vmax:
                num[i + (j-1)] -= ser[i] * s**j
        # multiply by 1/(1 - s^j t^j) = sum_k s^(jk) t^(jk)
        den = [Fraction(0)]*(vmax+1)
        for i in range(vmax+1):
            k = 0
            while i + j*k <= vmax:
                den[i + j*k] += num[i] * s**(j*k)
                k += 1
        ser = den
    return ser

def run_case(n1, n2, p, L):
    q = p
    m = min(n1, n2)
    box = p**L
    total = 0
    counts = [0]*(L+1)  # exact v for v < L; index L = "GE L"
    coords1 = [range(box)]*n1
    coords2 = [range(box)]*n2
    cap = L
    for a in itertools.product(*coords1):
        fc = list(a) + [1]
        for b in itertools.product(*coords2):
            gc = list(b) + [1]
            r = sylvester_det(fc, gc, n1, n2, box)
            counts[valuation(r, p, cap)] += 1
            total += 1
    pred = predicted_Pv(m, p, L)
    print(f"CASE (n1,n2)=({n1},{n2}) p={p} L={L}  total={total}", flush=True)
    allpass = True
    for v in range(L):
        want = pred[v] * total
        got = counts[v]
        ok = (want.denominator == 1 and want.numerator == got)
        allpass &= ok
        print(f"  v={v}: count={got}  predicted={want}  {'PASS' if ok else 'FAIL'}", flush=True)
    geL = total - sum(counts[v] for v in range(L))
    geL_pred = (1 - sum(pred[:L])) * total
    ok = (geL_pred.denominator == 1 and geL_pred.numerator == geL)
    allpass &= ok
    print(f"  GE{L}: count={geL}  predicted={geL_pred}  {'PASS' if ok else 'FAIL'}", flush=True)
    print(f"  => {'ALL PASS' if allpass else '*** MISMATCH ***'}", flush=True)
    return allpass

if __name__ == "__main__":
    cases = eval(sys.argv[1]) if len(sys.argv) > 1 else [
        (1,1,3,3), (1,2,2,3), (1,2,3,2), (1,3,2,2),
        (2,2,2,4), (2,2,3,2), (2,3,3,2), (2,4,2,2),
        (3,3,2,3), (3,3,3,2), (3,4,2,2), (4,4,2,2),
    ]
    ok = True
    for c in cases:
        ok &= run_case(*c)
    print("BATTERY:", "ALL PASS" if ok else "*** FAILURES PRESENT ***")
