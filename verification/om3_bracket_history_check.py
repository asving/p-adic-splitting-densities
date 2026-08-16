#!/usr/bin/env python3
"""OM-3 certification leg 4 (HYP.33, the (CS-2) stage bracket): the α-aggregation bracket
against REAL per-history counts at the m = 2 ground stage — the connection no landed artifact
guards (H.21/H.92 guard the bracket ARITHMETIC; this leg guards bracket-vs-polynomials).

Setup: the double-root branch at a fixed center — members f = x² + a₁x + a₀ over O/π^N with
v(a₁) ≥ 1, v(a₀) ≥ 1 (reduction x²), per-center normalization (EFF.GENIND.47).  The CONSERVATIVE
reader: polygon (w₁ = v(a₁), w₀ = v(a₀)) →
  · 2w₁ < min(w₀, N):        two integer-slope linear branches — DECIDED (split);
  · w₀ < N odd (2w₁ ≥ w₀):   DECIDED (ramified);
  · w₀ = 2k < N (w₁ ≥ k):    residual y² + b̄y + c̄ (b̄ = k-digit of a₁ if w₁ = k else 0,
                             c̄ = 2k-digit of a₀):  separable → DECIDED;  double root
                             (y − z)² → CONTINUE: recenter x ↦ π^k(y + z), rescale, recurse at
                             window N − 2k (child coefficients truncated to the child window —
                             the RAGGED truncation, conservative);
  · else (w₀ ≥ N as read, 2w₁ ≥ N):  UNDECIDED (head).

CLAIMS CERTIFIED (exhaustive enumeration, exact arithmetic):
  (C.1) [per-step mass factor]  #{members whose history is EXACTLY the composition (k₁,…,k_r)
        and then head} = Π_i (Q−1)·Q^{k_i}  ×  Q^{⌊(N−2κ)/2⌋}   (κ = Σk_i, head window N−2κ) —
        i.e. each continue-step k carries EXACTLY the mass-normalized factor (Q−1)Q^{c(2)·k}
        (letter × ghost), the (CS-2) bracket's term, against real counts.
  (C.2) [bracket aggregation]  Σ over depth-κ histories = alphaBracket(Q, 1, κ) · Q^{⌊(N−2κ)/2⌋}
        for 2κ + 1 ≤ N (all compositions visible), where alphaBracket is H.18's recursion
        (re-implemented here from its Lean definition and checked against H.20's closed form
        (Q−1)Q^{2κ−1}).
  (C.3) [telescope]  total undecided u(N) = Q^{N−1}  (and at odd p in mixed characteristic this
        equals the SEMANTIC count #{Δ ≡ 0 mod p^N} — decidedness = discriminant visibility).
  (C.4) [q = 3 non-degeneracy]  at Q = 3, κ = 2: the (2)- and (1,1)-composition real masses are
        18·head and 36·head — DIFFERENT (the coincidence-regime trap H.21 documents at q = 2).

Rings: mixed characteristic ℤ/p^N (p = 2, 3; N ≤ 7 resp. 5) and equal characteristic
F_q[t]/(t^N) (q = 2, 3, 4; N ≤ 7/5/4).  Exit 0 iff all green.
"""

import sys
from itertools import product
from collections import Counter

from om3_residual_census_check import FF

# ------------------------------- alphaBracket (H.18, re-implemented) --------------------------


def alpha_bracket(Q, c, mu):
    if mu == 0:
        return 1
    return sum((Q - 1) * Q ** (c * (k + 1)) * alpha_bracket(Q, c, mu - 1 - k)
               for k in range(mu))


# ------------------------------- arithmetic adapters ------------------------------------------


class MixedChar:
    """O = ℤ_p truncations; classes as ints; residue field F_p as ints mod p."""

    def __init__(self, p):
        self.p, self.Q = p, p
        self.name = f"Zp p={p}"

    def digits_range(self, w):  # classes of π·O/π^w·O, i.e. v ≥ 1 coefficients mod p^w
        return [self.p * j for j in range(self.p ** (w - 1))]

    def val(self, a, w):
        """v(a) as read mod p^w; returns w if a ≡ 0."""
        if a % (self.p ** w) == 0:
            return w
        v = 0
        while a % self.p == 0:
            a //= self.p
            v += 1
        return v

    def digit(self, a, i):
        return (a // self.p ** i) % self.p

    def res_dbl_root(self, b, c):
        """residual y² + b̄y + c̄: return z if double root else None (b, c ∈ F_p)."""
        p = self.p
        if p == 2:
            return c % 2 if b % 2 == 0 else None  # z = c̄ (sqrt in F_2)
        if (b * b - 4 * c) % p == 0:
            return (-b * pow(2, -1, p)) % p
        return None

    def child(self, a1, a0, k, z, N):
        """recenter x ↦ p^k(y+z), rescale; return (a1', a0') mod p^{N−2k}."""
        p = self.p
        n1 = a1 + 2 * z * p ** k
        n0 = a0 + a1 * z * p ** k + z * z * p ** (2 * k)
        assert n1 % p ** k == 0 and n0 % p ** (2 * k) == 0
        m = p ** (N - 2 * k)
        return (n1 // p ** k) % m, (n0 // p ** (2 * k)) % m


class EqualChar:
    """O = F_q[[t]] truncations; classes as tuples of FF elements; residue field F_q."""

    def __init__(self, p, kk):
        self.F = FF(p, kk)
        self.Q = self.F.q
        self.name = f"Fq[[t]] q={self.F.q}"

    def digits_range(self, w):
        F = self.F
        return [((F.zero,) + tail) for tail in product(F.elts, repeat=w - 1)]

    def val(self, a, w):
        for i in range(min(len(a), w)):
            if a[i] != self.F.zero:
                return i
        return w

    def digit(self, a, i):
        return a[i] if i < len(a) else self.F.zero

    def res_dbl_root(self, b, c):
        F = self.F
        if F.p == 2:
            if b != F.zero:
                return None
            z = c
            for _ in range(F.k - 1):  # z = c^(q/2) = c^(2^(k−1))
                z = F.mul(z, z)
            return z
        # odd char: disc = b² − 4c
        four_c = F.mul(F.add(F.add(F.one, F.one), F.add(F.one, F.one)), c)
        disc = F.add(F.mul(b, b), F.neg(four_c))
        if disc != F.zero:
            return None
        # z = −b/2
        two = F.add(F.one, F.one)
        twoinv = next(e for e in F.elts if F.mul(two, e) == F.one)
        return F.neg(F.mul(b, twoinv))

    def _addp(self, a, b, w):
        F = self.F
        return tuple(F.add(self.digit(a, i), self.digit(b, i)) for i in range(w))

    def _shiftmul(self, z, k, w):
        """z·t^k as a length-w tuple."""
        F = self.F
        return tuple(z if i == k else F.zero for i in range(w))

    def child(self, a1, a0, k, z, N):
        F = self.F
        w = N
        two_z = F.add(z, z)
        n1 = self._addp(a1, self._shiftmul(two_z, k, w), w)
        a1z = tuple(F.mul(self.digit(a1, i - k), z) if i >= k else F.zero for i in range(w))
        z2 = self._shiftmul(F.mul(z, z), 2 * k, w)
        n0 = self._addp(self._addp(a0, a1z, w), z2, w)
        m = N - 2 * k
        c1 = tuple(self.digit(n1, i + k) for i in range(m))
        c0 = tuple(self.digit(n0, i + 2 * k) for i in range(m))
        assert all(self.digit(n1, i) == F.zero for i in range(k))
        assert all(self.digit(n0, i) == F.zero for i in range(2 * k))
        return c1, c0


# ------------------------------- the conservative reader --------------------------------------


def read(A, a1, a0, N, hist):
    """returns ('dec', reason) or ('und', tuple(hist))."""
    w1 = A.val(a1, N)
    w0 = A.val(a0, N)
    if 2 * w1 < min(w0, N):
        return ('dec', 'split')
    if w0 < N and w0 % 2 == 1:
        return ('dec', 'ram')
    if w0 < N and w0 % 2 == 0:
        k = w0 // 2
        b = A.digit(a1, k) if w1 == k else (0 if isinstance(A, MixedChar) else A.F.zero)
        c = A.digit(a0, 2 * k)
        z = A.res_dbl_root(b, c)
        if z is None:
            return ('dec', 'res-sep')
        c1, c0 = A.child(a1, a0, k, z, N)
        return read(A, c1, c0, N - 2 * k, hist + (k,))
    return ('und', tuple(hist))


def check_ring(A, Nmax):
    ok = True
    Q = A.Q
    for N in range(1, Nmax + 1):
        tally = Counter()
        und = 0
        for a1 in A.digits_range(N):
            for a0 in A.digits_range(N):
                st, info = read(A, a1, a0, N, ())
                if st == 'und':
                    und += 1
                    tally[info] += 1
        # (C.3) telescope
        c3 = und == Q ** (N - 1)
        ok &= c3
        # (C.1) per-composition
        bad = []
        for comp, cnt in sorted(tally.items()):
            kap = sum(comp)
            headw = N - 2 * kap
            want = Q ** (headw // 2)
            for k in comp:
                want *= (Q - 1) * Q ** k
            if want != cnt:
                bad.append((comp, cnt, want))
        ok &= not bad
        # (C.2) per-κ aggregate = alphaBracket·head, on fully visible κ (2κ+1 ≤ N)
        aggbad = []
        for kap in range(1, (N - 1) // 2 + 1):
            agg = sum(cnt for comp, cnt in tally.items() if sum(comp) == kap)
            want = alpha_bracket(Q, 1, kap) * Q ** ((N - 2 * kap) // 2)
            closed = (Q - 1) * Q ** (2 * kap - 1) * Q ** ((N - 2 * kap) // 2)
            if agg != want or want != closed:
                aggbad.append((kap, agg, want, closed))
        ok &= not aggbad
        print(f"  [{'OK ' if c3 and not bad and not aggbad else 'FAIL'}] {A.name} N={N}: "
              f"und={und} (=Q^{N - 1}:{c3}) comps={dict(tally)}"
              + (f" C1BAD={bad}" if bad else "") + (f" C2BAD={aggbad}" if aggbad else ""))
        # (C.3 semantic) at odd p mixed char: undecided == #{Δ ≡ 0 mod p^N}
        if isinstance(A, MixedChar) and A.p % 2 == 1:
            sem = 0
            for a1 in A.digits_range(N):
                for a0 in A.digits_range(N):
                    if (a1 * a1 - 4 * a0) % (A.p ** N) == 0:
                        sem += 1
            s_ok = sem == und
            ok &= s_ok
            print(f"    [C.3-sem {'OK' if s_ok else 'FAIL'}] semantic Δ≡0 count = {sem}")
    return ok


def main():
    okall = True
    okall &= check_ring(MixedChar(2), 7)
    okall &= check_ring(MixedChar(3), 5)
    okall &= check_ring(EqualChar(2, 1), 7)
    okall &= check_ring(EqualChar(3, 1), 5)
    okall &= check_ring(EqualChar(2, 2), 4)  # F_4: prime-power residue field
    # (C.4) the q = 3 non-degeneracy cell, read off the mixed-char N = 5 tallies:
    A = MixedChar(3)
    N = 5
    tally = Counter()
    for a1 in A.digits_range(N):
        for a0 in A.digits_range(N):
            st, info = read(A, a1, a0, N, ())
            if st == 'und':
                tally[info] += 1
    t2, t11 = tally.get((2,), 0), tally.get((1, 1), 0)
    c4 = (t2, t11) == (2 * 9 * 1, (2 * 3) * (2 * 3) * 1) and t2 != t11
    okall &= c4
    print(f"[C.4 {'OK ' if c4 else 'FAIL'}] Q=3 N=5: mass((2))={t2}, mass((1,1))={t11} — distinct")
    print("\nRESULT:", "ALL CHECKS PASS" if okall else "FAILURES PRESENT")
    sys.exit(0 if okall else 1)


if __name__ == "__main__":
    main()
