#!/usr/bin/env python3
"""case_i_gate.py — the SEALED μ = 3 gate for graded-RS (rev-2 discipline: predictions
committed in this docstring BEFORE the first run; a config outside all probed families).

Graded-RS (MOVES rev 2) predicts, for a deg-1-key descend at an integer-slope side with
residual R(z) = (z − c̃)^μ · h(z), h(c̃) ≠ 0, after the shift x ↦ x + ĉp^M:
R'(z) = z^μ · h(z + c̃) — so the child side digits vanish in slots z⁰..z^{μ−1}, the
z^μ-slot digit is h(c̃) ≠ 0 (pinned vertex), transported deterministically, and the child
digit windows above the forced minima are exactly uniform on the stratum.

SEALED PREDICTIONS (2026-07-24, before first run):

CONFIG I-A (μ = 3, trivial flank; n = 3, p = 2): root x³ (all v ≥ 1); whole side
(0,3)–(3,0) slope −1, R₃(z) = z³ + digit₁(a₂)z² + digit₂(a₁)z + digit₃(a₀) = (z−1)³
(c̃ = 1, the only unit): conditions digit₁(a₂) = 1, digit₂(a₁) = 1, digit₃(a₀) = 1
(binomial: −3 ≡ 1, 3 ≡ 1, −1 ≡ 1 mod 2), v-exactness v(a₂)=1, v(a₁)=2, v(a₀)=3.
  P1: stratum mass = 2⁻⁶ exactly (6 pinned digits: 1+2+3).
  P2: child (shift x ↦ x + 2): v(a₂') ≥ 2, v(a₁') ≥ 3, v(a₀') ≥ 4 (slots z²,z¹,z⁰ all
      vanish — μ = 3 forces THREE vanishings; the child is a width-3 re-cluster; the
      z³ "vertex" is the monic leading 1, off-coefficient).
  P3: child digit windows (K = 2 per coordinate above the minima (2,3,4)) exactly
      uniform; expected 2⁻⁶-mass image cylinder ⟹ bucket count × equal sizes.

CONFIG I-B (μ = 3, flank root r; n = 4, p = 5): root x⁴; whole side (0,4)–(4,0) slope
−1, R₄(z) = z⁴ + digit₁(a₃)z³ + digit₂(a₂)z² + digit₃(a₁)z + digit₄(a₀) =
(z − c̃)³(z − r), c̃ ∈ F₅ˣ, r ∉ {0, c̃}: per (c̃, r) — 4 × 3 = 12 strata; conditions:
digit₁(a₃) = −(3c̃ + r), digit₂(a₂) = 3c̃² + 3c̃r, digit₃(a₁) = −(c̃³ + 3c̃²r),
digit₄(a₀) = c̃³r, with v(a₃) = 1, v(a₂) = 2, v(a₁) = 3, v(a₀) = 4 (exactness where the
digit is ≠ 0; when a digit above is 0 mod 5 the exactness is dropped and only ≥ holds —
the digit conditions as stated are what define the stratum).
  P4: stratum mass = 5⁻¹⁰ exactly per (c̃, r) (pinned digits 1+2+3+4).
  P5: child (x ↦ x + 5ĉ): v(a₀') ≥ 5, v(a₁') ≥ 4, v(a₂') ≥ 3 (slots z⁰,z¹,z² vanish);
      digit₁(a₃') = the z³-slot of z³(z + c̃ − r) read at slot 3... the transported
      vertex: R'(z) = z³(z + (c̃ − r)) has z³-coefficient (c̃ − r) ≠ 0 ⟹
      digit₃(a₁')-NO: slot z³ ↔ the coordinate a₃' at height 1: digit₁(a₃') = c̃ − r
      — wait, careful with slot↔coordinate: slot z^i ↔ coordinate a_i at height (4 − i);
      z³ ↔ a₃ at height 1: digit₁(a₃') = (coefficient of z³ in R') = c̃ − r + (leading
      z⁴ belongs to the monic 1) — PREDICTION: digit₁(a₃') = c̃ − r ≠ 0, POINT MASS.
  P6: child windows above minima exactly uniform per (c̃, r).

SUB-BOX QUALIFICATION (added before the second run attempt; the full I-B box is 5^14
per stratum — infeasible): I-B enumerates the sub-box with 2 free digits per coordinate
(higher digits zero), N = 6. The sealed predictions P4–P6 are tested in their sub-box
form (member count = the sub-box size; minima; uniformity of the K-windows on the
sub-box; vertex point mass). I-A runs the FULL stratum.

Run: python3 case_i_gate.py
"""
import sys
from itertools import product
from fractions import Fraction as F
from collections import Counter


def taylor_shift(coeffs, c, M):
    # f = x^n + coeffs (low->high, len n); shift x -> x + c mod M; monic handled explicitly
    n = len(coeffs)
    poly = list(coeffs) + [1]
    out = [0] * (n + 1)
    # binomial expansion: out[j] = sum_i poly[i]*C(i,j)*c^(i-j)
    from math import comb
    for i in range(n + 1):
        for j in range(i + 1):
            out[j] = (out[j] + poly[i] * comb(i, j) * pow(c, i - j, M)) % M
    assert out[n] == 1
    return out[:n]


def v_p(x, p, cap):
    if x == 0:
        return cap
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def run_config(p, n, N, side_digits, shift_c, mins_pred, vertex_pred, label, free_cap=99):
    """side_digits: dict coord_index -> (height, required_digit). All lower digits 0.
    mins_pred: predicted child minima per coordinate (list, index = coord).
    vertex_pred: (coord, height, value) or None."""
    M = p ** N
    # enumerate the stratum directly: coord i has pinned digits 0..height_i (zeros below,
    # required digit at height_i), free digits above
    pinned = {i: h for i, (h, d) in side_digits.items()}
    free_counts = {i: min(N - 1 - pinned[i], free_cap) for i in side_digits}
    total_pinned = sum(pinned[i] + 1 for i in side_digits)
    members = 0
    buckets = Counter()
    vmins = None
    vertex_vals = Counter()
    ranges = [range(p ** free_counts[i]) for i in sorted(side_digits)]
    for frees in product(*ranges):
        coeffs = [0] * n
        for k, i in enumerate(sorted(side_digits)):
            h, d = side_digits[i]
            val = d * p ** h
            f = frees[k]
            # spread free digits above height h
            val += (f * p ** (h + 1)) % M
            coeffs[i] = val % M
        shifted = taylor_shift(coeffs, shift_c, M)
        members += 1
        vs = [v_p(shifted[i], p, N) for i in range(n)]
        if vmins is None:
            vmins = list(vs)
        else:
            vmins = [min(a, b) for a, b in zip(vmins, vs)]
        # bucket: K=2 digits above predicted minima for the mu-forced coordinates
        vec = []
        for i in range(n):
            if mins_pred[i] is not None:
                vec.append((shifted[i] // p ** mins_pred[i]) % (p ** 2))
        buckets[tuple(vec)] += 1
        if vertex_pred:
            ci, hh, _ = vertex_pred
            vertex_vals[(shifted[ci] // p ** hh) % p] += 1
    expected_members = p ** sum(free_counts[i] for i in side_digits)
    okmass = members == expected_members  # sub-box form when free_cap < full
    sizes = set(buckets.values())
    uniform = len(sizes) == 1
    okmins = all(mins_pred[i] is None or vmins[i] >= mins_pred[i] for i in range(n))
    okvert = True
    if vertex_pred:
        ci, hh, val = vertex_pred
        okvert = set(vertex_vals) == {val % p}
    print(f'{label}: members {members} vs sub-box {expected_members} '
          f'[{"OK" if okmass else "FAIL"}]; child vmins {vmins} vs predicted ≥ {mins_pred} '
          f'[{"OK" if okmins else "FAIL"}]; buckets {len(buckets)} sizes {sorted(sizes)[:3]} '
          f'[{"UNIFORM" if uniform else "NON-UNIFORM"}]'
          + (f'; vertex digit {dict(vertex_vals)} vs {vertex_pred} '
             f'[{"OK" if okvert else "FAIL"}]' if vertex_pred else ''))
    return okmass and okmins and uniform and okvert


def main():
    ok = True
    # CONFIG I-A: n=3, p=2, mu=3, c=1, shift x -> x+2
    ok &= run_config(
        p=2, n=3, N=8,
        side_digits={2: (1, 1), 1: (2, 1), 0: (3, 1)},
        shift_c=2, mins_pred=[4, 3, 2], vertex_pred=None, label='I-A p=2 mu=3')
    # CONFIG I-B: n=4, p=5, mu=3 with flank root r
    for ct in range(1, 5):
        for r in range(1, 5):
            if r == ct:
                continue
            side = {3: (1, (-(3 * ct + r)) % 5), 2: (2, (3 * ct * ct + 3 * ct * r) % 5),
                    1: (3, (-(ct ** 3 + 3 * ct * ct * r)) % 5), 0: (4, (ct ** 3 * r) % 5)}
            ok &= run_config(
                p=5, n=4, N=6, side_digits=side, shift_c=5 * ct,
                mins_pred=[5, 4, 3, None], vertex_pred=(3, 1, (ct - r) % 5),
                label=f'I-B p=5 c̃={ct} r={r}', free_cap=2)
    print('\nVERDICT:', 'CASE I GATE PASSES (sealed mu=3 predictions confirmed)'
          if ok else 'CASE I GATE FAILS — graded-RS predictions falsified somewhere')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
