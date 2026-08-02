#!/usr/bin/env python3
"""HK-53 — the ν_{i+1}.e ≥ 2 RULING numerics trace (2026-08-08 wallclock 2026-08-02).

The mandated trace-the-numerics pass BEFORE the ruling artifact (charter: hardest-first
item 2).  Five asserted findings F1–F5, mirroring lean/LeanUrat/HC2/HK53_e2Ruling.lean:

F1  PARITY/STRIDE FENCE at the HK23 gate child (pair (2,5) over σ₁.w = 2·bw on C_fq):
    HK23's recorded ν₁ram side (width 2, digits at slots {0,2}) admits NO f — the tie
    4·bw(B₀) = 4·bw(B₂) + 10 is a mod-4 contradiction.  Lawful (2,5) sides have width
    e′² = 4 with the middle stride digit forced 0 (Lean: digit_stride_dvd/width_sq_dvd).
F2  FRAME ASCENT: on a G-tied (2,5) side the σ₁-frame values σ₁.w(B_j) + j·h′ strictly
    ascend (excess e′(e′−1)h′ per stride pair), so the frame min over on-side slots is
    the leftmost alone; at s0 = 0 nothing can tie from below — SideReads clause (iii)
    (the anchored ≥ 2-digit pattern) is UNSATISFIABLE (Lean: sideReads_belowWindow_tie,
    sideReads_unsat_e2_s0_zero, readsOf_e2_s0_zero_empty).
F3  ANCHOR-SPACING OBSTRUCTION: on a width-4 tie the two (S5) monomial positions of
    σ₁.R f are spaced 2sˢ+1 (odd, for EVERY stage Bézout pair (sˢ,tˢ) with
    2sˢ+5tˢ = 1), while HasAnchorK demands spacing +2 — the on-side route to clause
    (iii) is dead independently of F2.
F4  THE KILL SHAPE (why FALSE-SUSPECT was the wrong frame): at the traced non-adjacent
    μ₀ = 5 instance the DISPLAYED V9 form fails at the node-data level
    (σ₁.w(B μ₀) = 2·bw ∈ 2ℤ vs RHS = u*₀ = 1 odd) — but the SAME instance has no
    lawful read-1 side (its G-min sits at a single odd slot), i.e. the FALSE-witness
    and the ReadsOf pack cannot coexist: VACUITY-SUSPECT, not FALSE-suspect.
F5  THE CORRECTED SCALE (the re-key design): σ₁.w(B μ₀) = e′·σV.w(B μ₀)
    = strFrame(i+2)·lineᵢ.at(μ₀·cwᵢ) checks exactly on the trace (Lean:
    readVertex_stretch / readBox_stretch / displayed_iff_lineZero).

Run: uv run --with sympy python3 hk53_e2_ruling_trace.py   (exit 0 = all asserted)
"""
from sympy import Poly, symbols, ZZ, div, GF

X = symbols('X')


def ord2(n):
    if n == 0:
        return None
    n = abs(int(n))
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def bw(poly):  # the (1,1)-Gauss weight bw(Σ aᵢXⁱ) = minᵢ (ord₂ aᵢ + i)
    if poly.is_zero:
        return None
    return min(ord2(c) + int(m[0]) for m, c in poly.as_dict().items())


# ── F1: the HK23 ν₁ram width-2 side is mod-4 impossible; lawful width = 4 ────────────
# tie demand at stride 2 over σ₁.w = 2·bw:  4·w₀ = 4·w₂ + 2·5  →  0 ≡ 2 (mod 4)
assert all((4 * w0 - (4 * w2 + 10)) % 4 == 2 for w0 in range(20) for w2 in range(20)), "F1"
# width-4 tie IS solvable: 4·w₀ = 4·w₄ + 4·5 → w₀ = w₄ + 5
assert 4 * 5 == 4 * 0 + 20, "F1b"
print("F1  OK: (2,5) stride-2 tie impossible mod 4; width-4 tie solvable (w0 = w4 + 5)")

# ── F3: anchor spacing 2s+1 odd for every Bézout pair of (2,5) ───────────────────────
for s, t in [(-2, 1), (3, -1), (8, -3), (-7, 3)]:
    assert 2 * s + 5 * t == 1
    spacing = 5 * t + 4 * s  # pos(slot4) − pos(slot0) on a width-4 tie (bw drop 5)
    assert spacing == 2 * s + 1 and spacing % 2 == 1, "F3"
print("F3  OK: (S5)-position spacing 2s+1 odd for every (s,t); HasAnchorK demands +2")

# ── the traced non-adjacent e′ = 2 instance (root pattern ψ₂⁵, μ₀ = 5, u*₀ = 1) ──────
psi2 = Poly(X**2 + X + 1, X, domain=GF(2))
patt = [int(c) for c in (psi2**5).all_coeffs()[::-1]]  # ψ₂⁵ digits, slots 0..10
assert patt == [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1]
fexpr = X**12
for k, c in enumerate(patt):
    if c:
        fexpr += 2 ** (11 - k) * X**k
f = Poly(fexpr, X, domain=ZZ)
fq = Poly(X**2 + 2 * X + 4, X, domain=ZZ)  # the gate child key (U31.fq)

# read-0 side data: gam₀ = 11 on the pattern slots, everything else ≥ 12
for m, c in f.as_dict().items():
    j = int(m[0])
    w = ord2(c) + j
    if j <= 10 and patt[j]:
        assert w == 11, "read-0 side"
    else:
        assert w >= 12, "read-0 off-side"
# geometry: slope₀ = 1, intercept₀ = 7 (hLineU at u*₀ = 1), cw₀ = 2, μ₀ = 5, strF(1) = 1
mu0, RHS = 5, 7 - 1 * (5 * 2) / 2 * 2  # line₀.at(μ₀·cw₀)... computed explicitly below
line0_at = lambda b: 7 - 1 * b  # slope law: slope·(e₀·STR₀·D₀·...) — D₀ = 1: slope = 1
# NOTE the base-index scale: cw₀ = e₀g₀D₀ = 1·2·1 = 2, so μ₀·cw₀ = 10... but line₀ is
# per-BASE-index with D₀ = 1: hLineU pins line₀.at((s0+wSide)·D₀) = line₀.at(10) = u*₀:
# intercept = 11 (γ-tie: gam₀ = u*₀ + 10·1 = 11 ✓); vertex value line₀.at(μ₀·cw₀ = 10) = 1.
line0_at = lambda b: 11 - 1 * b
assert line0_at(10) == 1 == 11 - mu0 * (1 * 1 * 2), "lineAt_arith: gam − μ·e·h·g"

# fq-development of f
rem, B = f, []
while not rem.is_zero:
    q, r = div(rem, fq, domain=ZZ)
    B.append(r)
    rem = q
assert len(B) == 7
G = {j: 4 * bw(b) + 5 * j for j, b in enumerate(B) if not b.is_zero}       # read functional
FR = {j: 2 * bw(b) + 5 * j for j, b in enumerate(B) if not b.is_zero}      # σ₁-frame values

# ── F2: frame min at the single lowest slot; G-min single slot too ───────────────────
fmin = min(FR.values())
assert [j for j in FR if FR[j] == fmin] == [0], "F2 frame-min unique at slot 0"
print("F2  OK: σ₁-frame min unique (slot 0); no below-window slot exists at s0 = 0")

# ── F4: displayed-form kill + no lawful side coexist ─────────────────────────────────
lhs = 2 * bw(B[mu0])                    # σ₁.w(B μ₀) — always EVEN
assert not B[mu0].is_zero and lhs == 2 and lhs != line0_at(10), "F4 displayed FALSE at node level"
gam1 = min(G.values())
gmins = [j for j in G if G[j] == gam1]
assert gmins == [5] and gam1 % 2 == 1, "F4 G-min at a single odd slot — no lawful (2,5) side"
print(f"F4  OK: displayed σ₁.w(B 5) = {lhs} ≠ {line0_at(10)} = RHS; but G-min {gam1} at {gmins} — no lawful ν₁, no ReadsOf")

# ── F5: the corrected strFrame(i+2) scale checks ─────────────────────────────────────
sigmaV_w = bw(B[mu0])                   # σV.w = bw (identity regrade at the (1,1) root)
assert sigmaV_w == line0_at(10) == 1, "F5 σV-vertex law value"
assert 2 * sigmaV_w == 2 * line0_at(10) == lhs, "F5 corrected form: strF(i+2)·line₀.at = e′·σV.w"
# and the iff-zero reduction: displayed ⟺ (e′−1)·RHS = 0 ⟺ RHS = 0 — here RHS = 1 ≠ 0
assert (lhs == line0_at(10)) == (line0_at(10) == 0), "F5 displayed_iff_lineZero"
print("F5  OK: σ₁.w(B μ₀) = 2·σV.w(B μ₀) = strF(i+2)·line₀.at(μ₀·cw₀); displayed ⟺ line value 0")

print("\nALL FIVE FINDINGS GREEN — the ruling record stands "
      "(Lean: LeanUrat/HC2/HK53_e2Ruling.lean, 8 theorems, Lean-core).")
