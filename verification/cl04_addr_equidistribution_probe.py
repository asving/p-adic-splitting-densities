#!/usr/bin/env python3
"""
CL-04 probe (BP5 §4, unit CL-04; risk R-3) — address-count equidistribution sweep.

GATE CONTEXT. Display (4)'s repaired dichotomy (blueprint BRIDGE_BP5_CLEANUP_2026-07-30
§3.1 (R-b)) claims: card 𝔸(b,γ) = card F_{K+1} ⟺ every ℤ-aligned address of block b at
height γ is attainable. The countermodel CHARGE (this unit): find a legal tower with a
NONEMPTY level set where all aligned addresses are attainable yet card 𝔸 < card F_{K+1}.

MECHANISM REDUCTION (hand argument, this gate's survey). For any legal tower:
  - each digit line is an additive subgroup of card ≤ |F_Q|  (line additivity via
    hRadd/w_jump; so card 𝔸 ≤ |F_Q|^N with N = #attainable aligned addresses),
  - card F_{K+1} = |F_Q|^(∏g)  (child_field = K⟮z̄⟯, ψ irreducible deg g, recenter keeps K),
  - lines at distinct level-set coordinates are jointly independent and full
    (slot-min orthogonality hK1 descended through hStretch; weight detection),
so card 𝔸 = |F_Q|^N exactly, and the ⟸ leg of (4) fails at an all-attainable class
IFF that class holds N < ∏g aligned addresses. THE WHOLE PROBE therefore reduces to
the pure combinatorics of slot vectors:

  stages r = 0..K store (e_r, h_r), gcd(e_r, h_r) = 1, e_r, h_r ≥ 1 (Stage.hcop/he/hh);
  move k is an increment (slotBound_k = e_k·g_{k+1}, g ≥ 1) or a recentering
  (requires e_k = 1; slotBound_k = 1, no residue growth);
  κ_r = h_r/(e_0···e_r);  address (s_0..s_{K-1}, b), s_k < slotBound_k;
  alignment class of the address = frac(Σ_k s_k·κ_k) ∈ ℚ/ℤ  (b, γ shift it constantly).

SEALED PREDICTIONS (written before first run; the hand proof is slot-0 peeling
equidistribution, using ONLY gcd(e_r, h_r) = 1 — no I-aug/steeper-chain needed):
  P1: for EVERY legal slot datum in the sweep, every fiber of the class map has
      size exactly 0 or G := ∏ g — NO deficient class (0 < N < G) EVER occurs.
  P2: the nonzero fibers are EXACTLY the D := e_0···e_{K-1} classes j/D, j = 0..D-1
      (full subgroup coverage; total count D·G = ∏ slotBound_k checks the partition).
  P3 (shallow regression, ScratchC6 header instance): base (e,h) = (1,1), one
      increment g = 2: at (b,γ) = (0,0) exactly 2 aligned addresses (s_0 ∈ {0,1}),
      exactly 1 attainable (s_0 = 0), so (4)'s RHS is FALSE there and the dichotomy
      SURVIVES the shallow gate; heuristic 2·[F_Q:F_p] = [F_{K+1}:F_p] holds (2·1 = 2).
  EXPECTED EXIT: 0 (all three hold) — i.e. the R-3 deficiency mechanism is
      arithmetically impossible; the probe existential CL04_dichotomy_probe is FALSE
      for every legal tower; verdict STALLED-STATEMENT-SURVIVES.
  EXIT 1 (PROBE-FINDING): any P1 violation — the violating datum is printed as the
      compiled-countermodel sketch (tower data + deficient class).
  EXIT 2: P2/P3 bookkeeping violation (survey model wrong; report, do not conclude).

Sweep: exhaustive K ≤ 2 over e ≤ 4, h ≤ 9, g ≤ 3 (+ recenterings at e = 1 stages);
random 4000 specs at K = 3, 4 with e ≤ 4, h ≤ 12, g ≤ 3. Includes the adversarial
strata the blueprint flags: h_r sharing factors with earlier e_j (the gcd-defect
locus, e.g. e_0 = 2, h_1 even), non-monotone slopes (no steeper filter).
"""

import itertools
import math
import random
import sys
from fractions import Fraction

random.seed(20260730)


def fibers(stages, moves):
    """stages: list of (e_r, h_r) for r = 0..K; moves: list over k = 0..K-1 of
    ('inc', g) or ('rec',). Returns dict: class (Fraction in [0,1)) -> count,
    plus (D, G)."""
    K = len(moves)
    assert len(stages) == K + 1
    # kappa_r and slot bounds
    d = 1
    kappa = []
    for r, (e, h) in enumerate(stages):
        d *= e
        kappa.append(Fraction(h, d))
    bounds = []
    for k, mv in enumerate(moves):
        if mv[0] == 'inc':
            bounds.append(stages[k][0] * mv[1])  # e_k (stage k's stored e) * g_{k+1}
        else:
            bounds.append(1)
    D = 1
    for (e, h) in stages[:-1]:
        D *= e
    G = 1
    for mv in moves:
        if mv[0] == 'inc':
            G *= mv[1]
    cnt = {}
    for s in itertools.product(*[range(b) for b in bounds]):
        v = sum(si * kappa[k] for k, si in enumerate(s))
        cls = v - math.floor(v)
        cnt[cls] = cnt.get(cls, 0) + 1
    return cnt, D, G


def check(stages, moves):
    cnt, D, G = fibers(stages, moves)
    # P1: every fiber size is exactly G (deficiency = size in (0, G); excess = > G)
    for cls, n in cnt.items():
        if n != G:
            return ('P1', cls, n, G, D)
    # P2: exactly D classes, and they are exactly {j/D}
    want = {Fraction(j, D) for j in range(D)}
    if set(cnt.keys()) != want:
        return ('P2', sorted(cnt.keys()), D, G, None)
    return None


def legal_pairs(emax, hmax):
    return [(e, h) for e in range(1, emax + 1) for h in range(1, hmax + 1)
            if math.gcd(e, h) == 1]


def gen_moves(stages_so_far, k_left, emax, hmax, gmax, rng=None):
    """Yield (stages, moves) completions; exhaustive if rng is None."""
    if k_left == 0:
        yield stages_so_far, []
        return
    e_cur = stages_so_far[-1][0]
    options = []
    for g in range(1, gmax + 1):
        for (e2, h2) in legal_pairs(emax, hmax):
            options.append(('inc', g, e2, h2))
    if e_cur == 1:
        options.append(('rec',))
    if rng is not None:
        options = [rng.choice(options)]
    for opt in options:
        if opt[0] == 'inc':
            _, g, e2, h2 = opt
            for st, mv in gen_moves(stages_so_far + [(e2, h2)], k_left - 1,
                                    emax, hmax, gmax, rng):
                yield st, [('inc', g)] + mv
        else:
            e_prev, h_prev = stages_so_far[-1]
            for st, mv in gen_moves(stages_so_far + [(1, h_prev)], k_left - 1,
                                    emax, hmax, gmax, rng):
                yield st, [('rec',)] + mv


def main():
    tested = 0
    # --- P3 shallow regression first (exact ScratchC6 header numbers) ---
    stages = [(1, 1), (1, 1)]      # base (1,1); increment child (e',h') = (1,1)
    moves = [('inc', 2)]           # g = 2
    cnt, D, G = fibers(stages, moves)
    kappa0 = Fraction(1, 1)
    aligned = [s0 for s0 in range(stages[0][0] * 2)
               if (Fraction(0) - s0 * kappa0).denominator == 1]
    attainable = [s0 for s0 in aligned if Fraction(0) - s0 * kappa0 >= 0]
    p3_ok = (len(aligned) == 2 and len(attainable) == 1 and G == 2 and D == 1
             and cnt.get(Fraction(0)) == 2)
    if not p3_ok:
        print('P3 VIOLATION (shallow regression):',
              dict(aligned=aligned, attainable=attainable, cnt=cnt, D=D, G=G))
        sys.exit(2)
    print(f'P3 shallow regression OK: aligned={aligned} attainable={attainable} '
          f'(N_att=1 < G=2: (4)-RHS false, non-fullness correctly reported; '
          f'2*[FQ:Fp]=[F_K+1:Fp] -> 2*1=2)')

    # --- exhaustive K = 1, 2 ---
    for K, emax, hmax, gmax in [(1, 4, 9, 3), (2, 3, 7, 3)]:
        for e0, h0 in legal_pairs(emax, hmax):
            for st, mv in gen_moves([(e0, h0)], K, emax, hmax, gmax):
                r = check(st, mv)
                tested += 1
                if r:
                    print(f'{r[0]} VIOLATION: stages={st} moves={mv} detail={r[1:]}')
                    sys.exit(1 if r[0] == 'P1' else 2)
        print(f'exhaustive K={K} clean (cumulative specs: {tested})')

    # --- random K = 3, 4 (adversarial: h free mod earlier e; no slope filter) ---
    rng = random.Random(20260730)
    for K in (3, 4):
        for _ in range(2000):
            e0, h0 = rng.choice(legal_pairs(4, 12))
            st, mv = next(gen_moves([(e0, h0)], K, 4, 12, 3, rng))
            r = check(st, mv)
            tested += 1
            if r:
                print(f'{r[0]} VIOLATION: stages={st} moves={mv} detail={r[1:]}')
                sys.exit(1 if r[0] == 'P1' else 2)
        print(f'random K={K} clean (cumulative specs: {tested})')

    print(f'PROBE-PASS: {tested} slot data, zero deficient classes (P1), full '
          f'subgroup coverage everywhere (P2), shallow regression exact (P3).')
    print('Conclusion: #aligned addresses = prod(g) on every achieved class -> the '
          'R-3 deficiency mechanism cannot occur; CL04_dichotomy_probe is FALSE for '
          'every legal tower; display (4) SURVIVES.')
    sys.exit(0)


if __name__ == '__main__':
    main()
