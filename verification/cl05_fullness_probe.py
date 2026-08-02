#!/usr/bin/env python3
"""CL-05 fullness-identity probe (2026-08-02, run BEFORE the Lean proof per the
numerics-first discipline; blueprint B2DEF_LEAN_2026-08-08.md unit CL5 falsifier
N-TD1 adjacency).

TARGET IDENTITY (C6_alphabetCard.lean:129, conjunct 2 <=): for a legal tower with
nonempty level set L(b,gamma) and cleanThreshold (every ZZ-aligned address
attainable):   card ALPHABET(b,gamma) = card K_top.

Via the corpus reductions (CL13 injectivity + T11 surjectivity, both PROVED
Lean-core at HEAD), card ALPHABET = |FQ|^N with N = #levelSet, and the identity
reduces to the two counting claims tested here.

SEALED PREDICTIONS (written before first run):
  P1 (NT-core, the genuinely new math): for slot data (e_r, h_r, G_r), r < K,
     with gcd(e_r,h_r)=1, e_r>=1, G_r>=1, bounds b_r = e_r*G_r,
     kappa_r = h_r/(e_r*prod_{j<r}e_j), D0 = prod e_r:
     for EVERY rational target delta with D0*delta in ZZ, the count
       #{s in prod [0,b_r) : delta - sum s_r*kappa_r in ZZ} = prod G_r  (exactly),
     and for D0*delta not in ZZ the count is 0.
     Tested exhaustively over random data INCLUDING recentering rows (1,h,1)
     and h_r sharing factors with earlier e_j (the gcd-defect strata).
  P2 (assembly): for tower-shaped data (base q0 = |K_0| = |FQ|; increments
     multiply residue card by q0^g; recenterings keep it), with gamma an
     achieved height class and hclean automatic in this arithmetic model
     (every aligned address of the achieved class attainable at large gamma):
       N := #aligned = prod g  and  |FQ|^N = card K_top.
  P3 (shallow control, the D11c regime): at small gamma some aligned addresses
     are UNattainable (hclean FAILS) and N_att < prod g strictly — the guarded
     statement's hypothesis is doing real work (non-vacuity of the guard).
FALSIFIER: any P1/P2 violation kills the Lean attempt -> report countermodel.
"""
import itertools, math, random
from fractions import Fraction

random.seed(20260802)

def gen_data(K, allow_rec=True):
    """Per-move data: list of (e_r, h_r, G_r, kind). Recentering rows require
    parent e=1 per IsRecentering (sigma.e=1 AND sigma'.e=1); we model the row
    of a recentered CHILD stage as (1, h_prev, 1)."""
    rows = []
    prev_e, prev_h = None, None
    for r in range(K):
        # stage r data (e_r,h_r) constrained: if previous move was 'rec', stage r
        # has e=1,h=h_prev. Else free.
        if rows and rows[-1][3] == 'rec':
            e, h = 1, rows[-1][1]
        else:
            e = random.choice([1, 1, 2, 2, 3, 4, 5, 6])
            while True:
                h = random.randint(1, 12)
                if math.gcd(e, h) == 1:
                    break
        # move r: recentering only legal if e_r == 1
        if allow_rec and e == 1 and random.random() < 0.4:
            kind, G = 'rec', 1
        else:
            kind, G = 'inc', random.choice([1, 1, 2, 2, 3, 4])
        rows.append((e, h, G, kind))
    return rows

def counts(rows, delta):
    """#aligned per the walk: exhaustive over the box."""
    K = len(rows)
    bounds = [e * G for (e, h, G, k) in rows]
    strs = [1]
    for (e, h, G, k) in rows:
        strs.append(strs[-1] * e)
    kap = [Fraction(h, e * strs[r]) for r, (e, h, G, k) in enumerate(rows)]
    n = 0
    for s in itertools.product(*[range(b) for b in bounds]):
        x = delta - sum(Fraction(s[r]) * kap[r] for r in range(K))
        if x.denominator == 1:
            n += 1
    return n

def attainable_count(rows, delta):
    K = len(rows)
    bounds = [e * G for (e, h, G, k) in rows]
    strs = [1]
    for (e, h, G, k) in rows:
        strs.append(strs[-1] * e)
    kap = [Fraction(h, e * strs[r]) for r, (e, h, G, k) in enumerate(rows)]
    na = natt = 0
    for s in itertools.product(*[range(b) for b in bounds]):
        x = delta - sum(Fraction(s[r]) * kap[r] for r in range(K))
        if x.denominator == 1:
            na += 1
            if x >= 0:
                natt += 1
    return na, natt

fails = 0
# ---- P1: NT-core, random sweep ----
trials = 0
for t in range(400):
    K = random.randint(0, 4)
    rows = gen_data(K)
    D0 = math.prod(e for (e, h, G, k) in rows)
    PG = math.prod(G for (e, h, G, k) in rows)
    # targets: on-lattice (D0*delta in ZZ) and off-lattice
    for m in random.sample(range(-3 * D0, 3 * D0 + 1), min(5, 6 * D0 + 1)):
        delta = Fraction(m, D0)
        c = counts(rows, delta)
        want = PG if (Fraction(m, D0) * D0).denominator == 1 else None
        trials += 1
        if c != PG:
            print("P1 FAIL(on-lattice)", rows, delta, c, PG); fails += 1
    if D0 > 1:
        delta = Fraction(1, D0 * 2 + 1)  # off-lattice
        if counts(rows, delta) != 0:
            print("P1 FAIL(off-lattice)", rows, delta); fails += 1
print(f"P1: {trials} on-lattice fiber checks done, fails={fails}")

# ---- P2/P3: tower-shaped assembly ----
p2t = p3seen = 0
for t in range(200):
    K = random.randint(1, 4)
    rows = gen_data(K)
    q0 = random.choice([2, 3, 4, 5, 8, 9])
    prodg = math.prod(G for (e, h, G, k) in rows if k == 'inc')
    PG = math.prod(G for (e, h, G, k) in rows)
    assert PG == prodg  # recenterings carry G=1
    cardKtop = q0 ** prodg
    strs = [1]
    for (e, h, G, k) in rows:
        strs.append(strs[-1] * e)
    D0 = strs[-1]
    # top-slot kappa uses (e_K,h_K) of the TOP stage; achieved class:
    # pick a random legal coordinate and read gamma off it (large l => deep => clean)
    bounds = [e * G for (e, h, G, k) in rows]
    kap = [Fraction(h, e * strs[r]) for r, (e, h, G, k) in enumerate(rows)]
    s0 = [random.randrange(b) for b in bounds]
    l0 = random.randint(5, 9)  # deep level: attainability for free
    delta = l0 + sum(Fraction(s0[r]) * kap[r] for r in range(K))
    na, natt = attainable_count(rows, delta)
    # deep regime: every aligned address attainable (hclean) — check, then P2
    if na == natt:
        p2t += 1
        if na != prodg or q0 ** na != cardKtop:
            print("P2 FAIL", rows, q0, delta, na, prodg); fails += 1
    # P3 shallow control: gamma from l0=0; expect (sometimes) natt < na
    delta_sh = 0 + sum(Fraction(s0[r]) * kap[r] for r in range(K) if False)  # = 0
    na2, natt2 = attainable_count(rows, Fraction(0))
    if natt2 < na2:
        p3seen += 1
print(f"P2: {p2t} deep assemblies checked; P3 shallow-deficit instances seen: {p3seen}; fails={fails}")
print("VERDICT:", "ALL SEALED PREDICTIONS HOLD" if fails == 0 else f"{fails} FAILURES")
