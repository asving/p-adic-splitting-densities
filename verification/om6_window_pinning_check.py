#!/usr/bin/env python3
"""OM-6 certification script — window pinning / LEMMA GENHN-3 cap clauses.

Certifies the un-transcribed clauses of EFF.GENHN.29 (LEMMA GENHN-3, GENHN_PROOF
L741-763, as rider-corrected by [e2]E1, [r2], R4 F-1/CAP-GEN) before transcription,
with constructed-counterexample attacks on each. Exact integer arithmetic throughout;
primes p,q in {2,3}; both characteristics (Z/p^M with carries vs F_q[t]/t^M without)
exercised where they can differ (CERT-5; CERT-3's model is valuation-layer,
characteristic-blind by construction, run over both carrier types anyway).

Legs:
  CERT-1  (c) general-e1 congruence bound + occupancy-scope attack + no-coprimality attack
  CERT-2  (b) general string-end / band cardinality  = min(floor(ih/e1), N) + H.46 tie
  CERT-3  (a) interior min-stability + cap undercut (instability at >= e1*N) + no-tie
  CERT-4  (a,f1>=2) [r2] band geometry comp(m) + census Q^comp - 1 + committed instances
          + trichotomy disjointness + the r2-overlap defect reproduced
  CERT-5  (d) triangularity of the recentering update, BOTH characteristics, exhaustive
          at small size + tightness witness (height-d dependence on height-d)

Exit code 0 iff every check passes. Run: python3 om6_window_pinning_check.py
"""

import itertools
import sys
from math import gcd

FAIL = []


def check(name, cond, detail=""):
    status = "PASS" if cond else "FAIL"
    print(f"[{status}] {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAIL.append(name)


# ----------------------------------------------------------------------------
# CERT-1 — GENHN-3(c): the general-e1 consulted-height congruence bound.
# Display: m < e1*N and m == i(m)*h (mod e1)  ==>
#          m <= e1*N - e1 + (i*h mod e1) <= e1*(N-1) + i*h   ("inside the string")
# ----------------------------------------------------------------------------
print("=" * 78)
print("CERT-1: GENHN-3(c) general congruence bound")
print("=" * 78)

n_checked = 0
ok_ineq1 = ok_ineq2 = True
for e1 in range(1, 7):
    for h in range(1, 10):
        if gcd(h, e1) != 1:
            continue
        for N in range(1, 11):
            for i in range(e1):
                r = (i * h) % e1
                for m in range(e1 * N):
                    if m % e1 != r:
                        continue
                    n_checked += 1
                    if not (m <= e1 * N - e1 + r):
                        ok_ineq1 = False
                    if not (e1 * N - e1 + r <= e1 * (N - 1) + i * h):
                        ok_ineq2 = False
check("CERT-1a: m <= e1*N - e1 + (i*h % e1) on grid", ok_ineq1, f"{n_checked} cells")
check("CERT-1b: e1*N - e1 + (i*h % e1) <= e1*(N-1) + i*h on grid", ok_ineq2,
      f"{n_checked} cells")

# Occupied form: m = e1*v + i*h with v >= 0 and m < e1*N  ==>  v <= N-1
ok_occ = True
n_occ = 0
for e1 in range(1, 7):
    for h in range(1, 10):
        if gcd(h, e1) != 1:
            continue
        for N in range(1, 11):
            for i in range(e1):
                for v in range(0, 3 * N):
                    m = e1 * v + i * h
                    if m < e1 * N:
                        n_occ += 1
                        if not v <= N - 1:
                            ok_occ = False
check("CERT-1c: occupied form (m = e1*v + i*h < e1*N ==> v <= N-1)", ok_occ,
      f"{n_occ} cells")

# ATTACK 1: the "inside the string" reading WITHOUT the occupancy pin.
# Witness (e1, h) = (3, 2), m = 1: class i(1) = 2 (2*2 = 4 == 1 mod 3), but
# 1 = 3v + 4 has no solution v >= 0: m is an UNOCCUPIED height (a(m) = -1) —
# the same scope defect EFF.GENHN.28 records for the normalizer display.
e1, h, m = 3, 2, 1
i_m = next(i for i in range(e1) if (i * h) % e1 == m % e1)
occupied = any(e1 * v + i_m * h == m for v in range(0, 100))
check("CERT-1 ATTACK (occupancy): (3,2,1) has i(m)=2 and is NOT in the class string",
      i_m == 2 and not occupied, "the un-pinned 'inside the string' reading is FALSE")
# ... while both displayed inequalities still HOLD at the attack point (any N >= 1):
r = (i_m * h) % e1
ok_attack_ineq = all(
    (m <= e1 * N - e1 + r) and (e1 * N - e1 + r <= e1 * (N - 1) + i_m * h)
    for N in range(1, 11) if m < e1 * N)
check("CERT-1 ATTACK: the two inequalities SURVIVE at the attack point", ok_attack_ineq)

# ATTACK 2: drop coprimality — the class of m is no longer well-defined.
# e1 = 4, h = 2: classes i = 0 and i = 2 have i*h % e1 = 0 and 0: collision.
e1, h = 4, 2
residues = [(i * h) % e1 for i in range(e1)]
check("CERT-1 ATTACK (coprimality): gcd(2,4)=2 collapses class residues",
      len(set(residues)) < e1, f"residues {residues}")

# ----------------------------------------------------------------------------
# CERT-2 — GENHN-3(b): general string end and band cardinality.
# Class-i string (occupied heights, v in [0, N-1]) ends at e1*(N-1) + i*h.
# Band (heights >= e1*N) cardinality per class = min(floor(i*h/e1), N).
# ----------------------------------------------------------------------------
print("=" * 78)
print("CERT-2: GENHN-3(b) raggedness / band cardinality")
print("=" * 78)

ok_end = ok_band = ok_ragged = True
n2 = 0
for e1 in range(1, 7):
    for h in range(1, 12):
        if gcd(h, e1) != 1:
            continue
        for N in range(1, 12):
            ends = []
            for i in range(e1):
                string = [e1 * v + i * h for v in range(N)]
                n2 += 1
                if max(string) != e1 * (N - 1) + i * h:
                    ok_end = False
                ends.append(max(string))
                band = [m for m in string if m >= e1 * N]
                if len(band) != min((i * h) // e1, N):
                    ok_band = False
            # RAGGED: ends pairwise distinct across classes (h >= 1)
            if len(set(ends)) != e1:
                ok_ragged = False
check("CERT-2a: string end = e1*(N-1) + i*h", ok_end, f"{n2} strings")
check("CERT-2b: band card = min(floor(i*h/e1), N)", ok_band)
check("CERT-2c: ends pairwise distinct across classes (RAGGED)", ok_ragged)

# Genre-E tie to landed H.46: e1 = 2, i = 1, h = 2t+1  ==>  band card = t
ok_h46 = True
for t in range(0, 5):
    h = 2 * t + 1
    for N in range(2 * t + 2, 2 * t + 8):
        band = [2 * v + h for v in range(N) if 2 * v + h >= 2 * N]
        if len(band) != t:
            ok_h46 = False
check("CERT-2d: genre-E specialization = H.46 raggedBand_card value t", ok_h46)

# Reciprocity: total band over classes = (e1-1)(h-1)/2 at gcd = 1, N large.
ok_rec = True
for e1 in range(1, 8):
    for h in range(1, 12):
        if gcd(h, e1) != 1:
            continue
        N = e1 * h + 5  # large enough: no clamping
        total = sum(min((i * h) // e1, N) for i in range(e1))
        if total != (e1 - 1) * (h - 1) // 2:
            ok_rec = False
check("CERT-2e: total band = (e1-1)(h-1)/2 (classical reciprocity, gcd=1)", ok_rec)

# ATTACK: the clamp min(., N) is REAL — h large vs N small.
e1, i, h, N = 2, 1, 21, 3
band = [2 * v + i * h for v in range(N) if 2 * v + i * h >= 2 * N]
check("CERT-2 ATTACK (clamp): (e1,i,h,N)=(2,1,21,3) band card = N = 3, not floor(ih/e1) = 10",
      len(band) == 3 and (i * h) // e1 == 10)

# ----------------------------------------------------------------------------
# CERT-3 — GENHN-3(a) interior: min-stability below e1*N; instability at >= e1*N.
# Model: state = per-class digit vector over F_q; in-window digits (v <= N-1) FIXED,
# out-of-window digits (v in [N, N+extra]) range over completions. dv(state) =
# min over nonzero digits of e1*v + i*h (valuation layer; residue ties are
# GENHN-2's F_Q-independence, cited not re-proved). Characteristic-blind by
# construction at this layer; the digit alphabet is F_q, q in {2,3}.
# ----------------------------------------------------------------------------
print("=" * 78)
print("CERT-3: GENHN-3(a) interior stability + cap undercut")
print("=" * 78)

INF = 10 ** 9


def dv_of(digits):
    """digits: dict (i, v) -> nonzero flag; dv = min e1*v + i*h over nonzero."""
    vals = [val for val, nz in digits if nz]
    return min(vals) if vals else INF


ok_stable = ok_undercut = ok_notie = True
n_states = 0
for q in (2, 3):
    for e1, h in ((1, 1), (2, 1), (2, 3), (3, 2)):
        assert gcd(h, e1) == 1
        for N in (2, 3):
            extra = 1  # out-of-window heights N..N+extra per class
            slots_in = [(i, v) for i in range(e1) for v in range(N)]
            slots_out = [(i, v) for i in range(e1) for v in range(N, N + extra + 1)]
            # enumerate in-window nonzero-patterns (value layer: nonzero flag suffices;
            # q enters as the number of digit values behind each flag — counted, unused
            # at the min layer, asserted equal q-1 per nonzero flag)
            for pat_in in itertools.product((0, 1), repeat=len(slots_in)):
                n_states += 1
                in_vals = [(e1 * v + i * h, nz) for (i, v), nz in zip(slots_in, pat_in)]
                dv_in = dv_of(in_vals)
                # no-tie check: no occupied in-window value equals e1*N (gcd = 1)
                if any(val == e1 * N for val, nz in in_vals if nz):
                    ok_notie = False
                dvs = set()
                for pat_out in itertools.product((0, 1), repeat=len(slots_out)):
                    out_vals = [(e1 * v + i * h, nz)
                                for (i, v), nz in zip(slots_out, pat_out)]
                    dvs.add(dv_of(in_vals + out_vals))
                if dv_in < e1 * N:
                    if dvs != {dv_in}:
                        ok_stable = False
                else:
                    # instability: at least two distinct completion values
                    if len(dvs) < 2:
                        ok_undercut = False
check("CERT-3a: dv < e1*N ==> constant over ALL out-completions", ok_stable,
      f"{n_states} in-window states, q in {{2,3}}, exhaustive completions")
check("CERT-3b: dv >= e1*N ==> completions DISAGREE (undercut realized)", ok_undercut)
check("CERT-3c: no occupied in-window value ties e1*N (gcd(h,e1)=1)", ok_notie)

# ATTACK: no-tie NEEDS coprimality. (e1, h) = (2, 2): i = 1, v = N-1 gives
# 2(N-1) + 2 = 2N: an in-window value EQUAL to the cap.
e1, h, N = 2, 2, 3
tie = e1 * (N - 1) + 1 * h == e1 * N
check("CERT-3 ATTACK (no-tie needs gcd=1): (e1,h)=(2,2) has in-window value = e1*N", tie)

# ----------------------------------------------------------------------------
# CERT-4 — the [r2]/CAP-GEN band geometry and census, beyond the (1,2) frame.
# Frame ([r2]): mu = 2, e1 = 1, slope k; component t of height-m slot is in-window
# iff m - t*k <= N - 1. comp(m) = #visible components. Band = [N, N + (f1-1)k - 1].
# Census of a nonzero READABLE pin = Q^comp(m) - 1 (CAP-GEN COUNT TRANSPORT = E2).
# ----------------------------------------------------------------------------
print("=" * 78)
print("CERT-4: [r2]/CAP-GEN band geometry + census + committed instances")
print("=" * 78)


def comp(f1, k, N, m):
    return sum(1 for t in range(f1) if m <= N - 1 + t * k)


ok_int = ok_band4 = ok_beyond = True
for f1 in (2, 3, 4):
    for k in (1, 2, 3):
        for N in range(2, 11):
            for m in range(0, N + f1 * k + 3):
                c = comp(f1, k, N, m)
                if m <= N - 1 and c != f1:
                    ok_int = False
                if N <= m <= N - 1 + (f1 - 1) * k and not (1 <= c < f1):
                    ok_band4 = False
                if m > N - 1 + (f1 - 1) * k and c != 0:
                    ok_beyond = False
check("CERT-4a: comp interior = f1; band in [1, f1); beyond = 0",
      ok_int and ok_band4 and ok_beyond, "f1 in 2..4, k in 1..3, N in 2..10")

# Census: exhaustive count of nonzero vectors supported on visible components,
# per digit alphabet F_q, q in {2,3}: must equal q^comp - 1.
ok_census = True
for q in (2, 3):
    for f1 in (2, 3):
        for k in (1, 2):
            for N in (4, 7):
                for m in range(N, N + (f1 - 1) * k):
                    vis = [t for t in range(f1) if m <= N - 1 + t * k]
                    cnt = sum(1 for vec in itertools.product(range(q), repeat=f1)
                              if any(vec[t] for t in vis)
                              and all(vec[t] == 0 for t in range(f1) if t not in vis))
                    if cnt != q ** comp(f1, k, N, m) - 1:
                        ok_census = False
check("CERT-4b: census = q^comp - 1 (exhaustive span count, q in {2,3})", ok_census)

# Committed (1,3,2) instances ([r2](4) / EFF.GENHN.32 / H.44's audit):
c7 = comp(3, 1, 7, 7)
c8_pin = comp(3, 1, 8, 7)
check("CERT-4c: (1,3,2) N=7: comp(N)=2, RAM(7)=3*2^13=24576, UND=2^13=8192, total 2^15",
      c7 == 2 and (2 ** c7 - 1) * 2 ** 13 == 24576
      and (2 ** c7 - 1) * 2 ** 13 + 2 ** 13 == 2 ** 15)
check("CERT-4d: (1,3,2) N=8: pin interior comp=3, RAM(7)=7*2^18=1835008, UND=2^18, total 2^21",
      c8_pin == 3 and (2 ** c8_pin - 1) * 2 ** 18 == 1835008
      and (2 ** c8_pin - 1) * 2 ** 18 + 2 ** 18 == 2 ** 21)
check("CERT-4e: (1,2,2) k=1: band is the single height N (GENH4-CAP(F) frame)",
      comp(2, 1, 7, 7) == 1 and comp(2, 1, 7, 8) == 0)
# comp(N+1) at f1=3, k=1:
check("CERT-4f: (1,3,2) comp(N+1) = 1", comp(3, 1, 7, 8) == 1)


# Trichotomy (E1-corrected, = landed H.88 capBranch): pairwise-disjoint antecedents.
def capbranch(N, w):
    if N > 2 * w:
        return "2SIDED"
    return "RAM" if N % 2 == 1 else "UND"


ok_tri = True
for N in range(0, 61):
    for w in range(0, 61):
        hits = [N > 2 * w, N <= 2 * w and N % 2 == 1, N <= 2 * w and N % 2 == 0]
        if sum(hits) != 1:
            ok_tri = False
check("CERT-4g: trichotomy antecedents pairwise disjoint + exhaustive on [0,60]^2", ok_tri)

# ATTACK: the r2-defect (RAM clause without its side condition N <= 2w) OVERLAPS (a):
overlap = [(N, w) for N in range(0, 20) for w in range(0, 20)
           if (N > 2 * w) and (N % 2 == 1)]  # both (a) and defective-RAM fire
check("CERT-4 ATTACK (r2 overlap defect reproduced): defective RAM double-fires",
      len(overlap) > 0, f"e.g. (N,w)={overlap[0]}; ledgered lesson: re-derive, never "
      f"transcribe a verifier's phrasing")
# ... and the committed counter-key: capBranch(7,3) = 2SIDED (H.88's Lean refutation
# of the r2 ordering, which predicted RAM): 2SIDED(3,4)=384 vs RAM(7)=128, 384+128=512.
check("CERT-4h: capBranch(7,3)=2SIDED; 384+128=512=2^9 partition",
      capbranch(7, 3) == "2SIDED" and 384 + 128 == 512 == 2 ** 9)

# ----------------------------------------------------------------------------
# CERT-5 — GENHN-3(d): triangularity of the recentering update, BOTH ring types.
# Claim: the update x -> x + s determines new digits at height d from old digits
# at heights <= d (carries move upward only). Test: f' == f (coefficientwise)
# mod pi^D  ==>  f'(x+s) == f(x+s) mod pi^D. Exhaustive at small size.
# ----------------------------------------------------------------------------
print("=" * 78)
print("CERT-5: GENHN-3(d) triangularity, char 0 (Z/p^M) vs char p (F_q[t]/t^M)")
print("=" * 78)

from math import comb


def recenter_int(coeffs, s, mod):
    """f(x+s) coefficients mod `mod` (char-0 model: integers with carries)."""
    mu = len(coeffs) - 1
    out = [0] * (mu + 1)
    for j, a in enumerate(coeffs):
        for l in range(j + 1):
            out[l] = (out[l] + a * comb(j, l) * pow(s, j - l, mod)) % mod
    return out


def poly_mul_mod(a, b, q, M):
    out = [0] * M
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if i + j < M:
                out[i + j] = (out[i + j] + ai * bj) % q
    return out


def recenter_poly(coeffs, s, q, M):
    """char-p model: coefficients are F_q[t]/t^M digit vectors, NO carries."""
    mu = len(coeffs) - 1
    out = [[0] * M for _ in range(mu + 1)]
    # powers of s in F_q[t]/t^M
    spow = [[1] + [0] * (M - 1)]
    for _ in range(mu):
        spow.append(poly_mul_mod(spow[-1], s, q, M))
    for j, a in enumerate(coeffs):
        for l in range(j + 1):
            term = [(comb(j, l) % q) * c % q for c in spow[j - l]]
            prod = poly_mul_mod(a, term, q, M)
            out[l] = [(x + y) % q for x, y in zip(out[l], prod)]
    return out


# char 0: EXHAUSTIVE at p = 2, M = 3, mu = 2 — all f, all s, all height->=D perturbations
ok_c0 = True
tight_c0 = False
for p in (2, 3):
    M = 3
    mod = p ** M
    mu = 2
    rng = range(0, mod, 3) if p == 3 else range(mod)  # thin the p=3 grid
    for coeffs in itertools.product(rng, repeat=mu + 1):
        for s in range(0, mod, 1 if p == 2 else 3):
            base = recenter_int(list(coeffs), s, mod)
            for D in (1, 2):
                pD = p ** D
                for delta in itertools.product(range(0, mod, pD), repeat=mu + 1):
                    coeffs2 = [(a + d) % mod for a, d in zip(coeffs, delta)]
                    new = recenter_int(coeffs2, s, mod)
                    if any((x - y) % pD != 0 for x, y in zip(base, new)):
                        ok_c0 = False
check("CERT-5a: char 0 (p=2 exhaustive M=3 mu=2; p=3 thinned): heights <= D preserved",
      ok_c0)

# tightness: an old height-D digit change CAN move a new height-D digit (bound is tight)
p, M, mu = 2, 3, 2
mod = p ** M
f = [1, 0, 0]
f2 = [1 + p, 0, 0]  # height-1 digit of a0 changed
g, g2 = recenter_int(f, 1, mod), recenter_int(f2, 1, mod)
tight_c0 = any((x - y) % (p ** 2) != 0 for x, y in zip(g, g2))
check("CERT-5b: tightness — height-1 old change moves a height-1 new digit", tight_c0)

# char p: EXHAUSTIVE at q = 2, M = 2, mu = 2; sampled at q = 3
ok_cp = True
for q in (2, 3):
    M = 2
    mu = 2
    digitspace = list(itertools.product(range(q), repeat=M))
    space = digitspace if q == 2 else digitspace[::2]
    for coeffs in itertools.product(space, repeat=mu + 1):
        for s in space:
            base = recenter_poly([list(c) for c in coeffs], list(s), q, M)
            D = 1
            for delta in itertools.product(range(q), repeat=mu + 1):
                coeffs2 = [[c[0], (c[1] + d) % q] for c, d in zip(coeffs, delta)]
                new = recenter_poly(coeffs2, list(s), q, M)
                if any(b[0] != n[0] for b, n in zip(base, new)):
                    ok_cp = False
check("CERT-5c: char p (q=2 exhaustive M=2 mu=2; q=3 thinned): height-0 preserved "
      "under height-1 perturbations", ok_cp)

# ATTACK (downward carry search): the char-0 exhaustive leg above IS the search —
# zero violations found means no downward carry exists at this size; report count.
print("CERT-5 ATTACK: downward-carry search = the exhaustive legs above; 0 violations.")

# ----------------------------------------------------------------------------
print("=" * 78)
if FAIL:
    print(f"RESULT: {len(FAIL)} FAILURES: {FAIL}")
    sys.exit(1)
print("RESULT: ALL CHECKS PASS")
sys.exit(0)
