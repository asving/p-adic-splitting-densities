#!/usr/bin/env python3
"""
equalchar_probe.py — EMPIRICAL PROBE (not a proof), n = 2, O = F_q[[t]] (equal
characteristic), vs the mixed-characteristic O = Z_p check in `genuine_density_check.py`.

QUESTION (Asvin, 2026-08-13). The current capstone Prop quantifies over ALL complete
DVRs with finite residue field, including the equal-characteristic ones F_q[[t]] —
not just Z_p and its extensions. Do the F_q[[t]] splitting densities at n = 2 match the
SAME rational functions R_sigma(q) that the Z_p densities follow at q = p (per the W-11
corpus, `../../lean/notes/openmath/W11_PROOF_2026-08-08.md`)?

    W-11 closed forms (function of q alone):
        undecided count at level N   = q^N
        ram-decided count            = (q^(2N) - q^(2N-2K)) / (q+1),  K = floor(N/2)
        split-decided = inert-decided = (q^(2N) - q^N - ram) / 2
        limit densities: split = inert = q / (2(q+1)),  ram = 1/(q+1)

METHOD. Mirror `genuine_density_check.py`'s structure and level conventions exactly:
for O = F_q[t]]] and monic quadratics f(x) = x^2 + b x + c with b, c ranging over
q^N classes each (polynomials of degree < N, i.e. residues mod t^N), decide whether
EVERY lift to F_q[[t]] has a fixed splitting type by checking all q^(2K) refinements
to precision M = N + K, exactly as the Z_p script checks all p^(2K) refinements to
precision M = N + K. `decided_counts_equalchar` is the direct mirror of
`decided_counts`; only the atomic classifier changes (t-adic instead of p-adic).

DECISION PROCEDURE — two genuinely different certificates, by parity of q:

  * q ODD (q = 3 here): char(F_q) is odd, so the ordinary discriminant test survives
    unchanged — d = b^2 - 4c (now a power series over F_q, t-adic valuation instead
    of p-adic), v(d) odd => ram, v(d) even with unit leading coefficient a quadratic
    residue in F_q => split, else inert. This is `classify_odd`, a verbatim transport
    of the p-odd branch of `genuine_density_check.classify` with p -> t-adically-valued
    polynomials over F_q.

  * q = 2: char(F_q) = 2, so 4 = 0 and the discriminant test is VACUOUS (d = b^2
    always, carrying no information — this is exactly the case flagged in the task:
    "the char-2 case especially cannot use the odd-char discriminant square test
    naively"). The correct invariant is Artin-Schreier, not Kummer. `classify_char2`
    implements it via Hensel + recentring + Newton polygon, characteristic-uniform in
    spirit but char-2-specific in the arithmetic (derivation below the function). This
    is NOT a discriminant test in disguise; it tracks (v(b), v(c)) directly.

Both classifiers return one of {"split","inert","ram",None}; None means "not forced by
the working precision" (mirrors `classify(d,p,M)` returning None). `classify_odd` is
sound AND complete within precision M (same guarantee as the Z_p script: the only
unresolved case is d == 0 exactly, which never happens within finite M). `classify_char2`
is sound but only PARTIALLY complete (see its docstring) — the recursion can end with
both v(b) and v(c) still unresolved inside the working precision; those cells are
honestly reported as certificate-limited rather than guessed. This is a knowingly
conservative choice per the task's instruction that correctness matters more than depth.

HONESTY. This script is an empirical cross-check, not a proof of anything about
`OM.RealInstanceV2.montes_unconditional` or any other Lean capstone. It touches no Lean
file. Every count below is an exact enumeration (no sampling) at the stated precision.

Run:  python3 equalchar_probe.py
"""

import itertools
import os
import sys
import time
from fractions import Fraction

# Reuse (read-only import, no edits) the mixed-characteristic Z_p reference computation.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import genuine_density_check as zp  # decided_counts, w11_prediction, limit_densities


# ============================================================================
# Generic F_q[[t]] power-series arithmetic, q PRIME (q in {2,3} here), truncated
# representation: a length-L tuple of ints in [0,q), coefficient i = coeff of t^i.
# Addition is COEFFICIENT-WISE mod q (no carry) -- this is genuinely different
# arithmetic from the Z_p script's plain integers-mod-p^N, and is the reason this
# file cannot just reuse that script's classify() with p relabelled t.
# ============================================================================

def val(poly, q):
    """t-adic valuation within available precision: index of first nonzero coeff,
    or len(poly) if every coefficient seen so far is 0 (meaning 'valuation >=
    len(poly), unresolved at this precision')."""
    for i, c in enumerate(poly):
        if c % q != 0:
            return i
    return len(poly)


def padd(a, b, q):
    n = max(len(a), len(b))
    return tuple(((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % q
                 for i in range(n))


def pscale(k, a, q):
    return tuple((k * x) % q for x in a)


def psub(a, b, q):
    return padd(a, pscale(q - 1, b, q), q)


def pmul_trunc(a, b, q, M):
    """a * b truncated to length M (coefficients of t^0 .. t^{M-1})."""
    out = [0] * M
    la, lb = len(a), len(b)
    for i in range(min(la, M)):
        ai = a[i] % q
        if ai == 0:
            continue
        for j in range(min(lb, M - i)):
            out[i + j] = (out[i + j] + ai * b[j]) % q
    return tuple(out)


# ============================================================================
# q ODD branch: discriminant + Legendre symbol, direct transport of
# genuine_density_check.classify's "p odd" branch to t-adic polynomials over F_q.
# ============================================================================

def classify_odd(b, c, q, M):
    """b, c: length-M tuples over F_q, q an odd prime. Returns
    'split'/'inert'/'ram'/None. Sound and complete within precision M (the only
    unresolved case, v(d) >= M, requires d == 0 exactly on all M known digits,
    which the caller's refinement loop always eventually breaks for any lift
    with a nonzero digit before M -- exactly as in the Z_p script)."""
    d = psub(pmul_trunc(b, b, q, M), pscale(4 % q, c, q), q)
    v = val(d, q)
    if v >= M:
        return None
    if v % 2 == 1:
        return "ram"
    u = d[v] % q
    leg = pow(u, (q - 1) // 2, q)
    return "split" if leg == 1 else "inert"


# ============================================================================
# q = 2 branch: Artin-Schreier / Newton-polygon recursion.
#
# f(x) = x^2 + b x + c over F_2[[t]].  char = 2 => f'(x) = b identically (b, not
# 2x+b), so separability of f mod t depends on b(0) alone, not on any
# discriminant:
#
#   * b(0) = 1: f mod t = x^2 + x + c(0) is automatically separable (its
#     derivative b(0) = 1 =/= 0).  Hensel lifts the mod-t factorization type
#     verbatim: c(0) = 0 -> f mod t = x(x+1), two distinct F_2-roots -> SPLIT;
#     c(0) = 1 -> f mod t = x^2+x+1, the unique irreducible quadratic over F_2
#     -> INERT.  Decided from the residue alone, independent of all higher
#     digits of b, c.
#
#   * b(0) = 0: f mod t = x^2 + c(0) = (x + c(0))^2 (squaring is the IDENTITY
#     map on F_2, so every element has a unique, trivial-to-find square root --
#     this is the fact that makes q = 2 special among even q).  This is the
#     repeated-root / Eisenstein-adjacent case that needs genuine depth, exactly
#     as p = 2 needs the mod-8 test in Z_p.  Recentre x = y + c(0): because
#     char = 2 kills the cross term 2*r for ANY constant r, b is UNCHANGED by
#     recentring (b' = b, always -- unlike the odd-characteristic recentring
#     used implicitly in the discriminant test); c updates to
#     c' = c + c(0)*b + c(0).  By construction v(c') >= 1.
#
#     Now compare beta = v(b), gamma = v(c') via the Newton polygon of
#     y^2 + b y + c' (vertices (0,gamma), (1,beta), (2,0)):
#       - gamma finite, ODD:        2*beta > gamma  => RAM   (single segment,
#           slope -gamma/2 non-integer => both roots in the ramified ext.)
#         2*beta < gamma  => SPLIT (two length-1 segments => both roots in
#           the base field, at valuations beta and gamma-beta)
#         (2*beta == gamma impossible when gamma is odd)
#       - gamma finite, EVEN = 2d:
#         beta < d  => SPLIT (two length-1 segments again)
#         beta == d => rescaling by t^d makes b's residue a UNIT and c''s
#           residue the unique nonzero element of F_2 -- both forced to 1,
#           giving y'^2 + y' + 1 over F_2, the irreducible one => INERT,
#           always, deterministically (no further recursion possible: F_2 has
#           only one nonzero element)
#         beta > d  => rescale (b <- b / t^d, c' <- c' / t^gamma) and loop: the
#           rescaled b may now have nonzero residue (decide immediately) or may
#           still vanish mod t (recentre again and repeat) -- this is the
#           digit-at-a-time iteration the task asks for, mirroring how the Z_p
#           script's mod-8 test is itself a 3-extra-bit lookahead.
#       - beta unresolved within available precision but its KNOWN LOWER BOUND
#         already forces the comparison (e.g. 2*(known lower bound) > gamma, or
#         the lower bound already exceeds d) -- decide anyway.  Otherwise: None.
#
# SOUNDNESS: every branch above is a fact of Newton-polygon / Artin-Schreier
# theory about the ACTUAL power series, not about the truncation; the algorithm
# only ever uses truncated data to certify facts that hold for every possible
# continuation, so no unsound decision is possible by construction (verified by
# hand against x^2+x [split], x^2+x+1 [inert], x^2+t [Eisenstein => ram],
# x^2+t*x+t^2 [=t^2*(y^2+y+1) after x=ty => inert], x^2+t^2*x+t [Eisenstein => ram]).
# COMPLETENESS is only partial: the recursion can exhaust the working precision
# while both beta and gamma remain unresolved together, in which case the
# function honestly returns None (certificate-limited) rather than guessing.
# ============================================================================

def classify_char2(b, c, M):
    cur_b = list(b[:M])
    cur_c = list(c[:M])
    while True:
        Lb, Lc = len(cur_b), len(cur_c)
        if Lb == 0 or Lc == 0:
            return None
        b0 = cur_b[0] % 2
        if b0 == 1:
            c0 = cur_c[0] % 2
            return "split" if c0 == 0 else "inert"

        # b0 == 0: recentre by r = c0 (sqrt is the identity on F_2).
        r = cur_c[0] % 2
        if r == 0:
            new_c = list(cur_c)
        else:
            Lmin = min(Lb, Lc)
            new_c = [(cur_c[i] + cur_b[i]) % 2 for i in range(Lmin)]
        if new_c:
            new_c[0] ^= r
        cur_c = new_c

        beta = val(tuple(cur_b), 2)          # in [0, Lb]; == Lb means unresolved
        gamma = val(tuple(cur_c), 2)          # in [0, len(cur_c)]; == len means unresolved
        Lc2 = len(cur_c)
        beta_known = beta < Lb
        gamma_known = gamma < Lc2

        if not gamma_known:
            # gamma is only known as >= Lc2 (lower bound; true gamma, possibly
            # infinite if c is exactly 0, is >= Lc2). If beta is known and
            # already small enough that 2*beta < Lc2 <= gamma is forced no
            # matter how the unseen digits of c continue (including c == 0
            # exactly, i.e. f = x(x+b), still split since b != 0), decide
            # SPLIT without ever resolving gamma. This is the symmetric
            # counterpart of the "beta unresolved" completions below, and its
            # absence was the only source of spurious 'certificate-limited'
            # cells found while validating this script against Z_p (q=2,
            # N=3): the class b = t + O(t^3), c = O(t^3) is unconditionally
            # split in Z_p (v_2(disc) is pinned at exactly 2 by b alone) and
            # is now unconditionally split here too, by the same mechanism
            # (v(b) pinned small, so it alone forces v(disc-analogue) small).
            if beta_known and 2 * beta < Lc2:
                return "split"
            return None   # cannot pin down gamma enough to compare -- ambiguous

        if gamma % 2 == 1:
            if beta_known:
                if 2 * beta > gamma:
                    return "ram"
                if 2 * beta < gamma:
                    return "split"
                return None                   # unreachable: parity forbids equality
            # beta only known as >= Lb (lower bound)
            if 2 * Lb > gamma:
                return "ram"
            return None

        d = gamma // 2
        if beta_known:
            if beta < d:
                return "split"
            if beta == d:
                return "inert"
            cur_b = cur_b[d:]
            cur_c = cur_c[gamma:]
            continue
        # beta only known as >= Lb (lower bound)
        if Lb > d:
            cur_b = cur_b[d:]
            cur_c = cur_c[gamma:]
            continue
        return None


# ============================================================================
# Sanity checks against hand-derived examples (run once, at import time cost is
# negligible; abort loudly if any fails -- these pin the derivation above).
# ============================================================================

def _self_check():
    def pad(t, M):
        return tuple(t) + (0,) * (M - len(t))
    M = 8
    cases = [
        ((1, 0), (0, 0), "split"),      # x^2 + x
        ((1, 0), (1, 0), "inert"),      # x^2 + x + 1
        ((0, 0), (0, 1), "ram"),        # x^2 + t            (Eisenstein)
        ((0, 1), (0, 0, 1), "inert"),   # x^2 + t x + t^2  = t^2 (y^2+y+1), x = t y
        ((0, 0, 1), (0, 1), "ram"),     # x^2 + t^2 x + t    (Eisenstein)
    ]
    for b, c, expect in cases:
        got = classify_char2(pad(b, M), pad(c, M), M)
        assert got == expect, f"self-check failed: b={b} c={c} expected {expect} got {got}"


_self_check()


# ============================================================================
# decided_counts_equalchar -- direct mirror of genuine_density_check.decided_counts.
# ============================================================================

def decided_counts_equalchar(q, N, K):
    """Exact level-N decided counts for monic quadratics x^2+bx+c over F_q[[t]],
    using precision M = N+K, mirroring decided_counts(p, N, K) cell for cell."""
    M = N + K
    counts = {"split": 0, "inert": 0, "ram": 0}
    undecided = 0
    ambiguous = 0
    ext = list(itertools.product(range(q), repeat=K))
    classify = classify_char2 if q == 2 else (lambda bb, cc, MM: classify_odd(bb, cc, q, MM))
    for b0 in itertools.product(range(q), repeat=N):
        for c0 in itertools.product(range(q), repeat=N):
            types = set()
            for bext in ext:
                bfull = b0 + bext
                for cext in ext:
                    cfull = c0 + cext
                    types.add(classify(bfull, cfull, M))
            if types == {"split"} or types == {"inert"} or types == {"ram"}:
                counts[types.pop()] += 1
            else:
                undecided += 1
                if len(types - {None}) >= 2:
                    ambiguous += 1
    return counts, undecided, ambiguous


# ============================================================================
# Main: build the side-by-side table (equal-char vs mixed-char Z_p vs W-11).
# ============================================================================

def main():
    print("=" * 100)
    print("EQUAL-CHARACTERISTIC DENSITY PROBE  —  n = 2, O = F_q[[t]]  vs  O = Z_p  vs  W-11")
    print("(empirical cross-check; NOT a proof; no Lean touched)")
    print("=" * 100)

    plan = [
        (2, [1, 2, 3, 4], 6, 6),   # (q, levels, K_equalchar, K_mixed[reused from Z_p plan])
        (3, [1, 2, 3, 4], 3, 3),
    ]

    verdicts = {}
    for q, levels, Keq, Kzp in plan:
        lim = zp.limit_densities(q)
        print()
        print(f"--- q = {q}   certificate: {'Artin-Schreier/Newton-polygon (classify_char2)' if q == 2 else 'discriminant+QR (classify_odd, verbatim Z_p analogue)'} ---")
        print(f"    W-11 limits: split = inert = {lim['split']}, ram = {lim['ram']}")
        header = (f"{'N':>2} {'box':>6} | {'EQchar split':>12} {'EQchar inert':>12} "
                   f"{'EQchar ram':>10} {'EQ undec':>9} {'EQ amb':>7} | "
                   f"{'Zp split':>9} {'Zp inert':>9} {'Zp ram':>7} {'Zp undec':>9} | "
                   f"{'W11 split':>9} {'W11 ram':>8} {'W11 und':>8} | cell-match")
        print(header)
        first_divergence = None
        all_match = True
        for N in levels:
            t0 = time.time()
            eq_counts, eq_undec, eq_amb = decided_counts_equalchar(q, N, Keq)
            eq_dt = time.time() - t0
            zp_counts, zp_undec, zp_amb = zp.decided_counts(q, N, Kzp)
            pred, pundec = zp.w11_prediction(q, N)
            box = q ** (2 * N)

            cell_match = (eq_counts == zp_counts and eq_undec == zp_undec)
            if not cell_match and first_divergence is None:
                # identify which sigma first disagrees
                for sigma in ("split", "inert", "ram"):
                    if eq_counts[sigma] != zp_counts[sigma]:
                        first_divergence = (N, sigma, eq_counts[sigma], zp_counts[sigma])
                        break
                if first_divergence is None and eq_undec != zp_undec:
                    first_divergence = (N, "undecided", eq_undec, zp_undec)
            all_match = all_match and cell_match

            print(f"{N:>2} {box:>6} | {eq_counts['split']:>12} {eq_counts['inert']:>12} "
                  f"{eq_counts['ram']:>10} {eq_undec:>9} {eq_amb:>7} | "
                  f"{zp_counts['split']:>9} {zp_counts['inert']:>9} {zp_counts['ram']:>7} "
                  f"{zp_undec:>9} | {pred['split']:>9} {pred['ram']:>8} {pundec:>8} | "
                  f"{'YES' if cell_match else 'NO':>10}   ({eq_dt:.1f}s)")

        # limit trend: does EQchar decidedSeq(split)/box -> the same W-11 limit as N grows?
        Nmax = levels[-1]
        eq_counts_max, eq_undec_max, _ = decided_counts_equalchar(q, Nmax, Keq)
        trend_seq = Fraction(eq_counts_max["split"], q ** (2 * Nmax))
        trend_ok = abs(float(trend_seq) - float(lim["split"])) < 0.15  # loose, N is small

        print(f"    EQchar decidedSeq(split) at N={Nmax}: {trend_seq} = {float(trend_seq):.6f}  "
              f"vs W-11 limit {lim['split']} = {float(lim['split']):.6f}  "
              f"({'trend-consistent' if trend_ok else 'TREND MISMATCH'} at this small N)")

        if all_match:
            verdict = f"q={q}: cell-for-cell MATCH with Z_p and W-11 at every tested N."
        elif first_divergence:
            Nd, sigma, eqv, zpv = first_divergence
            verdict = (f"q={q}: DIVERGES from Z_p at (N={Nd}, sigma={sigma}): "
                       f"equal-char count {eqv} vs Z_p count {zpv}"
                       f"{' (trend still consistent with the W-11 LIMIT)' if trend_ok else ' (trend ALSO mismatched)'}.")
        else:
            verdict = f"q={q}: inconclusive (no clean match, no clean first divergence found)."
        verdicts[q] = verdict
        print(f"    VERDICT: {verdict}")

    print()
    print("=" * 100)
    print("SUMMARY VERDICTS")
    for q in verdicts:
        print(f"  {verdicts[q]}")
    print("=" * 100)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
