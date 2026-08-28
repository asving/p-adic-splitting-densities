#!/usr/bin/env python3
"""C16--C19 certificates for unit MSF3 (2026-08-28).

The checks use exact arithmetic over Z/q^N and SymPy only for the displayed universal
polynomial identities.  They certify finite instances, not the general statements in the
proof document.

Run from the repository root:

    python3 verification/openmath/h116b4_msf3_cert.py
"""

from collections import Counter
import itertools
import os
import sys

import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(REPO, "runs", "wave-b"))

import h116b4_lift_cert as cert
import OM2_h116b_gauge_resultant as om


FAILED = []


def check(name, ok, detail=""):
    print(("  ok    " if ok else "  FAIL  ") + name + ((" -- " + detail) if detail else ""))
    if not ok:
        FAILED.append(name)


def span_set(basis, q, dim):
    return {
        tuple(sum(co[i] * basis[i][k] for i in range(len(basis))) % q
              for k in range(dim))
        for co in itertools.product(range(q), repeat=len(basis))
    }


def subgroup(values, q):
    if not values:
        return False
    z = tuple(0 for _ in next(iter(values)))
    return z in values and all(
        tuple((a + b) % q for a, b in zip(x, y)) in values
        for x in values for y in values
    )


def sample_evenly(xs, cap):
    xs = sorted(xs)
    if len(xs) <= cap:
        return xs
    return xs[::max(1, len(xs) // cap)][:cap]


def case_data(tag, q, children, r, x, depth):
    m = sum(mu for mu, _, _ in children) + r
    genre_precision = depth + 4
    modulus = q ** genre_precision
    F = cert.phi(x, q, modulus, children, r, m)
    levels = cert.tree_levels(q, depth, m, children, r, F)
    # Several intended genres are DRAIN only in the short j=3/4 window.  Classify the
    # exact target in a longer window so that the printed row records its actual genre.
    genre = om.genre_of([a % modulus for a in F] + [1], q, genre_precision)
    return {
        "tag": tag, "q": q, "children": children, "r": r, "x": x,
        "m": m, "s": m - r, "F": F, "levels": levels, "genre": genre,
    }


def tangent_flags(C, max_grade):
    q, m, s = C["q"], C["m"], C["s"]
    NB = max_grade + 5
    M = q ** NB
    fs = cert.factors_at(C["x"], q, M, C["children"], C["r"])
    T = cert.bat.sylvester_matrix(q, NB, m, C["children"], fs[:-1], C["r"], fs[-1])
    return NB, cert.smith_flag(T, q, NB, s, max_grade + 1)


def c16_mixed_flags(cases):
    """Required j=3,4 table, including q=2,3,5, legal genres, and illegal mu=1."""
    print("-- C16: mixed-secant flags at grades 3 and 4")
    rows = []
    all_legal_green = True
    illegal_pattern = True
    for C in cases:
        NB, (tes, tflags) = tangent_flags(C, 4)
        q = C["q"]
        for j in (3, 4):
            mem = sample_evenly(C["levels"].get(j, []), 256)
            mismatches = 0
            congruent = 0
            for y in mem:
                # Membership in S_j is checked independently before comparing flags.
                px = cert.phi(C["x"], q, q ** j, C["children"], C["r"], C["m"])
                py = cert.phi(y, q, q ** j, C["children"], C["r"], C["m"])
                congruent += px == py
                D = cert.secant_matrix(q, NB, C["m"], C["children"], C["r"], C["x"], y)
                _, dflags = cert.smith_flag(D, q, NB, C["s"], 5)
                mismatches += not cert.same_span(tflags[j - 1], dflags[j - 1], q)
            rows.append((C["tag"], j, len(mem), mismatches, tes, C["genre"]))
            if C["tag"].startswith("ILLEGAL"):
                illegal_pattern &= (mismatches == 0 if j == 3 else mismatches > 0)
            else:
                all_legal_green &= mismatches == 0
            check(f"(C16) secant pairs really lie in one S_{j} [{C['tag']}]",
                  congruent == len(mem), f"{congruent}/{len(mem)}")
    check("(C16a) no j=3,4 MSF mismatch in the sampled legal genre cells",
          all_legal_green)
    check("(C16b) illegal mu=1 first mismatch occurs at j=4, not j=3",
          illegal_pattern)
    for tag, j, count, bad, es, genre in rows:
        print(f"  table {tag}: j={j}, pairs={count}, mismatches={bad}, "
              f"tangent-es={es}, genre={genre}")


def c17_counterexamples():
    """Symbolic identities and exact mixed-flag counterexamples."""
    print("-- C17: constructed simultaneous-defeat equations")
    Y, p, t = sp.symbols("Y p t")
    illegal = sp.expand((Y + p ** 2 * t) * (Y - p ** 2 * t) - Y ** 2)
    legal = sp.expand((Y ** 2 + p ** 2 * t * Y + p ** 4 * t ** 2)
                      * (Y - p ** 2 * t) - Y ** 3)
    check("(C17) SymPy mu=1 factor-transfer identity", illegal == -p ** 4 * t ** 2,
          str(illegal))
    check("(C17) SymPy mu=2 factor-transfer identity", legal == -p ** 6 * t ** 3,
          str(legal))

    # Illegal mu=1: x=(Y,Y), y=(Y+p^2,Y-p^2), so Phi(x)-Phi(y)=p^4.
    q = 3
    C = case_data("ILLEGAL q3 mu1 collision", q, [(1, 1, 1)], 1, (0, -q), 5)
    x, y, j = C["x"], (q, -q - q ** 2), 4
    NB = 9
    fs = cert.factors_at(x, q, q ** NB, C["children"], 1)
    T = cert.bat.sylvester_matrix(q, NB, 2, C["children"], fs[:-1], 1, fs[-1])
    D = cert.secant_matrix(q, NB, 2, C["children"], 1, x, y)
    te, tf = cert.smith_flag(T, q, NB, 1, 6)
    de, df = cert.smith_flag(D, q, NB, 1, 6)
    diff = [(a - b) % q ** NB for a, b in
            zip(cert.phi(x, q, q ** NB, C["children"], 1, 2),
                cert.phi(y, q, q ** NB, C["children"], 1, 2))]
    check("(C17a) illegal mu=1 pair is one depth-4 secant", all(a % q ** 4 == 0 for a in diff),
          f"difference={diff}, es(T)={te}, es(D)={de}")
    check("(C17b) illegal mu=1 MSF fails at j=4",
          not cert.same_span(tf[j - 1], df[j - 1], q))

    # Legal frame mu=2, but deliberately colliding cofactor.  For t=1:
    # x=(b0,b1,a)=(0,0,-p), y=(p^2,p,-p-p^2).
    for q in (2, 3, 5):
        children = [(2, 1, 1)]
        x, y, j = (0, 0, -q), (q ** 2, q, -q - q ** 2), 6
        NB, M = 11, q ** 11
        fs = cert.factors_at(x, q, M, children, 1)
        T = cert.bat.sylvester_matrix(q, NB, 3, children, fs[:-1], 1, fs[-1])
        D = cert.secant_matrix(q, NB, 3, children, 1, x, y)
        te, tf = cert.smith_flag(T, q, NB, 2, 8)
        de, df = cert.smith_flag(D, q, NB, 2, 8)
        diff = [(a - b) % M for a, b in
                zip(cert.phi(x, q, M, children, 1, 3),
                    cert.phi(y, q, M, children, 1, 3))]
        target = [a % q ** 8 for a in cert.phi(x, q, q ** 8, children, 1, 3)] + [1]
        genre = om.genre_of(target, q, 8)
        check(f"(C17c) legal-mu raw pair has Phi(x)-Phi(y)=p^6 [{q=}]",
              diff[0] == q ** 6 and diff[1:] == [0, 0],
              f"difference={diff}; target-genre={genre}")
        check(f"(C17d) unrestricted MSF fails first at j=6 in this pair [{q=}]",
              all(cert.same_span(tf[k - 1], df[k - 1], q) for k in range(1, 6))
              and not cert.same_span(tf[j - 1], df[j - 1], q),
              f"es(T)={te}, es(D)={de}")


def c18_sr(cases):
    """Reverse-inclusion SR table: V_j(T_x) is compared with actual omega image."""
    print("-- C18: secant realization at grades 3 and 4")
    total_rows = 0
    for C in cases:
        q = C["q"]
        _, (_, tflags) = tangent_flags(C, 4)
        for j in (3, 4):
            mem = C["levels"].get(j, [])
            image = {cert.omega_of(y, C["F"], q, j, C["m"], C["s"],
                                   C["children"], C["r"]) for y in mem}
            Vj = span_set(tflags[j - 1], q, C["s"])
            ok = Vj <= image
            check(f"(C18) SR reverse inclusion V_{j}(T_x) <= image(omega_{j}) [{C['tag']}]",
                  ok, f"#S={len(mem)}, #V={len(Vj)}, #image={len(image)}")
            total_rows += 1
    print(f"  table C18 rows={total_rows} (all fibre members used; no y-sampling)")


def translation_action(C, n, delta):
    q = C["q"]
    mem = C["levels"][n]
    S = set(mem)
    omega = {z: cert.omega_of(z, C["F"], q, n, C["m"], C["s"],
                              C["children"], C["r"]) for z in mem}
    shift = None
    for z in mem:
        zz = tuple((z[i] + delta[i]) % q ** n for i in range(C["m"]))
        if zz not in S:
            return False, None
        dz = tuple((omega[zz][i] - omega[z][i]) % q for i in range(C["s"]))
        if shift is None:
            shift = dz
        elif shift != dz:
            return False, None
    return True, shift


def c19_pairing_wash(deep_cases):
    """n=5,6 uniformity and explicit grade-shift translations in a genre family."""
    print("-- C19: grade-shift pairing and WASH at n=5,6")
    for C in deep_cases:
        q = C["q"]
        for n in (5, 6):
            mem = C["levels"][n]
            hist = Counter(cert.omega_of(y, C["F"], q, n, C["m"], C["s"],
                                         C["children"], C["r"]) for y in mem)
            image = set(hist)
            uniform = len(set(hist.values())) == 1
            check(f"(C19) U({n}|F) and subgroup image in the separated mu=2 cell [{C['tag']}]",
                  uniform and subgroup(image, q),
                  f"#S={len(mem)}, #image={len(image)}, fibre={sorted(set(hist.values()))}")

            # In Y=X-p coordinates and Q_x=Y-p, these are the two exact translations
            # used in the proof: the X-direction bottom-column washer and the coupled
            # constant-direction grade-shift washer.
            dx = (q ** (n - 2), 0, 0)
            dc = (q ** (n - 3), q ** (n - 3), -q ** (n - 2))
            okx, sx = translation_action(C, n, dx)
            okc, sc = translation_action(C, n, dc)
            independent = cert.rank_modq([sx, sc], q) == 2 if okx and okc else False
            check(f"(C19b) two commuting digit translations pair every omega fibre [{C['tag']}, n={n}]",
                  okx and okc and independent, f"shifts={sx},{sc}")


def main():
    print("h116b4_msf3_cert -- MSF/SR/pairing certificates (2026-08-28)")
    cases = [
        case_data("q2 mu2 k1 r1", 2, [(2, 1, 1)], 1, (0, 0, -4), 4),
        case_data("q3 mu2 k1 r1", 3, [(2, 1, 1)], 1, (0, 0, -6), 4),
        case_data("q5 mu2 k1 r1", 5, [(2, 1, 1)], 1, (0, 0, -10), 4),
        case_data("q3 two slope1 children r0", 3,
                  [(2, 1, 1), (2, 1, 2)], 0, (0, 0, 0, 0), 4),
        case_data("q3 mu3 k1 r1", 3, [(3, 1, 1)], 1, (0, 0, 0, -6), 4),
        case_data("q3 mu2 k2 r1", 3, [(2, 2, 1)], 1, (0, 0, -3), 4),
        case_data("q3 mu2 k1 r2", 3, [(2, 1, 1)], 2, (0, 0, 3, 0), 4),
        case_data("ILLEGAL q3 mu1 collision", 3, [(1, 1, 1)], 1, (0, -3), 4),
    ]
    c16_mixed_flags(cases)
    c17_counterexamples()
    c18_sr(cases)

    deep = [
        case_data("q2 mu2 k1 r1", 2, [(2, 1, 1)], 1, (0, 0, -4), 6),
        case_data("q3 mu2 k1 r1", 3, [(2, 1, 1)], 1, (0, 0, -6), 6),
        case_data("q5 mu2 k1 r1", 5, [(2, 1, 1)], 1, (0, 0, -10), 6),
    ]
    c19_pairing_wash(deep)
    print()
    print(f"==== {len(FAILED)} FAILED ====" if FAILED else "==== ALL CHECKS PASSED ====")
    return 1 if FAILED else 0


if __name__ == "__main__":
    raise SystemExit(main())
