#!/usr/bin/env python3
"""O-11 rev-2 SUPPLEMENT: pin the V2 oracle identity as RATIONAL FUNCTIONS.

Pass-1 finding G-8 (`O11_pass1_verify.md`): the run-3/run-4 harness
(`o11_seriestie_check.py`, sealed, byte-stable since commit 3fc8f52)
establishes alpha_full(3) == true3 symbolically, where true3 is an
IN-HARNESS transcription of `padic_types.monic_cubic_pred`, and checks the
ACTUAL oracle only numerically at p in {2, 3, 5, 7} -- four points do not
pin a rational function, so the executed test was strictly weaker than the
sealed docstring ("alpha_full(3) == monic_cubic_pred identically") unless
the transcription is trusted.

THIS script closes that gap WITHOUT touching the sealed harness: for each
of the five cubic types it verifies

    alpha_full(3)[t] (q = k)  ==  monic_cubic_pred(k)[t]   EXACTLY

(sympy Rational vs Fraction) at every integer k = 2..45 (44 sample points).

Why 44 points suffice (the degree-bound argument, displayed):
  * Engine side: write alpha_full(3)[t] = N(q)/D(q) via sympy cancel/
    fraction; deg N and deg D are COMPUTED and printed per type.
  * Oracle side: by inspection of `padic_types.monic_cubic_pred` (five
    literal closed-form entries over d = q^5 - 1), every entry is
    P(q)/Q(q) with deg P <= 7 and deg Q <= 6.
  * Agreement at k with D(k) != 0, Q(k) != 0 means the polynomial
    N*Q - P*D (degree <= B := max(deg N + 6, 7 + deg D)) vanishes at k.
    If it vanishes at MORE than B points it is identically zero, i.e. the
    two rational functions are EQUAL.  The script asserts #points > B per
    type, and every k >= 2 avoids the poles (q = -1, q^5 = 1; nonvanishing
    of D(k), Q(k) is implied by the exact evaluations succeeding).
So ALL PASS here == the sealed V2 identity holds AT THE ORACLE ITSELF, and
the harness transcription true3 is verified a posteriori.

Run:  uv run --with sympy python o11_v2_oracle_pin.py
Exit nonzero on any FAIL.
"""
import sys

sys.path.insert(0, __file__.rsplit('/', 2)[0])  # verification/ on path

import sympy as sp                              # noqa: E402
import om_density_engine as e                   # noqa: E402
import padic_types as pt                        # noqa: E402

ORACLE_DEG_NUM = 7   # by inspection of padic_types.monic_cubic_pred
ORACLE_DEG_DEN = 6
POINTS = list(range(2, 46))                     # 44 points, all >= 2

FAILS = []


def report(name, ok, detail=""):
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")
    if not ok:
        FAILS.append(name)


def main():
    a3 = {e.CODE_N3[t]: sp.cancel(sp.simplify(v))
          for t, v in e.alpha_full(3).items()}
    q = e.q
    for t, expr in a3.items():
        N, D = sp.fraction(expr)
        degN, degD = sp.degree(N, q), sp.degree(D, q)
        B = max(degN + ORACLE_DEG_DEN, ORACLE_DEG_NUM + degD)
        report(f"pin {t} degree budget", len(POINTS) > B,
               f"deg N={degN}, deg D={degD}, bound B={B}, points={len(POINTS)}")
        bad = []
        for k in POINTS:
            engine_val = sp.Rational(expr.subs(q, sp.Integer(k)))
            oracle_val = pt.monic_cubic_pred(k)[t]
            if engine_val != sp.Rational(oracle_val.numerator,
                                         oracle_val.denominator):
                bad.append(k)
        report(f"pin {t} exact at {len(POINTS)} points", not bad,
               f"mismatches at {bad}" if bad else "all exact")
    print(f"\n{'ALL PASS' if not FAILS else 'FAILURES: ' + ', '.join(FAILS)}")
    return 1 if FAILS else 0


if __name__ == '__main__':
    sys.exit(main())
