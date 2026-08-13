#!/usr/bin/env python3
"""T1 GAUGE-COCYCLE §4.2 MACHINE BATTERY RE-RUN — checks 1..10 against the
CURRENT effective text (base + r1..r13 + the 2026-08-13 post-pass riders).

SCOPE.  This runner scores the TEN numbered checks of §4.2 in their EFFECTIVE
form:
    1..5  base §4.2, unamended
    6     base, REPLACED by R4-3 (self-excluding weld lint)
    7,8   appended by r8 (R8-1 / R8-2)
    9     appended by r11 (R11-1)
    10    appended by r13 (R13-8(iii)), PLUS post-pass Rider 5 which gives it
          its self-exclusion and its scoring scope.

REUSE.  Exact finite-field / frame / stage / C4 / C5 / C6 machinery is imported
UNMODIFIED from the sealed instrument
    verification/openmath/t1_gauge_battery.py
(the 213-row re-seal that ran GREEN at the r1/r2 state, artifact
runs/comp1/t1_battery_results.json).  Nothing in that file is edited; this
runner only imports it.  All arithmetic here is exact (int / Fraction /
finite-field), plus one independent non-textual PARI leg for check 10.

HONESTY.  A FAIL is reported, never repaired.  Where the effective text admits
two readings, BOTH are scored and the ambiguity is reported.
"""

from __future__ import annotations

import bisect
import importlib.util
import re
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

REPO = Path("/data/users/asvin/math-and-lean/p-adic-splitting-densities")
NOTE = REPO / "lean/notes/openmath/T1_GAUGE_COCYCLE_2026-08-12.md"
SEALED = REPO / "verification/openmath/t1_gauge_battery.py"
GENTOW2 = REPO / "lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md"

# ---------------------------------------------------------------- import the sealed machinery
_spec = importlib.util.spec_from_file_location("t1_sealed", SEALED)
T = importlib.util.module_from_spec(_spec)
sys.modules["t1_sealed"] = T
_spec.loader.exec_module(T)

F2, F3, F4, F5, F7 = T.F2, T.F3, T.F4, T.F5, T.F7
W = T.OMEGA            # omega, generator of F4^*
W2 = W * W
FRAME = T.FRAME_BY_NAME
STAGE = T.STAGE_BY_NAME
Frame = T.Frame

# ---------------------------------------------------------------- reporting
ROWS = []          # (check, name, got, want, ok)
AMBIG_ROWS = []    # (check, name, got, want, ok) — reported, NOT in verdicts
LOG = []


def say(s=""):
    LOG.append(str(s))
    print(s, flush=True)


def chk(check, name, got, want=True, note=""):
    ok = (got == want)
    ROWS.append((check, name, got, want, ok))
    tag = "ok  " if ok else "FAIL"
    extra = f"   [{note}]" if note else ""
    say(f"  {tag} C{check:<2} {name:<52} got={_s(got)}  want={_s(want)}{extra}")
    return ok


def ambig(check, name, got, want=True):
    ok = (got == want)
    AMBIG_ROWS.append((check, name, got, want, ok))
    say(f"  {'ok  ' if ok else 'AMBG'} C{str(check):<2} {name:<52} "
        f"got={_s(got)}  want={_s(want)}   [alternate reading; not scored "
        f"into the verdict]")
    return ok


def _s(v):
    if isinstance(v, T.FE):
        return _fe(v)
    if isinstance(v, (list, tuple)):
        return "[" + ",".join(_s(x) for x in v) + "]"
    return str(v)


def _fe(e):
    """Readable F4/F_p element."""
    if e.field is F4:
        return {(0, 0): "0", (1, 0): "1", (0, 1): "w", (1, 1): "w2"}[e.coeffs]
    return str(e.coeffs[0])


def poly_s(p):
    return "[" + ", ".join(_fe(c) for c in p) + "]"


def head(n, title):
    say("")
    say("=" * 78)
    say(f"CHECK {n} — {title}")
    say("=" * 78)


NOTE_TEXT = NOTE.read_text(encoding="utf-8")
NOTE_LINES = NOTE_TEXT.split("\n")
_OFFS = []
_o = 0
for _L in NOTE_LINES:
    _OFFS.append(_o)
    _o += len(_L) + 1


def lineno(pos):
    return bisect.bisect_right(_OFFS, pos)


# ================================================================ CHECK 1
def check1():
    head(1, "GENHN-LIFT boundary (integrality / degree / height / residue; "
            "f1>=2; low-height counterexample)")
    f4 = FRAME["F4"]        # e1=2, f1=2, h=1, eta=w, D'=4  -> f1>=2 leg
    p3 = FRAME["P3_WRAP"]   # e1=2, f1=1, h=1
    p5 = FRAME["P5"]        # e1=3, f1=1, h=2
    lp = FRAME["LP"]        # e1=5, f1=1, h=2

    live = []
    for M in range(5, 16):                       # M > D'h = 4, f1 = 2
        for lam in ([1, 0], [0, 1], [1, 1]):
            live.append((f"F4_M{M}_{''.join(map(str,lam))}", f4, M, lam))
    for M in range(3, 9):                        # P3: D'h = 2
        live.append((f"P3_M{M}", p3, M, [2]))
    for M in range(7, 13):                       # P5: D'=3, h=2 -> D'h = 6
        live.append((f"P5_M{M}", p5, M, [3]))
    for M in range(11, 16):                      # LP: D'=5, h=2 -> D'h = 10
        live.append((f"LP_M{M}", lp, M, [3]))

    say(f"  live cases: {len(live)} (frames F4[f1=2], P3, P5, LP)")
    nf1ge2 = 0
    for name, fr, M, lam in live:
        terms = T.lift_terms(fr, M, lam)
        if fr.f1 >= 2:
            nf1ge2 += 1
        chk(1, f"{name}.live_domain", T.lift_domain(fr, M))
        chk(1, f"{name}.integral", all(t.pi_exponent >= 0 for t in terms))
        chk(1, f"{name}.degree_lt_Dprime",
            max(t.x_exponent for t in terms) < fr.D)
        chk(1, f"{name}.exact_height",
            all(fr.e1 * t.pi_exponent + fr.h * t.x_exponent == M
                for t in terms))
        chk(1, f"{name}.residue", T.lift_residue(fr, terms),
            T.lambda_value(fr, lam))
        chk(1, f"{name}.xfree_criterion", T.actual_xfree_monomial(terms),
            T.predicted_xfree(fr, M, lam))
    chk(1, "coverage.f1_ge_2_cases_present", nf1ge2 >= 1,
        note=f"{nf1ge2} cases with f1>=2")

    # low-height counterexample (e1,f1,h,M) = (1,2,1,0)
    low = Frame("LOW_1_2_1", F4, 1, 2, 1, W, 1)
    say(f"  low counterexample frame: e1={low.e1} f1={low.f1} h={low.h} "
        f"D'={low.D} D'h={low.D*low.h}, M=0")
    chk(1, "low.M_not_in_live_domain", T.lift_domain(low, 0), False)
    # n(M) itself IS integral at M = 0:  i(0)=0, a(0)=0, n(0) = x^0 pi^0 = 1
    i0, a0 = low.i(0), low.a(0)
    chk(1, "low.n_of_M_is_integral", (i0, a0), (0, 0),
        note="n(0)=x^0 pi^0 = 1, integral")
    # but the eta-slot of a full K1-slot is NOT integral
    low_terms = T.lift_terms(low, 0, [0, 1])
    negs = [(t.x_exponent, t.pi_exponent) for t in low_terms
            if t.pi_exponent < 0]
    chk(1, "low.full_slot_refused_nonintegral", bool(negs), True,
        note=f"eta-slot (x^e,pi^e)={negs}")
    chk(1, "low.no_full_K1_slot_inferred_from_n_integrality",
        (T.lift_domain(low, 0) is False) and bool(negs), True)
    # boundary M = D'h exactly, and just below, on the f1=2 frame
    for nm, M in (("boundary_eq", 4), ("boundary_below", 3)):
        chk(1, f"F4.{nm}.refused", T.lift_domain(f4, M), False)


# ================================================================ CHECK 2
def check2():
    head(2, "Positive-wrap sign (corrected/naive + wrong-sign teeth; "
            "EXACT coefficient equality)")
    # (a) the wrap exponent is the displayed POSITIVE floor, verified from the
    #     (C2-wrap) monomial bookkeeping and not from the formula alone.
    for fr in T.FRAMES:
        for s in range(0, 7):
            iu = fr.i(fr.u2)
            Wexp = (s * iu) // fr.e1
            # n1(m) = x^{i(m)} pi^{(m - i(m) h)/e1}; compare n1(u2)^s / n1(s u2)
            xs = s * fr.i(fr.u2) - fr.i(s * fr.u2)
            ps = s * fr.a(fr.u2) - fr.a(s * fr.u2)
            chk(2, f"{fr.name}.wrap_monomial_s{s}", (xs, ps),
                (fr.e1 * Wexp, -fr.h * Wexp))
            chk(2, f"{fr.name}.theta_positive_exponent_s{s}",
                fr.theta(s), fr.eta ** Wexp)
            chk(2, f"{fr.name}.wrap_exponent_nonneg_s{s}", Wexp >= 0)

    # (b) corrected vs naive vs wrong-sign, EXACT coefficients.
    #     CONVENTION (matters): a MUTATED coherent digit is read back against
    #     the TRUE telescope -- that is what makes the mutation observable.
    for sname in ("X", "F4Q", "F4MU3", "P5"):
        st = STAGE[sname]
        th = T.stage_theta(st)
        gam = T.stage_gamma(st)
        corr = T.psi_from_c(st.frame.field, st.f2,
                            T.stage_multiplicative(st, gam, th))
        naive = T.psi_from_c(
            st.frame.field, st.f2,
            T.stage_multiplicative(st, T.stage_gamma(st, "gauge_naive"), th))
        ws = T.psi_from_c(
            st.frame.field, st.f2,
            T.stage_multiplicative(st, T.stage_gamma(st, "wrong_sign"), th))
        say(f"  stage {sname}: eta={_fe(st.frame.eta)} "
            f"ord(eta)={_ord(st.frame.eta)} "
            f"theta={[_fe(v) for v in th]}")
        say(f"      corr={poly_s(corr)}  naive={poly_s(naive)}  "
            f"wrong-sign={poly_s(ws)}")
        # the (C3) claim itself: the corrected multiplicative coefficient is
        # exactly c_t (no residual gauge factor)
        mult = T.stage_multiplicative(st, gam, th)
        chk(2, f"{sname}.corrected_mult_equals_c_exactly",
            [_fe(mult[t]) for t in range(st.f2)],
            [_fe(st.c[t]) for t in range(st.f2)])
        chk(2, f"{sname}.corr_ne_naive_coefficientwise", corr != naive)
        if _ord(st.frame.eta) > 2:
            chk(2, f"{sname}.corr_ne_wrongsign_coefficientwise", corr != ws)
        else:
            chk(2, f"{sname}.wrongsign_invisible_ord_eta_2", corr == ws, True,
                note="eta^2=1 makes the sign flip a no-op on this frame")

    # (c) the sigma-blind wrong-sign tooth at F4Q (the note's registered leg):
    #     SAME factor pattern, DIFFERENT coefficients.
    st = STAGE["F4Q"]
    th = T.stage_theta(st)
    gam = T.stage_gamma(st)
    corr = T.psi_from_c(F4, 2, T.stage_multiplicative(st, gam, th))
    ws = T.psi_from_c(F4, 2, T.stage_multiplicative(
        st, T.stage_gamma(st, "wrong_sign"), th))
    naive = T.psi_from_c(F4, 2, T.stage_multiplicative(
        st, T.stage_gamma(st, "gauge_naive"), th))
    say(f"  F4Q factor degrees: corr={T.factor_degrees(corr)} "
        f"wrong-sign={T.factor_degrees(ws)} naive={T.factor_degrees(naive)}")
    chk(2, "F4Q.wrongsign_same_factor_pattern",
        T.factor_degrees(ws), T.factor_degrees(corr))
    chk(2, "F4Q.wrongsign_caught_only_by_exact_coeffs", ws != corr)
    chk(2, "F4Q.naive_splits_corr_irreducible",
        (T.factor_degrees(naive), T.factor_degrees(corr)), ([1, 1], [2]))
    # note-registered exact values (§4.1 / T-2 header)
    chk(2, "F4Q.corrected_is_y2_y_omega", corr, [W, F4(1), F4(1)])
    chk(2, "F4Q.naive_is_y2_y_1", naive, [F4(1), F4(1), F4(1)])
    chk(2, "F4Q.wrongsign_is_y2_y_omega2", ws, [W2, F4(1), F4(1)])
    chk(2, "F4Q.corrected_digits_1_w2",
        [_fe(gam[t]) for t in (1, 0)], ["1", "w2"])
    chk(2, "F4Q.naive_digits_1_w",
        [_fe(T.stage_gamma(st, "gauge_naive")[t]) for t in (1, 0)],
        ["1", "w"])
    chk(2, "F4Q.wrongsign_digit_becomes_1",
        _fe(T.stage_gamma(st, "wrong_sign")[0]), "1")
    # §4.1's CORRECTED F4-JOINT display value (the sealed run's one RED row)
    psi_w = T.twisted_poly(corr, st.w)
    say(f"  F4-JOINT psi^(w), w=omega:  w^f psi(y/w) = {poly_s(psi_w)}")
    chk(2, "F4JOINT.psi_w_is_y2_omega_y_1", psi_w, [F4(1), W, F4(1)],
        note="note §4.1 corrected value y^2 + omega y + 1")
    chk(2, "F4JOINT.psi_w_preserves_factor_pattern",
        T.factor_degrees(psi_w), T.factor_degrees(corr))


def _ord(e):
    n, x = 1, e
    while x != e.field.one:
        x = x * e
        n += 1
    return n


# ================================================================ CHECK 3
def check3():
    head(3, "JA origin (nu=0; nu>0 with z^nu != 1; ROOT-OF-UNITY nu>0 with "
            "z^nu = 1; support/degree translation)")
    # tuple layout as consumed by the sealed instrument's battery_c4:
    #   (name, field, z, ell, e, nu, support), with beta swept (sealed: 5).
    seen_root = 0
    for name, field, z, ell, e, nu, supp in T.C4_CASES:
        for beta in (5, 1, 2, 3, 4, 7, 11):
            d = T.c4_data(field, z, ell, beta, e, nu, supp)
            raw, eps, znu = d["raw"], d["epsilon"], d["znu"]
            tag = f"{name}.b{beta}"
            if beta == 5:
                say(f"  {name}: z={_fe(z)} ell={ell} e={e} nu={nu} "
                    f"z^nu={_fe(znu)} raw={_fe(raw)} eps={_fe(eps)} "
                    f"supp(P)={d['p_support']} supp(H)={d['h_support']}")
            chk(3, f"{tag}.origin_identity", raw, znu * eps)   # (C4-origin)
            chk(3, f"{tag}.raw_equality_iff_znu_1",
                raw == eps, znu == field.one)
            chk(3, f"{tag}.tDef_formula", d["t_def"], nu - d["t_min"])
            if nu == 0:
                chk(3, f"{tag}.nu0_raw_equals_canonical", raw, eps)
            elif znu == field.one:
                if beta == 5:
                    seen_root += 1
                chk(3, f"{tag}.rootofunity_nu_pos_raw_still_equal", raw, eps,
                    note="refutes 'iff nu=0'")
            else:
                chk(3, f"{tag}.nonroot_fails_by_exactly_znu", raw / eps, znu)
                chk(3, f"{tag}.nonroot_raw_ne_eps", raw != eps)
            chk(3, f"{tag}.support_translation", d["h_support"],
                [nu + x for x in d["p_support"]])
            chk(3, f"{tag}.degree_translation",
                max(d["h_support"]), max(d["p_support"]) + nu)
    chk(3, "coverage.root_of_unity_nu_pos_case_present", seen_root >= 1,
        note=f"{seen_root} such frames")
    # the two JA teeth must fire
    nm, field, z, ell, e, nu, supp = [c for c in T.C4_CASES
                                      if c[0] == "nu2_nonroot"][0]
    d = T.c4_data(field, z, ell, 5, e, nu, supp)
    chk(3, "tooth.origin_drop_nu_fires", d["raw"] == d["epsilon"], False,
        note="dropping z^nu would identify them")
    nm2, f2f, z2, ell2, e2, nu2, sup2 = [c for c in T.C4_CASES
                                         if c[0] == "nu2_root"][0]
    d2 = T.c4_data(f2f, z2, ell2, 5, e2, nu2, sup2)
    chk(3, "tooth.origin_iff_nu0_fires",
        (d2["raw"] == d2["epsilon"], nu2 == 0), (True, False),
        note="raw equality holds although nu>0")


# ================================================================ CHECK 4
def check4():
    head(4, "HE6 coefficient normalization ((C5-normalizer-read), "
            "(C5-varpi-read), the -q(k) sign)")
    for case in T.C5_CASES:
        fr = case.frame
        k = case.k
        i = fr.i(k)
        bares = {t.j: (t.unit if t.valuation == 0 else fr.field.zero)
                 for t in case.terms}
        norm = T.gamma_k(case)
        bare = T.gamma_k(case, bare=True)
        direct = T.direct_normalizer_read(case)
        say(f"  C5 case {case.name}: k={k} i(k)={i} "
            f"terms={[(t.j, t.valuation, _fe(t.unit)) for t in case.terms]}")
        say(f"      bare res(a_j) = {[(j, _fe(v)) for j, v in bares.items()]} "
            f"-> gamma_bare={_fe(bare)};  normalized gamma_k={_fe(norm)}")
        if case.name == "A":
            chk(4, "A.all_bare_residues_zero",
                all(not v for v in bares.values()), True)
            chk(4, "A.normalized_residues_nonzero", bool(norm), True)
            chk(4, "A.bare_read_is_wrong", bare != norm)
            chk(4, "A.gamma_value", norm, W)
        chk(4, f"{case.name}.C5_normalizer_read", direct, norm)

    # the -q(k) sign, derived from the monomial exponents (not restated)
    fr = FRAME["F4"]
    for k in range(1, 13):
        q = fr.q(k)
        i = fr.i(k)
        i0 = fr.inv_h
        # n(k) / varpi^k  = x^{i - i0 k} pi^{(k-ih)/e1 - k(1-i0 h)/e1}
        xexp = i - i0 * k
        pexp = Fraction(k - i * fr.h, fr.e1) - Fraction(k * (1 - i0 * fr.h),
                                                        fr.e1)
        chk(4, f"varpi.exponents_k{k}", (xexp, pexp),
            (-fr.e1 * q, Fraction(fr.h * q)))
        # the monomial x^xexp pi^pexp is a POWER of x^{e1}/pi^h, exponent -q,
        # so its residue is eta^{-q}: read the residue off the exponents, do
        # not restate the formula.
        chk(4, f"varpi.monomial_is_power_of_grid_k{k}",
            (xexp % fr.e1 == 0, pexp == Fraction(-fr.h * (xexp // fr.e1))),
            (True, True))
        chk(4, f"varpi.residue_from_exponents_k{k}",
            fr.eta ** (xexp // fr.e1), fr.eta ** (-q))
        # sign tooth: eta^{+q} differs whenever eta^{2q} != 1
        if fr.eta ** (2 * q) != fr.field.one:
            chk(4, f"varpi.sign_tooth_k{k}", fr.eta ** (-q) != fr.eta ** q)
    # (C5-varpi-read) composite on case A, against hand-computed constants
    caseA = T.C5_BY_NAME["A"]
    q5 = fr.q(caseA.k)
    chk(4, "A.q_of_k_is_2", q5, 2, note="q(5) = (1*5 - 1)/2 = 2")
    chk(4, "A.eta_to_minus_q", _fe(fr.eta ** (-q5)), "w")
    chk(4, "A.varpi_read_composite",
        _fe(T.gamma_k(caseA) * fr.eta ** (-q5)), "w2",
        note="gamma_5 * eta^-2 = w * w = w2")
    chk(4, "A.varpi_read_wrong_sign_value",
        _fe(T.gamma_k(caseA) * fr.eta ** q5), "1",
        note="gamma_5 * eta^+2 = w * w2 = 1 -- differs")
    chk(4, "A.varpi_read_sign_matters",
        T.gamma_k(caseA) * fr.eta ** (-q5) != T.gamma_k(caseA) * fr.eta ** q5)
    # (C5-carry)
    bad = [(a, b) for a in range(0, 14) for b in range(0, 14)
           if fr.q(a + b) != fr.q(a) + fr.q(b) + fr.wrap(a, b)]
    chk(4, "C5_carry_identity_0_13", bad, [])


# ================================================================ CHECK 5
def check5():
    head(5, "Full orientation tooth (Theta := vartheta) — ALL THREE entries of "
            "the canonical mu=3 vector")
    st = STAGE["F4MU3"]
    th = T.stage_theta(st)
    gam = T.stage_gamma(st)
    say(f"  vartheta_(0..3) = {[_fe(v) for v in th]}   (note: (1,1,w,w))")
    say(f"  coherent digits (Gamma_2,Gamma_1,Gamma_0) = "
        f"{[_fe(gam[t]) for t in (2,1,0)]}   (note: (1,w,w))")
    chk(5, "vartheta_vector", [_fe(v) for v in th], ["1", "1", "w", "w"])
    chk(5, "coherent_digits", [_fe(gam[t]) for t in (2, 1, 0)],
        ["1", "w", "w"])

    good = T.stage_canonical_slots(st, gam, th, inverse_orientation=True)
    bad = T.stage_canonical_slots(st, gam, th, inverse_orientation=False)
    # B-units u(beta_t) = Theta(t) w^{f-t}
    ug = {t: (th[st.f2 - t].inverse()) * (st.w ** (st.f2 - t)) for t in range(3)}
    ub = {t: (th[st.f2 - t]) * (st.w ** (st.f2 - t)) for t in range(3)}
    say(f"  B-units (u(b2),u(b1),u(b0))  correct = "
        f"{[_fe(ug[t]) for t in (2,1,0)]}   (note: (w,w,w2))")
    say(f"  B-units (u(b2),u(b1),u(b0))  Theta=vartheta = "
        f"{[_fe(ub[t]) for t in (2,1,0)]}")
    say(f"  canonical vector (t=2,1,0)   correct = "
        f"{[_fe(good[t]) for t in (2,1,0)]}   (note: (w,w2,1))")
    say(f"  canonical vector (t=2,1,0)   Theta=vartheta = "
        f"{[_fe(bad[t]) for t in (2,1,0)]}")

    chk(5, "Bunits_all_three_correct", [_fe(ug[t]) for t in (2, 1, 0)],
        ["w", "w", "w2"])
    chk(5, "canonical_vector_all_three_correct",
        [_fe(good[t]) for t in (2, 1, 0)], ["w", "w2", "1"])
    pol = T.canonical_poly_from_slots(st, good)
    chk(5, "canonical_polynomial", poly_s(pol), poly_s([F4(1), W2, W, F4(1)]))
    cube = T.p_mul(T.p_mul([W, F4(1)], [W, F4(1)]), [W, F4(1)])
    chk(5, "canonical_is_y_plus_omega_cubed", pol, cube)
    # the note's third identity: canonical = w^3 psi(y/w)
    mult = T.psi_from_c(F4, 3, T.stage_multiplicative(st, gam, th))
    chk(5, "canonical_equals_w3_psi_y_over_w", T.twisted_poly(mult, st.w), pol)

    # score EACH of the three slots under the tooth (not only the s=2 B-unit)
    scored = 0
    for t in (2, 1, 0):
        differs = (good[t] != bad[t])
        scored += 1
        chk(5, f"tooth.slot_t{t}_scored", True)
        if t == 2:
            chk(5, "tooth.slot_t2_control_survives", differs, False,
                note="vartheta_1 = 1")
        else:
            chk(5, f"tooth.slot_t{t}_breaks", differs, True)
    chk(5, "tooth.all_three_slots_scored", scored, 3)
    chk(5, "tooth.fires_on_full_vector",
        [_fe(bad[t]) for t in (2, 1, 0)] != [_fe(good[t]) for t in (2, 1, 0)])


# ================================================================ CHECK 6
def check6():
    head(6, "Weld scope lint (R4-3 effective form: self-excluding, "
            "quotation-excluding, negation-excluding)")
    pats = {
        "one_transport_map": re.compile(r"\bone\s+transport\s+map\b", re.I),
        "unique_gauge": re.compile(r"\bunique\s+gauge\b", re.I),
    }
    NEG = (" no ", " not ", "neither", "does not", "proves no", "without",
           "cannot", "is not", "nor ", "withdrew", "withdrawn", "never",
           "no universal", "none")
    # R4-3's own lint specification block, plus the base check-6 line it replaces
    SPEC_RANGES = [(1176, 1192), (2366, 2382)]

    def in_spec(ln):
        return any(a <= ln <= b for a, b in SPEC_RANGES)

    def quoted(line, m):
        seg = line[:m.start()]
        # a rejected formulation quoted inside typographic or ASCII quotes
        return (seg.count("\u201c") > seg.count("\u201d")
                or seg.count('"') % 2 == 1
                or "rejected" in line.lower()
                or "quotation" in line.lower())

    def negated(line, m):
        low = " " + line.lower() + " "
        return any(tok in low for tok in NEG)

    mrx = re.compile(r"\bM[0-4]\b")
    crx = re.compile(r"compatib|coheren|commut|cross-face", re.I)

    def run_lint(lines, verbose=False):
        """Returns (literal_hits, compat_hits) surviving all three exclusions."""
        lit, comp = [], []
        for pname, rx in pats.items():
            for ln, line in enumerate(lines, 1):
                for m in rx.finditer(line):
                    why = ("spec" if in_spec(ln) else
                           "quoted-rejected" if quoted(line, m) else
                           "negation-scope" if negated(line, m) else None)
                    if verbose:
                        say(f"    match {pname} @L{ln}: "
                            f"{'EXCLUDED('+why+')' if why else 'LIVE'}  "
                            f"| {line.strip()[:110]}")
                    if why is None:
                        lit.append((pname, ln, line.strip()[:150]))
        for ln, line in enumerate(lines, 1):
            if in_spec(ln):
                continue
            if len(set(mrx.findall(line))) >= 2 and crx.search(line):
                if not negated(line, None):
                    comp.append((ln, line.strip()[:150]))
        return lit, comp

    lit, comp = run_lint(NOTE_LINES, verbose=True)
    say(f"  unexcluded literal-pattern hits: {len(lit)}; "
        f"M-field compatibility hits: {len(comp)}")
    for ln, s in comp:
        say(f"    M-field compatibility candidate @L{ln}: {s}")
    chk(6, "lint.no_live_one_transport_map",
        [u for u in lit if u[0] == "one_transport_map"], [])
    chk(6, "lint.no_live_unique_gauge",
        [u for u in lit if u[0] == "unique_gauge"], [])
    chk(6, "lint.no_affirmative_M_field_compatibility", comp, [])

    # MUTATION TEETH: a lint that cannot fail is worthless.
    mut1 = list(NOTE_LINES) + [
        "T1 proves one transport map across all five package fields.",
        "The gauge is a unique gauge determined by the telescope.",
        "The fields M1 and M3 satisfy a compatibility relation.",
    ]
    l1, c1 = run_lint(mut1)
    chk(6, "tooth.weld_single_map_fires",
        sorted({p for p, _, _ in l1}),
        ["one_transport_map", "unique_gauge"])
    chk(6, "tooth.weld_affirmative_compatibility_fires", len(c1) >= 1, True)
    # negated / quoted forms must remain nonmatches (no false positives)
    mut2 = list(NOTE_LINES) + [
        "T1 proves no one transport map and asserts no unique gauge.",
        "The rejected formulation “one transport map” is not adopted.",
    ]
    l2, _ = run_lint(mut2)
    chk(6, "tooth.negated_and_quoted_forms_stay_nonmatches", l2, [])

    # M3 / M4 fences, on the EFFECTIVE rows
    m3_eff = NOTE_LINES[3635]     # r10 supersession, 1-indexed L3636
    m4_eff = NOTE_LINES[1998]     # r2 replacement,   1-indexed L1999
    m4_base = NOTE_LINES[744]     # base row,         1-indexed L745
    say(f"  effective M3 row (L3636): {m3_eff.strip()[:150]}")
    say(f"  effective M4 row (L1999): {m4_eff.strip()[:150]}")
    chk(6, "lint.M3_effective_row_is_M3", m3_eff.strip().startswith("| \\(M3\\)"))
    chk(6, "lint.M3_scored_stratum_fence",
        "scored stratum" in m3_eff)
    chk(6, "lint.M4_effective_row_is_M4", m4_eff.strip().startswith("| \\(M4\\)"))
    chk(6, "lint.M4_W2C3_accepted_fence",
        "W2-C3" in m4_eff and "accepted fence" in m4_eff)
    chk(6, "lint.M4_base_row_also_fenced",
        "W2-C3" in m4_base and "accepted fence" in m4_base)
    # every OTHER M3 / M4 mention is prose about the rows, not a fresh use
    others = [ln for ln, line in enumerate(NOTE_LINES, 1)
              if re.search(r"\\\(M[34]\\\)|\bM[34]\b", line)
              and ln not in (745, 1999, 3636, 734, 735)]
    say(f"  other M3/M4 mentions at lines: {others}")
    chk(6, "lint.M3_M4_uses_enumerated", len(others) >= 1)
    # the boxed no-cross-face fence is present
    chk(6, "lint.no_cross_face_fence_present",
        "it proves no cross-face coherence theorem." in NOTE_TEXT)
    chk(6, "lint.gauge_uniqueness_withdrawn",
        "It also proves no uniqueness of the gauge." in NOTE_TEXT)


# ================================================================ CHECK 7
def check7():
    head(7, "General coefficient-space bound (deg k_t < deg Phi_i); mock "
            "high-degree higher-value perturbation")
    # (a) every level-1 lift used as a coefficient satisfies deg < D'
    n = 0
    for fr in T.FRAMES:
        for M in range(fr.D * fr.h + 1, fr.D * fr.h + 13):
            for lam in _lambdas(fr):
                terms = T.lift_terms(fr, M, lam)
                if not terms:
                    continue
                n += 1
                chk(7, f"{fr.name}.M{M}.deg_lt_degPhi1",
                    max(t.x_exponent for t in terms) < fr.D)
    say(f"  valid-lift degree rows: {n}")

    # (b) the MOCK: valid lift + high-degree strictly-higher-value term
    fr = FRAME["F4"]           # D' = 4
    M = 7
    lam = [1, 1]
    valid = T.lift_terms(fr, M, lam)
    say(f"  valid lift  M={M}: "
        f"{[(t.x_exponent, t.pi_exponent) for t in valid]}  "
        f"heights={[fr.e1*t.pi_exponent + fr.h*t.x_exponent for t in valid]}")
    # perturbation: x^{D'+2} pi^{a}, with a chosen so its height exceeds M
    px, ppi = fr.D + 2, 3
    pheight = fr.e1 * ppi + fr.h * px
    mock = list(valid) + [T.LiftTerm(r=99, coefficient=F4(1),
                                     x_exponent=px, pi_exponent=ppi)]
    say(f"  perturbation term: x^{px} pi^{ppi}, height={pheight} > M={M}")
    chk(7, "mock.perturbation_strictly_higher_value", pheight > M)
    chk(7, "mock.perturbation_integral", ppi >= 0)
    # height check still passes: exact height = min height over nonzero terms
    heights = [fr.e1 * t.pi_exponent + fr.h * t.x_exponent for t in mock]
    chk(7, "mock.passes_height_check", min(heights), M)
    # residue check still passes: the added term contributes 0 at height M
    res_valid = T.lift_residue(fr, valid)
    res_mock = T.lift_residue(fr, [t for t in mock
                                   if fr.e1 * t.pi_exponent
                                   + fr.h * t.x_exponent == M])
    chk(7, "mock.passes_residue_check", res_mock, res_valid)
    # but it is REJECTED by (C3-lift-coefficient-space)
    chk(7, "mock.rejected_by_coefficient_space",
        max(t.x_exponent for t in mock) < fr.D, False,
        note=f"deg={max(t.x_exponent for t in mock)} >= D'={fr.D}")
    chk(7, "mock.valid_accepted_by_coefficient_space",
        max(t.x_exponent for t in valid) < fr.D, True)
    chk(7, "mock.rejection_is_degree_only",
        (min(heights) == M, res_mock == res_valid,
         max(t.x_exponent for t in mock) < fr.D),
        (True, True, False))

    # (c) every lower key term has degree strictly below the leading term
    bad = []
    for d_i in range(1, 6):
        for e in range(1, 5):
            for f in range(1, 5):
                lead = e * f * d_i
                for t in range(0, f):
                    for degk in range(0, d_i):       # deg k_t < d_i
                        if degk + e * t * d_i >= lead:
                            bad.append((d_i, e, f, t, degk))
    chk(7, "lower_terms_strictly_below_leading", bad, [])
    chk(7, "boundary_e1_t_f_minus_1_strict",
        [(1, f, f - 1) for f in range(1, 5)
         if (f - 1) * 1 * 3 + 2 >= 1 * f * 3], [],
        note="d_i=3, deg k=2, e=1, t=f-1")

    # (d) the common-height bookkeeping (C3-common-height)
    for u in (3, 5, 7, 21):
        for f in (2, 3, 4):
            for t in range(f):
                s = f - t
                chk(7, f"common_height.u{u}.f{f}.t{t}",
                    s * u + t * u, f * u)


def _lambdas(fr):
    out = []
    for r in range(fr.f1):
        v = [0] * fr.f1
        v[r] = 1
        out.append(v)
    if fr.f1 >= 2:
        out.append([1] * fr.f1)
    return out


# ---------------------------------------------------------------- graded model
class GrElt:
    """Consumed homogeneous element c * X^lam of gr(mu_i); lam in Lambda_i."""

    __slots__ = ("lam", "c")

    def __init__(self, lam, c):
        self.lam = Fraction(lam)
        self.c = c

    def __mul__(self, o):
        return GrElt(self.lam + o.lam, self.c * o.c)

    def __pow__(self, k):
        r = GrElt(0, self.c.field.one)
        for _ in range(k):
            r = r * self
        return r

    def is_zero(self):
        return not self.c

    def __eq__(self, o):
        return isinstance(o, GrElt) and self.lam == o.lam and self.c == o.c

    def __repr__(self):
        return f"({self.lam}, {_fe(self.c)})"


def R_true(g):                       # scalar-valued read
    return g.c


def R_zero(g):                       # mock: vanishes on every positive grade
    return g.c if g.lam == 0 else g.c.field.zero


def R_in(g):                         # mock: initial form, valued in gr(mu_i)
    return GrElt(g.lam, g.c)


def _read_axioms(R, N, Kfield, kappa, name, chknum):
    """Score the displayed read axioms for a candidate read R."""
    ok = {}
    # (C3-ladder-multiplicativity)
    mults = []
    for s in range(1, 5):
        lhs = R(N ** s)
        rhs = R(N)
        rhs = rhs ** s if not isinstance(rhs, GrElt) else rhs ** s
        mults.append(lhs == rhs)
    ok["ladder_multiplicativity"] = all(mults)
    # (C3-graded-scalar-covariance): R(Xg) = R(X) res(g), g value-zero
    covs = []
    for X in (N, N ** 2, N ** 3, GrElt(0, Kfield.one)):
        for gc in [c for c in Kfield.elements() if c]:
            g = GrElt(0, gc)
            lhs = R(X * g)
            rx = R(X)
            rhs = rx * gc if not isinstance(rx, GrElt) else rx * GrElt(0, gc)
            covs.append(lhs == rhs)
    ok["graded_scalar_covariance"] = all(covs)
    # grade-zero rule
    zeros = []
    for gc in Kfield.elements():
        r = R(GrElt(0, gc))
        zeros.append((r.c if isinstance(r, GrElt) else r) == gc)
    ok["grade_zero_rule"] = all(zeros)
    # (C3-zero-read)
    rz = R(GrElt(kappa, Kfield.zero))
    ok["zero_read"] = (rz.c if isinstance(rz, GrElt) else rz) == Kfield.zero
    # (C3-ladder-nonvanishing)
    rn = R(N)
    ok["ladder_nonvanishing"] = not (rn.is_zero() if isinstance(rn, GrElt)
                                     else (not rn))
    # (C3-read-codomain): output is a K_i-scalar
    ok["read_codomain"] = not isinstance(rn, GrElt) or rn.lam == 0
    for k, v in ok.items():
        say(f"      {name}: {k:<28} {'PASS' if v else 'FAIL'}")
    return ok


# ================================================================ CHECK 8
def check8():
    head(8, "Ladder nonvanishing — mock read vanishing on every positive grade")
    K = F4
    kappa = Fraction(21, 4)                 # kappa_2 = u_3/e(mu_2) = 21/4
    N = GrElt(kappa, W)                     # N = n_2(u_3), base ladder monomial
    say(f"  graded model: K_i = F4, kappa_i = {kappa}, N = {N}")

    say("    -- true (scalar) read --")
    ax_t = _read_axioms(R_true, N, K, kappa, "R_true", 8)
    say("    -- mock read: zero on every positive grade --")
    ax_0 = _read_axioms(R_zero, N, K, kappa, "R_zero", 8)

    for k in ("ladder_multiplicativity", "graded_scalar_covariance",
              "grade_zero_rule", "zero_read", "read_codomain"):
        chk(8, f"mock_zero.satisfies_{k}", ax_0[k], True)
    chk(8, "mock_zero.violates_ladder_nonvanishing",
        ax_0["ladder_nonvanishing"], False)
    chk(8, "mock_zero.rejected_PRECISELY_by_nonvanishing",
        sorted(k for k, v in ax_0.items() if not v), ["ladder_nonvanishing"])
    chk(8, "true_read.satisfies_everything",
        sorted(k for k, v in ax_t.items() if not v), [])

    # no y/w_i or unit-substitution transport without the clause
    w_mock = R_zero(N)
    chk(8, "mock_zero.w_i_is_zero", not w_mock, True)
    try:
        _ = F4(1) / w_mock
        divides = True
    except ZeroDivisionError:
        divides = False
    chk(8, "mock_zero.y_over_w_undefined", divides, False)
    # w^{deg P} P(y/w) is not degree preserving when w = 0
    P = [W, F4(1), F4(1)]                        # y^2 + y + w
    chk(8, "mock_zero.transport_destroys_degree",
        [w_mock ** (len(P) - 1) * c for c in P],
        [F4(0), F4(0), F4(0)])
    w_true = R_true(N)
    chk(8, "true_read.w_i_is_unit", bool(w_true), True)
    tw = T.twisted_poly(P, w_true)
    chk(8, "true_read.transport_preserves_factor_pattern",
        T.factor_degrees(tw), T.factor_degrees(P))


# ================================================================ CHECK 9
def check9():
    head(9, "Read codomain — initial-form mock read into gr(mu_i)")
    K = F4
    kappa = Fraction(21, 4)
    N = GrElt(kappa, W)
    say(f"  graded model: K_i = F4, kappa_i = {kappa}, N = {N}")
    say("    -- mock read: g |-> in(g) in gr(mu_i) --")
    ax = _read_axioms(R_in, N, K, kappa, "R_in", 9)

    for k in ("ladder_multiplicativity", "graded_scalar_covariance",
              "grade_zero_rule", "zero_read", "ladder_nonvanishing"):
        chk(9, f"mock_in.satisfies_{k}", ax[k], True)
    chk(9, "mock_in.PASSES_check8_nonvanishing", ax["ladder_nonvanishing"],
        True, note="base ladder read is nonzero")
    chk(9, "mock_in.violates_read_codomain", ax["read_codomain"], False)
    chk(9, "mock_in.rejected_PRECISELY_by_codomain",
        sorted(k for k, v in ax.items() if not v), ["read_codomain"])

    w = R_in(N)
    chk(9, "mock_in.w_i_has_positive_grade", w.lam > 0, True,
        note=f"grade {w.lam}")
    chk(9, "mock_in.w_i_not_a_K_scalar", isinstance(w, GrElt) and w.lam != 0)
    chk(9, "mock_in.y_over_w_not_typeable_in_K_y",
        _typeable_in_Ky(w), False)
    chk(9, "mock_in.psi_w_not_typeable", _typeable_in_Ky(w), False)
    chk(9, "mock_in.w_pow_degP_not_a_scalar",
        isinstance(w ** 2, GrElt) and (w ** 2).lam != 0)
    chk(9, "true_read.output_is_K_scalar", _typeable_in_Ky(R_true(N)), True)

    # TEXT LEG: every effective site of y/w_i, psi^{(w_i)}, w_i^{deg P} sits
    # under (C3-read-codomain).
    say("  text leg — sites of y/w_i, psi_(i+1)^{(w_i)}, w_i^{\\deg P}:")
    site_rx = re.compile(r"y/w_i|\\psi_\{i\+1\}\^\{\(w_i\)\}|w_i\^\{\\deg P\}")
    hits = []
    for ln, line in enumerate(NOTE_LINES, 1):
        if site_rx.search(line):
            hits.append((ln, line.strip()[:150]))
    for ln, s in hits:
        say(f"      L{ln}: {s}")
    chk(9, "text.sites_found", len(hits) >= 1, True, note=f"{len(hits)} sites")
    # the codomain clause is declared and threaded
    chk(9, "text.C3_read_codomain_declared",
        "\\tag{C3-read-codomain}" in NOTE_TEXT)
    chk(9, "text.unit_gate_is_two_clause",
        "(C3-read-codomain) and (C3-ladder-nonvanishing)" in NOTE_TEXT)
    chk(9, "text.y_over_w_guarded_by_codomain",
        "Without (C3-read-codomain), \\(y/w_i\\) is not defined in \\(K_i[y]\\)"
        in NOTE_TEXT)
    chk(9, "text.codomain_named_before_psi_w",
        "the codomain and nonvanishing clauses are both supplied" in NOTE_TEXT)
    chk(9, "text.ledger_item_22_two_clause",
        "requires BOTH (C3-read-codomain) and (C3-ladder-nonvanishing)"
        in NOTE_TEXT)
    # the r8-only one-clause gate is EXPLICITLY superseded by R11-1, not left
    # standing alongside the two-clause gate
    chk(9, "text.r8_one_clause_gate_superseded",
        "with:\n\n> At every consumed site carrying\n> "
        "(C3-read-codomain) and (C3-ladder-nonvanishing)," in NOTE_TEXT)
    chk(9, "text.C7_M2_row_names_codomain",
        "(C3-ladder-nonvanishing), and (C3-read-codomain)." in NOTE_TEXT)


def _typeable_in_Ky(w):
    """y |-> y/w is an automorphism of K_i[y] only for a K_i-scalar unit w."""
    if isinstance(w, GrElt):
        return False
    return bool(w)


# ================================================================ CHECK 10
# ---- rider-5 scoring scope --------------------------------------------------
# Self-exclusions named by post-pass Rider 5:
#   * check 10's own instruction text (R13-8(iii) block + the rider's own
#     appended self-exclusion paragraph, which quotes it);
#   * the value-group declaration's own witness displays and prose IN THE
#     "Grade data (definitions)" paragraph: the boxed codomain display, the
#     dv_i(Phi_i)=u_{i+1}/e_{i+1} sentence, the dv_2(Phi_2)=21/2 display.
# Plus the rider's general scoping principle: "A site is scored only where the
# note CONSUMES the value" (its example: a display inside an explicit
# non-implication).
CHECK10_SPEC_LINES = set(range(4245, 4250)) | set(range(4318, 4326))
GRADE_DATA_DECL_LINES = set(range(4208, 4240))
NONIMPLICATION_LINES = {1855}


def check10():
    head(10, "Grade-data value group (GENTOW2 S2 witness) + dv-site scoring "
             "against the four consumed classes")

    # ---------------- (a) numeric leg, from the pinned GENTOW2 S2 tower
    u3, e3, emu2, emu3 = 21, 2, 4, 8
    nuPhi2 = Fraction(u3, emu3)               # 21/8
    dv2_Phi2 = Fraction(emu2) * nuPhi2        # 21/2
    dv2_Phi2_e3 = Fraction(e3) * dv2_Phi2     # 21
    say(f"  GENTOW2 S2 tower @ i=2: u_3={u3}, e_3={e3}, e(mu_2)={emu2}, "
        f"e(mu_3)={emu3}; nu(Phi_2)={nuPhi2}")
    chk(10, "witness.e3_does_not_divide_u3", u3 % e3 != 0, True,
        note=f"{u3} mod {e3} = {u3 % e3}")
    chk(10, "witness.dv2_Phi2_equals_u3_over_e3", dv2_Phi2, Fraction(u3, e3))
    chk(10, "witness.dv2_Phi2_nonintegral", dv2_Phi2.denominator != 1, True,
        note=f"dv_2(Phi_2) = {dv2_Phi2}")
    chk(10, "witness.dv2_Phi2_pow_e3_integral",
        (dv2_Phi2_e3.denominator == 1, dv2_Phi2_e3), (True, Fraction(u3)))
    chk(10, "witness.u3_equals_emu3_times_nu",
        Fraction(emu3) * nuPhi2, Fraction(u3))
    # codomain e(mu_i) Lambda_r = (e(mu_i)/e(mu_r)) Z
    chk(10, "witness.codomain_group",
        Fraction(emu2, emu3), Fraction(1, 2),
        note="dv_2 takes values in (1/2)Z, not Z")
    chk(10, "witness.equality_iff_no_further_ramification",
        Fraction(emu3, emu3), Fraction(1))

    # ---------------- (a') independent NON-TEXTUAL leg: PARI on the S2 tower
    gp = _pari_S2()
    if gp is None:
        chk(10, "pari.independent_leg_available", False, True,
            note="gp unavailable — leg not run")
    else:
        vres_Phi2, vres_Phip, deg3, nfac = gp
        say(f"  PARI: Phi'=x^2-2, Phi_2=Phi'^2-4x, Phi_3=Phi_2^2-16Phi'; "
            f"deg Phi_3={deg3}, Q_2-factors={nfac}")
        say(f"        v_2(Res(Phi_3,Phi_2))={vres_Phi2}  -> "
            f"nu(Phi_2)={Fraction(vres_Phi2, deg3)}")
        chk(10, "pari.Phi3_irreducible_over_Q2", nfac, 1)
        chk(10, "pari.nu_Phi2_is_21_over_8",
            Fraction(vres_Phi2, deg3), nuPhi2)
        chk(10, "pari.u3_equals_21", Fraction(emu3) * Fraction(vres_Phi2, deg3),
            Fraction(21))
        chk(10, "pari.nu_Phip_is_5_over_4",
            Fraction(vres_Phip, deg3), Fraction(5, 4),
            note="u_2 = e(mu_2)*nu(Phi') = 5")
        chk(10, "pari.emu3_is_denominator_of_nu_Phi2",
            Fraction(vres_Phi2, deg3).denominator, emu3)
    # the same numbers, read from the accepted GENTOW2 proof's S2 table
    g2 = GENTOW2.read_text(encoding="utf-8")
    chk(10, "source.GENTOW2_S2_nu_Phi2", "ν(Φ₂) = 21/8" in g2)
    chk(10, "source.GENTOW2_S2_kappa3", "| 21/2 |" in g2)
    chk(10, "source.GENTOW2_S2_e3_is_2",
        "denom 8 = e(µ₃) over e(µ₂) = 4 gives e₃ = 2" in g2)

    # ---------------- (b) dv-site scoring against the four consumed classes
    sites = _dv_sites()
    say(f"  dv occurrences: {len(sites)} "
        f"({sum(1 for s in sites if s['arg'] is not None)} with an argument)")
    strictA, strictB = [], []
    counts = {}
    for s in sites:
        cls = _classify(s)
        counts[cls] = counts.get(cls, 0) + 1
        s["class"] = cls
        if cls == "UNCLASSIFIED":
            strictA.append(s)
            strictB.append(s)
        elif cls == "SPEC-PROSE(reading-B only)":
            strictA.append(s)
    say("  class tally:")
    for k in sorted(counts):
        say(f"      {k:<34} {counts[k]}")
    say("  sites NOT covered by a class under the STRICT (enumeration-only) "
        "reading A:")
    for s in strictA:
        say(f"      L{s['line']}  dv{s['sub'] or ''}({(s['arg'] or '')[:44]}) "
            f"= {s['rhs'][:34]}")
    if not strictA:
        say("      (none)")
    say("  sites NOT covered under the CONSUMPTION-scoped reading B "
        "(the rider's stated principle):")
    for s in strictB:
        say(f"      L{s['line']}  dv{s['sub'] or ''}({(s['arg'] or '')[:44]}) "
            f"= {s['rhs'][:34]}")
    if not strictB:
        say("      (none)")

    chk(10, "sites.reading_B_all_classified",
        [f"L{s['line']}" for s in strictB], [])
    # the two explicit fail conditions, on the reading-B scored sites
    badZ, badK = [], []
    for s in sites:
        if s["class"].startswith(("EXCLUDED", "NONCONSUMED", "MENTION",
                                  "SPEC-PROSE")):
            continue
        if s["nonintegral"]:
            badZ.append(s["line"])
        if s["phi_bad_exponent"]:
            badK.append(s["line"])
    chk(10, "fail_cond.no_scored_site_consumes_nonintegral_dv",
        sorted(set(badZ)), [])
    chk(10, "fail_cond.no_scored_site_applies_dv_to_Phi_k_with_e_nmid_k",
        sorted(set(badK)), [])
    # READING A (enumeration-strict) recorded as an AMBIGUITY row, not folded
    # into the verdict -- see the ambiguity note printed below.
    ambig("10", "sites.reading_A_all_classified",
          [f"L{s['line']}" for s in strictA], [])
    say("")
    say("  *** AMBIGUITY (check 10 scoring scope) ***")
    say("  Rider 5 excludes 'this numbered check's own instruction text and")
    say("  the value-group declaration's own witness displays and prose IN")
    say("  THE Grade data (definitions) paragraph', then states the general")
    say("  principle 'A site is scored only where the note CONSUMES the")
    say("  value'.")
    say("  READING A (exclusion list exhaustive, restricted to the Grade-data")
    say("    paragraph): 5 sites fall outside every class and outside every")
    say("    named exclusion -> check 10 FAILS. The sites are R13-8's own")
    say("    Finding C-1 prose (L4196, four occurrences: the quoted")
    say("    dv_2(Phi_2)=21/2 falsification and the quoted grep for a bare")
    say("    dv_i(Phi_i)) and the §6 CHANGES record row (L4255, the")
    say("    'dv_2(Phi_2)=21/2 instance' phrase).")
    say("  READING B (consumption-scoped, the rider's own governing")
    say("    sentence): none of those five sites CONSUMES a dv value -- each")
    say("    exhibits or records it as the diagnosis that motivated the")
    say("    declaration -> check 10 PASSES.")
    say("  Reading B is scored as primary because the rider states the")
    say("  consumption criterion as a general principle (the non-implication")
    say("  is given as one example, after a colon), and because check 10's")
    say("  own first fail clause is itself consumption-scoped ('fail on any")
    say("  site that CONSUMES a dv_i-value outside Z').")
    say("  RESIDUE FOR THE GATE: the rider's exclusion list does not name")
    say("  R13-8's finding prose or the §6 record row, so a literal scorer")
    say("  fails them; a one-clause widening would remove the ambiguity.")
    say("")
    # the composed-key product scores as passing (rider R5, additivity)
    chk(10, "additivity.composed_key_product_passes",
        any(s["class"].startswith("CLASS(i)+(ii)") for s in sites), True)
    # the four classes are the note's own enumeration
    for tag in ("(i) Typed stage and lift heights",
                "(ii) Stage-key powers",
                "(iii) Value-zero factors",
                "(iv) The level-one grid"):
        chk(10, f"classes.note_enumerates_{tag[:5]}", tag in NOTE_TEXT)
    chk(10, "rider.self_exclusion_present",
        "Scored sites exclude this numbered check's own instruction text"
        in NOTE_TEXT)


def _pari_S2():
    script = (
        "Phip=x^2-2;Phi2=Phip^2-4*x;Phi3=Phi2^2-16*Phip;"
        "print(valuation(polresultant(Phi3,Phi2),2));"
        "print(valuation(polresultant(Phi3,Phip),2));"
        "print(poldegree(Phi3));"
        "print(matsize(factorpadic(Phi3,2,60))[1]);"
    )
    try:
        out = subprocess.run(["gp", "-q"], input=script, text=True,
                             capture_output=True, timeout=120)
    except Exception:
        return None
    if out.returncode != 0:
        return None
    vals = [int(x) for x in out.stdout.split()]
    return tuple(vals) if len(vals) == 4 else None


_DV_RE = re.compile(r"dv(_\{[^}]*\}|_[0-9A-Za-z])?")


def _dv_sites():
    sites = []
    txt = NOTE_TEXT
    for m in _DV_RE.finditer(txt):
        sub = (m.group(1) or "").lstrip("_").strip("{}")
        j = m.end()
        k = j
        while k < len(txt) and (txt[k] in " \t\n>"
                                or txt.startswith("\\!", k)
                                or txt.startswith("\\left", k)):
            if txt.startswith("\\!", k):
                k += 2
            elif txt.startswith("\\left", k):
                k += 5
            else:
                k += 1
        if k < len(txt) and txt[k] == "(":
            d, e = 0, k
            while e < len(txt):
                if txt[e] == "(":
                    d += 1
                elif txt[e] == ")":
                    d -= 1
                if d == 0:
                    break
                e += 1
            arg = " ".join(txt[k + 1:e].replace(">", " ").split())
            arg = arg.replace("\\right", "").replace("\\left", "").strip()
            rhs = " ".join(txt[e + 1:e + 70].replace("\n", " ")
                           .replace(">", " ").split())
        else:
            arg, rhs = None, " ".join(txt[m.end():m.end() + 60]
                                      .replace("\n", " ").split())
        sites.append({"line": lineno(m.start()), "sub": sub, "arg": arg,
                      "rhs": rhs})
    return sites


_CLASS_I = [
    r"^\\pi_\{i\+1\}$", r"^\\pi_\{i\+1\}\^\{u_\{i\+1\}\}$",
    r"^\\widehat n_i\(.*\)$", r"^\\widehat\{n\}_i\(.*\)$",
    r"^\\operatorname\{lift\}_i\(d;m\)$", r"^\\widehat k_t$",
    r"^L_M\(\\lambda\)$", r"^L_M\(0\)$",
]
_CLASS_IV = [r"^x$", r"^\\pi$", r"^A$", r"^\\widetilde a$",
             r"^\\widetilde\{\\lambda_r\}$", r"^L_M\(\\lambda\)$",
             r"^L_M\(0\)$", r"^\\widehat k_t$"]
_PHI_RE = re.compile(r"^\\Phi_(?P<i>[0-9i])(\^\{(?P<exp>.*)\})?$")
_PROD_RE = re.compile(r"^\\widehat k_t\\Phi_(?P<i>[0-9i])\^\{(?P<exp>.*)\}$")


def _classify(s):
    ln, sub, arg, rhs = s["line"], s["sub"], s["arg"], s["rhs"]
    s["nonintegral"] = False
    s["phi_bad_exponent"] = False
    if arg is None:
        return "MENTION (no argument)"
    if ln in CHECK10_SPEC_LINES:
        return "EXCLUDED: check-10 own spec (rider R5)"
    if ln in NONIMPLICATION_LINES:
        return "NONCONSUMED: inside explicit non-implication (rider R5)"
    # value-zero / infinite conventions -> class (iii)
    if arg == "0" or rhs.startswith("=+\\infty") or rhs.startswith("=0"):
        return "CLASS(iii) value-zero / zero convention"
    m = _PROD_RE.match(arg)
    if m:
        return "CLASS(i)+(ii) composed-key product (rider R5 additivity)"
    m = _PHI_RE.match(arg)
    if m:
        exp = m.group("exp")
        if exp is None:
            # bare Phi_i: non-integral in general
            s["nonintegral"] = True
            s["phi_bad_exponent"] = True
            if ln in GRADE_DATA_DECL_LINES:
                return ("EXCLUDED: value-group declaration display "
                        "(rider R5)")
            return "SPEC-PROSE(reading-B only)"
        if re.match(r"^e_\{i\+1\}", exp) or re.match(r"^e_3", exp):
            return "CLASS(ii) stage-key power e_{i+1}*k"
        s["phi_bad_exponent"] = True
        return "UNCLASSIFIED"
    for rx in _CLASS_I:
        if re.match(rx, arg):
            return "CLASS(i) typed stage / lift height"
    if sub in ("1", "") or sub == "1":
        for rx in _CLASS_IV:
            if re.match(rx, arg):
                return "CLASS(iv) level-one grid"
    for rx in _CLASS_IV:
        if re.match(rx, arg):
            return "CLASS(iv) level-one grid (unsubscripted dv = dv_1, R11-5)"
    if arg in ("g", "g_t", "w"):
        return "CLASS(iii) value-zero factor"
    return "UNCLASSIFIED"


# ================================================================ teeth
def teeth():
    head("T", "The four mandatory planted teeth (each must FIRE)")
    st = STAGE["F4MU3"]
    th = T.stage_theta(st)
    good = T.stage_canonical_slots(st, T.stage_gamma(st), th, True)
    fired = {}
    # T-1 gauge-naive
    naive = T.stage_canonical_slots(st, T.stage_gamma(st, "gauge_naive"),
                                    th, True)
    fired["gauge_naive"] = naive != good
    # T-2 wrong-sign: mutated digit read back against the TRUE telescope
    ws = T.stage_canonical_slots(st, T.stage_gamma(st, "wrong_sign"),
                                 th, True)
    fired["wrong_sign"] = ws != good
    # T-3 misindexed telescope
    th_mi = T.stage_theta(st, "misindexed_telescope")
    fired["misindexed_telescope"] = th_mi != th
    # T-4 inverse orientation
    inv = T.stage_canonical_slots(st, T.stage_gamma(st), th, False)
    fired["inverse_orientation"] = inv != good
    for k, v in fired.items():
        chk("T", f"tooth.{k}.fires", v, True)


# ================================================================ main
def main():
    say("T1 §4.2 MACHINE BATTERY RE-RUN — checks 1..10, effective text of "
        "2026-08-13 (r13 + post-pass riders)")
    say(f"note   : {NOTE}  ({len(NOTE_LINES)} lines)")
    say(f"reuse  : {SEALED}")
    say("")
    for fn in (check1, check2, check3, check4, check5, check6, check7,
               check8, check9, check10, teeth):
        fn()

    say("")
    say("=" * 78)
    say("PER-CHECK TABLE")
    say("=" * 78)
    say(f"{'#':<4}{'what it verifies':<58}{'rows':>6} {'fail':>5}  verdict")
    say("-" * 78)
    DESC = {
        1: "GENHN-LIFT boundary: integrality/degree/height/residue, f1>=2,"
           " low-M refusal",
        2: "positive wrap sign; corrected vs naive vs wrong-sign, EXACT"
           " coefficients",
        3: "JA origin: nu=0, z^nu!=1, ROOT-OF-UNITY nu>0, support/degree"
           " shift by nu",
        4: "HE6 normalization: normalizer-read, varpi-read, the -q(k) sign",
        5: "orientation tooth on ALL THREE canonical mu=3 slots + B-units",
        6: "weld scope lint (R4-3 self-excluding) + M3/M4 fences",
        7: "coefficient space deg k_t < deg Phi_i; mock perturbation rejected",
        8: "ladder nonvanishing: zero-on-positive-grades mock read rejected",
        9: "read codomain: initial-form mock read rejected (passes check 8)",
        10: "grade-data value group: GENTOW2 S2 witness + dv-site scoring",
        "T": "the four planted teeth each fire",
    }
    order = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, "T"]
    npass = 0
    for c in order:
        rows = [r for r in ROWS if r[0] == c]
        fails = [r for r in rows if not r[4]]
        verdict = "PASS" if not fails else "FAIL"
        if c != "T" and verdict == "PASS":
            npass += 1
        say(f"{str(c):<4}{DESC[c][:57]:<58}{len(rows):>6} {len(fails):>5}  "
            f"{verdict}")
        for r in fails:
            say(f"      FAILING ROW: {r[1]}  got={_s(r[2])} want={_s(r[3])}")
    say("-" * 78)
    say(f"TOTAL SCORED ROWS: {len(ROWS)}   FAILING: "
        f"{sum(1 for r in ROWS if not r[4])}")
    if AMBIG_ROWS:
        say("")
        say("AMBIGUITY ROWS (alternate reading, reported, not in verdicts):")
        for c, n, g, w, ok in AMBIG_ROWS:
            say(f"  C{c}  {n}  got={_s(g)} want={_s(w)}  "
                f"-> {'agrees' if ok else 'DIVERGES'}")
    say("")
    say(f"BATTERY: {npass}/10 PASS")
    return 0


if __name__ == "__main__":
    rc = main()
    out = Path(__file__).with_suffix(".log")
    out.write_text("\n".join(LOG) + "\n", encoding="utf-8")
    print(f"\n[log written to {out}]")
    sys.exit(rc)
