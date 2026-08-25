# Verdict — unit RP910: S2-source plan nodes RP-9 + RP-10 — the `normalized_mul` CORE, CLOSED

Date: 2026-08-25 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, rows RP-9
("Initial y-orders add under products, including all zero cases") and RP-10 ("Prove the
universal normalized residual product law"), on RP-8's landing (verdict_RP78.md:
`s2NormRes`, the strip pin, the reconstruction), RP-4's twisted product law, and RP-0's
grade arithmetic, under the U14 adjudication (`COR412_ADJUDICATION_2026-08-25.md` §1/§7:
`normalized_mul` is PLAIN and UNRESTRICTED per published Cor 4.12(3) — the strip absorbs
the carry).  File created (the ONLY repo file touched):
`leanfinal/Uniformity/ChapC/C130rp9.lean` (459 lines, 25 public declarations; not added to
any roll-up; no leanspec/ or other units' files touched; NO git commit).

## RP-9 — the `y`-order arithmetic (initial `y`-orders ADD, twist bookkeeping included)

★ **`s2GradedRes_natTrailingDegree_mul`** — at exact grades,
`j₀(g·z) = j₀(g) + j₀(z) + (β%2)·(β′%2)` in the trailing-degree carrier (RP-8's strip pin
certifies `ntd = j₀ = ⌊s/e₂⌋`): PROVED by taking `natTrailingDegree` of RP-4's twisted
identity `R_{β+β′}(g·z) = y^{(β%2)(β′%2)}·R_β(g)·R_{β′}(z)` over the residue-field domain
(mathlib `natTrailingDegree_mul`; both residuals nonzero at exact grade by RP-5/RP-6) —
U14 §7's floor identity `⌊(s+s′)/2⌋ = ⌊s/2⌋+⌊s′/2⌋+carry` as a THEOREM, not bookkeeping.
Companions: **`dvSideMin_div_two_mul_of_exact`** (the brief's display in published
coordinates, via the strip pin on all three polynomials); ★ **`dvSideMin_mul_of_exact`**
— the UNHALVED endpoint EQUALITY `s(g·z) = s(g) + s(z)`, upgrading NV-2/NV-3's `≤`
(`s2_dvSideMin_mul_le`, which needed endpoint-height hypotheses) via the parity pins
(`dvSideMin_mod_two_of_exact`) + a 4-way parity split feeding omega (the RP78 verdict's
omega-vs-product workaround genre: pre-reduce `(β%2)(β′%2)` to a numeral per branch);
**`s2GradeOf_mul`** (total extracted grades add) and the total-anchoring form
`s2GradedRes_natTrailingDegree_mul_total`.  **Zero cases** (the row's clause): the zero
polynomial has NO exact grade (`no_exact_grade_at_zero`, RP-0 re-exposed), so the
exact-grade laws are vacuously closed there; total carrier pinned
(`s2GradedRes_natTrailingDegree_zero`); the normalized zero cases are Def 3.15's own
`R₃(0) = 0` clause, discharged inside RP-10 and toothed.

## RP-10 — ★ the universal plain law `s2NormRes_mul` (published Cor 4.12(3))

★ **`s2NormRes_mul : ∀ g z, R₃(g·z) = R₃(g)·R₃(z)`** — UNIVERSAL: no grade, parity, or
nonzero premise (Cor 4.12(3)'s verbatim "for all g, h ∈ K[x]" scope).  Assembly = U14 §7
verbatim: cancel `X^{j₀(g·z)}` (`mul_right_cancel₀`, domain) between RP-8's reconstruction
`R₃(g·z)·y^{j₀(g·z)} = R_{β+β′}(g·z)` and the twist-composite
`y^c·(R₃(g)·y^{j₀(g)})·(R₃(z)·y^{j₀(z)})`, powers matched by RP-9's addition law; zero
branches via `s2NormRes_zero`.  Worker `s2NormRes_mul_of_exact` (caller-supplied grades).
Corollaries: **`s2NormRes_pow`** (unrestricted — contrast the adjudicated-unsound scalar
`Rgr_pow`, U14 §8.3), **`s2NormRes_coeff_zero_mul`** (U14 §8.3's `RgrNorm` normalized
scalar, cited to 4.12(3) NOT 4.12(2)).  **FD-0 pin** `s2_normalized_mul_fills`: any
`FGMNSourceData (s2DepthTwo) K 2 1 5` with `normalizedResidual = s2NormRes` satisfies the
C130fg `normalized_mul` field, byte-identical binders — zero residual FD-0 work for this
field.  **A-C.11 class-shape tooth** `s2_Rres_mul_shape`: the leanspec
`FGMNCalculus.Rres_mul` field shape (`∀ g h, Rres (g·h) = Rres g · Rres h`) at
`Rres := s2NormRes`.

## Teeth (all genres of the case split)

odd×odd carry LAW vs HAND decorrelated (`tooth_ntd_carry_law` = `tooth_ntd_carry_hand` = 1,
the latter off RP-1's landed `R₁₀(Φ′²) = X`); a NEW odd×odd pair beyond key powers
(`tooth_ntd_odd_pair`: grades (5,7), `(Φ′, x·Φ′)`, fresh grade-12 value `j₀ = 1`;
`tooth_normRes_mul_odd_odd`: `R₃(Φ′·(x·Φ′)) = 1` where the graded twist is live); mixed
parity LAW vs HAND (`tooth_normRes_mul_mixed` / `tooth_normRes_X_mul_key`, both give
`R₃(x·Φ′) = 1`); key powers re-derived through the universal law
(`tooth_normRes_key_pow_via_law`, matches RP-8's independent induction); both zero cases
(`tooth_normRes_mul_zero_left`/`_value`, `_right_value`).

## What was deliberately NOT claimed

No `FGMNSourceData`/`FGMNSourceLaws`/`FGMNCalculus` INSTANCE (FD-0/CC-17 rows); no A-C.11
field change and no `RgrNorm` amendment (the scalar `Rgr_mul` keeps its A-C.13-restored
`PrevGrade` premise, untouched); the graded plain law stays refuted at odd×odd (C130rp2's
tooth, not re-litigated); the ϖ-read dictionary stays on C.22/C.25's recorded boundary.
Flagged for human review (new statements): `s2GradedRes_natTrailingDegree_mul`,
`dvSideMin_mul_of_exact`, `s2NormRes_mul`, the FD-0/A-C.11 shape pins.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C130rp9.lean` — CLEAN (exit 0, 0 errors,
0 warnings, 0 sorry; first-compile clean).  Dependency stack prebuilt via
`lake build Uniformity.ChapC.C130rp8` (success, exit 0).  25 `#print axioms` rows, ALL
exactly `[propext, Classical.choice, Quot.sound]` (0 `sorryAx`); no new axiom, no `unsafe`,
no statement touched; `git status` shows ONLY the new `C130rp9.lean`.  No git commit (per
brief).
