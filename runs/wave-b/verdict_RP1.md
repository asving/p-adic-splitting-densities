# Verdict — unit RP1: S2-source plan node RP-1 (graded residual definition)

Date: 2026-08-25 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, row RP-1
"graded residual definition" (deps RP-0, `dev`, `twistRead`, terminal receiver). File created
(the ONLY file touched): `leanfinal/Uniformity/ChapC/C130rp1.lean` (31 public declarations +
2 private helpers + 1 shape example; not added to `Uniformity/ChapC.lean` or any roll-up).

## RP-1 (graded residual definition) — LANDED

Defined the TOTAL S2 graded residual `s2GradedRes : ℕ → Polynomial O →
Polynomial ((s2DepthTwo h2 hq).fld 2)` — byte-for-byte the abstract
`FGMNSourceData.gradedResidual` field shape (C130fg) at `r = 2`, pinned by a
`noncomputable example`. Published Def 3.13 concretized: the `t`-th `y`-coefficient
(`s2GradedCoeff`) is the C.22 ϖ-read `twistRead` — the SAME read C.25's `dvResPoly`
coefficients use — of the `Φ′`-development slot at abscissa `β % 2 + 2t` (Def 3.12's
`s₂(β) = β % 2` line parameterization at `(e₂, h₂) = (2, 5)`), at the on-line height
`(β − 5s)/2`, gated by the named line-membership `Prop` `S2SlotOnGrade` (`2·dv(Aₛ) + 5s = β`,
`dvSupp`'s own term shape); off-line slots contribute literal `0` (junk-total per corpus
convention). The bank: the gate normal form `s2SlotOnGrade_iff` (finite height + NATURAL line
equation `2m + 5s = β`); **finite-support pins** `s2GradedCoeff_eq_zero_of_natDegree_lt`
(from `dvHgt_top_of_gt` — the natDegree bound of the development the brief demanded) and
`…_of_grade_lt` / `s2GradedRes_natDegree_le` (support ≤ β); **proof-independence pins**:
★ the master coefficient law `s2GradedRes_coeff` (`(s2GradedRes β g).coeff t =
s2GradedCoeff β g t` for ALL `t` — the polynomial is determined by the total coefficient
function, no assembly choice visible), `s2GradedRes_eq_sum_range` (any range `M ≥ β+1`),
`s2GradedCoeff_eq_twistRead` (the `ℕ`-truncated height is the TRUE `dvHgt` on the gate — the
`dv2Res_pinned` genre from C78adj, for the one arithmetic choice made),
`s2GradedCoeff_pin_irrel` (`rfl` by definitional proof irrelevance; `H₀ = 1` forced by C.97's
`s2Frame_pin_unique`, not chosen), and slot completeness `s2SlotOnGrade_parity` +
`s2GradedCoeff_slot` (every on-line slot IS read, at `y`-power `s/2` = eq (11)'s `⌊s/e₂⌋`);
**the RP-2 zero-law shape, landed because it fell out**: ★ `s2GradedRes_zero_of_above`
(published Lemma 3.14, the literal `graded_zero_of_above` field shape against RP-0's
`S2AboveGrade`, via the new bridge `dvSupp_le_of_slotOnGrade`) and `s2GradedRes_zero`.
Computation teeth at RP-0's landed grades, each an eq (11) instance: `R₅(Φ′) = 1`
(`y^⌊1/2⌋`), `R₇(x·Φ′) = 1` (through C35b's landed `twistRead 1 x = 1`), `R₁₀(Φ′²) = X`
(`y^⌊2/2⌋` — the `y`-power is LIVE, the operator genuinely polynomial-valued per U9 Q2),
`R₃(Φ′) = 0` (the zero law fires at a concrete above-grade input), `R₇(x·Φ′) ≠ 0`
(non-vacuity). New frame values landed en route: `twistRead 0 1 = 1` at the S2 frame (the
height-0 companion of C35b's `twistRead_one_X`, with `slotIdx_zero`/`twistExp_zero`/
`slotWindow_zero`/`slotRes_zero_one`) and public `dev`/`dvHgt` teeth for `Φ′`, `x·Φ′`, `Φ′²`
(RP-8's key-power computations can reuse them).

## One adjudication (recorded, per the brief, against a plan-internal tension)

Plan §5.2's `gradedResidual` row says "using `dev (keyAt 2)`", but its own `nextValue` row
(and landed RP-0) fixes `nextValue = toZ (dvSupp … 5 2)`, the `Φ′ = keyAt 1` development
value — and FGMN's Def 3.13 residual must use the SAME development as its grading valuation
(else Lemma 3.14 is false). The brief's concrete meaning ("coefficients of the Φ′-development
whose (5,2)-weighted value equals β") resolves the tension in the only coherent direction;
the landed `s2GradedRes_zero_of_above` against RP-0's `S2AboveGrade` is the machine check
that the choice coheres. Codomain note: `(s2DepthTwo h2 hq).fld 2` is reached on the nose
(definitionally `K₁`, C.97's constant residue tower) — no `TerminalReceiver` transport was
needed at this occurrence; the receiver tie remains FD-0/OPEN-DICT-3's.

## What was deliberately NOT claimed

No `graded_add` (RP-2's remaining half) or product laws (RP-3–RP-6 CORE); no exact-grade
scalar nonvanishing (RP-7); no `normalizedResidual`/Def 3.15 strip or `dvResPoly` tie (RP-8);
no `FGMNSourceData`/`FGMNSourceLaws` instance (FD-0). The ϖ-read ↔ `ε(α)·R(a)(z)` evaluation
dictionary is consumed from C.22/C.25's recorded faithfulness boundary, not re-derived.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C130rp1.lean` — CLEAN (exit 0, 0 errors, 0
warnings, 0 sorry). `lake build Uniformity.ChapC.C130rp1` — success (8741 jobs). 36
`#print axioms` rows, ALL `[propext, Classical.choice, Quot.sound]` (Lean-core only); no new
axiom, no `unsafe`, no statement touched, no other file modified. No git commit (per brief).
