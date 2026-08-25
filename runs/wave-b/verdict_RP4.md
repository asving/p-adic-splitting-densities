# Verdict — unit RP4: S2-source plan node RP-4 (CORE 2/4 of `graded_mul`)

Date: 2026-08-25 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, row RP-4
("Recursive coefficient convolution formula for the depth-two graded residual"), under the
U14 adjudication (`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md`: grade-anchored
operator, carry-twisted arbitrary-grade law, printed plain law only on the PrevGrade scope).
File created (the ONLY repo file touched): `leanfinal/Uniformity/ChapC/C130rp4.lean`
(851 lines, 22 public declarations + 7 private helpers; not added to `Uniformity/ChapC.lean`
or any roll-up; no leanspec/ or other units' files touched; NO git commit).

## The formula — LANDED, in all the consumable forms

★ **`s2GradedCoeff_mul` (headline, twist-normalized coefficient convolution)**: at exact
grades `β` (of `g`), `β′` (of `z`), for EVERY `T`,
`Rgc_{β+β′}(g·z)(T + (β%2)·(β′%2)) = Σ_{t ≤ T} Rgc_β(g)(t) · Rgc_{β′}(z)(T−t)` — the
general-slot version of RP23's endpoint case (which is its `T = 0` shadow).
★ **`s2GradedCoeff_mul_zero_of_odd`**: odd×odd ⟹ `Rgc_{β+β′}(g·z)(0) = 0` — the one
coefficient below the twist; together the two determine EVERY coefficient.
**`s2GradedCoeff_mul_of_prevGrade`** (PrevGrade-specialized, published Cor 4.12(2)'s scope):
even `β′` kills the carry, plain convolution at every `T`.
**Product-polynomial forms** (what RP-6 consumes directly, via `Polynomial.coeff_mul`):
`s2GradedRes_mul_coeff` (`(R_{β+β′}(g·z)).coeff (T+c) = (R_β(g)·R_{β′}(z)).coeff T`),
`s2GradedRes_mul_coeff_zero_of_odd`, `s2GradedRes_mul_coeff_of_prevGrade`.
★ **Assembled polynomial identities at exact grades** (the U14 §8.2 shape, so RP-5/RP-6
consume without restating): `s2GradedRes_mul_of_exact`
(`R_{β+β′}(g·z) = X^{(β%2)·(β′%2)} · (R_β(g)·R_{β′}(z))` — the repo's OWN arbitrary-grade
generalization, NOT a Cor 4.12(2) transcription) and `s2GradedRes_mul_of_prevGrade` (the
plain law under `β′ % 2 = 0`). RP-6's remaining assembly: the exact-grade conjunct
`S2ExactGrade (β+β′) (g·z)` (available from `S2ExactGrade_mul`), arbitrary/junk-input
handling, and the C130fg field retype.

## The engine (new, and how the proof goes)

Direct convolution over slots (no induction needed — the "recursion" of the plan row lives
in the depth-two reads): the `(T+c)`-coefficient reads slot `S = (β+β′)%2 + 2(T+c)` at the
on-line height `m` unconditionally (RP-2's floor bridge + NV-4's `s2_dvSupp_mul`). New
generic ★ `dev_mul_conv_split`: `dev(g·z)(S) = Σ_{j+i=S} (g_j·z_i) %ₘ Φ′ + Σ_{j+i=S−1}
dev(g_j·z_i)(1)` — main diagonal plus carry diagonal, ANY corpus frame (double development
+ B35a shift laws; a two-digit product's own development stops at index 1). New generic
★ `twistRead_finsetSum_of_le` / `le_stageHeight_finsetSum` (RP23's two-term read additivity
iterated over C127's ultrametric). Pricing: new `ceil_le_dvHgt_of_le_dvSupp` (EVERY slot of
a grade-floored polynomial clears the rounded-up on-line height `⌈(β−5j)/2⌉` — no parity or
membership hypothesis), new ★ `le_stageHeight_mul_modByMonic` (the `≥` half of the survival
core, companion of NV-3's `≤` half), and new `s2_dev_mul_one` (`dev Φ′ (a·b) 1 = C(a₁b₁)`,
the carry digit, by division uniqueness) with its height floor. Kill pattern: carry terms
and off-parity/out-of-grade main terms price `≥ m+1` and read `0`
(`twistRead_eq_zero_of_lt`); surviving on-parity terms factor through RP23's
`s2_twistRead_mul_modByMonic` at `m = Ha + Hb` and convert back through the floor bridge.
The carry `c` is handled as an abstract natural pinned by the LINEAR relation
`β%2 + β′%2 = (β+β′)%2 + 2c` (private aux), so every arithmetic goal stays omega-linear;
the public headline instantiates `c = (β%2)·(β′%2)` by the four-way parity check.

## Teeth (regressions against RP-1/RP23's landed values)

`tooth_conv_carry`: at `(5,5)`, `T=0`, the GENERAL formula reproduces the endpoint carry
`Rgc₁₀(Φ′²)(1) = 1·1 = 1`. `tooth_conv_low`: `Rgc₁₀(Φ′²)(0) = 0` — consistent with landed
`R₁₀(Φ′²) = X`. `tooth_conv_prevGrade`: plain law at `(5,2)` gives `Rgc₇(Φ′·x)(0) = 1`, and
`tooth_conv_prevGrade_matches` pins the same value against RP-1's landed `R₇(x·Φ′) = 1`.
`tooth_mul_poly` + `tooth_mul_poly_check`: the polynomial identity at `(5,5)` re-derives
`R₁₀(Φ′²) = X^1·(1·1) = X` — the general law reproduces both the landed value AND the
plain-shape refutation genre.

## What was deliberately NOT claimed

No exact-grade conjunct bundling and no arbitrary-input (junk-grade) product law (RP-6); no
inner residual product beyond S2 short digits and no normalized-residual twist absorption
(RP-5/RP-8); no `graded_scalar_nonzero` (RP-7); no `FGMNSourceData/Laws` instance (FD-0).
The ϖ-read ↔ `ε(α)·R(a)(z)` dictionary stays on C.22/C.25's recorded faithfulness boundary.
Flagged for human review (new general statements): `dev_mul_conv_split`,
`le_stageHeight_finsetSum`, `twistRead_finsetSum_of_le`, `ceil_le_dvHgt_of_le_dvSupp`,
`le_stageHeight_mul_modByMonic`, `s2_dev_mul_one`.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C130rp4.lean` — CLEAN (exit 0, 0 errors,
0 warnings, 0 sorry). `lake build Uniformity.ChapC.C130rp4` — success (8743 jobs). 22
`#print axioms` rows, ALL `[propext, Classical.choice, Quot.sound]` (Lean-core only;
0 `sorryAx`); no new axiom, no `unsafe`, no statement touched, no other file modified
(`git status` on `leanfinal/Uniformity` shows only this file plus NP3's own in-flight
`C130np3.lean`, untouched). No git commit (per brief).
