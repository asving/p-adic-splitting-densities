# Verdict — unit RP78: S2-source plan nodes RP-7 + RP-8 — scalar nonzero + the normalized residual `R₃`

Date: 2026-08-25 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, rows RP-7
("Prove `graded_scalar_nonzero` under the exact `< 4` fence", deps RP-1, `degree_dev_lt`,
residue kernel API) and RP-8 ("Define total `R₃`, prove constant-term nonzero for nonzero
inputs, and compute key powers", deps RP-1, endpoint/side API), on RP-5/RP-6's landing
(verdict_RP56.md: `exists_slotOnGrade_of_exact`, `s2GradedRes_ne_zero_of_exact`) and RP-4's
product identities, under the U14 adjudication (`COR412_ADJUDICATION_2026-08-25.md` §3/§7:
Def 3.15 print-read — `R_r(g) = R_{r,α}(g)/y^{j₀}`, `j₀ = ⌊s(g)/e_r⌋`, `R_r(0) = 0`).
File created (the ONLY repo file touched): `leanfinal/Uniformity/ChapC/C130rp8.lean`
(691 lines, 35 public declarations + 3 private helpers + 1 shape-pin example; not added to
any roll-up; no leanspec/ or other units' files touched; NO git commit).

## RP-7 — `graded_scalar_nonzero` under the `< 4` fence (published Thm 4.1 + Cor 4.9(1))

★ **`s2_graded_scalar_nonzero`** — the C130fg field shape verbatim at the concrete chain:
`∀ β g, S2ExactGrade β g → deg g < deg ((s2DepthTwoKeyChain).keyAt 2) → g ≠ 0 →
(R_β(g)).coeff 0 ≠ 0`; worker `s2GradedRes_coeff_zero_ne_zero_of_exact` (numeric `< 4`
fence); FD-0 pin `s2_graded_scalar_nonzero_fills` (for ANY `FGMNSourceData` with
`nextValue = s2Hgt₂`, `gradedResidual = s2GradedRes` — the fence numeral is DERIVED from
`K`'s own `keyAt_degree` law at live stage 2, not assumed; `s2KeyChain_keyAt_two_natDegree
= 4 = Dcum 2`).

**How the fence enters (the row's "work it out honestly" charge)**: ONLY as
`deg g < 2·deg Φ′` — the `Φ′`-development stops at slot 1, so RP-5's gate witness sits at
abscissa `s ≤ 1` (slots `≥ 2` have zero digit → `⊤` height → on no line, B.04 + C127), i.e.
at `y`-power `⌊s/2⌋ = 0`, where the exact-height ϖ-read is nonzero (the new shared core
`s2GradedCoeff_ne_zero_of_slotOnGrade`: gate → exact height → C.23's `slotRes_ne_zero`
through `s2_twistRead_eq_slotRes`).  No differently-shaped fence needed: at S2,
`deg (keyAt 2) = e₂f₂·deg Φ′ = 2·deg Φ′ = 4` on the nose.  The residual "concentrated at
y-order 0" intuition is TRUE below the fence and needs no separate lemma.  **The fence is
SHARP** (`tooth_scalar_fence_sharp` + `tooth_key_sq_natDegree`): `Φ′²` has degree exactly 4,
exact grade 10, and scalar `0` (`R₁₀(Φ′²) = X`) — U9 Q2's "fence is ESSENTIAL" ruling,
machine-witnessed.  `tooth_scalar_fires`: the law fires on the grade-5 key.

## RP-8 — the total normalized residual `s2NormRes` (published Def 3.15)

* **`s2GradeOf g := (dvSupp … g 5 2).toNat`** — the total grade extraction; for `g ≠ 0` it
  IS the unique exact grade (`S2ExactGrade_s2GradeOf`, `s2GradeOf_eq_of_exact`; RP-0's
  existence/uniqueness), so the normalization is anchored at Def 3.15's own `α = μ(g)`.
* ★ **`s2NormRes g`** — strip the minimal `y`-power (`divX` iterated `natTrailingDegree`
  times) from `s2GradedRes (s2GradeOf g) g`; C130fg `normalizedResidual` shape-pinned.
  **The strip pin** (★ `s2GradedRes_natTrailingDegree_eq`) certifies the trailing-degree
  strip IS Def 3.15's `j₀ = ⌊s(g)/e₂⌋ = dvSideMin g / 2`: every on-line slot reads nonzero
  (the shared core) and everything left of C.07's left endpoint is off-line.  Junk totality:
  the ONLY gradeless input is `0` (RP-0), and there `s2NormRes 0 = 0` is published Def
  3.15's OWN zero clause (`s2NormRes_zero`; sharp: `s2NormRes_eq_zero_iff`).
* ★ **constant term NONZERO** (`s2NormRes_coeff_zero_ne_zero`, the Cor 4.9(3) genre):
  `g ≠ 0 → (R₃(g)).coeff 0 ≠ 0` — RP-5's nonvanishing + the strip (the stripped constant
  term is the trailing coefficient).  Corollary `s2NormRes_ne_zero`.
* **reconstruction** (`s2NormRes_mul_X_pow_of_exact`, RP-9's consumable):
  `R₃(g)·y^{j₀} = R_β(g)` at the exact grade — Def 3.15's display, the shape from which
  RP-9/RP-10 derive `y`-order addition and twist absorption (U14 §7); master coefficient
  laws `s2NormRes_coeff`/`_of_exact`; grade-witness independence `s2NormRes_of_exact`.
* ★ **key powers** (`s2GradedRes_key_pow` + `s2NormRes_key_pow`, published eq (11) at ALL
  `k`, by induction through RP-4's twisted product law — the odd×odd carry `y^{k%2}`
  composes the floor `⌊(k+1)/2⌋ = ⌊k/2⌋ + k%2`): `R_{5k}(Φ′^k) = y^{⌊k/2⌋}` and
  `R₃(Φ′^k) = 1`; in particular **`s2NormRes_key : R₃(Φ′) = 1`** — the
  `Rres_keyAt`/`carried_key_residual` GENRE (A-C.11) at the development key `Φ′ = keyAt 1`
  (FGMN's `φ₂`) — and `s2NormRes_one : R₃(1) = 1`.  New base tooth `tooth_gradedRes_one`
  (`R₀(1) = 1`), grade bank `S2ExactGrade_one`/`S2ExactGrade_key_pow` (`μ₂(Φ′^k) = 5k`).
* **the degree law FALLS OUT** (★ `s2NormRes_natDegree_of_exact`, Cor 4.9(3)'s
  `deg = (s′−s)/e`): `deg R₃(g) = (dvSideMax g − dvSideMin g)/2`, via the right-endpoint pin
  `s2GradedRes_natDegree_eq` and the strip bookkeeping `s2NormRes_natDegree_add_of_exact`.
* **twist absorption, witnessed** (`tooth_normalized_mul_absorbs`): on the odd×odd pair
  whose PLAIN graded law is machine-refuted, `R₃(Φ′²) = 1 = R₃(Φ′)·R₃(Φ′)` — the
  single-pair witness of `normalized_mul` (Cor 4.12(3)); `tooth_normRes_key_sq`,
  `tooth_normRes_X` regressions.  Generic toolkit: `coeff_divX_iterate`,
  `divX_iterate_mul_X_pow`, `divX_iterate_X_pow`.

## What was deliberately NOT claimed

No `normalized_mul` (RP-9/RP-10 — only its single-pair tooth); no `y`-order addition law
(RP-9); no `carried_key_residual` FIELD instance (the literal S2 field is about
`keyAt 2 = composedKey`, FGMN's `φ₃` — KP-6's row); no `FGMNSourceData/Laws` instance
(FD-0).  The ϖ-read ↔ `ε(α)·R(a)(z)` dictionary stays on C.22/C.25's recorded boundary.
Flagged for human review (new statements): `s2GradeOf`, `s2NormRes` (trailing-degree strip,
certified = `⌊s(g)/e₂⌋` by the strip pin), `s2_graded_scalar_nonzero` (+worker/fills), the
two endpoint pins, the degree law.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C130rp8.lean` — CLEAN (exit 0, 0 errors,
0 warnings, 0 sorry).  Dependency stack prebuilt via `lake build Uniformity.ChapC.C130rp6`
(8745 jobs, success).  38 `#print axioms` rows, ALL exactly
`[propext, Classical.choice, Quot.sound]` (0 `sorryAx`); no new axiom, no `unsafe`, no
statement touched; `git status leanfinal/Uniformity` shows ONLY the new `C130rp8.lean`.
Toolchain note: the pinned `omega` fails on the combined goal
`5*k % 2 * (5 % 2) + k/2 = (k+1)/2` (incompleteness witnessed in scratch), worked around by
pre-reducing `5*k % 2 = k % 2` (itself omega-provable) before the final call.
No git commit (per brief).
