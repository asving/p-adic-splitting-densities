# VERDICT — UNIT D4C (rows D4-13..D4-18): the μ₅ refinement stack's CLOSER

**File**: `leanfinal/Uniformity/ChapC/C136e2.lean` (1797 lines, imports `C136e1` + `C130lb`)
**Build**: GREEN — `lake env lean Uniformity/ChapC/C136e2.lean` exits clean, zero errors,
zero warnings, zero `sorry`.
**Axioms**: all 68 `#print axioms` reports in the AxCheck footer read exactly
`[propext, Classical.choice, Quot.sound]` — Lean core only, no cited axiom enters.

## ★★★ THE μ₅ MILESTONE (D4-18) LANDED

`s2Mu5_calculus_nonempty : Nonempty (FGMNCalculus (s2DepthFour h2 hq) 1 1 171)`
— the deep-witness campaign's key-tail closer at `(e', f', u') = (1, 1, 171)`, via
`fgmn_model_calculus_nonempty` fired at the D4-17 records, UNCONDITIONAL (no open
hypothesis, Lean-core footprint).  No depth-five `keyAt`/`KeyChain` was built (out of
scope per the row; the triple is OPERATOR data over the landed `s2DepthFour`).

## Per-row table

| Row | Status | Declarations |
|---|---|---|
| **D4-13** | **LANDED** | `S2Mu5InitialEquiv`, `S2Mu5Dvd`, `S2Mu5Minimal`, `S2Mu5Irreducible`, `S2Mu5KeyPoly`; law bank `s2Hgt₅_neg`, `s2Hgt₅_eq_top_iff`, `S2Mu5InitialEquiv_{refl,symm,trans,equivalence,hgt_eq,zero_left,zero_right}`, `S2Mu5ExactGrade_of_initialEquiv`, `s2Mu5GradeOf_eq_of_initialEquiv`, `S2Mu5Dvd_{of_dvd,self,zero,congr_right}`, `s2Mu5NormRes_eq_of_initialEquiv`, `mu5NormRes_dvd_of_S2Mu5Dvd`, `s2Mu5GradedRes_eq_C_of_natDegree_lt_sixteen`, `s2Mu5NormRes_isUnit_of_natDegree_lt_sixteen`, `S2Mu5Dvd_of_mu5NormRes_dvd`, ★ `S2Mu5Dvd_iff_mu5NormRes_dvd` (monic `deg ≤ 16` nonunit-residual scope).  The backward translation ported with NO case split — the one-slot remainder mechanism, as the blueprint predicted. |
| **D4-14** | **LANDED** | `s2Mu5Irreducible_of_irreducible_normRes`, `s2Mu5Minimal_of_not_isUnit_normRes`, `s2Mu5Minimal_of_irreducible_normRes`, `s2Mu5_key_criterion` (fence `1·1·deg(keyAt 4) = 16`), ★ `S2Mu5KeyPoly_leaf`, ★ `S2Mu5KeyPoly_g16` (THE CARRIED KEY), `s2Mu5NormRes_g16`, `tooth_g16_mu5_vs_mu4`.  **Recorded deviation**: the μ₄ odd-carry parity obstruction has no μ₅ analogue; the carried key's minimality/primality were proved by the flagged SHORTCUT — the grade-comparison route through e1's landed `s2Mu5GradedRes_key = X` (`not_mu5Dvd_g16_of_coeff_zero_ne`: anything `g16` μ₅-divides has vanishing residual scalar, while D4-08 protects everything of degree `< 16`); primality is the slot-zero dichotomy with zero parity cases.  The shortcut worked on the first attempt — no port of C136d3 Parts 0–2 was needed. |
| **D4-15** | **LANDED** (incl. optional [DWR] legs) | `s2Mu5_key_irreducible`, `s2Mu5Leaf_irreducible`, `s2_g16_irreducible`, `s2Mu5Leaf_ne_g16`, `s2Mu5Leaf_map_irreducible`, `s2_g16_map_irreducible` (Gauss forward direction via `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`; `import Uniformity.ChapC.C130lb` added as predicted), `s2Mu5_leaf_keyAt4_coprime_fractionMap`, ★ `s2Mu5_leafSq_keyAt4_coprime_fractionMap` (the row's literal ask).  Coprimality via `Irreducible.coprime_iff_not_dvd` (mathlib, Bézout scope) + `Irreducible.associated_of_dvd` + `Polynomial.eq_of_monic_of_associated` + fraction-map injectivity.  **Optional [DWR] §11.1 legs ALSO landed**: `s2_g16_add_one_monic`, `s2_g16_add_one_natDegree`, `s2_g16_add_one_coprime_g16` (Bézout witness over `O[x]` itself), `s2Mu5_leaf_g16_add_one_coprime_fractionMap`. |
| **D4-16** | **LANDED — GENERAL CONVERSE, digit-ledger-free** | Bank: `s2Mu5Minimal_natDegree_sixteen_dvd`, `s2Mu5Minimal_exactGrade`, `s2Mu5KeyPoly_natDegree_sixteen_dvd`, `s2Mu5KeyPoly_exactGrade`, `s2Mu5KeyPoly_gradedRes_natDegree`; ★★ `s2Mu5_residual_to_initial` (Prop 5.6 (2)→(3) at μ₅), `s2Mu5_initial_iff_residual` (the full field shape), `not_S2Mu5InitialEquiv_leaf_g16` (the concrete tangent fact, `X+1 ≠ 1`).  **The ~680-line μ₄ digit-bound bank was NOT ported**: the divisibility pin's pair bound `μ₄(A)+μ₄(Q) ≤ 170` is VALUATION MULTIPLICATIVITY (`S2Mu4ExactGrade_mul`) plus ONE top-slot read on the monic degree-16 product (`dev_top_eq_one` at slot 2 of the `g₈`-development) — tight against the [G5F] floor `170 < 171`.  New structural ingredient vs. μ₄: a μ₅ key's residual strip is trivial (`ntd = 0`) UNLESS the key is in the `∼ g16` fiber (`normRes = 1`, `deg = 16`, `gradedRes = X`) — the trailing dichotomy `key_trailing_dichotomy`, proved by one-step deflation through μ₅-primality. |
| **D4-17** | **LANDED** | `s2Mu5_hex` (existence realized by the LANDED LEAF — genuinely non-vacuous), `s2Mu5_normalized_recipe_field` (the recipe in the μ₅-graded display; NON-VACUOUS, unlike every `e'=2` predecessor — note e1's D4-11 statement reads the scalar slot through the μ₄ operator, the field demands the μ₅ read; both scalars are the unit `1` of 𝔽₂, bridged here), `s2Mu5_graded_scalar_nonzero`, `S2Mu5KeyPoly_keyAt_four`, `s2Mu5NormRes_keyAt_four`, `s2LetterFour`, `s2LetterFour_ne_zero`, ★★ `s2SourceDataFour : FGMNSourceData (s2DepthFour h2 hq) (s2DepthFourKeyChain h2 hq) 1 1 171` + 7 `rfl` read pins, ★★ `s2SourceLawsFour` — all THIRTEEN laws UNCONDITIONAL. |
| **D4-18** | **LANDED** | ★★★ `s2Mu5_calculus_nonempty : Nonempty (FGMNCalculus (s2DepthFour h2 hq) 1 1 171)` — the μ₅ milestone. |

## Deviations / notes for review

1. **New-statement trust boundary**: every `def` (`S2Mu5InitialEquiv/Dvd/Minimal/
   Irreducible/KeyPoly`, `s2LetterFour`, `s2SourceDataFour`) is a fresh statement shape,
   flagged for human review per repo policy.  All are byte-level mirrors of the μ₄
   D3-15/D3-18 shapes with `(s2Hgt₄, 85, 2, g8) ↦ (s2Hgt₅, 171, 1, g16)`.
2. **D4-14 mechanism swap** (recorded in the file's section headers): parity obstruction
   → grade-comparison obstruction (`gradedRes(g16) = X` kills scalar slots).  This is a
   genuinely different (and simpler) proof than C136d3's, not a port.
3. **D4-16 mechanism swap**: seven inner cleared digit bounds → valuation
   multiplicativity + top-slot read (`mu4_pair_grade_le`).  The general converse holds
   at μ₅ (it was NOT downgraded to the narrow fallback).
4. **D4-17 recipe display bridge**: e1's `s2Mu5_normalized_recipe` (D4-11) displays the
   scalar slot through `s2Mu4GradedRes`; the `FGMNSourceLaws.normalized_recipe` field
   demands `s2Mu5GradedRes`.  `s2Mu5_normalized_recipe_field` proves the field shape from
   the landed one (both scalar reads are `1` in the 2-element field, by
   D4-08 μ₅-side / the landed μ₄ collapse μ₄-side).  No landed statement was touched.
5. New generic helper `dev_top_monic` (private): the `Ψ`-adic top digit of a monic
   polynomial of degree `m·deg Ψ + r` (`r < deg Ψ`) is monic of degree `r` — the
   general-`r` companion of `C131v.dev_top_eq_one`, proved by the same induction.

## Verification transcript

- `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136e2.lean`
  → exit 0, no output (after each row and at final state, 2026-08-29).
- AxCheck footer: 68 `#print axioms`, all exactly `[propext, Classical.choice, Quot.sound]`.
- `grep -c sorry` → 1 (the word inside the module docstring's status line; zero proof sorries).
