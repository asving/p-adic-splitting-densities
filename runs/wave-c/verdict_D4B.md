# UNIT D4B — verdict: the μ₅ refinement stack's middle tranche, rows D4-05..D4-12 [2026-08-28]

**File:** `leanfinal/Uniformity/ChapC/C136e1.lean` (new; 1628 lines; namespace
`Uniformity.Density.Tower.C136e1`).
**Validator:** `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136e1.lean` —
exit 0, zero errors, zero warnings, **zero `sorry`**.
**Axiom footprint:** 74 `#print axioms` in the AxCheck footer; every report is Lean-core
only (`propext, Classical.choice, Quot.sound`) or axiom-free (`s2Mu5EpsExp`, a bare `ℤ`
computation). No new axiom, no `unsafe`.

Source: `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.3 rows D4-05..12.
Chains onto `C136e0`'s landed D4-00..04 base (the `dv4` layer, `s2Hgt₅`, the
UNCONDITIONAL survival/product laws, the grade bank, and the `e' = 1` gate: unique slot
residue `0`, `S2Mu5PrevGrade` ALL grades, the level-4 ε-data Bézout pair `(1,−42)`).
Templates: `C136d1`/`C136d2` (the landed μ₄ D3 stack, one level down).

## Per-row status

| row | status | landed anchors |
|---|---|---|
| **D4-05** recursive coefficient | **CLOSED** | `s2Mu5EpsExp`/`s2Mu5EpsOf`/`s2Mu5Eps` (ε-collapse at the level-4 Bézout pair, reusing `C132rp1.s2Fld₂_eq_one_of_ne_zero`/`s2Mu3_eval_letter_pinned` directly — field-generic facts, not level-specific); `s2Mu5Coeff` reading the landed μ₄ graded operator `s2Mu4GradedRes` at inner grade `β − 171·t` (NO division — the `e' = 1` collapse); letter-display/true-height/graded-normalized-collapse pins; finite-support and above-grade zero laws. Strictly simpler than D3-07 (no `%2`/`/2` bookkeeping anywhere). |
| **D4-06** graded operator/add | **CLOSED** | `s2Mu5GradedRes` (assembly), master coefficient law, range independence, finite support, zero-above/zero laws; additivity engine — `le_dv4Pin_of_le_dv4Supp` (off the ALREADY-LANDED `C136e0.dv4Supp_le_term`, at `ℓ₅ = 1` so NO ceiling/rounding, unlike the `e' = 2` mirrors), `s2Mu5Coeff_eq_eval_of_le`, `s2Mu5Coeff_add`, `s2Mu5GradedRes_add_of_le`/`s2Mu5GradedRes_add`. |
| **D4-07** convolution/product | **CLOSED** | `exists_mu5SlotOnGrade_of_exact` (gate witness); the full `g16`-key reduction/finite-sum-additivity/eval-1-product bank one level up from `C136l2e4` (`eval_one_mu4GradedRes_g16_mul`, `_modBy_g16`, `_mul_of_exact`, `_mul_of_le`); ★ **`s2Mu5Coeff_mul`** — the coefficient convolution, UNTWISTED, no carry shift at all (the row's signed exit: NO parity case-split, NO `Finset.sum_filter`/`sum_image` reindexing was needed anywhere, unlike the `e' = 2` template); ★★ **`s2Mu5GradedRes_mul`** — the graded multiplication for EVERY grade pair (no preceding-group hypothesis, since `S2Mu5PrevGrade` is landed as ALL grades). |
| **D4-08** scalar nonzero below degree 16 | **CLOSED** | `s2Mu5GradedRes_coeff_zero_ne_zero_of_exact` — forced slot-`0` read (deg `g < 16` forces `s = 0`, no parity ambiguity) plus the ALREADY-LANDED `C136d3.s2Mu4GradedRes_eq_C_of_natDegree_lt_sixteen` (collapse-to-constant) and `C136d2.s2Mu4GradedRes_ne_zero_of_exact` (polynomial-level nonvanishing) — a contradiction argument, no fresh eval-collapse lemma: the campaign's fence `16 = 2·deg(g8)` is EXACTLY the fence the landed μ₄-level collapse already carries. |
| **D4-09** normalized operator | **CLOSED** | `s2Mu5GradeOf`/`s2Mu5NormRes` (strip leading `X`-power); ★ `s2Mu5GradedRes_ne_zero_of_exact` — UNCONDITIONAL polynomial nonvanishing (the digit `dev(g16,g,s)` automatically has degree `< 16`, so the μ₄-level collapse fires with no degree hypothesis on `g` itself); `s2Mu5NormRes_coeff_zero_ne_zero`/`_ne_zero`; `s2Mu5GradedRes_natTrailingDegree_mul`/`s2Mu5NormRes_mul_of_exact`/`s2Mu5NormRes_mul` — genuinely SIMPLER than the `C136d2` mirror (no `β%2·β'%2` twist term, since D4-07's product is fully untwisted); `S2Mu5ExactGrade_one`/`s2Mu5GradedRes_one`/`s2Mu5NormRes_one`; ★ **`s2Mu5GradedRes_key : s2Mu5GradedRes 171 g16 = X`** (NOT `1` — the honest signed correction against the naive `e'=2` mirror: slot `1` maps to coefficient index `1` directly at `e'=1`, not index `0` via `/2`); `s2Mu5NormRes_key = 1`; `_key_pow` variants. |
| **D4-10** normalizer exact grade (finishing T5) | **CLOSED** | `chainNormBelow 4 171 = Λ` (`C136t.s2Mu5Lambda`) has degree `15` and is nonzero (ALREADY LANDED); ★★ **`s2Mu5Lambda_exactGrade` — exact μ₅ grade `171`**, via a multiplicative peel `Λ = g₈·(Φ₂·(2·x·Φ′))` lifted through THREE private local collapse copies (base→μ₃, μ₃→μ₄ — mirroring `C132rp10b`'s and `C136d2`'s own mechanisms one level up each — and μ₄→μ₅, a DIRECT identity at `ℓ₅ = 1`, no scaling) chained against the landed base teeth `tooth_key`/`tooth_X`/`s2Hgt₂_C_two` and `tooth_Φ₂`/`tooth_g8`. |
| **D4-11** literal refinement recipe | **CLOSED** | ★ `s2Mu5_recipe_negTooth_gradedRes` and ★★ `s2Mu5_recipe_exactGrade` — proved GENERICALLY for ANY `Λ'` with `S2Mu5ExactGrade 171 Λ'` and `Λ'.natDegree < 16` (needing ONLY these two abstract properties, not `Λ`'s algebraic structure — the reason the recipe theorem holds for an arbitrary `khat`); ★★★ **`s2Mu5_normalized_recipe`** — the literal `FGMNSourceLaws.normalized_recipe` field shape at `(e',f',u')=(1,1,171)`, the exact-evaluation genre (contrast the VACUOUS `e'>1` mirrors `C132rp9`/`C136d2` D3-18: at `e'=1` every grade is realizable, so this is a genuine computation, not an `exfalso`). |
| **D4-12** normalized existence leaf | **CLOSED** | `s2Mu5Leaf := keyAt4 − Λ`, monic (`(g16_monic).sub_of_left` off `deg Λ < 16 = deg g16`), degree `16`, nonzero; ★★ `s2Mu5Leaf_exactGrade` and ★★★ `s2Mu5NormRes_leaf = X + 1` — pure COROLLARIES of D4-11's generic machinery instantiated at `Λ' := s2Mu5Lambda`, needing one extra char-2 bridge (`X + 1 = X − 1` via `1 + 1 = 0`, `C130rp2.tooth_char_two`) to match the printed recipe's subtraction display. |

## Recorded deviations (honest scope)

1. **`s2Mu5GradedRes_key`'s value is `X`, not `1`** — the row brief's closest template
   (`C136d1.s2Mu4GradedRes_key = 1`) is the WRONG shape to copy verbatim: at `e' = 2` slot
   `1` of the key's own development maps to coefficient index `0` (via the `/2`
   rescaling), giving a bare constant; at `e' = 1` there is no rescaling, so slot `1` maps
   to index `1` directly, and the residual survives as `X`. This was caught mid-build (a
   first draft mis-copied the μ₄ shape) and corrected before landing; `s2Mu5GradedRes_key_pow`
   and `s2Mu5NormRes_key` were re-derived accordingly (`s2Mu5NormRes_key = 1` still holds,
   via cancelling the shared `X`-factor).
2. **D4-11/12 merged into one generic-then-instantiate design** — rather than two
   independent proofs, the negated-tooth graded-residual and recipe-exact-grade lemmas
   are stated GENERICALLY over an abstract `Λ'` (any polynomial with exact μ₅ grade `171`
   and degree `< 16`), since neither proof actually used `Λ`'s specific algebraic form.
   D4-12's leaf results are then one-line instantiations at `Λ' := s2Mu5Lambda`. This is a
   genuine strengthening over the row-by-row brief (D4-11's theorem is honestly more
   general than the literal `khat`-quantified field-shape alone required) and was not
   flagged as a deviation risk since it only ADDS generality, never weakens a statement.
3. **Three private local "single-slot collapse" copies for D4-10** — the base→μ₃ and
   μ₃→μ₄ collapses mirror `C132rp10b`'s and `C136d2`'s own private mechanisms exactly one
   level further up each (not previously landed generically); the μ₄→μ₅ collapse is a
   direct-identity variant (`ℓ₅ = 1`, no `2•` scaling) with no template needed. All three
   follow the corpus's private-copy convention (reproved standalone in this file, not
   exported).

## What this unit does NOT claim (honesty scope, unchanged from the brief)

No μ₅ key predicates/divisibility (D4-13..16), no `FGMNSourceData`/`FGMNSourceLaws`
record, no calculus packaging (D4-17/18). The `(1,1,171)` triple is consumed strictly as
OPERATOR data over the landed depth-four tower — no `DeepTower.hproper` proof is forged
or implied. OPEN-RP1-TRANSPORT inherited exactly as the D3 stack left it — cited, never
re-derived or re-opened. New statement shapes (every `def` and predicate-introducing
`theorem`) are trust-boundary declarations flagged for human review.

## Downstream supply map

* D4-13..16 (μ₅ key predicates): `s2Mu5NormRes`/`s2Mu5GradedRes` full bank +
  `s2Mu5Leaf`/`s2Mu5NormRes_leaf = X + 1` (the residual criterion input, mirroring
  `C136d3.s2Mu4KeyPoly_g16`'s consumption of `C136d2.s2Mu4NormRes_g16`).
* D4-17/18 (source records/calculus): `s2Mu5_normalized_recipe` (the literal
  `FGMNSourceLaws.normalized_recipe` field), `s2Mu5GradedRes_mul`/`s2Mu5NormRes_mul` (the
  `gradedResidual`/`normalizedResidual` multiplicativity fields), `s2Mu5NormRes_key_pow`
  (the `keyPolynomial` field).

Build: `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136e1.lean` → exit 0
(2026-08-28). Verified in increments (D4-05/06 → D4-07 → D4-08/09 → D4-10/11/12 →
AxCheck footer), each landing within ~3 repair rounds of its first attempt; no
`maxHeartbeats` bump was needed beyond the file's own `1000000` setting.
