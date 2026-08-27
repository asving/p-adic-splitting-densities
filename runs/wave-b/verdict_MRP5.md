# VERDICT — unit MRP5 (node M3-RP5: the μ₃ recursive coefficient convolution)

**Status: LANDED — sorry-free, Lean-core-only, first-attempt green modulo two mechanical
signature fixes.**

Node M3-RP5 of `docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6: every μ₃ graded coefficient
of a product is the convolution of the factors' μ₃ coefficients, with μ₂ residual
multiplicativity doing the coefficient calculation.  Landed in
`leanfinal/Uniformity/ChapC/C132rp5.lean` (846 lines, node tag [M3-RP5, 2026-08-27]);
verified `lake env lean Uniformity/ChapC/C132rp5.lean` from `leanfinal/`, exit 0, no
warnings.  No existing file touched.

## The headline

`s2Mu3Coeff_mul` — at μ₃ exact grades (`S2Mu3ExactGrade β g`, `S2Mu3ExactGrade β' z`), for
EVERY `T`:

```
s2Mu3Coeff (β+β') (g·z) (T + s2Mu3Carry β β')
  = Σ_{t ≤ T} s2Mu3Coeff β g t · s2Mu3Coeff β' z (T−t)
```

with companions `s2Mu3Coeff_mul_zero_of_odd` (odd×odd: the index-0 coefficient of the
product vanishes — the carry-forced below-twist zero) and `s2Mu3Coeff_mul_of_prevGrade`
(even `β'`: plain convolution, published Cor 4.12(2)'s scope) — the exact μ₂ trio's shapes
(`C130rp4.lean:626-709`) one level up, RP-6's coefficient inputs.

## The GENUINELY-NEW mechanism (informal argument in the file docstring, §§1–5)

1. **Split**: `dev Φ₂ (g·z) S` = reduced main diagonal + carry diagonal
   (`dev_mul_conv_split_monic` — `C130rp4.dev_mul_conv_split` generalized off the frame to
   an arbitrary monic key; its proof needed only monicity + positive degree).
2. **Pricing kills**: carry diagonal ≥ m+1 STRICTLY (nv3b's sharp quotient bound + the odd
   step 21 forcing `⌈(2m+21)/2⌉ = m+11`); off-parity main terms ≥ m+1 (double round-up);
   survivors reindex onto `t ≤ T` by RP4's abscissa arithmetic.
3. **The new leg — reduction invisibility** (`eval_one_gradedRes_modByKey` +
   `eval_one_gradedRes_key_mul`): the main-diagonal term is the REDUCED product
   `(A·B) %ₘ Φ₂ = A·B − Φ₂·Q`, and the discrepancy `Φ₂·Q` is NOT killed by pricing (nv3b
   records its floor `≥ m` as tight) but by VALUE: at exact grade the strip +
   `s2NormRes_mul` factor its read through `N₂(Φ₂) = X+1` (`C130kp5.s2NormRes_composedKey`),
   which evaluates at the collapsed letter 1 to `1+1 = 0` in char 2
   (`C130rp2.tooth_char_two`).  This is the S2 shadow of the paper's own mechanism
   (`R_{r−1}(φ_r)` vanishes at `z_{r−1}`) — exactly where μ₂ residual multiplicativity
   enters, twice: termwise product read AND the reduction kill.
4. **Gate-free bridge** (`s2Mu3Coeff_eq_eval_of_le`): RP1's `s2Mu3Coeff_eq_eval` needs the
   gate; the convolution needs the floor-only form (off-gate slots price strictly above m,
   both sides 0).  New public lemma, RP6/RP8-reusable.
5. **ε ≡ 1 collapse VERIFIED to kill the ε-bookkeeping** (docstring point 5): the
   coefficient carries ε already collapsed (RP1's `s2Mu3EpsOf_eq_one`, every nonzero
   letter), so the published ε-cocycle never appears in any statement or proof; RP1's
   letter-display pin re-expands each side to the ε-dressed display for every letter.

## Teeth (non-vacuity, the carry genre)

`tooth_mu3Coeff_mul_Φ₂Φ₂ : s2Mu3Coeff 42 (Φ₂·Φ₂) 1 = 1` (convolution firing through RP0's
`tooth_Φ₂`, RP1's `tooth_mu3Coeff_Φ₂`, RP4's `tooth_carry_Φ₂Φ₂`) and
`tooth_mu3Coeff_mul_zero_Φ₂Φ₂ : s2Mu3Coeff 42 (Φ₂·Φ₂) 0 = 0`.

## Honesty scope

No polynomial-level `Polynomial.ext` assembly (`R₃(g·z) = X^c·(R₃g·R₃z)`) — that is RP6's
row.  The identification `s2GradedRes = R_{2,α}` remains RP1's inherited
OPEN-RP1-TRANSPORT leg (2); no theorem here consumes it.

**Flagged for human review** (new statements): `dev_mul_conv_split_monic`,
`eval_one_gradedRes_key_mul`, `eval_one_gradedRes_modByKey`, `eval_one_gradedRes_mul_of_le`,
`s2Mu3Coeff_eq_eval_of_le`, `s2Mu3Coeff_mul`, `s2Mu3Coeff_mul_zero_of_odd`,
`s2Mu3Coeff_mul_of_prevGrade`.

## AxChk footer (all 13 printed declarations, verbatim from the green run)

```
'Uniformity.Density.Tower.C132rp5.dev_mul_conv_split_monic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.s2GradedRes_finsetSum_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.eval_one_gradedRes_key_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.eval_one_gradedRes_modByKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.eval_one_gradedRes_mul_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.eval_one_gradedRes_mul_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.ceil_le_dvSupp_dev' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.s2Mu3Coeff_eq_eval_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.s2Mu3Coeff_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.s2Mu3Coeff_mul_zero_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.s2Mu3Coeff_mul_of_prevGrade' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.tooth_mu3Coeff_mul_Φ₂Φ₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp5.tooth_mu3Coeff_mul_zero_Φ₂Φ₂' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Zero `sorry` (grep count 0), zero new axiom, zero `unsafe`.  Repo footprint: the one new
file + this verdict.
