# UNIT L2E4 verdict — generic `hconv` audited; D3-10 landed

Date: 2026-08-28  
Target: `leanfinal/Uniformity/ChapC/C136l2e4.lean`

## STATUS FIRST

| row | status | exact result |
|---|---|---|
| **`hconv` fixed-grade read law** | **RED — refuted at the bare normalized carrier** | A24A's off-side-junk channel does **not** apply at the requested product-support slot, but a separate anchor-normalization obstruction remains. The absolute fixed-grade read weights a summand by a power of `AdjoinRoot.root L.r` determined by the offset of its own residual window from the common grade base. The quoted `hconv` sums the own-height `dv2Res` values without those weights. `fixedGrade_unweighted_add_forces_letter_one` machine-checks the terminal cancellation: identifying a nonzero one-step shifted contribution `η*b` with `b` forces `η = 1`; general `LevelDatum` supplies no such hypothesis. Therefore the quoted unconditional statement is not declared as a theorem. |
| **fire `dv2ResPoly_mul_of_coeff_convolution`** | **RED — cannot fire honestly** | The landed consumer remains correct as a conditional assembly theorem, but its exact `hconv` premise cannot be supplied for bare `dv2Res`. Consequently no unconditional generic `dv2ResPoly` product theorem is asserted in this unit. |
| **D3-10 μ₄ coefficient convolution `(85,2)`** | **GREEN — LANDED by the D3AD cheap mirror** | `C136l2e4.s2Mu4Coeff_mul` proves the coefficient convolution with the D3-09 carry. It works through the genuinely fixed-grade inner operator `s2Mu3GradedRes`, not by a false valuation-polymorphic instantiation of the `LevelDatum`-rooted engine. Lean core only. |

## 1. `hconv`: exact adjudication

The requested slot is

```lean
dev Ψ (g * z)
  (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz + t * ℓ₂)
```

with `t ≤ dv2SideDeg ...`. Thus it lies at the fixed product grade. Strict pair pricing
kills every off-line main term and the carry diagonal. This verifies the requested A24A
scoping point explicitly:

> **A24A's unguarded off-side coefficient channel does not bite here.**

That does not make the bare normalized read additive. At a common absolute grade, let `j₀`
be the common lattice base and suppose a term's own side begins at
`jm = j₀ + δ·L.ℓ`. The level-1 identity proved by the existing `lineRes_eq_shift` mechanism
has the form

```text
absolute line read = own residual polynomial * X^δ.
```

After evaluation at the level letter `η := AdjoinRoot.root L.r`, this is

```text
absolute read = η^δ * own-height normalized read.
```

Therefore absolute-read additivity gives a **weighted** diagonal sum. To obtain the quoted
unweighted `hconv`, the missing terminal equation is exactly

```text
∑ p, η^(δ_p) * R_p = η^(δ_total) * ∑ p, R_p,
```

or equivalently

```text
∑ p, (η^(δ_p) - η^(δ_total)) * R_p = 0.
```

No pair-pricing, survival, or product-height hypothesis identifies the offsets `δ_p`.
Already for two nonzero contributions with offsets `0` and `1`, the required cancellation
reduces to

```lean
a + η * b = a + b
```

and `C136l2e4.fixedGrade_unweighted_add_forces_letter_one` proves that this forces
`η = 1`. A general `LevelDatum` assumes `L.r` monic/irreducible, positive degree, and
nonzero constant coefficient; it does **not** assume `AdjoinRoot.root L.r = 1`.

This is the exact obstruction after the absolute-read accounting. It is independent of
A24A's off-side defect and remains on the support line.

## 2. Fired product law

`C136l2e3.dv2ResPoly_mul_of_coeff_convolution` still assembles a polynomial identity from
the quoted premise, but the premise is stronger than the valid absolute weighted law.
Firing it unconditionally would therefore certify a false normalization change. No theorem
with that claim was added.

The generic repair is a carrier change, not another pricing lemma: define the level-2
residual polynomial coefficientwise using a fixed absolute grade/anchor, or include the
required root-offset weights. Either repair is outside this unit because it changes the
signed carrier consumed by landed files.

## 3. D3-10 landed

The S2 μ₄ coefficient law is nevertheless valid and now proved:

```lean
theorem s2Mu4Coeff_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g)
    (hz : S2Mu4ExactGrade h2 hq β' z) (T : ℕ) :
    s2Mu4Coeff h2 hq (β + β') (g * z) (T + s2Mu4Carry β β')
      = ∑ t ∈ Finset.range (T + 1),
          s2Mu4Coeff h2 hq β g t * s2Mu4Coeff h2 hq β' z (T - t)
```

Proof route, mirroring `C132rp5` one level up:

- `dev_mul_conv_split_monic` at `g8` splits the main and carry diagonals.
- D3AD's landed `dv2Supp_mul_modByKey_eq` and
  `dv2Supp_add_le_key_quot_add` give the main floor and strict carry floor; the key grade
  is `42`, so `2·42 + 1 = 85` supplies the strict step.
- `s2Mu3GradedRes_add_of_le` and its finite-sum iteration read the convolution at one fixed
  inner grade. The carry and off-parity terms vanish above that grade.
- Reduction modulo `g8` is invisible after evaluation at the S2 letter `1`:
  `s2Mu3NormRes_g8 = X + 1`, whose value at `1` is zero in the two-element field.
- `s2Mu3NormRes_mul` supplies the surviving termwise products; D3-09's
  `s2Mu4Carry_parity` supplies the outer carry index.

This is precisely D3AD's cheap-mirror pattern: the nested inner valuation uses its landed
`dv2Supp` laws directly. No nonexistent depth-three `LevelDatum` or valuation-polymorphic
root is fabricated.

## Verification, repair log, and footprint

The required command was run after the skeleton, after each helper increment, and after
the D3-10 theorem:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136l2e4.lean
```

Final exit status: `0`.

The skeleton compiled first pass. The D3 mirror needed three mechanical repair batches:
namespace qualification for the side-min bank, local copies of two private `ℕ∞` cast
helpers, and one cast-normalization simplification. The generic attempt stopped at the
mathematical weighted/unweighted equation displayed in §1, not at an unresolved Lean
metavariable.

The AxCheck footer reports exactly `[propext, Classical.choice, Quot.sound]` for the
diagnostic, all fixed-grade helper laws, and `s2Mu4Coeff_mul`. There is no `sorry`, new
axiom, `unsafe`, or inherited `exists_dvDissection` citation. No landed or leanspec file was
edited; `C136f14b.lean` was not touched; no git operation was run.
