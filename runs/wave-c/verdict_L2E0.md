# UNIT L2E0 verdict — L2E-00, L2E-01, L2E-02 LANDED (2026-08-28)

## Headline

The opening milestone of the shared level-2 multiplicative engine is **LANDED** in
`leanfinal/Uniformity/ChapC/C136l2e0.lean`.

The file is rooted at an arbitrary `LevelDatum`.  Its public declarations contain no S2
datum, S2 theorem, or S2 numeral.  The L2E-00 hypotheses expose `IsMuKey L Ψ`, an exact
key-grade pin, and the outer floor directly, so both the F1 context and the future D3
adapter can instantiate the same shapes.  L2E-02 uses `IsTestKey L Ψ` only where the
additional identification of the key's residual symbol with `L.r` is mathematically
needed.

Verification command, run after the skeleton and after every proof increment:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136l2e0.lean
```

Final run: **exit 0**, zero errors, zero warnings, zero `sorry`, and every AxCheck footprint
is exactly `[propext, Classical.choice, Quot.sound]`.

## Per-node status

| node | status | landed output |
|---|---|---|
| L2E-00 | **LANDED — shape lock** | `Dv2SlotCarryLawStatement`, `Dv2TwistProductLawStatement`; `Prop`-valued definitions only, with no assertion smuggled through the shape lock. |
| L2E-01 | **LANDED** | `dv2FullReadPoly`, `dv2FullRead`, `dv2FullRead_add_of_le`, `dv2FullRead_eq_zero_of_lt`.  The polynomial read keeps every aligned coefficient below the height line before the `dvResPoly` side-degree truncation, then evaluates through `AdjoinRoot.mk L.r`. |
| L2E-02 | **LANDED** | `dv2Hgt_testKey` pins the exact carry height `L.ℓ * L.seam`; `dv2FullRead_testKey` reconstructs the residual polynomial as `L.r` coefficientwise and closes with `AdjoinRoot.mk_self`. |

## Exact public declaration texts landed

```lean
def Dv2SlotCarryLawStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ (L : LevelDatum F H₀ hpin) (Ψ : Polynomial O), IsMuKey L Ψ →
  ∀ (KΨ : ℕ), dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞) →
  ∀ (u₂ ℓ₂ : ℕ), 0 < ℓ₂ → ℓ₂ * KΨ < u₂ →
  ∀ a b : Polynomial O, a.natDegree < Ψ.natDegree → b.natDegree < Ψ.natDegree →
  ∀ ka kb δ : ℕ, dv2Hgt L a = (ka : ℕ∞) → dv2Hgt L b = (kb : ℕ∞) →
    L.shift ka + L.shift kb = L.shift (ka + kb) + L.ℓ * δ →
    dv2Res L (dev Ψ (a * b) 0)
      = AdjoinRoot.root L.r ^ δ * (dv2Res L a * dv2Res L b)

def Dv2TwistProductLawStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ (L : LevelDatum F H₀ hpin) (Ψ : Polynomial O), IsMuKey L Ψ →
  ∀ (KΨ : ℕ), dvSupp F Ψ L.u L.ℓ = (KΨ : ℕ∞) →
  ∀ (u₂ ℓ₂ : ℕ), 0 < ℓ₂ → ℓ₂ * KΨ < u₂ →
  ∀ a b : Polynomial O, a.natDegree < Ψ.natDegree → b.natDegree < Ψ.natDegree →
  ∀ ka kb : ℕ, dv2Hgt L a = (ka : ℕ∞) → dv2Hgt L b = (kb : ℕ∞) →
    dv2Res L (dev Ψ (a * b) 0)
      = AdjoinRoot.root L.r ^ L.cocycle ka kb * (dv2Res L a * dv2Res L b)

noncomputable def dv2FullReadPoly (L : LevelDatum F H₀ hpin) (k : ℕ)
    (P : Polynomial O) : Polynomial (F.stageField H₀ hpin) :=
  open Classical in
  ((Finset.range (k + 1)).filter
      (fun t => (L.shift k + L.ℓ * t) * L.u ≤ k)).sum fun t =>
    Polynomial.C
        (F.twistRead H₀ hpin ((k - (L.shift k + L.ℓ * t) * L.u) / L.ℓ)
          (dev F.key P (L.shift k + L.ℓ * t)))
      * Polynomial.X ^ t

noncomputable def dv2FullRead (L : LevelDatum F H₀ hpin) (k : ℕ)
    (P : Polynomial O) : AdjoinRoot L.r :=
  AdjoinRoot.mk L.r (dv2FullReadPoly L k P)

theorem dv2FullRead_add_of_le (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {A B : Polynomial O} {k : ℕ}
    (hA : (k : ℕ∞) ≤ dv2Hgt L A) (hB : (k : ℕ∞) ≤ dv2Hgt L B) :
    dv2FullRead L k (A + B) = dv2FullRead L k A + dv2FullRead L k B

theorem dv2FullRead_eq_zero_of_lt (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {A : Polynomial O} {k : ℕ} (hk : (k : ℕ∞) < dv2Hgt L A) :
    dv2FullRead L k A = 0

theorem dv2Hgt_testKey (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨ : IsTestKey L Ψ) :
    dv2Hgt L Ψ = ((L.ℓ * L.seam : ℕ) : ℕ∞)

theorem dv2FullRead_testKey (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) :
    dv2FullRead L (L.ℓ * L.seam) Ψ = 0
```

## Footprints

All eight public declarations print only Lean core:

```text
[propext, Classical.choice, Quot.sound]
```

No declaration inherits `exists_dvDissection` or any other project axiom.

## Opens handed to the next increment

1. L2E-03 must identify the full read with the total coherent `dv2Res` on exact reduced
   digits and prove its nonvanishing; the present file deliberately does not assert that
   bridge without the exact-height/degree fences.
2. L2E-04 must prove either shape lock, using `dv2FullRead_testKey` to kill the key term
   and `dv2FullRead_add_of_le` to split the product/remainder decomposition.
3. L2E-05--09 remain the pair-pricing, support/min-max, pin-addition, and coefficientwise
   convolution layers.  F1.4/F1.5/F1.6 and D3-03/D3-10 remain downstream and are not
   restated or specialized here.

Trust-boundary review remains required for the two L2E-00 statement shapes and the
`dv2FullReadPoly`/`dv2FullRead` definitions.  No landed or leanspec file was edited, no
aggregate import was changed, and no git operation was performed.
