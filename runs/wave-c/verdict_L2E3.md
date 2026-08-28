# Verdict L2E3 — shared level-2 engine final nodes

Date: 2026-08-28

## FIVE ACCEPTANCE TESTS — STATUS FIRST

| acceptance test | status | exact result |
|---|---|---|
| **F1.4 / C.39 `dv2ResPoly_scalar`** | **RED — corrected-shape conflict** | Not declared.  With normalized `dv2Res_mul`/`dv2SlotCarryLaw`, the complement scalar is clean.  The signed extra root power requires the unsupplied identity `root ^ L.cocycle (pinHeight ...) (complementConst ...) = 1`.  Reintroducing it into normalized `dv2Res` would contradict the binding L2E1/L2E2 correction. |
| **F1.6 / C.64 `mult₂_readable`** | **LANDED, established `hh` supplier delta** | `C136l2e3.mult₂_readable` has both signed conclusion equalities byte-for-byte under the re-signed A-C.22 floor, with the already-established F-row binder delta `hh : 0 < F.h`.  It uses C134p1d/C134p1, the singleton complement side, and L2E-07 min/max laws. |
| **F1.5 / C.38 `dv2ResPoly_radical_eq`** | **PARTIAL — exact adapter landed** | `dv2ResPoly_radical_eq_of_scalar` proves the exact degree equality and every-monic-irreducible divisibility iff from a nonzero scalar identity.  `γg_ne_zero` lands with the allowed inherited dissection footprint.  The signed row remains blocked only by RED F1.4. |
| **D3-03 `Dv3ResSurv`** | **RED — missing depth-three datum adapter** | Not declared. `C136d0.Dv3ResSurv` reads `dv2Supp L Ψ₂ u₂ ℓ₂` with arbitrary inner data; L2E is rooted at a `LevelDatum` whose inner read is the bundled `dvSupp F _ L.u L.ℓ`.  No landed depth-three `LevelDatum`/operator adapter identifies these shapes. |
| **D3-10 `(85,2)` convolution** | **RED — depends on D3-03 adapter and fixed-grade read** | Not declared.  It cannot be an L2E-09 instance until the preceding adapter exists, and L2E-09 itself stops at the fixed-grade coefficient-read goal recorded below. |

Target: `leanfinal/Uniformity/ChapC/C136l2e3.lean`

## Node status

| node | status | landed result / exact open |
|---|---|---|
| **L2E-09 coefficientwise residual product** | **PARTIAL** | `dv2ResPoly_coeff_of_le`, `dv2ResPoly_coeff_of_gt`, and `dv2ResPoly_mul_of_coeff_convolution` land the complete polynomial coefficient assembly.  The latter exposes the one remaining premise `hconv` at the correct fixed product grade. |
| **L2E-10 complement specialization** | **PARTIAL** | `dv2SideSet_eq_singleton_zero_of_not_muDvd` proves the complement side is exactly `{0}`; min, max, and degree-zero corollaries land. `γg_ne_zero` lands.  The signed scalar itself is RED because it asks for the rejected normalized root factor. |
| **L2E-11 adapters + acceptance** | **PARTIAL** | F1.6 lands; the exact F1.5 scalar-to-radical adapter lands; the D3 adapter is absent, so D3-03/D3-10 do not elaborate. |

## L2E-09 exact failing subgoal

After endpoint and degree additivity and after expanding one coefficient with the generic
development convolution split, the missing statement is the fixed-grade read law represented
verbatim by the `hconv` premise of `dv2ResPoly_mul_of_coeff_convolution`:

```lean
dv2Res L (dev Ψ (g * z)
  (dv2SideMin L Ψ (g * z) u₂ ℓ₂ hngz + t * ℓ₂)) =
  ∑ t₁ ∈ Finset.range (t + 1),
    (if t₁ ≤ dv2SideDeg L Ψ g u₂ ℓ₂ hng then
      dv2Res L (dev Ψ g
        (dv2SideMin L Ψ g u₂ ℓ₂ hng + t₁ * ℓ₂)) else 0) *
    (if t - t₁ ≤ dv2SideDeg L Ψ z u₂ ℓ₂ hnz then
      dv2Res L (dev Ψ z
        (dv2SideMin L Ψ z u₂ ℓ₂ hnz + (t - t₁) * ℓ₂)) else 0)
```

The landed `C136l2e1.dv2Res_mul` handles each individual nonzero product.  It does not
handle the displayed sum: `dv2Res` normalizes at its input's own height.  Equal-grade
main-diagonal terms can cancel, raising the sum's own height, and no landed fixed-grade
additive read theorem converts that sum to the sum of the reads.  The absolute full read
has the required fixed-grade behavior, but `dv2ResPoly` is defined using `dv2Res`, not
`dv2FullRead`.

## F1.4 exact failing subgoal

The corrected normalized law yields no root factor.  Comparing it with signed C.39 and
cancelling the nonzero complement scalar and a nonzero block residual leaves exactly:

```lean
(AdjoinRoot.root L.r) ^
  L.cocycle
    (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne')
    (complementConst L f) = 1
```

No landed hypothesis trivializes this cocycle/root power.  This is the same obstruction
as L2E1's corrected-shape audit, now at the signed complement scalar.  The carry belongs
to `dv2FullRead`, not normalized `dv2Res`.

## D3 exact adapter mismatch

The demanded D3 carrier expands to:

```lean
C136d0.Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃
```

whose digit heights are `dv3Hgt L Ψ₂ u₂ ℓ₂ = dv2Supp L Ψ₂ _ u₂ ℓ₂`.  The current L2E
theorems accept only a `LevelDatum` and use `dv2Hgt L = dvSupp F _ L.u L.ℓ`.  The T2
`DeepTower`/`KeyChain` records do not construct the missing next `LevelDatum`, so there is
no type-correct `(g8,85,2)` instantiation to apply.  D3-10 inherits this mismatch.

## Verification and footprint

The required command was run after the skeleton and after every landed increment:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136l2e3.lean
```

Final exit status: `0`.

The coefficient extraction/assembly, singleton-side geometry, and scalar-to-radical
adapter use Lean core only. `γg_ne_zero` and `mult₂_readable` use exactly Lean core plus
the inherited allowlisted `Uniformity.Density.Tower.exists_dvDissection` supplier.
There is no `sorry`, new axiom, or D3-special assumption.  No landed or leanspec file was
edited, and no git operation was run.
