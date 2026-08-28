# UNIT F14C verdict — anchored carry lands; weighted assembly exposes a nonstationary-carry boundary (2026-08-28)

## TWO LEGS — STATUS FIRST

| honest remainder leg | status | exact result |
|---|---|---|
| **1. anchored/weighted digit-split convolution assembly** | **YELLOW — structural weighted assembler LANDED; digit-split supplier still open** | `C136f14c.dv2ResPolyAnchWeightedConv` records the honest antidiagonal weights, and `dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution` is the anchored twin of L2E3's conditional polynomial assembler. It compiles Lean-core. The premise identifying the fixed-grade read of `dev Ψ (g*z)` with that weighted antidiagonal has not been supplied from `dev_mul_conv_split_monic` + strict pair/carry pricing. No unweighted equality is asserted. |
| **2. absolute full-read carry law** | **GREEN — LANDED, universally inhabited** | `dv2FullRead_mul_of_eq` proves the exact-height core from `dv2FullReadPoly_eq_shift`, clean `dv2Res_mul`, inner side-min additivity, and explicit anchor-offset arithmetic. `dv2FullReadCarryLaw : Dv2FullReadCarryLawStatement O` handles zero factors and every strict-floor case by vanishing. This closes A24B's recorded-unproven definition, frame-generically. |

## FIRED SIGNED ROWS — STATUS SECOND

| signed row | status | exact result |
|---|---|---|
| **C.39 / F1.4 `dv2ResPolyAnch_scalar`** | **RED — not fired honestly** | Applying the now-proved carry law produces the slot weight `root ^ L.cocycle (M₂' - t*u₂) (complementConst L f)`. The enacted conclusion demands the single base-slot weight `root ^ L.cocycle M₂' (complementConst L f)` for every `t`. No enacted hypothesis or landed theorem makes this inner cocycle stationary under subtraction by `t*u₂`; `Nat.Coprime u₂ ℓ₂` is an outer-lattice condition and supplies no relation between `u₂` and `L.ℓ`. |
| **C.38 / F1.5 `dv2ResPolyAnch_radical_eq`** | **YELLOW — formal adapter LANDED; signed row cannot fire before C.39** | `dv2ResPolyAnch_radical_eq_of_scalar` transposes L2E3's adapter to the repaired carrier and is Lean-core. It gives the enacted degree/radical conclusion from any nonzero anchored scalar identity. Since C.39 is not available, the unconditional signed C.38 name is not declared. |

## 1. What landed in `C136f14c.lean`

### 1.1 Carry law

`dv2FullRead_mul_of_eq` rewrites each exact full read as

```text
root^((sideMin - shift grade)/L.ℓ) * dv2Res
```

using A24B's public `dv2FullReadPoly_eq_shift`. Inner support and side-min
multiplicativity give the product grade and add the three side minima; the supplied
shift equation then proves the exponent identity

```text
γ = δ + α + β.
```

The clean normalized law `C136l2e1.dv2Res_mul` finishes the exact case. The public
`dv2FullReadCarryLaw` extends it to L2E2's full floors-only statement: zero factors have
top height and zero read at every finite grade; if either requested grade is strictly
below its exact grade, both the corresponding factor read and the product read vanish.

### 1.2 Honest weighted carrier and assembler

`dv2ResPolyAnchWeightedConv` has coefficient `t`

```text
Σ t₁ ≤ t,
  root ^ L.cocycle (Mg - t₁*u₂) (Mz - (t-t₁)*u₂)
    * RAnch(g)[t₁] * RAnch(z)[t-t₁],
```

with the two side-degree guards explicit. This is precisely the weight suppressed by
the bare L2E3 `hconv` and identified in `verdict_L2E4.md`.

`dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution` performs the full coefficientwise
polynomial assembly once the displayed fixed-grade digit-convolution equality is
provided. It handles in-range and beyond-degree coefficients and contains no scalar
stationarity assumption.

`dv2ResPolyAnchWeightedConv_eq_C_mul_of_weight_stationary` proves the exact terminal
collapse: if all these root powers equal a fixed `c`, the weighted carrier is
`C c * (RAnch(g) * RAnch(z))`. Thus the file machine-separates honest weighted assembly
from the additional normalization needed for a constant-scalar law.

### 1.3 Anchored F1.5 adapter

`dv2ResPolyAnch_radical_eq_of_scalar` is L2E3's
`dv2ResPoly_radical_eq_of_scalar` proof over `dv2ResPolyAnch`: a nonzero scalar gives an
isUnit constant polynomial, hence preserves natural degree and all irreducible monic
divisors.

## 2. Exact remaining subgoals

### 2.1 Digit-split supplier

The premise of `dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution` remains to be proved:
for every in-range `t`, the absolute read of

```text
dev Ψ (g*z) (min(g*z) + t*ℓ₂)
```

at grade `Mgz - t*u₂` equals the guarded weighted antidiagonal in §1.2. The intended
route is `C132rp5.dev_mul_conv_split_monic`, fixed-grade additivity, L2E1/L2E2 strict
off-pair and carry pricing, `dv2FullRead_modByMonic`, and the now-landed
`dv2FullReadCarryLaw`. This unit did not complete that pricing/reindexing proof.

### 2.2 New terminal stationarity subgoal for the enacted C.39

Even after §2.1, the block/complement specialization has complement outer degree zero,
so coefficient `t` carries

```text
root ^ L.cocycle (M₂' - t*u₂) (complementConst L f).
```

To obtain the enacted byte-as-is scalar, one still needs, through the block side degree,

```text
root ^ L.cocycle (M₂' - t*u₂) (complementConst L f)
  = root ^ L.cocycle M₂' (complementConst L f).
```

This is not the carry law: it is a claim that different carries are equal. A sufficient
arithmetic genre would be invariance of the inner shift under subtracting `t*u₂` (for
example from an appropriate `L.ℓ ∣ u₂` premise plus the line-floor inequality), but the
re-signed C.39 has no such premise. The S2 battery could not see this issue because its
`K₂ = 𝔽₂` has `root = 1`, collapsing all root powers.

## 3. Verification and trust footprint

Required scoped command:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136f14c.lean
```

Result: **EXIT 0**. AxCheck reports exactly `[propext, Classical.choice, Quot.sound]` for
the carry core/law, weighted carrier/assembler/stationarity collapse, and anchored
radical adapter. There is no `sorry`, new axiom, `unsafe`, cite, or inherited
`exists_dvDissection` dependency.

## 4. Footprint

* `leanfinal/Uniformity/ChapC/C136f14c.lean` — CREATED.
* `runs/wave-c/verdict_F14C.md` — CREATED.
* No landed predecessor or leanspec file edited.
* No git operation run.
