/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D15

/-!
# Uniformity.ChapD.D27 — the A2/HETOW binary-carry composite law

**Chapter D, NODE D.27** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1
gauge layer; amendments A-1 and A-D.1 govern — A-D.1 does not re-sign the SIGNATURE, but it DOES
add this node to gate D.66's DEPENDS as leg 1's binary-carry grid, and its finding D-F1 is why
the frame executed at the foot of this file is FRAME-H2 and not the `h = 1` X frame).
ENV-D1 — the arithmetic arena: pure `ℕ`/`ℤ`, no `O`, no polynomials. One signed declaration.

*The T1 side of the A2/HETOW consumption check.* `EFF.T1.26`'s effective check reads
"`(H-HETOW-LOCAL)` + `(C5-monomial-ratio)` + `(C5-carry)` ⟹ the three pinned HETOW displays".
T1's own contribution to it is the **binary-carry composite law**: for `a b u₂ : ℤ` and a carry
bit `c₂ ≤ 1`,

```
q(a + b − c₂u₂) = q(a) + q(b) + wrap(a,b) − c₂·(q(u₂) + wrap(a + b − c₂u₂, u₂)).
```

That is `EFF.T1.26`'s derivation verbatim — "two applications of C5-carry in the two binary
cases" — with D.15's `(C5-carry)` as the single input.

## What this node does NOT state (the supplier fence, transcribed)

The first two pinned HETOW displays are **D.19 verbatim** (the monomial ratio and its residue);
the third pin's exponent is THIS law read through the supplier's identification. The level-two
**supplier interface** — the bridge `n̂₂(k)/n₂(k) = n̂(m(k))/ϖ^{m(k)}`, the function `m`, the
range `0 ≤ s(a) < e₂`, the carry `c₂ᴴᴱᵀ = ⌊(s(k)+s(k′))/e₂⌋ ∈ {0,1}`, and the identification of
`τ` — is `(H-HETOW-LOCAL)`, "external and essential": `EFF.HETOW [supplied-by: chapter C]`. It is
NOT stated here, and the assembled three-display conclusion is chapter C's to fire with this node
and D.19 as the T1 legs.

**Non-import, transcribed:** T1 does not absorb HETOW-4(c)–(d). The side-assembly brackets, the
telescoping coefficient identity, the side-letter equality, the routing transport, and the common
refinement polynomial remain HETOW/HE7 supplier conclusions.

## The route (the blueprint's own, executed)

`interval_cases c₂`, then:

* `c₂ = 0`: the correction term is `0` and the goal collapses to D.15's `qexp_add` at `(a, b)`.
* `c₂ = 1`: apply D.15 twice — once to the pair `(a + b − u₂, u₂)`, whose sum is `a + b`, and
  once to `(a, b)`. The two equations share the left-hand side `q(a+b)`, and eliminating it is a
  linear step (`linarith`). This is exactly "two applications of C5-carry".

## Faithfulness

**`c₂ : ℕ` with `hc : c₂ ≤ 1` — the binary conditionality is a HYPOTHESIS, not a convention.**
`EFF.T1.26` asserts the linear carry formula ONLY for the binary carry, and that restriction is
load-bearing: for `c₂ ≥ 2` the displayed right-hand side is not `q(a + b − c₂u₂)`, because
`q(c₂u₂) ≠ c₂·q(u₂)` in general. Both frames below execute a REFUTATION row at `c₂ = 2` —
at `e₁ = 2, h = 1` with `(a,b,u₂) = (0,0,1)` the two sides are `−1` and `0`; at FRAME-H2
(`e₁ = 3, h = 2`) with `(a,b,u₂) = (−1,−1,1)` they are `−3` and `−4`. Dropping `hc` therefore
makes the statement FALSE, and nothing here is weakened by carrying it.

**Signs and casts.** `wrap` is `ℕ`-valued (D.14) and `c₂` is `ℕ`, so both appear under `ℤ`-casts;
the subtraction `a + b − c₂·u₂` and the trailing `− c₂·(…)` are `ℤ`-subtractions, matching
`EFF.T1.26`'s display. `he` and `hcop` are inherited from D.15 unchanged — `hcop` is what makes
`qexp`'s defining division exact, so it is not decoration here either.

**No new definition** — this node introduces none, so no trust-boundary flag is raised beyond
D.14/D.15's own.

DEPENDS: D.14 (`wrap`), D.15 (`qexp`, `qexp_add`) — both landed at `Uniformity.ChapD.D14`/`D15`;
D.13's `iexp_one` and `iexp_eq_of_inv` for the executed frames. No mathlib lemma beyond
`interval_cases`, `push_cast`, `linarith`.

SOURCE: `EFF.T1.26` (the three pinned displays, the boxed effective check, the supplier interface
`0 ≤ s(a) < e₂` and `c₂ᴴᴱᵀ ∈ {0,1}`, the binary-carry conditionality "the linear carry formula is
asserted only for the binary carry", and the HETOW-4(c)–(d) non-import).

**TEETH.** T1 §7 attacks 5 and 8 → §12; the third-pin display itself → chapter-C placeholder edge
(§11); gate **D.66** leg 1 owns the `e₁ = 2, h = 1` binary-carry grid. Per finding D-F1 that grid
cannot separate `qexp` from `aexp` (at `h = 1` they are the same function), so the frame executed
below is **FRAME-H2** (`e₁ = 3, h = 2`, D.66 leg 5), where `i₀ = 2 ≠ 1` — this file is the only
place in chapter D where the binary-carry law is scored at `h > 1`.

ENVIRONMENT: ENV-D1.

## Status

Sorry-free, axiom-free (Lean core only): `qexp_binary_carry` is a PROVED theorem here, not the
leanspec `axiom` stub.
-/

namespace Uniformity.Density.Gauge

/-- **D.27 — the binary-carry composite law.**
`q(a + b − c₂u₂) = q(a) + q(b) + wrap(a,b) − c₂·(q(u₂) + wrap(a + b − c₂u₂, u₂))` for a carry
bit `c₂ ≤ 1` (`EFF.T1.26`, "two applications of C5-carry in the two binary cases").  The
hypothesis `hc` is load-bearing: at `c₂ = 2` the identity is false (refutation rows at the foot
of this file).  The supplier interface `(H-HETOW-LOCAL)` is NOT stated here — it is
`EFF.HETOW [supplied-by: chapter C]`. -/
theorem qexp_binary_carry (e₁ h : ℕ) (he : 0 < e₁) (hcop : Nat.Coprime h e₁)
    (a b u₂ : ℤ) (c₂ : ℕ) (hc : c₂ ≤ 1) :
    qexp e₁ h (a + b - c₂ * u₂)
      = qexp e₁ h a + qexp e₁ h b + wrap e₁ h a b
        - c₂ * (qexp e₁ h u₂ + wrap e₁ h (a + b - c₂ * u₂) u₂) := by
  interval_cases c₂
  · -- no carry: the correction term vanishes and this IS `(C5-carry)`.
    simpa using qexp_add e₁ h he hcop a b
  · -- one carry: `(C5-carry)` at `(a + b − u₂, u₂)` and at `(a, b)`, then eliminate `q(a+b)`.
    have hsum : a + b - (1 : ℕ) * u₂ + u₂ = a + b := by push_cast; ring
    have h1 := qexp_add e₁ h he hcop (a + b - (1 : ℕ) * u₂) u₂
    rw [hsum] at h1
    have h2 := qexp_add e₁ h he hcop a b
    push_cast
    push_cast at h1 h2
    linarith [h1, h2]

end Uniformity.Density.Gauge

/-! ## The executed frames (A-D.1 gate-writing rider: `simp only [...]; decide`, never bare)

Two things are scored here that gate D.66's leg-1 grid cannot score.

1. **The law at `h > 1`.** D.66 leg 1 runs the binary-carry grid at `e₁ = 2, h = 1`, where
   `i₀ = 1` and `qexp ≡ aexp` identically (finding D-F1), so a `qexp`/`aexp` confusion survives
   it. FRAME-H2 — `e₁ = 3, h = 2`, coprime, `2⁻¹ = 2` in `ZMod 3`, `i₀ = iexp 3 2 1 = 2 ≠ 1`
   (D.66 leg 5) — is the frame at which the two functions differ, and the grid below runs this
   node's law there, on `a, b ∈ {−1,…,2}`, `u₂ ∈ {1,2,3}`, both carry bits, negative heights
   included.
2. **The necessity of `hc`.** One refutation row per frame at `c₂ = 2`.

`iexp` is NOT `decide`-reducible (defect D-D1), so every row reduces through D.13's
`iexp_eq_of_inv` (at `h = 2`, where `iexp_one` does not apply) or `iexp_one` (at `h = 1`) BEFORE
deciding. No `native_decide`. -/

section Frames

open Uniformity.Density.Gauge

/-- FRAME-H2's inverse datum, `decide`-able: `2 · 2 = 1` in `ZMod 3`. -/
private theorem d27_frameH2_inv : ((2 : ℕ) : ZMod 3) * 2 = 1 := by decide

/-- The GC-11 reducer at FRAME-H2: `iexp 3 2 k = (2k mod 3)`, from D.13's `iexp_eq_of_inv`. -/
private theorem d27_frameH2_iexp (k : ℤ) : iexp 3 2 k = ((k : ZMod 3) * 2).val :=
  iexp_eq_of_inv 3 2 2 d27_frameH2_inv k

/-- **The binary-carry law EXECUTED at FRAME-H2** (`e₁ = 3, h = 2`), both carry bits, on
`a, b ∈ {−1,…,2}` and `u₂ ∈ {1,2,3}` — the only `h > 1` scoring of this node in chapter D. -/
example : ∀ a ∈ ([-1, 0, 1, 2] : List ℤ), ∀ b ∈ ([-1, 0, 1, 2] : List ℤ),
    ∀ u ∈ ([1, 2, 3] : List ℤ), ∀ c ∈ ([0, 1] : List ℕ),
      qexp 3 2 (a + b - c * u)
        = qexp 3 2 a + qexp 3 2 b + wrap 3 2 a b
          - c * (qexp 3 2 u + wrap 3 2 (a + b - c * u) u) := by
  simp only [qexp, wrap, d27_frameH2_iexp]; decide

/-- The `c₂ = 1` branch is LIVE at FRAME-H2: the correction term is not identically zero, so the
grid above is not silently re-running the `c₂ = 0` case twice. -/
example : qexp 3 2 2 + wrap 3 2 ((0 : ℤ) + 0 - (1 : ℕ) * 2) 2 ≠ 0 := by
  simp only [qexp, wrap, d27_frameH2_iexp]; decide

/-- **`hc : c₂ ≤ 1` is necessary, at FRAME-H2.**  At `c₂ = 2`, `(a,b,u₂) = (−1,−1,1)` the two
sides are `−3` and `−4`. -/
example : qexp 3 2 ((-1 : ℤ) + -1 - (2 : ℕ) * 1)
    ≠ qexp 3 2 (-1) + qexp 3 2 (-1) + wrap 3 2 (-1) (-1)
      - (2 : ℕ) * (qexp 3 2 1 + wrap 3 2 ((-1 : ℤ) + -1 - (2 : ℕ) * 1) 1) := by
  simp only [qexp, wrap, d27_frameH2_iexp]; decide

/-- **`hc : c₂ ≤ 1` is necessary, at the X frame too** (`e₁ = 2, h = 1`): at `c₂ = 2`,
`(a,b,u₂) = (0,0,1)` the two sides are `−1` and `0`.  The failure is not an artefact of the
`h > 1` frame. -/
example : qexp 2 1 ((0 : ℤ) + 0 - (2 : ℕ) * 1)
    ≠ qexp 2 1 0 + qexp 2 1 0 + wrap 2 1 0 0
      - (2 : ℕ) * (qexp 2 1 1 + wrap 2 1 ((0 : ℤ) + 0 - (2 : ℕ) * 1) 1) := by
  simp only [qexp, wrap, iexp_one]; decide

end Frames

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.qexp_binary_carry

end AxCheck
