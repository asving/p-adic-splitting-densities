/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D02

/-!
# Uniformity.ChapD.D11 — `tau_bracket_telescope`, the descending bracket telescope `(T3-BKT)`

**Chapter D, NODE D.11** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, the abstract
cocycle arena; amendments A-1, A-D.1, A-D.2 govern — none of them re-signs this node, so the
SIGNATURE below is the one signed at composition and re-stubbed at stage 0e in
`leanspec/Leanspec/ChapD.lean`). ENV-D2. One public declaration.

*The descending bracket telescope `(T3-BKT)`, group level.* For `H₀ q : ℤ` and `t : ℕ`, with
the descending height ladder `H_r := H₀ − r·q`,

  `∏_{r=0}^{t−1} τ_N(H_{r+1}, q) = n(H_t) · (n q)^t · (n H₀)⁻¹`.

This is `EFF.T3.15`'s boxed `(T3-BKT)`, transcribed at the level where it is actually true of
nothing but the group: `τ` is D.02's normalizer cocycle, `n` is D.01's section, and the whole
content is that consecutive normalizers cancel down the ladder.

## What the product index means (the transcription pin)

`Finset.range t` runs `r = 0, …, t−1`, and the factor at `r` is `τ_N(H_{r+1}, q)` — the height
argument is `H₀ − (r+1)·q`, i.e. the ladder step BELOW the one indexed by `r`. That off-by-one is
the corpus's own: the product's first factor is `τ(H₁, q)`, not `τ(H₀, q)`, and the surviving
endpoint on the right is `n(H_t)` against `(n H₀)⁻¹`. A transcription that starts the product at
`τ(H₀, q)` proves a different (and false) identity — it would leave `n(H₀ + q)` uncancelled.

## The route (the blueprint's own, executed)

Induction on `t`.

* **Base `t = 0`.** The empty product is `1`; the right side is `n(H₀ − 0·q) · (n q)^0 · (n H₀)⁻¹`,
  which `simp` collapses through `Nat.cast_zero`, `zero_mul`, `sub_zero`, `pow_zero` and
  `mul_inv_cancel`. Note `n_zero` is NOT consumed here — the base case is cancellation, not
  normalization.
* **Step.** `Finset.prod_range_succ` peels the new factor `τ_N(H₀ − (t+1)q, q)`, the induction
  hypothesis rewrites the head, and D.02's definition of `τ` exposes
  `n(H₀ − (t+1)q) · n(q) · (n(H₀ − (t+1)q + q))⁻¹`. The cast rewrite
  `H₀ − (t+1)q + q = H₀ − tq` (by `ring`) is what makes the intermediate normalizer literally the
  one produced by the induction hypothesis, so it cancels — "`H_r = H_{r+1} + q`, so
  `τ(H_{r+1},q) = n(H_{r+1})n(q)/n(H_r)`; multiplication cancels the intermediate normalizers"
  (`EFF.T3.15`'s verbatim derivation). `push_cast` normalizes `↑(t+1)` to `↑t + 1` on the right,
  `pow_succ` splits `(n q)^{t+1}`, and one `mul_comm` puts the two sides in the same
  `group`-normal order.

"This is an iteration of the imported cocycle seam, not a new proof of its normalization or
cocycle law" — accordingly this node depends only on D.02's DEFINITION of `τ`, and neither the
cocycle law (D.03) nor the endpoints (D.02's two lemmas) are used. The file imports D.02 for the
definition alone.

## Faithfulness

No new definition is introduced here, so there is no trust-boundary object; the one transcription
choice is the product index discussed above, and it is pinned by the surviving endpoints. The
identity is stated in the bare `CommGroup` of ENV-D2 — no valuation, no residue, no tower — so
every consumer (D.43's ABS-HE4 interface, D.40's comparison) gets it before any of those layers
exist, which is exactly D-1's licence.

DEPENDS: D.02 (`NormSection.tau`, landed at `Uniformity.ChapD.D02`; only the definition, not the
endpoint lemmas) → D.01 (`NormSection`) · mathlib `Finset.prod_range_succ`, `pow_succ`,
`mul_comm` and the `group` normalizer — all name-verified at the v4.31.0 pin.

SOURCE: `EFF.T3.15` (the boxed `(T3-BKT)` with `H_t = H₀ − tq`, product over `r = 0,…,t−1` of
`τ_N(H_{r+1}, q)`).

**TEETH.** T3 §8.3(2) (HETOW-4 clause (c): "coefficient telescope … fully supplied by
`(T3-BKT)`") → THIS Lean theorem, plus the ABS-HE4 interface at D.43. Nothing numeric is owed at
this node: the statement is a `∀`-quantified group identity with no concrete frame in the
blueprint's TEETH row, and the D.43 boundary table is where it is consumed.

ENVIRONMENT: ENV-D2 (`{G : Type*} [CommGroup G]`, written inline per the B.42 binder rule — this
file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only): a PROVED theorem here, not the leanspec `axiom` stub.
-/

namespace Uniformity.Density.Gauge

/-- **D.11 — `(T3-BKT)`, the descending bracket telescope** (`EFF.T3.15`).  With
`H_r := H₀ − r·q`, the product of the cocycles down the ladder telescopes:
`∏_{r<t} τ_N(H_{r+1}, q) = n(H_t)·(n q)^t·(n H₀)⁻¹`.  Group level: no valuation, no residue. -/
theorem NormSection.tau_bracket_telescope {G : Type*} [CommGroup G]
    (N : NormSection G) (H₀ q : ℤ) (t : ℕ) :
    (Finset.range t).prod (fun r => N.tau (H₀ - (r + 1) * q) q)
      = N.n (H₀ - t * q) * (N.n q) ^ t * (N.n H₀)⁻¹ := by
  induction t with
  | zero => simp
  | succ t ih =>
      -- `H_{t+1} + q = H_t`: this is what makes the intermediate normalizer cancel.
      have hcast : H₀ - ((t : ℤ) + 1) * q + q = H₀ - (t : ℤ) * q := by ring
      rw [Finset.prod_range_succ, ih, NormSection.tau, hcast]
      push_cast
      rw [pow_succ, mul_comm]
      group

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.NormSection.tau_bracket_telescope

end AxCheck
