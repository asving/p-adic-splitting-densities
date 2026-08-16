/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E02
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapE.E08 — the lift-threshold implication `(‡) ⟹ (†)` at a rung

**Chapter E, NODE E.08** [lemma] (`blueprint/CHAP-E_sigma_ladder.md` §3), ENV-E1 (the arithmetic
arena: threshold bookkeeping, no local base `O`).

One rung `R = (ℓ, g, u, T)` (E.01), a bound seed `b`, and a height `k` decomposed as
`ℓ*m₀ + s₀*u = k` with `s₀ < ℓ` (E.03's Bézout data, taken as explicit arguments — the H.54
`stageLift'` convention). The k-uniform lift criterion

  `(‡)  (L − 1)·u + ℓ·b ≤ k`,  `L = ℓg = R.slotCount`

implies the per-height criterion

  `(†)  (g − 1)·u + b ≤ m₀`.

That is `EFF.HE7.12`'s closing step verbatim at level 2 (`b = (D′−1)h`: "`m₀ = (k − s₀u)/ℓ ≥
(k − (ℓ−1)u)/ℓ`, and `k ≥ (ℓd_r−1)u + ℓ(D′−1)h` gives `m₀ ≥ (d_r−1)u + (D′−1)h = (†₂)`"), and
R1-c's "the same arithmetic as §S4.2's (‡₂) step" at every level (`EFF.HE7.111`: "The bound
recursion is unchanged — values never see the twist"). The left-hand side of `(‡)` is exactly
`R.nextBound b` (E.02), so the k-uniform form consumers actually use reads `R.nextBound b ≤ k`.

## Reading the hypotheses, and the three truncated subtractions

`(‡)`'s `slotCount − 1`, `(†)`'s `g − 1` and the internal `ℓ − 1` are `ℕ`-truncated, and none of
them fires on a legal rung: `R.hℓ` and `R.hg` give `1 ≤ ℓ`, `1 ≤ g`, hence `1 ≤ L`. The proof
below never divides: it clears `ℓ` by cancellation (`Nat.le_of_mul_le_mul_left`) rather than
reproducing the source's `(k − s₀u)/ℓ`, which is the same argument with the division removed.

Direction only: this is `(‡) ⟹ (†)`. The converse fails and its failure is the point of the
sharpness teeth — a `k` can satisfy `(†)` at its own `m₀` while sitting below the k-uniform
threshold. The non-necessity direction is E.32's set arithmetic plus E.68's enumeration gate; no
clause here asserts it.

BOUNDARY EXACTNESS (the gate instance, `leanspec/Leanspec/ChapE.lean`): at the frame-2 rung
`(ℓ,g,u,T) = (2,2,5,2)` with `b = 1`, `k = 17`, `s₀ = 1`, `m₀ = 6` both sides are equalities —
`(‡)` reads `(4−1)·5 + 2·1 = 17 ≤ 17` and `(†)` reads `(2−1)·5 + 1 = 6 ≤ 6`. So the inequality
cannot be strengthened to a strict one, and no slack is hiding in the statement.

DEPENDS: E.01 (`RungDatum`, and its `hℓ`/`hg` side conditions), E.02 (`slotCount`, and
`nextBound` as the reading of `(‡)`'s left side).

PROOF: write `g = g' + 1`, so `slotCount − 1 = ℓ*g' + (ℓ − 1)` exactly (no truncation left) and
the goal is `g'*u + b ≤ m₀`. Multiply the goal by `ℓ`: `(‡)` reads
`ℓ*(g'*u + b) + (ℓ−1)*u ≤ k = ℓ*m₀ + s₀*u`, and `s₀ ≤ ℓ − 1` gives `s₀*u ≤ (ℓ−1)*u`, so
`ℓ*(g'*u + b) ≤ ℓ*m₀`; cancel `ℓ ≥ 1`.

SOURCE: `EFF.HE7.12` ((LIFT₂)'s `(†₂)`/`(‡₂)` displays and the closing implication);
`EFF.HE7.111` (R1-c, the level-`i` form); `EFF.T2.10` (`(FULL2)`/`(FULL2-U)`, the T2-side
statement of the same two bounds).

TEETH: HE7-T-LIFT2SHARP (exact reachable sets vs. closed-form thresholds, ten frames,
deliberately at `f₁ ≥ 2, d_r ≥ 2`) — the implication is a Lean theorem here; the sharpness
(non-necessity) direction stays with E.32/E.68.

ENVIRONMENT: ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **The lift-threshold implication `(‡) ⟹ (†)`** (`EFF.HE7.12`, `EFF.HE7.111`): if the height
`k` clears the k-uniform threshold `(L−1)·u + ℓ·b = R.nextBound b`, then its Bézout height
exponent `m₀` clears the per-height threshold `(g−1)·u + b`. -/
theorem lift_threshold_step (R : RungDatum) {b k m₀ s₀ : ℕ}
    (hs : s₀ < R.ℓ) (hk : R.ℓ * m₀ + s₀ * R.u = k)
    (hcrit : (R.slotCount - 1) * R.u + R.ℓ * b ≤ k) :
    (R.g - 1) * R.u + b ≤ m₀ := by
  have hℓ := R.hℓ
  have hg := R.hg
  obtain ⟨g', hg'⟩ : ∃ g', R.g = g' + 1 := ⟨R.g - 1, by omega⟩
  -- `slotCount − 1 = ℓ*g' + (ℓ − 1)`: both truncations cleared at once
  have hsc : R.slotCount - 1 = R.ℓ * g' + (R.ℓ - 1) := by
    have h1 : R.slotCount = R.ℓ * g' + R.ℓ := by
      simp [RungDatum.slotCount, hg', Nat.mul_succ]
    omega
  have hgsub : R.g - 1 = g' := by omega
  rw [hgsub]
  refine Nat.le_of_mul_le_mul_left ?_ hℓ
  -- `s₀ ≤ ℓ − 1`, so the slot term never eats more than the `(ℓ−1)u` the criterion pays
  have hsu : s₀ * R.u ≤ (R.ℓ - 1) * R.u := Nat.mul_le_mul_right _ (by omega)
  have expand : (R.ℓ * g' + (R.ℓ - 1)) * R.u + R.ℓ * b
      = R.ℓ * (g' * R.u + b) + (R.ℓ - 1) * R.u := by ring
  rw [hsc, expand] at hcrit
  omega

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.lift_threshold_step

end AxCheck
