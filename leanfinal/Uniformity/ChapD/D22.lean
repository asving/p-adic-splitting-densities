/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapD.D22 — `(C4-origin)`, the modular-origin comparison

**Chapter D, NODE D.22** [lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1
gauge layer; amendments A-1, A-D.1 govern — this node's signature is unamended). ENV-D2. Two
public declarations (the signed theorem and its signed sibling, same file).

*`(C4-origin)`: the modular-origin comparison.* For `e ℓ β : ℤ` with `e > 0` and a group
element `z` (stated over a bare `CommGroup`; the corpus's `z ∈ K^×` instance follows), put

* `s_min(β) := (ℓ·β) % e` — the modular origin,
* `t_min(β) := (ℓ·β − s_min(β))/e`,
* `ε(β) := z^{−t_min(β)}`.

If the actual slot `s_act = s_min(β) + ν·e` with `ν : ℕ`, and `t_Def := (s_act − ℓ·β)/e`, then

  `z^{t_Def} = z^ν · ε(β)`,  i.e.  `ε(β) = z^{t_Def − ν}`,

and **raw equality `z^{t_Def} = ε(β)` holds exactly when `z^ν = 1`** — "it holds in particular
when `ν = 0`". That is `EFF.T1.32`'s exact root-of-unity criterion: "JA-EPS-CORR is absorbed
verbatim in (C4), including the exact root-of-unity criterion `z^ν = 1`". The criterion is an
`iff`, not a one-way implication, and this node lands it as one.

The two C4 lemmas are deliberately separate nodes with separate hypotheses: `(C4-support)`
(D.23) is NOT a consequence of `(C4-origin)`, and nothing here transports polynomial support.

## Faithfulness

**⚠ Trust-boundary transcription.** Three points, flagged for the chapter cross-read:

* *`%` is `Int.emod` at the v4.31.0 pin*, so `s_min(β) = (ℓ·β) % e` is the NONNEGATIVE
  representative whenever `e > 0` (`(-21) % 5 = 4`). That is exactly the corpus's "modular
  origin" reading `0 ≤ s_min < e`, and it is what makes `t_min = (ℓβ − s_min)/e` the honest
  floor `⌊ℓβ/e⌋`. No sign hypothesis on `ℓ`, `β` or `s_act` is needed or taken.
* *the divisions are exact.* Both `(ℓβ − s_min)/e` and `(s_act − ℓβ)/e` divide exactly — the
  first by `Int.emod`'s defining identity, the second from `hs`. The proof establishes both
  before dividing, so no `Int`-division truncation enters the identity.
* *`he : 0 < e` is signed and consumed* (only through `e ≠ 0`, which is all the arithmetic
  needs). The signature is frozen; the hypothesis is kept as signed and NOT weakened to
  `e ≠ 0`, since `e` is a ramification index downstream and positivity is the honest
  precondition there.

DEPENDS: none landed. Mathlib `Int.mul_ediv_add_emod`, `Int.mul_ediv_cancel_left`,
`zpow_add`, `mul_eq_right` — all name-verified at the pin (`mul_left_eq_self` does NOT exist at
v4.31.0; the cancellation `iff` is `mul_eq_right`).

**PROOF.** `EFF.T1.16` verbatim: "Substitute `s_act = s_min + νe` into `t_Def = (s_act − ℓβ)/e`
to obtain `t_Def = ν − t_min`, then exponentiate by `z`." In Lean, with
`hm : e * (ℓβ / e) + ℓβ % e = ℓβ`: (1) `ℓβ − ℓβ % e = e * (ℓβ / e)`, so `t_min = ℓβ / e`;
(2) `s_act − ℓβ = e * (ν − ℓβ / e)` after substituting `hs`, so `t_Def = ν − ℓβ / e`; both
divisions are then discharged by `Int.mul_ediv_cancel_left` under `e ≠ 0`. The exponent identity
`t_Def = ν + (−t_min)` gives the group identity by `zpow_add`. The sibling `iff` cancels `ε(β)`
on the right (`mul_eq_right`).

SOURCE: `EFF.T1.16` (the boxed `(C4-origin)` plus the raw-equality clause); `EFF.T1.29` (the A5
pin `z^{t_Def} = z^ν ε(β)` — the GENTOW-4.1(c)/S3 gauge input, the OUT-interface to chapter C);
`EFF.T1.32` (the exact root-of-unity criterion, absorbed verbatim).

**TEETH.** T1 §4.2 check 3; §7 attacks 1 and 6 → Lean theorem (this node) + the §12 executable
regression. The attack this node's `iff` kills is the one-way reading, under which a nontrivial
`z^ν` could be silently dropped from the origin comparison.

ENVIRONMENT: ENV-D2 (`z` in any `CommGroup`).

## Status

Sorry-free, axiom-free (Lean core only). Both declarations are PROVED theorems here, not the
leanspec `axiom` stubs.
-/

namespace Uniformity.Density.Gauge

/-- `(C4-origin)` (`EFF.T1.16`, `EFF.T1.29`): with the modular origin `s_min = (ℓβ) % e`, the
offset `t_min = (ℓβ − s_min)/e` and `ε(β) = z^{−t_min}`, an actual slot `s_act = s_min + νe`
has `z^{t_Def} = z^ν · ε(β)`, where `t_Def = (s_act − ℓβ)/e`. -/
theorem c4_origin {G : Type*} [CommGroup G] (z : G) (e ℓ β : ℤ) (he : 0 < e)
    (ν : ℕ) (s_act : ℤ) (hs : s_act = (ℓ * β) % e + ν * e) :
    z ^ ((s_act - ℓ * β) / e) = z ^ (ν : ℤ) * z ^ (-((ℓ * β - (ℓ * β) % e) / e)) := by
  have he' : e ≠ 0 := ne_of_gt he
  have hm : e * (ℓ * β / e) + ℓ * β % e = ℓ * β := Int.mul_ediv_add_emod (ℓ * β) e
  -- `t_min = ⌊ℓβ/e⌋`: the first division is exact.
  have h1 : (ℓ * β - ℓ * β % e) / e = ℓ * β / e := by
    have hx : ℓ * β - ℓ * β % e = e * (ℓ * β / e) := by linear_combination -hm
    rw [hx, Int.mul_ediv_cancel_left _ he']
  -- `t_Def = ν − t_min`: the second division is exact, by `hs`.
  have h2 : (s_act - ℓ * β) / e = (ν : ℤ) - ℓ * β / e := by
    have hx : s_act - ℓ * β = e * ((ν : ℤ) - ℓ * β / e) := by
      rw [hs]; linear_combination hm
    rw [hx, Int.mul_ediv_cancel_left _ he']
  rw [h1, h2, sub_eq_add_neg, zpow_add]

/-- The exact root-of-unity criterion of `(C4-origin)` (`EFF.T1.16`, `EFF.T1.32`): the RAW
equality `z^{t_Def} = ε(β)` holds **iff** `z^ν = 1` — in particular whenever `ν = 0`. -/
theorem c4_origin_raw_iff {G : Type*} [CommGroup G] (z : G) (e ℓ β : ℤ) (he : 0 < e)
    (ν : ℕ) (s_act : ℤ) (hs : s_act = (ℓ * β) % e + ν * e) :
    z ^ ((s_act - ℓ * β) / e) = z ^ (-((ℓ * β - (ℓ * β) % e) / e)) ↔ z ^ (ν : ℤ) = 1 := by
  rw [c4_origin z e ℓ β he ν s_act hs]
  exact mul_eq_right

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.c4_origin
#print axioms Uniformity.Density.Gauge.c4_origin_raw_iff

end AxCheck
