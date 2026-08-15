/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B17

/-!
# Uniformity.ChapB.B19 — two distinct slopes share at most one abscissa

**Chapter B, NODE B.19** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

*The vertex property.*  Let `0 < ℓ`, `0 < ℓ'`, `suppVal φ f u ℓ ≠ ⊤`, `suppVal φ f u' ℓ' ≠ ⊤`,
and `u * ℓ' ≠ u' * ℓ` (the two slopes `u/ℓ` and `u'/ℓ'` are distinct).  If `j` and `j'` are both
on the `(u,ℓ)`-side **and** both on the `(u',ℓ')`-side, then `j = j'`.

Two distinct sides of the polygon meet in at most one point: the vertex.  In the
support-function representation (DECISION D-1) this is sixteen lines of `ℤ`-arithmetic —
the two `OnSide` equations at the two slopes give the two `ℤ`-identities
`ℓ*(H − H') = u*(j' − j)` and `ℓ'*(H − H') = u'*(j' − j)`, and cross-multiplying kills the
heights and leaves `(u*ℓ' − u'*ℓ)*(j' − j) = 0`.

Signed binders: `{ℓ ℓ' : ℕ}` is the blueprint's `[repaired: A-F.3/B-D16]` form — `ℓ` and `ℓ'`
had no binder in the pre-repair text and survived only through `autoImplicit`; the explicit
binders are written in Lean's first-occurrence auto-bind order, so the elaborated type is
unchanged.

DEPENDS: B.11 (`npHgt`) · B.14 (`suppVal`) · B.16 (`OnSide`) · B.17's public helpers
`npHgt_ne_top_of_onSide` and `onSide_nat_eq` · mathlib `WithTop.ne_top_iff_exists`,
`mul_eq_zero`, `sub_eq_zero`, `Nat.cast_injective`.

**PROOF.**
1. As in B.17 steps 1–2, extract `H := npHgt φ f j` and `H' := npHgt φ f j'` as naturals and
   the two `ℕ`-equalities `ℓ*H + u*j = ℓ*H' + u*j'` and `ℓ'*H + u'*j = ℓ'*H' + u'*j'`.
   (The heights are properties of the abscissae alone, so the *same* `H`, `H'` serve both
   slopes; `hℓ'`/`htop'` are what make the second extraction legitimate, and are used for it.)
2. In `ℤ`: `ℓ*(H − H') = u*(j' − j)` and `ℓ'*(H − H') = u'*(j' − j)`.
3. Multiply the first by `ℓ'` and the second by `ℓ`: `ℓ'*u*(j' − j) = ℓ*u'*(j' − j)`, i.e.
   `(u*ℓ' − u'*ℓ)*(j' − j) = 0`.
4. `hne` gives `(u*ℓ' − u'*ℓ : ℤ) ≠ 0`, so `j' − j = 0` by `mul_eq_zero`, i.e. `j = j'`
   (`Int.natCast_inj`).

## Minimum-hypothesis note

`hne` is the whole content: at `u * ℓ' = u' * ℓ` the two "sides" are the same side and carry
the whole side's worth of abscissae.  `0 < ℓ`, `0 < ℓ'`, `htop` and `htop'` are what make the
two heights finite (B.17 step 1); without them `ℓ • ⊤ + u*j = ⊤` holds at every `j` and every
abscissa is vacuously on side.

## WHY THIS REPLACES THE HULL (blueprint, in force)

In the `Finset (ℕ × ℕ)` representation the analogous fact is the vertex/collinearity
bookkeeping that the quarry's `HullStability.lean` spends 1744 lines on, and whose naive form
is **provably false** (`NewtonPolygon.lean:784`, `npVertices_not_stable_of_hull_preserved`,
witness `S = {(0,0),(1,0)}`, `S' = {(0,0)}`).  Here it is sixteen lines of `ℤ`-arithmetic with
no representation to stabilise.  This node is DECISION D-1's **criterion-C5 certificate**.

SOURCE: `EFF.HE3.13` (*"each side has a `dv`-slope … in lowest terms"*); `EFF.HE6.10`.

TEETH: signed non-applicable as a battery item; internal decision evidence (see above).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.19 — two distinct slopes share at most one abscissa (the vertex property).**  If the
slopes `u/ℓ` and `u'/ℓ'` are distinct (`u * ℓ' ≠ u' * ℓ`), both sides are finite, and `j`, `j'`
both lie on both sides, then `j = j'`. -/
theorem eq_of_onSide_onSide {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') {φ f : Polynomial O}
    {u u' j j' : ℕ}
    (hne : u * ℓ' ≠ u' * ℓ)
    (htop : suppVal φ f u ℓ ≠ ⊤) (htop' : suppVal φ f u' ℓ' ≠ ⊤)
    (hj : OnSide φ f u ℓ j) (hj' : OnSide φ f u ℓ j')
    (hk : OnSide φ f u' ℓ' j) (hk' : OnSide φ f u' ℓ' j') : j = j' := by
  -- Step 1: the two heights, as naturals.  Finiteness at `j` is B.17 step 1 on the
  -- `(u,ℓ)`-side, finiteness at `j'` is B.17 step 1 on the `(u',ℓ')`-side; the two agree
  -- because `npHgt` does not see the slope.
  obtain ⟨H, hH⟩ := WithTop.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide hℓ htop hj)
  obtain ⟨H', hH'⟩ := WithTop.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide hℓ' htop' hk')
  -- Step 1, continued: the two `ℕ`-equations, one per slope.
  have key : ℓ * H + u * j = ℓ * H' + u * j' := onSide_nat_eq hH.symm hH'.symm hj hj'
  have key' : ℓ' * H + u' * j = ℓ' * H' + u' * j' := onSide_nat_eq hH.symm hH'.symm hk hk'
  -- Step 2: the same two equations in `ℤ`.
  have keyZ : (ℓ : ℤ) * (H : ℤ) + (u : ℤ) * (j : ℤ) = (ℓ : ℤ) * (H' : ℤ) + (u : ℤ) * (j' : ℤ) :=
    by exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) key
  have keyZ' :
      (ℓ' : ℤ) * (H : ℤ) + (u' : ℤ) * (j : ℤ) = (ℓ' : ℤ) * (H' : ℤ) + (u' : ℤ) * (j' : ℤ) :=
    by exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) key'
  -- Step 3: cross-multiply — the heights cancel.
  have hprod : ((u : ℤ) * (ℓ' : ℤ) - (u' : ℤ) * (ℓ : ℤ)) * ((j' : ℤ) - (j : ℤ)) = 0 := by
    nlinarith [keyZ, keyZ']
  -- Step 4: the first factor is nonzero, so the second vanishes.
  have hnz : ((u : ℤ) * (ℓ' : ℤ) - (u' : ℤ) * (ℓ : ℤ)) ≠ 0 := by
    intro h
    refine hne ?_
    have : (u : ℤ) * (ℓ' : ℤ) = (u' : ℤ) * (ℓ : ℤ) := by linarith [sub_eq_zero.mp h]
    exact_mod_cast this
  have : (j' : ℤ) - (j : ℤ) = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hnz
    · exact h
  have : (j : ℤ) = (j' : ℤ) := by linarith
  exact_mod_cast this

section AxCheck
#print axioms Uniformity.Density.Leaf.eq_of_onSide_onSide
end AxCheck

end Uniformity.Density.Leaf
