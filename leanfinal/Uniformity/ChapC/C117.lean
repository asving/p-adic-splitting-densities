/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C11

/-!
# Uniformity.ChapC.C117 — `Visible₂`: level-2 window visibility

**Chapter C, NODE C.117** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §12, the level-`N`
tower certificates; the A-C.1 amendment set governs). **ENV-C3** (nothing in the two signed
statements consumes finiteness, so no instance binder appears — the environment is the §12
section's, not this node's demand). Two signed declarations: the predicate and its monotonicity.

*Level-2 window visibility.* `Visible₂ L Ψ f N` says that **every height the level-2 read of `f`
consults is below the cleared window bound** `(F.e₁ * L.ℓ) * N`:

```
Visible₂ L Ψ f N  :=  ∀ j ≤ deg f / D″, dv2Pin L Ψ f j ≠ ⊤ → dv2Pin L Ψ f j < (e₁·ℓ)·N
```

with `D″ = L.keyDeg₂` (C.09) and `dv2Pin` the level-2 pins (C.11). This is B.75's pattern one
level up: at order 0 the visibility gate bounds the `npHgt`-pins of the `φ`-development by the
window; here it bounds the `dv₂`-pins of the `Ψ`-development by the same window, cleared by the
level's own denominator.

## Why the bound is `(F.e₁ * L.ℓ) * N` and not `N`

The level-2 pins are `ℓ`-cleared **and** `e₁`-cleared: `dv2Pin = dvSupp F (dev Ψ f j) L.u L.ℓ`
(C.11), and C.06's `dvSupp` already carries the stage denominator `e₁` through `stageHeight`,
while `L.ℓ` is cleared on top of it by C.11's own `inf_j (ℓ • · + u·j)` convention (GC-2's ruling:
clearing the denominator is what keeps every value in `ℕ∞`; the price is that consumers remember
the factor). A window of `N` `π`-digits therefore reaches cleared value `(e₁·ℓ)·N`, and that
product — not `N` — is the honest gate. Getting this wrong in either direction is silent: too
small a bound makes the predicate unsatisfiable at live data, too large a bound makes C.118's
congruence false. The two clearing factors are exactly the two denominators C.11's docstring
lists, and no third one enters at this level.

## The abscissa-0 pin, and why it is right HERE and only here

GC-1's closing rule separates the **visibility API** from the **residual-read API**: a visibility
predicate bounds *every consulted height*, a residual read bounds only the heights on one side.
The blueprint's ⚠ note for this node is that the abscissa-0 pin is the correct one here precisely
because visibility quantifies over all `j` in the read's range — there is no side to select, so
no side-dependent normalization can enter, and the pin at abscissa `0` is the unique convention
that makes the bound uniform in `j`. Consumers that DO select a side (C.118's residual half, the
§7 reads) must re-pin at their own abscissa; they may not inherit this one.

## The `≠ ⊤` guard is not a weakening

`dv2Pin L Ψ f j = ⊤` exactly when `dev Ψ f j = 0` (C.11's `dvSupp` of the zero polynomial), i.e.
when the development coefficient is absent. An absent coefficient consults no height, so the
window says nothing about it and must not be asked to: without the guard the predicate would be
false for every `f` whose `Ψ`-development is not full, which is every `f` of degree `< D″·(deg f
/ D″ + 1)` with a vanishing top slot. The guard is what makes `Visible₂` a statement about
*consulted* data, which is the only form C.118 can transport.

## Monotonicity

`Visible₂_mono`: a wider window sees at least as much. Immediate from `N ≤ N'` and monotonicity
of `k ↦ (e₁·ℓ)·k` — but it is a signed declaration because every §12 consumer needs to align two
members' windows before applying C.118, and the alignment step is exactly this lemma. Note the
direction: visibility at the SMALLER window is the stronger hypothesis.

**DEPENDS.** C.11 (`dv2Pin`) · C.21 · B.75 (template + the GC-1 visibility/residual split) — by
committed node ID (GC-13(b)). The single import is `Uniformity.ChapC.C11`, which pulls C.06 and
C.09 (hence C.01–C.03) and the B chain. C.21 is a design dependency (the read whose heights are
being bounded is built from the slot residue), not a term-level one: nothing in these two
statements mentions `slotRes`.

**PROOF.** Definitional; the monotonicity is `lt_of_lt_of_le` against the cast of
`Nat.mul_le_mul_left`.

**SOURCE.** B.75 (D-4's visibility layer, the level-1 twin of this predicate);
`EFF.GENTOW1.39` / C.58(e) (the window content identity that makes visibility the right gate —
what a window class determines is exactly the development digits below the bound).

**TEETH.** §13 rows (the certificate gate); not dischargeable at this node's binders, since an
abstract `KeyFrame O π` offers no numeral to `#guard` (the standing D7 consequence, as at
C.15/C.17/C.22).

ENVIRONMENT: ENV-C3.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The signed declarations -/

/-- **NODE C.117 — level-2 window visibility.** Every height the level-2 read of `f` at the
level-2 key `Ψ` consults — i.e. every non-`⊤` pin `dv2Pin L Ψ f j` for `j` in the read's range
`j ≤ deg f / D″` — sits strictly below the cleared window bound `(F.e₁ * L.ℓ) * N`.

B.75's pattern at the `dv₂`-ladder. Pinned at abscissa `0`: visibility bounds EVERY consulted
height, so there is no side to select and the abscissa-`0` pin is the right one here (GC-1's
visibility rule) — and only here; side-selecting consumers re-pin at their own abscissa. -/
def Visible₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (N : ℕ) : Prop :=
  ∀ j, j ≤ f.natDegree / L.keyDeg₂ → dv2Pin L Ψ f j ≠ ⊤ →
    dv2Pin L Ψ f j < (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞)

/-- **NODE C.117 — visibility is monotone in the window.** A wider window sees at least as much;
visibility at the smaller window is the stronger hypothesis. The §12 consumers use this to align
two members' windows before applying C.118's congruence. -/
theorem Visible₂_mono {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) {N N' : ℕ} (h : N ≤ N') :
    Visible₂ L Ψ f N → Visible₂ L Ψ f N' := by
  intro hvis j hj hne
  refine lt_of_lt_of_le (hvis j hj hne) ?_
  exact_mod_cast Nat.mul_le_mul_left (F.e₁ * L.ℓ) h

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.Visible₂
#print axioms Uniformity.Density.Tower.Visible₂_mono

end AxCheck
