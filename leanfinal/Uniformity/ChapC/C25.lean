/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C07
import Uniformity.ChapC.C22

/-!
# Uniformity.ChapC.C25 — `dvResPoly`: the level residual polynomial `R_λ`

**Chapter C, NODE C.25** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the slot-exactness
layer; the A-C.1 amendment set governs). **ENV-C1**. One signed declaration, definitional.

`EFF.HE6.11`'s display, at the ϖ-read and the GC-1 `sideMin` pin:

`R_λ(Z) := Σ_{t ≤ d} res(A_{j₁+tℓ}(θ) / ϖ(θ)^{m₁−tu}) · Z^t ∈ K[Z]`,

with `j₁ := dvSideMin F f u ℓ hne₂` the side's left endpoint (C.07(c)), `d := dvSideDeg F f u ℓ
hne₂` its residual degree (C.07(e)), `m₁ := M₀` the pinned height of the development coefficient
sitting at `j₁`, and `res(·/ϖ^k)` the C.22 ϖ-read `twistRead F H₀ hpin k`. The `t`-th coefficient
is the ϖ-read of the `(j₁ + tℓ)`-th `Φ′`-development coefficient `dev F.key f (j₁ + tℓ)` (B.02) at
its **on-side** height `M₀ − tu`.

## Why the `t`-th height argument is `M₀ − t·u`

Points of the side at slope `−u/ℓ` satisfy the line equation `ℓ·(height) + u·(abscissa) = const`
(C.07(a)'s `DvOnSide`, whose defining equation is exactly `dvSupp = ℓ • dvHgt + u * j`). Moving
`t` steps of horizontal length `ℓ` from `j₁` therefore drops the cleared height by `t·ℓ·u`, i.e.
the uncleared height by `t·u`. So the pin at abscissa `j₁ + tℓ` is `M₀ − tu` — the same
bookkeeping B.28 does one level down, and the reason the level pin `M₀` (a single `ℕ`) suffices to
address every coefficient of `R_λ`.

## Totality, and where the junk lives

Nothing here asserts that abscissa `j₁ + tℓ` is on the side. When it is **not**, its development
coefficient sits strictly above the side, its true height exceeds `M₀ − tu`, and every window
digit that `slotRes` reads undershoots its valuation, so `digAt`'s junk-`0` discipline (B.24)
makes the `t`-th coefficient `0` — no `Option`, no partiality, exactly B.28's pattern. Likewise
`M₀ - t * u` is `ℕ`-truncated subtraction; on the intended inputs (`t ≤ d`, side points) it never
truncates, and where it would, the coefficient is junk-`0` anyway. **This is a definition and
carries no correctness claim**: that the coefficient vanishes *iff* the abscissa is off-side, and
that `natDegree = d` with `coeff 0 ≠ 0`, is C.26's content and must be consumed from there.

## ⚠ FAITHFULNESS (trust boundary)

Carried from the blueprint, two clauses.

1. `EFF.HE6.11` glosses the variable `Z` as "the class of `y^ℓ/ϖ^u`". That gloss is
   **closure-side and is documentation only**. The polynomial's identity *as data* is the
   coefficient list above; the semantic tie to the factors of `f` is C.27 plus the §5 laws, and it
   is never to be assumed from the gloss.
2. The read is C.22's `twistRead`, **not** a literal quotient by ϖ, because ϖ ∉ `O[x]`
   (`EFF.HE6.11`'s `[r1]` bracket: `ϖ = x^{i₀}π^{a₀}` with `a₀` possibly negative). Only ϖ's
   exponent arithmetic survives the recast, which is the whole content of C.22 and the reason the
   `[r2]` sign lives there rather than here.

## Binder notes (stub-gate defects, cured upstream)

**D4.** The blueprint writes the pin binder as `(hpin : _)`; the gate-verified twin writes the pin
equation out (`npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)`),
and that is the signed text landed here, matching C.03/C.19/C.21/C.22 verbatim.

**D5.** `dvSideDeg` is one of the three members C.07's signature block promised in a trailing
comment and did not declare; C.07 landed the cluster, so it is available by committed node ID.

`hpin₂` is a **correctness side condition on the numeral `M₀`**, not body data — the definition is
total for any `M₀`, and the pin is what makes it the corpus's `R_λ` rather than a shifted read.
The unused-variable linter is disabled for this declaration on C.03's precedent (same situation
there for `hpin`).

**DEPENDS.** C.06 (`dvHgt`) · C.07 (`dvSideSet`, `dvSideMin`, `dvSideDeg`) · C.22 (`twistRead`) ·
C.03 (`stageField`) · B.02 (`dev`) — by committed node ID (GC-13(b)). The two imports are
`Uniformity.ChapC.C07` (pulling C.06, C.02 and the B chain) and `Uniformity.ChapC.C22` (pulling
C.21, C.19, C.17, C.16, C.15, C.03, C.01, B.25).

**PROOF.** Definitional.

SOURCE: `EFF.HE6.11` (the `R_λ` display, verbatim, together with the `[r1]` bracket's warning that
ϖ ∉ `O[x]`); `EFF.HE6.10` (sides and lengths).

**TEETH.** Signed **non-applicable** at the definition — C.26 carries the correctness teeth (the
coefficient-vanishing iff, the degree, the nonzero constant term), and blueprint §13's frame audit
(`R_λ = r²` at the `EFF.HE6R1.18` frame, the `q = 2` / `q = 3` gate instances) fires against C.26,
not against this node.

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The signed declaration -/

-- `hpin₂` pins the level height `M₀` (GC-1's `sideMin` pin); it is a correctness side condition
-- on the numeral, not body data, exactly as `hpin` is at C.03.
set_option linter.unusedVariables false in
/-- `R_λ(Z) := Σ_t res(A_{j₁+tℓ}(θ)/ϖ(θ)^{m₁−tu})·Z^t ∈ K[Z]` (`EFF.HE6.11`), through the
C.22 ϖ-read at the GC-1 `sideMin` pin.

Off-side abscissae contribute junk-`0` coefficients (B.24's `digAt` discipline), which is what
makes the formula total; the exactness statement is C.26's, never this definition's. -/
noncomputable def dvResPoly (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    (f : Polynomial O) (u ℓ : ℕ) (hne₂ : (dvSideSet F f u ℓ).Nonempty) (M₀ : ℕ)
    (hpin₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) :
    Polynomial (F.stageField H₀ hpin) :=
  ((Finset.range (dvSideDeg F f u ℓ hne₂ + 1)).sum fun t =>
    Polynomial.C (F.twistRead H₀ hpin (M₀ - t * u) (dev F.key f (dvSideMin F f u ℓ hne₂ + t * ℓ)))
      * Polynomial.X ^ t)

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dvResPoly

end AxCheck
