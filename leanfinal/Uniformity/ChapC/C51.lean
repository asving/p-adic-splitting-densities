/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C29
import Uniformity.ChapC.C44

/-!
# Uniformity.ChapC.C51 — `towerLocus`: the tower-entry locus `𝒯` (FULL side only)

**Chapter C, NODE C.51** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §6, composed keys and
the tower bridges; the A-C.1 amendment set governs, and the SIGNATURE is
`[signed: A-C.1 — elaborated in leanspec/Leanspec/ChapC.lean]`). **ENV-C1**. One signed
declaration, definitional.

## What the locus is

`towerLocus T μ₂` — the set of monic `f ∈ O[X]` of degree `n = μ₂·D₂` (C.42's composed degree
`D₂ = D′·e₂f₂ = (e₁f₁)(e₂f₂)`) whose **level-1 read exhibits the FULL inner side**:

* `IsDvPure F f T.u₂ T.e₂` (C.29) — the `Φ′`-polygon of `f` is the single side of inner slope
  `−u₂/e₂`, end to end, i.e. from `(0, μ₁·κ₂)` cleared to `(μ₁, 0)`;
* the side residual is `r̃ ^ μ₂` — C.25's `dvResPoly` read, with `r̃ = towerLabel T` the C.44
  translated label (the twist-coherent normalization *is* the `dvResPoly` read, C.25's fixed
  convention, which is why no extra coherence hypothesis appears).

Every §6 GENTOW1 statement is scoped to `𝒯`: the **FULL-side fence** of `EFF.GENTOW1.14`, which
the corpus repeats at `EFF.GENTOW1.46`. Partial inner sides are **not** in scope here — they are
§8's GENTOW4 territory, and a consumer that meets one has left this locus rather than found a
counterexample to it.

## Two shape decisions, both signed at A-C.1

* **The residual EXPONENT is `μ₂`, not `f₂μ₂` — a caught defect (C-H12 class).** The committed
  display writes the exponent as `e₂f₂μ₂/e₂ = f₂μ₂`; that quantity is the residual's **DEGREE**,
  not its exponent. With `deg r̃ = f₂` (C.44's `towerLabel_spec`), `deg (r̃ ^ μ₂) = f₂μ₂` is exactly
  the side degree the display names, so the two readings agree on the degree and differ on the
  polynomial — and only the exponent `μ₂` is consistent with C.26's degree law for `dvResPoly`.
  The two coincide precisely at `f₂ = 1`, the coincidence regime that hid the slip.
* **The pins are ∀-quantified here, where C.29's `HasLabel` makes them existential.** The
  nonemptiness witness `hne`, the pinned height numeral `M₀` and its pin `hp` are `dvResPoly`'s
  dependent plumbing; membership in `𝒯` asserts the residual identity **for every** such choice.
  This is the stronger reading and the one A-C.1 signs ("pins ∀-quantified (they exist by
  purity)") — purity supplies `hne`, and `M₀` is determined by `hp`, so the ∀ ranges over a
  singleton-up-to-proof-irrelevance family and costs nothing to a supplier while giving every
  consumer the instance it needs without re-deriving the pin.

## Binder note

The pin binder is C.14a's **named** proposition `F.Pin H₀` (amendment A-C.1(c)), not the
written-out `npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)`
of C.03/C.09/C.25/C.42/C.44. The two are definitionally equal — `KeyFrame.Pin` is exactly that
equation — so `TowerDatum F H₀ hpin`, `dvResPoly F H₀ hpin …` and `towerLabel T` all elaborate
against it unchanged. This is the stub's own binder shape and the shape the whole §6 block
(`budgetFloor`, `towerFreeCount`, `towerLocus_iff_budget`, `towerLocus_fibration`,
`towerLocus_node_floor`) is written in, so it is landed as signed rather than normalized to the
older spelling.

`Set (Polynomial O)` and not a `Finset`: the locus is a condition on all of `O[X]`, and the
counting statements (C.53's fibration) cut it down to a coefficient box before counting.

## ⚠ FAITHFULNESS (trust boundary, flagged for human review)

Two clauses, both carried.

1. **The FULL-side fence is part of the definition, not a lemma.** `IsDvPure` at `(u₂, e₂)` is
   what makes the inner side span the whole abscissa range; dropping it would silently widen `𝒯`
   to polygons with a second inner slope, and every §6 count downstream would be false. The
   scope restriction is `EFF.GENTOW1.14`'s, transcribed.
2. **`towerLabel` carries the twist.** The residual is compared to a power of C.44's *translated*
   label `r̃ = η^{−Q f₂}·ψ₂(η^Q Z)` (`Q = twistExp u₂`), not to a power of the raw inner residual
   `ψ₂`. The translation is what makes the comparison well-posed against C.25's ϖ-read; reading
   this clause as "`R_λ = ψ₂^{μ₂}`" is a faithfulness error.

**DEPENDS.** C.25 (`dvResPoly`) · C.29 (`IsDvPure`) · C.42 (`TowerDatum`, `D₂`) · C.44
(`towerLabel`) · C.14a (`KeyFrame.Pin`) — by committed node ID (GC-13(b)). The three imports are
`Uniformity.ChapC.C14a`, `Uniformity.ChapC.C29` (pulling C.09, C.25, C.07, C.06) and
`Uniformity.ChapC.C44` (pulling C.42, C.19, C.15, C.03).

**PROOF.** Definitional. The body is the gate-verified `leanspec/Leanspec/ChapC.lean` stub body
verbatim.

SOURCE: `EFF.GENTOW1.14` (verbatim, including the FULL-side fence); `EFF.GENTOW1.46` (the fence
repeated).

**TEETH.** P-4's level-1 entry gate (12 random in-budget members per family, REAL 180) —
**executable regression retained**, not a Lean theorem: a membership predicate carries no
correctness claim to test in Lean, and the gate's content is that the predicate's members are the
polynomials PARI reads as tower-entry.

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The signed declaration -/

/-- **C.51 — the tower-entry locus `𝒯` (FULL side only).** Monic `f` of degree `μ₂·D₂` whose
level-1 read is one full inner side of slope `−u₂/e₂` with residual `r̃ ^ μ₂` (`EFF.GENTOW1.14`).

The residual exponent is `μ₂` (A-C.1's caught defect: the display's `e₂f₂μ₂/e₂` is the side
DEGREE); `r̃` is C.44's translated label, not the raw `ψ₂`; and the pins are ∀-quantified,
purity supplying the nonemptiness witness. -/
def towerLocus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) : Set (Polynomial O) :=
  {f | f.Monic ∧ f.natDegree = μ₂ * T.D₂ ∧ IsDvPure F f T.u₂ T.e₂ ∧
    ∀ (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin f T.u₂ T.e₂ hne M₀ hp = (towerLabel T) ^ μ₂}

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.towerLocus

end AxCheck
