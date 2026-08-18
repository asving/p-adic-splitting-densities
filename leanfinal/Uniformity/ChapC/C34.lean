/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C26
import Uniformity.ChapC.C29

/-!
# Uniformity.ChapC.C34 — the residual dissection at the level polygon (SKELETON)

**Chapter C, NODE C.34** [theorem] [fresh] [signed: A-C.1]
(`blueprint/CHAP-C_tower_grammar.md` §5). ENV-C2. One signed declaration:
`exists_dv_residual_dissection`, signed at the consumed `(λ, r)`-block clause (the
"in particular" of the blueprint STATEMENT — what C.35/C.36/C.61 read); the general
coprime-prime-power refinement is proof content (B.48's route), not a second public
statement. Statement transcribed byte-exact from `leanspec/Leanspec/ChapC.lean`
(A-C.1 §5 block, byte-frozen there).

## MANDATORY vacuity audit (A-C.7 registry, five instances) — VERDICT: no instance

Audited against the five-instance registry (C.111 `hnode` unpinned carrier; C.94
self-loop; C.113 unconditional `hne`; C.118 clause-1 one-sided `≠ ⊤` guard; C.118
clause-2 unguarded consulted side data), plus A-C.8.4's extra low-degree-purity row:

* **`L : LevelDatum`** — the label is fenced at the source: `hℓ : 0 < ℓ`, `hcop`, the
  floor `hκ`, and `r` monic IRREDUCIBLE with `0 < natDegree` and `coeff 0 ≠ 0` (C.09).
  No unit-`r` stratum (on which `hdvd` would be unconditional and the complement clause
  unsatisfiable) and no `ℓ = 0` stratum (on which `0 • ⊤ = 0` would let ⊤-height
  abscissae attain the support) exists.
* **`hpure : IsDvPure F g L.u L.ℓ`** — the KNOWN C.66 low-degree collapse
  (`0 < deg g < D′` makes the two conjuncts coincide at abscissa `0`) is fenced HERE by
  `hdvd`: on that stratum the side is the single point `{0}` (`dvSideDeg = 0`), so
  `dvResPoly` is the constant `C (read at the pinned height)`, nonzero by C.26's
  pinned-read law (`natDegree_dvResPoly`, clause (iii): `coeff 0 ≠ 0`), and the
  nonconstant irreducible `L.r` divides no nonzero constant of the stage-field
  polynomial ring. `hdvd` is UNSATISFIABLE on the degenerate stratum — the guard binds.
  (This fence is a machine-checkable consequence of C.26; it lands as a lemma in this
  unit's leg 2.)
* **`hne : (dvSideSet F g L.u L.ℓ).Nonempty`** — C.113-SHAPE NOTE, benign: for monic
  `g` under `L.hℓ : 0 < ℓ` this is always inhabited (some `dev` block of a nonzero
  polynomial is nonzero, its `stageHeight` is finite, the finite-range `inf` is
  attained, and `0 < ℓ` blocks the `0 • ⊤ = 0` escape), so `hne` carries no fence
  content — but it is a dependent WITNESS binder (needed to state `dvSideMin`/
  `dvResPoly`), C.25's plumbing pattern, not a guard. The content guards are
  `hpure`/`hdvd`.
* **`{M₀} (hp : dvHgt … = (M₀ : ℕ∞))`** — the GC-1 numeral pin (C.25's `hpin₂`
  pattern): side members have finite height BY `DvOnSide`'s second conjunct (the
  finiteness is carried positively in the side-set definition, C.07), so `M₀` always
  exists and is unique. A pin, not a guard; the ⊤-height stratum is excluded one level
  earlier, positively — NOT by a C.118-style one-sided `≠ ⊤ →` implication. No such
  implication-guard occurs anywhere in the statement.
* **The complement `∀ (hne') (M₀') (hp'), ¬ L.r ∣ dvResPoly … g' …` (and its twin in
  the uniqueness clause)** — the C.118-pattern question is whether a degenerate
  competitor `g''` can satisfy this VACUOUSLY (empty quantification domain) and defeat
  uniqueness. It cannot: `g''` is constrained monic, and for monic `g''` under
  `L.hℓ > 0` the domain is never empty (same argument as `hne` above — the side set is
  nonempty and its min has finite height, so `(hne', M₀', hp')` always exists). The
  ∀-form over the complement's OWN pin witnesses is the blueprint's dependent-plumbing
  resolution, and it quantifies over a provably nonempty domain.
* **C.111 shape** — no unpinned carrier: `fS`, `g'` are tied to `g` by the product
  equation, `HasLabel`, monicity, and the complement clause; `HasLabel`'s internal
  existentials are pinned to `fS`'s own side read (C.29).
* **C.94 shape** — no relation/history is quantified; `(fS', g'') = (fS, g')` in the
  uniqueness clause is a consistency instance, not a collapse.

One SEAM (not a vacuity defect, recorded per the blueprint's C.39 note): the blueprint
STATEMENT text reads "up to the C.39-class unit scalar", while the signed Lean clause
uses `HasLabel` (C.29), whose residual clause is the EXACT power `dvResPoly … = L.r ^ m`.
The A-C.1 signature resolved the scalar to the exact-power normal form; discharging it
is part of the proof obligation (C.26's leading-read control), not a statement defect.

## Frontier situation (C.33's record applies)

DEPENDS: C.25 · C.26 · C.29 · C.33 · B.44–B.48 (route templates) · landed Hensel
engine. The signed route is B.48's graded-coprime lift AT THE `dv`-CARRIER — the same
missing dv-graded Hensel engine recorded at `C33_BLOCKED_2026-08-17.md` (no dv-level
analogue of B.39/B.40/B.41 exists; the only completeness-consuming ChapC nodes are not
Hensel-shaped). The A-C.8 cite pair for C.33 is owner-SIGNED but lands only when the
§A-C.8.5 certification is fully green, and in any case covers C.33's SLOPE dissection,
not this node's residual dissection. See `C34_BLOCKED_2026-08-18.md` (this directory)
for this node's own frontier record once the reachable legs are landed.
-/

namespace Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **NODE C.34** — the residual dissection at the level polygon, signed at the consumed
`(λ, r)`-block clause: under C.33's context, a `dv`-pure monic `g` whose level residual
is divisible by the label's `L.r` splits as `g = fS * g'` with `HasLabel L fS`, the
complement's residual `r`-free (∀-quantified over its own pin witnesses), uniquely so.
Byte-exact to `leanspec/Leanspec/ChapC.lean` (A-C.1 §5). -/
theorem exists_dv_residual_dissection {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {g : Polynomial O} (hg : g.Monic) (hpure : IsDvPure F g L.u L.ℓ)
    (hne : (dvSideSet F g L.u L.ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞))
    (hdvd : L.r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp) :
    ∃ fS g' : Polynomial O, g = fS * g' ∧ HasLabel L fS ∧ g'.Monic ∧
      (∀ (hne' : (dvSideSet F g' L.u L.ℓ).Nonempty) (M₀' : ℕ)
        (hp' : dvHgt F g' (dvSideMin F g' L.u L.ℓ hne') = (M₀' : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g' L.u L.ℓ hne' M₀' hp') ∧
      ∀ fS' g'' : Polynomial O, g = fS' * g'' → HasLabel L fS' → g''.Monic →
        (∀ (hne' : (dvSideSet F g'' L.u L.ℓ).Nonempty) (M₀' : ℕ)
          (hp' : dvHgt F g'' (dvSideMin F g'' L.u L.ℓ hne') = (M₀' : ℕ∞)),
          ¬ L.r ∣ dvResPoly F H₀ hpin g'' L.u L.ℓ hne' M₀' hp') →
        fS' = fS ∧ g'' = g' := by
  sorry

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.exists_dv_residual_dissection

end AxCheck
