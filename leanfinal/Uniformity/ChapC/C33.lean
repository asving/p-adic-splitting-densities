/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C26
import Uniformity.ChapC.C29

/-!
# Uniformity.ChapC.C33 — the slope dissection at the level polygon

**Chapter C, NODE C.33** [theorem] [fresh] [signed: A-C.1]
(`blueprint/CHAP-C_tower_grammar.md` §5). ENV-C. Three signed declarations: the witness
structure `DvDissection` (B.42's landed template at the `dv`-carrier, packaged per GC-4's
inductive-domain licence) and the two theorem clauses `exists_dvDissection` /
`dvDissection_unique`.

*The statement (B.41/B.42 one level up).* Over the complete bundle, a monic `f` with
`F.key ∤ f` dissects along the sides of its level polygon above the frame floor: monic
`dv`-pure factors, one per side, each with the `(SEP)`-free degree law
`deg f_i = D′·(ℓ_i·dvSideDeg)` (= `D′·L_λ`), a below-floor monic remainder with no
above-floor sides, the product identity, and the side-detection iff; the monic dissection
is unique.

## Status

SKELETON — statements transcribed byte-exactly from `leanspec/Leanspec/ChapC.lean`
(A-C.1 §5, `axiom` → `theorem`); proofs in progress.
-/

namespace Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The witness type of C.33's dissection (B.41/B.42 one level up, at B.42's landed template
shape): slopes in lowest terms above the frame floor, per-side monic `dv`-pure factors with
the `(SEP)`-free degree law `deg f_i = D′·L_λ`, a below-floor monic remainder, the product,
and the side-detection iff. -/
structure DvDissection (F : KeyFrame O π) (f : Polynomial O) : Type _ where
  slopes : Finset (ℕ × ℕ)
  factor : ℕ × ℕ → Polynomial O
  below : Polynomial O
  hslopes : ∀ p ∈ slopes,
    0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ p.2 * ((F.e₁ * F.f₁) * F.h) < p.1
  hdistinct : ∀ p ∈ slopes, ∀ q ∈ slopes, p ≠ q → p.1 * q.2 ≠ q.1 * p.2
  hmonic : ∀ p ∈ slopes, (factor p).Monic
  hpure : ∀ p ∈ slopes, IsDvPure F (factor p) p.1 p.2
  hdeg : ∀ p ∈ slopes, ∀ hne : (dvSideSet F f p.1 p.2).Nonempty,
    (factor p).natDegree = (F.e₁ * F.f₁) * (p.2 * dvSideDeg F f p.1 p.2 hne)
  hbelow_monic : below.Monic
  hbelow : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
    ∀ hne : (dvSideSet F below u ℓ).Nonempty, dvSideDeg F below u ℓ hne = 0
  hprod : f = below * ∏ p ∈ slopes, factor p
  hsides : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
    ((u, ℓ) ∈ slopes ↔ ∃ hne : (dvSideSet F f u ℓ).Nonempty, 0 < dvSideDeg F f u ℓ hne)

/-- **Uniqueness, leg 1 (the slope sets agree).** Pure clause plumbing: each dissection's
`hslopes` establishes the floor/coprimality/positivity preconditions under which BOTH
dissections' `hsides` iffs fire against the same `f`-side data, so membership transfers.
No completeness, no `hπ`, no monicity of `f` needed for this leg. -/
theorem DvDissection.slopes_eq {F : KeyFrame O π} {f : Polynomial O}
    (D D' : DvDissection F f) : D.slopes = D'.slopes := by
  ext p
  constructor
  · intro hp
    obtain ⟨h2, hcop, hfloor⟩ := D.hslopes p hp
    exact (Prod.mk.eta (p := p) ▸ (D'.hsides p.1 p.2 h2 hcop hfloor).2)
      ((D.hsides p.1 p.2 h2 hcop hfloor).1 (Prod.mk.eta (p := p) ▸ hp))
  · intro hp
    obtain ⟨h2, hcop, hfloor⟩ := D'.hslopes p hp
    exact (Prod.mk.eta (p := p) ▸ (D.hsides p.1 p.2 h2 hcop hfloor).2)
      ((D'.hsides p.1 p.2 h2 hcop hfloor).1 (Prod.mk.eta (p := p) ▸ hp))

/-- **C.33 existence** — the slope dissection at the level polygon exists for every monic
`f` with `F.key ∤ f`, over the complete bundle. -/
theorem exists_dvDissection (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f) :
    Nonempty (DvDissection F f) := by
  sorry

/-- **C.33 uniqueness** — the monic dissection is unique: same slopes, same below-floor
remainder, same factor at each slope. -/
theorem dvDissection_unique (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f)
    (D D' : DvDissection F f) :
    D.slopes = D'.slopes ∧ D.below = D'.below ∧ ∀ p ∈ D.slopes, D.factor p = D'.factor p := by
  sorry

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.DvDissection
#print axioms Uniformity.Density.Tower.exists_dvDissection
#print axioms Uniformity.Density.Tower.dvDissection_unique

end AxCheck
