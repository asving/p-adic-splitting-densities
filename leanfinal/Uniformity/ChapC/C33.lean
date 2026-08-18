/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C26
import Uniformity.ChapC.C29

/-!
# Uniformity.ChapC.C33 — the slope dissection at the level polygon (PARTIAL landing)

**Chapter C, NODE C.33** [theorem] [fresh] [signed: A-C.1]
(`blueprint/CHAP-C_tower_grammar.md` §5). ENV-C. Three signed declarations: the witness
structure `DvDissection` (B.42's landed template at the `dv`-carrier, packaged per GC-4's
inductive-domain licence) and the two theorem clauses `exists_dvDissection` /
`dvDissection_unique`.

## ⚠ PARTIAL LANDING — the two signed theorems are ROUTE-BLOCKED

**Landed here (sorry-free, Lean-core):**

* `DvDissection` — the signed witness type, byte-exact to `leanspec/Leanspec/ChapC.lean`
  (A-C.1 §5). This is what C.35's choice and the §5 consumers need to STATE things.
* `DvDissection.slopes_eq` — uniqueness leg 1: any two dissections of the same `f` carry
  the same slope set (pure clause plumbing off `hslopes` + `hsides`).
* `DvDissection.below_eq_of_factor_eq` — uniqueness leg 2 REDUCTION: if the per-slope
  factors agree then the below-floor remainders agree (monic cancellation off `hprod`).
* `dvDissection_unique_of_factor_eq` — the packaging: the FULL signed uniqueness
  conclusion follows from the per-slope factor leg alone. So the entire remaining content
  of `dvDissection_unique` is the one goal `∀ p ∈ D.slopes, D.factor p = D'.factor p`
  (purity separation), and the entire remaining content of the node is that plus
  `exists_dvDissection`.

**NOT landed — `exists_dvDissection` and `dvDissection_unique`.** Their signed statements
remain in `leanspec/Leanspec/ChapC.lean` (byte-frozen, untouched). The obstruction record
is **`C33_BLOCKED_2026-08-17.md`** (this directory): the signed PROOF route re-runs
B.41/B.42's two-piece split one level up, but (i) the multi-side peel needs the graded
Hensel AT A VERTEX that is machine-checked missing already at order 1
(`../ChapB/B42_ROUTE_BLOCKED.lean.txt` — the reason B.42 itself is an owner-signed
gate-(b) axiom), (ii) no `dv`-level Hensel engine exists at all (no analogue of
B.39/B.40/B.41 at the `dv`-carrier), (iii) B.41/B.42 are not consumable directly
(`IsKey F.key` is FALSE at `F.h ≥ 1`, C01 header) and B.42's axiom hypotheses
(`hres`/`h0`, single-branch) do not match even at the degenerate frame, and (iv) the
uniqueness separation leg needs cross-slope `dv`-polygon additivity, which is landed
nowhere and is NOT part of C.66's signed same-slope clause. Neither statement is claimed
false — both are the classical theorem of the polygon at the level (r = 1) carrier and
are expected true as signed.

## Status

Sorry-free, axiom-free (Lean core only) — for the PARTIAL scope above. The two signed
theorem clauses are OPEN, blocked per the record.
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

/-- **Uniqueness, leg 2 as a REDUCTION (the below-floor remainders agree, given the
factors do).** From the two `hprod`s the products over the common slope set (leg 1) agree,
and the product of the monic factors is monic hence a regular element of the domain
`O[X]`; cancel it. No completeness, no `hπ`, no monicity of `f` needed. -/
theorem DvDissection.below_eq_of_factor_eq {F : KeyFrame O π} {f : Polynomial O}
    (D D' : DvDissection F f) (hfac : ∀ p ∈ D.slopes, D.factor p = D'.factor p) :
    D.below = D'.below := by
  have hP : ∏ p ∈ D.slopes, D.factor p = ∏ p ∈ D'.slopes, D'.factor p := by
    rw [← D.slopes_eq D']
    exact Finset.prod_congr rfl hfac
  have hmon : (∏ p ∈ D.slopes, D.factor p).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun p hp => D.hmonic p hp)
  have key : D.below * ∏ p ∈ D.slopes, D.factor p
      = D'.below * ∏ p ∈ D.slopes, D.factor p :=
    calc D.below * ∏ p ∈ D.slopes, D.factor p = f := D.hprod.symm
      _ = D'.below * ∏ p ∈ D'.slopes, D'.factor p := D'.hprod
      _ = D'.below * ∏ p ∈ D.slopes, D.factor p := by rw [hP]
  exact mul_right_cancel₀ hmon.ne_zero key

/-- **The uniqueness frontier, made exact.** The FULL signed conclusion of
`dvDissection_unique` follows from the per-slope factor leg alone; so the missing content
of the signed uniqueness theorem is EXACTLY the purity-separation goal
`∀ p ∈ D.slopes, D.factor p = D'.factor p` (see `C33_BLOCKED_2026-08-17.md`). -/
theorem dvDissection_unique_of_factor_eq {F : KeyFrame O π} {f : Polynomial O}
    (D D' : DvDissection F f) (hfac : ∀ p ∈ D.slopes, D.factor p = D'.factor p) :
    D.slopes = D'.slopes ∧ D.below = D'.below ∧ ∀ p ∈ D.slopes, D.factor p = D'.factor p :=
  ⟨D.slopes_eq D', D.below_eq_of_factor_eq D' hfac, hfac⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.DvDissection
#print axioms Uniformity.Density.Tower.DvDissection.slopes_eq
#print axioms Uniformity.Density.Tower.DvDissection.below_eq_of_factor_eq
#print axioms Uniformity.Density.Tower.dvDissection_unique_of_factor_eq

end AxCheck
