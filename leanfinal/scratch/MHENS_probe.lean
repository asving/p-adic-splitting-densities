/-
MHENS probe (2026-08-26) — statement-shape elaboration for the dv-graded one-slope
Hensel engine (docs/in-progress/HENSEL_ENGINE_2026-08-26.md §2).

Prop-DEFINITIONS only (the C35b `D13Statement` pattern): every engine signature is
elaborated against the landed vocabulary, so binder shapes/carrier types are
machine-checked without asserting anything.  One PROVED implication at the end
(unpinned frontier ⟹ pinned frontier) with its axiom footprint.

Zero `sorry`, zero `axiom`.
-/
import Uniformity.ChapC.C35
import Uniformity.ChapC.C66b

namespace Uniformity.Density.Tower.MHENS

open Uniformity.Density.Leaf IsLocalRing Polynomial
open Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The DEGREE-PINNED label (doc §2 Theorem C, §7.3 repair R1): `HasLabel` plus the
classical `D′ ∣ deg` pin of LEMMA HE7-6.  The §7 refutation shows the unpinned
`HasLabel` admits far junk factors; this is the repaired primary object. -/
def HasLabelPinned {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) : Prop :=
  HasLabel L g ∧ (F.e₁ * F.f₁) ∣ g.natDegree

/-- The PINNED frontier (doc §8): `BlockFrontier`'s body with the maximality
quantifier restricted to pinned labels.  This is the discharge target of the repaired
F1.H3; the unpinned `BlockFrontier` is refutable from `BlockContext` (doc §7.2.2). -/
def BlockFrontierPinned {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : Prop :=
  ∃ fS : Polynomial O, HasLabel L fS ∧ fS ∣ f ∧ (F.e₁ * F.f₁) ∣ fS.natDegree ∧
    ∀ fS' : Polynomial O, HasLabelPinned L fS' → fS' ∣ f → fS' ∣ fS

/-- Theorem M, clauses 1–2 (doc §2/§3.2): the mixed support/side product law. -/
def MixedSupportLawStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
  ∀ g z : Polynomial O, g ≠ 0 → z ≠ 0 →
    dvSupp F (g * z) u ℓ = dvSupp F g u ℓ + dvSupp F z u ℓ ∧
    ∀ (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
      (hngz : (dvSideSet F (g * z) u ℓ).Nonempty),
      dvSideMin F (g * z) u ℓ hngz = dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz ∧
      dvSideMax F (g * z) u ℓ hngz = dvSideMax F g u ℓ hng + dvSideMax F z u ℓ hnz

/-- Theorem M, clause 3 (doc §3.3): the mixed residual product law, with the explicit
twist-cocycle unit `τ` (`= 1` on the `fgmn_dv_exact_mul` fence). -/
def MixedResidualLawStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
  ∀ g z : Polynomial O, g ≠ 0 → z ≠ 0 →
  ∀ (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) (Mg Mz Mgz : ℕ)
    (hpg : dvHgt F g (dvSideMin F g u ℓ hng) = (Mg : ℕ∞))
    (hpz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Mz : ℕ∞))
    (hpgz : dvHgt F (g * z) (dvSideMin F (g * z) u ℓ hngz) = (Mgz : ℕ∞)),
    ∃ τ : (F.stageField H₀ hpin)ˣ,
      dvResPoly F H₀ hpin (g * z) u ℓ hngz Mgz hpgz
        = Polynomial.C (τ : F.stageField H₀ hpin)
          * (dvResPoly F H₀ hpin g u ℓ hng Mg hpg
             * dvResPoly F H₀ hpin z u ℓ hnz Mz hpz)

/-- Theorem A (doc §2/§4): the dv-graded one-slope Hensel existence, B.41-shaped
conclusion with exact residual identities.  The `D′ ∣ deg g` rider is load-bearing
(doc §7). -/
def EngineExistenceStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
  ∀ g : Polynomial O, g.Monic → 0 < g.natDegree → (F.e₁ * F.f₁) ∣ g.natDegree →
    IsDvPure F g u ℓ →
  ∀ (hne : (dvSideSet F g u ℓ).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞)),
  ∀ G H : Polynomial (F.stageField H₀ hpin), G.Monic → H.Monic → IsCoprime G H →
    G.coeff 0 ≠ 0 → H.coeff 0 ≠ 0 →
    dvResPoly F H₀ hpin g u ℓ hne M₀ hp = G * H →
  ∃ g₁ g₂ : Polynomial O, g = g₁ * g₂ ∧ g₁.Monic ∧ g₂.Monic ∧
    g₁.natDegree = ℓ * (F.e₁ * F.f₁) * G.natDegree ∧
    g₂.natDegree = ℓ * (F.e₁ * F.f₁) * H.natDegree ∧
    IsDvPure F g₁ u ℓ ∧ IsDvPure F g₂ u ℓ ∧
    dvHgt F g₁ 0 = ((u * G.natDegree : ℕ) : ℕ∞) ∧
    dvHgt F g₂ 0 = ((u * H.natDegree : ℕ) : ℕ∞) ∧
    (∀ (hne₁ : (dvSideSet F g₁ u ℓ).Nonempty) (M₁ : ℕ)
      (hp₁ : dvHgt F g₁ (dvSideMin F g₁ u ℓ hne₁) = (M₁ : ℕ∞)),
      dvResPoly F H₀ hpin g₁ u ℓ hne₁ M₁ hp₁ = G) ∧
    (∀ (hne₂ : (dvSideSet F g₂ u ℓ).Nonempty) (M₂ : ℕ)
      (hp₂ : dvHgt F g₂ (dvSideMin F g₂ u ℓ hne₂) = (M₂ : ℕ∞)),
      dvResPoly F H₀ hpin g₂ u ℓ hne₂ M₂ hp₂ = H)

/-- Theorem B (doc §2/§5): uniqueness of the labelled split on the `D′ ∣ deg`
stratum — completeness-free.  On the defective stratum this is REFUTED (doc §7). -/
def EngineUniquenessStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (L : LevelDatum F H₀ hpin), Irreducible π → 0 < F.h →
  ∀ g : Polynomial O, g.Monic → IsDvPure F g L.u L.ℓ →
    (F.e₁ * F.f₁) ∣ g.natDegree →
  ∀ a b a' b' : Polynomial O, g = a * b → g = a' * b' →
    HasLabel L a → HasLabel L a' → b.Monic → b'.Monic →
    (∀ (hne : (dvSideSet F b L.u L.ℓ).Nonempty) (M : ℕ)
      (hp : dvHgt F b (dvSideMin F b L.u L.ℓ hne) = (M : ℕ∞)),
      ¬ L.r ∣ dvResPoly F H₀ hpin b L.u L.ℓ hne M hp) →
    (∀ (hne : (dvSideSet F b' L.u L.ℓ).Nonempty) (M : ℕ)
      (hp : dvHgt F b' (dvSideMin F b' L.u L.ℓ hne) = (M : ℕ∞)),
      ¬ L.r ∣ dvResPoly F H₀ hpin b' L.u L.ℓ hne M hp) →
    a' = a ∧ b' = b

/-- PROVED: the unpinned frontier implies the pinned one (the repair only SHRINKS the
maximality quantifier; the witness clauses are identical).  The converse is exactly
what the §7 refutation separates. -/
theorem blockFrontierPinned_of_blockFrontier {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) {f : Polynomial O}
    (h : BlockFrontier L f) : BlockFrontierPinned L f := by
  obtain ⟨fS, hlab, hdvd, hdeg, hmax⟩ := h
  exact ⟨fS, hlab, hdvd, hdeg, fun fS' hlab' hdvd' => hmax fS' hlab'.1 hdvd'⟩

end Uniformity.Density.Tower.MHENS

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.MHENS.HasLabelPinned
#print axioms Uniformity.Density.Tower.MHENS.BlockFrontierPinned
#print axioms Uniformity.Density.Tower.MHENS.MixedSupportLawStatement
#print axioms Uniformity.Density.Tower.MHENS.MixedResidualLawStatement
#print axioms Uniformity.Density.Tower.MHENS.EngineExistenceStatement
#print axioms Uniformity.Density.Tower.MHENS.EngineUniquenessStatement
#print axioms Uniformity.Density.Tower.MHENS.blockFrontierPinned_of_blockFrontier

end AxCheck
