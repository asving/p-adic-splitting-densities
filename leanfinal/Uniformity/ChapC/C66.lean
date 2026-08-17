/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C25
import Uniformity.ChapC.C29

/-!
# Uniformity.ChapC.C66 — the [FGMN] residual-multiplicativity axiom (gate-(b) cite)

**Chapter C, NODE C.66 `[cite:FGMN]`** — the SECOND landed literature-cite axiom of the
formalization (after chapter B's `exists_slope_factorization`), at the **A-C.6 REDRAFTED
statement** (the A-C.1 draft was machine-refuted pre-landing; record:
`C66_REFUTATION.lean.txt`; redraft: `leanspec/Leanspec/ChapC.lean`, A-C.6 block, transcribed
here verbatim into the landed vocabulary).

## Faithfulness entry

* **Publication.** J. Guàrdia, J. Montes, E. Nart (with the FGMN residual-ideals line),
  *J. Algebra* **427** (2015) 30–75, DOI 10.1016/j.jalgebra.2014.12.022. Cited results:
  **Thm 2.8** (principal-polygon additivity), **Cor 4.9(3)** and **Cor 4.12(3)** (residual
  multiplicativity `R_i(gh) = R_i(g)·R_i(h)` up to the nonzero constant). Numbering per the
  A-3 audit (`docs/CITE_NUMBERING_AUDIT_2026-08-16.md`); the statement texts are verified
  against the in-repo layout print `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`.
* **Scope fence.** Exactly the multiplicativity clause that Step II of `LEMMA GENTOW-6.1`
  consumes — never the full FGMN machinery, never the closed form of `w`.
* **The `hfloor` fence is the source's own standing hypothesis.** [FGMN] states the product
  theorems for the PRINCIPAL polygon `N⁻` only (`λ > 0`), and prints the refuting boundary
  pair immediately after Thm 2.8. In cleared coordinates `λ = u/ℓ − (e₁f₁)·h`, so `λ > 0` is
  `hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u`; the A-C.1 draft OMITTED it and was refuted at
  exactly `λ = 0`.
* **The degree binders `hdg`/`hdg'`/`hpos`/`hpos'` are CONSERVATIVE** (the source's
  Cor 4.12(3) is degree-free once `λ > 0`): they mirror B.42 clause 3 and C.33's `hdeg`,
  every consumer supplies them for free, and they independently kill the refuting pair.
  The owner may strike them without touching the cite's faithfulness (A-C.6 §I.6 displays
  the choice); they are KEPT to keep the trusted base as narrow as possible.
* **Signature.** Owner-signed 2026-08-17 under the ratification-by-compile ruling
  (PROJECT_STATE append #84): the final acceptance check is the capstone's axiom footprint
  being exactly Lean core + the signed cites, enforced mechanically by the chapter-I
  `#axiom_core`/`#axiom_reg` build guards.

## Non-vacuity / consistency

* **Satisfiability**: `C66_REDRAFT_CERT.lean.txt` leg B exhibits a full instance of every
  binder at the landed `s2Frame` (C.97) over `ℤ₂` with `g = x² + 2` at `(u, ℓ) = (4, 1)` —
  the hypotheses are jointly inhabited, so the axiom is not vacuously true.
* **Non-refutability**: the SAME program that refuted the A-C.1 draft no longer elaborates
  against this statement (it dies at the `hfloor` binder, and `refutingPair_hfloor_false` /
  `refutingPair_hdg_false` PROVE the fence excludes the refuting data) — cert record leg A.
* **Numeric leg**: `verification/ac6_cite_redraft_check.py` PART 1 — 26 in-binder
  multiplicativity pairs over the stage field, exact arithmetic, green.

The strict-sweep allowlist after this landing:
`{propext, Classical.choice, Quot.sound, exists_slope_factorization, fgmn_residual_mul, …}`
(each landed gate-(b) cite is appended as it lands).
-/

namespace Uniformity.Density.Tower

open Polynomial Uniformity.Density.Leaf

set_option linter.unusedVariables false in
/-- **NODE C.66 `[cite:FGMN]` (gate (b)).** Residual multiplicativity at the dv-layer: on the
`λ > 0` region (the `hfloor` fence), the residual polynomial of a product of dv-pure monic
polynomials is the product of their residual polynomials up to a nonzero stage-field constant.
[FGMN] Thm 2.8 + Cor 4.9(3) + Cor 4.12(3); the full faithfulness entry is the module
docstring. Statement = the A-C.6 redraft, byte-transcribed. -/
axiom fgmn_residual_mul :
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    {g g' : Polynomial O} (hg : g.Monic) (hg' : g'.Monic) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hdg' : F.e₁ * F.f₁ ∣ g'.natDegree)
    (hpos : 0 < g.natDegree) (hpos' : 0 < g'.natDegree)
    (hpg : IsDvPure F g u ℓ) (hpg' : IsDvPure F g' u ℓ)
    (hne : (dvSideSet F g u ℓ).Nonempty) (hne' : (dvSideSet F g' u ℓ).Nonempty)
    (hne'' : (dvSideSet F (g * g') u ℓ).Nonempty)
    {M₀ M₀' M₀'' : ℕ}
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞))
    (hp' : dvHgt F g' (dvSideMin F g' u ℓ hne') = (M₀' : ℕ∞))
    (hp'' : dvHgt F (g * g') (dvSideMin F (g * g') u ℓ hne'') = (M₀'' : ℕ∞)),
    ∃ c : F.stageField H₀ hpin, c ≠ 0 ∧
      dvResPoly F H₀ hpin (g * g') u ℓ hne'' M₀'' hp''
        = Polynomial.C c
            * (dvResPoly F H₀ hpin g u ℓ hne M₀ hp * dvResPoly F H₀ hpin g' u ℓ hne' M₀' hp')

end Uniformity.Density.Tower

/-! ## Axiom footprint (the axiom prints itself; consumers inherit it) -/

section AxCheck
#print axioms Uniformity.Density.Tower.fgmn_residual_mul
end AxCheck
