/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOf
import Uniformity.HenselFactorization

/-!
# Uniformity.Density.TypeOfAlgebra — the peel law for `typeOf`, and two leaf instances

This file collects the "peel law" chain from `spec/CERTAIN_NODES_2026-08-14.md`:

* **CN-02** `monicFactors_mul` — monic factorizations add over products.
* **CN-03** `typeOf_mul` — the peel/product law for `typeOf` on `.data`, the Lean discharge of
  HE7.A clause 6 ("their ramification and residue degrees are obtained by multiplying the
  successive displayed `e`- and `f`-increments").
* **CN-23** `FactorizationType.degree_mk_add` — the matching degree bookkeeping, pure `Multiset`
  arithmetic, introducing no algebraic structure on `FactorizationType`.
* **CN-14** `typeOf_prod_X_sub_C` — the totally split type at every degree `n`, by induction on
  `n` through CN-03 and the landed `typeOf_of_natDegree_one`.
* **CN-18** `typeOf_of_residual_coprime` — the order-0 / level-1 peel: the landed
  `Hensel.exists_monic_factorization_dvr` with CN-03's conclusion appended.

None of these add any instance to `FactorizationType` itself (see the REJECTED R14 entry of the
spec): the peel law is stated entirely on `.data` and on the explicit multiset sum
`⟨σ.data + τ.data⟩`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

section Peel

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **CN-02 — monic factorizations add over products.** No coprimality or separability
hypothesis: `Monic` on `f` and `g` is all that is used. -/
theorem monicFactors_mul {f g : Polynomial O} (hf : f.Monic) (hg : g.Monic) :
    monicFactors (f * g) = monicFactors f + monicFactors g := by
  apply monicFactors_eq
  have hf' := monicFactors_spec hf
  have hg' := monicFactors_spec hg
  refine ⟨fun p hp => ?_, ?_⟩
  · rcases Multiset.mem_add.1 hp with h1 | h1
    · exact hf'.1 p h1
    · exact hg'.1 p h1
  · rw [Multiset.prod_add, hf'.2, hg'.2]

/-- **CN-03 — the peel/product law for `typeOf`.** Stated on `.data`, not on any addition
structure for `FactorizationType`, so it survives verbatim if such structure is later added
(see the module docstring). -/
theorem typeOf_mul {f g : Polynomial O} (hf : f.Monic) (hg : g.Monic) :
    (typeOf (f * g)).data = (typeOf f).data + (typeOf g).data := by
  rw [typeOf_data, typeOf_data, typeOf_data, monicFactors_mul hf hg, Multiset.map_add]

end Peel

end Uniformity.Density

namespace Uniformity

/-- **CN-23 — the degree bookkeeping half of the peel law.** Pure `Multiset` arithmetic over the
frozen `FactorizationType.degree`; introduces no algebraic structure on `FactorizationType`. -/
theorem FactorizationType.degree_mk_add (σ τ : FactorizationType) :
    (⟨σ.data + τ.data⟩ : FactorizationType).degree = σ.degree + τ.degree := by
  simp [FactorizationType.degree, Multiset.map_add, Multiset.sum_add]

end Uniformity

namespace Uniformity.Density

open IsLocalRing Polynomial

section SplitLeaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **CN-14 — the totally split type at every `n`.** Induction on `n` via `Fin.prod_univ_castSucc`
to peel the last linear factor, CN-03 to read the type of the product, and the landed
`typeOf_of_natDegree_one` for the peeled factor's type. The `n = 0` base case is the empty
product `1`, whose type is `⟨0⟩ = ⟨Multiset.replicate 0 (1,1)⟩`. -/
theorem typeOf_prod_X_sub_C {n : ℕ} (r : Fin n → O) :
    typeOf (∏ i : Fin n, (X - C (r i))) = ⟨Multiset.replicate n (1, 1)⟩ := by
  induction n with
  | zero =>
    have h1 : (∏ i : Fin 0, (X - C (r i))) = 1 := Fin.prod_univ_zero _
    have hF : IsMonicFactorization (1 : Polynomial O) 0 :=
      ⟨fun p hp => absurd hp (Multiset.notMem_zero p), Multiset.prod_zero⟩
    rw [h1]
    apply FactorizationType.ext
    simp [typeOf_data, monicFactors_eq hF]
  | succ n ih =>
    have hsplit : (∏ i : Fin (n + 1), (X - C (r i)))
        = (∏ i : Fin n, (X - C (r (Fin.castSucc i)))) * (X - C (r (Fin.last n))) :=
      Fin.prod_univ_castSucc _
    have hG : (∏ i : Fin n, (X - C (r (Fin.castSucc i)))).Monic :=
      monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
    have hH : (X - C (r (Fin.last n))).Monic := monic_X_sub_C _
    have hHtype : typeOf (X - C (r (Fin.last n))) = ⟨({(1, 1)} : Multiset (ℕ × ℕ))⟩ :=
      typeOf_of_natDegree_one hH (natDegree_X_sub_C _)
    have hGtype : typeOf (∏ i : Fin n, (X - C (r (Fin.castSucc i))))
        = ⟨Multiset.replicate n (1, 1)⟩ := ih (fun i => r (Fin.castSucc i))
    apply FactorizationType.ext
    rw [hsplit, typeOf_mul hG hH, hGtype, hHtype]
    show Multiset.replicate n (1, 1) + {(1, 1)} = Multiset.replicate (n + 1) (1, 1)
    rw [← Multiset.replicate_one (1, 1), ← Multiset.replicate_add]

end SplitLeaf

end Uniformity.Density

namespace Uniformity.Density

open Uniformity.Hensel IsLocalRing Polynomial

section ResidualCoprime

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- **CN-18 — the order-0 / level-1 peel.** Welds the landed
`Hensel.exists_monic_factorization_dvr` to CN-03's conclusion. -/
theorem typeOf_of_residual_coprime {f : Polynomial O} (hf : f.Monic)
    {g₀ h₀ : Polynomial (ResidueField O)} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hfgh : f.map (residue O) = g₀ * h₀) :
    ∃ g h : Polynomial O, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (residue O) = g₀ ∧ h.map (residue O) = h₀ ∧
      g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree ∧
      (typeOf f).data = (typeOf g).data + (typeOf h).data := by
  obtain ⟨g, h, hg, hh, hfeq, hgmap, hhmap, hgdeg, hhdeg⟩ :=
    exists_monic_factorization_dvr O hf hg₀ hh₀ hcop hfgh
  exact ⟨g, h, hg, hh, hfeq, hgmap, hhmap, hgdeg, hhdeg, hfeq ▸ typeOf_mul hg hh⟩

end ResidualCoprime

end Uniformity.Density
