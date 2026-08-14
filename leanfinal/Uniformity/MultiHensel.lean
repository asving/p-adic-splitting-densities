/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.HenselFactorization

/-!
# Uniformity.MultiHensel — the `n`-fold Hensel factorization

**CN-17** of `spec/CERTAIN_NODES_2026-08-14.md` (ledger HYP.03): *a finite pairwise-coprime
residual factorization lifts to the corresponding finite monic factorization.*

The landed two-block theorem is `Hensel.exists_monic_factorization`
(`HenselFactorization.lean:393`); this file iterates it over a `Finset` by induction, peeling one
index at a time and using `IsCoprime.prod_right` to see the peeled factor as coprime to the
product of the rest.

Two deliberate features of the contract, both from the spec's RISK line:

* the lifted family `g : ι → Polynomial R` is a **total** function while only `i ∈ s` is
  constrained — the value off `s` is junk (`1`), and *no* clause pins it, so the interface is not
  over-fixed;
* **uniqueness is not part of this contract**. A consumer that needs it should book a separate
  node from `Hensel.monic_factorization_unique`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity

namespace Hensel

open Polynomial IsLocalRing

section MultiHensel

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]

/-- The induction behind CN-17: same statement, with the polynomial `f` (and the hypotheses that
mention it) universally quantified inside the motive, so that the `insert` step may apply the
inductive hypothesis to the *cofactor* rather than to `f`. -/
private theorem exists_monic_factorization_finset_aux {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (g₀ : ι → Polynomial (ResidueField R)) :
    ∀ {f : Polynomial R}, f.Monic → (∀ i ∈ s, (g₀ i).Monic) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g₀ i) (g₀ j)) →
      f.map (residue R) = ∏ i ∈ s, g₀ i →
      ∃ g : ι → Polynomial R, (∀ i ∈ s, (g i).Monic) ∧ f = ∏ i ∈ s, g i ∧
        (∀ i ∈ s, (g i).map (residue R) = g₀ i) ∧
        (∀ i ∈ s, (g i).natDegree = (g₀ i).natDegree) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf _ _ hfgh
    rw [Finset.prod_empty] at hfgh
    have hdeg : f.natDegree = 0 := by
      rw [natDegree_eq_of_map_eq hf hfgh, natDegree_one]
    refine ⟨fun _ => 1, by simp, ?_, by simp, by simp⟩
    rw [Finset.prod_empty]
    exact eq_one_of_monic_natDegree_zero hf hdeg
  | insert i s hi ih =>
    intro f hf hmon hcop hfgh
    -- peel the block at `i`: it is coprime to the product of the remaining blocks
    have hgi : (g₀ i).Monic := hmon i (Finset.mem_insert_self i s)
    have hprod : (∏ j ∈ s, g₀ j).Monic :=
      monic_prod_of_monic _ _ (fun j hj => hmon j (Finset.mem_insert_of_mem hj))
    have hcopi : IsCoprime (g₀ i) (∏ j ∈ s, g₀ j) :=
      IsCoprime.prod_right (fun j hj => hcop i (Finset.mem_insert_self i s) j
        (Finset.mem_insert_of_mem hj) (by rintro rfl; exact hi hj))
    have hsplit : f.map (residue R) = g₀ i * ∏ j ∈ s, g₀ j := by
      rw [hfgh, Finset.prod_insert hi]
    obtain ⟨g, h, hgm, hhm, hfeq, hgr, hhr, hgd, -⟩ :=
      exists_monic_factorization hf hgi hprod hcopi hsplit
    -- and recurse on the cofactor
    obtain ⟨gs, hgsm, hheq, hgsr, hgsd⟩ := ih hhm
      (fun j hj => hmon j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk hjk =>
        hcop j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      hhr
    have hupd : ∀ j ∈ s, (if j = i then g else gs j) = gs j := fun j hj =>
      if_neg (by rintro rfl; exact hi hj)
    refine ⟨fun j => if j = i then g else gs j, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj'
      · simpa using hgm
      · simpa [hupd j hj'] using hgsm j hj'
    · have hp : ∏ j ∈ insert i s, (if j = i then g else gs j) = g * ∏ j ∈ s, gs j := by
        rw [Finset.prod_insert hi, Finset.prod_congr rfl hupd]
        simp
      rw [hp, ← hheq]
      exact hfeq
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj'
      · simpa using hgr
      · simpa [hupd j hj'] using hgsr j hj'
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj'
      · simpa using hgd
      · simpa [hupd j hj'] using hgsd j hj'

/-- **CN-17 — the `n`-fold Hensel factorization.** Over a complete local ring, a finite
*pairwise-coprime* monic factorization of the residue reduction of a monic `f` lifts to a monic
factorization of `f` indexed by the same finite set, with the degrees of the residual blocks.

The lifted family is total; only its values on `s` are constrained (see the module docstring).
Uniqueness is deliberately not asserted. -/
theorem exists_monic_factorization_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {f : Polynomial R} (hf : f.Monic) (g₀ : ι → Polynomial (ResidueField R))
    (hmon : ∀ i ∈ s, (g₀ i).Monic)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g₀ i) (g₀ j))
    (hfgh : f.map (residue R) = ∏ i ∈ s, g₀ i) :
    ∃ g : ι → Polynomial R, (∀ i ∈ s, (g i).Monic) ∧ f = ∏ i ∈ s, g i ∧
      (∀ i ∈ s, (g i).map (residue R) = g₀ i) ∧
      (∀ i ∈ s, (g i).natDegree = (g₀ i).natDegree) :=
  exists_monic_factorization_finset_aux s g₀ hf hmon hcop hfgh

end MultiHensel

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Hensel.exists_monic_factorization_finset

end AxCheck

end Hensel

end Uniformity
