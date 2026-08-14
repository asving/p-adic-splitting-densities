/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.Density.DensityAPI — the general-`n` density/census API (CN-05 … CN-11)

**FORMALIZATION BATCH B** (`spec/CERTAIN_NODES_2026-08-14.md`, nodes CN-05–CN-11): the
density/census lemmas that are certain on the capstone path regardless of the open design
decisions, generalizing landed `n = 2` instances (`Gates.lean`, `Drainage.lean`) to every
degree `n`, over the `decidedSeq`/`possibleSeq`/`decidedDensity`/`genuineDensity` machinery of
`GenuineDensity.lean`. This unit lands CN-05/CN-06 (edge: CN-06 depends on CN-05) and
CN-07/CN-08 (edge: CN-08 depends on CN-07).

* **CN-05** `genuineDensity_eq_zero_of_forall_ne` (+ helper `decidedDensity_eq_zero_of_forall_ne`):
  a type that no monic degree-`n` polynomial ever has gets density `0`. This is the `num = 0`
  branch of `UniformityStatement` (`Statement.lean:71`) for every non-occurring `σ`.
* **CN-06** `genuineDensity_eq_zero_of_degree_ne`: an off-degree type gets density `0` — the
  clause that makes the capstone's `σ.degree = n` hypothesis non-decorative.
* **CN-07** `proj_eq_iff_dvd`: class equality at level `N` is coefficientwise congruence mod
  `π ^ N`, at every `n` (generalizing the one-directional `Drainage.lean:639
  congAt_of_proj_eq`, which is `n = 2` only, to an iff at general `n`).
* **CN-08** `decidedAt_of_congr`: a congruence-invariant certificate on the coefficients decides
  the class — the single interface between certificates and `decidedSet` membership.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial Filter Topology

/-! ## CN-05 : non-occurring types have density `0` -/

section NonOccurring

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **CN-05.** If no monic degree-`n` polynomial over `O` ever has type `σ`, the genuine density
of `σ` is `0`: every level-`N` possible set is empty, so `possibleSeq` is identically `0` and its
infimum is `0`. -/
theorem genuineDensity_eq_zero_of_forall_ne {n : ℕ} {σ : FactorizationType}
    (h : ∀ a : Fin n → O, typeOf (monicPoly a) ≠ σ) : genuineDensity O n σ = 0 := by
  have hseq0 : possibleSeq O n σ = fun _ => (0 : ℝ) := by
    funext N
    have hempty : possibleSet O n σ N = ∅ := by
      ext c
      simp only [possibleSet, PossibleAt, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨a, -, hta⟩
      exact h a hta
    rw [possibleSeq, possibleCount, hempty]
    simp
  unfold genuineDensity
  rw [hseq0]
  exact ciInf_const

/-- **CN-05, helper.** Immediate from `decidedDensity_le_genuineDensity`: the certified (inner)
density is sandwiched between `0` and the genuine (outer) one, which CN-05 puts at `0`. -/
theorem decidedDensity_eq_zero_of_forall_ne {n : ℕ} {σ : FactorizationType}
    (h : ∀ a : Fin n → O, typeOf (monicPoly a) ≠ σ) : decidedDensity O n σ = 0 := by
  have hg := genuineDensity_eq_zero_of_forall_ne h
  have hle := decidedDensity_le_genuineDensity (O := O) n σ
  rw [hg] at hle
  exact le_antisymm hle (decidedDensity_nonneg n σ)

end NonOccurring

/-! ## CN-06 : off-degree types have density `0` -/

section OffDegree

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **CN-06.** `typeOf_degree` forces every monic degree-`n` polynomial's type to have degree
`n`; if `σ.degree ≠ n` no such polynomial can have type `σ`, so CN-05 applies. This is the
clause that makes the capstone's `σ.degree = n` hypothesis do real work
(`Statement.lean:59`). -/
theorem genuineDensity_eq_zero_of_degree_ne {n : ℕ} {σ : FactorizationType}
    (h : σ.degree ≠ n) : genuineDensity O n σ = 0 := by
  refine genuineDensity_eq_zero_of_forall_ne (fun a hσ => h ?_)
  rw [← hσ, typeOf_degree (monicPoly_monic a), monicPoly_natDegree]

end OffDegree

/-! ## CN-07 / CN-08 : the certificate/census interface, general `n` -/

section CertInterface

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-- **CN-07.** Two coefficient vectors have the same level-`N` class iff they are congruent mod
`π ^ N` in every coordinate. Generalizes the one-directional `Drainage.lean:639
congAt_of_proj_eq` (`n = 2` only) to an iff at every `n`; every certificate→census translation
at every degree factors through this. -/
theorem proj_eq_iff_dvd (hπ : Irreducible π) {n N : ℕ} (a b : Fin n → O) :
    proj O n N a = proj O n N b ↔ ∀ i, π ^ N ∣ (b i - a i) := by
  constructor
  · intro h i
    have hi := congrFun h i
    rw [proj, proj, Ideal.Quotient.eq] at hi
    exact dvd_sub_comm.1 ((mem_maximalIdeal_pow_iff_dvd hπ N _).1 hi)
  · intro h
    funext i
    rw [proj, proj, Ideal.Quotient.eq]
    exact (mem_maximalIdeal_pow_iff_dvd hπ N _).2 (dvd_sub_comm.1 (h i))

/-- **CN-08.** A certificate on the coefficients of `a` that is invariant under congruence mod
`π ^ N` — i.e. forces the same type `σ` on every congruent `b` — decides the level-`N` class of
`a`. The single interface between "certificate is congruence-invariant" and `decidedSet`
membership, at every `n`. -/
theorem decidedAt_of_congr (hπ : Irreducible π) {n N : ℕ} {σ : FactorizationType}
    {a : Fin n → O}
    (h : ∀ b : Fin n → O, (∀ i, π ^ N ∣ (b i - a i)) → typeOf (monicPoly b) = σ) :
    DecidedAt O n σ N (proj O n N a) := by
  intro b hb
  exact h b ((proj_eq_iff_dvd hπ a b).1 hb.symm)

end CertInterface

end Uniformity.Density
