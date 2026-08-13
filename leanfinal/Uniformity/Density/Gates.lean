/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Statement

/-!
# Uniformity.Density.Gates — machine-checked gates on the genuine density

The verification target of Part 1: **do the definitions compute the densities we expect?**

* **G1 (`n = 1`, EXACT).** Every monic linear polynomial has type `⟨{(1,1)}⟩`, so every class at
  every level is decided and `genuineDensity O 1 ⟨{(1,1)}⟩ = 1` — exactly, over every complete
  DVR with finite residue field (`genuineDensity_linear_eq_one`). Every other type has density
  exactly `0` (`genuineDensity_one_of_ne`), so `n = 1` also gives an **exact σ-separation**
  (`gate_sigma_separation_one`).
* **G2 (`n = 2`, algebraic half).** A monic quadratic that splits into two monic linear factors
  has type `⟨{(1,1),(1,1)}⟩` (`typeOf_mul_linear`).
* **G3 (`n = 2`, LOWER BOUND, every `O`).** Hensel's lemma at a simple residue root shows the
  level-1 class `(a₀, a₁) ≡ (0, 1)` is split-decided, so
  `1 / q ^ 2 ≤ genuineDensity O 2 splitType` (`gate_split_lower`). At `q = 2` this reads
  `1/4 ≤ density(split)`; the W-11 corpus value is `q/(2(q+1)) = 1/3`. ✓ consistent.
* **G4 (`n = 2`, σ-separation).** The degree-1 type has density `0` at degree `2`
  (`genuineDensity_two_linType_eq_zero`), while split has density `≥ 1/q² > 0`; so the density
  genuinely depends on σ at `n = 2` as well (`gate_sigma_separation_two`).

Everything here is proved for an ARBITRARY complete DVR with finite residue field — the gates
are not `ℤ_[2]`-only. `gate_padic_two` instantiates G3 at `ℤ_[2]` for the concrete number.

**What is NOT here** (honest scope, see `notes/GENUINE_DENSITY_2026-08-13.md` §STATUS):
exact `n = 2` values, the inert/ramified lower bounds, and the matching upper bounds. Those
need the full order-0 census (all `q-1` split classes at level 1, plus Eisenstein and
irreducible-reduction certificates) — stated in the note as open targets.
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial Filter Topology

/-! ## 0. The named types -/

/-- The degree-1 type `{(1,1)}`: one unramified linear factor. -/
def linType : FactorizationType := ⟨{(1, 1)}⟩

/-- The degree-2 SPLIT type `{(1,1),(1,1)}`: two unramified linear factors. -/
def splitType : FactorizationType := ⟨{(1, 1), (1, 1)}⟩

/-- The degree-2 INERT type `{(1,2)}`: one unramified quadratic factor. -/
def inertType : FactorizationType := ⟨{(1, 2)}⟩

/-- The degree-2 RAMIFIED type `{(2,1)}`: one totally ramified quadratic factor. -/
def ramType : FactorizationType := ⟨{(2, 1)}⟩

theorem linType_degree : linType.degree = 1 := by simp [linType, FactorizationType.degree]
theorem splitType_degree : splitType.degree = 2 := by
  simp [splitType, FactorizationType.degree]
theorem inertType_degree : inertType.degree = 2 := by
  simp [inertType, FactorizationType.degree]
theorem ramType_degree : ramType.degree = 2 := by simp [ramType, FactorizationType.degree]

theorem splitType_ne_linType : splitType ≠ linType := by
  intro h
  have := congrArg (fun σ => Multiset.card σ.data) h
  simp [splitType, linType] at this

/-! ## 1. G1 — degree 1, exact -/

section DegreeOne

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Every monic degree-1 polynomial over `O` has type `linType`. -/
theorem typeOf_monicPoly_one (a : Fin 1 → O) : typeOf (monicPoly a) = linType :=
  typeOf_of_natDegree_one (monicPoly_monic a) (monicPoly_natDegree a)

theorem decidedSet_one (N : ℕ) : decidedSet O 1 linType N = Set.univ := by
  ext c
  simp only [Set.mem_univ, iff_true]
  intro a _
  exact typeOf_monicPoly_one a

theorem decidedCount_one (N : ℕ) : decidedCount O 1 linType N = residueCard O ^ (1 * N) := by
  rw [decidedCount, decidedSet_one, Nat.card_congr (Equiv.Set.univ (Coeff O 1 N)), card_coeff]

theorem decidedSeq_one (N : ℕ) : decidedSeq O 1 linType N = 1 := by
  rw [decidedSeq, decidedCount_one, div_eq_one_iff_eq (qpow_ne _)]
  push_cast
  ring

/-- **G1 (exact).** The density of monic *linear* polynomials of the (unique possible) type
`{(1,1)}` is exactly `1`, over every complete DVR with finite residue field. -/
theorem genuineDensity_linear_eq_one : genuineDensity O 1 linType = 1 := by
  rw [genuineDensity]
  simp [decidedSeq_one]

/-- **G1 (exact, complement).** Every other type has density exactly `0` at degree 1. -/
theorem genuineDensity_one_of_ne {σ : FactorizationType} (hσ : σ ≠ linType) :
    genuineDensity O 1 σ = 0 := by
  have hempty : ∀ N, decidedSet O 1 σ N = ∅ := by
    intro N
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hc
    obtain ⟨a, ha⟩ := proj_surjective O 1 N c
    exact hσ (((hc a ha).symm.trans (typeOf_monicPoly_one a)))
  have hzero : ∀ N, decidedSeq O 1 σ N = 0 := by
    intro N
    rw [decidedSeq, decidedCount, hempty N]
    simp
  rw [genuineDensity]
  simp [hzero]

/-- **G1 σ-separation (exact).** Two distinct degree-≤1 types get *different* densities: the
definition is genuinely σ-dependent, not a σ-discarding constant. -/
theorem gate_sigma_separation_one :
    genuineDensity O 1 linType ≠ genuineDensity O 1 splitType := by
  rw [genuineDensity_linear_eq_one, genuineDensity_one_of_ne splitType_ne_linType]
  norm_num

end DegreeOne

/-! ## 2. G2 — the split type of a product of two monic linear factors -/

section Split

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **G2.** A monic quadratic that factors into two monic linear factors has type
`{(1,1),(1,1)}` — the SPLIT type. -/
theorem typeOf_mul_linear (r s : O) : typeOf ((X - C r) * (X - C s)) = splitType := by
  have hr : (X - C r : Polynomial O).Monic := monic_X_sub_C r
  have hs : (X - C s : Polynomial O).Monic := monic_X_sub_C s
  have hrd : (X - C r : Polynomial O).natDegree = 1 := natDegree_X_sub_C r
  have hsd : (X - C s : Polynomial O).natDegree = 1 := natDegree_X_sub_C s
  have hF : IsMonicFactorization ((X - C r) * (X - C s)) {X - C r, X - C s} := by
    refine ⟨?_, by simp⟩
    intro g hg
    rcases Multiset.mem_cons.1 hg with rfl | hg
    · exact ⟨hr, irreducible_of_monic_natDegree_one hr hrd⟩
    · rw [Multiset.mem_singleton.1 hg]
      exact ⟨hs, irreducible_of_monic_natDegree_one hs hsd⟩
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [splitType, efPair_of_natDegree_one hr hrd, efPair_of_natDegree_one hs hsd]

end Split

/-! ## 3. G3 — the `n = 2` lower bound, by Hensel at a simple residue root -/

section SplitLower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

theorem monicPoly_two_expand (a : Fin 2 → O) :
    monicPoly a = X ^ 2 + C (a 1) * X + C (a 0) := by
  simp only [monicPoly, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one]
  ring

theorem monicPoly_two_eval (a : Fin 2 → O) (x : O) :
    (monicPoly a).eval x = x ^ 2 + a 0 + a 1 * x := by
  rw [monicPoly_two_expand]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
  ring

theorem monicPoly_two_deriv_eval (a : Fin 2 → O) (x : O) :
    ((monicPoly a).derivative).eval x = 2 * x + a 1 := by
  rw [monicPoly_two_expand]
  simp only [derivative_add, derivative_pow, derivative_X, derivative_C, derivative_mul,
    eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_zero, eval_one]
  ring

/-- **Hensel's split certificate.** If `a₀ ∈ 𝔪` and `a₁` is a unit, the monic quadratic
`X² + a₁X + a₀` has a root `r ≡ 0 (mod 𝔪)`, hence factors into two monic linear factors, hence
has the SPLIT type. (Only one Hensel lift is needed: the second root is `-a₁ - r`.) -/
theorem typeOf_split_of_unit (a : Fin 2 → O) (h0 : a 0 ∈ maximalIdeal O) (h1 : IsUnit (a 1)) :
    typeOf (monicPoly a) = splitType := by
  obtain ⟨r, hr, -⟩ :=
    HenselianLocalRing.is_henselian (monicPoly a) (monicPoly_monic a) 0
      (by rw [monicPoly_two_eval]; simpa using h0)
      (by rw [monicPoly_two_deriv_eval]; simpa using h1)
  have hroot : r ^ 2 + a 0 + a 1 * r = 0 := by
    have := hr
    rwa [IsRoot, monicPoly_two_eval] at this
  have ha0 : a 0 = -(r ^ 2) - a 1 * r := by linear_combination hroot
  have hfac : monicPoly a = (X - C r) * (X - C (-(a 1) - r)) := by
    rw [monicPoly_two_expand, ha0]
    simp only [map_sub, map_neg, map_mul, map_pow]
    ring
  rw [hfac]
  exact typeOf_mul_linear r _

/-- The level-1 class `(a₀, a₁) ≡ (0, 1)` is SPLIT-decided: every lift has `a₀ ∈ 𝔪` and `a₁` a
unit, so `typeOf_split_of_unit` applies. -/
theorem split_decided_class :
    DecidedAt O 2 splitType 1 (proj O 2 1 ![0, 1]) := by
  intro b hb
  have hb0 : b 0 - (0 : O) ∈ (maximalIdeal O) ^ 1 := by
    have := congrFun hb 0
    rwa [proj, proj, Ideal.Quotient.eq] at this
  have hb1 : b 1 - (1 : O) ∈ (maximalIdeal O) ^ 1 := by
    have := congrFun hb 1
    rwa [proj, proj, Ideal.Quotient.eq] at this
  rw [pow_one] at hb0 hb1
  refine typeOf_split_of_unit b (by simpa using hb0) ?_
  by_contra hu
  have hmem : b 1 ∈ maximalIdeal O := mem_maximalIdeal _ |>.2 (mem_nonunits_iff.2 hu)
  have hone : (1 : O) ∈ maximalIdeal O := by
    have h := Ideal.sub_mem _ hmem hb1
    simpa using h
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hone)

/-- **G3 (lower bound, every `O`).** `1 / q ^ 2 ≤ genuineDensity O 2 splitType`. At `q = 2` this
is `1/4`; the W-11 corpus value of the split density is `q / (2(q+1)) = 1/3`. -/
theorem gate_split_lower :
    1 / (residueCard O : ℝ) ^ 2 ≤ genuineDensity O 2 splitType := by
  have hne : (decidedSet O 2 splitType 1).Nonempty := ⟨_, split_decided_class⟩
  have hpos : 0 < decidedCount O 2 splitType 1 := by
    rw [decidedCount]
    have : Nonempty (decidedSet O 2 splitType 1) := hne.to_subtype
    exact Nat.card_pos
  have hA : (1 : ℝ) ≤ (decidedCount O 2 splitType 1 : ℝ) := by exact_mod_cast hpos
  have hc : (0 : ℝ) < (residueCard O : ℝ) ^ 2 := qpow_pos (O := O) 2
  have h1 : 1 / (residueCard O : ℝ) ^ 2 ≤ decidedSeq O 2 splitType 1 := by
    rw [decidedSeq, show (2 : ℕ) * 1 = 2 from rfl, div_le_div_iff₀ hc hc]
    nlinarith [hA, hc]
  exact h1.trans (decidedSeq_le_genuineDensity 2 splitType 1)

/-- The `ℤ_[2]` instance of G3: the split density at the wild prime is at least `1/4`
(W-11's exact value there is `1/3`). -/
theorem gate_padic_two : 1 / (2 : ℝ) ^ 2 ≤ genuineDensity ℤ_[2] 2 splitType := by
  have := gate_split_lower (O := ℤ_[2])
  rwa [residueCard_padicInt 2] at this

end SplitLower

/-! ## 4. G4 — σ-separation at `n = 2` -/

section SepTwo

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- No monic *quadratic* has the degree-1 type `{(1,1)}`: a single irreducible factor of a
monic quadratic has degree 2, and its `(e,f)` pair is `(2/m, m)` with `1 ≤ m ≤ 2`
(`m = inertiaDegOf ≤ deg = 2` because `2 ∈ normValues`), never `(1,1)`. -/
theorem typeOf_monicPoly_two_ne_linType (a : Fin 2 → O) : typeOf (monicPoly a) ≠ linType := by
  intro h
  have hmonic := monicPoly_monic a
  have hdeg := monicPoly_natDegree a
  have hdata : (monicFactors (monicPoly a)).map efPair = {(1, 1)} := congrArg (·.data) h
  have hcard : Multiset.card (monicFactors (monicPoly a)) = 1 := by
    have := congrArg Multiset.card hdata
    simpa using this
  obtain ⟨g, hg⟩ := Multiset.card_eq_one.1 hcard
  have hspec := monicFactors_spec hmonic
  rw [hg] at hspec hdata
  have hgf : g = monicPoly a := by simpa using hspec.2
  have hgd : g.natDegree = 2 := by rw [hgf, hdeg]
  have hef : efPair g = (1, 1) := by simpa using hdata
  -- `inertiaDegOf g ≤ 2` since `2 = deg g ∈ normValues g`
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmem : g.natDegree ∈ normValues g :=
    natDegree_mem_normValues (hgf ▸ hmonic) (by omega) hπ
  have hle : inertiaDegOf g ≤ 2 := by
    rw [inertiaDegOf, ← hgd]; exact Nat.sInf_le hmem
  have hne : (normValues g).Nonempty := ⟨g.natDegree, hmem⟩
  have hpos : 0 < inertiaDegOf g := (Nat.sInf_mem hne).1
  have h2 : inertiaDegOf g = 1 := (Prod.mk.injEq _ _ _ _ ▸ hef).2
  have h1 : ramIndexOf g = 1 := (Prod.mk.injEq _ _ _ _ ▸ hef).1
  rw [ramIndexOf, hgd, h2] at h1
  omega

/-- The degree-1 type has density exactly `0` among monic quadratics. -/
theorem genuineDensity_two_linType_eq_zero : genuineDensity O 2 linType = 0 := by
  have hempty : ∀ N, decidedSet O 2 linType N = ∅ := by
    intro N
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hc
    obtain ⟨a, ha⟩ := proj_surjective O 2 N c
    exact typeOf_monicPoly_two_ne_linType a (hc a ha)
  have hzero : ∀ N, decidedSeq O 2 linType N = 0 := by
    intro N
    rw [decidedSeq, decidedCount, hempty N]
    simp
  rw [genuineDensity]
  simp [hzero]

/-- **G4 (σ-separation at `n = 2`).** At degree 2 the split type has strictly positive density
while the degree-1 type has density `0`: the density is genuinely σ-keyed at `n = 2`. -/
theorem gate_sigma_separation_two :
    genuineDensity O 2 linType < genuineDensity O 2 splitType := by
  rw [genuineDensity_two_linType_eq_zero]
  exact lt_of_lt_of_le (one_div_pos.2 (qpow_pos (O := O) 2)) (gate_split_lower (O := O))

end SepTwo

section AxCheck

-- Every gate must be Lean core ONLY (`propext`, `Classical.choice`, `Quot.sound`).
#print axioms Uniformity.Density.genuineDensity_linear_eq_one
#print axioms Uniformity.Density.genuineDensity_one_of_ne
#print axioms Uniformity.Density.gate_sigma_separation_one
#print axioms Uniformity.Density.typeOf_mul_linear
#print axioms Uniformity.Density.typeOf_split_of_unit
#print axioms Uniformity.Density.gate_split_lower
#print axioms Uniformity.Density.gate_padic_two
#print axioms Uniformity.Density.genuineDensity_two_linType_eq_zero
#print axioms Uniformity.Density.gate_sigma_separation_two
#print axioms Uniformity.Density.decidedSeq_tendsto
#print axioms Uniformity.Density.possibleSeq_tendsto
#print axioms Uniformity.Density.upperDensity_eq_of_drainage
#print axioms Uniformity.Density.genuineDensity_le_upperDensity
#print axioms Uniformity.Density.sum_genuineDensity_le_one
#print axioms Uniformity.Density.card_res
#print axioms Uniformity.Density.UniformityStatement.toPadic

end AxCheck

end Uniformity.Density
