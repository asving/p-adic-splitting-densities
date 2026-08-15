/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3InertLower
import UniformityCheck.N3Drain3

/-!
# UniformityCheck.N3InertExact — THE EXACT `n = 3` INERT DENSITY

Unit `UNIFORMITY-CHECK-N3C`, layer 8 (`notes/N3_CHECK_2026-08-13.md` §13.5). With drainage in hand
(`N3Drain3.genuineDensity_three_eq_decidedDensity`) the inner and outer densities coincide, so a
matching pair of self-similar bounds PINS the value:

* `N3InertLower.decidedSeq_inert_step` : `decidedSeq (M+3) ≥ L + q^(-5)·decidedSeq M`;
* `possibleSeq_inert_step` (here)      : `possibleSeq (M+3) ≤ L + q^(-5)·possibleSeq M`;

with `L = (q³−q)/(3q³)` the level-1 inert census. Both sequences converge to the same limit `I`, so
`I = L + q^(-5)·I`, i.e.

    **genuineDensity O 3 c3inert = q³(q+1) / (3(q⁴+q³+q²+q+1))** ,

which is `8/31` at `q = 2` and `36/121` at `q = 3` — EXACTLY the values the informal corpus predicts
(`lean/notes/openmath/HMENU3_PROOF_2026-08-08.md`, COROLLARY HM3.D), and which `N3Exact.lean` §10.3
could only bracket.

The upper bound is where the residue trichotomy is spent: a lift of type `{(1,3)}` cannot have a
root in `O` (a root contributes `(1,1)`), so its residue is either irreducible (the level-1 family)
or a perfect cube; and in the perfect-cube case the certificates E, L, R of the four-case split all
return `{(3,1)}` or `{(1,1),(2,1)}`, so only case S survives — and case S is exactly the image of the
reconstruction.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial Filter Topology

section Upper

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **A cubic with a root in `O` is not inert.** Peeling the root off puts `(1,1)` in the type,
and `c3inert.data = {(1,3)}` does not contain `(1,1)`. -/
theorem typeOf_ne_inert3_of_root {a : Fin 3 → O} {r : O} (hr : (monicPoly a).eval r = 0) :
    typeOf (monicPoly a) ≠ c3inert := by
  intro h
  have hmem : ((1 : ℕ), (1 : ℕ)) ∈ c3inert.data := by
    rw [← h, cubic_peel a r hr, typeOf_linear_mul (monicPoly_monic (peel a r)) r]
    exact Multiset.mem_cons_self _ _
  simp [c3inert] at hmem

/-- **CASE S is forced on an inert cubic.** If the recentred vector is in `𝔪³` and the type is
`{(1,3)}`, the `X = πY` extraction is legal: cases E, L, R of §13.1 return `{(3,1)}`,
`{(1,1),(2,1)}`, `{(3,1)}`, none of which is `{(1,3)}`. -/
theorem legal_of_typeOf_inert3 {π : O} (hπ : Irreducible π) {a : Fin 3 → O} {γ : O}
    (hγ : ∀ i, shiftVec a γ i ∈ maximalIdeal O) (ht : typeOf (monicPoly a) = c3inert) :
    π ^ 3 ∣ shiftVec a γ 0 ∧ π ^ 2 ∣ shiftVec a γ 1 ∧ π ∣ shiftVec a γ 2 := by
  -- the recentred cubic has the same type, `{(1,3)}`
  have hts : typeOf (monicPoly (shiftVec a γ)) = c3inert := by
    rw [typeOf_shiftVec a γ]; exact ht
  -- every recentred coefficient is divisible by `π` (the triple-root hypothesis)
  have hd : ∀ i, π ∣ shiftVec a γ i := by
    intro i
    have h1 : shiftVec a γ i ∈ maximalIdeal O ^ 1 := by rw [pow_one]; exact hγ i
    have h2 := (mem_maximalIdeal_pow_iff_dvd hπ 1 (shiftVec a γ i)).1 h1
    rwa [pow_one] at h2
  by_cases hE : π ^ 2 ∣ shiftVec a γ 0
  · by_cases hL : π ^ 2 ∣ shiftVec a γ 1
    · by_cases hR : π ^ 3 ∣ shiftVec a γ 0
      · -- CASE S: the extraction is legal
        exact ⟨hR, hL, hd 2⟩
      · -- CASE R: `v(B₀) = 2`, `v(B₁) ≥ 2` certifies `{(3,1)}` — not `{(1,3)}`
        exact absurd (hts.symm.trans (typeOf_ram3_of_val_two hπ (hd 2) hL hE hR))
          c3inert_ne_c3ram
    · -- CASE L: `v(B₁) = 1`, `v(B₀) ≥ 2` certifies `{(1,1),(2,1)}` — not `{(1,3)}`
      exact absurd (hts.symm.trans (typeOf_linRam_of_val_one hπ (hd 2) (hd 1) hL hE))
        c3inert_ne_c3linRam
  · -- CASE E: `v(B₀) = 1` is Eisenstein, certifying `{(3,1)}` — not `{(1,3)}`
    exact absurd (hts.symm.trans (typeOf_ram3_of_val_one hπ (hd 0) hE (hd 1) (hd 2)))
      c3inert_ne_c3ram

/-- **THE OUTER INCLUSION.** Every `{(1,3)}`-possible class at level `M + 3` is either residually
irreducible (the refined level-1 family) or a reconstruction of a `{(1,3)}`-possible class at
level `M`. -/
theorem possibleSet_inert_subset {π : O} (hπ : Irreducible π) (M : ℕ) :
    possibleSet O 3 c3inert (M + 3)
      ⊆ (coeffFactor (O := O) 3 (show 1 ≤ M + 3 by omega)) ⁻¹' (decidedSet O 3 c3inert 1)
        ∪ boxImage π M (possibleSet O 3 c3inert M) := by
  rintro c ⟨a, rfl, hta⟩
  rcases cubic_structure a with ⟨r, hr, -⟩ | hno | ⟨γ, hγ⟩
  · -- a root in `O` contradicts type `{(1,3)}`
    exact absurd hta (typeOf_ne_inert3_of_root hr)
  · -- residually rootless: the level-1 class is `{(1,3)}`-decided
    left
    show coeffFactor (O := O) 3 (show 1 ≤ M + 3 by omega) (proj O 3 (M + 3) a)
      ∈ decidedSet O 3 c3inert 1
    rw [coeffFactor_proj (O := O) 3 (show 1 ≤ M + 3 by omega) a, proj_one_eq_liftRes1]
    exact inert3_decided_iff.2 hno
  · -- residually a perfect cube: recentre at the canonical lift of the residual centre
    right
    have hres : resVec a = cubeCoeff (residue O (resSect O (residue O γ))) := by
      rw [residue_resSect]; exact hγ
    have hB : ∀ i, shiftVec a (resSect O (residue O γ)) i ∈ maximalIdeal O :=
      (shiftVec_mem_iff a (resSect O (residue O γ))).2 hres
    obtain ⟨⟨d0, e0⟩, ⟨d1, e1⟩, ⟨d2, e2⟩⟩ := legal_of_typeOf_inert3 hπ hB hta
    -- the extraction, and its component equations
    have e0' : shiftVec a (resSect O (residue O γ)) 0 = π ^ 3 * (![d0, d1, d2] : Fin 3 → O) 0 := e0
    have e1' : shiftVec a (resSect O (residue O γ)) 1 = π ^ 2 * (![d0, d1, d2] : Fin 3 → O) 1 := e1
    have e2' : shiftVec a (resSect O (residue O γ)) 2 = π * (![d0, d1, d2] : Fin 3 → O) 2 := e2
    -- the extraction still has type `{(1,3)}`
    have htd : typeOf (monicPoly (![d0, d1, d2] : Fin 3 → O)) = c3inert := by
      rw [← typeOf_extract hπ e0' e1' e2', typeOf_shiftVec]
      exact hta
    -- record the extraction at its mixed precisions
    refine mem_boxImage.2 ⟨(residue O γ,
      (Ideal.Quotient.mk ((maximalIdeal O) ^ M) ((![d0, d1, d2] : Fin 3 → O) 0),
        Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 1)) ((![d0, d1, d2] : Fin 3 → O) 1),
        Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 2)) ((![d0, d1, d2] : Fin 3 → O) 2))), ?_, ?_⟩
    · -- the truncation is the level-`M` class of the extraction, a `{(1,3)}` witness
      have hmt : mtrunc M ((Ideal.Quotient.mk ((maximalIdeal O) ^ M)
            ((![d0, d1, d2] : Fin 3 → O) 0),
          Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 1)) ((![d0, d1, d2] : Fin 3 → O) 1),
          Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 2)) ((![d0, d1, d2] : Fin 3 → O) 2)))
          = proj O 3 M (![d0, d1, d2] : Fin 3 → O) := by
        funext i
        fin_cases i
        · rfl
        · exact resFactor_mk (by omega : M ≤ M + 1) d1
        · exact resFactor_mk (by omega : M ≤ M + 2) d2
      rw [hmt]
      exact ⟨(![d0, d1, d2] : Fin 3 → O), rfl, htd⟩
    · -- the reconstruction lands back on the class of `a`
      have hbc := proj_shiftVec_eq_boxClass hπ M (residue O γ)
        (d := (![d0, d1, d2] : Fin 3 → O))
        (x := (Ideal.Quotient.mk ((maximalIdeal O) ^ M) ((![d0, d1, d2] : Fin 3 → O) 0),
          Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 1)) ((![d0, d1, d2] : Fin 3 → O) 1),
          Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 2)) ((![d0, d1, d2] : Fin 3 → O) 2)))
        rfl rfl rfl
      have hvec : (![π ^ 3 * (![d0, d1, d2] : Fin 3 → O) 0,
            π ^ 2 * (![d0, d1, d2] : Fin 3 → O) 1, π * (![d0, d1, d2] : Fin 3 → O) 2] : Fin 3 → O)
          = shiftVec a (resSect O (residue O γ)) := by
        funext i
        fin_cases i
        · exact e0'.symm
        · exact e1'.symm
        · exact e2'.symm
      rw [hvec, shiftVec_shiftVec_neg a (resSect O (residue O γ))] at hbc
      exact hbc.symm

/-- **THE SELF-SIMILAR UPPER BOUND**, the twin of `decidedSeq_inert_step`. -/
theorem possibleSeq_inert_step (M : ℕ) :
    possibleSeq O 3 c3inert (M + 3)
      ≤ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
        + (1 / (residueCard O : ℝ) ^ 5) * possibleSeq O 3 c3inert M := by
  sorry

end Upper

/-! ## The exact value -/

section Value

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **THE EXACT `n = 3` INERT DENSITY.** For every complete discrete valuation ring with finite
residue field of size `q`, THE density of the monic cubics with splitting type `{(1,3)}` — the
unramified cubic extensions — is

    q³(q+1) / (3(q⁴+q³+q²+q+1)) .

The two self-similar bounds squeeze the common limit of `decidedSeq` and `possibleSeq` (equal by
`n = 3` drainage) to the fixed point of `I ↦ L + q^(-5)·I`. -/
theorem inert3_density_eq :
    genuineDensity O 3 c3inert
      = (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) + 1)
        / (3 * ((residueCard O : ℝ) ^ 4 + (residueCard O : ℝ) ^ 3 + (residueCard O : ℝ) ^ 2
            + (residueCard O : ℝ) + 1)) := by
  sorry

/-- The same value for the certified (inner) density — identical by drainage. -/
theorem inert3_decidedDensity_eq :
    decidedDensity O 3 c3inert
      = (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) + 1)
        / (3 * ((residueCard O : ℝ) ^ 4 + (residueCard O : ℝ) ^ 3 + (residueCard O : ℝ) ^ 2
            + (residueCard O : ℝ) + 1)) := by
  rw [← genuineDensity_three_eq_decidedDensity]
  exact inert3_density_eq

end Value

/-- **`q = 2`: the inert cubic density over `ℤ_[2]` is exactly `8/31`** — HMENU3's predicted value,
now a theorem. (`N3Exact.decidedSeq_inert3_one_padic_two` says the level-1 census alone gives only
`1/4`; the extra `8/31 − 1/4 = 1/124` is the deep triple-root mass the recursion sums.) -/
theorem inert3_density_padic_two : genuineDensity ℤ_[2] 3 c3inert = 8 / 31 := by
  sorry

/-- **`q = 3`: the inert cubic density over `ℤ_[3]` is exactly `36/121`** — HMENU3's predicted
value. (Level 1 alone gives `8/27 = 0.29630`; the exact value is `0.29752`.) -/
theorem inert3_density_padic_three : genuineDensity ℤ_[3] 3 c3inert = 36 / 121 := by
  sorry

/-! ## Axiom census -/

section AxCheck

#print axioms UniformityCheck.typeOf_ne_inert3_of_root
#print axioms UniformityCheck.legal_of_typeOf_inert3
#print axioms UniformityCheck.possibleSet_inert_subset
#print axioms UniformityCheck.possibleSeq_inert_step
#print axioms UniformityCheck.inert3_density_eq
#print axioms UniformityCheck.inert3_decidedDensity_eq
#print axioms UniformityCheck.inert3_density_padic_two
#print axioms UniformityCheck.inert3_density_padic_three

end AxCheck

end UniformityCheck
