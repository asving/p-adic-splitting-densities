/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G58
import Uniformity.ChapG.G61I

/-!
# Uniformity.ChapG.G61e — the ramified lower bound `(q−1)/q⁴ ≤ decidedDensity O 3 c3ram`

**Chapter G, NODE G.61e** (`blueprint/CHAP-G_base_cases_menus.md` §9), the fifth of the five
SPLIT-MANDATED sub-nodes of G.61: the totally ramified family `{(3,1)}`.

A **level-2** family. The Eisenstein condition "`a₀` of exact valuation `1`, `a₁` and `a₂` in `𝔪`"
is visible at window `2`, so it cuts out a product of level-2 valuation strata:
`exactSet π 1 2 × dvdSet π 1 2 × dvdSet π 1 2`, of size `(q−1)·q·q`, whence
`(q−1)q²/q⁶ = (q−1)/q⁴`.

DEPENDS: G.58 (`typeOf_ram3_of_eisenstein`), G.61.0 (`decidedDensity_ge_of_inj`,
`dvd_of_mem_dvdSet`, `mem_dvdSet_of_dvd`, `card_dvdSet_two`, `card_exactSet_two`) · landed
`mem_maximalIdeal_iff_dvd`, `mem_maximalIdeal_pow_iff_dvd` (`Drainage.lean`), `two_le_residueCard`,
`qR_pos`.

PROOF sketch. For `x` of exact valuation `1` and `y, z` divisible by `π`, every lift `b` of
`![x, y, z]` has `b 0 ∈ 𝔪 \ 𝔪²` and `b 1, b 2 ∈ 𝔪` (read off `dvd_of_mem_dvdSet` in one direction
and `mem_dvdSet_of_dvd` in the other), so G.58 fires. The three coordinates are recovered from the
vector, so the map into `Coeff O 3 2` is injective, and `decidedDensity_ge_of_inj` applies with
`#A = (q−1)·q·q`.

⚠ RE-DERIVATION TARGET (blueprint H-9): `leancheck/UniformityCheck/N3Gates.lean`
(`ram3_decided`) and `N3Density.lean` (`gate_ram3_lower`) land the same content; re-derived here
against `leanfinal`'s own G.58 certificate (whose hypothesis shape — `∀ i, a i ∈ 𝔪` plus
`a 0 ∉ 𝔪²` — differs from `leancheck`'s four separate hypotheses).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-! ## 1. The level-2 certificate -/

/-- **EISENSTEIN CUBIC, level 2.** Every class with `a₀` of exact valuation `1` and `a₁, a₂`
divisible by `π` is `{(3,1)}`-decided at window `2`. -/
theorem ram3_decided (hπ : Irreducible π) (x : exactSet π 1 2) (y z : dvdSet π 1 2) :
    DecidedAt O 3 c3ram 2 (![x.1, y.1, z.1] : Coeff O 3 2) := by
  intro b hb
  have hb0 : (Ideal.Quotient.mk _ (b 0) : Res O 2) = x.1 := congrFun hb 0
  have hb1 : (Ideal.Quotient.mk _ (b 1) : Res O 2) = y.1 := congrFun hb 1
  have hb2 : (Ideal.Quotient.mk _ (b 2) : Res O 2) = z.1 := congrFun hb 2
  have h0 : b 0 ∈ maximalIdeal O := by
    refine (mem_maximalIdeal_iff_dvd hπ _).2 ?_
    have h := dvd_of_mem_dvdSet hπ (k := 1) (N := 2) (by omega) (a := b 0)
      (by rw [hb0]; exact x.2.1)
    simpa using h
  have h1 : b 1 ∈ maximalIdeal O := by
    refine (mem_maximalIdeal_iff_dvd hπ _).2 ?_
    have h := dvd_of_mem_dvdSet hπ (k := 1) (N := 2) (by omega) (a := b 1)
      (by rw [hb1]; exact y.2)
    simpa using h
  have h2 : b 2 ∈ maximalIdeal O := by
    refine (mem_maximalIdeal_iff_dvd hπ _).2 ?_
    have h := dvd_of_mem_dvdSet hπ (k := 1) (N := 2) (by omega) (a := b 2)
      (by rw [hb2]; exact z.2)
    simpa using h
  have h0' : b 0 ∉ (maximalIdeal O) ^ 2 := by
    intro hmem
    refine x.2.2 ?_
    rw [← hb0]
    exact mem_dvdSet_of_dvd (k := 2) ((mem_maximalIdeal_pow_iff_dvd hπ 2 _).1 hmem)
  refine typeOf_ram3_of_eisenstein (fun i => ?_) h0'
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-! ## 2. The gate -/

/-- **G.61e.** `(q − 1) / q⁴ ≤ decidedDensity O 3 c3ram`, every `O`. A LOWER BOUND, not the
density. -/
theorem gate_ram3_lower [IsAdicComplete (maximalIdeal O) O] :
    ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4 ≤ decidedDensity O 3 c3ram := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hbound := decidedDensity_ge_of_inj (O := O) (n := 3) (N := 2) (σ := c3ram)
    (A := (exactSet π 1 2) × (dvdSet π 1 2) × (dvdSet π 1 2))
    (fun p => ![p.1.1, p.2.1.1, p.2.2.1])
    (by
      rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
      exact Prod.ext (Subtype.ext h0) (Prod.ext (Subtype.ext h1) (Subtype.ext h2)))
    (fun p => ram3_decided hπ p.1 p.2.1 p.2.2)
  have he := card_exactSet_two (O := O) hπ
  have hd := card_dvdSet_two (O := O) hπ
  have hq2 : (2 : ℕ) ≤ residueCard O := two_le_residueCard O
  have hcards : Nat.card ((exactSet π 1 2) × (dvdSet π 1 2) × (dvdSet π 1 2))
      = Nat.card (exactSet π 1 2) * (Nat.card (dvdSet π 1 2) * Nat.card (dvdSet π 1 2)) := by
    rw [Nat.card_prod, Nat.card_prod]
  have hE : Nat.card (exactSet π 1 2) = residueCard O - 1 := by omega
  have hq1 : (1 : ℕ) ≤ residueCard O := by omega
  have hcast : (Nat.card ((exactSet π 1 2) × (dvdSet π 1 2) × (dvdSet π 1 2)) : ℝ)
      = ((residueCard O : ℝ) - 1) * (residueCard O : ℝ) ^ 2 := by
    rw [hcards, hd, hE]
    push_cast [Nat.cast_sub hq1]
    ring
  rw [hcast] at hbound
  refine le_trans (le_of_eq ?_) hbound
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  rw [show (3 : ℕ) * 2 = 6 from rfl]
  field_simp

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.ram3_decided
#print axioms Uniformity.Density.gate_ram3_lower

end AxCheck
