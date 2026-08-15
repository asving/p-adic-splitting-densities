/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G59
import Uniformity.ChapG.G61I

/-!
# Uniformity.ChapG.G61d — the linear × ramified bound `(q−1)²/q⁴ ≤ decidedDensity O 3 c3linRam`

**Chapter G, NODE G.61d** (`blueprint/CHAP-G_base_cases_menus.md` §9), the fourth of the five
SPLIT-MANDATED sub-nodes of G.61: the family `{(1,1),(2,1)}` — a linear factor times an Eisenstein
quadratic.

A **level-2** family. The certificate "`a₂` a unit, `a₁ ∈ 𝔪`, `a₀` of exact valuation `1`" is
visible at window `2`, so it cuts out `exactSet π 1 2 × dvdSet π 1 2 × unitSet π 2`, of size
`(q−1)·q·(q²−q)`, whence `(q−1)²q²/q⁶ = (q−1)²/q⁴`.

DEPENDS: G.59 (`typeOf_linRam_of_residue`), G.61.0 (`decidedDensity_ge_of_inj`, `unitSet`,
`dvd_of_mem_dvdSet`, `mem_dvdSet_of_dvd`, `card_dvdSet_two`, `card_exactSet_two`,
`card_unitSet_two`) · landed `mem_maximalIdeal_iff_dvd`, `mem_maximalIdeal_pow_iff_dvd`
(`Drainage.lean`), `notMem_maximalIdeal`, `two_le_residueCard`, `qR_pos`.

PROOF sketch. The three strata are read off the lift `b` of `![x, y, z]`: `b 0 ∈ 𝔪 \ 𝔪²` from `x`
(both directions of the `dvdSet` bridge), `b 1 ∈ 𝔪` from `y`, and `IsUnit (b 2)` from `z` (if
`b 2 ∈ 𝔪` then `π ∣ b 2`, putting `z.1` back into `dvdSet π 1 2`). G.59 then fires. The map into
`Coeff O 3 2` is injective coordinatewise, so `decidedDensity_ge_of_inj` applies with
`#A = (q−1)·q·(q²−q)`.

⚠ RE-DERIVATION TARGET (blueprint H-9): `leancheck/UniformityCheck/N3Density.lean`
(`linRam_decided`, `gate_linRam_lower`) lands the same content; re-derived here against
`leanfinal`'s own G.59 certificate and G.61.0's stratum bridges (`leancheck` routes the same
readings through its own `dvd_res_iff`/`resPi`, which have no `leanfinal` counterpart).

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

/-- **LINEAR × RAMIFIED QUADRATIC, level 2.** Every class with `a₂` a unit, `a₁ ∈ 𝔪` and `a₀` of
exact valuation `1` is `{(1,1),(2,1)}`-decided at window `2`. -/
theorem linRam_decided [IsAdicComplete (maximalIdeal O) O] (hπ : Irreducible π)
    (x : exactSet π 1 2) (y : dvdSet π 1 2) (z : unitSet π 2) :
    DecidedAt O 3 c3linRam 2 (![x.1, y.1, z.1] : Coeff O 3 2) := by
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
  have h0' : b 0 ∉ (maximalIdeal O) ^ 2 := by
    intro hmem
    refine x.2.2 ?_
    rw [← hb0]
    exact mem_dvdSet_of_dvd (k := 2) ((mem_maximalIdeal_pow_iff_dvd hπ 2 _).1 hmem)
  have h2 : IsUnit (b 2) := by
    refine notMem_maximalIdeal.1 (fun hmem => z.2 ?_)
    rw [← hb2]
    exact mem_dvdSet_of_dvd (k := 1)
      (by simpa using (mem_maximalIdeal_iff_dvd hπ _).1 hmem)
  exact typeOf_linRam_of_residue h2 h1 h0 h0'

/-! ## 2. The gate -/

/-- **G.61d.** `(q − 1)² / q⁴ ≤ decidedDensity O 3 c3linRam`, every `O`. A LOWER BOUND, not the
density. -/
theorem gate_linRam3_lower [IsAdicComplete (maximalIdeal O) O] :
    ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 4 ≤ decidedDensity O 3 c3linRam := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hbound := decidedDensity_ge_of_inj (O := O) (n := 3) (N := 2) (σ := c3linRam)
    (A := (exactSet π 1 2) × (dvdSet π 1 2) × (unitSet π 2))
    (fun p => ![p.1.1, p.2.1.1, p.2.2.1])
    (by
      rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
      exact Prod.ext (Subtype.ext h0) (Prod.ext (Subtype.ext h1) (Subtype.ext h2)))
    (fun p => linRam_decided hπ p.1 p.2.1 p.2.2)
  have he := card_exactSet_two (O := O) hπ
  have hd := card_dvdSet_two (O := O) hπ
  have hu := card_unitSet_two (O := O) hπ
  have hq2 : (2 : ℕ) ≤ residueCard O := two_le_residueCard O
  have hcards : Nat.card ((exactSet π 1 2) × (dvdSet π 1 2) × (unitSet π 2))
      = Nat.card (exactSet π 1 2) * (Nat.card (dvdSet π 1 2) * Nat.card (unitSet π 2)) := by
    rw [Nat.card_prod, Nat.card_prod]
  have hE : Nat.card (exactSet π 1 2) = residueCard O - 1 := by omega
  have hU : Nat.card (unitSet π 2) = residueCard O ^ 2 - residueCard O := by omega
  have hq1 : (1 : ℕ) ≤ residueCard O := by omega
  have hqq : residueCard O ≤ residueCard O ^ 2 := Nat.le_self_pow (by norm_num) _
  have hcast : (Nat.card ((exactSet π 1 2) × (dvdSet π 1 2) × (unitSet π 2)) : ℝ)
      = ((residueCard O : ℝ) - 1) ^ 2 * (residueCard O : ℝ) ^ 2 := by
    rw [hcards, hd, hE, hU]
    push_cast [Nat.cast_sub hq1, Nat.cast_sub hqq]
    ring
  rw [hcast] at hbound
  refine le_trans (le_of_eq ?_) hbound
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  rw [show (3 : ℕ) * 2 = 6 from rfl]
  field_simp

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.linRam_decided
#print axioms Uniformity.Density.gate_linRam3_lower

end AxCheck
