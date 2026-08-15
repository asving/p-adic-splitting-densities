/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G57
import Uniformity.ChapG.G60
import Uniformity.ChapG.G61I

/-!
# Uniformity.ChapG.G61c — the inert bound `(q³−q)/(3q³) ≤ decidedDensity O 3 c3inert`

**Chapter G, NODE G.61c** (`blueprint/CHAP-G_base_cases_menus.md` §9), the third of the five
SPLIT-MANDATED sub-nodes of G.61: the inert family `{(1,3)}`.

A **level-1** family, counted on the residue field. A class whose residue cubic has NO root in the
residue field is inert-decided: the reduced cubic is then irreducible (degree `3`, no root), and
G.57 lifts irreducibility of the reduction to inertness of the cubic. G.60a counts those residue
cubics subtraction-free (`3·#{no root} + q = q³`), so the family has `(q³−q)/3` level-1 classes and
the bound is `(q³−q)/(3q³)`.

DEPENDS: G.57 (`typeOf_inert3_of_irreducible_map`), G.60a (`three_mul_card_noRootCubic`,
`NoRootCubic`), G.61.0 (`decidedDensity_ge_of_inj`, `liftRes1`, `liftRes1_injective`,
`residue_comp_of_proj_liftRes1`) · mathlib
`Polynomial.irreducible_of_degree_le_three_of_not_isRoot`; landed `monicPoly_natDegree`, `qR_pos`.

PROOF sketch. `residue_comp_of_proj_liftRes1` says every lift `b` of `liftRes1 v` reduces
coefficientwise to `v`, so `(monicPoly b).map (residue O) = monicPoly v`; the latter has degree `3`
and, by `NoRootCubic v`, no root, hence is irreducible; G.57 gives type `c3inert`. Injectivity of
`liftRes1` then feeds `decidedDensity_ge_of_inj` with
`A := {v // NoRootCubic v}`, `#A = (q³−q)/3` in the subtraction-free form G.60a supplies.

⚠ RE-DERIVATION TARGET (blueprint H-9): `leancheck/UniformityCheck/N3Gates.lean`
(`inert3_decided`, `gate_inert3_lower`) lands the same content; re-derived here against
`leanfinal`'s own G.57 certificate (which asks for `Irreducible ((monicPoly a).map (residue O))`
directly, so no `cub3`/`resVec` layer is needed).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial Menu

/-! ## 1. Reduction of a monic polynomial, coefficientwise -/

section Reduce

/-- Reducing a monic polynomial along a ring hom reduces its coefficient vector. -/
private theorem g61c_map_monicPoly {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] (φ : R →+* S) {n : ℕ} (a : Fin n → R) :
    (monicPoly a).map φ = monicPoly (fun i => φ (a i)) := by
  simp only [monicPoly, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]

/-- The evaluation of a monic cubic, expanded. -/
private theorem g61c_cubic_eval {K : Type*} [CommRing K] [IsDomain K] (a : Fin 3 → K) (x : K) :
    (monicPoly a).eval x = x ^ 3 + a 2 * x ^ 2 + a 1 * x + a 0 := by
  have hexp : monicPoly a = X ^ 3 + C (a 2) * X ^ 2 + C (a 1) * X + C (a 0) := by
    simp only [monicPoly, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
      pow_one, mul_one]
    ring
  rw [hexp]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]

end Reduce

/-! ## 2. The level-1 certificate -/

section Cert

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **CUBIC INERT, level 1.** A class whose residue cubic has no root is `{(1,3)}`-decided. -/
theorem inert3_decided [IsAdicComplete (maximalIdeal O) O]
    {v : Fin 3 → ResidueField O} (hv : NoRootCubic v) :
    DecidedAt O 3 c3inert 1 (liftRes1 v) := by
  intro b hb
  refine typeOf_inert3_of_irreducible_map ?_
  have hres : (fun i => residue O (b i)) = v := residue_comp_of_proj_liftRes1 hb
  rw [g61c_map_monicPoly (residue O) b, hres]
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ (fun y hy => ?_)
  · rw [Finset.mem_Icc, monicPoly_natDegree]
    omega
  · refine hv y ?_
    rw [← g61c_cubic_eval v y]
    exact hy

end Cert

/-! ## 3. The gate -/

section Gate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **G.61c.** `(q³ − q) / (3 q³) ≤ decidedDensity O 3 c3inert`, every `O`. A LOWER BOUND, not the
density. -/
theorem gate_inert3_lower [IsAdicComplete (maximalIdeal O) O] :
    ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
      ≤ decidedDensity O 3 c3inert := by
  classical
  have hbound := decidedDensity_ge_of_inj (O := O) (n := 3) (N := 1) (σ := c3inert)
    (A := {v : Fin 3 → ResidueField O // NoRootCubic v})
    (fun v => liftRes1 v.1)
    (fun _ _ h => Subtype.ext (liftRes1_injective h))
    (fun v => inert3_decided v.2)
  have hcount := three_mul_card_noRootCubic (ResidueField O)
  have hcast : (3 : ℝ) * (Nat.card {v : Fin 3 → ResidueField O // NoRootCubic v} : ℝ)
      + (residueCard O : ℝ) = (residueCard O : ℝ) ^ 3 := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcount
    push_cast at h
    simpa [residueCard] using h
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  refine le_trans (le_of_eq ?_) hbound
  rw [show (3 : ℕ) * 1 = 3 from rfl]
  field_simp
  linarith [hcast]

end Gate

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.inert3_decided
#print axioms Uniformity.Density.gate_inert3_lower

end AxCheck
