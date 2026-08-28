/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B32b

/-!
# Uniformity.ChapC.C131ae0 — the `C131ae.suppVal_add_eq_left_of_lt` leaf, split out

**[UNT 2026-08-28]** This file exists ONLY to break a textual import cycle blocking the
physical retirement of the declared cite `fgmn_dv_exact_mul` (see `C66b.lean`'s dated
`[H0LEG 2026-08-28]` retirement note and `runs/wave-c/verdict_H0LEG.md`).

**What moved and why.** `C130nv.lean` used exactly ONE declaration from `C131ae.lean`:
`Uniformity.Density.Tower.C131ae.suppVal_add_eq_left_of_lt` (two call sites, C.05's
budget-floor case split). But `C131ae.lean` also imports `C131ac.lean` (for its own main
theorem, `mem_towerLocus_of_budget`, unaffected by this file), and `C131ac.lean` is the
sole proof consumer of the axiom `fgmn_dv_exact_mul`. That put `C131ac` INSIDE the import
foundation of every C130nv-descendant file (`C130nv2/C130nv3/C133mh1/C133mh3/...`),
including `C133h0leg.lean`, whose whole point is to supply the axiom's replacement
theorem — an import cycle if `C66b.lean` were converted to import `C133h0leg` in place.

The moved declarations below (`addVal_neg_one`, `addVal_neg`, `gaussVal_neg`,
`dev_zero_any`, `dev_neg_of_monic`, `suppVal_neg`, `suppVal_add_eq_left_of_lt`) are the
self-contained "Part 1 — negation-invariance and the ultrametric equality-off-ties law"
section of `C131ae.lean` (former lines 90–160, `section Ultrametric … end Ultrametric`),
moved here **VERBATIM** (byte-identical text; only the containing file and this docstring
are new — machine-diffed against the pre-move text in `C131ae.lean`'s git history).
They depend only on chapter B (`B32a`/`B32b`, imported here via `B32b`), never on
`C131ac`/`C66b`. `C131ae.lean` now `import`s this file (same namespace,
`Uniformity.Density.Tower.C131ae`, so every existing qualified reference — in
`C131ae.lean` itself and in `C130nv.lean` — resolves unchanged) instead of carrying the
section body directly.

No proof or statement was touched by this split: `lake env lean` diagnostics are the
check, and the AxCheck footer below is this file's own certificate (Lean-core).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131ae

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-! ## Part 1 — negation-invariance and the ultrametric equality-off-ties law
(moved verbatim from `C131ae.lean`, former lines 90–160; `[UNT 2026-08-28]`) -/

section Ultrametric

variable {φ : Polynomial O} {u ℓ : ℕ}

/-- `-1` has valuation `0`, being a unit. -/
private theorem addVal_neg_one : addVal O (-1 : O) = 0 :=
  IsDiscreteValuationRing.addVal_eq_zero_iff.2 isUnit_one.neg

/-- `addVal` does not see negation: `-1` is a unit. -/
theorem addVal_neg (x : O) : addVal O (-x) = addVal O x := by
  have h1 : (-x : O) = (-1 : O) * x := by ring
  rw [h1, IsDiscreteValuationRing.addVal_mul, addVal_neg_one, zero_add]

/-- `gaussVal` does not see negation: `-1` is a unit. -/
theorem gaussVal_neg (a : Polynomial O) : gaussVal (-a) = gaussVal a := by
  have hdeg : (-a).natDegree = a.natDegree := Polynomial.natDegree_neg a
  simp only [gaussVal, hdeg]
  refine Finset.inf_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_neg, addVal_neg]

/-- `dev` of `0` vanishes at every abscissa. -/
private theorem dev_zero_any (ψ : Polynomial O) : ∀ j, dev ψ (0 : Polynomial O) j = 0 := by
  intro j
  induction j with
  | zero => exact Polynomial.zero_modByMonic ψ
  | succ j ih =>
      show dev ψ ((0 : Polynomial O) /ₘ ψ) j = 0
      rw [Polynomial.zero_divByMonic]
      exact ih

/-- `dev` sends negation to negation. -/
theorem dev_neg_of_monic (hφ : φ.Monic) (a : Polynomial O) (j : ℕ) :
    dev φ (-a) j = - dev φ a j := by
  have h := dev_add_of_monic hφ a (-a) j
  simp only [add_neg_cancel] at h
  rw [dev_zero_any φ j] at h
  linear_combination -h

/-- `suppVal` does not see negation. -/
theorem suppVal_neg (hφ : φ.Monic) (a : Polynomial O) :
    suppVal φ (-a) u ℓ = suppVal φ a u ℓ := by
  have hdeg : (-a).natDegree = a.natDegree := Polynomial.natDegree_neg a
  simp only [suppVal, hdeg]
  refine Finset.inf_congr rfl fun j _ => ?_
  congr 1
  congr 1
  show gaussVal (dev φ (-a) j) = gaussVal (dev φ a j)
  rw [dev_neg_of_monic hφ, gaussVal_neg]

/-- **Ultrametric equality off ties.** If `a`'s cleared support is strictly below `b`'s,
adding `b` to `a` changes nothing. -/
theorem suppVal_add_eq_left_of_lt (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hℓ : 0 < ℓ) (u : ℕ)
    {a b : Polynomial O} (h : suppVal φ a u ℓ < suppVal φ b u ℓ) :
    suppVal φ (a + b) u ℓ = suppVal φ a u ℓ := by
  have h1 : suppVal φ a u ℓ ≤ suppVal φ (a + b) u ℓ := by
    have hmin := min_suppVal_le_suppVal_add hφ hd hℓ u a b
    rwa [min_eq_left h.le] at hmin
  have hnegb : suppVal φ (-b) u ℓ = suppVal φ b u ℓ := suppVal_neg hφ b
  have heq : a + b + -b = a := by ring
  have h2 : suppVal φ (a + b) u ℓ ≤ suppVal φ a u ℓ := by
    by_contra hcon
    push_neg at hcon
    have hb' : suppVal φ a u ℓ < suppVal φ (-b) u ℓ := by rw [hnegb]; exact h
    have hmin2 := min_suppVal_le_suppVal_add hφ hd hℓ u (a + b) (-b)
    rw [heq] at hmin2
    exact absurd hmin2 (not_le.mpr (lt_min hcon hb'))
  exact le_antisymm h2 h1

end Ultrametric

end Uniformity.Density.Tower.C131ae

/-! ## Axiom footprint — this leaf must be Lean-core (`[UNT 2026-08-28]` check) -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131ae.addVal_neg
#print axioms Uniformity.Density.Tower.C131ae.gaussVal_neg
#print axioms Uniformity.Density.Tower.C131ae.dev_neg_of_monic
#print axioms Uniformity.Density.Tower.C131ae.suppVal_neg
#print axioms Uniformity.Density.Tower.C131ae.suppVal_add_eq_left_of_lt

end AxCheck
