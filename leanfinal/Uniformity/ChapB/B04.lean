/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B02

/-!
# Uniformity.ChapB.B04 — the `φ`-adic development vanishes past the degree

**Chapter B, NODE B.04** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

The `φ`-adic development of `f` is a finite object: if `φ` is monic with `0 < deg φ` and
`f.natDegree < j * φ.natDegree` then `dev φ f j = 0`. In particular `dev φ f j = 0` for every
`j > f.natDegree`, since `1 ≤ φ.natDegree`.

DEPENDS: B.02 (`dev`) · mathlib `Polynomial.natDegree_divByMonic`,
`Polynomial.divByMonic_eq_zero_iff`, `Polynomial.degree_lt_degree`, `Polynomial.zero_modByMonic`,
`Polynomial.zero_divByMonic`.

**PROOF.** Induction on `j`, generalising `f`.

* `j = 0`: the hypothesis reads `f.natDegree < 0`, impossible.
* `j + 1`: split on whether `f` reaches the degree of `φ`.
  * `f.natDegree < φ.natDegree`: then `f.degree < φ.degree` (`degree_lt_degree`, which handles
    `f = 0` as `⊥ < φ.degree`), so `f /ₘ φ = 0` by `divByMonic_eq_zero_iff`, and
    `dev φ f (j+1) = dev φ 0 j = 0` by the private helper `dev_zero`.
  * `φ.natDegree ≤ f.natDegree`: `natDegree_divByMonic` gives
    `(f /ₘ φ).natDegree = f.natDegree - φ.natDegree`, which is `< j * φ.natDegree` by `omega`
    once `(j+1) * φ.natDegree` is unfolded as `j * φ.natDegree + φ.natDegree`
    (`Nat.succ_mul`); apply the induction hypothesis at `f /ₘ φ`.

The private helper `dev_zero : dev φ 0 j = 0` is the same induction on `j`, using
`zero_modByMonic` and `zero_divByMonic`.

SOURCE: `EFF.W12.23` (the development is finite: `j` ranges over `j ≤ m`); `EFF.HE3.13`
(`A_μ = 1`, i.e. the development stops).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

-- (`dev` is defined over any `CommRing`; the DVR structure plays no role in this helper.)
omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The development of the zero polynomial is identically zero. -/
private theorem dev_zero (φ : Polynomial O) : ∀ j : ℕ, dev φ (0 : Polynomial O) j = 0 := by
  intro j
  induction j with
  | zero => exact zero_modByMonic φ
  | succ j ih => rw [show dev φ (0 : Polynomial O) (j + 1) = dev φ (0 /ₘ φ) j from rfl,
      zero_divByMonic]; exact ih

-- The signed hypothesis `hd : 0 < φ.natDegree` is kept (frozen signature) but is not consumed:
-- the induction only needs `hφ` plus `Nat` arithmetic. At `φ.natDegree = 0` the statement is
-- vacuous anyway (`f.natDegree < j * 0 = 0` is false), so nothing is lost.
set_option linter.unusedVariables false in
/-- The `φ`-adic development vanishes past the degree: `dev φ f j = 0` as soon as
`f.natDegree < j * φ.natDegree`. -/
theorem dev_eq_zero_of_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    ∀ (f : Polynomial O) (j : ℕ), f.natDegree < j * φ.natDegree → dev φ f j = 0 := by
  intro f j
  induction j generalizing f with
  | zero => intro h; simp at h
  | succ j ih =>
    intro h
    rw [show dev φ f (j + 1) = dev φ (f /ₘ φ) j from rfl]
    by_cases hlt : f.natDegree < φ.natDegree
    · rw [(divByMonic_eq_zero_iff hφ).2 (degree_lt_degree hlt)]
      exact dev_zero φ j
    · refine ih (f /ₘ φ) ?_
      rw [natDegree_divByMonic f hφ]
      rw [Nat.succ_mul] at h
      omega

section AxCheck
#print axioms Uniformity.Density.Leaf.dev_eq_zero_of_lt
end AxCheck

end Uniformity.Density.Leaf
