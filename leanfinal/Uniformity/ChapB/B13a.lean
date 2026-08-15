/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B02

/-!
# Uniformity.ChapB.B13a — the top development coefficient of a monic `f` is `1`

**Chapter B, NODE B.13** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A — **part a of the mandated 2-way split** (`dev_top` here, `npHgt_top`
in `B13b.lean`; the split is mandated because the monicity-of-the-quotient obligation of
step 3 below is the node's largest single piece).

*The top of the polygon.* Let `φ` be monic with `m := φ.natDegree > 0` and let `f` be monic
with `f.natDegree = μ * m`. Then `dev φ f μ = 1`: the `φ`-adic development of a monic `f`
is `f = φ ^ μ + Σ_{j < μ} (dev φ f j) φ ^ j`, so its top coefficient is the constant `1`.

DEPENDS: B.02 (`dev`) · mathlib `Polynomial.eq_one_of_monic_natDegree_zero`,
`Polynomial.modByMonic_eq_self_iff`, `Polynomial.natDegree_divByMonic`,
`Polynomial.leadingCoeff_divByMonic_of_monic`.

**PROOF.** Induction on `μ`, generalising `f`.

1. `μ = 0`: `f.natDegree = 0` and `f` monic force `f = 1`
   (`eq_one_of_monic_natDegree_zero`); then `dev φ f 0 = 1 %ₘ φ = 1` because
   `(1 : O[X]).degree = 0 < φ.degree` (`modByMonic_eq_self_iff hφ`, using
   `natDegree_pos_iff_degree_pos` on `hd`).
2. `μ + 1`: first `φ.degree ≤ f.degree`, since both are monic hence nonzero and
   `φ.natDegree = m ≤ (μ + 1) * m = f.natDegree`. Then
   `leadingCoeff_divByMonic_of_monic hφ` says `(f /ₘ φ).leadingCoeff = f.leadingCoeff = 1`,
   i.e. `f /ₘ φ` is monic, and `natDegree_divByMonic` says
   `(f /ₘ φ).natDegree = (μ + 1) * m - m = μ * m`. Finally
   `dev φ f (μ + 1) = dev φ (f /ₘ φ) μ` by definition, so the induction hypothesis at
   `f /ₘ φ` closes the goal.

The blueprint's alternative route through `Polynomial.Monic.natDegree_divByMonic` /
`Polynomial.Monic.divByMonic` is not taken: neither name exists at the pin, and
`leadingCoeff_divByMonic_of_monic` (which does) gives the monicity of the quotient in one
step from the degree comparison.

SOURCE: `EFF.HE3.13` verbatim (*"`A_μ = 1`, `dv = 0`"*); `EFF.HE6.10` (*"`dv(A_μ) = 0`"*);
`EFF.W12.23` (the polygon includes the terminal point).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The top of the polygon.** For `φ` monic of positive degree and `f` monic of degree
`μ * φ.natDegree`, the `μ`-th `φ`-adic development coefficient of `f` is the constant `1`. -/
theorem dev_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : Polynomial O}
    (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) : dev φ f μ = 1 := by
  nontriviality O
  induction μ generalizing f with
  | zero =>
    have hf1 : f = 1 := eq_one_of_monic_natDegree_zero hf (by simpa using hdeg)
    change f %ₘ φ = 1
    rw [hf1]
    refine (modByMonic_eq_self_iff hφ).2 ?_
    rw [degree_one]
    exact natDegree_pos_iff_degree_pos.1 hd
  | succ μ ih =>
    -- `φ.degree ≤ f.degree`, from `φ.natDegree ≤ f.natDegree` and nonvanishing of both.
    have hle : φ.degree ≤ f.degree := by
      rw [degree_eq_natDegree hφ.ne_zero, degree_eq_natDegree hf.ne_zero, Nat.cast_le, hdeg,
        Nat.succ_mul]
      exact Nat.le_add_left _ _
    -- the quotient of a monic by a monic of smaller degree is monic
    have hq : (f /ₘ φ).Monic := by
      have := leadingCoeff_divByMonic_of_monic hφ hle
      rw [hf.leadingCoeff] at this
      exact this
    -- and its degree drops by exactly `φ.natDegree`
    have hqdeg : (f /ₘ φ).natDegree = μ * φ.natDegree := by
      rw [natDegree_divByMonic f hφ, hdeg, Nat.succ_mul]
      omega
    change dev φ (f /ₘ φ) μ = 1
    exact ih hq hqdeg

section AxCheck
#print axioms Uniformity.Density.Leaf.dev_top
end AxCheck

end Uniformity.Density.Leaf
