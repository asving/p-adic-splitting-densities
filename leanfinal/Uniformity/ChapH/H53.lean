/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapH.H53 — within-class independence: `1, η, …, η^{f₁−1}` are `F`-independent

**Chapter H, NODE H.53** (`blueprint/CHAP-H_general_induction.md` §8, the slot/lift layer).
Source: `EFF.GENHN.27`: *"at a within-class tie among `i, i+e₁, …, i+e₁(f₁−1)` the residue is
`Σ_t res(a_{i+e₁t})·η^t ≠ 0` because `{1, η, …, η^{f₁−1}}` are `F_Q`-independent
(`deg ψ = f₁`)"*, with the corpus derivation *"a vanishing `F_Q`-combination of `1, η, …,
η^{f₁−1}` with some nonzero coefficient contradicts `[F_Q(η) : F_Q] = f₁`"*.

`η` is NOT constructed here (its corpus construction `res(θ^{e₁}π^{−h})` needs the stage carrier);
it enters as *any* integral element whose minimal polynomial has degree `Module.finrank F K`, so
the node is carrier-free and the stage layer supplies `η` as a hypothesis.

DEPENDS: none beyond mathlib (`minpoly.degree_le_of_ne_zero`, `minpoly.ne_zero`,
`Polynomial.degree_sum_fin_lt`, `Polynomial.finsetSum_coeff`).

**PROOF** (the blueprint's recommended route B). Set `p := Σ_t C (l t) * X^t ∈ F[X]`. Then
`aeval η p = 0` by `hsum`, and `deg p < f = natDegree (minpoly F η) = deg (minpoly F η)`; were
`p ≠ 0`, `minpoly.degree_le_of_ne_zero` would give `deg (minpoly F η) ≤ deg p`, a contradiction.
So `p = 0`, and `l t = p.coeff t = 0` for each `t`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Induction

open Polynomial in
/-- **H.53 — residue-field independence.** If the minimal polynomial of `η : K` over the subfield
`F` has degree `[K : F] = f`, then `1, η, …, η^{f-1}` are `F`-linearly independent: a vanishing
combination `Σ_t l t · η^t = 0` has all `l t = 0`. -/
theorem eta_independent {F K : Type*} [Field F] [Field K] [Algebra F K] {η : K}
    (hgen : (minpoly F η).natDegree = Module.finrank F K) (hint : IsIntegral F η)
    {f : ℕ} (hf : f = Module.finrank F K) (l : Fin f → F)
    (hsum : ∑ t : Fin f, algebraMap F K (l t) * η ^ (t : ℕ) = 0) :
    ∀ t, l t = 0 := by
  classical
  -- the interpolating polynomial `p = Σ_t (l t) X^t`
  set p : F[X] := ∑ t : Fin f, C (l t) * X ^ (t : ℕ) with hpdef
  have hminNe : minpoly F η ≠ 0 := minpoly.ne_zero hint
  have hnatDeg : (minpoly F η).natDegree = f := by rw [hgen, hf]
  have hminDeg : (minpoly F η).degree = (f : WithBot ℕ) := by
    rw [degree_eq_natDegree hminNe, hnatDeg]
  have haeval : aeval η p = 0 := by
    rw [hpdef]
    simpa using hsum
  have hdeg : p.degree < (minpoly F η).degree := by
    rw [hminDeg, hpdef]
    exact degree_sum_fin_lt l
  have hp0 : p = 0 := by
    by_contra hne
    exact absurd (minpoly.degree_le_of_ne_zero F η hne haeval) (not_le.2 hdeg)
  intro t
  have hcoeff : p.coeff (t : ℕ) = l t := by
    rw [hpdef, finsetSum_coeff]
    simp [coeff_C_mul, coeff_X_pow, Fin.val_eq_val]
  rw [← hcoeff, hp0, coeff_zero]

section AxCheck
#print axioms Uniformity.Density.Induction.eta_independent
end AxCheck

end Uniformity.Density.Induction
