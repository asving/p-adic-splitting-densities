/-
Unit XF.4 resRootSum  [PROVED — Lean-core axioms only]
moves_ref: "Res(f, f′) over the n−1 roots of f′" + the n·v_p(n) offset.
sketch: resultant map-commutation helper; root-product over V.L
(`resultant_eq_prod_roots_sub` + eval-product lemmas); lc(f′) = n.
deps: XF.3-independent (V explicit — INTERNAL unit). difficulty: HARD.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem resRootSum (p n : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (f : Polynomial ℤ_[p])
    (hm : f.Monic) (hd : f.natDegree = n)
    (V : ValExt p ((f.map PadicInt.Coe.ringHom).derivative)) :
    ‖f.resultant f.derivative‖ =
      ‖(n : ℚ_[p])‖ ^ n *
        ((((f.map PadicInt.Coe.ringHom).derivative.map (algebraMap ℚ_[p] V.L)).roots).map
          (fun θ => V.w (Polynomial.aeval θ (f.map PadicInt.Coe.ringHom)))).prod := by
  classical
  -- The composite ring hom ℤ_[p] → ℚ_[p] → V.L.
  set ρ : ℤ_[p] →+* V.L := (algebraMap ℚ_[p] V.L).comp PadicInt.Coe.ringHom with hρ
  -- Injectivity of the two factors, hence of the composite.
  have hφinj : Function.Injective (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) := by
    intro a b h
    rw [PadicInt.Coe.ringHom_apply, PadicInt.Coe.ringHom_apply] at h
    exact Subtype.coe_inj.mp h
  have hψinj : Function.Injective (algebraMap ℚ_[p] V.L) := (algebraMap ℚ_[p] V.L).injective
  have hρinj : Function.Injective ρ := by
    rw [hρ, RingHom.coe_comp]; exact hψinj.comp hφinj
  -- Degree / leading-coeff bookkeeping for H := f.map ρ.  (Explicit hom arguments are
  -- required throughout: a bare `derivative_map` would match the frozen occurrence of
  -- `(f.map Coe.ringHom).derivative` inside `V.L`'s type index and produce a bad motive.)
  have hHd : (f.map ρ).natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective hρinj, hd]
  have hHderivdeg : (f.map ρ).derivative.natDegree = f.derivative.natDegree := by
    rw [Polynomial.derivative_map f ρ, Polynomial.natDegree_map_eq_of_injective hρinj]
  have hg : (f.map ρ).natDegree ≤ f.natDegree := (hHd.trans hd.symm).le
  -- `(f.map ρ).derivative` rewritten as `(f.map Coe.ringHom).derivative.map (algebraMap ..)`.
  have hgmap : (f.map ρ).derivative
      = (f.map PadicInt.Coe.ringHom).derivative.map (algebraMap ℚ_[p] V.L) := by
    rw [hρ, ← Polynomial.map_map,
      Polynomial.derivative_map (f.map PadicInt.Coe.ringHom) (algebraMap ℚ_[p] V.L)]
  -- The derivative splits over V.L.
  have hsplit : (f.map ρ).derivative.Splits := by
    rw [hgmap]; exact V.splits
  -- The leading coefficient of H.derivative is (n : ℚ_[p]) pushed into V.L.
  have hlc : (f.map ρ).derivative.leadingCoeff = algebraMap ℚ_[p] V.L (n : ℚ_[p]) := by
    rw [Polynomial.derivative_map f ρ, Polynomial.leadingCoeff_map_of_injective hρinj,
      Polynomial.leadingCoeff_derivative, hm.leadingCoeff, one_mul, hd, hρ]
    simp
  have hlcw : V.w ((f.map ρ).derivative.leadingCoeff) = ‖(n : ℚ_[p])‖ := by
    rw [hlc, V.ext]
  have hsign : ∀ k : ℕ, V.w ((-1 : V.L) ^ k) = 1 := by
    intro k
    rw [map_pow, AbsoluteValue.map_neg, map_one, one_pow]
  -- Step 1: the ℤ_[p]-norm of the resultant equals its V.w-image.
  have L1 : ‖f.resultant f.derivative‖ = V.w (ρ (f.resultant f.derivative)) := by
    rw [hρ, RingHom.comp_apply, PadicInt.norm_def, ← V.ext, PadicInt.Coe.ringHom_apply]
  -- Step 2: push the resultant through ρ.
  have L2 : ρ (f.resultant f.derivative)
      = Polynomial.resultant (f.map ρ) (f.map ρ).derivative f.natDegree f.derivative.natDegree := by
    rw [Polynomial.derivative_map f ρ, Polynomial.resultant_map_map]
  -- Step 3: the root-product identity, taken under V.w.
  have L3 : V.w (Polynomial.resultant (f.map ρ) (f.map ρ).derivative f.natDegree f.derivative.natDegree)
      = ‖(n : ℚ_[p])‖ ^ n *
          (((f.map ρ).derivative.roots).map (fun θ => V.w ((f.map ρ).eval θ))).prod := by
    rw [Polynomial.resultant_comm,
      show f.derivative.natDegree = (f.map ρ).derivative.natDegree from hHderivdeg.symm,
      Polynomial.resultant_eq_prod_eval (f.map ρ).derivative (f.map ρ) f.natDegree hg hsplit,
      map_mul, hsign, one_mul, map_mul, map_pow, hlcw, hd, map_multiset_prod, Multiset.map_map]
    rfl
  -- Match the goal's roots multiset and evaluation function to H's.
  have heval : ∀ θ : V.L,
      (Polynomial.aeval θ) (f.map PadicInt.Coe.ringHom) = (f.map ρ).eval θ := by
    intro θ
    rw [← Polynomial.eval_map_algebraMap, Polynomial.map_map, ← hρ]
  rw [L1, L2, L3, ← hgmap]
  simp only [heval]

end LeanUrat.MovesX
