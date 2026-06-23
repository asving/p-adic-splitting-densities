/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.RatFn

/-!
# LeanUrat.OMInduction — the novel BB3-∞ induction (abstract)

The genuinely-new step of `BB3_infinity.md`: a function defined by a well-founded OM-order recursion
with rational coefficients and a nonzero self-loop pivot is itself a uniform rational function of `q`.

`clusterVol T q = (Σ_{cells} coeff(q) · ∏_{children} clusterVol(child, q)) / pivot(q)`, where the
children have strictly smaller `size` (GMN-III strict descent), the coefficients are rational (BB1 ×
BB3), and the pivot is nonzero on `q > 1` (L5fix self-loop). Proof: well-founded induction on `size`,
closing each step with the `RatFn` closure lemmas. Everything `p`-dependent-looking (child volumes,
residual counts) is rational by IH / BB3, so no characteristic dependence survives.

PROVED sorry-free; no axioms beyond Lean core.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OMInduction

open RatFn

/-- **The BB3-∞ induction (abstract).** A function defined by the well-founded OM recursion with
rational coefficients and a pole-free self-loop pivot is a uniform rational function of `q`. -/
theorem clusterVol_isRational
    {Shape : Type*} (size : Shape → ℕ)
    (clusterVol : Shape → ℕ → ℚ)
    (contribs : Shape → List ((ℕ → ℚ) × List Shape))
    (pivot : Shape → (ℕ → ℚ))
    (hrec : ∀ (T : Shape) (q : ℕ), 1 < q →
        clusterVol T q
          = ((contribs T).map
                (fun c => c.1 q * (c.2.map (fun ch => clusterVol ch q)).prod)).sum / pivot T q)
    (hdescend : ∀ (T : Shape), ∀ c ∈ contribs T, ∀ ch ∈ c.2, size ch < size T)
    (hcoeff : ∀ (T : Shape), ∀ c ∈ contribs T, IsRationalFn c.1)
    (hpivot_rat : ∀ (T : Shape), IsRationalFn (pivot T))
    (hpivot_ne : ∀ (T : Shape) (q : ℕ), 1 < q → pivot T q ≠ 0) :
    ∀ T : Shape, IsRationalFn (clusterVol T) := by
  -- `IsRationalFn` only constrains a function at `q > 1`, so it is invariant under any change of
  -- the function that preserves its values there.  We use this to rewrite `clusterVol T` (via the
  -- well-founded recursion `hrec`) into the divided sum-of-products that the `RatFn` closure lemmas
  -- recognise.
  have congr_of_eq_gt_one :
      ∀ {f g : ℕ → ℚ}, (∀ q : ℕ, 1 < q → f q = g q) → IsRationalFn g → IsRationalFn f := by
    rintro f g hfg ⟨num, den, hden, h⟩
    refine ⟨num, den, hden, fun q hq => ⟨(h q hq).1, ?_⟩⟩
    rw [hfg q hq, (h q hq).2]
  -- Strong induction on the cluster size `size T`.  We prove the statement for every `T` with
  -- `size T = n`, by strong induction on `n` (every descent child has strictly smaller size).
  suffices H : ∀ n : ℕ, ∀ T : Shape, size T = n → IsRationalFn (clusterVol T) by
    exact fun T => H (size T) T rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hT
    -- The recursion realises `clusterVol T` (at every `q > 1`) as a quotient `S q / pivot T q`,
    -- where `S` is a finite sum over `contribs T` of `coeff q * ∏ children-vols q`.
    set S : ℕ → ℚ :=
      fun q => ((contribs T).map
        (fun c => c.1 q * (c.2.map (fun ch => clusterVol ch q)).prod)).sum with hS
    -- Each summand `c.1 q * (∏ child-vols)` is rational: the coefficient by `hcoeff`, the product
    -- by the induction hypothesis applied to each (strictly smaller) child via `isRationalFn_listProd`.
    have hsum_terms : ∀ f ∈ (contribs T).map
        (fun c => fun q => c.1 q * (c.2.map (fun ch => clusterVol ch q)).prod),
        IsRationalFn f := by
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨c, hc, rfl⟩ := hf
      -- product of the child volumes is rational
      have hprod : IsRationalFn (fun q => (c.2.map (fun ch => clusterVol ch q)).prod) := by
        have hp := RatFn.isRationalFn_listProd (c.2.map (fun ch => clusterVol ch))
          (fun g hg => by
            obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hg
            exact ih (size ch) (by have := hdescend T c hc ch hch; omega) ch rfl)
        -- `(c.2.map (fun ch => clusterVol ch)).map (fun f => f q) = c.2.map (fun ch => clusterVol ch q)`
        have hmap : (fun q => ((c.2.map (fun ch => clusterVol ch)).map (fun f => f q)).prod)
            = (fun q => (c.2.map (fun ch => clusterVol ch q)).prod) := by
          funext q; rw [List.map_map]; rfl
        rwa [hmap] at hp
      exact RatFn.isRationalFn_mul (hcoeff T c hc) hprod
    -- the whole sum `S` is rational
    have hSrat : IsRationalFn S := by
      have hsum := RatFn.isRationalFn_listSum
        ((contribs T).map (fun c => fun q => c.1 q * (c.2.map (fun ch => clusterVol ch q)).prod))
        hsum_terms
      -- rewrite the `.map (fun f => f q)` of the contribution-functions back to the pointwise form
      rw [hS]
      have hmap : (fun q => (((contribs T).map
            (fun c => fun q => c.1 q * (c.2.map (fun ch => clusterVol ch q)).prod)).map
            (fun f => f q)).sum)
          = (fun q => ((contribs T).map
            (fun c => c.1 q * (c.2.map (fun ch => clusterVol ch q)).prod)).sum) := by
        funext q; rw [List.map_map]; rfl
      rwa [hmap] at hsum
    -- dividing by the pole-free pivot stays rational
    have hdiv : IsRationalFn (fun q => S q / pivot T q) :=
      RatFn.isRationalFn_div hSrat (hpivot_rat T) (fun q hq => hpivot_ne T q hq)
    -- and `clusterVol T` agrees with that quotient on `q > 1` (by `hrec`), hence is rational.
    refine congr_of_eq_gt_one (g := fun q => S q / pivot T q) ?_ hdiv
    intro q hq
    rw [hrec T q hq, hS]

end LeanUrat.OMInduction
