/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface

/-!
# LeanUrat.L7 — Functional equation by interpolation from tame primes (`notes/L7_proof.md`)

**Lemma L7** (PROVED sorry-free). Given (H-L6) a single `S_σ ∈ ℚ(t)` representing `ρ(n,σ;q)` at
**every** prime power `q`, and (H-tame) a *palindromic* `R_σ ∈ ℚ(t)` representing `ρ` at all tame
prime powers `q = p^k`, `p > n` — an **infinite** set — the identity theorem for `ℚ(t)` forces
`S_σ = R_σ`, hence `S_σ` is palindromic and the functional equation `ρ(n,σ;q⁻¹) = ρ(n,σ;q)` holds
at *every* prime, wild included.

We work at the level of the `DensityFoundation` interface and represent rational functions by a
numerator/denominator pair of `ℚ[t]` with nonvanishing denominator on the relevant set (matching
`Interface.tame_functionalEquation` / `perShapeVolume_rational`). The two pieces:

* `ratfunc_agree_of_infinite` — the algebraic core (identity theorem): two `num/den` pairs agreeing
  on an infinite set of points (no poles there) have `num₁ * den₂ = num₂ * den₁`. PROVED from
  mathlib (`Polynomial.eq_zero_of_infinite_isRoot`), sorry-free.
* `tame_to_all_primes` — the L7 conclusion: given (H-L6) and (H-tame), the all-prime representative
  agrees with the tame representative in `ℚ(t)` (`num * tden = tnum * den`). The tame prime-power
  set is infinite (Euclid: infinitely many primes `> n`) and pole-free (its `tden`-roots removed),
  and the algebraic core finishes. Sorry-free.
* `eval_reflect_eq` / `reflect_ne` / `isPalindromic_of_agree` — the palindromy *transfer* packaging:
  agreement in `ℚ(t)` plus palindromy of the tame `tnum/tden` (the faithful semantic
  `Interface.IsPalindromic`) gives palindromy of `num/den`, again by the identity theorem applied to
  the cross-multiplied palindromy polynomial. Sorry-free; this is what the Goal Theorem consumes.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.L7

open Polynomial

/-- **Evaluation-at-inverse bridge.** For `x ≠ 0` and `N ≥ f.natDegree`, the reflected polynomial
satisfies `(reflect N f).eval x = f.eval x⁻¹ · x^N`. This is `Polynomial.eval₂_reflect_mul_pow`
specialized to `ℚ` (with `eval₂ (RingHom.id ℚ) = eval` and `⅟x = x⁻¹`), reorganized so that the
left side is `(reflect N f).eval x`. It converts the (non-polynomial) "evaluate at `x⁻¹`" appearing
in `IsPalindromic` into a genuine polynomial evaluation, enabling the identity theorem. -/
theorem eval_reflect_eq (f : Polynomial ℚ) (x : ℚ) (hx : x ≠ 0) (N : ℕ) (hf : f.natDegree ≤ N) :
    (Polynomial.reflect N f).eval x = f.eval x⁻¹ * x ^ N := by
  have hxinv : x⁻¹ ≠ 0 := inv_ne_zero hx
  haveI : Invertible x⁻¹ := invertibleOfNonzero hxinv
  have key := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℚ) x⁻¹ N f hf
  rw [eval₂_id, eval₂_id, invOf_eq_inv, inv_inv] at key
  -- key : (reflect N f).eval x * (x⁻¹) ^ N = f.eval x⁻¹
  have hxpow : (x⁻¹ : ℚ) ^ N * x ^ N = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
  calc (Polynomial.reflect N f).eval x
      = (Polynomial.reflect N f).eval x * ((x⁻¹) ^ N * x ^ N) := by rw [hxpow, mul_one]
    _ = ((Polynomial.reflect N f).eval x * (x⁻¹) ^ N) * x ^ N := by ring
    _ = f.eval x⁻¹ * x ^ N := by rw [key]

/-- The reflection of a nonzero polynomial is nonzero (`Polynomial.reflect_eq_zero_iff`). -/
theorem reflect_ne (f : Polynomial ℚ) (hf : f ≠ 0) (N : ℕ) : Polynomial.reflect N f ≠ 0 := by
  intro h
  exact hf (Polynomial.reflect_eq_zero_iff.mp h)

/-- **Palindromy transfer (the L7 packaging lemma).** If `num/den` and `tnum/tden` agree in `ℚ(t)`
(the cross-multiplied `num * tden = tnum * den`), with `den ≠ 0`, `tden ≠ 0`, and `tnum/tden`
*palindromic* (`Interface.IsPalindromic`, the faithful semantic `R(1/x) = R(x)`), then `num/den` is
palindromic. This is exactly the step the Goal needs: the all-prime representative `num/den` inherits
the tame representative's functional equation.

The pointwise-pole subtlety is genuine — at a specific `x` we do *not* know `tden(x) ≠ 0`, so the
naive pointwise transfer fails. Instead we prove the *polynomial* identity
`(reflect N num) * den = num * (reflect N den)` (which encodes "`num/den` palindromic"; via
`eval_reflect_eq` it is `num(x⁻¹)·den(x) = num(x)·den(x⁻¹)` cleared of inverses) by the **identity
theorem** `Polynomial.eq_zero_of_infinite_isRoot`: it holds on the cofinite set where `x ≠ 0` and
all four of `den, tden` and their inverse-evaluations are nonzero (there the transfer is pure field
algebra through the tame palindromy `htpalin`). A polynomial identity then evaluates everywhere,
giving palindromy of `num/den` at every admissible `x` — including the poles of `tden`. -/
theorem isPalindromic_of_agree
    (num den tnum tden : Polynomial ℚ)
    (hden : den ≠ 0) (htden : tden ≠ 0)
    (hagree : num * tden = tnum * den)
    (htpalin : IsPalindromic tnum tden) :
    IsPalindromic num den := by
  classical
  -- A single degree bound `N` exceeding all four polynomials' degrees.
  set N : ℕ := max (max num.natDegree den.natDegree) (max tnum.natDegree tden.natDegree) with hN
  have hNnum : num.natDegree ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNden : den.natDegree ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNtnum : tnum.natDegree ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hNtden : tden.natDegree ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  -- The reflected denominators are nonzero (used for finiteness of their root sets).
  have hrden : Polynomial.reflect N den ≠ 0 := reflect_ne den hden N
  have hrtden : Polynomial.reflect N tden ≠ 0 := reflect_ne tden htden N
  -- The "bad" set: zero, and the (finitely many) roots of the four relevant nonzero polynomials.
  set B : Set ℚ := {(0 : ℚ)} ∪ {x | den.IsRoot x} ∪ {x | tden.IsRoot x}
      ∪ {x | (Polynomial.reflect N den).IsRoot x} ∪ {x | (Polynomial.reflect N tden).IsRoot x}
      with hBdef
  have hBfin : B.Finite := by
    refine Set.Finite.union (Set.Finite.union (Set.Finite.union (Set.Finite.union ?_ ?_) ?_) ?_) ?_
    · exact Set.finite_singleton 0
    · exact Polynomial.finite_setOf_isRoot hden
    · exact Polynomial.finite_setOf_isRoot htden
    · exact Polynomial.finite_setOf_isRoot hrden
    · exact Polynomial.finite_setOf_isRoot hrtden
  -- The target polynomial identity (cross-multiplied palindromy of `num/den`).
  have hpoly : (Polynomial.reflect N num) * den = num * (Polynomial.reflect N den) := by
    have hsub : (Polynomial.reflect N num) * den - num * (Polynomial.reflect N den) = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.Infinite.mono (s := Bᶜ) _ (Set.Finite.infinite_compl hBfin)
      intro x hx
      -- Unpack: `x ∉ B` gives all five nonvanishings.
      simp only [hBdef, Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_setOf_eq, Polynomial.IsRoot, not_or] at hx
      obtain ⟨⟨⟨⟨hx0, hdenx⟩, htdenx⟩, hrdenx⟩, hrtdenx⟩ := hx
      -- `x ≠ 0`.
      have hxne : x ≠ 0 := hx0
      have hxinv : x⁻¹ ≠ 0 := inv_ne_zero hxne
      -- Inverse-evaluation nonvanishing from reflect nonvanishing.
      have hdenxinv : den.eval x⁻¹ ≠ 0 := by
        have := eval_reflect_eq den x hxne N hNden
        intro h0
        apply hrdenx
        rw [this, h0, zero_mul]
      have htdenxinv : tden.eval x⁻¹ ≠ 0 := by
        have := eval_reflect_eq tden x hxne N hNtden
        intro h0
        apply hrtdenx
        rw [this, h0, zero_mul]
      -- Cross-multiplied agreement at `x` and at `x⁻¹` (from `hagree` as a polynomial identity).
      have hag_x : num.eval x * tden.eval x = tnum.eval x * den.eval x := by
        have := congrArg (Polynomial.eval x) hagree
        simpa [Polynomial.eval_mul] using this
      have hag_xinv : num.eval x⁻¹ * tden.eval x⁻¹ = tnum.eval x⁻¹ * den.eval x⁻¹ := by
        have := congrArg (Polynomial.eval x⁻¹) hagree
        simpa [Polynomial.eval_mul] using this
      -- Palindromy of `tnum/tden` at `x`.
      have htp : tnum.eval x⁻¹ / tden.eval x⁻¹ = tnum.eval x / tden.eval x :=
        htpalin x hxne htdenx htdenxinv
      -- Pointwise palindromy of `num/den`: `num(x⁻¹) * den(x) = num(x) * den(x⁻¹)`.
      have hcross : num.eval x⁻¹ * den.eval x = num.eval x * den.eval x⁻¹ := by
        -- From `hag_x`, `hag_xinv`: `num/den = tnum/tden` at both points; chain via `htp`.
        have e1 : num.eval x / den.eval x = tnum.eval x / tden.eval x := by
          rw [div_eq_div_iff hdenx htdenx]; linear_combination hag_x
        have e2 : num.eval x⁻¹ / den.eval x⁻¹ = tnum.eval x⁻¹ / tden.eval x⁻¹ := by
          rw [div_eq_div_iff hdenxinv htdenxinv]; linear_combination hag_xinv
        have e3 : num.eval x⁻¹ / den.eval x⁻¹ = num.eval x / den.eval x :=
          e2.trans (htp.trans e1.symm)
        exact (div_eq_div_iff hdenxinv hdenx).mp e3
      -- Conclude the root condition at `x`.
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul]
      rw [eval_reflect_eq num x hxne N hNnum, eval_reflect_eq den x hxne N hNden]
      -- LHS: num(x⁻¹)·x^N·den(x) ; RHS: num(x)·den(x⁻¹)·x^N
      have hreorg : num.eval x⁻¹ * x ^ N * den.eval x - num.eval x * (den.eval x⁻¹ * x ^ N)
          = (num.eval x⁻¹ * den.eval x - num.eval x * den.eval x⁻¹) * x ^ N := by ring
      rw [hreorg, hcross]; ring
    exact sub_eq_zero.mp hsub
  -- Now derive the pointwise palindromy of `num/den` from the polynomial identity `hpoly`.
  intro x hxne hdenx hdenxinv
  -- Evaluate `hpoly` at `x`, then translate reflects back to inverse-evaluations.
  have heval := congrArg (Polynomial.eval x) hpoly
  rw [Polynomial.eval_mul, Polynomial.eval_mul,
      eval_reflect_eq num x hxne N hNnum, eval_reflect_eq den x hxne N hNden] at heval
  -- heval : num(x⁻¹)·x^N·den(x) = num(x)·(den(x⁻¹)·x^N)
  have hxpow : (x : ℚ) ^ N ≠ 0 := pow_ne_zero _ hxne
  have hcross : num.eval x⁻¹ * den.eval x = num.eval x * den.eval x⁻¹ := by
    have h2 : (num.eval x⁻¹ * den.eval x) * x ^ N = (num.eval x * den.eval x⁻¹) * x ^ N := by
      linear_combination heval
    exact mul_right_cancel₀ hxpow h2
  -- Divide out the (nonzero) denominators.
  rw [div_eq_div_iff hdenxinv hdenx]
  linear_combination hcross

/-- **Identity theorem for `ℚ(t)` (the algebraic core of L7, FULLY PROVED).** If two rational
functions `num₁/den₁` and `num₂/den₂` (denominators nonvanishing at every point of an infinite set
`T ⊆ ℚ`) agree at every point of `T`, then `num₁ * den₂ = num₂ * den₁` as polynomials (i.e. they
are equal in `ℚ(t)`). Proved via `Polynomial.eq_zero_of_infinite_isRoot`: the polynomial
`num₁·den₂ - num₂·den₁` has the infinite set `T` among its roots. -/
theorem ratfunc_agree_of_infinite
    (num₁ den₁ num₂ den₂ : Polynomial ℚ) (T : Set ℚ) (hT : T.Infinite)
    (hden₁ : ∀ a ∈ T, den₁.eval a ≠ 0) (hden₂ : ∀ a ∈ T, den₂.eval a ≠ 0)
    (hagree : ∀ a ∈ T, num₁.eval a / den₁.eval a = num₂.eval a / den₂.eval a) :
    num₁ * den₂ = num₂ * den₁ := by
  -- the polynomial P := num₁·den₂ - num₂·den₁ vanishes on all of T
  have hsub : num₁ * den₂ - num₂ * den₁ = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ hT
    intro a ha
    have h1 := hden₁ a ha
    have h2 := hden₂ a ha
    have heq := hagree a ha
    -- clear denominators: num₁·den₂ = num₂·den₁ at a
    have : num₁.eval a * den₂.eval a = num₂.eval a * den₁.eval a := by
      field_simp at heq
      linarith [heq]
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_mul]
    rw [this]; ring
  exact sub_eq_zero.mp hsub

/-- **Lemma L7 (functional equation transfer — `ℚ(t)` agreement).** Suppose:
* (H-L6) `S = num/den` (with `den` nonvanishing at all prime powers) represents `F.density n σ` at
  every prime power `q`;
* (H-tame) `R = tnum/tden` represents `F.density n σ` at all tame prime powers (`p > n`, `p` prime).

Then the all-prime representative `S` agrees with the tame `R` in `ℚ(t)`, i.e.
`num * tden = tnum * den`. (Palindromy of `R` is *not* needed for this agreement step — it is the
separate input consumed by `isPalindromic_of_agree` — so it is not a hypothesis here.)

The proof feeds the tame prime-power set (infinite by Euclid, pole-free after removing the finitely
many `tden`-poles) to `ratfunc_agree_of_infinite`. Sorry-free (`notes/L7_proof.md §3-4`). -/
theorem tame_to_all_primes
    (F : DensityFoundation) (n : ℕ) (σ : FactorizationType) (hσ : σ.degree = n)
    (num den tnum tden : Polynomial ℚ)
    (hden0 : den ≠ 0) (htden0 : tden ≠ 0)
    (hL6 : ∀ q : ℕ, 1 < q → den.eval (q : ℚ) ≠ 0 ∧ F.density n σ q = num.eval (q : ℚ) / den.eval (q : ℚ))
    -- (H-tame) in the exact `Interface.tame_functionalEquation` form (no per-point pole hypothesis;
    -- the finitely many `tden`-poles are removed inside the proof):
    (htame : ∀ q : ℕ, q.Prime → n < q →
      F.density n σ q = tnum.eval (q : ℚ) / tden.eval (q : ℚ)) :
    num * tden = tnum * den := by
  -- The tame natural primes `> n`, as a set of naturals.
  set Sℕ : Set ℕ := {m : ℕ | m.Prime ∧ n < m} with hSℕ
  -- `Sℕ` is infinite: `{m | m.Prime}` is infinite, and `Sℕ` differs from it by removing
  -- the finitely many primes `≤ n` (those `m ≤ n`, a subset of `{0,…,n}`).
  have hSℕ_inf : Sℕ.Infinite := by
    have hsub : {m : ℕ | m.Prime} \ {m : ℕ | m ≤ n} ⊆ Sℕ := by
      intro m hm
      exact ⟨hm.1, not_le.mp hm.2⟩
    apply Set.Infinite.mono hsub
    apply Set.Infinite.sdiff Nat.infinite_setOf_prime
    exact Set.finite_Iic n |>.subset (fun m hm => hm)
  -- Cast `Sℕ` into `ℚ`; the cast `ℕ → ℚ` is injective so the image is still infinite.
  set Tprime : Set ℚ := (Nat.cast : ℕ → ℚ) '' Sℕ with hTprime
  have hTprime_inf : Tprime.Infinite :=
    hSℕ_inf.image (Set.injOn_of_injective Nat.cast_injective)
  -- Remove the finitely many roots of `tden` (a nonzero polynomial) to kill `tden`-poles.
  set T : Set ℚ := Tprime \ {x : ℚ | tden.IsRoot x} with hT
  have hT_inf : T.Infinite :=
    hTprime_inf.sdiff (Polynomial.finite_setOf_isRoot htden0)
  -- On `T`: `den` does not vanish, `tden` does not vanish, and `num/den = tnum/tden`.
  -- Helper: every element of `T` comes from a tame prime `m > n`.
  have hmem : ∀ a ∈ T, ∃ m : ℕ, m.Prime ∧ n < m ∧ (m : ℚ) = a ∧ tden.eval a ≠ 0 := by
    rintro a ⟨⟨m, ⟨hmp, hmn⟩, rfl⟩, hroot⟩
    refine ⟨m, hmp, hmn, rfl, ?_⟩
    simpa [Polynomial.IsRoot] using hroot
  -- `den` nonvanishing on `T` (tame primes are `> n ≥ 0`, in particular `> 1`).
  have hden_T : ∀ a ∈ T, den.eval a ≠ 0 := by
    intro a ha
    obtain ⟨m, hmp, hmn, rfl, _⟩ := hmem a ha
    have h1 : 1 < m := hmp.one_lt
    exact (hL6 m h1).1
  -- `tden` nonvanishing on `T` (by construction we removed its roots).
  have htden_T : ∀ a ∈ T, tden.eval a ≠ 0 := by
    intro a ha
    obtain ⟨_, _, _, _, h⟩ := hmem a ha
    exact h
  -- Agreement of the two rational functions on `T`, via the common density value.
  have hagree_T : ∀ a ∈ T, num.eval a / den.eval a = tnum.eval a / tden.eval a := by
    intro a ha
    obtain ⟨m, hmp, hmn, rfl, _⟩ := hmem a ha
    have h1 : 1 < m := hmp.one_lt
    -- both equal `F.density n σ m`
    have hL := (hL6 m h1).2
    have hR := htame m hmp hmn
    rw [← hL, ← hR]
  -- Apply the algebraic core (identity theorem for `ℚ(t)`).
  exact ratfunc_agree_of_infinite num den tnum tden T hT_inf hden_T htden_T hagree_T

end LeanUrat.L7
