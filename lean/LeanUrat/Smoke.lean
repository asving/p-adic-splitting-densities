import Mathlib

/-!
Smoke test: confirm the formalization dev loop works by stating/closing real facts that the
uniform-rationality proof depends on. No `sorry`.
-/

open Polynomial

-- BB3 cornerstone: every finite field is perfect (Frobenius bijective) => no inseparable
-- irreducibles => "repeated factor = non-squarefree = discriminant locus" in every characteristic.
example (K : Type*) [Field K] [Finite K] : PerfectField K := inferInstance

-- Consequence we use: over a finite (hence perfect) field, an irreducible polynomial is separable.
example (K : Type*) [Field K] [Finite K] (p : K[X]) (hp : Irreducible p) : p.Separable :=
  PerfectField.separable_of_irreducible hp

-- L7 cornerstone: a polynomial over an infinite integral domain is determined by its values.
-- (Robust formulation via the roots of f - g; underlies the "agree at infinitely many tame
-- primes => equal in Q(t)" interpolation.)
example (R : Type*) [CommRing R] [IsDomain R] [Infinite R] (f g : R[X])
    (h : ∀ x : R, f.eval x = g.eval x) : f = g := by
  have hsub : f - g = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have : {x : R | (f - g).IsRoot x} = Set.univ := by
      ext x; simp [Polynomial.IsRoot, sub_eq_zero, h x]
    rw [this]; exact Set.infinite_univ
  exact sub_eq_zero.mp hsub
