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
    (h : ∀ x : R, f.eval x = g.eval x) : f = g :=
  Polynomial.funext h
