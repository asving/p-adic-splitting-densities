/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

/-- The base residual (§B2-DEF D.2, base stage).  The residue quotient
`F_Q = 𝔽_p[x]/(φ̄)` is identified with the base field `K0` through the SPECIFIED ring
isomorphism `emb`.  The residual reduces the leading coefficient of `f` mod `p` into the
prime subfield `𝔽_p ↪ AdjoinRoot φ̄`, transports it through `emb`, and places it as the
constant term of a Laurent polynomial over `↥K0`.  This is a ring-hom composite of
`leadingCoeff`, so it is multiplicative in the graded domain `gr = F_Q[π,y]`. -/
noncomputable def baseResidual {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (K0 : Subfield F) (φ : Polynomial ℤ_[p]) (_e _h : ℕ)
    (emb : AdjoinRoot (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) ≃+* ↥K0) :
    Polynomial ℤ_[p] → LaurentPolynomial ↥K0 :=
  fun f => LaurentPolynomial.C
    (emb (algebraMap (ZMod p) (AdjoinRoot (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))
      (PadicInt.toZMod f.leadingCoeff)))

theorem L1_baseResidual_laws {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (K0 : Subfield F) (φ : Polynomial ℤ_[p]) (e h : ℕ) (hmon : φ.Monic) (hd : 1 ≤ φ.natDegree) (he : 1 ≤ e) (hh : 1 ≤ h) (hcop : Nat.gcd e h = 1) (hirred : Irreducible (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p))) (emb : AdjoinRoot (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) ≃+* ↥K0) (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0) : baseResidual K0 φ e h emb (f * g) = baseResidual K0 φ e h emb f * baseResidual K0 φ e h emb g := by
  simp only [baseResidual, Polynomial.leadingCoeff_mul, map_mul]

end LeanUrat.Moves
