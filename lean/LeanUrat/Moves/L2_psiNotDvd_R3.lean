/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.L2_widthBound
import LeanUrat.Moves.L0_GRg

/-!
# Moves/L2 — ψ ∤ R(B) for B ∈ Ĉ∖0  (MOVES §D.3(d), ~2053-2055)  [ROUND 3]

Audit repair (round-2 was FAITHLESS: `ψ ≠ X` alone does NOT exclude `ψ = cX`, which would make
`toLaurent ψ` a UNIT).  R3 adds `hmon : ψ.Monic`, so monic + irreducible + `ψ ≠ X` pins `ψ` to a
genuine degree-`g` prime of `↥K[X]` not associated to `X`; hence `toLaurent ψ` is a non-unit and
divides no residual of a below-width coefficient.

Proof: `L2_widthBound` puts `supp(R B)` in a window `[a, a+g)`; `L0_GRg` writes
`R B = T a · toLaurent Ranch` with `Ranch ≠ 0`, `deg Ranch < g`.  If `toLaurent ψ ∣ R B` then,
dividing out the unit `T a`, `toLaurent ψ ∣ toLaurent Ranch`; clearing `X`-denominators
(`exists_T_pow`) and using injectivity of `toLaurent` gives `ψ ∣ Ranch · X^n` in `↥K[X]`.  `ψ` is
prime and `ψ ∤ X` (else `ψ = X`), so `ψ ∣ Ranch`, forcing `g = deg ψ ≤ deg Ranch < g` — absurd.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

theorem L2_psiNotDvd {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hBdeg : B.natDegree < σ.e * g * σ.Φ.natDegree) : ¬ (Polynomial.toLaurent ψ ∣ σ.R B) := by
  classical
  intro hdvd
  -- `g ≥ 1` since ψ is irreducible over a field.
  have hgpos : 0 < ψ.natDegree := hψ.natDegree_pos
  have hg1 : 1 ≤ g := by omega
  -- width window + anchored-polynomial form of R(B)
  obtain ⟨a, ha⟩ := L2_widthBound σ g hg1 B hB hBdeg
  obtain ⟨Ranch, hRdeg, hRB⟩ := L0_GRg (σ.hRne B hB) a g ha
  have hRanch_ne : Ranch ≠ 0 := by
    intro h
    rw [h, map_zero, mul_zero] at hRB
    exact σ.hRne B hB hRB
  -- divide out the unit `T a`: `toLaurent ψ ∣ toLaurent Ranch`
  have hdvdR : Polynomial.toLaurent ψ ∣ Polynomial.toLaurent Ranch := by
    have h := hdvd.mul_left (LaurentPolynomial.T (-a))
    rwa [hRB, ← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel,
      LaurentPolynomial.T_zero, one_mul] at h
  obtain ⟨q, hq⟩ := hdvdR
  obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow q
  -- clear `X`-denominators and reflect divisibility back to `↥K[X]`
  have hkey : Ranch * Polynomial.X ^ n = ψ * f' := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, map_mul, Polynomial.toLaurent_X_pow, hq, mul_assoc, ← hf']
  have hdiv : ψ ∣ Ranch * Polynomial.X ^ n := ⟨f', hkey⟩
  have hprime : Prime ψ := hψ.prime
  -- ψ ∤ X, else monic + associated ⟹ ψ = X
  have hnotdvdX : ¬ (ψ ∣ Polynomial.X) := by
    intro hdX
    exact hψz (Polynomial.eq_of_monic_of_associated hmon Polynomial.monic_X
      (hψ.associated_of_dvd Polynomial.irreducible_X hdX))
  rcases hprime.dvd_or_dvd hdiv with h1 | h2
  · have hle := Polynomial.natDegree_le_of_dvd h1 hRanch_ne
    omega
  · exact hnotdvdX (hprime.dvd_of_dvd_pow h2)

end LeanUrat.Moves
