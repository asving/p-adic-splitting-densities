/-
Unit C3.widthConfine — moves_ref: §C DOM(3)/C.1.0(b)(ii) (W): the factor interior lies inside
the read side's span — μ·e·g ≤ wSide from the recorded node data alone.

childWidth = e·g·Dwidth, so the claim reduces to μ·e·g ≤ wSide.  Ranch ≠ 0 (its constant
coefficient is pat 0 ≠ 0, hpat0); natDegree Ranch ≤ wSide/e (hRanch writes Ranch as a sum of
monomials of degree ≤ wSide/e); ψ^μ ∣ Ranch (hOrd.1) with ψ of degree g gives
μ·g = natDegree(ψ^μ) ≤ natDegree Ranch ≤ wSide/e (Polynomial.natDegree_le_of_dvd); multiply by
e and use hEdvd (e·(wSide/e) = wSide), then by Dwidth.
-/
import LeanUrat.MovesC.Defs

namespace LeanUrat.MovesC

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem C3_widthConfine (ν : Node p F) : ν.μ * ν.childWidth ≤ ν.wSide * ν.Dwidth := by
  -- Ranch is nonzero: its constant term is pat 0 ≠ 0.
  have hRne : ν.Ranch ≠ 0 := by
    have hc : ν.Ranch.coeff 0 = ν.pat 0 := by
      rw [ν.hRanch, Polynomial.finsetSum_coeff]
      simp [Polynomial.coeff_X_pow]
    intro h0
    apply ν.hpat0
    rw [← hc, h0, Polynomial.coeff_zero]
  -- natDegree Ranch ≤ wSide/e, since Ranch is a sum of monomials of degree ≤ wSide/e.
  have hdegR : ν.Ranch.natDegree ≤ ν.wSide / ν.e := by
    rw [ν.hRanch]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    rw [Finset.mem_range] at hk
    exact (Polynomial.natDegree_C_mul_X_pow_le (ν.pat k) k).trans (by omega)
  -- (ψ^μ).natDegree = μ·g.
  have hpow : (ν.ψ ^ ν.μ).natDegree = ν.μ * ν.g := by
    rw [Polynomial.natDegree_pow, ν.hψdeg]
  -- ψ^μ ∣ Ranch (hOrd.1) ⇒ μ·g ≤ natDegree Ranch ≤ wSide/e.
  have hle : ν.μ * ν.g ≤ ν.wSide / ν.e := by
    have h1 : (ν.ψ ^ ν.μ).natDegree ≤ ν.Ranch.natDegree :=
      Polynomial.natDegree_le_of_dvd ν.hOrd.1 hRne
    rw [hpow] at h1
    exact h1.trans hdegR
  -- Multiply by e, cancel using hEdvd (e·(wSide/e) = wSide).
  have hcancel : ν.e * (ν.wSide / ν.e) = ν.wSide := Nat.mul_div_cancel' ν.hEdvd
  have hkey : ν.e * (ν.μ * ν.g) ≤ ν.wSide := by
    calc ν.e * (ν.μ * ν.g) ≤ ν.e * (ν.wSide / ν.e) := Nat.mul_le_mul le_rfl hle
      _ = ν.wSide := hcancel
  -- Finish: multiply by Dwidth (childWidth = e·g·Dwidth definitionally).
  show ν.μ * (ν.e * ν.g * ν.Dwidth) ≤ ν.wSide * ν.Dwidth
  calc ν.μ * (ν.e * ν.g * ν.Dwidth)
      = (ν.e * (ν.μ * ν.g)) * ν.Dwidth := by ring
    _ ≤ ν.wSide * ν.Dwidth := Nat.mul_le_mul hkey le_rfl

end LeanUrat.MovesC
