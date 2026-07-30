/-
Unit C3.vtxPolyNe — moves_ref: §C.0 the transported vertex value's polynomial factor is NONZERO
(ord exact). ROUND 3 note: Node.vtx now carries m̂ = −t·h·g at the NODE's recorded read Bézout
pair (F10 fixed); this unit is unchanged (bare polynomials).

If (Ranch /ₘ ψ^μ) %ₘ ψ = 0 then ψ ∣ (Ranch /ₘ ψ^μ); combined with Ranch = ψ^μ·(Ranch /ₘ ψ^μ)
(ψ^μ ∣ Ranch, hord.1) this gives ψ^{μ+1} ∣ Ranch, contradicting hord.2.
-/
import LeanUrat.MovesC.Defs

namespace LeanUrat.MovesC

open Polynomial LeanUrat.Moves

theorem C3_vtxPolyNe {K : Type*} [Field K] (ψ Ranch : Polynomial K) (μ : ℕ) (hmonic : ψ.Monic) (hdeg : 0 < ψ.natDegree) (hord : OrdPsiPoly ψ Ranch μ) : (Ranch /ₘ ψ ^ μ) %ₘ ψ ≠ 0 := by
  intro hzero
  have hpow : (ψ ^ μ).Monic := hmonic.pow μ
  -- ψ^μ ∣ Ranch (hord.1) ⇒ Ranch %ₘ ψ^μ = 0, so Ranch = ψ^μ · (Ranch /ₘ ψ^μ).
  have hmod0 : Ranch %ₘ ψ ^ μ = 0 := (modByMonic_eq_zero_iff_dvd hpow).mpr hord.1
  have hRanch : Ranch = ψ ^ μ * (Ranch /ₘ ψ ^ μ) := by
    have h := modByMonic_add_div Ranch (ψ ^ μ)
    rw [hmod0, zero_add] at h
    exact h.symm
  -- hzero : (Ranch /ₘ ψ^μ) %ₘ ψ = 0 ⇒ ψ ∣ (Ranch /ₘ ψ^μ).
  obtain ⟨e, he⟩ := (modByMonic_eq_zero_iff_dvd hmonic).mp hzero
  -- Then ψ^{μ+1} ∣ Ranch, contradicting hord.2.
  exact hord.2 ⟨e, by rw [hRanch, he, pow_succ]; ring⟩
