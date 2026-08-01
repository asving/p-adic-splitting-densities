/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H5.Defs
import LeanUrat.MovesS.PowSubstOK

/-!
# Scaffold/HDischarge/H5/Kernels — Wave-1 kernels [HDISCHARGE_H5 units K1–K4]

Statements VERBATIM from `lean/blueprints/HDISCHARGE_H5.md` §4.3.

Unit K1: `memRcyc_mem_OKat` — the MemRcyc → OKat bridge at every q₀ ≥ 2
(the `MemRcyc.definedAt` skeleton — `MemRcyc.eq_div` presents f = P/s,
`RatFunc.denom_div_dvd` divides the reduced denominator into s, and
`cycS_eval_pos` (L5) kills the zero — retargeted to the `OKat` carrier via
`mem_OKat_iff`). Serves PACK-iii and PACK-i directly.

Unit K3: `evalAt_inv` — the inverse law of the `evalAt` ring hom on `OKat q₀`
(consumed by P1).

Unit K2b: `bnMember_beta_mem_OKat` — every solved leg β_e(σ) of a 𝔅_n member
is evaluation-regular at every rational q₀ ≥ 2 (route: `beta_memRcyc T.hbase
T.blocks` + K1). Consumed by R3 and B2 for their membership binders; discharges
the 𝔅_n side of PACK-iii together with K2a (§2.4).
-/

namespace LeanUrat.Scaffold.HDischarge.H5

open LeanUrat.MovesU (MemRcyc SplittingType cycS_eval_pos)
open LeanUrat.MovesS (OKat evalAt powSubst mem_OKat_iff)

/-- **Unit K1** (the MemRcyc → OKat bridge): every member of ℛ = ℚ[q][𝒮⁻¹]
lies in the evaluation-regular subring `OKat q₀` at every rational q₀ ≥ 2 —
its reduced denominator divides an 𝒮 member (`RatFunc.denom_div_dvd`), which
is strictly positive there (`cycS_eval_pos`, L5). [HDISCHARGE_H5 unit K1] -/
theorem memRcyc_mem_OKat {f : Qq} (hf : MemRcyc f) {q₀ : ℚ} (hq : 2 ≤ q₀) :
    f ∈ OKat q₀ := by
  rw [mem_OKat_iff]
  obtain ⟨P, s, hs, rfl⟩ := hf.eq_div
  obtain ⟨u, hu⟩ := RatFunc.denom_div_dvd P s
  have hpos := cycS_eval_pos hs hq
  rw [hu, Polynomial.eval_mul] at hpos
  intro h0
  rw [h0, zero_mul] at hpos
  exact lt_irrefl 0 hpos

/-- **Unit K4** (telescoping engine for R1 step 1): the σ-sum of the II-R8
verdict rows `rowOf` collapses — `comp`'s fibers partition the tuple space
(`Finset.sum_fiberwise`), and the full tuple sum factors through the pi type
(`Finset.prod_univ_sum`) — to the mass times the product over hand-off legs of
the base-changed lower-β totals. No convergence content: all index types are
finite. [HDISCHARGE_H5 unit K4] -/
theorem sum_rowOf {n : ℕ} (β : ℕ → SplittingType n → Qq) (m : Qq)
    (H : List (ℕ × ℕ+))
    (comp : ((i : Fin H.length) → SplittingType n) → SplittingType n) :
    (∑ σ : SplittingType n, rowOf β m H comp σ)
      = m * ∏ i : Fin H.length,
          (∑ σ' : SplittingType n, powSubst (H.get i).2 (β (H.get i).1 σ')) := by
  classical
  unfold rowOf
  rw [Finset.sum_fiberwise, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.mul_sum]

/-- **Unit K2a** (PACK-iii, entry side): every entry of a 𝔅_n member is
evaluation-regular at every rational pool q₀ ≥ 2 — II-R13
(`BnMember.entries_memRcyc`) puts the entry in ℛ = ℚ[q][𝒮⁻¹], and K1
transports ℛ-membership to the `OKat` carrier. With K2b this discharges
PACK-iii at the 𝔅_n side for the two corpus collections; scope per blueprint
§2.4: the σ-keyed roster identification of REALIZED table rows and the chain
seam stay DISPLAYED open (route-a/route-b territory, never claimed here).
[HDISCHARGE_H5 unit K2a] -/
theorem bnMember_entries_mem_OKat {n : ℕ} (T : BnMember n) :
    ∀ e, ∀ g ∈ T.entries e, ∀ q₀ : ℚ, 2 ≤ q₀ → g ∈ OKat q₀ :=
  fun e g hg _q₀ hq => memRcyc_mem_OKat (T.entries_memRcyc e g hg) hq

/-- **Unit K3** (the inverse law): the `evalAt` ring hom takes inverses to
inverses whenever both `f` and `f⁻¹` are evaluation-regular and the evaluation
of `f` is nonzero. [HDISCHARGE_H5 unit K3] -/
theorem evalAt_inv {q₀ : ℚ} {f : Qq} (hf : f ∈ OKat q₀) (hfi : f⁻¹ ∈ OKat q₀)
    (hne : evalAt q₀ ⟨f, hf⟩ ≠ 0) :
    evalAt q₀ ⟨f⁻¹, hfi⟩ = (evalAt q₀ ⟨f, hf⟩)⁻¹ := by
  by_cases h0 : f = 0
  · exact absurd (by rw [show (⟨f, hf⟩ : OKat q₀) = 0 from Subtype.ext h0, map_zero]) hne
  · have hmul : (⟨f⁻¹, hfi⟩ : OKat q₀) * ⟨f, hf⟩ = 1 :=
      Subtype.ext (inv_mul_cancel₀ h0)
    have hev : evalAt q₀ ⟨f⁻¹, hfi⟩ * evalAt q₀ ⟨f, hf⟩ = 1 := by
      rw [← map_mul, hmul, map_one]
    exact eq_inv_of_mul_eq_one_left hev

/-- **Unit K2b**: every solved leg β_e(σ) of a 𝔅_n member is evaluation-regular
at every rational q₀ ≥ 2 — II-R5 (`beta_memRcyc`, fired from `T.hbase` +
`T.blocks`) puts β_e(σ) in ℛ = ℚ[q][𝒮⁻¹], and K1 (`memRcyc_mem_OKat`) lands ℛ
inside `OKat q₀`. Consumed by R3 and B2 for their membership binders;
discharges the 𝔅_n side of PACK-iii together with K2a (§2.4).
[HDISCHARGE_H5 unit K2b] -/
theorem bnMember_beta_mem_OKat {n : ℕ} (T : BnMember n) :
    ∀ e σ, ∀ q₀ : ℚ, 2 ≤ q₀ → T.β e σ ∈ OKat q₀ :=
  fun e σ _q₀ hq =>
    memRcyc_mem_OKat (beta_memRcyc T.hbase T.blocks e σ) hq

end LeanUrat.Scaffold.HDischarge.H5
