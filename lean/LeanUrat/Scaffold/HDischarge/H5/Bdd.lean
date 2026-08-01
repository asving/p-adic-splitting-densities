/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H5.RowSigma
import LeanUrat.Scaffold.HDischarge.H5.PackI

/-!
# Scaffold/HDischarge/H5/Bdd — Wave-3 (PACK-ii) bounds [HDISCHARGE_H5 units B1, B2]

Statements VERBATIM from `lean/blueprints/HDISCHARGE_H5.md` §4.5.

Unit B1: `beta_eval_nonneg` — every solved leg evaluates ≥ 0 at every rational
pool q₀ ≥ 2 (HARD; strong induction on e with q₀ generalized INSIDE the
induction — the leaf §2A.2 display: "uniform in q₀ … so the induction
hypothesis applies at the child pools q₀^{D_i}"). PROVED (prover B1):
* e ≤ 1: (BASE nonneg) = `M.base_nonneg`.
* 2 ≤ e ≤ n: `hsolve` presents β_e(σ) = u⁻¹·t_σ inside `OKat q₀`. The
  canonical row t_σ (fired via `W.trow_canonical`) is the finite double sum
  Σ_F Σ_τ m(F)·∏ᵢ powSubst Dᵢ (β_{μᵢ}(τᵢ)); each factor evaluates nonneg —
  the mass by (MNN) = `M.mass_nonneg` (membership binder from
  `M.mass_memRcyc` + K1 `memRcyc_mem_OKat`, the per-stratum regularity),
  each leg by the IH at the CHILD POOL q₀^{Dᵢ} (2 ≤ q₀ ≤ q₀^D by
  `le_self_pow`, D ≥ 1; μᵢ < e by `W.handoff_lt`; membership by K2b)
  transported THROUGH `powSubst_evalAt`. The pivot u evaluates positively by
  P0 (`solveU_eval_pos`, fired through `T.hblockU` + `W.booking_reentrant`),
  so the leg evaluates as nonneg row over positive pivot (K3 `evalAt_inv`).

Unit B2: `beta_eval_mem_Icc` — each evaluated β lands in [0,1]: nonnegativity
is B1 at the given σ, and the upper bound is one nonneg term (B1 at every σ')
of the evaluated row total, which is 1 by R3 (`rowSigma_eval`). Membership
binders from K2b (`bnMember_beta_mem_OKat`). Lands (PACK-ii) CONDITIONAL at
`REWitness`+`MassFacts` members (blueprint §1 door table, §2.3) — no ROOT
retirement claim.
-/

namespace LeanUrat.Scaffold.HDischarge.H5

open LeanUrat.MovesU (MemRcyc SplittingType)
open LeanUrat.MovesS (OKat evalAt powSubst powSubst_OKat powSubst_evalAt)

/-- **Unit B1** (evaluated nonnegativity): every solved leg β_e(σ), e ≤ n,
evaluates nonnegatively at every rational pool q₀ ≥ 2. The pool quantifier
sits INSIDE the induction (the IH must fire at the base-changed child pools
q₀^{D_i}); `e ≤ n` is REQUIRED (`mass_complete` supplies nothing above n).
Route: strong induction on e — `hsolve` → nonneg t (masses (MNN) × legs via
IH through `powSubst_evalAt` at the child pools) over positive pivot (P0).
[HDISCHARGE_H5 unit B1 — statement VERBATIM §4.5] -/
theorem beta_eval_nonneg {n : ℕ} (T : BnMember n) (W : REWitness T)
    (M : MassFacts T W) :
    ∀ e, e ≤ n → ∀ σ (q₀ : ℚ), 2 ≤ q₀ →
      ∀ h : T.β e σ ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨T.β e σ, h⟩ := by
  classical
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro hen σ q₀ hq h
    rcases Nat.lt_or_ge e 2 with he | he
    -- (BASE nonneg): e ≤ 1 fires the `MassFacts` base field.
    · exact M.base_nonneg e (Nat.lt_succ_iff.mp he) σ q₀ hq h
    -- 2 ≤ e: split the solve β_e(σ) = u⁻¹·t_σ inside the subring.
    · -- pivot memberships (K1 through the block's ℛ-data)
      have hu_mem : (T.blocks e he).u ∈ OKat q₀ :=
        memRcyc_mem_OKat (T.blocks e he).hu.2.1 hq
      have hui_mem : (T.blocks e he).u⁻¹ ∈ OKat q₀ :=
        memRcyc_mem_OKat (T.blocks e he).hu.2.2 hq
      -- row membership, transported from β's through the solve (t = u·β)
      have htrow_eq : (T.blocks e he).trow σ
          = (T.blocks e he).u * T.β e σ := by
        rw [(T.blocks e he).hsolve σ, ← mul_assoc,
          mul_inv_cancel₀ (T.blocks e he).hu.1, one_mul]
      have ht_mem : (T.blocks e he).trow σ ∈ OKat q₀ := by
        rw [htrow_eq]; exact (OKat q₀).mul_mem hu_mem h
      -- the solve, as subring elements
      have hsplit : (⟨T.β e σ, h⟩ : OKat q₀)
          = ⟨(T.blocks e he).u⁻¹, hui_mem⟩
            * ⟨(T.blocks e he).trow σ, ht_mem⟩ :=
        Subtype.ext ((T.blocks e he).hsolve σ)
      -- pivot positivity (P0, fired through hblockU + booking_reentrant)
      have hsu_mem : T.booking.solveU e ∈ OKat q₀ := by
        rw [← T.hblockU e he]; exact hu_mem
      have hupos : 0 < evalAt q₀ ⟨(T.blocks e he).u, hu_mem⟩ := by
        have hcast : (⟨(T.blocks e he).u, hu_mem⟩ : OKat q₀)
            = ⟨T.booking.solveU e, hsu_mem⟩ := Subtype.ext (T.hblockU e he)
        rw [hcast]
        exact solveU_eval_pos he T.booking W.booking_reentrant hq hsu_mem
      -- per-stratum mass memberships ((MNN) binder: mass_memRcyc + K1)
      have hm_mem : ∀ F : (W.exits e).idx, (W.exits e).mass F ∈ OKat q₀ :=
        fun F => memRcyc_mem_OKat (M.mass_memRcyc e F) hq
      -- child pools stay ≥ 2 (2 ≤ q₀ ≤ q₀^D, D ≥ 1)
      have hpool : ∀ δ : ℕ+, (2 : ℚ) ≤ q₀ ^ (δ : ℕ) := fun δ =>
        le_trans hq (le_self_pow₀ (le_trans one_le_two hq) δ.pos.ne')
      -- leg memberships at the child pools (K2b)
      have hleg_mem : ∀ (μ : ℕ) (δ : ℕ+) (σ' : SplittingType n),
          T.β μ σ' ∈ OKat (q₀ ^ (δ : ℕ)) :=
        fun μ δ σ' => bnMember_beta_mem_OKat T μ σ' _ (hpool δ)
      -- the canonical row, assembled inside the subring
      have hsubsum : (⟨(T.blocks e he).trow σ, ht_mem⟩ : OKat q₀)
          = ∑ F : (W.exits e).idx,
              ∑ τ ∈ Finset.univ.filter
                  (fun τ => (W.exits e).comp F τ = σ),
                (⟨(W.exits e).mass F, hm_mem F⟩ : OKat q₀) *
                ∏ i : Fin ((W.exits e).handoff F).length,
                  ⟨powSubst (((W.exits e).handoff F).get i).2
                      (T.β (((W.exits e).handoff F).get i).1 (τ i)),
                    powSubst_OKat _ q₀ _
                      (hleg_mem (((W.exits e).handoff F).get i).1
                        (((W.exits e).handoff F).get i).2 (τ i))⟩ := by
        refine Subtype.ext ?_
        push_cast
        rw [congrFun (W.trow_canonical e he) σ]
        simp only [tRow, rowOf]
      -- the row's eval is nonneg: masses (MNN) × legs (IH at child pools)
      have htnn : 0 ≤ evalAt q₀ ⟨(T.blocks e he).trow σ, ht_mem⟩ := by
        rw [hsubsum, map_sum]
        refine Finset.sum_nonneg fun F _ => ?_
        rw [map_sum]
        refine Finset.sum_nonneg fun τ _ => ?_
        rw [map_mul]
        refine mul_nonneg (M.mass_nonneg e F q₀ hq (hm_mem F)) ?_
        rw [map_prod]
        refine Finset.prod_nonneg fun i _ => ?_
        rw [powSubst_evalAt]
        exact ih (((W.exits e).handoff F).get i).1
          (W.handoff_lt e F _ (((W.exits e).handoff F).get_mem i))
          (le_of_lt (lt_of_lt_of_le
            (W.handoff_lt e F _ (((W.exits e).handoff F).get_mem i)) hen))
          (τ i) _ (hpool _) (hleg_mem _ _ (τ i))
      -- close: nonneg row over positive pivot (K3 inverse law)
      rw [hsplit, map_mul, evalAt_inv hu_mem hui_mem (ne_of_gt hupos)]
      exact mul_nonneg (le_of_lt (inv_pos.mpr hupos)) htnn

/-- **Unit B2** ((PACK-ii) at the member): each evaluated solved leg lies in
[0,1] — nonnegativity is B1, and the upper bound is `Finset.single_le_sum`:
the leg is one nonneg term (B1 at every σ') of the evaluated row total, which
is 1 by R3 (`rowSigma_eval`); the membership binder is transported to K2b's
by proof irrelevance of the `OKat q₀` carrier. [HDISCHARGE_H5 unit B2] -/
theorem beta_eval_mem_Icc {n : ℕ} (T : BnMember n) (W : REWitness T)
    (M : MassFacts T W) {q₀ : ℚ} (hq : 2 ≤ q₀) {e : ℕ} (he : e ≤ n)
    (σ : SplittingType n) (h : T.β e σ ∈ OKat q₀) :
    evalAt q₀ ⟨T.β e σ, h⟩ ∈ Set.Icc (0 : ℚ) 1 := by
  have hpi : (⟨T.β e σ, h⟩ : OKat q₀)
      = ⟨T.β e σ, bnMember_beta_mem_OKat T e σ q₀ hq⟩ := rfl
  rw [Set.mem_Icc]
  refine ⟨beta_eval_nonneg T W M e he σ q₀ hq h, ?_⟩
  calc evalAt q₀ ⟨T.β e σ, h⟩
      ≤ ∑ σ' : SplittingType n,
          evalAt q₀ ⟨T.β e σ', bnMember_beta_mem_OKat T e σ' q₀ hq⟩ := by
        rw [hpi]
        exact Finset.single_le_sum
          (fun σ' _ => beta_eval_nonneg T W M e he σ' q₀ hq
            (bnMember_beta_mem_OKat T e σ' q₀ hq))
          (Finset.mem_univ σ)
    _ = 1 := rowSigma_eval T W M hq he

end LeanUrat.Scaffold.HDischarge.H5
