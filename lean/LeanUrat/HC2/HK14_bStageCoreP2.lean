/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC2.HK13_bStageCoreP1a
import LeanUrat.Moves.ResVal

/-!
# HC2.HK14_bStageCoreP2 — HK-14: `StageCoreL` at the gate base stage, part 2

Bridge campaign BP2 (`lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md`, Block G, unit HK-14).
E-PHASE SKELETON: statements with `sorry` bodies; P-phase proves (hard-fable, est. ~120
lines).

**Unit HK-14** — blueprint statement: "`StageCoreL bStage` part 2 — `TvecUnitLaw` +
`CoeffLocLaw` at bStage: the degree-0 subring argument at a concrete 1-variable stage
(K = prime subfield; closure computations go through `Subring.closure` induction)."

CARRIER RESOLUTION: stated at `bStageP` (the HK-13 base-pin re-dress of `U31.bStage`),
per the transcription finding recorded in `HK13_bStageCoreP1a.lean`'s module header.
At `bStageP`: `Tvec = [(C 2, 1)]`, `t = 0`, `grRes (C 2) = C (bR (C 2)) · T (bw (C 2))
= C 1 · T 1 = T 1 = locT` — the T-provenance is carried by the single genuine
representative `C 2`.

HOSTING RESOLUTION (recorded): `StageCore`'s remaining field `tvec : TvecLaw σ` (the
round-4 two-sided product law) is named by NO unit of the blueprint's HK-13/HK-56/HK-14
split; it is hosted HERE with the T-vector machinery it shares with `TvecUnitLaw`
(minimal resolution — HK-16's `StageCore` assembly needs all eleven fields).

Statement shapes = `StageCore.tvec` / `StageCoreL.tvec_unit` / `StageCoreL.coeff_loc`
field types at `σ := bStageP`.

deps: HK-13 (carrier lemmas).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves

/-! ### `HK14R` — local helpers (units of the concrete localization `LTwo` at the gate
base stage; the K1_vertexPin `mUnit` toolkit is `private` there, so the three needed
units are built directly). -/
namespace HK14R

lemma hC2cast : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num

/-- The single representative of `bStageP` (any `Fin`-indexed access). -/
lemma reps_get (i : Fin bStageP.reps.length) :
    bStageP.reps.get i = Polynomial.C ((2 : ℕ) : ℤ_[2]) := by
  have hmem : bStageP.reps.get i ∈ [Polynomial.C ((2 : ℕ) : ℤ_[2])] :=
    bStageP.reps.get_mem i
  rw [List.mem_singleton] at hmem
  exact hmem

/-- The single T-vector entry of `bStageP` (any `Fin`-indexed access). -/
lemma tvec_get (i : Fin bStageP.Tvec.length) :
    bStageP.Tvec.get i = (Polynomial.C ((2 : ℕ) : ℤ_[2]), (1 : ℤ)) := by
  have hmem : bStageP.Tvec.get i ∈ [(Polynomial.C ((2 : ℕ) : ℤ_[2]), (1 : ℤ))] :=
    bStageP.Tvec.get_mem i
  rw [List.mem_singleton] at hmem
  exact hmem

/-- The outer-T unit (= `locT`), the graded unit of the representative `C 2`
(`grRes (C 2) = C 1 · T 1 = T 1`). -/
noncomputable def tU1 : (LTwo ↥bStageP.K)ˣ := locT ↥bStageP.K

/-- The mixed unit `C (T 1) · T 1` — the graded unit of the key `X`
(`grRes X = C (T 1) · T 1`: inner position 1, outer weight 1). -/
noncomputable def uYb : (LTwo ↥bStageP.K)ˣ where
  val := LaurentPolynomial.C (LaurentPolynomial.T 1) * LaurentPolynomial.T 1
  inv := LaurentPolynomial.C (LaurentPolynomial.T (-1)) * LaurentPolynomial.T (-1)
  val_inv := by
    rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add, add_neg_cancel,
      LaurentPolynomial.T_zero, map_one, one_mul, ← LaurentPolynomial.T_add,
      add_neg_cancel, LaurentPolynomial.T_zero]
  inv_val := by
    rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add, neg_add_cancel,
      LaurentPolynomial.T_zero, map_one, one_mul, ← LaurentPolynomial.T_add,
      neg_add_cancel, LaurentPolynomial.T_zero]

lemma huY : IsGrUnit bStageP bStageP.Φ uYb := by
  show (LaurentPolynomial.C (LaurentPolynomial.T 1) * LaurentPolynomial.T 1 :
      LTwo ↥bStageP.K)
    = LaurentPolynomial.C (bStageP.R bStageP.Φ) * LaurentPolynomial.T (bStageP.w bStageP.Φ)
  have hR : bStageP.R bStageP.Φ = LaurentPolynomial.T 1 := HK13R.bR_X
  have hw : bStageP.w bStageP.Φ = 1 := HK13R.bw_X
  rw [hR, hw]

lemma hu2 : IsGrUnit bStageP (Polynomial.C ((2 : ℕ) : ℤ_[2])) tU1 := by
  show (LaurentPolynomial.T 1 : LTwo ↥bStageP.K)
    = LaurentPolynomial.C (bStageP.R (Polynomial.C ((2 : ℕ) : ℤ_[2]))) *
        LaurentPolynomial.T (bStageP.w (Polynomial.C ((2 : ℕ) : ℤ_[2])))
  have hR : bStageP.R (Polynomial.C ((2 : ℕ) : ℤ_[2])) = 1 := by
    rw [hC2cast]
    exact HK13R.bR_C2
  have hw : bStageP.w (Polynomial.C ((2 : ℕ) : ℤ_[2])) = 1 := by
    rw [hC2cast]
    exact HK13R.bw_C2
  rw [hR, hw, map_one, one_mul]

end HK14R

/-- HK-14 (hosted `StageCore.tvec` shape — see the module-header hosting resolution): the
round-4 T-vector product law at the gate base stage — `w tvecNum = w tvecDen + 1` and
`R tvecNum = R tvecDen`.  At `bStageP`: `tvecNum = C 2` (exponent 1⁺, `Φ^{t⁺} = X⁰`),
`tvecDen = 1`; concretely `bw (C 2) = 1 = bw 1 + 1` and `bR (C 2) = 1 = bR 1`.
[Blueprint BP2 HK-14 (hosted); deps: HK-13.] -/
theorem bStageP_tvecLaw : TvecLaw bStageP := by
  have hnum : bStageP.tvecNum = Polynomial.C ((2 : ℕ) : ℤ_[2]) := by
    show ([(Polynomial.C ((2 : ℕ) : ℤ_[2]), (1 : ℤ))].map (fun q => q.1 ^ q.2.toNat)).prod *
        (X : Polynomial ℤ_[2]) ^ ((0 : ℤ)).toNat = Polynomial.C ((2 : ℕ) : ℤ_[2])
    simp
  have hden : bStageP.tvecDen = 1 := by
    show ([(Polynomial.C ((2 : ℕ) : ℤ_[2]), (1 : ℤ))].map (fun q => q.1 ^ (-q.2).toNat)).prod *
        (X : Polynomial ℤ_[2]) ^ ((-(0 : ℤ)).toNat) = 1
    simp
  constructor
  · rw [hnum, hden]
    have h1 : bStageP.w (Polynomial.C ((2 : ℕ) : ℤ_[2])) = 1 := by
      rw [HK14R.hC2cast]
      exact HK13R.bw_C2
    have h0 : bStageP.w (1 : Polynomial ℤ_[2]) = 0 := HK13R.bw_one
    rw [h1, h0]
    norm_num
  · rw [hnum, hden]
    have h1 : bStageP.R (Polynomial.C ((2 : ℕ) : ℤ_[2])) = 1 := by
      rw [HK14R.hC2cast]
      exact HK13R.bR_C2
    have h0 : bStageP.R (1 : Polynomial ℤ_[2]) = 1 := HK13R.bR_one
    rw [h1, h0]

/-- HK-14 (`StageCoreL.tvec_unit` shape): **the T-vector product law at the actual unit**
(demand 1) — graded units `uY` for `Φ = X` and `ru` for the single representative `C 2`
with `ru₀¹ · uY⁰ = locT K₂` in `L = L₀[T^{±1}]` (at `bStageP`: `grRes (C 2) = T 1 = locT`,
`t = 0`).  [Blueprint BP2 HK-14; deps: HK-13.] -/
theorem bStageP_tvecUnitLaw : TvecUnitLaw bStageP := by
  refine ⟨HK14R.uYb, fun _ => HK14R.tU1, HK14R.huY, fun i => ?_, ?_⟩
  · rw [HK14R.tvec_get i]
    exact HK14R.hu2
  · show (∏ i : Fin bStageP.Tvec.length,
        (fun _ => HK14R.tU1) i ^ ((bStageP.Tvec.get i).2)) * HK14R.uYb ^ bStageP.t
      = locT ↥bStageP.K
    have hprod : (∏ i : Fin bStageP.Tvec.length,
        (fun _ => HK14R.tU1) i ^ ((bStageP.Tvec.get i).2)) = HK14R.tU1 ^ (1 : ℤ) :=
      Fin.prod_univ_one _
    have ht : bStageP.t = (0 : ℤ) := rfl
    rw [hprod, zpow_one, ht, zpow_zero, mul_one]
    rfl

/-- HK-14 (`StageCoreL.coeff_loc` shape): **(S4) of the actual coefficient localization**
(demand 2) — the degree-0 part of `coeffLocSR` is exactly the `K₂`-constants (the
`Subring.closure` induction at the concrete 1-variable stage; K = prime subfield), and
the `z`-pinning: `z = V^{−h}·Y^{e}` realized by a degree-0 formal monomial vector (at
`bStageP`: `v = ((−1), 1)` over `reps = [C 2]` — weight `−1·1 + 1·1 = 0`, value
`(T 1)⁻¹ · (grRes X) = C z`).  [Blueprint BP2 HK-14; deps: HK-13.] -/
theorem bStageP_coeffLocLaw : CoeffLocLaw bStageP := by
  refine ⟨?_, ?_, ?_⟩
  · -- (a) degree-0 part ⊆ K: the localization sits inside the inner-constant subring,
    -- the range of the coefficientwise inner-C ring hom φ
    intro ℓ hℓ
    set φ : LaurentPolynomial ↥bStageP.K →+* LTwo ↥bStageP.K :=
      AddMonoidAlgebra.mapRingHom ℤ
        (LaurentPolynomial.C : ↥bStageP.K →+* LaurentPolynomial ↥bStageP.K) with hφdef
    have hφT : ∀ n : ℤ, φ (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
      intro n
      have h1 : (LaurentPolynomial.T n : LaurentPolynomial ↥bStageP.K)
          = AddMonoidAlgebra.single n 1 := by
        rw [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
      have h2 : (LaurentPolynomial.T n : LTwo ↥bStageP.K)
          = AddMonoidAlgebra.single n 1 := by
        rw [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
      rw [h1, hφdef, AddMonoidAlgebra.mapRingHom_single, map_one, h2]
    have hsub : bStageP.coeffLocSR ≤ φ.range := by
      refine Subring.closure_le.mpr ?_
      rintro x (⟨B, hB0, hBin, rfl⟩ | ⟨i, u, hu, rfl⟩)
      · have hc : B = Polynomial.C (B.coeff 0) := U31.is_const hBin
        have hb : B.coeff 0 ≠ 0 := fun h => hB0 (by rw [hc, h, map_zero])
        have hR : bStageP.R B = 1 := by
          rw [hc]
          exact HK13R.bR_const hb
        have hgr : bStageP.grRes B = LaurentPolynomial.T (bStageP.w B) := by
          rw [Stage.grRes, hR, map_one, one_mul]
        rw [hgr]
        exact ⟨LaurentPolynomial.T (bStageP.w B), hφT _⟩
      · have hR2 : bStageP.R (Polynomial.C ((2 : ℕ) : ℤ_[2])) = 1 := by
          rw [HK14R.hC2cast]
          exact HK13R.bR_C2
        have hw2 : bStageP.w (Polynomial.C ((2 : ℕ) : ℤ_[2])) = 1 := by
          rw [HK14R.hC2cast]
          exact HK13R.bw_C2
        have hval : (u : LTwo ↥bStageP.K) = LaurentPolynomial.T 1 := by
          rw [hu, HK14R.reps_get i, Stage.grRes, hR2, hw2, map_one, one_mul]
        have hinv : ((u⁻¹ : (LTwo ↥bStageP.K)ˣ) : LTwo ↥bStageP.K)
            = LaurentPolynomial.T (-1) := by
          have hu' : u = tUnit (LaurentPolynomial ↥bStageP.K) 1 := Units.ext hval
          have hti : (tUnit (LaurentPolynomial ↥bStageP.K) 1)⁻¹
              = tUnit (LaurentPolynomial ↥bStageP.K) (-1) := by
            refine inv_eq_of_mul_eq_one_right ?_
            apply Units.ext
            show LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1) = 1
            rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
          rw [hu', hti]
          rfl
        rw [hinv]
        exact ⟨LaurentPolynomial.T (-1), hφT _⟩
    obtain ⟨y, hy⟩ := hsub hℓ
    refine ⟨y (0 : ℤ), ?_⟩
    have h1 : φ y (0 : ℤ) = LaurentPolynomial.C (y (0 : ℤ)) := by
      rw [hφdef]
      exact AddMonoidAlgebra.mapRingHom_apply _ _ _
    have h2 : (LaurentPolynomial.C ℓ : LTwo ↥bStageP.K) (0 : ℤ) = ℓ := by
      have hs : (LaurentPolynomial.C ℓ : LTwo ↥bStageP.K)
          = AddMonoidAlgebra.single (0 : ℤ) ℓ := (LaurentPolynomial.single_eq_C ℓ).symm
      rw [hs]
      exact Finsupp.single_eq_same
    calc ℓ = (LaurentPolynomial.C ℓ : LTwo ↥bStageP.K) (0 : ℤ) := h2.symm
      _ = φ y (0 : ℤ) := by rw [hy]
      _ = LaurentPolynomial.C (y (0 : ℤ)) := h1
  · -- (b) K-constants lie in the subring: K₂ = {0, 1}
    intro d
    rcases bStageP_K_cases d with hd | hd
    · rw [hd, map_zero, map_zero]
      exact Subring.zero_mem _
    · rw [hd, map_one, map_one]
      exact Subring.one_mem _
  · -- (c) the z-pinning: z = V^{-1}·Y at the vector ((-1), 1)
    refine ⟨(fun _ => (-1 : ℤ), (1 : ℤ)), (HK14R.tU1)⁻¹ * HK14R.uYb, ?_, ?_, ?_⟩
    · show (∑ i : Fin bStageP.reps.length, (-1 : ℤ) * bStageP.w (bStageP.reps.get i))
          + (1 : ℤ) * (bStageP.h : ℤ) = 0
      have hwc : ∀ i : Fin bStageP.reps.length,
          (-1 : ℤ) * bStageP.w (bStageP.reps.get i) = -1 := by
        intro i
        rw [HK14R.reps_get i]
        have hw2 : bStageP.w (Polynomial.C ((2 : ℕ) : ℤ_[2])) = 1 := by
          rw [HK14R.hC2cast]
          exact HK13R.bw_C2
        rw [hw2, mul_one]
      rw [Finset.sum_congr rfl (fun i _ => hwc i), Finset.sum_const]
      have hcard : (Finset.univ : Finset (Fin bStageP.reps.length)).card = 1 := by
        rw [Finset.card_univ, Fintype.card_fin]
        rfl
      rw [hcard, one_smul]
      have hh : bStageP.h = 1 := rfl
      rw [hh]
      norm_num
    · refine ⟨fun _ => HK14R.tU1, HK14R.uYb, fun i => ?_, HK14R.huY, ?_⟩
      · rw [HK14R.reps_get i]
        exact HK14R.hu2
      · show (HK14R.tU1)⁻¹ * HK14R.uYb
            = (∏ i : Fin bStageP.reps.length, (fun _ => HK14R.tU1) i ^ (-1 : ℤ))
              * HK14R.uYb ^ (1 : ℤ)
        have hp : (∏ i : Fin bStageP.reps.length, (fun _ => HK14R.tU1) i ^ (-1 : ℤ))
            = HK14R.tU1 ^ (-1 : ℤ) := Fin.prod_univ_one _
        rw [hp, zpow_one, zpow_neg_one]
    · show LaurentPolynomial.T (-1) * (LaurentPolynomial.C (LaurentPolynomial.T 1) *
          LaurentPolynomial.T 1) = LaurentPolynomial.C (zvar ↥bStageP.K)
      rw [mul_left_comm, ← LaurentPolynomial.T_add, neg_add_cancel,
        LaurentPolynomial.T_zero, mul_one]

end LeanUrat.MovesJ
