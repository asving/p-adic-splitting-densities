/-
MovesGr HELD-UNIT ROUND (2026-07-27): machine-checked provability certificates + supported
fragments for the five held units (`L4_baseStage_exists`, `L4_base_nonvacuity_gate`,
`L4_TRANSvi`, `L4_TRANSstage`, `L5_recTRANSRS` — all FAITHLESS per
`lean/notes/MOVES_LEAN_SEMAUDIT_GR_2026-07-26.md` §B/§D). This file proves NO held unit;
it certifies exactly what the current `Defs` interface supports, so the fan-out record is
machine-checked rather than prose. NEW statements (additive; statement fence untouched);
flagged for semantic-guardian review. The L5 certificate is `HeldUnits_L5_cert.lean`.

* `baseStage_hbase_empty` — the `L4_baseStage_exists` hypothesis `σ.wPrev = fun _ => 0`
  contradicts `σ.hS6b` (which demands a coefficient of parent weight `wPrev Φ + 1 = 1`):
  NO stage satisfies it, so the held unit is VACUOUSLY provable as stated. Proving it
  would be dishonest, not progress — it needs the faithful D.2 base-data restatement.
* `transitionCoreL_e0_false` — `TransitionCoreL σ σ' Φhat 0 h' zbar` is absurd
  (`base.child_e : σ'.e = 0` vs `σ'.he : 1 ≤ σ'.e`), so `L4_TRANSstage` (quantifying over
  ALL `e'` with no positivity/D.3-D.7 hypotheses) is provable only if `GenuineStageModel σ`
  is empty: non-vacuously unprovable as stated.
* `tvec_units_fragment` — the fragment of `TvecUnitLaw` (hence of `L4_TRANSvi`'s
  conclusion) the current interface DOES support: the key and every T-vector entry have
  genuinely UNIT initial forms in `L = LTwo ↥σ.K` (from `hRΦ`/`hTvec`/`hreps`/`hS5`).
  Only the product law `Π ru^aᵢ · uY^t = locT` needs data absent from
  `Stage`+`GenuineStageModel` (the ℤ-exponents of `σ.Tvec` are unconstrained — the
  Tvec-blindness already recorded at `L4_genuine_imp_stageCoreL_v2`).
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- CERT (held unit `L4_baseStage_exists`): the hypothesis `σ.wPrev = fun _ => 0` is
UNSATISFIABLE — `hS6b` at `ν = σ.wPrev σ.Φ + 1` (scalar `1`) produces a coefficient `B`
with `σ.wPrev B = σ.wPrev σ.Φ + 1`, impossible for the constant-0 `wPrev`. -/
theorem baseStage_hbase_empty (σ : Stage p F) (hbase : σ.wPrev = fun _ => (0 : ℤ)) :
    False := by
  obtain ⟨B, hB0, hBC, hBw, -⟩ := σ.hS6b (σ.wPrev σ.Φ + 1) 1 (lt_add_one _)
  simp only [hbase] at hBw
  omega

/-- CERT (held unit `L4_TRANSstage`): at `e' = 0` no child stage exists —
`TransitionCoreL` forces `σ'.e = 0` against `σ'.he`. So the held statement (which takes
ARBITRARY `e'`) can hold only vacuously. -/
theorem transitionCoreL_e0_false (σ σ' : Stage p F) (Φhat : Polynomial ℤ_[p]) (h' : ℕ)
    (zbar : Fˣ) (ht : TransitionCoreL σ σ' Φhat 0 h' zbar) : False := by
  have h0 := ht.base.child_e
  have h1 := σ'.he
  omega

/-- FRAGMENT (held unit `L4_TRANSvi` / `TvecUnitLaw`): the two unit-ness conjuncts of
`TvecUnitLaw` are derivable from the current interface — the key's initial form
`grRes Φ = C (T s) · T h` and every T-vector entry's initial form
`grRes ũ = C (C c · T (−t·wPrev ũ)) · T (w ũ)` (via `hS5` through `hTvec`/`hreps`) are
units of `LTwo`. The PRODUCT law is not derivable (exponents free). -/
theorem tvec_units_fragment (σ : Stage p F) :
    ∃ (uY : (LTwo ↥σ.K)ˣ) (ru : Fin σ.Tvec.length → (LTwo ↥σ.K)ˣ),
      IsGrUnit σ σ.Φ uY ∧ ∀ i, IsGrUnit σ (σ.Tvec.get i).1 (ru i) := by
  have hTu : ∀ k : ℤ, IsUnit (LaurentPolynomial.T k : LaurentPolynomial ↥σ.K) :=
    fun k => ⟨tUnit ↥σ.K k, rfl⟩
  have hTu2 : ∀ k : ℤ, IsUnit (LaurentPolynomial.T k : LTwo ↥σ.K) :=
    fun k => ⟨tUnit (LaurentPolynomial ↥σ.K) k, rfl⟩
  have hY : IsUnit (σ.grRes σ.Φ) := by
    simp only [Stage.grRes, σ.hRΦ]
    exact ((hTu σ.s).map (LaurentPolynomial.C : LaurentPolynomial ↥σ.K →+* LTwo ↥σ.K)).mul
      (hTu2 (σ.w σ.Φ))
  have hent : ∀ i : Fin σ.Tvec.length, IsUnit (σ.grRes (σ.Tvec.get i).1) := by
    intro i
    have hmem : (σ.Tvec.get i).1 ∈ σ.reps := by
      rw [← σ.hTvec]
      exact List.mem_map_of_mem (List.get_mem _ _)
    obtain ⟨hne, hin⟩ := σ.hreps _ hmem
    obtain ⟨c, hc⟩ := σ.hS5 _ hne hin
    simp only [Stage.grRes, hc]
    have h1 : IsUnit (LaurentPolynomial.C (c : ↥σ.K)) :=
      c.isUnit.map (LaurentPolynomial.C : ↥σ.K →+* LaurentPolynomial ↥σ.K)
    exact (((h1.mul (hTu _)).map
      (LaurentPolynomial.C : LaurentPolynomial ↥σ.K →+* LTwo ↥σ.K)).mul (hTu2 _))
  exact ⟨hY.unit, fun i => (hent i).unit, hY.unit_spec, fun i => (hent i).unit_spec⟩

#print axioms baseStage_hbase_empty
#print axioms transitionCoreL_e0_false
#print axioms tvec_units_fragment
