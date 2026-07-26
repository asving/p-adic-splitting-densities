import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

/-!
# MovesGr / L4_genuine_imp_stageCoreL (v2) — the bridge, RESTRUCTURED (partial proof + pinned gaps)

Statement byte-identical to `MANIFEST.json`. Honest status: `sorry` on exactly the obligations
that the `(σ : Stage) (M : GenuineStageModel σ)` interface does not determine; everything the
interface DOES determine is machine-checked below. Classification of the 13 obligations
(11 `StageCore` fields + `tvec_unit` + `coeff_loc`):

* **PROVED, all p** — `w_strict` (via `Rg.if_add_lt` = `L1_initialForm_add_lt` + DirectSum
  component extraction; no ring-addition needed), and clause 1 of `coeff` (from `σ.hS6b` at
  `ν = wPrev Φ + 1`).
* **PROVED for odd p; `sorry` confined to `IsUnit (2:ℤ_[p]) = False` (p = 2)** — `R_neg` and
  `w_jump`. NOTE the intended graded route (map `initialForm`-cancellation through `Θ∘ι`) is
  BLOCKED for every p by an interface gap in `GradedRingStr`: nothing ties `Rg.ring`'s ADDITION
  (or zero) to the `DirectSum` addition on `S.Gr` — `mul_of`/`one_def`/`if_mul`/`if_add_lt`
  constrain only `*`, `1`, and the strict-tie. The proof below instead derives `R(-1) = -1`
  arithmetically: `w(C c) = 0` for units `c` (via `S.w_smul` + `hwmul`), `R 1 = 1` (via
  `one_def` + `discharge`), `R(C 2) = R(1+1) = 2` (`hRadd`, needs `w(C 2) = 0`, i.e. 2 a unit),
  `R(-1) = R(1) - R(C 2) = -1` (`hRadd` on `C(-1) + C 2 = 1`), then `R(-f) = R(-1)·R(f)`
  (`hRmul`) and `w_jump` via `g = -f + (f+g)` + `hRlt`. At p = 2 with `char F ≠ 2` and
  `w(C 2) > 0`, `hRlt` on `1 + C(-2)` FORCES `R(-1) = 1`, so `R_neg` would force `char K = 2`:
  the p = 2 case is underivable because `Defs.lean` never ties `char F` to `p` (F is only
  "morally" `𝔽_{p^{n!}}`). Fix upstream: add `CharP F p` (or the additive tie in
  `GradedRingStr`, which restores the graded route for all p).
* **`sorry`, UNDERIVABLE from the interface (free-field independence)** — `wPrev_mul`,
  `wPrev_ult`, `prevIaug` (σ.wPrev is free off the coefficient space — perturbing it at `Φ^2`
  resp. `Φ` preserves every `Stage` law and every `M` field, `M` never mentions `wPrev`);
  `tvec` and `tvec_unit` (σ.Tvec's ℤ-exponents are free — `hTvec` fixes only `map fst`, and `M`
  is Tvec-blind); `reps_nonempty`/`p_is_rep` (σ.reps enters `M` only through the SET-image in
  `homMon_gen`, which cannot force list membership of `C p`).
* **`sorry`, derivable in principle but not completed here** — `coeff` clauses 2-3 (from σ alone:
  `hS5`-monomial product induction; positions/degrees couple as `(-t·ν, e·ν)` so equal weight ⇒
  equal position, and `e·kⱼ = j − tγ` gives the stride generating ℤ); `slot`.2 (σ alone: distinct
  positions ⇒ termwise vanishing); `slot`.1 blocked by the same additive-tie gap as above;
  `coeff_loc` clause 1 (graded-invariant closure induction), clauses 2-3 underivable (need
  genuine reps / the z-pinning, absent as above).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Dep unit `L4_grRes_eq_genuine`, inlined (not built as an olean): the discharge equation
read right-to-left. -/
private lemma grRes_eq_genuine (σ : Stage p F) (M : GenuineStageModel σ) (f : Polynomial ℤ_[p])
    (hf : f ≠ 0) : letI := M.Rg.ring; letI := M.Loring; letI := M.alg;
    σ.grRes f = M.Θ (algebraMap M.S.Gr M.Lo (M.S.initialForm f)) :=
  (M.discharge f hf).symm

/-- Dep unit `L1_initialForm_add_lt`, inlined (not built as an olean): the D.1(b) strict tie. -/
private lemma initialForm_add_lt (S : SideVal p) (Rg : GradedRingStr S)
    (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (hlt : S.deg f < S.deg g) : S.initialForm (f + g) = S.initialForm f :=
  Rg.if_add_lt f g hf hg hfg hlt

/-- `C` is injective on any Laurent-polynomial ring (coefficient extraction at 0). -/
private lemma laurC_inj {R : Type*} [CommSemiring R] {x y : R}
    (h : LaurentPolynomial.C x = LaurentPolynomial.C y) : x = y := by
  have h0 := congrArg (fun q => q 0) h
  simpa using h0

/-- The stage valuation of `1` is `0` (σ-only: `hwmul 1 1`). -/
private lemma w_one_stage (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/-- The genuine side degree computes the stage valuation on nonzero elements. -/
private lemma deg_eq_w (σ : Stage p F) (M : GenuineStageModel σ) {f : Polynomial ℤ_[p]}
    (hf : f ≠ 0) : M.S.deg f = σ.w f := by
  unfold SideVal.deg
  rw [M.hSw f hf]
  rfl

/-- Stage valuations are negation-invariant (via the genuine model's `w_neg`). -/
private lemma w_neg_stage (σ : Stage p F) (M : GenuineStageModel σ) {f : Polynomial ℤ_[p]}
    (hf : f ≠ 0) : σ.w (-f) = σ.w f := by
  have h : M.S.w (-f) = M.S.w f := M.S.w_neg f
  rw [M.hSw (-f) (neg_ne_zero.mpr hf), M.hSw f hf] at h
  exact_mod_cast h

/-- `w(C c) = 0` for every unit scalar `c` (via `S.w_smul` at `1` and `hwmul`). -/
private lemma w_C_unit (σ : Stage p F) (M : GenuineStageModel σ) {c : ℤ_[p]}
    (hc : IsUnit c) : σ.w (Polynomial.C c) = 0 := by
  obtain ⟨u, rfl⟩ := hc
  have key : ∀ d : ℤ_[p], d ≠ 0 → 0 ≤ σ.w (Polynomial.C d) := by
    intro d hd
    have hs := M.S.w_smul d 1
    rw [mul_one] at hs
    rw [M.hSw 1 one_ne_zero, M.hSw (Polynomial.C d) (by simpa using hd),
      w_one_stage σ] at hs
    exact_mod_cast hs
  have h1 : Polynomial.C (u : ℤ_[p]) * Polynomial.C ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    rw [← Polynomial.C_mul]
    simp
  have hmul := σ.hwmul (Polynomial.C (u : ℤ_[p])) (Polynomial.C ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))
    (by simp [u.ne_zero]) (by simp [(u⁻¹).ne_zero])
  rw [h1, w_one_stage σ] at hmul
  have k1 := key (u : ℤ_[p]) u.ne_zero
  have k2 := key ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) (u⁻¹).ne_zero
  omega

/-- `R 1 = 1`, through the genuine model (`one_def` + `discharge`). -/
private lemma R_one (σ : Stage p F) (M : GenuineStageModel σ) : σ.R 1 = 1 := by
  letI := M.Rg.ring; letI := M.Loring; letI := M.alg
  have h : σ.grRes 1 = M.Θ (algebraMap M.S.Gr M.Lo (M.S.initialForm 1)) :=
    grRes_eq_genuine σ M 1 one_ne_zero
  rw [← M.Rg.one_def, map_one, map_one] at h
  unfold Stage.grRes at h
  rw [w_one_stage σ, LaurentPolynomial.T_zero, mul_one] at h
  have h1 : LaurentPolynomial.C (σ.R 1) = LaurentPolynomial.C (1 : LaurentPolynomial ↥σ.K) := by
    rw [h, map_one]
  exact laurC_inj h1

/-- `R(-1) = -1` whenever `2` is a unit of `ℤ_[p]` (all odd `p`), via `hRadd` on
`1 + 1 = C 2` and `C(-1) + C 2 = 1`. -/
private lemma R_neg_one (σ : Stage p F) (M : GenuineStageModel σ)
    (h2 : IsUnit (2 : ℤ_[p])) : σ.R (-1) = -1 := by
  have hC2 : (Polynomial.C (2 : ℤ_[p])) = 1 + 1 := by
    rw [show (2 : ℤ_[p]) = 1 + 1 by norm_num, Polynomial.C_add, Polynomial.C_1]
  have hC2ne : (Polynomial.C (2 : ℤ_[p])) ≠ 0 := by
    simp
  have hw2 : σ.w (Polynomial.C (2 : ℤ_[p])) = 0 := w_C_unit σ M h2
  have hR2 : σ.R (Polynomial.C (2 : ℤ_[p])) = 2 := by
    have h := σ.hRadd 1 1 one_ne_zero one_ne_zero (by rw [← hC2]; exact hC2ne) rfl
      (by rw [← hC2, hw2, w_one_stage σ])
    rw [← hC2] at h
    rw [h, R_one σ M]
    ring
  have hkey : (-1 : Polynomial ℤ_[p]) + Polynomial.C (2 : ℤ_[p]) = 1 := by
    rw [hC2]; ring
  have hwneg1 : σ.w (-1 : Polynomial ℤ_[p]) = 0 := by
    rw [w_neg_stage σ M one_ne_zero, w_one_stage σ]
  have h := σ.hRadd (-1) (Polynomial.C (2 : ℤ_[p])) (by simp) hC2ne
    (by rw [hkey]; exact one_ne_zero) (by rw [hwneg1, hw2])
    (by rw [hkey, w_one_stage σ, hwneg1])
  rw [hkey, R_one σ M, hR2] at h
  linear_combination -h

/-- **`R_neg` for odd `p`**: `R(-f) = -R(f)` (via `-f = (-1)·f` and `hRmul`). -/
private lemma R_neg_odd (σ : Stage p F) (M : GenuineStageModel σ)
    (h2 : IsUnit (2 : ℤ_[p])) (f : Polynomial ℤ_[p]) : σ.R (-f) = - σ.R f := by
  by_cases hf : f = 0
  · subst hf; rw [neg_zero, σ.hR0, neg_zero]
  · have h := σ.hRmul (-1) f (by simp) hf
    rw [neg_one_mul] at h
    rw [h, R_neg_one σ M h2]
    ring

/-- **`w_jump` for odd `p`**: at an equal-weight jump the residuals cancel
(via `g = -f + (f+g)`, `hRlt`, and `R_neg_odd`). -/
private lemma w_jump_odd (σ : Stage p F) (M : GenuineStageModel σ) (h2 : IsUnit (2 : ℤ_[p]))
    {f g : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (_hww : σ.w f = σ.w g) (hjump : σ.w f < σ.w (f + g)) : σ.R f + σ.R g = 0 := by
  have hlt : σ.w (-f) < σ.w (f + g) := by rw [w_neg_stage σ M hf]; exact hjump
  have h := σ.hRlt (-f) (f + g) (neg_ne_zero.mpr hf) hfg
    (by rw [neg_add_cancel_left]; exact hg) hlt
  rw [neg_add_cancel_left] at h
  rw [h, R_neg_odd σ M h2 f]
  ring

/-- **`w_strict`, all `p`**: a strictly lower weight dominates the sum's weight (via
`Rg.if_add_lt` = `L1_initialForm_add_lt` and DirectSum component extraction; needs no
ring-addition tie). -/
private lemma w_strict_model (σ : Stage p F) (M : GenuineStageModel σ)
    {f g : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0) (hlt : σ.w f < σ.w g) :
    σ.w (f + g) = σ.w f := by
  have hfg : f + g ≠ 0 := by
    intro h
    have hgf : g = -f := eq_neg_of_add_eq_zero_right h
    rw [hgf, w_neg_stage σ M hf] at hlt
    exact lt_irrefl _ hlt
  have h1 : M.S.initialForm (f + g) = M.S.initialForm f :=
    initialForm_add_lt M.S M.Rg f g hf hg hfg
      (by rw [deg_eq_w σ M hf, deg_eq_w σ M hg]; exact hlt)
  have hdeg : M.S.deg (f + g) = M.S.deg f := by
    by_contra hne
    have h2 := congrArg (fun x : M.S.Gr => x (M.S.deg (f + g))) h1
    simp only [SideVal.initialForm, DirectSum.of_eq_same] at h2
    rw [DirectSum.of_eq_of_ne _ _ _ hne] at h2
    rw [SideVal.mkPiece, Submodule.Quotient.mk_eq_zero] at h2
    have hlt2 : (M.S.deg (f + g) : WithTop ℤ) < M.S.w (f + g) := h2
    rw [M.S.deg_eq hfg] at hlt2
    exact lt_irrefl _ hlt2
  rw [← deg_eq_w σ M hfg, ← deg_eq_w σ M hf]
  exact hdeg

theorem L4_genuine_imp_stageCoreL (σ : Stage p F) (M : GenuineStageModel σ) : StageCoreL σ := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- wPrev_mul: UNDERIVABLE (σ.wPrev free off C; M is wPrev-blind) — see header
    sorry
  · -- wPrev_ult: UNDERIVABLE — see header
    sorry
  · -- reps_nonempty: UNDERIVABLE (homMon_gen sees only the reps SET-image) — see header
    sorry
  · -- p_is_rep: UNDERIVABLE — see header
    sorry
  · -- w_strict: PROVED (all p)
    exact fun f g hf hg hlt => w_strict_model σ M hf hg hlt
  · -- w_jump: PROVED for odd p; the residual sorry is exactly p = 2 — see header
    intro f g hf hg hfg hww hjump
    by_cases h2 : IsUnit (2 : ℤ_[p])
    · exact w_jump_odd σ M h2 hf hg hfg hww hjump
    · sorry
  · -- R_neg: PROVED for odd p; the residual sorry is exactly p = 2 — see header
    intro f
    by_cases h2 : IsUnit (2 : ℤ_[p])
    · exact R_neg_odd σ M h2 f
    · sorry
  · -- tvec: UNDERIVABLE (σ.Tvec exponents free; M is Tvec-blind) — see header
    sorry
  · -- prevIaug: UNDERIVABLE (σ.wPrev Φ unbounded above) — see header
    sorry
  · -- slot: clause 1 blocked by the GradedRingStr additive-tie gap; clause 2 σ-derivable
    -- in principle (distinct positions) but not completed — see header
    sorry
  · -- coeff: clause 1 PROVED from hS6b; clauses 2-3 σ-derivable in principle, not completed
    refine ⟨fun c => ?_, sorry, sorry⟩
    obtain ⟨B, hB0, hBC, hBw, hBR⟩ := σ.hS6b (σ.wPrev σ.Φ + 1) c (lt_add_one _)
    exact ⟨B, σ.wPrev σ.Φ + 1, hB0, hBC, hBw, hBR⟩
  · -- tvec_unit: UNDERIVABLE (same free exponents as tvec) — see header
    sorry
  · -- coeff_loc: clause 1 derivable in principle; clauses 2-3 UNDERIVABLE — see header
    sorry
