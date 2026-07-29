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
* **PROVED, all p, via `add_def` (§8.1 OPTION (a), signed off 2026-07-28)** — `R_neg`,
  `w_jump`, and `slot`.1. These were the add_def-gated legs: the graded route (map
  `initialForm`-identities through `Θ∘ι`) was blocked because nothing tied `Rg.ring`'s
  ADDITION/zero to the DirectSum's; the `add_def` field opens it (`ring_add_eq` and the
  bridge lemmas below). The former odd-p arithmetic detour (`R_neg_odd`/`w_jump_odd`,
  retained below for the record) is superseded by the uniform `R_neg_model`/`w_jump_model`;
  `slot`.1 is `slot_decomp_model` (the additive γ-graded evaluation `EV`).
RED-MODULE REPAIR 2026-07-29 (census-gap discovery): this module was recorded proved but
was red at HEAD — two `Gr`-level instance-diamond breaks (non-defeq projection paths into
the opaque `Rg.ring` on the `Gr` abbrev, poisonous under the lakefile's
`maxSynthPendingDepth = 3`, which `lake build` applies but `lake env lean` does not — the
verification discrepancy that let the red record pass) in `of_neg_ring` and `R_neg_model`'s
`hIF`/`map_neg` step. `of_neg_ring` (consumer-less after the repair) was dropped;
`R_neg_model` was re-routed through the additive γ-graded evaluation `EV` (see the lemma
docstrings). Statements unchanged; the sorried-obligation classification below is
unchanged.

* **`sorry`, UNDERIVABLE from the interface (free-field independence; v2 classification,
  unchanged — the unit is audited FAITHLESS-overreaching, #21)** — `wPrev_mul`,
  `wPrev_ult`, `prevIaug` (σ.wPrev is free off the coefficient space — perturbing it at `Φ^2`
  resp. `Φ` preserves every `Stage` law and every `M` field, `M` never mentions `wPrev`);
  `tvec` and `tvec_unit` (σ.Tvec's ℤ-exponents are free — `hTvec` fixes only `map fst`, and `M`
  is Tvec-blind); `reps_nonempty`/`p_is_rep` (σ.reps enters `M` only through the SET-image in
  `homMon_gen`, which cannot force list membership of `C p`).
* **`sorry`, derivable in principle but not completed here (v2 classification, unchanged)** —
  `coeff` clauses 2-3 (from σ alone: `hS5`-monomial product induction; positions/degrees couple
  as `(-t·ν, e·ν)` so equal weight ⇒ equal position, and `e·kⱼ = j − tγ` gives the stride
  generating ℤ); `slot`.2 (σ alone: distinct positions ⇒ termwise vanishing);
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

/-! ### The `add_def` graded route (§8.1 OPTION (a), signed off 2026-07-28)

With the `GradedRingStr.add_def` field (ring `+` componentwise = the DirectSum's), the
ring's `0`/`-` are pinned and `initialForm`-identities transport through `Θ ∘ ι`
additively. This closes the former p = 2 legs (`R_neg`, `w_jump` — now uniform in p,
superseding the odd-p arithmetic detour above) and `slot`.1. -/

/-- ring `+` = DirectSum `+` (elementwise, from the componentwise `add_def`). -/
private lemma ring_add_eq (S : SideVal p) (Rg : GradedRingStr S) (x y : S.Gr) :
    (letI := Rg.ring; x + y) = x + y := by
  refine DFinsupp.ext fun γ => ?_
  rw [Rg.add_def]
  rfl

/-- degree-γ `of`-classes add through the ring's `+`. -/
private lemma of_add_of (S : SideVal p) (Rg : GradedRingStr S) (γ : ℤ) (a b : S.grPiece γ) :
    (letI := Rg.ring;
      DirectSum.of (fun δ => S.grPiece δ) γ a + DirectSum.of (fun δ => S.grPiece δ) γ b)
      = DirectSum.of (fun δ => S.grPiece δ) γ (a + b) :=
  (ring_add_eq S Rg _ _).trans ((DirectSum.of (fun δ => S.grPiece δ) γ).map_add a b).symm

/-- `of γ 0` is the RING zero (uniqueness of the additive identity, via `add_def`). -/
private lemma of_zero_ring (S : SideVal p) (Rg : GradedRingStr S) (γ : ℤ) :
    DirectSum.of (fun δ => S.grPiece δ) γ (0 : S.grPiece γ)
      = (letI := Rg.ring; (0 : S.Gr)) := by
  letI := Rg.ring
  have h1 := of_add_of S Rg γ 0 0
  rw [add_zero] at h1
  exact add_right_cancel (h1.trans (zero_add _).symm)

/- (RED-MODULE REPAIR 2026-07-29: the v2 draft had `of_neg_ring` here — "ring negation =
componentwise negation on `of`-classes", proved by a Gr-level
`neg_eq_of_add_eq_zero_right`. Under the build options (`maxSynthPendingDepth = 3`,
applied by `lake build` but NOT by `lake env lean` — the discrepancy that let this module
be recorded green while red) EVERY Gr-level generic group-lemma application resolves its
class query through an instance path non-defeq to the `+` pinned in `of_add_of`/`add_def`,
so no proof body of that statement built. Its sole consumer was `R_neg_model`'s `hIF`
step, which is now re-routed through `EV` (below) and never needs a Gr-level negation;
the lemma is dropped rather than repaired.) -/

/-- index/representative transport for `of ∘ mk`. -/
private lemma of_mk_congr (S : SideVal p) {γ γ' : ℤ} (h : γ = γ')
    {a a' : Polynomial ℤ_[p]} (hv : a = a')
    (ha : ((γ : ℤ) : WithTop ℤ) ≤ S.w a) (ha' : ((γ' : ℤ) : WithTop ℤ) ≤ S.w a') :
    DirectSum.of (fun δ => S.grPiece δ) γ (Submodule.Quotient.mk ⟨a, ha⟩)
      = DirectSum.of (fun δ => S.grPiece δ) γ' (Submodule.Quotient.mk ⟨a', ha'⟩) := by
  subst h; subst hv; rfl

/-- the genuine initial form, re-indexed to a KNOWN weight `γ = σ.w g`. -/
private lemma initialForm_eq_of_mk (σ : Stage p F) (M : GenuineStageModel σ)
    {g : Polynomial ℤ_[p]} (hg0 : g ≠ 0) {γ : ℤ} (hwg : σ.w g = γ)
    (hmem : ((γ : ℤ) : WithTop ℤ) ≤ M.S.w g) :
    DirectSum.of (fun δ => M.S.grPiece δ) γ (Submodule.Quotient.mk ⟨g, hmem⟩)
      = M.S.initialForm g := by
  have hdeg : γ = M.S.deg g := by rw [deg_eq_w σ M hg0, hwg]
  unfold SideVal.initialForm SideVal.mkPiece
  exact of_mk_congr M.S hdeg rfl hmem (M.S.coe_deg_le g)

/-- the γ-graded evaluation `A_{≥γ} → L₀[T^{±1}]`, `u ↦ Θ(ι(of γ [u]))`. -/
private noncomputable def EV (σ : Stage p F) (M : GenuineStageModel σ) (γ : ℤ)
    (u : M.S.ge γ) : LTwo ↥σ.K :=
  letI := M.Rg.ring; letI := M.Loring; letI := M.alg
  M.Θ (algebraMap M.S.Gr M.Lo
    (DirectSum.of (fun δ => M.S.grPiece δ) γ (Submodule.Quotient.mk u)))

private lemma EV_zero (σ : Stage p F) (M : GenuineStageModel σ) (γ : ℤ) :
    EV σ M γ 0 = 0 := by
  letI := M.Rg.ring; letI := M.Loring; letI := M.alg
  unfold EV
  rw [show (Submodule.Quotient.mk (0 : M.S.ge γ) : M.S.grPiece γ) = 0 from
      map_zero ((M.S.gtIn γ).mkQ),
    of_zero_ring M.S M.Rg γ, map_zero, map_zero]

private lemma EV_add (σ : Stage p F) (M : GenuineStageModel σ) (γ : ℤ) (u v : M.S.ge γ) :
    EV σ M γ (u + v) = EV σ M γ u + EV σ M γ v := by
  letI := M.Rg.ring; letI := M.Loring; letI := M.alg
  unfold EV
  rw [show (Submodule.Quotient.mk (u + v) : M.S.grPiece γ)
      = Submodule.Quotient.mk u + Submodule.Quotient.mk v from
      map_add ((M.S.gtIn γ).mkQ) u v,
    ← of_add_of M.S M.Rg γ, map_add, map_add]

private lemma EV_sum (σ : Stage p F) (M : GenuineStageModel σ) (γ : ℤ)
    (s : Finset ℕ) (u : ℕ → M.S.ge γ) :
    EV σ M γ (∑ j ∈ s, u j) = ∑ j ∈ s, EV σ M γ (u j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using EV_zero σ M γ
  | insert a s' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, EV_add, ih]

/-- `EV` computes `C (R g) · T γ` on weight-exactly-γ elements (including `g = 0`). -/
private lemma EV_val (σ : Stage p F) (M : GenuineStageModel σ) (γ : ℤ)
    {g : Polynomial ℤ_[p]} (hmem : ((γ : ℤ) : WithTop ℤ) ≤ M.S.w g)
    (hgw : g ≠ 0 → σ.w g = γ) :
    EV σ M γ ⟨g, hmem⟩ = LaurentPolynomial.C (σ.R g) * LaurentPolynomial.T γ := by
  by_cases h0 : g = 0
  · subst h0
    rw [show (⟨(0 : Polynomial ℤ_[p]), hmem⟩ : M.S.ge γ) = 0 from Subtype.ext rfl,
      EV_zero σ M γ, σ.hR0, map_zero, zero_mul]
  · letI := M.Rg.ring; letI := M.Loring; letI := M.alg
    unfold EV
    rw [initialForm_eq_of_mk σ M h0 (hgw h0) hmem, ← grRes_eq_genuine σ M g h0]
    unfold Stage.grRes
    rw [hgw h0]

/-- **`R_neg`, ALL p** — RED-MODULE REPAIR 2026-07-29: re-routed through the additive
γ-graded evaluation `EV` (all cancellation now happens in the honest Laurent ring and at
the submodule level, never at a `Gr`-level `-`; the original `hIF`/`map_neg` route pushed
the DirectSum negation through the `Rg.ring`-keyed `algebraMap` — the same non-defeq
instance diamond as `of_neg_ring`'s, and it never compiled). The content is unchanged:
`EV(f) + EV(−f) = EV(f + (−f)) = EV(0) = 0`, `EV_val` evaluates both terms, and
`T`-cancellation + `C`-injectivity conclude `R(−f) = −R(f)`. -/
private lemma R_neg_model (σ : Stage p F) (M : GenuineStageModel σ) (f : Polynomial ℤ_[p]) :
    σ.R (-f) = - σ.R f := by
  by_cases hf : f = 0
  · subst hf; rw [neg_zero, σ.hR0, neg_zero]
  · have hnf : (-f) ≠ 0 := neg_ne_zero.mpr hf
    have hw : σ.w (-f) = σ.w f := w_neg_stage σ M hf
    have hmem_f : ((σ.w f : ℤ) : WithTop ℤ) ≤ M.S.w f := by
      rw [M.hSw f hf]
    have hmem_nf : ((σ.w f : ℤ) : WithTop ℤ) ≤ M.S.w (-f) := by
      rw [M.hSw (-f) hnf]; exact_mod_cast hw.ge
    have hsum : (⟨f, hmem_f⟩ : M.S.ge (σ.w f)) + ⟨-f, hmem_nf⟩ = 0 :=
      Subtype.ext (by simp)
    have h1 := EV_add σ M (σ.w f) ⟨f, hmem_f⟩ ⟨-f, hmem_nf⟩
    rw [hsum, EV_zero σ M, EV_val σ M (σ.w f) hmem_f (fun _ => rfl),
      EV_val σ M (σ.w f) hmem_nf (fun _ => hw)] at h1
    -- h1 : 0 = C (R f) * T γ + C (R (-f)) * T γ
    have h2 := congrArg (fun t => t * LaurentPolynomial.T (-(σ.w f))) h1
    simp only [zero_mul, add_mul] at h2
    rw [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, mul_one,
      mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one] at h2
    -- h2 : 0 = C (R f) + C (R (-f))
    exact laurC_inj ((eq_neg_of_add_eq_zero_right h2.symm).trans (map_neg _ _).symm)

/-- **`w_jump`, ALL p** — via `g = -f + (f+g)`, `hRlt`, and `R_neg_model`. -/
private lemma w_jump_model (σ : Stage p F) (M : GenuineStageModel σ)
    {f g : Polynomial ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (_hww : σ.w f = σ.w g) (hjump : σ.w f < σ.w (f + g)) : σ.R f + σ.R g = 0 := by
  have hlt : σ.w (-f) < σ.w (f + g) := by rw [w_neg_stage σ M hf]; exact hjump
  have h := σ.hRlt (-f) (f + g) (neg_ne_zero.mpr hf) hfg
    (by rw [neg_add_cancel_left]; exact hg) hlt
  rw [neg_add_cancel_left] at h
  rw [h, R_neg_model σ M f]
  ring

/-- **`slot`.1 (decomposition), ALL p** — the graded route: `EV` is additive from `A_{≥γ}`
and computes `C (R ·) · T γ` termwise, so `R` decomposes across equal-weight slots. -/
private lemma slot_decomp_model (σ : Stage p F) (M : GenuineStageModel σ)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (γ : ℤ)
    (hBN : ∀ j, N ≤ j → B j = 0)
    (hBw : ∀ j, j < N → B j ≠ 0 → σ.w (B j * σ.Φ ^ j) = γ)
    (hne : (∑ j ∈ Finset.range N, B j * σ.Φ ^ j) ≠ 0)
    (hw : σ.w (∑ j ∈ Finset.range N, B j * σ.Φ ^ j) = γ) :
    σ.R (∑ j ∈ Finset.range N, B j * σ.Φ ^ j)
      = ∑ j ∈ Finset.range N, σ.R (B j * σ.Φ ^ j) := by
  have hmem : ∀ j, ((γ : ℤ) : WithTop ℤ) ≤ M.S.w (B j * σ.Φ ^ j) := by
    intro j
    by_cases h0 : B j * σ.Φ ^ j = 0
    · rw [h0, M.S.w_zero]; exact le_top
    · have hB : B j ≠ 0 := fun hB0 => h0 (by rw [hB0, zero_mul])
      have hjN : j < N := by
        by_contra hj
        exact hB (hBN j (not_lt.mp hj))
      rw [M.hSw _ h0, hBw j hjN hB]
  have hsum_mem : ((γ : ℤ) : WithTop ℤ) ≤ M.S.w (∑ j ∈ Finset.range N, B j * σ.Φ ^ j) := by
    rw [M.hSw _ hne, hw]
  have hcoe : ((∑ j ∈ Finset.range N, (⟨B j * σ.Φ ^ j, hmem j⟩ : M.S.ge γ) : M.S.ge γ) :
      Polynomial ℤ_[p]) = ∑ j ∈ Finset.range N, B j * σ.Φ ^ j :=
    map_sum ((M.S.ge γ).subtype) _ _
  have hEq : (⟨∑ j ∈ Finset.range N, B j * σ.Φ ^ j, hsum_mem⟩ : M.S.ge γ)
      = ∑ j ∈ Finset.range N, (⟨B j * σ.Φ ^ j, hmem j⟩ : M.S.ge γ) :=
    Subtype.ext hcoe.symm
  have hmain := EV_sum σ M γ (Finset.range N) (fun j => ⟨B j * σ.Φ ^ j, hmem j⟩)
  rw [← hEq, EV_val σ M γ hsum_mem (fun _ => hw)] at hmain
  have hterm : ∀ j ∈ Finset.range N,
      EV σ M γ (⟨B j * σ.Φ ^ j, hmem j⟩ : M.S.ge γ)
        = LaurentPolynomial.C (σ.R (B j * σ.Φ ^ j)) * LaurentPolynomial.T γ := fun j hj =>
    EV_val σ M γ (hmem j)
      (fun h0 => hBw j (Finset.mem_range.mp hj) (fun hB0 => h0 (by rw [hB0, zero_mul])))
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum] at hmain
  have h2 := congrArg (fun t => t * LaurentPolynomial.T (-γ)) hmain
  rw [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, mul_one,
    mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, mul_one] at h2
  exact laurC_inj h2

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
  · -- w_jump: PROVED, ALL p (add_def graded route, option (a) 2026-07-28)
    exact fun f g hf hg hfg hww hjump => w_jump_model σ M hf hg hfg hww hjump
  · -- R_neg: PROVED, ALL p (add_def graded route, option (a) 2026-07-28)
    exact fun f => R_neg_model σ M f
  · -- tvec: UNDERIVABLE (σ.Tvec exponents free; M is Tvec-blind) — see header
    sorry
  · -- prevIaug: UNDERIVABLE (σ.wPrev Φ unbounded above) — see header
    sorry
  · -- slot: clause 1 PROVED (add_def graded route); clause 2 σ-derivable in principle
    -- (distinct positions) but not completed — STAYS sorried, v2 classification
    exact ⟨fun B N γ hBN hBw hne hw => slot_decomp_model σ M B N γ hBN hBw hne hw, sorry⟩
  · -- coeff: clause 1 PROVED from hS6b; clauses 2-3 σ-derivable in principle, not completed
    refine ⟨fun c => ?_, sorry, sorry⟩
    obtain ⟨B, hB0, hBC, hBw, hBR⟩ := σ.hS6b (σ.wPrev σ.Φ + 1) c (lt_add_one _)
    exact ⟨B, σ.wPrev σ.Φ + 1, hB0, hBC, hBw, hBR⟩
  · -- tvec_unit: UNDERIVABLE (same free exponents as tvec) — see header
    sorry
  · -- coeff_loc: clause 1 derivable in principle; clauses 2-3 UNDERIVABLE — see header
    sorry
