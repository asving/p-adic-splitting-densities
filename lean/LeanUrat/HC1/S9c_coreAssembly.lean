/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.K1_vertexPin
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.S3_childK1
import LeanUrat.HC1.S5_childValuation
import LeanUrat.HC1.S9a_stageLiteral
import LeanUrat.HC1.S9w_residualLaws
import LeanUrat.HC1.S11a_coreTransport
import LeanUrat.HC1.V7_stripDischarge
import LeanUrat.Moves.L2_slotDecomp_R4
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L4_TRANSii
import LeanUrat.Moves.L4_TRANSviii_b_R4

/-!
# HC1.S9c_coreAssembly — StageCore of the constructed child + the TransitionCoreL
records

S9 DECOMPOSITION unit (blueprint §9.5): "S9c: StageCore assembly + TransitionCoreL
records (TransitionData rfl fields, child_Tvec, pinned child_dig_frame) +
SlotDecomp/CoeffFieldLawCore." Cumulative over S9a/S9b: the literal carries the
FULL round-5 transition record (`TransitionCoreL` — its `child_dig_frame` is the
pin's own clause via `VertexPin.to_child_dig_frame`, with `mfun := 0`, no
∃-slack) and `StageCore` (the seven non-twist legs are `S11a_coreTransport`'s
transport — consumed here to shrink the per-field work; the residual construction
facts are w_jump (the `ChildResLaws` w_jump conjunct, via S9w's lawful carrier —
re-threaded at the 2026-07-28 unbundle; formerly a `ChildResData` field), TvecLaw
(the transported-vector product law of the literal), SlotDecomp and
CoeffFieldLawCore (transports via `L4_TRANSvii_R4` + S6, per §9.5)).

**RESTATED (2026-07-28, mechanical-closer round — the S9a adjudication + the S9b
precedent applied verbatim): the increment guard `e·g > 1`.** The unguarded
statement is refuted at the `σ.e * g = 1` corner by EXACTLY S9a's kernel
argument: S9c's ∃ CONTAINS the refuted S9a shape (its `TransitionCoreL.base` is
the `TransitionData` whose `child_reps` puts the outgoing key `σ.Φ` on the child
list, `hreps` forces it into `C_Φ̂`, and at `e·g = 1` the degrees collide) —
`S9c_ungated_corner_refuted` below, the in-file machine-checked kernel,
delegating to `S9a_ungated_corner_refuted`. ADJUDICATION (S9a's, verbatim): the
note's LST tower-induction step carries the guard EXPLICITLY — MOVES 3755–3757:
"STEP at an INCREMENT ν_{i+1} (stage data (e_{i+1}, h_{i+1}), **e·g > 1**)" — and
the `e·g = 1` corner is the note's OTHER species, MOVES 3766–3767 (RECENTERING,
`Φ̂ ↦ Φ̂ + t`), handled by the PROVED S10_recStage, not by S9. The statement gains
the hypothesis `hEG : 1 < σ.e * g`; the refutation corner fails the guard by
`S9a_corner_fails_guard` (proved in S9a's file, statement-independent
arithmetic).

**PROVED (same round): the guarded assembly.** The S9a/S9b literal re-runs
verbatim (Bézout split, the S9w lawful carrier, the S2/S3/S5 childW plumbing,
the in-file hwult, hS6b′ + the coset hS6a′ via `L4_TRANSviii_b` + the V7 strip
discharge), then the S9c-specific conjuncts close from the census suppliers:
* `TransitionCoreL`: `TransitionData` = the construction records (all rfl on the
  literal); `child_Tvec` = rfl (the literal's Tvec IS the transported vector);
  `child_dig_frame` = the carrier's S5′ pin through
  `VertexPin.to_child_dig_frame` (`mfun := 0`, no ∃-slack).
* `VertexPin` + the childW tie: the carrier's own hS5′ pin / rfl (as S9a).
* `StageCore`: the seven non-twist legs from `S11a_coreTransport` (consumed as
  planned); w_jump = the `ChildResLaws` conjunct of S9w's lawful carrier;
  TvecLaw via the NEW in-file bridge `tvecLaw_of_tvecUnitLaw` from
  `K1_tvecUnitLaw_of_pin` (the pin kills the twist class; the two-evaluation
  shadow follows from the unit law by the bare Stage laws — this supplier
  SUPERSEDES the §9.5 "by construction" route, no new law needed); SlotDecomp
  via the clean Moves `L2_slotDecomp` (w_strict/w_jump/R_neg are exactly its
  inputs); CoeffFieldLawCore via the NEW in-file `coeffCore_of_stage` — all
  three (S4)-core clauses are derivable for EVERY stage from the bare fields +
  wPrev_mul (clause 1 from hS6b at one weight above the threshold; clause 2
  from hS5-monomiality + the hStretch product law; clause 3's exponent group
  hits −1 = −(e·s + h·t) on the pair (B₁, B₂·Φ^e) of hS6b realizers at parent
  weights ν₀ + h and ν₀ — the §9.5 "L4_TRANSvii_R4 + S6" plan is superseded by
  this leaner generic route, no new law needed).
difficulty: HARD (assembly). hyp: hEG (the adjudicated note guard).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## Generic bare-Stage helpers (the K1/L5 private-duplicate pattern) -/

private lemma w_one' (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

private lemma wPrev_one' (σ : Stage p F)
    (hwPm : ∀ f g, f ≠ 0 → g ≠ 0 → σ.wPrev (f * g) = σ.wPrev f + σ.wPrev g) :
    σ.wPrev 1 = 0 := by
  have h := hwPm 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

private lemma R_one' (σ : Stage p F) : σ.R 1 = 1 := by
  have h := σ.hRmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  have hne : σ.R 1 ≠ 0 := σ.hRne 1 one_ne_zero
  exact (mul_left_cancel₀ hne (by rw [mul_one]; exact h)).symm

private lemma w_pow' (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    σ.w (x ^ n) = (n : ℤ) * σ.w x := by
  induction n with
  | zero => simpa [pow_zero] using w_one' σ
  | succ k ih =>
      rw [pow_succ, σ.hwmul _ x (pow_ne_zero k hx) hx, ih]
      push_cast
      ring

private lemma R_pow' (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    σ.R (x ^ n) = σ.R x ^ n := by
  induction n with
  | zero => simpa [pow_zero] using R_one' σ
  | succ k ih => rw [pow_succ, σ.hRmul _ x (pow_ne_zero k hx) hx, ih, pow_succ]

private lemma list_prod_ne_zero' (l : List (Polynomial ℤ_[p])) (hl : ∀ x ∈ l, x ≠ 0) :
    l.prod ≠ 0 :=
  List.prod_ne_zero (fun h0 => (hl 0 h0) rfl)

private lemma fin_prod_get {M : Type*} [CommMonoid M] {α : Type*} (l : List α) (g : α → M) :
    ∏ i : Fin l.length, g (l.get i) = (l.map g).prod := by
  conv_rhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

private lemma tvec_entry_facts' (σ : Stage p F) {q : Polynomial ℤ_[p] × ℤ}
    (hq : q ∈ σ.Tvec) : q.1 ≠ 0 ∧ inC σ.Φ q.1 :=
  σ.hreps q.1 (by rw [← σ.hTvec]; exact List.mem_map_of_mem hq)

/-! ## Laurent monomial extraction, coefficient ring general (the LTwo case needs
`R = LaurentPolynomial K`, a semiring — K1's field-scoped private is duplicated
at the honest generality) -/

private lemma CT_apply'' {R : Type*} [Semiring R] (c : R) (n q : ℤ) :
    (LaurentPolynomial.C c * LaurentPolynomial.T n : LaurentPolynomial R) q
      = if n = q then c else 0 := by
  have h1 : LaurentPolynomial.C c * LaurentPolynomial.T n
      = (Finsupp.single n c : LaurentPolynomial R) :=
    (LaurentPolynomial.single_eq_C_mul_T c n).symm
  have h0 := congrArg (fun t : ℤ →₀ R => t q) h1
  exact h0.trans Finsupp.single_apply

private lemma CT_eq_extract' {R : Type*} [Semiring R] {c c' : R} {n n' : ℤ} (hc : c ≠ 0)
    (h : LaurentPolynomial.C c * LaurentPolynomial.T n
       = LaurentPolynomial.C c' * LaurentPolynomial.T n') : c = c' ∧ n = n' := by
  have h1 := congrArg (fun t : ℤ →₀ R => t n) h
  rw [CT_apply'', CT_apply'', if_pos rfl] at h1
  by_cases hnn : n' = n
  · subst hnn
    rw [if_pos rfl] at h1
    exact ⟨h1, rfl⟩
  · rw [if_neg hnn] at h1
    exact absurd h1 hc

/-! ## The initial-form (`grRes`) calculus on nonzero elements -/

private lemma grRes_one' (σ : Stage p F) : σ.grRes 1 = 1 := by
  rw [Stage.grRes, R_one' σ, w_one' σ, LaurentPolynomial.T_zero, map_one, one_mul]

private lemma grRes_mul' (σ : Stage p F) (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0) :
    σ.grRes (f * g) = σ.grRes f * σ.grRes g := by
  rw [Stage.grRes, Stage.grRes, Stage.grRes, σ.hRmul f g hf hg, σ.hwmul f g hf hg,
    map_mul, LaurentPolynomial.T_add]
  ring

private lemma grRes_pow' (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    σ.grRes (x ^ n) = σ.grRes x ^ n := by
  induction n with
  | zero => simpa [pow_zero] using grRes_one' σ
  | succ k ih => rw [pow_succ, grRes_mul' σ _ x (pow_ne_zero k hx) hx, ih, pow_succ]

private lemma grRes_list_prod' (σ : Stage p F) (l : List (Polynomial ℤ_[p]))
    (hl : ∀ x ∈ l, x ≠ 0) : σ.grRes l.prod = (l.map σ.grRes).prod := by
  induction l with
  | nil => simpa using grRes_one' σ
  | cons x xs ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons,
        grRes_mul' σ x xs.prod (hl x (by simp))
          (list_prod_ne_zero' xs (fun y hy => hl y (by simp [hy]))),
        ih (fun y hy => hl y (by simp [hy]))]

/-- The value of one side (num or den, exponent selector `eF`) of the T-vector unit
product IS the initial form of the corresponding literal element of `A`. -/
private lemma unit_side_val (σ : Stage p F)
    (uY : (LTwo ↥σ.K)ˣ) (ru : Fin σ.Tvec.length → (LTwo ↥σ.K)ˣ)
    (huY : IsGrUnit σ σ.Φ uY) (hru : ∀ i, IsGrUnit σ ((σ.Tvec.get i).1) (ru i))
    (eF : ℤ → ℕ) :
    (((∏ i, ru i ^ eF ((σ.Tvec.get i).2)) * uY ^ eF σ.t : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K)
      = σ.grRes ((σ.Tvec.map fun q => q.1 ^ eF q.2).prod * σ.Φ ^ eF σ.t) := by
  have hent : ∀ q ∈ σ.Tvec, q.1 ≠ 0 := fun q hq => (tvec_entry_facts' σ hq).1
  have hlist_ne : ∀ x ∈ σ.Tvec.map (fun q => q.1 ^ eF q.2), x ≠ 0 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact pow_ne_zero _ (hent q hq)
  -- push the value through the unit product
  have h1 : (((∏ i, ru i ^ eF ((σ.Tvec.get i).2)) * uY ^ eF σ.t : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K)
      = (∏ i, σ.grRes ((σ.Tvec.get i).1) ^ eF ((σ.Tvec.get i).2)) * σ.grRes σ.Φ ^ eF σ.t := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, huY]
    congr 1
    calc ((∏ i, ru i ^ eF ((σ.Tvec.get i).2) : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K)
        = Units.coeHom (LTwo ↥σ.K) (∏ i, ru i ^ eF ((σ.Tvec.get i).2)) := rfl
      _ = ∏ i, Units.coeHom (LTwo ↥σ.K) (ru i ^ eF ((σ.Tvec.get i).2)) :=
          map_prod (Units.coeHom (LTwo ↥σ.K)) _ Finset.univ
      _ = ∏ i, σ.grRes ((σ.Tvec.get i).1) ^ eF ((σ.Tvec.get i).2) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          show ((ru i ^ eF ((σ.Tvec.get i).2) : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K) = _
          rw [Units.val_pow_eq_pow_val, hru i]
  rw [h1]
  -- fold the initial-form powers/products back into grRes of the literal element
  have h2 : (∏ i, σ.grRes ((σ.Tvec.get i).1) ^ eF ((σ.Tvec.get i).2))
      = σ.grRes ((σ.Tvec.map fun q => q.1 ^ eF q.2).prod) := by
    have h3 : ∀ i : Fin σ.Tvec.length,
        σ.grRes ((σ.Tvec.get i).1) ^ eF ((σ.Tvec.get i).2)
          = σ.grRes (((σ.Tvec.get i).1) ^ eF ((σ.Tvec.get i).2)) := fun i =>
      (grRes_pow' σ _ (hent _ (σ.Tvec.get_mem i)) _).symm
    rw [Finset.prod_congr rfl (fun i _ => h3 i),
      fin_prod_get σ.Tvec (fun q => σ.grRes (q.1 ^ eF q.2)),
      grRes_list_prod' σ _ hlist_ne, List.map_map]
    rfl
  rw [h2, ← grRes_pow' σ σ.Φ σ.hmonic.ne_zero,
    ← grRes_mul' σ _ _ (list_prod_ne_zero' _ hlist_ne) (pow_ne_zero _ σ.hmonic.ne_zero)]

/-- **The T-law bridge**: the round-5 unit product law (`TvecUnitLaw`, at the actual
localized unit) implies the round-4 two-evaluation shadow (`TvecLaw`) for EVERY
stage, from the bare (S1)/D.1(e) laws alone. Consumed on the constructed child:
`K1_tvecUnitLaw_of_pin` supplies the unit law from the recorded pin, and this
bridge lands the `StageCore.tvec` leg. -/
private lemma tvecLaw_of_tvecUnitLaw (σ : Stage p F) (hu : TvecUnitLaw σ) : TvecLaw σ := by
  classical
  obtain ⟨uY, ru, huY, hru, hprod⟩ := hu
  have hent : ∀ q ∈ σ.Tvec, q.1 ≠ 0 := fun q hq => (tvec_entry_facts' σ hq).1
  have hside_ne : ∀ eF : ℤ → ℕ,
      (σ.Tvec.map fun q => q.1 ^ eF q.2).prod * σ.Φ ^ eF σ.t ≠ 0 := by
    intro eF
    refine mul_ne_zero (list_prod_ne_zero' _ ?_) (pow_ne_zero _ σ.hmonic.ne_zero)
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact pow_ne_zero _ (hent q hq)
  -- clear denominators: num = (the zpow product)·den, at the UNIT level (no inverses)
  have hcomb : ∀ (u : (LTwo ↥σ.K)ˣ) (b : ℤ), u ^ b * u ^ (-b).toNat = u ^ b.toNat := by
    intro u b
    rw [← zpow_natCast u (-b).toNat, ← zpow_natCast u b.toNat, ← zpow_add]
    congr 1
    omega
  have hND : ((∏ i, ru i ^ ((σ.Tvec.get i).2)) * uY ^ σ.t)
        * ((∏ i, ru i ^ ((-(σ.Tvec.get i).2).toNat)) * uY ^ ((-σ.t).toNat))
      = (∏ i, ru i ^ (((σ.Tvec.get i).2).toNat)) * uY ^ (σ.t.toNat) := by
    calc ((∏ i, ru i ^ ((σ.Tvec.get i).2)) * uY ^ σ.t)
          * ((∏ i, ru i ^ ((-(σ.Tvec.get i).2).toNat)) * uY ^ ((-σ.t).toNat))
        = ((∏ i, ru i ^ ((σ.Tvec.get i).2)) * (∏ i, ru i ^ ((-(σ.Tvec.get i).2).toNat)))
            * (uY ^ σ.t * uY ^ ((-σ.t).toNat)) :=
          mul_mul_mul_comm (∏ i, ru i ^ ((σ.Tvec.get i).2)) (uY ^ σ.t)
            (∏ i, ru i ^ ((-(σ.Tvec.get i).2).toNat)) (uY ^ ((-σ.t).toNat))
      _ = (∏ i, ru i ^ ((σ.Tvec.get i).2) * ru i ^ ((-(σ.Tvec.get i).2).toNat))
            * uY ^ (σ.t.toNat) := by
          rw [← Finset.prod_mul_distrib, hcomb uY σ.t]
      _ = (∏ i, ru i ^ (((σ.Tvec.get i).2).toNat)) * uY ^ (σ.t.toNat) :=
          congrArg (· * uY ^ σ.t.toNat) (Finset.prod_congr rfl fun i _ => hcomb _ _)
  have key : (∏ i, ru i ^ (((σ.Tvec.get i).2).toNat)) * uY ^ (σ.t.toNat)
      = locT ↥σ.K * ((∏ i, ru i ^ ((-(σ.Tvec.get i).2).toNat)) * uY ^ ((-σ.t).toNat)) := by
    rw [← hND, hprod]
  -- take values: both sides are initial forms of the literal num/den elements
  have hval : σ.grRes ((σ.Tvec.map fun q => q.1 ^ (q.2).toNat).prod * σ.Φ ^ (σ.t).toNat)
      = LaurentPolynomial.T 1
        * σ.grRes ((σ.Tvec.map fun q => q.1 ^ (-q.2).toNat).prod * σ.Φ ^ (-σ.t).toNat) := by
    calc σ.grRes ((σ.Tvec.map fun q => q.1 ^ (q.2).toNat).prod * σ.Φ ^ (σ.t).toNat)
        = (((∏ i, ru i ^ (((σ.Tvec.get i).2).toNat)) * uY ^ (σ.t.toNat) :
            (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K) :=
          (unit_side_val σ uY ru huY hru Int.toNat).symm
      _ = ((locT ↥σ.K * ((∏ i, ru i ^ ((-(σ.Tvec.get i).2).toNat)) * uY ^ ((-σ.t).toNat)) :
            (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K) := by rw [key]
      _ = LaurentPolynomial.T 1
            * σ.grRes ((σ.Tvec.map fun q => q.1 ^ (-q.2).toNat).prod * σ.Φ ^ (-σ.t).toNat) := by
          rw [Units.val_mul]
          exact congrArg (((locT ↥σ.K : (LTwo ↥σ.K)ˣ) : LTwo ↥σ.K) * ·)
            (unit_side_val σ uY ru huY hru (fun z => (-z).toNat))
  -- the two sides are the literal tvecNum/tvecDen
  have hN : σ.tvecNum = (σ.Tvec.map fun q => q.1 ^ (q.2).toNat).prod * σ.Φ ^ (σ.t).toNat := rfl
  have hD : σ.tvecDen
      = (σ.Tvec.map fun q => q.1 ^ (-q.2).toNat).prod * σ.Φ ^ (-σ.t).toNat := rfl
  rw [← hN, ← hD] at hval
  -- extract scalar and position from the monomial identity in L = L₀[T^{±1}]
  have hEq : LaurentPolynomial.C (σ.R σ.tvecNum) * LaurentPolynomial.T (σ.w σ.tvecNum)
      = LaurentPolynomial.C (σ.R σ.tvecDen) * LaurentPolynomial.T (1 + σ.w σ.tvecDen) := by
    have h := hval
    rw [Stage.grRes, Stage.grRes] at h
    rw [h, mul_left_comm, ← LaurentPolynomial.T_add]
  have hnum_ne : σ.tvecNum ≠ 0 := by rw [hN]; exact hside_ne Int.toNat
  obtain ⟨hR, hw⟩ := CT_eq_extract' (σ.hRne σ.tvecNum hnum_ne) hEq
  exact ⟨by omega, hR⟩

/-! ## The (S4) core from the bare fields: every stage with a multiplicative parent
valuation satisfies `CoeffFieldLawCore` -/

/-- The residual of a product of nonzero coefficients is a monomial unit at the
forced position `−t·wPrev` (the hS5 shapes multiply out). -/
private lemma coeff_prod_R' (σ : Stage p F)
    (hwPm : ∀ f g, f ≠ 0 → g ≠ 0 → σ.wPrev (f * g) = σ.wPrev f + σ.wPrev g)
    (l : List (Polynomial ℤ_[p])) (hl : ∀ u ∈ l, u ≠ 0 ∧ inC σ.Φ u) :
    ∃ c : (↥σ.K)ˣ,
      σ.R l.prod = LaurentPolynomial.C (c : ↥σ.K) *
        LaurentPolynomial.T (- σ.t * σ.wPrev l.prod) := by
  induction l with
  | nil =>
      refine ⟨1, ?_⟩
      rw [List.prod_nil, R_one' σ, wPrev_one' σ hwPm, mul_zero, LaurentPolynomial.T_zero,
        Units.val_one, map_one, one_mul]
  | cons u us ih =>
      have hu := hl u List.mem_cons_self
      have hus : ∀ x ∈ us, x ≠ 0 ∧ inC σ.Φ x := fun x hx => hl x (List.mem_cons_of_mem u hx)
      have husne : us.prod ≠ 0 := list_prod_ne_zero' us (fun x hx => (hus x hx).1)
      obtain ⟨cr, hcr⟩ := ih hus
      obtain ⟨cu, hcu⟩ := σ.hS5 u hu.1 hu.2
      refine ⟨cu * cr, ?_⟩
      rw [List.prod_cons, σ.hRmul u us.prod hu.1 husne, hcu, hcr,
        hwPm u us.prod hu.1 husne, Units.val_mul, map_mul, mul_mul_mul_comm,
        ← LaurentPolynomial.T_add]
      congr 1
      ring

/-- The hStretch product law: `w = e·wPrev` on products of coefficients. -/
private lemma w_coeff_prod' (σ : Stage p F)
    (hwPm : ∀ f g, f ≠ 0 → g ≠ 0 → σ.wPrev (f * g) = σ.wPrev f + σ.wPrev g)
    (l : List (Polynomial ℤ_[p])) (hl : ∀ u ∈ l, u ≠ 0 ∧ inC σ.Φ u) :
    σ.w l.prod = (σ.e : ℤ) * σ.wPrev l.prod := by
  induction l with
  | nil =>
      rw [List.prod_nil, w_one' σ, wPrev_one' σ hwPm, mul_zero]
  | cons u us ih =>
      have hu := hl u List.mem_cons_self
      have hus : ∀ x ∈ us, x ≠ 0 ∧ inC σ.Φ x := fun x hx => hl x (List.mem_cons_of_mem u hx)
      have husne : us.prod ≠ 0 := list_prod_ne_zero' us (fun x hx => (hus x hx).1)
      rw [List.prod_cons, σ.hwmul u us.prod hu.1 husne, hwPm u us.prod hu.1 husne,
        σ.hStretch u hu.1 hu.2, ih hus]
      ring

/-- **The (S4) core is generic**: every stage whose parent valuation is
multiplicative satisfies all three `CoeffFieldLawCore` clauses from the bare
`Stage` fields — clause 1 from `hS6b` one weight above the threshold; clause 2
from the hS5 monomial shapes + the hStretch product law (`e ≥ 1` cancels);
clause 3 because the exponent-group set contains `−1 = −(e·s + h·t)`, realized
by the pair `(B₁, B₂·Φ^e)` of `hS6b` realizers at parent weights `ν₀ + h`, `ν₀`. -/
private lemma coeffCore_of_stage (σ : Stage p F)
    (hwPm : ∀ f g, f ≠ 0 → g ≠ 0 → σ.wPrev (f * g) = σ.wPrev f + σ.wPrev g) :
    CoeffFieldLawCore σ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- clause 1: every current-field unit scalar realized at its forced position
    intro c
    obtain ⟨B, hB0, hBc, hBw, hBR⟩ := σ.hS6b (σ.wPrev σ.Φ + 1) c (lt_add_one _)
    exact ⟨B, σ.wPrev σ.Φ + 1, hB0, hBc, hBw, hBR⟩
  · -- clause 2: equal-weight coefficient products differ by a K-constant
    intro f g hf hg hfne hgne hwfg
    obtain ⟨lf, hlf, rfl⟩ := hf
    obtain ⟨lg, hlg, rfl⟩ := hg
    obtain ⟨cf, hcf⟩ := coeff_prod_R' σ hwPm lf hlf
    obtain ⟨cg, hcg⟩ := coeff_prod_R' σ hwPm lg hlg
    have he0 : ((σ.e : ℤ)) ≠ 0 := by
      have := σ.he
      omega
    have hwp : σ.wPrev lf.prod = σ.wPrev lg.prod := by
      apply mul_left_cancel₀ he0
      rw [← w_coeff_prod' σ hwPm lf hlf, ← w_coeff_prod' σ hwPm lg hlg]
      exact hwfg
    refine ⟨((cf * cg⁻¹ : (↥σ.K)ˣ) : ↥σ.K), ?_⟩
    have hdc : ((cf * cg⁻¹ : (↥σ.K)ˣ) : ↥σ.K) * (cg : ↥σ.K) = (cf : ↥σ.K) := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    rw [hcf, hcg, hwp, ← mul_assoc, ← map_mul, hdc]
  · -- clause 3: the exponent group is all of ℤ (−1 is realized; Bézout collapses it)
    have hh1 : (1 : ℤ) ≤ (σ.h : ℤ) := by exact_mod_cast σ.hh
    set ν₀ : ℤ := σ.wPrev σ.Φ + 1 with hν₀def
    have hν₀ : σ.wPrev σ.Φ < ν₀ := lt_add_one _
    have hν₁ : σ.wPrev σ.Φ < ν₀ + (σ.h : ℤ) := by omega
    obtain ⟨B₁, hB₁0, hB₁c, hB₁w, hB₁R⟩ := σ.hS6b (ν₀ + (σ.h : ℤ)) 1 hν₁
    obtain ⟨B₂, hB₂0, hB₂c, hB₂w, hB₂R⟩ := σ.hS6b ν₀ 1 hν₀
    have hΦpow_ne : σ.Φ ^ σ.e ≠ 0 := pow_ne_zero _ σ.hmonic.ne_zero
    have hg0 : B₂ * σ.Φ ^ σ.e ≠ 0 := mul_ne_zero hB₂0 hΦpow_ne
    have hIsF : IsUnitMonProd σ B₁ := by
      refine ⟨[B₁], 0, ?_, by simp⟩
      intro u hu
      rw [List.mem_singleton] at hu
      subst hu
      exact ⟨hB₁0, hB₁c⟩
    have hIsG : IsUnitMonProd σ (B₂ * σ.Φ ^ σ.e) := by
      refine ⟨[B₂], σ.e, ?_, by simp⟩
      intro u hu
      rw [List.mem_singleton] at hu
      subst hu
      exact ⟨hB₂0, hB₂c⟩
    have hweq : σ.w B₁ = σ.w (B₂ * σ.Φ ^ σ.e) := by
      rw [σ.hwmul B₂ _ hB₂0 hΦpow_ne, σ.hStretch B₁ hB₁0 hB₁c, σ.hStretch B₂ hB₂0 hB₂c,
        hB₁w, hB₂w, w_pow' σ σ.Φ σ.hmonic.ne_zero, σ.hwΦ]
      ring
    have hRg : σ.R (B₂ * σ.Φ ^ σ.e)
        = LaurentPolynomial.C ((1 : (↥σ.K)ˣ) : ↥σ.K) *
            LaurentPolynomial.T (- σ.t * ν₀ + (σ.e : ℤ) * σ.s) := by
      rw [σ.hRmul B₂ _ hB₂0 hΦpow_ne, hB₂R, R_pow' σ σ.Φ σ.hmonic.ne_zero, σ.hRΦ,
        LaurentPolynomial.T_pow, mul_assoc, ← LaurentPolynomial.T_add]
    have hn : (-1 : ℤ) = (- σ.t * (ν₀ + (σ.h : ℤ))) - (- σ.t * ν₀ + (σ.e : ℤ) * σ.s) := by
      have hb := σ.hbez
      linear_combination hb
    have hm1 : (-1 : ℤ) ∈
        {n : ℤ | ∃ (f g : Polynomial ℤ_[p]) (c c' : ↥σ.K) (k k' : ℤ),
          IsUnitMonProd σ f ∧ IsUnitMonProd σ g ∧ f ≠ 0 ∧ g ≠ 0 ∧ σ.w f = σ.w g ∧
          σ.R f = LaurentPolynomial.C c * LaurentPolynomial.T k ∧
          σ.R g = LaurentPolynomial.C c' * LaurentPolynomial.T k' ∧ n = k - k'} :=
      ⟨B₁, B₂ * σ.Φ ^ σ.e, ((1 : (↥σ.K)ˣ) : ↥σ.K), ((1 : (↥σ.K)ˣ) : ↥σ.K),
        - σ.t * (ν₀ + (σ.h : ℤ)), - σ.t * ν₀ + (σ.e : ℤ) * σ.s,
        hIsF, hIsG, hB₁0, hg0, hweq, hB₁R, hRg, hn⟩
    rw [AddSubgroup.eq_top_iff']
    intro n
    have h := AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hm1) (-n)
    have hzs : (-n) • (-1 : ℤ) = n := by
      rw [zsmul_eq_mul]
      push_cast
      ring
    rwa [hzs] at h

/-! ## The corner kernel (the shape the restated guard excludes) -/

/-- **The refutation kernel, machine-checked** (the S9a kernel transported): at
`σ.e * g = 1` — the recentering species, `deg Φ̂ = deg σ.Φ` — NO child stage can
carry the S9c record, since `TransitionCoreL.base` contains the (refuted) S9a
record. -/
theorem S9c_ungated_corner_refuted (σ : Stage p F) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hcorner : σ.e * g = 1) :
    ¬ ∃ σ' : Stage p F,
        TransitionCoreL σ σ' Φhat e' h' zbar ∧
        VertexPin σ σ' Φhat zbar ∧
        (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) ∧
        StageCore σ' := by
  rintro ⟨σ', tc, pin, hw, -⟩
  exact S9a_ungated_corner_refuted σ th hcorner ⟨σ', tc.base, pin, hw⟩

/-! ## The unit -/

/-- Unit S9c (RESTATED 2026-07-28 with the adjudicated note guard `e·g > 1`,
MOVES 3755–3757, per the S9a/S9b precedent — see the header): at every INCREMENT
read (`1 < σ.e * g`), the constructed child carries the full transition record,
the pin, the childW tie, and `StageCore`. -/
theorem S9c_coreAssembly (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hEG : 1 < σ.e * g) :
    ∃ σ' : Stage p F,
      TransitionCoreL σ σ' Φhat e' h' zbar ∧
      VertexPin σ σ' Φhat zbar ∧
      (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) ∧
      StageCore σ' := by
  classical
  -- ## Lift facts (L3) and the guard's degree consequence (the S9a_final body)
  obtain ⟨hmonΦ, hdegΦ⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hΦne : Φhat ≠ 0 := hmonΦ.ne_zero
  have hdeg1 : 1 ≤ Φhat.natDegree := by
    rw [hdegΦ]
    exact Nat.mul_pos (by omega : 0 < σ.e * g) σ.hdeg
  have hΦnatlt : σ.Φ.natDegree < Φhat.natDegree := by
    rw [hdegΦ]
    exact lt_mul_of_one_lt_left σ.hdeg hEG
  have hΦlt : σ.Φ.degree < Φhat.degree := by
    rw [Polynomial.degree_eq_natDegree σ.hmonic.ne_zero,
      Polynomial.degree_eq_natDegree hΦne]
    exact_mod_cast hΦnatlt
  -- ## The child Bézout pair, P2-pinned at e′ = 1 (the (vii) split)
  obtain ⟨s', t', hbez', ht'0⟩ :
      ∃ s' t' : ℤ, (e' : ℤ) * s' + (h' : ℤ) * t' = 1 ∧ (e' = 1 → t' = 0) := by
    by_cases he1 : e' = 1
    · exact ⟨1, 0, by rw [he1]; push_cast; ring, fun _ => rfl⟩
    · refine ⟨Nat.gcdA e' h', Nat.gcdB e' h', ?_, fun h => absurd h he1⟩
      have hg := Nat.gcd_eq_gcd_ab e' h'
      rw [th.hcop] at hg
      exact_mod_cast hg.symm
  -- ## The lawful D.7(vi)-normalized residual carrier (S9w)
  obtain ⟨hexD, hwstrict⟩ := S9w_residualLaws σ hσ th s' t' hbez' ht'0
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := hexD.choose_spec
  -- ## The childW plumbing (S2/S3/S5) + parent basics
  obtain ⟨hdevMin, hSMW⟩ := S2_childW σ Φhat hmonΦ hdeg1 e' h'
  have hw1 : σ.w 1 = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    omega
  obtain ⟨hwPhi, hK1c⟩ := S3_childK1 σ Φhat hmonΦ hdeg1 e' h' th.he' th.hh' hw1
  obtain ⟨hwmulc, hvalgrpc⟩ := S5_childValuation σ hσ th
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
    exact h
  -- ## The child ultrametric law (developments add slotwise; parent hwult per slot)
  have hwult : ∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
      min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g') ≤
        childW σ Φhat e' h' (f + g') := by
    intro f g' hf hg' hfg
    obtain ⟨Bf, Nf, hdf, hmf⟩ := hdevMin f hf
    obtain ⟨Bg, Ng, hdg, hmg⟩ := hdevMin g' hg'
    set N := max Nf Ng with hN
    -- the slotwise sum is a development of f + g' at length N
    have hsub_f : Finset.range Nf ⊆ Finset.range N := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_left _ _))
    have hsub_g : Finset.range Ng ⊆ Finset.range N := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_right _ _))
    have hsum_f : f = ∑ j ∈ Finset.range N, Bf j * Φhat ^ j := by
      rw [hdf.2.2]
      refine Finset.sum_subset hsub_f ?_
      intro j hjN hjNf
      rw [hdf.2.1 j (by simpa using hjNf), zero_mul]
    have hsum_g : g' = ∑ j ∈ Finset.range N, Bg j * Φhat ^ j := by
      rw [hdg.2.2]
      refine Finset.sum_subset hsub_g ?_
      intro j hjN hjNg
      rw [hdg.2.1 j (by simpa using hjNg), zero_mul]
    have hdevS : IsDevelopment Φhat (f + g') (fun j => Bf j + Bg j) N := by
      refine ⟨?_, ?_, ?_⟩
      · intro j
        exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt (hdf.1 j) (hdg.1 j))
      · intro j hj
        show Bf j + Bg j = 0
        rw [hdf.2.1 j (le_trans (le_max_left _ _) hj),
          hdg.2.1 j (le_trans (le_max_right _ _) hj), add_zero]
      · rw [hsum_f, hsum_g, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => (add_mul (Bf j) (Bg j) (Φhat ^ j)).symm
    obtain ⟨hlow, jS, hjSN, hjSnz, hjSeq⟩ := hSMW (f + g') _ N hfg hdevS
    rw [hjSeq]
    -- per-slot case split on which side is present
    by_cases hBf : Bf jS = 0
    · have hBg : Bg jS ≠ 0 := by
        intro hBg
        exact hjSnz (by rw [hBf, hBg, add_zero])
      have hjNg : jS < Ng := by
        by_contra hge
        exact hBg (hdg.2.1 jS (le_of_not_gt hge))
      have hle := (hmg.1) jS hjNg hBg
      have hval : σ.w (Bf jS + Bg jS) = σ.w (Bg jS) := by rw [hBf, zero_add]
      calc min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g')
          ≤ childW σ Φhat e' h' g' := min_le_right _ _
        _ ≤ (e' : ℤ) * σ.w (Bg jS) + (jS : ℤ) * (h' : ℤ) := hle
        _ = (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by rw [hval]
    · by_cases hBg : Bg jS = 0
      · have hjNf : jS < Nf := by
          by_contra hge
          exact hBf (hdf.2.1 jS (le_of_not_gt hge))
        have hle := (hmf.1) jS hjNf hBf
        have hval : σ.w (Bf jS + Bg jS) = σ.w (Bf jS) := by rw [hBg, add_zero]
        calc min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g')
            ≤ childW σ Φhat e' h' f := min_le_left _ _
          _ ≤ (e' : ℤ) * σ.w (Bf jS) + (jS : ℤ) * (h' : ℤ) := hle
          _ = (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by rw [hval]
      · -- both slots present: the parent ultrametric law
        have hjNf : jS < Nf := by
          by_contra hge
          exact hBf (hdf.2.1 jS (le_of_not_gt hge))
        have hjNg : jS < Ng := by
          by_contra hge
          exact hBg (hdg.2.1 jS (le_of_not_gt hge))
        have hult := σ.hwult (Bf jS) (Bg jS) hBf hBg hjSnz
        have hlef := (hmf.1) jS hjNf hBf
        have hleg := (hmg.1) jS hjNg hBg
        have he'nn : (0 : ℤ) ≤ (e' : ℤ) := Int.natCast_nonneg e'
        rcases min_cases (σ.w (Bf jS)) (σ.w (Bg jS)) with ⟨hmin, hcmp⟩ | ⟨hmin, hcmp⟩
        · have : childW σ Φhat e' h' f ≤ (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by
            have h2 : σ.w (Bf jS) ≤ σ.w (Bf jS + Bg jS) := by rw [← hmin]; exact hult
            have h3 := mul_le_mul_of_nonneg_left h2 he'nn
            linarith
          exact le_trans (min_le_left _ _) this
        · have : childW σ Φhat e' h' g' ≤ (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by
            have h2 : σ.w (Bg jS) ≤ σ.w (Bf jS + Bg jS) := by rw [← hmin]; exact hult
            have h3 := mul_le_mul_of_nonneg_left h2 he'nn
            linarith
          exact le_trans (min_le_right _ _) this
  -- ## (S6b′): full scalars above the key weight, via the Moves final `L4_TRANSviii_b`
  have hS6b' : ∀ (ν : ℤ) (a : (↥(σ.nextField zbar))ˣ), σ.w Φhat < ν →
      ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
        hexD.choose.Rc B = LaurentPolynomial.C ((a : ↥(σ.nextField zbar))) *
          LaurentPolynomial.T (- t' * ν) := by
    intro ν a hν
    obtain ⟨B, hBc, hdig, hnz⟩ := L4_TRANSviii_b σ hσ.core ψ g th.hdeg th.hmonic th.hirr
      th.hne_z Φhat th.hlift zbar hzbar ν hν ((a : ↥(σ.nextField zbar)) : F)
      (SetLike.coe_mem _)
    have hane : ((a : ↥(σ.nextField zbar)) : F) ≠ 0 := by
      have := a.ne_zero
      exact fun h => this (Subtype.ext h)
    obtain ⟨hB0, hBw⟩ := hnz hane
    obtain ⟨c', hc'R, hc'F⟩ := hexD.choose.hS5' B hB0 hBc
    have hcs : (c' : ↥(σ.nextField zbar)) = (a : ↥(σ.nextField zbar)) := by
      apply Subtype.ext
      rw [hc'F, hdig]
    refine ⟨B, hB0, hBc, hBw, ?_⟩
    rw [hc'R, hcs, hBw]
  -- ## (S6a′): the coset-orbit realizers (V5 fixed-point coset form, blueprint §10
  -- Key Finding 2).  Above the threshold: hS6b′ with base b = 1 (exact scalars).
  -- Below (the strip): the V7 discharge, exactly as in S9a_final (σ′-free).
  have hS6a' : ∀ ν ∈ childWeightSet σ Φhat, ∃ b : (↥(σ.nextField zbar))ˣ,
      ∀ c : (↥(σ.nextField zbar))ˣ,
      ((c : ↥(σ.nextField zbar)) : F) ∈ σ.FQ →
      ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
        hexD.choose.Rc B
          = LaurentPolynomial.C ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) *
            LaurentPolynomial.T (- t' * ν) := by
    intro ν hν
    rcases lt_or_ge (σ.w Φhat) ν with hgt | hle
    · exact ⟨1, fun c _ => by rw [mul_one]; exact hS6b' ν c hgt⟩
    · -- BELOW-THRESHOLD STRIP (ν ≤ σ.w Φ̂): the V7 discharge (S9a_final's route,
      -- 2026-07-28) — σ′-free: the parent (S6a) coset realizer ridden up the K1
      -- minimizing slot, pinned into Rc through the carrier's own hS5' (raw
      -- digPrime, mfun ≡ 0). Same kernel in Moves-lemma form: `Moves.L4_TRANSviii_c`.
      exact V7_stripDischarge σ hσ th s' t' hbez' ht'0 hexD.choose hexD.choose_spec ν hν
  -- ## The literal (the S9a/S9b construction, verbatim)
  let σ' : Stage p F :=
    { e := e', h := h', s := s', t := t',
      he := th.he', hh := th.hh', hcop := th.hcop, hbez := hbez', he1t := ht'0,
      Φ := Φhat, hmonic := hmonΦ, hdeg := hdeg1,
      w := childW σ Φhat e' h',
      wPrev := σ.w,
      K := σ.nextField zbar, FQ := σ.FQ,
      hFQ_le := le_trans σ.hFQ_le (σ.le_nextField zbar),
      R := hexD.choose.Rc,
      hwmul := hwmulc,
      hwult := hwult,
      hvalgrp := hvalgrpc,
      hwΦ := hwPhi,
      hStretch := fun B hB hBc => L4_TRANSii σ Φhat e' h' _ hSMW B hB hBc,
      hR0 := hR0, hRne := hRne, hRmul := hRmul, hRadd := hRadd, hRlt := hRlt,
      hRΦ := hexD.choose.hRPhi,
      hK1 := by rw [hwPhi]; exact hK1c,
      hS5 := fun B hB hBc =>
        ⟨(hexD.choose.hS5' B hB hBc).choose, (hexD.choose.hS5' B hB hBc).choose_spec.1⟩,
      reps := σ.reps ++ [σ.Φ],
      hreps := fun ũ hũ => by
        rcases List.mem_append.mp hũ with h | h
        · exact ⟨(σ.hreps ũ h).1, lt_trans (σ.hreps ũ h).2 hΦlt⟩
        · rw [List.mem_singleton] at h
          subst h
          exact ⟨σ.hmonic.ne_zero, hΦlt⟩,
      Tvec := σ.Tvec.map (fun q => (q.1, s' * q.2)) ++ [(σ.Φ, s' * σ.t)],
      hTvec := by
        rw [List.map_append, List.map_map]
        simp only [Function.comp_def, List.map_cons, List.map_nil]
        rw [σ.hTvec],
      weightSet := childWeightSet σ Φhat,
      hWS := fun B hB hBc => ⟨B, hB, hBc, rfl⟩,
      hS6a := hS6a',
      hS6b := hS6b' }
  -- ## The transition record (all definitional on the literal)
  have td : TransitionData σ σ' Φhat e' h' zbar :=
    { child_key := rfl, child_e := rfl, child_h := rfl,
      child_field := rfl, field_grow := σ.le_nextField zbar,
      child_base := rfl, child_wPrev := fun f => rfl, threshold := rfl,
      child_slotmin := hSMW, child_reps := rfl }
  -- ## The vertex pin: exactly the carrier's S5′ pinned shape (mfun ≡ 0)
  have pin : VertexPin σ σ' Φhat zbar := hexD.choose.hS5'
  -- ## The round-5 transition core: record + rfl vector + the pinned dig frame
  have tc : TransitionCoreL σ σ' Φhat e' h' zbar :=
    { base := td,
      child_Tvec := rfl,
      child_dig_frame := by
        obtain ⟨_, h⟩ := VertexPin.to_child_dig_frame pin
        exact ⟨0, h⟩ }
  -- ## StageCore: the seven non-twist legs via S11a (the F-5 certificate), the
  -- twist-class legs from the carrier + the pin bridges
  obtain ⟨hwpm, hwpu, hrne, hprep, hwstr, hRneg', hpIaug⟩ :=
    S11a_coreTransport σ σ' hσ th tc
  have hΦin : inC Φhat σ.Φ := hΦlt
  have hWjump' : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → σ'.w f = σ'.w g →
      σ'.w f < σ'.w (f + g) → σ'.R f + σ'.R g = 0 := hWjump
  have htvec : TvecLaw σ' :=
    tvecLaw_of_tvecUnitLaw σ' (K1_tvecUnitLaw_of_pin σ σ' hσ tc pin hΦin)
  refine ⟨σ', tc, pin, fun f _ => rfl, ?_⟩
  exact
    { wPrev_mul := hwpm, wPrev_ult := hwpu,
      reps_nonempty := hrne, p_is_rep := hprep,
      w_strict := hwstr, w_jump := hWjump', R_neg := hRneg',
      tvec := htvec, prevIaug := hpIaug,
      slot := L2_slotDecomp σ' hwstr hWjump' hRneg',
      coeff := coeffCore_of_stage σ' hwpm }

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9c_coreAssembly
#print axioms LeanUrat.HC1.S9c_ungated_corner_refuted
