/-
HDISCHARGE_H1 — `H1/RCWitness.lean`: THE COMPILED [RC] WITNESS (the B-M2 REVISION-8
"UNWITNESSED-ON-FILE" debt, discharged; unit note
`lean/notes/openmath/H1_BM2_2026-08-06.md`, REVISION 8 record; ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`).

THE DEBT: no compiled instance fired the antecedents of the recentering-carrier
corollaries `landingKey_recentering_K0` / `historyCoherent_recentering_K0`
(`H1/Conformance.lean`) — HK25's `H₂rec` has its recentering node TERMINAL (no
interior recentering transition, and its `lift` is the junk 0, so no `LandingKey`
either); all on-file `LandingKey` witnesses are non-recentering.

WHAT IS COMPILED HERE (sorry-free; no new axioms; no existing statement touched;
positive gates — the corollaries FIRE on a concrete instance):
* `rcCenter`/`σ₂rc`/`rcLift` — a GENUINE recentering off HK25's unramified gate child
  `σ₁rec` (p = 2, F4, key fq = X² + 2X + 4 at the pair (1, 3)): the realizer C 8 has
  `σ₁rec.w (C 8) = 3 = σ₁rec.w Φ̂` (via the transition record's slot-minimum law) and
  a position-0 monomial-unit residual (via `child_dig_frame` at t = 0); `S10_recStage`
  (HC1's D.10/TRANS-RS capstone) then CONSTRUCTS the recentered stage σ₂rc with the
  recording relation `IsRecenteringCore σ₁rec σ₂rc rcCenter rcLift` and `StageCoreL`.
* `ν₁rc` — the recentering read on σ₁rec CARRYING THE CONSTRUCTED LIFT (HK25's ν₁rec
  shape at the recorded center/lift: e = g = 1, h = 3, ψ = X − C(rcCenter),
  side (s0, wSide) = (0, 1), γ = 3, line ⟨3, 3/2⟩, μ = 1).
* `landingKey_ν₁rc : LandingKey ν₁rc σ₂rc.Φ` — the FIRST compiled recentering-species
  `LandingKey` witness (the recorded lift is a genuine center realizer;
  Φtop = Φ̂ − lift).
* `H₃rc` = ⟨[HK23.ν₀ram, ν₁rc, ν₂rc]⟩ with `coherent_H₃rc` — the first coherent
  history with an INTERIOR recentering transition (i = 1 fires `IsRecenteringCore`);
  ν₂rc is the terminal recentering-species read on σ₂rc (center 1, h = 5,
  line ⟨5, 5/2⟩ — strict steepening 3/2 < 5/2; the ties close by `Stage.he1t`/`hbez`
  at σ₂rc.e = 1).
* **THE GATES** — `rc_landingKey_gate` and `rc_historyCoherent_gate`: both [RC]
  corollaries of `H1/Conformance.lean` fire, concluding
  `K0Conformant σ₁rec 1 1 σ₂rc.Φ`. The TWO DEDICATED recentering corollaries
  (`landingKey_recentering_K0`, `historyCoherent_recentering_K0`) are hereby
  NON-VACUOUS [REV 10 scope fix, the pass-8 finding-2 fold: the recentering branch
  of `readsOf_landing_K0` remains UNWITNESSED — no compiled `ReadsOf` run contains
  a recentering read — so the non-vacuity claim scopes to the two corollaries, not
  the whole [RC] perimeter]. Precision: `rc_landingKey_gate` fires on `ν₁rc` /
  `landingKey_ν₁rc` DIRECTLY (ν₁rc is also H₃rc's node 1); `rc_historyCoherent_gate`
  fires on `H₃rc`/`coherent_H₃rc`.
* **THE ACTUAL-PAIR GATES [REV 10]** — `rc_landingKey_gate_actual` and
  `rc_historyCoherent_gate_actual`: the synthetic conclusions transported to
  ν₁rc's ACTUAL pair `K0Conformant ν₁rc.σ ν₁rc.g ν₁rc.e σ₂rc.Φ` via
  `k0_actual_of_recentering` (`H1/RecParamE.lean` — the pass-8 finding-1 transport:
  `Node.hspecRec` makes the actual pair (1, 1)).

* **THE WIRING GATE [REV 12]** — `rc_wireG_gate`: the REC-WIRE-G corollary
  `recParam_eg_of_recentering` (`H1/RecParamE.lean`, where REC-WIRE-G is now
  DISCHARGED) fires at H₃rc's interior recentering node 1, non-vacuously.

WHAT IS NOT CLAIMED: nothing beyond inhabitation, the hspecRec-transport, and the
[REV 12] wiring-corollary firing — the open REC-SL legs, GRADED-READ, and SITE-EXH
residues, and the RG-2 fence display of `H1/Conformance.lean` are all unchanged
(REC-PARAM's compiled e-half at its transition scope, the [REV 10] transport
lemma, and the [REV 12] REC-WIRE-G kernel + corollary pair are the sibling unit
`H1/RecParamE.lean`).
-/
import LeanUrat.HC2.HK25_recGate
import LeanUrat.HC1.S10_recStage
import LeanUrat.Scaffold.HDischarge.H1.Conformance
import LeanUrat.Scaffold.HDischarge.H1.RecParamE

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.Scaffold.HDischarge.H1

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesJ

namespace RCW

/-! ### §1 — the recentering realizer at the gate child σ₁rec (C 8 at weight 3) -/

private lemma fq_deg : U31.fq.degree = 2 := by
  rw [Polynomial.degree_eq_natDegree U31.fq_monic.ne_zero, U31.fq_natDegree]
  rfl

private lemma inC_fq_C8 : (Polynomial.C (8 : ℤ_[2])).degree < U31.fq.degree := by
  rw [fq_deg]
  exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)

private lemma C8_ne : (Polynomial.C (8 : ℤ_[2])) ≠ 0 :=
  Polynomial.C_ne_zero.mpr (by norm_num)

private lemma bw_C8 : U31.bw (Polynomial.C (8 : ℤ_[2])) = 3 := by
  have h : (8 : ℤ_[2]) = 2 ^ 3 * 1 := by norm_num
  rw [h, HK13R.bw_C_two_pow_mul HK13R.ρ_one_ne]
  norm_num

/-- The gate child's weight of the realizer: `σ₁rec.w (C 8) = 3` (the recorded
slot-minimum law of the transition record, at the one-slot self-development). -/
private lemma w_C8 : HK25.σ₁rec.w (Polynomial.C (8 : ℤ_[2])) = 3 := by
  have hdev : IsDevelopment U31.fq (Polynomial.C (8 : ℤ_[2]))
      (fun j => if j = 0 then Polynomial.C (8 : ℤ_[2]) else 0) 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      dsimp only
      split_ifs
      · exact inC_fq_C8
      · rw [Polynomial.degree_zero, fq_deg]
        decide
    · intro j hj
      dsimp only
      rw [if_neg (by omega)]
    · rw [Finset.sum_range_one]
      dsimp only
      rw [if_pos rfl, pow_zero, mul_one]
  obtain ⟨-, j, hjlt, -, heq⟩ :=
    HK25.tcl_rec0.base.child_slotmin (Polynomial.C (8 : ℤ_[2]))
      (fun j => if j = 0 then Polynomial.C (8 : ℤ_[2]) else 0) 1 C8_ne hdev
  have hj0 : j = 0 := by omega
  subst hj0
  simp at heq
  rw [heq]
  exact bw_C8

private lemma wΦ₁ : HK25.σ₁rec.w HK25.σ₁rec.Φ = 3 := by
  have h := HK25.σ₁rec.hwΦ
  rw [HK25.σ₁rec_pins.2.1] at h
  exact_mod_cast h

/-- **The recentering-realizer existence at σ₁rec** — `tt := C 8` realizes SOME
nonzero center: weight 3 = w(Φ̂) (`w_C8`/`wΦ₁`), position-0 monomial-unit residual
(the transition record's `child_dig_frame` at `σ₁rec.t = 0`; the digit scalar is the
recorded unit `c'`, whose value we never need). Exactly `S10_recStage`'s `hlift` row. -/
private lemma realizer_ex : ∃ cc : ↥HK25.σ₁rec.K, cc ≠ 0 ∧
    ∃ tt : Polynomial ℤ_[2], tt ≠ 0 ∧ inC HK25.σ₁rec.Φ tt ∧
      HK25.σ₁rec.w tt = HK25.σ₁rec.w HK25.σ₁rec.Φ ∧
      HK25.σ₁rec.R tt = LaurentPolynomial.C cc * LaurentPolynomial.T 0 := by
  obtain ⟨mfun, hdig⟩ := HK25.tcl_rec0.child_dig_frame
  obtain ⟨c', hR, -⟩ := hdig (Polynomial.C (8 : ℤ_[2])) C8_ne inC_fq_C8
  refine ⟨(c' : ↥HK25.σ₁rec.K), c'.ne_zero, Polynomial.C (8 : ℤ_[2]), C8_ne, ?_, ?_, ?_⟩
  · show (Polynomial.C (8 : ℤ_[2])).degree < HK25.σ₁rec.Φ.degree
    rw [HK25.σ₁rec_Φ]
    exact inC_fq_C8
  · rw [w_C8, wΦ₁]
  · rw [hR, HK25.σ₁rec_pins.2.2.2, neg_zero, zero_mul]

/-! ### §2 — the recentered stage σ₂rc, CONSTRUCTED (S10_recStage = D.10/TRANS-RS) -/

private lemma score₁ : StageCoreL HK25.σ₁rec :=
  (gateChildStage_exists 1 3 (le_refl 1) (by norm_num) (by norm_num)
    HK47.transHyp_gate.hiaug).choose_spec.2.1

/-- The recorded center (the classical digit unit of the realizer C 8). -/
noncomputable def rcCenter : ↥HK25.σ₁rec.K := realizer_ex.choose

lemma rcCenter_ne : rcCenter ≠ 0 := realizer_ex.choose_spec.1

private lemma recData : ∃ (σ' : Stage 2 F4) (tt : Polynomial ℤ_[2]),
    IsRecenteringCore HK25.σ₁rec σ' rcCenter tt ∧ StageCoreL σ' :=
  HC1.S10_recStage HK25.σ₁rec score₁ HK25.σ₁rec_pins.1 rcCenter rcCenter_ne
    realizer_ex.choose_spec.2

/-- **The recentered gate stage** — S10's constructed child of σ₁rec at the recorded
center (key Φ̂ − lift, same w/wPrev/K/FQ/weightSet). -/
noncomputable def σ₂rc : Stage 2 F4 := recData.choose

/-- **The recorded lift** realizing the center (S10's chosen realizer). -/
noncomputable def rcLift : Polynomial ℤ_[2] := recData.choose_spec.choose

/-- THE RECORDING RELATION — the interior recentering transition's coherence carrier. -/
lemma recCore : IsRecenteringCore HK25.σ₁rec σ₂rc rcCenter rcLift :=
  recData.choose_spec.choose_spec.1

lemma score₂ : StageCoreL σ₂rc := recData.choose_spec.choose_spec.2

lemma σ₂rc_e : σ₂rc.e = 1 := by
  obtain ⟨-, h, -⟩ := recCore.base
  exact h

lemma rcLift_inC : inC HK25.σ₁rec.Φ rcLift := by
  obtain ⟨-, -, -, h, -⟩ := recCore.base
  exact h

lemma rcLift_ne : rcLift ≠ 0 := by
  obtain ⟨-, -, -, -, h, -⟩ := recCore.base
  exact h

lemma rcLift_w : HK25.σ₁rec.w rcLift = HK25.σ₁rec.w HK25.σ₁rec.Φ := by
  obtain ⟨-, -, -, -, -, h, -⟩ := recCore.base
  exact h

lemma rcLift_R : HK25.σ₁rec.R rcLift
    = LaurentPolynomial.C rcCenter * LaurentPolynomial.T 0 := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := recCore.base
  exact h

lemma σ₂rc_Φ : σ₂rc.Φ = HK25.σ₁rec.Φ - rcLift := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := recCore.base
  exact h

lemma σ₂rc_Φ_natDegree : σ₂rc.Φ.natDegree = 2 := by
  have hlt : rcLift.degree < HK25.σ₁rec.Φ.degree := rcLift_inC
  rw [σ₂rc_Φ, Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_sub_eq_left_of_degree_lt hlt), HK25.σ₁rec_Φ, U31.fq_natDegree]

/-! ### §3 — the recentering read ν₁rc carrying the constructed lift -/

lemma rcCenter_F4_ne : ((rcCenter : ↥HK25.σ₁rec.K) : F4) ≠ 0 := by
  intro h0
  exact rcCenter_ne (HK25.σ₁rec.K.subtype.injective (by simpa using h0))

/-- **The recentering read** ν₁rc on the unramified gate child, at the RECORDED
center/lift (HK25's ν₁rec shape — e = g = 1, h = 3, side (0, 1), γ = 3,
line ⟨3, 3/2⟩, μ = 1 — with ψ = X − C(rcCenter), z̄ = the center's value, and the
CONSTRUCTED lift in the lift field: unlike HK25's junk-0 lift, this node fires
`LandingKey`'s recentering leg). -/
noncomputable def ν₁rc : Node 2 F4 where
  species := ReadSpecies.recentering
  σ := HK25.σ₁rec
  e := 1
  h := 3
  s := 1
  t := 0
  g := 1
  μ := 1
  a := 0
  s0 := 0
  wSide := 1
  Dwidth := 2
  line := ⟨3, 3/2⟩
  ustar := 0
  gam := 3
  zbar := Units.mk0 ((rcCenter : ↥HK25.σ₁rec.K) : F4) rcCenter_F4_ne
  center := rcCenter
  lift := rcLift
  ψ := Polynomial.X - Polynomial.C rcCenter
  pat := fun k => if k = 0 then -rcCenter else 1
  Ranch := Polynomial.X - Polynomial.C rcCenter
  he := le_refl 1
  hh := by norm_num
  hcop := by norm_num
  hbez := by norm_num
  hbezCanon := by norm_num
  hg := le_refl 1
  hμ := le_refl 1
  hEdvd := one_dvd 1
  hDwidth := by rw [HK25.σ₁rec_Φ]; exact U31.fq_natDegree.symm
  hψmonic := Polynomial.monic_X_sub_C rcCenter
  hψdeg := Polynomial.natDegree_X_sub_C rcCenter
  hψirr := Polynomial.irreducible_X_sub_C rcCenter
  hRanch := by
    show (Polynomial.X - Polynomial.C rcCenter : Polynomial ↥HK25.σ₁rec.K)
        = ∑ k ∈ Finset.range 2,
            Polynomial.C (if k = 0 then -rcCenter else 1)
              * (Polynomial.X : Polynomial ↥HK25.σ₁rec.K) ^ k
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [if_pos, if_neg (one_ne_zero : (1 : ℕ) ≠ 0), map_neg, Polynomial.C_1]
    ring
  hpat0 := by
    show (if (0 : ℕ) = 0 then -rcCenter else 1) ≠ 0
    rw [if_pos rfl]
    exact neg_ne_zero.mpr rcCenter_ne
  hpatTop := by
    show (if (1 / 1 : ℕ) = 0 then -rcCenter else 1) ≠ 0
    rw [if_neg (by norm_num)]
    exact one_ne_zero
  hAnchor := by norm_num
  hLineU := by
    show (3 : ℚ) - 3 / 2 * (((0 + 1) * 2 : ℕ) : ℚ) = 0
    norm_num
  hOrd := by
    constructor
    · rw [pow_one]
    · intro hdvd
      have hne : (Polynomial.X - Polynomial.C rcCenter
          : Polynomial ↥HK25.σ₁rec.K) ≠ 0 :=
        (Polynomial.monic_X_sub_C rcCenter).ne_zero
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at hle
      omega
  hzbarRoot := by
    show Polynomial.eval₂ HK25.σ₁rec.K.subtype
        (((Units.mk0 ((rcCenter : ↥HK25.σ₁rec.K) : F4) rcCenter_F4_ne : F4ˣ)) : F4)
        (Polynomial.X - Polynomial.C rcCenter) = 0
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp
  hspecInc := by intro h; simp at h
  hspecRec := fun _ => ⟨rfl, rfl⟩
  hspecRecCenter := fun _ => ⟨rfl, rfl⟩

/-! ### §4 — GATE A: the recentering `LandingKey` witness, and the corollary fires -/

/-- **The first compiled recentering-species `LandingKey`**: the recorded lift is a
genuine center realizer and the landing key is Φ̂ − lift = σ₂rc.Φ. -/
lemma landingKey_ν₁rc : LandingKey ν₁rc σ₂rc.Φ :=
  ⟨fun _ => ⟨rcLift_inC, rcLift_ne, rcLift_w, rcLift_R, σ₂rc_Φ⟩,
   fun hne => absurd rfl hne⟩

/-- **GATE A (positive)**: `landingKey_recentering_K0`'s antecedent is inhabited and
the corollary FIRES — the [RC] landing-carrier leg of Theorem LIFT-CONF's compiled
perimeter is non-vacuous. -/
theorem rc_landingKey_gate : K0Conformant HK25.σ₁rec 1 1 σ₂rc.Φ :=
  landingKey_recentering_K0 ν₁rc σ₂rc.Φ landingKey_ν₁rc rfl

/-- **GATE A at the ACTUAL pair [REV 10]**: the synthetic conclusion transported to
ν₁rc's actual read pair via `k0_actual_of_recentering` (`Node.hspecRec` makes the
actual pair (1, 1)) — the landing-carrier [RC] conclusion at (ν.e, ν.g) itself. -/
theorem rc_landingKey_gate_actual :
    K0Conformant ν₁rc.σ ν₁rc.g ν₁rc.e σ₂rc.Φ :=
  k0_actual_of_recentering ν₁rc σ₂rc.Φ rfl rc_landingKey_gate

/-! ### §5 — the terminal read ν₂rc on the recentered stage -/

/-- **The terminal read** ν₂rc on σ₂rc — HK25's ν₁rec recipe re-keyed to the
recentered stage at the steeper pair (1, 5): recentering species at center 1,
ψ = X − C 1, side (0, 1), γ = 5, line ⟨5, 5/2⟩ (strict steepening over 3/2), μ = 1,
Ranch = X + 1 (char 2). Terminal — its own transition never fires. -/
noncomputable def ν₂rc : Node 2 F4 where
  species := ReadSpecies.recentering
  σ := σ₂rc
  e := 1
  h := 5
  s := 1
  t := 0
  g := 1
  μ := 1
  a := 0
  s0 := 0
  wSide := 1
  Dwidth := 2
  line := ⟨5, 5/2⟩
  ustar := 0
  gam := 5
  zbar := 1
  center := 1
  lift := 0
  ψ := Polynomial.X - Polynomial.C 1
  pat := fun _ => 1
  Ranch := Polynomial.X + 1
  he := le_refl 1
  hh := by norm_num
  hcop := by norm_num
  hbez := by norm_num
  hbezCanon := by norm_num
  hg := le_refl 1
  hμ := le_refl 1
  hEdvd := one_dvd 1
  hDwidth := σ₂rc_Φ_natDegree.symm
  hψmonic := Polynomial.monic_X_sub_C 1
  hψdeg := Polynomial.natDegree_X_sub_C 1
  hψirr := Polynomial.irreducible_X_sub_C 1
  hRanch := by
    show (Polynomial.X + 1 : Polynomial ↥σ₂rc.K)
        = ∑ k ∈ Finset.range 2,
            (Polynomial.C (1 : ↥σ₂rc.K)
              * (Polynomial.X : Polynomial ↥σ₂rc.K) ^ k)
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp
    ring
  hpat0 := one_ne_zero
  hpatTop := one_ne_zero
  hAnchor := by norm_num
  hLineU := by
    show (5 : ℚ) - 5 / 2 * (((0 + 1) * 2 : ℕ) : ℚ) = 0
    norm_num
  hOrd := by
    have h11 : (1 : F4) + 1 = 0 := by
      rw [show (1 : F4) + 1 = 2 from by norm_num]
      exact_mod_cast CharP.cast_eq_zero F4 2
    have hneg : (-1 : ↥σ₂rc.K) = 1 := by
      apply σ₂rc.K.subtype.injective
      simp only [map_neg, map_one]
      exact neg_eq_iff_add_eq_zero.mpr h11
    have hψeq : (Polynomial.X - Polynomial.C (1 : ↥σ₂rc.K))
        = Polynomial.X + 1 := by
      rw [sub_eq_add_neg, ← Polynomial.C_neg, hneg, Polynomial.C_1]
    refine ⟨?_, ?_⟩
    · rw [pow_one]; exact dvd_of_eq hψeq
    · rw [hψeq]
      intro hdvd
      have hne : (Polynomial.X + 1 : Polynomial ↥σ₂rc.K) ≠ 0 := by
        rw [← Polynomial.C_1]; exact (Polynomial.monic_X_add_C 1).ne_zero
      have hnd : (Polynomial.X + 1 : Polynomial ↥σ₂rc.K).natDegree = 1 := by
        rw [← Polynomial.C_1]; exact Polynomial.natDegree_X_add_C 1
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne
      rw [Polynomial.natDegree_pow, hnd] at hle
      omega
  hzbarRoot := by
    show Polynomial.eval₂ σ₂rc.K.subtype ((1 : F4ˣ) : F4)
        (Polynomial.X - Polynomial.C 1) = 0
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp
  hspecInc := by intro h; simp at h
  hspecRec := fun _ => ⟨rfl, rfl⟩
  hspecRecCenter := by
    intro _
    refine ⟨rfl, ?_⟩
    simp

/-! ### §6 — the 3-node history with the INTERIOR recentering transition -/

/-- **THE INTERIOR-RECENTERING GATE HISTORY** H₃rc: bStageP root read → the
recentering read ν₁rc on the unramified (1, 3) child (INTERIOR — its transition
fires) → the terminal read ν₂rc on the recentered stage. -/
noncomputable def H₃rc : History 2 F4 where
  nodes := [HK23.ν₀ram, ν₁rc, ν₂rc]
  nonempty := by simp
  root_iff := by
    intro j hj
    have hj3 : j < 3 := by simpa using hj
    interval_cases j
    · exact iff_of_true rfl rfl
    · refine iff_of_false ?_ (by omega)
      show ν₁rc.species ≠ ReadSpecies.root
      intro hcontra
      exact ReadSpecies.noConfusion hcontra
    · refine iff_of_false ?_ (by omega)
      show ν₂rc.species ≠ ReadSpecies.root
      intro hcontra
      exact ReadSpecies.noConfusion hcontra

lemma H₃rc_len : H₃rc.nodes.length = 3 := rfl

lemma H₃rc_str0 : H₃rc.strFrame 0 = 1 := rfl

lemma H₃rc_str1 : H₃rc.strFrame 1 = 1 := rfl

lemma H₃rc_str2 : H₃rc.strFrame 2 = 1 := rfl

/-- **COHERENCE of H₃rc** — the i = 0 leg is HK25's (S-a) root transition verbatim
(regrade `HK23.regrade_gate`, lift `HK23.nodeLift_ν₀ram`, record `HK25.tcl_rec`);
the i = 1 leg is THE INTERIOR RECENTERING: `IsRecenteringCore σ₁rec σ₂rc` at the
node's recorded center/lift (= `recCore`, S10-constructed), ties closed by
`Stage.he1t`/`hbez` at σ₂rc.e = 1, window 0 + 1 ≤ 1 = μ₁, width chain
D₂ = 2 = 1·1·2, strict steepening 3/2 < 5/2. -/
theorem coherent_H₃rc : HistoryCoherent H₃rc := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hj
    show (Polynomial.X : Polynomial ℤ_[2]).natDegree = 1
    exact Polynomial.natDegree_X
  · -- slope law
    intro i hi
    have hi3 : i < 3 := H₃rc_len ▸ hi
    interval_cases i
    · show (1 : ℚ) * (((1 : ℕ) : ℚ) * ((H₃rc.strFrame 0 : ℕ) : ℚ) * ((1 : ℕ) : ℚ))
          = ((1 : ℕ) : ℚ)
      rw [H₃rc_str0]
      norm_num
    · show (3 / 2 : ℚ) * (((1 : ℕ) : ℚ) * ((H₃rc.strFrame 1 : ℕ) : ℚ) * ((2 : ℕ) : ℚ))
          = ((3 : ℕ) : ℚ)
      rw [H₃rc_str1]
      norm_num
    · show (5 / 2 : ℚ) * (((1 : ℕ) : ℚ) * ((H₃rc.strFrame 2 : ℕ) : ℚ) * ((2 : ℕ) : ℚ))
          = ((5 : ℕ) : ℚ)
      rw [H₃rc_str2]
      norm_num
  · -- γ-tie
    intro i hi
    have hi3 : i < 3 := H₃rc_len ▸ hi
    interval_cases i
    · show (((4 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((H₃rc.strFrame 0 : ℕ) : ℚ) * (0 : ℚ))
          + (((0 + 4 : ℕ)) : ℚ) * ((1 : ℕ) : ℚ)
      rw [H₃rc_str0]
      norm_num
    · show (((3 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((H₃rc.strFrame 1 : ℕ) : ℚ) * (0 : ℚ))
          + (((0 + 1 : ℕ)) : ℚ) * ((3 : ℕ) : ℚ)
      rw [H₃rc_str1]
      norm_num
    · show (((5 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((H₃rc.strFrame 2 : ℕ) : ℚ) * (0 : ℚ))
          + (((0 + 1 : ℕ)) : ℚ) * ((5 : ℕ) : ℚ)
      rw [H₃rc_str2]
      norm_num
  · -- the transition legs at i = 0 (root, non-recentering) and i = 1 (RECENTERING)
    intro i hi
    have hi3 : i + 1 < 3 := H₃rc_len ▸ hi
    have hii : i < 2 := by omega
    interval_cases i
    · -- i = 0: HK25's (S-a) root transition, verbatim
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro hcontra
        exact absurd hcontra (fun h => ReadSpecies.noConfusion h)
      · intro _
        refine ⟨rfl, HK23.σVgate, HK23.regrade_gate, ?_, ?_⟩
        · show IsNodeLift HK23.ν₀ram HK25.σ₁rec.Φ
          rw [HK25.σ₁rec_Φ]
          exact HK23.nodeLift_ν₀ram
        · show TransitionCoreL HK23.σVgate HK25.σ₁rec HK25.σ₁rec.Φ 1 3 U31.ν₀.zbar
          rw [HK25.σ₁rec_Φ]
          exact HK25.tcl_rec
      · intro _
        show HK25.σ₁rec.s = 1
        exact HK25.σ₁rec_pins.2.2.1
      · intro _
        show HK25.σ₁rec.t = 0
        exact HK25.σ₁rec_pins.2.2.2
      · show (0 + 1 : ℕ) ≤ 2
        omega
      · show (2 : ℕ) = 1 * 2 * 1
        norm_num
      · show (1 : ℚ) < 3 / 2
        norm_num
    · -- i = 1: THE INTERIOR RECENTERING TRANSITION
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _
        exact recCore
      · intro hne
        exact absurd rfl hne
      · intro _
        show σ₂rc.s = 1
        have hb := σ₂rc.hbez
        rw [σ₂rc_e, σ₂rc.he1t σ₂rc_e] at hb
        simpa using hb
      · intro _
        show σ₂rc.t = 0
        exact σ₂rc.he1t σ₂rc_e
      · show (0 + 1 : ℕ) ≤ 1
        omega
      · show (2 : ℕ) = 1 * 1 * 2
        norm_num
      · show (3 / 2 : ℚ) < 5 / 2
        norm_num

/-! ### §7 — GATE B: the history-carrier corollary fires at the interior recentering -/

/-- **GATE B (positive)**: `historyCoherent_recentering_K0`'s antecedent is inhabited
— H₃rc is coherent with node 1 an INTERIOR recentering — and the corollary FIRES,
concluding (K0) at the synthetic pair for the recentered child key. The [RC]
history-carrier leg of Theorem LIFT-CONF's compiled perimeter is non-vacuous. -/
theorem rc_historyCoherent_gate : K0Conformant HK25.σ₁rec 1 1 σ₂rc.Φ := by
  have hlen : H₃rc.nodes.length = 3 := rfl
  exact historyCoherent_recentering_K0 H₃rc coherent_H₃rc 1 (by omega) rfl

/-- **GATE B at the ACTUAL pair [REV 10]**: the synthetic conclusion transported to
ν₁rc's actual read pair via `k0_actual_of_recentering` (ν₁rc = H₃rc's interior
recentering node; `Node.hspecRec` makes the actual pair (1, 1)). -/
theorem rc_historyCoherent_gate_actual :
    K0Conformant ν₁rc.σ ν₁rc.g ν₁rc.e σ₂rc.Φ :=
  k0_actual_of_recentering ν₁rc σ₂rc.Φ rfl rc_historyCoherent_gate

/-- **GATE C [REV 12]: REC-WIRE-G FIRES at the interior recentering** — the non-fiat
wiring corollary `recParam_eg_of_recentering` (`H1/RecParamE.lean`) instantiates at
H₃rc's node 1 (the interior recentering read ν₁rc), deriving `ν₁rc.e = 1 ∧
ν₁rc.g = 1` from the coherence wiring (kernel degree preservation + the width chain
D₂ = 2 = 1·1·2), NOT from `Node.hspecRec`.  The conclusion is of course also
definitional for this concrete node — the gate's content is that the corollary's
antecedents are inhabited on file. -/
theorem rc_wireG_gate : ν₁rc.e = 1 ∧ ν₁rc.g = 1 := by
  have hlen : H₃rc.nodes.length = 3 := rfl
  exact recParam_eg_of_recentering H₃rc coherent_H₃rc 1 (by omega) rfl

end RCW

end LeanUrat.Scaffold.HDischarge.H1

#print axioms LeanUrat.Scaffold.HDischarge.H1.RCW.recCore
#print axioms LeanUrat.Scaffold.HDischarge.H1.RCW.landingKey_ν₁rc
#print axioms LeanUrat.Scaffold.HDischarge.H1.RCW.rc_landingKey_gate
#print axioms LeanUrat.Scaffold.HDischarge.H1.RCW.coherent_H₃rc
#print axioms LeanUrat.Scaffold.HDischarge.H1.RCW.rc_historyCoherent_gate
#print axioms LeanUrat.Scaffold.HDischarge.H1.RCW.rc_wireG_gate
#print axioms LeanUrat.Scaffold.HDischarge.H1.RCW.rc_landingKey_gate_actual
#print axioms LeanUrat.Scaffold.HDischarge.H1.RCW.rc_historyCoherent_gate_actual
