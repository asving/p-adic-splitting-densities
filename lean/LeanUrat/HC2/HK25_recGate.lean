import Mathlib
import LeanUrat.HC2.HK23_twoNodeGatePos
import LeanUrat.HC2.HK15_gateChildCarrier
import LeanUrat.HC2.U1_negWitness

/-!
# HK-25 — the recentering-ended gate history H₂ʳ and the UNCONDITIONAL U1-neg discharge
(post-wave unit 2, 2026-07-31; BP2 Block G unit HK-25, unblocked by the HK-06 wave)

`U1_negWitness.retiredKeysExist_false_of_witness` refutes the retired `hcoh`-keyed
`keys_exist` sentence GIVEN any coherent history whose LAST node is a RECENTERING — its
recorded honesty perimeter was the INHABITATION of that class.  This leaf builds the
witness and closes the perimeter:

* `σ₁rec` — the UNRAMIFIED gate child stage at the pair (1, 3): HK-15's discharged
  `gateChildStage` at the gate-pins tuple (1, 3, 1, 0) (S9-built, `TransitionCoreL
  bStageP σ₁rec fq 1 3` + StageCoreL + K = K₂⟮r₀⟯ = F4).  A recentering NODE forces
  `e = 1` (`Node.hspecRec`), so HK23's ramified child (pair (2,5)) cannot carry it —
  the (1,3) child is exactly the missing unramified carrier.
* `tcl_rec` — the transition record transported to the σV parent (`HK23.σVgate`;
  every field the record reads is definitionally shared — the HK23 `tcl_gate` idiom).
* `ν₁rec` — the RECENTERING-species read on σ₁rec: `e = g = 1`, `h = 3`,
  `ψ = X − C 1` at center 1 (`z̄₁ = 1`), single-cell side `s0 = 0, wSide = 1`,
  `γ₁ = 3`, `line = ⟨3, 3/2⟩` (slope law `(3/2)·(1·1·2) = 3`), `u*₁ = 0`, `μ = 1`,
  `Ranch = X + 1` (`(X − C 1) ∥ Ranch` in char 2).
* `H₂rec` = ⟨[HK23.ν₀ram, ν₁rec]⟩ with `coherent_H₂rec : HistoryCoherent H₂rec` —
  the root's (S-a) leg re-uses HK23's regrade (`σVgate`, `regrade_gate`) and lift
  (`nodeLift_ν₀ram`), keyed at the CHILD pair (1, 3) through `tcl_rec`; the Bézout
  ties fire at `σ₁rec.e = 1` and close by HK-15's gate pins (s = 1, t = 0).
* **`retiredKeysExist_false : ¬ RetiredKeysExistStmt 2 F4`** — THE DISCHARGE: the
  first UNCONDITIONAL compiled negation of the retired sentence (U1neg's surgery +
  this witness).  `keysLawful_hcoh_false` is the consumer-facing `KeysLawful` form.

Everything Lean-core (in-file `#print axioms`).  Statements elsewhere untouched.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace HK25

/-! ### §1 — the unramified gate child at the pair (1, 3) -/

/-- The unramified gate child stage — HK-15's `gateChildStage` at the discharged
gate-pins tuple (1, 3, 1, 0) (the `gateChildStage_gate_pins` instance). -/
noncomputable def σ₁rec : Stage 2 F4 :=
  gateChildStage 1 3 1 0 (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => rfl) HK47.transHyp_gate.hiaug

lemma σ₁rec_Φ : σ₁rec.Φ = U31.fq :=
  gateChildStage_Phi 1 3 1 0 (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => rfl) HK47.transHyp_gate.hiaug

lemma σ₁rec_pins : σ₁rec.e = 1 ∧ σ₁rec.h = 3 ∧ σ₁rec.s = 1 ∧ σ₁rec.t = 0 := by
  obtain ⟨he, hh, hst⟩ := gateChildStage_pair 1 3 1 0 (le_refl 1) (by norm_num)
    (by norm_num) (by norm_num) (fun _ => rfl) HK47.transHyp_gate.hiaug
  obtain ⟨hs, ht⟩ := hst rfl
  exact ⟨he, hh, hs, ht⟩

/-- The raw transition record at the bStageP parent (the S9 construction's output). -/
lemma tcl_rec0 : TransitionCoreL bStageP σ₁rec U31.fq 1 3 gateRoot :=
  (gateChildStage_exists 1 3 (le_refl 1) (by norm_num) (by norm_num)
    HK47.transHyp_gate.hiaug).choose_spec.1

/-- The transition record transported to the σV parent (the HK23 `tcl_gate` idiom:
every parent field `TransitionCoreL` reads is definitionally shared between `bStageP`
and `HK23.σVgate`; `gateRoot` is definitionally `U31.ν₀.zbar`). -/
lemma tcl_rec : TransitionCoreL HK23.σVgate σ₁rec U31.fq 1 3 U31.ν₀.zbar := by
  obtain ⟨base, hTvec, hdig⟩ := tcl_rec0
  exact ⟨⟨base.child_key, base.child_e, base.child_h, base.child_field, base.field_grow,
    base.child_base, base.child_wPrev, base.threshold, base.child_slotmin,
    base.child_reps⟩, hTvec, hdig⟩

/-! ### §2 — the recentering child node -/

/-- **The recentering read** ν₁rec on the unramified gate child: `e = g = 1`, `h = 3`,
`ψ = X − C 1` at the recorded center 1, `z̄₁ = 1`, side `s0 = 0, wSide = 1`, `γ₁ = 3`,
`u*₁ = 0` at the endpoint base index 2, `line = ⟨3, 3/2⟩`, `μ = 1`, `a = 0`,
`Ranch = X + 1` (= ψ in char 2). -/
noncomputable def ν₁rec : Node 2 F4 where
  species := ReadSpecies.recentering
  σ := σ₁rec
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
  hDwidth := by rw [σ₁rec_Φ]; exact U31.fq_natDegree.symm
  hψmonic := Polynomial.monic_X_sub_C 1
  hψdeg := Polynomial.natDegree_X_sub_C 1
  hψirr := Polynomial.irreducible_X_sub_C 1
  hRanch := by
    show (Polynomial.X + 1 : Polynomial ↥σ₁rec.K)
        = ∑ k ∈ Finset.range 2,
            (Polynomial.C (1 : ↥σ₁rec.K)
              * (Polynomial.X : Polynomial ↥σ₁rec.K) ^ k)
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp
    ring
  hpat0 := one_ne_zero
  hpatTop := one_ne_zero
  hAnchor := by norm_num
  hLineU := by
    show (3 : ℚ) - 3 / 2 * (((0 + 1) * 2 : ℕ) : ℚ) = 0
    norm_num
  hOrd := by
    have h2 : (2 : F4) = 0 := by exact_mod_cast CharP.cast_eq_zero F4 2
    have h11 : (1 : F4) + 1 = 0 := by
      rw [show (1 : F4) + 1 = 2 from by norm_num]; exact h2
    have hnegF : (-1 : F4) = 1 := neg_eq_iff_add_eq_zero.mpr h11
    have hneg : (-1 : ↥σ₁rec.K) = 1 := by
      apply σ₁rec.K.subtype.injective
      simp only [map_neg, map_one]
      exact hnegF
    have hψeq : (Polynomial.X - Polynomial.C (1 : ↥σ₁rec.K))
        = Polynomial.X + 1 := by
      rw [sub_eq_add_neg, ← Polynomial.C_neg, hneg, Polynomial.C_1]
    refine ⟨?_, ?_⟩
    · rw [pow_one]; exact dvd_of_eq hψeq
    · rw [hψeq]
      intro hdvd
      have hne : (Polynomial.X + 1 : Polynomial ↥σ₁rec.K) ≠ 0 := by
        rw [← Polynomial.C_1]; exact (Polynomial.monic_X_add_C 1).ne_zero
      have hnd : (Polynomial.X + 1 : Polynomial ↥σ₁rec.K).natDegree = 1 := by
        rw [← Polynomial.C_1]; exact Polynomial.natDegree_X_add_C 1
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne
      rw [Polynomial.natDegree_pow, hnd] at hle
      omega
  hzbarRoot := by
    show Polynomial.eval₂ σ₁rec.K.subtype ((1 : F4ˣ) : F4)
        (Polynomial.X - Polynomial.C 1) = 0
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp
  hspecInc := by intro h; simp at h
  hspecRec := fun _ => ⟨rfl, rfl⟩
  hspecRecCenter := by
    intro _
    refine ⟨rfl, ?_⟩
    simp

/-! ### §3 — the history and its coherence -/

/-- **THE RECENTERING-ENDED GATE HISTORY** H₂rec: bStageP root read → the recentering
read on the unramified (1,3) child. -/
noncomputable def H₂rec : History 2 F4 where
  nodes := [HK23.ν₀ram, ν₁rec]
  nonempty := by simp
  root_iff := by
    intro j hj
    have hj2 : j < 2 := by simpa using hj
    interval_cases j
    · exact iff_of_true rfl rfl
    · refine iff_of_false ?_ (by omega)
      show ν₁rec.species ≠ ReadSpecies.root
      intro hcontra
      exact ReadSpecies.noConfusion hcontra

lemma H₂rec_len : H₂rec.nodes.length = 2 := rfl

lemma H₂rec_str0 : H₂rec.strFrame 0 = 1 := rfl

lemma H₂rec_str1 : H₂rec.strFrame 1 = 1 := rfl

/-- **COHERENCE of H₂rec under the (S-a) re-keyed leg**: root-pair regrade =
`HK23.regrade_gate`, lift = `HK23.nodeLift_ν₀ram`, transition at the CHILD pair
(1, 3) = `tcl_rec`; the Bézout ties FIRE at `σ₁rec.e = 1` and close by the gate pins
(s = 1 = ν₁rec.s, t = 0 = ν₁rec.t); window `0 + 1 ≤ 2 = μ₀`; width chain
`D₁ = 2 = childWidth₀`; strict steepening `1 < 3/2`. -/
theorem coherent_H₂rec : HistoryCoherent H₂rec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hj
    show (Polynomial.X : Polynomial ℤ_[2]).natDegree = 1
    exact Polynomial.natDegree_X
  · -- slope law
    intro i hi
    have hi2 : i < 2 := H₂rec_len ▸ hi
    interval_cases i
    · show (1 : ℚ) * (((1 : ℕ) : ℚ) * ((H₂rec.strFrame 0 : ℕ) : ℚ) * ((1 : ℕ) : ℚ))
          = ((1 : ℕ) : ℚ)
      rw [H₂rec_str0]
      norm_num
    · show (3 / 2 : ℚ) * (((1 : ℕ) : ℚ) * ((H₂rec.strFrame 1 : ℕ) : ℚ) * ((2 : ℕ) : ℚ))
          = ((3 : ℕ) : ℚ)
      rw [H₂rec_str1]
      norm_num
  · -- γ-tie
    intro i hi
    have hi2 : i < 2 := H₂rec_len ▸ hi
    interval_cases i
    · show (((4 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((H₂rec.strFrame 0 : ℕ) : ℚ) * (0 : ℚ))
          + (((0 + 4 : ℕ)) : ℚ) * ((1 : ℕ) : ℚ)
      rw [H₂rec_str0]
      norm_num
    · show (((3 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((H₂rec.strFrame 1 : ℕ) : ℚ) * (0 : ℚ))
          + (((0 + 1 : ℕ)) : ℚ) * ((3 : ℕ) : ℚ)
      rw [H₂rec_str1]
      norm_num
  · -- the transition leg at i = 0 (the only interior index)
    intro i hi
    have hi1 : i = 0 := by
      have h2 : i + 1 < 2 := H₂rec_len ▸ hi
      omega
    subst hi1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- recentering clause: the root is not a recentering
      intro hcontra
      exact absurd hcontra (fun h => ReadSpecies.noConfusion h)
    · -- THE (S-a) LEG: RG-2 guard + σV regrade + root-pair lift + child-pair transition
      intro _
      refine ⟨rfl, HK23.σVgate, HK23.regrade_gate, ?_, ?_⟩
      · show IsNodeLift HK23.ν₀ram σ₁rec.Φ
        rw [σ₁rec_Φ]
        exact HK23.nodeLift_ν₀ram
      · show TransitionCoreL HK23.σVgate σ₁rec σ₁rec.Φ 1 3 U31.ν₀.zbar
        rw [σ₁rec_Φ]
        exact tcl_rec
    · -- s-tie, guarded at σ₁rec.e = 1: FIRES; closes by the gate pin s = 1
      intro _
      show σ₁rec.s = 1
      exact σ₁rec_pins.2.2.1
    · -- t-tie, guarded at σ₁rec.e = 1: FIRES; closes by the gate pin t = 0
      intro _
      show σ₁rec.t = 0
      exact σ₁rec_pins.2.2.2
    · -- window containment: 0 + 1 ≤ 2 = μ₀
      show (0 + 1 : ℕ) ≤ 2
      omega
    · -- width chain: D₁ = 2 = 1·2·1 = childWidth₀
      show (2 : ℕ) = 1 * 2 * 1
      norm_num
    · -- strict steepening: 1 < 3/2
      show (1 : ℚ) < 3 / 2
      norm_num

/-- The last node of H₂rec is a recentering — the exact hypothesis class of
`retiredKeysExist_false_of_witness`. -/
lemma lastRec_H₂rec :
    (H₂rec.nodes[H₂rec.nodes.length - 1]'(U1neg.last_lt H₂rec)).species
      = ReadSpecies.recentering := rfl

/-! ### §4 — THE DISCHARGE: the honesty perimeter of U1-neg closes -/

/-- **THE UNCONDITIONAL NEGATION** (HK-25's deliverable): the retired `hcoh`-keyed
`keys_exist` sentence is FALSE at (2, F4) — witnessed by H₂rec through U1neg's
lift-zeroing surgery.  The recorded honesty perimeter of
`retiredKeysExist_false_of_witness` (U1_negWitness.lean header) is CLOSED. -/
theorem retiredKeysExist_false : ¬ RetiredKeysExistStmt 2 F4 :=
  retiredKeysExist_false_of_witness H₂rec coherent_H₂rec lastRec_H₂rec

/-- The consumer-facing `KeysLawful` form of the discharge. -/
theorem keysLawful_hcoh_false :
    ¬ ∀ (H : History 2 F4), HistoryCoherent H →
        ∃ keys : ℕ → Polynomial ℤ_[2], KeysLawful H keys :=
  keysLawful_of_hcoh_false_of_witness H₂rec coherent_H₂rec lastRec_H₂rec

end HK25

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.HK25.tcl_rec
#print axioms LeanUrat.MovesJ.HK25.coherent_H₂rec
#print axioms LeanUrat.MovesJ.HK25.retiredKeysExist_false
#print axioms LeanUrat.MovesJ.HK25.keysLawful_hcoh_false
