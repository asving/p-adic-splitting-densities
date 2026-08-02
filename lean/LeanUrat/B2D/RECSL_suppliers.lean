/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.GR0b_suppliers
import LeanUrat.Moves.ResVal

/-!
# B2D/RECSL_suppliers — THE REC-SL SUPPLIER VERDICT (synthesis pass 5, F2; queue #5)
  [attempt-grade unit, 2026-08-08]

Charter: `docs/SYNTHESIS_PASS5_2026-08-08.md` F2 — do the three REC-SL digit legs
(B-M2's one untouched open: the `IsReadLift`-at-(1,1) form + the (SL-top)/(SL-dev)
obligations for the recentering digit `−lift`, `H1_BM2_2026-08-06.md` §S4 (i-c) leg (1))
follow HISTORY-LEVEL from the compiled GR0b supplier layer? Note:
`lean/notes/openmath/RECSL_F2_2026-08-08.md`. **NO sorry in this file.**

## VERDICT (2.75 of 3 legs SUPPLIED; one pin OBSTRUCTED, exactly identified)

* **(SL-top) — SUPPLIED, unconditional** (`recsl_slTop`): at a recentering record the
  fired key `Φ' = σ.Φ − lift` IS the D8 stride form
  `Φ' = σ.Φ^(e·g) + Σ_{k<g} t_k·σ.Φ^(e·k)` at the node's recorded pair (= (1,1) by
  `hspecRec`), digit `t_0 = −lift`, top coefficient literally 1, D_g = 1 hard-wired.
* **(SL-dev) DATA — SUPPLIED except one sign** (`recsl_slDev_data`): the digit `−lift`
  is nonzero (`IsRecentering` clause 5), in the window (clause 4 + `degree_neg`), of
  marched weight `ν.h·(g−0)` (clause 6 + `Stage.hwΦ` + the `ReadHyps` tie
  `readHyps_h_eq`), and its twist POSITION `−σ.t·wPrev(−lift)` is 0 (the route-(a)
  frame pin `ReadHyps.hσt` — GR34_DISPOSITION). The residual DIGIT law is supplied up
  to the sign `σ.R(−1)`: `σ.R(−lift) = σ.R(−1)·C(c̃)·T^0` with `ψ.coeff 0 = −c̃`
  (`hspecRecCenter`), and `node_hψ0` is exactly the `c̃ ≠ 0` pin.
* **THE OBSTRUCTION, compiled sharp** (`recsl_residual_iff_sign`): at a recentering
  record with `ReadHyps`, the (SL-dev) residual obligation for `−lift` holds IFF
  `σ.R(−1) = −1` at the frame. That sign law is `StageCore.R_neg` at `f = 1` — one of
  the three D.1(b) tie laws the corpus records as "true in every genuine graded model,
  UNDERIVABLE from the round-2 `Stage` fields" (`Moves/DefsCore.lean` StageCore
  docstring, the pathological-stage audit record). Neither `ReadHyps` (round-2 R-laws
  only) nor `HistoryCoherent`'s transition records (`TransitionCoreL`/
  `IsRecenteringCore` — no `StageCore` bundled) carry it: the GR0b supplier layer
  CANNOT reach the sign, matching the F2 warning (digit laws ≠ graded identities).
* **THE ASSEMBLED LEG, conditional on the one pin** (`recsl_isNodeLift`,
  `recsl_isReadLift_11`, history form `recsl_isNodeLift_of_history`): with the sign
  law as a DISPLAYED hypothesis `hsign : σ.R(−1) = −1`, the full `IsNodeLift`
  (= `IsReadLift` at the recorded pair; the (1,1) form via `hspecRec`) is PROVED at
  every recentering record, single-node and history-level. `signLaw_of_stageCore`
  discharges `hsign` from `StageCore` (supplied by the ENGINE face: the base
  constructs it, `L4.TRANSstage`/`L5.recTRANSRS` transport it) — so on engine-built
  towers the legs close outright (`recsl_isNodeLift_of_stageCore`).

Consumption shape for B-M2 (§S4 (i-c)): `recsl_isNodeLift_of_history` gives the [RC]
fired key the SAME `IsNodeLift` interface that `HistoryCoherent` records at [NR]
reads — KP-STEP's (SL) legs at recentering reads reduce to GRADED-READ + the
`StageCore` provenance of the frame, no recentering-specific residue.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesJ

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-! ## 1. Single-node recentering pins (no history) -/

/-- At a recentering, `ψ = z − c̃` (`hspecRecCenter`), so the ψ-anchor digit IS the
(negated) center: `ψ.coeff 0 = −c̃`. -/
theorem recsl_psi_coeff_zero (ν : Node p F)
    (hspec : ν.species = ReadSpecies.recentering) :
    ν.ψ.coeff 0 = -ν.center := by
  rw [(ν.hspecRecCenter hspec).1]
  simp

/-- The center pin: `c̃ ≠ 0` — this is `node_hψ0` (the GR0b `hψ0` supplier) read at a
recentering through `ψ = z − c̃`. No history needed. -/
theorem recsl_center_ne_zero (ν : Node p F)
    (hspec : ν.species = ReadSpecies.recentering) : ν.center ≠ 0 := by
  intro h0
  exact node_hψ0 ν (by rw [recsl_psi_coeff_zero ν hspec, h0, neg_zero])

/-! ## 2. Leg (SL-top) — the D8 stride form at the recentering key, UNCONDITIONAL -/

/-- **(SL-top), SUPPLIED**: the recentering fired key `Φ' = σ.Φ − lift` (`IsRecentering`
clause 8) IS `IsReadLift`'s displayed stride form at the node's recorded pair — top
coefficient LITERALLY 1, sole lower digit `t_0 = −lift`, D_g = 1 hard-wired (the sum
ranges over `k < g = 1`). Pure algebra from the record; no `ReadHyps`, no sign law. -/
theorem recsl_slTop (ν : Node p F) {σ' : Stage p F}
    (hspec : ν.species = ReadSpecies.recentering)
    (hrec : IsRecentering ν.σ σ' ν.center ν.lift) :
    σ'.Φ = ν.σ.Φ ^ (ν.e * ν.g)
      + ∑ k ∈ Finset.range ν.g, (if k = 0 then -ν.lift else 0) * ν.σ.Φ ^ (ν.e * k) := by
  obtain ⟨he1, hg1⟩ := ν.hspecRec hspec
  have hkey : σ'.Φ = ν.σ.Φ - ν.lift := hrec.2.2.2.2.2.2.2.1
  rw [hkey, he1, hg1]
  simp [sub_eq_add_neg]

/-! ## 3. Leg (SL-dev) DATA — window/weight/position supplied; the residual sign pinned -/

/-- **(SL-dev) data, SUPPLIED**: the recentering digit `−lift` is nonzero, in the
window, of marched weight `ν.h·(ν.g − 0)` (= `h·(g−k)` at the sole slot `k = 0`), and
its twist position `−σ.t·wPrev(−lift)` is 0 — the route-(a) frame pin `ReadHyps.hσt`
(supplied at history level by `frame_level_of_history`). The weight chain:
`w(−lift) = w(lift)` (`ResVal.w_neg`) `= w(σ.Φ)` (`IsRecentering` clause 6) `= σ.h`
(`Stage.hwΦ`) `= ν.h` (`readHyps_h_eq` — the `ReadHyps` frame-to-read tie). -/
theorem recsl_slDev_data (ν : Node p F) (R : ReadHyps ν) {σ' : Stage p F}
    (hspec : ν.species = ReadSpecies.recentering)
    (hrec : IsRecentering ν.σ σ' ν.center ν.lift) :
    -ν.lift ≠ 0 ∧ inC ν.σ.Φ (-ν.lift)
      ∧ ν.σ.w (-ν.lift) = (ν.h : ℤ) * ((ν.g : ℤ) - ((0 : ℕ) : ℤ))
      ∧ -ν.σ.t * ν.σ.wPrev (-ν.lift) = 0 := by
  obtain ⟨-, hg1⟩ := ν.hspecRec hspec
  have htne : ν.lift ≠ 0 := hrec.2.2.2.2.1
  have hin : inC ν.σ.Φ ν.lift := hrec.2.2.2.1
  have hwt : ν.σ.w ν.lift = ν.σ.w ν.σ.Φ := hrec.2.2.2.2.2.1
  refine ⟨neg_ne_zero.mpr htne, ?_, ?_, ?_⟩
  · simpa [inC, Polynomial.degree_neg] using hin
  · rw [ResVal.w_neg ν.σ ν.lift htne, hwt, ν.σ.hwΦ, readHyps_h_eq ν R, hg1]
    simp
  · rw [R.hσt]
    ring

/-- **THE COMPILED OBSTRUCTION PIN (sharp)**: at a recentering record with `ReadHyps`,
the (SL-dev) residual-digit obligation for `−lift` holds IFF the frame satisfies the
residual sign law `σ.R(−1) = −1`. Everything else is supplier-reachable; the sign is
NOT: it is `StageCore.R_neg` content (one of the three D.1(b) tie laws recorded as
UNDERIVABLE from the round-2 `Stage` fields — `Moves/DefsCore.lean`), and neither
`ReadHyps` nor `HistoryCoherent`'s transition records carry `StageCore`. Displayed
open lemma at the abstract recorded face:
`RECSL-SIGN: at every recentering read frame σ of a coherent history, σ.R(−1) = −1`
(supplied on engine-built towers by `StageCore.R_neg` via base construction +
transition transport). -/
theorem recsl_residual_iff_sign (ν : Node p F) (R : ReadHyps ν) {σ' : Stage p F}
    (hspec : ν.species = ReadSpecies.recentering)
    (hrec : IsRecentering ν.σ σ' ν.center ν.lift) :
    (ν.σ.R (-ν.lift) = LaurentPolynomial.C (ν.ψ.coeff 0)
        * LaurentPolynomial.T (-ν.σ.t * ν.σ.wPrev (-ν.lift)))
      ↔ ν.σ.R (-1 : Polynomial ℤ_[p]) = -1 := by
  have hcc : ν.center ≠ 0 := hrec.2.2.1
  have htne : ν.lift ≠ 0 := hrec.2.2.2.2.1
  have hRt : ν.σ.R ν.lift = LaurentPolynomial.C ν.center * LaurentPolynomial.T 0 :=
    hrec.2.2.2.2.2.2.1
  have hψc : ν.ψ.coeff 0 = -ν.center := recsl_psi_coeff_zero ν hspec
  rw [R.hσt, hψc, ResVal.R_neg ν.σ ν.lift htne, hRt]
  simp only [neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one, map_neg]
  constructor
  · intro h
    have hinv : (LaurentPolynomial.C ν.center : LaurentPolynomial ↥ν.σ.K)
        * LaurentPolynomial.C ν.center⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hcc, map_one]
    calc ν.σ.R (-1)
        = ν.σ.R (-1) * (LaurentPolynomial.C ν.center * LaurentPolynomial.C ν.center⁻¹) := by
          rw [hinv, mul_one]
      _ = (ν.σ.R (-1) * LaurentPolynomial.C ν.center) * LaurentPolynomial.C ν.center⁻¹ := by
          ring
      _ = -LaurentPolynomial.C ν.center * LaurentPolynomial.C ν.center⁻¹ := by rw [h]
      _ = -(LaurentPolynomial.C ν.center * LaurentPolynomial.C ν.center⁻¹) := by ring
      _ = -1 := by rw [hinv]
  · intro h
    rw [h]
    ring

/-! ## 4. Leg `IsReadLift`-at-(1,1) — ASSEMBLED, conditional on the one displayed pin -/

/-- **REC-SL assembled at a node**: at a recentering record with `ReadHyps` and the
DISPLAYED sign pin `hsign : σ.R(−1) = −1` (the sole non-supplied input — discharged by
`StageCore.R_neg` wherever the engine built the frame, `signLaw_of_stageCore`), the
fired key `Φ' = σ.Φ − lift` satisfies the FULL `IsNodeLift` predicate at the node's
recorded read pair — the same interface `HistoryCoherent` records at [NR] reads. -/
theorem recsl_isNodeLift (ν : Node p F) (R : ReadHyps ν) {σ' : Stage p F}
    (hspec : ν.species = ReadSpecies.recentering)
    (hrec : IsRecentering ν.σ σ' ν.center ν.lift)
    (hsign : ν.σ.R (-1 : Polynomial ℤ_[p]) = -1) :
    IsNodeLift ν σ'.Φ := by
  obtain ⟨he1, hg1⟩ := ν.hspecRec hspec
  refine ⟨fun k => if k = 0 then -ν.lift else 0, ?_, ?_, recsl_slTop ν hspec hrec⟩
  · intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (h0 ▸ hk) (node_hψ0 ν)
    · simp [Nat.pos_iff_ne_zero.mp h0]
  · intro k hkg hψk
    have h0 : k = 0 := by
      rw [hg1] at hkg
      exact Nat.lt_one_iff.mp hkg
    subst h0
    obtain ⟨hne, hin, hw, hpos⟩ := recsl_slDev_data ν R hspec hrec
    refine ⟨by simpa using hne, by simpa using hin, by simpa using hw, ?_⟩
    show ν.σ.R (-ν.lift) = LaurentPolynomial.C (ν.ψ.coeff 0)
        * LaurentPolynomial.T (-ν.σ.t * ν.σ.wPrev (-ν.lift))
    exact (recsl_residual_iff_sign ν R hspec hrec).mpr hsign

/-- The leg in B-M2's displayed spelling: `IsReadLift` AT THE SYNTHETIC PAIR (1, 1)
(`H1_BM2` §S4 (i-c) leg (1) — "the `IsReadLift`-at-(1, 1) form"). Same content as
`recsl_isNodeLift` through `hspecRec` + `isNodeLift_iff`. -/
theorem recsl_isReadLift_11 (ν : Node p F) (R : ReadHyps ν) {σ' : Stage p F}
    (hspec : ν.species = ReadSpecies.recentering)
    (hrec : IsRecentering ν.σ σ' ν.center ν.lift)
    (hsign : ν.σ.R (-1 : Polynomial ℤ_[p]) = -1) :
    IsReadLift ν.σ ν.ψ 1 1 ν.h σ'.Φ := by
  obtain ⟨he1, hg1⟩ := ν.hspecRec hspec
  have h := (isNodeLift_iff ν σ'.Φ).mp (recsl_isNodeLift ν R hspec hrec hsign)
  rwa [he1, hg1] at h

/-! ## 5. The `StageCore` discharge of the sign pin -/

/-- The sign law from `StageCore`: `R_neg` at `f = 1`. This is the ONLY corpus supplier
of the pin; it lives on the ENGINE face (base construction + `TRANSstage`/`recTRANSRS`
transport), NOT in `ReadHyps` or the `HistoryCoherent` records. -/
theorem signLaw_of_stageCore {σ : Stage p F} (hc : StageCore σ) :
    σ.R (-1 : Polynomial ℤ_[p]) = -1 := by
  have h := hc.R_neg 1
  rwa [ResVal.R_one σ] at h

/-- `recsl_isNodeLift` with the pin discharged by `StageCore` at the frame. -/
theorem recsl_isNodeLift_of_stageCore (ν : Node p F) (R : ReadHyps ν) {σ' : Stage p F}
    (hspec : ν.species = ReadSpecies.recentering)
    (hrec : IsRecentering ν.σ σ' ν.center ν.lift)
    (hcore : StageCore ν.σ) :
    IsNodeLift ν σ'.Φ :=
  recsl_isNodeLift ν R hspec hrec (signLaw_of_stageCore hcore)

/-! ## 6. The history-level packaging — the exact B-M2 consumption shape -/

/-- **REC-SL at history level**: in a coherent history, at a recentering read (node
`i+1`, species recentering) whose frame was created by a non-recentering transition
(the `readHyps_of_history_rec` configuration — the GR0b recentering-chain fence
applies as there) and whose own recentering transition is RECORDED (node `i+2`
exists), the fired key `σ_{i+2}.Φ` satisfies `IsNodeLift` at the recentering node —
given the ONE displayed pin `hsign` at the frame. Everything else is GR0b-supplied:
`ReadHyps` via `readHyps_of_history_rec` (`hspecRec` legality: σ-side e = 1 is
`IsRecentering` clause 1, the CL5 discovery), the recentering record via
`HistoryCoherent`'s recentering leg (`IsRecenteringCore.base`). -/
theorem recsl_isNodeLift_of_history {H : History p F} (hcoh : HistoryCoherent H)
    {i : ℕ} (hi2 : i + 1 + 1 < H.nodes.length)
    (hprev : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hspec : (H.nodes[i+1]'(by omega)).species = ReadSpecies.recentering)
    (hsign : (H.nodes[i+1]'(by omega)).σ.R (-1 : Polynomial ℤ_[p]) = -1) :
    IsNodeLift (H.nodes[i+1]'(by omega)) ((H.nodes[i+1+1]'hi2).σ.Φ) := by
  have R := readHyps_of_history_rec hcoh (by omega) hprev hspec
  obtain ⟨-, -, -, htrans⟩ := hcoh
  have hrec := (htrans (i+1) hi2).1 hspec
  exact recsl_isNodeLift _ R hspec hrec.base hsign

/-- The history form with the pin discharged by `StageCore` at the recentering frame
(available wherever the frame has engine provenance). -/
theorem recsl_isNodeLift_of_history_stageCore {H : History p F} (hcoh : HistoryCoherent H)
    {i : ℕ} (hi2 : i + 1 + 1 < H.nodes.length)
    (hprev : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (hspec : (H.nodes[i+1]'(by omega)).species = ReadSpecies.recentering)
    (hcore : StageCore (H.nodes[i+1]'(by omega)).σ) :
    IsNodeLift (H.nodes[i+1]'(by omega)) ((H.nodes[i+1+1]'hi2).σ.Φ) :=
  recsl_isNodeLift_of_history hcoh hi2 hprev hspec (signLaw_of_stageCore hcore)

end LeanUrat.B2D

#print axioms LeanUrat.B2D.recsl_slTop
#print axioms LeanUrat.B2D.recsl_slDev_data
#print axioms LeanUrat.B2D.recsl_residual_iff_sign
#print axioms LeanUrat.B2D.recsl_isNodeLift
#print axioms LeanUrat.B2D.recsl_isReadLift_11
#print axioms LeanUrat.B2D.recsl_isNodeLift_of_history
#print axioms LeanUrat.B2D.recsl_isNodeLift_of_history_stageCore
