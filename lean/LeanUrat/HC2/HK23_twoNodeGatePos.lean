/-
Unit HK-23-POS / THE POSITIVE 2-NODE GATE  (HK-06 wave acceptance test, 2026-07-31;
task #44 — queue item 3, duty (4): "build the previously-impossible 2-node instance
(bStageP root → R7Forge.ramifiedStage child) under the NEW keying — HK-22's positive
half").

THE GATE: `twoNodeGate_pos` — a compiled `History 2 F4` H₂ram with
* root node ν₀ram over the base pin `bStageP` (the (1,1) read of the inert quadratic
  residual ψ₂², i.e. the ROOT SIDE of an octic-class read: γ₀ = 4 on slots 0–4,
  vertex μ₀ = 2, `IsNodeLift ν₀ram fq` — the SAME landing key `fq = X² + 2X + 4` as
  U31's gate, at the same realizer witness),
* child node ν₁ram whose frame IS the forge's `R7Forge.ramifiedStage` (the S9-built
  (2,5)-child — `X² − p`-Eisenstein-side semantics at p = 2), reading the ADJACENT
  (2,5) side (slots 0–2, γ₁ = 10, ψ₁ = z − 1, adjacency s0₁ + wSide₁ = 2 = μ₀),
satisfying `HistoryCoherent H₂ram ∧ Realizable H₂ram ∧ InBox 4 H₂ram` — the EXACT
conjunction `HK22.twoNodeGate_isEmpty` proves unsatisfiable for the pre-wave keying
(now frozen there as `HistoryCoherentPre`).  This file is therefore the compiled
demonstration that the (S-a) two-step regrade re-key REPAIRED the V10/V11
stride-decoupling collision: the recorded lift stays at the ROOT's read pair (1,1)
(stride-1 — the parity kernel never fires), while the transition record rides the
CHILD's pair (2,5) through the σV regrade, exactly D.5 → D.7.

THE σV WITNESS: `σVgate` = `U31.bStage` re-dressed with bStageP's genuine
representatives (`reps = [C 2]`, `Tvec = [(C 2, 1)]`) — its `wPrev` is `bw = bStageP.w`
(the RegradeOf history invariant), its (1,1) pair is the root READ pair, and its
slot-min law is `Stage.hK1` at the base pin (the (1,1)-Gauss slot decomposition).
`TransitionCoreL σVgate ramifiedStage fq 2 5 z̄₀` is the forge record transported
field-by-field (every parent field TransitionCoreL reads — w/Φ/t/K/FQ/reps/Tvec/R —
is definitionally bStageP's).

HK-48 half-RECORD: H₂ram at i = 1 is the compiled countermodel instance for the OLD
`v9_readSteep_all`/`V9_readSteepness` statements under the new keying
(ν₁.e·ν₁.σ.h = 2·5 ≥ 5 = ν₁.h) — the reason the wave DELETED them (V9 archival block).

deps: MovesD/R7_ramifiedForge (bStageP + the forge), HC2/HK57 (the proved
`sideReads0_landing` whose non-recentering half is `IsNodeLift` at the shared
(σ = bStageP, ψ = ψ₂, g = 2, e = 1, h = 1) read data — defeq-transported here).
Axioms: Lean core only (#print axioms at EOF).
-/
import Mathlib
import LeanUrat.MovesD.R7_ramifiedForge
import LeanUrat.HC2.HK57

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace HK23

/-! ### §1 — the σV regrade witness at the root read -/

/-- **The gate regrade stage** σV: `U31.bStage` (whose `w = wPrev = bw`) carrying the
base pin's genuine representatives.  All fields `RegradeOf`/`TransitionCoreL` read are
definitionally `bStageP`'s except `wPrev`, which is `bw = bStageP.w` — the regrade's
history invariant. -/
noncomputable def σVgate : Stage 2 F4 :=
  { U31.bStage with
    reps := [Polynomial.C ((2 : ℕ) : ℤ_[2])]
    Tvec := [(Polynomial.C ((2 : ℕ) : ℤ_[2]), (1 : ℤ))]
    hreps := by
      intro ũ hũ
      rw [List.mem_singleton] at hũ
      subst hũ
      exact ⟨Polynomial.C_ne_zero.mpr (by norm_num), HK13R.inC_C⟩
    hTvec := rfl }

/-- The (1,1)-slot-minimum law of `bw` over itself at the key `X` — `Stage.hK1` at the
base stage, with the key weight `bw X = 1` folded in. -/
lemma slotmin_gate : IsSlotMinWeight σVgate.w bStageP.Φ 1 1 bStageP.w := by
  intro f B N hf hdev
  have hK := U31.bStage.hK1 f B N hf hdev
  have hwX : U31.bStage.w U31.bStage.Φ = 1 := by
    have h := U31.bStage.hwΦ
    exact_mod_cast h
  rw [hwX] at hK
  obtain ⟨hle, j, hj, hnz, heq⟩ := hK
  have hVw : ∀ x, σVgate.w x = U31.bStage.w x := fun _ => rfl
  have hPw : ∀ x, bStageP.w x = U31.bStage.w x := fun _ => rfl
  refine ⟨fun k hk hknz => ?_, j, hj, hnz, ?_⟩
  · have h1 := hle k hk hknz
    simp only at h1
    simp only [hVw, hPw]
    push_cast
    linarith [h1]
  · simp only at heq
    simp only [hVw, hPw]
    push_cast
    linarith [heq]

/-- **The gate regrade record**: `RegradeOf bStageP 1 1 σVgate` — the root read is at
the frame pair, so the regrade is the identity in the pair, with `wPrev` re-dressed to
the parent's `w = bw`. -/
lemma regrade_gate : RegradeOf bStageP 1 1 σVgate :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, slotmin_gate⟩

/-- **The STEP-2 transition record at the gate**: the forge's
`TransitionCoreL bStageP ramifiedStage fq 2 5 z̄₀` transported to the σV parent — every
parent field the record reads is definitionally shared. -/
lemma tcl_gate :
    TransitionCoreL σVgate R7Forge.ramifiedStage U31.fq 2 5 U31.ν₀.zbar := by
  obtain ⟨base, hTvec, hdig⟩ := R7Forge.ramifiedStage_trans
  exact ⟨⟨base.child_key, base.child_e, base.child_h, base.child_field, base.field_grow,
    base.child_base, base.child_wPrev, base.threshold, base.child_slotmin,
    base.child_reps⟩, hTvec, hdig⟩

/-! ### §2 — the root node: the (1,1) read with residual ψ₂², vertex μ₀ = 2 -/

/-- Char-2 collapse in the base residue field. -/
lemma K2_two_eq_zero : (2 : ↥U31.K2) = 0 := by
  apply U31.K2.subtype.injective
  rw [map_ofNat, map_zero]
  exact_mod_cast CharP.cast_eq_zero F4 2

/-- The char-2 square: `ψ₂² = z⁴ + z² + 1` over the base residue field. -/
lemma ψ₂_sq : (U31.ψ₂ : Polynomial ↥U31.K2) ^ 2
    = X ^ 4 + X ^ 2 + 1 := by
  have h2p : (Polynomial.C (2 : ↥U31.K2) : Polynomial ↥U31.K2) = 0 := by
    rw [K2_two_eq_zero, map_zero]
  have key : (U31.ψ₂ : Polynomial ↥U31.K2) ^ 2 - (X ^ 4 + X ^ 2 + 1)
      = Polynomial.C (2 : ↥U31.K2) * (X ^ 3 + X ^ 2 + X) := by
    unfold U31.ψ₂
    ring_nf
    rw [show ((2 : ℕ) : Polynomial ↥U31.K2) = Polynomial.C (2 : ↥U31.K2) by push_cast; ring]
    ring
  have hz : (U31.ψ₂ : Polynomial ↥U31.K2) ^ 2 - (X ^ 4 + X ^ 2 + 1) = 0 := by
    rw [key, h2p, zero_mul]
  linear_combination hz

/-- **The gate root node** ν₀ram: U31's inert (1,1) root read re-dressed for the
DOUBLE residual — pattern `(1,0,1,0,1)` on slots 0–4, `Ranch = ψ₂²`, vertex `μ = 2`,
side `γ₀ = 4`, `line = ⟨4, 1⟩`, `u* = 0` at the right endpoint base index 4.  The
frame is `bStageP`; `(ψ, g, e, h, s, t)` are exactly `U31.ν₀`'s, so `IsNodeLift` data
transport from HK-57's proved landing. -/
noncomputable def ν₀ram : Node 2 F4 where
  species := ReadSpecies.root
  σ := bStageP
  e := 1
  h := 1
  s := 1
  t := 0
  g := 2
  μ := 2
  a := 0
  s0 := 0
  wSide := 4
  Dwidth := 1
  line := ⟨4, 1⟩
  ustar := 0
  gam := 4
  zbar := U31.ν₀.zbar
  center := 0
  lift := 0
  ψ := U31.ψ₂
  pat := fun k => if k % 2 = 0 then 1 else 0
  Ranch := U31.ψ₂ ^ 2
  he := le_refl 1
  hh := le_refl 1
  hcop := by norm_num
  hbez := by norm_num
  hbezCanon := by norm_num
  hg := by norm_num
  hμ := by norm_num
  hEdvd := one_dvd 4
  hDwidth := natDegree_X.symm
  hψmonic := U31.ν₀.hψmonic
  hψdeg := U31.ν₀.hψdeg
  hψirr := U31.ν₀.hψirr
  hRanch := by
    show (U31.ψ₂ : Polynomial ↥U31.K2) ^ 2
        = ∑ k ∈ Finset.range (4 / 1 + 1),
            Polynomial.C (if k % 2 = 0 then (1 : ↥U31.K2) else 0) * X ^ k
    rw [ψ₂_sq]
    norm_num [Finset.sum_range_succ]
    ring
  hpat0 := by norm_num
  hpatTop := by norm_num
  hAnchor := by norm_num
  hLineU := by
    show (4 : ℚ) - 1 * (((0 + 4) * 1 : ℕ) : ℚ) = 0
    norm_num
  hOrd := by
    refine ⟨dvd_refl _, fun hdvd => ?_⟩
    have hne : (U31.ψ₂ : Polynomial ↥U31.K2) ^ 2 ≠ 0 :=
      pow_ne_zero _ U31.ν₀.hψmonic.ne_zero
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow] at hle
    have hd2 : (U31.ψ₂ : Polynomial ↥U31.K2).natDegree = 2 := U31.ν₀.hψdeg
    rw [hd2] at hle
    omega
  hzbarRoot := U31.ν₀.hzbarRoot
  hspecInc := by intro h; simp at h
  hspecRec := by intro h; simp at h
  hspecRecCenter := by intro h; simp at h

/-- The recorded lift at the gate root: `IsNodeLift ν₀ram fq` — HK-57's proved landing
transports (both nodes share every field `IsNodeLift` reads: σ = bStageP, ψ = ψ₂,
g = 2, (e, h) = (1, 1)). -/
lemma nodeLift_ν₀ram : IsNodeLift ν₀ram U31.fq := by
  have h := HK57.sideReads0_landing.2 (fun hcontra => ReadSpecies.noConfusion hcontra)
  obtain ⟨tt, h1, h2, h3⟩ := h
  exact ⟨tt, h1, h2, h3⟩

end HK23

end LeanUrat.MovesJ
