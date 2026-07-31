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
  have h2p : (2 : Polynomial ↥U31.K2) = 0 := by
    rw [← map_ofNat (Polynomial.C : ↥U31.K2 →+* Polynomial ↥U31.K2) 2,
      K2_two_eq_zero, map_zero]
  have key : (U31.ψ₂ : Polynomial ↥U31.K2) ^ 2 - (X ^ 4 + X ^ 2 + 1)
      = 2 * (X ^ 3 + X ^ 2 + X) := by
    unfold U31.ψ₂
    ring
  have hz : (U31.ψ₂ : Polynomial ↥U31.K2) ^ 2 - (X ^ 4 + X ^ 2 + 1) = 0 := by
    rw [key, h2p, zero_mul]
  linear_combination hz

/-- ψ₂-order of the double residual: `ψ₂² ∥ ψ₂²`. -/
lemma ord_ψ₂_sq : OrdPsiPoly (U31.ψ₂ : Polynomial ↥U31.K2) (U31.ψ₂ ^ 2) 2 := by
  refine ⟨dvd_refl _, fun hdvd => ?_⟩
  have hne : (U31.ψ₂ : Polynomial ↥U31.K2) ^ 2 ≠ 0 := pow_ne_zero _ HK13R.ψ₂_monic.ne_zero
  have hle := Polynomial.natDegree_le_of_dvd hdvd hne
  simp only [Polynomial.natDegree_pow, HK13R.ψ₂_natDegree] at hle
  omega

/-- The pattern sum realizing `ψ₂²` (the `hRanch` law of the gate root). -/
lemma ranch_ν₀ram : (U31.ψ₂ : Polynomial ↥U31.K2) ^ 2
    = ∑ k ∈ Finset.range 5,
        Polynomial.C (if k % 2 = 0 then (1 : ↥U31.K2) else 0) * X ^ k := by
  rw [ψ₂_sq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  norm_num
  ring

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
  hRanch := ranch_ν₀ram
  hpat0 := by norm_num
  hpatTop := by norm_num
  hAnchor := by norm_num
  hLineU := by
    show (4 : ℚ) - 1 * (((0 + 4) * 1 : ℕ) : ℚ) = 0
    norm_num
  hOrd := ord_ψ₂_sq
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

/-! ### §3 — the child node: the ADJACENT (2,5) read on the forged ramified frame -/

/-- The forged child key pin. -/
lemma Φram : R7Forge.ramifiedStage.Φ = U31.fq :=
  R7Forge.ramifiedStage_trans.base.child_key

/-- **The gate child node** ν₁ram: the ADJACENT (2,5) read on the forge frame — side
slots 0–2 with stride 2 (digits at slots 0 and 2), `γ₁ = 10`, canonical Bézout
`(s, t) = (−2, 1)`, `ψ₁ = z − 1`, `Ranch₁ = z + 1`, `z̄₁ = 1`, `line₁ = ⟨5, 5/4⟩`
(slope law `(5/4)·(2·1·2) = 5`), `u*₁ = 0` at the endpoint base index 4,
`a₁ = −5` (`2·(−5) = 0 − 1·10`). -/
noncomputable def ν₁ram : Node 2 F4 where
  species := ReadSpecies.increment
  σ := R7Forge.ramifiedStage
  e := 2
  h := 5
  s := -2
  t := 1
  g := 1
  μ := 1
  a := -5
  s0 := 0
  wSide := 2
  Dwidth := 2
  line := ⟨5, 5/4⟩
  ustar := 0
  gam := 10
  zbar := 1
  center := 1
  lift := 0
  ψ := Polynomial.X - Polynomial.C 1
  pat := fun _ => 1
  Ranch := Polynomial.X + 1
  he := by norm_num
  hh := by norm_num
  hcop := by norm_num
  hbez := by norm_num
  hbezCanon := by norm_num
  hg := le_refl 1
  hμ := le_refl 1
  hEdvd := by norm_num
  hDwidth := by rw [Φram]; exact U31.fq_natDegree.symm
  hψmonic := Polynomial.monic_X_sub_C 1
  hψdeg := Polynomial.natDegree_X_sub_C 1
  hψirr := Polynomial.irreducible_X_sub_C 1
  hRanch := by
    show (Polynomial.X + 1 : Polynomial ↥R7Forge.ramifiedStage.K)
        = ∑ k ∈ Finset.range 2,
            (Polynomial.C (1 : ↥R7Forge.ramifiedStage.K)
              * (Polynomial.X : Polynomial ↥R7Forge.ramifiedStage.K) ^ k)
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp
    ring
  hpat0 := one_ne_zero
  hpatTop := one_ne_zero
  hAnchor := by norm_num
  hLineU := by
    show (5 : ℚ) - 5 / 4 * (((0 + 2) * 2 : ℕ) : ℚ) = 0
    norm_num
  hOrd := by
    have h2 : (2 : F4) = 0 := by exact_mod_cast CharP.cast_eq_zero F4 2
    have h11 : (1 : F4) + 1 = 0 := by
      rw [show (1 : F4) + 1 = 2 from by norm_num]; exact h2
    have hnegF : (-1 : F4) = 1 := neg_eq_iff_add_eq_zero.mpr h11
    have hneg : (-1 : ↥R7Forge.ramifiedStage.K) = 1 := by
      apply R7Forge.ramifiedStage.K.subtype.injective
      simp only [map_neg, map_one]
      exact hnegF
    have hψeq : (Polynomial.X - Polynomial.C (1 : ↥R7Forge.ramifiedStage.K))
        = Polynomial.X + 1 := by
      rw [sub_eq_add_neg, ← Polynomial.C_neg, hneg, Polynomial.C_1]
    refine ⟨?_, ?_⟩
    · rw [pow_one]; exact dvd_of_eq hψeq
    · rw [hψeq]
      intro hdvd
      have hne : (Polynomial.X + 1 : Polynomial ↥R7Forge.ramifiedStage.K) ≠ 0 := by
        rw [← Polynomial.C_1]; exact (Polynomial.monic_X_add_C 1).ne_zero
      have hnd : (Polynomial.X + 1 : Polynomial ↥R7Forge.ramifiedStage.K).natDegree = 1 := by
        rw [← Polynomial.C_1]; exact Polynomial.natDegree_X_add_C 1
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne
      rw [Polynomial.natDegree_pow, hnd] at hle
      omega
  hzbarRoot := by
    show Polynomial.eval₂ R7Forge.ramifiedStage.K.subtype ((1 : F4ˣ) : F4)
        (Polynomial.X - Polynomial.C 1) = 0
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp
  hspecInc := fun _ => by norm_num
  hspecRec := by intro h; simp at h
  hspecRecCenter := by intro h; simp at h

/-! ### §4 — the history, its coherence, realizability, and the box -/

/-- **THE POSITIVE GATE HISTORY** H₂ram: bStageP root → ramifiedStage child. -/
noncomputable def H₂ram : History 2 F4 where
  nodes := [ν₀ram, ν₁ram]
  nonempty := by simp
  root_iff := by
    intro j hj
    have hj2 : j < 2 := by simpa using hj
    interval_cases j
    · exact iff_of_true rfl rfl
    · refine iff_of_false ?_ (by omega)
      show ν₁ram.species ≠ ReadSpecies.root
      intro hcontra
      exact ReadSpecies.noConfusion hcontra

lemma H₂ram_len : H₂ram.nodes.length = 2 := rfl

lemma H₂ram_str0 : H₂ram.strFrame 0 = 1 := rfl

lemma H₂ram_str1 : H₂ram.strFrame 1 = 1 := rfl

/-- **COHERENCE of the gate history under the (S-a) re-keyed leg** — the wave's
acceptance content: the recorded lift at the ROOT pair (identity-shaped regrade), the
transition record at the CHILD pair (2, 5) = the forge record, ties vacuous at the
ramified child (`σ₁.e = 2 ≠ 1`), adjacency `s0₁ + wSide₁ = 2 = μ₀`, width chain
`D₁ = 2 = childWidth₀`, strict steepening `1 < 5/4`. -/
theorem coherent_H₂ram : HistoryCoherent H₂ram := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hj
    show (Polynomial.X : Polynomial ℤ_[2]).natDegree = 1
    exact Polynomial.natDegree_X
  · -- slope law
    intro i hi
    have hi2 : i < 2 := H₂ram_len ▸ hi
    interval_cases i
    · show (1 : ℚ) * (((1 : ℕ) : ℚ) * ((H₂ram.strFrame 0 : ℕ) : ℚ) * ((1 : ℕ) : ℚ))
          = ((1 : ℕ) : ℚ)
      rw [H₂ram_str0]
      norm_num
    · show (5 / 4 : ℚ) * (((2 : ℕ) : ℚ) * ((H₂ram.strFrame 1 : ℕ) : ℚ) * ((2 : ℕ) : ℚ))
          = ((5 : ℕ) : ℚ)
      rw [H₂ram_str1]
      norm_num
  · -- γ-tie
    intro i hi
    have hi2 : i < 2 := H₂ram_len ▸ hi
    interval_cases i
    · show (((4 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((H₂ram.strFrame 0 : ℕ) : ℚ) * (0 : ℚ))
          + (((0 + 4 : ℕ)) : ℚ) * ((1 : ℕ) : ℚ)
      rw [H₂ram_str0]
      norm_num
    · show (((10 : ℤ) : ℚ)) = ((2 : ℕ) : ℚ) * (((H₂ram.strFrame 1 : ℕ) : ℚ) * (0 : ℚ))
          + (((0 + 2 : ℕ)) : ℚ) * ((5 : ℕ) : ℚ)
      rw [H₂ram_str1]
      norm_num
  · -- the transition leg at i = 0 (the only interior index)
    intro i hi
    have hi1 : i = 0 := by
      have h2 : i + 1 < 2 := H₂ram_len ▸ hi
      omega
    subst hi1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- recentering leg: the root is not a recentering
      intro hcontra
      exact absurd hcontra (fun h => ReadSpecies.noConfusion h)
    · -- THE (S-a) LEG: RG-2 guard + σV regrade + root-pair lift + child-pair transition
      intro _
      refine ⟨rfl, σVgate, regrade_gate, ?_, ?_⟩
      · show IsNodeLift ν₀ram R7Forge.ramifiedStage.Φ
        rw [Φram]
        exact nodeLift_ν₀ram
      · show TransitionCoreL σVgate R7Forge.ramifiedStage R7Forge.ramifiedStage.Φ 2 5
            U31.ν₀.zbar
        rw [Φram]
        exact tcl_gate
    · -- s-tie, guarded at σ₁.e = 1: vacuous (the forge child is ramified, e = 2)
      intro habs
      exact absurd (R7Forge.ramifiedStage_e.symm.trans habs) (by norm_num)
    · intro habs
      exact absurd (R7Forge.ramifiedStage_e.symm.trans habs) (by norm_num)
    · -- window containment (ADJACENT): 0 + 2 ≤ 2
      show (0 + 2 : ℕ) ≤ 2
      omega
    · -- width chain: D₁ = 2 = 1·2·1 = childWidth₀
      show (2 : ℕ) = 1 * 2 * 1
      norm_num
    · -- strict steepening: 1 < 5/4
      show (1 : ℚ) < 5 / 4
      norm_num

/-- The transported vertex value of the gate root is 1 (`a = 0`, `m̂ = 0`,
`Ranch/ψ^μ = ψ₂²/ψ₂² = 1`). -/
lemma vtx_ν₀ram : ν₀ram.vtx = 1 := by
  unfold Node.vtx
  have hexp : ν₀ram.a - (ν₀ram.μ : ℤ) * ν₀ram.mhat = 0 := by
    show (0 : ℤ) - (2 : ℤ) * ν₀ram.mhat = 0
    unfold Node.mhat
    show (0 : ℤ) - 2 * (-(0 : ℤ) * (1 : ℕ) * (2 : ℕ)) = 0
    norm_num
  rw [hexp, zpow_zero]
  have hpoly : ν₀ram.vtxPoly = 1 := by
    unfold Node.vtxPoly
    have hdiv : (U31.ψ₂ ^ 2 : Polynomial ↥U31.K2) /ₘ U31.ψ₂ ^ 2 = 1 := by
      have h := Polynomial.mul_divByMonic_cancel_left (1 : Polynomial ↥U31.K2)
        (HK13R.ψ₂_monic.pow 2)
      rwa [mul_one] at h
    show ((U31.ψ₂ ^ 2 : Polynomial ↥U31.K2) /ₘ U31.ψ₂ ^ (2 : ℕ)) %ₘ U31.ψ₂ = 1
    rw [hdiv]
    refine (Polynomial.modByMonic_eq_self_iff HK13R.ψ₂_monic).mpr ?_
    rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree HK13R.ψ₂_monic.ne_zero,
      HK13R.ψ₂_natDegree]
    norm_num
  rw [hpoly]
  simp

/-- **REALIZABILITY**: the appended (2,5) read is transition-admissible — the side is
ADJACENT (`s0₁ + wSide₁ = 2 = μ₀`), the pattern lead 1 equals the transported vertex
value `vtx ν₀ram = 1` ((HV)), the span slots enter strictly above the standing line
((SAE): `4 < 5` at slot 0, `2 < 5/2` at slot 1), and the vertex heights MATCH
(`line₁.at 4 = 0 = line₀.at 4`). -/
theorem realizable_H₂ram : Realizable H₂ram := by
  intro i hi
  have hi1 : i = 0 := by
    have h2 : i + 1 < 2 := H₂ram_len ▸ hi
    omega
  subst hi1
  show TransitionAdmissible ν₀ram ν₁ram
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (NA): non-adjacent premise is false (0 + 2 < 2)
    intro habs
    exact absurd (show (0 + 2 : ℕ) < 2 from habs) (by omega)
  · -- (HV): pattern lead = transported vertex value
    intro _
    show ((ν₁ram.pat (ν₁ram.wSide / ν₁ram.e) : ↥ν₁ram.σ.K) : F4) = ν₀ram.vtx
    rw [vtx_ν₀ram]
    show (((1 : ↥R7Forge.ramifiedStage.K)) : F4) = 1
    exact OneMemClass.coe_one _
  · -- (SAE): strict span entry below the vertex
    intro j h1 h2 h3
    have hj2 : j < 2 := h3
    interval_cases j
    · show Line.at ⟨4, 1⟩ (0 * ν₀ram.childWidth) < Line.at ⟨5, 5/4⟩ (0 * ν₀ram.childWidth)
      unfold Line.at
      norm_num
    · show Line.at ⟨4, 1⟩ (1 * ν₀ram.childWidth) < Line.at ⟨5, 5/4⟩ (1 * ν₀ram.childWidth)
      have hcw : ν₀ram.childWidth = 2 := rfl
      rw [hcw]
      unfold Line.at
      norm_num
  · -- vertex equality at adjacency
    intro _
    show Line.at ⟨5, 5/4⟩ (ν₀ram.μ * ν₀ram.childWidth) = Line.at ⟨4, 1⟩ (ν₀ram.μ * ν₀ram.childWidth)
    have hcw : ν₀ram.μ * ν₀ram.childWidth = 4 := rfl
    rw [hcw]
    unfold Line.at
    norm_num

/-- The gate history sits in the degree-4 box (root side `s0 + wSide = 4`). -/
theorem inBox_H₂ram : InBox 4 H₂ram := by
  intro hj
  show (0 + 4 : ℕ) ≤ 4
  omega

/-! ### §5 — THE PACKAGED POSITIVE GATE -/

/-- **THE HK-06 WAVE ACCEPTANCE GATE — PASSED** (the positive half of HK-22, the exact
conjunction `HK22.twoNodeGate_isEmpty` refutes for the frozen pre-wave keying): under
the ratified (S-a) two-step regrade keying there IS a 2-node history over the base pin
`bStageP` whose child frame is the forged `R7Forge.ramifiedStage`, satisfying
`HistoryCoherent ∧ Realizable ∧ InBox 4`.  The stride-decoupling collision is repaired:
the recorded lift rides the ROOT read pair (1,1); the transition record rides the CHILD
pair (2,5). -/
theorem twoNodeGate_pos :
    ∃ (H : History 2 F4) (hlen : 1 < H.nodes.length),
      (H.nodes[0]'(by omega)).σ = bStageP ∧
      (H.nodes[1]'hlen).σ = R7Forge.ramifiedStage ∧
      HistoryCoherent H ∧ Realizable H ∧ InBox 4 H :=
  ⟨H₂ram, by simp [H₂ram], rfl, rfl, coherent_H₂ram, realizable_H₂ram, inBox_H₂ram⟩

end HK23

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.HK23.regrade_gate
#print axioms LeanUrat.MovesJ.HK23.tcl_gate
#print axioms LeanUrat.MovesJ.HK23.nodeLift_ν₀ram
#print axioms LeanUrat.MovesJ.HK23.coherent_H₂ram
#print axioms LeanUrat.MovesJ.HK23.realizable_H₂ram
#print axioms LeanUrat.MovesJ.HK23.twoNodeGate_pos
