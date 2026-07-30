/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs

/-! # KE2 — [ATTEMPT] X2AffP: the affine threshold bound from a per-move law

BRIDGE CAMPAIGN unit **KE2** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E (E-ii) + §4 KE2).
PROVED (2026-07-30, prover BP4-P8) — sorry-free, Lean-core axiom footprint.

THE KERNEL: `X2AffP n X K` (MovesX/Defs.lean) — `thr(b) ≤ 1 + c₀·Σ h_r` on the
fourth-piece family. Blueprint sketch: branch induction through D.11's per-move
threshold form ("largest constrained height + 1") with scale product `Π e_i ≤ n`;
candidate `c₀ = n·C_move`.

RECORDED RESOLUTIONS:
1. ⚑ `ThresholdStep` is the blueprint-flagged NAMED LAW (the check "which XCtx
   threshold laws exist" came back EMPTY — `XCtx.threshold` is free data, the
   per-move form is unbuilt, so the ⚑ fires as the blueprint anticipates;
   hypothesis shape per Q4, never a new `XCtx` field). Its `step` field is the
   D.11 per-move form with the scale factor applied at CONTINUING INCREMENTS
   ONLY (`ν.continuing && ν.isIncrement`) — the minimal resolution against the
   repo vocabulary, since `HistWF.degProd` (the corpus's ONLY `Π e_i ≤ n`) is
   filtered on exactly that predicate. Whether D.11 also scales at recentering
   moves is part of the ⚑ ratification.
2. The constant hypothesis is `n·(C_move + 1) ≤ K.c0`, STRENGTHENED from the
   blueprint's candidate `c₀ = n·C_move`: unrolling the step law along a
   nonempty history yields `thr ≤ Π(scale) + C_move·Π(scale)·Σ h_r ≤
   n + n·C_move·Σ h_r`, and absorbing the root term `n` into the affine form
   `1 + c₀·Σ h_r` uses `Σ h_r ≥ 1` (each `ν.hpos`), costing the extra `+n·Σ h_r`.
   This is hypothesis-side slack only; `X2AffP` itself is untouched.

deps: KE11 (CM gate — the affine-envelope probe runs FIRST; acceptance of any
proof is gated on its candidate-stress record, REV 2 F5). Fallback: the
obstruction record with the branch shape whose threshold outruns the affine
bound. Consumers: XD4 `x2hypAssembled` (via `X2AffP` by name), KE9.

GATE RECORD (2026-07-30, prover BP4-P8): KE11 RAN FIRST and sealed clean
(22/22 PASS, exit 0; verification/results/ke11_affine_envelope.json): the
per-move ledger is census-consistent with `ThresholdStep` (C_move = 3 at
n = 3, = 2 at n = 2; every per-move increment ≤ C_move·h at scale 1), the
sketch candidate c₀ = n·C_move passes in-box (empirical minimal c₀ = n),
and the growth detector found no super-affine branch family.
`x2Aff_of_thresholdStep` PROVED below (Lean-core footprint); the ⚑ instance
leg for `ThresholdStep` remains owner-side (D.11/MovesD).
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

/-- KE2 helper — the partial scale product of a history: the product of the
increment degrees over the continuing increments (EXACTLY the `HistWF.degProd`
expression, so the wf field bounds it by `n`). -/
private def scaleN {n : ℕ} (H : XHistory n) : ℕ :=
  ((H.filter (fun ν => ν.continuing && ν.isIncrement)).map (·.e)).prod

private lemma scaleN_nil {n : ℕ} : scaleN ([] : XHistory n) = 1 := rfl

private lemma scaleN_append {n : ℕ} (H : XHistory n) (ν : XNode n) :
    scaleN (H ++ [ν])
      = scaleN H * (if ν.continuing && ν.isIncrement then ν.e else 1) := by
  unfold scaleN
  rw [List.filter_append, List.map_append, List.prod_append]
  by_cases h : (ν.continuing && ν.isIncrement) = true
  · simp [h]
  · simp [h]

private lemma one_le_scaleN {n : ℕ} (H : XHistory n) : 1 ≤ scaleN H := by
  have hpos : 0 < scaleN H := by
    unfold scaleN
    apply List.prod_pos
    intro a ha
    obtain ⟨ν, _, rfl⟩ := List.mem_map.mp ha
    exact ν.epos
  exact hpos

private lemma sumH_append {n : ℕ} (H : XHistory n) (ν : XNode n) :
    sumH (H ++ [ν]) = sumH H + ν.h := by
  simp [sumH]

private lemma sumH_nil {n : ℕ} : sumH ([] : XHistory n) = 0 := rfl

/-- **KE2 named law (⚑ ratification)** — D.11's per-move threshold form over one
context: the root threshold is at most `1`, and each child read moves the
threshold by at most the increment scale `e` times the parent threshold plus
`C_move` times the read's own height ("largest constrained height + 1", with the
scale applied at continuing increments only — resolution 1 of the module
docstring). Owner of the instance leg: the D.11/MovesD side (not this unit). -/
structure ThresholdStep (n p : ℕ) [Fact p.Prime] (C : XCtx n p)
    (Cmove : ℚ) : Prop where
  root : ∀ f : MonicBox n p, ((C.threshold (C.root f) : ℕ) : ℚ) ≤ 1
  step : ∀ (f : MonicBox n p) (b c : C.Branch f) (ν : XNode n),
    c ∈ C.children b → C.hist c = C.hist b ++ [ν] →
      ((C.threshold c : ℕ) : ℚ) ≤
        (if ν.continuing && ν.isIncrement then (ν.e : ℚ) else 1)
            * ((C.threshold b : ℕ) : ℚ)
          + Cmove * (ν.h : ℚ)

/-- **KE2 [ATTEMPT]** — `X2AffP` from the per-move law: branch induction along
the `parent` chain (every branch reaches the root, `C.reach`; each step appends
one node, `C.parent_hist`/`children_iff`), unrolling `ThresholdStep.step` and
bounding every partial scale product by `n` through `HistWF.degProd`
(`C.wf`; all factors ≥ 1 by `XNode.epos`). Constant bookkeeping per
resolution 2: `thr(b) ≤ n + n·C_move·Σ h_r ≤ 1 + n·(C_move+1)·Σ h_r ≤
1 + K.c0·Σ h_r`, the empty history closed by `root`. deps: KE11 (gate),
`ThresholdStep` (⚑). -/
theorem x2Aff_of_thresholdStep {n : ℕ} (X : XFamily n) (K : XConsts n)
    (Cmove : ℚ) (hCmove : 0 ≤ Cmove)
    (hstep : ∀ (p : ℕ) [Fact p.Prime], ThresholdStep n p (X.ctx p) Cmove)
    (hc0 : (n : ℚ) * (Cmove + 1) ≤ K.c0) :
    X2AffP n X K := by
  unfold X2AffP
  intro p _ f b hb
  -- The branch invariant, by induction along the parent chain:
  --   thr(b') ≤ scaleN(hist b') · (1 + Cmove·Σ h_r)
  -- (root: `ThresholdStep.root`; step: unroll `ThresholdStep.step`, absorbing
  -- the per-move `Cmove·h` term into the grown scale product via `1 ≤ s·P`).
  have key : ∀ b' : (X.ctx p).Branch f,
      ((X.ctx p).threshold b' : ℚ) ≤
        (scaleN ((X.ctx p).hist b') : ℚ)
          * (1 + Cmove * (sumH ((X.ctx p).hist b') : ℚ)) := by
    intro b'
    have hreach := (X.ctx p).reach b'
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        rw [(X.ctx p).hist_root f, scaleN_nil, sumH_nil]
        simpa using (hstep p).root f
    | @head a c hpar hrest ih =>
        obtain ⟨ν, hν⟩ := (X.ctx p).parent_hist a c hpar
        have hchild : a ∈ (X.ctx p).children c :=
          ((X.ctx p).children_iff c a).mpr hpar
        have hstep' := (hstep p).step f c a ν hchild hν
        rw [hν, scaleN_append, sumH_append]
        have hP1 : (1 : ℚ) ≤ (scaleN ((X.ctx p).hist c) : ℚ) := by
          exact_mod_cast one_le_scaleN ((X.ctx p).hist c)
        have hP0 : (0 : ℚ) ≤ (scaleN ((X.ctx p).hist c) : ℚ) := by linarith
        have hh0 : (0 : ℚ) ≤ (ν.h : ℚ) := Nat.cast_nonneg _
        have hS0 : (0 : ℚ) ≤ (sumH ((X.ctx p).hist c) : ℚ) := Nat.cast_nonneg _
        have hCh0 : (0 : ℚ) ≤ Cmove * (ν.h : ℚ) := mul_nonneg hCmove hh0
        by_cases hcase : (ν.continuing && ν.isIncrement) = true
        · simp only [hcase, if_true] at hstep' ⊢
          have he1 : (1 : ℚ) ≤ (ν.e : ℚ) := by exact_mod_cast ν.epos
          have he0 : (0 : ℚ) ≤ (ν.e : ℚ) := by linarith
          have hsP1 : (1 : ℚ) ≤
              (ν.e : ℚ) * (scaleN ((X.ctx p).hist c) : ℚ) := by nlinarith
          have habsorb : Cmove * (ν.h : ℚ) ≤
              ((ν.e : ℚ) * (scaleN ((X.ctx p).hist c) : ℚ)) * (Cmove * (ν.h : ℚ)) :=
            le_mul_of_one_le_left hCh0 hsP1
          have hmul : (ν.e : ℚ) * ((X.ctx p).threshold c : ℚ) ≤
              (ν.e : ℚ) * ((scaleN ((X.ctx p).hist c) : ℚ)
                * (1 + Cmove * (sumH ((X.ctx p).hist c) : ℚ))) :=
            mul_le_mul_of_nonneg_left ih he0
          push_cast
          calc ((X.ctx p).threshold a : ℚ)
              ≤ (ν.e : ℚ) * ((X.ctx p).threshold c : ℚ) + Cmove * (ν.h : ℚ) :=
                hstep'
            _ ≤ (ν.e : ℚ) * ((scaleN ((X.ctx p).hist c) : ℚ)
                  * (1 + Cmove * (sumH ((X.ctx p).hist c) : ℚ)))
                + ((ν.e : ℚ) * (scaleN ((X.ctx p).hist c) : ℚ))
                  * (Cmove * (ν.h : ℚ)) := by linarith
            _ = (scaleN ((X.ctx p).hist c) : ℚ) * (ν.e : ℚ)
                * (1 + Cmove * ((sumH ((X.ctx p).hist c) : ℚ) + (ν.h : ℚ))) := by
                ring
        · simp only [hcase] at hstep' ⊢
          have habsorb : Cmove * (ν.h : ℚ) ≤
              (scaleN ((X.ctx p).hist c) : ℚ) * (Cmove * (ν.h : ℚ)) :=
            le_mul_of_one_le_left hCh0 hP1
          push_cast
          calc ((X.ctx p).threshold a : ℚ)
              ≤ 1 * ((X.ctx p).threshold c : ℚ) + Cmove * (ν.h : ℚ) := hstep'
            _ ≤ (scaleN ((X.ctx p).hist c) : ℚ)
                  * (1 + Cmove * (sumH ((X.ctx p).hist c) : ℚ))
                + (scaleN ((X.ctx p).hist c) : ℚ) * (Cmove * (ν.h : ℚ)) := by
                linarith [ih]
            _ = (scaleN ((X.ctx p).hist c) : ℚ) * 1
                * (1 + Cmove * ((sumH ((X.ctx p).hist c) : ℚ) + (ν.h : ℚ))) := by
                ring
  -- Close: bound the scale product by `n` (degProd) and absorb the root term.
  have hPn : (scaleN ((X.ctx p).hist b) : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast ((X.ctx p).wf b).degProd
  have hP1 : (1 : ℚ) ≤ (scaleN ((X.ctx p).hist b) : ℚ) := by
    exact_mod_cast one_le_scaleN ((X.ctx p).hist b)
  have hS0 : (0 : ℚ) ≤ (sumH ((X.ctx p).hist b) : ℚ) := Nat.cast_nonneg _
  by_cases hH : (X.ctx p).hist b = []
  · have hkey := key b
    rw [hH, scaleN_nil, sumH_nil] at hkey
    rw [hH, sumH_nil]
    push_cast at hkey ⊢
    linarith
  · -- nonempty history: Σ h_r ≥ 1 (every node has h ≥ 1)
    have h1S : 1 ≤ sumH ((X.ctx p).hist b) := by
      obtain ⟨ν, hν⟩ := List.exists_mem_of_ne_nil _ hH
      have hmem : ν.h ∈ ((X.ctx p).hist b).map (·.h) :=
        List.mem_map_of_mem hν
      have hle : ν.h ≤ sumH ((X.ctx p).hist b) :=
        List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
      exact le_trans ν.hpos hle
    have hS1 : (1 : ℚ) ≤ (sumH ((X.ctx p).hist b) : ℚ) := by exact_mod_cast h1S
    have hn0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg _
    have hCS0 : (0 : ℚ) ≤ 1 + Cmove * (sumH ((X.ctx p).hist b) : ℚ) := by
      have := mul_nonneg hCmove hS0
      linarith
    have h2 : (scaleN ((X.ctx p).hist b) : ℚ)
        * (1 + Cmove * (sumH ((X.ctx p).hist b) : ℚ)) ≤
        (n : ℚ) * (1 + Cmove * (sumH ((X.ctx p).hist b) : ℚ)) :=
      mul_le_mul_of_nonneg_right hPn hCS0
    have h3 : (n : ℚ) * 1 ≤ (n : ℚ) * (sumH ((X.ctx p).hist b) : ℚ) :=
      mul_le_mul_of_nonneg_left hS1 hn0
    have h4 : ((n : ℚ) * (Cmove + 1)) * (sumH ((X.ctx p).hist b) : ℚ) ≤
        K.c0 * (sumH ((X.ctx p).hist b) : ℚ) :=
      mul_le_mul_of_nonneg_right hc0 hS0
    calc ((X.ctx p).threshold b : ℚ)
        ≤ (scaleN ((X.ctx p).hist b) : ℚ)
            * (1 + Cmove * (sumH ((X.ctx p).hist b) : ℚ)) := key b
      _ ≤ (n : ℚ) * (1 + Cmove * (sumH ((X.ctx p).hist b) : ℚ)) := h2
      _ = (n : ℚ) + (n : ℚ) * Cmove * (sumH ((X.ctx p).hist b) : ℚ) := by ring
      _ ≤ 1 + (n : ℚ) * (sumH ((X.ctx p).hist b) : ℚ)
            + (n : ℚ) * Cmove * (sumH ((X.ctx p).hist b) : ℚ) := by linarith
      _ = 1 + ((n : ℚ) * (Cmove + 1)) * (sumH ((X.ctx p).hist b) : ℚ) := by ring
      _ ≤ 1 + K.c0 * (sumH ((X.ctx p).hist b) : ℚ) := by linarith

end LeanUrat.MovesX
