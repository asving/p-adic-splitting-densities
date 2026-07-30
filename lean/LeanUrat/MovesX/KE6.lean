/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs

/-! # KE6 — [ATTEMPT] X2BridgeP clause 1: the Undec(N) set decomposition

BRIDGE CAMPAIGN unit **KE6** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E (E-v) + §4 KE6).
PROVED (prover pass 2026-07-30, BP4-P9-x3-assembly; Lean-core footprint;
KE12 gate ran FIRST and sealed CLEAN — 12/12 PASS, 0 FINDING, cover check
0 outside + 0 DEEP-UNATTRIBUTED at every probed level, both boxes).

THE KERNEL: the FIRST conjunct of `X2BridgeP n X` (MovesX/Defs.lean) —
`Undec(N) ⊆ discZero ∪ ⋃ nsFiber ∪ InfTree ∪ {∃ leaf b, ns-free, N < thr(b) + cap(b)}`.

RECORDED RESOLUTIONS:
1. ⚑ WITHDRAWN AT STATEMENT LEVEL: the blueprint flags a "likely" new named
   XCtx law `DetectAtThr` ("a complete branch tree with thr + cap ≤ N is
   decided at N") — the statement-transcription check found it NOT needed:
   `XCtx.detectBranch` (leaf + ns-free + `thr + capHB ≤ N → DetectedAt`),
   `XCtx.undec_spec` (`f ∉ Undec N ↔ Finite (Branch f) ∧ all leaves detected`)
   and `XCtx.nsCover` (an ns-leaf point lies in some fiber) already carry
   exactly the decomposition's content, so the unit is UNCONDITIONAL over the
   context and no new law is proposed. (Should the prover hit a gap after all,
   the ⚑ re-fires per the blueprint — never improvised.)
2. Stated over a bare `C : XCtx n p` (strictly more general than the family
   form); the `X2BridgeP` clause is verbatim the instance `C := X.ctx p`,
   consumed by KE7's assembly.

Sketch (contrapositive): take `f ∈ Undec N` outside the first three sets and
suppose no witness leaf. `f ∉ InfTree` gives `Finite (Branch f)`; a leaf with an
ns node would put `f` in `⋃ nsFiber` via `nsCover`, so every leaf is ns-free;
absence of a fourth-set witness gives `thr + capHB ≤ N` at every leaf, so
`detectBranch` detects every leaf (`capHB` is definitionally `detectBranch`'s
ite) and `undec_spec` expels `f` from `Undec N` — contradiction.

deps: KE12 (CM gate — the Undec-decomposition probe runs FIRST: clause 1 is a
genuine ∀, finitely refutable — the strongest gate genre of the area).
Consumers: KE7 (both the a.e. clause and the `X2BridgeP` assembly).
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

/-- **KE6 [ATTEMPT]** — the Undec(N) four-set cover (X2-BRIDGE clause 1),
unconditional over the context; statement verbatim the first conjunct of
`X2BridgeP` at `C := X.ctx p` (resolution 2 of the module docstring).
deps: KE12 (gate). Sketch: the module docstring's contrapositive through
`undec_spec`/`nsCover`/`detectBranch`. -/
theorem x2Bridge_cover {n p : ℕ} [Fact p.Prime] (C : XCtx n p) (N : ℕ) :
    C.Undec N ⊆ discZero n p ∪ (⋃ i, C.nsFiber i) ∪ InfTree C ∪
      { f | ∃ b : C.Branch f,
          IsLeafB C b ∧ NsFreeB C b ∧ N < C.threshold b + capHB C b } := by
  intro f hf
  by_contra hout
  simp only [Set.mem_union, not_or, Set.mem_iUnion, not_exists,
    Set.mem_setOf_eq, InfTree] at hout
  obtain ⟨⟨⟨hdz, hns⟩, hinf⟩, hwit⟩ := hout
  -- `f ∉ InfTree` gives finiteness of the branch type.
  have hfin : Finite (C.Branch f) := not_not.mp hinf
  -- Show every leaf is detected at `N`, so `undec_spec` expels `f` — contradiction.
  refine absurd ((C.undec_spec f N).mpr ⟨hfin, fun b hleaf => ?_⟩) (by exact fun h => h hf)
  -- Every leaf is ns-free (an ns node would put `f` in a fiber via `nsCover`).
  have hnsfree : ∀ ν ∈ C.hist b, ¬ C.nsTrack ν := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ν, hν, hns'⟩ := hcon
    obtain ⟨i, hi⟩ := C.nsCover f ⟨b, hleaf, ν, hν, hns'⟩
    exact hns i hi
  -- No fourth-set witness: the leaf's threshold + cap is within `N`.
  have hcap : C.threshold b + capHB C b ≤ N := by
    by_contra hgt
    push Not at hgt
    exact hwit b ⟨hleaf, hnsfree, hgt⟩
  -- `detectBranch` closes (`capHB` is definitionally its ite).
  exact C.detectBranch b hleaf hnsfree N (by simpa [capHB] using hcap)

end LeanUrat.MovesX
