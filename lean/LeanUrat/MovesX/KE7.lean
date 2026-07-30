/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.KE6
import LeanUrat.MovesX.XF10
import LeanUrat.MovesX.XG2d

/-! # KE7 — X2BridgeP clause 2 (the a.e. clause) + the X2BridgeP assembly

BRIDGE CAMPAIGN unit **KE7** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E (E-v continuation) + §4 KE7).
PROVED (prover pass 2026-07-30, BP4-P9-x3-assembly; Lean-core footprint).

THE KERNEL: the SECOND conjunct of `X2BridgeP n X` (MovesX/Defs.lean) — the
`Undec(N)`-members without a leaf witness form a `frac`-null set — plus the
assembly of both clauses into `X2BridgeP` itself.

Sketch ("clause 1 + null legs", routine given deps): by KE6's cover, the
witness-free part of `Undec N` sits inside `discZero ∪ ⋃ nsFiber ∪ InfTree`;
the three null legs are
* `discZero` null — XF10 `discZeroNull` (PROVED; needs `2 ≤ n`),
* `⋃ nsFiber` null — `NsNullP` (KE1's target; consumed by name, exactly as
  XG3 `x3Density` consumes it) + `nsCountable` + `frac_iUnion_null` (the XG3
  reindexing pattern),
* `InfTree` null — the route's own (a) leg, checked at XG3's exact form:
  XG2d `treeFinite` (PROVED) gives `f ∉ discZero → Finite (Branch f)` under
  `X3aRouteP`, i.e. `InfTree ⊆ discZero` — so this leg consumes `X3aRouteP`
  (with its `XConsts`) and `1 ≤ n`, and no new law is needed;
finite subadditivity (`frac_union_le` twice) + `frac_nonneg` close the zero.

RECORDED RESOLUTION: the hypothesis surface is `(hn : 2 ≤ n)`, `X3aRouteP`
(with its `K`) and `NsNullP` BY NAME — the same trio XG3's `x3Density` carries;
nothing weaker suffices for the InfTree leg (REV-3 tag: NO route avoids X.1b)
and nothing stronger is taken.

deps: KE6 (clause 1), KE1 (the nsFiber null leg, consumed as `NsNullP`).
Consumers: the X.2 envelope layers (CL-2/CL-3 tag inheritance); `X2BridgeP`'s
own consumers via the assembly below.
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

/-- **KE7 (a.e. clause)** — the witness-free part of `Undec N` is null, given
the route tags (module docstring sketch): KE6's cover + XF10 (`discZero`) +
`NsNullP` (fibers) + XG2d `treeFinite` under `X3aRouteP` (`InfTree ⊆ discZero`).
Statement verbatim the second conjunct of `X2BridgeP` at `p`, `N`. -/
theorem x2Bridge_nullClause {n : ℕ} (X : XFamily n) (K : XConsts n)
    (hn : 2 ≤ n) (R : X3aRouteP n X K) (NS : NsNullP n X)
    (p : ℕ) [Fact p.Prime] (N : ℕ) :
    (X.ctx p).frac { f | f ∈ (X.ctx p).Undec N ∧
      ¬ ∃ b : (X.ctx p).Branch f,
          IsLeafB (X.ctx p) b ∧ NsFreeB (X.ctx p) b ∧
            N < (X.ctx p).threshold b + capHB (X.ctx p) b } = 0 := by
  set C := X.ctx p with hC
  -- `frac (discZero) = 0` (XF.10).
  have hdz : C.frac (discZero n p) = 0 := discZeroNull n p hn C
  -- `frac ∅ = 0` (monotone into the null `discZero`).
  have hEmpty : C.frac (∅ : Set (MonicBox n p)) = 0 :=
    le_antisymm (by simpa [hdz] using C.frac_mono ∅ (discZero n p) (Set.empty_subset _))
      (C.frac_nonneg _)
  -- `frac (⋃ i, nsFiber i) = 0` (`NsNullP` + countability — the XG3 reindexing pattern).
  have hns : C.frac (⋃ i, C.nsFiber i) = 0 := by
    haveI : Countable C.nsIdx := C.nsCountable
    obtain ⟨e, he⟩ :
        ∃ e : ℕ → Option C.nsIdx, Function.Surjective e :=
      exists_surjective_nat _
    set g : Option C.nsIdx → Set (MonicBox n p) :=
      fun o => o.elim ∅ C.nsFiber with hg
    have hgnull : ∀ o, C.frac (g o) = 0 := by
      intro o
      cases o with
      | none => simpa [hg] using hEmpty
      | some i => simpa [hg] using NS p i
    have hunion : (⋃ i, C.nsFiber i) = ⋃ k, g (e k) := by
      rw [he.iUnion_comp g]
      simp [hg, Set.iUnion_option]
    rw [hunion]
    exact C.frac_iUnion_null (fun k => g (e k)) (fun k => hgnull (e k))
  -- KE6's cover + `InfTree ⊆ discZero` (XG2d `treeFinite` under the route tags):
  -- the witness-free part of `Undec N` sits inside `discZero ∪ ⋃ nsFiber`.
  have hsub : { f | f ∈ C.Undec N ∧
      ¬ ∃ b : C.Branch f,
          IsLeafB C b ∧ NsFreeB C b ∧ N < C.threshold b + capHB C b } ⊆
      discZero n p ∪ (⋃ i, C.nsFiber i) := by
    rintro f ⟨hf, hno⟩
    rcases x2Bridge_cover C N hf with ((h1 | h2) | hI) | hW
    · exact Or.inl h1
    · exact Or.inr h2
    · -- `f ∈ InfTree C`: off `discZero` the tree is finite (XG2d) — contradiction.
      by_cases hd : f ∈ discZero n p
      · exact Or.inl hd
      · exact absurd (treeFinite X K R p (by omega) f hd) hI
    · exact absurd hW hno
  -- Finite subadditivity + nonnegativity close the zero.
  refine le_antisymm ?_ (C.frac_nonneg _)
  calc C.frac { f | f ∈ C.Undec N ∧
      ¬ ∃ b : C.Branch f,
          IsLeafB C b ∧ NsFreeB C b ∧ N < C.threshold b + capHB C b }
      ≤ C.frac (discZero n p ∪ ⋃ i, C.nsFiber i) := C.frac_mono _ _ hsub
    _ ≤ C.frac (discZero n p) + C.frac (⋃ i, C.nsFiber i) := C.frac_union_le _ _
    _ = 0 := by rw [hdz, hns]; ring

/-- **KE7 (assembly)** — `X2BridgeP n X` from clause 1 (KE6, unconditional over
the context) and clause 2 (above), under the same named hypothesis surface.
deps: KE6, `x2Bridge_nullClause`. -/
theorem x2Bridge_assembled {n : ℕ} (X : XFamily n) (K : XConsts n)
    (hn : 2 ≤ n) (R : X3aRouteP n X K) (NS : NsNullP n X) :
    X2BridgeP n X := by
  intro p hp N
  exact ⟨x2Bridge_cover (X.ctx p) N, x2Bridge_nullClause X K hn R NS p N⟩

end LeanUrat.MovesX
