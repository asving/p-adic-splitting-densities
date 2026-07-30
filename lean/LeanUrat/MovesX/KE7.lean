/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs

/-! # KE7 — X2BridgeP clause 2 (the a.e. clause) + the X2BridgeP assembly

BRIDGE CAMPAIGN unit **KE7** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E (E-v continuation) + §4 KE7).
E-PHASE STATEMENT MODULE — statements with `sorry` bodies.

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
  sorry

/-- **KE7 (assembly)** — `X2BridgeP n X` from clause 1 (KE6, unconditional over
the context) and clause 2 (above), under the same named hypothesis surface.
deps: KE6, `x2Bridge_nullClause`. -/
theorem x2Bridge_assembled {n : ℕ} (X : XFamily n) (K : XConsts n)
    (hn : 2 ≤ n) (R : X3aRouteP n X K) (NS : NsNullP n X) :
    X2BridgeP n X := by
  sorry

end LeanUrat.MovesX
