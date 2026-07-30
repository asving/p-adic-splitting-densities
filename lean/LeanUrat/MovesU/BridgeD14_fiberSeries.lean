/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger
import LeanUrat.MovesU.BridgeD13_sliceFinite

/-!
# IB-D14 — `bridgeFibers : FiberSeries` ASSEMBLY (bridge campaign BP1, cluster c9)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†5)/(†9)
/ §4 group D (IB-D14) / §3.7 ORDERING CONSTRAINT ("`slice_finite` is consumed by
the DEFINITION of thrSlice, so F's construction takes it as an argument").

INFORMAL STATEMENT: assemble the per-(n, p) `FiberSeries n p X` of the bridge:
carrier `Tree` (IB-D3's (†5) subtype), `mass` (IB-D12's normalized fiber count),
`thr` (the VTree's own threshold through `vt`), `thrSlice` from the
`slice_finite` argument through IB-D13's `sliceFinset`, with `mem_slice_iff` /
`slice_exhausts` supplied by IB-D13's PROVED spec lemmas.

DEPS: D11–D13 (D13 landed — wired; D3/D12 enter as binders).  TRANSCRIPTION
RESOLUTION (recorded): IB-D3's carrier is another cluster's unit, not landed —
the assembly is PARAMETRIC in the carrier data (`Tree`/`mass`/`thr`) with the
`FiberSeries` fields' verbatim types (Defs.lean:227–238), exactly the
"fields above the line feed constructions" split of §3.7: `slice_finite` is the
BridgeKernels row (or the R6-probe theorem `realizedSelf_slice_finite` of
BridgeD13, if the probe lands — then the row LEAVES the pack), taken as an
argument.  IB-F4 instantiates `Tree` at IB-D3's carrier, `mass` at IB-D12's
`bridgeMass ∘ vt`, `thr` at `(vt ·).thr n`.

PROOF SKETCH: assembly-only (R, ~10) — record literal; `instTreeDeq` Classical;
`mem_slice_iff`/`slice_exhausts` are IB-D13's `mem_sliceFinset`/
`sliceFinset_exhausts` verbatim.  No sorry needed.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open scoped ENNReal

/-- (†5)/(†9) THE BRIDGE FIBER SERIES, parametric in IB-D3's carrier data (file
    header): `thrSlice` is DEFINED from the `slice_finite` witness through
    IB-D13's `sliceFinset`, so `mem_slice_iff`/`slice_exhausts` come from D13's
    PROVED spec lemmas — the §3.7 ordering constraint compiled. -/
noncomputable def bridgeFibers (n p : ℕ) [Fact p.Prime] (X : ClassifierSpec n p)
    (Tree : SplittingType n → Type)
    (mass : ∀ σ : SplittingType n, Tree σ → ℝ≥0∞)
    (thr : ∀ σ : SplittingType n, Tree σ → ℕ)
    (slice_finite : ∀ (σ : SplittingType n) (N : ℕ),
      {T : Tree σ | thr σ T ≤ N}.Finite) :
    FiberSeries n p X where
  Tree := Tree
  instTreeDeq := fun _ => Classical.decEq _
  mass := mass
  thr := thr
  thrSlice := fun σ N => sliceFinset (thr σ) N (slice_finite σ N)
  mem_slice_iff := fun σ N T => mem_sliceFinset (thr σ) N (slice_finite σ N) T
  slice_exhausts := fun σ T => sliceFinset_exhausts (thr σ) (slice_finite σ) T

/-- The slice reads through to IB-D13's `sliceFinset` (definitional display —
    the consumer-facing unfolding IB-F3/F6 use to key `cl7_slice` to the
    `slice_bound` row). -/
theorem bridgeFibers_thrSlice (n p : ℕ) [Fact p.Prime] (X : ClassifierSpec n p)
    (Tree : SplittingType n → Type)
    (mass : ∀ σ : SplittingType n, Tree σ → ℝ≥0∞)
    (thr : ∀ σ : SplittingType n, Tree σ → ℕ)
    (slice_finite : ∀ (σ : SplittingType n) (N : ℕ),
      {T : Tree σ | thr σ T ≤ N}.Finite)
    (σ : SplittingType n) (N : ℕ) :
    (bridgeFibers n p X Tree mass thr slice_finite).thrSlice σ N
      = sliceFinset (thr σ) N (slice_finite σ N) := rfl

end LeanUrat.MovesU
