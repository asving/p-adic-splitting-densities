/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesU.BridgeD1_treeModelWire
import LeanUrat.MovesU.BridgeD2_chartSemantics

/-!
# IB-D3 — THE σ-TYPED TREE CARRIER (bridge campaign BP1, cluster c7)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†5) /
§4 group D (IB-D3) / §5 R2.  Deps: IB-D1 (`bridgePol`/`bridgeTm`), IB-D2
(`bridgeChart`).  Charge: the carrier `Tree σ` of the constructed
`FiberSeries` (Architecture B, adjudicated Q1) + DecidableEq (Classical) +
the `lvl` accessor.

THE CARRIER (†5, as REPAIRED at the NSF-KEY execution — see below):
    Tree σ := {V : MovesT.VTree p (ZMod p) //
                 V.typemult = σ.1 ∧ RealizedSelf V ∧ MovesT.NsFree V}
    RealizedSelf V := Realizes (Tm (lvl V)) (chart (lvl V) _) V
    lvl V := max (V.thr n) 1
— σ-typed, complete finite canonical BY CONSTRUCTION (`VTree`'s own
`chains`/`hfin`/`hclosed`/`hleaf` fields), REALIZABLE at its own threshold
level, and NS-FREE (no ns-marked leaf).

NSF-KEY REPAIR (M02 §2's sanctioned minimal repair; sign-off of record
2026-08-05, BRIDGE_ADJUDICATIONS_2026-07-30.md:1709; retirement semantics
R11_REPAIR_DESIGN_V5_2026-08-04.md (NSF-KEY-RET); ripple enumeration
notes/openmath/UNITC_ripple.md): the original 2-clause carrier admitted
ns-marked self-realized trees — M02 §2's exact-square poison V₀, through
which `bridgeCanonical` decided window-degenerate loci ("totally split" on
exact squares) and `count_tie`/`canonical_stable`/`VPSound` were refutable
AS TYPED at the intended instance. The `MovesT.NsFree` conjunct
(MovesT/Defs.lean, the note's TREE-N hypothesis = `MovesT.treeN`'s `hdet`)
makes ns loci fiber NO carried tree, so they DRAIN to `none`/env(N) — the
M9/Phase-B drainage design — and the seam's `∀ T` rows range over exactly
the hdet-guarded corpus. `canonical_pin`, `vtree_eq_of_fiberAt`, and the
M02 Lemmas A/B are untouched (they never used the ns clause).

RISK R2 FAILURE-MODE DISPLAY (mandatory per §5 R2 — why realizability MUST be
in the carrier): over the naive carrier {V // V.typemult = σ.1} (all σ-typed
VTrees, realizability dropped), `TreePin.vt_real` — every carried tree
realizes at every level ≥ its threshold — is expected FALSE: the `VTree`
structure fields constrain only the tree's internal combinatorics
(finite closed chain set, leaf verdicts, hen payload of the right total
degree), so JUNK TREES of the correct typemult that NO box point fibers
(`fiberAt` empty at every level) inhabit the naive carrier, and no
countermodel unit can be dodged.  With `RealizedSelf` IN the carrier,
`vt_real` reduces to the transfer row (IB-D15 from IB-D5's `TransferRow`),
and NO countermodel unit is needed.  If a prover finds even the carrier
version false, the `TransferRow` is mis-scoped — report, adjudication (R2).

TRANSCRIPTION RESOLUTIONS (recorded per the E-phase rules):
* `Tm`/`chart` are wired to the PINNED exports `bridgeTm` (IB-D1, sorried
  designer obligation — R7 confirmed there) and `bridgeChart` (IB-D2) — per
  D1's charge that downstream D-group units NAME the pinned pair now.
* `lvl` is defined at the `VTree` level (`bridgeLvl`), generic in the residue
  field F (it reads only `V.thr n`); the carrier-level projection is
  `bridgeTree.lvl`.  The chart-guard positivity 0 < lvl V is `bridgeLvl_pos`
  (the max-with-1 exists exactly for this guard — same discipline as
  `TreePin.chart`, round-3 CRITICAL 1).
* FILE NAMING: the blueprint's group-D file `BridgeTrees.lean` was superseded
  by the fleet's per-unit convention (front-runners BridgeD1/D2/D10/D13
  landed per-unit; per-unit also keeps sibling clusters' units D9a/D11–D18
  out of edit conflicts under the new-files-only rule).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (†5)'s `lvl`: a tree's OWN working level, `lvl V := max (V.thr n) 1` —
    the threshold join with 1 so the guarded chart (round-3 CRITICAL 1)
    always applies.  Generic in the residue field (reads only `V.thr n`). -/
noncomputable def bridgeLvl {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (n : ℕ) (V : MovesT.VTree p F) : ℕ :=
  max (V.thr n) 1

/-- The chart guard at a tree's own level: 0 < lvl V (the `1` in the max). -/
theorem bridgeLvl_pos {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (n : ℕ) (V : MovesT.VTree p F) : 0 < bridgeLvl n V :=
  lt_of_lt_of_le zero_lt_one (le_max_right _ _)

/-- A tree's threshold is within its own level (IB-D15's entry point for the
    transfer from lvl). -/
theorem thr_le_bridgeLvl {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (n : ℕ) (V : MovesT.VTree p F) : V.thr n ≤ bridgeLvl n V :=
  le_max_left _ _

/-- (†5)'s `RealizedSelf`: V is realized at ITS OWN level lvl V, at the pinned
    model/chart (`bridgeTm` from IB-D1, `bridgeChart` from IB-D2).  This is
    the clause whose ABSENCE makes `vt_real` false over the naive carrier —
    see the R2 failure-mode display in the file header. -/
def RealizedSelf (n p : ℕ) [Fact p.Prime] (V : MovesT.VTree p (ZMod p)) : Prop :=
  MovesT.Realizes (bridgeTm p n (bridgeLvl n V))
    (bridgeChart n (bridgeLvl n V) (bridgeLvl_pos n V)) V

/-- (†5) THE TREE CARRIER: the σ-typed, self-realized, NS-FREE
    `MovesT.VTree`s — the constructed `FiberSeries.Tree σ` (Architecture B:
    the classifier IS the tree-fibering verdict, so this carrier is the ONE
    tree vocabulary).  Complete finite canonical BY CONSTRUCTION (`VTree`'s
    own fields); realizable at its own threshold level (`RealizedSelf`); no
    ns-marked leaf (`MovesT.NsFree` — the NSF-KEY repair conjunct, M02 §2:
    without it the exact-square poison V₀ is carried and the classifier
    decides window-degenerate loci; with it they drain to the envelope). -/
def bridgeTree (n p : ℕ) [Fact p.Prime] (σ : SplittingType n) : Type :=
  {V : MovesT.VTree p (ZMod p) //
    V.typemult = σ.1 ∧ RealizedSelf n p V ∧ MovesT.NsFree V}

/-- DecidableEq for the carrier (Classical — `FiberSeries.instTreeDeq`'s
    supply; gap 7 of the interface: needed to build the slice Finsets). -/
noncomputable instance (n p : ℕ) [Fact p.Prime] (σ : SplittingType n) :
    DecidableEq (bridgeTree n p σ) :=
  Classical.decEq _

/-- The carrier-level `lvl` projection (†9's mass is defined AT THE TREE'S OWN
    LEVEL — IB-D12 consumes this). -/
noncomputable def bridgeTree.lvl {n p : ℕ} [Fact p.Prime] {σ : SplittingType n}
    (T : bridgeTree n p σ) : ℕ :=
  bridgeLvl n T.1

end LeanUrat.MovesU
