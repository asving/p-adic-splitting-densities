/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.GRDefs

/-!
# B2D/GR0_readHyps — THE E-GATE: the `ReadHyps` supplier map  [B2DEF_LEAN unit GR-0; wave E]

Blueprint: `lean/blueprints/B2DEF_LEAN_2026-08-08.md` §4 + §5 (unit GR-0, [R1-C2/C4
fold]). moves_ref: D.0 (P1)–(P4), D.5. deps: E1. difficulty: medium; HIGH
information value. **NO sorry in this file** — the gate's whole content is what is
PROVED versus what is DISPLAYED.

## GATE VERDICT: PASS-WITH-DISPLAYED-RESIDUE

The §4 interface (`ReadHyps`, `graded_read`'s three-clause shape) ELABORATES against
the real carriers (`Node`, `GenuineStageModel`, `IsNodeLift`) — see `GR4_gradedRead`
compiling downstream. The supplier probe (order per the blueprint: coherence width
clause / `hDwidth`, `Node.hψdeg`, Stage T-vector laws, V34/S9w parent instances):

## THE SUPPLIER MAP (per `ReadHyps` field)

| field       | verdict | supplier |
|-------------|---------|----------|
| `hscale`    | **DISPLAYED-HYPOTHESIS** | none at a single node (see below) |
| `hbez`      | SUPPLIED | `Node.hbez` (the read's own recorded Bézout pair, F10) |
| `hbezCanon` | SUPPLIED | `Node.hbezCanon` (canonical window `0 ≤ t < e`) |
| `hψmonic`   | SUPPLIED | `Node.hψmonic` |
| `hψirr`     | SUPPLIED | `Node.hψirr` |
| `hψdeg`     | SUPPLIED | `Node.hψdeg` |
| `hψ0`       | **DISPLAYED-HYPOTHESIS** | none: at a recentering `ψ = z − c̃` (`Node.hspecRecCenter`) and no corpus law pins `c̃ ≠ 0` |
| `hRmul`     | SUPPLIED | `Stage.hRmul` at the parent `ν.σ` |
| `hRlt`      | SUPPLIED | `Stage.hRlt` at the parent |
| `hRadd`     | SUPPLIED | `Stage.hRadd` at the parent |
| `hRΦ`       | SUPPLIED | `Stage.hRΦ` at the parent |

**The `hscale` finding (the blueprint's NAMED RISK, probed).** `hscale` says
`(ν.h : ℤ) = ν.e · σ.w(σ.Φ)` — with `Stage.hwΦ` this is `ν.h = ν.e · ν.σ.h`, a tie
between the READ pair and the FRAME pair. Probe results:
* `Node` carries NO such field (checked against the full `MovesC.Node` field list);
  `Node.hDwidth` ties widths, not slopes.
* `HistoryCoherent` carries the slope law
  `line.slope · (e · strFrame · Dwidth) = h` PER NODE plus the cross-node slope
  monotonicity — a HISTORY-level supplier candidate for `hscale` (read slope vs. the
  frame-creating read's slope), but `graded_read` binds a single node, and deriving
  `hscale` from the history laws is real work (a wave-2a lemma target, NOT assumed).
* `kp_step` precedent: the corpus already displays exactly such pair ties as theorem
  hypotheses (`he : σ'.e = ν.e`, `hh : σ'.h = ν.h`). `hscale` follows that
  discipline: LISTED, NEVER SILENT.
Consequence per §5: wave 2a runs in the "GR-0's residue displayed" mode; the
hardest-hole ranking of §5 stands (the ranking's conditionality clause consulted —
no interface obstruction fired, so no re-adjudication is triggered).

**Non-vacuity of the supplier**: `readHyps_of_node_level` discharges `hscale` at the
level/inert configuration (`e = 1`, `h = σ.h` — the order-1 `nodeLift_key_res`
configuration), so the displayed residue is non-trivially dischargeable on a
recorded corpus configuration.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesGr

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **GR-0, the supplier map compiled** (blueprint §4 `readHyps_of_node`): every
`ReadHyps` field is proved from the recorded wiring EXCEPT the two displayed
residues, which ride as hypotheses (the kp_step displayed-binder precedent; see
the module docstring's table). -/
theorem readHyps_of_node (ν : Node p F)
    (hscale : (ν.h : ℤ) = (ν.e : ℤ) * ν.σ.w ν.σ.Φ)
    (hψ0 : ν.ψ.coeff 0 ≠ 0) :
    ReadHyps ν where
  hscale := hscale
  hbez := ν.hbez
  hbezCanon := ν.hbezCanon
  hψmonic := ν.hψmonic
  hψirr := ν.hψirr
  hψdeg := ν.hψdeg
  hψ0 := hψ0
  hRmul := ν.σ.hRmul
  hRlt := ν.σ.hRlt
  hRadd := ν.σ.hRadd
  hRΦ := ν.σ.hRΦ

/-- **GR-0 non-vacuity leg**: at the level/inert read configuration (`ν.e = 1`,
`ν.h = ν.σ.h` — exactly `nodeLift_key_res`'s order-1 configuration), the `hscale`
residue IS supplied by the corpus wiring (`Stage.hwΦ`), so the displayed pack is
inhabited on recorded configurations with only `hψ0` riding. -/
theorem readHyps_of_node_level (ν : Node p F)
    (hνe : ν.e = 1) (hlevel : ν.h = ν.σ.h)
    (hψ0 : ν.ψ.coeff 0 ≠ 0) :
    ReadHyps ν :=
  readHyps_of_node ν
    (by rw [hνe, ν.σ.hwΦ, hlevel]; push_cast; ring)
    hψ0

end LeanUrat.B2D

#print axioms LeanUrat.B2D.readHyps_of_node
#print axioms LeanUrat.B2D.readHyps_of_node_level
