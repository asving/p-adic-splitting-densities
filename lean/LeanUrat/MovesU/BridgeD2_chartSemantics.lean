/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-D2 — CHART SEMANTICS CHECK (bridge campaign BP1; front-runner ADJ unit)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 / §4
group D (IB-D2).  Charge: check `chartWitness` against `Realizes`'s read
positions — does the model read coefficient i's digits at the slots
`digitIdx i k`? — pin the choice, document against (†3)'s layout.

SEMANTIC READ (verified 2026-07-30 against the as-built MovesT sources):
`MovesT.Realizes (Tm N) χ V` unfolds through `VTree.fiberAt`, whose only direct
box reads are `redPoly χ x = X^n + Σ_b C (x (χ b)) X^b` (MovesT/Defs.lean:198,
the level-0 reduction) and its derived `henPayload χ x`.  So the chart χ tells
the model WHICH digit slots carry the coefficients' LEADING (level-0) digits.
Under (†3)'s slot layout — slot `digitIdx n N i k = i·N + k` carries the k-th
base-p digit of `(f i).val` (`TreePin.boxeq_digits`, DefsLedger.lean:351) — the
digit-0 chart `chartWitness n N hN : i ↦ digitIdx i 0` reads exactly the 0-th
base-p digit of coefficient i, i.e. the mod-p reduction of the coefficient box.
PINNED CHOICE: `bridgeChart := chartWitness` (the digit-0 chart), CONSISTENT
with (†3) — the two sorried pins below are the compiled form of the check.

TRANSCRIPTION RESOLUTION (recorded per the E-phase rules): the pins are stated
PARAMETRICALLY in `(boxeq, hdig)` — any box equivalence satisfying the (†3b)
digit law — because the concrete `boxEquivD` is IB-A11's deliverable (a
different cluster; file BridgeDict.lean does not exist yet).  Instance
discharge at the constructed pin is IB-A11 + IB-D18's duty.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Polynomial

/-- THE PINNED CHART (IB-D2's adjudication output): the digit-0 chart
    i ↦ digitIdx i 0 — `chartWitness`, re-exported under the bridge family's
    name so `TreePin.chart` (IB-D18) wires one designated object. -/
def bridgeChart (n N : ℕ) (hN : 0 < N) : Fin n → Fin (n * N) :=
  chartWitness n N hN

/-- The pinned chart is injective (`TreePin.chart_inj`'s supply), by the built
    `chartWitness_inj`. -/
theorem bridgeChart_inj (n N : ℕ) (hN : 0 < N) :
    Function.Injective (bridgeChart n N hN) :=
  chartWitness_inj n N hN

/-- THE SEMANTIC PIN, slot level: under the (†3b) digit law `hdig` (the
    `boxeq_digits` field, stated parametrically — see header), the digit-box
    value at the pinned chart's slot i IS coefficient i's leading base-p digit,
    i.e. the mod-p reduction of f i.  Proof route: the ℕ-level val identity
    `(f i).val = Σ_k (boxeq f (digitIdx i k)).val · p^k` (the digit values are
    < p, the sum is < p^N, so ZMod-val reads it exactly), then reduce mod p —
    only the k = 0 term survives. -/
theorem bridgeChart_reads_digit0 {p : ℕ} [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (boxeq : Box p n N ≃ MovesD.Box p (n * N))
    (hdig : ∀ (f : Box p n N) (i : Fin n),
      f i = ∑ k : Fin N, ((boxeq f (digitIdx n N i k)).val : ZMod (p ^ N))
        * (p : ZMod (p ^ N)) ^ (k : ℕ))
    (f : Box p n N) (i : Fin n) :
    boxeq f (bridgeChart n N hN i) = ((f i).val : ZMod p) := sorry

/-- THE SEMANTIC PIN, read level (the check the charge asks for, compiled): at
    the pinned chart, the model's level-0 reduction of the digit image of f IS
    the mod-p reduction of the coefficient box's monic polynomial — the model
    reads coefficient i's leading digit at slot `digitIdx i 0`, nothing else.
    Follows from `bridgeChart_reads_digit0` by unfolding `MovesT.redPoly`. -/
theorem redPoly_bridgeChart {p : ℕ} [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (boxeq : Box p n N ≃ MovesD.Box p (n * N))
    (hdig : ∀ (f : Box p n N) (i : Fin n),
      f i = ∑ k : Fin N, ((boxeq f (digitIdx n N i k)).val : ZMod (p ^ N))
        * (p : ZMod (p ^ N)) ^ (k : ℕ))
    (f : Box p n N) :
    MovesT.redPoly (bridgeChart n N hN) (boxeq f)
      = X ^ n + ∑ i : Fin n, C (((f i).val : ZMod p)) * X ^ (i : ℕ) := sorry

end LeanUrat.MovesU
