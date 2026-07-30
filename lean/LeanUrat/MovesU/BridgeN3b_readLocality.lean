/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeD2_chartSemantics
import LeanUrat.MovesT.G1_toyGate

/-!
# SYN-N3b — THE ReadLocality-FROM-SP8 PROBE (bridge campaign, N3 gate class)

Gate-class probe per `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` SYNTHESIS
PASS 1 ("N3 two upside probes ADDED to the gate class: … ReadLocality-provable-
from-SP8-construction (would discharge all three C2 faces)") and
`lean/notes/SYNTHESIS_PASS1_2026-07-30.md` N3/C2.  CHARGE: attempt to PROVE the
C2 unified ReadLocality law (chart_pin + cross-level child locality — the one
owner row unifying `MovesT.treeN_stable`'s `StableInputs` (TV-B2) and
`MovesU.TransferRow` (IB-D5)) from the SP8 `CanTreeModel` construction; on
success the kernel row is discharged entirely.

## PROBE VERDICT (2026-07-30): **STALLED — the row remains a genuine
## hypothesis.  Exact obstruction, three compiled/verified legs:**

**LEG 1 (no construction to prove from — the probe premise is counterfactual
at HEAD).**  The N3 note conjectured "the CANONICAL policy['s] … child
predicate is built from level-N digit reads".  As built: (i) SP8's
`canTreeModel_ofTreeModel` (MovesSp/SP8_instantiation.lean:101) CONSUMES
`T : MovesD.TreeModel` as a BINDER and returns the abstract SP-COMP interface —
it constructs NO tree model (IB-D1's R7 verification, re-confirmed this probe);
(ii) the `CanTreeModel` interface (MovesSp/Defs.lean) carries ONLY
`Branch`/`hTotal`/`len`/`hN1`/`datum`/`hRoot`/`hStage`/`hCoh`/`hHalt`/
`verdict`/`hVerdictPin` — NO child predicate and NO box/digit carrier (the box
enters only as `SpeciesReadout`'s fixed binder x), so the locality law is not
even STATABLE at that interface, let alone provable from it; (iii) the pinned
model `bridgeTm` (BridgeD1_treeModelWire.lean:67) is a SORRIED DESIGNER
OBLIGATION with no defining equations — a current-environment proof of any
locality law at `bridgeTm` could consume nothing beyond its TYPE, i.e. would
have to be TreeModel-interface-generic.

**LEG 2 (interface-generic derivation attempt — REFUTED, compiled below).**
`child_locality_not_interface_derivable`: a `TreeModel` satisfying all five
structure laws whose child predicate reads a beyond-window digit (slot 3 at
the (n, N, N') = (2, 1, 2) instance, window = first n·N = 2 slots).  So the
`TreeModel` laws alone do NOT entail the C2 child-locality face; by LEG 1(iii)
the row is not provable at the opaque `bridgeTm`.  SCOPE FENCE (the M1
soundness rule): this witness negates the INTERFACE-GENERIC universal, which
is stated NOWHERE as a sorried declaration; the landed rows (`StableInputs`,
`TransferRow` — hypothesis structures) and the fenced `MovesT.treeN_stable`
(whose statement is fiber-level and `KBTotTower`-guarded; E11's fence record:
no `KBTotTower` instance exists in-corpus) are NOT refuted, and no compiled
negation of any sorried universal is created here.

**LEG 3 (the one constructed component — a LOAD-BEARING LAYOUT MISMATCH for
the SYN-C2 merge, compiled below).**  The single ReadLocality ingredient that
IS already constructed is the pinned chart `bridgeChart = chartWitness`
(IB-D2).  TV-B2 types the row's chart face as
`chart_pin : ∀ N' ≥ N₀, ∀ b, (χat N' b : ℕ) < n` — the LEVEL-MAJOR "level-1
block" convention (TreeNStable's docstring: "coordinate c at level ⌊c/n⌋ + 1").
The bridge's (†3) layout is COEFFICIENT-MAJOR (`digitIdx i k = i·N + k`), and
`bridgeChart_levelMajor_chart_pin_false` PROVES chart_pin FAILS at the pinned
bridge chart already at (n, N') = (2, 2) — `bridgeChart 2 2 _ 1 = ⟨2, _⟩` and
¬(2 < 2).  Its (†3)-correct replacement is the rfl-display
`bridgeChart_eq_digitIdx0` ("the chart reads exactly coefficient b's digit-0
slot").  CONSEQUENCE FOR SYN-C2: `StableInputs` as typed is UNINSTANTIABLE at
the pinned bridge chart for n ≥ 2 (its chart_pin field is false there), while
`TransferRow` is chart_pin-free and states its locality through the STRUCTURED
box + `boxProj`/`boxeq` (layout-free).  The unified ReadLocality row must NOT
carry TV-B2's `< n` chart_pin form — state the chart face as the digit-slot
pin (`χat N' b = digitIdx n N' b 0`-genre) or keep it layout-free through the
(†3b) digit law, and state child locality through `boxProj` rather than
"first n·N coordinates".

**DISCHARGE PATH (recorded, not attempted here):** the IB-D1 designer round
(R7's re-plan trigger, already scheduled) must build `bridgeTm` with a child
predicate that is a level-cylinder BY CONSTRUCTION; the N3 upside then fires
FROM THE CONSTRUCTION (one proof discharging treeN_stable's inputs +
`StableInputs` + `TransferRow` simultaneously) — deferred to that round, not
dead.  Until then the C2 row is carried as the ONE named hypothesis.

No sorries in this file; both artifacts are Lean-core.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-! ## LEG 2 — the interface countermodel -/

/-- THE COUNTERMODEL (LEG 2): a legal `TreeModel` at (n, N') = (2, 2), working
    level m = n·N' = 4, over the toy policy, whose child predicate reads the
    BEYOND-WINDOW digit slot 3 (the window of the (N, N') = (1, 2) locality
    instance is the first n·N = 2 slots).  All five structure laws hold: `mem`
    is the root-only tree (the root's presence is the law `root_mem`; no
    `some`-chain is ever a member, so `mem_single`/`mem_snoc`/`mem_realizable`
    hold with both sides false/vacuous — `child` at `some`-states is
    UNCONSTRAINED by the interface, which is exactly the point). -/
noncomputable def probeChildModel :
    MovesD.TreeModel 2 (ZMod 2) 2 2 4 MovesT.polTriv where
  mem o _ := o = none
  child o _ x := o ≠ none ∧ x 3 = 1
  root_mem _ := rfl
  mem_single _ _ _ := by simp
  mem_snoc _ _ _ _ := by simp
  mem_realizable _ _ h := absurd h (by simp)

/-- **LEG 2, COMPILED**: the C2 child-locality face (the `child_cyl` /
    `child_local` inner law — agreement on the first n·N digits transfers the
    child relation) is NOT derivable from the `TreeModel` interface laws:
    `probeChildModel` violates it at (n, N, N') = (2, 1, 2).  Hence no
    interface-generic proof exists, and (LEG 1(iii)) no proof at the opaque
    sorried `bridgeTm` exists — the ReadLocality row is a GENUINE hypothesis
    until the designer construction lands. -/
theorem child_locality_not_interface_derivable :
    ¬ ∀ (T : MovesD.TreeModel 2 (ZMod 2) 2 2 4 MovesT.polTriv)
        (o : Option (MovesC.History 2 (ZMod 2))) (ν : MovesC.Node 2 (ZMod 2))
        (x x' : MovesD.Box 2 4),
        (∀ c : Fin 4, (c : ℕ) < 2 * 1 → x c = x' c) →
        (T.child o ν x ↔ T.child o ν x') := by
  intro h
  -- the witness site: a `some`-state (any history literal), any node, and the
  -- two boxes agreeing on the window slots {0, 1} but differing at slot 3
  have hx : probeChildModel.child (some MovesT.tA2a) MovesT.toyLeafA
      (fun c : Fin 4 => if (c : ℕ) = 3 then 1 else 0) :=
    ⟨by simp, by norm_num⟩
  have hagree : ∀ c : Fin 4, (c : ℕ) < 2 * 1 →
      (fun c : Fin 4 => if (c : ℕ) = 3 then (1 : ZMod 2) else 0) c
        = (fun _ : Fin 4 => (0 : ZMod 2)) c := by
    intro c hc
    simp only
    rw [if_neg (by omega)]
  have hbad : probeChildModel.child (some MovesT.tA2a) MovesT.toyLeafA
      (fun _ : Fin 4 => (0 : ZMod 2)) :=
    (h probeChildModel (some MovesT.tA2a) MovesT.toyLeafA _ _ hagree).mp hx
  have hbad' : (some MovesT.tA2a ≠ none) ∧ ((0 : ZMod 2) = 1) := hbad
  exact absurd hbad'.2 (by decide)

/-! ## LEG 3 — the chart-face layout mismatch at the pinned bridge chart -/

/-- **LEG 3, COMPILED (negative half)**: TV-B2's `chart_pin` form
    `(χat N' b : ℕ) < n` — the LEVEL-MAJOR "level-1 block" convention — is
    FALSE at the pinned bridge chart already at (n, N') = (2, 2):
    `bridgeChart 2 2 _ 1` is slot 1·2 + 0 = 2, and ¬(2 < 2).  So
    `StableInputs` AS TYPED is uninstantiable at the bridge's (†3) pins for
    n ≥ 2 — the SYN-C2 unified row must re-key its chart face (header,
    LEG 3). -/
theorem bridgeChart_levelMajor_chart_pin_false :
    ¬ ∀ b : Fin 2, ((bridgeChart 2 2 two_pos b : ℕ) < 2) := by
  intro h
  exact absurd (h 1) (by norm_num [bridgeChart, chartWitness, digitIdx])

/-- **LEG 3 (positive half, the (†3)-correct chart face)**: the pinned chart
    IS the digit-0 slot map — `bridgeChart n N hN b = digitIdx n N b ⟨0, hN⟩`,
    definitionally.  This (or the layout-free (†3b) digit-law route of
    BridgeD2's `bridgeChart_reads_digit0`) is the chart pin the unified
    ReadLocality row can actually carry. -/
theorem bridgeChart_eq_digitIdx0 (n N : ℕ) (hN : 0 < N) (b : Fin n) :
    bridgeChart n N hN b = digitIdx n N b ⟨0, hN⟩ := rfl

end LeanUrat.MovesU
