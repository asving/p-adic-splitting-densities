# THE 2-NODE GATE (HK-22, pre-wave form) — VERDICT: BLOCKED-FALSE, COMPILED (2026-07-31)

## What this unit was

The convergence unit (`BRIDGE_ADJUDICATIONS_2026-07-30.md`, CONVERGENCE section): FOUR
standing obligations — the HK-22 gate staging the HK-06 wave (queue item 3, task #44),
the U10d `zcStepConfineStmt_false_of_config` instantiation (item 17), the U1_negWitness
honesty perimeter, and the U15 SEED-EXIST wall's first real test — all wanted ONE
artifact: a compiled 2-node `History 2 F4` with root over the base pin `bStageP` and
child riding the forged ramified transition (`MovesD/R7_ramifiedForge.lean`:
`ramifiedStage : Stage 2 F4`, `ramifiedStage_trans : TransitionCoreL bStageP
ramifiedStage U31.fq 2 5 U31.ν₀.zbar`), satisfying the CURRENT (pre-HK-06)
`HistoryCoherent ∧ Realizable ∧ InBox n`.

**The verdict: that artifact does not exist, and its nonexistence is now a theorem.**
New leaf module `lean/LeanUrat/HC2/HK22_twoNodeGate.lean` (0 sorry; per-file gate green
first-pass modulo two name fixes; all five `#print axioms` = Lean core
`{propext, Classical.choice, Quot.sound}`).

## The obstruction (why P1 is impossible, exactly)

The pre-HK-06 `HistoryCoherent` (MovesC/Defs) keys BOTH halves of its i = 0
non-recentering leg at the PARENT node's recorded read pair:
`IsNodeLift (nodes[0]) (nodes[1]).σ.Φ ∧ TransitionCoreL (nodes[0]).σ (nodes[1]).σ
(nodes[1]).σ.Φ (nodes[0]).e (nodes[0]).h (nodes[0]).zbar`.

1. With `(nodes[1]).σ = ramifiedStage`, `TransitionCoreL`'s `child_e`/`child_key` pin
   `(nodes[0]).e = ramifiedStage.e = 2` and `(nodes[1]).σ.Φ = fq = X² + 2X + 4`.
2. `IsNodeLift` at stride `ν.e = 2` demands
   `fq = Φ₀^{2g} + Σ_{k<g} tt_k·Φ₀^{2k}` with `deg tt_k < deg Φ₀ = 1` (coherence
   clause 1 forces the root key monic of degree 1, `Φ₀ = X + C a`) — an EVEN
   polynomial in `Φ₀` with constant coefficients. Evaluating at the two points where
   `Φ₀` takes values `±1` gives `fq(1 − a) = fq(−1 − a)`, i.e. `4(1 − a) = 0`, i.e.
   **`a = 1` is the only surviving key** (`isNodeLift_fq_stride2_forces`).
3. But the same leg's `child_wPrev`, chained with the FORGE's `child_wPrev`
   (`ramifiedStage.wPrev = bStageP.w = bw` pointwise), forces the root frame's
   valuation to be `bw` — and `bw(X + C 1) = 0` (`bw_X_add_C_one`: `θ(X+C 1) = 2X+1`,
   normal 2-exponent 0), violating the root frame's own Stage laws
   `hwΦ : w Φ = h` and `hh : 1 ≤ h`.

So `ramifiedChild_twoNode_incoherent`: ANY `History 2 F4` whose second node's frame is
`ramifiedStage` is incoherent — **the root frame is not even pinned; no root frame
works**. `twoNodeGate_isEmpty` packages the charged conjunction (bStageP root +
ramifiedStage child + `HistoryCoherent ∧ Realizable ∧ InBox n`) as unsatisfiable ∀ n.
`isNodeLift_fq_stride2_false_at_bStageP` is the charge-keyed kernel corollary
(`bStageP.Φ = X ≠ X + C 1`).

## What the verdict MEANS

* **The gate cannot pass before the HK-06 wave, structurally.** The collision is the
  V10/V11 incompatibility class at the gate instance: the PROVED transition engine
  (S9/`TransHyp`) builds the child key at the FRAME pair (`IsStandardLift`, stride
  `σ.e = 1`) with the side `(e′, h′)` free, while the OLD coherence leg re-reads that
  key through `IsNodeLift` at the READ pair (stride `e′ = 2`). At any genuinely
  ramified read over the base pin the two strides differ and coherence is empty. The
  HK-06 (S-a) two-step regrade re-key is hereby NECESSARY (machine-certified), not just
  ratified. Per the Asvin sign-off ("Item 3 executes AFTER the in-flight HK-22 gate
  lands"): this is the gate landing — in its only pre-wave-satisfiable form, the
  compiled emptiness certificate. The wave may now execute; its HK-21/HK-22 staged/
  re-bound instances against the (NEW) clause set are the positive halves.
* **P2 (U10d instantiation): unreachable through this gate — wall now a theorem.**
  `U10dNeg.zcStepConfineStmt_false_of_config` needs a coherent+realizable 2-node
  history with a lawful `PresentSeed`; no such history exists pre-wave with an
  S9-forged ramified child. Queue item 17's exists-config leg stays parked BEHIND the
  wave (its recorded fresh-cut re-scope was itself signed off 2026-07-31, so the
  post-wave instantiation should target the REPAIRED U10d statement).
* **P3 (U1_negWitness perimeter) — NOTE ONLY, no leg attempted:** the perimeter
  (HK-25's recentering-ended variant H₂ʳ) is NOT excluded by this unit's obstruction —
  at i = 0 the root node is species `root`, so the `IsNodeLift ∧ TransitionCoreL` leg
  always fires, but an `e′ = 1` child remains formally open pre-wave — the parity
  kernel is stride-2-specific, and a stride-1 shape exists on paper: root read
  `(e, h) = (1, 2)` with linear `ψ`, `g = 1`, child key `X + C 4`
  (`IsNodeLift` weight `bw(C 4) = 2 = h·(g−0)` checks; the child's `(1,2)`-slot-min
  valuation over `bw` has `w′(X + C 4) = 2 = h′`, consistent with `hwΦ`). Pricing: a
  bStage-scale HAND build of the full child `Stage` (~600 lines) — the S9 route cannot
  produce it (S9's `TransHyp` demands IAug `h′ > e′·w(Φ̂)` while the OLD leg forces the
  transition pair onto the node's recorded pair, which for the frame-pair lift shape
  collapses to `(σ.e, σ.h) = (1, 1)`, refuted by IAug at `w(Φ̂) ≥ 1`). RECOMMENDATION:
  do not spend prover time; the wave lands first.
* **U15 SEED-EXIST**: still untested — its first real test now definitionally waits for
  the post-wave gate instance.

## Perimeter honesty (what is NOT compiled)

* The obstruction is compiled at the charged instance (child = `ramifiedStage`, key
  `fq`, stride 2). Even strides ≥ 4 and odd strides ≥ 3 over degree-1 root keys fail
  similarly (parity resp. degree accounting) but are NOT compiled.
* A pre-wave 2-node history with an `e′ = 1` HAND-BUILT child stage is not excluded
  (see P3 note). No claim is made about histories whose second frame is not
  `ramifiedStage`.

## M1 coexistence audit (clean)

The file proves negations of instance coherence and refutes NO sorried statement. Its
import closure = the forge's 64-module cone + this leaf (TreeCan-free; actual-sorry-free
— all grep hits in the cone are docstring text, and every consumed capstone is
Lean-core). `HK15_gateChildCarrier`'s sorried `gateChildStage` family (item 16,
SUSPECT-FALSE independently) is NOT imported and concerns the child-carrier
construction, not history coherence; `G1_toyGate`'s sorried toy pins are NOT imported
and live at different carriers.

## Verification record

* `lake env lean LeanUrat/HC2/HK22_twoNodeGate.lean` — 0 errors, 0 warnings.
* In-file `#print axioms` on all five public theorems
  (`isNodeLift_fq_stride2_forces`, `isNodeLift_fq_stride2_false_at_bStageP`,
  `bw_X_add_C_one`, `ramifiedChild_twoNode_incoherent`, `twoNodeGate_isEmpty`)
  → `[propext, Classical.choice, Quot.sound]`.
* Statement fence intact: no existing file touched; new leaf module + this note only.
* Deferred to the next manifest sweep: the HC2/MANIFEST.json HK-22 row (same deferral
  class as FORGE-B's).

## Handoff pointers

* HK-06 wave executor: consume `ramifiedChild_twoNode_incoherent` as the pre-gate
  emptiness certificate (the (g3)/HK-21 slot's OLD-leg half); the (NEW)-leg staged
  instance remains to be built WITH the wave (BP2 HK-21/HK-22 unit text).
* The stride-decoupling sentence for the wave's design record: "the recorded lift is
  frame-pair-shaped (D.5 at `σ.e`); the OLD coherence leg re-reads it at the transition
  pair — `isNodeLift_fq_stride2_forces` + `bw_X_add_C_one` is the compiled two-line
  proof that this collision empties the gate."
