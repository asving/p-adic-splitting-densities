# Unit DEC1 verdict — GC-13 partition-record instance bridge, decomposed

**Charge:** convert the GC-13 PARTITION-RECORD INSTANCE BRIDGE (the named blocker for
chapter E's `BlockSplitTarget`/`peel_row_law` and the E.57 endgame) into a
Sonnet-executable node plan. **Deliverables:**
`docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md` + `leanfinal/scratch/DEC1_check.lean`
(+ this verdict). Nothing in `leanspec/`, `leanfinal/Uniformity/`, or any roll-up touched.

## Verdict: PLAN DELIVERED — 7 nodes, 2 concrete rows, signatures elaboration-checked

| piece | verdict |
|---|---|
| Gap analysis (every `PartitionLeg` field vs. its C-record supplier) | DONE — plan §1; suppliers are C.63 clauses, ALL SIGNED-ONLY in leanspec; `hdisj`'s E-side schema supplier (E.36 `coprime_of_not_dvd`) LANDED; no field's supplier MISSING at the shadow-instance level |
| Node plan (E.22/23-genre, concrete rows, 30–45 min each) | DONE — N1–N5 the SPLIT row (`F = X²−1`, two linear classes: the om4 countermodel's interface shape at a LEGAL polynomial), N6–N7 the HI row (`F = X²+X+1`, one degree-2 class: the `hclsHi`/`hpureHi` branch NO landed gate exercises); 3 new files, 3 dispatch waves, dup/pure proofs in E57p.lean named as verbatim templates |
| Assembly node (deliverable 3) | DONE — N5 produces `Nonempty (PartitionLeg mixIface)` and fires `block_split_of_partitionLeg` end-to-end; N7 repeats at the hi row and consumes `dvd_classCount_hi` non-trivially (`2 ∣ 2` from the leg) |
| Elaboration check (deliverable 4) | GREEN — `lake env lean scratch/DEC1_check.lean` exit 0, zero sorry/axiom/unsafe, Lean-core footprints; includes TERM-checks of the two load-bearing joints: `legOfSpecs` (N3+N4 specs = exactly `PartitionLeg`'s constructor — lossless decomposition) and the firing route against the landed theorem |
| Genuinely MISSING objects (honest output, not planned) | NAMED — (i) C.63 `classSize_separable` landed in leanfinal (currently a leanspec axiom only; landing = prove, or cite-axiom behind the owner gate); (ii) the ARENA FUNCTOR `Uniformity.Density.Tower → Uniformity.Density.Ladder` (KeyFrame/LevelDatum row ⇒ SlotCarrier/BlockData/RungInterface + leg) — no blueprint node signs it; E.22/E.23 are declaration-free tables precisely because it does not exist; needs a blueprint amendment before any node plan |

## ⚠ Stop-the-line-grade side finding: leanspec `classSize_supply` (C.69) is refuted-by-instance

`ClassSizeSupplyData.read_form` (leanspec ChapC.lean:2359+, twin at
`leanfinal/Uniformity/ChapC/C140defs.lean:90–93`) quotes the NAKED C.64 law
`BlockContext L f → (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f` with no riders —
exactly the statement `leanfinal/Uniformity/ChapC/C64.lean` `blockDegEq_false`
machine-refutes at `(s2Frame, L₀, g₀)` over `ℤ_[2]` (3 = 2). Hence the leanspec axiom
`classSize_supply : ∀ L, ClassSizeSupplyData L` (ChapC.lean:2387) is FALSE at the probe
frame. A-C.10 (2026-08-24) re-signed the standalone `blockDeg_eq` axiom with the
`hlab`/`hdvd` riders but did not touch C.69's quoting clause — the bundle is out of sync
with its own re-signed supplier. Consequences already folded into the plan: the bridge
cites C.63 clauses only, never `classSize_supply`; a companion re-sign of `read_form`
(thread the A-C.10 riders) is an orchestrator/amendment item. The `mixed_tie` clause is
unaffected (floor conjunct only, TRUE at the probe per C67 `mult₂_g₀`); the landed
structure twin in C140defs is harmless (a `Prop`-former may be uninhabited).

## Verification

`cd leanfinal && lake env lean scratch/DEC1_check.lean` — exit 0;
`#print axioms` on all seven check declarations: at most
`{propext, Classical.choice, Quot.sound}`. Inputs read: E57p.lean (schema + both gates +
correspondence table), verdict_E57.md, leanspec ChapE A-E.7 block (`PartitionLeg` twin +
`BlockSplitTarget`), leanspec ChapC C.61–C.70, C140defs.lean, C61/C64/C67 (+ blocked/refutation
records), HX_SWEEP_2026-08-20.md, E22/E23 instance-record precedents, E36, E11/E12/E13,
verdict_XSC.md E-rows. Not committed (per brief).
