# Unit CC05 verdict — chain-carrier node CC-5 (stage source transcription)

## Verdict

**LANDED.** One new file `leanfinal/Uniformity/ChapC/C130st.lean`: the indexed stage
value/digit/full/lift source interface exported at freeze-v2's layer-C.130c names from the
landed `NodePointSource` (C130k, CC-1), plus the producing theorem `stageCarrier` yielding the
landed E.10 `Ladder.SlotCarrier` (the EXISTING structure, not a clone) from an instance at
every live stage. No `sorry`, no new axiom, no `unsafe`, no new structure, no touched files
outside the deliverable.

## Declarations (all in `Uniformity.Density.Tower`, all Lean-core)

`(DEG-EF)` bookkeeping on C.83's tower (namespace `DeepTower`):

* `fhat` — `f̂_i = f_1⋯f_i`, `ehat`'s residual companion
* `fhat_pos` — positivity on the live range via `W.hf` (mirror of C.87's `ehat_pos`)
* `Dcum_eq_ehat_mul_fhat` — `D_i = ê_i·f̂_i` (`Finset.prod_mul_distrib`; the per-stage
  `(e_j,f_j)` remain C.83 hypothesis fields — no source hypothesis manufactured)
* `Dcum_pos`

Indexed stage interface + producing theorem (namespace `NodePointSource`):

* `stageHgt`, `stageDig`, `StageFull` — the EFF.T2.05/.09 stage tables/predicate at the
  layer-C.130c names (defs = the CC-1 source fields)
* `stageLift` — EFF.T2.09 `(LIFT)` restated on the layer names (full heights only)
* **`stageCarrier`** — the CC-5 producing theorem: `NodePointSource → StageLive r i →
  Ladder.SlotCarrier O (W.fld i)`; `D := Dcum i`, `(eC,fC) := (ê_i, f̂_i)`, `hef` PROVED,
  every law field consumed verbatim from the EFF.T2.04/.05/.09 source fields
* Anti-drift pins (all `rfl`): `stageCarrier_D/eC/fC/hgt/dig/Full` — the carrier's tables ARE
  the source tables; `Full` is `S.Full i`, live and source-bound, not `True`
* Legal-point ties (the C130A "free tables" cure, through the carrier):
  `stageCarrier_hgt_eq_point_read` (carrier height = stage valuation of the actual polynomial
  evaluation at every legal point, slot range), `stageCarrier_dig_eq_point_read`

## Verification

Run from `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C130st.lean
```

Exit 0 (verified 2026-08-24); the 17 `#print axioms` lines each print exactly
`[propext, Classical.choice, Quot.sound]`.

## Notes for the orchestrator

* `DeepTower.fhat` is a new name in the shared `DeepTower` namespace — flagging for the
  in-flight CC03/CC04 units (C130tr/C130ln) in case either wants the same companion product;
  there is exactly one declaration site as of this landing.
* CC-6 (S2 level-2 stage regression) and CC-7 (threshold) consume this file's `stageCarrier`
  and the C130k threshold fields respectively; nothing here inhabits `NodePointSource`.
