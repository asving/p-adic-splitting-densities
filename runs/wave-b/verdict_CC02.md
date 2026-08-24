# CC-2 verdict (unit CC02) — S2 key bridge

**LANDED.**

New file: `leanfinal/Uniformity/ChapC/C130s2.lean` (namespace
`Uniformity.Density.Tower.C130s2`). Zero `sorry`, zero new axioms, zero `unsafe`;
all 19 declarations print `[propext, Classical.choice, Quot.sound]`. No other file touched.

## Declarations

Tower occurrence (design §6):
- `s2DepthTwo` — `(s2Witness h2 hq 1 (s2Frame_pin h2 hq)).trunc 2 : DeepTower (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 2`
- `s2DepthTwo_eq_trunc` (rfl anti-drift pin), `s2DepthTwo_stage1` (= (2,1,1)), `s2DepthTwo_stage2` (= (2,1,5))

The full `(e,f,u,ψ,step)` bridge to C.80's `s2Tower` (all definitional — same frame, same pin):
- `s2Bridge_e` : `.e 2 = s2Tower.e₂` · `s2Bridge_f` : `.f 2 = s2Tower.f₂` · `s2Bridge_u` : `.u 2 = s2Tower.u₂`
- `s2Bridge_ψ` : `.ψ 1 = s2Tower.ψ₂` (well-typed because `fld 1` IS the stage field; elaborates by `rfl`)
- `s2BridgeStep` : `.fld 2 ≃+* AdjoinRoot s2Tower.ψ₂` — the tower's own `step 1` retyped against ψ₂
  (the retyping compiling is the type-level ψ-bridge); `s2BridgeStep_eq_step` (no new equivalence
  invented, rfl); `s2BridgeStep_canonical` (term = `(quotientSpanXSubCAlgEquiv 1).toRingEquiv.symm`, rfl)
- Bookkeeping: `s2DepthTwo_Dcum_one` (= 2), `s2DepthTwo_Dcum_two` (= 4),
  `s2Bridge_Dcum` (`Dcum 2 = s2Tower.D₂`), `s2Bridge_Econst` (`Econst 2 = s2Tower.E₂`)

The promoted carrier instance (exit condition):
- `s2DepthTwoKeyAt` (+ `_one` = frame key `x²−2`, `_two` = `composedKey (s2Tower h2 hq)`)
- `s2DepthTwoKeyChain : KeyChain (s2DepthTwo h2 hq)` — against the **landed** C.130k `KeyChain`;
  all four fields discharged: `keyAt_one` definitional, `keyAt_monic` via frame `hmonic` /
  C.47 `composedKey_monic`, `keyAt_degree` via frame `hdeg` at `Dcum 1` / C.53b
  `composedKey_natDegree_D₂` through `s2Bridge_Dcum` at `Dcum 2`.
- Teeth: three `example`s — chain degrees 2 and 4, and level-2 degree = `s2Tower.D₂`.

## Honesty scope

Only the `KeyChain` row of design §6's full-instance ledger is closed. Stage tables,
Laurent normalizer, node points, threshold/WINDOW, terminal receiver, FGMN data/laws remain
open obligations of CC-3..CC-15. No `TowerDatum.deepTower` bridge invented; `linTower` untouched.
No read-only input (C130a/C130k, roll-ups, other units' files) modified.

## Verification

```
cd leanfinal
lake env lean Uniformity/ChapC/C130s2.lean   # exit 0; 19 lines, all Lean-core footprints
lake build Uniformity.ChapC.C130s2           # Build completed successfully (8680 jobs)
```
