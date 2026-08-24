# Unit CC07 verdict — chain-carrier node CC-7 (the threshold)

## Verdict: LANDED

One new file, `leanfinal/Uniformity/ChapC/C130th.lean` (imports C130st, the CC-5 layer).
Sorry-free; no new axiom; no `unsafe`; **no numeral and no function of `(W, i, F₀)`** — every
threshold-valued term is a projection of the inherited `thresholdZ`/`thresholdNat` fields of
`NodePointSource` (C130k), exactly per the design §5 ruling ("extra inherited field, with
WINDOW as a source law; not derivable from `(DeepTower,i,F₀)`"), which is quoted in the module
docstring. This is the carrier-level cure of freeze-v2 layer C.130d (BLOCKED at C130A;
`C130d.lean`'s freeze-vocabulary record left untouched).

## Declarations (all in `Uniformity.Density.Tower.NodePointSource`)

Integer/natural threshold dictionary (all consequences of the single `threshold_nonneg`
source field; live-guarded as the source is):

* `thresholdZ_nonneg` — `0 ≤ thresholdZ i` on live stages
* `thresholdZ_eq_natCast` — `thresholdZ i = (thresholdNat i : ℤ)`
* `thresholdNat_eq_toNat` — `thresholdNat i = (thresholdZ i).toNat` (theorem, not a definition)
* `thresholdNat_unique` — the ℕ avatar is the unique natural casting to `thresholdZ i`
* `coe_thresholdNat` — the dictionary in `WithTop ℤ` (the window's value type)
* `window_nat` — EFF.T2.11 `(WINDOW)` respelled at the natural avatar

`CanonicalThresholdAt` (design §5 schematic at the carrier level `(S, i, x, T)`; CC-8's
`RealizedInput` form is the definitional specialization at `(A.node, core.i, X.point)`):

* `CanonicalThresholdAt` — `T = thresholdNat i ∧ (thresholdZ i) < pointHgt i x (keyAt i) ∧ ≠ ⊤`
* `canonicalThresholdAt_def` — `Iff.rfl` anti-drift pin
* `canonicalThresholdAt_thresholdNat` — ★ the producing theorem (projection + dictionary; the
  mathematical content is the `window` source obligation, at a live stage and legal point)
* `CanonicalThresholdAt.eq_thresholdNat` / `.window_lt` / `.window_ne_top` — projections
* `CanonicalThresholdAt.unique` — rigidity
* `not_canonicalThresholdAt_of_ne` — the no-arbitrary-numeral refuter (unguarded)
* `canonicalThresholdAt_iff` — on live+legal domain, canonical ⟺ inherited
* `CanonicalThresholdAt.natCast_lt` — the ℕ-cast window bound for CC-8's block binding

Teeth against the tower (window + `key_value` + `point_exists`, all carried source laws):

* `thresholdZ_lt_u_succ` — gauge-live stages force `thresholdZ i < u_(i+1)` (point-free)
* `thresholdNat_lt_u_succ` — the ℕ spelling

## Verification

Run from `leanfinal/` (module target `Uniformity.ChapC.C130st` must be built; it is):

```text
lake env lean Uniformity/ChapC/C130th.lean
```

Exit 0, zero errors/warnings. `#print axioms` for all 18 new declarations prints exactly
`[propext, Classical.choice, Quot.sound]` (Lean core only).
