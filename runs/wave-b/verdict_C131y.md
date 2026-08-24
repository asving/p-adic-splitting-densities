# Unit C131y verdict

## C.131y′ — LANDED

**C.72's `shadow_faithful_band` is proved** in
`leanfinal/Uniformity/ChapC/C131y.lean` (namespace
`Uniformity.Density.Tower.C131y`).  Its statement is byte-identical to the signed leanspec
twin modulo `axiom → theorem` and namespace qualification.  The file is sorry-free and
uses no new axiom, no `unsafe`, and no exact-multiplicativity cite.

## Axiom footprint of the headline (verbatim)

```text
'Uniformity.Density.Tower.C131y.shadow_faithful_band' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only.  In particular, `fgmn_dv_exact_mul` is not consumed.

## Declarations

The 18 public declarations are:

* height/ultrametric layer: `addVal_neg`, `gaussVal_neg`, `suppVal_neg`,
  `suppVal_add_eq_left_of_lt`, `stageHeight_add_eq_left_of_lt`,
  `dvHgt_add_eq_left_of_lt`, `dvHgt_neg`, `dvHgt_add_min`,
  `dvHgt_eq_top_of_natDegree_lt`, `dvSupp_le_term`, `dvSupp_add_eq_left_of_lt`;
* fixed-height read layer: `slotRes_add_deep`, `twistRead_add_deep`;
* side/residual layer: `dvSideSet_add_deep`,
  `dvSideSet_nonempty_of_dvSupp_eq_coe`, `dvResPoly_add_deep`,
  `dv2Res_add_deep`;
* capstone: ★ `shadow_faithful_band`.

Every public declaration has a `#print axioms` entry in the file footer; every entry prints
`[propext, Classical.choice, Quot.sound]`.

## Proof shape

For `A := dev (composedKey T) f j` and
`B := shadowDev T f j - dev (composedKey T) f j`, C.131w′'s `shadow_floor` and
`hm : m < T.theta μ₂ j` give `m < dv2Hgt B`.  C.131x′'s
`dv2Hgt_add_eq_left_of_lt` therefore gives the exact height of `A + B = shadowDev T f j`.

For residues, `dv2Res_add_deep` proves the uncapped Cnv16 stability theorem directly from
C.22/C.25/C.38a.  Strict depth fixes every weighted coordinate on the finite side, hence the
whole `dvSideSet`; C.08's exact spacing law shows every height queried by `dvResPoly` remains
strictly below the corresponding perturbation digit; `twistRead_add_deep` then fixes every
coefficient.  Finally the proof unfolds C.38a's `dv2Res` choice wrapper and uses pin
uniqueness.  No multiplicative theorem is involved.

## Verification

From `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C131y.lean
```

Exit 0, zero errors, zero warnings.
