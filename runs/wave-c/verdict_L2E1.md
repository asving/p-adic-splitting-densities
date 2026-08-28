# Verdict L2E1 — shared level-2 multiplicative engine, nodes L2E-03--05

Date: 2026-08-28

Target: `leanfinal/Uniformity/ChapC/C136l2e1.lean`

The unit was built on `C136l2e0`, `C133mh3` Part 10, and `C134dv2g`.  No landed or
leanspec file was edited, no `C136d*.lean` file was touched, and no git operation was run.
All public declarations are frame-generic and contain no S2-special numeral.

## Per-node status

| node | status | result |
|---|---|---|
| L2E-03 | **LANDED** | `Dv2ResSurvRead` strengthens `Dv2ResSurv` with nonvanishing of `dv2Res L (dev Ψ (A*B) 0)`. `dv2ResSurvRead_of_testKey` proves it from the explicit test-key, μ-key, key-grade, height, degree, and outer-floor fences. The proof uses the landed height equality, the test-key recipe-degree identity, `not_residual_dvd_of_natDegree_lt`, and `AdjoinRoot.mk_eq_zero`. |
| L2E-04 | **RED — proposed twist shape not landed** | `dv2Res_mul` lands the actual normalized coherent-read law on unreduced nonzero products: `dv2Res L (A*B) = dv2Res L A * dv2Res L B`, directly from `C133mh3.dvResPoly_mul_gen`. The private checked diagnostic `root_cocycle_eq_one_of_twist_shape` shows that the L2E-00 twist shape, specialized to a short product where `%ₘ Ψ` is inactive and the two digit reads are nonzero, forces `AdjoinRoot.root L.r ^ L.cocycle ka kb = 1`. No current hypothesis trivializes either the cocycle or this root power. |
| L2E-05 | **LANDED** | `dv2PairLine_le`, `dv2PairLine_lt`, and `dv2Pair_endpoint_unique` port the non-strict pair price, strict off-pair price, and endpoint uniqueness interface to `dv2Pin`. Top pins are handled explicitly; finite pins use `lt_dv2Weight`. |

## L2E-04 exact open

Three routes were checked against the binding shape:

1. The full-read route carries an absolute shift cocycle, but `dv2Res` is the
   side-min-normalized read; the landed inverse twist is precisely what cancels that carry.
2. Applying `AdjoinRoot.mk L.r` to `C133mh3.dvResPoly_mul_gen` gives the compiled theorem
   `dv2Res_mul` with no root factor.
3. On the explicit degree fence `(a*b).natDegree < Ψ.natDegree`, reduction is inactive.
   Combining the requested L2E-00 conclusion with `dv2Res_mul` and L2E-03 nonvanishing
   cancels the nonzero product read and leaves the exact subgoal

```lean
AdjoinRoot.root L.r ^ L.cocycle ka kb = 1
```

That subgoal has no supplier and is not valid for a general nontrivial cocycle/root.  Thus
the public shape must be reviewed: either the conclusion should use the absolute full read
(where the carry belongs), or the normalized `dv2Res` conclusion should omit the root
factor.  Adding more height/degree/outer-floor fences does not supply the missing root-power
identity.

Consequently, L2E-04's named target and any downstream step requiring that exact twist
shape remain open.  L2E-03 and the pair-pricing/endpoint portion of L2E-05 are independently
available.

## Verification

Required command, run after the skeleton and after each landed increment:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136l2e1.lean
```

Final exit status: `0`.

Final AxCheck output:

```text
'Uniformity.Density.Tower.C136l2e1.Dv2ResSurvRead' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e1.dv2ResSurvRead_of_testKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e1.dv2Res_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e1.dv2PairLine_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e1.dv2PairLine_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e1.dv2Pair_endpoint_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only.  No `sorry`, new axiom, or dissection axiom footprint occurs.
