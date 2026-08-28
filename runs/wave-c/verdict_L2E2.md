# Verdict L2E2 — corrected shapes and shared level-2 engine L2E-06--08

Date: 2026-08-28

Target: `leanfinal/Uniformity/ChapC/C136l2e2.lean`

Status: **LANDED**.  The file is frame-generic, contains no S2-special numeral in any
public declaration, and verifies with Lean core only.  No landed or leanspec file was
edited; `I10DeepExport.lean` and `scratch/G5F_probe.lean` were not touched; no git
operation was run.

## Binding L2E1 correction incorporated

The 2026-08-28 correction is explicit in the new file:

* `C136l2e2.Dv2SlotCarryLawStatement` supersedes
  `C136l2e0.Dv2SlotCarryLawStatement`.  Its conclusion is the clean normalized law
  `dv2Res L (A * B) = dv2Res L A * dv2Res L B` for nonzero factors, with no root factor
  and no artificial carry premise.
* `dv2SlotCarryLaw` proves that corrected statement directly from
  `C136l2e1.dv2Res_mul`, the residual foundation identified by L2E1.
* `Dv2FullReadCarryLawStatement` records the separate absolute-read shape.  Only
  `dv2FullRead` carries `AdjoinRoot.root L.r ^ δ`; the dated docstring expressly
  supersedes `C136l2e0.Dv2TwistProductLawStatement` as a normalized-`dv2Res` shape.

Thus no downstream theorem in this file assumes or recreates the rejected normalized
root twist.

## Per-node status

| node | status | landed result |
|---|---|---|
| Corrected L2E-00 | **LANDED** | `Dv2SlotCarryLawStatement`, `Dv2FullReadCarryLawStatement`, and theorem `dv2SlotCarryLaw`; normalized products are clean, absolute full reads own the carry. |
| L2E-06 | **LANDED** | `dv2Supp_mul` proves `dv2Supp (g*z) = dv2Supp g + dv2Supp z` for arbitrary nonzero factors under the generic `Dv2ResSurv` interface.  Nonzero factors supply the side-set and finite endpoint packages internally, so this subsumes `C132nv2.dv2Supp_mul_eq_add_of_endpoint_le`'s conditional endpoint path. |
| L2E-07, strict engine | **LANDED** | `dv2Line_succ_le_of_no_pair` lifts the C133mh3 strict no-pair convolution contradiction to `dv2Pin`; `dv2Pin_mul_pair` gives exact height at a convolution-unique on-side pair. |
| L2E-07, minimum | **LANDED** | `dv2SideMin_mul` combines C132's forward bound with the missing reverse inequality: a product minimum strictly left of the sum admits no on-side pair, hence prices strictly above its own support line, contradiction.  This is the F13A reverse-inequality gap. |
| L2E-07, maximum | **LANDED** | `dv2SideMax_mul` proves the factor-maxima pair survives, then excludes a larger product maximum by the same strict no-pair contradiction. |
| L2E-07, degree | **LANDED** | A private level-2 congruence/span bank proves exact `ℓ₂`-divisibility of every side span; `dv2SideDeg_mul` follows from the exact min/max equalities and cancellation by `0 < ℓ₂`. |
| L2E-08 | **LANDED** | `dv2Pin_dv2SideMin_mul` proves finite pin heights add at the exact product side minimum. `dv2Pin_dv2SideMin_mul_with_carry` pairs it with `L.ℓ * L.cocycle Mg Mz = L.shift Mg + L.shift Mz - L.shift (Mg + Mz)`, recording exact absolute-read carry accounting without inserting it into normalized `dv2Res`. |

## Increment and repair record

The required command was run on the initial skeleton and after each landed increment.
All mathematical increments eventually reached exit status `0`.

The strict-no-pair/minimum increment required three local repair passes before its clean
verification.  The observed failures were recorded exactly:

1. Parser failures from accidental Unicode lambda arrows (`unexpected token '⇒'; expected
   '↦', '=>'`).
2. The duplicate signed/C132 endpoint definitions exposed a dependent rewrite mismatch;
   the failing product-minimum expression used
   `C132nv2.dv2SideMin ... hngz` while the target occurrence printed
   `dv2SideMin ... hngz`.  The proof was repaired by an explicit `change` and an equality
   transitivity step rather than rewriting through a dependent endpoint proof.
3. The last parser failure was `unexpected token 'at'; expected ')', ',' or ':'` in that
   explicit cast.  Correcting the parenthesized `ℕ`-to-`ℕ∞` cast closed the increment.

No failing subgoal remains.  In particular, the formerly missing reverse inequality is
proved, not recorded as an open.

## Verification

Required command:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136l2e2.lean
```

Final exit status: `0`.

Final AxCheck output:

```text
'Uniformity.Density.Tower.C136l2e2.Dv2SlotCarryLawStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e2.Dv2FullReadCarryLawStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C136l2e2.dv2SlotCarryLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e2.dv2Supp_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e2.dv2Line_succ_le_of_no_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C136l2e2.dv2SideMin_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e2.dv2Pin_mul_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e2.dv2SideMax_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e2.dv2SideDeg_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e2.dv2Pin_dv2SideMin_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C136l2e2.dv2Pin_dv2SideMin_mul_with_carry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

There is no `sorry`, new axiom, or dissection-axiom footprint.
