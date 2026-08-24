# Unit C131w verdict

## C.131w′ — LANDED

**C.72's `shadow_floor` — the dv-graded engine's headline theorem — is proved**, in the new
file `leanfinal/Uniformity/ChapC/C131w.lean` (909 lines, namespace
`Uniformity.Density.Tower.C131w`), with the signed statement (leanspec `ChapC.lean` NODE
C.72) byte-identical modulo `axiom → theorem` and the qualified
`IsLocalRing.ResidueField` spelling (same type; C72.lean's landed strata use the identical
spelling).  The companion `shadow_floor_statement` discharges C.72's signed statement
carrier `ShadowFloorStatement T hπ μ₂ f j` for every locus member and `j < μ₂` — the
anti-drift pin: the landed conclusion type-checks against the frozen carrier body.

## Axiom footprint of the headline (verbatim)

```text
'Uniformity.Density.Tower.C131w.shadow_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only — **no cite consumed** (no `fgmn_dv_exact_mul`, no `fgmn_residual_mul`).
All 20 new declarations print `[propext, Classical.choice, Quot.sound]`.  Zero `sorry`,
zero new axioms, zero `unsafe`, zero warnings.

## Proof shape (v2 §3.8's Cnv14, with one honest supersession)

Splice: `shadow_discrepancy` (C.131v′) + `dv2Hgt_neg` reduce the goal to
`Θ_j ≤ dv2Hgt (dev Φ₂ (censusOverflow T f) j)`; then three floors chain:

1. `towerLocus_entry_floor` — `hf`'s `IsDvPure` right endpoint gives `dv2Hgt f ≥ μ₂E₂`
   (the FULL-SIDE hypothesis, consumed exactly once, through `μ₁u₂ = μ₂E₂`);
2. `dv2Hgt_censusOverflow_floor` — `dv2Hgt (censusOverflow T f) ≥ μ₂E₂ + δ`: C.131n′'s
   `quotDigit_floor_of_le` ledgers `(μ₂−j′)E₂` onto every census digit (via `K_T_eq_xNF`
   + `devQ_eq_quotDigit`); the paid value is reassembled cleanly from C.131v′'s
   `collapse_unpaid_add_paid`/`collapse_unpaidValue` (no tagged-list work) and priced with
   the extra `δ` by the new **inner paid ledger** `dev_coeff_paid_floor` (F11's
   `paid ≥ 1 ⟹ +δ` invariant: strong induction on inner degree, tail branch =
   `xCarry_tail_floor`, paid branch = the exact `wtCoeff_paid_shift`, i.e. `u₂ = e₂D′h + δ`);
3. `dv2Hgt_dev_floor` — the new **honest-digit ledger** (F6–F8 at the honest key Φ₂):
   `dv2Hgt A ≥ w ⟹ dv2Hgt (dev Φ₂ A i) ≥ w − iE₂`, by strong induction on `natDegree A`,
   peeling the canonical top block against `Φ′^{M−q}·Φ₂` (outer-carry tail priced at `E₂`
   by `K_T_monomial_floor`/`wtCoeff_outer_key_shift`, paid branch =
   `recarry_moves_up_one`), all floors descending through C.131ad′'s `dev_coeff_floor`
   and converting through C.131t′'s `dv2Hgt_eq_WT_phiNF` (Cnv11).

Then `(μ₂E₂ + δ) − jE₂ = (μ₂−j)E₂ + δ = Θ_j` (recarry_cancel arithmetic, `hj : j < μ₂`).

**Supersession note (recorded in the module docstring):** C.131o′'s parameterized
`census_floor`/`PaidFloor` is NOT consumed.  Its instantiation gap — pricing the honest
Φ₂-redevelopment of the erased paid value, where x-overflow recarries across coordinates —
is exactly what the two new strong-induction ledgers close; they subsume the list-level
floor for this node.  The mathematical content (entry ledger + paid-δ + upward recarry) is
v2 §3.8's, unchanged; the signed statement is untouched.

## New declarations (20, all public unless noted)

Glue: `le_WT_of_forall_wtCoeff`, `WT_C_mul_X_pow_eq`, `xNF_add`, `dev_zero'`, `dev_neg`,
`xNF_neg`, `dv2Hgt_add_min`, `dv2Hgt_neg`, `le_dv2Hgt_of_eval` (lift-floor ⟹ height-floor,
the Cnv11∘carry-down workhorse), `K_T_eq_xNF` (+ private `coe_sub_le_of_le_add`,
`paid_floor_small`, `dev2_floor_small`).
Engine: `wtCoeff_paid_shift`, `dev_coeff_paid_floor` (inner paid ledger),
`dv2Hgt_dev_floor` (honest-digit ledger).
Census pricing: `sum_dev_tail`, `paidLift` (def), `eval_paidLift`, `WT_paidLift`,
`dv2Hgt_censusOverflow_floor`.
Locus: `towerLocus_entry_floor`.
Capstones: ★ `shadow_floor`, `shadow_floor_statement`.

## Verification

From `leanfinal/` (dependency oleans C131v/C131n/C131t/C131ad/C72 built first):

```text
lake env lean Uniformity/ChapC/C131w.lean
```

Exit 0, zero errors, zero warnings; every `#print axioms` line in the AxCheck footer is
`[propext, Classical.choice, Quot.sound]`.  `lake build Uniformity.ChapC.C131w` also
green (8665 jobs).
