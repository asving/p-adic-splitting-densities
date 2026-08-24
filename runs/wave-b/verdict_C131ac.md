# VERDICT — unit C131ac (NODE C.131ac′: exact powers + `composedKey_pow_mem_towerLocus`)

**LANDED** (whole node, first compile). File: `leanfinal/Uniformity/ChapC/C131ac.lean`.

## Declarations proved (with per-declaration axiom footprint)

| declaration | what it is | footprint |
|---|---|---|
| `exists_dvHgt_pin` | finite pin exists on any nonempty dv-side (`Finset.min'_mem` + `DvOnSide`'s finiteness conjunct; the C.48/C.118b inline argument, exported) | Lean core only |
| `dvResPoly_eq_of_eq` | witness-independence of `dvResPoly`: equal polynomials give equal residuals at ANY side witnesses/pins (proof irrelevance + `ℕ∞`-pin uniqueness); named to avoid collision with C.118b's different `dvResPoly_congr` | Lean core only |
| `fgmn_dv_exact_pow` | E3 combined: `0 < n` + gate fences + `IsDvPure F g u ℓ` ⟹ `IsDvPure F (g^n) u ℓ` ∧ every residual read of `g^n` = (residual of `g`)^n. Induction on `n`; ONE cite application per step; the name C66b's docstring reserves | Lean core + `fgmn_dv_exact_mul` (EXPECTED — declared cite) |
| `isDvPure_pow` | E3 purity projection | Lean core + `fgmn_dv_exact_mul` (EXPECTED) |
| `dvResPoly_pow_exact` | E3 residual projection (arbitrary witnesses both sides) | Lean core + `fgmn_dv_exact_mul` (EXPECTED) |
| `composedKey_pow_mem_towerLocus` | ★ C.52 Step 1 (`EFF.GENTOW1.20`), at the C52_OPEN-record signature: `composedKey T ^ μ₂ ∈ towerLocus T μ₂` for `0 < μ₂` | Lean core + `fgmn_dv_exact_mul` (EXPECTED) |

Cite-carrying declarations: exactly the four exact-power ones (`fgmn_dv_exact_pow`,
`isDvPure_pow`, `dvResPoly_pow_exact`, `composedKey_pow_mem_towerLocus`); the two
utilities are Lean-core.  No `sorry`, no new axiom, no `unsafe`, no statement touched
elsewhere; no other unit's file modified.

## How the headline discharges `towerLocus`'s four conjuncts

1. Monic: `(composedKey_monic T).pow μ₂` (C.47).
2. Degree `= μ₂ * T.D₂`: `Monic.natDegree_pow` + `composedKey_natDegree` (C.47) + the
   `keyDeg₂ = D₂` dictionary (C.48's landed pattern, re-derived locally).
3. `IsDvPure` of the power: `isTestKey_isDvPure` (C.131aa′) through `fgmn_dv_exact_pow`;
   gate fences at `Φ₂`: `T.hfloor` reassociated, `D′ ∣ D′·e₂·f₂ > 0`.
4. Exact residual `= towerLabel T ^ μ₂`: `dvResPoly_testKey` (C.131ab′) raised through the
   power theorem; base side witness `⟨0, hpure.1⟩`, pin from `exists_dvHgt_pin`.

## Verification command

```sh
cd leanfinal && lake env lean Uniformity/ChapC/C131ac.lean
```

Output: exactly the six `#print axioms` lines above (18 lines), zero warnings/errors.

## Notes for the orchestrator

- C66b's module docstring promises the companion theorem `fgmn_dv_exact_pow` "here" (in
  C66b); it now exists in C131ac.lean instead — a one-word docstring touch-up in C66b is
  optional, not done (C66b is another unit's landed file).
- `composedKey_pow_mem_towerLocus` unblocks the corresponding leg of
  `C52_OPEN_2026-08-18.lean.txt` (Step 1); Steps 0/2/3 remain open on C.131ad′–ag′.
- Imports added: C131aa, C66b, C47, C51 (no roll-up touched).
