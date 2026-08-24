# Unit C130B verdict — tower-instantiation freeze v2, layer C.130f

## Verdict

Overall: **SUPPLY / BLOCKED**.

| part | verdict | result |
|---|---|---|
| `LevelExponentLattice` | **LANDED** | Laurent exponent vectors on `(π,x,Φ₁,…,Φ_(j-1))`. |
| synchronized `GaugeLattice0` | **LANDED** | Product over the finite live gauge levels `1 ≤ j < r`. |
| `GaugeLattice.{uG}` export | **LANDED** | Explicit `ULift.{uG}` plus `gaugeLatticeEquiv := MulEquiv.ulift`. |
| `levelExponentHeight`, `levelHeight0`, `levelHeight` | **LANDED** | The source coefficient pattern and live projection family. |
| `levelNorm`, `normSection0`, `normSection` | **SUPPLY** | Literal C.83 `towerNorm` on nonnegative inputs, inverse Laurent word on negative inputs, synchronized componentwise, with `n(0)=1` proved. |
| all-integer exact-height law | **BLOCKED** | The freeze requires `levelHeight j (N.n k) = ofAdd k` for every `k : ℤ`, but C.83 supplies only `towerNorm : ℕ → ℕ → ℕ × ℕ × (Fin i → ℕ)` with truncated subtraction. At `(e₂,u₂,k)=(2,5,1)`, its top solve selects exponent `b=1` and truncates `(1-5)/2` to `0`, so the represented word has height `5`, not `1`. |

The exact missing carrier is an integer/Laurent general-depth normalizer, for example a
`DeepTower.towerNormLaurent : (i : ℕ) → ℤ → ℤ × ℤ × (Fin i → ℤ)`, together with its
range-guarded exact weighted-height theorem and an adjudicated compatibility theorem with
C.83's `towerNorm` only on the domain where its natural subtractions are nontruncated.  The
freeze's current demand that C.83 `towerNorm` itself be the nonnegative part at every
nonnegative height is false and cannot be transcribed without changing that requirement.

No exact-height theorem, `GaugeArena`, or mathematical interface containing that conclusion
was declared.  In particular, `NormSection` is used with its actual D.01 contract (`n_zero`
only), not strengthened by an unproved field.

## File and declarations

New file: `leanfinal/Uniformity/ChapC/C130f.lean`.

Declarations:

1. `Uniformity.Density.Tower.LiveLevel`
2. `Uniformity.Density.Tower.LevelExponentLattice`
3. `Uniformity.Density.Tower.GaugeLattice0`
4. `Uniformity.Density.Tower.GaugeLattice`
5. `Uniformity.Density.Tower.gaugeLatticeEquiv`
6. `Uniformity.Density.Tower.levelExponentHeight`
7. `Uniformity.Density.Tower.levelHeight0`
8. `Uniformity.Density.Tower.levelHeight`
9. `Uniformity.Density.Tower.towerNormLattice`
10. `Uniformity.Density.Tower.levelNorm`
11. `Uniformity.Density.Tower.towerSolve_zero`
12. `Uniformity.Density.Tower.KeyFrame.slotIdx_zero`
13. `Uniformity.Density.Tower.towerNorm_zero`
14. `Uniformity.Density.Tower.normSection0`
15. `Uniformity.Density.Tower.normSection`

Every declaration has a `#print axioms` line.  The reported footprint is Lean core only
(`propext`, `Classical.choice`, and/or `Quot.sound` as inherited); there is no `sorry`, new
axiom, `unsafe`, or `True`-bodied interface.

## Verification

Run from `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C130f.lean
```

Exit 0.
