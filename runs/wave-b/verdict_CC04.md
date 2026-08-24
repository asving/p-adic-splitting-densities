# Unit CC04 verdict — chain-carrier node CC-4, the Laurent normalizer solve

## Verdict

Overall: **SUPPLY + one STOP-THE-LINE finding** (exact height proved for ALL `k : ℤ`, no
`sorry`; the literal `C130k.LaurentNormalizer` instantiation is BLOCKED on a one-token
C.130f repair that this unit was not authorized to make — C.130f/C.130k are read-only).

| CC-4 clause | verdict | result |
|---|---|---|
| integer exponents by Bézout/rung recursion | **LANDED** | `DeepTower.laurentSolve` / `laurentNormAt`: C.83's ladder recursion over `ℤ`, same canonical `towerSolve`/`slotIdx` representative per rung, exact integer descent (the general-depth form of D62w's `deep3Section`). `n(0) = 1` proved. |
| exact height for ALL `k : ℤ` | **LANDED** | `laurentNormAt_exact_height`: at every stage-live level, `levelExponentHeightHat T i (laurentNormAt i k) = ofAdd k` for every `k : ℤ`. Bézout via `towerSolve_spec` (C.16's argument generalized to any coprime rung, H.51 `class_sep_bij`); rung peel `heightAux_snoc`; coprimality from C.83 `hcop` + frame `F.hcop`. |
| guarded `towerNorm` compatibility | **LANDED** | `NoTrunc` (the hereditary nontruncation domain C130B names) + `laurentSolve_eq_towerNorm`: THERE the Laurent solve IS C.83's word verbatim (no coprimality consumed); corollaries `towerNormLattice_eq_laurentNormAt`, `towerNormLattice_exact_heightHat` (retro-validation of C.83 on its honest domain). C130B's `(u₂,e₂,k)=(5,2,1)` site shown excluded by the guard (`example`). |
| the literal `LaurentNormalizer T` field | **BLOCKED on C.130f repair** | see the finding; constructor packaged as `laurentNormalizerOfAgree` behind the named agreement hypothesis, which becomes `fun _ _ _ => rfl` after the repair. |

## ⚠ STOP-THE-LINE FINDING (machine-checked)

**The landed `levelExponentHeight` (C.130f) has a mis-transcribed Φ-weight denominator:**
`T.e (a.1 + 2)` where the corpus pattern is `T.ehat (a.1 + 2)`.

* Evidence 1 — C.130f's own docstring states `(ê_j/ê_(a+2))u_(a+2)`.
* Evidence 2 — D62w's landed regressed lattices: depth-3 weights on `(π,x,Φ₁,Φ₂)` are
  `(8,4,10,21)` = `(ê₃, (ê₃/ê₁)u₁, (ê₃/ê₂)u₂, (ê₃/ê₃)u₃)`; the landed denominator gives
  `Φ₁ ↦ (ê₃/e₂)u₂ = 20 ≠ 10`. GENTOW5.21 rows force the same (`n̂₂(21)=2⁴Φ′: 16+5=21`).
* Evidence 3 — **formal refuter, landed in this file**:
  `isEmpty_laurentNormalizer_of_two_dvd : 2 ≤ r → 2 ∣ e₁ → 2 ∣ e₂ → IsEmpty (LaurentNormalizer T)`
  — under the landed weights, ALL level-2 weights are even, so `exact_height` can never hit
  `ofAdd 1`. Every S2/S4 witness chain (`e = 2` at all rungs — the intended first instance,
  CC-17) qualifies, so **no unit can ever build the landed `LaurentNormalizer` for the S2
  carrier as the structure now stands.**

**Repair (orchestrator decision):** one token in C.130f `levelExponentHeight`
(`T.e (a.1 + 2)` → `T.ehat (a.1 + 2)`). Consumers of the landed name: only C130k
(`LaurentNormalizer.exact_height`, `canonicalRead`/`arenaRead` kernels — the kernels of the
buggy height are also the WRONG subgroups, so CC-10/CC-11 would inherit the bug) and C130f
itself. This file's `levelExponentHeightHat` is a byte-mirror with the token fixed; after
the repair, `laurentNormalizerOfAgree T (fun _ _ _ => rfl) : LaurentNormalizer T` lands the
instance for EVERY tower, and `levelExponentHeightHat` can be deleted or kept as an alias.

## File and declarations

New file: `leanfinal/Uniformity/ChapC/C130ln.lean` (nothing else touched; C130a/f/k, C83,
C16, C87 consumed read-only).

Namespace `Uniformity.Density.Tower`: `towerSolve_spec` · `towerSolve_mod` ·
`KeyFrame.slotIdx_eq_towerSolve` · `KeyFrame.slotIdx_mod` · `towerSolve_rung_dvd` ·
`levelExponentHeightHat` · `levelExponentHeightHat_ofAdd` ·
`isEmpty_laurentNormalizer_of_two_dvd`; namespace `…DeepTower`: `ehat_one` ·
`natCast_ehat_div_succ` · `laurentSolve` · `laurentNormAt` · `laurentSolve_zero` ·
`laurentNormAt_zero` · `heightAux` · `heightAux_snoc` · `laurentSolve_exact` ·
`laurentNormAt_exact_height` · `NoTrunc` · `laurentSolve_eq_towerNorm` ·
`towerNormLattice_eq_laurentNormAt` · `towerNormLattice_exact_heightHat` ·
`laurentNormalizerOfAgree`.

Every declaration has a `#print axioms` line; all 23 report Lean core only (`propext`,
`Classical.choice`, `Quot.sound`). No `sorry`, no new axiom, no `unsafe`, no `True`-bodied
interface, no statement weakened.

## Verification

Run from `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C130ln.lean
```

Exit 0 (verified 2026-08-24; output = the 23 axiom-footprint lines, no warnings).
