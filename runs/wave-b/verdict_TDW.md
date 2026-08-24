# Unit TDW — `TowerDatum.deepTower` (the §10 preamble constants, constructed)

**VERDICT: LANDED.** New file `leanfinal/Uniformity/ChapC/C84d.lean`; both leanspec §10
preamble axiom constants (`leanspec/Leanspec/ChapC.lean` ~L2420) realized — `deepTower` as a
`noncomputable def`, `deepTower_data` as a `theorem` — signatures byte-matched against the
signed stubs (mechanical diff: identical modulo `axiom` → `noncomputable def`/`theorem`).
The C.100–C.103 GENTOW2 twins are now STATABLE (the C99gt/C102gt/C84:110 blocker removed).

## Declarations (all in `Uniformity.Density.Tower`, all Lean-core footprint)

* `KeyFrame.stageFieldInst` — `Field (F.stageField H₀ hpin)` at ANY frame (from `F.hresirr`;
  C.97's `s2StageFieldInst` generalized), `@[reducible]`.
* `TowerDatum.adjoinPsi₂FieldInst` — `Field (AdjoinRoot T.ψ₂)` (from `T.hψirr`), `@[reducible]`.
* `TowerDatum.deepFld` / `TowerDatum.deepFldField` — the two-rung telescope
  `fld 1 = stageField`, `fld 2 = AdjoinRoot ψ₂` (junk copies off-range) + its `Field` data.
* **`TowerDatum.deepTower`** — the `DeepTower F H₀ hpin 2`: rung 1 = frame `(e₁,f₁,h)`,
  rung 2 = `(e₂,f₂,u₂)`, `ψ 1 = T.ψ₂`, `base = step = RingEquiv.refl` (definitional iterate);
  `hproper`/`hcop`/`hψ` from `T.hcomp`/`T.hcop`/`T.hψ*`; `hfloor` = `T.hfloor` re-associated.
  `hπ` carried unused (signed signature's; C.97's carried-hypothesis precedent, flagged).
* **`TowerDatum.deepTower_data`** — the four signed clauses, `⟨rfl, rfl, rfl, ⟨RingEquiv.refl _⟩⟩`.
* Companions: `deepTower_stage1`, `deepTower_fld_one`, `deepTower_fld_two`,
  `deepTower_psi_one` (the type-level bridge pin, CC-2 style), `deepTower_Dcum`
  (`Dcum 2 = T.D₂`), `deepTower_Econst` (`Econst 2 = T.E₂`).

## Verification

```
cd leanfinal && lake env lean Uniformity/ChapC/C84d.lean     # zero errors/warnings
cd leanfinal && lake build Uniformity.ChapC.C84d              # module build green (8606 jobs)
cd leanfinal && lake env lean scratch/TDW_consumer_smoke.lean # consumer-side statability check
```

`#print axioms` (AxCheck footer, 12 declarations): `[propext, Classical.choice, Quot.sound]`
throughout — no sorry, no new axiom, no unsafe.  Smoke test elaborates the C.100 binder
`ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂`, `towerNorm` at the constructed chain, the
data-clause `E₂` tie, and `trunc`.

## Notes for consumers (GTR/C99r and the C84 reconciliation companion)

`fld 2` is DEFINITIONALLY `AdjoinRoot T.ψ₂` (`deepTower_fld_two : … = … := rfl`) and
`ψ 1 = T.ψ₂` by `rfl`, so the C.100-style arbitrary-ρ hypotheses can be instantiated at
`RingEquiv.refl`.  The rung fields reduce by `rfl` (`e/f/u` are `match`-literals), so
`towerNorm 1` at `T.deepTower hπ` computes with `(u₂, e₂)` without unfolding lemmas.
Trust-boundary flag: the telescope/junk conventions are recorded in the module docstring
(⚠ mandatory-review block).
