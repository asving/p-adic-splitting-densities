# Unit CC10 verdict — chain-carrier node CC-10 (the canonical L-valued read)

## Verdict: **LANDED**

New file: `leanfinal/Uniformity/ChapC/C130cr.lean` (design §4.2 / §8 row C.130h / §10 row
CC-10; freeze-v2 layer C.130h, OM-8 L3 excluded). Zero `sorry`, no new axiom, no `unsafe`, no
`True` body; all 49 `#print axioms` outputs are Lean-core only (`propext`,
`Classical.choice`, `Quot.sound`). No other file touched.

## What was constructed (namespace `Uniformity.Density.Tower`)

**Lattice letters + exact heights** (total in `i`; liveness only where C.87/CC-4 need it):
`levelExponentHeight_ofAdd` (rfl pin) · `piLetter`/`xLetter`/`keyLetter` +
`piLetter_height`/`xLetter_height`/`keyLetter_height` · `levelExponentHeight_mul_ofAdd`.

**Height classes from CC-4's exact normalizer** (`LaurentNormalizer` namespace):
`mul_norm_inv_mem_ker` · `heightClass`/`heightClass_coe` (τ-class `g·n̂_i(k)⁻¹`) ·
`heightClass_norm` · `defect`/`defect_coe` (`n̂(k)n̂(k')n̂(k+k')⁻¹`, a kernel element) ·
`heightClass_mul` (defect-corrected τ-multiplicativity — the general-depth D62w τ reduction).

**Distinguished generators**: `DeepTower.wrapGen`/`wrapGen_mem_ker`/`wrapClass`/`wrapClass_coe`
(W₀ = `x^{e₁}π^{−u₁}`, EFF.T1.01; kernel membership from `ehat_dvd`) ·
`LaurentNormalizer.letterClass`/`letterClass_coe` (Λ_a = `Φ_{a+1}^{e_{a+2}}·n̂_i(·)⁻¹` at its
exact height, DEF GENTOW5-1 S2.1/S2.3(3)) · `generatorWord`/`generatorWord_def`.

**Level-kernel views** (`NodePointSource` namespace): `wrapValue`/`letterValue` (+ `_def`
pins; the η/β exports of the CARRIED `canonicalRead` source field) ·
`canonicalRead_generatorWord` (★ the freeze §4 display `canonicalRes(τ) = η^m·∏β_a^{t_a}`,
L-valued) · `canonicalRead_heightClass_mul`.

**Synchronized-product export**: `kerLevelProj0`/`kerLevelProj0_coe` ·
`mulSingle_mem_ker_levelHeight0` · `kerLevelInsert0`/`kerLevelInsert0_coe` ·
`kerLevelProj0_kerLevelInsert0` · `kerGaugeEquiv` (concrete ↔ ULift kernels, via C130f's
`gaugeLatticeEquiv`, finding #28) · `canonicalRes0`/`canonicalRes0_apply` (★ C.130h concrete)
· `canonicalRes0_eq_one_of_level_one` + `canonicalRes0_insert_ne` (freeze §4's "other level
factors to 1", as THEOREMS) · `canonicalRes0_kerLevelInsert0` · `canonicalRes`/
`canonicalRes_apply`/`canonicalRes_symm_apply` (★ C.130h `Type uG` form) ·
`DeepTower.wrapClassSync` · `LaurentNormalizer.letterClassSync` ·
`canonicalRes0_wrapClassSync`/`canonicalRes0_letterClassSync`/`canonicalRes0_generatorWordSync`
(★ the distinguished-generator views on the synchronized product).

## Teeth (S2 depth-two, statements over ANY carrier instance)

D62w `d2g1`: `wrapGen = (−1, 2, ·)` at both live levels (rfl). D62w `d2g2`: the S2 normalizer
word at height 10 is `π²x` (`laurentSolve 1 10 = (2,1,0)`, equation-lemma unfold + `decide` —
`laurentSolve` is WF-compiled, so no bare-`rfl` defeq route exists), and the GENERAL
`letterClass` at S2 level 2 evaluates to `(−2, −1, 2) = Φ₁²·(π²x)⁻¹`. Plus generator-word and
synchronized-export specializations at the unique S2 live level.

## Honesty / fences (design invariants held)

- No agreement of any form between the canonical read and CC-11's separate read; nothing in
  the file is `Kt`-valued. No OM-8 L3 descent object.
- OPEN and NOT claimed (freeze v2 §4): the triangular-basis spanning/uniqueness bridge (every
  kernel element a generator word), and the C.130g bridge tying `letterValue` to the node
  β-classes. `canonicalRead` itself remains a carried source field; CC-10 exports it.

## Fence grep output

```text
$ rg -n 'arenaRead|GaugeArena|towerRead|peelUnit' leanfinal/Uniformity/ChapC/C130cr.lean
(empty; exit 1)
```

## Verification

From `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C130cr.lean   # exit 0, no warnings, 49 Lean-core axiom prints
lake build Uniformity.ChapC.C130cr           # Build completed successfully (8683 jobs)
```

Not committed (orchestrator commits). Files to stage: `leanfinal/Uniformity/ChapC/C130cr.lean`,
`runs/wave-b/verdict_CC10.md`.
