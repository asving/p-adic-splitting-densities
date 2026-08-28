# UNIT TSTK — verdict (2026-08-28)

**Scope.** DWC §6.1 tower/key carrier rows T1–T5 (T0 already DONE).  Deliverable:
`leanfinal/Uniformity/ChapC/C136t.lean` — NEW file, namespace
`Uniformity.Density.Tower.C136t`, header `[TSTK 2026-08-28]`.

**Build.** `lake env lean Uniformity/ChapC/C136t.lean` — zero errors, zero warnings,
zero `sorry`.  AxCheck footer: **all 36 printed declarations are exactly
`[propext, Classical.choice, Quot.sound]`** — Lean-core only, no cite inherited (in
particular the μ₃ key-criterion path `C132kp3 → C132kp0/1/2` is cite-free).  No landed or
leanspec file touched; no git ops.  GCW-6 fence respected: everything is DATA
(`DeepTower` / `KeyChain` / exponent + degree pins) — no `RealizedInput`, no socket, no
wired witness.

## Per-row status

| row | status | landed declarations (namespace `…Tower.C136t`) |
|---|---|---|
| **T1** | **LANDED** | `s2DepthThree` (= C97's `s2Witness` at pin `(1, s2Frame_pin)`; anti-drift `s2DepthThree_eq_witness`, `s2DepthThree_trunc_two` = `s2DepthTwo`, both `rfl`) · `s2DepthThreeKeyAt` (levels ≤ 2 DELEGATE to the landed `s2DepthTwoKeyAt`; `keyAt 3 = g8`, pin `s2DepthThreeKeyAt_three`) · degree pins `2/4/8` (`…_natDegree_one/two/three`) · monicity pins (`…_monic_one/two/three`) · `Dcum` pins `2/4/8` |
| **T2** | **LANDED** | `s2Mu3KeyPoly_g8 : S2Mu3KeyPoly h2 hq (g8 h2 hq)` — via `C132kp3.s2Mu3_key_criterion` fed `C132rp10.s2Mu3_gEight_monic/_natDegree`, `C132rp10b.s2Mu3NormRes_g8` (= `X+1`), `C132rp10.s2Mu3_X_add_one_irreducible` · `s2DepthThreeKeyChain : KeyChain (s2DepthThree h2 hq)` — the depth-three chain, all four C130k fields discharged |
| **T3** | **LANDED** | `s2WitnessFour (H₀ hpin) : DeepTower (s2Frame h2 hq) H₀ hpin 4` — stage `(2,1,85)`, `ψ₃ = X − C 1` (`s2WitnessFour_psi_three`), constant residue tower; `s2DepthFour` the pinned occurrence · pins: `s2WitnessFour_floor_four` (**84 < 85** off the datum's own `hfloor`), `s2WitnessFour_Dcum_four` (**Dcum 4 = 16**), `s2WitnessFour_values` (all nine stage numerals), `s2WitnessFour_agrees` (stagewise agreement with `s2Witness` on `1 ≤ i ≤ 3`).  §3.1's conjectural row 4 is now a Lean datum |
| **T4** | **LANDED (pin halves); exact-grade RECORDED-DEFERRED** | `s2DepthThree_towerNorm_two_eighty_five : towerNorm 2 85 = (8, 0, ![0, 1])` · `s2Mu4_chainNormBelow_three_eighty_five : I.chainNormBelow 3 85 = C(2⁸) · keyAt 2` for any `I : FGMNCalculus (s2DepthThree) 2 1 85` with `hkey : I.keyAt = (s2DepthThreeKeyChain).keyAt` (the landed C132rp9 genre) · degree pins `…tooth_natDegree = 4`, `…tooth_degree_lt_key` (4 < 8).  **Deferred per blueprint:** the μ₄ exact-grade-`170` supply waits on the D3 grade bank (D3-05/D3-13); recorded in the module docstring + the numeral tooth `2·1·85 = 170` |
| **T5** | **LANDED (pure exponent + Λ pins); chain-level polynomial pin RECORDED-DEFERRED** | pure exponent theorem `s2WitnessFour_towerNorm_three_one_seventy_one : towerNorm 3 171 = (1, 1, ![1, 1, 1])` (+ `s2DepthFour_…` instance) · `s2Mu5Lambda := C 2 · X · (Φ′ · Φ₂ · g₈)` (§3.3's Λ as a literal polynomial) · `s2Mu5_chainNormBelow_four_one_seventy_one : I.chainNormBelow 4 171 = s2Mu5Lambda` for any `I : FGMNCalculus (s2DepthFour) 1 1 171` with POINTWISE key premises `I.keyAt i = s2DepthThreeKeyAt i` (`i = 1, 2, 3` — `chainNorm 3` multiplies keys 1..3 only, so no `keyAt 4` is needed) · `s2Mu5Lambda_natDegree = 15`, `…_natDegree_lt` (15 < 16), `…_ne_zero`.  **Deferred per the blueprint's intentional two-part note:** the chain-level restatement `hkey : I.keyAt = (depth-four chain).keyAt` waits on D3-19's `keyAt 4 = g16` (no depth-four `KeyChain` exists before the μ₄ normalized-existence leaf); the μ₅ exact-grade-`171` supply waits on D4-03/D4-10 |

## Notes for downstream rows

1. **Kernel trap recorded** (probe `leanfinal/scratch/TSTK_probe.lean`, compiles green):
   a bare `rfl` for `s2DepthThreeKeyAt 2 = s2DepthTwoKeyAt 2` hits a KERNEL
   deterministic timeout — lazy-delta compares the unequal `ite` branches (`g8` vs the
   landed keys) argument-wise through `composedKey`/`Polynomial` internals.  Production
   fix in C136t: `show`-to-the-`ite` + `rw [if_pos …]`.  D3/D4 rows extending key
   functions by `ite` should reuse this pattern for the delegating-level pins.
2. The exponent-pin proof genre (C97's `s2Witness_values` towerNorm leg) scales to
   depth 3 and 4 unchanged: `simp only [DeepTower.towerNorm, <u/e rfl-pins>,
   <towerSolve rfl-pins>]` then `norm_num [<slotIdx pin>, Prod.ext_iff]`, `funext` +
   `fin_cases` for the exponent vector.  `simp only [DeepTower.towerNorm]` DOES unfold
   at the literal depths `2` and `3`.
3. T4's rung arithmetic: `towerSolve 21 2 85 = 1`, remainder 32; `towerSolve 5 2 32 = 0`,
   remainder 16; `slotIdx 16 = 0`, π-exponent 8.  T5's: solves `1,1,1` at
   `(85,171) → 43`, `(21,43) → 11`, `(5,11) → 3`; `slotIdx 3 = 1`, π-exponent 1.  Both
   match `verification/dwc_tower_cert.py` (§3.1/§3.3 rows).
4. The junk convention of `s2DepthThreeKeyAt` is `g8` at every index `> 2` and of
   `s2WitnessFour.u` is `85` at every index `> 3` (nothing reads either; `KeyChain`
   laws are `StageLive`-fenced, tower laws range-fenced).
