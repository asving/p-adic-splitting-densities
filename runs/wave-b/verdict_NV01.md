# Verdict — unit NV01: S2-source plan nodes NV-0/NV-1

Date: 2026-08-24 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §3, §5.1, §6 rows
NV-0/NV-1.  File created (the ONLY file touched): `leanfinal/Uniformity/ChapC/C130nv.lean`
(no roll-up edited; not added to `Uniformity/ChapC.lean`).

## NV-0 (polynomial-value shell) — **LANDED**

* `s2Hgt₁` (NEW): the S2 LEVEL-ONE cleared value `toZ ((s2Frame h2 hq).stageHeight A)`,
  with `rfl` anti-drift pins `s2Hgt₁_eq_stageHeight` and `s2Hgt₁_eq_suppVal`
  (= `toZ (suppVal X A 1 2)`, side `(u₁,ℓ₁) = (h,e₁) = (1,2)`).
* Level-one law bank (U12 `PolynomialValuation` shape, minus `map_mul` = NV-1):
  `s2Hgt₁_zero`, `s2Hgt₁_ne_top`, `s2Hgt₁_eq_top_iff`, `s2Hgt₁_ne_top_slot` (exact field
  shape at `Dcum 1`), `s2Hgt₁_add_ge`, `s2Hgt₁_add_eq`; teeth `s2Hgt₁_one` (=0),
  `s2Hgt₁_X` (=1, the cleared `v(x)=1/2`), `s2Hgt₁_C_two` (=2).
* Level-two half: `C130s6.s2Hgt₂` + bank is LANDED and NOT restated (dedup); added only the
  missing shell pieces — `s2Hgt₂_eq_top_iff` (U12 `finite_iff`) and the SHELL TIES
  `dvHgt_eq_stageHeight_dev` (generic `rfl`) / `s2_dvHgt_eq_s2Hgt₁_dev` (S2 `rfl`:
  level-2 slot heights ARE `s2Hgt₁` of the `Φ′`-development coefficients — the display
  NV-2..4 inducts on).
* Generic layer: `toZ_add` (the carrier dictionary is additive) and `suppVal_add_eq`
  (symmetric off-ties equality, both directions of C131ae's `suppVal_add_eq_left_of_lt`).

## NV-1 (level-one universal product) — **LANDED**

* ★ `s2Hgt₁_mul : s2Hgt₁ (A*B) = s2Hgt₁ A + s2Hgt₁ B` for ALL `A B` — all zero cases
  (⊤-absorbing), NO monic/pure/degree fences.  Engine: NEW `suppVal_mul_univ` (universal
  order-one product at any key, any positive coprime side, all zero cases).
* **Which landed lemma actually gives it (the row's charge):** B39a's `suppVal_mul_gen`
  (the general fenced product law), witnesses discharged by B39b `sideSet_nonempty_gen` +
  B43 `suppVal_ne_top_of_ne_zero`/`exists_sideMin_height`, zero cases by B32b
  `suppVal_zero_eq_top`.  `B09.gaussVal_mul` is the order-0 template and is NOT consumed.
* Teeth THROUGH the product law: `s2Hgt₁_X_sq` (=2), `s2Hgt₁_two_X` (=3),
  `s2Hgt₁_zero_mul` (=⊤).

## Not claimed (honesty)

No level-TWO product law (`dvSupp (A*B) 5 2` additivity is CORE NV-2..4); no node-source
inhabitation; no level-one digit/Full tables (NP-1); no localization/`AddValuation`
packaging (NV-5/6); the degenerate side `u = 0` is out of scope.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C130nv.lean` — CLEAN (0 errors, 0 warnings,
0 sorry); 22 `#print axioms` rows, ALL `[propext, Classical.choice, Quot.sound]` (Lean-core
only).  Import closure prebuilt via
`lake build Uniformity.ChapB.B43 Uniformity.ChapB.B39a Uniformity.ChapB.B83Kit
Uniformity.ChapC.C35b Uniformity.ChapC.C130s6 Uniformity.ChapC.C131ae` (completed, 8727
jobs).  No git commit (per brief).
