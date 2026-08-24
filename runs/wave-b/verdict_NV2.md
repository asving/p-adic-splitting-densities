# Verdict — unit NV2: S2-source plan node NV-2 (CORE 1/4 of the level-two product law)

Date: 2026-08-24 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §4, §6 row NV-2.
File created (the ONLY file touched): `leanfinal/Uniformity/ChapC/C130nv2.lean` (971 lines;
not added to any roll-up, per the NV01 precedent).

## The minimizer choice (design decision, recorded in the module docstring)

The minimizing outer-development slot of `A` is **C.07's landed `dvSideMin` — the LEFTMOST
slot attaining the `(u,ℓ)`-weighted minimum with finite height** (`Finset.min'` of
`dvSideSet`); ties resolve LEFT.  Chosen because it serves NV-3/NV-4: left endpoints add
under products (B39a's `sideMin` precedent one level up), everything strictly left is
strictly off-minimum (`not_dvOnSide_of_lt_dvSideMin`), and an on-side decomposition of
`jg + jz` is forced to `(jg, jz)` (`dvOnSide_endpoint_unique` — NV-3's "unique lowest
convolution term").

## LANDED (39 declarations, all in namespace `…Tower.C130nv2`)

* **Reads/strictness at the chosen minimizers**: public `dvSideSet` membership projections,
  `dvOnSide_dvSideMin`, `exists_dvSideMin_height`, `dvSupp_eq_of_dvOnSide` (weight identity,
  ℕ-cleared), `le_dvWeight`/`lt_dvWeight` (level-two `le/lt_weight_gen`).
* **Level-one engine at the frame**: `stageHeight_mul` (universal `dv(A·B)=dv(A)+dv(B)`,
  NV-1's `suppVal_mul_univ` at the frame side) + finite-sum ultrametric
  `le_weight_stageHeight_sum`.
* ★ **One-step MacLane expansion, EXACT** (`stageHeight_le_modByMonic`,
  `stageHeight_le_divByMonic`, `stageHeight_eq_min_mod_div`):
  `dv(w) = min(dv(w %ₘ Φ′), dv(w /ₘ Φ′) + dv(Φ′))` for ALL `w`.  The new mathematical core:
  non-cancellation is witnessed at the RIGHT endpoint of `q·Φ′`'s side (B39a
  `sideMin/sideDeg_mul_gen` + B.20 `sideMax_eq` + the frame key's purity `hpure.2`), an
  abscissa `≥ deg Φ′` the remainder cannot reach.  This is the carry compensation.
* ★ **Convolution term estimates, BOTH directions** (the row's charge):
  `stageHeight_dev_mul_eq` — the endpoint term's value is EXACTLY `Hg + Hz` (both
  directions at once, level-one product law); `le_line_dev_term` — every term of the outer
  convolution weighs `≥ Sg + Sz` at every slot, carries included, under admissibility
  `ℓ·dv(Φ′) ≤ u`; `lt_line_dev_term` — every non-(exact-slot, both-on-side) term weighs
  `≥ Sg + Sz + 1` under STRICT admissibility; `succ_le_of_weight_succ_le` extraction helper.
* ★ **Endpoint theorem**: `dvSupp_add_le_dvSupp_mul` — the FULL `≥` direction of NV-4
  (`dvSupp g + dvSupp z ≤ dvSupp (g·z)`, universal, all zero cases; the level-two B.33) —
  and the assembly bank `dvSupp_mul_of_endpoint_le` / `dvOnSide_mul_endpoint`
  (the sum of chosen minimizers IS a product minimizer) / `dvSideMin_mul_le` (bounded by) /
  `dvSupp_mul_eq_add_of_endpoint_le` (the NV-4 shape), all conditional on the ONE input
  NV-3 owes: `hup : dv(dev (g·z) (jg+jz)) ≤ Hg + Hz` (survival vs. residual cancellation).
* **S2 discharge + teeth**: `s2_h_pos`, `s2_stageHeight_key` (`dv(Φ′) = 2`, so admissibility
  is `4 ≤ 5`, STRICT), `s2_dvSupp_mul_ge`, `s2Hgt₂_mul_ge` (carrier form), `s2_dvSupp_X`/
  `s2_dvSupp_key` (ℕ∞ read-backs of landed values), and the end-to-end regression teeth
  `s2_dvSupp_X_mul_key` / `s2Hgt₂_X_mul_key`: **h₂(x·Φ′) = 7 = 2 + 5** — a NEW table value
  produced by the NV-2 machinery alone (`≥` by the universal product inequality, `≤` by the
  endpoint slot's weight), matching hand computation.

## What NV-3 consumes (exit surface, no restating needed)

At S2: reads at `dvSideMin`, `dvOnSide_endpoint_unique` + `not_dvOnSide_of_lt_dvSideMin`
(uniqueness of the lowest term), `stageHeight_dev_mul_eq` (exact surviving-term value),
`lt_line_dev_term` + `succ_le_of_weight_succ_le` (strictness of every other term),
`stageHeight_eq_min_mod_div` (the mod/div split for the cancellation analysis), then fire
`dvSupp_mul_eq_add_of_endpoint_le` with the proved `hup`.  NV-3's own core is exactly the
residual non-vanishing `dv(dev (g·z)(jg+jz)) ≤ Hg+Hz` (FGMN `ψ ∤ R(a)R(b)` by degrees).

## Not claimed (honesty)

No unconditional level-two product law (NV-3/NV-4); no degenerate frames (`0 < F.h`
required, per C130nv's scope note); admissibility `ℓ·dv(Φ′) ≤ u` is a hypothesis generically
and DISCHARGED at S2; no node-source fields touched.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C130nv2.lean` — CLEAN (exit 0, 0 errors,
0 warnings, 0 sorry); 39 `#print axioms` rows, ALL `[propext, Classical.choice, Quot.sound]`
(machine-checked by script over the joined output).  Import closure prebuilt
(`lake build … B39a B43 C34 C127 C131y C130nv`, 8736 jobs, success).  No git commit (per
brief); only file touched is `C130nv2.lean` (+ this verdict).
