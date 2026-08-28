# Verdict — H0LEG: the h = 0 leg LANDED; `fgmn_dv_exact_mul` PROVED IN FULL (Lean core)

**Date:** 2026-08-28
**Unit:** H0LEG (Fable tier)
**Charge:** prove the degenerate `h = 0` leg of the declared cite `fgmn_dv_exact_mul`
(C66b.lean:90), assemble the axiom's statement byte-identically as a theorem (gluing with
C133mh3's `fgmn_dv_exact_mul_thm` at `0 < F.h`), and run the retirement pass.

## RESULT

`leanfinal/Uniformity/ChapC/C133h0leg.lean` (~520 lines): `lake env lean` exit 0, ZERO
errors/warnings/`sorry`; all six printed footprints EXACTLY
`[propext, Classical.choice, Quot.sound]`.  The star:

* **`fgmn_dv_exact_mul_full`** — the axiom's statement **BYTE-IDENTICAL** (verified
  programmatically: unified diff of the axiom's binder+conclusion text vs the theorem's is
  EMPTY modulo the declaration name), no `h` hypothesis, proved by cases
  `F.h = 0` (this unit's leg) vs `0 < F.h` (`C133mh3.fgmn_dv_exact_mul_thm`).  Its
  Lean-core `#print axioms` in the AxCheck footer is the retirement's machine certificate:
  **the declared cite's content is a theorem of Lean core.  The FGMN gate-(b) literature
  import is mathematically redundant.**

## Vacuity check (charge item 2, executed FIRST)

NOT vacuous.  C01 admits `h = 0` explicitly (its `h`-field docstring; C.05 exists for it);
`hcop` forces `e₁ = 1` but neither `hpure` (slope-0 one-sidedness = unit constant term)
nor `hresirr` (irreducible residual read = irreducible reduction) forces `0 < h` — any
lift of an irreducible residue polynomial is an `h = 0` frame, and e.g. `g = key − π^u`
satisfies every premise at `(u, ℓ = 1)`, `u > 0`.  So the leg was proved, not refuted.

## The mechanism (the MH3 verdict's recommendation, executed)

At `h = 0`: `e₁ = 1` (coprimality), `slotIdx ≡ 0`, `twistExp ≡ 0` (twist trivial),
`slotWindow = range f₁`, `H₀ = 0` (pin collapse).  C.05's landed dictionary
(`dvHgt = npHgt F.key`, `dvSupp = suppVal F.key`) extends here to
`dvSideSet = sideSet F.key` under the finiteness guard `suppVal ≠ ⊤` — exactly the guard
C.05's DELTA note mandated (its `f = 0` refutation is the `⊤` case; here monicity supplies
finiteness via B43's `suppVal_ne_top_of_ne_zero`).  New leg-side theorems:

* `isKey_key : F.h = 0 → IsKey F.key` — the C.01-header seam ("IsKey holds exactly at the
  degenerate instance") made a theorem: `frameRes_eq_map` shows the frame residual IS the
  reduced key base-changed along B59a's `resFieldXEquiv`, and irreducibility transports
  back from `hresirr` (helpers `map_symm_map`, `irreducible_of_irreducible_map`).
* `h0Hom : resField F.key →+* F.stageField H₀ hpin` — `AdjoinRoot.lift` over
  `frameRes_eq_map`; `twistRead_eq_h0Hom_resMk` — the ϖ-read at `h = 0` IS B.25's `resMk`
  transported (twist factor `η⁻¹^0 = 1`; slot-window junk tail vanishes coefficientwise);
  `dvResPoly_eq_map_resPoly` — C.25's residual = B.29's residual mapped along `h0Hom`
  (coefficientwise via `coeff_sum_range_C_mul_X_pow`).
* `fgmn_dv_exact_mul_h0` — both conjuncts from the landed order-1 exact chain: purity via
  `sideMin_mul_gen'` + endpoint OnSide computed from `npHgt_top` + `suppVal_mul_gen`
  (the two reads of each factor's support pin `ℓ·H = u·(deg/D′)`); residual law via
  B39a/B43's `resPoly_mul_gen'` pulled through `Polynomial.map` of `h0Hom` (ring-hom
  transport — no injectivity needed).  **`hfloor` degenerates to exactly B39a's `0 < u`**
  — the floor hypothesis is consumed at precisely one point.

## Retirement pass (charge 4) — executed with ONE structural finding

**Finding: the physical removal is an import cycle today.**  The axiom's only proof
consumer is `C131ac.lean:120` (the pow induction feeding
`composedKey_pow_mem_towerLocus`); the import path
`C133mh3 → C133mh1 → C130nv3 → C130nv2 → C130nv → C131ae → C131ac` puts it INSIDE the
retiring theorem's own foundation.  There is NO mathematical circularity — C133mh3's
footprints are Lean-core, machine-checked; only the import graph passes through — but a
textual re-route of C131ac (or an in-place `axiom → theorem` conversion in C66b, whose
proof would need C133mh3) cannot compile.  Executed per charge 4(b)'s third option:

* **(b)** C66b.lean: axiom declaration UNTOUCHED; a dated `[H0LEG 2026-08-28] RETIRED AS A
  THEOREM` block added to the module docstring (what/when/why/where + "no NEW consumer may
  cite this axiom — cite `fgmn_dv_exact_mul_full`").  File re-verified: exit 0.
* **(c)** `docs/AXIOM_FAITHFULNESS.md`: the entry gains the dated RETIRED-AS-THEOREM
  record (provenance analysis retained; the owner's dictionary review noted as no longer
  load-bearing — the statement stands on Lean core).
* **(d)** Consumer re-route: BLOCKED by the cycle above — flagged to the orchestrator.
  Options: snip `C130nv → C131ae` (check how shallow that import is) or re-prove the
  C131a* chain's axiom-carrying decls against `fgmn_dv_exact_mul_full` in a downstream
  file and re-point C123r/C131uf/C131af.  Until then, footprints naming the axiom are
  PROVED REDUNDANT but unchanged.
* **(e)** Census/allowlist tooling: `spec/census_driver.py` + `spec/signed_name_census.py`
  SCAN for `axiom` keywords — no hardcoded allowlist exists in lean-side tooling, and the
  axiom is still (truthfully) declared, so nothing to edit; no C126 census file exists in
  ChapC.  The allowlist COUNT stays at seven until the physical removal; its member 7 is
  now redundant.  `docs/PROJECT_STATE.md` §3 (orchestrator-owned) not touched;
  `docs/LOG.md` + `docs/CITE_REVIEW_LIST.md` row 2 (owner review now de-risked) left for
  the orchestrator's checkpoint, per MH3 precedent.  Roll-up (`Uniformity/ChapC.lean`)
  not wired by this unit — orchestrator's checkpoint, per MH3 precedent.

## Files

* NEW: `leanfinal/Uniformity/ChapC/C133h0leg.lean` (the leg + the full theorem; AxCheck
  footer = the certificate).  Imports: C133mh3, C05, C84d, B39a, B43, B59a.
* EDITED (comment-only): `leanfinal/Uniformity/ChapC/C66b.lean` (docstring retirement
  block; axiom text byte-unchanged) — re-verified exit 0.
* EDITED: `docs/AXIOM_FAITHFULNESS.md` (RETIRED-AS-THEOREM record).
* No other file touched; no git ops (per charge).

## AxChk footer (`lake env lean Uniformity/ChapC/C133h0leg.lean`, exit 0)

```
'Uniformity.Density.Tower.C133h0leg.isKey_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133h0leg.frameRes_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133h0leg.dvSideSet_eq_sideSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133h0leg.dvResPoly_eq_map_resPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133h0leg.fgmn_dv_exact_mul_h0' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C133h0leg.fgmn_dv_exact_mul_full' depends on axioms: [propext, Classical.choice, Quot.sound]
```
