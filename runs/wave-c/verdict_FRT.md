# UNIT FRT verdict — landing F1.2–F1.8 on the `context_split` export (2026-08-28)

## Re-grounding

`runs/wave-c/verdict_CFS.md` named seven rows (F1.2 `block_complement_notdvd` through
F1.8 `level2_peel`) BLOCKED on the internal split data
`C133mh14.blockFrontier_of_context_of_theoremA`'s proof constructs but `BlockFrontier`
drops at export.  `runs/wave-c/verdict_CSX.md` landed `C134csx.context_split`
(`f = blockFactor L f * g₂ * Wf`, `g₂`/`Wf` monic, `Wf` point-sided at `(L.u, L.ℓ)`,
`g₂`'s residual not `L.r`-divisible at every pin) and predicted F1.2 needed one more
step: the quotient bridge against `f /ₘ blockFactor L f`.

This unit built that bridge and attempted each of the seven rows against it.  New file:
`leanfinal/Uniformity/ChapC/C134frt.lean` (imports `C134cfs`, `C134csx`, `C131aa`, `C28`,
`C60`, `C130s6`).  Verified: `timeout 580 lake env lean Uniformity/ChapC/C134frt.lean`,
exit 0, zero `sorry`.

## Row table — LANDED

| row | what landed | route | footprint |
|---|---|---|---|
| (bridge) | `context_split_quotient` — `f /ₘ blockFactor L f = g₂ * Wf`, carrying `context_split`'s `g₂`/`Wf` clauses verbatim | monic-division exactness (`Polynomial.div_modByMonic_unique`) against `context_split`'s product equation, since `blockFactor L f` is monic (`C134cfs.hasLabel_blockFactor`) | core + `exists_dvDissection` |
| F1.2 clause 1 | `testKey_dvd_iff_dvd_blockFactor` — `Ψ ∣ blockFactor L f ↔ Ψ ∣ f` for any test key `Ψ` | **bypasses `context_split` entirely.** (→) is `blockFactor_dvd` (F1.1); (←) is `blockFactor L f`'s OWN maximality clause (`C133mh15.blockFrontier_of_context`'s `hmax`), fed a test-key-is-a-labelled-block certificate (`hasLabel_of_isTestKey`, `keyDeg₁_dvd_natDegree_of_isTestKey` — new: `IsTestKey L Ψ ⟹ HasLabel L Ψ` with witness multiplicity 1, via `C131aa`'s `isTestKey_isDvPure` + `dvResPoly_testKey`) | core + `exists_dvDissection` |
| F1.2 clause 3 | `quotient_dvSupp_ne_top` — `dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ ≠ ⊤` | `dvSupp` of ANY nonzero polynomial is finite (`C130s6.dvSupp_ne_top_of_ne_zero`, no purity needed), applied to `g₂ * Wf ≠ 0` via the bridge | core + `exists_dvDissection` |

**Consistency note:** clause 1's route needs neither `context_split` nor any product
law — it was reachable the whole time, independent of tonight's `context_split` landing.
It is recorded here because the CFS/CSX sweep filed it under the same signed name.

## Row table — BLOCKED-BECAUSE (exact missing premise; not forced)

None of the seven signed names is declared as a `theorem`, `axiom`, or `sorry` — per the
C.33/C.34/C.40 convention, a signed statement is either proved in full or left to the
leanspec stub.  Full accounting in `C134frt.lean`'s own BLOCKED-BECAUSE section; summary:

| row | missing premise (exact) |
|---|---|
| F1.2 clause 2 (hence `block_complement_notdvd` as a whole) | `¬ L.r ∣ dvResPoly F H₀ hpin (g₂ * Wf) L.u L.ℓ …` — transporting `g₂`'s non-divisibility THROUGH multiplication by `Wf`. The only landed product laws (`fgmn_dv_exact_mul`, `fgmn_residual_mul`) demand BOTH factors `IsDvPure` with `D′ ∣ deg` and positive degree; `Wf` is merely point-sided (`context_split` exports no purity/degree data for it). The general (non-purity) law `C130nv2.dvSupp_add_le_dvSupp_mul` only bounds `dvSupp` from below; the exact form `dvSupp_mul_eq_add_of_endpoint_le` needs an "endpoint height" hypothesis `hup` that module's own header says is not unconditionally available outside the S2 numeric instantiation |
| F1.3 `dv2Supp_translation` | F1.2 in full (blocked) + the level-TWO analogue of the same missing transport (`dv2Pin_mul_complement`, the corpus's own still-open no-interaction lemma, plan sizing 70-120 lines; `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md`'s NV-1–NV-4 chain is the in-progress infrastructure) |
| F1.4 `dv2ResPoly_scalar` | F1.3 (blocked) — same translated pin |
| F1.5 `dv2ResPoly_radical_eq` | F1.4 (blocked) |
| F1.6 `mult₂_readable` | F1.3 (blocked) |
| F1.7 `dv2_length_sum` | F1.6 (blocked) |
| F1.8 `level2_peel` | unchanged from `C40.lean` (2026-08-20), re-verified today: clause (ii) needs C.61's `tier1_typeOf` at GENERAL `L.ℓ` (`C61.lean` still only proves `ℓ = 1`); clause (iii) sits on leanspec defect D13 (`C35b.lean`'s `hasLabel_natDegree_dvd_false` machine-refutes the settling question). Orthogonal to `context_split`'s export — the split data was never this row's blocker |

**Recommended next decomposer:** the level-one "point-sided complement" product law
(F1.2 clause 2's exact gap) is now the single node that would unlock F1.2 in full and
re-open F1.3–F1.7's chain — narrower than the general NV-2–NV-4 program, since it only
needs one factor point-sided rather than the fully general two-arbitrary-polynomial
case. F1.8 is independent (needs C.61 at general `ℓ`; unrelated node).

## Out of scope / no action

Chapters A/B/D/E/G, the budget-box frontier family (`towerLocus_fibration_of_frontier`),
and the leaky-selector refutation records — untouched, as in CFS.

## Verification record

```
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C134frt.lean
# exit 0
```

Per-decl footprints (AxCheck footer): `context_split_quotient`, `testKey_dvd_iff_dvd_blockFactor`,
`quotient_dvSupp_ne_top` — `[propext, Classical.choice, Quot.sound, exists_dvDissection]`;
`hasLabel_of_isTestKey`, `keyDeg₁_dvd_natDegree_of_isTestKey` — Lean core only
(`[propext, Classical.choice, Quot.sound]`). Zero `sorry`; no landed file edited; no new
axiom.
