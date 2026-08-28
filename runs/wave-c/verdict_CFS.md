# UNIT CFS verdict — the C.35 BlockFrontier-family unconditionalization sweep (2026-08-28)

## Re-grounding

The engine `C133mh15.blockFrontier_of_context : BlockContext L f → BlockFrontier L f`
landed tonight (footprint: Lean core + the one allowlisted C.33 dissection cite
`exists_dvDissection`).  `BlockFrontier L f` = existence of a maximal `(λ,r)`-labelled
monic divisor of `f` with the A-C.20 degree pin `D′ ∣ deg`; `BlockContext L f` = the §5
standing context (monic, squarefree, `¬ key ∣ f`, a genuine `(λ,r)`-side with
`r`-divisible residual).  This unit swept the corpus for every row that was BLOCKED on,
CONDITIONAL on, or carrying a `BlockFrontier`/`blockFactor_spec`/`BlockContext`-shaped
demand, and landed the unconditional forms that are genuine projections of the engine's
export.  New file: `leanfinal/Uniformity/ChapC/C134cfs.lean` (single import:
`C133mh15`).  Verified: `timeout 580 lake env lean Uniformity/ChapC/C134cfs.lean`,
exit 0.

## The one binder delta, stated once

Every landed twin carries **`hh : 0 < F.h`** beyond the signed binder lists — the
engine's frame-nondegeneracy entry.  `KeyFrame` formally admits the degenerate `h = 0`
frame (C01.lean:84-86) and `LevelDatum.hκ` (`ℓ·D′·h < u`) is vacuous at `h = 0`, so `hh`
is NOT derivable from the context; the corpus frame has `1 ≤ h` (C01 docstring).  All
other signed binders (`hπ : Irreducible π`, `[IsAdicComplete]`, `hctx : BlockContext`)
match byte-for-byte.

## Row table — LANDED (all in `C134cfs`, namespace `Uniformity.Density.Tower.C134cfs`)

| row | consumer / signed target | what it carried | landed unconditional form | footprint |
|---|---|---|---|---|
| F1.1 | signed `blockFactor_spec` (leanspec ChapC.lean:1608-1613); conditional carrier `blockFactor_spec_of_frontier` (C35.lean:310) | `hfr : BlockFrontier L f` | `C134cfs.blockFactor_spec` — signed four-conjunct conclusion byte-as-is from `hctx` (+`hh`) | core + `exists_dvDissection` |
| F1.1a | clause-1 consumers (rider `hlab`) | rider threading | `C134cfs.hasLabel_blockFactor` | core + `exists_dvDissection` |
| F1.1b | clause-2 consumers | rider threading | `C134cfs.blockFactor_dvd` | core + `exists_dvDissection` |
| F1.1c | re-signed C.64 `blockDeg_eq` (C150rb1.lean:135, riders `hlab`,`hdvd`; = `C64.blockDeg_eq_resigned`); GC13 bridge `read_form` demand (GC13_BRIDGE_PLAN_2026-08-25.md:51) | the `hlab`/`hdvd` riders | `C134cfs.blockDeg_eq` — the RIDER-DISCHARGED degree law `(blockFactor L f).natDegree = keyDeg₂ · mult₂` from `hctx` alone | core + `exists_dvDissection` |
| F1.1d | clause-4 consumers | — | `C134cfs.mult₂_pos` | core + `exists_dvDissection` |
| F1.1e | protected-shape consumers threading the A-C.20 degree pin | the `hdvd` rider | `C134cfs.keyDeg₁_dvd_blockFactor_natDegree` (`D′ ∣ deg blockFactor`, via `blockFactor_eq_of_frontier`) | core + `exists_dvDissection` |

**Consistency note (checked, not assumed):** the machine refutations
`C64.blockDegEq_false` and C67's `multiplicity_tie` refutation pin the pre-A-C.20
**leaky** selector (`blockFactorLeaky`/`mult₂Leaky` — C64.lean:78, C67.lean:243).  The
A-C.20 `blockFactor` is degree-pinned, and at the same `(s2Frame, L₀, g₀)` probe the
engine produces a labelled quadratic block inside the cubic (`2 = 2·1`).  No landed
refutation record conflicts with F1.1; the records stand against the leaky pair.
(Downstream note: C67's refutation may no longer bear on the PINNED `multiplicity_tie`
shape — it was never re-adjudicated post-A-C.20; out of this unit's scope.)

## Row table — BLOCKED-BECAUSE (exact missing premise; not forced)

The exported `BlockFrontier` is existence + maximality + the `D′` rider ONLY.  The
engine's internal split data (the complement factor `g₂`, its non-`r`-divisible
residual, the point-sided below/other-slope product `Wf`) is dropped at the export —
it exists inside `C133mh14.blockFrontier_of_context_of_theoremA`'s proof (steps 3-6)
but no theorem exports it.  None of these rows was ever landed even conditionally
(corpus grep: no `_of_frontier` variants exist for them).

| row | signed target | missing premise (exact) |
|---|---|---|
| F1.2 | `block_complement_notdvd` (leanspec:1614-1622) | an exported context-split theorem (F1.H1 consumer form): `f = blockFactor L f · g₂ · Wf` with `∀`-pin `¬ L.r ∣ dvResPoly … g₂ …` and `Wf` point-sided at `(L.u, L.ℓ)` — i.e. re-export of MH14's internal steps 3-6 |
| F1.3 | `dv2Supp_translation` | F1.2 + the no-interaction lemma `dv2Pin_mul_complement` (plan sizing 70-120 lines) |
| F1.4 | `dv2ResPoly_scalar` | F1.3 + `γg ≠ 0` + the cocycle telescope |
| F1.5 | `dv2ResPoly_radical_eq` | F1.4 (unit-scalar cancellation over `K₂`) |
| F1.6 | `mult₂_readable` | F1.3 (constant translation preserves the on-side set) |
| F1.7 | `dv2_length_sum` | F1.1 (landed here) + F1.6 |
| F1.8 | `level2_peel` | F1.1-F1.2 + C.61 (the C.27→C.59 chain, still open — F2 of BLOCKERS_PLAN) |
| C.34 | signed `exists_dv_residual_dissection` (leanspec:1562-1580); carrier `exists_dv_residual_dissection_of_frontier` (C34.lean:278, carries `hex`+`hsep`) | `hex`: Theorem A's entry rider `(F.e₁·F.f₁) ∣ deg g` (C133mh14.lean:269) is absent from the signed premises and can genuinely fail at bare pure `g` (C35b's labelled cubic); `hsep`: NO landed uniqueness supplier — `C133mh13.theoremC_placement` is maximality inside a squarefree `BlockContext` `f`, not two-split separation at bare pure `g` (= the never-landed F1.H2 consumer form) |

**Recommended next decomposer (from the blocked column):** a single ~60-line MH14
re-export node ("context split", F1.H1 consumer form) unlocks F1.2 and re-opens F1.3-F1.8
as the plan's chain; nothing else in the family moves without it.

## Out of scope / no action

* `towerLocus_fibration_of_frontier` (C53.lean:312): carries `BudgetBoxRead` — the
  C.52/C.53 budget-box frontier, a different family, closed separately by the dv-engine
  chain (`towerLocus_iff_budget`, commit 1a7fbda8).
* `C48.fullSide_block`, C67/C80 instance pins: construct their frontier legs from
  explicit witnesses (no carried hypothesis) or are refutation records — untouched.
* Chapters A/B/D/E/G: NO lean carriers (E23.lean:71, E51.lean:72 are prose mentions
  only).  No import fence needed; everything landed in the one C-file.
* `multiplicity_tie`, `tie_pure_power`, `dv2Pin_translation_interior`,
  `partial_projection`, `partial_block_decision`: downstream consumers per the plan
  (BLOCKERS_PLAN F1 tail; verdict_CCUR.md:94-98, 118-123) — explicitly excluded from
  the eight-row batch; not touched.

## Verification record

```
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C134cfs.lean
# exit 0
```

Per-decl footprints (printed by the AxCheck footer, all identical):
`blockFactor_spec`, `hasLabel_blockFactor`, `blockFactor_dvd`, `blockDeg_eq`,
`mult₂_pos`, `keyDeg₁_dvd_blockFactor_natDegree` — each exactly
`[propext, Classical.choice, Quot.sound, Uniformity.Density.Tower.exists_dvDissection]`.
Zero `sorry`; no landed file edited; no new axiom.
