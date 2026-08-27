# Unit MNV01 verdict — μ₃ campaign nodes M3-NV0 + M3-NV1

Date: 2026-08-27

## Scope

Executed `docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6 rows M3-NV0 and M3-NV1, in order,
against the rows' named landed inputs. No roll-up, `leanspec/`, or existing `leanfinal/` file
was touched; two new files were landed, opening the C132 series.

## M3-NV0 — `leanfinal/Uniformity/ChapC/C132nv0.lean`

Generalizes the `dvSupp` zero/finiteness/add/negation bank
(`Uniformity.Density.Tower.C130s6.dvSupp_zero_eq_top` through `dvSupp_add_eq`,
`C130s6.lean:169-293`) one level up to C.11's `dv2Supp L Ψ f u₂ ℓ₂` (`C11.lean:128-144`).
Landed declarations, all generic over `L : LevelDatum F H₀ hpin`, `Ψ : Polynomial O` (with
explicit `Ψ.Monic`/`0 < Ψ.natDegree` hypotheses where B32a's `dev_add_of_monic` or B04's
`dev_eq_zero_of_lt`/B05's `sum_dev_eq` need them), and any side `(u₂, ℓ₂)` — **no S2 numeral
occurs in any statement**:

- `dv2Pin_top_of_gt` (helper; mirror of C118a's `dvHgt_top_of_gt`)
- `dv2Supp_zero_eq_top`
- `dv2Supp_eq_inf_range`
- `dv2Supp_ne_top_of_ne_zero`
- `min_dv2Supp_le_dv2Supp_add`
- `dv2Supp_neg`
- `dv2Supp_add_eq_of_lt`
- `dv2Supp_add_eq`

Every slot-level step (zero, finiteness, negation, ultrametric inequality) is discharged by
one application of the corresponding landed `dvSupp` fact at `dv2Hgt`'s underlying side
(`dv2Hgt L A = dvSupp F A L.u L.ℓ` definitionally); the only new argument is climbing the
second `Finset.inf` layer, by the same range-truncation/ultrametric proofs C130s6 used one
level down, with `Ψ`'s development standing in for `F.key`'s.

## M3-NV1 — `leanfinal/Uniformity/ChapC/C132nv1.lean`

The first numeral instantiation of the M3-NV0 bank at the S2 depth-two occurrence. Defines

```lean
noncomputable def s2Hgt₃ (g : Polynomial O) : WithTop ℤ :=
  toZ (dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2)
```

(`L` is the same level datum `s2Hgt₂` reads, `s2DepthTwoKeyAt h2 hq 2` is CC-2's promoted
`Φ₂` per `s2DepthTwoKeyAt_two`, `C130s2.lean:181-182`) and pins:

- `s2Hgt₃_eq_dv2Supp` — the field-shape anti-drift `rfl` pin (mirror of `s2Hgt₂_eq_dvSupp`)
- `s2Hgt₃_zero`, `s2Hgt₃_ne_top` — zero/finiteness
- `s2Hgt₃_add_ge`, `s2Hgt₃_add_eq` — the ultrametric inequality and equality off ties
- `s2Hgt₃_Φ₂ : s2Hgt₃ h2 hq (s2DepthTwoKeyAt h2 hq 2) = ((21 : ℤ) : WithTop ℤ)` — the
  tower-height tooth (`= u₃`), the μ₃ analogue of `C130s6.s2Hgt₂_key`'s `h(Φ′) = 5 = u₂`

Two plumbing lemmas (`s2Φ₂_monic`, `s2Φ₂_natDegree : Φ₂.natDegree = 4`) derive `Φ₂`'s
monicity/degree from the already-landed `composedKey_monic` (C.47) and
`composedKey_natDegree_D₂` (C.53b) through CC-2's own bridge (`s2Bridge_Dcum`,
`s2DepthTwo_Dcum_two`) — no new degree/monicity fact invented. The `s2Hgt₃_Φ₂` computation
develops `Φ₂` in itself (`dev = 0` at `j=0`, `dev = 1` at `j=1`, `dev = 0` at `j=2,3,4`) and
reuses the landed `s2Hgt₂_one`/`s2Hgt₂_eq_dv2Hgt` facts (via `toZ_inj`) for the inner μ₂ read
at `1`, rather than re-deriving any frame-level computation.

## Build result

```text
cd leanfinal && lake env lean Uniformity/ChapC/C132nv0.lean   # exit 0
cd leanfinal && lake env lean Uniformity/ChapC/C132nv1.lean   # exit 0
cd leanfinal && lake build Uniformity.ChapC.C132nv1            # Build completed successfully (8687 jobs)
```

Zero `sorry` in both files (`grep -n sorry` empty). Every `#print axioms` footer reports only
`[propext, Classical.choice, Quot.sound]` — Lean-core, no new axiom. Three pre-existing-style
`linter.style.show` warnings fire in C132nv1 (the `show`-to-unfold-`dev`'s-recursive-equation
idiom, e.g. lines 142/150/159) — the same idiom already carries unfixed identical warnings in
the landed `C130s6.lean:496,524`, so this is accepted house style, not a regression.

## Notes for the next node (M3-NV2)

`s2Hgt₃`'s definition and all five pins are unconditional (no open hypothesis). The bank is
ready for M3-NV2 (porting the parameter-free endpoint/minimizer bank from `dvSupp` to
`dv2Supp`, per the campaign row) to consume directly.
