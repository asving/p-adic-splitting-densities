# Unit C131v verdict

## C.131v′ — LANDED

The shadow-discrepancy semantic identification (v2 §3.8 `Cnv13`) is landed in full, exact and
unconditional (no `towerLocus`/`μ₂` hypothesis; `hπ : Irreducible π` only, consumed through
C.47's `composedKey_natDegree` exactly as in C.73), in the new file
`leanfinal/Uniformity/ChapC/C131v.lean` (735 lines, namespace
`Uniformity.Density.Tower.C131v`).

## The identification (non-circular)

The census object is C.131m′'s `taggedOuterNF F (xNF F (composedKey T)) f j`, split by its
`paid` tag (`unpaidValue` / `paidValue` = erasure of the tag-filtered census) and collapsed to
`O[x]` by the two-step evaluation at `Y = F.key` (`collapse`, a ring hom).  Nothing is defined
as a normal form *of* the displayed difference; `censusOverflow T f` is built from the tagged
census alone (paid collapses against the powers of `composedKey T`).

Capstones (all with `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

* `shadowDev_eq_collapse_unpaid` — the shadow read IS the census's unpaid (reduced) collapse:
  `shadowDev T f j = collapse F (unpaidValue (taggedOuterNF F (xNF F (composedKey T)) f j))`.
* `shadowDev_eq_dev_corrected` — `shadowDev T f j = dev (composedKey T) (f - censusOverflow T f) j`.
* `shadow_discrepancy` — **the landed `Cnv13`**:
  `shadowDev T f j - dev (composedKey T) f j = - dev (composedKey T) (censusOverflow T f) j`,
  with the positively-signed companion `dev_sub_shadowDev`.

## Full declaration list (37, all sorry-free, Lean-core footprints)

Generic `devQ` complements: `devQ_map` (monic division commutes with ring-map images through
the tower — this is what makes the shadow tower the `AdjoinRoot.mk`-image of the two-variable
tower), `devQ_degree_lt`, `devQ_reconstruct` (the public reconstruction lemma v2 §2.7 F10
flagged missing), `devQ_neg`, `devQ_sub`, `dev_sub`, `monic_divByMonic`, `dev_top_eq_one`.

Two-variable-lift monicity: `xNF_eq_biRep`, `xNF_coeff_top`, `xNF_coeff_eq_zero_of_top_lt`,
`xNF_natDegree`, `xNF_monic` (the lift of a monic degree-`m·D′` polynomial is monic of
`Y`-degree `m`; instantiated at `composedKey T`, `m = e₂f₂`).

Census split and semantics (from C.131m′'s erasure theorem): `unpaidValue`, `paidValue`,
`unpaidValue_add_paidValue`, `unpaidValue_append`, `filter_zero_map_atOuter`,
`unpaidValue_map_atOuter`, `unpaidValue_taggedXNFUpTo`, `unpaidValue_taggedXNF`,
`unpaidValue_taggedCoeffwiseUpTo`, `unpaidValue_taggedOuterNF`, `collapse`, `collapse_apply`,
`collapse_eraseTagged`, `collapse_unpaidValue`, `collapse_unpaid_add_paid`.

Shadow tie and assembly: `reass_map`, `shadowDev_eq_reass_devQ`, `composedKey_natDegree_mul`,
`shadowDev_eq_collapse_unpaid`, `censusOverflow`, `collapse_unpaidValue_degree_lt`,
`shadowDev_eq_dev_corrected`, `shadow_discrepancy`, `dev_sub_shadowDev`.

## Proof mechanism (for C.131w′'s consumption)

Reconstruction + uniqueness at both keys: `devQ_reconstruct` presents `xNF F f` in powers of
`xNF F (composedKey T)`; evaluation at `Y = F.key` (through `taggedOuterNF_erasure` +
`outerNF_reconstruct`) presents `f = Σ (unpaid_{j'} + paid_{j'})·Φ₂^{j'}`; the unpaid
collapses are reduced (`collapse_unpaidValue_degree_lt`), so B.06's `dev_unique` identifies
them with the honest digits of `f - censusOverflow T f`; `dev_sub` peels off the honest read.
For `Cnv14`, F11's floor on the paid census terms now transfers to the displayed difference
through `shadow_discrepancy` (the difference is the `Φ₂`-redevelopment of the erased paid
census value).

## Verification

From `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C131v.lean
```

Succeeds with zero errors and zero warnings.  The file contains no `sorry`, no new axiom, no
`unsafe`.  Every `#print axioms` line prints `[propext, Classical.choice, Quot.sound]` or less
(`unpaidValue_append`: `[propext]`; the two defs `unpaidValue`/`paidValue`: no axioms).
