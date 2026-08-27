# HW1 verdict — H.116b4 fireable rows GR-1/2 and GR-3/3b

**VERDICT: LANDED.**  The two supply/fireable rows in
`docs/in-progress/H116B4_MAP_2026-08-26.md` are landed in the single preparatory file
`leanfinal/Uniformity/ChapH/H116b4a.lean`.  The signed theorem
`planted_presentation_card` is not stated or claimed here.  No fibre-to-fibre replant map is
defined.

## GR-1/2 — ghosts and raw/image bookkeeping

LANDED:

- `plantedFactorClass` and its range carrier `PlantedFactorImage` (`H116b4a.lean:30`, `:35`).
- `plantedFactorClass_eq_iff` and `plantedFactorClass_eq_iff_windowMap`, exposing exactly the
  landed shear windows `N - μ*k + k*j` (`:39`, `:90`).
- `card_plantedFactor_fiber`: one positive cardinal on every nonempty factor-image fibre
  (`:170`).
- `card_ker_plantedWindowMap` and `card_plantedFactor_fiber_closed`: the closed value
  `residueCard O ^ (k * (μ * (μ + 1) / 2))` (`:220`, `:265`).
- `card_rawFactorImages_fiber`: dependent-product constant-fibre bookkeeping (`:348`).
- `card_rawPres_eq_ghost_mul_imagePres`: the requested leaf identity
  `Nat.card Pres = (∏ p∈L, q^(k_p * (μ_p*(μ_p+1)/2))) * Nat.card ImgPres`
  (`:619`).  The cofactor coordinate is retained injectively and contributes no ghost.

The proof uses `proj_alphaParentCoeff_eq_iff`, quotient truncation surjectivity,
`card_preimage_of_surjective`, `card_res`, and `Nat.card_pi`.  No restricted-Smith or lifting
claim occurs.

## GR-3/3b — cofactor/Fit

LANDED:

- `ImageFactors`, `imageFactorProduct`, `imageProductClass`, `ImgPres`, and `Fit`
  (`H116b4a.lean:424`--`:465`).
- `cofactor_eq_of_imageProductClass_eq`: uniqueness of the monic cofactor over
  `O/𝔪^N`, using regularity of a monic polynomial rather than domain cancellation
  (`:470`).
- `imagePresentation_equiv_fit`: image presentations are equivalent to fitting factor-image
  tuples (`:501`).
- `cofactor_admissible_of_plantedPresentation`: reverse child-freeness, root-freeness at every
  occupied frame, and the forced content formula (`:651`).  Its proof runs
  `plantedPoly_frame_profile` backwards and uses `hasChildAt_mult_unique`; it does not use
  `plantedPoly_genre` as a converse.

## Elaboration and axiom check

Command from `leanfinal/`:

```text
lake env lean Uniformity/ChapH/H116b4a.lean
```

Result: exit 0.  There are zero `sorry` occurrences and no new axiom declarations.

The `#print axioms` footer is at `H116b4a.lean:850`--`:859`.  Every printed declaration has
the same Lean-core footprint:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, no declaration reports `sorryAx`.

## Plumbing-only deviations from the map sketch

1. The map abbreviated carrier definitions.  `PlantedFactorImage` is made explicitly as the
   range of the level-`N` planted coefficient class, while `ImageFactors`, `Pres`, `ImgPres`,
   and `Fit` are explicit dependent subtypes.
2. The map's ellipses conceal the positivity/window data needed by GR-1/2.  The landed
   statements expose `hN`, `hμ`, and `μ*k ≤ N-1`; the presentation product theorem exposes
   these coordinatewise as `hL`.
3. `imagePresentation_equiv_fit` exposes `hπ`, `hN`, and the degree identity `hdeg`.  These are
   needed only to establish that `O/𝔪^N` is nontrivial and that both monic products have
   the advertised degree.
4. The sketch name `RootFreeAtFrames` was not landed previously, so the reverse theorem expands
   its predicate verbatim.  Likewise, all genre assumptions hidden by the sketch's ellipses are
   explicit (`hm`, `hN`, `hdeg`, exact child set, and content data).
5. Mathlib/repository monic-polynomial helper statements carried domain assumptions unsuitable
   for `O/𝔪^N`.  Ring-level helper variants are proved locally; the mathematical content is
   unchanged.

No content deviation and no `BLOCKED-BECAUSE` occurred for either charged row.
